using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using ClassicUO.Assets;
using ClassicUO.Configuration;
using ClassicUO.Game.Data;
using ClassicUO.Game.GameObjects;
using ClassicUO.Game.Map;
using ClassicUO.Utility;
using ClassicUO.Utility.Logging;

namespace ClassicUO.Game.Managers
{
    public sealed class WalkableManager
    {
        private static WalkableManager _instance;
        private static readonly object _lock = new object();
        private const int CHUNK_SIZE = 8;
        private const int MAX_MAP_COUNT = 6;
        private const string WALKABLE_DATA_DIR = "walkable_cache";

        private readonly Dictionary<int, WalkableMapData> _mapData = new();
        private readonly Dictionary<int, WalkableMapData> _sessionModifications = new();
        private readonly Dictionary<int, bool> _mapGenerationComplete = new();
        private readonly Dictionary<int, int> _mapChunkGenerationIndex = new();
        private int _lastMapIndex = -1;
        private int _updateCounter = 0;
        private volatile bool _isGenerating = false;
        private readonly object _generationLock = new object();
        private int _chunksPerCycle = 1; // Start with 1 for performance measurement
        private const int TARGET_GENERATION_TIME_MS = 5;
        private const int MIN_CHUNKS_PER_CYCLE = 1;
        private const int MAX_CHUNKS_PER_CYCLE = 500;
        private readonly List<double> _recentGenerationTimes = new();
        private const int PERFORMANCE_SAMPLE_SIZE = 5;

        private WalkableManager()
        {
        }

        public static WalkableManager Instance
        {
            get
            {
                if (_instance == null)
                {
                    lock (_lock)
                    {
                        if (_instance == null)
                            _instance = new WalkableManager();
                    }
                }
                return _instance;
            }
        }

        public void Initialize()
        {
            CreateCacheDirectory();
            LoadAllMapData();
        }

        public bool IsWalkable(int x, int y)
        {
            if (!World.InGame || World.Map == null)
                return false;

            int mapIndex = World.Map.Index;

            // Check session modifications first
            if (_sessionModifications.TryGetValue(mapIndex, out var sessionData))
            {
                if (sessionData.HasDataForTile(x, y))
                {
                    return sessionData.GetWalkable(x, y);
                }
            }

            // Check persistent data
            if (_mapData.TryGetValue(mapIndex, out var mapData))
            {
                if (mapData.HasDataForTile(x, y))
                {
                    return mapData.GetWalkable(x, y);
                }
            }

            // If no data exists, calculate on demand
            return CalculateWalkabilityForTile(x, y);
        }

        public void SetSessionWalkable(int x, int y, bool walkable)
        {
            if (!World.InGame || World.Map == null)
                return;

            int mapIndex = World.Map.Index;

            if (!_sessionModifications.TryGetValue(mapIndex, out var sessionData))
            {
                sessionData = new WalkableMapData(mapIndex);
                _sessionModifications[mapIndex] = sessionData;
            }

            sessionData.SetWalkable(x, y, walkable);
        }

        public void Update()
        {
            if (!World.InGame || World.Map == null)
                return;

            int mapIndex = World.Map.Index;

            // Check if map has changed
            if (_lastMapIndex != mapIndex)
            {
                _lastMapIndex = mapIndex;
                ClearSessionModifications(); // Clear session mods when changing maps
            }

            // Only generate chunks if the map isn't fully generated yet
            if (!IsMapGenerationComplete(mapIndex))
            {
                _updateCounter++;

                // Generate chunks every other update
                if (_updateCounter % 2 == 0)
                {
                    GenerateNextChunks(_chunksPerCycle);
                }
            }
        }

        public bool IsMapGenerationComplete(int mapIndex)
        {
            return _mapGenerationComplete.TryGetValue(mapIndex, out var isComplete) && isComplete;
        }

        public bool IsCurrentMapReady()
        {
            if (!World.InGame || World.Map == null)
                return false;

            return IsMapGenerationComplete(World.Map.Index);
        }

        public (int current, int total) GetMapGenerationProgress(int mapIndex)
        {
            if (IsMapGenerationComplete(mapIndex))
            {
                int totalChunksX = MapLoader.Instance.MapBlocksSize[mapIndex, 0];
                int totalChunksY = MapLoader.Instance.MapBlocksSize[mapIndex, 1];
                int totalChunks = totalChunksX * totalChunksY;
                return (totalChunks, totalChunks);
            }

            int currentIndex = _mapChunkGenerationIndex.TryGetValue(mapIndex, out var index) ? index : 0;
            int totalChunksXCalc = MapLoader.Instance.MapBlocksSize[mapIndex, 0];
            int totalChunksYCalc = MapLoader.Instance.MapBlocksSize[mapIndex, 1];
            int totalChunksCalc = totalChunksXCalc * totalChunksYCalc;

            return (currentIndex, totalChunksCalc);
        }

        public (int current, int total) GetCurrentMapGenerationProgress()
        {
            if (!World.InGame || World.Map == null)
                return (0, 0);

            return GetMapGenerationProgress(World.Map.Index);
        }

        private ulong nextUpdateMessage = Time.Ticks;

        private void GenerateNextChunks(int numChunks)
        {
            if (!World.InGame || World.Map == null || _isGenerating)
                return;

            lock (_generationLock)
            {
                if (_isGenerating)
                    return;

                _isGenerating = true;
            }

            var stopwatch = Stopwatch.StartNew();

            try
            {
                int mapIndex = World.Map.Index;

                if (!_mapData.TryGetValue(mapIndex, out var mapData))
                {
                    mapData = new WalkableMapData(mapIndex);
                    _mapData[mapIndex] = mapData;
                }

                // Calculate chunks to generate
                int totalChunksX = MapLoader.Instance.MapBlocksSize[mapIndex, 0];
                int totalChunksY = MapLoader.Instance.MapBlocksSize[mapIndex, 1];
                int totalChunks = totalChunksX * totalChunksY;

                int currentIndex = _mapChunkGenerationIndex.TryGetValue(mapIndex, out var index) ? index : 0;

                // Generate multiple chunks up to the requested number
                int chunksGenerated = 0;
                while (chunksGenerated < numChunks && currentIndex < totalChunks)
                {
                    int chunkX = currentIndex / totalChunksY;
                    int chunkY = currentIndex % totalChunksY;

                    GenerateChunkWalkabilitySync(chunkX, chunkY, mapData);

                    currentIndex++;
                    chunksGenerated++;
                }

                if (Time.Ticks > nextUpdateMessage)
                {
                    var val = GetCurrentMapGenerationProgress();
                    GameActions.Print($"Generating pathfinding cache. {MathHelper.PercetangeOf(val.current, val.total)}% ({val.current}/{val.total})");
                    nextUpdateMessage = Time.Ticks + 5000;
                }

                // Update the generation index
                _mapChunkGenerationIndex[mapIndex] = currentIndex;

                // Check if generation is complete
                if (currentIndex >= totalChunks)
                {
                    _mapGenerationComplete[mapIndex] = true;
                    Log.Info($"[WalkableManager] Map {mapIndex} generation completed. Total chunks: {totalChunks}");
                    GameActions.Print($"Pathfinding cache completed for map {mapIndex}!");
                }
            }
            finally
            {
                stopwatch.Stop();

                // Record performance and adjust chunks per cycle
                double elapsedMs = stopwatch.Elapsed.TotalMilliseconds;
                AdjustChunksPerCycleBasedOnPerformance(elapsedMs, numChunks);

                lock (_generationLock)
                {
                    _isGenerating = false;
                }
            }
        }

        private void AdjustChunksPerCycleBasedOnPerformance(double elapsedMs, int chunksGenerated)
        {
            // Only adjust if we actually generated chunks
            if (chunksGenerated == 0)
                return;

            // Calculate time per chunk
            double timePerChunk = elapsedMs / chunksGenerated;

            // Add to recent generation times for smoothing
            _recentGenerationTimes.Add(elapsedMs);
            if (_recentGenerationTimes.Count > PERFORMANCE_SAMPLE_SIZE)
            {
                _recentGenerationTimes.RemoveAt(0);
            }

            // Only adjust after we have enough samples
            if (_recentGenerationTimes.Count < PERFORMANCE_SAMPLE_SIZE)
                return;

            // Calculate average time from recent samples
            double avgTime = 0;
            foreach (double time in _recentGenerationTimes)
            {
                avgTime += time;
            }
            avgTime /= _recentGenerationTimes.Count;

            int oldChunksPerCycle = _chunksPerCycle;

            // Adjust chunks per cycle based on performance
            if (avgTime < TARGET_GENERATION_TIME_MS * 0.8) // If we're significantly under target
            {
                // Increase chunks per cycle
                _chunksPerCycle = Math.Min(_chunksPerCycle + 1, MAX_CHUNKS_PER_CYCLE);
            }
            else if (avgTime > TARGET_GENERATION_TIME_MS * 1.2) // If we're significantly over target
            {
                // Decrease chunks per cycle
                _chunksPerCycle = Math.Max(_chunksPerCycle - 1, MIN_CHUNKS_PER_CYCLE);
            }

            // Log performance adjustments
            if (_chunksPerCycle != oldChunksPerCycle)
            {
                Log.Info($"[WalkableManager] Performance adjustment: {oldChunksPerCycle} -> {_chunksPerCycle} chunks/cycle (avg: {avgTime:F1}ms, target: {TARGET_GENERATION_TIME_MS}ms)");

                // Clear samples when we make an adjustment to get fresh data
                _recentGenerationTimes.Clear();
            }
        }

        private void GenerateChunkWalkabilitySync(int chunkX, int chunkY, WalkableMapData mapData)
        {
            try
            {
                // Generate walkability data for an 8x8 chunk synchronously
                for (int x = chunkX * CHUNK_SIZE; x < (chunkX + 1) * CHUNK_SIZE; x++)
                {
                    for (int y = chunkY * CHUNK_SIZE; y < (chunkY + 1) * CHUNK_SIZE; y++)
                    {
                        if (!mapData.HasDataForTile(x, y))
                        {
                            bool walkable = CalculateWalkabilityForTile(x, y);
                            mapData.SetWalkable(x, y, walkable);
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                Log.Error($"[WalkableManager] Error generating chunk ({chunkX}, {chunkY}): {ex.Message}");
            }
        }

        private void GenerateChunkWalkabilityAsync(int chunkX, int chunkY, WalkableMapData mapData)
        {
            Task.Run(() =>
            {
                try
                {
                    // Generate walkability data for an 8x8 chunk
                    for (int x = chunkX * CHUNK_SIZE; x < (chunkX + 1) * CHUNK_SIZE; x++)
                    {
                        for (int y = chunkY * CHUNK_SIZE; y < (chunkY + 1) * CHUNK_SIZE; y++)
                        {
                            if (!mapData.HasDataForTile(x, y))
                            {
                                bool walkable = CalculateWalkabilityForTile(x, y);
                                mapData.SetWalkable(x, y, walkable);
                            }
                        }
                    }
                }
                catch (Exception ex)
                {
                    Log.Error($"[WalkableManager] Error generating chunk ({chunkX}, {chunkY}): {ex.Message}");
                }
            });
        }

        private static Direction _unreleventDirection = Direction.NONE;

        private bool CalculateWalkabilityForTile(int x, int y)
        {
            try
            {
                if (World.Map == null)
                {
                    Log.Debug($"[WalkableManager] World.Map is null");
                    return false;
                }

                GameObject tile = World.Map.GetTile(x, y);
                if (tile == null)
                {
                    Log.Debug($"[WalkableManager] No tile found at ({x}, {y})");
                    return false;
                }


                // For now, let's use a very basic walkability check
                // If we can get a tile, and it's a land tile, consider it walkable
                // if (tile is Land land)
                // {
                //     //Log.Debug($"[WalkableManager] Land tile at ({x}, {y}) z={z}: true");
                //
                //     return true; // Very permissive for now
                // }
                sbyte z = World.Map.GetTileZ(x, y);
                return Pathfinder.CanWalk(ref _unreleventDirection, ref x, ref y, ref z, true);


                // For other tile types, also be permissive for debugging
                //Log.Debug($"[WalkableManager] Non-land tile at ({x}, {y}): true");
                return true;
            }
            catch (Exception ex)
            {
                Log.Warn($"[WalkableManager] Error calculating walkability at ({x}, {y}): {ex.Message}");
                return false;
            }
        }

        private void CreateCacheDirectory()
        {
            try
            {
                string cacheDir = Path.Combine(ProfileManager.ProfilePath ?? ".", WALKABLE_DATA_DIR);
                if (!Directory.Exists(cacheDir))
                {
                    Directory.CreateDirectory(cacheDir);
                }
            }
            catch (Exception ex)
            {
                Log.Error($"[WalkableManager] Failed to create cache directory: {ex.Message}");
            }
        }

        private void LoadAllMapData()
        {
            for (int mapIndex = 0; mapIndex < MAX_MAP_COUNT; mapIndex++)
            {
                LoadMapData(mapIndex);
            }
        }

        private void LoadMapData(int mapIndex)
        {
            try
            {
                string filename = GetMapDataFileName(mapIndex);
                if (File.Exists(filename))
                {
                    var mapData = new WalkableMapData(mapIndex);
                    mapData.LoadFromFile(filename);
                    _mapData[mapIndex] = mapData;

                    // Check if this map was fully generated
                    int totalChunksX = MapLoader.Instance.MapBlocksSize[mapIndex, 0];
                    int totalChunksY = MapLoader.Instance.MapBlocksSize[mapIndex, 1];
                    int totalChunks = totalChunksX * totalChunksY;

                    // Calculate how many generation chunks we have completed
                    int completedChunks = mapData.CalculateGenerationProgress(mapIndex);

                    if (completedChunks >= totalChunks)
                    {
                        // Map is fully generated
                        _mapGenerationComplete[mapIndex] = true;
                        Log.Info($"[WalkableManager] Map {mapIndex} loaded - fully generated ({completedChunks}/{totalChunks} chunks)");
                    }
                    else
                    {
                        // Continue generation from where we left off
                        _mapChunkGenerationIndex[mapIndex] = completedChunks;
                        Log.Info($"[WalkableManager] Map {mapIndex} loaded - continuing generation from chunk {completedChunks}/{totalChunks}");
                    }
                }
            }
            catch (Exception ex)
            {
                Log.Error($"[WalkableManager] Failed to load map data for map {mapIndex}: {ex.Message}");
            }
        }

        public void SaveMapData(int mapIndex)
        {
            try
            {
                if (_mapData.TryGetValue(mapIndex, out var mapData))
                {
                    string filename = GetMapDataFileName(mapIndex);
                    mapData.SaveToFile(filename);
                }
            }
            catch (Exception ex)
            {
                Log.Error($"[WalkableManager] Failed to save map data for map {mapIndex}: {ex.Message}");
            }
        }

        public void SaveAllMapData()
        {
            foreach (var kvp in _mapData)
            {
                SaveMapData(kvp.Key);
            }
        }

        private string GetMapDataFileName(int mapIndex)
        {
            string cacheDir = Path.Combine(ProfileManager.ProfilePath ?? ".", WALKABLE_DATA_DIR);
            return Path.Combine(cacheDir, $"walkable_map_{mapIndex}.dat");
        }

        public void ClearSessionModifications()
        {
            _sessionModifications.Clear();
        }

        public void Shutdown()
        {
            SaveAllMapData();
            _mapData.Clear();
            _sessionModifications.Clear();
        }
    }

    internal sealed class WalkableMapData
    {
        private readonly int _mapIndex;
        private readonly Dictionary<long, BitArray8x8> _chunks = new();
        private readonly object _dataLock = new object();

        public WalkableMapData(int mapIndex)
        {
            _mapIndex = mapIndex;
        }

        public bool HasDataForTile(int x, int y)
        {
            long chunkKey = GetChunkKey(x >> 3, y >> 3); // Changed from >> 5 to >> 3 for 8x8 chunks
            lock (_dataLock)
            {
                if (_chunks.TryGetValue(chunkKey, out var chunk))
                {
                    // Check if this specific tile has been set (not just if the chunk exists)
                    return chunk.IsSet(x & 7, y & 7);
                }
                return false;
            }
        }

        public bool GetWalkable(int x, int y)
        {
            long chunkKey = GetChunkKey(x >> 3, y >> 3); // Changed from >> 5 to >> 3 for 8x8 chunks
            lock (_dataLock)
            {
                if (_chunks.TryGetValue(chunkKey, out var chunk))
                {
                    return chunk.Get(x & 7, y & 7); // Changed from & 31 to & 7 for 8x8 chunks
                }
            }
            return false;
        }

        public void SetWalkable(int x, int y, bool walkable)
        {
            long chunkKey = GetChunkKey(x >> 3, y >> 3); // Changed from >> 5 to >> 3 for 8x8 chunks
            lock (_dataLock)
            {
                if (!_chunks.TryGetValue(chunkKey, out var chunk))
                {
                    chunk = new BitArray8x8(); // Changed from BitArray32x32 to BitArray8x8
                    _chunks[chunkKey] = chunk;
                }
                chunk.Set(x & 7, y & 7, walkable); // Changed from & 31 to & 7 for 8x8 chunks
            }
        }

        public int GetLoadedChunkCount()
        {
            // This is not accurate for continuation because chunks are 32x32 bit arrays
            // but generation works with 8x8 map chunks. We need a different approach.
            lock (_dataLock)
            {
                return _chunks.Count;
            }
        }

        public int CalculateGenerationProgress(int mapIndex)
        {
            // Calculate how many 8x8 map chunks we have data for
            // by checking which generation chunks have any walkable data
            int totalChunksX = MapLoader.Instance.MapBlocksSize[mapIndex, 0];
            int totalChunksY = MapLoader.Instance.MapBlocksSize[mapIndex, 1];

            int completedChunks = 0;

            lock (_dataLock)
            {
                // Check each 8x8 map chunk to see if we have data for it
                for (int chunkIndex = 0; chunkIndex < totalChunksX * totalChunksY; chunkIndex++)
                {
                    int chunkX = chunkIndex / totalChunksY;
                    int chunkY = chunkIndex % totalChunksY;

                    // Check if this 8x8 chunk has any data by sampling a few tiles
                    bool hasData = false;
                    for (int x = chunkX * 8; x < (chunkX + 1) * 8 && !hasData; x++)
                    {
                        for (int y = chunkY * 8; y < (chunkY + 1) * 8 && !hasData; y++)
                        {
                            if (HasDataForTile(x, y))
                            {
                                hasData = true;
                            }
                        }
                    }

                    if (hasData)
                    {
                        completedChunks = chunkIndex + 1; // +1 because we completed this chunk
                    }
                    else
                    {
                        break; // Sequential generation, so we can stop here
                    }
                }
            }

            return completedChunks;
        }

        private static long GetChunkKey(int chunkX, int chunkY)
        {
            return ((long)chunkX << 32) | (uint)chunkY;
        }

        public void SaveToFile(string filename)
        {
            string tempFilename = filename + ".tmp";

            try
            {
                using (var stream = new FileStream(tempFilename, FileMode.Create, FileAccess.Write))
                using (var writer = new BinaryWriter(stream))
                {
                    lock (_dataLock)
                    {
                        writer.Write(_mapIndex);
                        writer.Write(_chunks.Count);

                        foreach (var kvp in _chunks)
                        {
                            writer.Write(kvp.Key);
                            kvp.Value.WriteTo(writer);
                        }
                    }
                }

                // Atomic replace
                if (File.Exists(filename))
                {
                    File.Delete(filename);
                }
                File.Move(tempFilename, filename);
            }
            catch (Exception ex)
            {
                try
                {
                    if (File.Exists(tempFilename))
                    {
                        File.Delete(tempFilename);
                    }
                }
                catch { }

                throw new IOException($"Failed to save walkable data: {ex.Message}", ex);
            }
        }

        public void LoadFromFile(string filename)
        {
            try
            {
                using (var stream = new FileStream(filename, FileMode.Open, FileAccess.Read))
                using (var reader = new BinaryReader(stream))
                {
                    int mapIndex = reader.ReadInt32();
                    if (mapIndex != _mapIndex)
                    {
                        throw new InvalidDataException($"Map index mismatch: expected {_mapIndex}, got {mapIndex}");
                    }

                    int chunkCount = reader.ReadInt32();

                    lock (_dataLock)
                    {
                        _chunks.Clear();

                        for (int i = 0; i < chunkCount; i++)
                        {
                            long chunkKey = reader.ReadInt64();
                            var chunk = new BitArray8x8();
                            chunk.ReadFrom(reader);
                            _chunks[chunkKey] = chunk;
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                throw new IOException($"Failed to load walkable data: {ex.Message}", ex);
            }
        }
    }

    internal sealed class BitArray8x8
    {
        private readonly byte[] _data = new byte[8];
        private readonly byte[] _isset = new byte[8]; // Track which bits have been explicitly set

        public bool Get(int x, int y)
        {
            if (x < 0 || x >= 8 || y < 0 || y >= 8)
                return false;

            return (_data[y] & (1 << x)) != 0;
        }

        public bool IsSet(int x, int y)
        {
            if (x < 0 || x >= 8 || y < 0 || y >= 8)
                return false;

            return (_isset[y] & (1 << x)) != 0;
        }

        public void Set(int x, int y, bool value)
        {
            if (x < 0 || x >= 8 || y < 0 || y >= 8)
                return;

            // Mark this position as set
            _isset[y] |= (byte)(1 << x);

            // Set the actual data value
            if (value)
                _data[y] |= (byte)(1 << x);
            else
                _data[y] &= (byte)~(1 << x);
        }

        public void WriteTo(BinaryWriter writer)
        {
            // Write data array
            for (int i = 0; i < 8; i++)
            {
                writer.Write(_data[i]);
            }
            // Write isset array
            for (int i = 0; i < 8; i++)
            {
                writer.Write(_isset[i]);
            }
        }

        public void ReadFrom(BinaryReader reader)
        {
            // Read data array
            for (int i = 0; i < 8; i++)
            {
                _data[i] = reader.ReadByte();
            }
            // Read isset array
            for (int i = 0; i < 8; i++)
            {
                _isset[i] = reader.ReadByte();
            }
        }
    }

    internal sealed class BitArray32x32
    {
        private readonly uint[] _data = new uint[32];

        public bool Get(int x, int y)
        {
            if (x < 0 || x >= 32 || y < 0 || y >= 32)
                return false;

            return (_data[y] & (1u << x)) != 0;
        }

        public void Set(int x, int y, bool value)
        {
            if (x < 0 || x >= 32 || y < 0 || y >= 32)
                return;

            if (value)
                _data[y] |= (1u << x);
            else
                _data[y] &= ~(1u << x);
        }

        public void WriteTo(BinaryWriter writer)
        {
            for (int i = 0; i < 32; i++)
            {
                writer.Write(_data[i]);
            }
        }

        public void ReadFrom(BinaryReader reader)
        {
            for (int i = 0; i < 32; i++)
            {
                _data[i] = reader.ReadUInt32();
            }
        }
    }
}
