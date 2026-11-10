/**CFile****************************************************************

  FileName    [eslim3Checkpoint.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based local circuit improvement (eSLIM3).]

  Synopsis    [Portable publication of AIG checkpoints and timing records.]

  Author      [ABC contributors.]

  Date        [Ver. 1.0. Started - November 9, 2026.]

***********************************************************************/

#include "checkpoint.h"
#include <cerrno>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fcntl.h>
#include <sys/stat.h>
#ifdef _WIN32
#include <io.h>
#else
#include <unistd.h>
#endif

ABC_NAMESPACE_IMPL_START
namespace eSLIM3 {

  namespace {
    // Use the platform's exclusive-create flag rather than the C11 fopen
    // "x" extension, which is not supported by every CRT (including MSVC).
/**Function*************************************************************

  Synopsis    [Create a new binary file without overwriting an existing path.]

  Description [Uses the platform-specific exclusive-create flag and closes the descriptor if stream construction fails.]

  SideEffects [Creates a new file; returns an owned stream or NULL.]

***********************************************************************/
    FILE* createExclusive(const std::string& path) {
#ifdef _WIN32
      const int fd = _open(path.c_str(), _O_WRONLY | _O_CREAT | _O_EXCL | _O_BINARY, _S_IREAD | _S_IWRITE);
      if (fd < 0)
        return nullptr;
      FILE* file = _fdopen(fd, "wb");
      if (!file)
        _close(fd);
#else
      const int fd = open(path.c_str(), O_WRONLY | O_CREAT | O_EXCL, 0666);
      if (fd < 0)
        return nullptr;
      FILE* file = fdopen(fd, "wb");
      if (!file)
        close(fd);
#endif
      return file;
    }

/**Function*************************************************************

  Synopsis    [Check that no file or symbolic link occupies a checkpoint path.]

  Description [An inaccessible path is not treated as absent.]

  SideEffects [None.]

***********************************************************************/
    bool absent(const std::string& path) {
      std::error_code code;
      const auto status = std::filesystem::symlink_status(path, code);
      return status.type() == std::filesystem::file_type::not_found &&
             (!code || code == std::errc::no_such_file_or_directory);
    }
  }

/**Function*************************************************************

  Synopsis    [Parse strictly increasing positive checkpoint times.]

  Description [Rejects malformed values, overflow, duplicates, and times beyond the command timeout.]

  SideEffects [Clears and fills the caller-owned schedule.]

***********************************************************************/
  bool readCheckpointTimes(const char* text, unsigned timeout, std::vector<unsigned>& times) {
    times.clear();
    if (!text || !*text)
      return false;
    while (*text) {
      if (*text < '0' || *text > '9')
        return false;
      char* end;
      errno = 0;
      const unsigned long value = std::strtoul(text, &end, 10);
      if (errno == ERANGE || !value || value > UINT_MAX || value > timeout ||
          (!times.empty() && value <= times.back()) || (*end && *end != ','))
        return false;
      times.push_back(unsigned(value));
      if (!*end)
        return true;
      text = end + 1;
    }
    return false; // trailing comma
  }

/**Function*************************************************************

  Synopsis    [Initialize the state of one checkpoint writer.]

  Description [The prefix and schedule belong to this instance; clocks are reset after preflight succeeds.]

  SideEffects [Initializes writer-owned state.]

***********************************************************************/
  CheckpointWriter::CheckpointWriter(const char* prefix, const std::vector<unsigned>& times, unsigned timeout)
      : prefix(prefix), times(times), timeout(timeout), start(Clock::now()), cpu_start(std::clock()) {}

/**Function*************************************************************

  Synopsis    [Check destinations and writability before circuit optimization.]

  Description [Existing paths are preserved. A prefix-specific exclusive probe checks output access.]

  SideEffects [Creates and removes the probe; resets writer clocks and status.]

***********************************************************************/
  bool CheckpointWriter::prepare() {
    for (unsigned seconds : times) {
      const std::string base = prefix + "." + std::to_string(seconds) + "s";
      for (const char* suffix : {".aig", ".json", ".json.tmp"}) {
        if (!absent(base + suffix)) {
          std::fprintf(stderr, "eSLIM3: checkpoint destination already exists or cannot be inspected: %s\n", (base + suffix).c_str());
          error = true;
          return false;
        }
      }
    }
    // Fail before the expensive search if the destination is not writable.
    const std::string probe = prefix + ".checkpoint-probe.tmp";
    FILE* file = createExclusive(probe);
    if (!file) {
      std::fprintf(stderr, "eSLIM3: cannot create checkpoint files with prefix %s\n", prefix.c_str());
      error = true;
      return false;
    }
    const int status = std::fclose(file);
    const int removed = std::remove(probe.c_str());
    error = status != 0 || removed != 0;
    start = Clock::now();
    cpu_start = std::clock();
    return !error;
  }

/**Function*************************************************************

  Synopsis    [Return the next intermediate checkpoint deadline.]

  Description [The endpoint is published by the caller after final inprocessing.]

  SideEffects [None.]

***********************************************************************/
  CheckpointWriter::Clock::time_point CheckpointWriter::nextTime() const {
    // The endpoint includes final inprocessing. It is emitted by the caller
    // after the whole command, rather than by the optimization loop.
    return error || next == times.size() || times[next] == timeout ? Clock::time_point::max()
                                                                 : start + std::chrono::seconds(times[next]);
  }

/**Function*************************************************************

  Synopsis    [Publish all checkpoints currently due for this instance.]

  Description [Early completion publishes remaining records with their actual elapsed times. A failure disables further writes.]

  SideEffects [Writes requested files and advances writer state.]

***********************************************************************/
  CheckpointWriter::Clock::time_point CheckpointWriter::write(eSLIM3CirMan& circuit, bool finished) {
    while (!error && next < times.size() &&
           (finished || (times[next] < timeout && Clock::now() >= start + std::chrono::seconds(times[next])))) {
      error = !writeOne(circuit, times[next], finished);
      ++next;
    }
    return nextTime();
  }

/**Function*************************************************************

  Synopsis    [Write an AIG snapshot followed by its metadata commit marker.]

  Description [The AIG is closed before metadata is published. The caller retains ownership of the circuit on failure.]

  SideEffects [Creates snapshot files and prints their status.]

***********************************************************************/
  bool CheckpointWriter::writeOne(eSLIM3CirMan& circuit, unsigned requested, bool finished) {
    const double elapsed = std::chrono::duration<double>(Clock::now() - start).count();
    const double cpu = double(std::clock() - cpu_start) / CLOCKS_PER_SEC;
    const std::string base = prefix + "." + std::to_string(requested) + "s";
    const std::string aig = base + ".aig", json = base + ".json", temporary = json + ".tmp";
    Gia_Man_t* snapshot = circuit.eSLIM3CirManToGia();
    const int inputs = Gia_ManPiNum(snapshot), outputs = Gia_ManPoNum(snapshot);
    const int ands = Gia_ManAndNum(snapshot), depth = Gia_ManLevelNum(snapshot);
    Vec_Str_t* bytes = Gia_AigerWriteIntoMemoryStr(snapshot);
    FILE* file = createExclusive(aig);
    bool saved = false;
    if (file) {
      saved = std::fwrite(Vec_StrArray(bytes), 1, Vec_StrSize(bytes), file) == size_t(Vec_StrSize(bytes));
      const int closed = std::fclose(file);
      saved = saved && closed == 0;
    }
    Vec_StrFree(bytes);
    Gia_ManStop(snapshot);
    if (!saved) {
      std::fprintf(stderr, "eSLIM3: failed to write checkpoint %s\n", aig.c_str());
      return false;
    }
    // Readers watch for the JSON commit marker, which appears only after the
    // complete AIG has been closed. A partial write is never a ready snapshot.
    file = createExclusive(temporary);
    const char* stage = !finished ? "intermediate" : elapsed < requested ? "completed_early" : "final";
    if (!file) {
      std::fprintf(stderr, "eSLIM3: cannot create checkpoint metadata %s\n", temporary.c_str());
      return false;
    }
    const int printed = std::fprintf(file,
        "{\"requested_seconds\":%u,\"elapsed_seconds\":%.9f,\"cpu_seconds\":%.9f,"
        "\"stage\":\"%s\",\"inputs\":%d,\"outputs\":%d,\"ands\":%d,\"depth\":%d}\n",
        requested, elapsed, cpu, stage, inputs, outputs, ands, depth);
    const int closed = std::fclose(file);
    // Publish a closed metadata file by renaming within the same directory;
    // no hard-link support is required. Exclusive AIG/tmp creation prevents
    // two writers of this prefix from racing to publish the same snapshot.
    // Also refuse a destination created by someone else during the search.
    if (printed < 0 || closed || !absent(json) || std::rename(temporary.c_str(), json.c_str()) != 0) {
      std::fprintf(stderr, "eSLIM3: failed to publish checkpoint metadata %s\n", json.c_str());
      return false;
    }
    std::printf("Checkpoint: requested=%u elapsed=%.6f cpu=%.6f ands=%d depth=%d stage=%s file=%s\n",
                requested, elapsed, cpu, ands, depth, stage, aig.c_str());
    std::fflush(stdout);
    return true;
  }
}
ABC_NAMESPACE_IMPL_END
