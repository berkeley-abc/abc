/**CFile****************************************************************

  FileName    [checkpoint.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based local circuit improvement (eSLIM3).]

  Synopsis    [Serial AIG checkpoint configuration and publication.]

  Author      [ABC contributors.]

  Date        [Ver. 1.0. Started - November 9, 2026.]

***********************************************************************/

// AIG snapshots at safe boundaries of an uninterrupted serial search.
#ifndef ABC__OPT__ESLIM3__CHECKPOINT_h
#define ABC__OPT__ESLIM3__CHECKPOINT_h

#include <chrono>
#include <ctime>
#include <string>
#include <vector>
#include "eslim3CirMan.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  bool readCheckpointTimes(const char* text, unsigned timeout, std::vector<unsigned>& times);

  class CheckpointWriter {
    public:
      using Clock = std::chrono::steady_clock;
      CheckpointWriter(const char* prefix, const std::vector<unsigned>& times, unsigned timeout);
      bool prepare();
      Clock::time_point nextTime() const;
      Clock::time_point write(eSLIM3CirMan& circuit, bool finished = false);
      bool failed() const { return error; }

    private:
      std::string prefix;
      std::vector<unsigned> times;
      unsigned timeout;
      size_t next = 0;
      Clock::time_point start;
      std::clock_t cpu_start;
      bool error = false;
      bool writeOne(eSLIM3CirMan& circuit, unsigned requested, bool finished);
  };
}
ABC_NAMESPACE_CXX_HEADER_END
#endif
