#pragma once

#include <iostream>
#include <iomanip>
#include <random>

#include "rrrParameter.h"
#include "rrrTypes.h"

#include "rrrAbc.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  template <typename Ntk, typename Opt>
  class Scheduler {
  private:
    // pointer to network
    Ntk *pNtk;

    // parameters
    int nVerbose;
    int nFlow;

    // copy of parameter (maybe updated during the run)
    Parameter Par;

    // data
    time_point start;

    // time
    seconds GetRemainingTime();

  public:
    // constructor
    Scheduler(Ntk *pNtk, Parameter const *pPar);

    // run
    void Run();
  };

  /* {{{ time */

  template <typename Ntk, typename Opt>
  seconds Scheduler<Ntk, Opt>::GetRemainingTime() {
    if(Par.nTimeout == 0) {
      return 0;
    }
    time_point current = GetCurrentTime();
    seconds nTimeout = Par.nTimeout - DurationInSeconds(start, current);
    if(nTimeout == 0) { // avoid glitch
      return -1;
    }
    return nTimeout;
  }

  /* }}} */

  /* {{{ Constructor */
  
  template <typename Ntk, typename Opt>
  Scheduler<Ntk, Opt>::Scheduler(Ntk *pNtk, Parameter const *pPar) :
    pNtk(pNtk),
    nVerbose(pPar->nSchedulerVerbose),
    nFlow(pPar->nSchedulerFlow),
    Par(*pPar) {
    // TODO: allocations and other preparations should be done here
  }

  /* }}} */

  /* {{{ Run */
  
  // TODO: have multiplie optimizers running on different windows/partitions
  // TODO: run ABC on those windows or even on the entire network, maybe as a separate class
  
  template <typename Ntk, typename Opt>
  void Scheduler<Ntk, Opt>::Run() {
    start = GetCurrentTime();
    // prepare cost function
    std::function<double(Ntk *)> CostFunction;
    CostFunction = [](Ntk *pNtk) {
      int nTwoInputSize = 0;
      pNtk->ForEachInt([&](int id) {
        nTwoInputSize += pNtk->GetNumFanins(id) - 1;
      });
      return nTwoInputSize;
    };
    // start flow
    Opt opt(pNtk, &Par, CostFunction);
    switch(nFlow) {
    case 0:
      opt.Run(GetRemainingTime());
      break;
    case 1: { // transtoch
      double dCost = CostFunction(pNtk);
      double dBestCost = dCost;
      Ntk best(*pNtk);
      if(nVerbose) {
        std::cout << "start: cost = " << dCost << std::endl;
      }
      for(int i = 0; i < 10; i++) {
        if(GetRemainingTime() < 0) {
          break;
        }
        if(i != 0) {
          Abc9Execute(pNtk, "&if -K 6; &mfs; &st");
          dCost = CostFunction(pNtk);
          opt.UpdateNetwork(pNtk, true);
          if(nVerbose) {
            std::cout << "hop " << std::setw(3) << i << ": cost = " << dCost << std::endl;
          }
        }
        for(int j = 0; true; j++) {
          if(GetRemainingTime() < 0) {
            break;
          }
          opt.Randomize();
          opt.Run(GetRemainingTime());
          Abc9Execute(pNtk, "&dc2");
          double dNewCost = CostFunction(pNtk);
          if(nVerbose) {
            std::cout << "\tite " << std::setw(3) << j << ": cost = " << dNewCost << std::endl;
          }
          if(dNewCost < dCost) {
            dCost = dNewCost;
            opt.UpdateNetwork(pNtk, true);
          } else {
            break;
          }
        }
        if(dCost < dBestCost) {
          dBestCost = dCost;
          best = *pNtk;
          i = 0;
        }
      }
      *pNtk = best;
      if(nVerbose) {
        std::cout << "end: cost = " << dBestCost << std::endl;
      }
      break;
    }
    case 2: { // deep
      double dCost = CostFunction(pNtk);
      Ntk best(*pNtk);
      int n = 0;
      std::mt19937 rng(Par.iSeed);
      if(nVerbose) {
        std::cout << "start: cost = " << dCost << std::endl;
      }
      for(int i = 0; i < 1000000; i++) {
        if(GetRemainingTime() < 0) {
          break;
        }
        // deepsyn
        int fUseTwo = 0;
        std::string pCompress2rs = "balance -l; resub -K 6 -l; rewrite -l; resub -K 6 -N 2 -l; refactor -l; resub -K 8 -l; balance -l; resub -K 8 -N 2 -l; rewrite -l; resub -K 10 -l; rewrite -z -l; resub -K 10 -N 2 -l; balance -l; resub -K 12 -l; refactor -z -l; resub -K 12 -N 2 -l; rewrite -z -l; balance -l";
        unsigned Rand = rng();
        int fDch = Rand & 1;
        //int fCom = (Rand >> 1) & 3;
        int fCom = (Rand >> 1) & 1;
        int fFx  = (Rand >> 2) & 1;
        int KLut = fUseTwo ? 2 + (i % 5) : 3 + (i % 4);
        std::string pComp;
        if ( fCom == 3 )
          pComp = "; &put; " + pCompress2rs + "; " + pCompress2rs + "; " + pCompress2rs + "; &get";
        else if ( fCom == 2 )
          pComp = "; &put; " + pCompress2rs + "; " + pCompress2rs + "; &get";
        else if ( fCom == 1 )
          pComp = "; &put; " + pCompress2rs + "; &get";
        else if ( fCom == 0 )
          pComp = "; &dc2";
        std::string Command = "&dch";
        if(fDch)
          Command += " -f";
        Command += "; &if -a -K " + std::to_string(KLut) + "; &mfs -e -W 20 -L 20";
        if(fFx)
          Command += "; &fx; &st";
        Command += pComp;
        Abc9Execute(pNtk, Command);
        if(nVerbose) {
          std::cout << "ite " << std::setw(6) << i << ": cost = " << CostFunction(pNtk) << std::endl;
        }
        // rrr
        for(int j = 0; j < n; j++) {
          if(GetRemainingTime() < 0) {
            break;
          }
          opt.Randomize();
          opt.UpdateNetwork(pNtk, true);
          opt.Run(GetRemainingTime());
          if(rng() & 1) {
            Abc9Execute(pNtk, "&dc2");
          } else {
            Abc9Execute(pNtk, "&put; " + pCompress2rs + "; &get");
          }
          if(nVerbose) {
            std::cout << "\trrr " << std::setw(6) << j << ": cost = " << CostFunction(pNtk) << std::endl;
          }
        }
        // eval
        double dNewCost = CostFunction(pNtk);
        if(dNewCost < dCost) {
          dCost = dNewCost;
          best = *pNtk;
        } else {
          n++;
        }
      }
      *pNtk = best;
      if(nVerbose) {
        std::cout << "end: cost = " << dCost << std::endl;
      }
      break;
    }
    default:
      assert(0);
    }
    time_point end = GetCurrentTime();
    double elapsed_seconds = Duration(start, end);
    if(nVerbose) {
      std::cout << "elapsed: " << std::fixed << std::setprecision(3) << elapsed_seconds << "s" << std::endl;
    }
  }

  /* }}} */

}

ABC_NAMESPACE_CXX_HEADER_END
