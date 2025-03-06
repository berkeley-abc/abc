#pragma once

#include <queue>
#include <random>

#ifdef ABC_USE_PTHREADS
#include <thread>
#include <mutex>
#include <condition_variable>
#endif

#include "rrrParameter.h"
#include "rrrUtils.h"
#include "rrrPartitioner.h"
#include "rrrAbc.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  template <typename Ntk, typename Opt>
  class Scheduler {
  private:
    // job
    struct Job;
    struct CompareJobPointers;
    
    // pointer to network
    Ntk *pNtk;

    // parameters
    int nVerbose;
    int iSeed;
    int nFlow;
    int nRestarts;
    bool fMultiThreading;
    bool fPartitioning;
    bool fDeterministic;
    seconds nTimeout;
    std::function<double(Ntk *)> CostFunction;
    
    // data
    int nJobs;
    int nFinishedJobs;
    time_point start;
    Partitioner<Ntk> par;
    std::queue<Job *> qPendingJobs;
    Opt *pOpt; // used only in case of single thread execution
#ifdef ABC_USE_PTHREADS
    bool fTerminate;
    std::vector<std::thread> vThreads;
    std::priority_queue<Job *, std::vector<Job *>, CompareJobPointers> qFinishedJobs;
    std::mutex mutexAbc;
    std::mutex mutexPendingJobs;
    std::mutex mutexFinishedJobs;
    std::condition_variable condPendingJobs;
    std::condition_variable condFinishedJobs;
#endif

    // time
    seconds GetRemainingTime() const;

    // abc
    void CallAbc(Ntk *pNtk_, std::string Command);

    // run jobs
    void RunJob(Opt &opt, Job const *pJob);

    // manage jobs
    void CreateJob(Ntk *pNtk_, int iSeed_);
    void OnJobEnd(std::function<void(Job *pJob)> const &func);

    // thread
#ifdef ABC_USE_PTHREADS
    void Thread(Parameter const *pPar);
#endif
    
  public:
    // constructors
    Scheduler(Ntk *pNtk, Parameter const *pPar);
    ~Scheduler();
    
    // run
    void Run();
  };

  /* {{{ Job */
  
  template <typename Ntk, typename Opt>
  struct Scheduler<Ntk, Opt>::Job {
    // data
    int id;
    Ntk *pNtk;
    int iSeed;
    
    // constructor
    Job(int id, Ntk *pNtk, int iSeed) :
      id(id),
      pNtk(pNtk),
      iSeed(iSeed) {
    }
  };

  template <typename Ntk, typename Opt>
  struct Scheduler<Ntk, Opt>::CompareJobPointers {
    // smaller id comes first in priority_queue
    bool operator()(Job const *lhs, Job const *rhs) const {
      return lhs->id > rhs->id;
    }
  };
  
  /* }}} */

  /* {{{ Time */

  template <typename Ntk, typename Opt>
  seconds Scheduler<Ntk, Opt>::GetRemainingTime() const {
    if(nTimeout == 0) {
      return 0;
    }
    time_point current = GetCurrentTime();
    seconds nRemainingTime = nTimeout - DurationInSeconds(start, current);
    if(nRemainingTime == 0) { // avoid glitch
      return -1;
    }
    return nRemainingTime;
  }

  /* }}} */

  /* {{{ Abc */

  template <typename Ntk, typename Opt>
  inline void Scheduler<Ntk, Opt>::CallAbc(Ntk *pNtk_, std::string Command) {
#ifdef ABC_USE_PTHREADS
    if(fMultiThreading) {
      {
        std::unique_lock<std::mutex> l(mutexAbc);
        Abc9Execute(pNtk_, Command);
      }
      return;
    }
#endif
    Abc9Execute(pNtk_, Command);
  }

  /* }}} */
  
  /* {{{ Run jobs */

  template <typename Ntk, typename Opt>
  void Scheduler<Ntk, Opt>::RunJob(Opt &opt, Job const *pJob) {
    opt.UpdateNetwork(pJob->pNtk);
    // start flow
    switch(nFlow) {
    case 0:
      opt.ResetSeed(pJob->iSeed);
      opt.Run(GetRemainingTime());
      break;
    case 1: { // transtoch
      std::mt19937 rng(pJob->iSeed);
      double dCost = CostFunction(pJob->pNtk);
      double dBestCost = dCost;
      Ntk best(*(pJob->pNtk));
      if(nVerbose) {
        std::cout << "start: cost = " << dCost << std::endl;
      }
      for(int i = 0; i < 10; i++) {
        if(GetRemainingTime() < 0) {
          break;
        }
        if(i != 0) {
          CallAbc(pJob->pNtk, "&if -K 6; &mfs; &st");
          dCost = CostFunction(pJob->pNtk);
          opt.UpdateNetwork(pJob->pNtk, true);
          if(nVerbose) {
            std::cout << "hop " << std::setw(3) << i << ": cost = " << dCost << std::endl;
          }
        }
        for(int j = 0; true; j++) {
          if(GetRemainingTime() < 0) {
            break;
          }
          opt.Randomize(rng());
          opt.Run(GetRemainingTime());
          CallAbc(pJob->pNtk, "&dc2");
          double dNewCost = CostFunction(pJob->pNtk);
          if(nVerbose) {
            std::cout << "\tite " << std::setw(3) << j << ": cost = " << dNewCost << std::endl;
          }
          if(dNewCost < dCost) {
            dCost = dNewCost;
            opt.UpdateNetwork(pJob->pNtk, true);
          } else {
            break;
          }
        }
        if(dCost < dBestCost) {
          dBestCost = dCost;
          best = *(pJob->pNtk);
          i = 0;
        }
      }
      *(pJob->pNtk) = best;
      if(nVerbose) {
        std::cout << "end: cost = " << dBestCost << std::endl;
      }
      break;
    }
    case 2: { // deep
      std::mt19937 rng(pJob->iSeed);
      int n = 0;
      double dCost = CostFunction(pJob->pNtk);
      Ntk best(*(pJob->pNtk));
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
        CallAbc(pJob->pNtk, Command);
        if(nVerbose) {
          std::cout << "ite " << std::setw(6) << i << ": cost = " << CostFunction(pJob->pNtk) << std::endl;
        }
        // rrr
        for(int j = 0; j < n; j++) {
          if(GetRemainingTime() < 0) {
            break;
          }
          opt.UpdateNetwork(pJob->pNtk, true);
          opt.Randomize(rng());
          opt.Run(GetRemainingTime());
          if(rng() & 1) {
            CallAbc(pJob->pNtk, "&dc2");
          } else {
            CallAbc(pJob->pNtk, "&put; " + pCompress2rs + "; &get");
          }
          if(nVerbose) {
            std::cout << "\trrr " << std::setw(6) << j << ": cost = " << CostFunction(pJob->pNtk) << std::endl;
          }
        }
        // eval
        double dNewCost = CostFunction(pJob->pNtk);
        if(dNewCost < dCost) {
          dCost = dNewCost;
          best = *(pJob->pNtk);
        } else {
          n++;
        }
      }
      *(pJob->pNtk) = best;
      if(nVerbose) {
        std::cout << "end: cost = " << dCost << std::endl;
      }
      break;
    }
    default:
      assert(0);
    }
  }

  /* }}} */

  /* {{{ Manage jobs */

  template <typename Ntk, typename Opt>
  void Scheduler<Ntk, Opt>::CreateJob(Ntk *pNtk_, int iSeed_) {
    Job *pJob = new Job(nJobs++, pNtk_, iSeed_);
#ifdef ABC_USE_PTHREADS
    if(fMultiThreading) {
      {
        std::unique_lock<std::mutex> l(mutexPendingJobs);
        qPendingJobs.push(pJob);
        condPendingJobs.notify_one();
      }
      return;
    }
#endif
    qPendingJobs.push(pJob);
  }
  
  template <typename Ntk, typename Opt>
  void Scheduler<Ntk, Opt>::OnJobEnd(std::function<void(Job *pJob)> const &func) {
#ifdef ABC_USE_PTHREADS
    if(fMultiThreading) {
      Job *pJob = NULL;
      {
        std::unique_lock<std::mutex> l(mutexFinishedJobs);
        while(qFinishedJobs.empty() || (fDeterministic && qFinishedJobs.top()->id != nFinishedJobs)) {
          condFinishedJobs.wait(l);
        }
        pJob = qFinishedJobs.top();
        qFinishedJobs.pop();
      }
      assert(pJob != NULL);
      func(pJob);
      delete pJob;
      nFinishedJobs++;
      return;
    }
#endif
    // if single thread
    assert(!qPendingJobs.empty());
    Job *pJob = qPendingJobs.front();
    qPendingJobs.pop();
    RunJob(*pOpt, pJob);
    func(pJob);
    delete pJob;
    nFinishedJobs++;
  }
  
  /* }}} */

  /* {{{ Thread */

#ifdef ABC_USE_PTHREADS
  template <typename Ntk, typename Opt>
  void Scheduler<Ntk, Opt>::Thread(Parameter const *pPar) {
    Opt opt(pPar, CostFunction);
    while(true) {
      Job *pJob = NULL;
      {
        std::unique_lock<std::mutex> l(mutexPendingJobs);
        while(!fTerminate && qPendingJobs.empty()) {
          condPendingJobs.wait(l);
        }
        if(fTerminate) {
          assert(qPendingJobs.empty());
          return;
        }
        pJob = qPendingJobs.front();
        qPendingJobs.pop();
      }
      assert(pJob != NULL);
      RunJob(opt, pJob);
      {
        std::unique_lock<std::mutex> l(mutexFinishedJobs);
        qFinishedJobs.push(pJob);
        condFinishedJobs.notify_one();
      }
    }
  }
#endif

  /* }}} */
  
  /* {{{ Constructors */
  
  template <typename Ntk, typename Opt>
  Scheduler<Ntk, Opt>::Scheduler(Ntk *pNtk, Parameter const *pPar) :
    pNtk(pNtk),
    nVerbose(pPar->nSchedulerVerbose),
    iSeed(pPar->iSeed),
    nFlow(pPar->nSchedulerFlow),
    nRestarts(pPar->nRestarts),
    fMultiThreading(pPar->nThreads > 1),
    fPartitioning(pPar->nWindowSize > 0),
    fDeterministic(pPar->fDeterministic),
    nTimeout(pPar->nTimeout),
    nJobs(0),
    nFinishedJobs(0),
    par(pPar),
    pOpt(NULL) {
    // prepare cost function
    CostFunction = [](Ntk *pNtk) {
      int nTwoInputSize = 0;
      pNtk->ForEachInt([&](int id) {
        nTwoInputSize += pNtk->GetNumFanins(id) - 1;
      });
      return nTwoInputSize;
    };
#ifdef ABC_USE_PTHREADS
    fTerminate = false;
    if(fMultiThreading) {
      vThreads.reserve(pPar->nThreads);
      for(int i = 0; i < pPar->nThreads; i++) {
        vThreads.emplace_back(std::bind(&Scheduler::Thread, this, pPar));
      }
      return;
    }
#endif
    assert(!fMultiThreading);
    pOpt = new Opt(pPar, CostFunction);
  }

  template <typename Ntk, typename Opt>
  Scheduler<Ntk, Opt>::~Scheduler() {
#ifdef ABC_USE_PTHREADS
    if(fMultiThreading) {
      {
        std::unique_lock<std::mutex> l(mutexPendingJobs);
        fTerminate = true;
        condPendingJobs.notify_all();
      }
      for(std::thread &t: vThreads) {
        t.join();
      }
      return;
    }
#endif
    delete pOpt;
  }

  /* }}} */

  /* {{{ Run */
  
  template <typename Ntk, typename Opt>
  void Scheduler<Ntk, Opt>::Run() {
    start = GetCurrentTime();
    if(fPartitioning) {
      pNtk->Sweep();
      par.UpdateNetwork(pNtk);
      while(nJobs < nRestarts) {
        Ntk *pSubNtk = par.Extract(iSeed + nJobs);
        if(pSubNtk == NULL) {
          if(nJobs == nFinishedJobs) {
            std::cout << "failed to extract a window" << std::endl;
            break;
          }
          while(nFinishedJobs < nJobs) {
            OnJobEnd([&](Job *pJob) {
              std::cout << "job " << pJob->id << " finished (size = " << pJob->pNtk->GetNumInts() << ")" << std::endl;
              par.Insert(pJob->pNtk);
            });
          }
        } else {
          CreateJob(pSubNtk, iSeed + nJobs);
          std::cout << "job " << nJobs - 1 << " created (size = " << pSubNtk->GetNumInts() << ")" << std::endl;
        }
      }
      while(nFinishedJobs < nJobs) {
        OnJobEnd([&](Job *pJob) {
          std::cout << "job " << pJob->id << " finished (size = " << pJob->pNtk->GetNumInts() << ")" << std::endl;
          par.Insert(pJob->pNtk);
        });
      }
    } else if(nRestarts > 0) {
      fDeterministic = false; // it is deterministic anyways
      double dCost = CostFunction(pNtk);
      for(int i = 0; i < 1 + nRestarts; i++) {
        Ntk *pCopy = new Ntk(*pNtk);
        CreateJob(pCopy, iSeed + i);
      }
      for(int i = 0; i < 1 + nRestarts; i++) {
        OnJobEnd([&](Job *pJob) {
          double dNewCost = CostFunction(pJob->pNtk);
          if(nVerbose) {
            std::cout << "run " << pJob->id << ": cost = " << dNewCost << std::endl;
          }
          if(dNewCost < dCost) {
            dCost = dNewCost;
            *pNtk = *(pJob->pNtk);
          }
          delete pJob->pNtk;
        });
      }
    } else {
      CreateJob(pNtk, iSeed);
      OnJobEnd([&](Job *pJob) { (void)pJob; });
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
