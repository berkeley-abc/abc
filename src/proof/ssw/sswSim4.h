/**CFile****************************************************************

  FileName    [sswSim4.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential simulation.]

  Synopsis    [Rarity-guided simulation with seeded bounded model checking.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 11, 2026.]

  Revision    [$Id: sswSim4.h,v 1.00 2026/11/11 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__proof__ssw__sswSim4_h
#define ABC__proof__ssw__sswSim4_h

#include "aig/gia/gia.h"

ABC_NAMESPACE_HEADER_START

typedef struct Ssw_ParSim4_t_ Ssw_ParSim4_t;
struct Ssw_ParSim4_t_
{
    int nTimeOut;              // total wall-clock seconds
    int nWords;                // maximum 64-bit simulation words
    int nFrames;               // simulation frames per iteration
    int nBmcFrames;            // bounded search depth (0 disables BMC)
    int nBmcTime;              // maximum milliseconds per bounded search
    int nMemoryLimit;          // estimated memory budget in MiB
    int nSeed;                 // per-instance random seed
    int nRoundsMax;            // iteration limit (0 uses the time limit)
    int fUseGlucose;           // use the &bmcs -g backend
    int fLighthouses;          // target gates, rare states, and simulated relations
    int fPatterns;             // replay symbolic input patterns in simulation
    int fVerbose;
    int fSilent;
    abctime TimeToStop;
    int (*pFuncStop)(void *);
    void * pStopData;
    int nWordsUsed;
    int nRounds;
    int nBmcCalls;
    int nBmcHits;
    int nRestarts;
    int nFramesDone;
    int nStatesSaved;
    int fMemoryLimit;
    int iFrame;
    abctime timeSimulation;
    abctime timeBmc;
    abctime timeReplay;
};

extern void Ssw_Sim4SetDefaultParams( Ssw_ParSim4_t * pPars );
extern int Ssw_Sim4Perform( Gia_Man_t * pGia, Ssw_ParSim4_t * pPars );

ABC_NAMESPACE_HEADER_END

#endif
