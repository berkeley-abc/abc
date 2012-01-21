/**CFile****************************************************************

  FileName    [giaAbs.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbs.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__aig__gia__giaAbs_h
#define ABC__aig__gia__giaAbs_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////



ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// abstraction parameters
typedef struct Gia_ParAbs_t_ Gia_ParAbs_t;
struct Gia_ParAbs_t_
{
    int            Algo;         // the algorithm to be used
    int            nFramesMax;   // timeframes for PBA
    int            nConfMax;     // conflicts for PBA
    int            fDynamic;     // dynamic unfolding for PBA
    int            fConstr;      // use constraints
    int            nFramesBmc;   // timeframes for BMC
    int            nConfMaxBmc;  // conflicts for BMC
    int            nStableMax;   // the number of stable frames to quit
    int            nRatio;       // ratio of flops to quit
    int            TimeOut;      // approximate timeout in seconds
    int            TimeOutVT;    // approximate timeout in seconds
    int            nBobPar;      // Bob's parameter
    int            fUseBdds;     // use BDDs to refine abstraction
    int            fUseDprove;   // use 'dprove' to refine abstraction
    int            fUseStart;    // use starting frame
    int            fVerbose;     // verbose output
    int            fVeryVerbose; // printing additional information
    int            Status;       // the problem status
    int            nFramesDone;  // the number of frames covered
};

extern void Gia_ManAbsSetDefaultParams( Gia_ParAbs_t * p );

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

 


ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

