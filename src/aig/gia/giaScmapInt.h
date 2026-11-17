/**CFile****************************************************************

  FileName    [giaScmapInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Electrical model interface for shared-cell window search.]

***********************************************************************/

#ifndef ABC__aig__gia__giaScmapInt_h
#define ABC__aig__gia__giaScmapInt_h

#include "gia.h"

ABC_NAMESPACE_HEADER_START

typedef struct Scm_RfPair_t_ { float Value[2]; } Scm_RfPair_t;
typedef struct Scm_Qor_t_ { double Area; float Delay; int fValid; } Scm_Qor_t;

// Prefer feasible covers, then area; before feasibility, prefer delay.
static inline int Scm_QorTargetBetter( double Area, float Delay, double OldArea, float OldDelay, float Target )
{
    if ( (Delay <= Target) != (OldDelay <= Target) ) return Delay <= Target;
    if ( Delay > Target ) return Delay < OldDelay || (Delay == OldDelay && Area < OldArea);
    return Area < OldArea || (Area == OldArea && Delay < OldDelay);
}
extern void * Scm_WinModelStart( void );
extern void Scm_WinModelStop( void * pModel );
extern Scm_RfPair_t Scm_WinModelCap( void * pModel, int Gate, int Pin );
extern double Scm_WinModelCost( void * pModel, int Gate, float Load );
extern int Scm_WinModelCell( void * pModel, int Gate, Scm_RfPair_t Load,
    Scm_RfPair_t * pArrivals, Scm_RfPair_t * pSlews, Scm_RfPair_t * pArrival, Scm_RfPair_t * pSlew );
extern int Scm_WinModelRequired( void * pModel, int Gate, int Pin, Scm_RfPair_t Load,
    Scm_RfPair_t Slew, Scm_RfPair_t Required, Scm_RfPair_t * pRequired );
extern Gia_Man_t * Scm_ManWindowImprove( Gia_Man_t * pGia, Scm_Qor_t * pQor, int fVerbose, int fVeryVerbose );
extern Gia_Man_t * Scm_ManWindowLookahead( Gia_Man_t * pGia, Scm_Qor_t * pQor, int nTrials, int fVerbose, int fVeryVerbose );
extern Gia_Man_t * Scm_ManWindowTarget( Gia_Man_t * pGia, Scm_Qor_t * pQor, float DelayTarget, int nTrials, int fVerbose, int fVeryVerbose );
extern int Scm_WinModelLookahead( Gia_Man_t * pGia, double * pArea, float * pDelay );

ABC_NAMESPACE_HEADER_END

#endif
