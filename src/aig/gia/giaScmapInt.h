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

typedef struct Scm_WinPair_t_ { float Value[2]; } Scm_WinPair_t;
extern void * Scm_WinModelStart( void );
extern void Scm_WinModelStop( void * pModel );
extern float Scm_WinModelCap( void * pModel, int Gate, int Pin );
extern double Scm_WinModelCost( void * pModel, int Gate, float Load );
extern int Scm_WinModelCell( void * pModel, int Gate, float Load,
    Scm_WinPair_t * pArrivals, Scm_WinPair_t * pSlews, Scm_WinPair_t * pArrival, Scm_WinPair_t * pSlew );
extern Gia_Man_t * Scm_ManWindowImprove( Gia_Man_t * pGia, int fVerbose, int fVeryVerbose );

ABC_NAMESPACE_HEADER_END

#endif
