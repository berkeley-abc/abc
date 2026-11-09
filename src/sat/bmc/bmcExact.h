/**CFile****************************************************************

  FileName    [bmcExact.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Shared input, output, and minimum-search handling.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 8, 2026.]

***********************************************************************/

#ifndef ABC__sat__bmc__bmcExact_h
#define ABC__sat__bmc__bmcExact_h

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "aig/gia/gia.h"

ABC_NAMESPACE_HEADER_START

typedef struct Bmc_Exact_t_ Bmc_Exact_t;
struct Bmc_Exact_t_
{
    word * pTruth;           // owned, unmodified specification in original PI order
    Abc_Ntk_t * pNtk;        // borrowed source network, only for interface names
    int nVars;
};

extern int Bmc_ExactRead( Abc_Frame_t * pAbc, const char * pHex, int nInputs, int nMaxInputs, Bmc_Exact_t * p );
extern int Bmc_ExactInstall( Abc_Frame_t * pAbc, Gia_Man_t * pGia, Bmc_Exact_t * p );
extern int Bmc_ExactLut( Gia_Man_t * pGia, const word * pTruth, const int * pFans, int nFans, int Offset );
extern int Bmc_ExactContinue( int Status, int fMinimum, int nSeconds, int Count, int * pFirstUnknown );
extern void Bmc_ExactReport( int Status, int FirstUnknown, int Count, int Limit, const char * pUnit, const char * pScope );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
