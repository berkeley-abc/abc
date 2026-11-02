/**CFile****************************************************************

  FileName    [abcc.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Private declarations for ABC command integration.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#ifndef ABC__base__abcc__abcc_h
#define ABC__base__abcc__abcc_h

#include "base/main/main.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                      FUNCTION DECLARATIONS                       ///
////////////////////////////////////////////////////////////////////////

extern Vec_Int_t * Abc_FrameDeriveStatusArray( Vec_Ptr_t * vCexes );
extern Vec_Int_t * Abc_FrameDeriveStatusArray2( Vec_Ptr_t * vCexes );

extern void Abc_InitPrint( Abc_Frame_t * pAbc );
extern void Abc_InitIo( Abc_Frame_t * pAbc );
extern void Abc_InitNet( Abc_Frame_t * pAbc );
extern void Abc_InitLogic( Abc_Frame_t * pAbc );
extern void Abc_InitRewrite( Abc_Frame_t * pAbc );
extern void Abc_InitResub( Abc_Frame_t * pAbc );
extern void Abc_InitSweep( Abc_Frame_t * pAbc );
extern void Abc_InitMapLut( Abc_Frame_t * pAbc );
extern void Abc_InitMapCell( Abc_Frame_t * pAbc );
extern void Abc_InitSeq( Abc_Frame_t * pAbc );
extern void Abc_InitCec( Abc_Frame_t * pAbc );
extern void Abc_InitVerify( Abc_Frame_t * pAbc );
extern void Abc_InitAbstract( Abc_Frame_t * pAbc );
extern void Abc_InitSat( Abc_Frame_t * pAbc );
extern void Abc_InitExact( Abc_Frame_t * pAbc );
extern void Abc_InitArith( Abc_Frame_t * pAbc );
extern void Abc_InitSim( Abc_Frame_t * pAbc );
extern void Abc_InitGen( Abc_Frame_t * pAbc );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
