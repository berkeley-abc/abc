/**CFile****************************************************************

  FileName    [sfmLib.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Preprocessing genlib library.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmLib.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_DecCreateCnf( Vec_Int_t * vGateSizes, Vec_Wrd_t * vGateFuncs, Vec_Wec_t * vGateCnfs )
{
    Vec_Str_t * vCnf, * vCnfBase;
    Vec_Int_t * vCover;
    word uTruth;
    int i, nCubes;
    vCnf = Vec_StrAlloc( 100 );
    vCover = Vec_IntAlloc( 100 );
    Vec_WrdForEachEntry( vGateFuncs, uTruth, i )
    {
        nCubes = Sfm_TruthToCnf( uTruth, Vec_IntEntry(vGateSizes, i), vCover, vCnf );
        vCnfBase = (Vec_Str_t *)Vec_WecEntry( vGateCnfs, i );
        Vec_StrGrow( vCnfBase, Vec_StrSize(vCnf) );
        memcpy( Vec_StrArray(vCnfBase), Vec_StrArray(vCnf), Vec_StrSize(vCnf) );
        vCnfBase->nSize = Vec_StrSize(vCnf);
    }
    Vec_IntFree( vCover );
    Vec_StrFree( vCnf );
}

/**Function*************************************************************

  Synopsis    [Preprocess the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_LibPreprocess( Mio_Library_t * pLib, Vec_Int_t * vGateSizes, Vec_Wrd_t * vGateFuncs, Vec_Wec_t * vGateCnfs, Vec_Ptr_t * vGateHands )
{
    Mio_Gate_t * pGate;
    int nGates = Mio_LibraryReadGateNum(pLib);
    Vec_IntGrow( vGateSizes, nGates );
    Vec_WrdGrow( vGateFuncs, nGates );
    Vec_WecInit( vGateCnfs,  nGates );
    Vec_PtrGrow( vGateHands, nGates );
    Mio_LibraryForEachGate( pLib, pGate )
    {
        Vec_IntPush( vGateSizes, Mio_GateReadPinNum(pGate) );
        Vec_WrdPush( vGateFuncs, Mio_GateReadTruth(pGate) );
        Mio_GateSetValue( pGate, Vec_PtrSize(vGateHands) );
        Vec_PtrPush( vGateHands, pGate );
    }
    Sfm_DecCreateCnf( vGateSizes, vGateFuncs, vGateCnfs );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

