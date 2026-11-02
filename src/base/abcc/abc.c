/**CFile****************************************************************

  FileName    [abc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Command integration and shared frame helpers.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "sat/cnf/cnf.h"
#include "base/sn/snGia.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////




////////////////////////////////////////////////////////////////////////
///                       FUNCTION DEFINITIONS                       ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameReplaceCex( Abc_Frame_t * pAbc, Abc_Cex_t ** ppCex )
{
    // update CEX
    ABC_FREE( pAbc->pCex );
    pAbc->pCex = *ppCex;
    *ppCex = NULL;
    // remove CEX vector
    if ( pAbc->vCexVec )
    {
        Vec_PtrFreeFree( pAbc->vCexVec );
        pAbc->vCexVec = NULL;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameReplaceCexVec( Abc_Frame_t * pAbc, Vec_Ptr_t ** pvCexVec )
{
    // update CEX vector
    if ( pAbc->vCexVec )
        Vec_PtrFreeFree( pAbc->vCexVec );
    pAbc->vCexVec = *pvCexVec;
    *pvCexVec = NULL;
    // remove CEX
    ABC_FREE( pAbc->pCex );
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameReplacePoEquivs( Abc_Frame_t * pAbc, Vec_Ptr_t ** pvPoEquivs )
{
    if ( pAbc->vPoEquivs )
        Vec_VecFree( (Vec_Vec_t *)pAbc->vPoEquivs );
    pAbc->vPoEquivs = *pvPoEquivs;
    *pvPoEquivs = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameReplacePoStatuses( Abc_Frame_t * pAbc, Vec_Int_t ** pvStatuses )
{
    if ( pAbc->vStatuses )
        Vec_IntFree( pAbc->vStatuses );
    pAbc->vStatuses = *pvStatuses;
    *pvStatuses = NULL;
}

/**Function*************************************************************

  Synopsis    [Derives array of statuses from the array of CEXes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_FrameDeriveStatusArray( Vec_Ptr_t * vCexes )
{
    Vec_Int_t * vStatuses;
    Abc_Cex_t * pCex;
    int i;
    if ( vCexes == NULL )
        return NULL;
    vStatuses = Vec_IntAlloc( Vec_PtrSize(vCexes) );
    Vec_IntFill( vStatuses, Vec_PtrSize(vCexes), -1 ); // assume UNDEC
    Vec_PtrForEachEntry( Abc_Cex_t *, vCexes, pCex, i )
        if ( pCex != NULL )
            Vec_IntWriteEntry( vStatuses, i, 0 ); // set this output as SAT
    return vStatuses;
}

/**Function*************************************************************

  Synopsis    [Derives output statuses and removes proved-output sentinels.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_FrameDeriveStatusArray2( Vec_Ptr_t * vCexes )
{
    Vec_Int_t * vStatuses;
    Abc_Cex_t * pCex;
    int i;
    if ( vCexes == NULL )
        return NULL;
    vStatuses = Vec_IntAlloc( Vec_PtrSize(vCexes) );
    Vec_IntFill( vStatuses, Vec_PtrSize(vCexes), -1 ); // assume UNDEC
    Vec_PtrForEachEntry( Abc_Cex_t *, vCexes, pCex, i )
        if ( pCex == (Abc_Cex_t *)(ABC_PTRINT_T)1 )
        {
            Vec_IntWriteEntry( vStatuses, i, 1 ); // set this output as UNSAT
            Vec_PtrWriteEntry( vCexes, i, NULL );
        }
        else if ( pCex != NULL )
            Vec_IntWriteEntry( vStatuses, i, 0 ); // set this output as SAT
    return vStatuses;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameClearDesign()
{
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameUpdateGia( Abc_Frame_t * pAbc, Gia_Man_t * pNew )
{
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_FrameUpdateGia(): Transformation has failed.\n" );
        return;
    }
    // A replacement GIA has no proven relationship to the saved positional cut interface.
    Sn_ForgetGiaDescriptor(pAbc);
    if ( Gia_ManPoNum(pNew) == 0 )
        Abc_Print( 0, "The current GIA has no primary outputs. Some commands may not work correctly.\n" );
    if ( pNew == pAbc->pGia )
        return;
    // transfer names
    if (!pNew->vNamesIn && pAbc->pGia && pAbc->pGia->vNamesIn && Gia_ManCiNum(pNew) == Vec_PtrSize(pAbc->pGia->vNamesIn))
    {
        pNew->vNamesIn = pAbc->pGia->vNamesIn;
        pAbc->pGia->vNamesIn = NULL;
    }
    if (!pNew->vNamesOut && pAbc->pGia && pAbc->pGia->vNamesOut && Gia_ManCoNum(pNew) == Vec_PtrSize(pAbc->pGia->vNamesOut))
    {
        pNew->vNamesOut = pAbc->pGia->vNamesOut;
        pAbc->pGia->vNamesOut = NULL;
    }
    if (!pNew->vNamesNode && pAbc->pGia && pAbc->pGia->vNamesNode && Gia_ManObjNum(pNew) == Vec_PtrSize(pAbc->pGia->vNamesNode))
    {
        pNew->vNamesNode = pAbc->pGia->vNamesNode;
        pAbc->pGia->vNamesNode = NULL;
    }
    // update
    if ( pAbc->pGia2 )
        Gia_ManStop( pAbc->pGia2 );
    pAbc->pGia2 = pAbc->pGia;
    pAbc->pGia  = pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abc_FrameGetGia( Abc_Frame_t * pAbc )
{
    Gia_Man_t * pGia;
    if ( pAbc->pGia2 )
        Gia_ManStop( pAbc->pGia2 );
    pAbc->pGia2 = NULL;
    pGia = pAbc->pGia;
    pAbc->pGia = NULL;
    Sn_ForgetGiaDescriptor(pAbc);
    return pGia;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_Init( Abc_Frame_t * pAbc )
{
    Abc_InitPrint( pAbc );
    Abc_InitIo( pAbc );
    Abc_InitNet( pAbc );
    Abc_InitLogic( pAbc );
    Abc_InitRewrite( pAbc );
    Abc_InitResub( pAbc );
    Abc_InitSweep( pAbc );
    Abc_InitMapLut( pAbc );
    Abc_InitMapCell( pAbc );
    Abc_InitSeq( pAbc );
    Abc_InitCec( pAbc );
    Abc_InitVerify( pAbc );
    Abc_InitAbstract( pAbc );
    Abc_InitSat( pAbc );
    Abc_InitExact( pAbc );
    Abc_InitArith( pAbc );
    Abc_InitSim( pAbc );
    Abc_InitGen( pAbc );

//#ifndef _WIN32
//#endif

    {
//        extern Mf_ManTruthCount();
//        Mf_ManTruthCount();
    }

    {
        extern void Dar_LibStart();
        Dar_LibStart();
    }
    {
//        extern void Dau_DsdTest();
//        Dau_DsdTest();
//        extern void If_ManSatTest();
//        If_ManSatTest();
    }

//    if ( Sdm_ManCanRead() )
//        Sdm_ManRead();
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_End( Abc_Frame_t * pAbc )
{
    extern Abc_Frame_t * Abc_FrameGetGlobalFrame();
    Nf2_ManClearCache();
    Nf2_LibClearCache();
    Abc_FrameClearDesign();
    Cnf_ManFree();
    {
        extern int Abc_NtkCompareAndSaveBest( Abc_Ntk_t * pNtk );
        Abc_NtkCompareAndSaveBest( NULL );
    }
    {
        extern void Dar_LibStop();
        Dar_LibStop();
    }
    {
        extern void Aig_RManQuit();
        Aig_RManQuit();
    }
    {
        extern void Npn_ManClean();
        Npn_ManClean();
    }
    {
        extern void Sdm_ManQuit();
        Sdm_ManQuit();
    }
    Abc_NtkFraigStoreClean();
    Gia_ManStopP( &pAbc->pGia );
    Gia_ManStopP( &pAbc->pGia2 );
    Gia_ManStopP( &pAbc->pGiaBest );
    Gia_ManStopP( &pAbc->pGiaBest2 );
    Gia_ManStopP( &pAbc->pGiaSaved );
    if ( Abc_NtkRecIsRunning3() )
        Abc_NtkRecStop3();
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
