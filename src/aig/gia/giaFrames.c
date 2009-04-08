/**CFile****************************************************************

  FileName    [giaFrames.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Timeframe unrolling.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaFrames.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Gia_ManFra_t_ Gia_ManFra_t;
struct Gia_ManFra_t_
{
    Gia_ParFra_t *  pPars;  // parameters
    Gia_Man_t *     pAig;   // AIG to unroll
    Vec_Ptr_t *     vIns;   // inputs of each timeframe    
    Vec_Ptr_t *     vAnds;  // nodes of each timeframe    
    Vec_Ptr_t *     vOuts;  // outputs of each timeframe    
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFraSetDefaultParams( Gia_ParFra_t * p )
{
    memset( p, 0, sizeof(Gia_ParFra_t) );
    p->nFrames      =  32;    // the number of frames to unroll
    p->fInit        =   0;    // initialize the timeframes
    p->fVerbose     =   0;    // enables verbose output
}

/**Function*************************************************************

  Synopsis    [Creates manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_ManFra_t * Gia_ManFraStart( Gia_Man_t * pAig, Gia_ParFra_t * pPars )  
{ 
    Gia_ManFra_t * p;
    p = ABC_ALLOC( Gia_ManFra_t, 1 );
    memset( p, 0, sizeof(Gia_ManFra_t) );
    p->pAig  = pAig;
    p->pPars = pPars;
    return p;
}

/**Function*************************************************************

  Synopsis    [Deletes manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFraStop( Gia_ManFra_t * p )  
{
    Vec_VecFree( (Vec_Vec_t *)p->vIns );
    Vec_VecFree( (Vec_Vec_t *)p->vAnds );
    Vec_VecFree( (Vec_Vec_t *)p->vOuts );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Computes supports of all timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFraSupports( Gia_ManFra_t * p )
{
    Vec_Int_t * vIns = NULL, * vAnds, * vOuts;
    Gia_Obj_t * pObj;
    int f, i;
    p->vIns  = Vec_PtrStart( p->pPars->nFrames );
    p->vAnds = Vec_PtrStart( p->pPars->nFrames );
    p->vOuts = Vec_PtrStart( p->pPars->nFrames );
    Gia_ManResetTravId( p->pAig );
    for ( f = p->pPars->nFrames - 1; f >= 0; f-- )
    {
        vOuts = Gia_ManCollectPoIds( p->pAig );
        if ( vIns )
        Gia_ManForEachObjVec( vIns, p->pAig, pObj, i )
            if ( Gia_ObjIsRo(p->pAig, pObj) )
                Vec_IntPush( vOuts, Gia_ObjId( p->pAig, Gia_ObjRoToRi(p->pAig, pObj) ) );
        vIns = Vec_IntAlloc( 100 );
        Gia_ManCollectCis( p->pAig, Vec_IntArray(vOuts), Vec_IntSize(vOuts), vIns );
        vAnds = Vec_IntAlloc( 100 );
        Gia_ManCollectAnds( p->pAig, Vec_IntArray(vOuts), Vec_IntSize(vOuts), vAnds );
        Vec_PtrWriteEntry( p->vIns,  f, vIns );
        Vec_PtrWriteEntry( p->vAnds, f, vAnds );
        Vec_PtrWriteEntry( p->vOuts, f, vOuts );
    }
}

/**Function*************************************************************

  Synopsis    [Moves the first nRegs entries to the end.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFraTransformCis( Gia_Man_t * pAig, Vec_Int_t * vCis )
{
    int i, k = 0, Entry;
    Vec_IntForEachEntryStop( vCis, Entry, i, Gia_ManRegNum(pAig) )
        assert( Entry == i+1 );
    Vec_IntForEachEntryStart( vCis, Entry, i, Gia_ManRegNum(pAig) )
        Vec_IntWriteEntry( vCis, k++, Entry );
    for ( i = 0; i < Gia_ManRegNum(pAig); i++ )
        Vec_IntWriteEntry( vCis, k++, i+1 );
    assert( k == Vec_IntSize(vCis) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFramesInit( Gia_Man_t * pAig, Gia_ParFra_t * pPars )
{
    int fUseAllPis = 1;
    Gia_Man_t * pFrames, * pTemp;
    Gia_ManFra_t * p;
    Gia_Obj_t * pObj;
    Vec_Int_t * vIns, * vAnds, * vOuts;
    int i, f;
    p = Gia_ManFraStart( pAig, pPars );
    Gia_ManFraSupports( p );
    pFrames = Gia_ManStart( Vec_VecSizeSize((Vec_Vec_t*)p->vIns)+
        Vec_VecSizeSize((Vec_Vec_t*)p->vAnds)+Vec_VecSizeSize((Vec_Vec_t*)p->vOuts) );
    pFrames->pName = Gia_UtilStrsav( pAig->pName );
    Gia_ManHashAlloc( pFrames );
    Gia_ManConst0(pAig)->Value = 0;
    for ( f = 0; f < pPars->nFrames; f++ )
    {
        vIns  = Vec_PtrEntry( p->vIns,  f );
        vAnds = Vec_PtrEntry( p->vAnds, f );
        vOuts = Vec_PtrEntry( p->vOuts, f );
        if ( pPars->fVerbose )
            printf( "Frame %3d : CI = %6d. AND = %6d. CO = %6d.\n", 
            f, Vec_IntSize(vIns), Vec_IntSize(vAnds), Vec_IntSize(vOuts) );
        if ( fUseAllPis )
        {
            Gia_ManForEachPi( pAig, pObj, i )
                pObj->Value = Gia_ManAppendCi( pFrames );
            if ( f == 0 )
            {
                Gia_ManForEachObjVec( vIns, pAig, pObj, i )
                {
                    assert( Gia_ObjIsCi(pObj) );
                    if ( !Gia_ObjIsPi(pAig, pObj) )
                        pObj->Value = 0;
                }
            }
            else
            {
                Gia_ManForEachObjVec( vIns, pAig, pObj, i )
                {
                    assert( Gia_ObjIsCi(pObj) );
                    if ( !Gia_ObjIsPi(pAig, pObj) )
                        pObj->Value = Gia_ObjRoToRi(pAig, pObj)->Value;
                }
            }
        }
        else
        {
            if ( f == 0 )
            {
                Gia_ManForEachObjVec( vIns, pAig, pObj, i )
                {
                    assert( Gia_ObjIsCi(pObj) );
                    if ( Gia_ObjIsPi(pAig, pObj) )
                        pObj->Value = Gia_ManAppendCi( pFrames );
                    else
                        pObj->Value = 0;
                }
            }
            else
            {
                Gia_ManForEachObjVec( vIns, pAig, pObj, i )
                {
                    assert( Gia_ObjIsCi(pObj) );
                    if ( Gia_ObjIsPi(pAig, pObj) )
                        pObj->Value = Gia_ManAppendCi( pFrames );
                    else
                        pObj->Value = Gia_ObjRoToRi(pAig, pObj)->Value;
                }
            }
        }
        Gia_ManForEachObjVec( vAnds, pAig, pObj, i )
        {
            assert( Gia_ObjIsAnd(pObj) );
            pObj->Value = Gia_ManHashAnd( pFrames, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        }
        Gia_ManForEachObjVec( vOuts, pAig, pObj, i )
        {
            assert( Gia_ObjIsCo(pObj) );
            if ( Gia_ObjIsPo(pAig, pObj) )
                pObj->Value = Gia_ManAppendCo( pFrames, Gia_ObjFanin0Copy(pObj) );
            else
                pObj->Value = Gia_ObjFanin0Copy(pObj);
        }
    }
    Gia_ManFraStop( p );
    Gia_ManHashStop( pFrames );
    if ( Gia_ManCombMarkUsed(pFrames) < Gia_ManAndNum(pFrames) )
    {
        pFrames = Gia_ManDupMarked( pTemp = pFrames );
        if ( pPars->fVerbose )
            printf( "Before cleanup = %d nodes. After cleanup = %d nodes.\n", 
                Gia_ManAndNum(pTemp), Gia_ManAndNum(pFrames) );
        Gia_ManStop( pTemp );
    }
    else if ( pPars->fVerbose )
            printf( "Before cleanup = %d nodes. After cleanup = %d nodes.\n", 
                Gia_ManAndNum(pFrames), Gia_ManAndNum(pFrames) );
    return pFrames;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFrames( Gia_Man_t * pAig, Gia_ParFra_t * pPars )
{
    Gia_Man_t * pFrames, * pTemp;
    Gia_Obj_t * pObj;
    int i, f;
    assert( Gia_ManRegNum(pAig) > 0 );
    assert( pPars->nFrames > 0 );
    if ( pPars->fInit )
        return Gia_ManFramesInit( pAig, pPars );
    pFrames = Gia_ManStart( pPars->nFrames * Gia_ManObjNum(pAig) );
    pFrames->pName = Gia_UtilStrsav( pAig->pName );
    Gia_ManHashAlloc( pFrames );
    Gia_ManConst0(pAig)->Value = 0;
    for ( f = 0; f < pPars->nFrames; f++ )
    {
        if ( f == 0 )
        {
            Gia_ManForEachRo( pAig, pObj, i )
                pObj->Value = Gia_ManAppendCi( pFrames );
        }
        else
        {
            Gia_ManForEachRo( pAig, pObj, i )
                pObj->Value = Gia_ObjRoToRi( pAig, pObj )->Value;
        }
        Gia_ManForEachPi( pAig, pObj, i )
            pObj->Value = Gia_ManAppendCi( pFrames );
        Gia_ManForEachAnd( pAig, pObj, i )
            pObj->Value = Gia_ManHashAnd( pFrames, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Gia_ManForEachPo( pAig, pObj, i )
            pObj->Value = Gia_ManAppendCo( pFrames, Gia_ObjFanin0Copy(pObj) );
        if ( f == pPars->nFrames - 1 )
        {
            Gia_ManForEachRi( pAig, pObj, i )
                pObj->Value = Gia_ManAppendCo( pFrames, Gia_ObjFanin0Copy(pObj) );
        }
        else
        {
            Gia_ManForEachRi( pAig, pObj, i )
                pObj->Value = Gia_ObjFanin0Copy(pObj);
        }
    }
    Gia_ManHashStop( pFrames );
    Gia_ManFraTransformCis( pAig, pFrames->vCis );
    Gia_ManSetRegNum( pFrames, Gia_ManRegNum(pAig) );
    if ( Gia_ManCombMarkUsed(pFrames) < Gia_ManAndNum(pFrames) )
    {
        pFrames = Gia_ManDupMarked( pTemp = pFrames );
        if ( pPars->fVerbose )
            printf( "Before cleanup = %d nodes. After cleanup = %d nodes.\n", 
                Gia_ManAndNum(pTemp), Gia_ManAndNum(pFrames) );
        Gia_ManStop( pTemp );
    }
    else if ( pPars->fVerbose )
            printf( "Before cleanup = %d nodes. After cleanup = %d nodes.\n", 
                Gia_ManAndNum(pFrames), Gia_ManAndNum(pFrames) );
    return pFrames;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


