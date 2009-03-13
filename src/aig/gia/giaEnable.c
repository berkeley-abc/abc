/**CFile****************************************************************

  FileName    [gia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Structural detection of enables, sets and resets.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: gia.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_CollectSuper_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSuper )
{
    // if the new node is complemented or a PI, another gate begins
    if ( Gia_IsComplement(pObj) || Gia_ObjIsCi(pObj) )
    {
        Vec_IntPushUnique( vSuper, Gia_ObjId(p, Gia_Regular(pObj)) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    // go through the branches
    Gia_CollectSuper_rec( p, Gia_ObjChild0(pObj), vSuper );
    Gia_CollectSuper_rec( p, Gia_ObjChild1(pObj), vSuper );
}

/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_CollectSuper( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSuper )
{
    assert( !Gia_IsComplement(pObj) );
    Vec_IntClear( vSuper );
//    Gia_CollectSuper_rec( p, pObj, vSuper );
    if ( Gia_ObjIsAnd(pObj) )
    {
        Vec_IntPushUnique( vSuper, Gia_ObjId(p, Gia_ObjFanin0(pObj)) );
        Vec_IntPushUnique( vSuper, Gia_ObjId(p, Gia_ObjFanin1(pObj)) );
    }
    else
        Vec_IntPushUnique( vSuper, Gia_ObjId(p, Gia_Regular(pObj)) );

}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintSignals( Gia_Man_t * p, int * pFreq, char * pStr )
{
    Vec_Int_t * vObjs;
    int i, Counter = 0, nTotal = 0;
    vObjs = Vec_IntAlloc( 100 );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        if ( pFreq[i] > 1 )
        {
            nTotal += pFreq[i];
            Counter++;
        }
    printf( "%s (total = %d  driven = %d)\n", pStr, Counter, nTotal );
    Counter = 0;
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        if ( pFreq[i] > 10 )
        {
            printf( "%3d :   Obj = %6d   Refs = %6d   Freq = %6d\n", 
                ++Counter, i, Gia_ObjRefs(p, Gia_ManObj(p,i)), pFreq[i] );
            Vec_IntPush( vObjs, i );
        }
    Vec_IntFree( vObjs );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDetectSeqSignals( Gia_Man_t * p, int fSetReset, int fVerbose )
{
    Vec_Int_t * vSuper;
    Gia_Obj_t * pFlop, * pObjC, * pObj0, * pObj1, * pNode, * pTemp;
    int i, k, Ent, * pSets, * pResets, * pEnables;
    int nHaveSetReset = 0, nHaveEnable = 0;
    assert( Gia_ManRegNum(p) > 0 );
    pSets    = ABC_CALLOC( int, Gia_ManObjNum(p) );
    pResets  = ABC_CALLOC( int, Gia_ManObjNum(p) );
    pEnables = ABC_CALLOC( int, Gia_ManObjNum(p) );
    vSuper   = Vec_IntAlloc( 100 );
    Gia_ManForEachRi( p, pFlop, i )
    {
        pNode = Gia_ObjFanin0(pFlop);
        if ( !Gia_ObjIsAnd(pNode) )
            continue;
        // detect sets/resets
        Gia_CollectSuper( p, pNode, vSuper );
        if ( Gia_ObjFaninC0(pFlop) )
            Vec_IntForEachEntry( vSuper, Ent, k )
                pSets[Ent]++;
        else
            Vec_IntForEachEntry( vSuper, Ent, k )
                pResets[Ent]++;
        // detect enables
        if ( !Gia_ObjIsMuxType(pNode) )
            continue;
        pObjC = Gia_ObjRecognizeMux( pNode, &pObj0, &pObj1 );
        pTemp = Gia_ObjRiToRo( p, pFlop );
        if ( Gia_Regular(pObj0) != pTemp && Gia_Regular(pObj1) != pTemp )
            continue;
        if ( !Gia_ObjFaninC0(pFlop) )
        {
            pObj0 = Gia_Not(pObj0);
            pObj1 = Gia_Not(pObj1);
        }
        if ( Gia_IsComplement(pObjC) )
        {
            pObjC = Gia_Not(pObjC);
            pTemp = pObj0;
            pObj0 = pObj1;
            pObj1 = pTemp;
        }
        // detect controls
//        Gia_CollectSuper( p, pObjC, vSuper );
//        Vec_IntForEachEntry( vSuper, Ent, k )
//            pEnables[Ent]++;
        pEnables[Gia_ObjId(p, pObjC)]++;
        nHaveEnable++;
    }
    Gia_ManForEachRi( p, pFlop, i )
    {
        pNode = Gia_ObjFanin0(pFlop);
        if ( !Gia_ObjIsAnd(pNode) )
            continue;
        // detect sets/resets
        Gia_CollectSuper( p, pNode, vSuper );
        Vec_IntForEachEntry( vSuper, Ent, k )
            if ( pSets[Ent] > 1 || pResets[Ent] > 1 )
            {
                nHaveSetReset++;
                break;
            }
    }
    Vec_IntFree( vSuper );
    ABC_FREE( p->pRefs );
    Gia_ManCreateRefs( p );
    if ( fVerbose )
    {
        printf( "Flops with set/reset = %6d. Flops with enable = %6d.\n", nHaveSetReset, nHaveEnable );
        if ( fSetReset )
        {
            Gia_ManPrintSignals( p, pSets, "Set signals" );
            Gia_ManPrintSignals( p, pResets, "Reset signals" );
        }
        Gia_ManPrintSignals( p, pEnables, "Enable signals" );
    }
    ABC_FREE( p->pRefs );
    ABC_FREE( pSets );
    ABC_FREE( pResets );
    ABC_FREE( pEnables );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManDetectSeqSignalsWithFanout( Gia_Man_t * p, int nFanMax, int fVerbose )
{
    Vec_Int_t * vResult;
    Vec_Int_t * vSuper;
    Gia_Obj_t * pFlop, * pObjC, * pObj0, * pObj1, * pNode, * pTemp;
    int i, k, Ent, * pSets, * pResets, * pEnables;
    int nHaveSetReset = 0, nHaveEnable = 0;
    assert( Gia_ManRegNum(p) > 0 );
    pSets    = ABC_CALLOC( int, Gia_ManObjNum(p) );
    pResets  = ABC_CALLOC( int, Gia_ManObjNum(p) );
    pEnables = ABC_CALLOC( int, Gia_ManObjNum(p) );
    vSuper   = Vec_IntAlloc( 100 );
    Gia_ManForEachRi( p, pFlop, i )
    {
        pNode = Gia_ObjFanin0(pFlop);
        if ( !Gia_ObjIsAnd(pNode) )
            continue;
        // detect sets/resets
        Gia_CollectSuper( p, pNode, vSuper );
        if ( Gia_ObjFaninC0(pFlop) )
            Vec_IntForEachEntry( vSuper, Ent, k )
                pSets[Ent]++;
        else
            Vec_IntForEachEntry( vSuper, Ent, k )
                pResets[Ent]++;
        // detect enables
        if ( !Gia_ObjIsMuxType(pNode) )
            continue;
        pObjC = Gia_ObjRecognizeMux( pNode, &pObj0, &pObj1 );
        pTemp = Gia_ObjRiToRo( p, pFlop );
        if ( Gia_Regular(pObj0) != pTemp && Gia_Regular(pObj1) != pTemp )
            continue;
        if ( !Gia_ObjFaninC0(pFlop) )
        {
            pObj0 = Gia_Not(pObj0);
            pObj1 = Gia_Not(pObj1);
        }
        if ( Gia_IsComplement(pObjC) )
        {
            pObjC = Gia_Not(pObjC);
            pTemp = pObj0;
            pObj0 = pObj1;
            pObj1 = pTemp;
        }
        // detect controls
//        Gia_CollectSuper( p, pObjC, vSuper );
//        Vec_IntForEachEntry( vSuper, Ent, k )
//            pEnables[Ent]++;
        pEnables[Gia_ObjId(p, pObjC)]++;
        nHaveEnable++;
    }
    Gia_ManForEachRi( p, pFlop, i )
    {
        pNode = Gia_ObjFanin0(pFlop);
        if ( !Gia_ObjIsAnd(pNode) )
            continue;
        // detect sets/resets
        Gia_CollectSuper( p, pNode, vSuper );
        Vec_IntForEachEntry( vSuper, Ent, k )
            if ( pSets[Ent] > 1 || pResets[Ent] > 1 )
            {
                nHaveSetReset++;
                break;
            }
    }
    Vec_IntFree( vSuper );
    vResult  = Vec_IntAlloc( 100 );
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
        if ( pSets[i] > nFanMax )
        {
            if ( fVerbose )
                printf( "Adding set signal %d related to %d flops.\n", i, pSets[i] );
            Vec_IntPushUnique( vResult, i );
        }
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
        if ( pResets[i] > nFanMax )
        {
            if ( fVerbose )
                printf( "Adding reset signal %d related to %d flops.\n", i, pResets[i] );
            Vec_IntPushUnique( vResult, i );
        }
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
        if ( pEnables[i] > nFanMax )
        {
            if ( fVerbose )
                printf( "Adding enable signal %d related to %d flops.\n", i, pEnables[i] );
            Vec_IntPushUnique( vResult, i );
        }
    ABC_FREE( pSets );
    ABC_FREE( pResets );
    ABC_FREE( pEnables );
    return vResult;
}


/**Function*************************************************************

  Synopsis    [Transfers attributes from the original one to the final one.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManTransferFrames( Gia_Man_t * pAig, Gia_Man_t * pFrames, int nFrames, Gia_Man_t * pNew, Vec_Int_t * vSigs )
{
    Vec_Int_t * vSigsNew;
    Gia_Obj_t * pObj, * pObjF;
    int k, f;
    vSigsNew = Vec_IntAlloc( 100 );
    Gia_ManForEachObjVec( vSigs, pAig, pObj, k )
    {
        assert( Gia_ObjIsCand(pObj) );
        for ( f = 0; f < nFrames; f++ )
        {
            pObjF = Gia_ManObj( pFrames, Gia_Lit2Var(Gia_ObjCopyF( pAig, f, pObj )) );
            if ( pObjF->Value && ~pObjF->Value )
                Vec_IntPushUnique( vSigsNew, Gia_Lit2Var(pObjF->Value) );
        }
    }
    return vSigsNew;    
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManUnrollInit( Gia_Man_t * p, int nFrames )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj, * pObjRi, * pObjRo;
    int f, i;
    ABC_FREE( p->pCopies );
    p->pCopies = ABC_FALLOC( int, nFrames * Gia_ManObjNum(p) );
    pNew = Gia_ManStart( nFrames * Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachRo( p, pObj, i )
        Gia_ObjSetCopyF( p, 0, pObj, 0 );
    for ( f = 0; f < nFrames; f++ )
    {
        Gia_ObjSetCopyF( p, f, Gia_ManConst0(p), 0 );
        Gia_ManForEachPi( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManAppendCi(pNew) );
        Gia_ManForEachAnd( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManHashAnd(pNew, Gia_ObjFanin0CopyF(p, f, pObj), Gia_ObjFanin1CopyF(p, f, pObj)) );
        Gia_ManForEachCo( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ObjFanin0CopyF(p, f, pObj) );
        Gia_ManForEachPo( p, pObj, i )
            Gia_ManAppendCo( pNew, Gia_ObjCopyF(p, f, pObj) );
        if ( f == nFrames - 1 )
            break;
        Gia_ManForEachRiRo( p, pObjRi, pObjRo, i )
            Gia_ObjSetCopyF( p, f+1, pObjRo, Gia_ObjCopyF(p, f, pObjRi) );
    }
    Gia_ManHashStop( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Unrolls initialized timeframes while cofactoring some vars.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManUnrollAndCofactor( Gia_Man_t * p, int nFrames, int nFanMax, int fVerbose )
{
    Vec_Int_t * vCofSigs, * vTemp;
    Gia_Man_t * pAig, * pFrames, * pNew;
    // compute initialized timeframes
    pFrames  = Gia_ManUnrollInit( p, nFrames );
    pAig     = Gia_ManCleanup( pFrames );
    // compute and remap set/reset/enable signals
    vCofSigs = Gia_ManDetectSeqSignalsWithFanout( p, nFanMax, fVerbose );
    vCofSigs = Gia_ManTransferFrames( p, pFrames, nFrames, pAig, vTemp = vCofSigs );
    Vec_IntFree( vTemp );
    Gia_ManStop( pFrames );
    ABC_FREE( p->pCopies );
    // cofactor all these variables
    pNew = Gia_ManDupCofAllInt( pAig, vCofSigs, fVerbose );
    Vec_IntFree( vCofSigs );
    Gia_ManStop( pAig );
    return pNew;

}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


