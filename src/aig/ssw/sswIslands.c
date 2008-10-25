/**CFile****************************************************************

  FileName    [sswIslands.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [Detection of islands of difference.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswIslands.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Aig_Obj_t *  Aig_ObjChild0Copy2( Aig_Obj_t * pObj )  { return Aig_ObjFanin0(pObj)->pData? Aig_NotCond((Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj)) : NULL;  }
static inline Aig_Obj_t *  Aig_ObjChild1Copy2( Aig_Obj_t * pObj )  { return Aig_ObjFanin1(pObj)->pData? Aig_NotCond((Aig_Obj_t *)Aig_ObjFanin1(pObj)->pData, Aig_ObjFaninC1(pObj)) : NULL;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates pair of structurally equivalent nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_CreatePair( Vec_Int_t * vPairs, Aig_Obj_t * pObj0, Aig_Obj_t * pObj1 )
{
    pObj0->pData = pObj1;
    pObj1->pData = pObj0;
    Vec_IntPush( vPairs, pObj0->Id );
    Vec_IntPush( vPairs, pObj1->Id );
}

/**Function*************************************************************

  Synopsis    [Detects islands of common logic and returns them as pairs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ssw_DetectIslands( Aig_Man_t * p0, Aig_Man_t * p1, int nCommonFlops, int fVerbose )
{
    Vec_Int_t * vPairs;
    Aig_Obj_t * pObj0, * pObj1, * pFanin0, * pFanin1;
    int i;
    assert( Aig_ManRegNum(p0) > 0 );
    assert( Aig_ManRegNum(p1) > 0 );
    assert( Aig_ManRegNum(p0) >= nCommonFlops );
    assert( Aig_ManRegNum(p1) >= nCommonFlops );
    assert( Saig_ManPiNum(p0) == Saig_ManPiNum(p1) );
    assert( Saig_ManPoNum(p0) == Saig_ManPoNum(p1) );
    Aig_ManCleanData( p0 );
    Aig_ManCleanData( p1 );
    // start structural equivalence
    vPairs = Vec_IntAlloc( 1000 );
    Ssw_CreatePair( vPairs, Aig_ManConst1(p0), Aig_ManConst1(p1) );
    Saig_ManForEachPi( p0, pObj0, i )
        Ssw_CreatePair( vPairs, pObj0, Aig_ManPi(p1, i) );
    Saig_ManForEachLo( p0, pObj0, i )
    {
        if ( i == nCommonFlops )
            break;
        Ssw_CreatePair( vPairs, pObj0, Saig_ManLo(p1, i) );
    }
    // find structurally equivalent nodes
    Aig_ManForEachNode( p0, pObj0, i )
    {
        pFanin0 = Aig_ObjChild0Copy2( pObj0 );
        pFanin1 = Aig_ObjChild1Copy2( pObj0 );
        if ( pFanin0 == NULL || pFanin1 == NULL )
            continue;
        pObj1 = Aig_TableLookupTwo( p1, pFanin0, pFanin1 );
        if ( pObj1 == NULL )
            continue;
        Ssw_CreatePair( vPairs, pObj0, pObj1 );
    }
    return vPairs;
}

/**Function*************************************************************

  Synopsis    [Collects additional Lis and Los.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_CollectExtraLiLo( Aig_Man_t * p, int nCommonFlops, Vec_Ptr_t * vLis, Vec_Ptr_t * vLos )
{
    Aig_Obj_t * pObjLo, * pObjLi;
    int i;
    Saig_ManForEachLiLo( p, pObjLo, pObjLi, i )
    {
        if ( i < nCommonFlops )
            continue;
        Vec_PtrPush( vLis, pObjLi );
        Vec_PtrPush( vLos, pObjLo );
    }
}

/**Function*************************************************************

  Synopsis    [Overlays and extends the pairs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_OverlayIslands( Aig_Man_t * pTo, Aig_Man_t * pFrom, Vec_Ptr_t * vLisFrom, Vec_Ptr_t * vLosFrom, Vec_Int_t * vPairs, int nCommonFlops, int fToGoesFirst )
{
    Aig_Obj_t * pObjFrom, * pObjTo, * pFanin0To, * pFanin1To;
    int i;
    // create additional register outputs of From in To
    Vec_PtrForEachEntry( vLosFrom, pObjFrom, i )
    {
        pObjTo = Aig_ObjCreatePi( pTo );
        if( fToGoesFirst )
            Ssw_CreatePair( vPairs, pObjTo, pObjFrom );
        else
            Ssw_CreatePair( vPairs, pObjFrom, pObjTo );
    }
    // create additional nodes of From in To
    Aig_ManForEachNode( pFrom, pObjFrom, i )
    {
        if ( pObjFrom->pData != NULL )
            continue;
        pFanin0To = Aig_ObjChild0Copy2( pObjFrom );
        pFanin1To = Aig_ObjChild1Copy2( pObjFrom );
        assert( pFanin0To != NULL && pFanin1To != NULL );
        pObjTo = Aig_And( pTo, pFanin0To, pFanin1To );
        if( fToGoesFirst )
            Ssw_CreatePair( vPairs, pObjTo, pObjFrom );
        else
            Ssw_CreatePair( vPairs, pObjFrom, pObjTo );
    }
    // finally recreate additional register inputs
    Vec_PtrForEachEntry( vLisFrom, pObjFrom, i )
    {
        pFanin0To = Aig_ObjChild0Copy2( pObjFrom );
        Aig_ObjCreatePo( pTo, pFanin0To );
    }
    // update the number of registers
    Aig_ManSetRegNum( pTo, Aig_ManRegNum(pTo) + Vec_PtrSize(vLisFrom) );
}

/**Function*************************************************************

  Synopsis    [Overlays and extends the pairs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManMiterWithIslands( Aig_Man_t * p0, Aig_Man_t * p1, Aig_Man_t ** ppMiter, Vec_Int_t * vPairs )
{
    Aig_Man_t * pMiter;
    Vec_Int_t * vPairsNew;
    Aig_Obj_t * pObj0, * pObj1;
    int i;
    vPairsNew = Vec_IntAlloc( 1000 );
    pMiter = Saig_ManCreateMiter( p0, p1, 0 );
    for ( i = 0; i < Vec_IntSize(vPairs); i += 2 )
    {
        pObj0 = Aig_ManObj( p0, Vec_IntEntry(vPairs, i) );
        pObj1 = Aig_ManObj( p1, Vec_IntEntry(vPairs, i+1) );
        pObj0 = pObj0->pData;
        pObj1 = pObj1->pData;
        assert( !Aig_IsComplement(pObj0) );
        assert( !Aig_IsComplement(pObj1) );
        if ( pObj0 == pObj1 )
            continue;
        assert( pObj0->Id < pObj1->Id );
        Vec_IntPush( vPairsNew, pObj0->Id );
        Vec_IntPush( vPairsNew, pObj1->Id );
    }
    *ppMiter = pMiter;
    return vPairsNew;
}

/**Function*************************************************************

  Synopsis    [Solves SEC using structural similarity.]

  Description [Modifies both p0 and p1 by adding extra logic.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ssw_SecWithIslandsInternal( Aig_Man_t * p0, Aig_Man_t * p1, int nCommonFlops, int fVerbose, Ssw_Pars_t * pPars )
{
    Ssw_Man_t * p; 
    Ssw_Pars_t Pars;
    Vec_Int_t * vPairs, * vPairsMiter;
    Aig_Man_t * pMiter, * pAigNew;
    Vec_Ptr_t * vLis0, * vLos0, * vLis1, * vLos1; 
    int nNodes, nRegs;
    assert( Aig_ManRegNum(p0) > 0 );
    assert( Aig_ManRegNum(p1) > 0 );
    assert( Aig_ManRegNum(p0) >= nCommonFlops );
    assert( Aig_ManRegNum(p1) >= nCommonFlops );
    assert( Saig_ManPiNum(p0) == Saig_ManPiNum(p1) );
    assert( Saig_ManPoNum(p0) == Saig_ManPoNum(p1) );
    // derive pairs
    vPairs = Ssw_DetectIslands( p0, p1, nCommonFlops, fVerbose );
    if ( fVerbose )
    {
        printf( "Original managers:\n" );
        Aig_ManPrintStats( p0 );
        Aig_ManPrintStats( p1 );
        printf( "Detected %d PI pairs, %d LO pairs, and %d node pairs.\n", 
            Saig_ManPiNum(p0), nCommonFlops, Vec_IntSize(vPairs)/2 - Saig_ManPiNum(p0) - nCommonFlops - 1 );
    }
    // complete the manager with islands
    vLis0 = Vec_PtrAlloc( 100 );
    vLos0 = Vec_PtrAlloc( 100 );
    vLis1 = Vec_PtrAlloc( 100 );
    vLos1 = Vec_PtrAlloc( 100 );
    Ssw_CollectExtraLiLo( p0, nCommonFlops, vLis0, vLos0 );
    Ssw_CollectExtraLiLo( p1, nCommonFlops, vLis1, vLos1 );

    nRegs  = Saig_ManRegNum(p0);
    nNodes = Aig_ManNodeNum(p0);
    Ssw_OverlayIslands( p0, p1, vLis1, vLos1, vPairs, nCommonFlops, 1 );
    if ( fVerbose )
        printf( "Completed p0 with %d registers and %d nodes.\n", 
            Saig_ManRegNum(p0) - nRegs, Aig_ManNodeNum(p0) - nNodes );   
    
    nRegs  = Saig_ManRegNum(p1);
    nNodes = Aig_ManNodeNum(p1);
    Ssw_OverlayIslands( p1, p0, vLis0, vLos0, vPairs, nCommonFlops, 0 );
    if ( fVerbose )
        printf( "Completed p1 with %d registers and %d nodes.\n", 
            Saig_ManRegNum(p1) - nRegs, Aig_ManNodeNum(p1) - nNodes );   
    if ( fVerbose )
    {
        printf( "Modified managers:\n" );
        Aig_ManPrintStats( p0 );
        Aig_ManPrintStats( p1 );
    }

    Vec_PtrFree( vLis0 );
    Vec_PtrFree( vLos0 );
    Vec_PtrFree( vLis1 );
    Vec_PtrFree( vLos1 );
    // create sequential miter
    vPairsMiter = Saig_ManMiterWithIslands( p0, p1, &pMiter, vPairs );
    Vec_IntFree( vPairs );
    // if parameters are not given, create them
    if ( pPars == NULL )
        Ssw_ManSetDefaultParams( pPars = &Pars );
    // start the induction manager
    p = Ssw_ManCreate( pMiter, pPars );
    // create equivalence classes using these IDs
    p->ppClasses = Ssw_ClassesFromIslands( pMiter, vPairsMiter );
    p->pSml = Ssw_SmlStart( pMiter, 0, 1 + p->pPars->nFramesAddSim, 1 );
    Ssw_ClassesSetData( p->ppClasses, p->pSml, Ssw_SmlObjHashWord, Ssw_SmlObjIsConstWord, Ssw_SmlObjsAreEqualWord );
    // perform refinement of classes
    pAigNew = Ssw_SignalCorrespondenceRefine( p );
    // cleanup
    Ssw_ManStop( p );
    Aig_ManStop( pMiter );
    Vec_IntFree( vPairsMiter );
    return pAigNew;
}

/**Function*************************************************************

  Synopsis    [Solves SEC using structural similarity.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_SecWithIslands( Aig_Man_t * p0, Aig_Man_t * p1, int nCommonFlops, int fVerbose, Ssw_Pars_t * pPars )
{
    Aig_Man_t * pAigRes;
    Aig_Man_t * p0New, * p1New;
    int RetValue, clk = clock();
    // try the new AIGs
//    printf( "Performing verification using structural similarity.\n" );
    p0New = Aig_ManDupSimple( p0 );
    p1New = Aig_ManDupSimple( p1 );
    pAigRes = Ssw_SecWithIslandsInternal( p0New, p1New, nCommonFlops, fVerbose, pPars );
    Aig_ManStop( p0New );
    Aig_ManStop( p1New );
    // report the results
    RetValue = Ssw_MiterStatus( pAigRes, 1 );
    if ( RetValue == 1 )
        printf( "Verification successful.  " );
    else if ( RetValue == 0 )
        printf( "Verification failed with a counter-example.  " );
    else
        printf( "Verification UNDECIDED. The number of remaining regs = %d (total = %d).  ", 
            Aig_ManRegNum(pAigRes), Aig_ManRegNum(p0New)+Aig_ManRegNum(p1New) );
    PRT( "Time", clock() - clk );
    // cleanup
    Aig_ManStop( pAigRes );
    return RetValue;
}


/**Function*************************************************************

  Synopsis    [Solves SEC using structural similarity for the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_SecWithIslandsMiter( Aig_Man_t * pMiter, int nCommonFlops, int fVerbose )
{
    Aig_Man_t * pPart0, * pPart1;
    int RetValue;
    if ( fVerbose )
        Aig_ManPrintStats( pMiter );
    // demiter the miter
    if ( !Saig_ManDemiterSimpleDiff( pMiter, &pPart0, &pPart1 ) )
    {
        printf( "Demitering has failed.\n" );
        return -1;
    }
    if ( fVerbose )
    {
//        Aig_ManPrintStats( pPart0 );
//        Aig_ManPrintStats( pPart1 );
//        Aig_ManDumpBlif( pPart0, "part0.blif", NULL, NULL );
//        Aig_ManDumpBlif( pPart1, "part1.blif", NULL, NULL );
//        printf( "The result of demitering is written into files \"%s\" and \"%s\".\n", "part0.blif", "part1.blif" );
    }
    RetValue = Ssw_SecWithIslands( pPart0, pPart1, nCommonFlops, fVerbose, NULL );
    Aig_ManStop( pPart0 );
    Aig_ManStop( pPart1 );
    return RetValue;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


