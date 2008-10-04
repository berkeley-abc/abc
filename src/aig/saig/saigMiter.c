/**CFile****************************************************************

  FileName    [saigMiter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Computes sequential miter of two sequential AIGs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigMiter.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates sequential miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManCreateMiter( Aig_Man_t * p0, Aig_Man_t * p1, int Oper )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    assert( Saig_ManRegNum(p0) > 0 || Saig_ManRegNum(p1) > 0 );
    assert( Saig_ManPiNum(p0) == Saig_ManPiNum(p1) );
    assert( Saig_ManPoNum(p0) == Saig_ManPoNum(p1) );
    pNew = Aig_ManStart( Aig_ManObjNumMax(p0) + Aig_ManObjNumMax(p1) );
    pNew->pName = Aig_UtilStrsav( "miter" );
    // map constant nodes
    Aig_ManConst1(p0)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(p1)->pData = Aig_ManConst1(pNew);
    // map primary inputs
    Saig_ManForEachPi( p0, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Saig_ManForEachPi( p1, pObj, i )
        pObj->pData = Aig_ManPi( pNew, i );
    // map register outputs
    Saig_ManForEachLo( p0, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Saig_ManForEachLo( p1, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // map internal nodes
    Aig_ManForEachNode( p0, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Aig_ManForEachNode( p1, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create primary outputs
    Saig_ManForEachPo( p0, pObj, i )
    {
        if ( Oper == 0 ) // XOR
            pObj = Aig_Exor( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild0Copy(Aig_ManPo(p1,i)) );
        else if ( Oper == 1 ) // implication is PO(p0) -> PO(p1)  ...  complement is PO(p0) & !PO(p1) 
            pObj = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_Not(Aig_ObjChild0Copy(Aig_ManPo(p1,i))) );
        else
            assert( 0 );
        Aig_ObjCreatePo( pNew, pObj );
    }
    // create register inputs
    Saig_ManForEachLi( p0, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Saig_ManForEachLi( p1, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    // cleanup
    Aig_ManSetRegNum( pNew, Saig_ManRegNum(p0) + Saig_ManRegNum(p1) );
    Aig_ManCleanup( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Creates combinational miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManCreateMiterComb( Aig_Man_t * p0, Aig_Man_t * p1, int Oper )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManPiNum(p0) == Aig_ManPiNum(p1) );
    assert( Aig_ManPoNum(p0) == Aig_ManPoNum(p1) );
    pNew = Aig_ManStart( Aig_ManObjNumMax(p0) + Aig_ManObjNumMax(p1) );
    pNew->pName = Aig_UtilStrsav( "miter" );
    // map constant nodes
    Aig_ManConst1(p0)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(p1)->pData = Aig_ManConst1(pNew);
    // map primary inputs and register outputs
    Aig_ManForEachPi( p0, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Aig_ManForEachPi( p1, pObj, i )
        pObj->pData = Aig_ManPi( pNew, i );
    // map internal nodes
    Aig_ManForEachNode( p0, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Aig_ManForEachNode( p1, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create primary outputs
    Aig_ManForEachPo( p0, pObj, i )
    {
        if ( Oper == 0 ) // XOR
            pObj = Aig_Exor( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild0Copy(Aig_ManPo(p1,i)) );
        else if ( Oper == 1 ) // implication is PO(p0) -> PO(p1)  ...  complement is PO(p0) & !PO(p1) 
            pObj = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_Not(Aig_ObjChild0Copy(Aig_ManPo(p1,i))) );
        else
            assert( 0 );
        Aig_ObjCreatePo( pNew, pObj );
    }
    // cleanup
    Aig_ManSetRegNum( pNew, 0 );
    Aig_ManCleanup( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Create combinational timeframes by unrolling sequential circuits.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManUnrollTwo( Aig_Man_t * pBot, Aig_Man_t * pTop, int nFrames )
{
    Aig_Man_t * p, * pAig;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, f;
    assert( nFrames > 1 );
    assert( Saig_ManPiNum(pBot) == Saig_ManPiNum(pTop) );
    assert( Saig_ManPoNum(pBot) == Saig_ManPoNum(pTop) );
    assert( Saig_ManRegNum(pBot) == Saig_ManRegNum(pTop) );
    assert( Saig_ManRegNum(pBot) > 0 || Saig_ManRegNum(pTop) > 0 );
    // start timeframes
    p = Aig_ManStart( nFrames * AIG_MAX(Aig_ManObjNumMax(pBot), Aig_ManObjNumMax(pTop)) );
    p->pName = Aig_UtilStrsav( "frames" );
    // create variables for register outputs
    pAig = pBot;
    Saig_ManForEachLo( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( p );
    // add timeframes
    for ( f = 0; f < nFrames; f++ )
    {
        // create PI nodes for this frame
        Aig_ManConst1(pAig)->pData = Aig_ManConst1( p );
        Saig_ManForEachPi( pAig, pObj, i )
            pObj->pData = Aig_ObjCreatePi( p );
        // add internal nodes of this frame
        Aig_ManForEachNode( pAig, pObj, i )
            pObj->pData = Aig_And( p, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        if ( f == nFrames - 1 )
        {
            // create POs for this frame
            Aig_ManForEachPo( pAig, pObj, i )
                Aig_ObjCreatePo( p, Aig_ObjChild0Copy(pObj) );
            break;
        }
        // save register inputs
        Saig_ManForEachLi( pAig, pObj, i )
            pObj->pData = Aig_ObjChild0Copy(pObj);
        // transfer to register outputs
        Saig_ManForEachLiLo(  pAig, pObjLi, pObjLo, i )
            pObjLo->pData = pObjLi->pData;
        if ( f == 0 )
        {
            // transfer from pOld to pNew
            Saig_ManForEachLo( pAig, pObj, i )
                Saig_ManLo(pTop, i)->pData = pObj->pData;
            pAig = pTop;
        }
    }
    Aig_ManCleanup( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG while creating POs from the set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupNodes_old( Aig_Man_t * p, Vec_Ptr_t * vSet )
{
    Aig_Man_t * pNew, * pCopy;
    Aig_Obj_t * pObj;
    int i;
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
//    Saig_ManForEachPo( p, pObj, i )
//        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Vec_PtrForEachEntry( vSet, pObj, i )
        Aig_ObjCreatePo( pNew, Aig_NotCond((Aig_Obj_t *)Aig_Regular(pObj)->pData, Aig_IsComplement(pObj)) );
    Saig_ManForEachLi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManSetRegNum( pNew, Saig_ManRegNum(p) );
    // cleanup and return a copy
    Aig_ManSeqCleanup( pNew );
    pCopy = Aig_ManDupSimpleDfs( pNew );
    Aig_ManStop( pNew );
    return pCopy;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG while creating POs from the set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupNodes( Aig_Man_t * p, Vec_Ptr_t * vSet, int iPart )
{
    Aig_Man_t * pNew, * pCopy;
    Aig_Obj_t * pObj;
    int i;
    Aig_ManCleanData( p );
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    if ( iPart == 0 )
    {
        Saig_ManForEachLo( p, pObj, i )
            if ( i < Saig_ManRegNum(p)/2 )
                pObj->pData = Aig_ObjCreatePi( pNew );
    }
    else
    {
        Saig_ManForEachLo( p, pObj, i )
            if ( i >= Saig_ManRegNum(p)/2 )
                pObj->pData = Aig_ObjCreatePi( pNew );
    }
    Aig_ManForEachNode( p, pObj, i )
        if ( Aig_ObjFanin0(pObj)->pData && Aig_ObjFanin1(pObj)->pData )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
//    Saig_ManForEachPo( p, pObj, i )
//        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Vec_PtrForEachEntry( vSet, pObj, i )
        Aig_ObjCreatePo( pNew, Aig_NotCond((Aig_Obj_t *)Aig_Regular(pObj)->pData, Aig_IsComplement(pObj)) );
    if ( iPart == 0 )
    {
        Saig_ManForEachLi( p, pObj, i )
            if ( i < Saig_ManRegNum(p)/2 )
                pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    else
    {
        Saig_ManForEachLi( p, pObj, i )
            if ( i >= Saig_ManRegNum(p)/2 )
                pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Aig_ManSetRegNum( pNew, Saig_ManRegNum(p)/2 );
    // cleanup and return a copy
//    Aig_ManSeqCleanup( pNew );
    Aig_ManCleanup( pNew );
    pCopy = Aig_ManDupSimpleDfs( pNew );
    Aig_ManStop( pNew );
    return pCopy;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG to have constant-0 initial state.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManDemiterSimple( Aig_Man_t * p, Aig_Man_t ** ppAig0, Aig_Man_t ** ppAig1 )
{
    Vec_Ptr_t * vSet0, * vSet1;
    Aig_Obj_t * pObj, * pFanin, * pObj0, * pObj1;
    int i, Counter = 0;
    assert( Saig_ManRegNum(p) % 2 == 0 );
    vSet0 = Vec_PtrAlloc( Saig_ManPoNum(p) );
    vSet1 = Vec_PtrAlloc( Saig_ManPoNum(p) );
    Saig_ManForEachPo( p, pObj, i )
    {
        pFanin = Aig_ObjFanin0(pObj);
        if ( Aig_ObjIsConst1( pFanin ) )
        {
            if ( !Aig_ObjFaninC0(pObj) )
                printf( "The output number %d of the miter is constant 1.\n", i );
            Counter++;
            continue;
        }
        if ( !Aig_ObjIsNode(pFanin) || !Aig_ObjRecognizeExor( pFanin, &pObj0, &pObj1 ) )
        {
            printf( "The miter cannot be demitered.\n" );
            Vec_PtrFree( vSet0 );
            Vec_PtrFree( vSet1 );
            return 0;
        }
//        printf( "%d %d  ", Aig_Regular(pObj0)->Id, Aig_Regular(pObj1)->Id );
        if ( Aig_Regular(pObj0)->Id < Aig_Regular(pObj1)->Id )
        {
            Vec_PtrPush( vSet0, pObj0 );
            Vec_PtrPush( vSet1, pObj1 );
        }
        else
        {
            Vec_PtrPush( vSet0, pObj1 );
            Vec_PtrPush( vSet1, pObj0 );
        }
    }
//    printf( "Miter has %d constant outputs.\n", Counter );
//    printf( "\n" );
    if ( ppAig0 )
    {
        *ppAig0 = Aig_ManDupNodes( p, vSet0, 0 );
        FREE( (*ppAig0)->pName );
        (*ppAig0)->pName = Aig_UtilStrsav( "part0" );
    }
    if ( ppAig1 )
    {
        *ppAig1 = Aig_ManDupNodes( p, vSet1, 1 );
        FREE( (*ppAig1)->pName );
        (*ppAig1)->pName = Aig_UtilStrsav( "part1" );
    }
    Vec_PtrFree( vSet0 );
    Vec_PtrFree( vSet1 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Labels logic reachable from the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManDemiterLabel_rec( Aig_Man_t * p, Aig_Obj_t * pObj, int Value )
{
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    if ( Value ) 
        pObj->fMarkB = 1;
    else
        pObj->fMarkA = 1;
    if ( Saig_ObjIsPi(p, pObj) )
        return;
    if ( Saig_ObjIsLo(p, pObj) )
    {
        Saig_ManDemiterLabel_rec( p, Aig_ObjFanin0( Saig_ObjLoToLi(p, pObj) ), Value );
        return;
    }
    assert( Aig_ObjIsNode(pObj) );
    Saig_ManDemiterLabel_rec( p, Aig_ObjFanin0(pObj), Value );
    Saig_ManDemiterLabel_rec( p, Aig_ObjFanin1(pObj), Value );
}

/**Function*************************************************************

  Synopsis    [Returns the first labeled register encountered during traversal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Saig_ManGetLabeledRegister_rec( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pResult;
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return NULL;
    Aig_ObjSetTravIdCurrent(p, pObj);
    if ( Saig_ObjIsPi(p, pObj) )
        return NULL;
    if ( Saig_ObjIsLo(p, pObj) )
    {
        if ( pObj->fMarkA || pObj->fMarkB )
            return pObj;
        return Saig_ManGetLabeledRegister_rec( p, Aig_ObjFanin0( Saig_ObjLoToLi(p, pObj) ) );
    }
    assert( Aig_ObjIsNode(pObj) );
    pResult = Saig_ManGetLabeledRegister_rec( p, Aig_ObjFanin0(pObj) );
    if ( pResult )
        return pResult;
    return Saig_ManGetLabeledRegister_rec( p, Aig_ObjFanin1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG to have constant-0 initial state.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManDemiter( Aig_Man_t * p, Aig_Man_t ** ppAig0, Aig_Man_t ** ppAig1 )
{
    Vec_Ptr_t * vPairs, * vSet0, * vSet1;
    Aig_Obj_t * pObj, * pObj0, * pObj1, * pFlop0, * pFlop1;
    int i, Counter;
    assert( Saig_ManRegNum(p) > 0 );
    Aig_ManSetPioNumbers( p );
    // check if demitering is possible
    vPairs = Vec_PtrAlloc( 2 * Saig_ManPoNum(p) );
    Saig_ManForEachPo( p, pObj, i )
    {
        if ( !Aig_ObjRecognizeExor( Aig_ObjFanin0(pObj), &pObj0, &pObj1 ) )
        {
            Vec_PtrFree( vPairs );
            return 0;
        }
        Vec_PtrPush( vPairs, pObj0 );
        Vec_PtrPush( vPairs, pObj1 );
    }
    // start array of outputs
    vSet0 = Vec_PtrAlloc( Saig_ManPoNum(p) );
    vSet1 = Vec_PtrAlloc( Saig_ManPoNum(p) );
    // get the first pair of outputs
    pObj0 = Vec_PtrEntry( vPairs, 0 );
    pObj1 = Vec_PtrEntry( vPairs, 1 );
    // label registers reachable from the outputs
    Aig_ManIncrementTravId( p );
    Saig_ManDemiterLabel_rec( p, Aig_Regular(pObj0), 0 );
    Vec_PtrPush( vSet0, pObj0 );
    Aig_ManIncrementTravId( p );
    Saig_ManDemiterLabel_rec( p, Aig_Regular(pObj1), 1 );
    Vec_PtrPush( vSet1, pObj1 );
    // find where each output belongs
    for ( i = 2; i < Vec_PtrSize(vPairs); i += 2 )
    {
        pObj0 = Vec_PtrEntry( vPairs, i   );
        pObj1 = Vec_PtrEntry( vPairs, i+1 );

        Aig_ManIncrementTravId( p );
        pFlop0 = Saig_ManGetLabeledRegister_rec( p, Aig_Regular(pObj0) );

        Aig_ManIncrementTravId( p );
        pFlop1 = Saig_ManGetLabeledRegister_rec( p, Aig_Regular(pObj1) );

        if ( (pFlop0->fMarkA && pFlop0->fMarkB) || (pFlop1->fMarkA && pFlop1->fMarkB) || 
             (pFlop0->fMarkA && pFlop1->fMarkA) || (pFlop0->fMarkB && pFlop1->fMarkB)  )
            printf( "Ouput pair %4d: Difficult case...\n", i/2 );

        if ( pFlop0->fMarkB )
        {
            Saig_ManDemiterLabel_rec( p, pObj0, 1 );
            Vec_PtrPush( vSet0, pObj0 );
        }
        else // if ( pFlop0->fMarkA ) or none
        {
            Saig_ManDemiterLabel_rec( p, pObj0, 0 );
            Vec_PtrPush( vSet1, pObj0 );
        }

        if ( pFlop1->fMarkB )
        {
            Saig_ManDemiterLabel_rec( p, pObj1, 1 );
            Vec_PtrPush( vSet0, pObj1 );
        }
        else // if ( pFlop1->fMarkA ) or none
        {
            Saig_ManDemiterLabel_rec( p, pObj1, 0 );
            Vec_PtrPush( vSet1, pObj1 );
        }
    }
    // check if there are any flops in common
    Counter = 0;
    Saig_ManForEachLo( p, pObj, i )
        if ( pObj->fMarkA && pObj->fMarkB )
            Counter++;
    if ( Counter > 0 )
        printf( "The miters contains %d flops reachable from both AIGs.\n", Counter );

    // produce two miters
    if ( ppAig0 )
    {
        assert( 0 );
        *ppAig0 = Aig_ManDupNodes( p, vSet0, 0 ); // not ready
        FREE( (*ppAig0)->pName );
        (*ppAig0)->pName = Aig_UtilStrsav( "part0" );
    }
    if ( ppAig1 )
    {
        assert( 0 );
        *ppAig1 = Aig_ManDupNodes( p, vSet1, 1 ); // not ready
        FREE( (*ppAig1)->pName );
        (*ppAig1)->pName = Aig_UtilStrsav( "part1" );
    }
    Vec_PtrFree( vSet0 );
    Vec_PtrFree( vSet1 );
    Vec_PtrFree( vPairs );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Create specialized miter by unrolling two circuits.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManCreateMiterTwo( Aig_Man_t * pOld, Aig_Man_t * pNew, int nFrames )
{
    Aig_Man_t * pFrames0, * pFrames1, * pMiter;
    assert( Aig_ManNodeNum(pOld) <= Aig_ManNodeNum(pNew) );
    pFrames0 = Saig_ManUnrollTwo( pOld, pOld, nFrames );
    pFrames1 = Saig_ManUnrollTwo( pNew, pOld, nFrames );
    pMiter = Saig_ManCreateMiterComb( pFrames0, pFrames1, 0 );
    Aig_ManStop( pFrames0 );
    Aig_ManStop( pFrames1 );
    return pMiter;
}

/**Function*************************************************************

  Synopsis    [Reduces SEC to CEC for the special case of seq synthesis.]

  Description [The first circuit (pPart0) should be circuit before synthesis.
  The second circuit (pPart1) should be circuit after synthesis.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_SecSpecial( Aig_Man_t * pPart0, Aig_Man_t * pPart1, int fVerbose )
{
    extern int Fra_FraigCec( Aig_Man_t ** ppAig, int nConfLimit, int fVerbose );
    int nFrames = 2;   // modify to enable comparison over any number of frames
    Aig_Man_t * pMiterCec;
    int RetValue, clkTotal = clock();
//    assert( Aig_ManNodeNum(pPart0) <= Aig_ManNodeNum(pPart1) );
    if ( Aig_ManNodeNum(pPart0) >= Aig_ManNodeNum(pPart1) )
    {
        printf( "Warning: The design after synthesis is smaller!\n" );
        printf( "This warning may indicate that the order of designs is changed.\n" );
        printf( "The solver expects the original disign as first argument and\n" );
        printf( "the modified design as the second argument in Ssw_SecSpecial().\n" );
    }
    // create two-level miter
    pMiterCec = Saig_ManCreateMiterTwo( pPart0, pPart1, nFrames );
    if ( fVerbose )
    {
        Aig_ManPrintStats( pMiterCec );
//        Aig_ManDumpBlif( pMiterCec, "miter01.blif", NULL, NULL );
//        printf( "The new miter is written into file \"%s\".\n", "miter01.blif" );
    }
    // run CEC on this miter
    RetValue = Fra_FraigCec( &pMiterCec, 100000, fVerbose );
    // transfer model if given
//    if ( pNtk2 == NULL )
//        pNtk1->pModel = pMiterCec->pData, pMiterCec->pData = NULL;
    Aig_ManStop( pMiterCec );
    // report the miter
    if ( RetValue == 1 )
    {
        printf( "Networks are equivalent.   " );
PRT( "Time", clock() - clkTotal );
    }
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT.   " );
PRT( "Time", clock() - clkTotal );
    }
    else
    {
        printf( "Networks are UNDECIDED.   " );
PRT( "Time", clock() - clkTotal );
    }
    fflush( stdout );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Reduces SEC to CEC for the special case of seq synthesis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_SecSpecialMiter( Aig_Man_t * pMiter, int fVerbose )
{
    Aig_Man_t * pPart0, * pPart1;
    int RetValue;
    if ( fVerbose )
        Aig_ManPrintStats( pMiter );
    // demiter the miter
    if ( !Saig_ManDemiterSimple( pMiter, &pPart0, &pPart1 ) )
    {
        printf( "Demitering has failed.\n" );
        return -1;
    }
    if ( fVerbose )
    {
        Aig_ManPrintStats( pPart0 );
        Aig_ManPrintStats( pPart1 );
//        Aig_ManDumpBlif( pPart0, "part0.blif", NULL, NULL );
//        Aig_ManDumpBlif( pPart1, "part1.blif", NULL, NULL );
//        printf( "The result of demitering is written into files \"%s\" and \"%s\".\n", "part0.blif", "part1.blif" );
    }
    RetValue = Ssw_SecSpecial( pPart0, pPart1, fVerbose );
    Aig_ManStop( pPart0 );
    Aig_ManStop( pPart1 );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


