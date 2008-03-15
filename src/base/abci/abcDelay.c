/**CFile****************************************************************

  FileName    [abcDelay.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Delay trace and speedup.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDelay.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "if.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline float Abc_ObjArrival( Abc_Obj_t * pNode )                 { return pNode->pNtk->pLutTimes[3*pNode->Id+0]; }
static inline float Abc_ObjRequired( Abc_Obj_t * pNode )                { return pNode->pNtk->pLutTimes[3*pNode->Id+1]; }
static inline float Abc_ObjSlack( Abc_Obj_t * pNode )                   { return pNode->pNtk->pLutTimes[3*pNode->Id+2]; }

static inline void  Abc_ObjSetArrival( Abc_Obj_t * pNode, float Time )  { pNode->pNtk->pLutTimes[3*pNode->Id+0] = Time; }
static inline void  Abc_ObjSetRequired( Abc_Obj_t * pNode, float Time ) { pNode->pNtk->pLutTimes[3*pNode->Id+1] = Time; }
static inline void  Abc_ObjSetSlack( Abc_Obj_t * pNode, float Time )    { pNode->pNtk->pLutTimes[3*pNode->Id+2] = Time; }

extern void * Abc_FrameReadLibLut();   

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sorts the pins in the decreasing order of delays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDelayTraceSortPins( Abc_Obj_t * pNode, int * pPinPerm, float * pPinDelays )
{
    Abc_Obj_t * pFanin;
    int i, j, best_i, temp;
    // start the trivial permutation and collect pin delays
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        pPinPerm[i] = i;
        pPinDelays[i] = Abc_ObjArrival(pFanin);
    }
    // selection sort the pins in the decreasible order of delays
    // this order will match the increasing order of LUT input pins
    for ( i = 0; i < Abc_ObjFaninNum(pNode)-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < Abc_ObjFaninNum(pNode); j++ )
            if ( pPinDelays[pPinPerm[j]] > pPinDelays[pPinPerm[best_i]] )
                best_i = j;
        if ( best_i == i )
            continue;
        temp = pPinPerm[i]; 
        pPinPerm[i] = pPinPerm[best_i]; 
        pPinPerm[best_i] = temp;
    }
    // verify
    assert( Abc_ObjFaninNum(pNode) == 0 || pPinPerm[0] < Abc_ObjFaninNum(pNode) );
    for ( i = 1; i < Abc_ObjFaninNum(pNode); i++ )
    {
        assert( pPinPerm[i] < Abc_ObjFaninNum(pNode) );
        assert( pPinDelays[pPinPerm[i-1]] >= pPinDelays[pPinPerm[i]] );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Abc_NtkDelayTraceLut( Abc_Ntk_t * pNtk, int fUseLutLib )
{
    int fUseSorting = 1;
    int pPinPerm[32];
    float pPinDelays[32];
    If_Lib_t * pLutLib;
    Abc_Obj_t * pNode, * pFanin;
    Vec_Ptr_t * vNodes;
    float tArrival, tRequired, tSlack, * pDelays;
    int i, k;

    assert( Abc_NtkIsLogic(pNtk) );
    // get the library
    pLutLib = fUseLutLib?  Abc_FrameReadLibLut() : NULL;
    if ( pLutLib && pLutLib->LutMax < Abc_NtkGetFaninMax(pNtk) )
    {
        printf( "The max LUT size (%d) is less than the max fanin count (%d).\n", 
            pLutLib->LutMax, Abc_NtkGetFaninMax(pNtk) );
        return -ABC_INFINITY;
    }

    // initialize the arrival times
    FREE( pNtk->pLutTimes );
    pNtk->pLutTimes = ALLOC( float, 3 * Abc_NtkObjNumMax(pNtk) );
    for ( i = 0; i < Abc_NtkObjNumMax(pNtk); i++ )
    {
        pNtk->pLutTimes[3*i+0] = pNtk->pLutTimes[3*i+2] = 0;
        pNtk->pLutTimes[3*i+1] = ABC_INFINITY;
    }

    // propagate arrival times
    vNodes = Abc_NtkDfs( pNtk, 1 );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        tArrival = -ABC_INFINITY;
        if ( pLutLib == NULL )
        {
            Abc_ObjForEachFanin( pNode, pFanin, k )
                if ( tArrival < Abc_ObjArrival(pFanin) + 1.0 )
                    tArrival = Abc_ObjArrival(pFanin) + 1.0;
        }
        else if ( !pLutLib->fVarPinDelays )
        {
            pDelays = pLutLib->pLutDelays[Abc_ObjFaninNum(pNode)];
            Abc_ObjForEachFanin( pNode, pFanin, k )
                if ( tArrival < Abc_ObjArrival(pFanin) + pDelays[0] )
                    tArrival = Abc_ObjArrival(pFanin) + pDelays[0];
        }
        else
        {
            pDelays = pLutLib->pLutDelays[Abc_ObjFaninNum(pNode)];
            if ( fUseSorting )
            {
                Abc_NtkDelayTraceSortPins( pNode, pPinPerm, pPinDelays );
                Abc_ObjForEachFanin( pNode, pFanin, k ) 
                    if ( tArrival < Abc_ObjArrival(Abc_ObjFanin(pNode,pPinPerm[k])) + pDelays[k] )
                        tArrival = Abc_ObjArrival(Abc_ObjFanin(pNode,pPinPerm[k])) + pDelays[k];
            }
            else
            {
                Abc_ObjForEachFanin( pNode, pFanin, k )
                    if ( tArrival < Abc_ObjArrival(pFanin) + pDelays[k] )
                        tArrival = Abc_ObjArrival(pFanin) + pDelays[k];
            }
        }
        if ( Abc_ObjFaninNum(pNode) == 0 )
            tArrival = 0.0;
        Abc_ObjSetArrival( pNode, tArrival );
    }
    Vec_PtrFree( vNodes );

    // get the latest arrival times
    tArrival = -ABC_INFINITY;
    Abc_NtkForEachCo( pNtk, pNode, i )
        if ( tArrival < Abc_ObjArrival(Abc_ObjFanin0(pNode)) )
            tArrival = Abc_ObjArrival(Abc_ObjFanin0(pNode));

    // initialize the required times
    Abc_NtkForEachCo( pNtk, pNode, i )
        if ( Abc_ObjRequired(Abc_ObjFanin0(pNode)) > tArrival )
            Abc_ObjSetRequired( Abc_ObjFanin0(pNode), tArrival );

    // propagate the required times
    vNodes = Abc_NtkDfsReverse( pNtk );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        if ( pLutLib == NULL )
        {
            tRequired = Abc_ObjRequired(pNode) - (float)1.0;
            Abc_ObjForEachFanin( pNode, pFanin, k )
                if ( Abc_ObjRequired(pFanin) > tRequired )
                    Abc_ObjSetRequired( pFanin, tRequired );
        }
        else if ( !pLutLib->fVarPinDelays )
        {
            pDelays = pLutLib->pLutDelays[Abc_ObjFaninNum(pNode)];
            tRequired = Abc_ObjRequired(pNode) - pDelays[0];
            Abc_ObjForEachFanin( pNode, pFanin, k )
                if ( Abc_ObjRequired(pFanin) > tRequired )
                    Abc_ObjSetRequired( pFanin, tRequired );
        }
        else 
        {
            pDelays = pLutLib->pLutDelays[Abc_ObjFaninNum(pNode)];
            if ( fUseSorting )
            {
                Abc_NtkDelayTraceSortPins( pNode, pPinPerm, pPinDelays );
                Abc_ObjForEachFanin( pNode, pFanin, k )
                {
                    tRequired = Abc_ObjRequired(pNode) - pDelays[k];
                    if ( Abc_ObjRequired(Abc_ObjFanin(pNode,pPinPerm[k])) > tRequired )
                        Abc_ObjSetRequired( Abc_ObjFanin(pNode,pPinPerm[k]), tRequired );
                }
            }
            else
            {
                Abc_ObjForEachFanin( pNode, pFanin, k )
                {
                    tRequired = Abc_ObjRequired(pNode) - pDelays[k];
                    if ( Abc_ObjRequired(pFanin) > tRequired )
                        Abc_ObjSetRequired( pFanin, tRequired );
                }
            }
        }
        // set slack for this object
        tSlack = Abc_ObjRequired(pNode) - Abc_ObjArrival(pNode);
        assert( tSlack + 0.001 > 0.0 );
        Abc_ObjSetSlack( pNode, tSlack < 0.0 ? 0.0 : tSlack );
    }
    Vec_PtrFree( vNodes );
    return tArrival;
}

/**Function*************************************************************

  Synopsis    [Determines timing-critical edges of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Abc_NtkDelayTraceTCEdges( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, float tDelta, int fUseLutLib )
{
    int pPinPerm[32];
    float pPinDelays[32];
    If_Lib_t * pLutLib;
    Abc_Obj_t * pFanin;
    unsigned uResult = 0;
    float tRequired, * pDelays;
    int k;
    pLutLib = fUseLutLib?  Abc_FrameReadLibLut() : NULL;
    tRequired = Abc_ObjRequired(pNode);
    if ( pLutLib == NULL )
    {
        Abc_ObjForEachFanin( pNode, pFanin, k )
            if ( tRequired < Abc_ObjArrival(pFanin) + 1.0 + tDelta )
                uResult |= (1 << k);
    }
    else if ( !pLutLib->fVarPinDelays )
    {
        pDelays = pLutLib->pLutDelays[Abc_ObjFaninNum(pNode)];
        Abc_ObjForEachFanin( pNode, pFanin, k )
            if ( tRequired < Abc_ObjArrival(pFanin) + pDelays[0] + tDelta )
                uResult |= (1 << k);
    }
    else
    {
        pDelays = pLutLib->pLutDelays[Abc_ObjFaninNum(pNode)];
        Abc_NtkDelayTraceSortPins( pNode, pPinPerm, pPinDelays );
        Abc_ObjForEachFanin( pNode, pFanin, k )
            if ( tRequired < Abc_ObjArrival(Abc_ObjFanin(pNode,pPinPerm[k])) + pDelays[k] + tDelta )
                uResult |= (1 << pPinPerm[k]);
    }
    return uResult;
}

/**Function*************************************************************

  Synopsis    [Delay tracing of the LUT mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDelayTracePrint( Abc_Ntk_t * pNtk, int fUseLutLib, int fVerbose )
{
    Abc_Obj_t * pNode;
    If_Lib_t * pLutLib;
    int i, Nodes, * pCounters;
    float tArrival, tDelta, nSteps, Num;
    // get the library
    pLutLib = fUseLutLib?  Abc_FrameReadLibLut() : NULL;
    if ( pLutLib && pLutLib->LutMax < Abc_NtkGetFaninMax(pNtk) )
    {
        printf( "The max LUT size (%d) is less than the max fanin count (%d).\n", 
            pLutLib->LutMax, Abc_NtkGetFaninMax(pNtk) );
        return;
    }
    // decide how many steps
    nSteps = fUseLutLib ? 20 : Abc_NtkLevel(pNtk);
    pCounters = ALLOC( int, nSteps + 1 );
    memset( pCounters, 0, sizeof(int)*(nSteps + 1) );
    // perform delay trace
    tArrival = Abc_NtkDelayTraceLut( pNtk, fUseLutLib );
    tDelta = tArrival / nSteps;
    // count how many nodes have slack in the corresponding intervals
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_ObjFaninNum(pNode) == 0 )
            continue;
        Num = Abc_ObjSlack(pNode) / tDelta;
        assert( Num >=0 && Num <= nSteps );
        pCounters[(int)Num]++;
    }
    // print the results
    printf( "Max delay = %6.2f. Delay trace using %s model:\n", tArrival, fUseLutLib? "LUT library" : "unit-delay" );
    Nodes = 0;
    for ( i = 0; i < nSteps; i++ )
    {
        Nodes += pCounters[i];
        printf( "%3d %s : %5d  (%6.2f %%)\n", fUseLutLib? 5*(i+1) : i+1, 
            fUseLutLib? "%":"lev", Nodes, 100.0*Nodes/Abc_NtkNodeNum(pNtk) );
    }
    free( pCounters );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_AigCheckTfi_rec( Abc_Obj_t * pNode, Abc_Obj_t * pOld )
{
    // check the trivial cases
    if ( pNode == NULL )
        return 0;
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    if ( pNode == pOld )
        return 1;
    // skip the visited node
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return 0;
    Abc_NodeSetTravIdCurrent( pNode );
    // check the children
    if ( Abc_AigCheckTfi_rec( Abc_ObjFanin0(pNode), pOld ) )
        return 1;
    if ( Abc_AigCheckTfi_rec( Abc_ObjFanin1(pNode), pOld ) )
        return 1;
    // check equivalent nodes
    return Abc_AigCheckTfi_rec( pNode->pData, pOld );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_AigCheckTfi( Abc_Obj_t * pNew, Abc_Obj_t * pOld )
{
    assert( !Abc_ObjIsComplement(pNew) );
    assert( !Abc_ObjIsComplement(pOld) );
    Abc_NtkIncrementTravId( pNew->pNtk );
    return Abc_AigCheckTfi_rec( pNew, pOld );
}

/**Function*************************************************************

  Synopsis    [Adds strashed nodes for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkSpeedupNode_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    if ( Abc_NodeIsTravIdCurrent(pNode) )
        return 1;
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    assert( Abc_ObjIsNode(pNode) );
    Abc_NodeSetTravIdCurrent( pNode );
    if ( !Abc_NtkSpeedupNode_rec( Abc_ObjFanin0(pNode), vNodes ) )
        return 0;
    if ( !Abc_NtkSpeedupNode_rec( Abc_ObjFanin1(pNode), vNodes ) )
        return 0;
    Vec_PtrPush( vNodes, pNode );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds strashed nodes for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSpeedupNode( Abc_Ntk_t * pNtk, Abc_Ntk_t * pAig, Abc_Obj_t * pNode, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vTimes )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pObj2, * pAnd;
    Abc_Obj_t * ppCofs[32];
    int nCofs, i, k, nSkip;

    // quit of regulars are the same
    Vec_PtrForEachEntry( vLeaves, pObj, i )
    Vec_PtrForEachEntry( vLeaves, pObj2, k )
        if ( i != k && Abc_ObjRegular(pObj->pCopy) == Abc_ObjRegular(pObj2->pCopy) )
        {
//            printf( "Identical after structural hashing!!!\n" );
            return;
        }

    // collect the AIG nodes
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkIncrementTravId( pAig );
    Abc_NodeSetTravIdCurrent( Abc_AigConst1(pAig) );
    Vec_PtrForEachEntry( vLeaves, pObj, i )
    {
        pAnd = pObj->pCopy;
        Abc_NodeSetTravIdCurrent( Abc_ObjRegular(pAnd) );
    }
    // traverse from the root node
    pAnd = pNode->pCopy;
    if ( !Abc_NtkSpeedupNode_rec( Abc_ObjRegular(pAnd), vNodes ) )
    {
//        printf( "Bad node!!!\n" );
        Vec_PtrFree( vNodes );
        return;
    }

    // derive cofactors
    nCofs = (1 << Vec_PtrSize(vTimes));
    for ( i = 0; i < nCofs; i++ )
    {
        Vec_PtrForEachEntry( vLeaves, pObj, k )
        {
            pAnd = pObj->pCopy;
            Abc_ObjRegular(pAnd)->pCopy = Abc_ObjRegular(pAnd);
        }
        Vec_PtrForEachEntry( vTimes, pObj, k )
        {
            pAnd = pObj->pCopy;
            Abc_ObjRegular(pAnd)->pCopy = Abc_ObjNotCond( Abc_AigConst1(pAig), ((i & (1<<k)) == 0) );
        }
        Vec_PtrForEachEntry( vNodes, pObj, k )
            pObj->pCopy = Abc_AigAnd( pAig->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
        // save the result
        pAnd = pNode->pCopy;
        ppCofs[i] = Abc_ObjNotCond( Abc_ObjRegular(pAnd)->pCopy, Abc_ObjIsComplement(pAnd) );
    }
    Vec_PtrFree( vNodes );

//Abc_ObjAddFanin( Abc_NtkCreatePo(pAig), ppCofs[0] );
//Abc_ObjAddFanin( Abc_NtkCreatePo(pAig), ppCofs[1] );

    // collect the resulting tree
    Vec_PtrForEachEntry( vTimes, pObj, k )
        for ( nSkip = (1<<k), i = 0; i < nCofs; i += 2*nSkip )
        {
            pAnd = pObj->pCopy;
            ppCofs[i] = Abc_AigMux( pAig->pManFunc, Abc_ObjRegular(pAnd), ppCofs[i+nSkip], ppCofs[i] );
        }
//Abc_ObjAddFanin( Abc_NtkCreatePo(pAig), ppCofs[0] );

    // create choice node
    pAnd = Abc_ObjRegular(pNode->pCopy); // repr
    pObj = Abc_ObjRegular(ppCofs[0]);    // new
    if ( pAnd->pData == NULL && pObj->pData == NULL && !Abc_AigCheckTfi(pObj, pAnd) )
    {
        pObj->pData = pAnd->pData;
        pAnd->pData = pObj;
    }

}

/**Function*************************************************************

  Synopsis    [Adds choices to speed up the network by the given percentage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkSpeedup( Abc_Ntk_t * pNtk, int fUseLutLib, int Percentage, int Degree, int fVerbose, int fVeryVerbose )
{
    Abc_Ntk_t * pNtkNew;
    Vec_Ptr_t * vTimeCries, * vTimeFanins;
    Abc_Obj_t * pNode, * pFanin, * pFanin2;
    float tDelta, tArrival;
    int i, k, k2, Counter, CounterRes, nTimeCris;
    unsigned * puTCEdges;
    // perform delay trace
    tArrival = Abc_NtkDelayTraceLut( pNtk, fUseLutLib );
    tDelta = fUseLutLib ? tArrival*Percentage/100.0 : 1.0;
    if ( fVerbose )
    {
        printf( "Max delay = %.2f. Delta = %.2f. ", tArrival, tDelta );
        printf( "Using %s model. ", fUseLutLib? "LUT library" : "unit-delay" );
        if ( fUseLutLib )
            printf( "Percentage = %d. ", Percentage );
        printf( "\n" );
    }
    // mark the timing critical nodes and edges
    puTCEdges = ALLOC( int, Abc_NtkObjNumMax(pNtk) );
    memset( puTCEdges, 0, sizeof(int) * Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_ObjSlack(pNode) >= tDelta )
            continue;
        puTCEdges[pNode->Id] = Abc_NtkDelayTraceTCEdges( pNtk, pNode, tDelta, fUseLutLib );
    }
    if ( fVerbose )
    {
        Counter = CounterRes = 0;
        Abc_NtkForEachNode( pNtk, pNode, i )
        {
            Abc_ObjForEachFanin( pNode, pFanin, k )
                if ( !Abc_ObjIsCi(pFanin) && Abc_ObjSlack(pFanin) < tDelta )
                    Counter++;
            CounterRes += Extra_WordCountOnes( puTCEdges[pNode->Id] );
        }
        printf( "Edges: Total = %7d. 0-slack = %7d. Critical = %7d. Ratio = %4.2f\n", 
            Abc_NtkGetTotalFanins(pNtk), Counter, CounterRes, 1.0*CounterRes/Counter );
    }
    // start the resulting network
    pNtkNew = Abc_NtkStrash( pNtk, 0, 1, 0 );

    // collect nodes to be used for resynthesis
    Counter = CounterRes = 0;
    vTimeCries = Vec_PtrAlloc( 16 );
    vTimeFanins = Vec_PtrAlloc( 16 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_ObjSlack(pNode) >= tDelta )
            continue;
        // count the number of non-PI timing-critical nodes
        nTimeCris = 0;
        Abc_ObjForEachFanin( pNode, pFanin, k )
            if ( !Abc_ObjIsCi(pFanin) && (puTCEdges[pNode->Id] & (1<<k)) )
                nTimeCris++;
        if ( !fVeryVerbose && nTimeCris == 0 )
            continue;
        Counter++;
        // count the total number of timing critical second-generation nodes
        Vec_PtrClear( vTimeCries );
        if ( nTimeCris )
        {
            Abc_ObjForEachFanin( pNode, pFanin, k )
                if ( !Abc_ObjIsCi(pFanin) && (puTCEdges[pNode->Id] & (1<<k)) )
                    Abc_ObjForEachFanin( pFanin, pFanin2, k2 )
                        if ( puTCEdges[pFanin->Id] & (1<<k2) )
                            Vec_PtrPushUnique( vTimeCries, pFanin2 );
        }
//        if ( !fVeryVerbose && (Vec_PtrSize(vTimeCries) == 0 || Vec_PtrSize(vTimeCries) > Degree) )
        if ( (Vec_PtrSize(vTimeCries) == 0 || Vec_PtrSize(vTimeCries) > Degree) )
            continue;
        CounterRes++;
        // collect second generation nodes
        Vec_PtrClear( vTimeFanins );
        Abc_ObjForEachFanin( pNode, pFanin, k )
        {
            if ( Abc_ObjIsCi(pFanin) )
                Vec_PtrPushUnique( vTimeFanins, pFanin );
            else
                Abc_ObjForEachFanin( pFanin, pFanin2, k2 )
                    Vec_PtrPushUnique( vTimeFanins, pFanin2 );                    
        }
        // print the results
        if ( fVeryVerbose )
        {
        printf( "%5d Node %5d : %d %2d %2d  ", Counter, pNode->Id, 
            nTimeCris, Vec_PtrSize(vTimeCries), Vec_PtrSize(vTimeFanins) );
        Abc_ObjForEachFanin( pNode, pFanin, k )
            printf( "%d(%.2f)%s ", pFanin->Id, Abc_ObjSlack(pFanin), (puTCEdges[pNode->Id] & (1<<k))? "*":"" );
        printf( "\n" );
        }
        // add the node to choices
        if ( Vec_PtrSize(vTimeCries) == 0 || Vec_PtrSize(vTimeCries) > Degree )
            continue;
        // order the fanins in the increasing order of criticalily
        if ( Vec_PtrSize(vTimeCries) > 1 )
        {
            pFanin = Vec_PtrEntry( vTimeCries, 0 );
            pFanin2 = Vec_PtrEntry( vTimeCries, 1 );
            if ( Abc_ObjSlack(pFanin) < Abc_ObjSlack(pFanin2) )
            {
                Vec_PtrWriteEntry( vTimeCries, 0, pFanin2 );
                Vec_PtrWriteEntry( vTimeCries, 1, pFanin );
            }
        }
        if ( Vec_PtrSize(vTimeCries) > 2 )
        {
            pFanin = Vec_PtrEntry( vTimeCries, 1 );
            pFanin2 = Vec_PtrEntry( vTimeCries, 2 );
            if ( Abc_ObjSlack(pFanin) < Abc_ObjSlack(pFanin2) )
            {
                Vec_PtrWriteEntry( vTimeCries, 1, pFanin2 );
                Vec_PtrWriteEntry( vTimeCries, 2, pFanin );
            }
            pFanin = Vec_PtrEntry( vTimeCries, 0 );
            pFanin2 = Vec_PtrEntry( vTimeCries, 1 );
            if ( Abc_ObjSlack(pFanin) < Abc_ObjSlack(pFanin2) )
            {
                Vec_PtrWriteEntry( vTimeCries, 0, pFanin2 );
                Vec_PtrWriteEntry( vTimeCries, 1, pFanin );
            }
        }
        // add choice
        Abc_NtkSpeedupNode( pNtk, pNtkNew, pNode, vTimeFanins, vTimeCries );
    }
    Vec_PtrFree( vTimeCries );
    Vec_PtrFree( vTimeFanins );
    free( puTCEdges );
    if ( fVerbose )
        printf( "Nodes: Total = %7d. 0-slack = %7d. Workable = %7d. Ratio = %4.2f\n", 
            Abc_NtkNodeNum(pNtk), Counter, CounterRes, 1.0*CounterRes/Counter ); 

    // remove invalid choice nodes
    Abc_AigForEachAnd( pNtkNew, pNode, i )
        if ( pNode->pData )
        {
            if ( Abc_ObjFanoutNum(pNode->pData) > 0 )
                pNode->pData = NULL;
        }

    // return the result
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


