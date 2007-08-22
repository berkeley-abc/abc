/**CFile****************************************************************

  FileName    [fraImp.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    [Detecting and proving implications.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraImp.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int   Sml_ImpLeft( int Imp )               { return Imp & 0xFFFF;         }
static inline int   Sml_ImpRight( int Imp )              { return Imp >> 16;            }
static inline int   Sml_ImpCreate( int Left, int Right ) { return (Right << 16) | Left; }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts the number of 1s in each siminfo of each node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int * Fra_SmlCountOnes( Fra_Sml_t * p )
{
    Aig_Obj_t * pObj;
    unsigned * pSim;
    int i, k, * pnBits; 
    pnBits = ALLOC( int, Aig_ManObjIdMax(p->pAig) + 1 );  
    memset( pnBits, 0, sizeof(int) * (Aig_ManObjIdMax(p->pAig) + 1) );
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        pSim = Fra_ObjSim( p, i );
        for ( k = p->nWordsPref; k < p->nWordsTotal; k++ )
            pnBits[i] += Aig_WordCountOnes( pSim[k] );
    }
    return pnBits;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if implications holds.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sml_NodeCheckImp( Fra_Sml_t * p, int Left, int Right )
{
    unsigned * pSimL, * pSimR;
    int k;
    pSimL = Fra_ObjSim( p, Left );
    pSimR = Fra_ObjSim( p, Right );
    for ( k = p->nWordsPref; k < p->nWordsTotal; k++ )
        if ( pSimL[k] & ~pSimR[k] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Counts the number of 1s in the reverse implication.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sml_NodeNotImpWeight( Fra_Sml_t * p, int Left, int Right )
{
    unsigned * pSimL, * pSimR;
    int k, Counter = 0;
    pSimL = Fra_ObjSim( p, Left );
    pSimR = Fra_ObjSim( p, Right );
    for ( k = p->nWordsPref; k < p->nWordsTotal; k++ )
        Counter += Aig_WordCountOnes( pSimL[k] & ~pSimR[k] );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Returns the array of nodes sorted by the number of 1s.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Fra_SmlSortUsingOnes( Fra_Sml_t * p, int fLatchCorr )
{
    Aig_Obj_t * pObj;
    Vec_Ptr_t * vNodes;
    int i, nNodes, nTotal, nBits, * pnNodes, * pnBits, * pMemory;
    assert( p->nWordsTotal > 0 );
    // count 1s in each node's siminfo
    pnBits = Fra_SmlCountOnes( p );
    // count number of nodes having that many 1s
    nNodes = 0;
    nBits = p->nWordsTotal * 32;
    pnNodes = ALLOC( int, nBits + 1 );
    memset( pnNodes, 0, sizeof(int) * (nBits + 1) );
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( i == 0 ) continue;
        // skip non-PI and non-internal nodes
        if ( fLatchCorr )
        {
            if ( !Aig_ObjIsPi(pObj) )
                continue;
        }
        else
        {
            if ( !Aig_ObjIsNode(pObj) && !Aig_ObjIsPi(pObj) )
                continue;
        }
        // skip nodes participating in the classes
//        if ( Fra_ClassObjRepr(pObj) )
//            continue;
        assert( pnBits[i] <= nBits ); // "<" because of normalized info
        pnNodes[pnBits[i]]++;
        nNodes++;
    }
    // allocate memory for all the nodes
    pMemory = ALLOC( int, nNodes + nBits + 1 );  
    // markup the memory for each node
    vNodes = Vec_PtrAlloc( nBits + 1 );
    Vec_PtrPush( vNodes, pMemory );
    for ( i = 1; i <= nBits; i++ )
    {
        pMemory += pnNodes[i-1] + 1;
        Vec_PtrPush( vNodes, pMemory );
    }
    // add the nodes
    memset( pnNodes, 0, sizeof(int) * (nBits + 1) );
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( i == 0 ) continue;
        // skip non-PI and non-internal nodes
        if ( fLatchCorr )
        {
            if ( !Aig_ObjIsPi(pObj) )
                continue;
        }
        else
        {
            if ( !Aig_ObjIsNode(pObj) && !Aig_ObjIsPi(pObj) )
                continue;
        }
        // skip nodes participating in the classes
//        if ( Fra_ClassObjRepr(pObj) )
//            continue;
        pMemory = Vec_PtrEntry( vNodes, pnBits[i] );
        pMemory[ pnNodes[pnBits[i]]++ ] = i;
    }
    // add 0s in the end
    nTotal = 0;
    Vec_PtrForEachEntry( vNodes, pMemory, i )
    {
        pMemory[ pnNodes[i]++ ] = 0;
        nTotal += pnNodes[i];
    }
    assert( nTotal == nNodes + nBits + 1 );
    free( pnNodes );
    free( pnBits );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Returns the array of implications with the highest cost.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Fra_SmlSelectMaxCost( Vec_Int_t * vImps, int * pCosts, int nCostMax, int nImpLimit, int * pCostRange )
{
    Vec_Int_t * vImpsNew;
    int * pCostCount, nImpCount, Imp, i, c;
    assert( Vec_IntSize(vImps) >= nImpLimit );
    // count how many implications have each cost
    pCostCount = ALLOC( int, nCostMax + 1 );
    memset( pCostCount, 0, sizeof(int) * (nCostMax + 1) );
    for ( i = 0; i < Vec_IntSize(vImps); i++ )
    {
        assert( pCosts[i] <= nCostMax );
        pCostCount[ pCosts[i] ]++;
    }
    assert( pCostCount[0] == 0 );
    // select the bound on the cost (above this bound, implication will be included)
    nImpCount = 0;
    for ( c = nCostMax; c > 0; c-- )
    {
        nImpCount += pCostCount[c];
        if ( nImpCount >= nImpLimit )
            break;
    }
//    printf( "Cost range >= %d.\n", c );
    // collect implications with the given costs
    vImpsNew = Vec_IntAlloc( nImpLimit );
    Vec_IntForEachEntry( vImps, Imp, i )
    {
        if ( pCosts[i] < c )
            continue;
        Vec_IntPush( vImpsNew, Imp );
        if ( Vec_IntSize( vImpsNew ) == nImpLimit )
            break;
    }
    free( pCostCount );
    if ( pCostRange )
        *pCostRange = c;
    return vImpsNew;
}

/**Function*************************************************************

  Synopsis    [Compares two implications using their largest ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sml_CompareMaxId( unsigned short * pImp1, unsigned short * pImp2 )
{
    int Max1 = AIG_MAX( pImp1[0], pImp1[1] );
    int Max2 = AIG_MAX( pImp2[0], pImp2[1] );
    if ( Max1 < Max2 )
        return -1;
    if ( Max1 > Max2  )
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Derives implication candidates.]

  Description [Implication candidates have the property that 
  (1) they hold using sequential simulation information
  (2) they do not hold using combinational simulation information
  (3) they have as high expressive power as possible (heuristically)
      that is, they are easy to disprove combinationally
      meaning they cover relatively larger sequential subspace.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Fra_ImpDerive( Fra_Man_t * p, int nImpMaxLimit, int nImpUseLimit, int fLatchCorr )
{
//    Aig_Obj_t * pObj;
    int nSimWords = 64;
    Fra_Sml_t * pSeq, * pComb;
    Vec_Int_t * vImps, * vTemp;
    Vec_Ptr_t * vNodes;
    int * pImpCosts, * pNodesI, * pNodesK;
    int nImpsTotal = 0, nImpsTried = 0, nImpsNonSeq = 0, nImpsComb = 0, nImpsCollected = 0;
    int CostMin = AIG_INFINITY, CostMax = 0;
    int i, k, Imp, CostRange, clk = clock();
    assert( nImpMaxLimit > 0 && nImpUseLimit > 0 && nImpUseLimit <= nImpMaxLimit );
    // normalize both managers
    pComb = Fra_SmlSimulateComb( p->pManAig, nSimWords );
    pSeq = Fra_SmlSimulateSeq( p->pManAig, p->pPars->nFramesP, nSimWords, 1 );
    // get the nodes sorted by the number of 1s
    vNodes = Fra_SmlSortUsingOnes( pSeq, fLatchCorr );
/*
Aig_ManForEachObj( p->pManAig, pObj, i )
{
    printf( "%6s", Aig_ObjIsPi(pObj)? "pi" : (Aig_ObjIsNode(pObj)? "node" : "other" ) );
    printf( "%d (%d) :\n", i, pObj->fPhase );
    Extra_PrintBinary( stdout, Fra_ObjSim( pComb, i ), 64 ); printf( "\n" );
    Extra_PrintBinary( stdout, Fra_ObjSim( pSeq, i ), 64 ); printf( "\n" );
}
*/
    // count the total number of implications
    for ( k = nSimWords * 32; k > 0; k-- )
    for ( i = k - 1; i > 0; i-- )
    for ( pNodesI = Vec_PtrEntry( vNodes, i ); *pNodesI; pNodesI++ )
    for ( pNodesK = Vec_PtrEntry( vNodes, k ); *pNodesK; pNodesK++ )
        nImpsTotal++;

    // compute implications and their costs
    pImpCosts = ALLOC( int, nImpMaxLimit );
    vImps = Vec_IntAlloc( nImpMaxLimit );
    for ( k = pSeq->nWordsTotal * 32; k > 0; k-- )
        for ( i = k - 1; i > 0; i-- )
        {
            for ( pNodesI = Vec_PtrEntry( vNodes, i ); *pNodesI; pNodesI++ )
            for ( pNodesK = Vec_PtrEntry( vNodes, k ); *pNodesK; pNodesK++ )
            {
                nImpsTried++;
                if ( !Sml_NodeCheckImp(pSeq, *pNodesI, *pNodesK) )
                {
                    nImpsNonSeq++;
                    continue;
                }
                if ( Sml_NodeCheckImp(pComb, *pNodesI, *pNodesK) )
                {
                    nImpsComb++;
                    continue;
                }
//                printf( "d=%d c=%d  ", k-i, Sml_NodeNotImpWeight(pComb, *pNodesI, *pNodesK) );
 
                nImpsCollected++;
                Imp = Sml_ImpCreate( *pNodesI, *pNodesK );
                pImpCosts[ Vec_IntSize(vImps) ] = Sml_NodeNotImpWeight(pComb, *pNodesI, *pNodesK);
                CostMin = AIG_MIN( CostMin, pImpCosts[ Vec_IntSize(vImps) ] );
                CostMax = AIG_MAX( CostMax, pImpCosts[ Vec_IntSize(vImps) ] );
                Vec_IntPush( vImps, Imp );
                if ( Vec_IntSize(vImps) == nImpMaxLimit )
                    goto finish;
            } 
        }
finish:
    Fra_SmlStop( pComb );
    Fra_SmlStop( pSeq );

    // select implications with the highest cost
    CostRange = CostMin;
    if ( Vec_IntSize(vImps) > nImpUseLimit )
    {
        vImps = Fra_SmlSelectMaxCost( vTemp = vImps, pImpCosts, nSimWords * 32, nImpUseLimit, &CostRange );
        Vec_IntFree( vTemp );  
    }

    // dealloc
    free( pImpCosts ); 
    free( Vec_PtrEntry(vNodes, 0) );
    Vec_PtrFree( vNodes );
    // reorder implications topologically
    qsort( (void *)Vec_IntArray(vImps), Vec_IntSize(vImps), sizeof(int), 
            (int (*)(const void *, const void *)) Sml_CompareMaxId );
if ( p->pPars->fVerbose )
{
printf( "Tot = %d. Try = %d. NonS = %d. C = %d. Found = %d.  Cost = [%d < %d < %d] ", 
    nImpsTotal, nImpsTried, nImpsNonSeq, nImpsComb, nImpsCollected, CostMin, CostRange, CostMax );
PRT( "Time", clock() - clk );
}
    return vImps;
}

// the following three procedures are called to 
// - add implications to the SAT solver
// - check implications using the SAT solver
// - refine implications using after a cex is generated

/**Function*************************************************************

  Synopsis    [Add implication clauses to the SAT solver.]

  Description [Note that implications should be checked in the first frame!]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ImpAddToSolver( Fra_Man_t * p, Vec_Int_t * vImps, int * pSatVarNums )
{
    sat_solver * pSat = p->pSat;
    Aig_Obj_t * pLeft, * pRight;
    Aig_Obj_t * pLeftF, * pRightF;
    int pLits[2], Imp, Left, Right, i, f, status;
    int fComplL, fComplR;
    Vec_IntForEachEntry( vImps, Imp, i )
    {
        // get the corresponding nodes
        pLeft = Aig_ManObj( p->pManAig, Sml_ImpLeft(Imp) );
        pRight = Aig_ManObj( p->pManAig, Sml_ImpRight(Imp) );
        // check if all the nodes are present
        for ( f = 0; f < p->pPars->nFramesK; f++ )
        {
            // map these info fraig
            pLeftF = Fra_ObjFraig( pLeft, f );
            pRightF = Fra_ObjFraig( pRight, f );
            if ( Aig_ObjIsNone(Aig_Regular(pLeftF)) || Aig_ObjIsNone(Aig_Regular(pRightF)) )
            {
                Vec_IntWriteEntry( vImps, i, 0 );
                break;
            }
        }
        if ( f < p->pPars->nFramesK )
            continue;
        // add constraints in each timeframe
        for ( f = 0; f < p->pPars->nFramesK; f++ )
        {
            // map these info fraig
            pLeftF = Fra_ObjFraig( pLeft, f );
            pRightF = Fra_ObjFraig( pRight, f );
            // get the corresponding SAT numbers
            Left = pSatVarNums[ Aig_Regular(pLeftF)->Id ];
            Right = pSatVarNums[ Aig_Regular(pRightF)->Id ];
            assert( Left > 0  && Left < p->nSatVars );
            assert( Right > 0 && Right < p->nSatVars );
            // get the complemented attributes
            fComplL = pLeft->fPhase ^ Aig_IsComplement(pLeftF);
            fComplR = pRight->fPhase ^ Aig_IsComplement(pRightF);
            // get the constaint
            // L => R      L' v R     (complement = L & R')
            pLits[0] = 2 * Left  + !fComplL;
            pLits[1] = 2 * Right +  fComplR;
            // add contraint to solver
            if ( !sat_solver_addclause( pSat, pLits, pLits + 2 ) )
            {
                sat_solver_delete( pSat );
                p->pSat = NULL;
                return;
            }
        }
    }
    status = sat_solver_simplify(pSat);
    if ( status == 0 )
    {
        sat_solver_delete( pSat );
        p->pSat = NULL;
    }
//    printf( "Total imps = %d. ", Vec_IntSize(vImps) );
    Fra_ImpCompactArray( vImps );
//    printf( "Valid imps = %d. \n", Vec_IntSize(vImps) );
}

/**Function*************************************************************

  Synopsis    [Check implications for the node (if they are present).]

  Description [Returns the new position in the array.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ImpCheckForNode( Fra_Man_t * p, Vec_Int_t * vImps, Aig_Obj_t * pNode, int Pos )
{
    Aig_Obj_t * pLeft, * pRight;
    Aig_Obj_t * pLeftF, * pRightF;
    int i, Imp, Left, Right, Max;
    int fComplL, fComplR;
    Vec_IntForEachEntryStart( vImps, Imp, i, Pos )
    {
        if ( Imp == 0 )
            continue;
        Left = Sml_ImpLeft(Imp);
        Right = Sml_ImpRight(Imp);
        Max = AIG_MAX( Left, Right );
        assert( Max >= pNode->Id );
        if ( Max > pNode->Id )
            return i;
        // get the corresponding nodes
        pLeft  = Aig_ManObj( p->pManAig, Left );
        pRight = Aig_ManObj( p->pManAig, Right );
        // get the corresponding FRAIG nodes
        pLeftF  = Fra_ObjFraig( pLeft, p->pPars->nFramesK );
        pRightF = Fra_ObjFraig( pRight, p->pPars->nFramesK );
        // get the complemented attributes
        fComplL = pLeft->fPhase ^ Aig_IsComplement(pLeftF);
        fComplR = pRight->fPhase ^ Aig_IsComplement(pRightF);
        // check equality
        if ( Aig_Regular(pLeftF) == Aig_Regular(pRightF) )
        {
//            assert( fComplL == fComplR );
//            if ( fComplL != fComplR )
//                printf( "Fra_ImpCheckForNode(): Unexpected situation!\n" );
            if ( fComplL != fComplR )
                Vec_IntWriteEntry( vImps, i, 0 );
            continue;
        }
        // check the implication 
        // - if true, a clause is added
        // - if false, a cex is simulated
        // make sure the implication is refined
        if ( Fra_NodesAreImp( p, Aig_Regular(pLeftF), Aig_Regular(pRightF), fComplL, fComplR ) == 0 )
        {
            Fra_SmlResimulate( p );
            if ( Vec_IntEntry(vImps, i) != 0 )
                printf( "Fra_ImpCheckForNode(): Implication is not refined!\n" );
            assert( Vec_IntEntry(vImps, i) == 0 );
        }
    }
    return i;
}

/**Function*************************************************************

  Synopsis    [Removes those implications that no longer hold.]

  Description [Returns 1 if refinement has happened.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_ImpRefineUsingCex( Fra_Man_t * p, Vec_Int_t * vImps )
{
    Aig_Obj_t * pLeft, * pRight;
    int Imp, i, RetValue = 0;
    Vec_IntForEachEntry( vImps, Imp, i )
    {
        if ( Imp == 0 )
            continue;
        // get the corresponding nodes
        pLeft = Aig_ManObj( p->pManAig, Sml_ImpLeft(Imp) );
        pRight = Aig_ManObj( p->pManAig, Sml_ImpRight(Imp) );
        // check if implication holds using this simulation info
        if ( !Sml_NodeCheckImp(p->pSml, pLeft->Id, pRight->Id) )
        {
            Vec_IntWriteEntry( vImps, i, 0 );
            RetValue = 1;
        }
    }
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Removes empty implications.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ImpCompactArray( Vec_Int_t * vImps )
{
    int i, k, Imp;
    k = 0;
    Vec_IntForEachEntry( vImps, Imp, i )
        if ( Imp )
            Vec_IntWriteEntry( vImps, k++, Imp );
    Vec_IntShrink( vImps, k );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


