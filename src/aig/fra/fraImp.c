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

// simulation manager
typedef struct Sml_Man_t_   Sml_Man_t;
struct Sml_Man_t_
{
    Aig_Man_t *      pAig;
    int              nFrames;
    int              nWordsFrame;
    int              nWordsTotal;
    unsigned         pData[0];
};

static inline unsigned * Sml_ObjSim( Sml_Man_t * p, int Id )  { return p->pData + p->nWordsTotal * Id; }
static inline int        Sml_ImpLeft( int Imp )               { return Imp & 0xFFFF;                   }
static inline int        Sml_ImpRight( int Imp )              { return Imp >> 16;                      }
static inline int        Sml_ImpCreate( int Left, int Right ) { return (Right << 16) | Left;           }

static int * s_ImpCost = NULL;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates simulation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sml_Man_t * Sml_ManStart( Aig_Man_t * pAig, int nFrames, int nWordsFrame )
{
    Sml_Man_t * p;
    assert( Aig_ManObjIdMax(pAig) + 1 < (1 << 16) );
    p = (Sml_Man_t *)malloc( sizeof(Sml_Man_t) + sizeof(unsigned) * (Aig_ManObjIdMax(pAig) + 1) * nFrames * nWordsFrame );
    memset( p, 0, sizeof(Sml_Man_t) + sizeof(unsigned) * nFrames * nWordsFrame );
    p->nFrames     = nFrames;
    p->nWordsFrame = nWordsFrame;
    p->nWordsTotal = nFrames * nWordsFrame;
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates simulation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sml_ManStop( Sml_Man_t * p )
{
    free( p );
}


/**Function*************************************************************

  Synopsis    [Assigns random patterns to the PI node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sml_ManAssignRandom( Sml_Man_t * p, Aig_Obj_t * pObj )
{
    unsigned * pSims;
    int i;
    assert( Aig_ObjIsPi(pObj) );
    pSims = Sml_ObjSim( p, pObj->Id );
    for ( i = 0; i < p->nWordsTotal; i++ )
        pSims[i] = Fra_ObjRandomSim();
}

/**Function*************************************************************

  Synopsis    [Assigns constant patterns to the PI node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sml_ManAssignConst( Sml_Man_t * p, Aig_Obj_t * pObj, int fConst1, int iFrame )
{
    unsigned * pSims;
    int i;
    assert( Aig_ObjIsPi(pObj) );
    pSims = Sml_ObjSim( p, pObj->Id ) + p->nWordsFrame * iFrame;
    for ( i = 0; i < p->nWordsFrame; i++ )
        pSims[i] = fConst1? ~(unsigned)0 : 0;
}

/**Function*************************************************************

  Synopsis    [Assings random simulation info for the PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sml_ManInitialize( Sml_Man_t * p, int fInit )
{
    Aig_Obj_t * pObj;
    int i;
    if ( fInit )
    {
        assert( Aig_ManRegNum(p->pAig) > 0 );
        assert( Aig_ManRegNum(p->pAig) < Aig_ManPiNum(p->pAig) );
        // assign random info for primary inputs
        Aig_ManForEachPiSeq( p->pAig, pObj, i )
            Sml_ManAssignRandom( p, pObj );
        // assign the initial state for the latches
        Aig_ManForEachLoSeq( p->pAig, pObj, i )
            Sml_ManAssignConst( p, pObj, 0, 0 );
    }
    else
    {
        Aig_ManForEachPi( p->pAig, pObj, i )
            Sml_ManAssignRandom( p, pObj );
    }
}

/**Function*************************************************************

  Synopsis    [Assings distance-1 simulation info for the PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sml_ManAssignDist1( Sml_Man_t * p, unsigned * pPat )
{
    Aig_Obj_t * pObj;
    int f, i, k, Limit, nTruePis;
    assert( p->nFrames > 0 );
    if ( p->nFrames == 1 )
    {
        // copy the PI info 
        Aig_ManForEachPi( p->pAig, pObj, i )
            Sml_ManAssignConst( p, pObj, Aig_InfoHasBit(pPat, i), 0 );
        // flip one bit
        Limit = AIG_MIN( Aig_ManPiNum(p->pAig), p->nWordsTotal * 32 - 1 );
        for ( i = 0; i < Limit; i++ )
            Aig_InfoXorBit( Sml_ObjSim( p, Aig_ManPi(p->pAig,i)->Id ), i+1 );
    }
    else
    {
        // copy the PI info for each frame
        nTruePis = Aig_ManPiNum(p->pAig) - Aig_ManRegNum(p->pAig);
        for ( f = 0; f < p->nFrames; f++ )
            Aig_ManForEachPiSeq( p->pAig, pObj, i )
                Sml_ManAssignConst( p, pObj, Aig_InfoHasBit(pPat, nTruePis * f + i), f );
        // copy the latch info 
        k = 0;
        Aig_ManForEachLoSeq( p->pAig, pObj, i )
            Sml_ManAssignConst( p, pObj, Aig_InfoHasBit(pPat, nTruePis * p->nFrames + k++), 0 );
//        assert( p->pManFraig == NULL || nTruePis * p->nFrames + k == Aig_ManPiNum(p->pManFraig) );

        // flip one bit of the last frame
        if ( p->nFrames == 2 )
        {
            Limit = AIG_MIN( nTruePis, p->nWordsFrame * 32 - 1 );
            for ( i = 0; i < Limit; i++ )
                Aig_InfoXorBit( Sml_ObjSim( p, Aig_ManPi(p->pAig, i)->Id ), i+1 );
//            Aig_InfoXorBit( Sml_ObjSim( p, Aig_ManPi(p->pAig, nTruePis*(p->nFrames-2) + i)->Id ), i+1 );
        }
    }
}


/**Function*************************************************************

  Synopsis    [Simulates one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sml_NodeSimulate( Sml_Man_t * p, Aig_Obj_t * pObj, int iFrame )
{
    unsigned * pSims, * pSims0, * pSims1;
    int fCompl, fCompl0, fCompl1, i;
    int nSimWords = p->nWordsFrame;
    assert( !Aig_IsComplement(pObj) );
    assert( Aig_ObjIsNode(pObj) );
    assert( iFrame == 0 || nSimWords < p->nWordsTotal );
    // get hold of the simulation information
    pSims  = Fra_ObjSim(pObj) + nSimWords * iFrame;
    pSims0 = Fra_ObjSim(Aig_ObjFanin0(pObj)) + nSimWords * iFrame;
    pSims1 = Fra_ObjSim(Aig_ObjFanin1(pObj)) + nSimWords * iFrame;
    // get complemented attributes of the children using their random info
    fCompl  = pObj->fPhase;
    fCompl0 = Aig_ObjPhaseReal(Aig_ObjChild0(pObj));
    fCompl1 = Aig_ObjPhaseReal(Aig_ObjChild1(pObj));
    // simulate
    if ( fCompl0 && fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < nSimWords; i++ )
                pSims[i] = (pSims0[i] | pSims1[i]);
        else
            for ( i = 0; i < nSimWords; i++ )
                pSims[i] = ~(pSims0[i] | pSims1[i]);
    }
    else if ( fCompl0 && !fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < nSimWords; i++ )
                pSims[i] = (pSims0[i] | ~pSims1[i]);
        else
            for ( i = 0; i < nSimWords; i++ )
                pSims[i] = (~pSims0[i] & pSims1[i]);
    }
    else if ( !fCompl0 && fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < nSimWords; i++ )
                pSims[i] = (~pSims0[i] | pSims1[i]);
        else
            for ( i = 0; i < nSimWords; i++ )
                pSims[i] = (pSims0[i] & ~pSims1[i]);
    }
    else // if ( !fCompl0 && !fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < nSimWords; i++ )
                pSims[i] = ~(pSims0[i] & pSims1[i]);
        else
            for ( i = 0; i < nSimWords; i++ )
                pSims[i] = (pSims0[i] & pSims1[i]);
    }
}

/**Function*************************************************************

  Synopsis    [Simulates one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sml_NodeCopyFanin( Sml_Man_t * p, Aig_Obj_t * pObj, int iFrame )
{
    unsigned * pSims, * pSims0;
    int fCompl, fCompl0, i;
    int nSimWords = p->nWordsFrame;
    assert( !Aig_IsComplement(pObj) );
    assert( Aig_ObjIsPo(pObj) );
    assert( iFrame == 0 || nSimWords < p->nWordsTotal );
    // get hold of the simulation information
    pSims  = Sml_ObjSim(p, pObj->Id) + nSimWords * iFrame;
    pSims0 = Sml_ObjSim(p, Aig_ObjFanin0(pObj)->Id) + nSimWords * iFrame;
    // get complemented attributes of the children using their random info
    fCompl  = pObj->fPhase;
    fCompl0 = Aig_ObjPhaseReal(Aig_ObjChild0(pObj));
    // copy information as it is
    if ( fCompl0 )
        for ( i = 0; i < nSimWords; i++ )
            pSims[i] = ~pSims0[i];
    else
        for ( i = 0; i < nSimWords; i++ )
            pSims[i] = pSims0[i];
}

/**Function*************************************************************

  Synopsis    [Simulates one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sml_NodeTransferNext( Sml_Man_t * p, Aig_Obj_t * pOut, Aig_Obj_t * pIn, int iFrame )
{
    unsigned * pSims0, * pSims1;
    int i, nSimWords = p->nWordsFrame;
    assert( !Aig_IsComplement(pOut) );
    assert( !Aig_IsComplement(pIn) );
    assert( Aig_ObjIsPo(pOut) );
    assert( Aig_ObjIsPi(pIn) );
    assert( iFrame == 0 || nSimWords < p->nWordsTotal );
    // get hold of the simulation information
    pSims0 = Sml_ObjSim(p, pOut->Id) + nSimWords * iFrame;
    pSims1 = Sml_ObjSim(p, pIn->Id) + nSimWords * (iFrame+1);
    // copy information as it is
    for ( i = 0; i < nSimWords; i++ )
        pSims1[i] = pSims0[i];
}


/**Function*************************************************************

  Synopsis    [Simulates AIG manager.]

  Description [Assumes that the PI simulation info is attached.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sml_SimulateOne( Sml_Man_t * p )
{
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int f, i, clk;
clk = clock();
    for ( f = 0; f < p->nFrames; f++ )
    {
        // simulate the nodes
        Aig_ManForEachNode( p->pAig, pObj, i )
            Sml_NodeSimulate( p, pObj, f );
        if ( f == p->nFrames - 1 )
            break;
        // copy simulation info into outputs
        Aig_ManForEachLiSeq( p->pAig, pObj, i )
            Sml_NodeCopyFanin( p, pObj, f );
        // copy simulation info into the inputs
//        for ( i = 0; i < Aig_ManRegNum(p->pAig); i++ )
//            Sml_NodeTransferNext( p, Aig_ManLi(p->pAig, i), Aig_ManLo(p->pAig, i), f );
        Aig_ManForEachLiLoSeq( p->pAig, pObjLi, pObjLo, i )
            Sml_NodeTransferNext( p, pObjLi, pObjLo, f );
    }
//p->timeSim += clock() - clk;
//p->nSimRounds++;
}

/**Function*************************************************************

  Synopsis    [Performs simulation of the uninitialized circuit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sml_Man_t * Sml_ManSimulateComb( Aig_Man_t * pAig, int nWords )
{
    Sml_Man_t * p;
    p = Sml_ManStart( pAig, 1, nWords );
    Sml_ManInitialize( p, 0 );
    Sml_SimulateOne( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Performs simulation of the initialized circuit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sml_Man_t * Sml_ManSimulateSeq( Aig_Man_t * pAig, int nFrames, int nWords )
{
    Sml_Man_t * p;
    p = Sml_ManStart( pAig, nFrames, nWords );
    Sml_ManInitialize( p, 1 );
    Sml_SimulateOne( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Counts the number of 1s in each siminfo of each node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Sml_ManCountOnes( Sml_Man_t * p )
{
    Aig_Obj_t * pObj;
    unsigned * pSim;
    int i, k, * pnBits; 
    pnBits = ALLOC( int, Aig_ManObjIdMax(p->pAig) + 1 );  
    memset( pnBits, 0, sizeof(int) * Aig_ManObjIdMax(p->pAig) + 1 );
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        pSim = Sml_ObjSim( p, i );
        for ( k = 0; k < p->nWordsTotal; k++ )
            pnBits[i] += Aig_WordCountOnes( pSim[k] );
    }
    return pnBits;
}

/**Function*************************************************************

  Synopsis    [Counts the number of 1s in the reverse implication.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sml_NodeNotImpCost( Sml_Man_t * p, int Left, int Right )
{
    unsigned * pSimL, * pSimR;
    int k, Counter = 0;
    pSimL = Sml_ObjSim( p, Left );
    pSimR = Sml_ObjSim( p, Right );
    for ( k = 0; k < p->nWordsTotal; k++ )
        Counter += Aig_WordCountOnes( pSimL[k] & ~pSimR[k] );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if implications holds.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sml_NodeCheckImp( Sml_Man_t * p, int Left, int Right )
{
    unsigned * pSimL, * pSimR;
    int k;
    pSimL = Sml_ObjSim( p, Left );
    pSimR = Sml_ObjSim( p, Right );
    for ( k = 0; k < p->nWordsTotal; k++ )
        if ( pSimL[k] & ~pSimR[k] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the array of nodes sorted by the number of 1s.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Sml_ManSortUsingOnes( Sml_Man_t * p )
{
    Aig_Obj_t * pObj;
    Vec_Ptr_t * vNodes;
    int i, nNodes, nTotal, nBits, * pnNodes, * pnBits, * pMemory;
    // count 1s in each node's siminfo
    pnBits = Sml_ManCountOnes( p );
    // count number of nodes having that many 1s
    nBits = p->nWordsTotal * 32;
    assert( nBits >= 32 );
    nNodes = 0;
    pnNodes = ALLOC( int, nBits );
    memset( pnNodes, 0, sizeof(int) * nBits );
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( i == 0 ) continue;
        assert( pnBits[i] < nBits ); // "<" because of normalized info
        pnNodes[pnBits[i]]++;
        nNodes++;
    }
    // allocate memory for all the nodes
    pMemory = ALLOC( int, nNodes + nBits );  
    // markup the memory for each node
    vNodes = Vec_PtrAlloc( nBits );
    Vec_PtrPush( vNodes, pMemory );
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( i == 0 ) continue;
        pMemory += pnBits[i-1] + 1;
        Vec_PtrPush( vNodes, pMemory );
    }
    // add the nodes
    memset( pnNodes, 0, sizeof(int) * nBits );
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( i == 0 ) continue;
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
    assert( nTotal == nNodes + nBits );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Compares two implications using their cost.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sml_CompareCost( int * pNum1, int * pNum2 )
{
    int Cost1 = s_ImpCost[*pNum1];
    int Cost2 = s_ImpCost[*pNum2];
    if ( Cost1 > Cost2 )
        return -1;
    if ( Cost1 < Cost2  )
        return 1;
    return 0; 
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
      - this means they are relatively far in terms of Humming distance
        meaning their complement covers a larger Boolean space
      - they are easy to disprove combinationally
        meaning they cover relatively a larger sequential subspace.]
               
  SideEffects [The managers should have the first pattern (000...)]

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Sml_ManImpDerive( Fra_Man_t * p, int nImpMaxLimit, int nImpUseLimit )
{
    Sml_Man_t * pSeq, * pComb;
    Vec_Int_t * vImps, * vTemp;
    Vec_Ptr_t * vNodes;
    int * pNodesI, * pNodesK, * pNumbers;
    int i, k, Imp;
    assert( nImpMaxLimit > 0 && nImpUseLimit > 0 && nImpUseLimit <= nImpMaxLimit );
    // normalize both managers
    pComb = Sml_ManSimulateComb( p->pManAig, 32 );
    pSeq = Sml_ManSimulateSeq( p->pManAig, 32, 1 );
    // get the nodes sorted by the number of 1s
    vNodes = Sml_ManSortUsingOnes( pSeq );
    // compute implications and their costs
    s_ImpCost = ALLOC( int, nImpMaxLimit );
    vImps = Vec_IntAlloc( nImpMaxLimit );
    for ( k = pSeq->nWordsTotal * 32 - 1; k >= 0; k-- )
        for ( i = k - 1; i >= 0; i-- )
        {
            for ( pNodesI = Vec_PtrEntry( vNodes, i ); *pNodesI; pNodesI++ )
            for ( pNodesK = Vec_PtrEntry( vNodes, k ); *pNodesK; pNodesK++ )
            {
                if ( Sml_NodeCheckImp(pSeq, *pNodesI, *pNodesK) &&
                    !Sml_NodeCheckImp(pComb, *pNodesI, *pNodesK) )
                {
                    Imp = Sml_ImpCreate( *pNodesI, *pNodesK );
                    s_ImpCost[ Vec_IntSize(vImps) ] = Sml_NodeNotImpCost(pComb, *pNodesI, *pNodesK);
                    Vec_IntPush( vImps, Imp );
                }
                if ( Vec_IntSize(vImps) == nImpMaxLimit )
                    goto finish;
            }
        }
finish:
    Sml_ManStop( pComb );
    Sml_ManStop( pSeq );

    // sort implications by their cost
    pNumbers = ALLOC( int, Vec_IntSize(vImps) );
    for ( i = 0; i < Vec_IntSize(vImps); i++ )
        pNumbers[i] = i;
    qsort( (void *)pNumbers, Vec_IntSize(vImps), sizeof(int), 
            (int (*)(const void *, const void *)) Sml_CompareCost );
    // reorder implications
    vTemp = Vec_IntAlloc( nImpUseLimit );
    for ( i = 0; i < nImpUseLimit; i++ )
        Vec_IntPush( vTemp, Vec_IntEntry( vImps, pNumbers[i] ) );
    Vec_IntFree( vImps );  vImps = vTemp;
    // dealloc
    free( pNumbers );
    free( s_ImpCost ); s_ImpCost = NULL;
    free( Vec_PtrEntry(vNodes, 0) );
    Vec_PtrFree( vNodes );
    // order implications by the max ID involved
    qsort( (void *)Vec_IntArray(vImps), Vec_IntSize(vImps), sizeof(int), 
            (int (*)(const void *, const void *)) Sml_CompareMaxId );
    return vImps;
}

// the following three procedures are called to 
// - add implications to the SAT solver
// - check implications using the SAT solver
// - refine implications using after a cex is generated

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ImpAddToSolver( Fra_Man_t * p, Vec_Int_t * vImps )
{
    sat_solver * pSat = p->pSat;
    Aig_Obj_t * pLeft, * pRight;
    Aig_Obj_t * pLeftF, * pRightF;
    int pLits[2], Imp, Left, Right, i, f, status;
    Vec_IntForEachEntry( vImps, Imp, i )
    {
        // get the corresponding nodes
        pLeft = Aig_ManObj( p->pManAig, Sml_ImpLeft(Imp) );
        pRight = Aig_ManObj( p->pManAig, Sml_ImpRight(Imp) );
        // add constraints in each timeframe
        for ( f = 0; f < p->pPars->nFramesK; f++ )
        {
            // map these info fraig
            pLeftF = Fra_ObjFraig( pLeft, f );
            pRightF = Fra_ObjFraig( pRight, f );
            // get the corresponding SAT numbers
            Left = Fra_ObjSatNum( Aig_Regular(pLeftF) );
            Right = Fra_ObjSatNum( Aig_Regular(pRightF) );
            assert( Left > 0  && Left < p->nSatVars );
            assert( Right > 0 && Right < p->nSatVars );
            // get the constaint
            // L => R      L' v R      L & R'
            pLits[0] = 2 * Left  + !Aig_ObjPhaseReal(pLeftF);
            pLits[1] = 2 * Right +  Aig_ObjPhaseReal(pRightF);
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
    int i, Imp, Left, Right, Max;
    Vec_IntForEachEntryStart( vImps, Imp, i, Pos )
    {
        Left = Sml_ImpLeft(Imp);
        Right = Sml_ImpRight(Imp);
        Max = AIG_MAX( Left, Right );
        assert( Max >= pNode->Id );
        if ( Max > pNode->Id )
            return i;
        // get the corresponding nodes
        pLeft = Aig_ManObj( p->pManAig, Left );
        pRight = Aig_ManObj( p->pManAig, Right );
        // check the implication 
        // - if true, a clause is added
        // - if false, a cex is simulated
//        Fra_NodesAreImp( p, pLeft, pRight );
        // make sure the implication is refined
        assert( Vec_IntEntry(vImps, Pos) == 0 );
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
        if ( !Sml_NodeCheckImp(p->pSim, pLeft->Id, pRight->Id) )
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


