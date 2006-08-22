/**CFile****************************************************************

  FileName    [abcVanImp.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Implementation of van Eijk's method for implications.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 2, 2005.]

  Revision    [$Id: abcVanImp.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "fraig.h"
#include "sim.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Van_Man_t_ Van_Man_t;
struct Van_Man_t_
{
    // single frame representation
    Abc_Ntk_t *      pNtkSingle;    // single frame
    Vec_Int_t *      vCounters;     // the counters of 1s in the simulation info
    Vec_Ptr_t *      vZeros;        // the set of constant 0 candidates
    Vec_Int_t *      vImps;         // the set of all implications
    Vec_Int_t *      vImpsMis;      // the minimum independent set of implications
    // multiple frame representation
    Abc_Ntk_t *      pNtkMulti;     // multiple frame
    Vec_Ptr_t *      vCorresp;      // the correspondence between single frame and multiple frames
    // parameters
    int              nFrames;       // the number of timeframes
    int              nWords;        // the number of simulation words
    int              nIdMax;        // the maximum ID in the single frame
    int              fVerbose;      // the verbosiness flag
    // statistics
    int              nPairsAll;
    int              nImpsAll;
    int              nEquals;
    int              nZeros;
    // runtime
    int              timeAll;
    int              timeSim;
    int              timeAdd;
    int              timeCheck;
    int              timeInfo;
    int              timeMis;
};

static void           Abc_NtkVanImpCompute( Van_Man_t * p );
static Vec_Ptr_t *    Abc_NtkVanImpSortByOnes( Van_Man_t * p );
static void           Abc_NtkVanImpComputeAll( Van_Man_t * p );
static Vec_Int_t *    Abc_NtkVanImpComputeMis( Van_Man_t * p );
static void           Abc_NtkVanImpManFree( Van_Man_t * p );
static void           Abc_NtkVanImpFilter( Van_Man_t * p, Fraig_Man_t * pFraig, Vec_Ptr_t * vZeros, Vec_Int_t * vImps );
static int            Abc_NtkVanImpCountEqual( Van_Man_t * p );

static Abc_Ntk_t *    Abc_NtkVanImpDeriveExdc( Abc_Ntk_t * pNtk, Vec_Ptr_t * vZeros, Vec_Int_t * vImps );

extern Abc_Ntk_t *    Abc_NtkVanEijkFrames( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCorresp, int nFrames, int fAddLast, int fShortNames );
extern void           Abc_NtkVanEijkAddFrame( Abc_Ntk_t * pNtkFrames, Abc_Ntk_t * pNtk, int iFrame, Vec_Ptr_t * vCorresp, Vec_Ptr_t * vOrder, int fShortNames );
extern Fraig_Man_t *  Abc_NtkVanEijkFraig( Abc_Ntk_t * pMulti, int fInit );

////////////////////////////////////////////////////////////////////////
///                     INLINED FUNCTIONS                            ///
////////////////////////////////////////////////////////////////////////

// returns the correspondence of the node in the frame
static inline Abc_Obj_t * Abc_NodeVanImpReadCorresp( Abc_Obj_t * pNode, Vec_Ptr_t * vCorresp, int iFrame ) 
{
    return Vec_PtrEntry( vCorresp, iFrame * Abc_NtkObjNumMax(pNode->pNtk) + pNode->Id ); 
}
// returns the left node of the implication
static inline Abc_Obj_t * Abc_NodeVanGetLeft( Abc_Ntk_t * pNtk, unsigned Imp ) 
{
    return Abc_NtkObj( pNtk, Imp >> 16 );
}
// returns the right node of the implication
static inline Abc_Obj_t * Abc_NodeVanGetRight( Abc_Ntk_t * pNtk, unsigned Imp ) 
{
    return Abc_NtkObj( pNtk, Imp & 0xFFFF );
}
// returns the implication
static inline unsigned Abc_NodeVanGetImp( Abc_Obj_t * pLeft, Abc_Obj_t * pRight ) 
{
    return (pLeft->Id << 16) | pRight->Id;
}
// returns the right node of the implication
static inline void Abc_NodeVanPrintImp( unsigned Imp ) 
{
    printf( "%d -> %d  ", Imp >> 16, Imp & 0xFFFF );
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derives implications that hold sequentially.]

  Description [Adds EXDC network to the current network to record the 
  set of computed sequentially equivalence implications, representing
  a subset of unreachable states.]
               
  SideEffects []
 
  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkVanImp( Abc_Ntk_t * pNtk, int nFrames, int fExdc, int fVerbose )
{
    Fraig_Params_t Params;
    Abc_Ntk_t * pNtkNew;
    Van_Man_t * p;

    assert( Abc_NtkIsStrash(pNtk) );

    // start the manager
    p = ALLOC( Van_Man_t, 1 );
    memset( p, 0, sizeof(Van_Man_t) );
    p->nFrames  = nFrames;
    p->fVerbose = fVerbose;
    p->vCorresp = Vec_PtrAlloc( 100 );

    // FRAIG the network to get rid of combinational equivalences
    Fraig_ParamsSetDefaultFull( &Params );
    p->pNtkSingle = Abc_NtkFraig( pNtk, &Params, 0, 0 );
    p->nIdMax     = Abc_NtkObjNumMax( p->pNtkSingle );
    Abc_AigSetNodePhases( p->pNtkSingle );
    Abc_NtkCleanNext( p->pNtkSingle );
//    if ( fVerbose )
//        printf( "The number of ANDs in 1 timeframe  = %d.\n", Abc_NtkNodeNum(p->pNtkSingle) );

    // derive multiple time-frames and node correspondence (to be used in the inductive case)
    p->pNtkMulti = Abc_NtkVanEijkFrames( p->pNtkSingle, p->vCorresp, nFrames, 1, 0 );
//    if ( fVerbose )
//        printf( "The number of ANDs in %d timeframes = %d.\n", nFrames + 1, Abc_NtkNodeNum(p->pNtkMulti) );

    // get the implications
    Abc_NtkVanImpCompute( p );

    // create the new network with EXDC correspondingn to the computed implications
    if ( fExdc && (Vec_PtrSize(p->vZeros) > 0 || Vec_IntSize(p->vImpsMis) > 0) )
    {
        if ( p->pNtkSingle->pExdc )
        {
            printf( "The old EXDC network is thrown away.\n" );
            Abc_NtkDelete( p->pNtkSingle->pExdc );
            p->pNtkSingle->pExdc = NULL;
        }
        pNtkNew = Abc_NtkDup( p->pNtkSingle );  
        pNtkNew->pExdc = Abc_NtkVanImpDeriveExdc( p->pNtkSingle, p->vZeros, p->vImpsMis );
    }
    else
        pNtkNew = Abc_NtkDup( p->pNtkSingle );  

    // free stuff
    Abc_NtkVanImpManFree( p );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Frees the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVanImpManFree( Van_Man_t * p )
{
    Abc_NtkDelete( p->pNtkMulti );
    Abc_NtkDelete( p->pNtkSingle );
    Vec_PtrFree( p->vCorresp );
    Vec_PtrFree( p->vZeros );
    Vec_IntFree( p->vCounters );
    Vec_IntFree( p->vImpsMis );
    Vec_IntFree( p->vImps );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Derives the minimum independent set of sequential implications.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVanImpCompute( Van_Man_t * p )
{
    Fraig_Man_t * pFraig;
    Vec_Ptr_t * vZeros;
    Vec_Int_t * vImps, * vImpsTemp;
    int nIters, clk;

    // compute all implications and count 1s in the simulation info
clk = clock();
    Abc_NtkVanImpComputeAll( p );
p->timeAll += clock() - clk;

    // compute the MIS
clk = clock();
    p->vImpsMis = Abc_NtkVanImpComputeMis( p );
p->timeMis += clock() - clk;

    if ( p->fVerbose )
    {
        printf( "Pairs = %8d. Imps = %8d. Seq = %7d. MIS = %7d. Equ = %5d. Const = %5d.\n", 
            p->nPairsAll, p->nImpsAll, Vec_IntSize(p->vImps), Vec_IntSize(p->vImpsMis), p->nEquals, p->nZeros );
        PRT( "Visiting all nodes pairs while preparing for the inductive case", p->timeAll );
        printf( "Start    :  Seq = %7d.  MIS = %7d.  Const = %5d.\n", Vec_IntSize(p->vImps), Vec_IntSize(p->vImpsMis), Vec_PtrSize(p->vZeros) );
    }

    // iterate to perform the iterative filtering of implications
    for ( nIters = 1; Vec_PtrSize(p->vZeros) > 0 || Vec_IntSize(p->vImps) > 0; nIters++ )
    {
        // FRAIG the ununitialized frames
        pFraig = Abc_NtkVanEijkFraig( p->pNtkMulti, 0 );

        // assuming that zeros and imps hold in the first k-1 frames 
        // check if they hold in the k-th frame
        vZeros = Vec_PtrAlloc( 100 );
        vImps = Vec_IntAlloc( 100 );
        Abc_NtkVanImpFilter( p, pFraig, vZeros, vImps );
        Fraig_ManFree( pFraig );

clk = clock();
        vImpsTemp = p->vImps;
        p->vImps = vImps;
        Vec_IntFree( p->vImpsMis );
        p->vImpsMis = Abc_NtkVanImpComputeMis( p );
        p->vImps = vImpsTemp;
p->timeMis += clock() - clk;

        // report the results
        if ( p->fVerbose )
            printf( "Iter = %2d:  Seq = %7d.  MIS = %7d.  Const = %5d.\n", nIters, Vec_IntSize(vImps), Vec_IntSize(p->vImpsMis), Vec_PtrSize(vZeros) );

        // if the fixed point is reaches, quit the loop
        if ( Vec_PtrSize(vZeros) == Vec_PtrSize(p->vZeros) && Vec_IntSize(vImps) == Vec_IntSize(p->vImps) )
        { // no change
            Vec_PtrFree(vZeros);
            Vec_IntFree(vImps);
            break;
        }

        // update the sets
        Vec_PtrFree( p->vZeros );  p->vZeros = vZeros;
        Vec_IntFree( p->vImps );   p->vImps  = vImps;
    }

    // compute the MIS
clk = clock();
    Vec_IntFree( p->vImpsMis );
    p->vImpsMis = Abc_NtkVanImpComputeMis( p );
//    p->vImpsMis = Vec_IntDup( p->vImps );
p->timeMis += clock() - clk;
    if ( p->fVerbose )
        printf( "Final    :  Seq = %7d.  MIS = %7d.  Const = %5d.\n", Vec_IntSize(p->vImps), Vec_IntSize(p->vImpsMis), Vec_PtrSize(p->vZeros) );


/*
    if ( p->fVerbose )
    {
        PRT( "All   ", p->timeAll   );
        PRT( "Sim   ", p->timeSim   );
        PRT( "Add   ", p->timeAdd   );
        PRT( "Check ", p->timeCheck );
        PRT( "Mis   ", p->timeMis   );
    }
*/

/*
    // print the implications in the MIS
    if ( p->fVerbose )
    {
        Abc_Obj_t * pNode, * pNode1, * pNode2;
        unsigned Imp;
        int i;
        if ( Vec_PtrSize(p->vZeros) )
        {
            printf( "The const nodes are: " );
            Vec_PtrForEachEntry( p->vZeros, pNode, i )
                printf( "%d(%d) ", pNode->Id, pNode->fPhase );
            printf( "\n" );
        }
        if ( Vec_IntSize(p->vImpsMis) )
        {
            printf( "The implications are: " );
            Vec_IntForEachEntry( p->vImpsMis, Imp, i )
            {
                pNode1  = Abc_NodeVanGetLeft( p->pNtkSingle, Imp );
                pNode2  = Abc_NodeVanGetRight( p->pNtkSingle, Imp );
                printf( "%d(%d)=>%d(%d) ", pNode1->Id, pNode1->fPhase, pNode2->Id, pNode2->fPhase );
            }
            printf( "\n" );
        }
    }
*/
}

/**Function*************************************************************

  Synopsis    [Filters zeros and implications by performing one inductive step.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVanImpFilter( Van_Man_t * p, Fraig_Man_t * pFraig, Vec_Ptr_t * vZeros, Vec_Int_t * vImps )
{
    ProgressBar * pProgress;
    Abc_Obj_t * pNode, * pNodeM1, * pNodeM2, * pNode1, * pNode2, * pObj;
    Fraig_Node_t * pFNode1, * pFNode2;
    Fraig_Node_t * ppFNodes[2];
    unsigned Imp;
    int i, f, k, clk;

clk = clock();
    for ( f = 0; f < p->nFrames; f++ )
    {
        // add new clauses for zeros
        Vec_PtrForEachEntry( p->vZeros, pNode, i )
        {
            pNodeM1 = Abc_NodeVanImpReadCorresp( pNode, p->vCorresp, f );
            pFNode1 = Fraig_NotCond( Abc_ObjRegular(pNodeM1)->pCopy, Abc_ObjIsComplement(pNodeM1) );
            pFNode1 = Fraig_NotCond( pFNode1, !pNode->fPhase );
            Fraig_ManAddClause( pFraig, &pFNode1, 1 );
        }
        // add new clauses for imps
        Vec_IntForEachEntry( p->vImps, Imp, i )
        {
            pNode1  = Abc_NodeVanGetLeft( p->pNtkSingle, Imp );
            pNode2  = Abc_NodeVanGetRight( p->pNtkSingle, Imp );
            pNodeM1 = Abc_NodeVanImpReadCorresp( pNode1, p->vCorresp, f );
            pNodeM2 = Abc_NodeVanImpReadCorresp( pNode2, p->vCorresp, f );
            pFNode1 = Fraig_NotCond( Abc_ObjRegular(pNodeM1)->pCopy, Abc_ObjIsComplement(pNodeM1) );
            pFNode2 = Fraig_NotCond( Abc_ObjRegular(pNodeM2)->pCopy, Abc_ObjIsComplement(pNodeM2) );
            ppFNodes[0] = Fraig_NotCond( pFNode1, !pNode1->fPhase );
            ppFNodes[1] = Fraig_NotCond( pFNode2,  pNode2->fPhase );
//            assert( Fraig_Regular(ppFNodes[0]) != Fraig_Regular(ppFNodes[1]) );
            Fraig_ManAddClause( pFraig, ppFNodes, 2 );
        }
    }
p->timeAdd += clock() - clk;

    // check the zero nodes
clk = clock();
    Vec_PtrClear( vZeros );
    Vec_PtrForEachEntry( p->vZeros, pNode, i )
    {
        pNodeM1 = Abc_NodeVanImpReadCorresp( pNode, p->vCorresp, p->nFrames );
        pFNode1 = Fraig_NotCond( Abc_ObjRegular(pNodeM1)->pCopy, Abc_ObjIsComplement(pNodeM1) );
        pFNode1 = Fraig_Regular(pFNode1);
        pFNode2 = Fraig_ManReadConst1(pFraig);
        if ( pFNode1 == pFNode2 || Fraig_NodeIsEquivalent( pFraig, pFNode1, pFNode2, -1, 100 ) )
            Vec_PtrPush( vZeros, pNode );
        else
        {
            // since we disproved this zero, we should add all possible implications to p->vImps
            // these implications will be checked below and only correct ones will remain
            Abc_NtkForEachObj( p->pNtkSingle, pObj, k )
            {
                if ( Abc_ObjIsPo(pObj) )
                    continue;
                if ( Vec_IntEntry( p->vCounters, pObj->Id ) > 0 )
                    Vec_IntPush( p->vImps, Abc_NodeVanGetImp(pNode, pObj) );
            }
        }
    }

    // check implications
    pProgress = Extra_ProgressBarStart( stdout, p->vImps->nSize );
    Vec_IntClear( vImps );
    Vec_IntForEachEntry( p->vImps, Imp, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        pNode1  = Abc_NodeVanGetLeft( p->pNtkSingle, Imp );
        pNode2  = Abc_NodeVanGetRight( p->pNtkSingle, Imp );
        pNodeM1 = Abc_NodeVanImpReadCorresp( pNode1, p->vCorresp, p->nFrames );
        pNodeM2 = Abc_NodeVanImpReadCorresp( pNode2, p->vCorresp, p->nFrames );
        pFNode1 = Fraig_NotCond( Abc_ObjRegular(pNodeM1)->pCopy, Abc_ObjIsComplement(pNodeM1) );
        pFNode2 = Fraig_NotCond( Abc_ObjRegular(pNodeM2)->pCopy, Abc_ObjIsComplement(pNodeM2) );
        pFNode1 = Fraig_NotCond( pFNode1, !pNode1->fPhase );
        pFNode2 = Fraig_NotCond( pFNode2,  pNode2->fPhase );
        if ( pFNode1 == Fraig_Not(pFNode2) )
        {
            Vec_IntPush( vImps, Imp );
            continue;
        }
        if ( pFNode1 == pFNode2 )
        {
            if ( pFNode1 == Fraig_Not( Fraig_ManReadConst1(pFraig) ) )
                continue;
            if ( pFNode1 == Fraig_ManReadConst1(pFraig) )
            {
                Vec_IntPush( vImps, Imp );
                continue;
            }
            pFNode1 = Fraig_Regular(pFNode1);
            pFNode2 = Fraig_ManReadConst1(pFraig);
            if ( Fraig_NodeIsEquivalent( pFraig, pFNode1, pFNode2, -1, 100 ) )
                Vec_IntPush( vImps, Imp );
            continue;
        }
            
        if ( Fraig_ManCheckClauseUsingSat( pFraig, pFNode1, pFNode2, -1 ) )
            Vec_IntPush( vImps, Imp );
    }
    Extra_ProgressBarStop( pProgress );
p->timeCheck += clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Computes all implications.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVanImpComputeAll( Van_Man_t * p )
{
    ProgressBar * pProgress;
    Fraig_Man_t * pManSingle;
    Vec_Ptr_t * vInfo;
    Abc_Obj_t * pObj, * pNode1, * pNode2, * pConst1;
    Fraig_Node_t * pFNode1, * pFNode2;
    unsigned * pPats1, * pPats2;
    int nFrames, nUnsigned, RetValue;
    int clk, i, k, Count1, Count2;

    // decide how many frames to simulate
    nFrames   = 32;
    nUnsigned = 32;
    p->nWords = nFrames * nUnsigned;

    // simulate randomly the initialized frames
clk = clock();
    vInfo = Sim_SimulateSeqRandom( p->pNtkSingle, nFrames, nUnsigned );

    // complement the info for those nodes whose phase is 1
    Abc_NtkForEachObj( p->pNtkSingle, pObj, i )
        if ( pObj->fPhase )
            Sim_UtilSetCompl( Sim_SimInfoGet(vInfo, pObj), p->nWords );

    // compute the number of ones for each node
    p->vCounters = Sim_UtilCountOnesArray( vInfo, p->nWords );
p->timeSim += clock() - clk;

    // FRAIG the uninitialized frame
    pManSingle = Abc_NtkVanEijkFraig( p->pNtkSingle, 0 );
    // now pNode->pCopy are assigned the pointers to the corresponding FRAIG nodes

/*
Abc_NtkForEachPi( p->pNtkSingle, pNode1, i )
printf( "PI = %d\n", pNode1->Id );
Abc_NtkForEachLatch( p->pNtkSingle, pNode1, i )
printf( "Latch = %d\n", pNode1->Id );
Abc_NtkForEachPo( p->pNtkSingle, pNode1, i )
printf( "PO = %d\n", pNode1->Id );
*/

    // go through the pairs of signals in the frames
    pProgress = Extra_ProgressBarStart( stdout, p->nIdMax );
    pConst1 = Abc_AigConst1(p->pNtkSingle);
    p->vImps = Vec_IntAlloc( 100 );
    p->vZeros = Vec_PtrAlloc( 100 );
    Abc_NtkForEachObj( p->pNtkSingle, pNode1, i )
    {
        if ( Abc_ObjIsPo(pNode1) )
            continue;
        if ( pNode1 == pConst1 )
            continue;
        Extra_ProgressBarUpdate( pProgress, i, NULL );

        // get the number of zeros of this node
        Count1 = Vec_IntEntry( p->vCounters, pNode1->Id );
        if ( Count1 == 0 )
        {
            Vec_PtrPush( p->vZeros, pNode1 );
            p->nZeros++;
            continue;
        }
        pPats1 = Sim_SimInfoGet(vInfo, pNode1);

        Abc_NtkForEachObj( p->pNtkSingle, pNode2, k )
        {
            if ( k >= i )
                break;
            if ( Abc_ObjIsPo(pNode2) )
                continue;
            if ( pNode2 == pConst1 )
                continue;
            p->nPairsAll++;

            // here we have a pair of nodes (pNode1 and pNode2) 
            // such that Id(pNode1) < Id(pNode2)
            assert( pNode2->Id < pNode1->Id );

            // get the number of zeros of this node
            Count2 = Vec_IntEntry( p->vCounters, pNode2->Id );
            if ( Count2 == 0 )
                continue;
            pPats2 = Sim_SimInfoGet(vInfo, pNode2);

            // check for implications
            if ( Count1 < Count2 )
            { 
//clk = clock();
                RetValue = Sim_UtilInfoIsImp( pPats1, pPats2, p->nWords );
//p->timeInfo += clock() - clk;
                if ( !RetValue )
                    continue;
                p->nImpsAll++;
                // pPats1 => pPats2  or  pPats1' v pPats2
                pFNode1 = Fraig_NotCond( pNode1->pCopy, !pNode1->fPhase );
                pFNode2 = Fraig_NotCond( pNode2->pCopy,  pNode2->fPhase );
                // check if this implication is combinational
                if ( Fraig_ManCheckClauseUsingSimInfo( pManSingle, pFNode1, pFNode2 ) )
                    continue;
                // otherwise record it
                Vec_IntPush( p->vImps, Abc_NodeVanGetImp(pNode1, pNode2) );
            }
            else if ( Count2 < Count1 )
            { 
//clk = clock();
                RetValue = Sim_UtilInfoIsImp( pPats2, pPats1, p->nWords );
//p->timeInfo += clock() - clk;
                if ( !RetValue )
                    continue;
                p->nImpsAll++;
                // pPats2 => pPats2  or  pPats2' v pPats1
                pFNode2 = Fraig_NotCond( pNode2->pCopy, !pNode2->fPhase );
                pFNode1 = Fraig_NotCond( pNode1->pCopy,  pNode1->fPhase );
                // check if this implication is combinational
                if ( Fraig_ManCheckClauseUsingSimInfo( pManSingle, pFNode1, pFNode2 ) )
                    continue;
                // otherwise record it
                Vec_IntPush( p->vImps, Abc_NodeVanGetImp(pNode2, pNode1) );
            }
            else
            {
//clk = clock();
                RetValue = Sim_UtilInfoIsEqual(pPats1, pPats2, p->nWords);
//p->timeInfo += clock() - clk;
                if ( !RetValue )
                    continue;
                p->nEquals++;
                // get the FRAIG nodes
                pFNode1 = Fraig_NotCond( pNode1->pCopy, pNode1->fPhase );
                pFNode2 = Fraig_NotCond( pNode2->pCopy, pNode2->fPhase );

                // check if this implication is combinational
                if ( Fraig_ManCheckClauseUsingSimInfo( pManSingle, Fraig_Not(pFNode1), pFNode2 ) )
                {
                    if ( !Fraig_ManCheckClauseUsingSimInfo( pManSingle, pFNode1, Fraig_Not(pFNode2) ) )
                        Vec_IntPush( p->vImps, Abc_NodeVanGetImp(pNode2, pNode1) );
                    else
                        assert( 0 ); // impossible for FRAIG
                }
                else
                {
                    Vec_IntPush( p->vImps, Abc_NodeVanGetImp(pNode1, pNode2) );
                    if ( !Fraig_ManCheckClauseUsingSimInfo( pManSingle, pFNode1, Fraig_Not(pFNode2) ) )
                        Vec_IntPush( p->vImps, Abc_NodeVanGetImp(pNode2, pNode1) );
                }
            }
//            printf( "Implication %d %d -> %d %d \n", pNode1->Id, pNode1->fPhase, pNode2->Id, pNode2->fPhase );
        }
    }
    Fraig_ManFree( pManSingle );
    Sim_UtilInfoFree( vInfo );
    Extra_ProgressBarStop( pProgress );
}


/**Function*************************************************************

  Synopsis    [Sorts the nodes.]

  Description [Sorts the nodes appearing in the left-hand sides of the 
  implications by the number of 1s in their simulation info.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkVanImpSortByOnes( Van_Man_t * p )
{
    Abc_Obj_t * pNode, * pList;
    Vec_Ptr_t * vSorted;
    unsigned Imp;
    int i, nOnes;

    // start the sorted array
    vSorted = Vec_PtrStart( p->nWords * 32 );
    // go through the implications
    Abc_NtkIncrementTravId( p->pNtkSingle );
    Vec_IntForEachEntry( p->vImps, Imp, i )
    {
        pNode = Abc_NodeVanGetLeft( p->pNtkSingle, Imp );
        assert( !Abc_ObjIsPo(pNode) );
        // if this node is already visited, skip
        if ( Abc_NodeIsTravIdCurrent( pNode ) )
            continue;
        // mark the node as visited
        Abc_NodeSetTravIdCurrent( pNode );

        // add the node to the list
        nOnes = Vec_IntEntry( p->vCounters, pNode->Id );
        pList = Vec_PtrEntry( vSorted, nOnes );
        pNode->pNext = pList;
        Vec_PtrWriteEntry( vSorted, nOnes, pNode );
    }
    return vSorted;
}

/**Function*************************************************************

  Synopsis    [Computes the array of beginnings.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkVanImpComputeBegs( Van_Man_t * p )
{
    Vec_Int_t * vBegins;
    unsigned Imp;
    int i, ItemLast, ItemCur;

    // sort the implications (by the number of the left-hand-side node)
    Vec_IntSort( p->vImps, 0 );

    // start the array of beginnings
    vBegins = Vec_IntStart( p->nIdMax + 1 );

    // mark the begining of each node's implications
    ItemLast = 0;
    Vec_IntForEachEntry( p->vImps, Imp, i )
    {
        ItemCur = (Imp >> 16);
        if ( ItemCur == ItemLast )
            continue;
        Vec_IntWriteEntry( vBegins, ItemCur, i );
        ItemLast = ItemCur;
    }
    // fill in the empty spaces
    ItemLast = Vec_IntSize(p->vImps);
    Vec_IntWriteEntry( vBegins, p->nIdMax, ItemLast );
    Vec_IntForEachEntryReverse( vBegins, ItemCur, i )
    {
        if ( ItemCur == 0 )
            Vec_IntWriteEntry( vBegins, i, ItemLast );
        else 
            ItemLast = ItemCur;
    }

    Imp = Vec_IntEntry( p->vImps, 0 );
    ItemCur = (Imp >> 16);
    for ( i = 0; i <= ItemCur; i++ )
        Vec_IntWriteEntry( vBegins, i, 0 );
    return vBegins;
}

/**Function*************************************************************

  Synopsis    [Derives the minimum subset of implications.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVanImpMark_rec( Abc_Obj_t * pNode, Vec_Vec_t * vImpsMis )
{
    Vec_Int_t * vNexts;
    int i, Next;
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // mark the children
    vNexts = Vec_VecEntry( vImpsMis, pNode->Id );
    Vec_IntForEachEntry( vNexts, Next, i )
        Abc_NtkVanImpMark_rec( Abc_NtkObj(pNode->pNtk, Next), vImpsMis );
}

/**Function*************************************************************

  Synopsis    [Derives the minimum subset of implications.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkVanImpComputeMis( Van_Man_t * p )
{
    Abc_Obj_t * pNode, * pNext, * pList;
    Vec_Vec_t * vMatrix;
    Vec_Ptr_t * vSorted;
    Vec_Int_t * vBegins;
    Vec_Int_t * vImpsMis;
    int i, k, iStart, iStop;
    void * pEntry;
    unsigned Imp;

    if ( Vec_IntSize(p->vImps) == 0 )
        return Vec_IntAlloc(0);

    // compute the sorted list of nodes by the number of 1s
    Abc_NtkCleanNext( p->pNtkSingle );
    vSorted = Abc_NtkVanImpSortByOnes( p );

    // compute the array of beginnings
    vBegins = Abc_NtkVanImpComputeBegs( p );

/*
Vec_IntForEachEntry( p->vImps, Imp, i )
{
    printf( "%d: ", i );
    Abc_NodeVanPrintImp( Imp );
}
printf( "\n\n" );
Vec_IntForEachEntry( vBegins, Imp, i )
    printf( "%d=%d ", i, Imp );
printf( "\n\n" );
*/

    // compute the MIS by considering nodes in the reverse order of ones
    vMatrix = Vec_VecStart( p->nIdMax );
    Vec_PtrForEachEntryReverse( vSorted, pList, i )
    {
        for ( pNode = pList; pNode; pNode = pNode->pNext )
        {
            // get the starting and stopping implication of this node
            iStart = Vec_IntEntry( vBegins, pNode->Id );
            iStop  = Vec_IntEntry( vBegins, pNode->Id + 1 );
            if ( iStart == iStop )
                continue;
            assert( iStart < iStop );
            // go through all the implications of this node
            Abc_NtkIncrementTravId( p->pNtkSingle );
            Abc_NodeIsTravIdCurrent( pNode );
            Vec_IntForEachEntryStartStop( p->vImps, Imp, k, iStart, iStop )
            {
                assert( pNode == Abc_NodeVanGetLeft(p->pNtkSingle, Imp) );
                pNext = Abc_NodeVanGetRight(p->pNtkSingle, Imp);
                // if this node is already visited, skip
                if ( Abc_NodeIsTravIdCurrent( pNext ) )
                    continue;
                assert( pNode->Id != pNext->Id );
                // add implication
                Vec_VecPush( vMatrix, pNode->Id, (void *)pNext->Id );
                // recursively mark dependent nodes
                Abc_NtkVanImpMark_rec( pNext, vMatrix );
            }
        }
    }
    Vec_IntFree( vBegins );
    Vec_PtrFree( vSorted );

    // transfer the MIS into the normal array
    vImpsMis = Vec_IntAlloc( 100 );
    Vec_VecForEachEntry( vMatrix, pEntry, i, k )
    {
        assert( (i << 16) != ((int)pEntry) );
        Vec_IntPush( vImpsMis, (i << 16) | ((int)pEntry) );
    }
    Vec_VecFree( vMatrix );
    return vImpsMis;
}


/**Function*************************************************************

  Synopsis    [Count equal pairs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkVanImpCountEqual( Van_Man_t * p )
{
    Abc_Obj_t * pNode1, * pNode2, * pNode3;
    Vec_Int_t * vBegins;
    int iStart, iStop;
    unsigned Imp, ImpR;
    int i, k, Counter;

    // compute the array of beginnings
    vBegins = Abc_NtkVanImpComputeBegs( p );

    // go through each node and out
    Counter = 0;
    Vec_IntForEachEntry( p->vImps, Imp, i )
    {
        pNode1 = Abc_NodeVanGetLeft( p->pNtkSingle, Imp );
        pNode2 = Abc_NodeVanGetRight( p->pNtkSingle, Imp );
        if ( pNode1->Id > pNode2->Id )
            continue;
        iStart = Vec_IntEntry( vBegins, pNode2->Id );
        iStop  = Vec_IntEntry( vBegins, pNode2->Id + 1 );
        Vec_IntForEachEntryStartStop( p->vImps, ImpR, k, iStart, iStop )
        {
            assert( pNode2 == Abc_NodeVanGetLeft(p->pNtkSingle, ImpR) );
            pNode3 = Abc_NodeVanGetRight(p->pNtkSingle, ImpR);
            if ( pNode1 == pNode3 )
            {
                Counter++;
                break;
            }
        }
    }
    Vec_IntFree( vBegins );
    return Counter;
}


/**Function*************************************************************

  Synopsis    [Create EXDC from the equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkVanImpDeriveExdc( Abc_Ntk_t * pNtk, Vec_Ptr_t * vZeros, Vec_Int_t * vImps )
{
    Abc_Ntk_t * pNtkNew; 
    Vec_Ptr_t * vCone;
    Abc_Obj_t * pObj, * pMiter, * pTotal, * pNode, * pNode1, * pNode2;//, * pObjNew;
    unsigned Imp;
    int i, k;

    assert( Abc_NtkIsStrash(pNtk) );

    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc );
    pNtkNew->pName = Extra_UtilStrsav( "exdc" );
    pNtkNew->pSpec = NULL;

    // map the constant nodes
    Abc_AigConst1(pNtk)->pCopy = Abc_AigConst1(pNtkNew);
    // for each CI, create PI
    Abc_NtkForEachCi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj->pCopy = Abc_NtkCreatePi(pNtkNew), Abc_ObjName(pObj) );
    // cannot add latches here because pLatch->pCopy pointers are used

    // build logic cone for zero nodes
    pTotal = Abc_ObjNot( Abc_AigConst1(pNtkNew) );
    Vec_PtrForEachEntry( vZeros, pNode, i )
    {
        // build the logic cone for the node
        if ( Abc_ObjFaninNum(pNode) == 2 )
        {
            vCone = Abc_NtkDfsNodes( pNtk, &pNode, 1 );
            Vec_PtrForEachEntry( vCone, pObj, k )
                pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
            Vec_PtrFree( vCone );
            assert( pObj == pNode );
        }
        // complement if there is phase difference
        pNode->pCopy = Abc_ObjNotCond( pNode->pCopy, pNode->fPhase );

        // add it to the EXDC
        pTotal = Abc_AigOr( pNtkNew->pManFunc, pTotal, pNode->pCopy );
    }

    // create logic cones for the implications
    Vec_IntForEachEntry( vImps, Imp, i )
    {
        pNode1 = Abc_NtkObj(pNtk, Imp >> 16);
        pNode2 = Abc_NtkObj(pNtk, Imp & 0xFFFF);

        // build the logic cone for the first node
        if ( Abc_ObjFaninNum(pNode1) == 2 )
        {
            vCone = Abc_NtkDfsNodes( pNtk, &pNode1, 1 );
            Vec_PtrForEachEntry( vCone, pObj, k )
                pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
            Vec_PtrFree( vCone );
            assert( pObj == pNode1 );
        }
        // complement if there is phase difference
        pNode1->pCopy = Abc_ObjNotCond( pNode1->pCopy, pNode1->fPhase );

        // build the logic cone for the second node
        if ( Abc_ObjFaninNum(pNode2) == 2 )
        {
            vCone = Abc_NtkDfsNodes( pNtk, &pNode2, 1 );
            Vec_PtrForEachEntry( vCone, pObj, k )
                pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
            Vec_PtrFree( vCone );
            assert( pObj == pNode2 );
        }
        // complement if there is phase difference
        pNode2->pCopy = Abc_ObjNotCond( pNode2->pCopy, pNode2->fPhase );

        // build the implication and add it to the EXDC
        pMiter = Abc_AigAnd( pNtkNew->pManFunc, pNode1->pCopy, Abc_ObjNot(pNode2->pCopy) );
        pTotal = Abc_AigOr( pNtkNew->pManFunc, pTotal, pMiter );
    }
/*
    // create the only PO
    pObjNew = Abc_NtkCreatePo( pNtkNew );
    // add the PO name
    Abc_NtkLogicStoreName( pObjNew, "DC" );
    // add the PO
    Abc_ObjAddFanin( pObjNew, pTotal );

    // quontify the PIs existentially
    pNtkNew = Abc_NtkMiterQuantifyPis( pNtkNew );

    // get the new PO
    pObjNew = Abc_NtkPo( pNtkNew, 0 );
    // remember the miter output
    pTotal = Abc_ObjChild0( pObjNew );
    // remove the PO
    Abc_NtkDeleteObj( pObjNew );

    // make the old network point to the new things
    Abc_AigConst1(pNtk)->pCopy = Abc_AigConst1(pNtkNew);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = Abc_NtkPi( pNtkNew, i );
*/

    // for each CO, create PO (skip POs equal to CIs because of name conflict)
    Abc_NtkForEachPo( pNtk, pObj, i )
        if ( !Abc_ObjIsCi(Abc_ObjFanin0(pObj)) )
            Abc_NtkLogicStoreName( pObj->pCopy = Abc_NtkCreatePo(pNtkNew), Abc_ObjName(pObj) );
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj->pCopy = Abc_NtkCreatePo(pNtkNew), Abc_ObjNameSuffix(pObj, "_in") );

    // link to the POs of the network
    Abc_NtkForEachPo( pNtk, pObj, i )
        if ( !Abc_ObjIsCi(Abc_ObjFanin0(pObj)) )
            Abc_ObjAddFanin( pObj->pCopy, pTotal );
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_ObjAddFanin( pObj->pCopy, pTotal );

    // remove the extra nodes
    Abc_AigCleanup( pNtkNew->pManFunc );

    // check the result
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkVanImpDeriveExdc: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


