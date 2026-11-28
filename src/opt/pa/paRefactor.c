/**CFile****************************************************************

  FileName    [paRefactor.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [Placement-aware refactoring.]

  Author      [Anqi Lu, from abcRefactor.c by Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paRefactor.c,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "paInt.h"
#include "bool/kit/kit.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Fixed refactoring parameters (ABC's refactor defaults with level update).
#define PA_REF_NODE_SIZE_MAX 10 // the limit on the size of the supernode
#define PA_REF_CONE_SIZE_MAX 16 // the limit on the size of the containing cone

// Per-pass, direct-mapped memoization of the pure truth-to-graph step.
// Keys contain the complete ordered truth table and variable count. At most
// 1024 entries of 16 KiB each; a collision/oversize entry only causes a miss.
#define PA_REF_CACHE_SIZE 1024
#define PA_REF_CACHE_ENTRY_BYTES 16384
typedef struct Pa_RefCacheEntry_t_
{
    word Hash;
    int nVars;
    unsigned * pTruth;
    Dec_Graph_t * pGraph;
} Pa_RefCacheEntry_t;

typedef struct Pa_ManRef_t_ Pa_ManRef_t;
struct Pa_ManRef_t_
{
    Vec_Ptr_t * vVars;    // truth tables
    Vec_Ptr_t * vFuncs;   // functions
    Vec_Int_t * vMemory;  // memory
    Vec_Ptr_t * vVisited; // temporary
    Pa_RefCacheEntry_t * pFactorCache;
    int nLastGain;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns function of the cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word * Pa_NodeConeTruth( Vec_Ptr_t * vVars, Vec_Ptr_t * vFuncs, int nWordsMax, Abc_Obj_t * pRoot,
                                Vec_Ptr_t * vLeaves, Vec_Ptr_t * vVisited )
{
    Abc_Obj_t * pNode;
    word *pTruth0, *pTruth1, *pTruth = NULL;
    int i, k, nWords = Abc_Truth6WordNum( Vec_PtrSize( vLeaves ) );
    // get nodes in the cut without fanins in the DFS order
    Abc_NodeConeCollect( &pRoot, 1, vLeaves, vVisited, 0 );
    // set elementary functions
    Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pNode, i ) pNode->pCopy = (Abc_Obj_t *)Vec_PtrEntry( vVars, i );
    // prepare functions
    for ( i = Vec_PtrSize( vFuncs ); i < Vec_PtrSize( vVisited ); i++ )
        Vec_PtrPush( vFuncs, ABC_ALLOC( word, nWordsMax ) );
    // compute functions for the collected nodes
    Vec_PtrForEachEntry( Abc_Obj_t *, vVisited, pNode, i )
    {
        assert( !Abc_ObjIsPi( pNode ) );
        pTruth0 = (word *)Abc_ObjFanin0( pNode )->pCopy;
        pTruth1 = (word *)Abc_ObjFanin1( pNode )->pCopy;
        pTruth = (word *)Vec_PtrEntry( vFuncs, i );
        if ( Abc_ObjFaninC0( pNode ) )
        {
            if ( Abc_ObjFaninC1( pNode ) )
                for ( k = 0; k < nWords; k++ )
                    pTruth[k] = ~pTruth0[k] & ~pTruth1[k];
            else
                for ( k = 0; k < nWords; k++ )
                    pTruth[k] = ~pTruth0[k] & pTruth1[k];
        }
        else
        {
            if ( Abc_ObjFaninC1( pNode ) )
                for ( k = 0; k < nWords; k++ )
                    pTruth[k] = pTruth0[k] & ~pTruth1[k];
            else
                for ( k = 0; k < nWords; k++ )
                    pTruth[k] = pTruth0[k] & pTruth1[k];
        }
        pNode->pCopy = (Abc_Obj_t *)pTruth;
    }
    return pTruth;
}
/**Function*************************************************************

  Synopsis    [Returns 1 if the truth table is constant 0.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_NodeConeIsConst0( word * pTruth, int nVars )
{
    int k, nWords = Abc_Truth6WordNum( nVars );
    for ( k = 0; k < nWords; k++ )
        if ( pTruth[k] )
            return 0;
    return 1;
}
/**Function*************************************************************

  Synopsis    [Returns 1 if the truth table is constant 1.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_NodeConeIsConst1( word * pTruth, int nVars )
{
    int k, nWords = Abc_Truth6WordNum( nVars );
    for ( k = 0; k < nWords; k++ )
        if ( ~pTruth[k] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Resynthesizes the node using refactoring.]

  Description [Returns the factored form of the cut function if the
               placement evaluator accepts it (no node loss, positive
               score), or NULL.]

***********************************************************************/
static Dec_Graph_t * Pa_RefGraphCopy( const Dec_Graph_t * pGraph )
{
    Dec_Graph_t * pCopy;
    if ( pGraph == NULL )
        return NULL;
    pCopy = ABC_ALLOC( Dec_Graph_t, 1 );
    *pCopy = *pGraph;
    pCopy->nCap = pGraph->nSize;
    pCopy->pNodes = ABC_ALLOC( Dec_Node_t, pCopy->nCap );
    memcpy( pCopy->pNodes, pGraph->pNodes, sizeof( Dec_Node_t ) * pCopy->nSize );
    return pCopy;
}

/**Function*************************************************************

  Synopsis    [Factors the truth table of a cut, reusing the results of the pass.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Dec_Graph_t * Pa_RefFactorCached( Pa_ManRef_t * p, unsigned * pTruth, int nVars )
{
    int i, nWords = Kit_TruthWordNum( nVars );
    word Hash = (word)nVars + ABC_CONST( 1469598103934665603 );
    Pa_RefCacheEntry_t * pEntry;
    Dec_Graph_t * pGraph;
    for ( i = 0; i < nWords; ++i )
        Hash = ( Hash ^ pTruth[i] ) * ABC_CONST( 1099511628211 );
    Hash ^= Hash >> 32;
    pEntry = p->pFactorCache + ( Hash & ( PA_REF_CACHE_SIZE - 1 ) );
    if ( pEntry->pTruth && pEntry->Hash == Hash && pEntry->nVars == nVars &&
         !memcmp( pEntry->pTruth, pTruth, sizeof( unsigned ) * nWords ) )
    {
        return Pa_RefGraphCopy( pEntry->pGraph );
    }
    pGraph = (Dec_Graph_t *)Kit_TruthToGraph( pTruth, nVars, p->vMemory );
    if ( sizeof( unsigned ) * nWords + ( pGraph ? sizeof( Dec_Node_t ) * pGraph->nSize : 0 ) <=
         PA_REF_CACHE_ENTRY_BYTES )
    {
        ABC_FREE( pEntry->pTruth );
        if ( pEntry->pGraph )
            Dec_GraphFree( pEntry->pGraph );
        pEntry->Hash = Hash;
        pEntry->nVars = nVars;
        pEntry->pTruth = ABC_ALLOC( unsigned, nWords );
        memcpy( pEntry->pTruth, pTruth, sizeof( unsigned ) * nWords );
        // Store before leaves are bound or materialization writes pFunc.
        pEntry->pGraph = Pa_RefGraphCopy( pGraph );
    }
    return pGraph;
}

/**Function*************************************************************

  Synopsis    [Factors the cut function of a node and scores the factored form.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Dec_Graph_t * Pa_NodeRefactor( Pa_ManRef_t * p, Abc_Obj_t * pNode, Vec_Ptr_t * vFanins )
{
    int nVars = Vec_PtrSize( vFanins );
    int nWordsMax = Abc_Truth6WordNum( PA_REF_NODE_SIZE_MAX );
    int Required = Abc_ObjRequiredLevel( pNode );
    Dec_Graph_t * pFForm;
    Abc_Obj_t * pFanin;
    word * pTruth;
    double Score;
    int i, nNodesSaved, Gain;

    // get the function of the cut
    pTruth = Pa_NodeConeTruth( p->vVars, p->vFuncs, nWordsMax, pNode, vFanins, p->vVisited );
    if ( pTruth == NULL )
        return NULL;

    // a constant node
    if ( Pa_NodeConeIsConst0( pTruth, nVars ) || Pa_NodeConeIsConst1( pTruth, nVars ) )
    {
        Dec_Graph_t * pConst = Pa_NodeConeIsConst0( pTruth, nVars ) ? Dec_GraphCreateConst0() : Dec_GraphCreateConst1();
        Vec_PtrForEachEntry( Abc_Obj_t *, vFanins, pFanin, i ) Abc_ObjRegular( pFanin )->vFanouts.nSize++;
        Abc_NtkIncrementTravId( pNode->pNtk );
        nNodesSaved = Abc_NodeMffcLabelAig( pNode );
        Vec_PtrForEachEntry( Abc_Obj_t *, vFanins, pFanin, i ) Abc_ObjRegular( pFanin )->vFanouts.nSize--;
        if ( !Pa_ManEvaluateCandidate( pNode, pConst, nNodesSaved, Required, 0, &Gain, &Score, NULL, NULL, NULL ) ||
             Gain < 0 || Score <= 1.0e-10 )
        {
            Dec_GraphFree( pConst );
            return NULL;
        }
        p->nLastGain = Gain;
        return pConst;
    }

    // get the factored form
    pFForm = Pa_RefFactorCached( p, (unsigned *)pTruth, nVars );
    if ( pFForm == NULL )
        return NULL;

    // mark the fanin boundary
    // (can mark only essential fanins, belonging to bNodeFunc!)
    Vec_PtrForEachEntry( Abc_Obj_t *, vFanins, pFanin, i ) pFanin->vFanouts.nSize++;
    // label MFFC with current traversal ID
    Abc_NtkIncrementTravId( pNode->pNtk );
    nNodesSaved = Abc_NodeMffcLabelAig( pNode );
    // unmark the fanin boundary and set the fanins as leaves in the form
    Vec_PtrForEachEntry( Abc_Obj_t *, vFanins, pFanin, i )
    {
        pFanin->vFanouts.nSize--;
        Dec_GraphNode( pFForm, i )->pFunc = pFanin;
    }
    if ( !Pa_ManEvaluateCandidate( pNode, pFForm, nNodesSaved, Required, 0, &Gain, &Score, NULL, NULL, NULL ) ||
         Gain < 0 || Score <= 1.0e-10 )
    {
        Dec_GraphFree( pFForm );
        return NULL;
    }
    p->nLastGain = Gain;
    return pFForm;
}

/**Function*************************************************************

  Synopsis    [Starts the resynthesis manager.]

***********************************************************************/
static Pa_ManRef_t * Pa_NtkManRefStart( void )
{
    Pa_ManRef_t * p;
    p = ABC_ALLOC( Pa_ManRef_t, 1 );
    memset( p, 0, sizeof( Pa_ManRef_t ) );
    p->vVisited = Vec_PtrAlloc( 100 );
    p->vVars = Vec_PtrAllocTruthTables( Abc_MaxInt( PA_REF_NODE_SIZE_MAX, 6 ) );
    p->vFuncs = Vec_PtrAlloc( 100 );
    p->vMemory = Vec_IntAlloc( 1 << 16 );
    p->pFactorCache = ABC_CALLOC( Pa_RefCacheEntry_t, PA_REF_CACHE_SIZE );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

***********************************************************************/
static void Pa_NtkManRefStop( Pa_ManRef_t * p )
{
    int i;
    for ( i = 0; i < PA_REF_CACHE_SIZE; ++i )
    {
        ABC_FREE( p->pFactorCache[i].pTruth );
        if ( p->pFactorCache[i].pGraph )
            Dec_GraphFree( p->pFactorCache[i].pGraph );
    }
    ABC_FREE( p->pFactorCache );
    Vec_PtrFreeFree( p->vFuncs );
    Vec_PtrFree( p->vVars );
    Vec_IntFree( p->vMemory );
    Vec_PtrFree( p->vVisited );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Placement-aware refactoring.]

  Description [Starting from each node, computes a reconvergence-driven cut,
               factors the cut function, and replaces the MFFC of the node
               by the factored form if the evaluator accepts it. Levels are
               updated.]

***********************************************************************/
int Pa_NtkRefactor( Abc_Ntk_t * pNtk, Pa_Filter_t * pFilter, int fReassignIds )
{
    Pa_ManRef_t * pManRef;
    Abc_ManCut_t * pManCut;
    Dec_Graph_t * pFForm;
    Vec_Ptr_t * vFanins;
    Abc_Obj_t * pNode;
    int i, nNodes, RetValue = 1;

    assert( Abc_NtkIsStrash( pNtk ) );
    if ( !Pa_ManHasPlacement( pNtk ) )
        return -1;
    Abc_AigCleanup( (Abc_Aig_t *)pNtk->pManFunc );
    if ( !Pa_ManBeginPass( pNtk ) )
        return -1;
    if ( !Pa_ManPrepareTimingPass( pNtk ) )
    {
        Pa_ManEndPass( pNtk );
        return -1;
    }
    pManCut = Abc_NtkManCutStart( PA_REF_NODE_SIZE_MAX, PA_REF_CONE_SIZE_MAX, 2, 1000 );
    pManRef = Pa_NtkManRefStart();
    Abc_NtkStartReverseLevels( pNtk, 0 );

    // resynthesize each node once
    nNodes = Abc_NtkObjNumMax( pNtk );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_NodeIsPersistant( pNode ) || Abc_ObjFanoutNum( pNode ) > 1000 )
            continue;
        // stop if all nodes have been tried once
        if ( i >= nNodes )
            break;
        if ( pFilter && !pFilter->fVisit( pFilter->pData, pNode ) )
            continue;
        vFanins = Abc_NodeFindCut( pManCut, pNode, 0 );
        pFForm = Pa_NodeRefactor( pManRef, pNode, vFanins );
        if ( pFilter && pFilter->fDone )
            pFilter->fDone( pFilter->pData, pNode, pFForm != NULL );
        if ( pFForm == NULL )
            continue;
        if ( !Pa_ManCommitCandidate( pNode, pFForm, vFanins, 1, pManRef->nLastGain ) )
        {
            Dec_GraphFree( pFForm );
            RetValue = -1;
            break;
        }
        Dec_GraphFree( pFForm );
    }
    Abc_NtkManCutStop( pManCut );
    Pa_NtkManRefStop( pManRef );
    if ( !Pa_ManBeginEdit( pNtk ) )
        RetValue = -1;
    if ( fReassignIds )
        Abc_NtkReassignIds( pNtk );
    if ( RetValue >= 0 && !Pa_ManFinishEdit( pNtk ) )
        RetValue = -1;
    if ( RetValue >= 0 && !Pa_ManEndPass( pNtk ) )
        RetValue = -1;
    if ( RetValue < 0 )
    {
        Pa_ManClearPlacement();
        return RetValue;
    }
    Abc_NtkStopReverseLevels( pNtk );
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Pa_NtkRefactor: The network check has failed.\n" );
        return 0;
    }
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
