/**CFile****************************************************************

  FileName    [seqMapCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Construction and manipulation of sequential AIGs.]

  Synopsis    [The core of SC mapping/retiming package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: seqMapCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "seqInt.h"
#include "main.h"
#include "mio.h"
#include "mapper.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Abc_Ntk_t *  Seq_NtkMapDup( Abc_Ntk_t * pNtk );
extern int          Seq_NtkMapInitCompatible( Abc_Ntk_t * pNtk, int fVerbose );
extern Abc_Ntk_t *  Seq_NtkSeqMapMapped( Abc_Ntk_t * pNtk );

static int          Seq_MapMappingCount( Abc_Ntk_t * pNtk );
static int          Seq_MapMappingCount_rec( Abc_Ntk_t * pNtk, unsigned SeqEdge, Vec_Ptr_t * vLeaves );
static Abc_Obj_t *  Seq_MapMappingBuild_rec( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtk, unsigned SeqEdge, int fTop, int fCompl, int LagCut, Vec_Ptr_t * vLeaves, unsigned uPhase );
static DdNode *     Seq_MapMappingBdd_rec( DdManager * dd, Abc_Ntk_t * pNtk, unsigned SeqEdge, Vec_Ptr_t * vLeaves );
static void         Seq_MapMappingEdges_rec( Abc_Ntk_t * pNtk, unsigned SeqEdge, Abc_Obj_t * pPrev, Vec_Ptr_t * vLeaves, Vec_Vec_t * vMapEdges );
static void         Seq_MapMappingConnect_rec( Abc_Ntk_t * pNtk, unsigned SeqEdge, Abc_Obj_t * pPrev, int Edge, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves );
static DdNode *     Seq_MapMappingConnectBdd_rec( Abc_Ntk_t * pNtk, unsigned SeqEdge, Abc_Obj_t * pPrev, int Edge, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs Map mapping and retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_MapRetime( Abc_Ntk_t * pNtk, int nMaxIters, int fVerbose )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Abc_Ntk_t * pNtkNew;
    Abc_Ntk_t * pNtkMap;
    int RetValue;

    // derive the supergate library
    if ( Abc_FrameReadLibSuper() == NULL && Abc_FrameReadLibGen() )
    {
        printf( "A simple supergate library is derived from gate library \"%s\".\n", 
            Mio_LibraryReadName(Abc_FrameReadLibGen()) );
        Map_SuperLibDeriveFromGenlib( Abc_FrameReadLibGen() );
    }
    p->pSuperLib   = Abc_FrameReadLibSuper();
    p->nVarsMax    = Map_SuperLibReadVarsMax(p->pSuperLib);
    p->nMaxIters   = nMaxIters;
    p->fStandCells = 1;

    // find the best mapping and retiming for all nodes (p->vLValues, p->vBestCuts, p->vLags)
    Seq_MapRetimeDelayLags( pNtk, fVerbose );
    if ( RetValue = Abc_NtkGetChoiceNum(pNtk) )
    {
        printf( "The network has %d choices. Deriving the resulting network is skipped.\n", RetValue );
        return NULL;
    }

    // duplicate the nodes contained in multiple cuts
    pNtkNew = Seq_NtkMapDup( pNtk );
    return pNtkNew;
    
    // implement the retiming
    RetValue = Seq_NtkImplementRetiming( pNtkNew, ((Abc_Seq_t *)pNtkNew->pManFunc)->vLags, fVerbose );
    if ( RetValue == 0 )
        printf( "Retiming completed but initial state computation has failed.\n" );
//    return pNtkNew;

    // check the compatibility of initial states computed
    if ( RetValue = Seq_NtkMapInitCompatible( pNtkNew, fVerbose ) )
    {
        printf( "The number of LUTs with incompatible edges = %d.\n", RetValue );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }

    // create the final mapped network
    pNtkMap = Seq_NtkSeqMapMapped( pNtkNew );
    Abc_NtkDelete( pNtkNew );
    return pNtkMap;
}

/**Function*************************************************************

  Synopsis    [Derives the network by duplicating some of the nodes.]

  Description [Information about mapping is given as mapping nodes (p->vMapAnds)
  and best cuts for each node (p->vMapCuts).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkMapDup( Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * pNew, * p = pNtk->pManFunc;
    Seq_Match_t * pMatch;
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pFanin, * pFaninNew, * pLeaf;
    Vec_Ptr_t * vLeaves;
    unsigned SeqEdge;
    int i, k, nObjsNew, Lag;
    
    assert( Abc_NtkIsSeq(pNtk) );

    // start the expanded network
    pNtkNew = Abc_NtkStartFrom( pNtk, pNtk->ntkType, pNtk->ntkFunc );
    Abc_NtkCleanNext(pNtk);

    // start the new sequential AIG manager
    nObjsNew = 1 + Abc_NtkPiNum(pNtk) + Abc_NtkPoNum(pNtk) + Seq_MapMappingCount(pNtk);
    Seq_Resize( pNtkNew->pManFunc, nObjsNew );

    // duplicate the nodes in the mapping
    Vec_PtrForEachEntry( p->vMapAnds, pMatch, i )
    {
//        Abc_NtkDupObj( pNtkNew, pMatch->pAnd );
        if ( !pMatch->fCompl )
            pMatch->pAnd->pCopy = Abc_NtkCreateNode( pNtkNew );
        else
            pMatch->pAnd->pNext = Abc_NtkCreateNode( pNtkNew );
    }

    // recursively construct the internals of each node
    Vec_PtrForEachEntry( p->vMapAnds, pMatch, i )
    {
        vLeaves = Vec_VecEntry( p->vMapCuts, i );
        Seq_MapMappingBuild_rec( pNtkNew, pNtk, pMatch->pAnd->Id << 8, 1, pMatch->fCompl, Seq_NodeGetLag(pMatch->pAnd), vLeaves, pMatch->uPhase );
    }
    assert( nObjsNew == pNtkNew->nObjs );

    // set the POs
//    Abc_NtkFinalize( pNtk, pNtkNew );
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        pFanin = Abc_ObjFanin0(pObj);
        if ( Abc_ObjFaninC0(pObj) )
            pFaninNew = pFanin->pNext ? pFanin->pNext : Abc_ObjNot(pFanin->pCopy);
        else
            pFaninNew = pFanin->pCopy ? pFanin->pCopy : Abc_ObjNot(pFanin->pNext);
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
    }

    // duplicate the latches on the PO edges
    Abc_NtkForEachPo( pNtk, pObj, i )
        Seq_NodeDupLats( pObj->pCopy, pObj, 0 );

    // transfer the mapping info to the new manager
    Vec_PtrForEachEntry( p->vMapAnds, pMatch, i )
    {
        // get the leaves of the cut
        vLeaves = Vec_VecEntry( p->vMapCuts, i );
        // convert the leaf nodes
        Vec_PtrForEachEntry( vLeaves, pLeaf, k )
        {
            SeqEdge = (unsigned)pLeaf;
            pLeaf = Abc_NtkObj( pNtk, SeqEdge >> 8 );
            Lag = (SeqEdge & 255) + Seq_NodeGetLag(pMatch->pAnd) - Seq_NodeGetLag(pLeaf);
            assert( Lag >= 0 );
            // translate the old leaf into the leaf in the new network
//            Vec_PtrWriteEntry( vLeaves, k, (void *)((pLeaf->pCopy->Id << 8) | Lag) );

//            printf( "%d -> %d\n", pLeaf->Id, pLeaf->pCopy->Id );
        }
        // convert the root node
//        Vec_PtrWriteEntry( p->vMapAnds, i, pObj->pCopy );
        pMatch->pAnd = pMatch->pAnd->pCopy;
    }
    pNew = pNtkNew->pManFunc;
    pNew->nVarsMax  = p->nVarsMax;
    pNew->vMapAnds  = p->vMapAnds;   p->vMapAnds  = NULL;
    pNew->vMapCuts  = p->vMapCuts;   p->vMapCuts  = NULL;

    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Seq_NtkMapDup(): Network check has failed.\n" );
    return pNtkNew;
}


/**Function*************************************************************

  Synopsis    [Checks if the initial states are compatible.]

  Description [Checks of all the initial states on the fanins edges
  of the cut have compatible number of latches and initial states.
  If this is not true, then the mapped network with the does not have initial 
  state. Returns the number of LUTs with incompatible edges.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_NtkMapInitCompatible( Abc_Ntk_t * pNtk, int fVerbose )
{
    return 1;
}

/**Function*************************************************************

  Synopsis    [Derives the final mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkSeqMapMapped( Abc_Ntk_t * pNtk )
{
    return NULL;
}



/**Function*************************************************************

  Synopsis    [Counts the number of nodes in the bag.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_MapMappingCount( Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Vec_Ptr_t * vLeaves;
    Seq_Match_t * pMatch;
    int i, Counter = 0;
    Vec_PtrForEachEntry( p->vMapAnds, pMatch, i )
    {
        vLeaves = Vec_VecEntry( p->vMapCuts, i );
        Counter += Seq_MapMappingCount_rec( pNtk, pMatch->pAnd->Id << 8, vLeaves );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Counts the number of nodes in the bag.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_MapMappingCount_rec( Abc_Ntk_t * pNtk, unsigned SeqEdge, Vec_Ptr_t * vLeaves )
{
    Abc_Obj_t * pObj, * pLeaf;
    unsigned SeqEdge0, SeqEdge1;
    int Lag, i;
    // get the object and the lag
    pObj = Abc_NtkObj( pNtk, SeqEdge >> 8 );
    Lag  = SeqEdge & 255;
    // if the node is the fanin of the cut, return
    Vec_PtrForEachEntry( vLeaves, pLeaf, i )
        if ( SeqEdge == (unsigned)pLeaf )
            return 0;
    // continue unfolding
    assert( Abc_NodeIsAigAnd(pObj) );
    // get new sequential edges
    assert( Lag + Seq_ObjFaninL0(pObj) < 255 );
    assert( Lag + Seq_ObjFaninL1(pObj) < 255 );
    SeqEdge0 = (Abc_ObjFanin0(pObj)->Id << 8) + Lag + Seq_ObjFaninL0(pObj);
    SeqEdge1 = (Abc_ObjFanin1(pObj)->Id << 8) + Lag + Seq_ObjFaninL1(pObj);
    // call for the children
    return 1 + Seq_MapMappingCount_rec( pNtk, SeqEdge0, vLeaves ) + 
        Seq_MapMappingCount_rec( pNtk, SeqEdge1, vLeaves );
}

/**Function*************************************************************

  Synopsis    [Collects the edges pointing to the leaves of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Seq_MapMappingBuild_rec( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtk, unsigned SeqEdge, int fTop, int fCompl, int LagCut, Vec_Ptr_t * vLeaves, unsigned uPhase )
{
    Abc_Obj_t * pObj, * pObjNew, * pLeaf, * pFaninNew0, * pFaninNew1;
    unsigned SeqEdge0, SeqEdge1;
    int Lag, i;
    // get the object and the lag
    pObj = Abc_NtkObj( pNtk, SeqEdge >> 8 );
    Lag  = SeqEdge & 255;
    // if the node is the fanin of the cut, return
    Vec_PtrForEachEntry( vLeaves, pLeaf, i )
        if ( SeqEdge == (unsigned)pLeaf )
        {
//            if ( uPhase & (1 << i) ) // negative phase is required
//                return pObj->pNext? pObj->pNext : Abc_ObjNot(pObj->pCopy);
//            else // positive phase is required
//                return pObj->pCopy? pObj->pCopy : Abc_ObjNot(pObj->pNext);
            return pObj->pCopy? pObj->pCopy : Abc_ObjNot(pObj->pNext);
        }
    // continue unfolding
    assert( Abc_NodeIsAigAnd(pObj) );
    // get new sequential edges
    assert( Lag + Seq_ObjFaninL0(pObj) < 255 );
    assert( Lag + Seq_ObjFaninL1(pObj) < 255 );
    SeqEdge0 = (Abc_ObjFanin0(pObj)->Id << 8) + Lag + Seq_ObjFaninL0(pObj);
    SeqEdge1 = (Abc_ObjFanin1(pObj)->Id << 8) + Lag + Seq_ObjFaninL1(pObj);
    // call for the children    
    pObjNew = fTop? (fCompl? pObj->pNext : pObj->pCopy) : Abc_NtkCreateNode( pNtkNew );
    // solve subproblems
    pFaninNew0 = Seq_MapMappingBuild_rec( pNtkNew, pNtk, SeqEdge0, 0, fCompl, LagCut, vLeaves, uPhase );
    pFaninNew1 = Seq_MapMappingBuild_rec( pNtkNew, pNtk, SeqEdge1, 0, fCompl, LagCut, vLeaves, uPhase );
    // add the fanins to the node
    Abc_ObjAddFanin( pObjNew, Abc_ObjNotCond( pFaninNew0, Abc_ObjFaninC0(pObj) ) );
    Abc_ObjAddFanin( pObjNew, Abc_ObjNotCond( pFaninNew1, Abc_ObjFaninC1(pObj) ) );
    Seq_NodeDupLats( pObjNew, pObj, 0 );
    Seq_NodeDupLats( pObjNew, pObj, 1 );
    // set the lag of the new node equal to the internal lag plus mapping/retiming lag
    Seq_NodeSetLag( pObjNew, (char)(Lag + LagCut) );
//    Seq_NodeSetLag( pObjNew, (char)(Lag) );
    return pObjNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


