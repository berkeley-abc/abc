/**CFile****************************************************************

  FileName    [seqFpgaCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Construction and manipulation of sequential AIGs.]

  Synopsis    [The core of FPGA mapping/retiming package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: seqFpgaCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "seqInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t *  Seq_NtkFpgaDup( Abc_Ntk_t * pNtk );
static int          Seq_NtkFpgaInitCompatible( Abc_Ntk_t * pNtk );
static Abc_Ntk_t *  Seq_NtkSeqFpgaMapped( Abc_Ntk_t * pNtkNew );
static int          Seq_FpgaMappingCount( Abc_Ntk_t * pNtk );
static int          Seq_FpgaMappingCount_rec( Abc_Ntk_t * pNtk, unsigned SeqEdge, Vec_Ptr_t * vLeaves );
static DdNode *     Seq_FpgaMappingBdd_rec( DdManager * dd, Abc_Ntk_t * pNtk, unsigned SeqEdge, Vec_Ptr_t * vLeaves );
static void         Seq_FpgaMappingEdges_rec( Abc_Ntk_t * pNtk, unsigned SeqEdge, Abc_Obj_t * pPrev, Vec_Ptr_t * vLeaves, Vec_Vec_t * vMapEdges );
static Abc_Obj_t *  Seq_FpgaMappingBuild_rec( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtk, unsigned SeqEdge, int fTop, Vec_Ptr_t * vLeaves );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs FPGA mapping and retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkFpgaMapRetime( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Ntk_t * pNtkMap;
    int RetValue;
    // find the best mapping and retiming for all nodes (p->vLValues, p->vBestCuts, p->vLags)
    Seq_FpgaMappingDelays( pNtk, fVerbose );
    // duplicate the nodes contained in multiple cuts
    pNtkNew = Seq_NtkFpgaDup( pNtk );
    // implement the retiming
    RetValue = Seq_NtkImplementRetiming( pNtkNew, ((Abc_Seq_t *)pNtkNew->pManFunc)->vLags, fVerbose );
    if ( RetValue == 0 )
        printf( "Retiming completed but initial state computation has failed.\n" );
    // check the compatibility of initial states computed
    if ( RetValue = Seq_NtkFpgaInitCompatible( pNtkNew ) )
    {
        printf( "The number of LUTs with incompatible edges = %d.\n", RetValue );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    // create the final mapped network
    pNtkMap = Seq_NtkSeqFpgaMapped( pNtkNew );
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
Abc_Ntk_t * Seq_NtkFpgaDup( Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * pNew, * p = pNtk->pManFunc;
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pLeaf;
    Vec_Ptr_t * vLeaves;
    unsigned SeqEdge;
    int i, k, nObjsNew;
    
    assert( Abc_NtkIsSeq(pNtk) );

    // start the expanded network
    pNtkNew = Abc_NtkStartFrom( pNtk, pNtk->ntkType, pNtk->ntkFunc );

    // start the new sequential AIG manager
    nObjsNew = 1 + Abc_NtkPiNum(pNtk) + Abc_NtkPoNum(pNtk) + Seq_FpgaMappingCount(pNtk);
    Seq_Resize( pNtkNew->pManFunc, nObjsNew );

    // duplicate the nodes in the mapping
    Vec_PtrForEachEntry( p->vMapAnds, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj );

    // recursively construct the internals of each node
    Vec_PtrForEachEntry( p->vMapAnds, pObj, i )
    {
        vLeaves = Vec_VecEntry( p->vMapCuts, i );
        Seq_FpgaMappingBuild_rec( pNtkNew, pNtk, pObj->Id << 8, 1, vLeaves );
    }
    assert( nObjsNew == pNtkNew->nObjs );

    // set the POs
    Abc_NtkFinalize( pNtk, pNtkNew );

//Abc_NtkShowAig( pNtkNew );

    // transfer the mapping info to the new manager
    Vec_PtrForEachEntry( p->vMapAnds, pObj, i )
    {
        // convert the root node
        Vec_PtrWriteEntry( p->vMapAnds, i, pObj->pCopy );
        // get the leaves of the cut
        vLeaves = Vec_VecEntry( p->vMapCuts, i );
        // convert the leaf nodes
        Vec_PtrForEachEntry( vLeaves, pLeaf, k )
        {
            SeqEdge = (unsigned)pLeaf;
            pLeaf = Abc_NtkObj( pNtk, SeqEdge >> 8 );
            // translate the old leaf into the leaf in the new network
            Vec_PtrWriteEntry( vLeaves, k, (void *)((pLeaf->pCopy->Id << 8) | (SeqEdge & 255)) );
//            printf( "%d -> %d\n", pLeaf->Id, pLeaf->pCopy->Id );
        }
    }
    pNew = pNtkNew->pManFunc;
    pNew->nVarsMax  = p->nVarsMax;
    pNew->vMapAnds  = p->vMapAnds;   p->vMapAnds  = NULL;
    pNew->vMapCuts  = p->vMapCuts;   p->vMapCuts  = NULL;

    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Seq_NtkFpgaDup(): Network check has failed.\n" );
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
int Seq_NtkFpgaInitCompatible( Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Abc_Obj_t * pAnd, * pLeaf, * pFanout0, * pFanout1;
    Vec_Vec_t * vTotalEdges;
    Vec_Ptr_t * vLeaves, * vEdges;
    int i, k, m, Edge0, Edge1, nLatchBefore, nLatchAfter, nLatches1, nLatches2;
    unsigned SeqEdge;
    int CountBad = 0;

    vTotalEdges = Vec_VecStart( p->nVarsMax );
    // go through all the nodes (cuts) used in the mapping
    Vec_PtrForEachEntry( p->vMapAnds, pAnd, i )
    {
//        printf( "*** Node %d.\n", pAnd->Id );

        // get the cut of this gate
        vLeaves = Vec_VecEntry( p->vMapCuts, i );

        // get the edges pointing to the leaves
        Vec_VecClear( vTotalEdges );
        Seq_FpgaMappingEdges_rec( pNtk, pAnd->Id << 8, NULL, vLeaves, vTotalEdges );

        // for each leaf, consider its edges
        Vec_PtrForEachEntry( vLeaves, pLeaf, k )
        {
            SeqEdge = (unsigned)pLeaf;
            pLeaf = Abc_NtkObj( pNtk, SeqEdge >> 8 );
            nLatchBefore = SeqEdge & 255;

            // get the resulting lag of this node
            nLatchAfter = nLatchBefore + Seq_NodeGetLag(pAnd) - Seq_NodeGetLag(pLeaf);
            assert( nLatchAfter >= 0 );
            if ( nLatchAfter == 0 )
                continue;

            // go through the edges
            vEdges = Vec_VecEntry( vTotalEdges, k );
            pFanout0 = NULL;
            Vec_PtrForEachEntry( vEdges, pFanout1, m )
            {
                Edge1    = Abc_ObjIsComplement(pFanout1);
                pFanout1 = Abc_ObjRegular(pFanout1);
//printf( "Fanin = %d. Fanout = %d.\n", pLeaf->Id, pFanout1->Id );

                // make sure this is the same fanin
                if ( Edge1 )
                    assert( pLeaf == Abc_ObjFanin1(pFanout1) );
                else
                    assert( pLeaf == Abc_ObjFanin0(pFanout1) );

                // save the first one
                if ( pFanout0 == NULL )
                {
                    pFanout0 = pFanout1;
                    Edge0    = Edge1;
                    continue;
                }
                // compare the rings
                // if they have different number of latches, this is the bug
                nLatches1 = Seq_NodeCountLats(pFanout0, Edge0);
                nLatches2 = Seq_NodeCountLats(pFanout1, Edge1);
                assert( nLatches1 == nLatches2 );
                assert( nLatches1 > 0 );

                // if they have different initial states, this is the problem
                if ( !Seq_NodeCompareLats(pFanout0, Edge0, pFanout1, Edge1) )
                {
                    CountBad++;
                    break;
                }
            }
        }
    }
    Vec_VecFree( vTotalEdges );
    return CountBad;
}

/**Function*************************************************************

  Synopsis    [Derives the final mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkSeqFpgaMapped( Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Seq_Lat_t * pLat, * pRing;
    Abc_Ntk_t * pNtkMap; 
    Vec_Vec_t * vTotalEdges;
    Vec_Ptr_t * vLeaves, * vMapEdges;
    Abc_Obj_t * pObj, * pAnd, * pLeaf, * pFanout, * pFanin, * pLatch;
    int i, k, m, Edge, nLatches, nLatchBefore, nLatchAfter;
    unsigned SeqEdge;

    assert( Abc_NtkIsSeq(pNtk) );

    // start the network
    pNtkMap = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_BDD );

    // duplicate the nodes used in the mapping
    Vec_PtrForEachEntry( p->vMapAnds, pAnd, i )
    {
        pAnd->pCopy = Abc_NtkCreateNode( pNtkMap );
        // get the leaves of this gate
        vLeaves = Vec_VecEntry( p->vMapCuts, i );
        // get the BDD of the node
        pAnd->pCopy->pData = Seq_FpgaMappingBdd_rec( pNtkMap->pManFunc, pNtk, pAnd->Id << 8, vLeaves );
        Cudd_Ref( pAnd->pCopy->pData );
    }   

    // construct nodes in the mapped network
    vTotalEdges = Vec_VecStart( p->nVarsMax );
    Vec_PtrForEachEntry( p->vMapAnds, pAnd, i )
    {
        // get the leaves of this gate
        vLeaves = Vec_VecEntry( p->vMapCuts, i );
        // get the edges pointing to the leaves
        Vec_VecClear( vTotalEdges );
        Seq_FpgaMappingEdges_rec( pNtk, pAnd->Id << 8, NULL, vLeaves, vTotalEdges );
        // for each leaf, consider its edges
        Vec_PtrForEachEntry( vLeaves, pLeaf, k )
        {
            SeqEdge = (unsigned)pLeaf;
            pLeaf = Abc_NtkObj( pNtk, SeqEdge >> 8 );
            nLatchBefore = SeqEdge & 255;

            // get the resulting lag of this node
            nLatchAfter = nLatchBefore + Seq_NodeGetLag(pAnd) - Seq_NodeGetLag(pLeaf);
            assert( nLatchAfter >= 0 );
            if ( nLatchAfter == 0 )
            {
                // add the fanin
                Abc_ObjAddFanin( pAnd->pCopy, pLeaf->pCopy );
                continue;
            }

            // get the first edge
            vMapEdges = Vec_VecEntry( vTotalEdges, k );
            pFanout = Vec_PtrEntry( vMapEdges, 0 );
            Edge    = Abc_ObjIsComplement(pFanout);
            pFanout = Abc_ObjRegular(pFanout);
            // make sure this is the same fanin
            if ( Edge )
                assert( pLeaf == Abc_ObjFanin1(pFanout) );
            else
                assert( pLeaf == Abc_ObjFanin0(pFanout) );
            nLatches = Seq_NodeCountLats(pFanout, Edge);
            assert( nLatches > 0 );

            // for each implicit latch add the real latch
            pFanin = pLeaf->pCopy;
            pRing  = Seq_NodeGetRing(pFanout, Edge);
            for ( m = 0, pLat = Seq_LatPrev(pRing); m < nLatches; m++, pLat = Seq_LatPrev(pLat) )
            {
                pLatch = Abc_NtkCreateLatch( pNtkMap );
                pLatch->pData = (void *)Seq_LatInit(pLat);
                Abc_ObjAddFanin( pLatch, pFanin );
                pFanin = pLatch;
            }
            // finally connect to the latch
            Abc_ObjAddFanin( pAnd->pCopy, pFanin );
        }
    }
    Vec_VecFree( vTotalEdges );

    // set the POs
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        pFanin = Abc_ObjFanin0(pObj)->pCopy;
        if ( Abc_ObjFaninL0(pObj) > 0 )
        {
            pRing = Seq_NodeGetRing(pObj, 0);
            for ( m = 0, pLat = Seq_LatPrev(pRing); m < nLatches; m++, pLat = Seq_LatPrev(pLat) )
            {
                pLatch = Abc_NtkCreateLatch( pNtkMap );
                pLatch->pData = (void *)Seq_LatInit(pLat);
                Abc_ObjAddFanin( pLatch, pFanin );
                pFanin = pLatch;
            }
        }
        pFanin = Abc_ObjNotCond(pFanin, Abc_ObjFaninC0(pObj));
        Abc_ObjAddFanin( pObj->pCopy, pFanin );
    }

    // add the latches and their names
    Abc_NtkAddDummyLatchNames( pNtkMap );
    Abc_NtkForEachLatch( pNtkMap, pLatch, i )
    {
        Vec_PtrPush( pNtkMap->vCis, pLatch );
        Vec_PtrPush( pNtkMap->vCos, pLatch );
    }

    // fix the problem with complemented and duplicated CO edges
    Abc_NtkLogicMakeSimpleCos( pNtkMap, 1 );

    if ( !Abc_NtkCheck( pNtkMap ) )
        fprintf( stdout, "Seq_NtkSeqFpgaMapped(): Network check has failed.\n" );
    return pNtkMap;
}


/**Function*************************************************************

  Synopsis    [Counts the number of nodes in the bag.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_FpgaMappingCount( Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Vec_Ptr_t * vLeaves;
    Abc_Obj_t * pAnd;
    int i, Counter = 0;
    Vec_PtrForEachEntry( p->vMapAnds, pAnd, i )
    {
        vLeaves = Vec_VecEntry( p->vMapCuts, i );
        Counter += Seq_FpgaMappingCount_rec( pNtk, pAnd->Id << 8, vLeaves );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Counts the number of nodes in the bag.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_FpgaMappingCount_rec( Abc_Ntk_t * pNtk, unsigned SeqEdge, Vec_Ptr_t * vLeaves )
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
    assert( Lag + Abc_ObjFaninL0(pObj) < 255 );
    assert( Lag + Abc_ObjFaninL1(pObj) < 255 );
    SeqEdge0 = (Abc_ObjFanin0(pObj)->Id << 8) + Lag + Abc_ObjFaninL0(pObj);
    SeqEdge1 = (Abc_ObjFanin1(pObj)->Id << 8) + Lag + Abc_ObjFaninL1(pObj);
    // call for the children
    return 1 + Seq_FpgaMappingCount_rec( pNtk, SeqEdge0, vLeaves ) + 
        Seq_FpgaMappingCount_rec( pNtk, SeqEdge1, vLeaves );
}

/**Function*************************************************************

  Synopsis    [Derives the BDD of the selected cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Seq_FpgaMappingBdd_rec( DdManager * dd, Abc_Ntk_t * pNtk, unsigned SeqEdge, Vec_Ptr_t * vLeaves )
{
    Abc_Obj_t * pObj, * pLeaf;
    DdNode * bFunc0, * bFunc1, * bFunc;
    unsigned SeqEdge0, SeqEdge1;
    int Lag, i;
    // get the object and the lag
    pObj = Abc_NtkObj( pNtk, SeqEdge >> 8 );
    Lag  = SeqEdge & 255;
    // if the node is the fanin of the cut, return
    Vec_PtrForEachEntry( vLeaves, pLeaf, i )
        if ( SeqEdge == (unsigned)pLeaf )
            return Cudd_bddIthVar( dd, i );
    // continue unfolding
    assert( Abc_NodeIsAigAnd(pObj) );
    // get new sequential edges
    assert( Lag + Abc_ObjFaninL0(pObj) < 255 );
    assert( Lag + Abc_ObjFaninL1(pObj) < 255 );
    SeqEdge0 = (Abc_ObjFanin0(pObj)->Id << 8) + Lag + Abc_ObjFaninL0(pObj);
    SeqEdge1 = (Abc_ObjFanin1(pObj)->Id << 8) + Lag + Abc_ObjFaninL1(pObj);
    // call for the children
    bFunc0 = Seq_FpgaMappingBdd_rec( dd, pNtk, SeqEdge0, vLeaves );    Cudd_Ref( bFunc0 );
    bFunc1 = Seq_FpgaMappingBdd_rec( dd, pNtk, SeqEdge1, vLeaves );    Cudd_Ref( bFunc1 );
    // get the BDD of the node
    bFunc  = Cudd_bddAnd( dd, Cudd_NotCond(bFunc0, Abc_ObjFaninC0(pObj)), Cudd_NotCond(bFunc1, Abc_ObjFaninC1(pObj)) );  Cudd_Ref( bFunc );
    Cudd_RecursiveDeref( dd, bFunc0 );
    Cudd_RecursiveDeref( dd, bFunc1 );
    // return the BDD
    Cudd_Deref( bFunc );
    return bFunc;
}

/**Function*************************************************************

  Synopsis    [Collects the edges pointing to the leaves of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Seq_FpgaMappingEdges_rec( Abc_Ntk_t * pNtk, unsigned SeqEdge, Abc_Obj_t * pPrev, Vec_Ptr_t * vLeaves, Vec_Vec_t * vMapEdges )
{
    Abc_Obj_t * pObj, * pLeaf;
    unsigned SeqEdge0, SeqEdge1;
    int Lag, i;
    // get the object and the lag
    pObj = Abc_NtkObj( pNtk, SeqEdge >> 8 );
    Lag  = SeqEdge & 255;
    // if the node is the fanin of the cut, return
    Vec_PtrForEachEntry( vLeaves, pLeaf, i )
    {
        if ( SeqEdge == (unsigned)pLeaf )
        {
            assert( pPrev != NULL );
            Vec_VecPush( vMapEdges, i, pPrev );
            return;
        }
    }
    // continue unfolding
    assert( Abc_NodeIsAigAnd(pObj) );
    // get new sequential edges
    assert( Lag + Abc_ObjFaninL0(pObj) < 255 );
    assert( Lag + Abc_ObjFaninL1(pObj) < 255 );
    SeqEdge0 = (Abc_ObjFanin0(pObj)->Id << 8) + Lag + Abc_ObjFaninL0(pObj);
    SeqEdge1 = (Abc_ObjFanin1(pObj)->Id << 8) + Lag + Abc_ObjFaninL1(pObj);
    // call for the children    
    Seq_FpgaMappingEdges_rec( pNtk, SeqEdge0, pObj            , vLeaves, vMapEdges );
    Seq_FpgaMappingEdges_rec( pNtk, SeqEdge1, Abc_ObjNot(pObj), vLeaves, vMapEdges );
}

/**Function*************************************************************

  Synopsis    [Collects the edges pointing to the leaves of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Seq_FpgaMappingBuild_rec( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtk, unsigned SeqEdge, int fTop, Vec_Ptr_t * vLeaves )
{
    Abc_Obj_t * pObj, * pObjNew, * pLeaf, * pFaninNew0, * pFaninNew1;
    unsigned SeqEdge0, SeqEdge1;
    int TotalLag, Lag, i;
    // get the object and the lag
    pObj = Abc_NtkObj( pNtk, SeqEdge >> 8 );
    Lag  = SeqEdge & 255;
    // if the node is the fanin of the cut, return
    Vec_PtrForEachEntry( vLeaves, pLeaf, i )
        if ( SeqEdge == (unsigned)pLeaf )
            return pObj->pCopy;
    // continue unfolding
    assert( Abc_NodeIsAigAnd(pObj) );
    // get new sequential edges
    assert( Lag + Abc_ObjFaninL0(pObj) < 255 );
    assert( Lag + Abc_ObjFaninL1(pObj) < 255 );
    SeqEdge0 = (Abc_ObjFanin0(pObj)->Id << 8) + Lag + Abc_ObjFaninL0(pObj);
    SeqEdge1 = (Abc_ObjFanin1(pObj)->Id << 8) + Lag + Abc_ObjFaninL1(pObj);
    // call for the children    
    pObjNew = fTop? pObj->pCopy : Abc_NtkCreateNode( pNtkNew );
    // solve subproblems
    pFaninNew0 = Seq_FpgaMappingBuild_rec( pNtkNew, pNtk, SeqEdge0, 0, vLeaves );
    pFaninNew1 = Seq_FpgaMappingBuild_rec( pNtkNew, pNtk, SeqEdge1, 0, vLeaves );
    // add the fanins to the node
    Abc_ObjAddFanin( pObjNew, Abc_ObjNotCond( pFaninNew0, Abc_ObjFaninC0(pObj) ) );
    Abc_ObjAddFanin( pObjNew, Abc_ObjNotCond( pFaninNew1, Abc_ObjFaninC1(pObj) ) );
    Seq_NodeDupLats( pObjNew, pObj, 0 );
    Seq_NodeDupLats( pObjNew, pObj, 1 );
    // set the lag of the new node equal to the internal lag plus mapping/retiming lag
    TotalLag = Lag + Seq_NodeGetLag(pObj);
    Seq_NodeSetLag( pObjNew, (char)TotalLag );
    return pObjNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


