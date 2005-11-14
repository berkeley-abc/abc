/**CFile****************************************************************

  FileName    [seqFpgaCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Construction and manipulation of sequential AIGs.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: seqFpgaCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "seqInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t * Seq_NtkSeqFpgaDup( Abc_Ntk_t * pNtk );
static Abc_Ntk_t * Seq_NtkSeqFpgaMapped( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtk );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs FPGA mapping and retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkSeqFpgaRetime( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Seq_t * p;
    Abc_Ntk_t * pNtkNew;
    Abc_Ntk_t * pNtkMap;
    int RetValue;
    // find the best mapping and retiming (p->vMapping, p->vLags)
    Seq_NtkSeqFpgaMapping( pNtk, fVerbose );
    // duplicate the nodes contained in multiple cuts
    pNtkNew = Seq_NtkSeqFpgaDup( pNtk );
    // implement this retiming
    p = pNtkNew->pManFunc;
    RetValue = Seq_NtkImplementRetiming( pNtkNew, p->vLags, fVerbose );
    if ( RetValue == 0 )
        printf( "Retiming completed but initial state computation has failed.\n" );
    // create the final mapped network
    pNtkMap = Seq_NtkSeqFpgaMapped( pNtkNew, pNtk );
    Abc_NtkDelete( pNtkNew );
    return pNtkMap;
}

/**Function*************************************************************

  Synopsis    [Derives the network by duplicating some of the nodes.]

  Description [Information about mapping is given as 
  (1) array of mapping nodes (p->vMapAnds), 
  (2) array of best cuts for each node (p->vMapCuts), 
  (3) array of nodes subsumed by each cut (p->vMapBags),
  (4) array of lags of each node in the cut (p->vMapLags).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkSeqFpgaDup( Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pLeaf, * pNode, * pDriver, * pDriverNew;
    Vec_Ptr_t * vLeaves, * vInside, * vLags;
    int i, k, TotalLag;
    
    assert( Abc_NtkIsSeq(pNtk) );

    // start the network
    pNtkNew = Abc_NtkStartFrom( pNtk, pNtk->ntkType, pNtk->ntkFunc );

    // set the next pointers
    Abc_NtkForEachPi( pNtk, pObj, i )
        pObj->pNext = pObj->pCopy;
    Abc_NtkForEachNode( pNtk, pObj, i )
        pObj->pNext = NULL;

    // start the new sequential AIG manager
    Seq_Resize( pNtkNew->pManFunc, 10 + Abc_NtkPiNum(pNtk) + Abc_NtkPoNum(pNtk) + Vec_VecSizeSize(p->vMapBags) );

    // create the nodes
    Vec_PtrForEachEntry( p->vMapAnds, pObj, i )
    {
        // make sure the leaves are assigned
        vLeaves = Vec_VecEntry( p->vMapCuts, i );
        Vec_PtrForEachEntry( vLeaves, pLeaf, k )
        {
            assert( pLeaf->pNext );
            pLeaf->pCopy = pLeaf->pNext;
        }
        // recursively construct the internals
        vInside = Vec_VecEntry( p->vMapBags, i );
        vLags   = Vec_VecEntry( p->vMapLags, i );
        Vec_PtrForEachEntry( vInside, pNode, k )
        {
            Abc_NtkDupObj( pNtkNew, pNode );
            Abc_ObjAddFanin( pNode->pCopy, Abc_ObjChild0Copy(pNode) );
            Abc_ObjAddFanin( pNode->pCopy, Abc_ObjChild1Copy(pNode) );
            Abc_ObjSetFaninL( pNode->pCopy, 0, Abc_ObjFaninL(pNode, 0) );
            Abc_ObjSetFaninL( pNode->pCopy, 1, Abc_ObjFaninL(pNode, 1) );
            Seq_NodeDupLats( pNode->pCopy, pNode, 0 );
            Seq_NodeDupLats( pNode->pCopy, pNode, 1 );
            // set the lag of the new node
            TotalLag = Seq_NodeGetLag(pObj) + (char)Vec_PtrEntry(vLags, k);
            Seq_NodeSetLag( pNode->pCopy, (char)TotalLag );
        }
        // set the copy of the last node
        pObj->pNext = pObj->pCopy;
    }

    // set the POs
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        pDriver    = Abc_ObjFanin0(pObj);
        pDriverNew = Abc_ObjNotCond(pDriver->pNext, Abc_ObjFaninC0(pObj));
        Abc_ObjAddFanin( pObj->pCopy, pDriverNew );
    }

    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Seq_NtkSeqFpgaDup(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Derives the final mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkSeqFpgaMapped( Abc_Ntk_t * pNtkNew, Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkMap; 
    pNtkMap = NULL;
    if ( !Abc_NtkCheck( pNtkMap ) )
        fprintf( stdout, "Seq_NtkSeqFpgaMapped(): Network check has failed.\n" );
    return pNtkMap;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


