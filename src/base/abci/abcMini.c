/**CFile****************************************************************

  FileName    [abcMini.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface to the minimalistic AIG package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcMini.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/abc/miniaig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Mini_Aig_t * Abc_NtkToMini( Abc_Ntk_t * pNtk );
static Abc_Ntk_t * Abc_NtkFromMini( Abc_Ntk_t * pNtkOld, Mini_Aig_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeFanin0Copy( Abc_Ntk_t * pNtk, Vec_Int_t * vCopies, Mini_Aig_t * p, int Id )
{
    int Lit = Mini_AigNodeFanin0( p, Id );
    Lit = Abc_LitNotCond( Vec_IntEntry(vCopies, Abc_Lit2Var(Lit)), Abc_LitIsCompl(Lit) );
    return Abc_ObjNotCond( Abc_NtkObj(pNtk, Abc_Lit2Var(Lit)), Abc_LitIsCompl(Lit) ); 
}
Abc_Obj_t * Abc_NodeFanin1Copy( Abc_Ntk_t * pNtk, Vec_Int_t * vCopies, Mini_Aig_t * p, int Id )
{
    int Lit = Mini_AigNodeFanin1( p, Id );
    Lit = Abc_LitNotCond( Vec_IntEntry(vCopies, Abc_Lit2Var(Lit)), Abc_LitIsCompl(Lit) );
    return Abc_ObjNotCond( Abc_NtkObj(pNtk, Abc_Lit2Var(Lit)), Abc_LitIsCompl(Lit) ); 
}
int Abc_NodeToLit( Abc_Obj_t * pObj )
{
    return Abc_LitNotCond( Abc_ObjId(Abc_ObjRegular(pObj)), Abc_ObjIsComplement(pObj) );
}

Abc_Ntk_t * Abc_NtkFromMiniAig( Mini_Aig_t * p )
{
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj;
    Vec_Int_t * vCopies;
    int i, nNodes;
    // get the number of nodes
    nNodes = Mini_AigNumNodes(p);
    // create ABC network
    pNtk = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1 );
    // create mapping from MiniAIG into ABC objects
    vCopies = Vec_IntAlloc( nNodes );
    Vec_IntPush( vCopies, Abc_LitNot(Abc_NodeToLit(Abc_AigConst1(pNtk))) );
    // iterate through the objects
    for ( i = 1; i < nNodes; i++ )
    {
        if ( Mini_AigNodeIsPi( p, i ) )
            pObj = Abc_NtkCreatePi(pNtk);
        else if ( Mini_AigNodeIsPo( p, i ) )
            Abc_ObjAddFanin( (pObj = Abc_NtkCreatePo(pNtk)), Abc_NodeFanin0Copy(pNtk, vCopies, p, i) );
        else if ( Mini_AigNodeIsAnd( p, i ) )
            pObj = Abc_AigAnd((Abc_Aig_t *)pNtk->pManFunc, Abc_NodeFanin0Copy(pNtk, vCopies, p, i), Abc_NodeFanin1Copy(pNtk, vCopies, p, i));
        else assert( 0 );
        Vec_IntPush( vCopies, Abc_NodeToLit(pObj) );
    }
    Abc_AigCleanup( (Abc_Aig_t *)pNtk->pManFunc );
    Vec_IntFree( vCopies );
    Abc_NtkAddDummyPiNames( pNtk );
    Abc_NtkAddDummyPoNames( pNtk );
    if ( !Abc_NtkCheck( pNtk ) )
        fprintf( stdout, "Abc_NtkFromMini(): Network check has failed.\n" );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mini_Aig_t * Abc_NtkToMiniAig( Abc_Ntk_t * pNtk )
{
    Mini_Aig_t * p = NULL;
/*
    Abc_Obj_t * pObj;
    int i;
    // create the manager
    p = Hop_ManStart();
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Hop_ManConst1(p);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Hop_ObjCreatePi(p);
    // perform the conversion of the internal nodes (assumes DFS ordering)
    Abc_NtkForEachNode( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Hop_And( p, (Hop_Obj_t *)Abc_ObjChild0Copy(pObj), (Hop_Obj_t *)Abc_ObjChild1Copy(pObj) );
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Hop_ObjCreatePo( p, (Hop_Obj_t *)Abc_ObjChild0Copy(pObj) );
    Hop_ManCleanup( p );
*/
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkInputMiniAig( Mini_Aig_t * p )
{
    Abc_Ntk_t * pNtk;
    Abc_Frame_t * pAbc = Abc_FrameReadGlobalFrame();
    if ( pAbc == NULL )
        printf( "ABC framework is not initialized by calling Abc_Start()\n" );
    pNtk = Abc_NtkFromMiniAig( p );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
//    Abc_NtkDelete( pNtk );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

