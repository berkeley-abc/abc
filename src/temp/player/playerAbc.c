/**CFile****************************************************************

  FileName    [playerAbc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [PLAyer decomposition package.]

  Synopsis    [Bridge between ABC and PLAyer.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 20, 2006.]

  Revision    [$Id: playerAbc.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "player.h"
#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Ivy_Man_t * Ivy_ManFromAbc( Abc_Ntk_t * p );
static Abc_Ntk_t * Ivy_ManToAbc( Abc_Ntk_t * pNtkOld, Ivy_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

#if 0

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to PLAyer for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Abc_NtkPlayer( void * pNtk, int nLutMax, int nPlaMax, int fVerbose )
{
    int fUseRewriting = 1;
    Ivy_Man_t * pMan, * pManExt;
    Abc_Ntk_t * pNtkAig;

    if ( !Abc_NtkIsStrash(pNtk) )
        return NULL;
    // convert to the new AIG manager
    pMan = Ivy_ManFromAbc( pNtk );
    // check the correctness of conversion
    if ( !Ivy_ManCheck( pMan ) )
    {
        printf( "Abc_NtkPlayer: Internal AIG check has failed.\n" );
        Ivy_ManStop( pMan );
        return NULL;
    }
    if ( fVerbose )
        Ivy_ManPrintStats( pMan );
    if ( fUseRewriting )
    {
        // simplify
        pMan = Ivy_ManResyn( pManExt = pMan, 1, 0 );
        Ivy_ManStop( pManExt );
        if ( fVerbose )
            Ivy_ManPrintStats( pMan );
    }
    // perform decomposition/mapping into PLAs/LUTs
    pManExt = Pla_ManDecompose( pMan, nLutMax, nPlaMax, fVerbose );
    Ivy_ManStop( pMan );
    pMan = pManExt;
    if ( fVerbose )
        Ivy_ManPrintStats( pMan );
    // convert from the extended AIG manager into an SOP network
    pNtkAig = Ivy_ManToAbc( pNtk, pMan );
    Ivy_ManStop( pMan );
    // chech the resulting network
    if ( !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkPlayer: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Converts from strashed AIG in ABC into strash AIG in IVY.]

  Description [Assumes DFS ordering of nodes in the AIG of ABC.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Man_t * Ivy_ManFromAbc( Abc_Ntk_t * pNtk )
{
    Ivy_Man_t * pMan;
    Abc_Obj_t * pObj;
    int i;
    // create the manager
    pMan = Ivy_ManStart( Abc_NtkCiNum(pNtk), Abc_NtkCoNum(pNtk), Abc_NtkNodeNum(pNtk) + 10 );
    // create the PIs
    Abc_NtkConst1(pNtk)->pCopy = (Abc_Obj_t *)Ivy_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Ivy_ManPi(pMan, i);
    // perform the conversion of the internal nodes
    Abc_AigForEachAnd( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Ivy_And( (Ivy_Obj_t *)Abc_ObjChild0Copy(pObj), (Ivy_Obj_t *)Abc_ObjChild1Copy(pObj) );
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Ivy_ObjConnect( Ivy_ManPo(pMan, i), (Ivy_Obj_t *)Abc_ObjChild0Copy(pObj) );
    Ivy_ManCleanup( pMan );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Converts AIG manager after PLA/LUT mapping into a logic ABC network.]

  Description [The AIG manager contains nodes with extended functionality.
  Node types are in pObj->Type. Node fanins are in pObj->vFanins. Functions
  of LUT nodes are in pMan->vTruths.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Ivy_ManToAbc( Abc_Ntk_t * pNtkOld, Ivy_Man_t * pMan )
{
    Abc_Ntk_t * pNtkNew;
    Vec_Int_t * vIvyNodes, * vIvyFanins, * vTruths = pMan->vTruths;
    Abc_Obj_t * pObj, * pObjNew, * pFaninNew;
    Ivy_Obj_t * pIvyNode, * pIvyFanin;
    int pCompls[PLAYER_FANIN_LIMIT];
    int i, k, Fanin, nFanins;
    // start the new ABC network
    pNtkNew = Abc_NtkStartFrom( pNtkOld, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    // transfer the pointers to the basic nodes
    Ivy_ManCleanTravId(pMan);
    Ivy_ManConst1(pMan)->TravId = Abc_NtkConst1(pNtkNew)->Id;
    Abc_NtkForEachCi( pNtkNew, pObjNew, i )
        Ivy_ManPi(pMan, i)->TravId = pObjNew->Id;
    // construct the logic network isomorphic to logic network in the AIG manager
    vIvyNodes = Ivy_ManDfsExt( pMan );
    Ivy_ManForEachNodeVec( pMan, vIvyNodes, pIvyNode, i )
    {
        // get fanins of the old node
        vIvyFanins = Ivy_ObjGetFanins( pIvyNode );
        nFanins = Vec_IntSize(vIvyFanins);
        // create the new node
        pObjNew = Abc_NtkCreateNode( pNtkNew );
        Vec_IntForEachEntry( vIvyFanins, Fanin, k )
        {
            pIvyFanin = Ivy_ObjObj( pIvyNode, Ivy_EdgeId(Fanin) );
            pFaninNew = Abc_NtkObj( pNtkNew, pIvyFanin->TravId );
            Abc_ObjAddFanin( pObjNew, pFaninNew );
            pCompls[k] = Ivy_EdgeIsComplement(Fanin);
            assert( Ivy_ObjIsAndMulti(pIvyNode) || nFanins == 1 || pCompls[k] == 0 ); // EXOR/LUT cannot have complemented fanins
        }
        assert( k <= PLAYER_FANIN_LIMIT );
        // create logic function of the node
        if ( Ivy_ObjIsAndMulti(pIvyNode) )
            pObjNew->pData = Abc_SopCreateAnd( pNtkNew->pManFunc, nFanins, pCompls );
        else if ( Ivy_ObjIsExorMulti(pIvyNode) )
            pObjNew->pData = Abc_SopCreateXorSpecial( pNtkNew->pManFunc, nFanins );
        else if ( Ivy_ObjIsLut(pIvyNode) )
            pObjNew->pData = Abc_SopCreateFromTruth( pNtkNew->pManFunc, nFanins, Ivy_ObjGetTruth(pIvyNode) );
        else assert( 0 );
        assert( Abc_SopGetVarNum(pObjNew->pData) == nFanins );
        pIvyNode->TravId = pObjNew->Id;
    }
//Pla_ManComputeStats( pMan, vIvyNodes );
    Vec_IntFree( vIvyNodes );
    // connect the PO nodes
    Abc_NtkForEachCo( pNtkOld, pObj, i )
    {
        // get the old fanin of the PO node
        vIvyFanins = Ivy_ObjGetFanins( Ivy_ManPo(pMan, i) );
        Fanin     = Vec_IntEntry( vIvyFanins, 0 );
        pIvyFanin = Ivy_ManObj( pMan, Ivy_EdgeId(Fanin) );
        // get the new ABC node corresponding to the old fanin
        pFaninNew = Abc_NtkObj( pNtkNew, pIvyFanin->TravId );
        if ( Ivy_EdgeIsComplement(Fanin) ) // complement
        {
//            pFaninNew = Abc_NodeCreateInv(pNtkNew, pFaninNew);
            if ( Abc_ObjIsCi(pFaninNew) )
                pFaninNew = Abc_NodeCreateInv(pNtkNew, pFaninNew);
            else
            {
                // clone the node
                pObjNew = Abc_NodeClone( pFaninNew );
                // set complemented functions
                pObjNew->pData = Abc_SopRegister( pNtkNew->pManFunc, pFaninNew->pData );
                Abc_SopComplement(pObjNew->pData); 
                // return the new node
                pFaninNew = pObjNew;
            }
            assert( Abc_SopGetVarNum(pFaninNew->pData) == Abc_ObjFaninNum(pFaninNew) );
        }
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
    }
    // remove dangling nodes
    Abc_NtkForEachNode(pNtkNew, pObj, i)
        if ( Abc_ObjFanoutNum(pObj) == 0 )
            Abc_NtkDeleteObj(pObj); 
    // fix CIs feeding directly into COs
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    return pNtkNew;
}

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


