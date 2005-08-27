/**CFile****************************************************************

  FileName    [aigStrash.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Strashing of the current network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigStrash.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "extra.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// static functions
static void        Abc_NtkStrashPerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkAig, bool fAllNodes );
static Abc_Obj_t * Abc_NodeStrash( Abc_Aig_t * pMan, Abc_Obj_t * pNode );
static Abc_Obj_t * Abc_NodeStrashSop( Abc_Aig_t * pMan, Abc_Obj_t * pNode, char * pSop );
static Abc_Obj_t * Abc_NodeStrashFactor( Abc_Aig_t * pMan, Abc_Obj_t * pNode, char * pSop );

extern char *      Mio_GateReadSop( void * pGate );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the strashed AIG network.]

  Description [Converts the logic network or the AIG into a 
  structurally hashed AIG.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkStrash( Abc_Ntk_t * pNtk, bool fAllNodes )
{
    int fCheck = 1;
    Abc_Ntk_t * pNtkAig;
    int nNodes;

    assert( !Abc_NtkIsNetlist(pNtk) );
    if ( Abc_NtkIsLogicBdd(pNtk) )
    {
//        printf( "Converting node functions from BDD to SOP.\n" );
        Abc_NtkBddToSop(pNtk);
    }
    // print warning about choice nodes
    if ( Abc_NtkCountChoiceNodes( pNtk ) )
        printf( "Warning: The choice nodes in the initial AIG are removed by strashing.\n" );
    // perform strashing
    pNtkAig = Abc_NtkStartFrom( pNtk, ABC_NTK_AIG );
    Abc_NtkStrashPerform( pNtk, pNtkAig, fAllNodes );
    Abc_NtkFinalize( pNtk, pNtkAig );
    // print warning about self-feed latches
    if ( Abc_NtkCountSelfFeedLatches(pNtkAig) )
        printf( "The network has %d self-feeding latches.\n", Abc_NtkCountSelfFeedLatches(pNtkAig) );
    if ( nNodes = Abc_AigCleanup(pNtkAig->pManFunc) )
        printf( "Cleanup has removed %d nodes.\n", nNodes );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkAig->pExdc = Abc_NtkStrash( pNtk->pExdc, 0 );
    // make sure everything is okay
    if ( fCheck && !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkStrash: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Appends the second network to the first.]

  Description [Modifies the first network by adding the logic of the second. 
  Performs structural hashing while appending the networks. Does not add 
  the COs of the second. Does not change the second network. Returns 0 
  if the appending failed, 1 otherise.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkAppend( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 )
{
    int fCheck = 1;
    Abc_Obj_t * pObj;
    int i;
    // the first network should be an AIG
    assert( Abc_NtkIsAig(pNtk1) );
    assert( Abc_NtkIsLogic(pNtk2) || Abc_NtkIsAig(pNtk2) ); 
    if ( Abc_NtkIsLogicBdd(pNtk2) )
    {
//        printf( "Converting node functions from BDD to SOP.\n" );
        Abc_NtkBddToSop(pNtk2);
    }
    // check that the networks have the same PIs
    // reorder PIs of pNtk2 according to pNtk1
    if ( !Abc_NtkCompareSignals( pNtk1, pNtk2, 1 ) )
        return 0;
    // perform strashing
    Abc_NtkCleanCopy( pNtk2 );
    Abc_NtkForEachCi( pNtk2, pObj, i )
        pObj->pCopy = Abc_NtkCi(pNtk1, i); 
    // add pNtk2 to pNtk1 while strashing
    Abc_NtkStrashPerform( pNtk2, pNtk1, 1 );
    // make sure that everything is okay
    if ( fCheck && !Abc_NtkCheck( pNtk1 ) )
    {
        printf( "Abc_NtkAppend: The network check has failed.\n" );
        return 0;
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Prepares the network for strashing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkStrashPerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew, bool fAllNodes )
{
    ProgressBar * pProgress;
    Abc_Aig_t * pMan = pNtkNew->pManFunc;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode, * pNodeNew, * pObj;
    int i;

    // perform strashing
    vNodes = Abc_NtkDfs( pNtk, fAllNodes );
    pProgress = Extra_ProgressBarStart( stdout, vNodes->nSize );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // get the node
        assert( Abc_ObjIsNode(pNode) );
         // strash the node
        pNodeNew = Abc_NodeStrash( pMan, pNode );
        // get the old object
        pObj = Abc_ObjFanout0Ntk( pNode );
        // make sure the node is not yet strashed
        assert( pObj->pCopy == NULL );
        // mark the old object with the new AIG node
        pObj->pCopy = pNodeNew;
    }
    Vec_PtrFree( vNodes );
    Extra_ProgressBarStop( pProgress );
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeStrash( Abc_Aig_t * pMan, Abc_Obj_t * pNode )
{
    int fUseFactor = 1;
    char * pSop;

    assert( Abc_ObjIsNode(pNode) );

    // consider the case when the graph is an AIG
    if ( Abc_NtkIsAig(pNode->pNtk) )
    {
//        Abc_Obj_t * pChild0, * pChild1;
//        pChild0 = Abc_ObjFanin0(pNode);
//        pChild1 = Abc_ObjFanin1(pNode);
        if ( Abc_NodeIsConst(pNode) )
            return Abc_AigConst1(pMan);
        return Abc_AigAnd( pMan, Abc_ObjChild0Copy(pNode), Abc_ObjChild1Copy(pNode) );
    }

    // get the SOP of the node
    if ( Abc_NtkIsLogicMap(pNode->pNtk) )
        pSop = Mio_GateReadSop(pNode->pData);
    else
        pSop = pNode->pData;

    // consider the cconstant node
    if ( Abc_NodeIsConst(pNode) )
    {
        // check if the SOP is constant
        if ( Abc_SopIsConst1(pSop) )
            return Abc_AigConst1(pMan);
        return Abc_ObjNot( Abc_AigConst1(pMan) );
    }

    // decide when to use factoring
    if ( fUseFactor && Abc_ObjFaninNum(pNode) > 2 && Abc_SopGetCubeNum(pSop) > 1 )
        return Abc_NodeStrashFactor( pMan, pNode, pSop );
    return Abc_NodeStrashSop( pMan, pNode, pSop );
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeStrashSop( Abc_Aig_t * pMan, Abc_Obj_t * pNode, char * pSop )
{
    Abc_Obj_t * pFanin, * pAnd, * pSum;
    Abc_Obj_t * pConst1 = Abc_AigConst1(pMan);
    char * pCube;
    int i, nFanins;

    // get the number of node's fanins
    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum(pSop) );
    // go through the cubes of the node's SOP
    pSum = Abc_ObjNot(pConst1);
    Abc_SopForEachCube( pSop, nFanins, pCube )
    {
        // create the AND of literals
        pAnd = pConst1;
        Abc_ObjForEachFanin( pNode, pFanin, i ) // pFanin can be a net
        {
            if ( pCube[i] == '1' )
                pAnd = Abc_AigAnd( pMan, pAnd, pFanin->pCopy );
            else if ( pCube[i] == '0' )
                pAnd = Abc_AigAnd( pMan, pAnd, Abc_ObjNot(pFanin->pCopy) );
        }
        // add to the sum of cubes
        pSum = Abc_AigOr( pMan, pSum, pAnd );
    }
    // decide whether to complement the result
    if ( Abc_SopIsComplement(pSop) )
        pSum = Abc_ObjNot(pSum);
    return pSum;
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeStrashFactor( Abc_Aig_t * pMan, Abc_Obj_t * pRoot, char * pSop )
{
    Vec_Int_t * vForm;
    Vec_Ptr_t * vAnds;
    Abc_Obj_t * pAnd, * pFanin;
    int i;
    // derive the factored form
    vForm = Ft_Factor( pSop );
    // collect the fanins
    vAnds = Vec_PtrAlloc( 20 );
    Abc_ObjForEachFanin( pRoot, pFanin, i )
        Vec_PtrPush( vAnds, pFanin->pCopy );
    // perform strashing
    pAnd = Abc_NodeStrashDec( pMan, vAnds, vForm );
    Vec_PtrFree( vAnds );
    Vec_IntFree( vForm );
    return pAnd;
}

/**Function*************************************************************

  Synopsis    [Strashes the factored form into the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeStrashDec( Abc_Aig_t * pMan, Vec_Ptr_t * vFanins, Vec_Int_t * vForm )
{
    Abc_Obj_t * pAnd, * pAnd0, * pAnd1;
    Ft_Node_t * pFtNode;
    int i, nVars;

    // sanity checks
    nVars = Ft_FactorGetNumVars( vForm );
    assert( nVars >= 0 );
    assert( vForm->nSize > nVars );

    // check for constant function
    pFtNode = Ft_NodeRead( vForm, 0 );
    if ( pFtNode->fConst )
        return Abc_ObjNotCond( Abc_AigConst1(pMan), pFtNode->fCompl );
    assert( nVars == vFanins->nSize );

    // compute the function of other nodes
    for ( i = nVars; i < vForm->nSize; i++ )
    {
        pFtNode = Ft_NodeRead( vForm, i );
        pAnd0   = Abc_ObjNotCond( vFanins->pArray[pFtNode->iFanin0], pFtNode->fCompl0 ); 
        pAnd1   = Abc_ObjNotCond( vFanins->pArray[pFtNode->iFanin1], pFtNode->fCompl1 ); 
        pAnd    = Abc_AigAnd( pMan, pAnd0, pAnd1 );
        Vec_PtrPush( vFanins, pAnd );
//printf( "Adding " );  Abc_AigPrintNode( pAnd );
    }
    assert( vForm->nSize = vFanins->nSize );

    // complement the result if necessary
    pFtNode = Ft_NodeReadLast( vForm );
    pAnd = Abc_ObjNotCond( pAnd, pFtNode->fCompl );
    return pAnd;
}

/**Function*************************************************************

  Synopsis    [Counts the number of new nodes added when using this factored form,]

  Description [Returns NodeMax + 1 if the number of nodes and levels exceeded 
  the given limit or the number of levels exceeded the maximum allowed level.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeStrashDecCount( Abc_Aig_t * pMan, Abc_Obj_t * pRoot, Vec_Ptr_t * vFanins, Vec_Int_t * vForm, Vec_Int_t * vLevels, int NodeMax, int LevelMax )
{
    Abc_Obj_t * pAnd, * pAnd0, * pAnd1, * pTop;
    Ft_Node_t * pFtNode;
    int i, nVars, LevelNew, LevelOld, Counter;

    // sanity checks
    nVars = Ft_FactorGetNumVars( vForm );
    assert( nVars >= 0 );
    assert( vForm->nSize > nVars );

    // check for constant function
    pFtNode = Ft_NodeRead( vForm, 0 );
    if ( pFtNode->fConst )
        return 0;
    assert( nVars == vFanins->nSize ); 

    // set the levels
    Vec_IntClear( vLevels );
    Vec_PtrForEachEntry( vFanins, pAnd, i )
        Vec_IntPush( vLevels, Abc_ObjRegular(pAnd)->Level );

    // compute the function of other nodes
    Counter = 0;
    for ( i = nVars; i < vForm->nSize; i++ )
    {
        pFtNode = Ft_NodeRead( vForm, i );
        // check for buffer/inverter
        if ( pFtNode->iFanin0 == pFtNode->iFanin1 )
        {
            assert( vForm->nSize == nVars + 1 );
            pAnd = Vec_PtrEntry(vFanins, pFtNode->iFanin0);  
            pAnd = Abc_ObjNotCond( pAnd, pFtNode->fCompl );
            Vec_PtrPush( vFanins, pAnd );
            break;
        }

        pAnd0   = Vec_PtrEntry(vFanins, pFtNode->iFanin0);  
        pAnd1   = Vec_PtrEntry(vFanins, pFtNode->iFanin1);  
        if ( pAnd0 && pAnd1 )
        {
            pAnd0 = Abc_ObjNotCond( pAnd0, pFtNode->fCompl0 );
            pAnd1 = Abc_ObjNotCond( pAnd1, pFtNode->fCompl1 );
            pAnd  = Abc_AigAndLookup( pMan, pAnd0, pAnd1 );
        }
        else
            pAnd = NULL;
        // count the number of added nodes
        if ( pAnd == NULL || Abc_NodeIsTravIdCurrent( Abc_ObjRegular(pAnd) ) )
        {
            if ( pAnd )
            {
//printf( "Reusing labeled " );  Abc_AigPrintNode( pAnd );
            }
            Counter++;
            if ( Counter > NodeMax )
            {
                Vec_PtrShrink( vFanins, nVars );
                return -1;
            }
        }
        else
        {
//printf( "Reusing " );  Abc_AigPrintNode( pAnd );
        }

        // count the number of new levels
        LevelNew = -1;
        if ( pAnd )
        {
            if ( Abc_ObjRegular(pAnd) == Abc_AigConst1(pMan) )
                LevelNew = 0;
            else if ( Abc_ObjRegular(pAnd) == Abc_ObjRegular(pAnd0) )
                LevelNew = (int)Abc_ObjRegular(pAnd0)->Level;
            else if ( Abc_ObjRegular(pAnd) == Abc_ObjRegular(pAnd1) )
                LevelNew = (int)Abc_ObjRegular(pAnd1)->Level;
        }
        if ( LevelNew == -1 )
            LevelNew = 1 + ABC_MAX( Vec_IntEntry(vLevels, pFtNode->iFanin0), Vec_IntEntry(vLevels, pFtNode->iFanin1) );

//        assert( pAnd == NULL || LevelNew == LevelOld );
        if ( pAnd ) 
        {
            LevelOld = (int)Abc_ObjRegular(pAnd)->Level;
            if ( LevelNew != LevelOld ) 
            {
                int x = 0;
                Abc_Obj_t * pFanin0, * pFanin1;
                pFanin0 = Abc_ObjFanin0( Abc_ObjRegular(pAnd) );
                pFanin1 = Abc_ObjFanin1( Abc_ObjRegular(pAnd) );
                x = 0;
            }
        }

        if ( LevelNew > LevelMax )
        {
            Vec_PtrShrink( vFanins, nVars );
            return -1;
        }
        Vec_PtrPush( vFanins, pAnd );
        Vec_IntPush( vLevels, LevelNew );
    }
    assert( vForm->nSize = vFanins->nSize );

    // check if this is the same form
    pTop = Vec_PtrEntryLast(vFanins);
    if ( Abc_ObjRegular(pTop) == pRoot )
    {
        assert( !Abc_ObjIsComplement(pTop) );
        Vec_PtrShrink( vFanins, nVars );
        return -1;
    }
    Vec_PtrShrink( vFanins, nVars );
    return Counter;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


