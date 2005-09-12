/**CFile****************************************************************

  FileName    [abcRetImpl.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Implementation of retiming.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRetImpl.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abcs.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Abc_ObjRetimeForward( Abc_Obj_t * pObj );
static int  Abc_ObjRetimeBackward( Abc_Obj_t * pObj, Abc_Ntk_t * pNtk, stmm_table * tTable, Vec_Int_t * vValues );
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Implements the retiming on the sequential AIG.]

  Description [Split the retiming into forward and backward.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkImplementRetiming( Abc_Ntk_t * pNtk, Vec_Str_t * vLags )
{
    Vec_Int_t * vSteps;
    Vec_Ptr_t * vMoves;
    int RetValue;

    // forward retiming
    vSteps = Abc_NtkUtilRetimingSplit( vLags, 1 );
    // translate each set of steps into moves
    vMoves = Abc_NtkUtilRetimingGetMoves( pNtk, vSteps, 1 );
    // implement this retiming
    Abc_NtkImplementRetimingForward( pNtk, vMoves );
    Vec_IntFree( vSteps );
    Vec_PtrFree( vMoves );

    // backward retiming
    vSteps = Abc_NtkUtilRetimingSplit( vLags, 0 );
    // translate each set of steps into moves
    vMoves = Abc_NtkUtilRetimingGetMoves( pNtk, vSteps, 0 );
    // implement this retiming
    RetValue = Abc_NtkImplementRetimingBackward( pNtk, vMoves );
    Vec_IntFree( vSteps );
    Vec_PtrFree( vMoves );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Implements the given retiming on the sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkImplementRetimingForward( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMoves )
{
    Abc_Obj_t * pNode;
    int i;
    Vec_PtrForEachEntry( vMoves, pNode, i )
        Abc_ObjRetimeForward( pNode );
}

/**Function*************************************************************

  Synopsis    [Implements the given retiming on the sequential AIG.]

  Description [Returns 0 of initial state computation fails.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkImplementRetimingBackward( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMoves )
{
    Abc_RetEdge_t RetEdge;
    stmm_table * tTable;
    stmm_generator * gen;
    Vec_Int_t * vValues;
    Abc_Ntk_t * pNtkProb, * pNtkMiter, * pNtkCnf;
    Abc_Obj_t * pNode, * pNodeNew;
    int * pModel, Init, nDigits, RetValue, i;

    // return if the retiming is trivial
    if ( Vec_PtrSize(vMoves) == 0 )
        return 1;

    // start the table and the array of PO values
    tTable = stmm_init_table( stmm_numcmp, stmm_numhash );
    vValues = Vec_IntAlloc( 100 );

    // create the network for the initial state computation
    pNtkProb = Abc_NtkAlloc( ABC_TYPE_LOGIC, ABC_FUNC_SOP );

    // perform the backward moves and build the network
    Vec_PtrForEachEntry( vMoves, pNode, i )
        Abc_ObjRetimeBackward( pNode, pNtkProb, tTable, vValues );

    // add the PIs corresponding to the white spots
    stmm_foreach_item( tTable, gen, (char **)&RetEdge, (char **)&pNodeNew )
        Abc_ObjAddFanin( pNodeNew, Abc_NtkCreatePi(pNtkProb) );

    // add the PI/PO names
    nDigits = Extra_Base10Log( Abc_NtkPiNum(pNtkProb) );
    Abc_NtkForEachPi( pNtkProb, pNodeNew, i )
        Abc_NtkLogicStoreName( pNodeNew, Abc_ObjNameDummy("pi", i, nDigits) );
    nDigits = Extra_Base10Log( Abc_NtkPoNum(pNtkProb) );
    Abc_NtkForEachPo( pNtkProb, pNodeNew, i )
        Abc_NtkLogicStoreName( pNodeNew, Abc_ObjNameDummy("po", i, nDigits) );

    // make sure everything is okay with the network structure
    if ( !Abc_NtkDoCheck( pNtkProb ) )
    {
        printf( "Abc_NtkImplementRetimingBackward: The internal network check has failed.\n" );
        return 0;
    }

    // get the miter cone
    pNtkMiter = Abc_NtkCreateCone( pNtkProb, pNtkProb->vCos, vValues );
    Abc_NtkDelete( pNtkProb );
    Vec_IntFree( vValues );

    // transform the miter into a logic network for efficient CNF construction
    pNtkCnf = Abc_NtkRenode( pNtkMiter, 0, 100, 1, 0, 0 );
    Abc_NtkDelete( pNtkMiter );

    // solve the miter
    RetValue = Abc_NtkMiterSat( pNtkCnf, 30, 0 );
    pModel = pNtkCnf->pModel;  pNtkCnf->pModel = NULL;
    Abc_NtkDelete( pNtkCnf );

    // analyze the result
    if ( RetValue == -1 || RetValue == 1 )
    {
        stmm_free_table( tTable );
        return 0;
    }

    // set the values of the latches
    i = 0;
    stmm_foreach_item( tTable, gen, (char **)&RetEdge, (char **)&pNodeNew )
    {
        pNode = Abc_NtkObj( pNtk, RetEdge.iNode );
        Init = pModel[i]? ABC_INIT_ONE : ABC_INIT_ZERO;
        Abc_ObjFaninLSetInitOne( pNode, RetEdge.iEdge, RetEdge.iLatch, Init );
        i++;
    }
    stmm_free_table( tTable );
    free( pModel );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Retimes node forward by one latch.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjRetimeForward( Abc_Obj_t * pObj )  
{
    Abc_Obj_t * pFanout;
    int Init0, Init1, Init, i;
    assert( Abc_ObjFaninNum(pObj) == 2 );
    assert( Abc_ObjFaninL0(pObj) >= 1 );
    assert( Abc_ObjFaninL1(pObj) >= 1 );
    // remove the init values from the fanins
    Init0 = Abc_ObjFaninLDeleteFirst( pObj, 0 );
    Init1 = Abc_ObjFaninLDeleteFirst( pObj, 1 );
    assert( Init0 != ABC_INIT_NONE );
    assert( Init1 != ABC_INIT_NONE );
    // take into account the complements in the node
    if ( Abc_ObjFaninC0(pObj) )
    {
        if ( Init0 == ABC_INIT_ZERO )
            Init0 = ABC_INIT_ONE;
        else if ( Init0 == ABC_INIT_ONE )
            Init0 = ABC_INIT_ZERO;
    }
    if ( Abc_ObjFaninC1(pObj) )
    {
        if ( Init1 == ABC_INIT_ZERO )
            Init1 = ABC_INIT_ONE;
        else if ( Init1 == ABC_INIT_ONE )
            Init1 = ABC_INIT_ZERO;
    }
    // compute the value at the output of the node
    if ( Init0 == ABC_INIT_ZERO || Init1 == ABC_INIT_ZERO )
        Init = ABC_INIT_ZERO;
    else if ( Init0 == ABC_INIT_ONE && Init1 == ABC_INIT_ONE )
        Init = ABC_INIT_ONE;
    else
        Init = ABC_INIT_DC;
    // add the init values to the fanouts
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Abc_ObjFaninLInsertLast( pFanout, Abc_ObjEdgeNum(pFanout, pObj), Init );
}

/**Function*************************************************************

  Synopsis    [Retimes node backward by one latch.]

  Description [Constructs the problem for initial state computation.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjRetimeBackward( Abc_Obj_t * pObj, Abc_Ntk_t * pNtkNew, stmm_table * tTable, Vec_Int_t * vValues )  
{
    Abc_Obj_t * pFanout;
    Abc_InitType_t Init, Value;
    Abc_RetEdge_t Edge;
    Abc_Obj_t * pNodeNew, * pFanoutNew, * pBuf;
    unsigned Entry;
    int i, fMet0, fMet1, fMetX;

    // make sure the node can be retimed
    assert( Abc_ObjFanoutLMin(pObj) > 0 );
    // get the fanout values
    fMet0 = fMet1 = fMetX = 0;
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        Init = Abc_ObjFaninLGetInitLast( pFanout, Abc_ObjEdgeNum(pObj, pFanout) );
        if ( Init == ABC_INIT_ZERO )
            fMet0 = 1;
        else if ( Init == ABC_INIT_ONE )
            fMet1 = 1;
        else if ( Init == ABC_INIT_NONE )
            fMetX = 1;
    }
    // quit if conflict is found
    if ( fMet0 && fMet1 )
        return 0;

    // get the new initial value
    if ( !fMet0 && !fMet1 && !fMetX )
    {
        Init = ABC_INIT_DC;
        // do not add the node
        pNodeNew = NULL;
    }
    else
    {
        Init = ABC_INIT_NONE;
        // add the node to the network
        pNodeNew = Abc_NtkCreateNode( pNtkNew );
        pNodeNew->pData = Abc_SopCreateAnd2( pNtkNew->pManFunc, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    }

    // perform the changes
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        Edge.iNode = pFanout->Id;
        Edge.iEdge = Abc_ObjEdgeNum(pObj, pFanout);
        Edge.iLatch = Abc_ObjFaninL( pFanout, Edge.iEdge ) - 1;
        // try to delete this edge
        stmm_delete( tTable, (char **)&Edge, (char **)&pFanoutNew );
        // delete the entry
        Value = Abc_ObjFaninLDeleteLast( pFanout, Edge.iEdge );
        if ( Value == ABC_INIT_NONE )
            Abc_ObjAddFanin( pFanoutNew, pNodeNew );
    }

    // update the table for each of the edges
    Abc_ObjFaninLForEachValue( pObj, 0, Entry, i, Value )
    {
        if ( Value != ABC_INIT_NONE )
            continue;
        if ( !stmm_delete( tTable, (char **)&Edge, (char **)&pFanoutNew ) )
            assert( 0 );
        Edge.iLatch++;
        if ( stmm_insert( tTable, (char *)Abc_RetEdge2Int(Edge), (char *)pFanoutNew ) )
            assert( 0 );
    }
    Abc_ObjFaninLForEachValue( pObj, 1, Entry, i, Value )
    {
        if ( Value != ABC_INIT_NONE )
            continue;
        if ( !stmm_delete( tTable, (char **)&Edge, (char **)&pFanoutNew ) )
            assert( 0 );
        Edge.iLatch++;
        if ( stmm_insert( tTable, (char *)Abc_RetEdge2Int(Edge), (char *)pFanoutNew ) )
            assert( 0 );
    }
    Abc_ObjFaninLInsertFirst( pObj, 0, Init );
    Abc_ObjFaninLInsertFirst( pObj, 1, Init );

    // do not insert the don't-care node into the network
    if ( Init == ABC_INIT_DC )
        return 1;

    // add the buffer
    pBuf = Abc_NtkCreateNode( pNtkNew );
    pBuf->pData = Abc_SopCreateBuf( pNtkNew->pManFunc );
    Abc_ObjAddFanin( pNodeNew, pBuf );
    // point to it from the table
    Edge.iNode = pObj->Id;
    Edge.iEdge = 0;
    Edge.iLatch = 0;
    if ( stmm_insert( tTable, (char *)Abc_RetEdge2Int(Edge), (char *)pBuf ) )
        assert( 0 );

    // add the buffer
    pBuf = Abc_NtkCreateNode( pNtkNew );
    pBuf->pData = Abc_SopCreateBuf( pNtkNew->pManFunc );
    Abc_ObjAddFanin( pNodeNew, pBuf );
    // point to it from the table
    Edge.iNode = pObj->Id;
    Edge.iEdge = 1;
    Edge.iLatch = 0;
    if ( stmm_insert( tTable, (char *)Abc_RetEdge2Int(Edge), (char *)pBuf ) )
        assert( 0 );

    // check if the output value is required
    if ( fMet0 || fMet1 )
    {
        // add the PO and the value
        Abc_ObjAddFanin( Abc_NtkCreatePo(pNtkNew), pNodeNew );
        Vec_IntPush( vValues, fMet1 );
    }
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


