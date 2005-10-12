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
static void Abc_ObjRetimeBackwardUpdateEdge( Abc_Obj_t * pObj, int Edge, stmm_table * tTable );
static void Abc_NtkRetimeSetInitialValues( Abc_Ntk_t * pNtk, stmm_table * tTable, int * pModel );
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Implements the retiming on the sequential AIG.]

  Description [Split the retiming into forward and backward.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkImplementRetiming( Abc_Ntk_t * pNtk, Vec_Str_t * vLags, int fVerbose )
{
    Vec_Int_t * vSteps;
    Vec_Ptr_t * vMoves;
    int RetValue;

    // forward retiming
    vSteps = Abc_NtkUtilRetimingSplit( vLags, 1 );
    // translate each set of steps into moves
    if ( fVerbose )
    printf( "The number of forward steps  = %6d.\n", Vec_IntSize(vSteps) );
    vMoves = Abc_NtkUtilRetimingGetMoves( pNtk, vSteps, 1 );
    if ( fVerbose )
    printf( "The number of forward moves  = %6d.\n", Vec_PtrSize(vMoves) );
    // implement this retiming
    Abc_NtkImplementRetimingForward( pNtk, vMoves );
    Vec_IntFree( vSteps );
    Vec_PtrFree( vMoves );

    // backward retiming
    vSteps = Abc_NtkUtilRetimingSplit( vLags, 0 );
    // translate each set of steps into moves
    if ( fVerbose )
    printf( "The number of backward steps = %6d.\n", Vec_IntSize(vSteps) );
    vMoves = Abc_NtkUtilRetimingGetMoves( pNtk, vSteps, 0 );
    if ( fVerbose )
    printf( "The number of backward moves = %6d.\n", Vec_PtrSize(vMoves) );
    // implement this retiming
    RetValue = Abc_NtkImplementRetimingBackward( pNtk, vMoves, fVerbose );
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
        Abc_ObjFaninLInsertLast( pFanout, Abc_ObjEdgeNum(pObj, pFanout), Init );
}



/**Function*************************************************************

  Synopsis    [Implements the given retiming on the sequential AIG.]

  Description [Returns 0 of initial state computation fails.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkImplementRetimingBackward( Abc_Ntk_t * pNtk, Vec_Ptr_t * vMoves, int fVerbose )
{
    Abc_RetEdge_t RetEdge;
    stmm_table * tTable;
    stmm_generator * gen;
    Vec_Int_t * vValues;
    Abc_Ntk_t * pNtkProb, * pNtkMiter, * pNtkCnf;
    Abc_Obj_t * pNode, * pNodeNew;
    int * pModel, RetValue, i, clk;

    // return if the retiming is trivial
    if ( Vec_PtrSize(vMoves) == 0 )
        return 1;

    // create the network for the initial state computation
    // start the table and the array of PO values
    pNtkProb = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP );
    tTable   = stmm_init_table( stmm_numcmp, stmm_numhash );
    vValues  = Vec_IntAlloc( 100 );

    // perform the backward moves and build the network for initial state computation
    RetValue = 0;
    Vec_PtrForEachEntry( vMoves, pNode, i )
        RetValue |= Abc_ObjRetimeBackward( pNode, pNtkProb, tTable, vValues );

    // add the PIs corresponding to the white spots
    stmm_foreach_item( tTable, gen, (char **)&RetEdge, (char **)&pNodeNew )
        Abc_ObjAddFanin( pNodeNew, Abc_NtkCreatePi(pNtkProb) );

    // add the PI/PO names
    Abc_NtkAddDummyPiNames( pNtkProb );
    Abc_NtkAddDummyPoNames( pNtkProb );

    // make sure everything is okay with the network structure
    if ( !Abc_NtkDoCheck( pNtkProb ) )
    {
        printf( "Abc_NtkImplementRetimingBackward: The internal network check has failed.\n" );
        Abc_NtkRetimeSetInitialValues( pNtk, tTable, NULL );
        Abc_NtkDelete( pNtkProb );
        stmm_free_table( tTable );
        Vec_IntFree( vValues );
        return 0;
    }

    // check if conflict is found
    if ( RetValue )
    {
        printf( "Abc_NtkImplementRetimingBackward: A top level conflict is detected. DC latch values are used.\n" );
        Abc_NtkRetimeSetInitialValues( pNtk, tTable, NULL );
        Abc_NtkDelete( pNtkProb );
        stmm_free_table( tTable );
        Vec_IntFree( vValues );
        return 0;
    }

    // get the miter cone
    pNtkMiter = Abc_NtkCreateCone( pNtkProb, pNtkProb->vCos, vValues );
    Abc_NtkDelete( pNtkProb );
    Vec_IntFree( vValues );

    if ( fVerbose )
    printf( "The number of ANDs in the AIG = %5d.\n", Abc_NtkNodeNum(pNtkMiter) );

    // transform the miter into a logic network for efficient CNF construction
    pNtkCnf = Abc_NtkRenode( pNtkMiter, 0, 100, 1, 0, 0 );
    Abc_NtkDelete( pNtkMiter );

    // solve the miter
clk = clock();
    RetValue = Abc_NtkMiterSat( pNtkCnf, 30, 0 );
if ( fVerbose )
if ( clock() - clk > 500 )
{
PRT( "SAT solving time", clock() - clk );
}
    pModel = pNtkCnf->pModel;  pNtkCnf->pModel = NULL;
    Abc_NtkDelete( pNtkCnf );

    // analyze the result
    if ( RetValue == -1 || RetValue == 1 )
    {
        Abc_NtkRetimeSetInitialValues( pNtk, tTable, NULL );
        if ( RetValue == 1 )
            printf( "Abc_NtkImplementRetimingBackward: The problem is unsatisfiable. DC latch values are used.\n" );
        else
            printf( "Abc_NtkImplementRetimingBackward: The SAT problem timed out. DC latch values are used.\n" );
        stmm_free_table( tTable );
        return 0;
    }

    // set the values of the latches
    Abc_NtkRetimeSetInitialValues( pNtk, tTable, pModel );
    stmm_free_table( tTable );
    free( pModel );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Retimes node backward by one latch.]

  Description [Constructs the problem for initial state computation.
  Returns 1 if the conflict is found.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjRetimeBackward( Abc_Obj_t * pObj, Abc_Ntk_t * pNtkNew, stmm_table * tTable, Vec_Int_t * vValues )  
{
    Abc_Obj_t * pFanout;
    Abc_InitType_t Init, Value;
    Abc_RetEdge_t RetEdge;
    Abc_Obj_t * pNodeNew, * pFanoutNew, * pBuffer;
    int i, Edge, fMet0, fMet1, fMetN;

    // make sure the node can be retimed
    assert( Abc_ObjFanoutLMin(pObj) > 0 );
    // get the fanout values
    fMet0 = fMet1 = fMetN = 0;
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        Init = Abc_ObjFaninLGetInitLast( pFanout, Abc_ObjEdgeNum(pObj, pFanout) );
        if ( Init == ABC_INIT_ZERO )
            fMet0 = 1;
        else if ( Init == ABC_INIT_ONE )
            fMet1 = 1;
        else if ( Init == ABC_INIT_NONE )
            fMetN = 1;
    }

    // consider the case when all fanout latchs have don't-care values
    // the new values on the fanin edges will be don't-cares
    if ( !fMet0 && !fMet1 && !fMetN )
    {
        // update the fanout edges
        Abc_ObjForEachFanout( pObj, pFanout, i )
            Abc_ObjFaninLDeleteLast( pFanout, Abc_ObjEdgeNum(pObj, pFanout) );
        // update the fanin edges
        Abc_ObjRetimeBackwardUpdateEdge( pObj, 0, tTable );
        Abc_ObjRetimeBackwardUpdateEdge( pObj, 1, tTable );
        Abc_ObjFaninLInsertFirst( pObj, 0, ABC_INIT_DC );
        Abc_ObjFaninLInsertFirst( pObj, 1, ABC_INIT_DC );
        return 0;
    }
    // the initial values on the fanout edges contain 0, 1, or unknown
    // the new values on the fanin edges will be unknown

    // add new AND-gate to the network
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    pNodeNew->pData = Abc_SopCreateAnd2( pNtkNew->pManFunc, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );

    // add PO fanouts if any
    if ( fMet0 )
    {
        Abc_ObjAddFanin( Abc_NtkCreatePo(pNtkNew), pNodeNew );
        Vec_IntPush( vValues, 0 );
    }
    if ( fMet1 )
    {
        Abc_ObjAddFanin( Abc_NtkCreatePo(pNtkNew), pNodeNew );
        Vec_IntPush( vValues, 1 );
    }

    // perform the changes
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        Edge = Abc_ObjEdgeNum( pObj, pFanout );
        Value = Abc_ObjFaninLDeleteLast( pFanout, Edge );
        if ( Value != ABC_INIT_NONE )
            continue;
        // value is unknown, remove it from the table
        RetEdge.iNode  = pFanout->Id;
        RetEdge.iEdge  = Edge;
        RetEdge.iLatch = Abc_ObjFaninL( pFanout, Edge ); // after edge is removed
        if ( !stmm_delete( tTable, (char **)&RetEdge, (char **)&pFanoutNew ) )
            assert( 0 );
        // create the fanout of the AND gate
        Abc_ObjAddFanin( pFanoutNew, pNodeNew );
    }

    // update the fanin edges
    Abc_ObjRetimeBackwardUpdateEdge( pObj, 0, tTable );
    Abc_ObjRetimeBackwardUpdateEdge( pObj, 1, tTable );
    Abc_ObjFaninLInsertFirst( pObj, 0, ABC_INIT_NONE );
    Abc_ObjFaninLInsertFirst( pObj, 1, ABC_INIT_NONE );

    // add the buffer
    pBuffer = Abc_NtkCreateNode( pNtkNew );
    pBuffer->pData = Abc_SopCreateBuf( pNtkNew->pManFunc );
    Abc_ObjAddFanin( pNodeNew, pBuffer );
    // point to it from the table
    RetEdge.iNode  = pObj->Id;
    RetEdge.iEdge  = 0;
    RetEdge.iLatch = 0;
    if ( stmm_insert( tTable, (char *)Abc_RetEdge2Int(RetEdge), (char *)pBuffer ) )
        assert( 0 );

    // add the buffer
    pBuffer = Abc_NtkCreateNode( pNtkNew );
    pBuffer->pData = Abc_SopCreateBuf( pNtkNew->pManFunc );
    Abc_ObjAddFanin( pNodeNew, pBuffer );
    // point to it from the table
    RetEdge.iNode  = pObj->Id;
    RetEdge.iEdge  = 1;
    RetEdge.iLatch = 0;
    if ( stmm_insert( tTable, (char *)Abc_RetEdge2Int(RetEdge), (char *)pBuffer ) )
        assert( 0 );

    // report conflict is found
    return fMet0 && fMet1;
}

/**Function*************************************************************

  Synopsis    [Generates the printable edge label with the initial state.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjRetimeBackwardUpdateEdge( Abc_Obj_t * pObj, int Edge, stmm_table * tTable )
{
    Abc_Obj_t * pFanoutNew;
    Abc_RetEdge_t RetEdge;
    Abc_InitType_t Init;
    int nLatches, i;

    // get the number of latches on the edge
    nLatches = Abc_ObjFaninL( pObj, Edge );
    assert( nLatches <= ABC_MAX_EDGE_LATCH );
    for ( i = nLatches - 1; i >= 0; i-- )
    {
        // get the value of this latch
        Init = Abc_ObjFaninLGetInitOne( pObj, Edge, i );
        if ( Init != ABC_INIT_NONE )
            continue;
        // get the retiming edge
        RetEdge.iNode  = pObj->Id;
        RetEdge.iEdge  = Edge;
        RetEdge.iLatch = i;
        // remove entry from table and add it with a different key
        if ( !stmm_delete( tTable, (char **)&RetEdge, (char **)&pFanoutNew ) )
            assert( 0 );
        RetEdge.iLatch++;
        if ( stmm_insert( tTable, (char *)Abc_RetEdge2Int(RetEdge), (char *)pFanoutNew ) )
            assert( 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Sets the initial values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRetimeSetInitialValues( Abc_Ntk_t * pNtk, stmm_table * tTable, int * pModel )
{
    Abc_Obj_t * pNode;
    stmm_generator * gen;
    Abc_RetEdge_t RetEdge;
    Abc_InitType_t Init;
    int i;

    i = 0;
    stmm_foreach_item( tTable, gen, (char **)&RetEdge, NULL )
    {
        pNode = Abc_NtkObj( pNtk, RetEdge.iNode );
        Init = pModel? (pModel[i]? ABC_INIT_ONE : ABC_INIT_ZERO) : ABC_INIT_DC;
        Abc_ObjFaninLSetInitOne( pNode, RetEdge.iEdge, RetEdge.iLatch, Init );
        i++;
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


