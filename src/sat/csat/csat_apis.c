/**CFile****************************************************************

  FileName    [csat_apis.h]

  PackageName [Interface to CSAT.]

  Synopsis    [APIs, enums, and data structures expected from the use of CSAT.]

  Author      [Alan Mishchenko <alanmi@eecs.berkeley.edu>]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 28, 2005]

  Revision    [$Id: csat_apis.h,v 1.00 2005/08/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "fraig.h"
#include "csat_apis.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

struct CSAT_ManagerStruct_t
{
    // information about the problem
    stmm_table *          tName2Node;    // the hash table mapping names to nodes
    stmm_table *          tNode2Name;    // the hash table mapping nodes to names
    Abc_Ntk_t *           pNtk;          // the starting ABC network
    Abc_Ntk_t *           pTarget;       // the AIG representing the target
    char *                pDumpFileName; // the name of the file to dump the target network
    // solving parameters
    int                   mode;          // 0 = baseline;  1 = resource-aware fraiging
    Fraig_Params_t        Params;        // the set of parameters to call FRAIG package
    // information about the target 
    int                   nog;           // the numbers of gates in the target
    Vec_Ptr_t *           vNodes;        // the gates in the target
    Vec_Int_t *           vValues;       // the values of gate's outputs in the target
    // solution
    CSAT_Target_ResultT * pResult;       // the result of solving the target
};

static CSAT_Target_ResultT * CSAT_TargetResAlloc( int nVars );
static void CSAT_TargetResFree( CSAT_Target_ResultT * p );
static char * CSAT_GetNodeName( CSAT_Manager mng, Abc_Obj_t * pNode );

// some external procedures
extern Fraig_Man_t * Abc_NtkToFraig( Abc_Ntk_t * pNtk, Fraig_Params_t * pParams, int fAllNodes );
extern int Io_WriteBench( Abc_Ntk_t * pNtk, char * FileName );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
CSAT_Manager CSAT_InitManager()
{
    CSAT_Manager_t * mng;
    mng = ALLOC( CSAT_Manager_t, 1 );
    memset( mng, 0, sizeof(CSAT_Manager_t) );
    mng->pNtk = Abc_NtkAlloc( ABC_TYPE_LOGIC, ABC_FUNC_SOP );
    mng->pNtk->pName = util_strsav("csat_network");
    mng->tName2Node = stmm_init_table(strcmp, stmm_strhash);
    mng->tNode2Name = stmm_init_table(stmm_ptrcmp, stmm_ptrhash);
    mng->vNodes     = Vec_PtrAlloc( 100 );
    mng->vValues    = Vec_IntAlloc( 100 );
    return mng;
}

/**Function*************************************************************

  Synopsis    [Deletes the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_QuitManager( CSAT_Manager mng )
{
    if ( mng->tNode2Name ) stmm_free_table( mng->tNode2Name );
    if ( mng->tName2Node ) stmm_free_table( mng->tName2Node );
    if ( mng->pNtk )       Abc_NtkDelete( mng->pNtk );
    if ( mng->pTarget )    Abc_NtkDelete( mng->pTarget );
    if ( mng->vNodes )     Vec_PtrFree( mng->vNodes );
    if ( mng->vValues )    Vec_IntFree( mng->vValues );
    FREE( mng->pDumpFileName );
    free( mng );
}

/**Function*************************************************************

  Synopsis    [Sets solver options for learning.]

  Description [0 = baseline; 1 = resource-aware solving.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_SetSolveOption( CSAT_Manager mng, enum CSAT_OptionT option )
{
    mng->mode = option;
    if ( option == 0 )
        printf( "CSAT_SetSolveOption: Setting baseline solving mode.\n" );
    else if ( option == 1 )
        printf( "CSAT_SetSolveOption: Setting resource-aware solving mode.\n" );
    else
        printf( "CSAT_SetSolveOption: Unknown option.\n" );
}


/**Function*************************************************************

  Synopsis    [Adds a gate to the circuit.]

  Description [The meaning of the parameters are:
    type: the type of the gate to be added
    name: the name of the gate to be added, name should be unique in a circuit.
    nofi: number of fanins of the gate to be added;
    fanins: the name array of fanins of the gate to be added.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int CSAT_AddGate( CSAT_Manager mng, enum GateType type, char * name, int nofi, char ** fanins, int dc_attr )
{
    Abc_Obj_t * pObj, * pFanin;
    char * pSop;
    int i;

    switch( type )
    {
    case CSAT_BPI:
    case CSAT_BPPI:
        if ( nofi != 0 )
            { printf( "CSAT_AddGate: The PI/PPI gate \"%s\" has fanins.\n", name ); return 0; }
        // create the PI
        pObj = Abc_NtkCreatePi( mng->pNtk );
        stmm_insert( mng->tNode2Name, (char *)pObj, name );
        break;
    case CSAT_CONST:
    case CSAT_BAND:
    case CSAT_BNAND:
    case CSAT_BOR:
    case CSAT_BNOR:
    case CSAT_BXOR:
    case CSAT_BXNOR:
    case CSAT_BINV:
    case CSAT_BBUF:
        // create the node
        pObj = Abc_NtkCreateNode( mng->pNtk );
        // create the fanins
        for ( i = 0; i < nofi; i++ )
        {
            if ( !stmm_lookup( mng->tName2Node, fanins[i], (char **)&pFanin ) )
                { printf( "CSAT_AddGate: The fanin gate \"%s\" is not in the network.\n", fanins[i] ); return 0; }
            Abc_ObjAddFanin( pObj, pFanin );
        }
        // create the node function
        switch( type )
        {
            case CSAT_CONST:
                if ( nofi != 0 )
                    { printf( "CSAT_AddGate: The constant gate \"%s\" has fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateConst1( mng->pNtk->pManFunc );
                break;
            case CSAT_BAND:
                if ( nofi < 1 )
                    { printf( "CSAT_AddGate: The AND gate \"%s\" no fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateAnd( mng->pNtk->pManFunc, nofi );
                break;
            case CSAT_BNAND:
                if ( nofi < 1 )
                    { printf( "CSAT_AddGate: The NAND gate \"%s\" no fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateNand( mng->pNtk->pManFunc, nofi );
                break;
            case CSAT_BOR:
                if ( nofi < 1 )
                    { printf( "CSAT_AddGate: The OR gate \"%s\" no fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateOr( mng->pNtk->pManFunc, nofi, NULL );
                break;
            case CSAT_BNOR:
                if ( nofi < 1 )
                    { printf( "CSAT_AddGate: The NOR gate \"%s\" no fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateNor( mng->pNtk->pManFunc, nofi );
                break;
            case CSAT_BXOR:
                if ( nofi < 1 )
                    { printf( "CSAT_AddGate: The XOR gate \"%s\" no fanins.\n", name ); return 0; }
                if ( nofi > 2 )
                    { printf( "CSAT_AddGate: The XOR gate \"%s\" has more than two fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateXor( mng->pNtk->pManFunc, nofi );
                break;
            case CSAT_BXNOR:
                if ( nofi < 1 )
                    { printf( "CSAT_AddGate: The XNOR gate \"%s\" no fanins.\n", name ); return 0; }
                if ( nofi > 2 )
                    { printf( "CSAT_AddGate: The XNOR gate \"%s\" has more than two fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateNxor( mng->pNtk->pManFunc, nofi );
                break;
            case CSAT_BINV:
                if ( nofi != 1 )
                    { printf( "CSAT_AddGate: The inverter gate \"%s\" does not have exactly one fanin.\n", name ); return 0; }
                pSop = Abc_SopCreateInv( mng->pNtk->pManFunc );
                break;
            case CSAT_BBUF:
                if ( nofi != 1 )
                    { printf( "CSAT_AddGate: The buffer gate \"%s\" does not have exactly one fanin.\n", name ); return 0; }
                pSop = Abc_SopCreateBuf( mng->pNtk->pManFunc );
                break;
            default :
                break;
        }
        Abc_ObjSetData( pObj, pSop );
        break;
    case CSAT_BPPO:
    case CSAT_BPO:
        if ( nofi != 1 )
            { printf( "CSAT_AddGate: The PO/PPO gate \"%s\" does not have exactly one fanin.\n", name ); return 0; }
        // create the PO
        pObj = Abc_NtkCreatePo( mng->pNtk );
        stmm_insert( mng->tNode2Name, (char *)pObj, name );
        // connect to the PO fanin
        if ( !stmm_lookup( mng->tName2Node, fanins[0], (char **)&pFanin ) )
            { printf( "CSAT_AddGate: The fanin gate \"%s\" is not in the network.\n", fanins[0] ); return 0; }
        Abc_ObjAddFanin( pObj, pFanin );
        break;
    default:
        printf( "CSAT_AddGate: Unknown gate type.\n" );
        break;
    }
    if ( stmm_insert( mng->tName2Node, name, (char *)pObj ) )
        { printf( "CSAT_AddGate: The same gate \"%s\" is added twice.\n", name ); return 0; }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks integraty of the manager.]

  Description [Checks if there are gates that are not used by any primary output.
  If no such gates exist, return 1 else return 0.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int CSAT_Check_Integrity( CSAT_Manager mng )
{
    Abc_Ntk_t * pNtk = mng->pNtk;
    Abc_Obj_t * pObj;
    int i;

    // this procedure also finalizes construction of the ABC network
    Abc_NtkFixNonDrivenNets( pNtk );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, CSAT_GetNodeName(mng, pObj) );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, CSAT_GetNodeName(mng, pObj) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );

    // make sure everything is okay with the network structure
    if ( !Abc_NtkCheckRead( pNtk ) )
    {
        printf( "CSAT_Check_Integrity: The internal network check has failed.\n" );
        return 0;
    }

    // check that there is no dangling nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFanoutNum(pObj) == 0 )
        {
            printf( "CSAT_Check_Integrity: The network has dangling nodes.\n" );
            return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Sets time limit for solving a target.]

  Description [Runtime: time limit (in second).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_SetTimeLimit( CSAT_Manager mng, int runtime )
{
    printf( "CSAT_SetTimeLimit: The resource limit is not implemented (warning).\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_SetLearnLimit( CSAT_Manager mng, int num )
{
    printf( "CSAT_SetLearnLimit: The resource limit is not implemented (warning).\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_SetSolveBacktrackLimit( CSAT_Manager mng, int num )
{
    printf( "CSAT_SetSolveBacktrackLimit: The resource limit is not implemented (warning).\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_SetLearnBacktrackLimit( CSAT_Manager mng, int num )
{
    printf( "CSAT_SetLearnBacktrackLimit: The resource limit is not implemented (warning).\n" );
}

/**Function*************************************************************

  Synopsis    [Sets the file name to dump the structurally hashed network used for solving.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_EnableDump( CSAT_Manager mng, char * dump_file )
{
    FREE( mng->pDumpFileName );
    mng->pDumpFileName = util_strsav( dump_file );
}

/**Function*************************************************************

  Synopsis    [Adds a new target to the manager.]

  Description [The meaning of the parameters are:
    nog: number of gates that are in the targets,
    names: name array of gates,
    values: value array of the corresponding gates given in "names" to be solved. 
    The relation of them is AND.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int CSAT_AddTarget( CSAT_Manager mng, int nog, char ** names, int * values )
{
    Abc_Obj_t * pObj;
    int i;
    if ( nog < 1 )
        { printf( "CSAT_AddTarget: The target has no gates.\n" ); return 0; }
    // clear storage for the target
    mng->nog = 0;
    Vec_PtrClear( mng->vNodes );
    Vec_IntClear( mng->vValues );
    // save the target
    for ( i = 0; i < nog; i++ )
    {
        if ( !stmm_lookup( mng->tName2Node, names[i], (char **)&pObj ) )
            { printf( "CSAT_AddTarget: The target gate \"%s\" is not in the network.\n", names[i] ); return 0; }
        Vec_PtrPush( mng->vNodes, pObj );
        if ( values[i] < 0 || values[i] > 1 )
            { printf( "CSAT_AddTarget: The value of gate \"%s\" is not 0 or 1.\n", names[i] ); return 0; }
        Vec_IntPush( mng->vValues, values[i] );
    }
    mng->nog = nog;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Initialize the solver internal data structure.]

  Description [Prepares the solver to work on one specific target
  set by calling CSAT_AddTarget before.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_SolveInit( CSAT_Manager mng )
{
    Fraig_Params_t * pParams = &mng->Params;
    int nWords1, nWords2, nWordsMin;

    // check if the target is available
    assert( mng->nog == Vec_PtrSize(mng->vNodes) );
    if ( mng->nog == 0 )
        { printf( "CSAT_SolveInit: Target is not specified by CSAT_AddTarget().\n" ); return; }

    // free the previous target network if present
    if ( mng->pTarget ) Abc_NtkDelete( mng->pTarget );

    // set the new target network
    mng->pTarget = Abc_NtkCreateCone( mng->pNtk, mng->vNodes, mng->vValues );

    // to determine the number of simulation patterns
    // use the following strategy
    // at least 64 words (32 words random and 32 words dynamic)
    // no more than 256M for one circuit (128M + 128M)
    nWords1 = 32;
    nWords2 = (1<<27) / (Abc_NtkNodeNum(mng->pTarget) + Abc_NtkCiNum(mng->pTarget));
    nWordsMin = ABC_MIN( nWords1, nWords2 );

    // set parameters for fraiging
    memset( pParams, 0, sizeof(Fraig_Params_t) );
    pParams->nPatsRand  = nWordsMin * 32; // the number of words of random simulation info
    pParams->nPatsDyna  = nWordsMin * 32; // the number of words of dynamic simulation info
    pParams->nBTLimit   = 99;             // the max number of backtracks to perform at a node
    pParams->fFuncRed   = mng->mode;      // performs only one level hashing
    pParams->fFeedBack  = 1;              // enables solver feedback
    pParams->fDist1Pats = 1;              // enables distance-1 patterns
    pParams->fDoSparse  = 0;              // performs equiv tests for sparse functions 
    pParams->fChoicing  = 0;              // enables recording structural choices
    pParams->fTryProve  = 1;              // tries to solve the final miter
    pParams->fVerbose   = 0;              // the verbosiness flag
    pParams->fVerboseP  = 0;              // the verbosiness flag for proof reporting
}

/**Function*************************************************************

  Synopsis    [Currently not implemented.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_AnalyzeTargets( CSAT_Manager mng )
{
}

/**Function*************************************************************

  Synopsis    [Solves the targets added by CSAT_AddTarget().]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
enum CSAT_StatusT CSAT_Solve( CSAT_Manager mng )
{
    Fraig_Man_t * pMan;
    int * pModel;
    int RetValue, i;

    // check if the target network is available
    if ( mng->pTarget == NULL )
        { printf( "CSAT_Solve: Target network is not derived by CSAT_SolveInit().\n" ); return UNDETERMINED; }

    // transform the target into a fraig
    pMan = Abc_NtkToFraig( mng->pTarget, &mng->Params, 0 ); 
    Fraig_ManProveMiter( pMan );

    // analyze the result
    mng->pResult = CSAT_TargetResAlloc( Abc_NtkCiNum(mng->pTarget) );
    RetValue = Fraig_ManCheckMiter( pMan );
    if ( RetValue == -1 )
        mng->pResult->status = UNDETERMINED;
    else if ( RetValue == 1 )
        mng->pResult->status = UNSATISFIABLE;
    else if ( RetValue == 0 )
    {
        mng->pResult->status = SATISFIABLE;
        pModel = Fraig_ManReadModel( pMan );
        assert( pModel != NULL );
        // create the array of PI names and values
        for ( i = 0; i < mng->pResult->no_sig; i++ )
        {
            mng->pResult->names[i] = CSAT_GetNodeName(mng, Abc_NtkCi(mng->pNtk, i)); // returns the same string that was given
            mng->pResult->values[i] = pModel[i];
        }
    }
    else 
        assert( 0 );

    // delete the fraig manager
    Fraig_ManFree( pMan );
    // delete the target
    Abc_NtkDelete( mng->pTarget );
    mng->pTarget = NULL;
    // return the status
    return mng->pResult->status;
}

/**Function*************************************************************

  Synopsis    [Gets the solve status of a target.]

  Description [TargetID: the target id returned by CSAT_AddTarget().]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
CSAT_Target_ResultT * CSAT_Get_Target_Result( CSAT_Manager mng, int TargetID )
{
    return mng->pResult;
}

/**Function*************************************************************

  Synopsis    [Dumps the target AIG into the BENCH file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_Dump_Bench_File( CSAT_Manager mng )
{
    Abc_Ntk_t * pNtkTemp;
    char * pFileName;

    // derive the netlist
    pNtkTemp = Abc_NtkLogicToNetlistBench( mng->pTarget );
    if ( pNtkTemp == NULL ) 
        { printf( "CSAT_Dump_Bench_File: Dumping BENCH has failed.\n" ); return; }
    pFileName = mng->pDumpFileName? mng->pDumpFileName: "abc_test.bench";
    Io_WriteBench( pNtkTemp, pFileName );
    Abc_NtkDelete( pNtkTemp );
}



/**Function*************************************************************

  Synopsis    [Allocates the target result.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
CSAT_Target_ResultT * CSAT_TargetResAlloc( int nVars )
{
    CSAT_Target_ResultT * p;
    p = ALLOC( CSAT_Target_ResultT, 1 );
    memset( p, 0, sizeof(CSAT_Target_ResultT) );
    p->no_sig = nVars;
    p->names = ALLOC( char *, nVars );
    p->values = ALLOC( int, nVars );
    memset( p->names, 0, sizeof(char *) * nVars );
    memset( p->values, 0, sizeof(int) * nVars );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the target result.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void CSAT_TargetResFree( CSAT_Target_ResultT * p )
{
    if ( p == NULL )
        return;
    FREE( p->names );
    FREE( p->values );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Dumps the target AIG into the BENCH file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * CSAT_GetNodeName( CSAT_Manager mng, Abc_Obj_t * pNode )
{
    char * pName = NULL;
    if ( !stmm_lookup( mng->tNode2Name, (char *)pNode, (char **)&pName ) )
    {
        assert( 0 );
    }
    return pName;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


