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

#define ABC_DEFAULT_TIMEOUT     60   // 60 seconds

struct ABC_ManagerStruct_t
{
    // information about the problem
    stmm_table *          tName2Node;    // the hash table mapping names to nodes
    stmm_table *          tNode2Name;    // the hash table mapping nodes to names
    Abc_Ntk_t *           pNtk;          // the starting ABC network
    Abc_Ntk_t *           pTarget;       // the AIG representing the target
    char *                pDumpFileName; // the name of the file to dump the target network
    Extra_MmFlex_t *      pMmNames;      // memory manager for signal names
    // solving parameters
    int                   mode;          // 0 = brute-force SAT;  1 = resource-aware FRAIG
    int                   nSeconds;      // time limit for pure SAT solving
    Fraig_Params_t        Params;        // the set of parameters to call FRAIG package
    // information about the target 
    int                   nog;           // the numbers of gates in the target
    Vec_Ptr_t *           vNodes;        // the gates in the target
    Vec_Int_t *           vValues;       // the values of gate's outputs in the target
    // solution
    ABC_Target_ResultT *  pResult;       // the result of solving the target
};

static ABC_Target_ResultT * ABC_TargetResAlloc( int nVars );
static char * ABC_GetNodeName( ABC_Manager mng, Abc_Obj_t * pNode );

// some external procedures
extern int Io_WriteBench( Abc_Ntk_t * pNtk, char * FileName );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
ABC_Manager ABC_InitManager()
{
    ABC_Manager_t * mng;
    mng = ALLOC( ABC_Manager_t, 1 );
    memset( mng, 0, sizeof(ABC_Manager_t) );
    mng->pNtk = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP );
    mng->pNtk->pName = util_strsav("csat_network");
    mng->tName2Node = stmm_init_table(strcmp, stmm_strhash);
    mng->tNode2Name = stmm_init_table(stmm_ptrcmp, stmm_ptrhash);
    mng->pMmNames   = Extra_MmFlexStart();
    mng->vNodes     = Vec_PtrAlloc( 100 );
    mng->vValues    = Vec_IntAlloc( 100 );
    mng->nSeconds   = ABC_DEFAULT_TIMEOUT;
    return mng;
}

/**Function*************************************************************

  Synopsis    [Deletes the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ABC_QuitManager( ABC_Manager mng )
{
    if ( mng->tNode2Name ) stmm_free_table( mng->tNode2Name );
    if ( mng->tName2Node ) stmm_free_table( mng->tName2Node );
    if ( mng->pMmNames )   Extra_MmFlexStop( mng->pMmNames, 0 );
    if ( mng->pNtk )       Abc_NtkDelete( mng->pNtk );
    if ( mng->pTarget )    Abc_NtkDelete( mng->pTarget );
    if ( mng->vNodes )     Vec_PtrFree( mng->vNodes );
    if ( mng->vValues )    Vec_IntFree( mng->vValues );
    FREE( mng->pDumpFileName );
    free( mng );
}

/**Function*************************************************************

  Synopsis    [Sets solver options for learning.]

  Description [0 = brute-force SAT;  1 = resource-aware FRAIG.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ABC_SetSolveOption( ABC_Manager mng, enum ABC_OptionT option )
{
    mng->mode = option;
    if ( option == 0 )
        printf( "ABC_SetSolveOption: Setting brute-force SAT mode.\n" );
    else if ( option == 1 )
        printf( "ABC_SetSolveOption: Setting resource-aware FRAIG mode.\n" );
    else
        printf( "ABC_SetSolveOption: Unknown solving mode.\n" );
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
int ABC_AddGate( ABC_Manager mng, enum GateType type, char * name, int nofi, char ** fanins, int dc_attr )
{
    Abc_Obj_t * pObj, * pFanin;
    char * pSop, * pNewName;
    int i;

    // save the name in the local memory manager
    pNewName = Extra_MmFlexEntryFetch( mng->pMmNames, strlen(name) + 1 );
    strcpy( pNewName, name );
    name = pNewName;

    // consider different cases, create the node, and map the node into the name
    switch( type )
    {
    case ABC_BPI:
    case ABC_BPPI:
        if ( nofi != 0 )
            { printf( "ABC_AddGate: The PI/PPI gate \"%s\" has fanins.\n", name ); return 0; }
        // create the PI
        pObj = Abc_NtkCreatePi( mng->pNtk );
        stmm_insert( mng->tNode2Name, (char *)pObj, name );
        break;
    case ABC_CONST:
    case ABC_BAND:
    case ABC_BNAND:
    case ABC_BOR:
    case ABC_BNOR:
    case ABC_BXOR:
    case ABC_BXNOR:
    case ABC_BINV:
    case ABC_BBUF:
        // create the node
        pObj = Abc_NtkCreateNode( mng->pNtk );
        // create the fanins
        for ( i = 0; i < nofi; i++ )
        {
            if ( !stmm_lookup( mng->tName2Node, fanins[i], (char **)&pFanin ) )
                { printf( "ABC_AddGate: The fanin gate \"%s\" is not in the network.\n", fanins[i] ); return 0; }
            Abc_ObjAddFanin( pObj, pFanin );
        }
        // create the node function
        switch( type )
        {
            case ABC_CONST:
                if ( nofi != 0 )
                    { printf( "ABC_AddGate: The constant gate \"%s\" has fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateConst1( mng->pNtk->pManFunc );
                break;
            case ABC_BAND:
                if ( nofi < 1 )
                    { printf( "ABC_AddGate: The AND gate \"%s\" no fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateAnd( mng->pNtk->pManFunc, nofi, NULL );
                break;
            case ABC_BNAND:
                if ( nofi < 1 )
                    { printf( "ABC_AddGate: The NAND gate \"%s\" no fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateNand( mng->pNtk->pManFunc, nofi );
                break;
            case ABC_BOR:
                if ( nofi < 1 )
                    { printf( "ABC_AddGate: The OR gate \"%s\" no fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateOr( mng->pNtk->pManFunc, nofi, NULL );
                break;
            case ABC_BNOR:
                if ( nofi < 1 )
                    { printf( "ABC_AddGate: The NOR gate \"%s\" no fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateNor( mng->pNtk->pManFunc, nofi );
                break;
            case ABC_BXOR:
                if ( nofi < 1 )
                    { printf( "ABC_AddGate: The XOR gate \"%s\" no fanins.\n", name ); return 0; }
                if ( nofi > 2 )
                    { printf( "ABC_AddGate: The XOR gate \"%s\" has more than two fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateXor( mng->pNtk->pManFunc, nofi );
                break;
            case ABC_BXNOR:
                if ( nofi < 1 )
                    { printf( "ABC_AddGate: The XNOR gate \"%s\" no fanins.\n", name ); return 0; }
                if ( nofi > 2 )
                    { printf( "ABC_AddGate: The XNOR gate \"%s\" has more than two fanins.\n", name ); return 0; }
                pSop = Abc_SopCreateNxor( mng->pNtk->pManFunc, nofi );
                break;
            case ABC_BINV:
                if ( nofi != 1 )
                    { printf( "ABC_AddGate: The inverter gate \"%s\" does not have exactly one fanin.\n", name ); return 0; }
                pSop = Abc_SopCreateInv( mng->pNtk->pManFunc );
                break;
            case ABC_BBUF:
                if ( nofi != 1 )
                    { printf( "ABC_AddGate: The buffer gate \"%s\" does not have exactly one fanin.\n", name ); return 0; }
                pSop = Abc_SopCreateBuf( mng->pNtk->pManFunc );
                break;
            default :
                break;
        }
        Abc_ObjSetData( pObj, pSop );
        break;
    case ABC_BPPO:
    case ABC_BPO:
        if ( nofi != 1 )
            { printf( "ABC_AddGate: The PO/PPO gate \"%s\" does not have exactly one fanin.\n", name ); return 0; }
        // create the PO
        pObj = Abc_NtkCreatePo( mng->pNtk );
        stmm_insert( mng->tNode2Name, (char *)pObj, name );
        // connect to the PO fanin
        if ( !stmm_lookup( mng->tName2Node, fanins[0], (char **)&pFanin ) )
            { printf( "ABC_AddGate: The fanin gate \"%s\" is not in the network.\n", fanins[0] ); return 0; }
        Abc_ObjAddFanin( pObj, pFanin );
        break;
    default:
        printf( "ABC_AddGate: Unknown gate type.\n" );
        break;
    }

    // map the name into the node
    if ( stmm_insert( mng->tName2Node, name, (char *)pObj ) )
        { printf( "ABC_AddGate: The same gate \"%s\" is added twice.\n", name ); return 0; }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks integraty of the manager.]

  Description [Checks if there are gates that are not used by any primary output.
  If no such gates exist, return 1 else return 0.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int ABC_Check_Integrity( ABC_Manager mng )
{
    Abc_Ntk_t * pNtk = mng->pNtk;
    Abc_Obj_t * pObj;
    int i;

    // this procedure also finalizes construction of the ABC network
    Abc_NtkFixNonDrivenNets( pNtk );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, ABC_GetNodeName(mng, pObj) );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj, ABC_GetNodeName(mng, pObj) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );

    // make sure everything is okay with the network structure
    if ( !Abc_NtkDoCheck( pNtk ) )
    {
        printf( "ABC_Check_Integrity: The internal network check has failed.\n" );
        return 0;
    }

    // check that there is no dangling nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( i == 0 ) 
            continue;
        if ( Abc_ObjFanoutNum(pObj) == 0 )
        {
            printf( "ABC_Check_Integrity: The network has dangling nodes.\n" );
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
void ABC_SetTimeLimit( ABC_Manager mng, int runtime )
{
    mng->nSeconds = runtime;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ABC_SetLearnLimit( ABC_Manager mng, int num )
{
    printf( "ABC_SetLearnLimit: The resource limit is not implemented (warning).\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ABC_SetSolveBacktrackLimit( ABC_Manager mng, int num )
{
    printf( "ABC_SetSolveBacktrackLimit: The resource limit is not implemented (warning).\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ABC_SetLearnBacktrackLimit( ABC_Manager mng, int num )
{
    printf( "ABC_SetLearnBacktrackLimit: The resource limit is not implemented (warning).\n" );
}

/**Function*************************************************************

  Synopsis    [Sets the file name to dump the structurally hashed network used for solving.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ABC_EnableDump( ABC_Manager mng, char * dump_file )
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
int ABC_AddTarget( ABC_Manager mng, int nog, char ** names, int * values )
{
    Abc_Obj_t * pObj;
    int i;
    if ( nog < 1 )
        { printf( "ABC_AddTarget: The target has no gates.\n" ); return 0; }
    // clear storage for the target
    mng->nog = 0;
    Vec_PtrClear( mng->vNodes );
    Vec_IntClear( mng->vValues );
    // save the target
    for ( i = 0; i < nog; i++ )
    {
        if ( !stmm_lookup( mng->tName2Node, names[i], (char **)&pObj ) )
            { printf( "ABC_AddTarget: The target gate \"%s\" is not in the network.\n", names[i] ); return 0; }
        Vec_PtrPush( mng->vNodes, pObj );
        if ( values[i] < 0 || values[i] > 1 )
            { printf( "ABC_AddTarget: The value of gate \"%s\" is not 0 or 1.\n", names[i] ); return 0; }
        Vec_IntPush( mng->vValues, values[i] );
    }
    mng->nog = nog;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Initialize the solver internal data structure.]

  Description [Prepares the solver to work on one specific target
  set by calling ABC_AddTarget before.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ABC_SolveInit( ABC_Manager mng )
{
    Fraig_Params_t * pParams = &mng->Params;
    int nWords1, nWords2, nWordsMin;

    // check if the target is available
    assert( mng->nog == Vec_PtrSize(mng->vNodes) );
    if ( mng->nog == 0 )
        { printf( "ABC_SolveInit: Target is not specified by ABC_AddTarget().\n" ); return; }

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
    pParams->nBTLimit   = 10;             // the max number of backtracks to perform at a node
    pParams->nSeconds   = mng->nSeconds;  // the time out for the final proof
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
void ABC_AnalyzeTargets( ABC_Manager mng )
{
}

/**Function*************************************************************

  Synopsis    [Solves the targets added by ABC_AddTarget().]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
enum ABC_StatusT ABC_Solve( ABC_Manager mng )
{
    Fraig_Man_t * pMan;
    Abc_Ntk_t * pCnf;
    int * pModel;
    int RetValue, i;

    // check if the target network is available
    if ( mng->pTarget == NULL )
        { printf( "ABC_Solve: Target network is not derived by ABC_SolveInit().\n" ); return UNDETERMINED; }

    // optimizations of the target go here
    // for example, to enable one pass of rewriting, uncomment this line
//    Abc_NtkRewrite( mng->pTarget, 0, 1, 0 );

    if ( mng->mode == 0 ) // brute-force SAT
    {
        // transform the AIG into a logic network for efficient CNF construction
        pCnf = Abc_NtkRenode( mng->pTarget, 0, 100, 1, 0, 0 );
        RetValue = Abc_NtkMiterSat( pCnf, mng->nSeconds, 0 );

        // analyze the result
        mng->pResult = ABC_TargetResAlloc( Abc_NtkCiNum(mng->pTarget) );
        if ( RetValue == -1 )
            mng->pResult->status = UNDETERMINED;
        else if ( RetValue == 1 )
            mng->pResult->status = UNSATISFIABLE;
        else if ( RetValue == 0 )
        {
            mng->pResult->status = SATISFIABLE;
            // create the array of PI names and values
            for ( i = 0; i < mng->pResult->no_sig; i++ )
            {
                mng->pResult->names[i] = ABC_GetNodeName(mng, Abc_NtkCi(mng->pNtk, i)); // returns the same string that was given
                mng->pResult->values[i] = pCnf->pModel[i];
            }
            FREE( mng->pTarget->pModel );
        }
        else assert( 0 );
        Abc_NtkDelete( pCnf );
    }
    else if ( mng->mode == 1 ) // resource-aware fraiging
    {
        // transform the target into a fraig
        pMan = Abc_NtkToFraig( mng->pTarget, &mng->Params, 0, 0 ); 
        Fraig_ManProveMiter( pMan );
        RetValue = Fraig_ManCheckMiter( pMan );

        // analyze the result
        mng->pResult = ABC_TargetResAlloc( Abc_NtkCiNum(mng->pTarget) );
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
                mng->pResult->names[i] = ABC_GetNodeName(mng, Abc_NtkCi(mng->pNtk, i)); // returns the same string that was given
                mng->pResult->values[i] = pModel[i];
            }
        }
        else assert( 0 );
        // delete the fraig manager
        Fraig_ManFree( pMan );
    }
    else
        assert( 0 );

    // delete the target
    Abc_NtkDelete( mng->pTarget );
    mng->pTarget = NULL;
    // return the status
    return mng->pResult->status;
}

/**Function*************************************************************

  Synopsis    [Gets the solve status of a target.]

  Description [TargetID: the target id returned by ABC_AddTarget().]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
ABC_Target_ResultT * ABC_Get_Target_Result( ABC_Manager mng, int TargetID )
{
    return mng->pResult;
}

/**Function*************************************************************

  Synopsis    [Dumps the original network into the BENCH file.]

  Description [This procedure should be modified to dump the target.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ABC_Dump_Bench_File( ABC_Manager mng )
{
    Abc_Ntk_t * pNtkTemp, * pNtkAig;
    char * pFileName;
 
    // derive the netlist
    pNtkAig = Abc_NtkStrash( mng->pNtk, 0, 0 );
    pNtkTemp = Abc_NtkLogicToNetlistBench( pNtkAig );
    Abc_NtkDelete( pNtkAig );
    if ( pNtkTemp == NULL ) 
        { printf( "ABC_Dump_Bench_File: Dumping BENCH has failed.\n" ); return; }
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
ABC_Target_ResultT * ABC_TargetResAlloc( int nVars )
{
    ABC_Target_ResultT * p;
    p = ALLOC( ABC_Target_ResultT, 1 );
    memset( p, 0, sizeof(ABC_Target_ResultT) );
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
void ABC_TargetResFree( ABC_Target_ResultT * p )
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
char * ABC_GetNodeName( ABC_Manager mng, Abc_Obj_t * pNode )
{
    char * pName = NULL;
    if ( !stmm_lookup( mng->tNode2Name, (char *)pNode, (char **)&pName ) )
    {
        assert( 0 );
    }
    return pName;
}



/**Function*************************************************************

  Synopsis    [This procedure applies a rewriting script to the network.]

  Description [Rewriting is performed without regard for the number of 
  logic levels. This corresponds to "circuit compression for formal 
  verification" (Per Bjesse et al, ICCAD 2004) but implemented in a more 
  exhaustive way than in the above paper.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void ABC_PerformRewriting( ABC_Manager mng )
{
    void * pAbc;
    char Command[1000];
    int clkBalan, clkResyn, clk;
    int fPrintStats = 1;
    int fUseResyn   = 1;

    // procedures to get the ABC framework and execute commands in it
    extern void * Abc_FrameGetGlobalFrame();
    extern void Abc_FrameReplaceCurrentNetwork( void * p, Abc_Ntk_t * pNtk );
    extern int  Cmd_CommandExecute( void * p, char * sCommand );
    extern Abc_Ntk_t * Abc_FrameReadNtk( void * p );


    // get the pointer to the ABC framework
    pAbc = Abc_FrameGetGlobalFrame();
    assert( pAbc != NULL );

    // replace the current network by the target network
    Abc_FrameReplaceCurrentNetwork( pAbc, mng->pTarget );

clk = clock();
    //////////////////////////////////////////////////////////////////////////
    // balance
    sprintf( Command, "balance" );
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return;
    }
clkBalan = clock() - clk;

    //////////////////////////////////////////////////////////////////////////
    // print stats
    if ( fPrintStats )
    {
        sprintf( Command, "print_stats" );
        if ( Cmd_CommandExecute( pAbc, Command ) )
        {
            fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
            return;
        }
    }

clk = clock();
    //////////////////////////////////////////////////////////////////////////
    // synthesize
    if ( fUseResyn )
    {
        sprintf( Command, "balance; rewrite -l; rewrite -lz; balance; rewrite -lz; balance" );
        if ( Cmd_CommandExecute( pAbc, Command ) )
        {
            fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
            return;
        }
    }
clkResyn = clock() - clk;

    //////////////////////////////////////////////////////////////////////////
    // print stats
    if ( fPrintStats )
    {
        sprintf( Command, "print_stats" );
        if ( Cmd_CommandExecute( pAbc, Command ) )
        {
            fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
            return;
        }
    }
    printf( "Balancing = %6.2f sec   ",   (float)(clkBalan)/(float)(CLOCKS_PER_SEC) );
    printf( "Rewriting = %6.2f sec   ",   (float)(clkResyn)/(float)(CLOCKS_PER_SEC) );
    printf( "\n" );

    // read the target network from the current network
    mng->pTarget = Abc_NtkDup( Abc_FrameReadNtk(pAbc) );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


