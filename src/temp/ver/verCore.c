/**CFile****************************************************************

  FileName    [verCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of structural Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 19, 2006.]

  Revision    [$Id: verCore.c,v 1.00 2006/08/19 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ver.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// types of verilog signals
typedef enum { 
    VER_SIG_NONE = 0,
    VER_SIG_INPUT,
    VER_SIG_OUTPUT,
    VER_SIG_INOUT,
    VER_SIG_REG,
    VER_SIG_WIRE
} Ver_SignalType_t;

static Ver_Man_t * Ver_ParseStart( char * pFileName, Abc_Lib_t * pGateLib );
static void Ver_ParseStop( Ver_Man_t * p );
static void Ver_ParseFreeData( Ver_Man_t * p );
static void Ver_ParseInternal( Ver_Man_t * p, int fCheck );
static int  Ver_ParseModule( Ver_Man_t * p );
static int  Ver_ParseSignal( Ver_Man_t * p, Ver_SignalType_t SigType );
static int  Ver_ParseAssign( Ver_Man_t * p );
static int  Ver_ParseAlways( Ver_Man_t * p );
static int  Ver_ParseInitial( Ver_Man_t * p );
static int  Ver_ParseGate( Ver_Man_t * p, Abc_Ntk_t * pNtkGate );

static Abc_Obj_t * Ver_ParseCreatePi( Abc_Ntk_t * pNtk, char * pName );
static Abc_Obj_t * Ver_ParseCreatePo( Abc_Ntk_t * pNtk, char * pName );
static Abc_Obj_t * Ver_ParseCreateLatch( Abc_Ntk_t * pNtk, char * pNetLI, char * pNetLO );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [File parser.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Lib_t * Ver_ParseFile( char * pFileName, Abc_Lib_t * pGateLib, int fCheck )
{
    Ver_Man_t * p;
    Abc_Lib_t * pDesign;
    // start the parser
    p = Ver_ParseStart( pFileName, pGateLib );
    // parse the file
    Ver_ParseInternal( p, fCheck );
    // save the result
    pDesign = p->pDesign;
    p->pDesign = NULL;
    // stop the parser
    Ver_ParseStop( p );
    return pDesign;
}

/**Function*************************************************************

  Synopsis    [Start parser.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ver_Man_t * Ver_ParseStart( char * pFileName, Abc_Lib_t * pGateLib )
{
    Ver_Man_t * p;
    p = ALLOC( Ver_Man_t, 1 );
    memset( p, 0, sizeof(Ver_Man_t) );
    p->pFileName = pFileName;
    p->pReader   = Ver_StreamAlloc( pFileName );
    p->pDesign   = Abc_LibCreate( pFileName );
    p->pGateLib  = pGateLib;
    p->Output    = stdout;
    p->pProgress = Extra_ProgressBarStart( stdout, Ver_StreamGetFileSize(p->pReader) );
    p->vNames    = Vec_PtrAlloc( 100 );
    p->vStackFn  = Vec_PtrAlloc( 100 );
    p->vStackOp  = Vec_IntAlloc( 100 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stop parser.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ver_ParseStop( Ver_Man_t * p )
{
    assert( p->pNtkCur == NULL );
    Ver_StreamFree( p->pReader );
    Extra_ProgressBarStop( p->pProgress );
    Vec_PtrFree( p->vNames   );
    Vec_PtrFree( p->vStackFn );
    Vec_IntFree( p->vStackOp );
    free( p );
}

/**Function*************************************************************

  Synopsis    [File parser.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ver_ParseInternal( Ver_Man_t * pMan, int fCheck )
{
    char * pToken;
    while ( 1 )
    {
        // get the next token
        pToken = Ver_ParseGetName( pMan );
        if ( pToken == NULL )
            break;
        if ( strcmp( pToken, "module" ) )
        {
            sprintf( pMan->sError, "Cannot read \"module\" directive." );
            Ver_ParsePrintErrorMessage( pMan );
            return;
        }

        // parse the module
        if ( !Ver_ParseModule( pMan ) )
            return;

        // check the network for correctness
        if ( fCheck && !Abc_NtkCheckRead( pMan->pNtkCur ) )
        {
            pMan->fTopLevel = 1;
            sprintf( pMan->sError, "The network check has failed.", pMan->pNtkCur->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return;
        }
        // add the module to the hash table
        if ( st_is_member( pMan->pDesign->tModules, pMan->pNtkCur->pName ) )
        {
            pMan->fTopLevel = 1;
            sprintf( pMan->sError, "Module \"%s\" is defined more than once.", pMan->pNtkCur->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return;
        }
        st_insert( pMan->pDesign->tModules, pMan->pNtkCur->pName, (char *)pMan->pNtkCur );
        pMan->pNtkCur = NULL;
    }
}

/**Function*************************************************************

  Synopsis    [File parser.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ver_ParseFreeData( Ver_Man_t * p )
{
    if ( p->pNtkCur )
    {
        Abc_NtkDelete( p->pNtkCur );
        p->pNtkCur = NULL;
    }
    if ( p->pDesign )
    {
        Abc_LibFree( p->pDesign );
        p->pDesign = NULL;
    }
}

/**Function*************************************************************

  Synopsis    [Prints the error message including the file name and line number.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ver_ParsePrintErrorMessage( Ver_Man_t * p )
{
    p->fError = 1;
    if ( p->fTopLevel ) // the line number is not given
        fprintf( p->Output, "%s: %s\n", p->pFileName, p->sError );
    else // print the error message with the line number
        fprintf( p->Output, "%s (line %d): %s\n", 
            p->pFileName, Ver_StreamGetLineNumber(p->pReader), p->sError );
    // free the data
    Ver_ParseFreeData( p );
}



/**Function*************************************************************

  Synopsis    [Parses one Verilog module.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseModule( Ver_Man_t * pMan )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Ntk_t * pNtk, * pNtkTemp;
    Abc_Obj_t * pNet;
    char * pWord, Symbol;
    int RetValue;

    // start the current network
    assert( pMan->pNtkCur == NULL );
    pNtk = pMan->pNtkCur = Abc_NtkAlloc( ABC_NTK_NETLIST, ABC_FUNC_BLACKBOX );

    pNtk->ntkFunc = ABC_FUNC_AIG;
    assert( pNtk->pManFunc == NULL );
    pNtk->pManFunc = pMan->pDesign->pManFunc;

    // get the network name
    pWord = Ver_ParseGetName( pMan );
    pNtk->pName = Extra_UtilStrsav( pWord );
    pNtk->pSpec = NULL;
/*
    // create constant nodes and nets
    pNet = Abc_NtkFindOrCreateNet( pNtk, "1'b0" );
    Abc_ObjAddFanin( pNet, xxxx AigAbc_AigConst1(pNtk) );
    pNet = Abc_NtkFindOrCreateNet( pNtk, "1'b1" );
    Abc_ObjAddFanin( pNet, Abc_AigConst1(pNtk) );
*/
    // make sure we stopped at the opening paranthesis
    if ( Ver_StreamScanChar(p) != '(' )
    {
        sprintf( pMan->sError, "Cannot find \"(\" after \"module\".", pNtk->pName );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    // skip to the end of parantheses
    while ( 1 )
    {
        Ver_StreamSkipToChars( p, ",/)" );
        while ( Ver_StreamScanChar(p) == '/' )
        {
            Ver_ParseSkipComments( pMan );
            Ver_StreamSkipToChars( p, ",/)" );
        }
        Symbol = Ver_StreamPopChar(p);
        if ( Symbol== ')' )
            break;
    }
    if ( !Ver_ParseSkipComments( pMan ) )
        return 0;
    Symbol = Ver_StreamPopChar(p);
    assert( Symbol == ';' );

    // parse the inputs/outputs/registers/wires/inouts
    while ( 1 )
    {
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        if ( !strcmp( pWord, "input" ) )
            RetValue = Ver_ParseSignal( pMan, VER_SIG_INPUT );
        else if ( !strcmp( pWord, "output" ) )
            RetValue = Ver_ParseSignal( pMan, VER_SIG_OUTPUT );
        else if ( !strcmp( pWord, "reg" ) )
            RetValue = Ver_ParseSignal( pMan, VER_SIG_REG );
        else if ( !strcmp( pWord, "wire" ) )
            RetValue = Ver_ParseSignal( pMan, VER_SIG_WIRE );
        else if ( !strcmp( pWord, "inout" ) )
            RetValue = Ver_ParseSignal( pMan, VER_SIG_INOUT );
        else 
            break;
        if ( RetValue == 0 )
            return 0;
    }

    // parse the remaining statements
    while ( 1 )
    {
        Extra_ProgressBarUpdate( pMan->pProgress, Ver_StreamGetCurPosition(p), NULL );
        if ( !strcmp( pWord, "assign" ) )
            RetValue = Ver_ParseAssign( pMan );
        else if ( !strcmp( pWord, "always" ) )
            RetValue = Ver_ParseAlways( pMan );
        else if ( !strcmp( pWord, "initial" ) )
            RetValue = Ver_ParseInitial( pMan );
        else if ( !strcmp( pWord, "endmodule" ) )
        {
            // if nothing is known, set the functionality to be black box
            Abc_NtkFinalizeRead( pNtk );
            break;
        }
        else if ( pMan->pGateLib && st_lookup(pMan->pGateLib->tModules, pWord, (char**)&pNtkTemp) ) // gate library
            RetValue = Ver_ParseGate( pMan, pNtkTemp );
        else if ( pMan->pDesign && st_lookup(pMan->pDesign->tModules, pWord, (char**)&pNtkTemp) ) // current design
            RetValue = Ver_ParseGate( pMan, pNtkTemp );
        else
        {
            printf( "Cannot find \"%s\".\n", pWord );
            Ver_StreamSkipToChars( p, ";" );
            Ver_StreamPopChar(p);

//            sprintf( pMan->sError, "Cannot find \"%s\" in the library.", pWord );
//            Ver_ParsePrintErrorMessage( pMan );
//            return 0;
        }
        if ( RetValue == 0 )
            return 0;
        // get new word
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses one directive.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseSignal( Ver_Man_t * pMan, Ver_SignalType_t SigType )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Ntk_t * pNtk = pMan->pNtkCur;
    char * pWord;
    char Symbol;
    while ( 1 )
    {
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        if ( SigType == VER_SIG_INPUT || SigType == VER_SIG_INOUT )
            Ver_ParseCreatePi( pNtk, pWord );
        if ( SigType == VER_SIG_OUTPUT || SigType == VER_SIG_INOUT )
            Ver_ParseCreatePo( pNtk, pWord );
        if ( SigType == VER_SIG_WIRE || SigType == VER_SIG_REG )
            Abc_NtkFindOrCreateNet( pNtk, pWord );
        Symbol = Ver_StreamPopChar(p);
        if ( Symbol == ',' )
            continue;
        if ( Symbol == ';' )
            return 1;
        break;
    }
    sprintf( pMan->sError, "Cannot parse signal line (expected , or ;)." );
    Ver_ParsePrintErrorMessage( pMan );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Parses one directive.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseAssign( Ver_Man_t * pMan )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Ntk_t * pNtk = pMan->pNtkCur;
    Abc_Obj_t * pNode, * pNet;
    char * pWord, * pName, * pEquation;
    DdNode * bFunc;
    char Symbol;
    int i, Length;

    // convert from the mapped netlist into the BDD netlist
    if ( pNtk->ntkFunc == ABC_FUNC_BLACKBOX )
    {
        pNtk->ntkFunc = ABC_FUNC_BDD;
        pNtk->pManFunc = Cudd_Init( 20, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    }
    else if ( pNtk->ntkFunc != ABC_FUNC_BDD )
    {
        sprintf( pMan->sError, "The network %s appears to mapped gates and assign statements. Currently such network are not allowed. One way to fix this problem is to replace assigns by buffers from the library.", pMan->pNtkCur );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    while ( 1 )
    {
        // get the name of the output signal
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // get the fanout net
        pNet = Abc_NtkFindNet( pNtk, pWord );
        if ( pNet == NULL )
        {
            sprintf( pMan->sError, "Cannot read the assign statement for %s (output wire is not defined).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // get the equal sign
        if ( Ver_StreamPopChar(p) != '=' )
        {
            sprintf( pMan->sError, "Cannot read the assign statement for %s (expected equality sign).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // skip the comments
        if ( !Ver_ParseSkipComments( pMan ) )
            return 0;
        // get the second name
        pEquation = Ver_StreamGetWord( p, ",;" );
        if ( pEquation == NULL )
            return 0;

        // parse the formula
        bFunc = Ver_FormulaParser( pEquation, pNtk->pManFunc, pMan->vNames, pMan->vStackFn, pMan->vStackOp, pMan->sError );  
        if ( bFunc == NULL )
        {
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        Cudd_Ref( bFunc );
        // create the node with the given inputs
        pNode = Abc_NtkCreateNode( pMan->pNtkCur );
        pNode->pData = bFunc;
        Abc_ObjAddFanin( pNet, pNode );
        // connect to fanin nets
        for ( i = 0; i < Vec_PtrSize(pMan->vNames)/2; i++ )
        {
            // get the name of this signal
            Length = (int)Vec_PtrEntry( pMan->vNames, 2*i );
            pName  = Vec_PtrEntry( pMan->vNames, 2*i + 1 );
            pName[Length] = 0;
            // find the corresponding net
            pNet = Abc_NtkFindNet( pNtk, pName );
            if ( pNet == NULL )
            {
                sprintf( pMan->sError, "Cannot read the assign statement for %s (input wire %d is not defined).", pWord, pName );
                Ver_ParsePrintErrorMessage( pMan );
                return 0;
            }
            Abc_ObjAddFanin( pNode, pNet );
        }
        Symbol = Ver_StreamPopChar(p);
        if ( Symbol == ',' )
            continue;
        if ( Symbol == ';' )
            return 1;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses one directive.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseAlways( Ver_Man_t * pMan )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Ntk_t * pNtk = pMan->pNtkCur;
    Abc_Obj_t * pNet, * pNet2;
    char * pWord, * pWord2;
    char Symbol;
    // parse the directive 
    pWord = Ver_ParseGetName( pMan );
    if ( pWord == NULL )
        return 0;
    if ( strcmp( pWord, "begin" ) )
    {
        sprintf( pMan->sError, "Cannot parse the always statement (expected \"begin\")." );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }
    // iterate over the initial states
    while ( 1 )
    {
        // get the name of the output signal
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // look for the end of directive
        if ( !strcmp( pWord, "end" ) )
            break;
        // get the fanout net
        pNet = Abc_NtkFindNet( pNtk, pWord );
        if ( pNet == NULL )
        {
            sprintf( pMan->sError, "Cannot read the always statement for %s (output wire is not defined).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // get the equal sign
        if ( Ver_StreamPopChar(p) != '=' )
        {
            sprintf( pMan->sError, "Cannot read the always statement for %s (expected equality sign).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // skip the comments
        if ( !Ver_ParseSkipComments( pMan ) )
            return 0;
        // get the second name
        pWord2 = Ver_ParseGetName( pMan );
        if ( pWord2 == NULL )
            return 0;
        // get the fanin net
        pNet2 = Abc_NtkFindNet( pNtk, pWord2 );
        if ( pNet2 == NULL )
        {
            sprintf( pMan->sError, "Cannot read the always statement for %s (input wire is not defined).", pWord2 );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // create the latch
        Ver_ParseCreateLatch( pNtk, pNet2->pData, pNet->pData );
        // remove the last symbol
        Symbol = Ver_StreamPopChar(p);
        assert( Symbol == ';' );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses one directive.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseInitial( Ver_Man_t * pMan )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Ntk_t * pNtk = pMan->pNtkCur;
    Abc_Obj_t * pNode, * pNet;
    char * pWord, * pEquation;
    char Symbol;
    // parse the directive 
    pWord = Ver_ParseGetName( pMan );
    if ( pWord == NULL )
        return 0;
    if ( strcmp( pWord, "begin" ) )
    {
        sprintf( pMan->sError, "Cannot parse the initial statement (expected \"begin\")." );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }
    // iterate over the initial states
    while ( 1 )
    {
        // get the name of the output signal
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // look for the end of directive
        if ( !strcmp( pWord, "end" ) )
            break;
        // get the fanout net
        pNet = Abc_NtkFindNet( pNtk, pWord );
        if ( pNet == NULL )
        {
            sprintf( pMan->sError, "Cannot read the initial statement for %s (output wire is not defined).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // get the equal sign
        if ( Ver_StreamPopChar(p) != '=' )
        {
            sprintf( pMan->sError, "Cannot read the initial statement for %s (expected equality sign).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // skip the comments
        if ( !Ver_ParseSkipComments( pMan ) )
            return 0;
        // get the second name
        pEquation = Ver_StreamGetWord( p, ";" );
        if ( pEquation == NULL )
            return 0;
        // find the corresponding latch
        pNode = Abc_ObjFanin0(pNet);
        assert( Abc_ObjIsLatch(pNode) );
        // set the initial state
        if ( pEquation[0] == '2' )
            Abc_LatchSetInitDc( pNode );
        else if ( pEquation[0] == '1')
            Abc_LatchSetInit1( pNode );
        else if ( pEquation[0] == '0' )
            Abc_LatchSetInit0( pNode );
        else
        {
            sprintf( pMan->sError, "Incorrect initial value of the latch %s (expected equality sign).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // remove the last symbol
        Symbol = Ver_StreamPopChar(p);
        assert( Symbol == ';' );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses one directive.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseGate( Ver_Man_t * pMan, Abc_Ntk_t * pNtkGate )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Ntk_t * pNtk = pMan->pNtkCur;
    Abc_Obj_t * pNetFormal, * pNetActual;
    Abc_Obj_t * pObj, * pNode;
    char * pWord, Symbol;
    int i, fCompl;

    // convert from the mapped netlist into the BDD netlist
    if ( pNtk->ntkFunc == ABC_FUNC_BLACKBOX )
    {
        pNtk->ntkFunc = ABC_FUNC_MAP;
        pNtk->pManFunc = pMan->pGateLib;
    }
    else if ( pNtk->ntkFunc != ABC_FUNC_MAP )
    {
        sprintf( pMan->sError, "The network %s appears to contain both mapped gates and assign statements. Currently such network are not allowed. One way to fix this problem is to replace assigns by buffers from the library.", pMan->pNtkCur );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    // clean the PI/PO pointers
    Abc_NtkForEachPi( pNtkGate, pObj, i )
        pObj->pCopy = NULL;
    Abc_NtkForEachPo( pNtkGate, pObj, i )
        pObj->pCopy = NULL;
    // parse the directive and set the pointers to the PIs/POs of the gate
    pWord = Ver_ParseGetName( pMan );
    if ( pWord == NULL )
        return 0;
    // this is gate name - throw it away
    if ( Ver_StreamPopChar(p) != '(' )
    {
        sprintf( pMan->sError, "Cannot parse gate %s (expected opening paranthesis).", pNtkGate->pName );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }
    // parse pairs of formal/actural inputs
    while ( 1 )
    {
        // process one pair of formal/actual parameters
        if ( Ver_StreamPopChar(p) != '.' )
        {
            sprintf( pMan->sError, "Cannot parse gate %s (expected .).", pNtkGate->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // parse the formal name
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // get the formal net
        if ( Abc_NtkIsNetlist(pNtkGate) )
            pNetFormal = Abc_NtkFindNet( pNtkGate, pWord );
        else // if ( Abc_NtkIsStrash(pNtkGate) )
            pNetFormal = Abc_NtkFindTerm( pNtkGate, pWord );
        if ( pNetFormal == NULL )
        {
            sprintf( pMan->sError, "Formal net is missing in gate %s.", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // open the paranthesis
        if ( Ver_StreamPopChar(p) != '(' )
        {
            sprintf( pMan->sError, "Cannot formal parameter %s of gate %s (expected opening paranthesis).", pWord, pNtkGate->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // parse the actual name
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // check if the name is complemented
        fCompl = (pWord[0] == '~');
        if ( fCompl )
            pWord++;
        // get the actual net
        pNetActual = Abc_NtkFindNet( pMan->pNtkCur, pWord );
        if ( pNetActual == NULL )
        {
            sprintf( pMan->sError, "Actual net is missing in gate %s.", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // close the paranthesis
        if ( Ver_StreamPopChar(p) != ')' )
        {
            sprintf( pMan->sError, "Cannot formal parameter %s of gate %s (expected closing paranthesis).", pWord, pNtkGate->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // process the pair
        if ( Abc_ObjIsPi(Abc_ObjFanin0Ntk(pNetFormal)) )  // PI net
            Abc_ObjFanin0Ntk(pNetFormal)->pCopy = pNetActual; // Abc_ObjNotCond( pNetActual, fCompl );
        else if ( Abc_ObjIsPo(Abc_ObjFanout0Ntk(pNetFormal)) )  // P0 net
        {
            assert( fCompl == 0 );
            Abc_ObjFanout0Ntk(pNetFormal)->pCopy = pNetActual; // Abc_ObjNotCond( pNetActual, fCompl );
        }
        else
        {
            sprintf( pMan->sError, "Cannot match formal net %s with PI or PO of the gate %s.", pWord, pNtkGate->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // check if it is the end of gate
        Ver_ParseSkipComments( pMan );
        Symbol = Ver_StreamPopChar(p);
        if ( Symbol == ')' )
            break;
        // skip comma
        if ( Symbol != ',' )
        {
            sprintf( pMan->sError, "Cannot formal parameter %s of gate %s (expected closing paranthesis).", pWord, pNtkGate->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        Ver_ParseSkipComments( pMan );
    }

    // check if it is the end of gate
    Ver_ParseSkipComments( pMan );
    if ( Ver_StreamPopChar(p) != ';' )
    {
        sprintf( pMan->sError, "Cannot read gate %s (expected closing semicolumn).", pNtkGate->pName );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    // make sure each input net is driven
    Abc_NtkForEachPi( pNtkGate, pObj, i )
        if ( pObj->pCopy == NULL )
        {
            sprintf( pMan->sError, "Formal input %s of gate %s has no actual input.", Abc_ObjFanout0(pObj)->pData, pNtkGate->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
/*
    // make sure each output net is driving something
    Abc_NtkForEachPo( pNtkGate, pObj, i )
        if ( pObj->pCopy == NULL )
        {
            sprintf( pMan->sError, "Formal output %s of gate %s has no actual output.", Abc_ObjFanin0(pObj)->pData, pNtkGate->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
*/
    // create a new node 
    pNode = Abc_NtkCreateNode( pMan->pNtkCur );
    // connect to fanin nets
    Abc_NtkForEachPi( pNtkGate, pObj, i )
        Abc_ObjAddFanin( pNode, pObj->pCopy );
    // connect to fanout nets
    Abc_NtkForEachPo( pNtkGate, pObj, i )
        if ( pObj->pCopy )
            Abc_ObjAddFanin( pObj->pCopy, pNode );
    // set the functionality
    pNode->pData = pNtkGate;
    return 1;
}


/**Function*************************************************************

  Synopsis    [Creates PI terminal and net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Ver_ParseCreatePi( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet, * pTerm;
    // get the PI net
    pNet  = Abc_NtkFindNet( pNtk, pName );
    if ( pNet )
        printf( "Warning: PI \"%s\" appears twice in the list.\n", pName );
    pNet  = Abc_NtkFindOrCreateNet( pNtk, pName );
    // add the PI node
    pTerm = Abc_NtkCreatePi( pNtk );
    Abc_ObjAddFanin( pNet, pTerm );
    return pTerm;
}

/**Function*************************************************************

  Synopsis    [Creates PO terminal and net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Ver_ParseCreatePo( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pNet, * pTerm;
    // get the PO net
    pNet  = Abc_NtkFindNet( pNtk, pName );
    if ( pNet && Abc_ObjFaninNum(pNet) == 0 )
        printf( "Warning: PO \"%s\" appears twice in the list.\n", pName );
    pNet  = Abc_NtkFindOrCreateNet( pNtk, pName );
    // add the PO node
    pTerm = Abc_NtkCreatePo( pNtk );
    Abc_ObjAddFanin( pTerm, pNet );
    return pTerm;
}

/**Function*************************************************************

  Synopsis    [Create a latch with the given input/output.]

  Description [By default, the latch value is unknown (ABC_INIT_NONE).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Ver_ParseCreateLatch( Abc_Ntk_t * pNtk, char * pNetLI, char * pNetLO )
{
    Abc_Obj_t * pLatch, * pNet;
    // create a new latch and add it to the network
    pLatch = Abc_NtkCreateLatch( pNtk );
    // get the LI net
    pNet = Abc_NtkFindOrCreateNet( pNtk, pNetLI );
    Abc_ObjAddFanin( pLatch, pNet );
    // get the LO net
    pNet = Abc_NtkFindOrCreateNet( pNtk, pNetLO );
    Abc_ObjAddFanin( pNet, pLatch );
    return pLatch;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


