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
#include "mio.h"
#include "main.h"

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

// types of verilog gates
typedef enum { 
    VER_GATE_AND = 0,
    VER_GATE_OR,
    VER_GATE_XOR,
    VER_GATE_BUF,
    VER_GATE_NAND,
    VER_GATE_NOR,
    VER_GATE_XNOR,
    VER_GATE_NOT
} Ver_GateType_t;

static Ver_Man_t * Ver_ParseStart( char * pFileName, Abc_Lib_t * pGateLib );
static void Ver_ParseStop( Ver_Man_t * p );
static void Ver_ParseFreeData( Ver_Man_t * p );
static void Ver_ParseInternal( Ver_Man_t * p );
static int  Ver_ParseModule( Ver_Man_t * p );
static int  Ver_ParseSignal( Ver_Man_t * p, Abc_Ntk_t * pNtk, Ver_SignalType_t SigType );
static int  Ver_ParseAlways( Ver_Man_t * p, Abc_Ntk_t * pNtk );
static int  Ver_ParseInitial( Ver_Man_t * p, Abc_Ntk_t * pNtk );
static int  Ver_ParseAssign( Ver_Man_t * p, Abc_Ntk_t * pNtk );
static int  Ver_ParseGateStandard( Ver_Man_t * pMan, Abc_Ntk_t * pNtk, Ver_GateType_t GateType );
static int  Ver_ParseGate( Ver_Man_t * p, Abc_Ntk_t * pNtk, Mio_Gate_t * pGate );
static int  Ver_ParseBox( Ver_Man_t * pMan, Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkBox );
static int  Ver_ParseConnectBox( Ver_Man_t * pMan, Abc_Obj_t * pBox );
static int  Vec_ParseAttachBoxes( Ver_Man_t * pMan );

static Abc_Obj_t * Ver_ParseCreatePi( Abc_Ntk_t * pNtk, char * pName );
static Abc_Obj_t * Ver_ParseCreatePo( Abc_Ntk_t * pNtk, char * pName );
static Abc_Obj_t * Ver_ParseCreateLatch( Abc_Ntk_t * pNtk, Abc_Obj_t * pNetLI, Abc_Obj_t * pNetLO );
static Abc_Obj_t * Ver_ParseCreateInv( Abc_Ntk_t * pNtk, Abc_Obj_t * pNet );

static inline int Ver_NtkIsDefined( Abc_Ntk_t * pNtkBox )  { assert( pNtkBox->pName );     return Abc_NtkPiNum(pNtkBox) || Abc_NtkPoNum(pNtkBox);  }
static inline int Ver_ObjIsConnected( Abc_Obj_t * pObj )   { assert( Abc_ObjIsBox(pObj) ); return Abc_ObjFaninNum(pObj) || Abc_ObjFanoutNum(pObj); }

int glo_fMapped = 0; // this is bad!

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

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
    if ( p->pReader == NULL )
        return NULL;
    p->Output    = stdout;
    p->pProgress = Extra_ProgressBarStart( stdout, Ver_StreamGetFileSize(p->pReader) );
    p->vNames    = Vec_PtrAlloc( 100 );
    p->vStackFn  = Vec_PtrAlloc( 100 );
    p->vStackOp  = Vec_IntAlloc( 100 );
    // create the design library and assign the technology library
    p->pDesign   = Abc_LibCreate( pFileName );
    p->pDesign->pLibrary = pGateLib;
    p->pDesign->pGenlib = Abc_FrameReadLibGen();
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
Abc_Lib_t * Ver_ParseFile( char * pFileName, Abc_Lib_t * pGateLib, int fCheck, int fUseMemMan )
{
    Ver_Man_t * p;
    Abc_Lib_t * pDesign;
    // start the parser
    p = Ver_ParseStart( pFileName, pGateLib );
    p->fMapped    = glo_fMapped;
    p->fCheck     = fCheck;
    p->fUseMemMan = fUseMemMan;
    if ( glo_fMapped )
    {
        Hop_ManStop(p->pDesign->pManFunc);
        p->pDesign->pManFunc = NULL;
    }
    // parse the file
    Ver_ParseInternal( p );
    // save the result
    pDesign = p->pDesign;
    p->pDesign = NULL;
    // stop the parser
    Ver_ParseStop( p );
    return pDesign;
}

/**Function*************************************************************

  Synopsis    [File parser.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ver_ParseInternal( Ver_Man_t * pMan )
{
    Abc_Ntk_t * pNtk;
    char * pToken;
    int i;

    // preparse the modeles
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
        if ( !Ver_ParseModule(pMan) )
            return;
    }

    // process defined and undefined boxes
    if ( !Vec_ParseAttachBoxes( pMan ) )
        return;

    // connect the boxes and check
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
    {
        // fix the dangling nets
        Abc_NtkFinalizeRead( pNtk );
        // check the network for correctness
        if ( pMan->fCheck && !Abc_NtkCheckRead( pNtk ) )
        {
            pMan->fTopLevel = 1;
            sprintf( pMan->sError, "The network check has failed.", pNtk->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return;
        }
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
    if ( p->pDesign )
    {
        Abc_LibFree( p->pDesign, NULL );
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

  Synopsis    [Finds the network by name or create a new blackbox network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Ver_ParseFindOrCreateNetwork( Ver_Man_t * pMan, char * pName )
{
    Abc_Ntk_t * pNtkNew;
    // check if the network exists
    if ( pNtkNew = Abc_LibFindModelByName( pMan->pDesign, pName ) )
        return pNtkNew;
//printf( "Creating network %s.\n", pName );
    // create new network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_NETLIST, ABC_FUNC_BLACKBOX, pMan->fUseMemMan );
    pNtkNew->pName = Extra_UtilStrsav( pName );
    pNtkNew->pSpec = NULL;
    // add module to the design
    Abc_LibAddModel( pMan->pDesign, pNtkNew );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Finds the network by name or create a new blackbox network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Ver_ParseFindNet( Abc_Ntk_t * pNtk, char * pName )
{
    Abc_Obj_t * pObj;
    if ( pObj = Abc_NtkFindNet(pNtk, pName) )
        return pObj;
    if ( !strcmp( pName, "1\'b0" ) )
        return Abc_NtkFindOrCreateNet( pNtk, "1\'b0" );
    if ( !strcmp( pName, "1\'b1" ) )
        return Abc_NtkFindOrCreateNet( pNtk, "1\'b1" );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the blackbox type into a different one.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseConvertNetwork( Ver_Man_t * pMan, Abc_Ntk_t * pNtk, int fMapped )
{
    if ( fMapped )
    {
        // convert from the blackbox into the network with local functions representated by AIGs
        if ( pNtk->ntkFunc == ABC_FUNC_BLACKBOX )
        {
            // change network type
            assert( pNtk->pManFunc == NULL );
            pNtk->ntkFunc = ABC_FUNC_MAP;
            pNtk->pManFunc = pMan->pDesign->pGenlib;
        }
        else if ( pNtk->ntkFunc != ABC_FUNC_MAP )
        {
            sprintf( pMan->sError, "The network %s appears to have both gates and assign statements. Currently such network are not allowed. One way to fix this problem might be to replace assigns by buffers from the library.", pNtk->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
    }
    else
    {
        // convert from the blackbox into the network with local functions representated by AIGs
        if ( pNtk->ntkFunc == ABC_FUNC_BLACKBOX )
        {
            // change network type
            assert( pNtk->pManFunc == NULL );
            pNtk->ntkFunc = ABC_FUNC_AIG;
            pNtk->pManFunc = pMan->pDesign->pManFunc;
        }
        else if ( pNtk->ntkFunc != ABC_FUNC_AIG )
        {
            sprintf( pMan->sError, "The network %s appears to have both gates and assign statements. Currently such network are not allowed. One way to fix this problem might be to replace assigns by buffers from the library.", pNtk->pName );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses one Verilog module.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseModule( Ver_Man_t * pMan )
{
    Mio_Gate_t * pGate;
    Ver_Stream_t * p = pMan->pReader;
    Abc_Ntk_t * pNtk, * pNtkTemp;
    char * pWord, Symbol;
    int RetValue;

    // get the network name
    pWord = Ver_ParseGetName( pMan );

    // get the network with this name
    pNtk = Ver_ParseFindOrCreateNetwork( pMan, pWord );

    // make sure we stopped at the opening paranthesis
    if ( Ver_StreamPopChar(p) != '(' )
    {
        sprintf( pMan->sError, "Cannot find \"(\" after \"module\".", pNtk->pName );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    // skip to the end of parantheses
    do {
        if ( Ver_ParseGetName( pMan ) == NULL )
            return 0;
        Symbol = Ver_StreamPopChar(p);
    } while ( Symbol == ',' );
    assert( Symbol == ')' );
    if ( !Ver_ParseSkipComments( pMan ) )
        return 0;
    Symbol = Ver_StreamPopChar(p);
    assert( Symbol == ';' );

    // parse the inputs/outputs/registers/wires/inouts
    while ( 1 )
    {
        Extra_ProgressBarUpdate( pMan->pProgress, Ver_StreamGetCurPosition(p), NULL );
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        if ( !strcmp( pWord, "input" ) )
            RetValue = Ver_ParseSignal( pMan, pNtk, VER_SIG_INPUT );
        else if ( !strcmp( pWord, "output" ) )
            RetValue = Ver_ParseSignal( pMan, pNtk, VER_SIG_OUTPUT );
        else if ( !strcmp( pWord, "reg" ) )
            RetValue = Ver_ParseSignal( pMan, pNtk, VER_SIG_REG );
        else if ( !strcmp( pWord, "wire" ) )
            RetValue = Ver_ParseSignal( pMan, pNtk, VER_SIG_WIRE );
        else if ( !strcmp( pWord, "inout" ) )
            RetValue = Ver_ParseSignal( pMan, pNtk, VER_SIG_INOUT );
        else 
            break;
        if ( RetValue == 0 )
            return 0;
    }

    // parse the remaining statements
    while ( 1 )
    {
        Extra_ProgressBarUpdate( pMan->pProgress, Ver_StreamGetCurPosition(p), NULL );

        if ( !strcmp( pWord, "and" ) )
            RetValue = Ver_ParseGateStandard( pMan, pNtk, VER_GATE_AND );
        else if ( !strcmp( pWord, "or" ) )
            RetValue = Ver_ParseGateStandard( pMan, pNtk, VER_GATE_OR );
        else if ( !strcmp( pWord, "xor" ) )
            RetValue = Ver_ParseGateStandard( pMan, pNtk, VER_GATE_XOR );
        else if ( !strcmp( pWord, "buf" ) )
            RetValue = Ver_ParseGateStandard( pMan, pNtk, VER_GATE_BUF );
        else if ( !strcmp( pWord, "nand" ) )
            RetValue = Ver_ParseGateStandard( pMan, pNtk, VER_GATE_NAND );
        else if ( !strcmp( pWord, "nor" ) )
            RetValue = Ver_ParseGateStandard( pMan, pNtk, VER_GATE_NOR );
        else if ( !strcmp( pWord, "xnor" ) )
            RetValue = Ver_ParseGateStandard( pMan, pNtk, VER_GATE_XNOR );
        else if ( !strcmp( pWord, "not" ) )
            RetValue = Ver_ParseGateStandard( pMan, pNtk, VER_GATE_NOT );

        else if ( !strcmp( pWord, "assign" ) )
            RetValue = Ver_ParseAssign( pMan, pNtk );
        else if ( !strcmp( pWord, "always" ) )
            RetValue = Ver_ParseAlways( pMan, pNtk );
        else if ( !strcmp( pWord, "initial" ) )
            RetValue = Ver_ParseInitial( pMan, pNtk );
        else if ( !strcmp( pWord, "endmodule" ) )
            break;
        else if ( pMan->pDesign->pGenlib && (pGate = Mio_LibraryReadGateByName(pMan->pDesign->pGenlib, pWord)) ) // current design
            RetValue = Ver_ParseGate( pMan, pNtk, pGate );
//        else if ( pMan->pDesign->pLibrary && st_lookup(pMan->pDesign->pLibrary->tModules, pWord, (char**)&pNtkTemp) ) // gate library
//            RetValue = Ver_ParseGate( pMan, pNtkTemp );
        else // assume this is the box used in the current design
        {
            pNtkTemp = Ver_ParseFindOrCreateNetwork( pMan, pWord );
            RetValue = Ver_ParseBox( pMan, pNtk, pNtkTemp );
        }
        if ( RetValue == 0 )
            return 0;
        // skip the comments
        if ( !Ver_ParseSkipComments( pMan ) )
            return 0;
        // get new word
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
    }

    // convert from the blackbox into the network with local functions representated by AIGs
    if ( pNtk->ntkFunc == ABC_FUNC_BLACKBOX )
    {
        if ( Abc_NtkNodeNum(pNtk) > 0 || Abc_NtkBoxNum(pNtk) > 0 )
        {
            if ( !Ver_ParseConvertNetwork( pMan, pNtk, pMan->fMapped ) )
                return 0;
        }
        else
        {
            Abc_Obj_t * pObj, * pBox, * pTerm;
            int i; 
            pBox = Abc_NtkCreateBlackbox(pNtk);
            Abc_NtkForEachPi( pNtk, pObj, i )
            {
                pTerm = Abc_NtkCreateBi(pNtk);
                Abc_ObjAddFanin( pTerm, Abc_ObjFanout0(pObj) );
                Abc_ObjAddFanin( pBox, pTerm );
            }
            Abc_NtkForEachPo( pNtk, pObj, i )
            {
                pTerm = Abc_NtkCreateBo(pNtk);
                Abc_ObjAddFanin( pTerm, pBox );
                Abc_ObjAddFanin( Abc_ObjFanin0(pObj), pTerm );
            }
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses one directive.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseSignal( Ver_Man_t * pMan, Abc_Ntk_t * pNtk, Ver_SignalType_t SigType )
{
    Ver_Stream_t * p = pMan->pReader;
    char Buffer[1000];
    int Lower, Upper, i;
    char * pWord;
    char Symbol;
    Lower = Upper = 0;
    while ( 1 )
    {
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;

        // check if the range is specified
        if ( pWord[0] == '[' && !pMan->fNameLast )
        {
            Lower = atoi( pWord + 1 );
            // find the splitter
            while ( *pWord && *pWord != ':' && *pWord != ']' )
                pWord++;
            if ( *pWord == 0 )
            {
                sprintf( pMan->sError, "Cannot find closing bracket in this line." );
                Ver_ParsePrintErrorMessage( pMan );
                return 0;
            }
            if ( *pWord == ']' )
                Upper = Lower;
            else
            {
                Upper = atoi( pWord + 1 );
                if ( Lower > Upper )
                    i = Lower, Lower = Upper, Upper = i;
                // find the closing paranthesis
                while ( *pWord && *pWord != ']' )
                    pWord++;
                if ( *pWord == 0 )
                {
                    sprintf( pMan->sError, "Cannot find closing bracket in this line." );
                    Ver_ParsePrintErrorMessage( pMan );
                    return 0;
                }
                assert( *pWord == ']' );
            }
            // check the case of no space between bracket and the next word
            if ( *(pWord+1) != 0 )
                pWord++;
            else
            {
                // get the signal name
                pWord = Ver_ParseGetName( pMan );
                if ( pWord == NULL )
                    return 0;
            }
        }

        // create signals
        if ( Lower == 0 && Upper == 0 )
        {
            if ( SigType == VER_SIG_INPUT || SigType == VER_SIG_INOUT )
                Ver_ParseCreatePi( pNtk, pWord );
            if ( SigType == VER_SIG_OUTPUT || SigType == VER_SIG_INOUT )
                Ver_ParseCreatePo( pNtk, pWord );
            if ( SigType == VER_SIG_WIRE || SigType == VER_SIG_REG )
                Abc_NtkFindOrCreateNet( pNtk, pWord );
        }
        else
        {
            for ( i = Lower; i <= Upper; i++ )
            {
                sprintf( Buffer, "%s[%d]", pWord, i );
                if ( SigType == VER_SIG_INPUT || SigType == VER_SIG_INOUT )
                    Ver_ParseCreatePi( pNtk, Buffer );
                if ( SigType == VER_SIG_OUTPUT || SigType == VER_SIG_INOUT )
                    Ver_ParseCreatePo( pNtk, Buffer );
                if ( SigType == VER_SIG_WIRE || SigType == VER_SIG_REG )
                    Abc_NtkFindOrCreateNet( pNtk, Buffer );
            }
        }

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
int Ver_ParseAlways( Ver_Man_t * pMan, Abc_Ntk_t * pNtk )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Obj_t * pNet, * pNet2;
    int fStopAfterOne;
    char * pWord, * pWord2;
    char Symbol;
    // parse the directive 
    pWord = Ver_ParseGetName( pMan );
    if ( pWord == NULL )
        return 0;
    if ( pWord[0] == '@' )
    {
        Ver_StreamSkipToChars( p, ")" );
        Ver_StreamPopChar(p);
        // parse the directive 
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
    }
    // decide how many statements to parse
    fStopAfterOne = 0;
    if ( strcmp( pWord, "begin" ) )
        fStopAfterOne = 1;
    // iterate over the initial states
    while ( 1 )
    {
        if ( !fStopAfterOne )
        {
            // get the name of the output signal
            pWord = Ver_ParseGetName( pMan );
            if ( pWord == NULL )
                return 0;
            // look for the end of directive
            if ( !strcmp( pWord, "end" ) )
                break;
        }
        // get the fanout net
        pNet = Ver_ParseFindNet( pNtk, pWord );
        if ( pNet == NULL )
        {
            sprintf( pMan->sError, "Cannot read the always statement for %s (output wire is not defined).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // get the equality sign
        Symbol = Ver_StreamPopChar(p);
        if ( Symbol != '<' && Symbol != '=' )
        {
            sprintf( pMan->sError, "Cannot read the assign statement for %s (expected <= or =).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        if ( Symbol == '<' )
            Ver_StreamPopChar(p);
        // skip the comments
        if ( !Ver_ParseSkipComments( pMan ) )
            return 0;
        // get the second name
        pWord2 = Ver_ParseGetName( pMan );
        if ( pWord2 == NULL )
            return 0;
        // check if the name is complemented
        if ( pWord2[0] == '~' )
        {
            pNet2 = Ver_ParseFindNet( pNtk, pWord2+1 );
            pNet2 = Ver_ParseCreateInv( pNtk, pNet2 );
        }
        else
            pNet2 = Ver_ParseFindNet( pNtk, pWord2 );
        if ( pNet2 == NULL )
        {
            sprintf( pMan->sError, "Cannot read the always statement for %s (input wire is not defined).", pWord2 );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // create the latch
        Ver_ParseCreateLatch( pNtk, pNet2, pNet );
        // remove the last symbol
        Symbol = Ver_StreamPopChar(p);
        assert( Symbol == ';' );
        // quit if only one directive
        if ( fStopAfterOne )
            break;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses one directive.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseInitial( Ver_Man_t * pMan, Abc_Ntk_t * pNtk )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Obj_t * pNode, * pNet;
    int fStopAfterOne;
    char * pWord, * pEquation;
    char Symbol;
    // parse the directive 
    pWord = Ver_ParseGetName( pMan );
    if ( pWord == NULL )
        return 0;
    // decide how many statements to parse
    fStopAfterOne = 0;
    if ( strcmp( pWord, "begin" ) )
        fStopAfterOne = 1;
    // iterate over the initial states
    while ( 1 )
    {
        if ( !fStopAfterOne )
        {
            // get the name of the output signal
            pWord = Ver_ParseGetName( pMan );
            if ( pWord == NULL )
                return 0;
            // look for the end of directive
            if ( !strcmp( pWord, "end" ) )
                break;
        }
        // get the fanout net
        pNet = Ver_ParseFindNet( pNtk, pWord );
        if ( pNet == NULL )
        {
            sprintf( pMan->sError, "Cannot read the initial statement for %s (output wire is not defined).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // get the equality sign
        Symbol = Ver_StreamPopChar(p);
        if ( Symbol != '<' && Symbol != '=' )
        {
            sprintf( pMan->sError, "Cannot read the assign statement for %s (expected <= or =).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        if ( Symbol == '<' )
            Ver_StreamPopChar(p);
        // skip the comments
        if ( !Ver_ParseSkipComments( pMan ) )
            return 0;
        // get the second name
        pEquation = Ver_StreamGetWord( p, ";" );
        if ( pEquation == NULL )
            return 0;
        // find the corresponding latch
        if ( Abc_ObjFaninNum(pNet) == 0 )
        {
            sprintf( pMan->sError, "Cannot find the latch to assign the initial value." );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        pNode = Abc_ObjFanin0(Abc_ObjFanin0(pNet));
        assert( Abc_ObjIsLatch(pNode) );
        // set the initial state
        if ( !strcmp(pEquation, "0") || !strcmp(pEquation, "1\'b0") )
            Abc_LatchSetInit0( pNode );
        else if ( !strcmp(pEquation, "1") || !strcmp(pEquation, "1\'b1") )
            Abc_LatchSetInit1( pNode );
//        else if ( !strcmp(pEquation, "2") )
//            Abc_LatchSetInitDc( pNode );
        else 
        {
            sprintf( pMan->sError, "Incorrect initial value of the latch %s.", Abc_ObjName(pNet) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // remove the last symbol
        Symbol = Ver_StreamPopChar(p);
        assert( Symbol == ';' );
        // quit if only one directive
        if ( fStopAfterOne )
            break;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses one directive.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseAssign( Ver_Man_t * pMan, Abc_Ntk_t * pNtk )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Obj_t * pNode, * pNet;
    char * pWord, * pName, * pEquation;
    Hop_Obj_t * pFunc;
    char Symbol;
    int i, Length, fReduction;

//    if ( Ver_StreamGetLineNumber(p) == 2756 )
//    {
//        int x = 0;
//    }

    // convert from the blackbox into the network with local functions representated by AIGs
    if ( !Ver_ParseConvertNetwork( pMan, pNtk, pMan->fMapped ) )
        return 0;

    while ( 1 )
    {
        // get the name of the output signal
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // consider the case of reduction operations
        fReduction = 0;
        if ( pWord[0] == '{' && !pMan->fNameLast )
            fReduction = 1;
        if ( fReduction )
        {
            pWord++;
            pWord[strlen(pWord)-1] = 0;
            assert( pWord[0] != '\\' );
        }
        // get the fanout net
        pNet = Ver_ParseFindNet( pNtk, pWord );
        if ( pNet == NULL )
        {
            sprintf( pMan->sError, "Cannot read the assign statement for %s (output wire is not defined).", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // get the equality sign
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
        if ( fReduction )
            pEquation = Ver_StreamGetWord( p, ";" );
        else
            pEquation = Ver_StreamGetWord( p, ",;" );
        if ( pEquation == NULL )
        {
            sprintf( pMan->sError, "Cannot read the equation for %s.", Abc_ObjName(pNet) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // consider the case of mapped network
        if ( pMan->fMapped )
        {
            Vec_PtrClear( pMan->vNames );
            if ( !strcmp( pEquation, "1\'b0" ) )
                pFunc = (Hop_Obj_t *)Mio_LibraryReadConst0(Abc_FrameReadLibGen());
            else if ( !strcmp( pEquation, "1\'b1" ) )
                pFunc = (Hop_Obj_t *)Mio_LibraryReadConst1(Abc_FrameReadLibGen());
            else
            {
                if ( Ver_ParseFindNet(pNtk, pEquation) == NULL )
                {
                    sprintf( pMan->sError, "Cannot read Verilog with non-trivail assignments in the mapped netlist.", pEquation );
                    Ver_ParsePrintErrorMessage( pMan );
                    return 0;
                }
                Vec_PtrPush( pMan->vNames, (void *)strlen(pEquation) );
                Vec_PtrPush( pMan->vNames, pEquation );
                // get the buffer
                pFunc = (Hop_Obj_t *)Mio_LibraryReadBuf(Abc_FrameReadLibGen());
            }
        }
        else
        {
            // parse the formula
            if ( fReduction )
                pFunc = Ver_FormulaReduction( pEquation, pNtk->pManFunc, pMan->vNames, pMan->sError );  
            else
                pFunc = Ver_FormulaParser( pEquation, pNtk->pManFunc, pMan->vNames, pMan->vStackFn, pMan->vStackOp, pMan->sError );  
            if ( pFunc == NULL )
            {
                Ver_ParsePrintErrorMessage( pMan );
                return 0;
            }
        }

        // create the node with the given inputs
        pNode = Abc_NtkCreateNode( pNtk );
        pNode->pData = pFunc;
        Abc_ObjAddFanin( pNet, pNode );
        // connect to fanin nets
        for ( i = 0; i < Vec_PtrSize(pMan->vNames)/2; i++ )
        {
            // get the name of this signal
            Length = (int)Vec_PtrEntry( pMan->vNames, 2*i );
            pName  = Vec_PtrEntry( pMan->vNames, 2*i + 1 );
            pName[Length] = 0;
            // find the corresponding net
            pNet = Ver_ParseFindNet( pNtk, pName );
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
int Ver_ParseGateStandard( Ver_Man_t * pMan, Abc_Ntk_t * pNtk, Ver_GateType_t GateType )
{
    Ver_Stream_t * p = pMan->pReader;
    Abc_Obj_t * pNet, * pNode;
    char * pWord, Symbol;

    // convert from the blackbox into the network with local functions representated by AIGs
    if ( !Ver_ParseConvertNetwork( pMan, pNtk, pMan->fMapped ) )
        return 0;

    // this is gate name - throw it away
    if ( Ver_StreamPopChar(p) != '(' )
    {
        sprintf( pMan->sError, "Cannot parse a standard gate (expected opening paranthesis)." );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }
    Ver_ParseSkipComments( pMan );

    // create the node
    pNode = Abc_NtkCreateNode( pNtk );

    // parse pairs of formal/actural inputs
    while ( 1 )
    {
        // parse the output name
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // get the net corresponding to this output
        pNet = Ver_ParseFindNet( pNtk, pWord );
        if ( pNet == NULL )
        {
            sprintf( pMan->sError, "Net is missing in gate %s.", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        // if this is the first net, add it as an output
        if ( Abc_ObjFanoutNum(pNode) == 0 )
            Abc_ObjAddFanin( pNet, pNode );
        else
            Abc_ObjAddFanin( pNode, pNet );
        // check if it is the end of gate
        Ver_ParseSkipComments( pMan );
        Symbol = Ver_StreamPopChar(p);
        if ( Symbol == ')' )
            break;
        // skip comma
        if ( Symbol != ',' )
        {
            sprintf( pMan->sError, "Cannot parse a standard gate %s (expected closing paranthesis).", Abc_ObjName(Abc_ObjFanout0(pNode)) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        Ver_ParseSkipComments( pMan );
    }
    if ( (GateType == VER_GATE_BUF || GateType == VER_GATE_NOT) && Abc_ObjFaninNum(pNode) != 1 )
    {
        sprintf( pMan->sError, "Buffer or interver with multiple fanouts %s (currently not supported).", Abc_ObjName(Abc_ObjFanout0(pNode)) );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    // check if it is the end of gate
    Ver_ParseSkipComments( pMan );
    if ( Ver_StreamPopChar(p) != ';' )
    {
        sprintf( pMan->sError, "Cannot read standard gate %s (expected closing semicolumn).", Abc_ObjName(Abc_ObjFanout0(pNode)) );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }
    // add logic function
    if ( GateType == VER_GATE_AND || GateType == VER_GATE_NAND )
        pNode->pData = Hop_CreateAnd( pNtk->pManFunc, Abc_ObjFaninNum(pNode) );
    else if ( GateType == VER_GATE_OR || GateType == VER_GATE_NOR )
        pNode->pData = Hop_CreateOr( pNtk->pManFunc, Abc_ObjFaninNum(pNode) );
    else if ( GateType == VER_GATE_XOR || GateType == VER_GATE_XNOR )
        pNode->pData = Hop_CreateExor( pNtk->pManFunc, Abc_ObjFaninNum(pNode) );
    else if ( GateType == VER_GATE_BUF || GateType == VER_GATE_NOT )
        pNode->pData = Hop_CreateAnd( pNtk->pManFunc, Abc_ObjFaninNum(pNode) );
    if ( GateType == VER_GATE_NAND || GateType == VER_GATE_NOR || GateType == VER_GATE_XNOR || GateType == VER_GATE_NOT )
        pNode->pData = Hop_Not( pNode->pData );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses one directive.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseGate( Ver_Man_t * pMan, Abc_Ntk_t * pNtk, Mio_Gate_t * pGate )
{
    Mio_Pin_t * pGatePin;
    Ver_Stream_t * p = pMan->pReader;
    Abc_Obj_t * pNetActual, * pNode;
    char * pWord, Symbol;

    // convert from the blackbox into the network with local functions representated by gates
    if ( 1 != pMan->fMapped )
    {
        sprintf( pMan->sError, "The network appears to be mapped. Use \"r -m\" to read mapped Verilog." );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    // update the network type if needed
    if ( !Ver_ParseConvertNetwork( pMan, pNtk, 1 ) )
        return 0;

    // parse the directive and set the pointers to the PIs/POs of the gate
    pWord = Ver_ParseGetName( pMan );
    if ( pWord == NULL )
        return 0;
    // this is gate name - throw it away
    if ( Ver_StreamPopChar(p) != '(' )
    {
        sprintf( pMan->sError, "Cannot parse gate %s (expected opening paranthesis).", Mio_GateReadName(pGate) );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    // start the node
    pNode = Abc_NtkCreateNode( pNtk );
    pNode->pData = pGate;

    // parse pairs of formal/actural inputs
    pGatePin = Mio_GateReadPins(pGate);
    while ( 1 )
    {
        // process one pair of formal/actual parameters
        if ( Ver_StreamPopChar(p) != '.' )
        {
            sprintf( pMan->sError, "Cannot parse gate %s (expected .).", Mio_GateReadName(pGate) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // parse the formal name
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;

        // make sure that the formal name is the same as the gate's
        if ( Mio_GateReadInputs(pGate) == Abc_ObjFaninNum(pNode) ) 
        {
            if ( strcmp(pWord, Mio_GateReadOutName(pGate)) )
            {
                sprintf( pMan->sError, "Formal output name listed %s is different from the name of the gate output %s.", pWord, Mio_GateReadOutName(pGate) );
                Ver_ParsePrintErrorMessage( pMan );
                return 0;
            }
        }
        else
        {
            if ( strcmp(pWord, Mio_PinReadName(pGatePin)) )
            {
                sprintf( pMan->sError, "Formal input name listed %s is different from the name of the corresponding pin %s.", pWord, Mio_PinReadName(pGatePin) );
                Ver_ParsePrintErrorMessage( pMan );
                return 0;
            }
        }

        // open the paranthesis
        if ( Ver_StreamPopChar(p) != '(' )
        {
            sprintf( pMan->sError, "Cannot formal parameter %s of gate %s (expected opening paranthesis).", pWord, Mio_GateReadName(pGate) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // parse the actual name
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // check if the name is complemented
        assert( pWord[0] != '~' );
/*
        fCompl = (pWord[0] == '~');
        if ( fCompl )
        {
            fComplUsed = 1;
            pWord++;
            if ( pNtk->pData == NULL )
                pNtk->pData = Extra_MmFlexStart();
        }
*/
        // get the actual net
        pNetActual = Ver_ParseFindNet( pNtk, pWord );
        if ( pNetActual == NULL )
        {
            sprintf( pMan->sError, "Actual net %s is missing.", pWord );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // close the paranthesis
        if ( Ver_StreamPopChar(p) != ')' )
        {
            sprintf( pMan->sError, "Cannot formal parameter %s of gate %s (expected closing paranthesis).", pWord, Mio_GateReadName(pGate) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // add the fanin
        if ( Mio_GateReadInputs(pGate) == Abc_ObjFaninNum(pNode) )
            Abc_ObjAddFanin( pNetActual, pNode ); // fanout
        else
            Abc_ObjAddFanin( pNode, pNetActual ); // fanin

        // check if it is the end of gate
        Ver_ParseSkipComments( pMan );
        Symbol = Ver_StreamPopChar(p);
        if ( Symbol == ')' )
            break;

        // skip comma
        if ( Symbol != ',' )
        {
            sprintf( pMan->sError, "Cannot formal parameter %s of gate %s (expected closing paranthesis).", pWord, Mio_GateReadName(pGate) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        Ver_ParseSkipComments( pMan );

        // get the next pin
        pGatePin = Mio_PinReadNext(pGatePin);
    }

    // check that the gate as the same number of input
    if ( !(Abc_ObjFaninNum(pNode) == Mio_GateReadInputs(pGate) && Abc_ObjFanoutNum(pNode) == 1) )
    {
        sprintf( pMan->sError, "Parsing of gate %s has failed.", Mio_GateReadName(pGate) );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    // check if it is the end of gate
    Ver_ParseSkipComments( pMan );
    if ( Ver_StreamPopChar(p) != ';' )
    {
        sprintf( pMan->sError, "Cannot read gate %s (expected closing semicolumn).", Mio_GateReadName(pGate) );
        Ver_ParsePrintErrorMessage( pMan );
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
int Ver_ParseBox( Ver_Man_t * pMan, Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkBox )
{
    Ver_Stream_t * p = pMan->pReader;
    Vec_Ptr_t * vNetPairs;
    Abc_Obj_t * pNetFormal, * pNetActual;
    Abc_Obj_t * pNode;
    char * pWord, Symbol;
    int fCompl;

    // parse the directive and set the pointers to the PIs/POs of the gate
    pWord = Ver_ParseGetName( pMan );
    if ( pWord == NULL )
        return 0;

    // create box to represent this gate
    pNode = Abc_NtkCreateBlackbox( pNtk );
    pNode->pData = pNtkBox;
    Abc_ObjAssignName( pNode, pWord, NULL );

    // continue parsing the box
    if ( Ver_StreamPopChar(p) != '(' )
    {
        sprintf( pMan->sError, "Cannot parse gate %s (expected opening paranthesis).", Abc_ObjName(pNode) );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    // parse pairs of formal/actural inputs
    vNetPairs = Vec_PtrAlloc( 16 );
    pNode->pCopy = (Abc_Obj_t *)vNetPairs;
    while ( 1 )
    {
        // process one pair of formal/actual parameters
        if ( Ver_StreamPopChar(p) != '.' )
        {
            sprintf( pMan->sError, "Cannot parse gate %s (expected .).", Abc_ObjName(pNode) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // parse the formal name
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // get the formal net
        pNetFormal = Abc_NtkFindOrCreateNet( pNtkBox, pWord );
        Vec_PtrPush( vNetPairs, pNetFormal );

        // open the paranthesis
        if ( Ver_StreamPopChar(p) != '(' )
        {
            sprintf( pMan->sError, "Cannot formal parameter %s of gate %s (expected opening paranthesis).", pWord, Abc_ObjName(pNode));
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }

        // parse the actual name
        pWord = Ver_ParseGetName( pMan );
        if ( pWord == NULL )
            return 0;
        // consider the case of empty name
        fCompl = 0;
        if ( pWord[0] == 0 )
        {
            // remove the formal net
//            Vec_PtrPop( vNetPairs );
            pNetActual = Abc_NtkCreateObj( pNtk, ABC_OBJ_NET );
        }
        else
        {
/*
            // check if the name is complemented
            fCompl = (pWord[0] == '~');
            if ( fCompl )
            {
                pWord++;
                if ( pNtk->pData == NULL )
                    pNtk->pData = Extra_MmFlexStart();
            }
*/
            // get the actual net
            pNetActual = Ver_ParseFindNet( pNtk, pWord );
            if ( pNetActual == NULL )
            {
                sprintf( pMan->sError, "Actual net is missing in gate %s.", Abc_ObjName(pNode) );
                Ver_ParsePrintErrorMessage( pMan );
                return 0;
            }
        }
        Vec_PtrPush( vNetPairs, Abc_ObjNotCond( pNetActual, fCompl ) );

        // close the paranthesis
        if ( Ver_StreamPopChar(p) != ')' )
        {
            sprintf( pMan->sError, "Cannot formal parameter %s of gate %s (expected closing paranthesis).", pWord, Abc_ObjName(pNode) );
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
            sprintf( pMan->sError, "Cannot formal parameter %s of gate %s (expected closing paranthesis).", pWord, Abc_ObjName(pNode) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        Ver_ParseSkipComments( pMan );
    }

    // check if it is the end of gate
    Ver_ParseSkipComments( pMan );
    if ( Ver_StreamPopChar(p) != ';' )
    {
        sprintf( pMan->sError, "Cannot read gate %s (expected closing semicolumn).", Abc_ObjName(pNode) );
        Ver_ParsePrintErrorMessage( pMan );
        return 0;
    }

    return 1;
}

/**Function*************************************************************

  Synopsis    [Connects one box to the network]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ver_ParseConnectBox( Ver_Man_t * pMan, Abc_Obj_t * pBox )
{
    Vec_Ptr_t * vNetPairs = (Vec_Ptr_t *)pBox->pCopy;
    Abc_Ntk_t * pNtk = pBox->pNtk;
    Abc_Ntk_t * pNtkBox = pBox->pData;
    Abc_Obj_t * pNet, * pTerm, * pTermNew;
    int i;

    assert( !Ver_ObjIsConnected(pBox) );
    assert( Ver_NtkIsDefined(pNtkBox) );
    assert( !Abc_NtkHasBlackbox(pNtkBox) || Abc_NtkBoxNum(pNtkBox) == 1 );

    // clean the PI/PO nets
    Abc_NtkForEachPi( pNtkBox, pTerm, i )
        Abc_ObjFanout0(pTerm)->pCopy = NULL;
    Abc_NtkForEachPo( pNtkBox, pTerm, i )
        Abc_ObjFanin0(pTerm)->pCopy = NULL;

    // map formal nets into actual nets
    Vec_PtrForEachEntry( vNetPairs, pNet, i )
    {
        // get the actual net corresponding to this formal net (pNet)
        pNet->pCopy = Vec_PtrEntry( vNetPairs, ++i );
        // make sure the actual net is not complemented (otherwise need to use polarity)
        assert( !Abc_ObjIsComplement(pNet->pCopy) );
    }

    // make sure all PI nets are assigned
    Abc_NtkForEachPi( pNtkBox, pTerm, i )
    {
        if ( Abc_ObjFanout0(pTerm)->pCopy == NULL )
        {
            sprintf( pMan->sError, "Input formal net %s of network %s is not driven in box %s.", 
                Abc_ObjName(Abc_ObjFanout0(pTerm)), pNtkBox->pName, Abc_ObjName(pBox) );
            Ver_ParsePrintErrorMessage( pMan );
            return 0;
        }
        pTermNew = Abc_NtkCreateBi( pNtk );
        Abc_ObjAddFanin( pBox, pTermNew );
        Abc_ObjAddFanin( pTermNew, Abc_ObjFanout0(pTerm)->pCopy );
    }

    // create fanins of the box
    Abc_NtkForEachPo( pNtkBox, pTerm, i )
    {
        if ( Abc_ObjFanin0(pTerm)->pCopy == NULL )
            Abc_ObjFanin0(pTerm)->pCopy = Abc_NtkCreateObj( pNtk, ABC_OBJ_NET );
        pTermNew = Abc_NtkCreateBo( pNtk );
        Abc_ObjAddFanin( Abc_ObjFanin0(pTerm)->pCopy, pTermNew );
        Abc_ObjAddFanin( pTermNew, pBox );
    }

    // free the mapping
    Vec_PtrFree( vNetPairs );
    pBox->pCopy = NULL;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Attaches the boxes to the network.]

  Description [Makes sure that the undefined boxes are connected correctly.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Vec_ParseAttachBoxes( Ver_Man_t * pMan )
{
    Abc_Ntk_t * pNtk, * pNtkBox;
    Vec_Ptr_t * vEnvoys, * vNetPairs, * vPivots;
    Abc_Obj_t * pBox, * pTerm, * pNet, * pNetDr, * pNetAct;
    int i, k, m, nBoxes;

    // connect defined boxes
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
    {
        Abc_NtkForEachBlackbox( pNtk, pBox, k )
        {
            if ( pBox->pData && Ver_NtkIsDefined(pBox->pData) )
                if ( !Ver_ParseConnectBox( pMan, pBox ) )
                    return 0;
        }
    }

    // convert blackboxes to whiteboxes
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
        Abc_NtkForEachBlackbox( pNtk, pBox, k )
        {
            pNtkBox = pBox->pData;
            if ( pNtkBox == NULL )
                continue;

            if ( !strcmp( pNtkBox->pName, "ADDHX1" ) )
            {
                int x = 0;
            }

            if ( pBox->pData && !Abc_NtkHasBlackbox(pBox->pData) )
                Abc_ObjBlackboxToWhitebox( pBox );
        }   


    // search for undefined boxes
    nBoxes = 0;
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
        nBoxes += !Ver_NtkIsDefined(pNtk);
    // quit if no undefined boxes are found
    if ( nBoxes == 0 )
        return 1;

    // count how many times each box occurs
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
    {
        assert( pNtk->pData == NULL );
        pNtk->pData = NULL;
    }
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
        Abc_NtkForEachBlackbox( pNtk, pBox, k )
        {
            if ( pBox->pData == NULL )
                continue;
            pNtkBox = pBox->pData;
            pNtkBox->pData = (void *)((int)pNtkBox->pData + 1);
        }

    // print the boxes
    printf( "Warning: The design contains %d undefined objects interpreted as blackboxes:\n", nBoxes );
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
        if ( !Ver_NtkIsDefined(pNtk) )
            printf( "%s (%d)  ", Abc_NtkName(pNtk), (int)pNtk->pData );
    printf( "\n" );

    // clean the boxes
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
        pNtk->pData = NULL;


    // map actual nets into formal nets belonging to the undef boxes
    vPivots = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
    {
        Abc_NtkForEachBlackbox( pNtk, pBox, k )
        {
            if ( pBox->pData == NULL || Ver_NtkIsDefined(pBox->pData) )
                continue;
            vNetPairs = (Vec_Ptr_t *)pBox->pCopy;
            Vec_PtrForEachEntry( vNetPairs, pNet, m )
            {
                pNetAct = Vec_PtrEntry( vNetPairs, ++m );
                // skip already driven nets and constants
                if ( Abc_ObjFaninNum(pNetAct) == 1 )
                    continue;
                if ( !(strcmp(Abc_ObjName(pNetAct), "1\'b0") && strcmp(Abc_ObjName(pNetAct), "1\'b1")) ) // constant
                    continue;
                // add this net
                if ( pNetAct->pData == NULL )
                {
                    pNetAct->pData = Vec_PtrAlloc( 16 );
                    Vec_PtrPush( vPivots, pNetAct );
                }
                vEnvoys = pNetAct->pData;
                Vec_PtrPush( vEnvoys, pNet );
            }
        }
    }

    // for each pivot net, find the driver
    Vec_PtrForEachEntry( vPivots, pNetAct, i )
    {
        char * pName = Abc_ObjName(pNetAct);
/*
        if ( !strcmp( Abc_ObjName(pNetAct), "dma_fifo_ff_cnt[2]" ) )
        {
            int x = 0;
        }
*/
        assert( Abc_ObjFaninNum(pNetAct) == 0 );
        assert( strcmp(Abc_ObjName(pNetAct), "1\'b0") && strcmp(Abc_ObjName(pNetAct), "1\'b1") );
        vEnvoys = pNetAct->pData; pNetAct->pData = NULL;
        // find the driver starting from the last nets
        pNetDr = NULL;
        for ( m = 0; m < 64; m++ )
        {
            Vec_PtrForEachEntry( vEnvoys, pNet, k )
            {
                if ( Abc_ObjId(pNet) == 0 )
                    continue;
                if ( (int)Abc_ObjId(pNet) == Abc_NtkObjNumMax(pNet->pNtk) - 1 - m )
                {
                    pNetDr = pNet;
                    break;
                }
            }
            if ( pNetDr )
                break;
        }
        assert( pNetDr != NULL );
        Vec_PtrWriteEntry( vPivots, i, pNetDr );
        Vec_PtrFree( vEnvoys );
    }

    // for each pivot net, create driver
    Vec_PtrForEachEntry( vPivots, pNetDr, i )
    {
        if ( pNetDr == NULL )
            continue;
        assert( Abc_ObjFaninNum(pNetDr) <= 1 );
        if ( Abc_ObjFaninNum(pNetDr) == 1 )
            continue;
        // drive this net with the box
        pTerm = Abc_NtkCreateBo( pNetDr->pNtk );
        assert( Abc_NtkBoxNum(pNetDr->pNtk) <= 1 );
        pBox = Abc_NtkBoxNum(pNetDr->pNtk)? Abc_NtkBox(pNetDr->pNtk,0) : Abc_NtkCreateBlackbox(pNetDr->pNtk);
        Abc_ObjAddFanin( Abc_NtkCreatePo(pNetDr->pNtk), pNetDr );
        Abc_ObjAddFanin( pNetDr, pTerm );
        Abc_ObjAddFanin( pTerm, pBox );
    }
    Vec_PtrFree( vPivots );

    // connect the remaining boxes
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
    {
        if ( Abc_NtkPiNum(pNtk) )
            continue;
        Abc_NtkForEachNet( pNtk, pNet, k )
        {
            if ( Abc_ObjFaninNum(pNet) )
                continue;
            // drive this net
            pTerm = Abc_NtkCreateBi( pNet->pNtk );
            assert( Abc_NtkBoxNum(pNet->pNtk) <= 1 );
            pBox = Abc_NtkBoxNum(pNet->pNtk)? Abc_NtkBox(pNet->pNtk,0) : Abc_NtkCreateBlackbox(pNet->pNtk);
            Abc_ObjAddFanin( pBox, pTerm );
            Abc_ObjAddFanin( pTerm, pNet );
            Abc_ObjAddFanin( pNet, Abc_NtkCreatePi(pNet->pNtk) );
        }
    }

    // connect the remaining boxes
    Vec_PtrForEachEntry( pMan->pDesign->vModules, pNtk, i )
    {
        Abc_NtkForEachBlackbox( pNtk, pBox, k )
        {
            char * pName = Abc_ObjName(pBox);
            if ( !Ver_ObjIsConnected(pBox) )
                if ( !Ver_ParseConnectBox( pMan, pBox ) )
                    return 0;
        }
    }
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
//    pNet  = Ver_ParseFindNet( pNtk, pName );
//    if ( pNet )
//        printf( "Warning: PI \"%s\" appears twice in the list.\n", pName );
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
//    pNet  = Ver_ParseFindNet( pNtk, pName );
//    if ( pNet && Abc_ObjFaninNum(pNet) == 0 )
//        printf( "Warning: PO \"%s\" appears twice in the list.\n", pName );
    pNet  = Abc_NtkFindOrCreateNet( pNtk, pName );
    // add the PO node
    pTerm = Abc_NtkCreatePo( pNtk );
    Abc_ObjAddFanin( pTerm, pNet );
    return pTerm;
}

/**Function*************************************************************

  Synopsis    [Create a latch with the given input/output.]

  Description [By default, the latch value is a don't-care.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Ver_ParseCreateLatch( Abc_Ntk_t * pNtk, Abc_Obj_t * pNetLI, Abc_Obj_t * pNetLO )
{
    Abc_Obj_t * pLatch, * pTerm;
    // add the BO terminal
    pTerm = Abc_NtkCreateBi( pNtk );
    Abc_ObjAddFanin( pTerm, pNetLI );
    // add the latch box
    pLatch = Abc_NtkCreateLatch( pNtk );
    Abc_ObjAddFanin( pLatch, pTerm  );
    // add the BI terminal
    pTerm = Abc_NtkCreateBo( pNtk );
    Abc_ObjAddFanin( pTerm, pLatch );
    // get the LO net
    Abc_ObjAddFanin( pNetLO, pTerm );
    // set latch name
    Abc_ObjAssignName( pLatch, Abc_ObjName(pNetLO), "L" );
    Abc_LatchSetInitDc( pLatch );
    return pLatch;
}

/**Function*************************************************************

  Synopsis    [Creates inverter and returns its net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Ver_ParseCreateInv( Abc_Ntk_t * pNtk, Abc_Obj_t * pNet )
{
    Abc_Obj_t * pObj;
    pObj = Abc_NtkCreateNodeInv( pNtk, pNet );
    pNet = Abc_NtkCreateObj( pNtk, ABC_OBJ_NET );
    Abc_ObjAddFanin( pNet, pObj );
    return pNet;
}



/*
    // allocate memory to remember the phase
    pPolarity = NULL;
    if ( fComplUsed )
    {
        int nBytes = 4 * Abc_BitWordNum( Abc_NtkPiNum(pNtkBox) );
        pPolarity = (unsigned *)Extra_MmFlexEntryFetch( pNtk->pData, nBytes );
        memset( pPolarity, 0, nBytes );
    }
    // create box to represent this gate
    if ( Abc_NtkHasBlackbox(pNtkBox) )
        pNode = Abc_NtkCreateBlackbox( pNtk );
    else
        pNode = Abc_NtkCreateWhitebox( pNtk );
    pNode->pNext = (Abc_Obj_t *)pPolarity;
    pNode->pData = pNtkBox;
    // connect to fanin nets
    Abc_NtkForEachPi( pNtkBox, pObj, i )
    {
        if ( pPolarity && Abc_ObjIsComplement(pObj->pCopy) )
        {
            Abc_InfoSetBit( pPolarity, i );
            pObj->pCopy = Abc_ObjRegular( pObj->pCopy );
        }
        assert( !Abc_ObjIsComplement(pObj->pCopy) );
//        Abc_ObjAddFanin( pNode, pObj->pCopy );
        pTerm = Abc_NtkCreateBi( pNtk );
        Abc_ObjAddFanin( pTerm, pObj->pCopy );
        Abc_ObjAddFanin( pNode, pTerm );
    }
    // connect to fanout nets
    Abc_NtkForEachPo( pNtkBox, pObj, i )
    {
        if ( pObj->pCopy == NULL )
            pObj->pCopy = Abc_NtkFindOrCreateNet(pNtk, NULL);
//        Abc_ObjAddFanin( pObj->pCopy, pNode );
        pTerm = Abc_NtkCreateBo( pNtk );
        Abc_ObjAddFanin( pTerm, pNode );
        Abc_ObjAddFanin( pObj->pCopy, pTerm );
    }
*/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


