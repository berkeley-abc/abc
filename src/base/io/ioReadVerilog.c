/**CFile****************************************************************

  FileName    [ioReadVerilog.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to read a subset of structural Verilog from IWLS 2005 benchmark.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioReadVerilog.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Io_ReadVer_t_        Io_ReadVer_t;   // all reading info
struct Io_ReadVer_t_
{
    // general info about file
    char *              pFileName;    // the name of the file
    Extra_FileReader_t* pReader;      // the input file reader
    // current processing info
    st_table *          tKeywords;    // mapping of keywords into codes
    Abc_Ntk_t *         pNtk;         // the primary network
    // the error message
    FILE *              Output;       // the output stream
    char                sError[1000]; // the error string generated during parsing
    int                 LineCur;      // the line currently being parsed
    Vec_Ptr_t *         vSkipped;     // temporary storage for skipped objects
};

// verilog keyword types
typedef enum { 
    VER_NONE      =  0,
    VER_MODULE    = -1,
    VER_ENDMODULE = -2,
    VER_INPUT     = -3,
    VER_OUTPUT    = -4,
    VER_INOUT     = -5,
    VER_WIRE      = -6,
    VER_ASSIGN    = -7
} Ver_KeywordType_t;

// the list of verilog keywords
static char * s_Keywords[10] = 
{
    NULL,            // unused
    "module",        // -1
    "endmodule",     // -2
    "input",         // -3
    "output",        // -4 
    "inout",         // -5
    "wire",          // -6
    "assign"         // -7
};

// the list of gates in the Cadence library
static char * s_CadenceGates[40][5] = 
{
    { "INVX1",     "1", "1",  "0 1\n",                   NULL }, // 0
    { "INVX2",     "1", "1",  "0 1\n",                   NULL }, // 1
    { "INVX4",     "1", "1",  "0 1\n",                   NULL }, // 2
    { "INVX8",     "1", "1",  "0 1\n",                   NULL }, // 3
    { "BUFX1",     "1", "1",  "1 1\n",                   NULL }, // 4
    { "BUFX3",     "1", "1",  "1 1\n",                   NULL }, // 5
    { "NOR2X1",    "2", "1",  "00 1\n",                  NULL }, // 6
    { "NOR3X1",    "3", "1",  "000 1\n",                 NULL }, // 7
    { "NOR4X1",    "4", "1",  "0000 1\n",                NULL }, // 8
    { "NAND2X1",   "2", "1",  "11 0\n",                  NULL }, // 9
    { "NAND2X2",   "2", "1",  "11 0\n",                  NULL }, // 10
    { "NAND3X1",   "3", "1",  "111 0\n",                 NULL }, // 11
    { "NAND4X1",   "4", "1",  "1111 0\n",                NULL }, // 12
    { "OR2X1",     "2", "1",  "00 0\n",                  NULL }, // 13
    { "OR4X1",     "4", "1",  "0000 0\n",                NULL }, // 14
    { "AND2X1",    "2", "1",  "11 1\n",                  NULL }, // 15
    { "XOR2X1",    "2", "1",  "01 1\n10 1\n",            NULL }, // 16
    { "MX2X1",     "3", "1",  "01- 1\n1-1 1\n",          NULL }, // 17
    { "OAI21X1",   "3", "1",  "00- 1\n--0 1\n",          NULL }, // 18
    { "OAI22X1",   "4", "1",  "00-- 1\n--00 1\n",        NULL }, // 19
    { "OAI33X1",   "6", "1",  "000--- 1\n---000 1\n",    NULL }, // 20
    { "AOI21X1",   "3", "1",  "11- 0\n--1 0\n",          NULL }, // 21
    { "AOI22X1",   "4", "1",  "11-- 0\n--11 0\n",        NULL }, // 22
    { "CLKBUFX1",  "1", "1",  "1 1\n",                   NULL }, // 23
    { "CLKBUFX2",  "1", "1",  "1 1\n",                   NULL }, // 24
    { "CLKBUFX3",  "1", "1",  "1 1\n",                   NULL }, // 25
    { "ADDHX1",    "2", "2",  "11 1\n",                  "01 1\n10 1\n"                 }, // 26
    { "ADDFX1",    "3", "2",  "11- 1\n-11 1\n1-1 1\n",   "001 1\n010 1\n100 1\n111 1\n" }, // 27
    { "DFFSRX1",   "1", "1",  NULL,                      NULL }, // 28
    { "DFFX1",     "1", "1",  NULL,                      NULL }, // 29
    { "SDFFSRX1",  "1", "1",  NULL,                      NULL }, // 30
    { "TLATSRX1",  "1", "1",  NULL,                      NULL }, // 31
    { "TLATX1",    "1", "1",  NULL,                      NULL }, // 32
    { "TBUFX1",    "1", "1",  NULL,                      NULL }, // 33
    { "TBUFX2",    "1", "1",  NULL,                      NULL }, // 34
    { "TBUFX4",    "1", "1",  NULL,                      NULL }, // 35
    { "TBUFX8",    "1", "1",  NULL,                      NULL }, // 36
    { "TINVX1",    "1", "1",  NULL,                      NULL }  // 37
};

static Io_ReadVer_t * Io_ReadVerFile( char * pFileName );
static Abc_Ntk_t *    Io_ReadVerNetwork( Io_ReadVer_t * p );
static bool           Io_ReadVerNetworkAssign( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens );
static bool           Io_ReadVerNetworkSignal( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens, int LineType );
static bool           Io_ReadVerNetworkGateSimple( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens, int LineType );
static bool           Io_ReadVerNetworkGateComplex( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens, int LineType );
static bool           Io_ReadVerNetworkLatch( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens );
static void           Io_ReadVerPrintErrorMessage( Io_ReadVer_t * p );
static void           Io_ReadVerFree( Io_ReadVer_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads the network from a Verilog file.]

  Description [Works only for IWLS 2005 benchmarks.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadVerilog( char * pFileName, int fCheck )
{
    Io_ReadVer_t * p;
    Abc_Ntk_t * pNtk;

    // start the file
    p = Io_ReadVerFile( pFileName );
    if ( p == NULL )
        return NULL;

    // read the network
    pNtk = Io_ReadVerNetwork( p );
    Io_ReadVerFree( p );
    if ( pNtk == NULL )
        return NULL;

    // make sure that everything is okay with the network structure
    if ( fCheck && !Abc_NtkCheckRead( pNtk ) )
    {
        printf( "Io_ReadVerilog: The network check has failed.\n" );
        Abc_NtkDelete( pNtk );
        return NULL;
    }
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Starts the reading data structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Io_ReadVer_t * Io_ReadVerFile( char * pFileName )
{
    Extra_FileReader_t * pReader;
    Io_ReadVer_t * p;
    int i;

    // start the reader
    pReader = Extra_FileReaderAlloc( pFileName, "/", ";", " \t\r\n,()" );
    if ( pReader == NULL )
        return NULL;

    // start the reading data structure
    p = ALLOC( Io_ReadVer_t, 1 );
    memset( p, 0, sizeof(Io_ReadVer_t) );
    p->pFileName = pFileName;
    p->pReader   = pReader;
    p->Output    = stdout;
    p->vSkipped  = Vec_PtrAlloc( 100 );

    // insert the keywords and gate names into the hash table
    p->tKeywords = st_init_table(strcmp, st_strhash);
    for ( i = 0; i < 10; i++ )
        if ( s_Keywords[i] )
            st_insert( p->tKeywords, (char *)s_Keywords[i], (char *)-i );
    for ( i = 0; i < 40; i++ )
        if ( s_CadenceGates[i][0] )
            st_insert( p->tKeywords, (char *)s_CadenceGates[i][0], (char *)i );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the data structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_ReadVerFree( Io_ReadVer_t * p )
{
    Extra_FileReaderFree( p->pReader );
    Vec_PtrFree( p->vSkipped );
    st_free_table( p->tKeywords );
    FREE( p );
}

/**Function*************************************************************

  Synopsis    [Prints the error message including the file name and line number.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_ReadVerPrintErrorMessage( Io_ReadVer_t * p )
{
    if ( p->LineCur == 0 ) // the line number is not given
        fprintf( p->Output, "%s: %s\n", p->pFileName, p->sError );
    else // print the error message with the line number
        fprintf( p->Output, "%s (line %d): %s\n", p->pFileName, p->LineCur, p->sError );
}

/**Function*************************************************************

  Synopsis    [Reads the verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadVerNetwork( Io_ReadVer_t * p )
{
    char Buffer[1000];
    ProgressBar * pProgress;
    Ver_KeywordType_t LineType;
    Vec_Ptr_t * vTokens;
    Abc_Ntk_t * pNtk;
    char * pModelName;
    int i;

    // read the model name
    vTokens = Extra_FileReaderGetTokens( p->pReader );
    if ( vTokens == NULL || strcmp( vTokens->pArray[0], "module" ) )
    {
        p->LineCur = 0;
        sprintf( p->sError, "Wrong input file format." );
        Io_ReadVerPrintErrorMessage( p );
        return NULL;
    }
    pModelName = vTokens->pArray[1];

    // allocate the empty network
    pNtk = Abc_NtkAlloc( ABC_TYPE_NETLIST, ABC_FUNC_SOP );
    pNtk->pName = util_strsav( pModelName );
    pNtk->pSpec = util_strsav( p->pFileName );

    // create constant nodes and nets
    Abc_NtkFindOrCreateNet( pNtk, "1'b0" );
    Abc_NtkFindOrCreateNet( pNtk, "1'b1" );
    Io_ReadCreateConst( pNtk, "1'b0", 0 );
    Io_ReadCreateConst( pNtk, "1'b1", 1 );

    // read the inputs/outputs
    pProgress = Extra_ProgressBarStart( stdout, Extra_FileReaderGetFileSize(p->pReader) );
    for ( i = 0; vTokens = Extra_FileReaderGetTokens(p->pReader); i++ )
    {
        Extra_ProgressBarUpdate( pProgress, Extra_FileReaderGetCurPosition(p->pReader), NULL );

        // get the line type
        if ( !st_lookup( p->tKeywords, vTokens->pArray[0], (char **)&LineType ) )
        {
            p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
            sprintf( p->sError, "The first token \"%s\" cannot be recognized.", vTokens->pArray[0] );
            Io_ReadVerPrintErrorMessage( p );
            return NULL;
        }
        // consider Verilog directives
        if ( LineType < 0 )
        {
            if ( LineType == VER_ENDMODULE )
                break;
            if ( LineType == VER_ASSIGN )
            {
                if ( !Io_ReadVerNetworkAssign( p, pNtk, vTokens ) )
                    return NULL;
                continue;
            }
            if ( !Io_ReadVerNetworkSignal( p, pNtk, vTokens, LineType ) )
                return NULL;
            continue;
        }
        // proces single output gates
        if ( LineType < 26 )
        {
            if ( !Io_ReadVerNetworkGateSimple( p, pNtk, vTokens, LineType ) )
                return NULL;
            continue;
        }
        // process complex gates
        if ( LineType < 28 )
        {
            if ( !Io_ReadVerNetworkGateComplex( p, pNtk, vTokens, LineType ) )
                return NULL;
            continue;

        }
        // process the latches
        if ( LineType < 33 )
        {
            if ( !Io_ReadVerNetworkLatch( p, pNtk, vTokens ) )
                return NULL;
            continue;
        }
        // add the tri-state element to the skipped ones
        sprintf( Buffer, "%s %s", vTokens->pArray[0], vTokens->pArray[1] );
        Vec_PtrPush( p->vSkipped, util_strsav(Buffer) );
    }
    Extra_ProgressBarStop( pProgress );

    if ( p->vSkipped->nSize > 0 )
    {
        printf( "IoReadVerilog() skipped %d tri-state elements:\n", p->vSkipped->nSize );
        for ( i = 0; i < p->vSkipped->nSize; i++ )
        {
            if ( i < 2 )
                printf( "%s,\n", p->vSkipped->pArray[i] );
            else 
            {
                printf( "%s, etc.\n", p->vSkipped->pArray[i] );
                break;
            }
        }
        for ( i = 0; i < p->vSkipped->nSize; i++ )
            free( p->vSkipped->pArray[i] );
    }
    Abc_NtkFinalizeRead( pNtk );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Reads one assign directive in the verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Io_ReadVerNetworkAssign( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens )
{
    assert( strcmp( vTokens->pArray[0], "assign" ) == 0 );
    // make sure the driving variable exists
    if ( !Abc_NtkFindNet( pNtk, vTokens->pArray[3] ) )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "Cannot find net \"%s\". The assign operator is handled only for assignment to a variable and a constant.", vTokens->pArray[3] );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    // make sure the driven variable exists
    if ( !Abc_NtkFindNet( pNtk, vTokens->pArray[1] ) )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "Cannot find net \"%s\".", vTokens->pArray[1] );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    // create a buffer
    Io_ReadCreateBuf( pNtk, vTokens->pArray[3], vTokens->pArray[1] );  
    return 1;
}

/**Function*************************************************************

  Synopsis    [Reads one signal the verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Io_ReadVerNetworkSignal( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens, int LineType )
{
    Abc_Obj_t * pNet;
    char Buffer[1000];
    char * pToken;
    int nSignals, k, Start, s;
    
    nSignals = 0;
    pToken = vTokens->pArray[1];
    if ( pToken[0] == '[' )
    {
        nSignals = atoi(pToken + 1) + 1;
        if ( nSignals < 1 || nSignals > 1024 )
        {
            p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
            sprintf( p->sError, "Incorrect number of signals in the expression \"%s\".", pToken );
            Io_ReadVerPrintErrorMessage( p );
            return 0;
        }
        if ( nSignals == 1 )
            nSignals = 0;
        Start = 2;
    }
    else
        Start = 1;
    for ( k = Start; k < vTokens->nSize; k++ ) 
    {
        pToken = vTokens->pArray[k];
        // print the signal name
        if ( nSignals )
        {
            for ( s = 0; s < nSignals; s++ )
            {
                sprintf( Buffer, "%s[%d]", pToken, s );
                if ( LineType == VER_INPUT || LineType == VER_INOUT )
                    Io_ReadCreatePi( pNtk, Buffer );
                if ( LineType == VER_OUTPUT || LineType == VER_INOUT )
                    Io_ReadCreatePo( pNtk, Buffer );
                if ( LineType != VER_INPUT && LineType != VER_OUTPUT && LineType != VER_INOUT )
                    pNet = Abc_NtkFindOrCreateNet( pNtk, Buffer );
            }
        }
        else
        {
            if ( LineType == VER_INPUT || LineType == VER_INOUT )
                Io_ReadCreatePi( pNtk, pToken );
            if ( LineType == VER_OUTPUT || LineType == VER_INOUT )
                Io_ReadCreatePo( pNtk, pToken );
            if ( LineType != VER_INPUT && LineType != VER_OUTPUT && LineType != VER_INOUT )
                pNet = Abc_NtkFindOrCreateNet( pNtk, pToken );
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Reads a simple gate from the verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Io_ReadVerNetworkGateSimple( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens, int LineType )
{
    Abc_Obj_t * pNet, * pNode;
    char * pToken;
    int nFanins, k;

    // create the node
    pNode = Abc_NtkCreateNode( pNtk );
    // add the fanin nets
    nFanins = s_CadenceGates[LineType][1][0] - '0';
    // skip the gate type and gate name
    for ( k = 2; k < vTokens->nSize - 1; k++ )
    {
        pToken = vTokens->pArray[k];
        if ( pToken[0] == '.' )
            continue;
        pNet = Abc_NtkFindNet( pNtk, pToken );
        if ( pNet )
        {
            Abc_ObjAddFanin( pNode, pNet );
            continue;
        }
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "Cannot find net \"%s\".", pToken );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    if ( Abc_ObjFaninNum(pNode) != nFanins )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "Gate \"%s\" has a wrong number of inputs.", vTokens->pArray[1] );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }

    // add the fanout net
    pToken = vTokens->pArray[vTokens->nSize - 1];
    if ( pToken[0] == '.' )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "Gate \"%s\" does not have a fanout.", vTokens->pArray[1] );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    pNet = Abc_NtkFindNet( pNtk, pToken );
    if ( pNet == NULL )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "Cannot find net \"%s\".", pToken );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    Abc_ObjAddFanin( pNet, pNode );
    // set the function
    Abc_ObjSetData( pNode, Abc_SopRegister(pNtk->pManFunc, s_CadenceGates[LineType][3]) );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Reads a complex gate from the verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Io_ReadVerNetworkGateComplex( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens, int LineType )
{
    Abc_Obj_t * pNode1, * pNode2, * pNet;
    char * pToken, * pToken1, * pToken2;
    int nFanins, k;

    // create the nodes
    pNode1 = Abc_NtkCreateNode( pNtk );     
    pNode2 = Abc_NtkCreateNode( pNtk );     
    // skip the gate type and gate name
    // add the fanin nets
    nFanins = s_CadenceGates[LineType][1][0] - '0';
    for ( k = 2; k < vTokens->nSize; k++ )
    {
        pToken = vTokens->pArray[k];
        if ( pToken[0] == '.' )
            continue;
        pNet = Abc_NtkFindNet( pNtk, pToken );
        if ( pNet == NULL )
        {
            p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
            sprintf( p->sError, "Cannot find net \"%s\".", pToken );
            Io_ReadVerPrintErrorMessage( p );
            return 0;
        }
        Abc_ObjAddFanin( pNode1, pNet );
        Abc_ObjAddFanin( pNode2, pNet );
        if ( Abc_ObjFaninNum(pNode1) == nFanins )
        {
            k++;
            break;
        }
    }
    // find the tokens corresponding to the output
    pToken1 = pToken2 = NULL;
    for (  ; k < vTokens->nSize; k++ )
    {
        pToken = vTokens->pArray[k];
        if ( pToken[0] == '.' )
            continue;
        if ( pToken1 == NULL )
            pToken1 = pToken;
        else 
            pToken2 = pToken;
    }
    // quit if one of the tokens is not given
    if ( pToken1 == NULL || pToken2 == NULL )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "An output of a two-output gate \"%s\" is not specified.", vTokens->pArray[1] );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }

    // add the fanout net
    pNet = Abc_NtkFindNet( pNtk, pToken1 );
    if ( pNet == NULL )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "Cannot find net \"%s\".", pToken1 );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    Abc_ObjAddFanin( pNet, pNode1 );

    // add the fanout net
    pNet = Abc_NtkFindNet( pNtk, pToken2 );
    if ( pNet == NULL )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "Cannot find net \"%s\".", pToken2 );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    Abc_ObjAddFanin( pNet, pNode2 );
    Abc_ObjSetData( pNode1, Abc_SopRegister(pNtk->pManFunc, s_CadenceGates[LineType][3]) );
    Abc_ObjSetData( pNode2, Abc_SopRegister(pNtk->pManFunc, s_CadenceGates[LineType][4]) );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Reads a latch from the verilog file.]

  Description [This procedure treats T-latch as if it were D-latch.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Io_ReadVerNetworkLatch( Io_ReadVer_t * p, Abc_Ntk_t * pNtk, Vec_Ptr_t * vTokens )
{
    Abc_Obj_t * pLatch, * pNet;
    char * pLatchName;
    char * pToken, * pToken2, * pTokenRN, * pTokenSN, * pTokenSI, * pTokenSE, * pTokenD, * pTokenQ, * pTokenQN;
    int k, fRN1, fSN1;

    // get the latch name
    pLatchName = vTokens->pArray[1];

    // collect the FF signals
    pTokenRN = pTokenSN = pTokenSI = pTokenSE = pTokenD = pTokenQ = pTokenQN = NULL;
    for ( k = 2; k < vTokens->nSize-1; k++ )
    {
        pToken  = vTokens->pArray[k];
        pToken2 = vTokens->pArray[k+1];
        if ( pToken[1] == 'R' && pToken[2] == 'N' && pToken[3] == 0 )
            pTokenRN = (pToken2[0] == '.')? NULL : pToken2;
        else if ( pToken[1] == 'S' && pToken[2] == 'N' && pToken[3] == 0 )
            pTokenSN = (pToken2[0] == '.')? NULL : pToken2;
        else if ( pToken[1] == 'S' && pToken[2] == 'I' && pToken[3] == 0 )
            pTokenSI = (pToken2[0] == '.')? NULL : pToken2;
        else if ( pToken[1] == 'S' && pToken[2] == 'E' && pToken[3] == 0 )
            pTokenSE = (pToken2[0] == '.')? NULL : pToken2;
        else if ( pToken[1] == 'D' && pToken[2] == 0 )
            pTokenD  = (pToken2[0] == '.')? NULL : pToken2;
        else if ( pToken[1] == 'Q' && pToken[2] == 0 )
            pTokenQ  = (pToken2[0] == '.')? NULL : pToken2;
        else if ( pToken[1] == 'Q' && pToken[2] == 'N' && pToken[3] == 0 )
            pTokenQN = (pToken2[0] == '.')? NULL : pToken2;
        else if ( pToken[1] == 'C' && pToken[2] == 'K' && pToken[3] == 0 ) {}
        else
            assert( 0 );
        if ( pToken2[0] != '.' )
            k++;
    }

    if ( pTokenD == NULL )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 1 );
        sprintf( p->sError, "Cannot read pin D of the latch \"%s\".", pLatchName );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    if ( pTokenQ == NULL && pTokenQN == NULL )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 1 );
        sprintf( p->sError, "Cannot read pins Q/QN of the latch \"%s\".", pLatchName );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    if ( (pTokenRN == NULL) ^ (pTokenSN == NULL) )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 1 );
        sprintf( p->sError, "Cannot read pins RN/SN of the latch \"%s\".", pLatchName );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }
    if ( Abc_NtkFindNet( pNtk, pTokenD ) == NULL )
    {
        p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
        sprintf( p->sError, "Cannot find latch input net \"%s\".", pTokenD );
        Io_ReadVerPrintErrorMessage( p );
        return 0;
    }

    // create the latch
    pLatch = Io_ReadCreateLatch( pNtk, pTokenD, pLatchName );

    // create the buffer if Q signal is available
    if ( pTokenQ )
    {
        pNet = Abc_NtkFindNet( pNtk, pTokenQ );
        if ( pNet == NULL )
        {
            p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
            sprintf( p->sError, "Cannot find latch output net \"%s\".", pTokenQ );
            Io_ReadVerPrintErrorMessage( p );
            return 0;
        }
        Io_ReadCreateBuf( pNtk, pLatchName, pTokenQ );
    }
    if ( pTokenQN )
    {
        pNet = Abc_NtkFindNet( pNtk, pTokenQN );
        if ( pNet == NULL )
        {
            p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
            sprintf( p->sError, "Cannot find latch output net \"%s\".", pTokenQN );
            Io_ReadVerPrintErrorMessage( p );
            return 0;
        }
        Io_ReadCreateInv( pNtk, pLatchName, pTokenQN );
    }

    // set the initial value
    if ( pTokenRN == NULL && pTokenSN == NULL )
        Abc_LatchSetInitDc( pLatch );
    else 
    {
        fRN1 = (strcmp( pTokenRN, "1'b1" ) == 0);
        fSN1 = (strcmp( pTokenSN, "1'b1" ) == 0);
        if ( fRN1 && fSN1 )
            Abc_LatchSetInitDc( pLatch );
        else if ( fRN1 )
            Abc_LatchSetInit1( pLatch );
        else if ( fSN1 )
            Abc_LatchSetInit0( pLatch );
        else
        {
            p->LineCur = Extra_FileReaderGetLineNumber( p->pReader, 0 );
            sprintf( p->sError, "Cannot read the initial value of latch \"%s\".", pLatchName );
            Io_ReadVerPrintErrorMessage( p );
            return 0;
        }
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



