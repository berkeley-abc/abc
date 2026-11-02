/**CFile****************************************************************

  FileName    [abcIo.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ABC command integration.]

  Synopsis    [Design I/O and saved networks.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 27, 2026.]

***********************************************************************/

#include "abcc.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "base/sn/snRead.h"
#include "base/sn/snGia.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandSendAig                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSendStatus             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBackup                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRestore                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbcSave                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbcLoad                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Get                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Put                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9MoveNames          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Save               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Save2              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SaveAig            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Load               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Load2              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9LoadAig            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Read               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReadBlif           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReadCBlif          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReadStg            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReadVer            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9WriteVer           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Write              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9WriteLut           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9LNetRead           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Undo               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9CatBtor            ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
extern Vec_Ptr_t * Abc_NtkCollectCiNames( Abc_Ntk_t * pNtk );
extern Vec_Ptr_t * Abc_NtkCollectCoNames( Abc_Ntk_t * pNtk );

/**Function*************************************************************

  Synopsis    [Registers design i/o and saved networks commands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_InitIo( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Various",      "send_aig",      Abc_CommandSendAig,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "send_status",   Abc_CommandSendStatus,       0 );
    Cmd_CommandAdd( pAbc, "Various",      "backup",        Abc_CommandBackup,           0 );
    Cmd_CommandAdd( pAbc, "Various",      "restore",       Abc_CommandRestore,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "save",          Abc_CommandAbcSave,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "load",          Abc_CommandAbcLoad,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&get",          Abc_CommandAbc9Get,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&put",          Abc_CommandAbc9Put,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&move_names",   Abc_CommandAbc9MoveNames,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&save",         Abc_CommandAbc9Save,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&save2",        Abc_CommandAbc9Save2,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&saveaig",      Abc_CommandAbc9SaveAig,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&load",         Abc_CommandAbc9Load,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&load2",        Abc_CommandAbc9Load2,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&loadaig",      Abc_CommandAbc9LoadAig,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&r",            Abc_CommandAbc9Read,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&read",         Abc_CommandAbc9Read,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&read_blif",    Abc_CommandAbc9ReadBlif,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&read_cblif",   Abc_CommandAbc9ReadCBlif,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&read_stg",     Abc_CommandAbc9ReadStg,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&read_ver",     Abc_CommandAbc9ReadVer,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&write_ver",    Abc_CommandAbc9WriteVer,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&w",            Abc_CommandAbc9Write,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&write",        Abc_CommandAbc9Write,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&wlut",         Abc_CommandAbc9WriteLut,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&lnetread",     Abc_CommandAbc9LNetRead,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&undo",         Abc_CommandAbc9Undo,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&catbtor",      Abc_CommandAbc9CatBtor,                0 );
}

////////////////////////////////////////////////////////////////////////
///                       FUNCTION DEFINITIONS                       ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSendAig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    const int BRIDGE_NETLIST = 106;
//    const int BRIDGE_ABS_NETLIST = 107;

    int c, fAndSpace = 1, fAbsNetlist = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAndSpace ^= 1;
            break;
        case 'b':
            fAbsNetlist ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_FrameIsBridgeMode() )
    {
        Abc_Print( -1, "The bridge mode is not available.\n" );
        return 1;
    }
    if ( fAndSpace )
    {
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "There is no AIG in the &-space.\n" );
            return 1;
        }
        Gia_ManToBridgeAbsNetlist( stdout, pAbc->pGia, fAbsNetlist ? BRIDGE_ABS_NETLIST : BRIDGE_NETLIST );
    }
    else
    {
        Aig_Man_t * pAig;
        Gia_Man_t * pGia;
        if ( pAbc->pNtkCur == NULL )
        {
            Abc_Print( -1, "There is no network in the main-space.\n" );
            return 1;
        }
        if ( !Abc_NtkIsStrash(pAbc->pNtkCur) )
        {
            Abc_Print( -1, "The main-space network is not an AIG.\n" );
            return 1;
        }
        pAig = Abc_NtkToDar( pAbc->pNtkCur, 0, 1 );
        pGia = Gia_ManFromAig( pAig );
        Aig_ManStop( pAig );
        Gia_ManToBridgeAbsNetlist( stdout, pGia, fAbsNetlist ? BRIDGE_ABS_NETLIST : BRIDGE_NETLIST  );
        Gia_ManStop( pGia );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: send_aig -a\n" );
    Abc_Print( -2, "\t         sends current AIG to the bridge\n" );
    Abc_Print( -2, "\t-a     : toggle sending AIG from &-space [default = %s]\n", fAndSpace? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle sending netlist tagged as \"abstraction\". [default = %s]\n", fAbsNetlist? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSendStatus( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_ManToBridgeResult( FILE * pFile, int Result, Abc_Cex_t * pCex, int iPoProved );
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_FrameIsBridgeMode() )
    {
        Abc_Print( -1, "The bridge mode is not available.\n" );
        return 1;
    }
    if ( pAbc->Status == 0 && pAbc->pCex == NULL )
    {
        Abc_Print( -1, "Status is \"sat\", but current CEX is not available.\n" );
        return 1;
    }
    Gia_ManToBridgeResult( stdout, pAbc->Status, pAbc->pCex, 0 );
    return 0;

usage:
    Abc_Print( -2, "usage: send_status\n" );
    Abc_Print( -2, "\t         sends current status to the bridge\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBackup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( pAbc->pNtkBackup )
        Abc_NtkDelete( pAbc->pNtkBackup );
    pAbc->pNtkBackup = Abc_NtkDup( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: backup [-h]\n" );
    Abc_Print( -2, "\t        backs up the current network\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Restores the network backup.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRestore( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pAbc->pNtkBackup == NULL )
    {
        Abc_Print( -1, "There is no backup network.\n" );
        return 1;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, Abc_NtkDup(pAbc->pNtkBackup) );
    pAbc->nFrames = -1;
    pAbc->Status = -1;
    return 0;

usage:
    Abc_Print( -2, "usage: restore [-h]\n" );
    Abc_Print( -2, "\t        restores the current network\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compares to versions of the design and finds the best.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_NtkCompareWithBest( Abc_Ntk_t * pBest, Abc_Ntk_t * p, 
    float * pnBestNtkArea,  float * pnBestNtkDelay, 
    int *   pnBestNtkNodes, int *   pnBestNtkLevels, int fArea )
{ 
    float nNtkArea   = (float)Abc_NtkGetMappedArea(p);
    float nNtkDelay  = (float)Abc_NtkDelayTrace(p, NULL, NULL, 0);
    int   nNtkNodes  = Abc_NtkNodeNum(p);
    int   nNtkLevels = Abc_NtkLevel(p);

    if ( pBest == NULL ||
         Abc_NtkPiNum(pBest)    != Abc_NtkPiNum(p)    ||
         Abc_NtkPoNum(pBest)    != Abc_NtkPoNum(p)    ||
         Abc_NtkLatchNum(pBest) != Abc_NtkLatchNum(p) ||
         strcmp(Abc_NtkName(pBest), Abc_NtkName(p))   ||
//         (!fArea && (*pnBestNtkLevels > nNtkLevels || (*pnBestNtkLevels == nNtkLevels && *pnBestNtkDelay > nNtkDelay ))) ||
//         ( fArea && (*pnBestNtkNodes  > nNtkNodes  || (*pnBestNtkNodes  == nNtkNodes  && *pnBestNtkArea  > nNtkArea  )))
         (!fArea && (*pnBestNtkDelay > nNtkDelay || (*pnBestNtkDelay == nNtkDelay && *pnBestNtkArea  > nNtkArea  ))) ||
         ( fArea && (*pnBestNtkArea  > nNtkArea  || (*pnBestNtkArea  == nNtkArea  && *pnBestNtkDelay > nNtkDelay )))
       )
    {
        *pnBestNtkArea   = nNtkArea;
        *pnBestNtkDelay  = nNtkDelay; 
        *pnBestNtkNodes  = nNtkNodes;
        *pnBestNtkLevels = nNtkLevels;
        printf( "\nUpdating the best network (Area = %10.2f  Delay = %10.2f  Nodes = %6d  Level = %6d).\n\n", 
            nNtkArea, nNtkDelay, nNtkNodes, nNtkLevels );
        return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbcSave( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fArea = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fArea ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pNtkCur == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkHasMapping(pAbc->pNtkCur) )
    {
        Abc_Print( -1, "Network has no mapping.\n" );
        return 1;
    }
    if ( !Abc_NtkCompareWithBest( pAbc->pNtkBest, pAbc->pNtkCur, 
             &pAbc->nBestNtkArea,  &pAbc->nBestNtkDelay, 
             &pAbc->nBestNtkNodes, &pAbc->nBestNtkLevels, fArea ) )
        return 0;
    // save the design as best
    if ( pAbc->pNtkBest ) Abc_NtkDelete( pAbc->pNtkBest );
    pAbc->pNtkBest = Abc_NtkDup(pAbc->pNtkCur);
    return 0;

usage:
    Abc_Print( -2, "usage: save [-ah]\n" );
    Abc_Print( -2, "\t        compares and possibly saves network with mapping\n" );
    Abc_Print( -2, "\t-a    : toggle using area as the primary metric [default = %s]\n", fArea? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbcLoad( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    // restore from best
    if ( pAbc->pNtkBest == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbcLoad(): There is no best design saved.\n" );
        return 1;
    }
    if ( pAbc->pNtkCur ) Abc_NtkDelete( pAbc->pNtkCur );
    pAbc->pNtkCur = Abc_NtkDup(pAbc->pNtkBest);
    return 0;

usage:
    Abc_Print( -2, "usage: load [-h]\n" );
    Abc_Print( -2, "\t        loads mapped network previously saved by \"save\"\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Read( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc3_ReadShowHie( char * pFileName, int fFlat );
    extern Gia_Man_t * Gia_MiniAigSuperDerive( char * pFileName, int fVerbose );
    extern Gia_Man_t * Gia_FileSimpleRead( char * pFileName, int fNames, char * pFileW );
    extern Gia_Man_t * Gia_ManCreateXors( Gia_Man_t * p );
    Gia_Man_t * pAig = NULL;
    FILE * pFile;
    char ** pArgvNew;
    char * FileName, * pTemp;
    int c, nArgcNew;
    int fMiniAig = 0;
    int fMiniAig2 = 0;
    int fMiniLut = 0;
    int fVerbose = 0;
    int fGiaSimple = 0;
    int fSkipStrash = 0;
    int fNewReader = 0;
    int fDetectXors = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "csxmnlpvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fGiaSimple ^= 1;
            break;
        case 's':
            fSkipStrash ^= 1;
            break;
        case 'x':
            fDetectXors ^= 1;
            break;
        case 'm':
            fMiniAig ^= 1;
            break;
        case 'n':
            fMiniAig2 ^= 1;
            break;
        case 'l':
            fMiniLut ^= 1;
            break;
        case 'p':
            fNewReader ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }

    // get the input file name
    FileName = pArgvNew[0];
    // fix the wrong symbol
    for ( pTemp = FileName; *pTemp; pTemp++ )
        if ( *pTemp == '>' )
            *pTemp = '\\';
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".aig", ".blif", ".pla", ".eqn", ".bench" )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    if ( fNewReader )
        pAig = Gia_FileSimpleRead( FileName, fGiaSimple, NULL );
    else if ( fMiniAig )
        pAig = Gia_ManReadMiniAig( FileName, fGiaSimple || fSkipStrash );
    else if ( fMiniAig2 )
        pAig = Gia_MiniAigSuperDerive( FileName, fVerbose );
    else if ( fMiniLut )
        pAig = Gia_ManReadMiniLut( FileName );
//    else if ( Extra_FileIsType( FileName, ".v", NULL, NULL ) )
//        Abc3_ReadShowHie( FileName, fSkipStrash );
    else
    {
        pAig = Gia_AigerRead( FileName, fGiaSimple, fSkipStrash, 0 );
        if ( fDetectXors )
        {
            Gia_Man_t * pTemp;
            pAig = Gia_ManCreateXors( pTemp = pAig );
            Gia_ManStop( pTemp );
        }
    }
    if ( pAig )
        Abc_FrameUpdateGia( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &r [-csxmnlvh] <file>\n" );
    Abc_Print( -2, "\t         reads the current AIG from the AIGER file\n" );
    Abc_Print( -2, "\t-c     : toggles reading simple AIG [default = %s]\n", fGiaSimple? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggles structural hashing while reading [default = %s]\n", !fSkipStrash? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggles detecting XORs while reading [default = %s]\n", fDetectXors? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggles reading MiniAIG rather than AIGER file [default = %s]\n", fMiniAig? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggles reading MiniAIG as a set of supergates [default = %s]\n", fMiniAig2? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggles reading MiniLUT rather than AIGER file [default = %s]\n", fMiniLut? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReadBlif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Abc_NtkHieCecTest( char * pFileName, int fVerbose );
    Gia_Man_t * pAig;
    FILE * pFile;
    char ** pArgvNew;
    char * FileName, * pTemp;
    int nArgcNew;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }

    // get the input file name
    FileName = pArgvNew[0];
    // fix the wrong symbol
    for ( pTemp = FileName; *pTemp; pTemp++ )
        if ( *pTemp == '>' )
            *pTemp = '\\';
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".blif", NULL, NULL, NULL, NULL )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    pAig = Abc_NtkHieCecTest( FileName, fVerbose );
    Abc_FrameUpdateGia( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &read_blif [-vh] <file>\n" );
    Abc_Print( -2, "\t         a specialized reader for hierarchical BLIF files\n" );
    Abc_Print( -2, "\t         (for general-purpose BLIFs, please use \"read_blif\")\n" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReadCBlif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Abc_NtkHieCecTest2( char * pFileName, char * pModelName, int fVerbose );
    Gia_Man_t * pAig;
    FILE * pFile;
    char ** pArgvNew;
    char * FileName, * pTemp;
    char * pModelName = NULL;
    int nArgcNew;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Mvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a file name.\n" );
                goto usage;
            }
            pModelName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }

    // get the input file name
    FileName = pArgvNew[0];
    // fix the wrong symbol
    for ( pTemp = FileName; *pTemp; pTemp++ )
        if ( *pTemp == '>' )
            *pTemp = '\\';
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".cblif", NULL, NULL, NULL, NULL )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    pAig = Abc_NtkHieCecTest2( FileName, pModelName, fVerbose );
    Abc_FrameUpdateGia( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &read_cblif [-M name] [-vh] <file>\n" );
    Abc_Print( -2, "\t         reads CBLIF file and collapse it into an AIG\n" );
    Abc_Print( -2, "\t-M name: module name to collapse [default = <root_module>]\n" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReadStg( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pAig;
    FILE * pFile;
    char * FileName, ** pArgvNew;
    int c, nArgcNew;
    int kHot = 1;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            kHot = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( kHot < 1 || kHot > 5 )
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }

    // get the input file name
    FileName = pArgvNew[0];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        return 1;
    }
    fclose( pFile );

    pAig = Gia_ManStgRead( FileName, kHot, fVerbose );
    Abc_FrameUpdateGia( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &read_stg [-K <num>] [-vh] <file>\n" );
    Abc_Print( -2, "\t         reads STG file and generates K-hot-encoded AIG\n" );
    Abc_Print( -2, "\t-K num : the K parameter for hotness of the encoding (1 <= K <= 5) [default = %d]\n", kHot );
    Abc_Print( -2, "\t-v     : toggles printing state codes [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReadVer( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    Gia_Man_t * pAig;
    FILE * pFile;
    char ** pArgvNew;
    char * pFileName, * pTemp;
    int nArgcNew;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }

    // get the input file name
    pFileName = pArgvNew[0];
    // fix the wrong symbol
    for ( pTemp = pFileName; *pTemp; pTemp++ )
        if ( *pTemp == '>' )
            *pTemp = '\\';
    if ( (pFile = fopen( pFileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", pFileName );
        if ( (pFileName = Extra_FileGetSimilarName( pFileName, ".v", ".blif", NULL, NULL, NULL )) )
            Abc_Print( 1, "Did you mean \"%s\"?", pFileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );
    // read hierarchical Verilog
    pNtk = Io_ReadNetlist( pFileName, Io_ReadFileType(pFileName), 0 );
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Reading hierarchical Verilog has failed.\n" );
        return 1;
    }
    pAig = Abc_NtkFlattenHierarchyGia( pNtk, NULL, fVerbose );
    Abc_NtkDelete( pNtk );
    Abc_FrameUpdateGia( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &read_ver [-vh] <file>\n" );
    Abc_Print( -2, "\t         a specialized reader for hierarchical Verilog files\n" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Get( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Aig_Man_t * Abc_NtkToDarChoices( Abc_Ntk_t * pNtk );
    Abc_Ntk_t * pStrash;
    Aig_Man_t * pAig;
    Gia_Man_t * pGia, * pTemp;
    char * pInits;
    int c, fGiaSimple = 0, fMapped = 0, fNames = 0, fReuseNames = 0, fSibls = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cmnrvsh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fGiaSimple ^= 1;
            break;
        case 'm':
            fMapped ^= 1;
            break;
        case 'n':
            fNames ^= 1;
            break;
        case 'r':
            fReuseNames ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 's':
            fSibls ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pNtkCur == NULL )
    {
        Abc_Print( -1, "There is no current network\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash( pAbc->pNtkCur ) )
    {
        if ( fGiaSimple || fMapped )
        {
            assert( Abc_NtkIsLogic(pAbc->pNtkCur) );
            Abc_NtkToAig( pAbc->pNtkCur );
            pGia = Abc_NtkAigToGia( pAbc->pNtkCur, fGiaSimple );
        }
        else
        {
            // derive comb GIA
            pStrash = Abc_NtkStrash( pAbc->pNtkCur, 0, 1, 0 );
            pAig = Abc_NtkToDar( pStrash, 0, 0 );
            Abc_NtkDelete( pStrash );
            pGia = Gia_ManFromAig( pAig );
            Aig_ManStop( pAig );
        }
    }
    else
    {
        if ( Abc_NtkGetChoiceNum(pAbc->pNtkCur) )
        {
            pAig = Abc_NtkToDarChoices( pAbc->pNtkCur );
            pGia = fSibls ? Gia_ManFromAigChoices( pAig ) : Gia_ManFromAig( pAig );
        }
        else
        {
            pAig = Abc_NtkToDar( pAbc->pNtkCur, 0, 1 );
            pGia = Gia_ManFromAig( pAig );
        }
        Aig_ManStop( pAig );
    }
    // copy names
    if ( fNames )
    {
        pGia->vNamesIn  = Abc_NtkCollectCiNames( pAbc->pNtkCur );
        pGia->vNamesOut = Abc_NtkCollectCoNames( pAbc->pNtkCur );
        // Abc_NtkToDar() has complemented the 1-valued flops of a strashed network
        if ( Abc_NtkIsStrash(pAbc->pNtkCur) )
            Gia_ManRenameFlopOutputs( pGia );
    }
    // Normalize initialization after copying names so new terminals are named, too.
    if ( !Abc_NtkIsStrash(pAbc->pNtkCur) && !fGiaSimple && !fMapped )
    {
        pInits = Abc_NtkCollectLatchValuesStr( pAbc->pNtkCur );
        pGia = Gia_ManDupZeroUndc( pTemp = pGia, pInits, 0, 0, fVerbose );
        Gia_ManStop( pTemp );
        ABC_FREE( pInits );
    }
    // copy user timing information
    if ( pAbc->pNtkCur->pManTime != NULL )
    {
        Abc_Ntk_t * pNtk = pAbc->pNtkCur;
        Vec_FltFreeP( &pGia->vInArrs );
        Vec_FltFreeP( &pGia->vOutReqs );
        pGia->DefInArrs  = Abc_NtkReadDefaultArrivalWorst(pNtk);
        pGia->DefOutReqs = Abc_NtkReadDefaultRequiredWorst(pNtk);
        pGia->vInArrs  = Vec_FltAllocArray( Abc_NtkGetCiArrivalFloats(pNtk), Abc_NtkCiNum(pNtk) );
        pGia->vOutReqs = Vec_FltAllocArray( Abc_NtkGetCoRequiredFloats(pNtk), Abc_NtkCoNum(pNtk) );
        pGia->And2Delay = pNtk->AndGateDelay;
    }
    if ( fReuseNames ) 
    {
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "There is no current AIG to reuse names from.\n" );
            return 1;
        }
        if ( Gia_ManCiNum(pGia) != Gia_ManCiNum(pAbc->pGia) )
        {
            Abc_Print( -1, "The number of CIs differ.\n" );
            return 1;
        }
        if ( Gia_ManCoNum(pGia) != Gia_ManCoNum(pAbc->pGia) )
        {
            Abc_Print( -1, "The number of COs differ.\n" );
            return 1;
        }
        ABC_SWAP( Vec_Ptr_t *, pGia->vNamesIn,  pAbc->pGia->vNamesIn  );
        ABC_SWAP( Vec_Ptr_t *, pGia->vNamesOut, pAbc->pGia->vNamesOut );
    }
    Abc_FrameUpdateGia( pAbc, pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &get [-cmnrvsh] <file>\n" );
    Abc_Print( -2, "\t         converts the current network into GIA and moves it to the &-space\n" );
    Abc_Print( -2, "\t         (if the network is a sequential logic network, normalizes the flops\n" );
    Abc_Print( -2, "\t         to have const-0 initial values, equivalent to \"undc; st; zero\")\n" );
    Abc_Print( -2, "\t-c     : toggles allowing simple GIA to be imported [default = %s]\n", fGiaSimple? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggles preserving the current mapping [default = %s]\n", fMapped? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggles saving CI/CO names of the AIG [default = %s]\n", fNames? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggles reusing CI/CO names of the current AIG [default = %s]\n", fReuseNames? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggles exporting choice nodes as GIA siblings (pSibls) for &if-based mapping [default = %s]\n", fSibls? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Put( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkFromDarChoices( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan );
    extern void Abc_NtkRedirectCiCo( Abc_Ntk_t * pNtk );
    extern Abc_Ntk_t * Abc_NtkFromCellMappedGia( Gia_Man_t * p, int fUseBuffs );
    extern Abc_Ntk_t * Abc_NtkFromMappedGia( Gia_Man_t * p, int fFindEnables, int fUseBuffs );
    extern Abc_Ntk_t * Abc_NtkFromMappedGiaAnd5( Gia_Man_t * p, int fFindEnables, int fUseBuffs );
    extern Abc_Ntk_t * Abc_NtkFromMappedGia2( Gia_Man_t * p, int fFindEnables, int fUseBuffs, int fCheckAnd5, int fVerbose );

    Aig_Man_t * pMan;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int fStatusClear = 1;
    int fFindEnables = 0;
    int fUseBuffs    = 0;
    int fCheckAnd5   = 0;
    int c, fVerbose  = 0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "seiovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fStatusClear ^= 1;
            break;
        case 'e':
            fFindEnables ^= 1;
            break;
        case 'i':
            fCheckAnd5 ^= 1;
            break;
        case 'o':
            fUseBuffs ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( fFindEnables )
        pNtk = Abc_NtkFromMappedGia( pAbc->pGia, 1, fUseBuffs );
    else if ( Gia_ManHasCellMapping(pAbc->pGia) )
        pNtk = Abc_NtkFromCellMappedGia( pAbc->pGia, fUseBuffs );
    else if ( Gia_ManHasMapping(pAbc->pGia) || pAbc->pGia->pMuxes )
        pNtk = Abc_NtkFromMappedGia2( pAbc->pGia, 0, fUseBuffs, fCheckAnd5, fVerbose );
    else if ( Gia_ManHasDangling(pAbc->pGia) == 0 )
    {
        pMan = Gia_ManToAig( pAbc->pGia, 0 );
        pNtk = Abc_NtkFromAigPhase( pMan );
        pNtk->pName = Extra_UtilStrsav(pMan->pName);
        Aig_ManStop( pMan );
    }
    else
    {
        Abc_Ntk_t * pNtkNoCh;
        Abc_Print( 0, "Transforming AIG with %d choice nodes.\n", Gia_ManEquivCountClasses(pAbc->pGia) );
        // create network without choices
        pMan = Gia_ManToAig( pAbc->pGia, 0 );
        pNtkNoCh = Abc_NtkFromAigPhase( pMan );
        pNtkNoCh->pName = Extra_UtilStrsav(pMan->pName);
        Aig_ManStop( pMan );
        // derive network with choices
        pMan = Gia_ManToAig( pAbc->pGia, 1 );
        pNtk = Abc_NtkFromDarChoices( pNtkNoCh, pMan );
        Abc_NtkDelete( pNtkNoCh );
        Aig_ManStop( pMan );
    }
    if ( pNtk == NULL )
        return 1;
    // transfer explicit flop initialization (register-box initialization is separate)
    if ( pAbc->pGia->vRegInits &&
         (!pAbc->pGia->pManTime || Gia_ManRegBoxNum(pAbc->pGia) == 0) )
    {
        Abc_Obj_t * pLatch;
        int i, k = 0, Init;
        if ( Vec_IntSize(pAbc->pGia->vRegInits) != Abc_NtkLatchNum(pNtk) )
        {
            Abc_Print( -1, "The number of register initial values does not match the number of latches.\n" );
            Abc_NtkDelete( pNtk );
            return 1;
        }
        Abc_NtkForEachLatch( pNtk, pLatch, i )
        {
            Init = Vec_IntEntry( pAbc->pGia->vRegInits, k++ );
            if ( Init == 0 )
                Abc_LatchSetInit0( pLatch );
            else if ( Init == 1 )
                Abc_LatchSetInit1( pLatch );
            else
                Abc_LatchSetInitDc( pLatch );
        }
    }
    // transfer the spec name to the pNtk
    if( pAbc->pGia->pSpec )
    {
        ABC_FREE( pNtk->pSpec );
        pNtk->pSpec = Extra_UtilStrsav( pAbc->pGia->pSpec );
    }
    // transfer PI names to pNtk
    if ( pAbc->pGia->vNamesIn )
    {
        Abc_Obj_t * pObj;
        int i;
        Abc_NtkForEachCi( pNtk, pObj, i ) {
            if (i < Vec_PtrSize(pAbc->pGia->vNamesIn)) {
                Nm_ManDeleteIdName(pNtk->pManName, pObj->Id);
                Abc_ObjAssignName( pObj, (char *)Vec_PtrEntry(pAbc->pGia->vNamesIn, i), NULL );
            }
        }
    }
    // transfer PO names to pNtk
    if ( pAbc->pGia->vNamesOut )
    {
        char pSuffix[1000];
        Abc_Obj_t * pObj; int i;
        unsigned char nDigits = (unsigned char)Abc_Base10Log( Abc_NtkLatchNum(pNtk) );
        Abc_NtkForEachCo( pNtk, pObj, i ) {
            if (i < Vec_PtrSize(pAbc->pGia->vNamesOut)) {
                Nm_ManDeleteIdName(pNtk->pManName, pObj->Id);
                if ( Abc_ObjIsPo(pObj) )
                    Abc_ObjAssignName( pObj, (char *)Vec_PtrEntry(pAbc->pGia->vNamesOut, i), NULL );
                else
                {
                    assert( i >= Abc_NtkPoNum(pNtk) );
                    sprintf( pSuffix, "_li%0*d", nDigits, i-Abc_NtkPoNum(pNtk) );
                    Abc_ObjAssignName( pObj, (char *)Vec_PtrEntry(pAbc->pGia->vNamesOut, i), pSuffix );
                }
            }
        }
    }
    if ( pAbc->pGia->vNamesNode )
        Abc_Print( 0, "Internal nodes names are not transferred.\n" );

    // decouple CI/CO with the same name
    if ( !Abc_NtkIsStrash(pNtk) && (pAbc->pGia->vNamesIn || pAbc->pGia->vNamesOut) )
        Abc_NtkRedirectCiCo( pNtk );

    // transfer timing information
    if ( pAbc->pGia->vInArrs || pAbc->pGia->vOutReqs )
    {
        Abc_Obj_t * pObj; int i;
        Abc_NtkTimeInitialize( pNtk, NULL );
        Abc_NtkTimeSetDefaultArrival( pNtk, pAbc->pGia->DefInArrs, pAbc->pGia->DefInArrs );
        Abc_NtkTimeSetDefaultRequired( pNtk, pAbc->pGia->DefOutReqs, pAbc->pGia->DefOutReqs );
        if ( pAbc->pGia->vInArrs )
            Abc_NtkForEachCi( pNtk, pObj, i )
                Abc_NtkTimeSetArrival( pNtk, Abc_ObjId(pObj), Vec_FltEntry(pAbc->pGia->vInArrs, i), Vec_FltEntry(pAbc->pGia->vInArrs, i) );
        if ( pAbc->pGia->vOutReqs )
            Abc_NtkForEachCo( pNtk, pObj, i )
                Abc_NtkTimeSetRequired( pNtk, Abc_ObjId(pObj), Vec_FltEntry(pAbc->pGia->vOutReqs, i), Vec_FltEntry(pAbc->pGia->vOutReqs, i) );
    }

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    if ( fStatusClear )
        Abc_FrameClearVerifStatus( pAbc );
    return 0;

usage:
    Abc_Print( -2, "usage: &put [-seiovh]\n" );
    Abc_Print( -2, "\t         transfer the current network into the old ABC\n" );
    Abc_Print( -2, "\t-s     : toggle clearning verification status [default = %s]\n", fStatusClear? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle extracting MUXes for flop enables [default = %s]\n", fFindEnables? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle AND-decomposable polarity for 5-input LUTs [default = %s]\n", fCheckAnd5? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggles using buffers to decouple combinational outputs [default = %s]\n", fUseBuffs? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9MoveNames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "nvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pNtkCur == NULL )
    {
        Abc_Print( -1, "There is no current network\n" );
        return 1;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "There is no current AIG.\n" );
        return 1;
    }
    if ( Gia_ManCiNum(pAbc->pGia) != Abc_NtkCiNum(pAbc->pNtkCur) )
    {
        Abc_Print( -1, "The number of CIs does not match.\n" );
        return 1;
    }
    if ( Gia_ManCoNum(pAbc->pGia) != Abc_NtkCoNum(pAbc->pNtkCur) )
    {
        Abc_Print( -1, "The number of COs does not match.\n" );
        return 1;
    }
    if ( pAbc->pGia->vNamesIn  )    Vec_PtrFreeFree( pAbc->pGia->vNamesIn );
    if ( pAbc->pGia->vNamesOut )    Vec_PtrFreeFree( pAbc->pGia->vNamesOut );
    pAbc->pGia->vNamesIn  = Abc_NtkCollectCiNames( pAbc->pNtkCur );
    pAbc->pGia->vNamesOut = Abc_NtkCollectCoNames( pAbc->pNtkCur );
    return 0;

usage:
    Abc_Print( -2, "usage: &move_names [-vh]\n" );
    Abc_Print( -2, "\t         move CI/CO names\n" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compares to versions of the design and finds the best.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_ManCompareWithBest( Gia_Man_t * pBest, Gia_Man_t * p, int * pnBestLuts, int * pnBestEdges, int * pnBestLevels, int fArea )
{
    int nCurLuts, nCurEdges, nCurLevels;
    Gia_ManLutParams( p, &nCurLuts, &nCurEdges, &nCurLevels );
    if ( pBest == NULL ||
         Gia_ManPiNum(pBest) != Gia_ManPiNum(p) ||
         Gia_ManPoNum(pBest) != Gia_ManPoNum(p) ||
         Gia_ManRegNum(pBest) != Gia_ManRegNum(p) ||
         strcmp(Gia_ManName(pBest), Gia_ManName(p)) ||
         (!fArea && (*pnBestLevels > nCurLevels || (*pnBestLevels == nCurLevels && 2*(*pnBestLuts) + *pnBestEdges > 2*nCurLuts + nCurEdges))) ||
         ( fArea && (*pnBestLuts   > nCurLuts   || (*pnBestLuts   == nCurLuts   && *pnBestLevels > nCurLevels)))
       )
    {
        *pnBestLuts = nCurLuts;
        *pnBestEdges = nCurEdges;
        *pnBestLevels = nCurLevels;
        //printf( "\nUpdating best (%d %d %d).\n\n", nCurLuts, nCurEdges, nCurLevels );
        return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Save( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fArea = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fArea ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "GIA has no mapping.\n" );
        return 1;
    }
    if ( !Gia_ManCompareWithBest( pAbc->pGiaBest, pAbc->pGia, &pAbc->nBestLuts, &pAbc->nBestEdges, &pAbc->nBestLevels, fArea ) )
        return 0;
    // save the design as best
    Gia_ManStopP( &pAbc->pGiaBest );
    pAbc->pGiaBest = Gia_ManDupWithAttributes( pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &save [-ah]\n" );
    Abc_Print( -2, "\t        compares and possibly saves AIG with mapping\n" );
    Abc_Print( -2, "\t-a    : toggle using area as the primary metric [default = %s]\n", fArea? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Save2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fArea = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fArea ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "GIA has no mapping.\n" );
        return 1;
    }
    if ( !Gia_ManCompareWithBest( pAbc->pGiaBest2, pAbc->pGia, &pAbc->nBestLuts2, &pAbc->nBestEdges2, &pAbc->nBestLevels2, fArea ) )
        return 0;
    // save the design as best
    Gia_ManStopP( &pAbc->pGiaBest2 );
    pAbc->pGiaBest2 = Gia_ManDupWithAttributes( pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &save2 [-ah]\n" );
    Abc_Print( -2, "\t        compares and possibly saves AIG with mapping\n" );
    Abc_Print( -2, "\t-a    : toggle using area as the primary metric [default = %s]\n", fArea? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SaveAig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fClear = 0, fArea = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fClear ^= 1;
            break;
        case 'a':
            fArea ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( fClear )
    {
        Gia_ManStopP( &pAbc->pGiaSaved );
        return 0;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( fArea && pAbc->pGiaSaved != NULL && Gia_ManAndNum(pAbc->pGiaSaved) <= Gia_ManAndNum(pAbc->pGia) )
        return 0;
    if ( !fArea && pAbc->pGiaSaved != NULL && !(Gia_ManLevelNum(pAbc->pGiaSaved) > Gia_ManLevelNum(pAbc->pGia) || (Gia_ManLevelNum(pAbc->pGiaSaved) == Gia_ManLevelNum(pAbc->pGia) && Gia_ManAndNum(pAbc->pGiaSaved) > Gia_ManAndNum(pAbc->pGia))) )
        return 0;
    // save the design as best
    Gia_ManStopP( &pAbc->pGiaSaved );
    pAbc->pGiaSaved = Gia_ManDupWithAttributes( pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &saveaig [-cah]\n" );
    Abc_Print( -2, "\t        saves the current AIG into the internal storage\n" );
    Abc_Print( -2, "\t-c    : toggle clearing the saved AIG [default = %s]\n", fClear? "yes": "no" );
    Abc_Print( -2, "\t-a    : toggle saving AIG with the smaller area [default = %s]\n", fArea? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Load( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    // restore from best
    if ( pAbc->pGiaBest == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Load(): There is no best design saved.\n" );
        return 1;
    }
    Gia_ManStopP( &pAbc->pGia );
    pAbc->pGia = Gia_ManDupWithAttributes( pAbc->pGiaBest );
    Sn_ForgetGiaDescriptor(pAbc);
    return 0;

usage:
    Abc_Print( -2, "usage: &load [-h]\n" );
    Abc_Print( -2, "\t        loads AIG with mapping previously saved by &save\n" );
    Abc_Print( -2, "\t        (after loading the previously saved AIG can be loaded again)\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Load2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    // restore from best
    if ( pAbc->pGiaBest2 == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Load2(): There is no best design saved.\n" );
        return 1;
    }
    Gia_ManStopP( &pAbc->pGia );
    pAbc->pGia = pAbc->pGiaBest2;
    Sn_ForgetGiaDescriptor(pAbc);
    pAbc->pGiaBest2 = NULL;
    pAbc->nBestLuts2 = 0;
    pAbc->nBestEdges2 = 0;
    pAbc->nBestLevels2 = 0;
    return 0;

usage:
    Abc_Print( -2, "usage: &load2 [-h]\n" );
    Abc_Print( -2, "\t        loads AIG with mapping previously saved by &save2\n" );
    Abc_Print( -2, "\t        (after loading the previously saved AIG cannot be loaded again)\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9LoadAig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    // restore from best
    if ( pAbc->pGiaSaved == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9LoadAig(): There is no design saved.\n" );
        return 1;
    }
    Gia_ManStopP( &pAbc->pGia );
    pAbc->pGia = Gia_ManDupWithAttributes( pAbc->pGiaSaved );
    Sn_ForgetGiaDescriptor(pAbc);
    return 0;

usage:
    Abc_Print( -2, "usage: &loadaig [-h]\n" );
    Abc_Print( -2, "\t        loads AIG previously saved by &saveaig\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9WriteVer( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_WriteVerilogInt( char * pFileName, Gia_Man_t * pGia, int fUseGates, int fVerbose, int fUseCtrlPis );
    extern void Gia_WriteMappedVerilog( char * pFileName, Gia_Man_t * pGia, int fVerbose );
    char * pFileSpec = NULL;
    Abc_Ntk_t * pNtkSpec = NULL;
    char * pFileName;
    char ** pArgvNew;
    int c, nArgcNew;
    int fUseCtrlPis = 0;
    int fUseGates = 0;
    int fUseLuts = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Scglvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a file name.\n" );
                goto usage;
            }
            pFileSpec = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'c':
            fUseCtrlPis ^= 1;
            break;
        case 'g':
            fUseGates ^= 1;
            break;
        case 'l':
            fUseLuts ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "Expecting output file name on the command line.\n" );
        return 1;
    }
    pFileName = argv[globalUtilOptind];
    if ( pFileSpec == NULL )
    {
        if ( pAbc->pGia == NULL )
        {
            Abc_Print( -1, "There is no AIG to write.\n" );
            return 1;
        }
        // Check if we should write LUT-based Verilog
        if ( fUseLuts )
        {
            if ( !Gia_ManHasMapping(pAbc->pGia) )
            {
                Abc_Print( -1, "Cannot write LUT-based Verilog because AIG is not mapped.\n" );
                Abc_Print( -1, "Use \"&if\" to map the AIG first, or omit the -l flag.\n" );
                return 1;
            }
            Gia_WriteMappedVerilog( pFileName, pAbc->pGia, fVerbose );
        }
        else
        {
            Gia_WriteVerilogInt( pFileName, pAbc->pGia, fUseGates, fVerbose, fUseCtrlPis );
        }
    }
    else
    {
        if ( pAbc->pNtkCur == NULL )
        {
            Abc_Print( -1, "There is no mapped file to write.\n" );
            return 1;
        }
        pNtkSpec = Io_ReadNetlist( pFileSpec, Io_ReadFileType(pFileSpec), 0 );
        if ( pNtkSpec == NULL )
        {
            Abc_Print( -1, "Reading hierarchical Verilog for the specification has failed.\n" );
            return 1;
        }
        Abc_NtkInsertHierarchyGia( pNtkSpec, pAbc->pNtkCur, fVerbose );
        Io_WriteVerilog( pNtkSpec, pFileName, 0, 0 );
        Abc_NtkDelete( pNtkSpec );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &write_ver [-S <file>] [-cglvh] <file>\n" );
    Abc_Print( -2, "\t          writes hierarchical Verilog\n" );
    Abc_Print( -2, "\t-S file : file name for the original design (required when hierarchy is present)\n" );
    Abc_Print( -2, "\t-c      : add clk/rst ports for seq AIGs [default = %s]\n", fUseCtrlPis? "no": "yes" );
    Abc_Print( -2, "\t-g      : toggle output gates vs assign-statements [default = %s]\n", fUseGates? "gates": "assigns" );
    Abc_Print( -2, "\t-l      : write LUT6-based Verilog for mapped AIGs [default = %s]\n", fUseLuts? "yes": "no" );
    Abc_Print( -2, "\t-v      : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    Abc_Print( -2, "\t<file>  : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Write( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileName;
    char ** pArgvNew;
    int c, nArgcNew;
    int fUnique  = 0;
    int fVerilog = 0;
    int fVerNand = 0;
    int fInter   = 0;
    int fInterComb = 0;
    int fAssign  = 0;
    int fVerBufs = 0;
    int fMiniAig = 0;
    int fMiniLut = 0;
    int fWriteNewLine = 0;
    int fReverse = 0;
    int fSkipComment = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "upqicabmlnrsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'u':
            fUnique ^= 1;
            break;
        case 'p':
            fVerilog ^= 1;
            break;
        case 'q':
            fVerNand ^= 1;
            break;
        case 'i':
            fInter ^= 1;
            break;
        case 'c':
            fInterComb ^= 1;
            break;      
        case 'a':
            fAssign ^= 1;
            break;                        
        case 'b':
            fVerBufs ^= 1;
            break;
        case 'm':
            fMiniAig ^= 1;
            break;
        case 'l':
            fMiniLut ^= 1;
            break;
        case 'n':
            fWriteNewLine ^= 1;
            break;
        case 'r':
            fReverse ^= 1;
            break;            
        case 's':
            fSkipComment ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Write(): There is no AIG to write.\n" );
        return 1;
    }
    pFileName = argv[globalUtilOptind];
    if ( fUnique )
    {
        Gia_Man_t * pGia = Gia_ManIsoCanonicize( pAbc->pGia, fVerbose );
        Gia_AigerWriteSimple( pGia, pFileName );
        Gia_ManStop( pGia );
    }
    else if ( fVerNand )
        Gia_ManDumpVerilogNand( pAbc->pGia, pFileName );
    else if ( fVerilog )
        Gia_ManDumpVerilog( pAbc->pGia, pFileName, NULL, fVerBufs, fInter, fInterComb, fAssign, fReverse );
    else if ( fMiniAig )
        Gia_ManWriteMiniAig( pAbc->pGia, pFileName );
    else if ( fMiniLut )
        Gia_ManWriteMiniLut( pAbc->pGia, pFileName );
    else
        Gia_AigerWriteS( pAbc->pGia, pFileName, 0, 0, fWriteNewLine, fSkipComment );
    return 0;

usage:
    Abc_Print( -2, "usage: &w [-upqicabmlnsvh] <file>\n" );
    Abc_Print( -2, "\t         writes the current AIG into the AIGER file\n" );
    Abc_Print( -2, "\t-u     : toggle writing canonical AIG structure [default = %s]\n", fUnique? "yes" : "no" );
    Abc_Print( -2, "\t-p     : toggle writing Verilog with 'and' and 'not' [default = %s]\n", fVerilog? "yes" : "no" );
    Abc_Print( -2, "\t-q     : toggle writing Verilog with NAND-gates [default = %s]\n", fVerNand? "yes" : "no" );
    Abc_Print( -2, "\t-i     : toggle writing the interface module in Verilog [default = %s]\n", fInter? "yes" : "no" );
    Abc_Print( -2, "\t-c     : toggle writing the interface module in Verilog [default = %s]\n", fInterComb? "yes" : "no" );
    Abc_Print( -2, "\t-a     : toggle writing the interface module with assign-statements [default = %s]\n", fAssign? "yes" : "no" );
    Abc_Print( -2, "\t-b     : toggle writing additional buffers in Verilog [default = %s]\n", fVerBufs? "yes" : "no" );
    Abc_Print( -2, "\t-m     : toggle writing MiniAIG rather than AIGER [default = %s]\n", fMiniAig? "yes" : "no" );
    Abc_Print( -2, "\t-l     : toggle writing MiniLUT rather than AIGER [default = %s]\n", fMiniLut? "yes" : "no" );
    Abc_Print( -2, "\t-n     : toggle writing \'\\n\' after \'c\' in the AIGER file [default = %s]\n", fWriteNewLine? "yes": "no" );
    //Abc_Print( -2, "\t-r     : toggle reversing the order of input/output bits [default = %s]\n", fReverse? "yes": "no" );    
    Abc_Print( -2, "\t-s     : toggle skipping the timestamp in the output file [default = %s]\n", fSkipComment? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9WriteLut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_AigerWriteLut( Gia_Man_t * pGia, char * pFileName );
    char * pFileName;
    char ** pArgvNew;
    int c, nArgcNew;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }
    pFileName = argv[globalUtilOptind];
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9WriteLut(): There is no AIG to write.\n" );
        return 1;
    }
    if ( !Gia_ManHasMapping(pAbc->pGia) )
    {
        Abc_Print( -1, "Abc_CommandAbc9WriteLut(): AIG has no mapping.\n" );
        return 1;
    }
    Gia_AigerWriteLut( pAbc->pGia, pFileName );
    return 0;

usage:
    Abc_Print( -2, "usage: &wlut [-umvh] <file>\n" );
    Abc_Print( -2, "\t         writes the the current LUT mapping into a binary file\n" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9LNetRead( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Vec_WrdReadTest( char * pFileName );
    extern void Gia_ManReadSimInfoInputs( char * pFileName, char * pFileOut1, int fVerbose );
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc == globalUtilOptind + 2 ) // read 1 file, write 1 file
    {
        Gia_ManReadSimInfoInputs( argv[globalUtilOptind], argv[globalUtilOptind+1], fVerbose );
        return 0;
    }
    if ( strstr(argv[globalUtilOptind], ".v") )
    {
        Gia_Man_t * pNew = Vec_WrdReadTest( argv[globalUtilOptind] );
        if ( pNew == NULL )
        {
            printf( "Cannot read network from file \"%s\".\n", argv[globalUtilOptind] );
            return 0;
        }
        Abc_FrameUpdateGia( pAbc, pNew );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &lnetread [-vh] <file> <file2>\n" );
    Abc_Print( -2, "\t           reads and converts the network or the simulation data\n" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    Abc_Print( -2, "\t<file>   : input file name with simulation information\n");
    Abc_Print( -2, "\t<file2>  : output file name with simulation information\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Undo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Undo(): There is no design.\n" );
        return 1;
    }
    if ( pAbc->pGia2 == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Undo(): There is no previously saved network.\n" );
        return 1;
    }
    Gia_ManStop( pAbc->pGia );
    pAbc->pGia = pAbc->pGia2;
    Sn_ForgetGiaDescriptor(pAbc);
    pAbc->pGia2 = NULL;
    return 0;

usage:
    Abc_Print( -2, "usage: &undo [-h]\n" );
    Abc_Print( -2, "\t        reverses the previous AIG transformation\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses and prints a BTOR file.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9CatBtor( Abc_Frame_t * pAbc, int argc, char ** argv ) {
    extern int32_t Abc_BtorCat( char * pFileName, int fVerbose );
  
    int c, fVerbose = 0;
    char * pFileName;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "v" ) ) != EOF )
    {
        switch ( c ) {
        case 'v' :
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( argc == globalUtilOptind + 1 )
        pFileName = argv[globalUtilOptind];
    else
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 0;
    }

    return Abc_BtorCat( pFileName, fVerbose );

usage:
    Abc_Print( -2, "usage: &catbtor [-v] <file>\n" );
    Abc_Print( -2, "\t          parse BTOR file and print to stdout.\n" );
    Abc_Print( -2, "\t-v      : toggle printing verbose information\n");
    Abc_Print( -2, "\t<file>  : input BTOR file\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////
