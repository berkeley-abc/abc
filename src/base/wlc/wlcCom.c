/**CFile****************************************************************

  FileName    [wlcCom.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Command handlers.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcCom.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"
#include "base/main/mainInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int  Abc_CommandReadWlc  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Abc_CommandWriteWlc ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Abc_CommandPs       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Abc_CommandBlast    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Abc_CommandPsInv    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Abc_CommandGetInv   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Abc_CommandTest     ( Abc_Frame_t * pAbc, int argc, char ** argv );

static inline Wlc_Ntk_t * Wlc_AbcGetNtk( Abc_Frame_t * pAbc )                       { return (Wlc_Ntk_t *)pAbc->pAbcWlc;                      }
static inline void        Wlc_AbcFreeNtk( Abc_Frame_t * pAbc )                      { if ( pAbc->pAbcWlc ) Wlc_NtkFree(Wlc_AbcGetNtk(pAbc));  }
static inline void        Wlc_AbcUpdateNtk( Abc_Frame_t * pAbc, Wlc_Ntk_t * pNtk )  { Wlc_AbcFreeNtk(pAbc); pAbc->pAbcWlc = pNtk;             }

static inline Vec_Int_t * Wlc_AbcGetInv( Abc_Frame_t * pAbc )                       { return pAbc->pAbcWlcInv;                                }
static inline Vec_Int_t * Wlc_AbcGetCnf( Abc_Frame_t * pAbc )                       { return pAbc->pAbcWlcCnf;                                }
static inline Vec_Str_t * Wlc_AbcGetStr( Abc_Frame_t * pAbc )                       { return pAbc->pAbcWlcStr;                                }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Wlc_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Word level", "%read",       Abc_CommandReadWlc,   0 );
    Cmd_CommandAdd( pAbc, "Word level", "%write",      Abc_CommandWriteWlc,  0 );
    Cmd_CommandAdd( pAbc, "Word level", "%ps",         Abc_CommandPs,        0 );
    Cmd_CommandAdd( pAbc, "Word level", "%blast",      Abc_CommandBlast,     0 );
    Cmd_CommandAdd( pAbc, "Word level", "%psinv",      Abc_CommandPsInv,     0 );
    Cmd_CommandAdd( pAbc, "Word level", "%getinv",     Abc_CommandGetInv,    0 );
    Cmd_CommandAdd( pAbc, "Word level", "%test",       Abc_CommandTest,      0 );
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Wlc_End( Abc_Frame_t * pAbc )
{
    Wlc_AbcFreeNtk( pAbc );
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Wlc_SetNtk( Abc_Frame_t * pAbc, Wlc_Ntk_t * pNtk )
{
    Wlc_AbcUpdateNtk( pAbc, pNtk );
}


/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Abc_CommandReadWlc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Wlc_Ntk_t * pNtk = NULL;
    char * pFileName = NULL;
    int fOldParser   =    0;
    int fPrintTree   =    0;
    int c, fVerbose  =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "opvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'o':
            fPrintTree ^= 1;
            break;
        case 'p':
            fOldParser ^= 1;
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
    if ( argc != globalUtilOptind + 1 )
    {
        printf( "Abc_CommandReadWlc(): Input file name should be given on the command line.\n" );
        return 0;
    }
    // get the file name
    pFileName = argv[globalUtilOptind];
    if ( (pFile = fopen( pFileName, "r" )) == NULL )
    {
        Abc_Print( 1, "Cannot open input file \"%s\". ", pFileName );
        if ( (pFileName = Extra_FileGetSimilarName( pFileName, ".v", ".smt", ".smt2", NULL, NULL )) )
            Abc_Print( 1, "Did you mean \"%s\"?", pFileName );
        Abc_Print( 1, "\n" );
        return 0;
    }
    fclose( pFile );

    // perform reading
    if ( !strcmp( Extra_FileNameExtension(pFileName), "v" )  )
        pNtk = Wlc_ReadVer( pFileName );
    else if ( !strcmp( Extra_FileNameExtension(pFileName), "smt" ) || !strcmp( Extra_FileNameExtension(pFileName), "smt2" )  )
        pNtk = Wlc_ReadSmt( pFileName, fOldParser, fPrintTree );
    else
    {
        printf( "Abc_CommandReadWlc(): Unknown file extension.\n" );
        return 0;
    }
    Wlc_AbcUpdateNtk( pAbc, pNtk );
    return 0;
usage:
    Abc_Print( -2, "usage: %%read [-opvh] <file_name>\n" );
    Abc_Print( -2, "\t         reads word-level design from Verilog file\n" );
    Abc_Print( -2, "\t-o     : toggle using old SMT-LIB parser [default = %s]\n", fOldParser? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle printing parse SMT-LIB tree [default = %s]\n", fPrintTree? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Abc_CommandWriteWlc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Wlc_Ntk_t * pNtk = Wlc_AbcGetNtk(pAbc);
    char * pFileName = NULL;
    int fAddCos      =    0; 
    int fSplitNodes  =    0; 
    int fNoFlops     =    0;
    int c, fVerbose  =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "anfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAddCos ^= 1;
            break;
        case 'n':
            fSplitNodes ^= 1;
            break;
        case 'f':
            fNoFlops ^= 1;
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
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Abc_CommandWriteWlc(): There is no current design.\n" );
        return 0;
    }
    if ( argc == globalUtilOptind )
        pFileName = Extra_FileNameGenericAppend( pNtk->pName, "_out.v" );
    else if ( argc == globalUtilOptind + 1 )
        pFileName = argv[globalUtilOptind];
    else
    {
        printf( "Output file name should be given on the command line.\n" );
        return 0;
    }
    if ( fSplitNodes )
    {
        pNtk = Wlc_NtkDupSingleNodes( pNtk );
        Wlc_WriteVer( pNtk, pFileName, fAddCos, fNoFlops );
        Wlc_NtkFree( pNtk );
    }
    else
        Wlc_WriteVer( pNtk, pFileName, fAddCos, fNoFlops );

    return 0;
usage:
    Abc_Print( -2, "usage: %%write [-anfvh]\n" );
    Abc_Print( -2, "\t         writes the design into a file\n" );
    Abc_Print( -2, "\t-a     : toggle adding a CO for each node [default = %s]\n",       fAddCos? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle splitting into individual nodes [default = %s]\n", fSplitNodes? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle skipping flops when writing file [default = %s]\n",fNoFlops? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",    fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Abc_CommandPs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Wlc_Ntk_t * pNtk = Wlc_AbcGetNtk(pAbc);
    int fShowMulti   = 0;
    int fShowAdder   = 0;
    int fDistrib     = 0;
    int c, fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "madvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'm':
            fShowMulti ^= 1;
            break;
        case 'a':
            fShowAdder ^= 1;
            break;
        case 'd':
            fDistrib ^= 1;
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
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Abc_CommandPs(): There is no current design.\n" );
        return 0;
    }
    Wlc_NtkPrintStats( pNtk, fDistrib, fVerbose );
    if ( fShowMulti )
        Wlc_NtkPrintNodes( pNtk, WLC_OBJ_ARI_MULTI );
    if ( fShowAdder )
        Wlc_NtkPrintNodes( pNtk, WLC_OBJ_ARI_ADD );
    return 0;
usage:
    Abc_Print( -2, "usage: %%ps [-madvh]\n" );
    Abc_Print( -2, "\t         prints statistics\n" );
    Abc_Print( -2, "\t-m     : toggle printing multipliers [default = %s]\n",         fShowMulti? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle printing adders [default = %s]\n",              fShowAdder? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle printing distrubition [default = %s]\n",        fDistrib? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Abc_CommandBlast( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Wlc_Ntk_t * pNtk = Wlc_AbcGetNtk(pAbc);
    Vec_Int_t * vBoxIds = NULL;
    Gia_Man_t * pNew = NULL;
    int c, fGiaSimple = 0, fAddOutputs = 0, fMulti = 0, fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "comvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fGiaSimple ^= 1;
            break;
        case 'o':
            fAddOutputs ^= 1;
            break;
        case 'm':
            fMulti ^= 1;
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
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Abc_CommandBlast(): There is no current design.\n" );
        return 0;
    }
    if ( fMulti )
    {
        vBoxIds = Wlc_NtkCollectMultipliers( pNtk );
        if ( vBoxIds == NULL )
            Abc_Print( 1, "Warning:  There is no multipliers in the design.\n" );
    }
    // transform
    pNew = Wlc_NtkBitBlast( pNtk, vBoxIds, fGiaSimple, fAddOutputs );
    Vec_IntFreeP( &vBoxIds );
    if ( pNew == NULL )
    {
        Abc_Print( 1, "Abc_CommandBlast(): Bit-blasting has failed.\n" );
        return 0;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: %%blast [-comvh]\n" );
    Abc_Print( -2, "\t         performs bit-blasting of the word-level design\n" );
    Abc_Print( -2, "\t-c     : toggle using AIG w/o const propagation and strashing [default = %s]\n", fGiaSimple? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle using additional POs on the word-level boundaries [default = %s]\n", fAddOutputs? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle creating boxes for all multipliers in the design [default = %s]\n", fMulti? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Abc_CommandPsInv( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Wlc_NtkPrintInvStats( Wlc_Ntk_t * pNtk, Vec_Int_t * vInv, int fVerbose );
    Wlc_Ntk_t * pNtk = Wlc_AbcGetNtk(pAbc);
    int c, fVerbose  = 0;
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
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Abc_CommandPsInv(): There is no current design.\n" );
        return 0;
    }
    if ( Wlc_AbcGetNtk(pAbc) == NULL )
    {
        Abc_Print( 1, "Abc_CommandPsInv(): There is no saved invariant.\n" );
        return 0;
    }
    if ( Wlc_AbcGetInv(pAbc) == NULL )
    {
        Abc_Print( 1, "Abc_CommandPsInv(): Invariant is not available.\n" );
        return 0;
    }
    Wlc_NtkPrintInvStats( pNtk, Wlc_AbcGetInv(pAbc), fVerbose );
    return 0;
    usage:
    Abc_Print( -2, "usage: %%psinv [-vh]\n" );
    Abc_Print( -2, "\t         prints statistics for inductive invariant\n" );
    Abc_Print( -2, "\t         (in the case of \'sat\' or \'undecided\', inifity clauses are used)\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Abc_CommandGetInv( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Wlc_NtkGetInv( Wlc_Ntk_t * pNtk, Vec_Int_t * vInv, Vec_Str_t * vSop, int fVerbose );
    Abc_Ntk_t * pMainNtk;
    Wlc_Ntk_t * pNtk = Wlc_AbcGetNtk(pAbc);
    int c, fVerbose  = 0;
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
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Abc_CommandGetInv(): There is no current design.\n" );
        return 0;
    }
    if ( Wlc_AbcGetNtk(pAbc) == NULL )
    {
        Abc_Print( 1, "Abc_CommandGetInv(): There is no saved invariant.\n" );
        return 0;
    }
    if ( Wlc_AbcGetInv(pAbc) == NULL )
    {
        Abc_Print( 1, "Abc_CommandGetInv(): Invariant is not available.\n" );
        return 0;
    }
    // derive the network
    pMainNtk = Wlc_NtkGetInv( pNtk, Wlc_AbcGetInv(pAbc), Wlc_AbcGetStr(pAbc), fVerbose );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pMainNtk );
    return 0;
    usage:
    Abc_Print( -2, "usage: %%getinv [-vh]\n" );
    Abc_Print( -2, "\t         places invariant found by PDR as the current network in the main-space\n" );
    Abc_Print( -2, "\t         (in the case of \'sat\' or \'undecided\', inifity clauses are used)\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Abc_CommandTest( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Wlc_NtkSimulateTest( Wlc_Ntk_t * p );
    Wlc_Ntk_t * pNtk = Wlc_AbcGetNtk(pAbc);
    int c, fVerbose  = 0;
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
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Abc_CommandBlast(): There is no current design.\n" );
        return 0;
    }
    // transform
    //pNtk = Wlc_NtkUifNodePairs( pNtk, NULL );
    //pNtk = Wlc_NtkAbstractNodes( pNtk, NULL );
    //Wlc_AbcUpdateNtk( pAbc, pNtk );
    //Wlc_GenerateSmtStdout( pAbc );
    //Wlc_NtkSimulateTest( (Wlc_Ntk_t *)pAbc->pAbcWlc );
    pNtk = Wlc_NtkDupSingleNodes( pNtk );
    Wlc_AbcUpdateNtk( pAbc, pNtk );
    return 0;
usage:
    Abc_Print( -2, "usage: %%test [-vh]\n" );
    Abc_Print( -2, "\t         experiments with word-level networks\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

