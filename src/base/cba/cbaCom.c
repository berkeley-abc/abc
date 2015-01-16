/**CFile****************************************************************

  FileName    [cbaCom.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaCom.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "base/main/mainInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int  Cba_CommandRead     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Cba_CommandWrite    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Cba_CommandPs       ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Cba_CommandBlast    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  Cba_CommandTest     ( Abc_Frame_t * pAbc, int argc, char ** argv );

static inline Cba_Ntk_t * Cba_AbcGetNtk( Abc_Frame_t * pAbc )                       { return (Cba_Ntk_t *)pAbc->pAbcCba;                                  }
static inline void        Cba_AbcFreeNtk( Abc_Frame_t * pAbc )                      { if ( pAbc->pAbcCba ) Cba_ManFree(Cba_NtkMan(Cba_AbcGetNtk(pAbc)));  }
static inline void        Cba_AbcUpdateNtk( Abc_Frame_t * pAbc, Cba_Ntk_t * pNtk )  { Cba_AbcFreeNtk(pAbc); pAbc->pAbcCba = pNtk;                         }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Cba_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "New word level", "@read",       Cba_CommandRead,      0 );
    Cmd_CommandAdd( pAbc, "New word level", "@write",      Cba_CommandWrite,     0 );
    Cmd_CommandAdd( pAbc, "New word level", "@ps",         Cba_CommandPs,        0 );
    Cmd_CommandAdd( pAbc, "New word level", "@blast",      Cba_CommandBlast,     0 );
    Cmd_CommandAdd( pAbc, "New word level", "@test",       Cba_CommandTest,      0 );
}

/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Cba_End( Abc_Frame_t * pAbc )
{
    Cba_AbcFreeNtk( pAbc );
}


/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Cba_CommandRead( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Cba_Ntk_t * pNtk = NULL;
    char * pFileName = NULL;
    int c, fVerbose  =    0;
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
    if ( argc != globalUtilOptind + 1 )
    {
        printf( "Cba_CommandRead(): Input file name should be given on the command line.\n" );
        return 0;
    }
    // get the file name
    pFileName = argv[globalUtilOptind];
    if ( (pFile = fopen( pFileName, "r" )) == NULL )
    {
        Abc_Print( 1, "Cannot open input file \"%s\". ", pFileName );
        if ( (pFileName = Extra_FileGetSimilarName( pFileName, ".v", ".blif", NULL, NULL, NULL )) )
            Abc_Print( 1, "Did you mean \"%s\"?", pFileName );
        Abc_Print( 1, "\n" );
        return 0;
    }
    fclose( pFile );

    // perform reading
    //pNtk = Cba_ReadVer( pFileName );
    Cba_AbcUpdateNtk( pAbc, pNtk );
    return 0;
usage:
    Abc_Print( -2, "usage: @read [-vh] <file_name>\n" );
    Abc_Print( -2, "\t         reads word-level design from Verilog file\n" );
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
int Cba_CommandWrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cba_Ntk_t * pNtk = Cba_AbcGetNtk(pAbc);
    char * pFileName = NULL;
    int c, fVerbose  =    0;
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
        Abc_Print( 1, "Cba_CommandWrite(): There is no current design.\n" );
        return 0;
    }
    if ( argc == globalUtilOptind )
        pFileName = Extra_FileNameGenericAppend( Cba_NtkMan(pNtk)->pName, "_out.v" );
    else if ( argc == globalUtilOptind + 1 )
        pFileName = argv[globalUtilOptind];
    else
    {
        printf( "Output file name should be given on the command line.\n" );
        return 0;
    }
    //Cba_WriteVer( pNtk, pFileName );
    return 0;
usage:
    Abc_Print( -2, "usage: @write [-vh]\n" );
    Abc_Print( -2, "\t         writes the design into a file\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",        fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Cba_CommandPs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cba_Ntk_t * pNtk = Cba_AbcGetNtk(pAbc);
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
        Abc_Print( 1, "Cba_CommandPs(): There is no current design.\n" );
        return 0;
    }
//    Cba_NtkPrintStats( pNtk, fDistrib, fVerbose );
    return 0;
usage:
    Abc_Print( -2, "usage: @ps [-vh]\n" );
    Abc_Print( -2, "\t         prints statistics\n" );
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
int Cba_CommandBlast( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cba_Ntk_t * pNtk = Cba_AbcGetNtk(pAbc);
    //Vec_Int_t * vBoxIds = NULL;
    Gia_Man_t * pNew = NULL;
    int c, fMulti = 0, fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "mvh" ) ) != EOF )
    {
        switch ( c )
        {
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
        Abc_Print( 1, "Cba_CommandBlast(): There is no current design.\n" );
        return 0;
    }
    if ( fMulti )
    {
//        vBoxIds = Cba_NtkCollectMultipliers( pNtk );
//        if ( vBoxIds == NULL )
//            Abc_Print( 1, "Warning:  There is no multipliers in the design.\n" );
    }
    // transform
//    pNew = Cba_NtkBitBlast( pNtk, vBoxIds );
//    Vec_IntFreeP( &vBoxIds );
    if ( pNew == NULL )
    {
        Abc_Print( 1, "Cba_CommandBlast(): Bit-blasting has failed.\n" );
        return 0;
    }
    Abc_FrameUpdateGia( pAbc, pNew );
    return 0;
usage:
    Abc_Print( -2, "usage: @blast [-mvh]\n" );
    Abc_Print( -2, "\t         performs bit-blasting of the word-level design\n" );
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
int Cba_CommandTest( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Cba_ManReadDesExperiment( Abc_Ntk_t * pNtk );
    Abc_Ntk_t * pAbcNtk;
    //Cba_Ntk_t * pNtk = Cba_AbcGetNtk(pAbc);
//    char * pFileName = "c/hie/dump/1/netlist_1.v";
//    char * pFileName = "c/hie/dump/3/netlist_18.v";
    char * pFileName = "c/hie/dump/1/netlist_0.v";
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
/*
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Cba_CommandTest(): There is no current design.\n" );
        return 0;
    }
*/
    // transform
    pAbcNtk = Io_ReadNetlist( pFileName, Io_ReadFileType(pFileName), 0 );
    Cba_ManReadDesExperiment( pAbcNtk );
    Abc_NtkDelete( pAbcNtk );
    return 0;
usage:
    Abc_Print( -2, "usage: @test [-vh]\n" );
    Abc_Print( -2, "\t         experiments with word-level networks\n" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

