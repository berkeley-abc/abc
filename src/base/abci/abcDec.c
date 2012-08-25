/**CFile****************************************************************

  FileName    [abcDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures for testing and comparing decomposition algorithms.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "misc/extra/extra.h"
#include "misc/vec/vec.h"

#include "bool/bdc/bdc.h"
#include "bool/dec/dec.h"
#include "bool/kit/kit.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
// decomposition type
// 0 - none
// 1 - factoring
// 2 - bi-decomposition
// 3 - DSD

// data-structure to store a bunch of truth tables
typedef struct Abc_TtStore_t_  Abc_TtStore_t;
struct Abc_TtStore_t_ 
{
    int               nVars;
    int               nWords;
    int               nFuncs;
    word **           pFuncs;
};

// read/write/flip i-th bit of a bit string table:
static inline int     Abc_TruthGetBit( word * p, int i )         { return (int)(p[i>>6] >> (i & 63)) & 1;        }
static inline void    Abc_TruthSetBit( word * p, int i )         { p[i>>6] |= (((word)1)<<(i & 63));             }
static inline void    Abc_TruthXorBit( word * p, int i )         { p[i>>6] ^= (((word)1)<<(i & 63));             }

// read/write k-th digit d of a hexadecimal number:
static inline int     Abc_TruthGetHex( word * p, int k )         { return (int)(p[k>>4] >> ((k<<2) & 63)) & 15;  }
static inline void    Abc_TruthSetHex( word * p, int k, int d )  { p[k>>4] |= (((word)d)<<((k<<2) & 63));        }
static inline void    Abc_TruthXorHex( word * p, int k, int d )  { p[k>>4] ^= (((word)d)<<((k<<2) & 63));        }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// read one hex character
static inline int  Abc_TruthReadHexDigit( char HexChar )
{
    if ( HexChar >= '0' && HexChar <= '9' )
        return HexChar - '0';
    if ( HexChar >= 'A' && HexChar <= 'F' )
        return HexChar - 'A' + 10;
    if ( HexChar >= 'a' && HexChar <= 'f' )
        return HexChar - 'a' + 10;
    assert( 0 ); // not a hexadecimal symbol
    return -1; // return value which makes no sense
}

// write one hex character
static inline void Abc_TruthWriteHexDigit( FILE * pFile, int HexDigit )
{
    assert( HexDigit >= 0 && HexDigit < 16 );
    if ( HexDigit < 10 )
        fprintf( pFile, "%d", HexDigit );
    else
        fprintf( pFile, "%c", 'A' + HexDigit-10 );
}

// read one truth table in hexadecimal
void Abc_TruthReadHex( word * pTruth, char * pString, int nVars )
{
    int nWords = (nVars < 7)? 1 : (1 << (nVars-6));
    int k, Digit, nDigits = (nWords << 4);
    char EndSymbol;
    // skip the first 2 symbols if they are "0x"
    if ( pString[0] == '0' && pString[1] == 'x' )
        pString += 2;
    // get the last symbol
    EndSymbol = pString[nDigits];
    // the end symbol of the TT (the one immediately following hex digits)
    // should be one of the following: space, a new-line, or a zero-terminator
    // (note that on Windows symbols '\r' can be inserted before each '\n')
    assert( EndSymbol == ' ' || EndSymbol == '\n' || EndSymbol == '\r' || EndSymbol == '\0' );
    // read hexadecimal digits in the reverse order
    // (the last symbol in the string is the least significant digit)
    for ( k = 0; k < nDigits; k++ )
    {
        Digit = Abc_TruthReadHexDigit( pString[nDigits - 1 - k] );
        assert( Digit >= 0 && Digit < 16 );
        Abc_TruthSetHex( pTruth, k, Digit );
    }
}

// write one truth table in hexadecimal (do not add end-of-line!)
void Abc_TruthWriteHex( FILE * pFile, word * pTruth, int nVars )
{
    int nDigits, Digit, k;
    nDigits = (1 << (nVars-2));
    for ( k = 0; k < nDigits; k++ )
    {
        Digit = Abc_TruthGetHex( pTruth, k );
        assert( Digit >= 0 && Digit < 16 );
        Abc_TruthWriteHexDigit( pFile, Digit );
    }
}


/**Function*************************************************************

  Synopsis    [Allocate/Deallocate storage for truth tables..]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_TtStore_t * Abc_TruthStoreAlloc( int nVars, int nFuncs )
{
    Abc_TtStore_t * p;
    int i;
    p = (Abc_TtStore_t *)malloc( sizeof(Abc_TtStore_t) );
    p->nVars  =  nVars;
    p->nWords = (nVars < 7) ? 1 : (1 << (nVars-6));
    p->nFuncs =  nFuncs;
    // alloc storage for 'nFuncs' truth tables as one chunk of memory
    p->pFuncs = (word **)malloc( (sizeof(word *) + sizeof(word) * p->nWords) * p->nFuncs );
    // assign and clean the truth table storage
    p->pFuncs[0] = (word *)(p->pFuncs + p->nFuncs);
    memset( p->pFuncs[0], 0, sizeof(word) * p->nWords * p->nFuncs );
    // split it up into individual truth tables
    for ( i = 1; i < p->nFuncs; i++ )
        p->pFuncs[i] = p->pFuncs[i-1] + p->nWords;
    return p;
}
void Abc_TtStoreFree( Abc_TtStore_t * p )
{
    free( p->pFuncs );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Read file contents.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_FileRead( char * pFileName )
{
    FILE * pFile;
    char * pBuffer;
    int nFileSize, RetValue;
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return NULL;
    }
    // get the file size, in bytes
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile );  
    // move the file current reading position to the beginning
    rewind( pFile ); 
    // load the contents of the file into memory
    pBuffer = (char *)malloc( nFileSize + 3 );
    RetValue = fread( pBuffer, nFileSize, 1, pFile );
    // add several empty lines at the end
    // (these will be used to signal the end of parsing)
    pBuffer[ nFileSize + 0] = '\n';
    pBuffer[ nFileSize + 1] = '\n';
    // terminate the string with '\0'
    pBuffer[ nFileSize + 2] = '\0';
    fclose( pFile );
    return pBuffer;
}

/**Function*************************************************************

  Synopsis    [Determine the number of variables by reading the first line.]

  Description [Determine the number of functions by counting the lines.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TruthGetParams( char * pFileName, int * pnVars, int * pnTruths )
{
    char * pContents;
    int i, nVars, nLines;
    // prepare the output 
    if ( pnVars )
        *pnVars = 0;
    if ( pnTruths )
        *pnTruths = 0;
    // read data from file
    pContents = Abc_FileRead( pFileName );
    if ( pContents == NULL )
        return;
    // count the number of symbols before the first space or new-line
    // (note that on Windows symbols '\r' can be inserted before each '\n')
    for ( i = 0; pContents[i]; i++ )
        if ( pContents[i] == ' ' || pContents[i] == '\n' || pContents[i] == '\r' )
            break;
    if ( pContents[i] == 0 )
        printf( "Strange, the input file does not have spaces and new-lines...\n" );

    // acount for the fact that truth tables may have "0x" at the beginning of each line
    if ( pContents[0] == '0' && pContents[1] == 'x' )
        i = i - 2;

    // determine the number of variables
    for ( nVars = 0; nVars < 32; nVars++ )
        if ( 4 * i == (1 << nVars) ) // the number of bits equal to the size of truth table
            break;
    if ( nVars < 2 || nVars > 16 )
    {
        printf( "Does not look like the input file contains truth tables...\n" );
        return;
    }
    if ( pnVars )
        *pnVars = nVars;

    // determine the number of functions by counting the lines
    nLines = 0;
    for ( i = 0; pContents[i]; i++ )
        nLines += (pContents[i] == '\n');
    if ( pnTruths )
        *pnTruths = nLines;
    ABC_FREE( pContents );
}


/**Function*************************************************************

  Synopsis    [Read truth tables from file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TruthStoreRead( char * pFileName, Abc_TtStore_t * p )
{
    char * pContents;
    int i, nLines;
    pContents = Abc_FileRead( pFileName );
    if ( pContents == NULL )
        return;
    // here it is assumed (without checking!) that each line of the file 
    // begins with a string of hexadecimal chars followed by space

    // the file will be read till the first empty line (pContents[i] == '\n')
    // (note that Abc_FileRead() added several empty lines at the end of the file contents)
    for ( nLines = i = 0; pContents[i] != '\n'; )
    {
        // read one line
        Abc_TruthReadHex( p->pFuncs[nLines++], &pContents[i], p->nVars );
        // skip till after the end-of-line symbol
        // (note that end-of-line symbol is also skipped)
        while ( pContents[i++] != '\n' );
    }
    // adjust the number of functions read 
    // (we may have allocated more storage because some lines in the file were empty)
    assert( p->nFuncs >= nLines );
    p->nFuncs = nLines;
    ABC_FREE( pContents );
}

/**Function*************************************************************

  Synopsis    [Write truth tables into file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TtStoreWrite( char * pFileName, Abc_TtStore_t * p )
{
    FILE * pFile;
    int i;
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for writing.\n", pFileName );
        return;
    }
    for ( i = 0; i < p->nFuncs; i++ )
    {
        Abc_TruthWriteHex( pFile, p->pFuncs[i], p->nVars );
        fprintf( pFile, "\n" );
    }
    fclose( pFile );
}


/**Function*************************************************************

  Synopsis    [Read truth tables from input file and write them into output file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_TtStore_t * Abc_TtStoreLoad( char * pFileName )
{ 
    Abc_TtStore_t * p;
    char * pFileInput  = pFileName;
    int nVars, nTruths;

    // figure out how many truth table and how many variables
    Abc_TruthGetParams( pFileInput, &nVars, &nTruths );
    if ( nVars < 2 || nVars > 16 || nTruths == 0 )
        return NULL;

    // allocate data-structure
    p = Abc_TruthStoreAlloc( nVars, nTruths );

    // read info from file
    Abc_TruthStoreRead( pFileInput, p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Read truth tables from input file and write them into output file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TtStoreTest( char * pFileName )
{ 
    Abc_TtStore_t * p;
    char * pFileInput  = pFileName;
    char * pFileOutput = "out.txt";

    // read info from file
    p = Abc_TtStoreLoad( pFileInput );
    if ( p == NULL )
        return;

    // write into another file
    Abc_TtStoreWrite( pFileOutput, p );

    // delete data-structure
    Abc_TtStoreFree( p );
    printf( "Input file \"%s\" was copied into output file \"%s\".\n", pFileInput, pFileOutput );
}

/**Function*************************************************************

  Synopsis    [Apply decomposition to the truth table.]

  Description [Returns the number of AIG nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TruthDecPerform( Abc_TtStore_t * p, int DecType, int fVerbose )
{
    clock_t clk = clock();
    int i, nNodes = 0;

    char * pAlgoName = NULL;
    if ( DecType == 1 )
        pAlgoName = "factoring";
    else if ( DecType == 2 )
        pAlgoName = "bi-decomp";
    else if ( DecType == 3 )
        pAlgoName = "DSD";

    if ( pAlgoName )
        printf( "Applying %-10s to %8d func%s of %2d vars...  ",  
            pAlgoName, p->nFuncs, (p->nFuncs == 1 ? "":"s"), p->nVars );
    if ( fVerbose )
        printf( "\n" );

    if ( DecType == 1 )
    {
        // perform algebraic factoring and count AIG nodes
        Dec_Graph_t * pFForm;
        Vec_Int_t * vCover;
        Vec_Str_t * vStr;
        char * pSopStr;
        vStr = Vec_StrAlloc( 10000 );
        vCover = Vec_IntAlloc( 1 << 16 );
        for ( i = 0; i < p->nFuncs; i++ )
        {
            if ( fVerbose )
                printf( "%7d : ", i );
            pSopStr = Kit_PlaFromTruthNew( (unsigned *)p->pFuncs[i], p->nVars, vCover, vStr );
            pFForm = Dec_Factor( pSopStr );
            nNodes += Dec_GraphNodeNum( pFForm );
            if ( fVerbose )
                Dec_GraphPrint( stdout, pFForm, NULL, NULL );
            Dec_GraphFree( pFForm );
        }
        Vec_IntFree( vCover );
        Vec_StrFree( vStr );
    }
    else if ( DecType == 2 )
    {
        // perform bi-decomposition and count AIG nodes
        Bdc_Man_t * pManDec;
        Bdc_Par_t Pars = {0}, * pPars = &Pars;
        pPars->nVarsMax = p->nVars;
        pManDec = Bdc_ManAlloc( pPars );
        for ( i = 0; i < p->nFuncs; i++ )
        {
            if ( fVerbose )
                printf( "%7d :      ", i );
            Bdc_ManDecompose( pManDec, (unsigned *)p->pFuncs[i], NULL, p->nVars, NULL, 1000 );
            nNodes += Bdc_ManAndNum( pManDec );
            if ( fVerbose )
                Bdc_ManDecPrint( pManDec );
        }
        Bdc_ManFree( pManDec );
    }
    else if ( DecType == 3 )
    {
        // perform disjoint-support decomposition and count AIG nodes
        // (non-DSD blocks are decomposed into 2:1 MUXes, each counting as 3 AIG nodes)
        Kit_DsdNtk_t * pNtk;
        for ( i = 0; i < p->nFuncs; i++ )
        {
            if ( fVerbose )
                printf( "%7d :      ", i );
            pNtk = Kit_DsdDecomposeMux( (unsigned *)p->pFuncs[i], p->nVars, 3 );
            if ( fVerbose )
                Kit_DsdPrintExpanded( pNtk ), printf( "\n" );
            nNodes += Kit_DsdCountAigNodes( pNtk );
            Kit_DsdNtkFree( pNtk );
        }
    }
    else assert( 0 );

    printf( "AIG nodes =%9d  ", nNodes );
    Abc_PrintTime( 1, "Time", clock() - clk );
}

/**Function*************************************************************

  Synopsis    [Apply decomposition to truth tables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TruthDecTest( char * pFileName, int DecType, int fVerbose )
{
    Abc_TtStore_t * p;
    int nVars, nTruths;

    // figure out how many truth tables and how many variables
    Abc_TruthGetParams( pFileName, &nVars, &nTruths );
    if ( nVars < 2 || nVars > 16 || nTruths == 0 )
        return;

    // allocate data-structure
    p = Abc_TruthStoreAlloc( nVars, nTruths );

    // read info from file
    Abc_TruthStoreRead( pFileName, p );

    // consider functions from the file
    Abc_TruthDecPerform( p, DecType, fVerbose );

    // delete data-structure
    Abc_TtStoreFree( p );
//    printf( "Finished decomposing truth tables from file \"%s\".\n", pFileName );
}


/**Function*************************************************************

  Synopsis    [Testbench for decomposition algorithms.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_DecTest( char * pFileName, int DecType, int fVerbose )
{
    if ( fVerbose )
        printf( "Using truth tables from file \"%s\"...\n", pFileName );
    if ( DecType == 0 )
        Abc_TtStoreTest( pFileName );
    else if ( DecType >= 1 && DecType <= 3 )
        Abc_TruthDecTest( pFileName, DecType, fVerbose );
    else
        printf( "Unknown decomposition type value (%d).\n", DecType );
    fflush( stdout );
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

