/**CFile****************************************************************

  FileName    [abcNpn.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures for testing and comparing semi-canonical forms.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcNpn.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "misc/extra/extra.h"
#include "misc/vec/vec.h"

#include "bool/kit/kit.h"
#include "bool/lucky/lucky.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
// semi-canonical form types
// 0 - none
// 1 - based on counting 1s in cofactors
// 2 - based on minimum truth table value
// 3 - exact NPN

// data-structure to store a bunch of truth tables
typedef struct Abc_TtStore_t_  Abc_TtStore_t;
struct Abc_TtStore_t_ 
{
    int               nVars;
    int               nWords;
    int               nFuncs;
    word **           pFuncs;
};

extern Abc_TtStore_t * Abc_TruthStoreLoad( char * pFileName );
extern void            Abc_TruthStoreFree( Abc_TtStore_t * p );
extern void            Abc_TruthStoreTest( char * pFileName );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts the number of unique truth tables.]

  Description []
               
  SideEffects [] 

  SeeAlso     []

***********************************************************************/
int nWords = 0; // unfortunate global variable
int Abc_TruthCompare( word * p1, word * p2 ) { return memcmp(p1, p2, sizeof(word) * nWords); }
int Abc_TruthNpnCountUnique( Abc_TtStore_t * p )
{
    int i, nUnique;
    // sort them by value
    nWords = p->nWords;
    assert( nWords > 0 );
    qsort( (void *)p->pFuncs[0], p->nFuncs, nWords * sizeof(word), (int(*)(const void *,const void *))Abc_TruthCompare );
    // count the number of unqiue functions
    nUnique = p->nFuncs;
    for ( i = 1; i < p->nFuncs; i++ )
        if ( !memcmp( p->pFuncs[i-1], p->pFuncs[i], sizeof(word) * nWords ) )
            nUnique--;
    return nUnique;
}

/**Function*************************************************************

  Synopsis    [Apply decomposition to the truth table.]

  Description [Returns the number of AIG nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TruthNpnPerform( Abc_TtStore_t * p, int NpnType, int fVerbose )
{
    short pStore[16];
    char pCanonPerm[16];
    unsigned pAux[2048];

    clock_t clk = clock();
    int i, nFuncs = 0;

    char * pAlgoName = NULL;
    if ( NpnType == 1 )
        pAlgoName = "counting 1s  ";
    else if ( NpnType == 2 )
        pAlgoName = "minimizing TT";
    else if ( NpnType == 3 )
        pAlgoName = "exact NPN    ";

    assert( p->nVars <= 16 );
    if ( pAlgoName )
        printf( "Applying %-10s to %8d func%s of %2d vars...  ",  
            pAlgoName, p->nFuncs, (p->nFuncs == 1 ? "":"s"), p->nVars );
    if ( fVerbose )
        printf( "\n" );

    if ( NpnType == 1 )
    {
        for ( i = 0; i < p->nFuncs; i++ )
        {
            if ( fVerbose )
                printf( "%7d : ", i );
            Kit_TruthSemiCanonicize( (unsigned *)p->pFuncs[i], pAux, p->nVars, pCanonPerm, pStore );
            if ( fVerbose )
                Extra_PrintHex( stdout, (unsigned *)p->pFuncs[i], p->nVars ), printf( "\n" );
        }
    }
    else if ( NpnType == 2 )
    {
        for ( i = 0; i < p->nFuncs; i++ )
        {
            if ( fVerbose )
                printf( "%7d : ", i );
            Kit_TruthSemiCanonicize_new( (unsigned *)p->pFuncs[i], pAux, p->nVars, pCanonPerm );
            if ( fVerbose )
                Extra_PrintHex( stdout, (unsigned *)p->pFuncs[i], p->nVars ), printf( "\n" );
        }
    }
    else if ( NpnType == 3 )
    {
        int * pComp = Extra_GreyCodeSchedule( p->nVars );
        int * pPerm = Extra_PermSchedule( p->nVars );
        if ( p->nVars == 6 )
        {
            for ( i = 0; i < p->nFuncs; i++ )
            {
                if ( fVerbose )
                    printf( "%7d : ", i );
                *((word *)p->pFuncs[i]) = Extra_Truth6Minimum( *((word *)p->pFuncs[i]), pComp, pPerm );
                if ( fVerbose )
                    Extra_PrintHex( stdout, (unsigned *)p->pFuncs[i], p->nVars ), printf( "\n" );
            }
        }
        else
            printf( "This feature only works for 6-variable functions.\n" );
        ABC_FREE( pComp );
        ABC_FREE( pPerm );
    }
    else assert( 0 );

    clk = clock() - clk;
    printf( "Classes =%9d  ", Abc_TruthNpnCountUnique(p) );
    Abc_PrintTime( 1, "Time", clk );
}

/**Function*************************************************************

  Synopsis    [Apply decomposition to truth tables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_TruthNpnTest( char * pFileName, int NpnType, int fVerbose )
{
    Abc_TtStore_t * p;

    // read info from file
    p = Abc_TruthStoreLoad( pFileName );
    if ( p == NULL )
        return;

    // consider functions from the file
    Abc_TruthNpnPerform( p, NpnType, fVerbose );

    // delete data-structure
    Abc_TruthStoreFree( p );
//    printf( "Finished computing canonical forms for functions from file \"%s\".\n", pFileName );
}


/**Function*************************************************************

  Synopsis    [Testbench for decomposition algorithms.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NpnTest( char * pFileName, int NpnType, int fVerbose )
{
    if ( fVerbose )
        printf( "Using truth tables from file \"%s\"...\n", pFileName );
    if ( NpnType == 0 )
        Abc_TruthStoreTest( pFileName );
    else if ( NpnType >= 1 && NpnType <= 3 )
        Abc_TruthNpnTest( pFileName, NpnType, fVerbose );
    else
        printf( "Unknown canonical form value (%d).\n", NpnType );
    fflush( stdout );
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

