/**CFile****************************************************************

  FileName    [cutTable.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [K-feasible cut computation package.]

  Synopsis    [Hashing cuts to prevent duplication.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cutTable.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cutInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

struct Cut_HashTableStruct_t_
{
    int                  nBins;
    Cut_Cut_t **         pBins;
    int                  nEntries;
    int *                pPlaces;
    int                  nPlaces;
    int                  timeLookup;
};

// iterator through all the cuts of the list
#define Cut_TableListForEachCut( pList, pCut )               \
    for ( pCut = pList;                                      \
          pCut;                                              \
          pCut = pCut->pData )
#define Cut_TableListForEachCutSafe( pList, pCut, pCut2 )    \
    for ( pCut = pList,                                      \
          pCut2 = pCut? pCut->pData: NULL;                   \
          pCut;                                              \
          pCut = pCut2,                                      \
          pCut2 = pCut? pCut->pData: NULL )

// primes used to compute the hash key
static int s_HashPrimes[10] = { 109, 499, 557, 619, 631, 709, 797, 881, 907, 991 };

// hashing function
static inline unsigned Cut_HashKey( Cut_Cut_t * pCut )
{
    unsigned i, uRes = pCut->nLeaves * s_HashPrimes[9];
    for ( i = 0; i < pCut->nLeaves + pCut->fSeq; i++ )
        uRes += s_HashPrimes[i] * pCut->pLeaves[i];
    return uRes;
}

// hashing function
static inline int Cut_CompareTwo( Cut_Cut_t * pCut1, Cut_Cut_t * pCut2 )
{
    unsigned i;
    if ( pCut1->nLeaves != pCut2->nLeaves )
        return 1;
    for ( i = 0; i < pCut1->nLeaves; i++ )
        if ( pCut1->pLeaves[i] != pCut2->pLeaves[i] )
            return 1;
    return 0;
}

static void Cut_TableResize( Cut_HashTable_t * pTable );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_HashTable_t * Cut_TableStart( int Size )
{
    Cut_HashTable_t * pTable;
    pTable = ALLOC( Cut_HashTable_t, 1 );
    memset( pTable, 0, sizeof(Cut_HashTable_t) );
    // allocate the table
    pTable->nBins = Cudd_PrimeCopy( Size );
    pTable->pBins = ALLOC( Cut_Cut_t *, pTable->nBins );
    memset( pTable->pBins, 0, sizeof(Cut_Cut_t *) * pTable->nBins );
    pTable->pPlaces = ALLOC( int, pTable->nBins );
    return pTable;
}

/**Function*************************************************************

  Synopsis    [Stops the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_TableStop( Cut_HashTable_t * pTable )
{
    FREE( pTable->pPlaces );
    free( pTable->pBins );
    free( pTable );
}

/**Function*************************************************************

  Synopsis    [Check the existence of a cut in the lookup table]

  Description [Returns 1 if the entry is found.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cut_TableLookup( Cut_HashTable_t * pTable, Cut_Cut_t * pCut, int fStore )
{
    Cut_Cut_t * pEnt;
    unsigned Key;
    int clk = clock();

    Key = Cut_HashKey(pCut) % pTable->nBins; 
    Cut_TableListForEachCut( pTable->pBins[Key], pEnt )
    {
        if ( !Cut_CompareTwo( pEnt, pCut ) )
        {
pTable->timeLookup += clock() - clk;
            return 1;
        }
    }
    if ( pTable->nEntries > 2 * pTable->nBins )
    {
        Cut_TableResize( pTable );
        Key = Cut_HashKey(pCut) % pTable->nBins; 
    }
    // remember the place
    if ( fStore && pTable->pBins[Key] == NULL )
        pTable->pPlaces[ pTable->nPlaces++ ] = Key;
    // add the cut to the table
    pCut->pData = pTable->pBins[Key];
    pTable->pBins[Key] = pCut;
    pTable->nEntries++;
pTable->timeLookup += clock() - clk;
    return 0;
}


/**Function*************************************************************

  Synopsis    [Stops the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_TableClear( Cut_HashTable_t * pTable )
{
    int i;
    assert( pTable->nPlaces <= pTable->nBins );
    for ( i = 0; i < pTable->nPlaces; i++ )
    {
        assert( pTable->pBins[ pTable->pPlaces[i] ] );
        pTable->pBins[ pTable->pPlaces[i] ] = NULL;
    }
    pTable->nPlaces = 0;
    pTable->nEntries = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_TableResize( Cut_HashTable_t * pTable )
{
    Cut_Cut_t ** pBinsNew;
    Cut_Cut_t * pEnt, * pEnt2;
    int nBinsNew, Counter, i, clk;
    unsigned Key;

clk = clock();
    // get the new table size
    nBinsNew = Cudd_PrimeCopy( 3 * pTable->nBins ); 
    // allocate a new array
    pBinsNew = ALLOC( Cut_Cut_t *, nBinsNew );
    memset( pBinsNew, 0, sizeof(Cut_Cut_t *) * nBinsNew );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < pTable->nBins; i++ )
        Cut_TableListForEachCutSafe( pTable->pBins[i], pEnt, pEnt2 )
        {
            Key = Cut_HashKey(pEnt) % nBinsNew;
            pEnt->pData   = pBinsNew[Key];
            pBinsNew[Key] = pEnt;
            Counter++;
        }
    assert( Counter == pTable->nEntries );
//    printf( "Increasing the structural table size from %6d to %6d. ", pMan->nBins, nBinsNew );
//    PRT( "Time", clock() - clk );
    // replace the table and the parameters
    free( pTable->pBins );
    pTable->pBins = pBinsNew;
    pTable->nBins = nBinsNew;
}

/**Function*************************************************************

  Synopsis    [Stops the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cut_TableReadTime( Cut_HashTable_t * pTable )
{
    if ( pTable == NULL )
        return 0;
    return pTable->timeLookup;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


