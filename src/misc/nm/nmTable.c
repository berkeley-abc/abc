/**CFile****************************************************************

  FileName    [nmTable.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Name manager.]

  Synopsis    [Hash table for the name manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nmTable.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "nmInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// hashing for integers
static unsigned Nm_HashNumber( int Num, int TableSize ) 
{
    unsigned Key = 0;
    Key ^= ( Num        & 0xFF) * 7937;
    Key ^= ((Num >>  8) & 0xFF) * 2971;
    Key ^= ((Num >> 16) & 0xFF) * 911;
    Key ^= ((Num >> 24) & 0xFF) * 353;
    return Key % TableSize;
}

// hashing for strings
static unsigned Nm_HashString( char * pName, int TableSize ) 
{
    static int s_Primes[10] = { 
        1291, 1699, 2357, 4177, 5147, 
        5647, 6343, 7103, 7873, 8147
    };
    unsigned i, Key = 0;
    for ( i = 0; pName[i] != '\0'; i++ )
        Key ^= s_Primes[i%10]*pName[i]*pName[i];
    return Key % TableSize;
}

static void Nm_ManResize( Nm_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Adds an entry to two hash tables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nm_ManTableAdd( Nm_Man_t * p, Nm_Entry_t * pEntry )
{
    int i;
    // resize the tables if needed
    if ( p->nEntries * p->nSizeFactor > p->nBins )
    {
//        Nm_ManPrintTables( p );
        Nm_ManResize( p );
    }
    // hash it by ID
    for ( i = Nm_HashNumber(pEntry->ObjId, p->nBins); p->pBinsI2N[i]; i = (i+1) % p->nBins )
        if ( p->pBinsI2N[i] == pEntry )
            return 0;
    assert( p->pBinsI2N[i] == NULL );
    p->pBinsI2N[i] = pEntry;
    // hash it by Name
    for ( i = Nm_HashString(pEntry->Name, p->nBins); p->pBinsN2I[i]; i = (i+1) % p->nBins )
        if ( p->pBinsN2I[i] == pEntry )
            return 0;
    assert( p->pBinsN2I[i] == NULL );
    p->pBinsN2I[i] = pEntry;
    // report successfully added entry
    p->nEntries++;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Deletes the entry from two hash tables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nm_ManTableDelete( Nm_Man_t * p, Nm_Entry_t * pEntry )
{
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Looks up the entry by ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nm_Entry_t * Nm_ManTableLookupId( Nm_Man_t * p, int ObjId )
{
    int i;
    for ( i = Nm_HashNumber(ObjId, p->nBins); p->pBinsI2N[i]; i = (i+1) % p->nBins )
        if ( p->pBinsI2N[i]->ObjId == ObjId )
            return p->pBinsI2N[i];
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Looks up the entry by name. May return two entries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nm_Entry_t * Nm_ManTableLookupName( Nm_Man_t * p, char * pName, Nm_Entry_t ** ppSecond )
{
    Nm_Entry_t * pFirst, * pSecond;
    int i, Counter = 0;
    pFirst = pSecond = NULL;
    for ( i = Nm_HashString(pName, p->nBins); p->pBinsN2I[i]; i = (i+1) % p->nBins )
        if ( strcmp(p->pBinsN2I[i]->Name, pName) == 0 )
        {
            if ( pFirst == NULL )
                pFirst = p->pBinsN2I[i];
            else if ( pSecond == NULL )
                pSecond = p->pBinsN2I[i];
            else
                assert( 0 ); // name appears more than 2 times
        }
        else
            Counter++;
    if ( Counter > 100 )
    printf( "%d ", Counter );
    // save the names
    if ( ppSecond )
        *ppSecond = pSecond;
    return pFirst;
}


/**Function*************************************************************

  Synopsis    [Resizes the table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nm_ManResize( Nm_Man_t * p )
{
    Nm_Entry_t ** pBinsNewI2N, ** pBinsNewN2I, * pEntry;
    int nBinsNew, Counter, e, i, clk;

clk = clock();
    // get the new table size
    nBinsNew = Cudd_PrimeCopy( p->nGrowthFactor * p->nBins ); 
    // allocate a new array
    pBinsNewI2N = ALLOC( Nm_Entry_t *, nBinsNew );
    pBinsNewN2I = ALLOC( Nm_Entry_t *, nBinsNew );
    memset( pBinsNewI2N, 0, sizeof(Nm_Entry_t *) * nBinsNew );
    memset( pBinsNewN2I, 0, sizeof(Nm_Entry_t *) * nBinsNew );
    // rehash the entries from the old table
    Counter = 0;
    for ( e = 0; e < p->nBins; e++ )
    {
        pEntry = p->pBinsI2N[e];
        if ( pEntry == NULL )
            continue;
        Counter++;

        // hash it by ID
        for ( i = Nm_HashNumber(pEntry->ObjId, nBinsNew); pBinsNewI2N[i]; i = (i+1) % nBinsNew )
            if ( pBinsNewI2N[i] == pEntry )
                assert( 0 );
        assert( pBinsNewI2N[i] == NULL );
        pBinsNewI2N[i] = pEntry;
        // hash it by Name
        for ( i = Nm_HashString(pEntry->Name, nBinsNew); pBinsNewN2I[i]; i = (i+1) % nBinsNew )
            if ( pBinsNewN2I[i] == pEntry )
                assert( 0 );
        assert( pBinsNewN2I[i] == NULL );
        pBinsNewN2I[i] = pEntry;
    }
    assert( Counter == p->nEntries );
//    printf( "Increasing the structural table size from %6d to %6d. ", p->nBins, nBinsNew );
//    PRT( "Time", clock() - clk );
    // replace the table and the parameters
    free( p->pBinsI2N );
    free( p->pBinsN2I );
    p->pBinsI2N = pBinsNewI2N;
    p->pBinsN2I = pBinsNewN2I;
    p->nBins = nBinsNew;
}



/**Function*************************************************************

  Synopsis    [Returns the smallest prime larger than the number.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned int Cudd_PrimeNm( unsigned int  p)
{
    int i,pn;

    p--;
    do {
        p++;
        if (p&1) {
        pn = 1;
        i = 3;
        while ((unsigned) (i * i) <= p) {
        if (p % i == 0) {
            pn = 0;
            break;
        }
        i += 2;
        }
    } else {
        pn = 0;
    }
    } while (!pn);
    return(p);

} /* end of Cudd_Prime */

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


