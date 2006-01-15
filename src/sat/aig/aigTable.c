/**CFile****************************************************************

  FileName    [aigTable.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigTable.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the hash table 
struct Aig_Table_t_
{
    Aig_Node_t **    pBins;         // the table bins
    int              nBins;         // the size of the table
    int              nEntries;      // the total number of entries in the table
};

// iterators through the entries in the linked lists of nodes
#define Aig_TableBinForEachEntry( pBin, pEnt )                 \
    for ( pEnt = pBin;                                         \
          pEnt;                                                \
          pEnt = pEnt->NextH? Aig_ManNode(pEnt->pMan, pEnt->NextH) : NULL )
#define Aig_TableBinForEachEntrySafe( pBin, pEnt, pEnt2 )      \
    for ( pEnt = pBin,                                         \
          pEnt2 = pEnt? Aig_NodeNextH(pEnt) : NULL;            \
          pEnt;                                                \
          pEnt = pEnt2,                                        \
          pEnt2 = pEnt? Aig_NodeNextH(pEnt) : NULL )

// hash key for the structural hash table
static inline unsigned Abc_HashKey2( Aig_Node_t * p0, Aig_Node_t * p1, int TableSize ) { return ((unsigned)(p0) + (unsigned)(p1) * 12582917) % TableSize; }
//static inline unsigned Abc_HashKey2( Aig_Node_t * p0, Aig_Node_t * p1, int TableSize ) { return ((unsigned)((a)->Id + (b)->Id) * ((a)->Id + (b)->Id + 1) / 2) % TableSize; }

static unsigned int Cudd_PrimeAig( unsigned int  p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Table_t * Aig_TableCreate( int nSize )
{
    Aig_Table_t * p;
    // allocate the table
    p = ALLOC( Aig_Table_t, 1 );
    memset( p, 0, sizeof(Aig_Table_t) );
    // allocate and clean the bins
    p->nBins = Cudd_PrimeAig(nSize);
    p->pBins = ALLOC( Aig_Node_t *, p->nBins );
    memset( p->pBins, 0, sizeof(Aig_Node_t *) * p->nBins );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the supergate hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableFree( Aig_Table_t * p )
{
    FREE( p->pBins );
    FREE( p );
}

/**Function*************************************************************

  Synopsis    [Returns the number of nodes in the table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_TableNumNodes( Aig_Table_t * p )
{
    return p->nEntries;
}

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_TableLookupNode( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1 )
{
    Aig_Node_t * pAnd;
    unsigned Key;
    assert( Aig_Regular(p0)->Id < Aig_Regular(p1)->Id );
    assert( p0->pMan == p1->pMan );
    // get the hash key for these two nodes
    Key = Abc_HashKey2( p0, p1, pMan->pTable->nBins );
    // find the matching node in the table
    Aig_TableBinForEachEntry( pMan->pTable->pBins[Key], pAnd )
        if ( p0 == Aig_NodeChild0(pAnd) && p1 == Aig_NodeChild1(pAnd) )
             return pAnd;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_TableInsertNode( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1, Aig_Node_t * pAnd )
{
    unsigned Key;
    assert( Aig_Regular(p0)->Id < Aig_Regular(p1)->Id );
    // check if it is a good time for table resizing
    if ( pMan->pTable->nEntries > 2 * pMan->pTable->nBins )
        Aig_TableResize( pMan );
    // add the node to the corresponding linked list in the table
    Key = Abc_HashKey2( p0, p1, pMan->pTable->nBins );
    pAnd->NextH = pMan->pTable->pBins[Key]->Id;
    pMan->pTable->pBins[Key]->NextH = pAnd->Id;
    pMan->pTable->nEntries++;
    return pAnd;
}


/**Function*************************************************************

  Synopsis    [Deletes an AIG node from the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableDeleteNode( Aig_Man_t * pMan, Aig_Node_t * pThis )
{
    Aig_Node_t * pAnd, * pPlace = NULL;
    unsigned Key;
    assert( !Aig_IsComplement(pThis) );
    assert( Aig_NodeIsAnd(pThis) );
    assert( pMan == pThis->pMan );
    // get the hash key for these two nodes
    Key = Abc_HashKey2( Aig_NodeChild0(pThis), Aig_NodeChild1(pThis), pMan->pTable->nBins );
    // find the matching node in the table
    Aig_TableBinForEachEntry( pMan->pTable->pBins[Key], pAnd )
    {
        if ( pThis != pAnd )
        {
            pPlace = pAnd;
            continue;
        }
        if ( pPlace == NULL )
            pMan->pTable->pBins[Key] = Aig_NodeNextH(pThis);
        else
            pPlace->NextH = pThis->Id;
        break;
    }
    assert( pThis == pAnd );
    pMan->pTable->nEntries--;
}

/**Function*************************************************************

  Synopsis    [Resizes the hash table of AIG nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableResize( Aig_Man_t * pMan )
{
    Aig_Node_t ** pBinsNew;
    Aig_Node_t * pEnt, * pEnt2;
    int nBinsNew, Counter, i, clk;
    unsigned Key;

clk = clock();
    // get the new table size
    nBinsNew = Cudd_PrimeCopy( 3 * pMan->pTable->nBins ); 
    // allocate a new array
    pBinsNew = ALLOC( Aig_Node_t *, nBinsNew );
    memset( pBinsNew, 0, sizeof(Aig_Node_t *) * nBinsNew );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < pMan->pTable->nBins; i++ )
        Aig_TableBinForEachEntrySafe( pMan->pTable->pBins[i], pEnt, pEnt2 )
        {
            Key = Abc_HashKey2( Aig_NodeChild0(pEnt), Aig_NodeChild1(pEnt), nBinsNew );
            pEnt->NextH = pBinsNew[Key]->Id;
            pBinsNew[Key]->NextH = pEnt->Id;
            Counter++;
        }
    assert( Counter == pMan->pTable->nEntries );
//    printf( "Increasing the structural table size from %6d to %6d. ", pMan->nBins, nBinsNew );
//    PRT( "Time", clock() - clk );
    // replace the table and the parameters
    free( pMan->pTable->pBins );
    pMan->pTable->pBins = pBinsNew;
    pMan->pTable->nBins = nBinsNew;
}

/**Function*************************************************************

  Synopsis    [Resizes the hash table of AIG nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableRehash( Aig_Man_t * pMan )
{
    Aig_Node_t ** pBinsNew;
    Aig_Node_t * pEnt, * pEnt2;
    unsigned Key;
    int Counter, Temp, i;
    // allocate a new array
    pBinsNew = ALLOC( Aig_Node_t *, pMan->pTable->nBins );
    memset( pBinsNew, 0, sizeof(Aig_Node_t *) * pMan->pTable->nBins );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < pMan->pTable->nBins; i++ )
        Aig_TableBinForEachEntrySafe( pMan->pTable->pBins[i], pEnt, pEnt2 )
        {
            // swap the fanins if needed
            if ( pEnt->Fans[0].iNode > pEnt->Fans[1].iNode )
            {
                Temp = pEnt->Fans[0].iNode;
                pEnt->Fans[0].iNode = pEnt->Fans[1].iNode;
                pEnt->Fans[1].iNode = Temp;
                Temp = pEnt->Fans[0].fComp;
                pEnt->Fans[0].fComp = pEnt->Fans[1].fComp;
                pEnt->Fans[1].fComp = Temp;
           }
            // rehash the node
            Key = Abc_HashKey2( Aig_NodeChild0(pEnt), Aig_NodeChild1(pEnt), pMan->pTable->nBins );
            pEnt->NextH = pBinsNew[Key]->Id;
            pBinsNew[Key]->NextH = pEnt->Id;
            Counter++;
        }
    assert( Counter == pMan->pTable->nEntries );
    // replace the table and the parameters
    free( pMan->pTable->pBins );
    pMan->pTable->pBins = pBinsNew;
}

/**Function*************************************************************

  Synopsis    [Returns the smallest prime larger than the number.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned int Cudd_PrimeAig( unsigned int p )
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


