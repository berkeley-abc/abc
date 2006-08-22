/**CFile****************************************************************

  FileName    [aigTable.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Minimalistic And-Inverter Graph package.]

  Synopsis    [Structural hashing table.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006. ]

  Revision    [$Id: aigTable.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// hashing the node
static unsigned long Aig_Hash( Aig_Obj_t * pObj, int TableSize ) 
{
    unsigned long Key = Aig_ObjIsExor(pObj) * 1699;
    Key ^= (long)Aig_ObjFanin0(pObj) * 7937;
    Key ^= (long)Aig_ObjFanin1(pObj) * 2971;
    Key ^= Aig_ObjFaninC0(pObj) * 911;
    Key ^= Aig_ObjFaninC1(pObj) * 353;
    return Key % TableSize;
}

// returns the place where this node is stored (or should be stored)
static Aig_Obj_t ** Aig_TableFind( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    int i;
    assert( Aig_ObjChild0(pObj) && Aig_ObjChild1(pObj) );
    assert( Aig_ObjChild0(pObj) <  Aig_ObjChild1(pObj) );
    for ( i = Aig_Hash(pObj, p->nTableSize); p->pTable[i]; i = (i+1) % p->nTableSize )
        if ( p->pTable[i] == pObj )
            break;
    return p->pTable + i;
}

static void         Aig_TableResize( Aig_Man_t * p );
static unsigned int Cudd_PrimeAig( unsigned int  p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Checks if node with the given attributes is in the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_TableLookup( Aig_Man_t * p, Aig_Obj_t * pGhost )
{
    int i;
    assert( !Aig_IsComplement(pGhost) );
    assert( Aig_ObjChild0(pGhost) && Aig_ObjChild1(pGhost) );
    assert( Aig_ObjChild0(pGhost) <  Aig_ObjChild1(pGhost) );
    if ( p->fRefCount && (!Aig_ObjRefs(Aig_ObjFanin0(pGhost)) || !Aig_ObjRefs(Aig_ObjFanin1(pGhost))) )
        return NULL;
    for ( i = Aig_Hash(pGhost, p->nTableSize); p->pTable[i]; i = (i+1) % p->nTableSize )
    {
        if ( Aig_ObjChild0(p->pTable[i]) == Aig_ObjChild0(pGhost) && 
             Aig_ObjChild1(p->pTable[i]) == Aig_ObjChild1(pGhost) && 
             Aig_ObjType(p->pTable[i]) == Aig_ObjType(pGhost) )
            return p->pTable[i];
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Adds the new node to the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableInsert( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t ** ppPlace;
    assert( !Aig_IsComplement(pObj) );
    assert( Aig_TableLookup(p, pObj) == NULL );
    if ( p->nTableSize < 2 * Aig_ManNodeNum(p) )
        Aig_TableResize( p );
    ppPlace = Aig_TableFind( p, pObj );
    assert( *ppPlace == NULL );
    *ppPlace = pObj;
}

/**Function*************************************************************

  Synopsis    [Deletes the node from the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableDelete( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pEntry, ** ppPlace;
    int i;
    assert( !Aig_IsComplement(pObj) );
    ppPlace = Aig_TableFind( p, pObj );
    assert( *ppPlace == pObj ); // node should be in the table
    *ppPlace = NULL;
    // rehash the adjacent entries
    i = ppPlace - p->pTable;
    for ( i = (i+1) % p->nTableSize; p->pTable[i]; i = (i+1) % p->nTableSize )
    {
        pEntry = p->pTable[i];
        p->pTable[i] = 0;
        Aig_TableInsert( p, pEntry );
    }
}

/**Function*************************************************************

  Synopsis    [Count the number of nodes in the table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_TableCountEntries( Aig_Man_t * p )
{
    int i, Counter = 0;
    for ( i = 0; i < p->nTableSize; i++ )
        Counter += (p->pTable[i] != NULL);
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Resizes the table.]

  Description [Typically this procedure should not be called.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableResize( Aig_Man_t * p )
{
    Aig_Obj_t ** pTableOld, ** ppPlace;
    int nTableSizeOld, Counter, nEntries, e, clk;
clk = clock();
    // save the old table
    pTableOld = p->pTable;
    nTableSizeOld = p->nTableSize;
    // get the new table
    p->nTableSize = Cudd_PrimeAig( 5 * Aig_ManNodeNum(p) ); 
    p->pTable = ALLOC( Aig_Obj_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Aig_Obj_t *) * p->nTableSize );
    // rehash the entries from the old table
    Counter = 0;
    for ( e = 0; e < nTableSizeOld; e++ )
    {
        if ( pTableOld[e] == 0 )
            continue;
        Counter++;
        // get the place where this entry goes in the table table
        ppPlace = Aig_TableFind( p, pTableOld[e] );
        assert( *ppPlace == NULL ); // should not be in the table
        *ppPlace = pTableOld[e];
    }
    nEntries = Aig_ManNodeNum(p);
//    assert( Counter == nEntries );
//    printf( "Increasing the structural table size from %6d to %6d. ", nTableSizeOld, p->nTableSize );
//    PRT( "Time", clock() - clk );
    // replace the table and the parameters
    free( pTableOld );
}

/**Function********************************************************************

  Synopsis    [Profiles the hash table.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Aig_TableProfile( Aig_Man_t * p )
{
    int i, Counter = 0;
    for ( i = 0; i < p->nTableSize; i++ )
    {
        if ( p->pTable[i] )
            Counter++;
        else if ( Counter )
        {
            printf( "%d ", Counter );
            Counter = 0;
        }
    }
}

/**Function********************************************************************

  Synopsis    [Returns the next prime &gt;= p.]

  Description [Copied from CUDD, for stand-aloneness.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
unsigned int Cudd_PrimeAig( unsigned int  p)
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


