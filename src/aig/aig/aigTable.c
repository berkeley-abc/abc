/**CFile****************************************************************

  FileName    [aigTable.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Structural hashing table.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigTable.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

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
    Aig_Obj_t ** ppEntry;
    if ( Aig_ObjIsLatch(pObj) )
    {
        assert( Aig_ObjChild0(pObj) && Aig_ObjChild1(pObj) == NULL );
    }
    else
    {
        assert( Aig_ObjChild0(pObj) && Aig_ObjChild1(pObj) );
        assert( Aig_ObjFanin0(pObj)->Id < Aig_ObjFanin1(pObj)->Id );
    }
    for ( ppEntry = p->pTable + Aig_Hash(pObj, p->nTableSize); *ppEntry; ppEntry = &(*ppEntry)->pNext )
        if ( *ppEntry == pObj )
            return ppEntry;
    assert( *ppEntry == NULL );
    return ppEntry;
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
    Aig_Obj_t * pEntry;
    assert( !Aig_IsComplement(pGhost) );
    if ( pGhost->Type == AIG_OBJ_LATCH )
    {
        assert( Aig_ObjChild0(pGhost) && Aig_ObjChild1(pGhost) == NULL );
        if ( !Aig_ObjRefs(Aig_ObjFanin0(pGhost)) )
            return NULL;
    }
    else
    {
        assert( pGhost->Type == AIG_OBJ_AND );
        assert( Aig_ObjChild0(pGhost) && Aig_ObjChild1(pGhost) );
        assert( Aig_ObjFanin0(pGhost)->Id < Aig_ObjFanin1(pGhost)->Id );
        if ( !Aig_ObjRefs(Aig_ObjFanin0(pGhost)) || !Aig_ObjRefs(Aig_ObjFanin1(pGhost)) )
            return NULL;
    }
    for ( pEntry = p->pTable[Aig_Hash(pGhost, p->nTableSize)]; pEntry; pEntry = pEntry->pNext )
    {
        if ( Aig_ObjChild0(pEntry) == Aig_ObjChild0(pGhost) && 
             Aig_ObjChild1(pEntry) == Aig_ObjChild1(pGhost) && 
             Aig_ObjType(pEntry) == Aig_ObjType(pGhost) )
            return pEntry;
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
    if ( (pObj->Id & 0xFF) == 0 && 2 * p->nTableSize < Aig_ManNodeNum(p) )
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
    Aig_Obj_t ** ppPlace;
    assert( !Aig_IsComplement(pObj) );
    ppPlace = Aig_TableFind( p, pObj );
    assert( *ppPlace == pObj ); // node should be in the table
    // remove the node
    *ppPlace = pObj->pNext;
    pObj->pNext = NULL;
}

/**Function*************************************************************

  Synopsis    [Count the number of nodes in the table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_TableCountEntries( Aig_Man_t * p )
{
    Aig_Obj_t * pEntry;
    int i, Counter = 0;
    for ( i = 0; i < p->nTableSize; i++ )
        for ( pEntry = p->pTable[i]; pEntry; pEntry = pEntry->pNext )
            Counter++;
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
    Aig_Obj_t * pEntry, * pNext;
    Aig_Obj_t ** pTableOld, ** ppPlace;
    int nTableSizeOld, Counter, nEntries, i, clk;
clk = clock();
    // save the old table
    pTableOld = p->pTable;
    nTableSizeOld = p->nTableSize;
    // get the new table
    p->nTableSize = Cudd_PrimeAig( 2 * Aig_ManNodeNum(p) ); 
    p->pTable = ALLOC( Aig_Obj_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Aig_Obj_t *) * p->nTableSize );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < nTableSizeOld; i++ )
    for ( pEntry = pTableOld[i], pNext = pEntry? pEntry->pNext : NULL; pEntry; pEntry = pNext, pNext = pEntry? pEntry->pNext : NULL )
    {
        // get the place where this entry goes in the table 
        ppPlace = Aig_TableFind( p, pEntry );
        assert( *ppPlace == NULL ); // should not be there
        // add the entry to the list
        *ppPlace = pEntry;
        pEntry->pNext = NULL;
        Counter++;
    }
    nEntries = Aig_ManNodeNum(p);
    assert( Counter == nEntries );
    printf( "Increasing the structural table size from %6d to %6d. ", nTableSizeOld, p->nTableSize );
    PRT( "Time", clock() - clk );
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
    Aig_Obj_t * pEntry;
    int i, Counter;
    for ( i = 0; i < p->nTableSize; i++ )
    {
        Counter = 0;
        for ( pEntry = p->pTable[i]; pEntry; pEntry = pEntry->pNext )
            Counter++;
        if ( Counter ) 
            printf( "%d ", Counter );
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


