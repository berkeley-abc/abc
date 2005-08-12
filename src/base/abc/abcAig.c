/**CFile****************************************************************

  FileName    [abcAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Simple structural hashing package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcAig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the simple AIG manager
struct Abc_Aig_t_
{
    Abc_Ntk_t *       pAig;          // the AIG network
    Abc_Obj_t *       pConst1;       // the constant 1 node
    Abc_Obj_t **      pBins;         // the table bins
    int               nBins;         // the size of the table
    int               nEntries;      // the total number of entries in the table
    Vec_Ptr_t *       vNodes;        // the temporary array of nodes
};

// iterators through the entries in the linked lists of nodes
#define Abc_AigBinForEachEntry( pBin, pEnt )                   \
    for ( pEnt = pBin;                                         \
          pEnt;                                                \
          pEnt = pEnt->pNext )
#define Abc_AigBinForEachEntrySafe( pBin, pEnt, pEnt2 )        \
    for ( pEnt = pBin,                                         \
          pEnt2 = pEnt? pEnt->pNext: NULL;                     \
          pEnt;                                                \
          pEnt = pEnt2,                                        \
          pEnt2 = pEnt? pEnt->pNext: NULL )

// hash key for the structural hash table
static inline unsigned Abc_HashKey2( Abc_Obj_t * p0, Abc_Obj_t * p1, int TableSize ) { return ((unsigned)(p0) + (unsigned)(p1) * 12582917) % TableSize; }
//static inline unsigned Abc_HashKey2( Abc_Obj_t * p0, Abc_Obj_t * p1, int TableSize ) { return ((unsigned)((a)->Id + (b)->Id) * ((a)->Id + (b)->Id + 1) / 2) % TableSize; }

// static hash table procedures
static void Abc_AigResize( Abc_Aig_t * pMan );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the local AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Aig_t * Abc_AigAlloc( Abc_Ntk_t * pNtkAig )
{
    Abc_Aig_t * pMan;
    // start the manager
    pMan = ALLOC( Abc_Aig_t, 1 );
    memset( pMan, 0, sizeof(Abc_Aig_t) );
    // allocate the table
    pMan->nBins    = Cudd_PrimeCopy( 10000 );
    pMan->pBins    = ALLOC( Abc_Obj_t *, pMan->nBins );
    memset( pMan->pBins, 0, sizeof(Abc_Obj_t *) * pMan->nBins );
    pMan->vNodes   = Vec_PtrAlloc( 100 );
    // save the current network
    pMan->pAig     = pNtkAig;
    pMan->pConst1  = Abc_NtkCreateNode( pNtkAig );    
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Deallocates the local AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_AigFree( Abc_Aig_t * pMan )
{
    // free the table
    Vec_PtrFree( pMan->vNodes );
    free( pMan->pBins );
    free( pMan );
}

/**Function*************************************************************

  Synopsis    [Read the constant 1 node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigConst1( Abc_Aig_t * pMan )  
{ 
    return pMan->pConst1; 
} 

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigAnd( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 )
{
    Abc_Obj_t * pAnd;
    unsigned Key;
    // check for trivial cases
    if ( p0 == p1 )
        return p0;
    if ( p0 == Abc_ObjNot(p1) )
        return Abc_ObjNot(pMan->pConst1);
    if ( Abc_ObjRegular(p0) == pMan->pConst1 )
    {
        if ( p0 == pMan->pConst1 )
            return p1;
        return Abc_ObjNot(pMan->pConst1);
    }
    if ( Abc_ObjRegular(p1) == pMan->pConst1 )
    {
        if ( p1 == pMan->pConst1 )
            return p0;
        return Abc_ObjNot(pMan->pConst1);
    }
    // order the arguments
    if ( Abc_ObjRegular(p0)->Id > Abc_ObjRegular(p1)->Id )
        pAnd = p0, p0 = p1, p1 = pAnd;
    // get the hash key for these two nodes
    Key = Abc_HashKey2( p0, p1, pMan->nBins );
    // find the mataching node in the table
    Abc_AigBinForEachEntry( pMan->pBins[Key], pAnd )
        if ( Abc_ObjFanin0(pAnd)  == Abc_ObjRegular(p0) && 
             Abc_ObjFanin1(pAnd)  == Abc_ObjRegular(p1) &&  
             Abc_ObjFaninC0(pAnd) == Abc_ObjIsComplement(p0) && 
             Abc_ObjFaninC1(pAnd) == Abc_ObjIsComplement(p1) )
             return pAnd;
    // check if it is a good time for table resizing
    if ( pMan->nEntries > 2 * pMan->nBins )
    {
        Abc_AigResize( pMan );
        Key = Abc_HashKey2( p0, p1, pMan->nBins );
    }
    // create the new node
    pAnd = Abc_NtkCreateNode( pMan->pAig );
    Abc_ObjAddFanin( pAnd, p0 );
    Abc_ObjAddFanin( pAnd, p1 );
    // set the level of the new node
    pAnd->Level      = 1 + ABC_MAX( Abc_ObjRegular(p0)->Level, Abc_ObjRegular(p1)->Level ); 
    // add the node to the corresponding linked list in the table
    pAnd->pNext      = pMan->pBins[Key];
    pMan->pBins[Key] = pAnd;
    pMan->nEntries++;
    return pAnd;
}

/**Function*************************************************************

  Synopsis    [Implements Boolean AND.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigOr( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 )
{
    return Abc_ObjNot( Abc_AigAnd( pMan, Abc_ObjNot(p0), Abc_ObjNot(p1) ) );
}

/**Function*************************************************************

  Synopsis    [Implements Boolean AND.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigXor( Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1 )
{
    return Abc_AigOr( pMan, Abc_AigAnd(pMan, p0, Abc_ObjNot(p1)), 
                            Abc_AigAnd(pMan, p1, Abc_ObjNot(p0)) );
}

/**Function*************************************************************

  Synopsis    [Implements the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_AigMiter( Abc_Aig_t * pMan, Vec_Ptr_t * vPairs )
{
    Abc_Obj_t * pMiter, * pXor;
    int i;
    assert( vPairs->nSize % 2 == 0 );
    // go through the cubes of the node's SOP
    pMiter = Abc_ObjNot(pMan->pConst1);
    for ( i = 0; i < vPairs->nSize; i += 2 )
    {
        pXor   = Abc_AigXor( pMan, vPairs->pArray[i], vPairs->pArray[i+1] );
        pMiter = Abc_AigOr( pMan, pMiter, pXor );
    }
    return pMiter;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node has at least one complemented fanout.]

  Description [A fanout is complemented if the fanout's fanin edge pointing
  to the given node is complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_AigNodeHasComplFanoutEdge( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout;
    int i, iFanin;
    Abc_ObjForEachFanout( pNode, pFanout, i )
    {
        iFanin = Vec_FanFindEntry( &pFanout->vFanins, pNode->Id );
        assert( iFanin >= 0 );
        if ( Abc_ObjFaninC( pFanout, iFanin ) )
            return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node has at least one complemented fanout.]

  Description [A fanout is complemented if the fanout's fanin edge pointing
  to the given node is complemented. Only the fanouts with current TravId
  are counted.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_AigNodeHasComplFanoutEdgeTrav( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout;
    int i, iFanin;
    Abc_ObjForEachFanout( pNode, pFanout, i )
    {
        if ( !Abc_NodeIsTravIdCurrent(pFanout) )
            continue;
        iFanin = Vec_FanFindEntry( &pFanout->vFanins, pNode->Id );
        assert( iFanin >= 0 );
        if ( Abc_ObjFaninC( pFanout, iFanin ) )
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
void Abc_AigResize( Abc_Aig_t * pMan )
{
    Abc_Obj_t ** pBinsNew;
    Abc_Obj_t * pEnt, * pEnt2;
    int nBinsNew, Counter, i, clk;
    unsigned Key;

clk = clock();
    // get the new table size
    nBinsNew = Cudd_PrimeCopy(2 * pMan->nBins); 
    // allocate a new array
    pBinsNew = ALLOC( Abc_Obj_t *, nBinsNew );
    memset( pBinsNew, 0, sizeof(Abc_Obj_t *) * nBinsNew );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < pMan->nBins; i++ )
        Abc_AigBinForEachEntrySafe( pMan->pBins[i], pEnt, pEnt2 )
        {
            Key = Abc_HashKey2( Abc_ObjFanin(pEnt,0), Abc_ObjFanin(pEnt,1), nBinsNew );
            pEnt->pNext   = pBinsNew[Key];
            pBinsNew[Key] = pEnt;
            Counter++;
        }
    assert( Counter == pMan->nEntries );
//    printf( "Increasing the structural table size from %6d to %6d. ", pMan->nBins, nBinsNew );
//    PRT( "Time", clock() - clk );
    // replace the table and the parameters
    free( pMan->pBins );
    pMan->pBins = pBinsNew;
    pMan->nBins = nBinsNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


