/**CFile****************************************************************

  FileName    [pdrUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdrUtil.c,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdrInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs fast mapping for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_IntSelectSort( int * pArray, int nSize )
{
    int temp, i, j, best_i;
    for ( i = 0; i < nSize-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < nSize; j++ )
            if ( pArray[j] < pArray[best_i] )
                best_i = j;
        temp = pArray[i]; 
        pArray[i] = pArray[best_i]; 
        pArray[best_i] = temp;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetCreate( Vec_Int_t * vLits, Vec_Int_t * vPiLits )
{
    Pdr_Set_t * p;
    int i;
    assert( Vec_IntSize(vLits) + Vec_IntSize(vPiLits) < (1<<15) );
    p = (Pdr_Set_t *)ABC_ALLOC( char, sizeof(Pdr_Set_t) + (Vec_IntSize(vLits) + Vec_IntSize(vPiLits)) * sizeof(int) );
    p->nLits  = Vec_IntSize(vLits);
    p->nTotal = Vec_IntSize(vLits) + Vec_IntSize(vPiLits);
    p->nRefs  = 1;
    p->Sign   = 0;
    for ( i = 0; i < p->nLits; i++ )
    {
        p->Lits[i] = Vec_IntEntry(vLits, i);
        p->Sign   |= ((word)1 << (p->Lits[i] % 63));
    }
    Vec_IntSelectSort( p->Lits, p->nLits );
/*
    for ( i = 0; i < p->nLits; i++ )
        printf( "%d ", p->Lits[i] );
    printf( "\n" );
*/
    // remember PI literals 
    for ( i = p->nLits; i < p->nTotal; i++ )
        p->Lits[i] = Vec_IntEntry(vPiLits, i-p->nLits);
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetCreateFrom( Pdr_Set_t * pSet, int iRemove )
{
    Pdr_Set_t * p;
    int i, k = 0;
    assert( iRemove >= 0 && iRemove < pSet->nLits );
    p = (Pdr_Set_t *)ABC_ALLOC( char, sizeof(Pdr_Set_t) + (pSet->nTotal - 1) * sizeof(int) );
    p->nLits  = pSet->nLits - 1;
    p->nTotal = pSet->nTotal - 1;
    p->nRefs  = 1;
    p->Sign   = 0;
    for ( i = 0; i < pSet->nTotal; i++ )
    {
        if ( i == iRemove )
            continue;
        p->Lits[k++] = pSet->Lits[i];
        if ( i >= pSet->nLits )
            continue;
        p->Sign   |= ((word)1 << (pSet->Lits[i] % 63));
    }
    assert( k == p->nTotal );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetCreateSubset( Pdr_Set_t * pSet, int * pLits, int nLits )
{
    Pdr_Set_t * p;
    int i, k = 0;
    assert( nLits >= 0 && nLits <= pSet->nLits );
    p = (Pdr_Set_t *)ABC_ALLOC( char, sizeof(Pdr_Set_t) + (nLits + pSet->nTotal - pSet->nLits) * sizeof(int) );
    p->nLits  = nLits;
    p->nTotal = nLits + pSet->nTotal - pSet->nLits;
    p->nRefs  = 1;
    p->Sign   = 0;
    for ( i = 0; i < nLits; i++ )
    {
        assert( pLits[i] >= 0 );
        p->Lits[k++] = pLits[i];
        p->Sign   |= ((word)1 << (pLits[i] % 63));
    }
    Vec_IntSelectSort( p->Lits, p->nLits );
    for ( i = pSet->nLits; i < pSet->nTotal; i++ )
        p->Lits[k++] = pSet->Lits[i];
    assert( k == p->nTotal );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetDup( Pdr_Set_t * pSet )
{
    Pdr_Set_t * p;
    int i;
    p = (Pdr_Set_t *)ABC_ALLOC( char, sizeof(Pdr_Set_t) + pSet->nTotal * sizeof(int) );
    p->nLits  = pSet->nLits;
    p->nTotal = pSet->nTotal;
    p->nRefs  = 1;
    p->Sign   = pSet->Sign;
    for ( i = 0; i < pSet->nTotal; i++ )
        p->Lits[i] = pSet->Lits[i];
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t * Pdr_SetRef( Pdr_Set_t * p )
{
    p->nRefs++;
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_SetDeref( Pdr_Set_t * p )
{
    if ( --p->nRefs == 0 )
        ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_SetPrint( FILE * pFile, Pdr_Set_t * p, int nRegs, Vec_Int_t * vFlopCounts )
{
    char * pBuff;
    int i, k, Entry;
    pBuff = ABC_ALLOC( char, nRegs + 1 );
    for ( i = 0; i < nRegs; i++ )
        pBuff[i] = '-';
    pBuff[i] = 0;
    for ( i = 0; i < p->nLits; i++ )
    {
        if ( p->Lits[i] == -1 )
            continue;
        pBuff[lit_var(p->Lits[i])] = (lit_sign(p->Lits[i])? '0':'1');
    }
    if ( vFlopCounts )
    {
        // skip some literals
        k = 0;
        Vec_IntForEachEntry( vFlopCounts, Entry, i )
            if ( Entry ) 
                pBuff[k++] = pBuff[i];
        pBuff[k] = 0;
    }
    fprintf( pFile, "%s", pBuff );
    ABC_FREE( pBuff );
}

/**Function*************************************************************

  Synopsis    [Return 1 if pOld set-theoretically contains pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_SetContains( Pdr_Set_t * pOld, Pdr_Set_t * pNew )
{
    int * pOldInt, * pNewInt;
    assert( pOld->nLits > 0 );
    assert( pNew->nLits > 0 );
    if ( pOld->nLits < pNew->nLits )
        return 0;
    if ( (pOld->Sign & pNew->Sign) != pNew->Sign )
        return 0;
    pOldInt = pOld->Lits + pOld->nLits - 1;
    pNewInt = pNew->Lits + pNew->nLits - 1;
    while ( pNew->Lits <= pNewInt )
    {
        if ( pOld->Lits > pOldInt )
            return 0;
        assert( *pNewInt != -1 );
        assert( *pOldInt != -1 );
        if ( *pNewInt == *pOldInt )
            pNewInt--, pOldInt--;
        else if ( *pNewInt < *pOldInt )
            pOldInt--;
        else
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Return 1 if the state cube contains init state (000...0).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_SetIsInit( Pdr_Set_t * pCube, int iRemove )
{
    int i;
    for ( i = 0; i < pCube->nLits; i++ )
    {
        assert( pCube->Lits[i] != -1 );
        if ( i == iRemove )
            continue;
        if ( lit_sign( pCube->Lits[i] ) == 0 )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_SetCompare( Pdr_Set_t ** pp1, Pdr_Set_t ** pp2 )
{
    Pdr_Set_t * p1 = *pp1;
    Pdr_Set_t * p2 = *pp2;
    int i;
    for ( i = 0; i < p1->nLits && i < p2->nLits; i++ )
    {
        if ( p1->Lits[i] > p2->Lits[i] )
            return -1;
        if ( p1->Lits[i] < p2->Lits[i] )
            return 1;
    }
    if ( i == p1->nLits && i < p2->nLits )
        return -1;
    if ( i < p1->nLits && i == p2->nLits )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Obl_t * Pdr_OblStart( int k, int prio, Pdr_Set_t * pState, Pdr_Obl_t * pNext )
{
    Pdr_Obl_t * p;
    p = ABC_ALLOC( Pdr_Obl_t, 1 );
    p->iFrame = k;
    p->prio   = prio;
    p->nRefs  = 1;
    p->pState = pState;
    p->pNext  = pNext;
    p->pLink  = NULL;
    return p;    
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Obl_t * Pdr_OblRef( Pdr_Obl_t * p )
{
    p->nRefs++;
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_OblDeref( Pdr_Obl_t * p )
{
    if ( --p->nRefs == 0 )
    {
        if ( p->pNext )
            Pdr_OblDeref( p->pNext );
        Pdr_SetDeref( p->pState );
        ABC_FREE( p );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_QueueIsEmpty( Pdr_Man_t * p )
{
    return p->pQueue == NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Obl_t * Pdr_QueueHead( Pdr_Man_t * p )
{
    return p->pQueue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Obl_t * Pdr_QueuePop( Pdr_Man_t * p )
{
    Pdr_Obl_t * pRes = p->pQueue;
    if ( p->pQueue == NULL )
        return NULL;
    p->pQueue = p->pQueue->pLink;
    Pdr_OblDeref( pRes );
    return pRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_QueuePush( Pdr_Man_t * p, Pdr_Obl_t * pObl )
{
    Pdr_Obl_t * pTemp, ** ppPrev;
    p->nObligs++;
    Pdr_OblRef( pObl );
    if ( p->pQueue == NULL )
    {
        p->pQueue = pObl;
        return;
    }
    for ( ppPrev = &p->pQueue, pTemp = p->pQueue; pTemp; ppPrev = &pTemp->pLink, pTemp = pTemp->pLink )
        if ( pTemp->iFrame > pObl->iFrame || (pTemp->iFrame == pObl->iFrame && pTemp->prio > pObl->prio) )
            break;
    *ppPrev = pObl;
    pObl->pLink = pTemp;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_QueuePrint( Pdr_Man_t * p )
{
    Pdr_Obl_t * pObl;
    for ( pObl = p->pQueue; pObl; pObl = pObl->pLink )
        printf( "Frame = %2d.  Prio = %8d.\n", pObl->iFrame, pObl->prio );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_QueueStop( Pdr_Man_t * p )
{
    Pdr_Obl_t * pObl;
    while ( !Pdr_QueueIsEmpty(p) )
    {
        pObl = Pdr_QueuePop(p);
        Pdr_OblDeref( pObl );
    }
    p->pQueue = NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

