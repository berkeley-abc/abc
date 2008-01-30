/**CFile****************************************************************

  FileName    [vecPtr.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resizable arrays.]

  Synopsis    [Resizable arrays of generic pointers.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: vecPtr.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __VEC_PTR_H__
#define __VEC_PTR_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include "extra.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Vec_Ptr_t_       Vec_Ptr_t;
struct Vec_Ptr_t_ 
{
    int              nCap;
    int              nSize;
    void **          pArray;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

// iterators through entries
#define Vec_PtrForEachEntry( vVec, pEntry, i )                                               \
    for ( i = 0; (i < Vec_PtrSize(vVec)) && (((pEntry) = Vec_PtrEntry(vVec, i)), 1); i++ )
#define Vec_PtrForEachEntryStart( vVec, pEntry, i, Start )                                   \
    for ( i = Start; (i < Vec_PtrSize(vVec)) && (((pEntry) = Vec_PtrEntry(vVec, i)), 1); i++ )
#define Vec_PtrForEachEntryReverse( vVec, pEntry, i )                                        \
    for ( i = Vec_PtrSize(vVec) - 1; (i >= 0) && (((pEntry) = Vec_PtrEntry(vVec, i)), 1); i-- )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates a vector with the given capacity.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Ptr_t * Vec_PtrAlloc( int nCap )
{
    Vec_Ptr_t * p;
    p = ALLOC( Vec_Ptr_t, 1 );
    if ( nCap > 0 && nCap < 8 )
        nCap = 8;
    p->nSize  = 0;
    p->nCap   = nCap;
    p->pArray = p->nCap? ALLOC( void *, p->nCap ) : NULL;
    return p;
}

/**Function*************************************************************

  Synopsis    [Allocates a vector with the given size and cleans it.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Ptr_t * Vec_PtrStart( int nSize )
{
    Vec_Ptr_t * p;
    p = Vec_PtrAlloc( nSize );
    p->nSize = nSize;
    memset( p->pArray, 0, sizeof(void *) * nSize );
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates the vector from an integer array of the given size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Ptr_t * Vec_PtrAllocArray( void ** pArray, int nSize )
{
    Vec_Ptr_t * p;
    p = ALLOC( Vec_Ptr_t, 1 );
    p->nSize  = nSize;
    p->nCap   = nSize;
    p->pArray = pArray;
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates the vector from an integer array of the given size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Ptr_t * Vec_PtrAllocArrayCopy( void ** pArray, int nSize )
{
    Vec_Ptr_t * p;
    p = ALLOC( Vec_Ptr_t, 1 );
    p->nSize  = nSize;
    p->nCap   = nSize;
    p->pArray = ALLOC( void *, nSize );
    memcpy( p->pArray, pArray, sizeof(void *) * nSize );
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicates the integer array.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Ptr_t * Vec_PtrDup( Vec_Ptr_t * pVec )
{
    Vec_Ptr_t * p;
    p = ALLOC( Vec_Ptr_t, 1 );
    p->nSize  = pVec->nSize;
    p->nCap   = pVec->nCap;
    p->pArray = p->nCap? ALLOC( void *, p->nCap ) : NULL;
    memcpy( p->pArray, pVec->pArray, sizeof(void *) * pVec->nSize );
    return p;
}

/**Function*************************************************************

  Synopsis    [Transfers the array into another vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Ptr_t * Vec_PtrDupArray( Vec_Ptr_t * pVec )
{
    Vec_Ptr_t * p;
    p = ALLOC( Vec_Ptr_t, 1 );
    p->nSize  = pVec->nSize;
    p->nCap   = pVec->nCap;
    p->pArray = pVec->pArray;
    pVec->nSize  = 0;
    pVec->nCap   = 0;
    pVec->pArray = NULL;
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrFree( Vec_Ptr_t * p )
{
    FREE( p->pArray );
    FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void ** Vec_PtrReleaseArray( Vec_Ptr_t * p )
{
    void ** pArray = p->pArray;
    p->nCap = 0;
    p->nSize = 0;
    p->pArray = NULL;
    return pArray;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void ** Vec_PtrArray( Vec_Ptr_t * p )
{
    return p->pArray;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_PtrSize( Vec_Ptr_t * p )
{
    return p->nSize;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void * Vec_PtrEntry( Vec_Ptr_t * p, int i )
{
    assert( i >= 0 && i < p->nSize );
    return p->pArray[i];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrWriteEntry( Vec_Ptr_t * p, int i, void * Entry )
{
    assert( i >= 0 && i < p->nSize );
    p->pArray[i] = Entry;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void * Vec_PtrEntryLast( Vec_Ptr_t * p )
{
    return p->pArray[p->nSize-1];
}

/**Function*************************************************************

  Synopsis    [Resizes the vector to the given capacity.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrGrow( Vec_Ptr_t * p, int nCapMin )
{
    if ( p->nCap >= nCapMin )
        return;
    p->pArray = REALLOC( void *, p->pArray, nCapMin ); 
    p->nCap   = nCapMin;
}

/**Function*************************************************************

  Synopsis    [Fills the vector with given number of entries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrFill( Vec_Ptr_t * p, int nSize, void * Entry )
{
    int i;
    Vec_PtrGrow( p, nSize );
    for ( i = 0; i < nSize; i++ )
        p->pArray[i] = Entry;
    p->nSize = nSize;
}

/**Function*************************************************************

  Synopsis    [Fills the vector with given number of entries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrFillExtra( Vec_Ptr_t * p, int nSize, void * Entry )
{
    int i;
    if ( p->nSize >= nSize )
        return;
    Vec_PtrGrow( p, nSize );
    for ( i = p->nSize; i < nSize; i++ )
        p->pArray[i] = Entry;
    p->nSize = nSize;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrShrink( Vec_Ptr_t * p, int nSizeNew )
{
    assert( p->nSize >= nSizeNew );
    p->nSize = nSizeNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrClear( Vec_Ptr_t * p )
{
    p->nSize = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrPush( Vec_Ptr_t * p, void * Entry )
{
    if ( p->nSize == p->nCap )
    {
        if ( p->nCap < 16 )
            Vec_PtrGrow( p, 16 );
        else
            Vec_PtrGrow( p, 2 * p->nCap );
    }
    p->pArray[p->nSize++] = Entry;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_PtrPushUnique( Vec_Ptr_t * p, void * Entry )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        if ( p->pArray[i] == Entry )
            return 1;
    Vec_PtrPush( p, Entry );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns the last entry and removes it from the list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void * Vec_PtrPop( Vec_Ptr_t * p )
{
    assert( p->nSize > 0 );
    return p->pArray[--p->nSize];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrRemove( Vec_Ptr_t * p, void * Entry )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        if ( p->pArray[i] == Entry )
            break;
    assert( i < p->nSize );
    for ( i++; i < p->nSize; i++ )
        p->pArray[i-1] = p->pArray[i];
    p->nSize--;
}

/**Function*************************************************************

  Synopsis    [Moves the first nItems to the end.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrReorder( Vec_Ptr_t * p, int nItems )
{
    assert( nItems < p->nSize );
    Vec_PtrGrow( p, nItems + p->nSize );
    memmove( (char **)p->pArray + p->nSize, p->pArray, nItems * sizeof(void*) );
    memmove( p->pArray, (char **)p->pArray + nItems, p->nSize * sizeof(void*) );
}

/**Function*************************************************************

  Synopsis    [Sorting the entries by their integer value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrSort( Vec_Ptr_t * p, int (*Vec_PtrSortCompare)() )
{
    qsort( (void *)p->pArray, p->nSize, sizeof(void *), 
            (int (*)(const void *, const void *)) Vec_PtrSortCompare );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

