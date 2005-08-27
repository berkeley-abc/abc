/**CFile****************************************************************

  FileName    [vecFan.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resizable arrays.]

  Synopsis    [Resizable arrays of integers (fanins/fanouts) with memory management.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: vecFan.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __VEC_FAN_H__
#define __VEC_FAN_H__

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

typedef struct Abc_Fan_t_       Abc_Fan_t;
struct Abc_Fan_t_ // 1 word
{
    unsigned         iFan    : 24;  // the ID of the object
    unsigned         nLats   :  7;  // the number of latches (up to 31)
    unsigned         fCompl  :  1;  // the complemented attribute
};

typedef struct Vec_Fan_t_       Vec_Fan_t;
struct Vec_Fan_t_ 
{
    int              nCap;
    int              nSize;
    Abc_Fan_t *      pArray;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

#define Vec_FanForEachEntry( vVec, Entry, i )                                               \
    for ( i = 0; (i < Vec_FanSize(vVec)) && (((Entry) = Vec_FanEntry(vVec, i)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts an integer into the simple fanin structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_Fan_t Vec_Int2Fan( int iFan )
{
    return *((Abc_Fan_t *)&iFan);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_Fan_t * Vec_FanArray( Vec_Fan_t * p )
{
    return p->pArray;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_FanSize( Vec_Fan_t * p )
{
    return p->nSize;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_Fan_t Vec_FanEntry( Vec_Fan_t * p, int i )
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
static inline void Vec_FanWriteEntry( Vec_Fan_t * p, int i, Abc_Fan_t Entry )
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
static inline Abc_Fan_t Vec_FanEntryLast( Vec_Fan_t * p )
{
    return p->pArray[p->nSize-1];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_FanShrink( Vec_Fan_t * p, int nSizeNew )
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
static inline void Vec_FanClear( Vec_Fan_t * p )
{
    p->nSize = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_FanPush( Extra_MmStep_t * pMemMan, Vec_Fan_t * p, Abc_Fan_t Entry )
{
    if ( p->nSize == p->nCap )
    {
        Abc_Fan_t * pArray;
        int i;

        if ( p->nSize == 0 )
            p->nCap = 1;
        pArray = (Abc_Fan_t *)Extra_MmStepEntryFetch( pMemMan, p->nCap * 8 );
//        pArray = ALLOC( int, p->nCap * 2 );
        if ( p->pArray )
        {
            for ( i = 0; i < p->nSize; i++ )
                pArray[i] = p->pArray[i];
            Extra_MmStepEntryRecycle( pMemMan, (char *)p->pArray, p->nCap * 4 );
//            free( p->pArray );
        }
        p->nCap *= 2;
        p->pArray = pArray;
    }
    p->pArray[p->nSize++] = Entry;
}

/**Function*************************************************************

  Synopsis    [Returns the last entry and removes it from the list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_Fan_t Vec_FanPop( Vec_Fan_t * p )
{
    assert( p->nSize > 0 );
    return p->pArray[--p->nSize];
}

/**Function*************************************************************

  Synopsis    [Find entry.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_FanFindEntry( Vec_Fan_t * p, unsigned iFan )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        if ( p->pArray[i].iFan == iFan )
            return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Deletes entry.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_FanDeleteEntry( Vec_Fan_t * p, unsigned iFan )
{
/*
    int i, k, fFound = 0;
    for ( i = k = 0; i < p->nSize; i++ )
    {
        if ( p->pArray[i].iFan == iFan )
            fFound = 1;
        else
            p->pArray[k++] = p->pArray[i];
    }
    p->nSize = k;
    return fFound;
*/
    int i;
    for ( i = 0; i < p->nSize; i++ )
        if ( p->pArray[i].iFan == iFan )
            break;
    if ( i == p->nSize )
        return 0;
    for ( i++; i < p->nSize; i++ )
        p->pArray[i-1] = p->pArray[i];
    p->nSize--;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Comparison procedure for two integers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_FanSortCompare1( int * pp1, int * pp2 )
{
    // for some reason commenting out lines (as shown) led to crashing of the release version
    if ( *pp1 < *pp2 )
        return -1;
    if ( *pp1 > *pp2 ) //
        return 1;
    return 0; //
}

/**Function*************************************************************

  Synopsis    [Comparison procedure for two integers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_FanSortCompare2( int * pp1, int * pp2 )
{
    // for some reason commenting out lines (as shown) led to crashing of the release version
    if ( *pp1 > *pp2 )
        return -1;
    if ( *pp1 < *pp2 ) //
        return 1;
    return 0; //
}

/**Function*************************************************************

  Synopsis    [Sorting the entries by their integer value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_FanSort( Vec_Fan_t * p, int fReverse )
{
    if ( fReverse ) 
        qsort( (void *)p->pArray, p->nSize, sizeof(int), 
                (int (*)(const void *, const void *)) Vec_FanSortCompare2 );
    else
        qsort( (void *)p->pArray, p->nSize, sizeof(int), 
                (int (*)(const void *, const void *)) Vec_FanSortCompare1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

