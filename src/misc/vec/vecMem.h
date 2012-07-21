/**CFile****************************************************************

  FileName    [vecMem.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resizable arrays.]

  Synopsis    [Resizable array of memory pieces.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 20, 2012.]

  Revision    [$Id: vecMem.h,v 1.00 2012/07/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__misc__vec__vecMem_h
#define ABC__misc__vec__vecMem_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>

ABC_NAMESPACE_HEADER_START

/* 
   This vector stores pieces of memory of the given size.
   It is useful for representing truth tables and any other objects
   of the fixed size.  It is better that Extra_MmFixed because the
   entry IDs can be used as handles to retrieve memory pieces without 
   the need for an array of pointers from entry IDs into memory pieces
   (this can save 8(4) bytes per object on a 64(32)-bit platform).
*/

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Vec_Mem_t_       Vec_Mem_t;
struct Vec_Mem_t_ 
{
    int              nEntrySize;  // entry size (in terms of 8-byte words)
    int              nEntries;    // number of entries currently used
    int              LogPageSze;  // log2 of page size (in terms of entries)
    int              PageMask;    // page mask
    int              nPageAlloc;  // number of pages currently allocated
    int              iPage;       // the number of a page currently used   
    word **          ppPages;     // memory pages
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define Vec_MemForEachEntry( vVec, pEntry, i )                                              \
    for ( i = 0; (i < Vec_MemEntryNum(vVec)) && ((pEntry) = Vec_MemReadEntry(vVec, i)); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates a memory vector.]

  Description [Entry size is in terms of 8-byte words. Page size is log2
  of the number of entries on one page.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Mem_t * Vec_MemAlloc( int nEntrySize, int LogPageSze )
{
    Vec_Mem_t * p;
    p = ABC_CALLOC( Vec_Mem_t, 1 );
    p->nEntrySize = nEntrySize;
    p->LogPageSze = LogPageSze;
    p->PageMask   = (1 << p->LogPageSze) - 1;
    p->iPage      = -1;
    return p;
}
static inline void Vec_MemFree( Vec_Mem_t * p )
{
    int i;
    for ( i = 0; i <= p->iPage; i++ )
        ABC_FREE( p->ppPages[i] );
    ABC_FREE( p->ppPages );
    ABC_FREE( p );
}
static inline void Vec_MemFreeP( Vec_Mem_t ** p )
{
    if ( *p == NULL )
        return;
    Vec_MemFree( *p );
    *p = NULL;
}
static inline Vec_Mem_t * Vec_MemDup( Vec_Mem_t * pVec )
{
    Vec_Mem_t * p = NULL;
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicates the integer array.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_MemFill( Vec_Mem_t * pVec, int nEntries )
{
}
static inline void Vec_MemClean( Vec_Mem_t * pVec, int nEntries )
{
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_MemEntrySize( Vec_Mem_t * p )
{
    return p->nEntrySize;
}
static inline int Vec_MemEntryNum( Vec_Mem_t * p )
{
    return p->nEntries;
}
static inline int Vec_MemPageSize( Vec_Mem_t * p )
{
    return p->LogPageSze;
}
static inline int Vec_MemPageNum( Vec_Mem_t * p )
{
    return p->iPage+1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline double Vec_MemMemory( Vec_Mem_t * p )
{
    return (double)sizeof(word) * p->nEntrySize * (1 << p->LogPageSze) * (p->iPage + 1) + (double)sizeof(word *) * p->nPageAlloc + (double)sizeof(Vec_Mem_t);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word * Vec_MemReadEntry( Vec_Mem_t * p, int i )
{
    assert( i >= 0 && i < p->nEntries );
    return p->ppPages[i >> p->LogPageSze] + p->nEntrySize * (i & p->PageMask);
}
static inline word * Vec_MemReadEntryLast( Vec_Mem_t * p )
{
    assert( p->nEntries > 0 );
    return Vec_MemReadEntry( p, p->nEntries-1 );
}
static inline void Vec_MemWriteEntry( Vec_Mem_t * p, int i, word * pEntry )
{
    word * pPlace = Vec_MemReadEntry( p, i );
    memmove( pPlace, pEntry, sizeof(word) * p->nEntrySize );
}
static inline word * Vec_MemGetEntry( Vec_Mem_t * p, int i )
{
    assert( i >= 0 );
    if ( i >= p->nEntries )
    {
        int k, iPageNew = (i >> p->LogPageSze);
        if ( p->iPage < iPageNew )
        {
            // realloc page pointers if needed
            if ( iPageNew >= p->nPageAlloc )
                p->ppPages = ABC_REALLOC( word *, p->ppPages, (p->nPageAlloc = p->nPageAlloc ? 2 * p->nPageAlloc : iPageNew + 32) );
            // allocate new pages if needed
            for ( k = p->iPage + 1; k <= iPageNew; k++ )
                p->ppPages[k] = ABC_ALLOC( word, p->nEntrySize * (1 << p->LogPageSze) );
            // update page counter
            p->iPage = iPageNew;
        }
        // update entry counter
        p->nEntries = i + 1;
    }
    return Vec_MemReadEntry( p, i );
}
static inline void Vec_MemSetEntry( Vec_Mem_t * p, int i, word * pEntry )
{
    word * pPlace = Vec_MemGetEntry( p, i );
    memmove( pPlace, pEntry, sizeof(word) * p->nEntrySize );
}
static inline void Vec_MemPush( Vec_Mem_t * p, word * pEntry )
{
    word * pPlace = Vec_MemGetEntry( p, p->nEntries );
    memmove( pPlace, pEntry, sizeof(word) * p->nEntrySize );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_MemShrink( Vec_Mem_t * p, int nEntriesNew )
{
    int i, iPageOld = p->iPage;
    assert( nEntriesNew <= p->nEntries );
    p->nEntries = nEntriesNew;
    p->iPage = (nEntriesNew >> p->LogPageSze);
    for ( i = p->iPage + 1; i <= iPageOld; i++ )
        ABC_FREE( p->ppPages[i] );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_MemPrint( Vec_Mem_t * vVec )
{
    word * pEntry;
    int i;
    printf( "Memory vector has %d entries: ", Vec_MemEntryNum(vVec) );
    Vec_MemForEachEntry( vVec, pEntry, i )
    {
        printf( "%3d : ", i );
        // add printout here
        printf( "\n" );
    }
}


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

