/**CFile****************************************************************

  FileName    [vecRec.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resizable arrays.]

  Synopsis    [Array of records.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: vecRec.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__sat__bsat__vecRec_h
#define ABC__sat__bsat__vecRec_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>

ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// data-structure for logging entries
// memory is allocated in 'p->Mask+1' int chunks
// the first 'int' of each entry cannot be 0
typedef struct Vec_Rec_t_ Vec_Rec_t;
struct Vec_Rec_t_ 
{
    int                Mask;         // mask for the log size
    int                hCurrent;     // current position
    int                hShadow;      // current position
    int                nEntries;     // total number of entries
    int                nChunks;      // total number of chunks
    int                nChunksAlloc; // the number of allocated chunks
    int **             pChunks;      // the chunks
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

// p is vector of records
// Size is given by the user
// Handle is returned to the user
// c (chunk) and s (shift) are variables used here
#define Vec_RecForEachEntry( p, Size, Handle, c, s )   \
    for ( c = 1; c <= p->nChunks; c++ )                \
        for ( s = 0; p->pChunks[c][s] && ((Handle) = (((c)<<16)|(s))); s += Size, assert(s < p->Mask) )

#define Vec_RecForEachEntryStart( p, Size, Handle, c, s, hStart )   \
    for ( c = Vec_RecChunk(hStart), s = Vec_RecShift(hStart); c <= p->nChunks; c++, s = 0 )                \
        for ( ; p->pChunks[c][s] && ((Handle) = (((c)<<16)|(s))); s += Size, assert(s < p->Mask) )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Rec_t * Vec_RecAlloc()
{
    Vec_Rec_t * p;
    p = ABC_CALLOC( Vec_Rec_t, 1 );
    p->Mask          = (1 << 15) - 1; // chunk size = 2^15 ints = 128 Kb
    p->hCurrent      = (1 << 16);
    p->nChunks       = 1;
    p->nChunksAlloc  = 16;
    p->pChunks       = ABC_CALLOC( int *, p->nChunksAlloc );
    p->pChunks[0]    = NULL;
    p->pChunks[1]    = ABC_ALLOC( int, (1 << 16) );
    p->pChunks[1][0] = 0;
    return p;
}
static inline void Vec_RecAlloc_( Vec_Rec_t * p )
{
//    Vec_Rec_t * p;
//    p = ABC_CALLOC( Vec_Rec_t, 1 );
    memset( p, 0, sizeof(Vec_Rec_t) );
    p->Mask          = (1 << 15) - 1; // chunk size = 2^15 ints = 128 Kb
    p->hCurrent      = (1 << 16);
    p->nChunks       = 1;
    p->nChunksAlloc  = 16;
    p->pChunks       = ABC_CALLOC( int *, p->nChunksAlloc );
    p->pChunks[0]    = NULL;
    p->pChunks[1]    = ABC_ALLOC( int, (1 << 16) );
    p->pChunks[1][0] = 0;
//    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_RecChunk( int i )
{
    return i>>16;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_RecShift( int i )
{
    return i&0xFFFF;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_RecSize( Vec_Rec_t * p )
{
    return Vec_RecChunk(p->hCurrent) * (p->Mask + 1); 
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_RecEntryNum( Vec_Rec_t * p )
{
    return p->nEntries;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_RecEntry( Vec_Rec_t * p, int i )
{
    assert( i <= p->hCurrent );
    return p->pChunks[Vec_RecChunk(i)][Vec_RecShift(i)];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int * Vec_RecEntryP( Vec_Rec_t * p, int i )
{
    assert( i <= p->hCurrent );
    return p->pChunks[Vec_RecChunk(i)] + Vec_RecShift(i);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_RecRestart( Vec_Rec_t * p )
{
    p->hCurrent = (1 << 16);
    p->nChunks  = 1;
    p->nEntries = 0;
    p->pChunks[1][0] = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_RecShrink( Vec_Rec_t * p, int h )
{
    int i;
    assert( Vec_RecEntry(p, h) == 0 );
    for ( i = Vec_RecChunk(h)+1; i < p->nChunksAlloc; i++ )
        ABC_FREE( p->pChunks[i] );
    p->nChunks = Vec_RecChunk(h);
    p->hCurrent = h;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_RecFree( Vec_Rec_t * p )
{
    int i;
    for ( i = 0; i < p->nChunksAlloc; i++ )
        ABC_FREE( p->pChunks[i] );
    ABC_FREE( p->pChunks );
    ABC_FREE( p );
}
static inline void Vec_RecFree_( Vec_Rec_t * p )
{
    int i;
    for ( i = 0; i < p->nChunksAlloc; i++ )
        ABC_FREE( p->pChunks[i] );
    ABC_FREE( p->pChunks );
//    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_RecAppend( Vec_Rec_t * p, int nSize )
{
    assert( nSize <= p->Mask );
    assert( Vec_RecEntry(p, p->hCurrent) == 0 );
    assert( Vec_RecChunk(p->hCurrent) == p->nChunks );
    if ( Vec_RecShift(p->hCurrent) + nSize >= p->Mask )
    {
        if ( ++p->nChunks == p->nChunksAlloc )
        {
            p->pChunks = ABC_REALLOC( int *, p->pChunks, p->nChunksAlloc * 2 );
            memset( p->pChunks + p->nChunksAlloc, 0, sizeof(int *) * p->nChunksAlloc );
            p->nChunksAlloc *= 2;
        }
        if ( p->pChunks[p->nChunks] == NULL )
            p->pChunks[p->nChunks] = ABC_ALLOC( int, (p->Mask + 1) );
        p->pChunks[p->nChunks][0] = 0;
        p->hCurrent = p->nChunks << 16;
    }
    p->hCurrent += nSize;
    *Vec_RecEntryP(p, p->hCurrent) = 0;
    p->nEntries++;
    return p->hCurrent - nSize;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_RecPush( Vec_Rec_t * p, int * pArray, int nSize )
{
    int Handle = Vec_RecAppend( p, nSize );
    memmove( Vec_RecEntryP(p, Handle), pArray, sizeof(int) * nSize );
    return Handle;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_RecSetShadow( Vec_Rec_t * p, int hShadow )
{
    p->hShadow = hShadow;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_RecReadShadow( Vec_Rec_t * p )
{
    return p->hShadow;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_RecAppendShadow( Vec_Rec_t * p, int nSize )
{
    if ( Vec_RecShift(p->hShadow) + nSize >= p->Mask )
        p->hShadow = ((Vec_RecChunk(p->hShadow) + 1) << 16);
    p->hShadow += nSize;
    return p->hShadow - nSize;
}


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

