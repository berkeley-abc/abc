/**CFile****************************************************************

  FileName    [esop.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cover manipulation package.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: esop.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __ESOP_H__
#define __ESOP_H__

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include "vec.h"
#include "mem.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Esop_Man_t_      Esop_Man_t;
typedef struct Esop_Cube_t_     Esop_Cube_t;
typedef struct Mem_Fixed_t_  Mem_Fixed_t;    

struct Esop_Man_t_
{
    int               nVars;          // the number of vars
    int               nWords;         // the number of words
    Mem_Fixed_t *     pMemMan1;       // memory manager for cubes
    Mem_Fixed_t *     pMemMan2;       // memory manager for cubes
    Mem_Fixed_t *     pMemMan4;       // memory manager for cubes
    Mem_Fixed_t *     pMemMan8;       // memory manager for cubes
    // temporary cubes
    Esop_Cube_t *     pOne0;          // tautology cube
    Esop_Cube_t *     pOne1;          // tautology cube
    Esop_Cube_t *     pTriv0;         // trivial cube
    Esop_Cube_t *     pTriv1;         // trivial cube
    Esop_Cube_t *     pTemp;          // cube for computing the distance
    Esop_Cube_t *     pBubble;        // cube used as a separator
    // temporary storage for the new cover
    int               nCubes;         // the number of cubes
    Esop_Cube_t **    ppStore;        // storage for cubes by number of literals
};

struct Esop_Cube_t_
{
    Esop_Cube_t *     pNext;          // the pointer to the next cube in the cover
    unsigned          nVars    : 10;  // the number of variables
    unsigned          nWords   : 12;  // the number of machine words
    unsigned          nLits    : 10;  // the number of literals in the cube
    unsigned          uData[1];       // the bit-data for the cube
};

#define ALLOC(type, num)     ((type *) malloc(sizeof(type) * (num)))
#define FREE(obj)             ((obj) ? (free((char *) (obj)), (obj) = 0) : 0)
#define REALLOC(type, obj, num)    \
        ((obj) ? ((type *) realloc((char *)(obj), sizeof(type) * (num))) : \
         ((type *) malloc(sizeof(type) * (num))))

// iterators through the entries in the linked lists of cubes
#define Esop_CoverForEachCube( pCover, pCube )                  \
    for ( pCube = pCover;                                       \
          pCube;                                                \
          pCube = pCube->pNext )
#define Esop_CoverForEachCubeSafe( pCover, pCube, pCube2 )      \
    for ( pCube = pCover,                                       \
          pCube2 = pCube? pCube->pNext: NULL;                   \
          pCube;                                                \
          pCube = pCube2,                                       \
          pCube2 = pCube? pCube->pNext: NULL )
#define Esop_CoverForEachCubePrev( pCover, pCube, ppPrev )      \
    for ( pCube = pCover,                                       \
          ppPrev = &(pCover);                                   \
          pCube;                                                \
          ppPrev = &pCube->pNext,                               \
          pCube = pCube->pNext )


// macros to get hold of bits and values in the cubes
static inline int    Esop_CubeHasBit( Esop_Cube_t * p, int i )              { return (p->uData[i >> 5] & (1<<(i & 31))) > 0;         }
static inline void   Esop_CubeSetBit( Esop_Cube_t * p, int i )              { p->uData[i >> 5] |= (1<<(i & 31));                     }
static inline void   Esop_CubeXorBit( Esop_Cube_t * p, int i )              { p->uData[i >> 5] ^= (1<<(i & 31));                     }
static inline int    Esop_CubeGetVar( Esop_Cube_t * p, int Var )            { return 3 & (p->uData[(Var<<1)>>5] >> ((Var<<1) & 31)); }
static inline void   Esop_CubeXorVar( Esop_Cube_t * p, int Var, int Value ) { p->uData[(Var<<1)>>5] ^= (Value<<((Var<<1) & 31));     }
static inline int    Esop_BitWordNum( int nBits )                           { return (nBits>>5) + ((nBits&31) > 0);                  }

/*=== esopMem.c ===========================================================*/
extern Mem_Fixed_t * Mem_FixedStart( int nEntrySize );
extern void          Mem_FixedStop( Mem_Fixed_t * p, int fVerbose );
extern char *        Mem_FixedEntryFetch( Mem_Fixed_t * p );
extern void          Mem_FixedEntryRecycle( Mem_Fixed_t * p, char * pEntry );
extern void          Mem_FixedRestart( Mem_Fixed_t * p );
extern int           Mem_FixedReadMemUsage( Mem_Fixed_t * p );
/*=== esopMin.c ===========================================================*/
extern void          Esop_EsopMinimize( Esop_Man_t * p );
extern void          Esop_EsopAddCube( Esop_Man_t * p, Esop_Cube_t * pCube );
/*=== esopMan.c ===========================================================*/
extern Esop_Man_t *  Esop_ManAlloc( int nVars );
extern void          Esop_ManClean( Esop_Man_t * p, int nSupp );
extern void          Esop_ManFree( Esop_Man_t * p );
/*=== esopUtil.c ===========================================================*/
extern void          Esop_CubeWrite( FILE * pFile, Esop_Cube_t * pCube );
extern void          Esop_CoverWrite( FILE * pFile, Esop_Cube_t * pCover );
extern void          Esop_CoverWriteStore( FILE * pFile, Esop_Man_t * p );
extern void          Esop_CoverWriteFile( Esop_Cube_t * pCover, char * pName, int fEsop );
extern void          Esop_CoverCheck( Esop_Man_t * p );
extern int           Esop_CubeCheck( Esop_Cube_t * pCube );
extern Esop_Cube_t * Esop_CoverCollect( Esop_Man_t * p, int nSuppSize );
extern void          Esop_CoverExpand( Esop_Man_t * p, Esop_Cube_t * pCover );
extern int           Esop_CoverSuppVarNum( Esop_Man_t * p, Esop_Cube_t * pCover );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Creates the cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Esop_Cube_t * Esop_CubeAlloc( Esop_Man_t * p )
{
    Esop_Cube_t * pCube;
    if ( p->nWords <= 1 )
        pCube = (Esop_Cube_t *)Mem_FixedEntryFetch( p->pMemMan1 );
    else if ( p->nWords <= 2 )
        pCube = (Esop_Cube_t *)Mem_FixedEntryFetch( p->pMemMan2 );
    else if ( p->nWords <= 4 )
        pCube = (Esop_Cube_t *)Mem_FixedEntryFetch( p->pMemMan4 );
    else if ( p->nWords <= 8 )
        pCube = (Esop_Cube_t *)Mem_FixedEntryFetch( p->pMemMan8 );
    pCube->pNext  = NULL;
    pCube->nVars  = p->nVars;
    pCube->nWords = p->nWords;
    pCube->nLits  = 0;
    memset( pCube->uData, 0xff, sizeof(unsigned) * p->nWords );
    return pCube;
}

/**Function*************************************************************

  Synopsis    [Creates the cube representing elementary var.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Esop_Cube_t * Esop_CubeAllocVar( Esop_Man_t * p, int iVar, int fCompl )
{
    Esop_Cube_t * pCube;
    pCube = Esop_CubeAlloc( p );
    Esop_CubeXorBit( pCube, iVar*2+fCompl );
    pCube->nLits = 1;
    return pCube;
}

/**Function*************************************************************

  Synopsis    [Creates the cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Esop_Cube_t * Esop_CubeDup( Esop_Man_t * p, Esop_Cube_t * pCopy )
{
    Esop_Cube_t * pCube;
    pCube = Esop_CubeAlloc( p );
    memcpy( pCube->uData, pCopy->uData, sizeof(unsigned) * p->nWords );
    pCube->nLits = pCopy->nLits;
    return pCube;
}

/**Function*************************************************************

  Synopsis    [Recycles the cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Esop_CubeRecycle( Esop_Man_t * p, Esop_Cube_t * pCube )
{
    if ( pCube->nWords <= 1 )
        Mem_FixedEntryRecycle( p->pMemMan1, (char *)pCube );
    else if ( pCube->nWords <= 2 )
        Mem_FixedEntryRecycle( p->pMemMan2, (char *)pCube );
    else if ( pCube->nWords <= 4 )
        Mem_FixedEntryRecycle( p->pMemMan4, (char *)pCube );
    else if ( pCube->nWords <= 8 )
        Mem_FixedEntryRecycle( p->pMemMan8, (char *)pCube );
}

/**Function*************************************************************

  Synopsis    [Recycles the cube cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Esop_CoverRecycle( Esop_Man_t * p, Esop_Cube_t * pCover )
{
    Esop_Cube_t * pCube, * pCube2;
    if ( pCover == NULL )
        return;
    if ( pCover->nWords <= 1 )
        Esop_CoverForEachCubeSafe( pCover, pCube, pCube2 )
            Mem_FixedEntryRecycle( p->pMemMan1, (char *)pCube );
    else if ( pCover->nWords <= 2 )
        Esop_CoverForEachCubeSafe( pCover, pCube, pCube2 )
            Mem_FixedEntryRecycle( p->pMemMan2, (char *)pCube );
    else if ( pCover->nWords <= 4 )
        Esop_CoverForEachCubeSafe( pCover, pCube, pCube2 )
            Mem_FixedEntryRecycle( p->pMemMan4, (char *)pCube );
    else if ( pCover->nWords <= 8 )
        Esop_CoverForEachCubeSafe( pCover, pCube, pCube2 )
            Mem_FixedEntryRecycle( p->pMemMan8, (char *)pCube );
}

/**Function*************************************************************

  Synopsis    [Recycles the cube cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Esop_Cube_t * Esop_CoverDup( Esop_Man_t * p, Esop_Cube_t * pCover )
{
    Esop_Cube_t * pCube, * pCubeNew;
    Esop_Cube_t * pCoverNew = NULL, ** ppTail = &pCoverNew;
    Esop_CoverForEachCube( pCover, pCube )
    {
        pCubeNew = Esop_CubeDup( p, pCube );
        *ppTail = pCubeNew;
        ppTail = &pCubeNew->pNext;
    }
    *ppTail = NULL;
    return pCoverNew;
}


/**Function*************************************************************

  Synopsis    [Counts the number of cubes in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Esop_CubeCountLits( Esop_Cube_t * pCube )
{
    unsigned uData;
    int Count = 0, i, w;
    for ( w = 0; w < (int)pCube->nWords; w++ )
    {
        uData = pCube->uData[w] ^ (pCube->uData[w] >> 1);
        for ( i = 0; i < 32; i += 2 )
            if ( uData & (1 << i) )
                Count++;
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Counts the number of cubes in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Esop_CubeGetLits( Esop_Cube_t * pCube, Vec_Int_t * vLits )
{
    unsigned uData;
    int i, w;
    Vec_IntClear( vLits );
    for ( w = 0; w < (int)pCube->nWords; w++ )
    {
        uData = pCube->uData[w] ^ (pCube->uData[w] >> 1);
        for ( i = 0; i < 32; i += 2 )
            if ( uData & (1 << i) )
                Vec_IntPush( vLits, w*16 + i/2 );
    }
}

/**Function*************************************************************

  Synopsis    [Counts the number of cubes in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Esop_CoverCountCubes( Esop_Cube_t * pCover )
{
    Esop_Cube_t * pCube;
    int Count = 0;
    Esop_CoverForEachCube( pCover, pCube )
        Count++;
    return Count;
}


/**Function*************************************************************

  Synopsis    [Checks if two cubes are disjoint.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Esop_CubesDisjoint( Esop_Cube_t * pCube0, Esop_Cube_t * pCube1 )
{
    unsigned uData;
    int i;
    assert( pCube0->nVars == pCube1->nVars );
    for ( i = 0; i < (int)pCube0->nWords; i++ )
    {
        uData = pCube0->uData[i] & pCube1->uData[i];
        uData = (uData | (uData >> 1)) & 0x55555555;
        if ( uData != 0x55555555 )
            return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Collects the disjoint variables of the two cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Esop_CoverGetDisjVars( Esop_Cube_t * pThis, Esop_Cube_t * pCube, Vec_Int_t * vVars )
{
    unsigned uData;
    int i, w;
    Vec_IntClear( vVars );
    for ( w = 0; w < (int)pCube->nWords; w++ )
    {
        uData  = pThis->uData[w] & (pThis->uData[w] >> 1) & 0x55555555;
        uData &= (pCube->uData[w] ^ (pCube->uData[w] >> 1));
        if ( uData == 0 )
            continue;
        for ( i = 0; i < 32; i += 2 )
            if ( uData & (1 << i) )
                Vec_IntPush( vVars, w*16 + i/2 );
    }
}

/**Function*************************************************************

  Synopsis    [Checks if two cubes are disjoint.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Esop_CubesDistOne( Esop_Cube_t * pCube0, Esop_Cube_t * pCube1, Esop_Cube_t * pTemp )
{
    unsigned uData;
    int i, fFound = 0;
    for ( i = 0; i < (int)pCube0->nWords; i++ )
    {
        uData = pCube0->uData[i] ^ pCube1->uData[i];
        if ( uData == 0 )
        {
            if ( pTemp ) pTemp->uData[i] = 0;
            continue;
        }
        if ( fFound )
            return 0;
        uData = (uData | (uData >> 1)) & 0x55555555;
        if ( (uData & (uData-1)) > 0 ) // more than one 1
            return 0;
        if ( pTemp ) pTemp->uData[i] = uData | (uData << 1);
        fFound = 1;
    }
    if ( fFound == 0 )
    {
        printf( "\n" );
        Esop_CubeWrite( stdout, pCube0 );
        Esop_CubeWrite( stdout, pCube1 );
        printf( "Error: Esop_CubesDistOne() looks at two equal cubes!\n" );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks if two cubes are disjoint.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Esop_CubesDistTwo( Esop_Cube_t * pCube0, Esop_Cube_t * pCube1, int * pVar0, int * pVar1 )
{
    unsigned uData;//, uData2;
    int i, k, Var0 = -1, Var1 = -1;
    for ( i = 0; i < (int)pCube0->nWords; i++ )
    {
        uData = pCube0->uData[i] ^ pCube1->uData[i];
        if ( uData == 0 )
            continue;
        if ( Var0 >= 0 && Var1 >= 0 ) // more than two 1s
            return 0;
        uData = (uData | (uData >> 1)) & 0x55555555;
        if ( (Var0 >= 0 || Var1 >= 0) && (uData & (uData-1)) > 0 )
            return 0;
        for ( k = 0; k < 32; k += 2 )
            if ( uData & (1 << k) )
            {
                if ( Var0 == -1 )
                    Var0 = 16 * i + k/2;
                else if ( Var1 == -1 )
                    Var1 = 16 * i + k/2;
                else
                    return 0;
            }
        /*
        if ( Var0 >= 0 )
        {
            uData &= 0xFFFF;
            uData2 = (uData >> 16);
            if ( uData && uData2 )
                return 0;
            if ( uData )
            {
            }
            uData }= uData2;
            uData &= 0x
        }
        */
    }
    if ( Var0 >= 0 && Var1 >= 0 )
    {
        *pVar0 = Var0;
        *pVar1 = Var1;
        return 1;
    }
    if ( Var0 == -1 || Var1 == -1 )
    {
        printf( "\n" );
        Esop_CubeWrite( stdout, pCube0 );
        Esop_CubeWrite( stdout, pCube1 );
        printf( "Error: Esop_CubesDistTwo() looks at two equal cubes or dist1 cubes!\n" );
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Makes the produce of two cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Esop_Cube_t * Esop_CubesProduct( Esop_Man_t * p, Esop_Cube_t * pCube0, Esop_Cube_t * pCube1 )
{
    Esop_Cube_t * pCube;
    int i;
    assert( pCube0->nVars == pCube1->nVars );
    pCube = Esop_CubeAlloc( p );
    for ( i = 0; i < p->nWords; i++ )
        pCube->uData[i] = pCube0->uData[i] & pCube1->uData[i];
    pCube->nLits = Esop_CubeCountLits( pCube );
    return pCube;
}

/**Function*************************************************************

  Synopsis    [Makes the produce of two cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Esop_Cube_t * Esop_CubesXor( Esop_Man_t * p, Esop_Cube_t * pCube0, Esop_Cube_t * pCube1 )
{
    Esop_Cube_t * pCube;
    int i;
    assert( pCube0->nVars == pCube1->nVars );
    pCube = Esop_CubeAlloc( p );
    for ( i = 0; i < p->nWords; i++ )
        pCube->uData[i] = pCube0->uData[i] ^ pCube1->uData[i];
    pCube->nLits = Esop_CubeCountLits( pCube );
    return pCube;
}

/**Function*************************************************************

  Synopsis    [Makes the produce of two cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Esop_CubesAreEqual( Esop_Cube_t * pCube0, Esop_Cube_t * pCube1 )
{
    int i;
    for ( i = 0; i < (int)pCube0->nWords; i++ )
        if ( pCube0->uData[i] != pCube1->uData[i] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pCube1 is contained in pCube0, bitwise.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Esop_CubeIsContained( Esop_Cube_t * pCube0, Esop_Cube_t * pCube1 )
{
    int i;
    for ( i = 0; i < (int)pCube0->nWords; i++ )
        if ( (pCube0->uData[i] & pCube1->uData[i]) != pCube1->uData[i] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Transforms the cube into the result of merging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Esop_CubesTransform( Esop_Cube_t * pCube, Esop_Cube_t * pDist, Esop_Cube_t * pMask )
{
    int w;
    for ( w = 0; w < (int)pCube->nWords; w++ )
    {
        pCube->uData[w]  =  pCube->uData[w] ^ pDist->uData[w];
        pCube->uData[w] |= (pDist->uData[w] & ~pMask->uData[w]);
    }
}

/**Function*************************************************************

  Synopsis    [Transforms the cube into the result of distance-1 merging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Esop_CubesTransformOr( Esop_Cube_t * pCube, Esop_Cube_t * pDist )
{
    int w;
    for ( w = 0; w < (int)pCube->nWords; w++ )
        pCube->uData[w] |= pDist->uData[w];
}



/**Function*************************************************************

  Synopsis    [Sorts the cover in the increasing number of literals.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Esop_CoverExpandRemoveEqual( Esop_Man_t * p, Esop_Cube_t * pCover )
{
    Esop_Cube_t * pCube, * pCube2, * pThis;
    if ( pCover == NULL )
    {
        Esop_ManClean( p, p->nVars );
        return;
    }
    Esop_ManClean( p, pCover->nVars );
    Esop_CoverForEachCubeSafe( pCover, pCube, pCube2 )
    {
        // go through the linked list
        Esop_CoverForEachCube( p->ppStore[pCube->nLits], pThis )
            if ( Esop_CubesAreEqual( pCube, pThis ) )
            {
                Esop_CubeRecycle( p, pCube );
                break;
            }
        if ( pThis != NULL )
            continue;
        pCube->pNext = p->ppStore[pCube->nLits];
        p->ppStore[pCube->nLits] = pCube;
        p->nCubes++;
    }
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the given cube is contained in one of the cubes of the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Esop_CoverContainsCube( Esop_Man_t * p, Esop_Cube_t * pCube )
{
    Esop_Cube_t * pThis;
    int i;
/*
    // this cube cannot be equal to any cube
    Esop_CoverForEachCube( p->ppStore[pCube->nLits], pThis )
    {
        if ( Esop_CubesAreEqual( pCube, pThis ) )
        {
            Esop_CubeWrite( stdout, pCube );
            assert( 0 );
        }
    }
*/
    // try to find a containing cube
    for ( i = 0; i <= (int)pCube->nLits; i++ )
    Esop_CoverForEachCube( p->ppStore[i], pThis )
    {
        // skip the bubble
        if ( pThis != p->pBubble && Esop_CubeIsContained( pThis, pCube ) )
            return 1;
    }
    return 0;
}

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


