/**CFile****************************************************************

  FileName    [xyzMinSop.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cover manipulation package.]

  Synopsis    [SOP manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: xyzMinSop.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "xyzInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Min_SopRewrite( Min_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Min_SopMinimize( Min_Man_t * p )
{
    int nCubesInit, nCubesOld, nIter;
    if ( p->nCubes < 3 )
        return;
    nIter = 0;
    nCubesInit = p->nCubes;
    do {
        nCubesOld = p->nCubes;
        Min_SopRewrite( p );
        nIter++;
    }
    while ( 100.0*(nCubesOld - p->nCubes)/nCubesOld > 3.0 );

//    printf( "%d:%d->%d ", nIter, nCubesInit, p->nCubes );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Min_SopRewrite( Min_Man_t * p )
{
    Min_Cube_t * pCube, ** ppPrev;
    Min_Cube_t * pThis, ** ppPrevT;
    Min_Cube_t * pTemp;
    int v00, v01, v10, v11, Var0, Var1, Index;
    int nPairs = 0;

    // insert the bubble before the first cube
    p->pBubble->pNext = p->ppStore[0];
    p->ppStore[0] = p->pBubble;
    p->pBubble->nLits = 0;

    // go through the cubes
    while ( 1 )
    {
        // get the index of the bubble
        Index = p->pBubble->nLits;

        // find the bubble
        Min_CoverForEachCubePrev( p->ppStore[Index], pCube, ppPrev )
            if ( pCube == p->pBubble )
                break;
        assert( pCube == p->pBubble );

        // remove the bubble, get the next cube after the bubble
        *ppPrev = p->pBubble->pNext;
        pCube = p->pBubble->pNext;
        if ( pCube == NULL )
            for ( Index++; Index <= p->nVars; Index++ )
                if ( p->ppStore[Index] )
                {
                    ppPrev = &(p->ppStore[Index]);
                    pCube = p->ppStore[Index];
                    break;
                }
        // stop if there is no more cubes
        if ( pCube == NULL )
            break;

        // find the first dist2 cube
        Min_CoverForEachCubePrev( pCube->pNext, pThis, ppPrevT )
            if ( Min_CubesDistTwo( pCube, pThis, &Var0, &Var1 ) )
                break;
        if ( pThis == NULL && Index < p->nVars )
        Min_CoverForEachCubePrev( p->ppStore[Index+1], pThis, ppPrevT )
            if ( Min_CubesDistTwo( pCube, pThis, &Var0, &Var1 ) )
                break;
        // continue if there is no dist2 cube
        if ( pThis == NULL )
        {
            // insert the bubble after the cube
            p->pBubble->pNext = pCube->pNext;
            pCube->pNext = p->pBubble;
            p->pBubble->nLits = pCube->nLits;
            continue;
        }
        nPairs++;

        // remove the cubes, insert the bubble instead of pCube
        *ppPrevT = pThis->pNext;
        *ppPrev = p->pBubble;
        p->pBubble->pNext = pCube->pNext;
        p->pBubble->nLits = pCube->nLits;
        p->nCubes -= 2;


        // save the dist2 parameters
        v00 = Min_CubeGetVar( pCube, Var0 );
        v01 = Min_CubeGetVar( pCube, Var1 );
        v10 = Min_CubeGetVar( pThis, Var0 );
        v11 = Min_CubeGetVar( pThis, Var1 );
        assert( v00 != v10 && v01 != v11 );
        assert( v00 != 3   || v01 != 3 );
        assert( v10 != 3   || v11 != 3 );

        // skip the case when rewriting is impossible
        if ( v00 != 3 && v01 != 3 && v10 != 3 && v11 != 3 )
            continue;

        // if one of them does not have DC lit, move it
        if ( v00 != 3 && v01 != 3 )
        {
            pTemp = pCube; pCube = pThis; pThis = pTemp;
            Index = v00; v00 = v10; v10 = Index;
            Index = v01; v01 = v11; v11 = Index;
        }

//printf( "\n" );
//Min_CubeWrite( stdout, pCube );
//Min_CubeWrite( stdout, pThis );

        // make sure the first cube has first var DC
        if ( v00 != 3 )
        {
            assert( v01 == 3 );
            Index = Var0; Var0 = Var1; Var1 = Index;
            Index = v00; v00 = v01; v01 = Index;
            Index = v10; v10 = v11; v11 = Index;
        }

        // consider both cases: both have DC lit
        if ( v00 == 3 && v11 == 3 )
        {
            assert( v01 != 3 && v10 != 3 );
            // try two reduced cubes

        }
        else // the first cube has DC lit
        {
            assert( v01 != 3 && v10 != 3 && v11 != 3 );
            // try reduced and expanded cube
        }
    }
//    printf( "Pairs = %d  ", nPairs );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Min_SopAddCube( Min_Man_t * p, Min_Cube_t * pCube )
{
    return 1;
}




/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Min_SopDist1Merge( Min_Man_t * p )
{
    Min_Cube_t * pCube, * pCube2, * pCubeNew;
    int i;
    for ( i = p->nVars; i >= 0; i-- )
    {
        Min_CoverForEachCube( p->ppStore[i], pCube )
        Min_CoverForEachCube( pCube->pNext, pCube2 )
        {
            assert( pCube->nLits == pCube2->nLits );
            if ( !Min_CubesDistOne( pCube, pCube2, NULL ) )
                continue;
            pCubeNew = Min_CubesXor( p, pCube, pCube2 );
            assert( pCubeNew->nLits == pCube->nLits - 1 );
            pCubeNew->pNext = p->ppStore[pCubeNew->nLits];
            p->ppStore[pCubeNew->nLits] = pCubeNew;
            p->nCubes++;
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Min_SopContain( Min_Man_t * p )
{
    Min_Cube_t * pCube, * pCube2, ** ppPrev;
    int i, k;
    for ( i = 0; i <= p->nVars; i++ )
    {
        Min_CoverForEachCube( p->ppStore[i], pCube )
        Min_CoverForEachCubePrev( pCube->pNext, pCube2, ppPrev )
        {
            if ( !Min_CubesAreEqual( pCube, pCube2 ) )
                continue;
            *ppPrev = pCube2->pNext;
            Min_CubeRecycle( p, pCube2 );
            p->nCubes--;
        }
        for ( k = i + 1; k <= p->nVars; k++ )
        Min_CoverForEachCubePrev( p->ppStore[k], pCube2, ppPrev )
        {
            if ( !Min_CubeIsContained( pCube, pCube2 ) )
                continue;
            *ppPrev = pCube2->pNext;
            Min_CubeRecycle( p, pCube2 );
            p->nCubes--;
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Min_Cube_t * Min_SopComplement( Min_Man_t * p, Min_Cube_t * pSharp )
{
     Vec_Int_t * vVars;
     Min_Cube_t * pCover, * pCube, * pNext, * pReady, * pThis, ** ppPrev;
     int Num, Value, i;

     // get the variables
     vVars = Vec_IntAlloc( 100 );
    // create the tautology cube
     pCover = Min_CubeAlloc( p );
     // sharp it with all cubes
     Min_CoverForEachCube( pSharp, pCube )
     Min_CoverForEachCubePrev( pCover, pThis, ppPrev )
     {
        if ( Min_CubesDisjoint( pThis, pCube ) )
            continue;
        // remember the next pointer
        pNext = pThis->pNext;
        // get the variables, in which pThis is '-' while pCube is fixed
        Min_CoverGetDisjVars( pThis, pCube, vVars );
        // generate the disjoint cubes
        pReady = pThis;
        Vec_IntForEachEntryReverse( vVars, Num, i )
        {
            // correct the literal
            Min_CubeXorVar( pReady, vVars->pArray[i], 3 );
            if ( i == 0 )
                break;
            // create the new cube and clean this value
            Value = Min_CubeGetVar( pReady, vVars->pArray[i] );
            pReady = Min_CubeDup( p, pReady );
            Min_CubeXorVar( pReady, vVars->pArray[i], 3 ^ Value );
            // add to the cover
            *ppPrev = pReady;
            ppPrev = &pReady->pNext;
        }
        pThis = pReady;
        pThis->pNext = pNext;
     }
     Vec_IntFree( vVars );

     // perform dist-1 merge and contain
     Min_CoverExpandRemoveEqual( p, pCover );
     Min_SopDist1Merge( p );
     Min_SopContain( p );
     return Min_CoverCollect( p, p->nVars );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


