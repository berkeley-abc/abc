/**CFile****************************************************************

  FileName    [playerUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [PLA decomposition package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: playerUtil.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "player.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Merges two supports.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pla_ManMergeTwoSupports( Pla_Man_t * p, Vec_Int_t * vSupp0, Vec_Int_t * vSupp1, Vec_Int_t * vSupp )
{
    int k0, k1;

    assert( vSupp0->nSize && vSupp1->nSize );

    Vec_IntFill( p->vComTo0, vSupp0->nSize + vSupp1->nSize, -1 );
    Vec_IntFill( p->vComTo1, vSupp0->nSize + vSupp1->nSize, -1 );
    Vec_IntClear( p->vPairs0 );
    Vec_IntClear( p->vPairs1 );

    vSupp->nSize  = 0;
    vSupp->nCap   = vSupp0->nSize + vSupp1->nSize;
    vSupp->pArray = ALLOC( int, vSupp->nCap );

    for ( k0 = k1 = 0; k0 < vSupp0->nSize && k1 < vSupp1->nSize; )
    {
        if ( vSupp0->pArray[k0] == vSupp1->pArray[k1] )
        {
            Vec_IntWriteEntry( p->vComTo0, vSupp->nSize, k0 );
            Vec_IntWriteEntry( p->vComTo1, vSupp->nSize, k1 );
            Vec_IntPush( p->vPairs0, k0 );
            Vec_IntPush( p->vPairs1, k1 );
            Vec_IntPush( vSupp, vSupp0->pArray[k0] );
            k0++; k1++;
        }
        else if ( vSupp0->pArray[k0] < vSupp1->pArray[k1] )
        {
            Vec_IntWriteEntry( p->vComTo0, vSupp->nSize, k0 );
            Vec_IntPush( vSupp, vSupp0->pArray[k0] );
            k0++;
        }
        else 
        {
            Vec_IntWriteEntry( p->vComTo1, vSupp->nSize, k1 );
            Vec_IntPush( vSupp, vSupp1->pArray[k1] );
            k1++;
        }
    }
    for ( ; k0 < vSupp0->nSize; k0++ )
    {
        Vec_IntWriteEntry( p->vComTo0, vSupp->nSize, k0 );
        Vec_IntPush( vSupp, vSupp0->pArray[k0] );
    }
    for ( ; k1 < vSupp1->nSize; k1++ )
    {
        Vec_IntWriteEntry( p->vComTo1, vSupp->nSize, k1 );
        Vec_IntPush( vSupp, vSupp1->pArray[k1] );
    }
/*
    printf( "Zero : " );
    for ( k = 0; k < vSupp0->nSize; k++ )
        printf( "%d ", vSupp0->pArray[k] );
    printf( "\n" );

    printf( "One  : " );
    for ( k = 0; k < vSupp1->nSize; k++ )
        printf( "%d ", vSupp1->pArray[k] );
    printf( "\n" );

    printf( "Sum  : " );
    for ( k = 0; k < vSupp->nSize; k++ )
        printf( "%d ", vSupp->pArray[k] );
    printf( "\n" );
    printf( "\n" );
*/
    return Vec_IntSize(vSupp);
}


/**Function*************************************************************

  Synopsis    [Computes the produce of two covers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Esop_Cube_t * Pla_ManAndTwoCovers( Pla_Man_t * p, Esop_Cube_t * pCover0, Esop_Cube_t * pCover1, int nSupp, int fStopAtLimit )
{
    Esop_Cube_t * pCube, * pCube0, * pCube1;
    Esop_Cube_t * pCover;
    int i, Val0, Val1;
    assert( pCover0 != PLA_EMPTY && pCover1 != PLA_EMPTY );

    // clean storage
    assert( nSupp <= p->nPlaMax );
    Esop_ManClean( p->pManMin, nSupp );
    // go through the cube pairs
    Esop_CoverForEachCube( pCover0, pCube0 )
    Esop_CoverForEachCube( pCover1, pCube1 )
    {
        // go through the support variables of the cubes
        for ( i = 0; i < p->vPairs0->nSize; i++ )
        {
            Val0 = Esop_CubeGetVar( pCube0, p->vPairs0->pArray[i] );
            Val1 = Esop_CubeGetVar( pCube1, p->vPairs1->pArray[i] );
            if ( (Val0 & Val1) == 0 )
                break;
        }
        // check disjointness
        if ( i < p->vPairs0->nSize )
            continue;

        if ( fStopAtLimit && p->pManMin->nCubes > p->nCubesMax )
        {
            pCover = Esop_CoverCollect( p->pManMin, nSupp );
//Esop_CoverWriteFile( pCover, "large", 1 );
            Esop_CoverRecycle( p->pManMin, pCover );
            return PLA_EMPTY;
        }

        // create the product cube
        pCube = Esop_CubeAlloc( p->pManMin );

        // add the literals
        pCube->nLits = 0;
        for ( i = 0; i < nSupp; i++ )
        {
            if ( p->vComTo0->pArray[i] == -1 )
                Val0 = 3;
            else
                Val0 = Esop_CubeGetVar( pCube0, p->vComTo0->pArray[i] );

            if ( p->vComTo1->pArray[i] == -1 )
                Val1 = 3;
            else
                Val1 = Esop_CubeGetVar( pCube1, p->vComTo1->pArray[i] );

            if ( (Val0 & Val1) == 3 )
                continue;

            Esop_CubeXorVar( pCube, i, (Val0 & Val1) ^ 3 );
            pCube->nLits++;
        }
        // add the cube to storage
        Esop_EsopAddCube( p->pManMin, pCube );
    }

    // minimize the cover
    Esop_EsopMinimize( p->pManMin );
    pCover = Esop_CoverCollect( p->pManMin, nSupp );

    // quit if the cover is too large
    if ( fStopAtLimit && Esop_CoverCountCubes(pCover) > p->nPlaMax )
    {
        Esop_CoverRecycle( p->pManMin, pCover );
        return PLA_EMPTY;
    }
//    if ( pCover && pCover->nWords > 4 )
//        printf( "%d", pCover->nWords );
//    else
//        printf( "." );
    return pCover;
}

/**Function*************************************************************

  Synopsis    [Computes the EXOR of two covers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Esop_Cube_t * Pla_ManExorTwoCovers( Pla_Man_t * p, Esop_Cube_t * pCover0, Esop_Cube_t * pCover1, int nSupp, int fStopAtLimit )
{
    Esop_Cube_t * pCube, * pCube0, * pCube1;
    Esop_Cube_t * pCover;
    int i, Val0, Val1;
    assert( pCover0 != PLA_EMPTY && pCover1 != PLA_EMPTY );

    // clean storage
    assert( nSupp <= p->nPlaMax );
    Esop_ManClean( p->pManMin, nSupp );
    Esop_CoverForEachCube( pCover0, pCube0 )
    {
        // create the cube
        pCube = Esop_CubeAlloc( p->pManMin );
        pCube->nLits = 0;
        for ( i = 0; i < p->vComTo0->nSize; i++ )
        {
            if ( p->vComTo0->pArray[i] == -1 )
                continue;
            Val0 = Esop_CubeGetVar( pCube0, p->vComTo0->pArray[i] );
            if ( Val0 == 3 )
                continue;
            Esop_CubeXorVar( pCube, i, Val0 ^ 3 );
            pCube->nLits++;
        }
        if ( fStopAtLimit && p->pManMin->nCubes > p->nCubesMax )
        {
            pCover = Esop_CoverCollect( p->pManMin, nSupp );
            Esop_CoverRecycle( p->pManMin, pCover );
            return PLA_EMPTY;
        }
        // add the cube to storage
        Esop_EsopAddCube( p->pManMin, pCube );
    }
    Esop_CoverForEachCube( pCover1, pCube1 )
    {
        // create the cube
        pCube = Esop_CubeAlloc( p->pManMin );
        pCube->nLits = 0;
        for ( i = 0; i < p->vComTo1->nSize; i++ )
        {
            if ( p->vComTo1->pArray[i] == -1 )
                continue;
            Val1 = Esop_CubeGetVar( pCube1, p->vComTo1->pArray[i] );
            if ( Val1 == 3 )
                continue;
            Esop_CubeXorVar( pCube, i, Val1 ^ 3 );
            pCube->nLits++;
        }
        if ( fStopAtLimit && p->pManMin->nCubes > p->nCubesMax )
        {
            pCover = Esop_CoverCollect( p->pManMin, nSupp );
            Esop_CoverRecycle( p->pManMin, pCover );
            return PLA_EMPTY;
        }
        // add the cube to storage
        Esop_EsopAddCube( p->pManMin, pCube );
    }

    // minimize the cover
    Esop_EsopMinimize( p->pManMin );
    pCover = Esop_CoverCollect( p->pManMin, nSupp );

    // quit if the cover is too large
    if ( fStopAtLimit && Esop_CoverCountCubes(pCover) > p->nPlaMax )
    {
        Esop_CoverRecycle( p->pManMin, pCover );
        return PLA_EMPTY;
    }
    return pCover;
}

/**Function*************************************************************

  Synopsis    [Computes area/delay of the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pla_ManComputeStats( Ivy_Man_t * p, Vec_Int_t * vNodes )
{
    Ivy_Obj_t * pObj, * pFanin;
    Vec_Int_t * vFanins;
    int Area, Delay, Fanin, nFanins, i, k;

    Delay = Area = 0;
    // compute levels and area
    Ivy_ManForEachPi( p, pObj, i )
        pObj->Level = 0;
    Ivy_ManForEachNodeVec( p, vNodes, pObj, i )
    {
        // compute level of the node
        pObj->Level = 0;        
        vFanins = Ivy_ObjGetFanins( pObj );
        Vec_IntForEachEntry( vFanins, Fanin, k )
        {
            pFanin = Ivy_ManObj(p, Ivy_FanId(Fanin));
            pObj->Level = IVY_MAX( pObj->Level, pFanin->Level );
        }
        pObj->Level += 1;
        // compute area of the node
        nFanins = Ivy_ObjFaninNum( pObj );
        if ( nFanins <= 4 )
            Area += 1;
        else if ( nFanins <= 6 )
            Area += 2;
        else if ( nFanins <= 8 )
            Area += 4;
        else if ( nFanins <= 16 )
            Area += 8;
        else if ( nFanins <= 32 )
            Area += 16;
        else if ( nFanins <= 64 )
            Area += 32;
        else if ( nFanins <= 128 )
            Area += 64;
        else
            assert( 0 );
    }
    Ivy_ManForEachPo( p, pObj, i )
    {
        Fanin = Ivy_ObjReadFanin(pObj, 0);
        pFanin = Ivy_ManObj( p, Ivy_FanId(Fanin) );
        pObj->Level = pFanin->Level;
        Delay = IVY_MAX( Delay, (int)pObj->Level );
    }
    printf( "Area = %d. Delay = %d.\n", Area, Delay );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


