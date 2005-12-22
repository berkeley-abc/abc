/**CFile****************************************************************

  FileName    [xyzCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cover manipulation package.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: xyzCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "xyz.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void        Abc_NtkXyzCovers( Xyz_Man_t * p, Abc_Ntk_t * pNtk, bool fVerbose );
static int         Abc_NtkXyzCoversOne( Xyz_Man_t * p, Abc_Ntk_t * pNtk, bool fVerbose );
static void        Abc_NtkXyzCovers_rec( Xyz_Man_t * p, Abc_Obj_t * pObj, Vec_Ptr_t * vBoundary );

static int         Abc_NodeXyzPropagateEsop( Xyz_Man_t * p, Abc_Obj_t * pObj, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1 );
static int         Abc_NodeXyzPropagateSop( Xyz_Man_t * p, Abc_Obj_t * pObj, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1 );
static int         Abc_NodeXyzUnionEsop( Xyz_Man_t * p, Min_Cube_t * pCover0, Min_Cube_t * pCover1, int nSupp );
static int         Abc_NodeXyzUnionSop( Xyz_Man_t * p, Min_Cube_t * pCover0, Min_Cube_t * pCover1, int nSupp );
static int         Abc_NodeXyzProductEsop( Xyz_Man_t * p, Min_Cube_t * pCover0, Min_Cube_t * pCover1, int nSupp );
static int         Abc_NodeXyzProductSop( Xyz_Man_t * p, Min_Cube_t * pCover0, Min_Cube_t * pCover1, int nSupp );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkXyz( Abc_Ntk_t * pNtk, int nFaninMax, bool fUseEsop, bool fUseSop, bool fUseInvs, bool fVerbose )
{
    Abc_Ntk_t * pNtkNew;
    Xyz_Man_t * p;

    assert( Abc_NtkIsStrash(pNtk) );

    // create the manager
    p = Xyz_ManAlloc( pNtk, nFaninMax );
    pNtk->pManCut = p;

    // perform mapping
    Abc_NtkXyzCovers( p, pNtk, fVerbose );

    // derive the final network
    if ( fUseInvs )
        pNtkNew = Abc_NtkXyzDeriveClean( p, pNtk );
    else
        pNtkNew = Abc_NtkXyzDerive( p, pNtk );

    Xyz_ManFree( p );
    pNtk->pManCut = NULL;

    // make sure that everything is okay
    if ( pNtkNew && !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkXyz: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Compute the supports.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkXyzCovers( Xyz_Man_t * p, Abc_Ntk_t * pNtk, bool fVerbose )
{
    Abc_Obj_t * pObj;
    int i, clk = clock();

    // start the manager
    p->vFanCounts = Abc_NtkFanoutCounts(pNtk);

    // set trivial cuts for the constant and the CIs
    pObj = Abc_NtkConst1(pNtk);
    pObj->fMarkA = 1;
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->fMarkA = 1;

    // perform iterative decomposition
    for ( i = 0; ; i++ )
    {
        if ( fVerbose )
        printf( "Iter %d : ", i+1 );
        if ( Abc_NtkXyzCoversOne(p, pNtk, fVerbose) )
            break;
    }

    // clean the cut-point markers
    Abc_NtkForEachObj( pNtk, pObj, i )
        pObj->fMarkA = 0;

if ( fVerbose )
{
PRT( "Total", clock() - clk );
}
}

/**Function*************************************************************

  Synopsis    [Compute the supports.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkXyzCoversOne( Xyz_Man_t * p, Abc_Ntk_t * pNtk, bool fVerbose )
{
    ProgressBar * pProgress;
    Abc_Obj_t * pObj;
    Vec_Ptr_t * vBoundary;
    int i, clk = clock();
    int Counter = 0;
    int fStop = 1;

    // array to collect the nodes in the new boundary
    vBoundary = Vec_PtrAlloc( 100 );

    // start from the COs and mark visited nodes using pObj->fMarkB
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // skip the solved nodes (including the CIs)
        pObj = Abc_ObjFanin0(pObj);
        if ( pObj->fMarkA )
        {
            Counter++;
            continue;
        } 

        // traverse the cone starting from this node
        Abc_NtkXyzCovers_rec( p, pObj, vBoundary );
        if ( Abc_ObjGetSupp(pObj) == NULL )
            fStop = 0;
        else
            Counter++;

/*
        printf( "%-15s : ", Abc_ObjName(pObj) ); 
        printf( "lev = %5d  ", pObj->Level );
        if ( Abc_ObjGetSupp(pObj) == NULL )
        {
            printf( "\n" );
            continue;
        }
        printf( "supp = %3d  ", Abc_ObjGetSupp(pObj)->nSize ); 
        printf( "esop = %3d  ", Min_CoverCountCubes( Abc_ObjGetCover2(pObj) ) ); 
        printf( "\n" );
*/
    }
    Extra_ProgressBarStop( pProgress );

    // clean visited nodes
    Abc_NtkForEachObj( pNtk, pObj, i )
        pObj->fMarkB = 0;

    // create the new boundary
    p->nBoundary = 0;
    Vec_PtrForEachEntry( vBoundary, pObj, i )
    {
        if ( !pObj->fMarkA )
        {
            pObj->fMarkA = 1;
            p->nBoundary++;
        }
    }
    Vec_PtrFree( vBoundary );

if ( fVerbose )
{
    printf( "Outs = %4d (%4d) Node = %6d (%6d) Max = %6d  Bound = %4d  ", 
        Counter, Abc_NtkCoNum(pNtk), p->nSupps, Abc_NtkNodeNum(pNtk), p->nSuppsMax, p->nBoundary );
PRT( "T", clock() - clk );
}
    return fStop;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkXyzCovers_rec( Xyz_Man_t * p, Abc_Obj_t * pObj, Vec_Ptr_t * vBoundary )
{
    Abc_Obj_t * pObj0, * pObj1;
    // return if the support is already computed
    if ( pObj->fMarkB || pObj->fMarkA || Abc_ObjGetSupp(pObj) )
        return;
    // mark as visited
    pObj->fMarkB = 1;
    // get the fanins
    pObj0 = Abc_ObjFanin0(pObj);
    pObj1 = Abc_ObjFanin1(pObj);
    // solve for the fanins
    Abc_NtkXyzCovers_rec( p, pObj0, vBoundary );
    Abc_NtkXyzCovers_rec( p, pObj1, vBoundary );
    // skip the node that spaced out
    if ( !pObj0->fMarkA && !Abc_ObjGetSupp(pObj0) ||     // fanin is not ready
         !pObj1->fMarkA && !Abc_ObjGetSupp(pObj1) ||     // fanin is not ready
         !Abc_NodeXyzPropagateEsop(p, pObj, pObj0, pObj1) )  // node's support or covers cannot be computed
    {
        // save the nodes of the future boundary
        if ( !pObj0->fMarkA && Abc_ObjGetSupp(pObj0) )
            Vec_PtrPush( vBoundary, pObj0 );
        if ( !pObj1->fMarkA && Abc_ObjGetSupp(pObj1) )
            Vec_PtrPush( vBoundary, pObj1 );
        return;
    }
    // consider dropping the fanin supports
//    Abc_NodeXyzDropData( p, pObj0 );
//    Abc_NodeXyzDropData( p, pObj1 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NodeXyzSupport( Xyz_Man_t * p, Vec_Int_t * vSupp0, Vec_Int_t * vSupp1 )
{
    Vec_Int_t * vSupp;
    int k0, k1;

    assert( vSupp0 && vSupp1 );
    Vec_IntFill( p->vComTo0, vSupp0->nSize + vSupp1->nSize, -1 );
    Vec_IntFill( p->vComTo1, vSupp0->nSize + vSupp1->nSize, -1 );
    Vec_IntClear( p->vPairs0 );
    Vec_IntClear( p->vPairs1 );

    vSupp = Vec_IntAlloc( vSupp0->nSize + vSupp1->nSize );
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
    for ( k0 = 0; k0 < vSupp0->nSize; k0++ )
        printf( "%d ", vSupp0->pArray[k0] );
    printf( "\n" );

    printf( "One  : " );
    for ( k1 = 0; k1 < vSupp1->nSize; k1++ )
        printf( "%d ", vSupp1->pArray[k1] );
    printf( "\n" );

    printf( "Sum  : " );
    for ( k0 = 0; k0 < vSupp->nSize; k0++ )
        printf( "%d ", vSupp->pArray[k0] );
    printf( "\n" );
    printf( "\n" );
*/
    return vSupp;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeXyzPropagateEsop( Xyz_Man_t * p, Abc_Obj_t * pObj, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1 )
{
    Min_Cube_t * pCover, * pCover0, * pCover1, * pCov0, * pCov1;
    Vec_Int_t * vSupp, * vSupp0, * vSupp1;

    if ( pObj0->fMarkA )  Vec_IntWriteEntry( p->vTriv0, 0, pObj0->Id );
    if ( pObj1->fMarkA )  Vec_IntWriteEntry( p->vTriv1, 0, pObj1->Id );

    // get the resulting support
    vSupp0 = pObj0->fMarkA? p->vTriv0 : Abc_ObjGetSupp(pObj0);
    vSupp1 = pObj1->fMarkA? p->vTriv1 : Abc_ObjGetSupp(pObj1);
    vSupp  = Abc_NodeXyzSupport( p, vSupp0, vSupp1 );

    // quit if support if too large
    if ( vSupp->nSize > p->nFaninMax )
    {
        Vec_IntFree( vSupp );
        return 0;
    }
   
    // get the covers
    pCov0 = pObj0->fMarkA? p->pManMin->pTriv0[0] : Abc_ObjGetCover2(pObj0);
    pCov1 = pObj1->fMarkA? p->pManMin->pTriv1[0] : Abc_ObjGetCover2(pObj1);

    // complement the first if needed
    if ( !Abc_ObjFaninC0(pObj) )
        pCover0 = pCov0;
    else if ( pCov0 && pCov0->nLits == 0 ) // topmost one is the tautology cube
        pCover0 = pCov0->pNext;
    else
        pCover0 = p->pManMin->pOne0, p->pManMin->pOne0->pNext = pCov0;

    // complement the second if needed
    if ( !Abc_ObjFaninC1(pObj) )
        pCover1 = pCov1;
    else if ( pCov1 && pCov1->nLits == 0 ) // topmost one is the tautology cube
        pCover1 = pCov1->pNext;
    else
        pCover1 = p->pManMin->pOne1, p->pManMin->pOne1->pNext = pCov1;

    // derive and minimize the cover (quit if too large)
    if ( !Abc_NodeXyzProductEsop( p, pCover0, pCover1, vSupp->nSize ) )
    {
        pCover = Min_CoverCollect( p->pManMin, vSupp->nSize );
        Min_CoverRecycle( p->pManMin, pCover );
        Vec_IntFree( vSupp );
        return 0;
    }

    // minimize the cover
    Min_EsopMinimize( p->pManMin );
    pCover = Min_CoverCollect( p->pManMin, vSupp->nSize );

    // quit if the cover is too large
    if ( Min_CoverCountCubes(pCover) > p->nFaninMax )
    {
        Min_CoverRecycle( p->pManMin, pCover );
        Vec_IntFree( vSupp );
        return 0;
    }

    // count statistics
    p->nSupps++;
    p->nSuppsMax = ABC_MAX( p->nSuppsMax, p->nSupps );

    // set the covers
    assert( Abc_ObjGetSupp(pObj) == NULL );
    Abc_ObjSetSupp( pObj, vSupp );
    Abc_ObjSetCover2( pObj, pCover );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeXyzPropagateSop( Xyz_Man_t * p, Abc_Obj_t * pObj, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1 )
{
    Min_Cube_t * pCoverP, * pCoverN, * pCover0, * pCover1;
    Vec_Int_t * vSupp, * vSupp0, * vSupp1;
    int fCompl0, fCompl1;

    if ( pObj0->fMarkA )  Vec_IntWriteEntry( p->vTriv0, 0, pObj0->Id );
    if ( pObj1->fMarkA )  Vec_IntWriteEntry( p->vTriv1, 0, pObj1->Id );

    // get the resulting support
    vSupp0 = pObj0->fMarkA? p->vTriv0 : Abc_ObjGetSupp(pObj0);
    vSupp1 = pObj1->fMarkA? p->vTriv1 : Abc_ObjGetSupp(pObj1);
    vSupp  = Abc_NodeXyzSupport( p, vSupp0, vSupp1 );

    // quit if support if too large
    if ( vSupp->nSize > p->nFaninMax )
    {
        Vec_IntFree( vSupp );
        return 0;
    }

    // get the complemented attributes
    fCompl0 = Abc_ObjFaninC0(pObj);
    fCompl1 = Abc_ObjFaninC1(pObj);
   
    // prepare the positive cover
    pCover0 = pObj0->fMarkA? p->pManMin->pTriv0[fCompl0] : Abc_ObjGetCover(pObj0, fCompl0);
    pCover1 = pObj1->fMarkA? p->pManMin->pTriv1[fCompl1] : Abc_ObjGetCover(pObj1, fCompl1);

    // derive and minimize the cover (quit if too large)
    if ( !pCover0 || !pCover1 )
        pCoverP = NULL;
    else if ( !Abc_NodeXyzProductSop( p, pCover0, pCover1, vSupp->nSize ) )
    {
        pCoverP = Min_CoverCollect( p->pManMin, vSupp->nSize );
        Min_CoverRecycle( p->pManMin, pCoverP );
        pCoverP = NULL;
    }
    else
    {
        Min_SopMinimize( p->pManMin );
        pCoverP = Min_CoverCollect( p->pManMin, vSupp->nSize );
        // quit if the cover is too large
        if ( Min_CoverCountCubes(pCoverP) > p->nFaninMax )
        {
            Min_CoverRecycle( p->pManMin, pCoverP );
            pCoverP = NULL;
        }
    }
   
    // prepare the negative cover
    pCover0 = pObj0->fMarkA? p->pManMin->pTriv0[!fCompl0] : Abc_ObjGetCover(pObj0, !fCompl0);
    pCover1 = pObj1->fMarkA? p->pManMin->pTriv1[!fCompl1] : Abc_ObjGetCover(pObj1, !fCompl1);

    // derive and minimize the cover (quit if too large)
    if ( !pCover0 || !pCover1 )
        pCoverN = NULL;
    else if ( !Abc_NodeXyzUnionSop( p, pCover0, pCover1, vSupp->nSize ) )
    {
        pCoverN = Min_CoverCollect( p->pManMin, vSupp->nSize );
        Min_CoverRecycle( p->pManMin, pCoverN );
        pCoverN = NULL;
    }
    else
    {
        Min_SopMinimize( p->pManMin );
        pCoverN = Min_CoverCollect( p->pManMin, vSupp->nSize );
        // quit if the cover is too large
        if ( Min_CoverCountCubes(pCoverN) > p->nFaninMax )
        {
            Min_CoverRecycle( p->pManMin, pCoverN );
            pCoverN = NULL;
        }
    }

    if ( pCoverP == NULL && pCoverN == NULL )
    {
        Vec_IntFree( vSupp );
        return 0;
    }

    // count statistics
    p->nSupps++;
    p->nSuppsMax = ABC_MAX( p->nSuppsMax, p->nSupps );

    // set the covers
    assert( Abc_ObjGetSupp(pObj) == NULL );
    Abc_ObjSetSupp( pObj, vSupp );
    Abc_ObjSetCover( pObj, pCoverP, 0 );
    Abc_ObjSetCover( pObj, pCoverN, 1 );
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeXyzProductEsop( Xyz_Man_t * p, Min_Cube_t * pCover0, Min_Cube_t * pCover1, int nSupp )
{
    Min_Cube_t * pCube, * pCube0, * pCube1;
    int i, Val0, Val1;

    // clean storage
    Min_ManClean( p->pManMin, nSupp );
    if ( pCover0 == NULL || pCover1 == NULL )
        return 1;

    // go through the cube pairs
    Min_CoverForEachCube( pCover0, pCube0 )
    Min_CoverForEachCube( pCover1, pCube1 )
    {
        // go through the support variables of the cubes
        for ( i = 0; i < p->vPairs0->nSize; i++ )
        {
            Val0 = Min_CubeGetVar( pCube0, p->vPairs0->pArray[i] );
            Val1 = Min_CubeGetVar( pCube1, p->vPairs1->pArray[i] );
            if ( (Val0 & Val1) == 0 )
                break;
        }
        // check disjointness
        if ( i < p->vPairs0->nSize )
            continue;

        if ( p->pManMin->nCubes >= p->nCubesMax )
            return 0;

        // create the product cube
        pCube = Min_CubeAlloc( p->pManMin );

        // add the literals
        pCube->nLits = 0;
        for ( i = 0; i < nSupp; i++ )
        {
            if ( p->vComTo0->pArray[i] == -1 )
                Val0 = 3;
            else
                Val0 = Min_CubeGetVar( pCube0, p->vComTo0->pArray[i] );

            if ( p->vComTo1->pArray[i] == -1 )
                Val1 = 3;
            else
                Val1 = Min_CubeGetVar( pCube1, p->vComTo1->pArray[i] );

            if ( (Val0 & Val1) == 3 )
                continue;

            Min_CubeXorVar( pCube, i, (Val0 & Val1) ^ 3 );
            pCube->nLits++;
        }
        // add the cube to storage
        while ( Min_EsopAddCube( p->pManMin, pCube ) );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeXyzProductSop( Xyz_Man_t * p, Min_Cube_t * pCover0, Min_Cube_t * pCover1, int nSupp )
{
    return 1;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeXyzUnionEsop( Xyz_Man_t * p, Min_Cube_t * pCover0, Min_Cube_t * pCover1, int nSupp )
{
    Min_Cube_t * pCube, * pCube0, * pCube1;
    int i, Val0, Val1;

    // clean storage
    Min_ManClean( p->pManMin, nSupp );
    if ( pCover0 )
    {
        Min_CoverForEachCube( pCover0, pCube0 )
        {
            // create the cube
            pCube = Min_CubeAlloc( p->pManMin );
            pCube->nLits = 0;
            for ( i = 0; i < p->vComTo0->nSize; i++ )
            {
                if ( p->vComTo0->pArray[i] == -1 )
                    continue;
                Val0 = Min_CubeGetVar( pCube0, p->vComTo0->pArray[i] );
                if ( Val0 == 3 )
                    continue;
                Min_CubeXorVar( pCube, i, Val0 ^ 3 );
                pCube->nLits++;
            }
            if ( p->pManMin->nCubes >= p->nCubesMax )
                return 0;
            // add the cube to storage
            while ( Min_EsopAddCube( p->pManMin, pCube ) );
        }
    }
    if ( pCover1 )
    {
        Min_CoverForEachCube( pCover1, pCube1 )
        {
            // create the cube
            pCube = Min_CubeAlloc( p->pManMin );
            pCube->nLits = 0;
            for ( i = 0; i < p->vComTo1->nSize; i++ )
            {
                if ( p->vComTo1->pArray[i] == -1 )
                    continue;
                Val1 = Min_CubeGetVar( pCube1, p->vComTo1->pArray[i] );
                if ( Val1 == 3 )
                    continue;
                Min_CubeXorVar( pCube, i, Val1 ^ 3 );
                pCube->nLits++;
            }
            if ( p->pManMin->nCubes >= p->nCubesMax )
                return 0;
            // add the cube to storage
            while ( Min_EsopAddCube( p->pManMin, pCube ) );
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeXyzUnionSop( Xyz_Man_t * p, Min_Cube_t * pCover0, Min_Cube_t * pCover1, int nSupp )
{
    return 1;
}




////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


