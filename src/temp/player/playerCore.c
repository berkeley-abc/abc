/**CFile****************************************************************

  FileName    [playerCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [PLA decomposition package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: playerCore.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/
 
#include "player.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Pla_ManDecomposeInt( Pla_Man_t * p );
static int Pla_ManDecomposeNode( Pla_Man_t * p, Ivy_Obj_t * pObj );
static void Pla_NodeGetSuppsAndCovers( Pla_Man_t * p, Ivy_Obj_t * pObj, int Level, 
    Vec_Int_t ** pvSuppA, Vec_Int_t ** pvSuppB, Esop_Cube_t ** pvCovA, Esop_Cube_t ** pvCovB );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs decomposition/mapping into PLAs and K-LUTs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Man_t * Pla_ManDecompose( Ivy_Man_t * pAig, int nLutMax, int nPlaMax, int fVerbose )
{
    Pla_Man_t * p;
    Ivy_Man_t * pAigNew;
    p = Pla_ManAlloc( pAig, nLutMax, nPlaMax );
    if ( !Pla_ManDecomposeInt( p ) )
    {
        printf( "Decomposition/mapping failed.\n" );
        Pla_ManFree( p );
        return NULL;
    }
    pAigNew = Pla_ManToAig( pAig );
//    if ( fVerbose )
//    printf( "PLA stats: Both = %6d. Pla = %6d. Lut = %6d. Total = %6d. Deref = %6d.\n", 
//        p->nNodesBoth, p->nNodesPla, p->nNodesLut, p->nNodes, p->nNodesDeref );
    Pla_ManFree( p );
    return pAigNew;
}

/**Function*************************************************************

  Synopsis    [Performs decomposition/mapping into PLAs and K-LUTs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pla_ManDecomposeInt( Pla_Man_t * p )
{
    Ivy_Man_t * pAig = p->pManAig;
    Ivy_Obj_t * pObj;
    Pla_Obj_t * pStr;
    int i;

    // prepare the PI structures
    Ivy_ManForEachPi( pAig, pObj, i )
    {
        pStr = Ivy_ObjPlaStr( pObj );
        pStr->fFixed = 1;
        pStr->Depth  = 0;
        pStr->nRefs  = (unsigned)pObj->nRefs;
        pStr->pCover[0] = PLA_EMPTY;
        pStr->pCover[1] = PLA_EMPTY;
    }

    // assuming DFS ordering of nodes in the manager
    Ivy_ManForEachNode( pAig, pObj, i )
        if ( !Pla_ManDecomposeNode(p, pObj) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Records decomposition statistics for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Pla_ManCountDecNodes( Pla_Man_t * p, Pla_Obj_t * pStr )
{
    if ( Vec_IntSize(pStr->vSupp) <= p->nLutMax && pStr->pCover[1] != PLA_EMPTY )    
        p->nNodesBoth++;
    else if ( Vec_IntSize(pStr->vSupp) <= p->nLutMax )    
        p->nNodesLut++;
    else if ( pStr->pCover[1] != PLA_EMPTY )    
        p->nNodesPla++;
}

/**Function*************************************************************

  Synopsis    [Performs decomposition/mapping for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pla_ManDecomposeNode( Pla_Man_t * p, Ivy_Obj_t * pObj )
{
    Pla_Obj_t * pStr, * pStr0, * pStr1;
    Vec_Int_t * vSuppA, * vSuppB, * vSupp0, * vSupp1;
    Esop_Cube_t * pCovA, * pCovB;
    int nSuppSize1, nSuppSize2;

    assert( pObj->nRefs > 0 );
    p->nNodes++;

    // get the structures
    pStr   = Ivy_ObjPlaStr( pObj );    
    pStr0  = Ivy_ObjPlaStr( Ivy_ObjFanin0( pObj ) );
    pStr1  = Ivy_ObjPlaStr( Ivy_ObjFanin1( pObj ) );
    vSupp0 = &pStr->vSupp[0];
    vSupp1 = &pStr->vSupp[1];
    pStr->pCover[0] = PLA_EMPTY;
    pStr->pCover[1] = PLA_EMPTY;

    // process level 1
    Pla_NodeGetSuppsAndCovers( p, pObj, 1, &vSuppA, &vSuppB, &pCovA, &pCovB );
    nSuppSize1 = Pla_ManMergeTwoSupports( p, vSuppA, vSuppB, vSupp0 );
    if ( nSuppSize1 > p->nPlaMax || pCovA == PLA_EMPTY || pCovB == PLA_EMPTY )
        pStr->pCover[0] = PLA_EMPTY;
    else if ( Ivy_ObjIsAnd(pObj) )
        pStr->pCover[0] = Pla_ManAndTwoCovers( p, pCovA, pCovB, nSuppSize1, 1 );
    else
        pStr->pCover[0] = Pla_ManExorTwoCovers( p, pCovA, pCovB, nSuppSize1, 1 );

    // process level 2
    if ( PLA_MAX(pStr0->Depth, pStr1->Depth) > 1 )
    {
        Pla_NodeGetSuppsAndCovers( p, pObj, 2, &vSuppA, &vSuppB, &pCovA, &pCovB );
        nSuppSize2 = Pla_ManMergeTwoSupports( p, vSuppA, vSuppB, vSupp1 );
        if ( nSuppSize2 > p->nPlaMax || pCovA == PLA_EMPTY || pCovB == PLA_EMPTY )
            pStr->pCover[1] = PLA_EMPTY;
        else if ( Ivy_ObjIsAnd(pObj) )
            pStr->pCover[1] = Pla_ManAndTwoCovers( p, pCovA, pCovB, nSuppSize2, 1 );
        else
            pStr->pCover[1] = Pla_ManExorTwoCovers( p, pCovA, pCovB, nSuppSize2, 1 );
    }

    // determine the level of this node
    pStr->nRefs = (unsigned)pObj->nRefs;
    pStr->Depth = PLA_MAX( pStr0->Depth, pStr1->Depth );
    pStr->Depth = pStr->Depth? pStr->Depth : 1;    
    if ( nSuppSize1 > p->nLutMax && pStr->pCover[1] == PLA_EMPTY )
    {
        pStr->Depth++;
        // free second level
        if ( pStr->pCover[1] != PLA_EMPTY )
            Esop_CoverRecycle( p->pManMin, pStr->pCover[1] );
        vSupp1->nCap = 0;
        vSupp1->nSize = 0;
        FREE( vSupp1->pArray );
        pStr->pCover[1] = PLA_EMPTY;
        // move first to second
        pStr->vSupp[1]  = pStr->vSupp[0];
        pStr->pCover[1] = pStr->pCover[0];
        vSupp0->nCap = 0;
        vSupp0->nSize = 0;
        vSupp0->pArray = NULL;
        pStr->pCover[0] = PLA_EMPTY;
        // get zero level
        Pla_NodeGetSuppsAndCovers( p, pObj, 0, &vSuppA, &vSuppB, &pCovA, &pCovB );
        nSuppSize2 = Pla_ManMergeTwoSupports( p, vSuppA, vSuppB, vSupp0 );
        assert( nSuppSize2 == 2 );
        if ( pCovA == PLA_EMPTY || pCovB == PLA_EMPTY )
            pStr->pCover[0] = PLA_EMPTY;
        else if ( Ivy_ObjIsAnd(pObj) )
            pStr->pCover[0] = Pla_ManAndTwoCovers( p, pCovA, pCovB, nSuppSize2, 0 );
        else
            pStr->pCover[0] = Pla_ManExorTwoCovers( p, pCovA, pCovB, nSuppSize2, 0 );
        // count stats
        if ( pStr0->fFixed == 0 )  Pla_ManCountDecNodes( p, pStr0 );
        if ( pStr1->fFixed == 0 )  Pla_ManCountDecNodes( p, pStr1 );
        // mark the nodes
        pStr0->fFixed = 1;
        pStr1->fFixed = 1;
    }
    else if ( pStr0->Depth < pStr1->Depth )
    {
        if ( pStr0->fFixed == 0 )  Pla_ManCountDecNodes( p, pStr0 );
        pStr0->fFixed = 1;
    }
    else // if ( pStr0->Depth > pStr1->Depth )
    {
        if ( pStr1->fFixed == 0 )  Pla_ManCountDecNodes( p, pStr1 );
        pStr1->fFixed = 1;
    }
    assert( pStr->Depth );

    // free some of the covers to save memory
    assert( pStr0->nRefs > 0 );
    assert( pStr1->nRefs > 0 );
    pStr0->nRefs--;
    pStr1->nRefs--;

    if ( pStr0->nRefs == 0 && !pStr0->fFixed )
        Pla_ManFreeStr( p, pStr0 ), p->nNodesDeref++;
    if ( pStr1->nRefs == 0 && !pStr1->fFixed )
        Pla_ManFreeStr( p, pStr1 ), p->nNodesDeref++;

    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns pointers to the support arrays on the given level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pla_NodeGetSuppsAndCovers( Pla_Man_t * p, Ivy_Obj_t * pObj, int Level, 
    Vec_Int_t ** pvSuppA, Vec_Int_t ** pvSuppB, Esop_Cube_t ** pvCovA, Esop_Cube_t ** pvCovB )
{
    Ivy_Obj_t * pFan0, * pFan1;
    Pla_Obj_t * pStr, * pStr0, * pStr1;
    Esop_Cube_t * pCovA, * pCovB;
    int fCompl0, fCompl1;
    assert( Level >= 0 && Level <= 2 );
    // get the complemented attributes
    fCompl0 = Ivy_ObjFaninC0( pObj );
    fCompl1 = Ivy_ObjFaninC1( pObj );
    // get the fanins
    pFan0 = Ivy_ObjFanin0( pObj );
    pFan1 = Ivy_ObjFanin1( pObj );
    // get the structures
    pStr  = Ivy_ObjPlaStr( pObj );    
    pStr0 = Ivy_ObjPlaStr( pFan0 );
    pStr1 = Ivy_ObjPlaStr( pFan1 );
    // make sure the fanins are processed
    assert( Ivy_ObjIsPi(pFan0) || pStr0->Depth > 0 );
    assert( Ivy_ObjIsPi(pFan1) || pStr1->Depth > 0 );
    // prepare the return values depending on the level
    Vec_IntWriteEntry( p->vTriv0, 0, pFan0->Id );
    Vec_IntWriteEntry( p->vTriv1, 0, pFan1->Id );
    *pvSuppA = p->vTriv0;
    *pvSuppB = p->vTriv1;
    pCovA = p->pManMin->pTriv0;
    pCovB = p->pManMin->pTriv1;
    if ( Level == 1 )
    {
        if ( pStr0->Depth == pStr1->Depth )
        {
            if ( pStr0->Depth > 0 )
            {
                *pvSuppA = &pStr0->vSupp[0];
                *pvSuppB = &pStr1->vSupp[0];
                pCovA = pStr0->pCover[0];
                pCovB = pStr1->pCover[0];
            }
        }
        else if ( pStr0->Depth < pStr1->Depth )
        {
            *pvSuppB = &pStr1->vSupp[0];
            pCovB = pStr1->pCover[0];
        }
        else // if ( pStr0->Depth > pStr1->Depth )
        {
            *pvSuppA = &pStr0->vSupp[0];
            pCovA = pStr0->pCover[0];
        }
    }
    else if ( Level == 2 )
    {
        if ( pStr0->Depth == pStr1->Depth )
        {
            *pvSuppA = &pStr0->vSupp[1];
            *pvSuppB = &pStr1->vSupp[1];
            pCovA = pStr0->pCover[1];
            pCovB = pStr1->pCover[1];
        }
        else if ( pStr0->Depth + 1 == pStr1->Depth )
        {
            *pvSuppA = &pStr0->vSupp[0];
            *pvSuppB = &pStr1->vSupp[1];
            pCovA = pStr0->pCover[0];
            pCovB = pStr1->pCover[1];
        }
        else if ( pStr0->Depth == pStr1->Depth + 1 )
        {
            *pvSuppA = &pStr0->vSupp[1];
            *pvSuppB = &pStr1->vSupp[0];
            pCovA = pStr0->pCover[1];
            pCovB = pStr1->pCover[0];
        }
        else if ( pStr0->Depth < pStr1->Depth )
        {
            *pvSuppB = &pStr1->vSupp[1];
            pCovB = pStr1->pCover[1];
        }
        else // if ( pStr0->Depth > pStr1->Depth )
        {
            *pvSuppA = &pStr0->vSupp[1];
            pCovA = pStr0->pCover[1];
        }
    }
    // complement the first if needed
    if ( pCovA == PLA_EMPTY || !fCompl0 )
        *pvCovA = pCovA;
    else if ( pCovA && pCovA->nLits == 0 ) // topmost one is the tautology cube
        *pvCovA = pCovA->pNext;
    else
        *pvCovA = p->pManMin->pOne0, p->pManMin->pOne0->pNext = pCovA;
    // complement the second if needed
    if ( pCovB == PLA_EMPTY || !fCompl1 )
        *pvCovB = pCovB;
    else if ( pCovB && pCovB->nLits == 0 ) // topmost one is the tautology cube
        *pvCovB = pCovB->pNext;
    else
        *pvCovB = p->pManMin->pOne1, p->pManMin->pOne1->pNext = pCovB;
}


/*
    if ( pObj->Id == 1371 )
    {
        int k;
        printf( "Zero : " );
        for ( k = 0; k < vSuppA->nSize; k++ )
            printf( "%d ", vSuppA->pArray[k] );
        printf( "\n" );
        printf( "One  : " );
        for ( k = 0; k < vSuppB->nSize; k++ )
            printf( "%d ", vSuppB->pArray[k] );
        printf( "\n" );
        printf( "Node  : " );
        for ( k = 0; k < vSupp0->nSize; k++ )
            printf( "%d ", vSupp0->pArray[k] );
        printf( "\n" );
        printf( "\n" );
        printf( "\n" );
        Esop_CoverWrite( stdout, pCovA );
        printf( "\n" );
        Esop_CoverWrite( stdout, pCovB );
        printf( "\n" );
    }
*/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


