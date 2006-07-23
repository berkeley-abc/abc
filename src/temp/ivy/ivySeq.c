/**CFile****************************************************************

  FileName    [ivySeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivySeq.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int Ivy_CutHashValue( int NodeId )  { return 1 << (NodeId % 31); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/







/**Function*************************************************************

  Synopsis    [Derives new cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Ivy_CutDeriveNew( Ivy_Cut_t * pCut, Ivy_Cut_t * pCutNew, int IdOld, int IdNew0, int IdNew1 )
{
    unsigned uHash = 0;
    int i, k;
    assert( pCut->nSize > 0 );
    assert( IdNew0 < IdNew1 );
    for ( i = k = 0; i < pCut->nSize; i++ )
    {
        if ( pCut->pArray[i] == IdOld )
            continue;
        if ( IdNew0 >= 0 )
        {
            if ( IdNew0 <= pCut->pArray[i] )
            {
                if ( IdNew0 < pCut->pArray[i] )
                {
                    if ( k == pCut->nSizeMax )
                        return 0;
                    pCutNew->pArray[ k++ ] = IdNew0;
                    uHash |= Ivy_CutHashValue( IdNew0 );
                }
                IdNew0 = -1;
            }
        }
        if ( IdNew1 >= 0 )
        {
            if ( IdNew1 <= pCut->pArray[i] )
            {
                if ( IdNew1 < pCut->pArray[i] )
                {
                    if ( k == pCut->nSizeMax )
                        return 0;
                    pCutNew->pArray[ k++ ] = IdNew1;
                    uHash |= Ivy_CutHashValue( IdNew1 );
                }
                IdNew1 = -1;
            }
        }
        if ( k == pCut->nSizeMax )
            return 0;
        pCutNew->pArray[ k++ ] = pCut->pArray[i];
        uHash |= Ivy_CutHashValue( pCut->pArray[i] );
    }
    if ( IdNew0 >= 0 )
    {
        if ( k == pCut->nSizeMax )
            return 0;
        pCutNew->pArray[ k++ ] = IdNew0;
        uHash |= Ivy_CutHashValue( IdNew0 );
    }
    if ( IdNew1 >= 0 )
    {
        if ( k == pCut->nSizeMax )
            return 0;
        pCutNew->pArray[ k++ ] = IdNew1;
        uHash |= Ivy_CutHashValue( IdNew1 );
    }
    pCutNew->nSize = k;
    pCutNew->uHash = uHash;
    assert( pCutNew->nSize <= pCut->nSizeMax );
    for ( i = 1; i < pCutNew->nSize; i++ )
        assert( pCutNew->pArray[i-1] < pCutNew->pArray[i] );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pDom is contained in pCut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Ivy_CutCheckDominance( Ivy_Cut_t * pDom, Ivy_Cut_t * pCut )
{
    int i, k;
    for ( i = 0; i < pDom->nSize; i++ )
    {
        assert( i==0 || pDom->pArray[i-1] < pDom->pArray[i] );
        for ( k = 0; k < pCut->nSize; k++ )
            if ( pDom->pArray[i] == pCut->pArray[k] )
                break;
        if ( k == pCut->nSize ) // node i in pDom is not contained in pCut
            return 0;
    }
    // every node in pDom is contained in pCut
    return 1;
}

/**Function*************************************************************

  Synopsis    [Check if the cut exists.]

  Description [Returns 1 if the cut exists.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_CutFindOrAddFilter( Ivy_Store_t * pCutStore, Ivy_Cut_t * pCutNew )
{
    Ivy_Cut_t * pCut;
    int i, k;
    assert( pCutNew->uHash );
    // try to find the cut
    for ( i = 0; i < pCutStore->nCuts; i++ )
    {
        pCut = pCutStore->pCuts + i;
        if ( pCut->nSize == 0 )
            continue;
        if ( pCut->nSize == pCutNew->nSize )
        {
            if ( pCut->uHash == pCutNew->uHash )
            {
                for ( k = 0; k < pCutNew->nSize; k++ )
                    if ( pCut->pArray[k] != pCutNew->pArray[k] )
                        break;
                if ( k == pCutNew->nSize )
                    return 1;
            }
            continue;
        }
        if ( pCut->nSize < pCutNew->nSize )
        {
            // skip the non-contained cuts
            if ( (pCut->uHash & pCutNew->uHash) != pCut->uHash )
                continue;
            // check containment seriously
            if ( Ivy_CutCheckDominance( pCut, pCutNew ) )
                return 1;
            continue;
        }
        // check potential containment of other cut

        // skip the non-contained cuts
        if ( (pCut->uHash & pCutNew->uHash) != pCutNew->uHash )
            continue;
        // check containment seriously
        if ( Ivy_CutCheckDominance( pCutNew, pCut ) )
        {
            // remove the current cut
            pCut->nSize = 0;
        }
    }
    assert( pCutStore->nCuts < pCutStore->nCutsMax );
    // add the cut
    pCut = pCutStore->pCuts + pCutStore->nCuts++;
    *pCut = *pCutNew;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Compresses the cut representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_CutCompactAll( Ivy_Store_t * pCutStore )
{
    Ivy_Cut_t * pCut;
    int i, k;
    pCutStore->nCutsM = 0;
    for ( i = k = 0; i < pCutStore->nCuts; i++ )
    {
        pCut = pCutStore->pCuts + i;
        if ( pCut->nSize == 0 )
            continue;
        if ( pCut->nSize < pCut->nSizeMax )
            pCutStore->nCutsM++;
        pCutStore->pCuts[k++] = *pCut;
    }
    pCutStore->nCuts = k;
}

/**Function*************************************************************

  Synopsis    [Print the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_CutPrintForNode( Ivy_Cut_t * pCut )
{
    int i;
    assert( pCut->nSize > 0 );
    printf( "%d : {", pCut->nSize );
    for ( i = 0; i < pCut->nSize; i++ )
        printf( " %d", pCut->pArray[i] );
    printf( " }\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_CutPrintForNodes( Ivy_Store_t * pCutStore )
{
    int i;
    printf( "Node %d\n", pCutStore->pCuts[0].pArray[0] );
    for ( i = 0; i < pCutStore->nCuts; i++ )
        Ivy_CutPrintForNode( pCutStore->pCuts + i );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Ivy_CutReadLeaf( Ivy_Obj_t * pFanin )
{
    assert( !Ivy_IsComplement(pFanin) );
    if ( !Ivy_ObjIsLatch(pFanin) )
        return Ivy_LeafCreate( pFanin->Id, 0 );
    return 1 + Ivy_CutReadLeaf( Ivy_ObjFanin0(pFanin) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Store_t * Ivy_CutComputeForNode( Ivy_Man_t * p, Ivy_Obj_t * pObj, int nLeaves )
{
    static Ivy_Store_t CutStore, * pCutStore = &CutStore;
    Ivy_Cut_t CutNew, * pCutNew = &CutNew, * pCut;
    Ivy_Man_t * pMan = p;
    Ivy_Obj_t * pLeaf;
    int i, k, Temp, nLats, iLeaf0, iLeaf1;

    assert( nLeaves <= IVY_CUT_INPUT );

    // start the structure
    pCutStore->nCuts = 0;
    pCutStore->nCutsMax = IVY_CUT_LIMIT;
    // start the trivial cut
    pCutNew->uHash = 0;
    pCutNew->nSize = 1;
    pCutNew->nSizeMax = nLeaves;
    pCutNew->pArray[0] = Ivy_LeafCreate( pObj->Id, 0 );
    pCutNew->uHash = Ivy_CutHashValue( pCutNew->pArray[0] );
    // add the trivial cut
    pCutStore->pCuts[pCutStore->nCuts++] = *pCutNew;
    assert( pCutStore->nCuts == 1 );

    // explore the cuts
    for ( i = 0; i < pCutStore->nCuts; i++ )
    {
        // expand this cut
        pCut = pCutStore->pCuts + i;
        if ( pCut->nSize == 0 )
            continue;
        for ( k = 0; k < pCut->nSize; k++ )
        {
            pLeaf = Ivy_ManObj( p, Ivy_LeafId(pCut->pArray[k]) );
            if ( Ivy_ObjIsCi(pLeaf) )
                continue;
            assert( Ivy_ObjIsNode(pLeaf) );
            nLats = Ivy_LeafLat(pCut->pArray[k]);
            // get the fanins fanins
            iLeaf0 = nLats + Ivy_CutReadLeaf( Ivy_ObjFanin0(pLeaf) );
            iLeaf1 = nLats + Ivy_CutReadLeaf( Ivy_ObjFanin1(pLeaf) );
            if ( iLeaf0 > iLeaf1 )
                Temp = iLeaf0, iLeaf0 = iLeaf1, iLeaf1 = Temp;
            // create the new cut
            if ( !Ivy_CutDeriveNew( pCut, pCutNew, pCut->pArray[k], iLeaf0, iLeaf1 ) )
                continue;
            // add the cut
            Ivy_CutFindOrAddFilter( pCutStore, pCutNew );
            if ( pCutStore->nCuts == IVY_CUT_LIMIT )
                break;
        }
        if ( pCutStore->nCuts == IVY_CUT_LIMIT )
            break;
    }
    if ( pCutStore->nCuts == IVY_CUT_LIMIT )
        pCutStore->fSatur = 1;
    else
        pCutStore->fSatur = 0;
//    printf( "%d ", pCutStore->nCuts );
    Ivy_CutCompactAll( pCutStore );
//    printf( "%d \n", pCutStore->nCuts );
//    Ivy_CutPrintForNodes( pCutStore );
    return pCutStore;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_CutComputeAll( Ivy_Man_t * p, int nInputs )
{
    Ivy_Store_t * pStore;
    Ivy_Obj_t * pObj;
    int i, nCutsTotal, nCutsTotalM, nNodeTotal, nNodeOver;
    int clk = clock();
    if ( nInputs > IVY_CUT_INPUT )
    {
        printf( "Cannot compute cuts for more than %d inputs.\n", IVY_CUT_INPUT );
        return;
    }
    nNodeTotal = nNodeOver = 0;
    nCutsTotal = nCutsTotalM = -Ivy_ManNodeNum(p);
    Ivy_ManForEachObj( p, pObj, i )
    {
        if ( !Ivy_ObjIsNode(pObj) )
            continue;
        pStore = Ivy_CutComputeForNode( p, pObj, nInputs );
        nCutsTotal  += pStore->nCuts;
        nCutsTotalM += pStore->nCutsM;
        nNodeOver   += pStore->fSatur;
        nNodeTotal++;
    }
    printf( "All = %6d. Minus = %6d. Triv = %6d.   Node = %6d. Satur = %6d.  ", 
        nCutsTotal, nCutsTotalM, Ivy_ManPiNum(p) + Ivy_ManNodeNum(p), nNodeTotal, nNodeOver );
    PRT( "Time", clock() - clk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


