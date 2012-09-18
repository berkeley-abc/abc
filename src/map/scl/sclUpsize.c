/**CFile****************************************************************

  FileName    [sclUpsize.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Selective increase of gate sizes.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclUpsize.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclInt.h"
#include "sclMan.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Vec_Int_t * Abc_SclFindCriticalCoWindow( SC_Man * p, int Window );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect near-critical COs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SclFindCriticalCoWindow( SC_Man * p, int Window )
{
    float fMaxArr = Abc_SclGetMaxDelay( p ) * (100.0 - Window) / 100.0;
    Vec_Int_t * vPivots;
    Abc_Obj_t * pObj;
    int i;
    vPivots = Vec_IntAlloc( 100 );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        if ( Abc_SclObjTimeMax(p, pObj) >= fMaxArr )
            Vec_IntPush( vPivots, Abc_ObjId(pObj) );
    assert( Vec_IntSize(vPivots) > 0 );
    return vPivots;
}

/**Function*************************************************************

  Synopsis    [Collect near-critical internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclFindCriticalNodeWindow_rec( SC_Man * p, Abc_Obj_t * pObj, Vec_Int_t * vPath, float fSlack )
{
    Abc_Obj_t * pNext;
    float fArrMax, fSlackFan;
    int i;
    if ( Abc_ObjIsCi(pObj) )
        return;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    assert( Abc_ObjIsNode(pObj) );
    // compute the max arrival time of the fanins
    fArrMax = Abc_SclGetMaxDelayNodeFanins( p, pObj );
    // traverse all fanins whose arrival times are within a window
    Abc_ObjForEachFanin( pObj, pNext, i )
    {
        fSlackFan = fSlack - (fArrMax - Abc_SclObjTimeMax(p, pNext));
        if ( fSlackFan >= 0 )
            Abc_SclFindCriticalNodeWindow_rec( p, pNext, vPath, fSlackFan );
    }
    Vec_IntPush( vPath, Abc_ObjId(pObj) );
}
Vec_Int_t * Abc_SclFindCriticalNodeWindow( SC_Man * p, Vec_Int_t * vPathCos, int Window )
{
    float fMaxArr = Abc_SclGetMaxDelay( p );
    float fSlack = fMaxArr * Window / 100.0;
    Vec_Int_t * vPath = Vec_IntAlloc( 100 );
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkIncrementTravId( p->pNtk ); 
    Abc_NtkForEachObjVec( vPathCos, p->pNtk, pObj, i )
        Abc_SclFindCriticalNodeWindow_rec( p, Abc_ObjFanin0(pObj), vPath, fSlack - (fMaxArr - Abc_SclObjTimeMax(p, pObj)) );
    // label critical nodes
    Abc_NtkForEachObjVec( vPath, p->pNtk, pObj, i )
        pObj->fMarkA = 1;
    return vPath;  
}
void Abc_SclUnmarkCriticalNodeWindow( SC_Man * p, Vec_Int_t * vPath )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachObjVec( vPath, p->pNtk, pObj, i )
        pObj->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Find the array of nodes to be updated.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SclFindNodesToUpdate( Abc_Obj_t * pObj )
{
    Vec_Int_t * vNodes;
    Abc_Obj_t * pNext, * pNext2;
    int i, k, Start;
    assert( Abc_ObjIsNode(pObj) );
    assert( pObj->fMarkA );
    vNodes = Vec_IntAlloc( 16 );
    // collect fanins, node, and fanouts
    Abc_ObjForEachFanin( pObj, pNext, i )
        if ( Abc_ObjIsNode(pNext) )
            Vec_IntPush( vNodes, Abc_ObjId(pNext) );
    Vec_IntPush( vNodes, Abc_ObjId(pObj) );
    Abc_ObjForEachFanout( pObj, pNext, i )
        if ( Abc_ObjIsNode(pNext) && pNext->fMarkA )
            Vec_IntPush( vNodes, Abc_ObjId(pNext) ), pNext->fMarkB = 1;
    // remember this position
    Start = Vec_IntSize(vNodes);
    // label collected nodes
    Abc_ObjForEachFanout( pObj, pNext, i )
        if ( Abc_ObjIsNode(pNext) && pNext->fMarkA )
            Abc_ObjForEachFanout( pNext, pNext2, k )
                if ( Abc_ObjIsNode(pNext2) && pNext2->fMarkA && !pNext2->fMarkB )
                    Vec_IntPush( vNodes, Abc_ObjId(pNext2) ), pNext2->fMarkB = 1;
    // clean the fanouts
    Abc_NtkForEachObjVec( vNodes, pObj->pNtk, pNext, i )
        pNext->fMarkB = 0;
    // save position at the last entry
    Vec_IntPush( vNodes, Start );
    return vNodes;
}


/**Function*************************************************************

  Synopsis    [Compute gain in changing the gate size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Abc_SclFindGain( SC_Man * p, Vec_Int_t * vCone )
{
    double dGain = 0;
    Abc_Obj_t * pObj;
    int i, Start;
    Start = Vec_IntEntryLast( vCone );
    vCone->nSize--;

    Abc_SclConeStore( p, vCone );
    Abc_SclTimeCone( p, vCone );
    Abc_NtkForEachObjVecStart( vCone, p->pNtk, pObj, i, Start )
        dGain += Abc_SclObjGain( p, pObj );
    Abc_SclConeRestore( p, vCone );
    dGain /= (Vec_IntSize(vCone) - Start);

    vCone->nSize++;
    return (float)dGain;
}

/**Function*************************************************************

  Synopsis    [Begin by upsizing gates will many fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SclFindUpsizes( SC_Man * p, Vec_Int_t * vPathNodes, int Ratio )
{
    SC_Cell * pCellOld, * pCellNew;
    Vec_Flt_t * vSavings;
    Vec_Int_t * vBests;
    Vec_Int_t * vCone;
    Vec_Int_t * vUpdates;
    Abc_Obj_t * pObj;
    float dGain, dGainBest = 0;
    int i, k, Entry, gateBest = -1;
    int nUpsizes = 0;

    vSavings = Vec_FltAlloc( Vec_IntSize(vPathNodes) );
    vBests = Vec_IntAlloc( Vec_IntSize(vPathNodes) );
    Abc_NtkForEachObjVec( vPathNodes, p->pNtk, pObj, i )
    {
        dGainBest = 0;
        pCellOld  = Abc_SclObjCell( p, pObj );
        assert( pCellOld->Id == Vec_IntEntry(p->vGates, Abc_ObjId(pObj)) );
        // try different gate sizes for this node
        vCone = Abc_SclFindNodesToUpdate( pObj );
        SC_RingForEachCell( pCellOld, pCellNew, k )
        {
            Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), pCellNew->Id );
    //printf( "changing %s for %s at node %d   ", pCellOld->pName, pCellNew->pName, Abc_ObjId(pObj) );
            Abc_SclUpdateLoad( p, pObj, pCellOld, pCellNew );
            dGain = Abc_SclFindGain( p, vCone );
            Abc_SclUpdateLoad( p, pObj, pCellNew, pCellOld );
    //printf( "gain is %f\n", dGain );
            if ( dGainBest < dGain )
            {
                dGainBest = dGain;
                gateBest = pCellNew->Id;
            }
        }
        Vec_IntFree( vCone );
        Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), pCellOld->Id );
        Vec_FltPush( vSavings, dGainBest );
        Vec_IntPush( vBests, gateBest );
    }
    assert( Vec_IntSize(vBests) == Vec_IntSize(vPathNodes) );

    // we have computed the gains - find the best ones
    {
        Vec_Int_t * vCosts;
        int * pPerm;
        float Max = Vec_FltFindMax( vSavings );
        float Factor = 1.0 * (1<<28) / Max;
        float This;
        int i, Limit;
        // find a good factor
        vCosts = Vec_IntAlloc( Vec_FltSize(vSavings) );
        Vec_FltForEachEntry( vSavings, This, i )
        {
            Vec_IntPush( vCosts, (int)(This * Factor) );
            assert( (int)(This * Factor) < (1<<30) );
        }
        pPerm = Abc_QuickSortCost( Vec_IntArray(vCosts), Vec_IntSize(vCosts), 1 );
        assert( Vec_FltEntry(vSavings, pPerm[0]) >= Vec_FltEntry(vSavings, pPerm[Vec_FltSize(vSavings)-1]) );
        // find those that are good to update
        Limit = Abc_MinInt( 1, (int)(0.01 * Ratio * Vec_IntSize(vBests)) ); 
        vUpdates = Vec_IntAlloc( Limit );
        for ( i = 0; i < Limit; i++ )
            if ( Vec_FltEntry(vSavings, pPerm[i]) > 0 )
                Vec_IntPush( vUpdates, pPerm[i] );
    }

    // update the network
    Vec_IntForEachEntry( vUpdates, Entry, i )
    {
        pObj = Abc_NtkObj( p->pNtk, Vec_IntEntry(vPathNodes, Entry) );
        // find new gate
        pCellOld = Abc_SclObjCell( p, pObj );
        pCellNew = SC_LibCell( p->pLib, Vec_IntEntry(vBests, Abc_ObjId(pObj)) );
        assert( pCellNew != NULL );
        // update gate
        Abc_SclUpdateLoad( p, pObj, pCellOld, pCellNew );
        p->SumArea += pCellNew->area - pCellOld->area;
        Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), pCellNew->Id );
    }


    Vec_IntFree( vUpdates );
    Vec_IntFree( vBests );
    Vec_FltFree( vSavings );
    return nUpsizes;
}


/**Function*************************************************************

  Synopsis    [Print cumulative statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclUpsizePrint( SC_Man * p, int Iter, Vec_Int_t * vPathPos, Vec_Int_t * vPathNodes, int nUpsizes )
{
    printf( "Iter %3d  ",        Iter );
    printf( "PathPOs:%5d. ",     Vec_IntSize(vPathPos) );
    printf( "PathNodes:%6d. ",   Vec_IntSize(vPathNodes) );
    printf( "Resized:%5d. ",     nUpsizes );
    printf( "D: " );
    printf( "%.2f -> %.2f ps ",  SC_LibTimePs(p->pLib, p->MaxDelay0), SC_LibTimePs(p->pLib, p->MaxDelay) );
    printf( "(%+.1f %%).  ",     100.0 * (p->MaxDelay - p->MaxDelay0)/ p->MaxDelay0 );
    printf( "A: " );
    printf( "%.2f -> %.2f ",     p->SumArea0, p->SumArea );
    printf( "(%+.1f %%).  ",     100.0 * (p->SumArea - p->SumArea0)/ p->SumArea0 );
    Abc_PrintTime( 1, "Time",    clock() - p->clkStart );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclUpsizePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int Window, int Ratio, int nIters, int fVerbose )
{
    SC_Man * p;
    Vec_Int_t * vPathPos;    // critical POs
    Vec_Int_t * vPathNodes;  // critical nodes and PIs
    int i, nUpsizes;

    // prepare the manager; collect init stats
    p = Abc_SclManStart( pLib, pNtk, 1 );

    // perform upsizing
    for ( i = 0; i < nIters; i++ )
    {
        vPathPos   = Abc_SclFindCriticalCoWindow( p, Window );
        vPathNodes = Abc_SclFindCriticalNodeWindow( p, vPathPos, Window );
        nUpsizes   = Abc_SclFindUpsizes( p, vPathNodes, Ratio );
        Abc_SclUnmarkCriticalNodeWindow( p, vPathNodes );
        Abc_SclTimeNtkRecompute( p, &p->SumArea, &p->MaxDelay );
        Abc_SclUpsizePrint( p, i, vPathPos, vPathNodes, nUpsizes );
        Vec_IntFree( vPathPos );
        Vec_IntFree( vPathNodes );
    }
//    Abc_NtkCleanMarkAB( pNtk );

    // save the result and quit
    Abc_SclManSetGates( pLib, pNtk, p->vGates ); // updates gate pointers
    Abc_SclManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

