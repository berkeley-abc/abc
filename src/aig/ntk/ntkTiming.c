/**CFile****************************************************************

  FileName    [ntkTiming.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Manipulation of timing information.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntkTiming.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern void * Abc_FrameReadLibLut();   

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrepareTiming( Ntk_Man_t * pNtk )
{
    Ntk_Obj_t * pObj;
    int i;
    Ntk_ManForEachObj( pNtk, pObj, i )
    {
        pObj->tArrival = pObj->tSlack = 0.0;
        pObj->tRequired = AIG_INFINITY;
    }
}

/**Function*************************************************************

  Synopsis    [Sorts the pins in the decreasing order of delays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManDelayTraceSortPins( Ntk_Obj_t * pNode, int * pPinPerm, float * pPinDelays )
{
    Ntk_Obj_t * pFanin;
    int i, j, best_i, temp;
    // start the trivial permutation and collect pin delays
    Ntk_ObjForEachFanin( pNode, pFanin, i )
    {
        pPinPerm[i] = i;
        pPinDelays[i] = Ntk_ObjArrival(pFanin);
    }
    // selection sort the pins in the decreasible order of delays
    // this order will match the increasing order of LUT input pins
    for ( i = 0; i < Ntk_ObjFaninNum(pNode)-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < Ntk_ObjFaninNum(pNode); j++ )
            if ( pPinDelays[pPinPerm[j]] > pPinDelays[pPinPerm[best_i]] )
                best_i = j;
        if ( best_i == i )
            continue;
        temp = pPinPerm[i]; 
        pPinPerm[i] = pPinPerm[best_i]; 
        pPinPerm[best_i] = temp;
    }
    // verify
    assert( Ntk_ObjFaninNum(pNode) == 0 || pPinPerm[0] < Ntk_ObjFaninNum(pNode) );
    for ( i = 1; i < Ntk_ObjFaninNum(pNode); i++ )
    {
        assert( pPinPerm[i] < Ntk_ObjFaninNum(pNode) );
        assert( pPinDelays[pPinPerm[i-1]] >= pPinDelays[pPinPerm[i]] );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Ntk_ManDelayTraceLut( Ntk_Man_t * pNtk, If_Lib_t * pLutLib )
{
    int fUseSorting = 1;
    int pPinPerm[32];
    float pPinDelays[32];
    Ntk_Obj_t * pObj, * pFanin;
    Vec_Ptr_t * vNodes;
    float tArrival, tRequired, tSlack, * pDelays;
    int i, k;

    // get the library
    if ( pLutLib && pLutLib->LutMax < Ntk_ManGetFaninMax(pNtk) )
    {
        printf( "The max LUT size (%d) is less than the max fanin count (%d).\n", 
            pLutLib->LutMax, Ntk_ManGetFaninMax(pNtk) );
        return -AIG_INFINITY;
    }

    // compute the reverse order of all objects
    vNodes = Ntk_ManDfsReverse( pNtk );

    // initialize the arrival times
    Abc_NtkPrepareTiming( pNtk );

    // propagate arrival times
    Tim_ManIncrementTravId( pNtk->pManTime );
    Ntk_ManForEachObj( pNtk, pObj, i )
    {
        if ( Ntk_ObjIsNode(pObj) )
        {
            tArrival = -AIG_INFINITY;
            if ( pLutLib == NULL )
            {
                Ntk_ObjForEachFanin( pObj, pFanin, k )
                    if ( tArrival < Ntk_ObjArrival(pFanin) + 1.0 )
                        tArrival = Ntk_ObjArrival(pFanin) + 1.0;
            }
            else if ( !pLutLib->fVarPinDelays )
            {
                pDelays = pLutLib->pLutDelays[Ntk_ObjFaninNum(pObj)];
                Ntk_ObjForEachFanin( pObj, pFanin, k )
                    if ( tArrival < Ntk_ObjArrival(pFanin) + pDelays[0] )
                        tArrival = Ntk_ObjArrival(pFanin) + pDelays[0];
            }
            else
            {
                pDelays = pLutLib->pLutDelays[Ntk_ObjFaninNum(pObj)];
                if ( fUseSorting )
                {
                    Ntk_ManDelayTraceSortPins( pObj, pPinPerm, pPinDelays );
                    Ntk_ObjForEachFanin( pObj, pFanin, k ) 
                        if ( tArrival < Ntk_ObjArrival(Ntk_ObjFanin(pObj,pPinPerm[k])) + pDelays[k] )
                            tArrival = Ntk_ObjArrival(Ntk_ObjFanin(pObj,pPinPerm[k])) + pDelays[k];
                }
                else
                {
                    Ntk_ObjForEachFanin( pObj, pFanin, k )
                        if ( tArrival < Ntk_ObjArrival(pFanin) + pDelays[k] )
                            tArrival = Ntk_ObjArrival(pFanin) + pDelays[k];
                }
            }
            if ( Ntk_ObjFaninNum(pObj) == 0 )
                tArrival = 0.0;
        }
        else if ( Ntk_ObjIsCi(pObj) )
        {
            tArrival = Tim_ManGetPiArrival( pNtk->pManTime, pObj->PioId );
        }
        else if ( Ntk_ObjIsCo(pObj) )
        {
            tArrival = Ntk_ObjArrival( Ntk_ObjFanin0(pObj) );
            Tim_ManSetPoArrival( pNtk->pManTime, pObj->PioId, tArrival );
        }
        else
            assert( 0 );
        Ntk_ObjSetArrival( pObj, tArrival );
    }

    // get the latest arrival times
    tArrival = -AIG_INFINITY;
    Ntk_ManForEachPo( pNtk, pObj, i )
        if ( tArrival < Ntk_ObjArrival(Ntk_ObjFanin0(pObj)) )
            tArrival = Ntk_ObjArrival(Ntk_ObjFanin0(pObj));

    // initialize the required times
    Ntk_ManForEachPo( pNtk, pObj, i )
        if ( Ntk_ObjRequired(Ntk_ObjFanin0(pObj)) > tArrival )
            Ntk_ObjSetRequired( Ntk_ObjFanin0(pObj), tArrival );

    // propagate the required times
    Tim_ManIncrementTravId( pNtk->pManTime );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        if ( Ntk_ObjIsNode(pObj) )
        {
            if ( pLutLib == NULL )
            {
                tRequired = Ntk_ObjRequired(pObj) - (float)1.0;
                Ntk_ObjForEachFanin( pObj, pFanin, k )
                    if ( Ntk_ObjRequired(pFanin) > tRequired )
                        Ntk_ObjSetRequired( pFanin, tRequired );
            }
            else if ( !pLutLib->fVarPinDelays )
            {
                pDelays = pLutLib->pLutDelays[Ntk_ObjFaninNum(pObj)];
                tRequired = Ntk_ObjRequired(pObj) - pDelays[0];
                Ntk_ObjForEachFanin( pObj, pFanin, k )
                    if ( Ntk_ObjRequired(pFanin) > tRequired )
                        Ntk_ObjSetRequired( pFanin, tRequired );
            }
            else 
            {
                pDelays = pLutLib->pLutDelays[Ntk_ObjFaninNum(pObj)];
                if ( fUseSorting )
                {
                    Ntk_ManDelayTraceSortPins( pObj, pPinPerm, pPinDelays );
                    Ntk_ObjForEachFanin( pObj, pFanin, k )
                    {
                        tRequired = Ntk_ObjRequired(pObj) - pDelays[k];
                        if ( Ntk_ObjRequired(Ntk_ObjFanin(pObj,pPinPerm[k])) > tRequired )
                            Ntk_ObjSetRequired( Ntk_ObjFanin(pObj,pPinPerm[k]), tRequired );
                    }
                }
                else
                {
                    Ntk_ObjForEachFanin( pObj, pFanin, k )
                    {
                        tRequired = Ntk_ObjRequired(pObj) - pDelays[k];
                        if ( Ntk_ObjRequired(pFanin) > tRequired )
                            Ntk_ObjSetRequired( pFanin, tRequired );
                    }
                }
            }
        }
        else if ( Ntk_ObjIsCi(pObj) )
        {
            tRequired = Ntk_ObjRequired(pObj);
            Tim_ManSetPiRequired( pNtk->pManTime, pObj->PioId, tRequired );
        }
        else if ( Ntk_ObjIsCo(pObj) )
        {
            tRequired = Tim_ManGetPoRequired( pNtk->pManTime, pObj->PioId );
            if ( Ntk_ObjRequired(Ntk_ObjFanin0(pObj)) > tRequired )
                Ntk_ObjSetRequired( Ntk_ObjFanin0(pObj), tRequired );
        }

        // set slack for this object
        tSlack = Ntk_ObjRequired(pObj) - Ntk_ObjArrival(pObj);
        assert( tSlack + 0.001 > 0.0 );
        Ntk_ObjSetSlack( pObj, tSlack < 0.0 ? 0.0 : tSlack );
    }
    Vec_PtrFree( vNodes );
    return tArrival;
}

/**Function*************************************************************

  Synopsis    [Delay tracing of the LUT mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManDelayTracePrint( Ntk_Man_t * pNtk, If_Lib_t * pLutLib )
{
    Ntk_Obj_t * pNode;
    int i, Nodes, * pCounters;
    float tArrival, tDelta, nSteps, Num;
    // get the library
    if ( pLutLib && pLutLib->LutMax < Ntk_ManGetFaninMax(pNtk) )
    {
        printf( "The max LUT size (%d) is less than the max fanin count (%d).\n", 
            pLutLib->LutMax, Ntk_ManGetFaninMax(pNtk) );
        return;
    }
    // decide how many steps
    nSteps = pLutLib ? 20 : Ntk_ManLevel(pNtk);
    pCounters = ALLOC( int, nSteps + 1 );
    memset( pCounters, 0, sizeof(int)*(nSteps + 1) );
    // perform delay trace
    tArrival = Ntk_ManDelayTraceLut( pNtk, pLutLib );
    tDelta = tArrival / nSteps;
    // count how many nodes have slack in the corresponding intervals
    Ntk_ManForEachNode( pNtk, pNode, i )
    {
        if ( Ntk_ObjFaninNum(pNode) == 0 )
            continue;
        Num = Ntk_ObjSlack(pNode) / tDelta;
        if ( Num > nSteps )
            continue;
        assert( Num >=0 && Num <= nSteps );
        pCounters[(int)Num]++;
    }
    // print the results
    printf( "Max delay = %6.2f. Delay trace using %s model:\n", tArrival, pLutLib? "LUT library" : "unit-delay" );
    Nodes = 0;
    for ( i = 0; i < nSteps; i++ )
    {
        Nodes += pCounters[i];
        printf( "%3d %s : %5d  (%6.2f %%)\n", pLutLib? 5*(i+1) : i+1, 
            pLutLib? "%":"lev", Nodes, 100.0*Nodes/Ntk_ManNodeNum(pNtk) );
    }
    free( pCounters );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


