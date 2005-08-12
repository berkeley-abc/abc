/**CFile****************************************************************

  FileName    [simSupp.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Simulation to determine functional support.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: simSupp.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "sim.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
static int    Sim_ComputeSuppRound( Sim_Man_t * p, bool fUseTargets );
static int    Sim_ComputeSuppRoundNode( Sim_Man_t * p, int iNumCi, bool fUseTargets );
static void   Sim_ComputeSuppSetTargets( Sim_Man_t * p );
static void   Sim_UtilAssignFromFifo( Sim_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Compute functional supports of the primary outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sim_Man_t * Sim_ComputeSupp( Abc_Ntk_t * pNtk )
{
    Sim_Man_t * p;
    int i, nSolved;

//    srand( time(NULL) );
    srand( 0xedfeedfe );

    // start the simulation manager
    p = Sim_ManStart( pNtk );
    Sim_UtilComputeStrSupp( p );

    // compute functional support using one round of random simulation
    Sim_UtilAssignRandom( p );
    Sim_ComputeSuppRound( p, 0 );

    // set the support targets 
    Sim_ComputeSuppSetTargets( p );
printf( "Initial targets    = %5d.\n", Vec_PtrSizeSize(p->vSuppTargs) );
    if ( Vec_PtrSizeSize(p->vSuppTargs) == 0 )
        goto exit;

    // compute patterns using one round of random simulation
    Sim_UtilAssignRandom( p );
    nSolved = Sim_ComputeSuppRound( p, 1 );
printf( "First step targets = %5d.   Solved = %5d.\n", Vec_PtrSizeSize(p->vSuppTargs), nSolved );
    if ( Vec_PtrSizeSize(p->vSuppTargs) == 0 )
        goto exit;

    // simulate until saturation
    for ( i = 0; i < 10; i++ )
    {
        // compute additional functional support
//         Sim_UtilAssignFromFifo( p );
        Sim_UtilAssignRandom( p );
        nSolved = Sim_ComputeSuppRound( p, 1 );
printf( "Next step targets  = %5d.   Solved = %5d.\n", Vec_PtrSizeSize(p->vSuppTargs), nSolved );
        if ( Vec_PtrSizeSize(p->vSuppTargs) == 0 )
            goto exit;
    }

exit:
//    return p;
    Sim_ManStop( p );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Computes functional support using one round of simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sim_ComputeSuppRound( Sim_Man_t * p, bool fUseTargets )
{
    Vec_Int_t * vTargets;
    Abc_Obj_t * pNode;
    int i, Counter = 0;
    // perform one round of random simulation
    Sim_UtilSimulate( p, 0 );
    // iterate through the CIs and detect COs that depend on them
    Abc_NtkForEachCi( p->pNtk, pNode, i )
    {
        vTargets = p->vSuppTargs->pArray[i];
        if ( fUseTargets && vTargets->nSize == 0 )
            continue;
        Counter += Sim_ComputeSuppRoundNode( p, i, fUseTargets );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Computes functional support for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sim_ComputeSuppRoundNode( Sim_Man_t * p, int iNumCi, bool fUseTargets )
{
    Sim_Pat_t * pPat;
    Vec_Int_t * vTargets;
    Vec_Ptr_t * vNodesByLevel;
    Abc_Obj_t * pNodeCi, * pNode;
    int i, k, v, Output, LuckyPat, fType0, fType1;
    int Counter = 0;
    // collect nodes by level in the TFO of the CI 
    // (this procedure increments TravId of the collected nodes)
    pNodeCi       = Abc_NtkCi( p->pNtk, iNumCi );
    vNodesByLevel = Abc_DfsLevelized( pNodeCi, 0 );
    // complement the simulation info of the selected CI
    Sim_UtilFlipSimInfo( p, pNodeCi );
    // simulate the levelized structure of nodes
    Vec_PtrForEachEntryByLevel( vNodesByLevel, pNode, i, k )
    {
        fType0 = Abc_NodeIsTravIdCurrent( Abc_ObjFanin0(pNode) );
        fType1 = Abc_NodeIsTravIdCurrent( Abc_ObjFanin1(pNode) );
        Sim_UtilSimulateNode( p, pNode, 1, fType0, fType1 );
    }
    // set the simulation info of the affected COs
    if ( fUseTargets )
    {
        vTargets = p->vSuppTargs->pArray[iNumCi];
        for ( i = vTargets->nSize - 1; i >= 0; i-- )
        {
            // get the target output
            Output = vTargets->pArray[i];
            // get the target node
            pNode  = Abc_NtkCo( p->pNtk, Output );
            // the output should be in the cone
            assert( Abc_NodeIsTravIdCurrent(pNode) );

            // simulate the node
            Sim_UtilSimulateNode( p, pNode, 1, 1, 1 );

            // skip if the simulation info is equal
            if ( Sim_UtilCompareSimInfo( p, pNode ) )
                continue;

            // otherwise, we solved a new target
            Vec_IntRemove( vTargets, Output );
            Counter++;
            // make sure this variable is not yet detected
            assert( !Sim_SuppFunHasVar(p, Output, iNumCi) );
            // set this variable
            Sim_SuppFunSetVar( p, Output, iNumCi );
            
            // detect the differences in the simulation info
            Sim_UtilInfoDetectDiffs( p->vSim0->pArray[pNode->Id], p->vSim1->pArray[pNode->Id], p->nSimWords, p->vDiffs );
            // create new patterns
            Vec_IntForEachEntry( p->vDiffs, LuckyPat, k )
            {
                // set the new pattern
                pPat = Sim_ManPatAlloc( p );
                pPat->Input  = iNumCi;
                pPat->Output = Output;
                Abc_NtkForEachCi( p->pNtk, pNodeCi, v )
                    if ( Sim_SimInfoHasVar( p, pNodeCi, LuckyPat ) )
                        Sim_SetBit( pPat->pData, v );
                Vec_PtrPush( p->vFifo, pPat );
                break;
            }
        }
    }
    else
    {
        Abc_NtkForEachCo( p->pNtk, pNode, Output )
        {
            if ( !Abc_NodeIsTravIdCurrent( pNode ) )
                continue;
            Sim_UtilSimulateNode( p, pNode, 1, 1, 1 );
            if ( !Sim_UtilCompareSimInfo( p, pNode ) )
            {
                if ( !Sim_SuppFunHasVar(p, Output, iNumCi) )
                    Counter++;
                Sim_SuppFunSetVar( p, Output, iNumCi );
            }
        }
    }
    Vec_PtrFreeFree( vNodesByLevel );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Sets the simulation targets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_ComputeSuppSetTargets( Sim_Man_t * p )
{
    Abc_Obj_t * pNode;
    unsigned * pSuppStr, * pSuppFun;
    int i, k, Num;
    Abc_NtkForEachCo( p->pNtk, pNode, i )
    {
        pSuppStr = p->vSuppStr->pArray[pNode->Id];
        pSuppFun = p->vSuppFun->pArray[i];
        // find vars in the structural support that are not in the functional support
        Sim_UtilInfoDetectNews( pSuppFun, pSuppStr, p->nSuppWords, p->vDiffs );
        Vec_IntForEachEntry( p->vDiffs, Num, k )
            Vec_IntPush( p->vSuppTargs->pArray[Num], i );
    }
}

/**Function*************************************************************

  Synopsis    [Sets the new patterns from fifo.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilAssignFromFifo( Sim_Man_t * p )
{
    Sim_Pat_t * pPat;
    int i;
    for ( i = 0; i < p->nSimBits; i++ )
    {
        pPat = Vec_PtrPop( p->vFifo );

    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


