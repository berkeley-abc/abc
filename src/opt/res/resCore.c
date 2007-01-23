/**CFile****************************************************************

  FileName    [resCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resynthesis package.]

  Synopsis    [Top-level resynthesis procedure.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 15, 2007.]

  Revision    [$Id: resCore.c,v 1.00 2007/01/15 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "res.h"
#include "kit.h"
#include "satStore.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Entrace into the resynthesis package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkResynthesize( Abc_Ntk_t * pNtk, int nWindow, int nSimWords, int fVerbose, int fVeryVerbose )
{
    Int_Man_t * pMan;
    Sto_Man_t * pCnf;
    Res_Win_t * pWin;
    Res_Sim_t * pSim;
    Abc_Ntk_t * pAig;
    Abc_Obj_t * pObj;
    Hop_Obj_t * pFunc;
    Kit_Graph_t * pGraph;
    Vec_Vec_t * vResubs;
    Vec_Ptr_t * vFanins;
    Vec_Int_t * vMemory;
    unsigned * puTruth;
    int i, k, nNodesOld, nFanins;
    assert( Abc_NtkHasAig(pNtk) );
    assert( nWindow > 0 && nWindow < 100 );
    vMemory = Vec_IntAlloc(0);
    // start the interpolation manager
    pMan = Int_ManAlloc( 512 );
    // start the window
    pWin = Res_WinAlloc();
    pSim = Res_SimAlloc( nSimWords );
    // set the number of levels
    Abc_NtkLevel( pNtk );
    // try resynthesizing nodes in the topological order
    nNodesOld = Abc_NtkObjNumMax(pNtk);
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( !Abc_ObjIsNode(pObj) )
            continue;
        if ( pObj->Id > nNodesOld )
            break;
        // create the window for this node
        if ( !Res_WinCompute(pObj, nWindow/10, nWindow%10, pWin) )
            continue;
        // collect the divisors
        Res_WinDivisors( pWin, pObj->Level - 1 );
        // create the AIG for the window
        pAig = Res_WndStrash( pWin );
        // prepare simulation info
        if ( !Res_SimPrepare( pSim, pAig ) )
        {
            Abc_NtkDelete( pAig );
            continue;
        }
        // find resub candidates for the node
        vResubs = Res_FilterCandidates( pWin, pSim );
        if ( vResubs )
        {
            // iterate through the resubstitutions
            Vec_VecForEachLevel( vResubs, vFanins, k )
            {
                extern Hop_Obj_t * Kit_GraphToHop( Hop_Man_t * pMan, Kit_Graph_t * pGraph );
                pCnf = Res_SatProveUnsat( pAig, vFanins );
                if ( pCnf == NULL )
                    continue;
                // interplate this proof
                nFanins = Int_ManInterpolate( pMan, pCnf, fVerbose, &puTruth );
                assert( nFanins == Vec_PtrSize(vFanins) - 2 );
                Sto_ManFree( pCnf );
                // transform interpolant into the AIG
                pGraph = Kit_TruthToGraph( puTruth, nFanins, vMemory );
                // derive the AIG for the decomposition tree
                pFunc = Kit_GraphToHop( pNtk->pManFunc, pGraph );
                Kit_GraphFree( pGraph );
                // update the network
                if ( pFunc == NULL )
                    Res_UpdateNetwork( pObj, vFanins, pFunc, pWin->vLevels );
                break;
            }
            Vec_VecFree( vResubs );
        }
        Abc_NtkDelete( pAig );
    }
    Res_WinFree( pWin );
    Res_SimFree( pSim );
    Int_ManFree( pMan );
    Vec_IntFree( vMemory );
    // check the resulting network
    if ( !Abc_NtkCheck( pNtk ) )
    {
        fprintf( stdout, "Abc_NtkResynthesize(): Network check has failed.\n" );
        return 0;
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


