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
#include "resInt.h"
#include "kit.h"
#include "satStore.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Res_Man_t_ Res_Man_t;
struct Res_Man_t_
{
    // general parameters
    Res_Par_t *   pPars;
    // specialized manager
    Res_Win_t *   pWin;          // windowing manager
    Abc_Ntk_t *   pAig;          // the strashed window
    Res_Sim_t *   pSim;          // simulation manager
    Sto_Man_t *   pCnf;          // the CNF of the SAT problem
    Int_Man_t *   pMan;          // interpolation manager;
    Vec_Int_t *   vMem;          // memory for intermediate SOPs
    Vec_Vec_t *   vResubs;       // resubstitution candidates
    Vec_Vec_t *   vLevels;       // levelized structure for updating
    // statistics
    int           nWins;         // the number of windows tried
    int           nWinNodes;     // the total number of window nodes
    int           nDivNodes;     // the total number of divisors
    int           nCandSets;     // the total number of candidates
    int           nProvedSets;   // the total number of proved groups
    int           nSimEmpty;     // the empty simulation info
    // runtime
    int           timeWin;       // windowing
    int           timeDiv;       // divisors
    int           timeAig;       // strashing
    int           timeSim;       // simulation
    int           timeCand;      // resubstitution candidates
    int           timeSat;       // SAT solving
    int           timeInt;       // interpolation 
    int           timeUpd;       // updating  
    int           timeTotal;     // total runtime
};

extern Hop_Obj_t * Kit_GraphToHop( Hop_Man_t * pMan, Kit_Graph_t * pGraph );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocate resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Res_Man_t * Res_ManAlloc( Res_Par_t * pPars )
{
    Res_Man_t * p;
    p = ALLOC( Res_Man_t, 1 );
    memset( p, 0, sizeof(Res_Man_t) );
    assert( pPars->nWindow > 0 && pPars->nWindow < 100 );
    assert( pPars->nCands > 0 && pPars->nCands < 100 );
    p->pPars = pPars;
    p->pWin = Res_WinAlloc();
    p->pSim = Res_SimAlloc( pPars->nSimWords );
    p->pMan = Int_ManAlloc( 512 );
    p->vMem = Vec_IntAlloc( 0 );
    p->vResubs = Vec_VecStart( pPars->nCands );
    p->vLevels = Vec_VecStart( 32 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocate resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_ManFree( Res_Man_t * p )
{
    if ( p->pPars->fVerbose )
    {
        printf( "Winds = %d. ", p->nWins );
        printf( "Nodes = %d. (Ave = %5.1f)  ", p->nWinNodes, 1.0*p->nWinNodes/p->nWins );
        printf( "Divs = %d. (Ave = %5.1f)  ",  p->nDivNodes, 1.0*p->nDivNodes/p->nWins );
        printf( "\n" );
        printf( "SimEmpt = %d. ", p->nSimEmpty );
        printf( "Cands = %d. ", p->nCandSets );
        printf( "Proved = %d. ", p->nProvedSets );
        printf( "\n" );

        PRT( "Windowing  ", p->timeWin );
        PRT( "Divisors   ", p->timeDiv );
        PRT( "Strashing  ", p->timeAig );
        PRT( "Simulation ", p->timeSim );
        PRT( "Candidates ", p->timeCand );
        PRT( "SAT solver ", p->timeSat );
        PRT( "Interpol   ", p->timeInt );
        PRT( "Undating   ", p->timeUpd );
        PRT( "TOTAL      ", p->timeTotal );
    }
    Res_WinFree( p->pWin );
    if ( p->pAig ) Abc_NtkDelete( p->pAig );
    Res_SimFree( p->pSim );
    if ( p->pCnf ) Sto_ManFree( p->pCnf );
    Int_ManFree( p->pMan );
    Vec_IntFree( p->vMem );
    Vec_VecFree( p->vResubs );
    Vec_VecFree( p->vLevels );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Entrace into the resynthesis package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkResynthesize( Abc_Ntk_t * pNtk, Res_Par_t * pPars )
{
    Res_Man_t * p;
    Abc_Obj_t * pObj;
    Hop_Obj_t * pFunc;
    Kit_Graph_t * pGraph;
    Vec_Ptr_t * vFanins;
    unsigned * puTruth;
    int i, k, RetValue, nNodesOld, nFanins;
    int clk, clkTotal = clock();
    assert( Abc_NtkHasAig(pNtk) );

    // start the manager
    p = Res_ManAlloc( pPars );
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
clk = clock();
        RetValue = Res_WinCompute( pObj, p->pPars->nWindow/10, p->pPars->nWindow%10, p->pWin );
p->timeWin += clock() - clk;
        if ( !RetValue )
            continue;

        p->nWins++;
        p->nWinNodes += Vec_VecSizeSize( p->pWin->vLevels );

        // collect the divisors
clk = clock();
        Res_WinDivisors( p->pWin, pObj->Level - 1 );
p->timeDiv += clock() - clk;
        p->nDivNodes += Vec_PtrSize( p->pWin->vDivs );

        // create the AIG for the window
clk = clock();
        if ( p->pAig ) Abc_NtkDelete( p->pAig );
        p->pAig = Res_WndStrash( p->pWin );
p->timeAig += clock() - clk;

        if ( p->pPars->fVeryVerbose )
        {
            printf( "%5d : ", pObj->Id );
            printf( "Win = %3d/%4d/%3d ", Vec_PtrSize(p->pWin->vLeaves), Vec_VecSizeSize(p->pWin->vLevels), Vec_PtrSize(p->pWin->vRoots) );
            printf( "D = %3d ", Vec_PtrSize(p->pWin->vDivs) );
            printf( "D+ = %3d ", p->pWin->nDivsPlus );
            printf( "AIG = %4d ", Abc_NtkNodeNum(p->pAig) );
            printf( "\n" );
        }

        // prepare simulation info
clk = clock();
        RetValue = Res_SimPrepare( p->pSim, p->pAig );
p->timeSim += clock() - clk;
        if ( !RetValue )
        {
            p->nSimEmpty++;
            continue;
        }

        // find resub candidates for the node
clk = clock();
        RetValue = Res_FilterCandidates( p->pWin, p->pAig, p->pSim, p->vResubs );
p->timeCand += clock() - clk;
        p->nCandSets += RetValue;
        if ( RetValue == 0 )
            continue;

        // iterate through candidate resubstitutions
        Vec_VecForEachLevel( p->vResubs, vFanins, k )
        {
            if ( Vec_PtrSize(vFanins) == 0 )
                break;

            // solve the SAT problem and get clauses
clk = clock();
            if ( p->pCnf ) Sto_ManFree( p->pCnf );
            p->pCnf = Res_SatProveUnsat( p->pAig, vFanins );
p->timeSat += clock() - clk;
            if ( p->pCnf == NULL )
            {
//                printf( " Sat\n" );
                continue;
            }
//            printf( " Unsat\n" );

            // write it into a file
//            Sto_ManDumpClauses( p->pCnf, "trace.cnf" );

            p->nProvedSets++;

            // interplate the problem if it was UNSAT
clk = clock();
            RetValue = Int_ManInterpolate( p->pMan, p->pCnf, p->pPars->fVerbose, &puTruth );
p->timeInt += clock() - clk;
            assert( RetValue == Vec_PtrSize(vFanins) - 2 );

            if ( puTruth )
            {
                Extra_PrintBinary( stdout, puTruth, 1 << RetValue );
                printf( "\n" );
            }

            continue;
            
            // transform interpolant into the AIG
            pGraph = Kit_TruthToGraph( puTruth, nFanins, p->vMem );

            // derive the AIG for the decomposition tree
            pFunc = Kit_GraphToHop( pNtk->pManFunc, pGraph );
            Kit_GraphFree( pGraph );

            // update the network
clk = clock();
            Res_UpdateNetwork( pObj, vFanins, pFunc, p->vLevels );
p->timeUpd += clock() - clk;
            break;
        }
    }

    // quit resubstitution manager
p->timeTotal = clock() - clkTotal;
    Res_ManFree( p );

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


