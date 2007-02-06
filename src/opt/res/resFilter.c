/**CFile****************************************************************

  FileName    [resFilter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resynthesis package.]

  Synopsis    [Filtering resubstitution candidates.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 15, 2007.]

  Revision    [$Id: resFilter.c,v 1.00 2007/01/15 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "resInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static unsigned * Res_FilterCollectFaninInfo( Res_Win_t * pWin, Res_Sim_t * pSim, unsigned uMask );
static int        Res_FilterCriticalFanin( Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Finds sets of feasible candidates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_FilterCandidatesNets( Res_Win_t * pWin, Abc_Ntk_t * pAig, Res_Sim_t * pSim, Vec_Vec_t * vResubs, Vec_Vec_t * vResubsW )
{
    Abc_Obj_t * pFanin, * pFanin2;
    unsigned * pInfo;
    int Counter, RetValue, i, k;

    // check that the info the node is one
    pInfo = Vec_PtrEntry( pSim->vOuts, 1 );
    RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
    if ( RetValue == 0 )
    {
//        printf( "Failed 1!\n" );
        return 0;
    }

    // collect the fanin info
    pInfo = Res_FilterCollectFaninInfo( pWin, pSim, ~0 );
    RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
    if ( RetValue == 0 )
    {
//        printf( "Failed 2!\n" );
        return 0;
    }

    // try removing fanins
//    printf( "Fanins: " );
    Counter = 0;
    Vec_VecClear( vResubs );
    Vec_VecClear( vResubsW );
    Abc_ObjForEachFanin( pWin->pNode, pFanin, i )
    {
        pInfo = Res_FilterCollectFaninInfo( pWin, pSim, ~(1 << i) );
        RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
        if ( RetValue )
        {
//            printf( "Node %4d. Candidate fanin %4d.\n", pWin->pNode->Id, pFanin->Id );

            // collect the nodes
            Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,0) );
            Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,1) );
            Abc_ObjForEachFanin( pWin->pNode, pFanin2, k )
            {
                if ( k != i )
                {
                    Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,2+k) );
                    Vec_VecPush( vResubsW, Counter, pFanin2 );
                }
            }
            Counter++;
        }
        if ( Counter == Vec_VecSize(vResubs) )
            break;            
//        printf( "%d", RetValue );
    }
//    printf( "\n\n" );
    return Counter;
}


/**Function*************************************************************

  Synopsis    [Finds sets of feasible candidates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_FilterCandidatesArea( Res_Win_t * pWin, Abc_Ntk_t * pAig, Res_Sim_t * pSim, Vec_Vec_t * vResubs, Vec_Vec_t * vResubsW )
{
    Abc_Obj_t * pFanin;
    unsigned * pInfo, * pInfo2;
    int Counter, RetValue, i, k, iBest;

    // check that the info the node is one
    pInfo = Vec_PtrEntry( pSim->vOuts, 1 );
    RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
    if ( RetValue == 0 )
    {
//        printf( "Failed 1!\n" );
        return 0;
    }

    // collect the fanin info
    pInfo = Res_FilterCollectFaninInfo( pWin, pSim, ~0 );
    RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
    if ( RetValue == 0 )
    {
//        printf( "Failed 2!\n" );
        return 0;
    }

    // try removing fanins
//    printf( "Fanins: " );
    Counter = 0;
    Vec_VecClear( vResubs );
    Vec_VecClear( vResubsW );
    // get the best fanins
    iBest = Res_FilterCriticalFanin( pWin->pNode );
    if ( iBest == -1 )
        return 0;

    // get the info without the critical fanin
    pInfo = Res_FilterCollectFaninInfo( pWin, pSim, ~(1 << iBest) );
    RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
    if ( RetValue )
    {
//        printf( "Can be done without one!\n" );
        // collect the nodes
        Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,0) );
        Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,1) );
        Abc_ObjForEachFanin( pWin->pNode, pFanin, k )
        {
            if ( k != iBest )
            {
                Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,2+k) );
                Vec_VecPush( vResubsW, Counter, pFanin );
            }
        }
        Counter++;
//        printf( "*" );
        return Counter;
    }

    // go through the divisors
    for ( i = Abc_ObjFaninNum(pWin->pNode) + 2; i < Abc_NtkPoNum(pAig); i++ )
    {
        pInfo2 = Vec_PtrEntry( pSim->vOuts, i );
        if ( !Abc_InfoIsOrOne( pInfo, pInfo2, pSim->nWordsOut ) )
            continue;
        // collect the nodes
        Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,0) );
        Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,1) );
        // collect the remaning fanins and the divisor
        Abc_ObjForEachFanin( pWin->pNode, pFanin, k )
        {
            if ( k != iBest )
            {
                Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,2+k) );
                Vec_VecPush( vResubsW, Counter, pFanin );
            }
        }
        // collect the divisor
        Vec_VecPush( vResubs, Counter, Abc_NtkPo(pAig,i) );
        Vec_VecPush( vResubsW, Counter, Vec_PtrEntry(pWin->vDivs, i-2-Abc_ObjFaninNum(pWin->pNode)) );
        Counter++;

        if ( Counter == Vec_VecSize(vResubs) )
            break;            
    }
    return Counter;
}


/**Function*************************************************************

  Synopsis    [Finds sets of feasible candidates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Res_FilterCollectFaninInfo( Res_Win_t * pWin, Res_Sim_t * pSim, unsigned uMask )
{
    Abc_Obj_t * pFanin;
    unsigned * pInfo;
    int i;
    pInfo = Vec_PtrEntry( pSim->vOuts, 0 );
    Abc_InfoClear( pInfo, pSim->nWordsOut );
    Abc_ObjForEachFanin( pWin->pNode, pFanin, i )
    {
        if ( uMask & (1 << i) )
            Abc_InfoOr( pInfo, Vec_PtrEntry(pSim->vOuts, 2+i), pSim->nWordsOut );
    }
    return pInfo;
}


/**Function*************************************************************

  Synopsis    [Returns the index of the most critical fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_FilterCriticalFanin( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin;
    int i, iBest = -1, CostMax = 0, CostCur;
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        if ( !Abc_ObjIsNode(pFanin) )
            continue;
        if ( Abc_ObjFanoutNum(pFanin) > 1 )
            continue;
        CostCur = Res_WinVisitMffc( pFanin );
        if ( CostMax < CostCur )
        {
            CostMax = CostCur;
            iBest = i;
        }
    }
//    if ( CostMax > 0 )
//        printf( "<%d>", CostMax );
    return iBest;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


