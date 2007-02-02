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

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Finds sets of feasible candidates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_FilterCandidates( Res_Win_t * pWin, Abc_Ntk_t * pAig, Res_Sim_t * pSim, Vec_Vec_t * vResubs, Vec_Vec_t * vResubsW )
{
    Abc_Obj_t * pFanin, * pFanin2;
    unsigned * pInfo;
    int Counter, RetValue, i, k;

    // check that the info the node is one
    pInfo = Vec_PtrEntry( pSim->vOuts, 1 );
    RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
    if ( RetValue == 0 )
        printf( "Failed 1!\n" );

    // collect the fanin info
    pInfo = Res_FilterCollectFaninInfo( pWin, pSim, ~0 );
    RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
    if ( RetValue == 0 )
        printf( "Failed 2!\n" );

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
//            printf( "Node %4d. Removing fanin %4d.\n", pWin->pNode->Id, Abc_ObjFaninId(pWin->pNode, i) );

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


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


