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
#include "res.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * Res_FilterCandidates( Res_Win_t * pWin, Res_Sim_t * pSim )
{
    unsigned * pInfo;
    Abc_Obj_t * pFanin;
    int i, RetValue;
    // check that the info the node is one
    pInfo = Vec_PtrEntry( pSim->vOuts, 1 );
    RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
    if ( RetValue == 0 )
        printf( "Failed 1!" );
    // collect the fanin info
    pInfo = Vec_PtrEntry( pSim->vOuts, 0 );
    Abc_InfoClear( pInfo, pSim->nWordsOut );
    Abc_ObjForEachFanin( pWin->pNode, pFanin, i )
        Abc_InfoOr( pInfo, Vec_PtrEntry( pSim->vOuts, 2+i ), pSim->nWordsOut );
    // check that the simulation info is constant 1
    RetValue = Abc_InfoIsOne( pInfo, pSim->nWordsOut );
    if ( RetValue == 0 )
        printf( "Failed 2!" );
    return NULL;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


