/**CFile****************************************************************

  FileName    [cgtMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Clock gating package.]

  Synopsis    [Decide what gate to use for what flop.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cgtMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cgtInt.h"
#include "sswInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Ssw_SmlCountXorImplication( Ssw_Sml_t * p, Aig_Obj_t * pObjLi, Aig_Obj_t * pObjLo, Aig_Obj_t * pCand );
extern int Ssw_SmlCheckXorImplication( Ssw_Sml_t * p, Aig_Obj_t * pObjLi, Aig_Obj_t * pObjLo, Aig_Obj_t * pCand );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Chooses what clock-gate to use for each register.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Cgt_ManDecide( Aig_Man_t * pAig, Vec_Vec_t * vGatesAll )
{
    Vec_Ptr_t * vGates;
    vGates = Vec_PtrStart( Saig_ManRegNum(pAig) );
    return vGates;
}

/**Function*************************************************************

  Synopsis    [Chooses what clock-gate to use for this register.]

  Description [Currently uses the naive approach: For each register, 
  choose the clock gate, which covers most of the transitions.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Cgt_ManDecideSimple( Aig_Man_t * pAig, Vec_Vec_t * vGatesAll )
{
    Ssw_Sml_t * pSml;
    Vec_Ptr_t * vGates, * vCands;
    Aig_Obj_t * pObjLi, * pObjLo, * pCand, * pCandBest;
    int i, k, nHitsCur, nHitsMax;
    vGates = Vec_PtrStart( Saig_ManRegNum(pAig) );
    pSml = Ssw_SmlSimulateSeq( pAig, 0, 32, 1 );
    Saig_ManForEachLiLo( pAig, pObjLi, pObjLo, i )
    {
        nHitsMax = 0;
        pCandBest = NULL;
        vCands = Vec_VecEntry( vGatesAll, i );
        Vec_PtrForEachEntry( vCands, pCand, k )
        {
            // check if this is indeed a clock-gate
            if ( !Ssw_SmlCheckXorImplication( pSml, pObjLi, pObjLo, pCand ) )
                printf( "Clock gate candidate is invalid!\n" );
            // find its characteristic number
            nHitsCur = Ssw_SmlCountXorImplication( pSml, pObjLi, pObjLo, pCand );
            if ( nHitsMax < nHitsCur )
            {
                nHitsMax = nHitsCur;
                pCandBest = pCand;
            }
        }
        if ( pCandBest != NULL )
            Vec_PtrWriteEntry( vGates, i, pCandBest );
    }
    Ssw_SmlStop( pSml );
    return vGates;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


