/**CFile****************************************************************

  FileName    [fraDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Fraig FRAIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraDfs.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_CheckTfi_rec( Fra_Man_t * p, Aig_Obj_t * pNode, Aig_Obj_t * pOld )
{
    // check the trivial cases
    if ( pNode == NULL )
        return 0;
//    if ( pNode->Id < pOld->Id ) // cannot use because of choicesof pNode
//        return 0;
    if ( pNode == pOld )
        return 1;
    // skip the visited node
    if ( Aig_ObjIsTravIdCurrent(p->pManFraig, pNode) )
        return 0;
    Aig_ObjSetTravIdCurrent(p->pManFraig, pNode);
    // check the children
    if ( Fra_CheckTfi_rec( p, Aig_ObjFanin0(pNode), pOld ) )
        return 1;
    if ( Fra_CheckTfi_rec( p, Aig_ObjFanin1(pNode), pOld ) )
        return 1;
    // check equivalent nodes
    return Fra_CheckTfi_rec( p, Fra_ObjReprFra(pNode), pOld );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_CheckTfi( Fra_Man_t * p, Aig_Obj_t * pNew, Aig_Obj_t * pOld )
{
    assert( !Aig_IsComplement(pNew) );
    assert( !Aig_IsComplement(pOld) );
    Aig_ManIncrementTravId( p->pManFraig );
    return Fra_CheckTfi_rec( p, pNew, pOld );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


