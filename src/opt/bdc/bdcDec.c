/**CFile****************************************************************

  FileName    [bdc_.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Truth-table-based bi-decomposition engine.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 30, 2007.]

  Revision    [$Id: bdc_.c,v 1.00 2007/01/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "bdcInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs one step of bi-decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Bdc_Fun_t * Bdc_ManDecompose_rec( Bdc_Man_t * p, Bdc_Isf_t * pIsf )
{
    Bdc_Fun_t * pFunc;
    Bdc_Isf_t IsfA, * pIsfA = &IsfA;
    Bdc_Isf_t IsfB, * pIsfB = &IsfB;
    int Type;
    Bdc_SuppMinimize( p, pIsf );
    if ( pFunc = Bdc_TableLookup( p, pIsf ) )
        return pFunc;
    pFunc = Bdc_ManNewNode( p );
    pFunc->Type = Bdc_DecomposeStep( p, pIsf, pIsfA, pIsfB );
    pFunc->pFan0 = Bdc_ManDecompose_rec( p, pIsfA );
    if ( Bdc_DecomposeUpdateRight( p, pIsf, pIsfA, pIsfB, pFunc->pFan0->puFunc ) )
    {
        p->nNodes--;
        return pFunc->pFan0;
    }
    pFunc->pFan1 = Bdc_ManDecompose_rec( p, pIsfA );
    pFunc->puFunc = Vec_IntFetch( p->vMemory, p->nWords );
    pFunc->puFunc = 





}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


