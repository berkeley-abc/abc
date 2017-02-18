/**CFile****************************************************************

  FileName    [pdrIncr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [PDR with incremental solving.]

  Author      [Yen-Sheng Ho, Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Feb. 17, 2017.]

  Revision    [$Id: pdrIncr.c$]

***********************************************************************/

#include "pdrInt.h"
#include "base/main/main.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int IPdr_ManSolve( Abc_Ntk_t * pNtk, Pdr_Par_t * pPars )
{
    int RetValue = -1;
    abctime clk = Abc_Clock();
    Aig_Man_t * pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 1 );

    RetValue = Pdr_ManSolve( pMan, pPars );
 
    if ( RetValue == 1 )
        Abc_Print( 1, "Property proved.  " );
    else 
    {
        if ( RetValue == 0 )
        {
            if ( pMan->pSeqModel == NULL )
                Abc_Print( 1, "Counter-example is not available.\n" );
            else
            {
                Abc_Print( 1, "Output %d of miter \"%s\" was asserted in frame %d.  ", pMan->pSeqModel->iPo, pNtk->pName, pMan->pSeqModel->iFrame );
                if ( !Saig_ManVerifyCex( pMan, pMan->pSeqModel ) )
                    Abc_Print( 1, "Counter-example verification has FAILED.\n" );
            }
        }
        else if ( RetValue == -1 )
            Abc_Print( 1, "Property UNDECIDED.  " );
        else
            assert( 0 );
    }
    ABC_PRT( "Time", Abc_Clock() - clk );


    ABC_FREE( pNtk->pSeqModel );
    pNtk->pSeqModel = pMan->pSeqModel;
    pMan->pSeqModel = NULL;
    if ( pNtk->vSeqModelVec )
        Vec_PtrFreeFree( pNtk->vSeqModelVec );
    pNtk->vSeqModelVec = pMan->vSeqModelVec;
    pMan->vSeqModelVec = NULL;
    Aig_ManStop( pMan );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
