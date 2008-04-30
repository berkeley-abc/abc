/**CFile****************************************************************

  FileName    [saigScl.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Sequential cleanup.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigScl.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Report registers useless for SEC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManReportUselessRegisters( Aig_Man_t * pAig )
{
    Aig_Obj_t * pObj, * pDriver;
    int i, Counter1, Counter2;
    // set PIO numbers
    Aig_ManSetPioNumbers( pAig );
    // check how many POs are driven by a register whose ref count is 1
    Counter1 = 0;
    Saig_ManForEachPo( pAig, pObj, i )
    {
        pDriver = Aig_ObjFanin0(pObj);
        if ( Saig_ObjIsLo(pAig, pDriver) && Aig_ObjRefs(pDriver) == 1 )
            Counter1++;
    }
    // check how many PIs have ref count 1 and drive a register
    Counter2 = 0;
    Saig_ManForEachLi( pAig, pObj, i )
    {
        pDriver = Aig_ObjFanin0(pObj);
        if ( Saig_ObjIsPi(pAig, pDriver) && Aig_ObjRefs(pDriver) == 1 )
            Counter2++;
    }
    if ( Counter1 )
        printf( "Network has %d (out of %d) registers driving POs.\n", Counter1, Saig_ManRegNum(pAig) );
    if ( Counter2 )
        printf( "Network has %d (out of %d) registers driven by PIs.\n", Counter2, Saig_ManRegNum(pAig) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


