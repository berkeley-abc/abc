/**CFile****************************************************************

  FileName    [ifDec07.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Performs additional check.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifDec07.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

int If_CutPerformCheckJ( If_Man_t * p, unsigned * pTruth, int nVars, int nLeaves, char * pStr )
{
    return 1;
}
word If_CutPerformDeriveJ( If_Man_t * p, unsigned * pTruth, int nVars, int nLeaves, char * pStr, int fDerive )
{
    return 0;
}
void If_PermUnpack( unsigned Value, int Pla2Var[9] )
{
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

