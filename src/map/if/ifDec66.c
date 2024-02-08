/**CFile****************************************************************

  FileName    [ifDec16.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Fast checking procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifDec16.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "bool/kit/kit.h"
#include "misc/vec/vecMem.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs ACD into 66 cascade.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutPerformCheck66( If_Man_t * p, unsigned * pTruth0, int nVars, int nLeaves, char * pStr )
{
    unsigned pTruth[IF_MAX_FUNC_LUTSIZE > 5 ? 1 << (IF_MAX_FUNC_LUTSIZE - 5) : 1];
    int i, Length;
    // stretch the truth table
    assert( nVars >= 6 );
    memcpy( pTruth, pTruth0, sizeof(word) * Abc_TtWordNum(nVars) );
    Abc_TtStretch6( (word *)pTruth, nLeaves, p->pPars->nLutSize );

    // if cutmin is disabled, minimize the function
    if ( !p->pPars->fCutMin )
        nLeaves = Abc_TtMinBase( (word *)pTruth, NULL, nLeaves, nVars );

    // quit if parameters are wrong
    Length = strlen(pStr);
    if ( Length != 2 )
    {
        printf( "Wrong LUT struct (%s)\n", pStr );
        return 0;
    }
    for ( i = 0; i < Length; i++ )
    {
      if ( pStr[i] != '6' )
      {
          printf( "The LUT size (%d) should belong to {6}.\n", pStr[i] - '0' );
          return 0;
      }
    }

    if ( nLeaves > 11 )
    {
        printf( "The cut size (%d) is too large for the LUT structure %s.\n", nLeaves, pStr );
        return 0;
    }

    // consider easy case
    if ( nLeaves <= 6 )
        return 1;

    // derive the decomposition
    return (int)(acd66_evaluate( (word *)pTruth, nVars, 1 ) > 0 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END