/**CFile****************************************************************

  FileName    [npnUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName []

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: npnUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "extra.h"
#include "npn.h"
#include "vec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_StartTruth8( uint8 uTruths[][32] )
{
    // elementary truth tables
    static uint8 Signs[3] = {
        0xAA,    // 1010 1010
        0xCC,    // 1100 1100
        0xF0     // 1111 0000
    };
    int v, i, nShift;
    for ( v = 0; v < 3; v++ )
        for ( i = 0; i < 32; i++ )
            uTruths[v][i] = Signs[v];
    for ( v = 3; v < 8; v++ )
    {
        nShift = (1 << (v-3));
        for ( i = 0; i < 32; i++, i = (i % nShift)? i : i + nShift )
        {
            uTruths[v][i]          = 0;
            uTruths[v][i + nShift] = 0xFF;
        }
    }
/*
    for ( v = 0; v < 8; v++ )
    {
        Extra_PrintBinary( stdout, (unsigned int*)uTruths[v], 90 );
        printf( "\n" );
    }
*/
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


