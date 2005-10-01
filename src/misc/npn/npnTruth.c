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

  Synopsis    [Checks if the variable belongs to the support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Extra_TruthCofactors( int nVars, uint8 * puTruth, uint8 * puElem[][32], 
    uint8 * puTruthCofs0[][32], uint8 * puTruthCofs1[][32] )
{
    int v;
    for ( v = 0; v < nVars; v++ )
    {
        Extra_BitSharp( nVars, puTruth, puElem[v], (uint8 *)puTruthCofs0[v] );
        Extra_BitAnd  ( nVars, puTruth, puElem[v], (uint8 *)puTruthCofs1[v] );
    }
}

/**Function*************************************************************

  Synopsis    [Checks if the variable belongs to the support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Extra_TruthCountCofactorOnes( int nVars, uint8 * puTruthCofs[][32], int * pCounts )
{
    int v, nBytes;
    nBytes = Extra_BitCharNum( nVars );
    for ( v = 0; v < nVars; v++ )
        pCounts[v] = Extra_CountOnes( puTruthCofs[v], nBytes );
}

/**Function*************************************************************

  Synopsis    [Checks if the variable belongs to the support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Extra_TruthHasVar( int nVars, uint8 * puTruth, int iVar )
{
    // elementary truth tables
    static uint8 Signs[3] = {
        0xAA,    // 1010 1010
        0xCC,    // 1100 1100
        0xF0     // 1111 0000
    };
    int nChars, nShift, i;
    assert( iVar < nVars );
    nChars = Extra_BitCharNum( nVars );
    if ( iVar < 3 )
    {
        nShift = (1 << iVar);
        for ( i = 0; i < nChars; i++ )
            if ( ((puTruth[i] & Signs[iVar]) >> nShift) != (puTruth[i] & ~Signs[iVar]) )
                return 1;
    }
    else
    {
        nShift = (1 << (iVar-3));
        for ( i = 0; i < nChars; i++, i = (i % nShift)? i : i + nShift )
            if ( puTruth[i] != puTruth[i+nShift] )
                return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks if the variable belongs to the support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Npn_VarsTest( int nVars, uint8 * puTruth )
{
    int v;
    int Counter = 0;
    for ( v = 0; v < nVars; v++ )
        Counter += Extra_TruthHasVar( nVars, puTruth, v );
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


