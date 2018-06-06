/**CFile****************************************************************

  FileName    [extraUtilPath.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [Path enumeration.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: extraUtilPath.c,v 1.0 2003/02/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "aig/gia/gia.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes AIG representing the set of all paths in the graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeVarX( int nSize, int y, int x )
{
    return Abc_Var2Lit( nSize * y + x, 0 );
}
int Abc_NodeVarY( int nSize, int y, int x )
{
    return Abc_Var2Lit( nSize * (nSize + 1) + nSize * x + y, 0 );
}

Gia_Man_t * Abc_EnumeratePaths( int nSize )
{
    Gia_Man_t * pTemp, * pGia = Gia_ManStart( 10000 );
    int * pNodes = ABC_CALLOC( int, nSize+1 );
    int x, y, nVars = 2*nSize*(nSize+1);
    for ( x = 0; x < nVars; x++ )
        Gia_ManAppendCi( pGia );
    Gia_ManHashAlloc( pGia );
    // y = 0; x = 0;
    pNodes[0] = 1;
    // y = 0; x > 0 
    for ( x = 1; x <= nSize; x++ )
        pNodes[x] = Gia_ManHashAnd( pGia, pNodes[x-1], Abc_NodeVarX(nSize, 0, x) );
    // y > 0; x >= 0
    for ( y = 1; y <= nSize; y++ )
    {
        // y > 0; x = 0
        pNodes[0] = Gia_ManHashAnd( pGia, pNodes[0], Abc_NodeVarY(nSize, y, 0) );
        // y > 0; x > 0
        for ( x = 1; x <= nSize; x++ )
        {
            int iHor  = Gia_ManHashAnd( pGia, pNodes[x-1], Abc_NodeVarX(nSize, y, x) );
            int iVer  = Gia_ManHashAnd( pGia, pNodes[x],   Abc_NodeVarY(nSize, y, x) );
            pNodes[x] = Gia_ManHashOr( pGia, iHor, iVer );
        }
    }
    Gia_ManAppendCo( pGia, pNodes[nSize] );
    pGia = Gia_ManCleanup( pTemp = pGia );
    Gia_ManStop( pTemp );
    ABC_FREE( pNodes );
    return pGia;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_EnumeratePathsTest()
{
    int nSize = 2;
    Gia_Man_t * pGia = Abc_EnumeratePaths( nSize );
    Gia_AigerWrite( pGia, "testpath.aig", 0, 0 );
    Gia_ManStop( pGia );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

