/**CFile****************************************************************

  FileName    [cswMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cut sweeping.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 11, 2007.]

  Revision    [$Id: cswMan.c,v 1.00 2007/07/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cswInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the cut sweeping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Csw_Man_t * Csw_ManStart( Dar_Man_t * pMan, int nCutsMax, int nLeafMax, int fVerbose )
{
    Csw_Man_t * p;
    Dar_Obj_t * pObj;
    int i;
    assert( nCutsMax >= 2  );
    assert( nLeafMax <= 16 );
    // allocate the fraiging manager
    p = ALLOC( Csw_Man_t, 1 );
    memset( p, 0, sizeof(Csw_Man_t) );
    p->nCutsMax = nCutsMax;
    p->nLeafMax = nLeafMax;
    p->fVerbose = fVerbose;
    p->pManAig  = pMan;
    // create the new manager
    p->pManRes  = Dar_ManStartFrom( pMan );
    assert( Dar_ManPiNum(p->pManAig) == Dar_ManPiNum(p->pManRes) );
    // allocate room for cuts and equivalent nodes
    p->pEquiv   = ALLOC( Dar_Obj_t *, Dar_ManObjIdMax(pMan) + 1 );
    p->pCuts    = ALLOC( Csw_Cut_t *, Dar_ManObjIdMax(pMan) + 1 );
    memset( p->pCuts, 0, sizeof(Dar_Obj_t *) * (Dar_ManObjIdMax(pMan) + 1) );
    // allocate memory manager
    p->nTruthWords = Dar_TruthWordNum(nLeafMax);
    p->nCutSize = sizeof(Csw_Cut_t) + sizeof(int) * nLeafMax + sizeof(unsigned) * p->nTruthWords;
    p->pMemCuts = Dar_MmFixedStart( p->nCutSize * p->nCutsMax, 512 );
    // allocate hash table for cuts
    p->nTableSize = Cudd_PrimeCws( Dar_ManNodeNum(pMan) * p->nCutsMax / 2 );
    p->pTable = ALLOC( Csw_Cut_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Dar_Obj_t *) * p->nTableSize );
    // set the pointers to the available fraig nodes
    Csw_ObjSetEquiv( p, Dar_ManConst1(p->pManAig), Dar_ManConst1(p->pManRes) );
    Dar_ManForEachPi( p->pManAig, pObj, i )
        Csw_ObjSetEquiv( p, pObj, Dar_ManPi(p->pManRes, i) );
    // room for temporary truth tables
    p->puTemp[0] = ALLOC( unsigned, 4 * p->nTruthWords );
    p->puTemp[1] = p->puTemp[0] + p->nTruthWords;
    p->puTemp[2] = p->puTemp[1] + p->nTruthWords;
    p->puTemp[3] = p->puTemp[2] + p->nTruthWords;
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Csw_ManStop( Csw_Man_t * p )
{
    free( p->puTemp[0] );
    Dar_MmFixedStop( p->pMemCuts, 0 );
    free( p->pEquiv );
    free( p->pCuts );
    free( p->pTable );
    free( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


