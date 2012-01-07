/**CFile****************************************************************

  FileName    [giaAbsVta.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Variable time-frame abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbsVta.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "satSolver2.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Vta_Obj_t_ Vta_Obj_t; // object
struct Vta_Obj_t_
{
    int           iObj;
    int           iFrame;
    int           iNext;
    unsigned      Prio   : 24;
    unsigned      Value  :  2;
    unsigned      fAdded :  1;
    unsigned      fVisit :  1;
    unsigned      fPi    :  1;
    unsigned      fConst :  1;
    int           fFlop  :  1;
    int           fAnd   :  1;
};

typedef struct Vta_Man_t_ Vta_Man_t; // manager
struct Vta_Man_t_
{
    // user data
    Gia_Man_t *   pGia;
    int           nFramesMax;   // maximum number of frames
    int           nConfMax;
    int           nTimeMax;
    int           fVerbose;
    // internal data
    int           nObjs;        // the number of objects
    int           nObjsAlloc;   // the number of objects
    int           nBins;        // number of hash table entries
    int *         pBins;        // hash table bins
    Vta_Obj_t *   pObjs;        // hash table bins
    // other data
    Vec_Int_t *   vTemp;     
    sat_solver2 * pSat;
};

static inline Vta_Obj_t *  Vec_ManObj( Vta_Man_t * p, int i )           { assert( i >= 0 && i < p->nObjs ); return i ? p->pObjs + i : NULL;                 }
static inline int          Vta_ObjId( Vta_Man_t * p, Vta_Obj_t * pObj ) { assert( pObj > p->pObjs && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vta_Man_t * Vga_ManStart( Gia_Man_t * pGia, int nFramesMax, int nConfMax, int nTimeMax, int fVerbose )
{
    Vta_Man_t * p;
    assert( nFramesMax > 0 && nFramesMax < 32 );
    p = ABC_CALLOC( Vta_Man_t, 1 );
    p->pGia       = pGia;
    p->nFramesMax = nFramesMax;    
    p->nConfMax   = nConfMax;
    p->nTimeMax   = nTimeMax;
    p->fVerbose   = fVerbose;
    // internal data
    p->nObjsAlloc = (1 << 20);
    p->pObjs      = ABC_CALLOC( Vta_Obj_t, p->nObjsAlloc );
    p->nObjs      = 1;
    p->nBins      = Gia_PrimeCudd( p->nObjsAlloc/3 );
    p->pBins      = ABC_CALLOC( int, p->nBins );
    // other data
    p->vTemp      = Vec_IntAlloc( 1000 );
    p->pSat       = sat_solver2_new();
    return p;
}

/**Function*************************************************************

  Synopsis    [Delete manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vga_ManStop( Vta_Man_t * p )
{
    Vec_IntFreeP( &p->vTemp );
    sat_solver2_delete( p->pSat );
    ABC_FREE( p->pBins );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vga_ManHash( int iObj, int iFrame, int nBins )
{
    return ((iObj + iFrame)*(iObj + iFrame + 1)) % nBins;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int * Vga_ManLookup( Vta_Man_t * p, int iObj, int iFrame )
{
    Vta_Obj_t * pThis;
    int * pPlace = p->pBins + Vga_ManHash( iObj, iFrame, p->nBins );
    for ( pThis = Vec_ManObj(p, *pPlace); 
          pThis;  pPlace = &pThis->iNext, 
          pThis = Vec_ManObj(p, *pPlace) )
        if ( pThis->iObj == iObj && pThis->iFrame == iFrame )
            break;
    return pPlace;
}
static inline Vta_Obj_t * Vga_ManFind( Vta_Man_t * p, int iObj, int iFrame )
{
    int * pPlace = Vga_ManLookup( p, iObj, iFrame );
    return Vec_ManObj(p, *pPlace);
}
static inline Vta_Obj_t * Vga_ManFindOrAdd( Vta_Man_t * p, int iObj, int iFrame )
{
    int * pPlace = Vga_ManLookup( p, iObj, iFrame );
    Vta_Obj_t * pThis = Vec_ManObj(p, *pPlace);
    if ( pThis )
        return pThis;
    *pPlace = p->nObjs++;
    pThis = Vec_ManObj(p, *pPlace);
    pThis->iObj   = iObj;
    pThis->iFrame = iFrame;
    return pThis;
}
static inline void Vga_ManDelete( Vta_Man_t * p, int iObj, int iFrame )
{
    int * pPlace = Vga_ManLookup( p, iObj, iFrame );
    Vta_Obj_t * pThis = Vec_ManObj(p, *pPlace);
    assert( pThis != NULL );
    *pPlace = pThis->iNext;
    pThis->iNext = -1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

/**Function*************************************************************

  Synopsis    [Collect nodes/flops involved in different timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_VtaTest( Gia_Man_t * p )
{
/*
    Vec_Int_t * vOrder, * vFraLims, * vRoots;
    Gia_Man_t * pCopy;
    int i, Entry;
    // the new AIG orders flops and PIs in the "natural" order
    vOrder = Gia_VtaCollect( p, &vFraLims, &vRoots );
 
    // print results
//  Gia_ManPrintStats( p, 0 );
    printf( "Obj =%8d.  Unused =%8d.  Frames =%6d.\n",
        Gia_ManObjNum(p), 
        Gia_ManObjNum(p) - Gia_ManCoNum(p) - Vec_IntSize(vOrder), 
        Vec_IntSize(vFraLims) - 1 );

    Vec_IntForEachEntry( vFraLims, Entry, i )
        printf( "%d=%d ", i, Entry );
    printf( "\n" );

    pCopy = Gia_VtaDup( p, vOrder );
//    Gia_ManStopP( &pCopy );

    // cleanup
    Vec_IntFree( vOrder );
    Vec_IntFree( vFraLims );
    Vec_IntFree( vRoots );
    return pCopy;
*/
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

