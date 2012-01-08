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
    unsigned      fNew   :  1;
//    unsigned      fPi    :  1;
//    unsigned      fConst :  1;
//    int           fFlop  :  1;
//    int           fAnd   :  1;
};

typedef struct Vta_Man_t_ Vta_Man_t; // manager
struct Vta_Man_t_
{
    // user data
    Gia_Man_t *   pGia;         // AIG manager
    int           nFramesMax;   // maximum number of frames
    int           nConfMax;     // conflict limit
    int           nTimeMax;     // runtime limit
    int           fVerbose;     // verbose flag
    // internal data
    int           nObjs;        // the number of objects
    int           nObjsAlloc;   // the number of objects allocated
    int           nBins;        // number of hash table entries
    int *         pBins;        // hash table bins
    Vta_Obj_t *   pObjs;        // hash table bins
    // abstraction
    int           nWords;       // the number of sim words for abs
    int           nFrames;      // the number of copmleted frames
    Vec_Int_t *   vAbs;         // abstraction
    // other data
    Vec_Int_t *   vCla2Var;     // map clauses into variables
    sat_solver2 * pSat;         // incremental SAT solver
};

static inline Vta_Obj_t *  Vta_ManObj( Vta_Man_t * p, int i )           { assert( i >= 0 && i < p->nObjs ); return i ? p->pObjs + i : NULL;                     }
static inline int          Vta_ObjId( Vta_Man_t * p, Vta_Obj_t * pObj ) { assert( pObj > p->pObjs && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs;      }

static inline unsigned *   Vta_ObjAbs( Vta_Man_t * p, int i )           { assert( i >= 0 && i < p->nObjs ); return (unsigned *)Vec_IntEntryP( p->vAbs, i*p->nWords ); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Detects how many frames are completed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vta_ManReadFrameStart( Vec_Int_t * p, int nWords )
{
    unsigned * pTotal, * pThis;
    int i, w, nObjs = Vec_IntSize(p) / nWords;
    assert( Vec_IntSize(p) % nWords == 0 );
    pTotal = ABC_CALLOC( unsigned, nWords );
    for ( i = 0; i < nObjs; i++ )
    {
        pThis = (unsigned *)Vec_IntEntryP( p, nWords * i );
        for ( w = 0; w < nWords; w++ )
            pTotal[w] |= pThis[i];
    }
    for ( i = nWords * 32 - 1; i >= 0; i-- )
        if ( Gia_InfoHasBit(pTotal, i) )
        {
            ABC_FREE( pTotal );
            return i+1;
        }
    ABC_FREE( pTotal );
    return -1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vta_Man_t * Vga_ManStart( Gia_Man_t * pGia, Vec_Int_t * vAbs, int nFramesMax, int nConfMax, int nTimeMax, int fVerbose )
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
    p->nBins      = Gia_PrimeCudd( p->nObjsAlloc/2 );
    p->pBins      = ABC_CALLOC( int, p->nBins );
    // abstraction
    p->nWords     = vAbs ? Vec_IntSize(vAbs) / Gia_ManObjNum(p->pGia) : 1;
    p->nFrames    = vAbs ? Vta_ManReadFrameStart( vAbs, p->nWords ) : 0;
    p->vAbs       = vAbs ? vAbs : Vec_IntStart( Gia_ManObjNum(p->pGia) * p->nWords );
    // other data
    p->vCla2Var   = Vec_IntAlloc( 1000 );
    p->pSat       = sat_solver2_new();
    assert( nFramesMax == 0 || p->nFrames < nFramesMax );
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
    assert( p->vAbs == NULL );
    Vec_IntFreeP( &p->vCla2Var );
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
    for ( pThis = Vta_ManObj(p, *pPlace); 
          pThis;  pPlace = &pThis->iNext, 
          pThis = Vta_ManObj(p, *pPlace) )
        if ( pThis->iObj == iObj && pThis->iFrame == iFrame )
            break;
    return pPlace;
}
static inline Vta_Obj_t * Vga_ManFind( Vta_Man_t * p, int iObj, int iFrame )
{
    int * pPlace = Vga_ManLookup( p, iObj, iFrame );
    return Vta_ManObj(p, *pPlace);
}
static inline Vta_Obj_t * Vga_ManFindOrAdd( Vta_Man_t * p, int iObj, int iFrame )
{
    Vta_Obj_t * pThis;
    int * pPlace;
    if ( p->nObjs == p->nObjsAlloc )
    {
        p->pObjs = ABC_REALLOC( Vta_Obj_t, p->pObjs, 2 * p->nObjsAlloc );
        memset( p->pObjs + p->nObjsAlloc, 0, p->nObjsAlloc * sizeof(Vta_Obj_t) );
        p->nObjsAlloc *= 2;
        // rehash entries in the table
    }
    pPlace = Vga_ManLookup( p, iObj, iFrame );
    if ( *pPlace )
        return Vta_ManObj(p, *pPlace);
    *pPlace = p->nObjs++;
    pThis = Vta_ManObj(p, *pPlace);
    pThis->iObj   = iObj;
    pThis->iFrame = iFrame;
    pThis->fNew   = 1;
    return pThis;
}
static inline void Vga_ManDelete( Vta_Man_t * p, int iObj, int iFrame )
{
    int * pPlace = Vga_ManLookup( p, iObj, iFrame );
    Vta_Obj_t * pThis = Vta_ManObj(p, *pPlace);
    assert( pThis != NULL );
    *pPlace = pThis->iNext;
    pThis->iNext = -1;
}

/**Function*************************************************************

  Synopsis    [Adds clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vga_ManAddClauses( Vta_Man_t * p, int iObjStart )
{
    Vta_Obj_t * pThis, * pThis0, * pThis1;
    Gia_Obj_t * pObj;
    int i;
    for ( i = iObjStart; i < p->nObjs; i++ )
    {
        pThis = Vta_ManObj( p, i );
        assert( !pThis->fAdded && !pThis->fNew );
        pObj = Gia_ManObj( p->pGia, pThis->iObj );
        if ( Gia_ObjIsAnd(pObj) )
        {
            pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame );
            pThis1 = Vga_ManFind( p, Gia_ObjFaninId1p(p->pGia, pObj), pThis->iFrame );
            if ( pThis0 && pThis1 )
            {
                pThis->fAdded = 1;
                sat_solver2_add_and( p->pSat, 
                    Vta_ObjId(p, pThis), Vta_ObjId(p, pThis0), Vta_ObjId(p, pThis1), 
                    Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), 0 );
                Vec_IntPush( p->vCla2Var, i );
                Vec_IntPush( p->vCla2Var, i );
                Vec_IntPush( p->vCla2Var, i );
            }
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            if ( pThis->iFrame == 0 )
            {
                pThis->fAdded = 1;
                sat_solver2_add_constraint( p->pSat, pThis->iObj, 1, 0 );
                Vec_IntPush( p->vCla2Var, i );
                Vec_IntPush( p->vCla2Var, i );
            }
            else
            {
                pObj = Gia_ObjRoToRi( p->pGia, pObj );
                pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame-1 );
                if ( pThis0 )
                {
                    pThis->fAdded = 1;
                    sat_solver2_add_buffer( p->pSat, 
                        Vta_ObjId(p, pThis), Vta_ObjId(p, pThis0), 
                        Gia_ObjFaninC0(pObj), 0 );  
                    Vec_IntPush( p->vCla2Var, i );
                    Vec_IntPush( p->vCla2Var, i );
                }
            }
        }
        else if ( Gia_ObjIsConst0(pObj) )
        {
            pThis->fAdded = 1;
            sat_solver2_add_const( p->pSat, Vta_ObjId(p, pThis), 1, 0 );
            Vec_IntPush( p->vCla2Var, i );
        }
        else if ( !Gia_ObjIsPi(p->pGia, pObj) )
            assert( 0 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vga_ManUnroll_rec( Vta_Man_t * p, int iObj, int iFrame )
{
    Gia_Obj_t * pObj;
    Vta_Obj_t * pThis = Vga_ManFindOrAdd( p, iObj, iFrame );
    assert( !Gia_ObjIsCo(pObj) );
    if ( !pThis->fNew )
        return;
    pThis->fNew = 0;
    pObj = Gia_ManObj( p->pGia, iObj );
    if ( Gia_ObjIsAnd(pObj) )
    {
        Vga_ManUnroll_rec( p, Gia_ObjFaninId0p(p->pGia, pObj), iFrame );
        Vga_ManUnroll_rec( p, Gia_ObjFaninId1p(p->pGia, pObj), iFrame );
    }
    else if ( Gia_ObjIsRo(p->pGia, pObj) )
    {
        if ( iFrame == 0 )
        {
            pThis = Vga_ManFindOrAdd( p, iObj, -1 );
            assert( pThis->fNew );
            pThis->fNew = 0;
        }
        else
        {
            pObj = Gia_ObjRoToRi( p->pGia, pObj );
            Vga_ManUnroll_rec( p, Gia_ObjFaninId0p(p->pGia, pObj), iFrame-1 );
        }
    }
    else if ( Gia_ObjIsPi(p->pGia, pObj) )
    {}
    else if ( Gia_ObjIsConst0(pObj) )
    {}
    else assert( 0 );    
}

/**Function*************************************************************

  Synopsis    [Finds the set of clauses involved in the UNSAT core.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Vta_ManUnsatCore( sat_solver2 * pSat, int nConfMax, int fVerbose, int * piRetValue )
{
    Vec_Int_t * vCore;
    int RetValue, clk = clock();
    if ( piRetValue )
        *piRetValue = -1;
    // solve the problem
    RetValue = sat_solver2_solve( pSat, NULL, NULL, (ABC_INT64_T)nConfMax, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( RetValue == l_Undef )
    {
//        if ( fVerbose )
            printf( "Conflict limit is reached.\n" );
        return NULL;
    }
    if ( RetValue == l_True )
    {
//        if ( fVerbose )
            printf( "The BMC problem is SAT.\n" );
        if ( piRetValue )
            *piRetValue = 0;
        return NULL;
    }
    if ( fVerbose )
    {
        printf( "UNSAT after %7d conflicts.      ", pSat->stats.conflicts );
        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    assert( RetValue == l_False );

    // derive the UNSAT core
    clk = clock();
    vCore = (Vec_Int_t *)Sat_ProofCore( pSat );
    if ( fVerbose )
    {
        printf( "Core is %8d clauses (out of %8d).   ", Vec_IntSize(vCore), sat_solver2_nclauses(pSat) );
        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    return vCore;
}

/**Function*************************************************************

  Synopsis    [Collect nodes/flops involved in different timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vec_IntDoubleWidth( Vec_Int_t * p, int nWords )
{
    int * pArray = ABC_CALLOC( int, Vec_IntSize(p) * 2 );
    int i, w, nObjs = Vec_IntSize(p) / nWords;
    assert( Vec_IntSize(p) % nWords == 0 );
    for ( i = 0; i < nObjs; i++ )
        for ( w = 0; w < nWords; w++ )
            pArray[2 * nWords * i + w] = p->pArray[nWords * i + w];
    ABC_FREE( p->pArray );
    p->pArray = pArray;
    p->nSize *= 2;
    p->nCap = p->nSize;
}

/**Function*************************************************************

  Synopsis    [Collect nodes/flops involved in different timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_VtaTest( Gia_Man_t * pAig, int nFramesMax, int nConfMax, int nTimeMax, int fVerbose )
{
    Vta_Man_t * p;
    Gia_Obj_t * pObj;
    Vec_Int_t * vCore;
    Vec_Int_t * vAbs = NULL;
    int f, i, iObjPrev, RetValue, Entry;
    assert( Gia_ManPoNum(pAig) == 1 );
    pObj = Gia_ManPo( pAig, 0 );
    // start the manager
    p = Vga_ManStart( pAig, vAbs, nFramesMax, nConfMax, nTimeMax, fVerbose );
    // iteragte though time frames
    for ( f = p->nFrames; f < nFramesMax; f++ )
    {
        if ( fVerbose )
            printf( "Frame %4d : ", f );
        if ( p->nWords * 32 == f )
        {
            Vec_IntDoubleWidth( vAbs, p->nWords );
            p->nWords *= 2;
        }
        iObjPrev = p->nObjs;
        Vga_ManUnroll_rec( p, Gia_ObjFaninId0p(p->pGia, pObj), f );
        Vga_ManAddClauses( p, iObjPrev );
        // run SAT solver
        vCore = Vta_ManUnsatCore( p->pSat, nConfMax, fVerbose, &RetValue );
        if ( vCore == NULL )
            break;
        // add core to storage
        Vec_IntForEachEntry( vCore, Entry, i )
            Gia_InfoSetBit( Vta_ObjAbs(p, Vec_IntEntry(p->vCla2Var, Entry)), f );
        Vec_IntFree( vCore );
    }
    vAbs = p->vAbs; p->vAbs = NULL;
    Vga_ManStop( p );

    // print statistics about the core
    Vec_IntFree( vAbs );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

