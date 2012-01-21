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

#define VTA_LARGE  0xFFFFFFF

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Vta_Obj_t_ Vta_Obj_t; // object
struct Vta_Obj_t_
{
    int           iObj;
    int           iFrame;
    int           iNext;
    unsigned      Prio   : 28;  // related to VTA_LARGE
    unsigned      Value  :  2;
    unsigned      fAdded :  1;
    unsigned      fNew   :  1;
};

typedef struct Vta_Man_t_ Vta_Man_t; // manager
struct Vta_Man_t_
{
    // user data
    Gia_Man_t *   pGia;         // AIG manager
    Gia_ParVta_t* pPars;        // parameters
    // internal data
    int           nObjs;        // the number of objects
    int           nObjsAlloc;   // the number of objects allocated
    int           nBins;        // number of hash table entries
    int *         pBins;        // hash table bins
    Vta_Obj_t *   pObjs;        // hash table bins
    Vec_Int_t *   vOrder;       // objects in DPS order
    // abstraction
    int           nObjBits;     // the number of bits to represent objects
    unsigned      nObjMask;     // object mask
    Vec_Ptr_t *   vFrames;      // start abstraction for each frame
    int           nWords;       // the number of words in the record
    Vec_Int_t *   vSeens;       // seen objects
    Vec_Bit_t *   vSeenGla;     // seen objects in all frames
    int           nSeenGla;     // seen objects in all frames
    // other data
    Vec_Int_t *   vCla2Var;     // map clauses into variables
    Vec_Ptr_t *   vCores;       // unsat core for each frame
    sat_solver2 * pSat;         // incremental SAT solver
};

#define VTA_VAR0   1
#define VTA_VAR1   2
#define VTA_VARX   3

static inline int Vta_ValIs0( Vta_Obj_t * pThis, int fCompl )
{
    return (pThis->Value == VTA_VAR0 && !fCompl) || (pThis->Value == VTA_VAR1 && fCompl);
}
static inline int Vta_ValIs1( Vta_Obj_t * pThis, int fCompl )
{
    return (pThis->Value == VTA_VAR1 && !fCompl) || (pThis->Value == VTA_VAR0 && fCompl);
}

static inline Vta_Obj_t *  Vta_ManObj( Vta_Man_t * p, int i )           { assert( i >= 0 && i < p->nObjs ); return i ? p->pObjs + i : NULL;                     }
static inline int          Vta_ObjId( Vta_Man_t * p, Vta_Obj_t * pObj ) { assert( pObj > p->pObjs && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs;      }

//static inline unsigned *   Vta_ObjAbsOld( Vta_Man_t * p, int i )   { assert( i >= 0 && i < p->nObjs ); return (unsigned *)Vec_IntEntryP( p->vAbs,    i*p->nWords ); }
//static inline unsigned *   Vta_ObjAbsNew( Vta_Man_t * p, int i )   { assert( i >= 0 && i < p->nObjs ); return (unsigned *)Vec_IntEntryP( p->vAbsNew, i*p->nWords ); }

#define Vta_ManForEachObj( p, pObj, i )                                 \
    for ( i = 1; (i < p->nObjs) && ((pObj) = Vta_ManObj(p, i)); i++ )
#define Vta_ManForEachObjVec( vVec, p, pObj, i )                        \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pObj) = Vta_ManObj(p, Vec_IntEntry(vVec,i))); i++ )
#define Vta_ManForEachObjVecReverse( vVec, p, pObj, i )                        \
    for ( i = Vec_IntSize(vVec) - 1; (i >= 1) && ((pObj) = Vta_ManObj(p, Vec_IntEntry(vVec,i))); i-- )

// abstraction is given as an array of integers:
// - the first entry is the number of timeframes (F)
// - the next (F+1) entries give the beginning position of each timeframe
// - the following entries give the object IDs
// invariant:  assert( vec[vec[0]+2] == size(vec) );

extern void Vga_ManAddClausesOne( Vta_Man_t * p, int iObj, int iFrame );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_VtaSetDefaultParams( Gia_ParVta_t * p )
{
    memset( p, 0, sizeof(Gia_ParVta_t) );
    p->nFramesStart  =   10;  
    p->nFramesMax    =    0;
    p->nConfLimit    =    0;
    p->nTimeOut      =   60;
    p->fVerbose      =    1;
}

/**Function*************************************************************

  Synopsis    [Converting from one array to per-frame arrays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Gia_VtaAbsToFrames( Vec_Int_t * vAbs )
{
    Vec_Ptr_t * vFrames;
    Vec_Int_t * vFrame;
    int i, k, Entry, iStart, iStop;
    int nFrames = Vec_IntEntry( vAbs, 0 );
    assert( Vec_IntEntry(vAbs, nFrames+1) == Vec_IntSize(vAbs) );
    vFrames = Vec_PtrAlloc( nFrames );
    for ( i = 0; i < nFrames; i++ )
    {
        iStart = Vec_IntEntry( vAbs, i+1 );
        iStop  = Vec_IntEntry( vAbs, i+2 );
        vFrame = Vec_IntAlloc( iStop - iStart );
        Vec_IntForEachEntryStartStop( vAbs, Entry, k, iStart, iStop )
            Vec_IntPush( vFrame, Entry );
        Vec_PtrPush( vFrames, vFrame );
    }
    assert( iStop == Vec_IntSize(vAbs) );
    return vFrames;
}

/**Function*************************************************************

  Synopsis    [Converting from per-frame arrays to one integer array.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_VtaFramesToAbs( Vec_Vec_t * vFrames )
{
    Vec_Int_t * vOne, * vAbs;
    int i, k, Entry, nSize;
    vAbs = Vec_IntAlloc( 2 + Vec_VecSize(vFrames) + Vec_VecSizeSize(vFrames) );
    Vec_IntPush( vAbs, Vec_VecSize(vFrames) );
    nSize = Vec_VecSize(vFrames) + 2;
    Vec_VecForEachLevelInt( vFrames, vOne, i )
    {
        Vec_IntPush( vAbs, nSize );
        nSize += Vec_IntSize( vOne );
    }
    Vec_IntPush( vAbs, nSize );
    assert( Vec_IntSize(vAbs) == Vec_VecSize(vFrames) + 2 );
    Vec_VecForEachLevelInt( vFrames, vOne, i )
        Vec_IntForEachEntry( vOne, Entry, k )
            Vec_IntPush( vAbs, Entry );
    assert( Vec_IntEntry(vAbs, Vec_IntEntry(vAbs,0)+1) == Vec_IntSize(vAbs) );
    return vAbs;
}

/**Function*************************************************************

  Synopsis    [Converting VTA vector to GLA vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_VtaConvertToGla( Gia_Man_t * p, Vec_Int_t * vAbs )
{
    Gia_Obj_t * pObj;
    Vec_Int_t * vPresent;
    int nObjMask, nObjs = Gia_ManObjNum(p);
    int i, Entry, nFrames = Vec_IntEntry( vAbs, 0 );
    assert( Vec_IntEntry(vAbs, nFrames+1) == Vec_IntSize(vAbs) );
    // get the bitmask
    nObjMask = (1 << Gia_Base2Log(nObjs)) - 1;
    assert( nObjs <= nObjMask );
    // go through objects
    vPresent = Vec_IntStart( nObjs );
    Vec_IntWriteEntry( vPresent, 0, 1 );
    Vec_IntForEachEntryStart( vAbs, Entry, i, nFrames+2 )
    {
        pObj = Gia_ManObj( p, (Entry &  nObjMask) );
        assert( Gia_ObjIsRo(p, pObj) || Gia_ObjIsAnd(pObj) || Gia_ObjIsConst0(pObj) );
        Vec_IntWriteEntry( vPresent, (Entry &  nObjMask), 1 );
    }
    return vPresent;
}

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

  Synopsis    [Detects how many frames are completed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Int_t * Vta_ManDeriveAbsAll( Vec_Int_t * p, int nWords )
{
    Vec_Int_t * vRes;
    unsigned * pThis;
    int i, w, nObjs = Vec_IntSize(p) / nWords;
    assert( Vec_IntSize(p) % nWords == 0 );
    vRes = Vec_IntAlloc( nObjs );
    for ( i = 0; i < nObjs; i++ )
    {
        pThis = (unsigned *)Vec_IntEntryP( p, nWords * i );
        for ( w = 0; w < nWords; w++ )
            if ( pThis[w] )
                break;
        Vec_IntPush( vRes, (int)(w < nWords) );
    }
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Collect nodes/flops involved in different timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Vec_IntDoubleWidth( Vec_Int_t * p, int nWords )
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
    return 2 * nWords;
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
    assert( iObj >= 0 && iFrame >= -1 );
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

  Synopsis    [Remaps core into frame/node pairs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vta_ManUnsatCoreRemap( Vta_Man_t * p, Vec_Int_t * vCore )
{
    Vta_Obj_t * pThis;
    int i, Entry;
    Vec_IntForEachEntry( vCore, Entry, i )
    {
        pThis = Vta_ManObj( p, Entry );
        Entry = (pThis->iFrame << p->nObjBits) | pThis->iObj;
        Vec_IntWriteEntry( vCore, i, Entry );
//printf( "%d^%d ", pThis->iObj, pThis->iFrame );
    }
//printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Compares two objects by their distance.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Vta_ManComputeDepthIncrease( Vta_Obj_t ** pp1, Vta_Obj_t ** pp2 )
{
    int Diff = (*pp1)->Prio - (*pp2)->Prio;
    if ( Diff < 0 )
        return -1;
    if ( Diff > 0 ) 
        return 1;
    Diff = (*pp1) - (*pp2);
    if ( Diff < 0 )
        return -1;
    if ( Diff > 0 ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the object is already used.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Vta_ManObjIsUsed( Vta_Man_t * p, int iObj )
{
    int i;
    unsigned * pInfo = (unsigned *)Vec_IntEntryP( p->vSeens, p->nWords * iObj );
    for ( i = 0; i < p->nWords; i++ )
        if ( pInfo[i] )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Refines abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Vta_ManRefineAbstraction( Vta_Man_t * p )
{
    Abc_Cex_t * pCex = NULL;
    Vec_Ptr_t * vTermsUsed, * vTermsUnused;
    Vta_Obj_t * pThis, * pThis0, * pThis1, * pTop;
    Gia_Obj_t * pObj;
    int i, Counter;
    assert( Vec_IntSize(p->vOrder) == p->nObjs - 1 );
    // clean depth field
    Vta_ManForEachObj( p, pThis, i )
    {
        pThis->Prio = VTA_LARGE;
        pThis->Value = sat_solver2_var_value(p->pSat, i) ? VTA_VAR1 : VTA_VAR0;
    }

    // set the last node
    pThis = Vta_ManObj( p, Vec_IntEntryLast(p->vOrder) );
    pThis->Prio = 1;

    // consider nodes in the reverse order
    vTermsUsed   = Vec_PtrAlloc( 1015 );
    vTermsUnused = Vec_PtrAlloc( 1016 );
    Vta_ManForEachObjVecReverse( p->vOrder, p, pThis, i )
    {
        // skip unreachable ones
        if ( pThis->Prio == VTA_LARGE )
            continue;
        // skip contants and PIs
        pObj = Gia_ManObj( p->pGia, pThis->iObj );
        if ( Gia_ObjIsConst0(pObj) || Gia_ObjIsPi(p->pGia, pObj) )
        {
            pThis->Prio = 0;
            continue;
        }
        // collect useful terminals
        assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(p->pGia, pObj) );
        if ( !pThis->fAdded )
        {
            assert( pThis->Prio > 0 || pThis->Prio < VTA_LARGE );
            if ( Vta_ManObjIsUsed(p, pThis->iObj) )
                Vec_PtrPush( vTermsUsed, pThis );
            else
                Vec_PtrPush( vTermsUnused, pThis );
            continue;
        }
        // propagate
        if ( Gia_ObjIsAnd(pObj) )
        {
            pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame );
            pThis1 = Vga_ManFind( p, Gia_ObjFaninId1p(p->pGia, pObj), pThis->iFrame );
            assert( pThis0 && pThis1 );
            pThis0->Prio = Abc_MinInt( pThis0->Prio, pThis->Prio + 1 );
            pThis1->Prio = Abc_MinInt( pThis1->Prio, pThis->Prio + 1 );
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            if ( pThis->iFrame == 0 )
                pThis->Prio = 0;
            else
            {
                pObj = Gia_ObjRoToRi( p->pGia, pObj );
                pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame-1 );
                assert( pThis0 );
                pThis0->Prio = Abc_MinInt( pThis0->Prio, pThis->Prio + 1 );
            }
        }
        else assert( 0 );
    }
    // objects with equal distance should receive priority based on number
    // those objects whose prototypes have been added in other timeframes
    // should have higher priority than the current object
    Vec_PtrSort( vTermsUsed,   (int (*)(void))Vta_ManComputeDepthIncrease );
    Vec_PtrSort( vTermsUnused, (int (*)(void))Vta_ManComputeDepthIncrease );
    // assign the priority based on these orders
    Counter = 1;
    Vec_PtrForEachEntry( Vta_Obj_t *, vTermsUsed, pThis, i )
        pThis->Prio = Counter++;
    Vec_PtrForEachEntry( Vta_Obj_t *, vTermsUnused, pThis, i )
        pThis->Prio = Counter++;


    // propagate in the direct order
    Vta_ManForEachObjVec( p->vOrder, p, pThis, i )
    {
        assert( pThis->fNew == 0 );
        // skip unreachable ones
        if ( pThis->Prio == VTA_LARGE )
            continue;
        // skip terminal objects
        if ( !pThis->fAdded )
            continue;
        // assumes that values are assigned!!!
        assert( pThis->Value != 0 );
        // propagate
        pObj = Gia_ManObj( p->pGia, pThis->iObj );
        assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(p->pGia, pObj) );

        if ( Gia_ObjIsAnd(pObj) )
        {
            pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame );
            pThis1 = Vga_ManFind( p, Gia_ObjFaninId1p(p->pGia, pObj), pThis->iFrame );
            assert( pThis0 && pThis1 );
            if ( pThis->Value == VTA_VAR1 )
            {
                assert( Vta_ValIs1(pThis0, Gia_ObjFaninC0(pObj)) && Vta_ValIs1(pThis1, Gia_ObjFaninC1(pObj)) );
                pThis->Prio = Abc_MaxInt( pThis0->Prio, pThis1->Prio );
            }
            else if ( pThis->Value == VTA_VAR0 )
            {
                if ( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) && Vta_ValIs0(pThis1, Gia_ObjFaninC1(pObj)) )
                    pThis->Prio = Abc_MinInt( pThis0->Prio, pThis1->Prio );
                else if ( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) )
                    pThis->Prio = pThis0->Prio;
                else if ( Vta_ValIs0(pThis1, Gia_ObjFaninC1(pObj)) )
                    pThis->Prio = pThis1->Prio;
                else assert( 0 );
            }
            else assert( 0 );
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            if ( pThis->iFrame > 0 )
            {
                pObj = Gia_ObjRoToRi( p->pGia, pObj );
                pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame-1 );
                assert( pThis0 );
                pThis->Prio = pThis0->Prio;
            }
        }
    }

    Vec_PtrClear( vTermsUsed );

    // select important values
    pTop = Vta_ManObj( p, Vec_IntEntryLast(p->vOrder) );
    pTop->fNew = 1;
    Vta_ManForEachObjVec( p->vOrder, p, pThis, i )
    {
        if ( pThis->fNew == 0 )
            continue;
        pThis->fNew = 0;
        assert( pThis->Prio >= 0 && pThis->Prio <= pTop->Prio );
        // skip terminal objects
        if ( !pThis->fAdded )
        {
            Vec_PtrPush( vTermsUsed, pThis );
            continue;
        }
        // assumes that values are assigned!!!
        assert( pThis->Value != 0 );
        // propagate
        pObj = Gia_ManObj( p->pGia, pThis->iObj );
        assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(p->pGia, pObj) );
        if ( Gia_ObjIsAnd(pObj) )
        {
            pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame );
            pThis1 = Vga_ManFind( p, Gia_ObjFaninId1p(p->pGia, pObj), pThis->iFrame );
            assert( pThis0 && pThis1 );
            if ( pThis->Value == VTA_VAR1 )
            {
                assert( Vta_ValIs1(pThis0, Gia_ObjFaninC0(pObj)) && Vta_ValIs1(pThis1, Gia_ObjFaninC1(pObj)) );
                pThis0->fNew = 1;
                pThis1->fNew = 1;
            }
            else if ( pThis->Value == VTA_VAR0 )
            {
                if ( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) && Vta_ValIs0(pThis1, Gia_ObjFaninC1(pObj)) )
                {
                    assert( pThis0->Prio <= pThis->Prio );
                    assert( pThis1->Prio <= pThis->Prio );
                    if ( pThis0->Prio <= pThis1->Prio )
                        pThis0->fNew = 1;
                    else
                        pThis1->fNew = 1;
                }
                else if ( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) )
                    pThis0->fNew = 1;
                else if ( Vta_ValIs0(pThis1, Gia_ObjFaninC1(pObj)) )
                    pThis1->fNew = 1;
                else assert( 0 );
            }
            else assert( 0 );
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            if ( pThis->iFrame > 0 )
            {
                pObj = Gia_ObjRoToRi( p->pGia, pObj );
                pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame-1 );
                assert( pThis0 );
                pThis0->fNew = 1;
            }
        }
    }

    // verify
    Vta_ManForEachObj( p, pThis, i )
        pThis->Value = VTA_VARX;
    Vec_PtrForEachEntry( Vta_Obj_t *, vTermsUsed, pThis, i )
        pThis->Value = sat_solver2_var_value(p->pSat, Vta_ObjId(p, pThis)) ? VTA_VAR1 : VTA_VAR0;
    // simulate 
    Vta_ManForEachObjVec( p->vOrder, p, pThis, i )
    {
        assert( pThis->fNew == 0 );
        pObj = Gia_ManObj( p->pGia, pThis->iObj );
        if ( Gia_ObjIsAnd(pObj) )
        {
            pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame );
            pThis1 = Vga_ManFind( p, Gia_ObjFaninId1p(p->pGia, pObj), pThis->iFrame );
            assert( pThis0 && pThis1 );
            if ( Vta_ValIs1(pThis0, Gia_ObjFaninC0(pObj)) && Vta_ValIs1(pThis1, Gia_ObjFaninC1(pObj)) )
                pThis->Value = VTA_VAR1;
            else if ( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) || Vta_ValIs0(pThis1, Gia_ObjFaninC1(pObj)) )
                pThis->Value = VTA_VAR0;
            else
                pThis->Value = VTA_VARX;
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            if ( pThis->iFrame > 0 )
            {
                pObj = Gia_ObjRoToRi( p->pGia, pObj );
                pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame-1 );
                assert( pThis0 );
                if ( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) )
                    pThis->Value = VTA_VAR0;
                else if ( Vta_ValIs1(pThis0, Gia_ObjFaninC0(pObj)) )
                    pThis->Value = VTA_VAR1;
                else
                    pThis->Value = VTA_VARX;
            }
        }
        // double check the solver
        if ( pThis->Value != VTA_VARX )
            assert( (int)pThis->Value == (sat_solver2_var_value(p->pSat, Vta_ObjId(p, pThis)) ? VTA_VAR1 : VTA_VAR0) );
    }

    // check the output
    if ( pTop->Value != VTA_VAR1 )
        printf( "Vta_ManRefineAbstraction(): Terminary simulation verification failed!\n" );

    // produce true counter-example
    if ( pTop->Prio == 0 )
    {
        pCex = NULL;
        pCex = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), p->pPars->iFrame+1 );
        pCex->iPo = 0;
        pCex->iFrame = p->pPars->iFrame;
        Vec_PtrForEachEntry( Vta_Obj_t *, vTermsUsed, pThis, i )
        {
            assert( pThis->Value == VTA_VAR0 || pThis->Value == VTA_VAR1 );
            pObj = Gia_ManObj( p->pGia, pThis->iObj );
            assert( Gia_ObjIsConst0(pObj) || Gia_ObjIsCi(pObj) );
            if ( Gia_ObjIsRo(p->pGia, pObj) )
                assert( pThis->iFrame == 0 && pThis->Value == VTA_VAR0 );
            else if ( Gia_ObjIsPi(p->pGia, pObj) && pThis->Value == VTA_VAR1 )
                Gia_InfoSetBit( pCex->pData, pCex->nRegs + pThis->iFrame * pCex->nPis + Gia_ObjCioId(pObj) );
        }
    }
    // perform refinement
    else
    {
        Vec_PtrForEachEntry( Vta_Obj_t *, vTermsUsed, pThis, i )
        {
            assert( !pThis->fAdded );
            pObj = Gia_ManObj( p->pGia, pThis->iObj );
            if ( Gia_ObjIsAnd(pObj) )
            {
                Vga_ManFindOrAdd( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame );
                Vga_ManFindOrAdd( p, Gia_ObjFaninId1p(p->pGia, pObj), pThis->iFrame );
            }
            else if ( Gia_ObjIsRo(p->pGia, pObj) )
            {
                if ( pThis->iFrame > 0 )
                {
                    pObj = Gia_ObjRoToRi( p->pGia, pObj );
                    Vga_ManFindOrAdd( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame-1 );
                }
            }
            else assert( 0 );
        }
        // add clauses
        Vec_PtrForEachEntry( Vta_Obj_t *, vTermsUsed, pThis, i )
            Vga_ManAddClausesOne( p, pThis->iObj, pThis->iFrame );
    }

    Vec_PtrFree( vTermsUsed );
    Vec_PtrFree( vTermsUnused );
    return pCex;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vta_Man_t * Vga_ManStart( Gia_Man_t * pGia, Gia_ParVta_t * pPars )
{
    Vta_Man_t * p;
    p = ABC_CALLOC( Vta_Man_t, 1 );
    p->pGia        = pGia;
    p->pPars       = pPars;
    // internal data
    p->nObjsAlloc  = (1 << 20);
    p->pObjs       = ABC_CALLOC( Vta_Obj_t, p->nObjsAlloc );
    p->nObjs       = 1;
    p->nBins       = Abc_PrimeCudd( p->nObjsAlloc/2 );
    p->pBins       = ABC_CALLOC( int, p->nBins );
    p->vOrder      = Vec_IntAlloc( 1013 );
    // abstraction
    p->nObjBits    = Gia_Base2Log( Gia_ManObjNum(pGia) );
    p->nObjMask    = (1 << p->nObjBits) - 1;
    assert( Gia_ManObjNum(pGia) <= (int)p->nObjMask );
    p->nWords      = 1;
    p->vSeens      = Vec_IntStart( Gia_ManObjNum(pGia) * p->nWords );
    p->vSeenGla    = Vec_BitStart( Gia_ManObjNum(pGia) );
    p->nSeenGla    = 1;
    // start the abstraction
    if ( pGia->vObjClasses == NULL )
        p->vFrames = Gia_ManUnrollAbs( pGia, pPars->nFramesStart );
    else
    {
        p->vFrames = Gia_VtaAbsToFrames( pGia->vObjClasses );
        // update parameters
        if ( pPars->nFramesStart != Vec_PtrSize(p->vFrames) )
        {
            printf( "Starting frame count is changed to match the abstraction (from %d to %d).\n", pPars->nFramesStart, Vec_PtrSize(p->vFrames) ); 
            pPars->nFramesStart = Vec_PtrSize(p->vFrames);
        }
        if ( pPars->nFramesMax && pPars->nFramesMax < pPars->nFramesStart )
        {
            printf( "Maximum frame count is changed to match the starting frames (from %d to %d).\n", pPars->nFramesMax, pPars->nFramesStart ); 
            pPars->nFramesMax = Abc_MaxInt( pPars->nFramesMax, pPars->nFramesStart );
        }
    }
    // other data
    p->vCla2Var    = Vec_IntAlloc( 1000 );
    p->vCores      = Vec_PtrAlloc( 100 );
    p->pSat        = sat_solver2_new();
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
    if ( p->pPars->fVerbose )
        printf( "SAT solver:  Variables = %d. Clauses = %d. Conflicts = %d.\n", 
            sat_solver2_nvars(p->pSat), sat_solver2_nclauses(p->pSat), sat_solver2_nconflicts(p->pSat) );

    Vec_VecFreeP( (Vec_Vec_t **)&p->vCores );
    Vec_VecFreeP( (Vec_Vec_t **)&p->vFrames );
    Vec_BitFreeP( &p->vSeenGla );
    Vec_IntFreeP( &p->vSeens );
    Vec_IntFreeP( &p->vOrder );
    Vec_IntFreeP( &p->vCla2Var );
    sat_solver2_delete( p->pSat );
    ABC_FREE( p->pBins );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Finds the set of clauses involved in the UNSAT core.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Vta_ManUnsatCore( int iLit, Vec_Int_t * vCla2Var, sat_solver2 * pSat, int nConfMax, int fVerbose, int * piRetValue )
{
    Vec_Int_t * vPres;
    Vec_Int_t * vCore;
    int k, i, Entry, RetValue, clk = clock();
    int nConfPrev = pSat->stats.conflicts;
    if ( piRetValue )
        *piRetValue = 1;
    // solve the problem
    RetValue = sat_solver2_solve( pSat, &iLit, &iLit+1, (ABC_INT64_T)nConfMax, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( RetValue == l_Undef )
    {
        if ( piRetValue )
            *piRetValue = -1;
        return NULL;
    }
    if ( RetValue == l_True )
    {
        if ( piRetValue )
            *piRetValue = 0;
        return NULL;
    }
    if ( fVerbose )
    {
        printf( "%6d", (int)pSat->stats.conflicts - nConfPrev );
//        printf( "UNSAT after %7d conflicts.      ", pSat->stats.conflicts );
//        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    assert( RetValue == l_False );

    // derive the UNSAT core
    clk = clock();
    vCore = (Vec_Int_t *)Sat_ProofCore( pSat );
    if ( fVerbose )
    {
//        printf( "Core is %8d clauses (out of %8d).   ", Vec_IntSize(vCore), sat_solver2_nclauses(pSat) );
//        Abc_PrintTime( 1, "Time", clock() - clk );
    }

    // remap core into variables
    clk = clock();
    vPres = Vec_IntStart( sat_solver2_nvars(pSat) );
    k = 0; 
    Vec_IntForEachEntry( vCore, Entry, i )
    {
        Entry = Vec_IntEntry(vCla2Var, Entry);
        if ( Vec_IntEntry(vPres, Entry) )
            continue;
        Vec_IntWriteEntry( vPres, Entry, 1 );
        Vec_IntWriteEntry( vCore, k++, Entry );
    }
    Vec_IntShrink( vCore, k );
    Vec_IntFree( vPres );
    if ( fVerbose )
    {
//        printf( "Core is %8d vars    (out of %8d).   ", Vec_IntSize(vCore), sat_solver2_nvars(pSat) );
//        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    return vCore;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vta_ManAbsPrintFrame( Vta_Man_t * p, Vec_Int_t * vCore, int nFrames )
{
    unsigned * pInfo, * pCountAll, * pCountUni;
    int i, k, iFrame, iObj, Entry;
    // print info about frames
    pCountAll = ABC_CALLOC( int, nFrames + 1 );
    pCountUni = ABC_CALLOC( int, nFrames + 1 );
    Vec_IntForEachEntry( vCore, Entry, i )
    {
        iObj   = (Entry &  p->nObjMask);
        iFrame = (Entry >> p->nObjBits);
        assert( iFrame < nFrames );
        pInfo  = (unsigned *)Vec_IntEntryP( p->vSeens, p->nWords * iObj );
        if ( Gia_InfoHasBit(pInfo, iFrame) == 0 )
        {
            Gia_InfoSetBit( pInfo, iFrame );
            pCountUni[iFrame+1]++;
            pCountUni[0]++;
        }
        pCountAll[iFrame+1]++;
        pCountAll[0]++;
        if ( !Vec_BitEntry(p->vSeenGla, iObj) )
        {
            Vec_BitWriteEntry(p->vSeenGla, iObj, 1);
            p->nSeenGla++;
        }
    }
//    printf( "%5d%5d", pCountAll[0], pCountUni[0] ); 
    printf( "%6d", p->nSeenGla ); 
    printf( "%6d", pCountAll[0] ); 
    for ( k = 0; k < nFrames; k++ )
//        printf( "%5d%5d  ", pCountAll[k+1], pCountUni[k+1] ); 
        printf( "%4d", pCountAll[k+1] ); 
    printf( "\n" );
    fflush( stdout );
    ABC_FREE( pCountAll );
    ABC_FREE( pCountUni );
}

/**Function*************************************************************

  Synopsis    [Adds clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vga_ManAddClausesOne( Vta_Man_t * p, int iObj, int iFrame )
{ 
    Vta_Obj_t * pThis0, * pThis1;
    Gia_Obj_t * pObj = Gia_ManObj( p->pGia, iObj );
    Vta_Obj_t * pThis = Vga_ManFindOrAdd( p, iObj, iFrame );
    int iMainVar = Vta_ObjId(p, pThis);
    assert( pThis->iObj == iObj && pThis->iFrame == iFrame );
    if ( pThis->fAdded )
        return;
    pThis->fAdded = 1;
    if ( Gia_ObjIsAnd(pObj) )
    {
        pThis0 = Vga_ManFindOrAdd( p, Gia_ObjFaninId0p(p->pGia, pObj), iFrame );
        pThis1 = Vga_ManFindOrAdd( p, Gia_ObjFaninId1p(p->pGia, pObj), iFrame );
        sat_solver2_add_and( p->pSat, iMainVar, Vta_ObjId(p, pThis0), Vta_ObjId(p, pThis1), 
            Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), 0 );
        Vec_IntPush( p->vCla2Var, iMainVar );
        Vec_IntPush( p->vCla2Var, iMainVar );
        Vec_IntPush( p->vCla2Var, iMainVar );
//printf( "Adding node %d (var %d)\n", iObj, iMainVar );
    }
    else if ( Gia_ObjIsRo(p->pGia, pObj) )
    {
//printf( "Adding flop %d (var %d)\n", iObj, iMainVar );
        if ( iFrame == 0 )
        {
            if ( p->pPars->fUseTermVars )
            {
                pThis0 = Vga_ManFindOrAdd( p, iObj, -1 );
                sat_solver2_add_constraint( p->pSat, iMainVar, Vta_ObjId(p, pThis0), 1, 0 );
                Vec_IntPush( p->vCla2Var, iMainVar );
                Vec_IntPush( p->vCla2Var, iMainVar );
            }
            else
            {
                sat_solver2_add_const( p->pSat, iMainVar, 1, 0 );
                Vec_IntPush( p->vCla2Var, iMainVar );
            }
        }
        else
        {
            pObj = Gia_ObjRoToRi( p->pGia, pObj );
            pThis0 = Vga_ManFindOrAdd( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame-1 );
            sat_solver2_add_buffer( p->pSat, iMainVar, Vta_ObjId(p, pThis0), Gia_ObjFaninC0(pObj), 0 );  
            Vec_IntPush( p->vCla2Var, iMainVar );
            Vec_IntPush( p->vCla2Var, iMainVar );
        }
    }
    else if ( Gia_ObjIsConst0(pObj) )
    {
//printf( "Adding const %d (var %d)\n", iObj, iMainVar );
        sat_solver2_add_const( p->pSat, iMainVar, 1, 0 );
        Vec_IntPush( p->vCla2Var, iMainVar );
    }
    else //if ( !Gia_ObjIsPi(p->pGia, pObj) )
        assert( 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vga_ManLoadSlice( Vta_Man_t * p, Vec_Int_t * vOne, int Lift )
{
    int i, Entry;
    Vec_IntForEachEntry( vOne, Entry, i )
        Vga_ManAddClausesOne( p, Entry & p->nObjMask, (Entry >> p->nObjBits) + Lift );
}

/**Function*************************************************************

  Synopsis    [Returns the output literal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vga_ManGetOutLit( Vta_Man_t * p, int f )
{
    Gia_Obj_t * pObj = Gia_ManPo(p->pGia, 0);
    Vta_Obj_t * pThis = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), f );
    assert( pThis != NULL && pThis->fAdded );
    return Gia_Var2Lit( Vta_ObjId(p, pThis), Gia_ObjFaninC0(pObj) );
}

/**Function*************************************************************

  Synopsis    [Collect nodes/flops involved in different timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_VtaPerform( Gia_Man_t * pAig, Gia_ParVta_t * pPars )
{
    Vta_Man_t * p;
    Vta_Obj_t * pThis;
    Vec_Int_t * vCore;
    Abc_Cex_t * pCex = NULL;
    Gia_Obj_t * pObj;
    int i, f, Status, RetValue = -1;
    int clk = clock();
    // preconditions
    assert( Gia_ManPoNum(pAig) == 1 );
    assert( pPars->nFramesMax == 0 || pPars->nFramesStart <= pPars->nFramesMax );
    // start the manager
    p = Vga_ManStart( pAig, pPars );
    // perform initial abstraction
    if ( p->pPars->fVerbose )
        printf( "Frame  Confl  One   All  F0  F1  F2  F3 ...\n" );
    for ( f = 0; !p->pPars->nFramesMax || f < p->pPars->nFramesMax; f++ )
    {
        if ( p->pPars->fVerbose )
            printf( "%3d :", f );
        p->pPars->iFrame = f;
        // realloc storage for abstraction marks
        if ( f == p->nWords * 32 )
            p->nWords = Vec_IntDoubleWidth( p->vSeens, p->nWords );
        // check this timeframe
        if ( f < p->pPars->nFramesStart )
        {
            // load this timeframe
            Vga_ManLoadSlice( p, Vec_PtrEntry(p->vFrames, f), 0 );
            // run SAT solver
            vCore = Vta_ManUnsatCore( Vga_ManGetOutLit(p, f), p->vCla2Var, p->pSat, pPars->nConfLimit, p->pPars->fVerbose, &Status );
            assert( (vCore != NULL) == (Status == 1) );
            if ( Status == -1 )
                break;
            if ( Status == 0 )
            {
                // make sure, there was no initial abstraction (otherwise, it was invalid)
                assert( pAig->vObjClasses == NULL );
                // derive counter-example
                pCex = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), p->pPars->iFrame+1 );
                pCex->iPo = 0;
                pCex->iFrame = p->pPars->iFrame;
                Vta_ManForEachObj( p, pThis, i )
                {
                    pObj = Gia_ManObj( p->pGia, pThis->iObj );
                    if ( Gia_ObjIsPi(p->pGia, pObj) && sat_solver2_var_value(p->pSat, Vta_ObjId(p, pThis)) )
                        Gia_InfoSetBit( pCex->pData, pCex->nRegs + pThis->iFrame * pCex->nPis + Gia_ObjCioId(pObj) );
                }
            }
        }
        else
        {
/*
            // load the time frame
            int Limit = Abc_MinInt(5, p->pPars->nFramesStart);
            for ( i = 1; i <= Limit; i++ )
                Vga_ManLoadSlice( p, Vec_PtrEntry(p->vCores, f-i), i );
            // iterate as long as there are counter-examples
            do {
                vCore = Vta_ManUnsatCore( Vga_ManGetOutLit(p, f), p->vCla2Var, p->pSat, pPars->nConfLimit, pPars->fVerbose, &Status );
                assert( (vCore != NULL) == (Status == 1) );
                if ( Status == -1 ) // resource limit is reached
                    break;
                if ( vCore != NULL )
                {
                    // rollback and add the core
                    // return and double check
                    break;
                }
                pCex = Vta_ManRefineAbstraction( p );
            } 
            while ( pCex == NULL );
            if ( Status == -1 ) // resource limit is reached
                break;
*/
        }
        if ( pCex != NULL )
        {
            printf( "True CEX is detected.\n" );
            RetValue = 0;
            break;
        }
        if ( vCore == NULL )
        {
            printf( "Resource limit is exhausted.\n" );
            RetValue = -1;
            break;
        }
        // add the core
        Vta_ManUnsatCoreRemap( p, vCore );
        Vec_PtrPush( p->vCores, vCore );
        // print the result
        if ( p->pPars->fVerbose )
            Vta_ManAbsPrintFrame( p, vCore, f+1 );

        if ( f == p->pPars->nFramesStart-1 )
            break;
    }
    // analize the results
    if ( pCex == NULL )
    {
        assert( Vec_PtrSize(p->vCores) > 0 );
        if ( pAig->vObjClasses != NULL )
            printf( "Replacing the old abstraction by a new one.\n" );
        Vec_IntFreeP( &pAig->vObjClasses );
        pAig->vObjClasses = Gia_VtaFramesToAbs( (Vec_Vec_t *)p->vCores );
        if ( Status == -1 )
            printf( "SAT solver ran out of resources at %d conflicts in frame %d.  ", pPars->nConfLimit, f );
        else
            printf( "SAT solver completed %d frames and produced an abstraction.  ", f+1 );
    }
    else
    {
        ABC_FREE( p->pGia->pCexSeq );
        p->pGia->pCexSeq = pCex;
        if ( !Gia_ManVerifyCex( p->pGia, pCex, 0 ) )
            printf( "Gia_VtaPerform(): CEX verification has failed!\n" );
        printf( "Counter-example detected in frame %d.  ", f );
    }
    Abc_PrintTime( 1, "Time", clock() - clk );
    Vga_ManStop( p );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

