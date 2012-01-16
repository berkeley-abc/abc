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

#define VTA_LARGE  0xFFFFFF

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Vta_Obj_t_ Vta_Obj_t; // object
struct Vta_Obj_t_
{
    int           iObj;
    int           iFrame;
    int           iNext;
    unsigned      Prio   : 24;  // related to VTA_LARGE
    unsigned      Value  :  2;
    unsigned      fAdded :  1;
    unsigned      fNew   :  1;
};

typedef struct Vta_Man_t_ Vta_Man_t; // manager
struct Vta_Man_t_
{
    // user data
    Gia_Man_t *   pGia;         // AIG manager
    int           nFramesStart; // the number of starting frames
    int           nFramesMax;   // maximum number of frames
    int           nConfMax;     // conflict limit
    int           nTimeMax;     // runtime limit
    int           fVerbose;     // verbose flag
    // internal data
    int           iFrame;       // current frame
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

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converting from one array to per-frame arrays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Vta_ManAbsToFrames( Vec_Int_t * vAbs )
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
Vec_Int_t * Vta_ManFramesToAbs( Vec_Vec_t * vFrames )
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

  Synopsis    [Prints the results.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*
void Vta_ManAbsPrint( Vta_Man_t * p, int fThis )
{
    Vec_Ptr_t * vInfos;
    Vec_Int_t * vPres;
    unsigned * pInfo;
    int CountAll, CountUni;
    int Entry, i, w, f;
    // collected used nodes
    vInfos = Vec_PtrAlloc( 1000 );
    Vec_IntForEachEntry( p->vAbsAll, Entry, i )
    {
        if ( Entry )
            Vec_PtrPush( vInfos, Vta_ObjAbsNew(p, i) );

        pInfo = Vta_ObjAbsNew(p, i);
        for ( w = 0; w < p->nWords; w++ )
            if ( pInfo[w] )
                break;
        assert( Entry == (int)(w < p->nWords) );
    }
    printf( "%d", Vec_PtrSize(vInfos) );
    // print results for used nodes
    vPres = Vec_IntStart( Vec_PtrSize(vInfos) );
    for ( f = 0; f <= fThis; f++ )
    {
        CountAll = CountUni = 0;
        Vec_PtrForEachEntry( unsigned *, vInfos, pInfo, i )
        {
            if ( !Gia_InfoHasBit(pInfo, f) )
                continue;
            CountAll++;
            if ( Vec_IntEntry(vPres, i) )
                continue;
            CountUni++;
            Vec_IntWriteEntry( vPres, i, 1 );
        }
        printf( "  %d(%d)", CountAll, CountUni );
    }
    printf( "\n" );
    Vec_PtrFree( vInfos );
    Vec_IntFree( vPres );
}
*/

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vta_Man_t * Vga_ManStart( Gia_Man_t * pGia, int nFramesStart, int nFramesMax, int nConfMax, int nTimeMax, int fVerbose )
{
    Vta_Man_t * p;
    assert( nFramesMax == 0 || nFramesStart <= nFramesMax );
    p = ABC_CALLOC( Vta_Man_t, 1 );
    p->pGia         = pGia;
    p->nFramesStart = nFramesStart;    
    p->nFramesMax   = nFramesMax;    
    p->nConfMax     = nConfMax;
    p->nTimeMax     = nTimeMax;
    p->fVerbose     = fVerbose;
    // internal data
    p->nObjsAlloc   = (1 << 20);
    p->pObjs        = ABC_CALLOC( Vta_Obj_t, p->nObjsAlloc );
    p->nObjs        = 1;
    p->nBins        = Gia_PrimeCudd( p->nObjsAlloc/2 );
    p->pBins        = ABC_CALLOC( int, p->nBins );
    p->vOrder       = Vec_IntAlloc( 1013 );
    // abstraction
    p->nObjBits     = Gia_Base2Log( Gia_ManObjNum(pGia) );
    p->nObjMask     = (1 << p->nObjBits) - 1;
    assert( Gia_ManObjNum(pGia) <= (int)p->nObjMask );
    p->nWords       = 1;
    p->vSeens       = Vec_IntStart( Gia_ManObjNum(pGia) * p->nWords );
    // start the abstraction
    if ( pGia->vObjClasses )
        p->vFrames  = Vta_ManAbsToFrames( pGia->vObjClasses );
    else
        p->vFrames  = Gia_ManUnrollAbs( pGia, nFramesStart );
    // other data
    p->vCla2Var     = Vec_IntAlloc( 1000 );
    p->vCores       = Vec_PtrAlloc( 100 );
    p->pSat         = sat_solver2_new();



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
    Vec_VecFreeP( (Vec_Vec_t **)&p->vCores );
    Vec_IntFreeP( &p->vSeens );
    Vec_IntFreeP( &p->vOrder );
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
void Vga_ManAddClausesOne( Vta_Man_t * p, Vta_Obj_t * pThis )
{
    Vta_Obj_t * pThis0, * pThis1;
    Gia_Obj_t * pObj;
    int i = Vta_ObjId( p, pThis );
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

/**Function*************************************************************

  Synopsis    [Finds the set of clauses involved in the UNSAT core.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Vta_ManUnsatCore( Vec_Int_t * vCla2Var, sat_solver2 * pSat, int nConfMax, int fVerbose, int * piRetValue )
{
    Vec_Int_t * vPres;
    Vec_Int_t * vCore;
    int k, i, Entry, RetValue, clk = clock();
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
        printf( "Core is %8d vars (out of %8d).   ", Vec_IntSize(vCore), sat_solver2_nvars(pSat) );
        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    return vCore;
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
    }
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
            unsigned * pInfo = (unsigned *)Vec_IntEntryP( p->vSeens, p->nWords * pThis->iObj );
            int i;
            for ( i = 0; i < p->nWords; i++ )
                if ( pInfo[i] )
                    break;
            assert( pThis->Prio > 0 || pThis->Prio < VTA_LARGE );
//            if ( Vec_IntEntry(p->vAbsAll, pThis->iObj) )
            if ( i < p->nWords )
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
        pCex = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), p->iFrame+1 );
        pCex->iPo = 0;
        pCex->iFrame = p->iFrame;
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
            Vga_ManAddClausesOne( p, pThis );
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
static inline void Vga_ManUnroll_rec( Vta_Man_t * p, int iObj, int iFrame )
{
    int iVar;
    Gia_Obj_t * pObj;
    Vta_Obj_t * pThis;
//    if ( !Gia_InfoHasBit( Vta_ObjAbsOld(p, iObj), iFrame ) )
//        return;
    pThis = Vga_ManFindOrAdd( p, iObj, iFrame );
    if ( !pThis->fNew )
        return;
    pThis->fNew = 0;
    iVar = Vta_ObjId( p, pThis );
    pObj = Gia_ManObj( p->pGia, iObj );
    assert( !Gia_ObjIsCo(pObj) );
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
    Vec_IntPush( p->vOrder, iVar );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vta_ManAbsPrintFrame( Vta_Man_t * p, Vec_Int_t * vCore, int iFrame )
{
    int i, k, iObj, Entry;
    unsigned * pInfo, * pCountAll, * pCountUni;
    // print info about frames
    pCountAll = ABC_CALLOC( int, iFrame + 2 );
    pCountUni = ABC_CALLOC( int, iFrame + 2 );
    Vec_IntForEachEntry( vCore, Entry, i )
    {
        iObj   = (Entry &  p->nObjMask);
        iFrame = (Entry >> p->nObjBits);
        pInfo  = (unsigned *)Vec_IntEntryP( p->vSeens, p->nWords * iObj );
        if ( Gia_InfoHasBit(pInfo, iFrame) == 0 )
        {
            Gia_InfoSetBit( pInfo, iFrame );
            pCountUni[iFrame+1]++;
            pCountUni[0]++;
        }
        pCountAll[iFrame+1]++;
        pCountAll[0]++;

        printf( "%5d%5d  ", pCountAll[0], pCountUni[0] ); 
        for ( k = 0; k <= iFrame; k++ )
            printf( "%5d%5d  ", pCountAll[k+1], pCountUni[k+1] ); 
        printf( "\n" );
    }
    ABC_FREE( pCountAll );
    ABC_FREE( pCountUni );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vga_ManAddOneSlice( Vta_Man_t * p, Vec_Int_t * vOne, int Lift )
{
    int Entry, i;
    Vec_IntForEachEntry( vOne, Entry, i )
        Vga_ManFindOrAdd( p, Entry & p->nObjMask, (Entry >> p->nObjBits) + Lift );
}

/**Function*************************************************************

  Synopsis    [Collect nodes/flops involved in different timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_VtaTest( Gia_Man_t * pAig, int nFramesStart, int nFramesMax, int nConfMax, int nTimeMax, int fVerbose )
{
    Vta_Man_t * p;
    Gia_Obj_t * pObj;
    Abc_Cex_t * pCex = NULL;
    Vec_Int_t * vCore, * vOne;
    int f, i, iObjPrev, RetValue, Limit;
    assert( Gia_ManPoNum(pAig) == 1 );
    pObj = Gia_ManPo( pAig, 0 );
    // start the manager
    p = Vga_ManStart( pAig, nFramesStart, nFramesMax, nConfMax, nTimeMax, fVerbose );
    // perform initial abstraction
    for ( f = 0; f < nFramesMax; f++ )
    {
        if ( f == p->nWords * 32 )
            p->nWords = Vec_IntDoubleWidth( p->vSeens, p->nWords );
        p->iFrame = f;
        if ( fVerbose )
            printf( "Frame %4d : ", f );
        if ( f < nFramesStart )
        {
            // load the time frame
            iObjPrev = p->nObjs;
            vOne = Vec_PtrEntry( p->vFrames, f );
            Vga_ManAddOneSlice( p, vOne, 0 );
            for ( i = iObjPrev; i < p->nObjs; i++ )
                Vga_ManAddClausesOne( p, Vta_ManObj(p, i) );
            // run SAT solver
            vCore = Vta_ManUnsatCore( p->vCla2Var, p->pSat, nConfMax, fVerbose, &RetValue );
            if ( vCore == NULL && RetValue == 0 )
            {
                // make sure, there was no initial abstraction (otherwise, it was invalid)
                assert( pAig->vObjClasses == NULL );
                // derive counter-example
                pCex = NULL;
                break;
            }
        }
        else
        {
            break;

            Limit = Abc_MinInt(3, nFramesStart);
            // load the time frame
            iObjPrev = p->nObjs;
            for ( i = 1; i <= Limit; i++ )
            {
                vOne = Vec_PtrEntry( p->vCores, f-i );
                Vga_ManAddOneSlice( p, vOne, i );
            }
            for ( i = iObjPrev; i < p->nObjs; i++ )
                Vga_ManAddClausesOne( p, Vta_ManObj(p, i) );
            // iterate as long as there are counter-examples
            while ( 1 )
            {
                vCore = Vta_ManUnsatCore( p->vCla2Var, p->pSat, nConfMax, fVerbose, &RetValue );
                if ( RetValue ) // resource limit is reached
                {
                    assert( vCore == NULL );
                    break;
                }
                if ( vCore != NULL )
                {
                    // unroll the solver, add the core
                    // return and double check
                    break;
                }
                pCex = Vta_ManRefineAbstraction( p );
                if ( pCex != NULL )
                    break;
            }
        }
        if ( pCex != NULL )
        {
            // the problem is SAT
        }
        if ( vCore == NULL )
        {
            // resource limit is reached
        }
        // add the core
        Vec_PtrPush( p->vCores, vCore );
        // print the result
        if ( fVerbose )
            Vta_ManAbsPrintFrame( p, vCore, f );
    }
    assert( Vec_PtrSize(p->vCores) > 0 );
    if ( pAig->vObjClasses != NULL )
        printf( "Replacing the old abstraction by a new one.\n" );
    Vec_IntFreeP( &pAig->vObjClasses );
    pAig->vObjClasses = Vta_ManFramesToAbs( (Vec_Vec_t *)p->vCores );
    Vga_ManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

