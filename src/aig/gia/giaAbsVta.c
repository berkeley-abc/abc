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
#include "src/sat/bsat/satSolver2.h"

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
    unsigned      fVisit :  1;
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
    Vta_Obj_t *   pObjs;        // storage for objects
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
    Vec_Int_t *   vAddedNew;    // the IDs of variables added to the solver
    // statistics 
    int           timeSat;
    int           timeUnsat;
    int           timeCex;
    int           timeOther;
};


// ternary simulation

#define VTA_VAR0   1
#define VTA_VAR1   2
#define VTA_VARX   3

static inline int Vta_ValIs0( Vta_Obj_t * pThis, int fCompl )
{
    if ( pThis->Value == VTA_VAR1 && fCompl )
        return 1;
    if ( pThis->Value == VTA_VAR0 && !fCompl )
        return 1;
    return 0;
}
static inline int Vta_ValIs1( Vta_Obj_t * pThis, int fCompl )
{
    if ( pThis->Value == VTA_VAR0 && fCompl )
        return 1;
    if ( pThis->Value == VTA_VAR1 && !fCompl )
        return 1;
    return 0;
}

static inline Vta_Obj_t *  Vta_ManObj( Vta_Man_t * p, int i )           { assert( i >= 0 && i < p->nObjs ); return i ? p->pObjs + i : NULL;                     }
static inline int          Vta_ObjId( Vta_Man_t * p, Vta_Obj_t * pObj ) { assert( pObj > p->pObjs && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs;      }

#define Vta_ManForEachObj( p, pObj, i )                                 \
    for ( i = 1; (i < p->nObjs) && ((pObj) = Vta_ManObj(p, i)); i++ )
#define Vta_ManForEachObjObj( p, pObjVta, pObjGia, i )                  \
    for ( i = 1; (i < p->nObjs) && ((pObjVta) = Vta_ManObj(p, i)) && ((pObjGia) = Gia_ManObj(p->pGia, pObjVta->iObj)); i++ )
#define Vta_ManForEachObjObjReverse( p, pObjVta, pObjGia, i )           \
    for ( i = Vec_IntSize(vVec) - 1; (i >= 1) && ((pObjVta) = Vta_ManObj(p, i)) && ((pObjGia) = Gia_ManObj(p->pGia, pObjVta->iObj)); i++ )

#define Vta_ManForEachObjVec( vVec, p, pObj, i )                        \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pObj) = Vta_ManObj(p, Vec_IntEntry(vVec,i))); i++ )
#define Vta_ManForEachObjVecReverse( vVec, p, pObj, i )                 \
    for ( i = Vec_IntSize(vVec) - 1; (i >= 0) && ((pObj) = Vta_ManObj(p, Vec_IntEntry(vVec,i))); i-- )

#define Vta_ManForEachObjObjVec( vVec, p, pObj, pObjG, i )              \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pObj) = Vta_ManObj(p, Vec_IntEntry(vVec,i))) && ((pObjG) = Gia_ManObj(p->pGia, pObj->iObj)); i++ )
#define Vta_ManForEachObjObjVecReverse( vVec, p, pObj, pObjG, i )       \
    for ( i = Vec_IntSize(vVec) - 1; (i >= 0) && ((pObj) = Vta_ManObj(p, Vec_IntEntry(vVec,i))) && ((pObjG) = Gia_ManObj(p->pGia, pObj->iObj)); i-- )


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
    p->nFramesStart  =    5;   // starting frame 
    p->nFramesMax    =   10;   // maximum frames
    p->nFramesOver   =    3;   // overlap frames
    p->nConfLimit    =    0;   // conflict limit
    p->nTimeOut      =   60;   // timeout in seconds
    p->fUseTermVars  =    0;   // use terminal variables
    p->fVerbose      =    0;   // verbose flag
    p->iFrame        =   -1;   // the number of frames covered 
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
    nObjMask = (1 << Abc_Base2Log(nObjs)) - 1;
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
        if ( Abc_InfoHasBit(pTotal, i) )
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
    return ((unsigned)((iObj + iFrame)*(iObj + iFrame + 1))) % nBins;
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
    int i, * pPlace;
    assert( iObj >= 0 && iFrame >= -1 );
    if ( p->nObjs == p->nObjsAlloc )
    {
        // resize objects
        p->pObjs = ABC_REALLOC( Vta_Obj_t, p->pObjs, 2 * p->nObjsAlloc );
        memset( p->pObjs + p->nObjsAlloc, 0, p->nObjsAlloc * sizeof(Vta_Obj_t) );
        p->nObjsAlloc *= 2;
        // rehash entries in the table
        ABC_FREE( p->pBins );
        p->nBins = Abc_PrimeCudd( 2 * p->nBins );
        p->pBins = ABC_CALLOC( int, p->nBins );
        Vta_ManForEachObj( p, pThis, i )
        {
            pThis->iNext = 0;
            pPlace = Vga_ManLookup( p, pThis->iObj, pThis->iFrame );
            assert( *pPlace == 0 );
            *pPlace = i;
        }
    }
    pPlace = Vga_ManLookup( p, iObj, iFrame );
    if ( *pPlace )
        return Vta_ManObj(p, *pPlace);
    *pPlace = p->nObjs++;
    pThis = Vta_ManObj(p, *pPlace);
    pThis->iObj   = iObj;
    pThis->iFrame = iFrame;
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

  Synopsis    [Derives counter-example using current assignments.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Vga_ManDeriveCex( Vta_Man_t * p )
{
    Abc_Cex_t * pCex;
    Vta_Obj_t * pThis;
    Gia_Obj_t * pObj;
    int i;
    pCex = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), p->pPars->iFrame+1 );
    pCex->iPo = 0;
    pCex->iFrame = p->pPars->iFrame;
    Vta_ManForEachObjObj( p, pThis, pObj, i )
        if ( Gia_ObjIsPi(p->pGia, pObj) && sat_solver2_var_value(p->pSat, Vta_ObjId(p, pThis)) )
            Abc_InfoSetBit( pCex->pData, pCex->nRegs + pThis->iFrame * pCex->nPis + Gia_ObjCioId(pObj) );
    return pCex;
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

  Synopsis    [Finds predecessors of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vta_ObjPreds( Vta_Man_t * p, Vta_Obj_t * pThis, Gia_Obj_t * pObj, Vta_Obj_t ** ppThis0, Vta_Obj_t ** ppThis1 )
{
    *ppThis0 = NULL;
    *ppThis1 = NULL;
    if ( !pThis->fAdded )
        return;
    assert( !Gia_ObjIsPi(p->pGia, pObj) );
    if ( Gia_ObjIsConst0(pObj) || (Gia_ObjIsCi(pObj) && pThis->iFrame == 0) )
        return;
    if ( Gia_ObjIsAnd(pObj) )
    {
        *ppThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame );
        *ppThis1 = Vga_ManFind( p, Gia_ObjFaninId1p(p->pGia, pObj), pThis->iFrame );
        assert( *ppThis0 && *ppThis1 );
        return;
    }
    assert( Gia_ObjIsRo(p->pGia, pObj) && pThis->iFrame > 0 );
    pObj = Gia_ObjRoToRi( p->pGia, pObj );
    *ppThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame-1 );
    assert( *ppThis0 );
}

/**Function*************************************************************

  Synopsis    [Collect const/PI/RO/AND in a topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vta_ManCollectNodes_rec( Vta_Man_t * p, Vta_Obj_t * pThis, Vec_Int_t * vOrder )
{
    Gia_Obj_t * pObj;
    Vta_Obj_t * pThis0, * pThis1;
    if ( pThis->fVisit )
        return;
    pThis->fVisit = 1;
    pObj = Gia_ManObj( p->pGia, pThis->iObj );
    Vta_ObjPreds( p, pThis, pObj, &pThis0, &pThis1 );
    if ( pThis0 ) Vta_ManCollectNodes_rec( p, pThis0, vOrder );
    if ( pThis1 ) Vta_ManCollectNodes_rec( p, pThis1, vOrder );
    Vec_IntPush( vOrder, Vta_ObjId(p, pThis) );
}
Vec_Int_t * Vta_ManCollectNodes( Vta_Man_t * p, int f )
{
    Vta_Obj_t * pThis;
    Gia_Obj_t * pObj;
    Vec_IntClear( p->vOrder );
    pObj = Gia_ManPo( p->pGia, 0 );
    pThis = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), f );
    assert( pThis != NULL );
    assert( !pThis->fVisit );
    Vta_ManCollectNodes_rec( p, pThis, p->vOrder );
    assert( pThis->fVisit );
    return p->vOrder;
}

/**Function*************************************************************

  Synopsis    [Refines abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vta_ManSatVerify( Vta_Man_t * p )
{
    Vta_Obj_t * pThis, * pThis0, * pThis1;
    Gia_Obj_t * pObj;
    int i;
    Vta_ManForEachObj( p, pThis, i )
        pThis->Value = (sat_solver2_var_value(p->pSat, i) ? VTA_VAR1 : VTA_VAR0);
    Vta_ManForEachObjObj( p, pThis, pObj, i )
    {
        if ( !pThis->fAdded )
            continue;
        Vta_ObjPreds( p, pThis, pObj, &pThis0, &pThis1 );
        if ( Gia_ObjIsAnd(pObj) )
        {
            int iVar  = Vta_ObjId(p, pThis);
            int iVar0 = Vta_ObjId(p, pThis0);
            int iVar1 = Vta_ObjId(p, pThis1);
            if ( pThis->Value == VTA_VAR1 )
                assert( Vta_ValIs1(pThis0, Gia_ObjFaninC0(pObj)) && Vta_ValIs1(pThis1, Gia_ObjFaninC1(pObj)) );
            else if ( pThis->Value == VTA_VAR0 )
                assert( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) || Vta_ValIs0(pThis1, Gia_ObjFaninC1(pObj)) );
            else assert( 0 );
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            int VarA = Vta_ObjId(p,pThis);
            int VarB = !pThis0 ? 0 : Vta_ObjId(p,pThis0);
            pObj = Gia_ObjRoToRi( p->pGia, pObj );
            if ( pThis->iFrame == 0 )
                assert( pThis->Value == VTA_VAR0 );
            else if ( pThis->Value == VTA_VAR0 )
                assert( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) );
            else if ( pThis->Value == VTA_VAR1 )
                assert( Vta_ValIs1(pThis0, Gia_ObjFaninC0(pObj)) );
            else assert( 0 );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Refines abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Vta_ManRefineAbstraction( Vta_Man_t * p, int f )
{
    Abc_Cex_t * pCex = NULL;
    Vec_Int_t * vOrder, * vTermsToAdd;
    Vec_Ptr_t * vTermsUsed, * vTermsUnused;
    Vta_Obj_t * pThis, * pThis0, * pThis1, * pTop;
    Gia_Obj_t * pObj;
    int i, Counter;

//    Vta_ManSatVerify( p );

    // collect nodes in a topological order
    vOrder = Vta_ManCollectNodes( p, f );
    Vta_ManForEachObjObjVec( vOrder, p, pThis, pObj, i )
    {
        pThis->Prio = VTA_LARGE;
        pThis->Value = sat_solver2_var_value(p->pSat, Vta_ObjId(p, pThis)) ? VTA_VAR1 : VTA_VAR0;
        pThis->fVisit = 0;
    }
/*
    // verify
    Vta_ManForEachObjObjVec( vOrder, p, pThis, pObj, i )
    {
        if ( !pThis->fAdded )
            continue;
        Vta_ObjPreds( p, pThis, pObj, &pThis0, &pThis1 );
        if ( Gia_ObjIsAnd(pObj) )
        {
            if ( pThis->Value == VTA_VAR1 )
                assert( Vta_ValIs1(pThis0, Gia_ObjFaninC0(pObj)) && Vta_ValIs1(pThis1, Gia_ObjFaninC1(pObj)) );
            else if ( pThis->Value == VTA_VAR0 )
                assert( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) || Vta_ValIs0(pThis1, Gia_ObjFaninC1(pObj)) );
            else assert( 0 );
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            pObj = Gia_ObjRoToRi( p->pGia, pObj );
            if ( pThis->iFrame == 0 )
                assert( pThis->Value == VTA_VAR0 );
            else if ( pThis->Value == VTA_VAR0 )
                assert( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) );
            else if ( pThis->Value == VTA_VAR1 )
                assert( Vta_ValIs1(pThis0, Gia_ObjFaninC0(pObj)) );
            else assert( 0 );
        }
    }
*/
    // compute distance in reverse order
    pThis = Vta_ManObj( p, Vec_IntEntryLast(vOrder) );
    pThis->Prio  = 1;
    // collect used and unused terms
    vTermsUsed   = Vec_PtrAlloc( 1015 );
    vTermsUnused = Vec_PtrAlloc( 1016 );
    Vta_ManForEachObjObjVecReverse( vOrder, p, pThis, pObj, i )
    {
        // there is no unreachable states
        assert( pThis->Prio < VTA_LARGE );
        // skip constants and PIs
        if ( Gia_ObjIsConst0(pObj) || Gia_ObjIsPi(p->pGia, pObj) )
        {
            pThis->Prio = 0; // set highest priority
            continue;
        }
        // collect terminals
        assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(p->pGia, pObj) );
        if ( !pThis->fAdded )
        {
            assert( pThis->Prio > 0 );
            if ( Vta_ManObjIsUsed(p, pThis->iObj) )
                Vec_PtrPush( vTermsUsed, pThis );
            else
                Vec_PtrPush( vTermsUnused, pThis );
            continue;
        }
        // propagate
        Vta_ObjPreds( p, pThis, pObj, &pThis0, &pThis1 );
        if ( pThis0 ) 
            pThis0->Prio = Abc_MinInt( pThis0->Prio, pThis->Prio + 1 );
        if ( pThis1 ) 
            pThis1->Prio = Abc_MinInt( pThis1->Prio, pThis->Prio + 1 );
    }
    // objects with equal distance should receive priority based on number
    // those objects whose prototypes have been added in other timeframes
    // should have higher priority than the current object
    Vec_PtrSort( vTermsUsed,   (int (*)(void))Vta_ManComputeDepthIncrease );
    Vec_PtrSort( vTermsUnused, (int (*)(void))Vta_ManComputeDepthIncrease );
    if ( Vec_PtrSize(vTermsUsed) > 1 )
    {
        pThis0 = (Vta_Obj_t *)Vec_PtrEntry(vTermsUsed, 0);
        pThis1 = (Vta_Obj_t *)Vec_PtrEntryLast(vTermsUsed);
        assert( pThis0->Prio <= pThis1->Prio );
    }
    // assign the priority based on these orders
    Counter = 1;
    Vec_PtrForEachEntry( Vta_Obj_t *, vTermsUsed, pThis, i )
        pThis->Prio = Counter++;
    Vec_PtrForEachEntry( Vta_Obj_t *, vTermsUnused, pThis, i )
        pThis->Prio = Counter++;
//    printf( "Used %d  Unused %d\n", Vec_PtrSize(vTermsUsed), Vec_PtrSize(vTermsUnused) );

    Vec_PtrFree( vTermsUsed );
    Vec_PtrFree( vTermsUnused );


    // propagate in the direct order
    Vta_ManForEachObjObjVec( vOrder, p, pThis, pObj, i )
    {
        assert( pThis->fVisit == 0 );
        assert( pThis->Prio < VTA_LARGE );
        // skip terminal objects
        if ( !pThis->fAdded )
            continue;
        // assumes that values are assigned!!!
        assert( pThis->Value != 0 );
        // propagate
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
                    pThis->Prio = Abc_MinInt( pThis0->Prio, pThis1->Prio ); // choice!!!
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
            else
                pThis->Prio = 0;
        }
        else if ( Gia_ObjIsConst0(pObj) )
            pThis->Prio = 0;
        else
            assert( 0 );
    }

    // select important values
    pTop = Vta_ManObj( p, Vec_IntEntryLast(vOrder) );
    pTop->fVisit = 1;
    vTermsToAdd = Vec_IntAlloc( 100 );
    Vta_ManForEachObjObjVecReverse( vOrder, p, pThis, pObj, i )
    {
        if ( !pThis->fVisit )
            continue;
        pThis->fVisit = 0;
        assert( pThis->Prio >= 0 && pThis->Prio <= pTop->Prio );
        // skip terminal objects
        if ( !pThis->fAdded )
        {
            assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsRo(p->pGia, pObj) || Gia_ObjIsConst0(pObj) || Gia_ObjIsPi(p->pGia, pObj) );
            Vec_IntPush( vTermsToAdd, Vta_ObjId(p, pThis) );
            continue;
        }
        // assumes that values are assigned!!!
        assert( pThis->Value != 0 );
        // propagate
        if ( Gia_ObjIsAnd(pObj) )
        {
            pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame );
            pThis1 = Vga_ManFind( p, Gia_ObjFaninId1p(p->pGia, pObj), pThis->iFrame );
            assert( pThis0 && pThis1 );
            if ( pThis->Value == VTA_VAR1 )
            {
                assert( Vta_ValIs1(pThis0, Gia_ObjFaninC0(pObj)) && Vta_ValIs1(pThis1, Gia_ObjFaninC1(pObj)) );
                assert( pThis0->Prio <= pThis->Prio );
                assert( pThis1->Prio <= pThis->Prio );
                pThis0->fVisit = 1;
                pThis1->fVisit = 1;
            }
            else if ( pThis->Value == VTA_VAR0 )
            {
                if ( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) && Vta_ValIs0(pThis1, Gia_ObjFaninC1(pObj)) )
                {
                    if ( pThis0->fVisit )
                    {
                    }
                    else if ( pThis1->fVisit )
                    {
                    }
                    else if ( pThis0->Prio <= pThis1->Prio ) // choice!!!
                    {
                        pThis0->fVisit = 1;
                        assert( pThis0->Prio == pThis->Prio );
                    }
                    else
                    {
                        pThis1->fVisit = 1;
                        assert( pThis1->Prio == pThis->Prio );
                    }
                }
                else if ( Vta_ValIs0(pThis0, Gia_ObjFaninC0(pObj)) )
                {
                    pThis0->fVisit = 1;
                    assert( pThis0->Prio == pThis->Prio );
                }
                else if ( Vta_ValIs0(pThis1, Gia_ObjFaninC1(pObj)) )
                {
                    pThis1->fVisit = 1;
                    assert( pThis1->Prio == pThis->Prio );
                }
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
                pThis0->fVisit = 1;
                assert( pThis0->Prio == pThis->Prio );
            }
        }
        else if ( !Gia_ObjIsConst0(pObj) )
            assert( 0 );
    }

/*
    // verify
    Vta_ManForEachObjVec( vOrder, p, pThis, i )
        pThis->Value = VTA_VARX;
    Vta_ManForEachObjVec( vTermsToAdd, p, pThis, i )
    {
        assert( !pThis->fAdded );
        pThis->Value = sat_solver2_var_value(p->pSat, Vta_ObjId(p, pThis)) ? VTA_VAR1 : VTA_VAR0;
    }
    // simulate 
    Vta_ManForEachObjObjVec( vOrder, p, pThis, pObj, i )
    {
        assert( pThis->fVisit == 0 );
        if ( !pThis->fAdded )
            continue;
        if ( Gia_ObjIsAnd(pObj) )
        {
            pThis0 = Vga_ManFind( p, Gia_ObjFaninId0p(p->pGia, pObj), pThis->iFrame );
            pThis1 = Vga_ManFind( p, Gia_ObjFaninId1p(p->pGia, pObj), pThis->iFrame );
            assert( pThis0 && pThis1 );
//            printf( "AND %d  %d %d  ", Vta_ObjId(p, pThis), Vta_ObjId(p,pThis0), Vta_ObjId(p,pThis1) );
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
//            printf( "RO %d  ", Vta_ObjId(p, pThis), Vta_ObjId(p,pThis0) );
            }
            else
            {
//            printf( "RO %d frame0  ", Vta_ObjId(p, pThis) );
                pThis->Value = VTA_VAR0;
            }
        }
        else if ( Gia_ObjIsConst0(pObj) )
        {
//            printf( "CONST0 %d  ", Vta_ObjId(p, pThis) );
            pThis->Value = VTA_VAR0;
        }
        else assert( 0 );
//        printf( "val = %d. \n", (pThis->Value==VTA_VAR0) ? 0 : ((pThis->Value==VTA_VAR0) ? 1 : 2 ) );
        // double check the solver
        assert( pThis->Value == VTA_VARX || (int)pThis->Value == (sat_solver2_var_value(p->pSat, Vta_ObjId(p, pThis)) ? VTA_VAR1 : VTA_VAR0) );
    }

    // check the output
    if ( !Vta_ValIs1(pTop, Gia_ObjFaninC0(Gia_ManPo(p->pGia, 0))) )
        printf( "Vta_ManRefineAbstraction(): Terminary simulation verification failed!\n" );
//    else
//        printf( "Verification OK.\n" );
*/

    // produce true counter-example
    if ( pTop->Prio == 0 )
        pCex = Vga_ManDeriveCex( p );
    else
    {
        int nObjOld = p->nObjs;
        Vta_ManForEachObjObjVec( vTermsToAdd, p, pThis, pObj, i )
            if ( !Gia_ObjIsPi(p->pGia, pObj) )
                Vga_ManAddClausesOne( p, pThis->iObj, pThis->iFrame );
        sat_solver2_simplify( p->pSat );
    }
    Vec_IntFree( vTermsToAdd );
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
    p->nBins       = Abc_PrimeCudd( 2*p->nObjsAlloc );
    p->pBins       = ABC_CALLOC( int, p->nBins );
    p->vOrder      = Vec_IntAlloc( 1013 );
    // abstraction
    p->nObjBits    = Abc_Base2Log( Gia_ManObjNum(pGia) );
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
    p->vCla2Var    = Vec_IntAlloc( 1000 );  Vec_IntPush( p->vCla2Var, -1 );
    p->vCores      = Vec_PtrAlloc( 100 );
    p->pSat        = sat_solver2_new();
    p->vAddedNew   = Vec_IntAlloc( 1000 );
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
//    if ( p->pPars->fVerbose )
        printf( "SAT solver:  Variables = %d. Clauses = %d. Conflicts = %d.\n", 
            sat_solver2_nvars(p->pSat), sat_solver2_nclauses(p->pSat), sat_solver2_nconflicts(p->pSat) );

    Vec_VecFreeP( (Vec_Vec_t **)&p->vCores );
    Vec_VecFreeP( (Vec_Vec_t **)&p->vFrames );
    Vec_BitFreeP( &p->vSeenGla );
    Vec_IntFreeP( &p->vSeens );
    Vec_IntFreeP( &p->vOrder );
    Vec_IntFreeP( &p->vCla2Var );
    Vec_IntFreeP( &p->vAddedNew );
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
Vec_Int_t * Vta_ManUnsatCore( int iLit, Vec_Int_t * vCla2Var, sat_solver2 * pSat, int nConfMax, int fVerbose, int * piRetValue, int * pnConfls )
{
    Vec_Int_t * vPres;
    Vec_Int_t * vCore;
    int k, i, Entry, RetValue, clk = clock();
    int nConfPrev = pSat->stats.conflicts;
    if ( piRetValue )
        *piRetValue = 1;
    // solve the problem
    RetValue = sat_solver2_solve( pSat, &iLit, &iLit+1, (ABC_INT64_T)nConfMax, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( pnConfls )
        *pnConfls = (int)pSat->stats.conflicts - nConfPrev;
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
//        printf( "%6d", (int)pSat->stats.conflicts - nConfPrev );
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
void Vta_ManAbsPrintFrame( Vta_Man_t * p, Vec_Int_t * vCore, int nFrames, int nCexes, int fVerbose )
{
    unsigned * pInfo;
    int * pCountAll, * pCountUni;
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
        if ( !Abc_InfoHasBit(pInfo, iFrame) )
        {
            Abc_InfoSetBit( pInfo, iFrame );
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
    if ( fVerbose )
    {
    //    printf( "%5d%5d", pCountAll[0], pCountUni[0] ); 
        printf( "%6d", p->nSeenGla ); 
        printf( "%5d", nCexes ); 
        printf( "%7d", pCountAll[0] ); 
        for ( k = 0; k < nFrames; k++ )
    //        printf( "%5d%5d  ", pCountAll[k+1], pCountUni[k+1] ); 
            printf( "%5d", pCountAll[k+1] ); 
        printf( "\n" );
        fflush( stdout );
    }
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
    int iThis0, iMainVar = Vta_ObjId(p, pThis);
    assert( pThis->iObj == iObj && pThis->iFrame == iFrame );
    if ( pThis->fAdded )
        return;
    pThis->fAdded = 1;
    Vec_IntPush( p->vAddedNew, iMainVar );
    if ( Gia_ObjIsAnd(pObj) )
    {
        pThis0 = Vga_ManFindOrAdd( p, Gia_ObjFaninId0p(p->pGia, pObj), iFrame );
        iThis0 = Vta_ObjId(p, pThis0);
        pThis1 = Vga_ManFindOrAdd( p, Gia_ObjFaninId1p(p->pGia, pObj), iFrame );
        sat_solver2_add_and( p->pSat, iMainVar, iThis0, Vta_ObjId(p, pThis1), 
            Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), 0 );
        Vec_IntPush( p->vCla2Var, iMainVar );
        Vec_IntPush( p->vCla2Var, iMainVar );
        Vec_IntPush( p->vCla2Var, iMainVar );
    }
    else if ( Gia_ObjIsRo(p->pGia, pObj) )
    {
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
            pThis0 = Vga_ManFindOrAdd( p, Gia_ObjFaninId0p(p->pGia, pObj), iFrame-1 );
            sat_solver2_add_buffer( p->pSat, iMainVar, Vta_ObjId(p, pThis0), Gia_ObjFaninC0(pObj), 0 );  
            Vec_IntPush( p->vCla2Var, iMainVar );
            Vec_IntPush( p->vCla2Var, iMainVar );
        }
    }
    else if ( Gia_ObjIsConst0(pObj) )
    {
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
    sat_solver2_simplify( p->pSat );
//    printf( "\n\n" );
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
    return Abc_Var2Lit( Vta_ObjId(p, pThis), Gia_ObjFaninC0(pObj) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vga_ManPrintCore( Vta_Man_t * p, Vec_Int_t * vCore, int Lift )
{
    int i, Entry, iObj, iFrame;
    Vec_IntForEachEntry( vCore, Entry, i )
    {
        iObj   = (Entry &  p->nObjMask);
        iFrame = (Entry >> p->nObjBits);
        printf( "%d*%d ", iObj, iFrame+Lift );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vga_ManRollBack( Vta_Man_t * p, int nObjOld )
{
    Vta_Obj_t * pThis  = p->pObjs + nObjOld;
    Vta_Obj_t * pLimit = p->pObjs + p->nObjs;
    int i, Entry;
    for ( ; pThis < pLimit; pThis++ )
        Vga_ManDelete( p, pThis->iObj, pThis->iFrame );
    memset( p->pObjs + nObjOld, 0, sizeof(Vta_Obj_t) * (p->nObjs - nObjOld) );
    p->nObjs = nObjOld;
    Vec_IntForEachEntry( p->vAddedNew, Entry, i )
        if ( Entry < p->nObjs )
        {
            pThis = Vta_ManObj(p, Entry);
            assert( pThis->fAdded == 1 );
            pThis->fAdded = 0;
        }
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
    Vec_Int_t * vCore;
    Abc_Cex_t * pCex = NULL;
    int i, f, nConfls, Status, RetValue = -1;
    int clk = clock(), clk2;
    // preconditions
    assert( Gia_ManPoNum(pAig) == 1 );
    assert( pPars->nFramesMax == 0 || pPars->nFramesStart <= pPars->nFramesMax );
    // start the manager
    p = Vga_ManStart( pAig, pPars );
    // perform initial abstraction
    if ( p->pPars->fVerbose )
        printf( "Frame  Confl  One  Cex    All   F0   F1   F2   F3  ...\n" );
    for ( f = 0; !p->pPars->nFramesMax || f < p->pPars->nFramesMax; f++ )
    {
        if ( p->pPars->fVerbose )
            printf( "%3d :", f );
        p->pPars->iFrame = f;
        // realloc storage for abstraction marks
        if ( f == p->nWords * 32 )
            p->nWords = Vec_IntDoubleWidth( p->vSeens, p->nWords );
        // check this timeframe
        i = 0; 
        if ( f < p->pPars->nFramesStart )
        {
//            printf( " Adding %8d  ", Vec_IntSize(Vec_PtrEntry(p->vFrames, f)) );
            Vga_ManAddClausesOne( p, 0, f );
            Vga_ManLoadSlice( p, (Vec_Int_t *)Vec_PtrEntry(p->vFrames, f), 0 );
        }
        else
        {
            // create bookmark to be used for rollback
            int nObjOld = p->nObjs;
            sat_solver2_bookmark( p->pSat );
            Vec_IntClear( p->vAddedNew );
            // load the time frame
            for ( i = 1; i <= Abc_MinInt(p->pPars->nFramesOver, p->pPars->nFramesStart); i++ )
                Vga_ManLoadSlice( p, (Vec_Int_t *)Vec_PtrEntry(p->vCores, f-i), i );
            // iterate as long as there are counter-examples
            for ( i = 0; ; i++ )
            { 
                clk2 = clock();
                vCore = Vta_ManUnsatCore( Vga_ManGetOutLit(p, f), p->vCla2Var, p->pSat, pPars->nConfLimit, pPars->fVerbose, &Status, &nConfls );
                assert( (vCore != NULL) == (Status == 1) );
                if ( Status == -1 ) // resource limit is reached
                    goto finish;
                if ( vCore != NULL )
                {
                    p->timeUnsat += clock() - clk2;
                    break;
                }
                p->timeSat += clock() - clk2;
                assert( Status == 0 );
                // perform the refinement
                clk2 = clock();
                pCex = Vta_ManRefineAbstraction( p, f );
                p->timeCex += clock() - clk2;
                if ( pCex != NULL )
                    goto finish;
            }
            assert( Status == 1 );
            // valid core is obtained
            Vta_ManUnsatCoreRemap( p, vCore );
            Vec_IntSort( vCore, 1 );
            // update the SAT solver
            sat_solver2_rollback( p->pSat );
            // update storage
            Vga_ManRollBack( p, nObjOld );
            Vec_IntShrink( p->vCla2Var, (int)p->pSat->stats.clauses+1 );
            // load this timeframe
            Vga_ManLoadSlice( p, vCore, 0 );
            Vec_IntFree( vCore );
        }
        // run SAT solver
        clk2 = clock();
        vCore = Vta_ManUnsatCore( Vga_ManGetOutLit(p, f), p->vCla2Var, p->pSat, pPars->nConfLimit, p->pPars->fVerbose, &Status, &nConfls );
        p->timeUnsat += clock() - clk2;
        if ( p->pPars->fVerbose )
            printf( "%6d", nConfls );
        assert( (vCore != NULL) == (Status == 1) );
        if ( Status == -1 ) // resource limit is reached
            break;
        if ( Status == 0 )
        {
            Vta_ManSatVerify( p );
            // make sure, there was no initial abstraction (otherwise, it was invalid)
            assert( pAig->vObjClasses == NULL && f < p->pPars->nFramesStart );
            pCex = Vga_ManDeriveCex( p );
            break;
        }
        // add the core
        Vta_ManUnsatCoreRemap( p, vCore );
        // add in direct topological order
        Vec_IntSort( vCore, 1 );
        Vec_PtrPush( p->vCores, vCore );
        // print the result
        Vta_ManAbsPrintFrame( p, vCore, f+1, i, p->pPars->fVerbose );
    }
finish:
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
            printf( "SAT solver completed %d frames and produced an abstraction.  ", f );
    }
    else
    {
        ABC_FREE( p->pGia->pCexSeq );
        p->pGia->pCexSeq = pCex;
        if ( !Gia_ManVerifyCex( p->pGia, pCex, 0 ) )
            printf( "    Gia_VtaPerform(): CEX verification has failed!\n" );
        printf( "Counter-example detected in frame %d.  ", f );
    }
    Abc_PrintTime( 1, "Time", clock() - clk );

    p->timeOther = (clock() - clk) - p->timeUnsat - p->timeSat - p->timeCex;
    ABC_PRTP( "Solver UNSAT", p->timeUnsat,  clock() - clk );
    ABC_PRTP( "Solver SAT  ", p->timeSat,    clock() - clk );
    ABC_PRTP( "Refinement  ", p->timeCex,    clock() - clk );
    ABC_PRTP( "Other       ", p->timeOther,  clock() - clk );
    ABC_PRTP( "TOTAL       ", clock() - clk, clock() - clk );

    Vga_ManStop( p );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

