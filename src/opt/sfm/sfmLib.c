/**CFile****************************************************************

  FileName    [sfmLib.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Preprocessing genlib library.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmLib.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"
#include "misc/vec/vecMem.h"
#include "misc/util/utilTruth.h"
#include "misc/extra/extra.h"
#include "map/mio/exp.h"
#include "opt/dau/dau.h"
#include "base/main/main.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

struct Sfm_Fun_t_
{
    int             Next;          // next function in the list
    int             Area;          // area of this function
    char            pFansT[8];     // top gate ID, followed by fanin perm
    char            pFansB[8];     // bottom gate ID, followed by fanin perm
};
struct Sfm_Lib_t_
{
    Mio_Cell2_t *   pCells;        // library gates
    int             nCells;        // library gate count
    int             nObjs;         // object count
    int             nObjsAlloc;    // object count
    Sfm_Fun_t *     pObjs;         // objects  
    Vec_Mem_t *     vTtMem;        // truth tables
    Vec_Int_t       vLists;        // lists of funcs for each truth table
    Vec_Int_t       vCounts;       // counters of functions for each truth table
};

static inline Sfm_Fun_t * Sfm_LibFun( Sfm_Lib_t * p, int i ) { return i == -1 ? NULL : p->pObjs + i; }

#define Sfm_LibForEachSuper( p, pObj, Func ) \
    for ( pObj = Sfm_LibFun(p, Vec_IntEntry(&p->vLists, Func)); pObj; pObj = Sfm_LibFun(p, pObj->Next) )


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_DecCreateCnf( Vec_Int_t * vGateSizes, Vec_Wrd_t * vGateFuncs, Vec_Wec_t * vGateCnfs )
{
    Vec_Str_t * vCnf, * vCnfBase;
    Vec_Int_t * vCover;
    word uTruth;
    int i, nCubes;
    vCnf = Vec_StrAlloc( 100 );
    vCover = Vec_IntAlloc( 100 );
    Vec_WrdForEachEntry( vGateFuncs, uTruth, i )
    {
        nCubes = Sfm_TruthToCnf( uTruth, Vec_IntEntry(vGateSizes, i), vCover, vCnf );
        vCnfBase = (Vec_Str_t *)Vec_WecEntry( vGateCnfs, i );
        Vec_StrGrow( vCnfBase, Vec_StrSize(vCnf) );
        memcpy( Vec_StrArray(vCnfBase), Vec_StrArray(vCnf), Vec_StrSize(vCnf) );
        vCnfBase->nSize = Vec_StrSize(vCnf);
    }
    Vec_IntFree( vCover );
    Vec_StrFree( vCnf );
}

/**Function*************************************************************

  Synopsis    [Preprocess the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_LibPreprocess( Mio_Library_t * pLib, Vec_Int_t * vGateSizes, Vec_Wrd_t * vGateFuncs, Vec_Wec_t * vGateCnfs, Vec_Ptr_t * vGateHands )
{
    Mio_Gate_t * pGate;
    int nGates = Mio_LibraryReadGateNum(pLib);
    Vec_IntGrow( vGateSizes, nGates );
    Vec_WrdGrow( vGateFuncs, nGates );
    Vec_WecInit( vGateCnfs,  nGates );
    Vec_PtrGrow( vGateHands, nGates );
    Mio_LibraryForEachGate( pLib, pGate )
    {
        Vec_IntPush( vGateSizes, Mio_GateReadPinNum(pGate) );
        Vec_WrdPush( vGateFuncs, Mio_GateReadTruth(pGate) );
        Mio_GateSetValue( pGate, Vec_PtrSize(vGateHands) );
        Vec_PtrPush( vGateHands, pGate );
    }
    Sfm_DecCreateCnf( vGateSizes, vGateFuncs, vGateCnfs );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_LibFindComplInputGate( Vec_Wrd_t * vFuncs, int iGate, int nFanins, int iFanin, int * piFaninNew )
{
    word uTruthGate = Vec_WrdEntry(vFuncs, iGate);
    word uTruth, uTruthNew = Abc_Tt6Flip( uTruthGate, iFanin ); 
    int i;
    assert( iFanin >= 0 && iFanin < nFanins );
    if ( piFaninNew ) *piFaninNew = iFanin;
    Vec_WrdForEachEntry( vFuncs, uTruth, i )
        if ( uTruth == uTruthNew )
            return i;
    if ( iFanin-1 >= 0 && Abc_Tt6SwapAdjacent(uTruthGate, iFanin-1) == uTruthGate ) // symmetric with prev
    {
        if ( piFaninNew ) *piFaninNew = iFanin-1;
        uTruthNew = Abc_Tt6Flip( uTruthGate, iFanin-1 );
        Vec_WrdForEachEntry( vFuncs, uTruth, i )
            if ( uTruth == uTruthNew )
                return i;
    }
    if ( iFanin+1 < nFanins && Abc_Tt6SwapAdjacent(uTruthGate, iFanin) == uTruthGate ) // symmetric with next
    {
        if ( piFaninNew ) *piFaninNew = iFanin+1;
        uTruthNew = Abc_Tt6Flip( uTruthGate, iFanin+1 );
        Vec_WrdForEachEntry( vFuncs, uTruth, i )
            if ( uTruth == uTruthNew )
                return i;
    }
    if ( piFaninNew ) *piFaninNew = -1;
    return -1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sfm_Lib_t * Sfm_LibStart( int nVars )
{
    Sfm_Lib_t * p = ABC_CALLOC( Sfm_Lib_t, 1 );
    p->vTtMem = Vec_MemAllocForTT( nVars, 0 );   
    Vec_IntGrow( &p->vLists,  (1 << 16) );
    Vec_IntGrow( &p->vCounts, (1 << 16) );
    Vec_IntFill( &p->vLists,  2, -1 );
    Vec_IntFill( &p->vCounts, 2, -1 );
    p->nObjsAlloc = (1 << 16);
    p->pObjs = ABC_CALLOC( Sfm_Fun_t, p->nObjsAlloc );
    return p;
}
void Sfm_LibStop( Sfm_Lib_t * p )
{
    Vec_MemHashFree( p->vTtMem );
    Vec_MemFree( p->vTtMem );
    Vec_IntErase( &p->vLists );
    Vec_IntErase( &p->vCounts );
    ABC_FREE( p->pCells );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Sfm_LibTruthTwo( Mio_Cell2_t * pCellBot, Mio_Cell2_t * pCellTop, int InTop )
{
    word uTruthBot = Exp_Truth6( pCellBot->nFanins, pCellBot->vExpr, NULL );
    word uFanins[6]; int i, k;
    assert( InTop >= 0 && InTop < (int)pCellTop->nFanins );
    for ( i = 0, k = pCellBot->nFanins; i < (int)pCellTop->nFanins; i++ )
        if ( i == InTop )
            uFanins[i] = uTruthBot;
        else
            uFanins[i] = s_Truths6[k++];
    assert( (int)pCellBot->nFanins + (int)pCellTop->nFanins == k + 1 );
    uTruthBot = Exp_Truth6( pCellTop->nFanins, pCellTop->vExpr, uFanins );
    return uTruthBot;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_LibPrepareAdd( Sfm_Lib_t * p, word uTruth, int * Perm, int nFanins, Mio_Cell2_t * pCellBot, Mio_Cell2_t * pCellTop, int InTop )
{
    Sfm_Fun_t * pObj;
    int InvPerm[6], Area = (int)pCellBot->Area + (pCellTop ? (int)pCellTop->Area : 0);
    int i, k, iFunc = Vec_MemHashInsert( p->vTtMem, &uTruth );
    if ( iFunc == Vec_IntSize(&p->vLists) )
    {
        Vec_IntPush( &p->vLists, -1 );
        Vec_IntPush( &p->vCounts, 0 );
    }
    assert( pCellBot != NULL );
    // iterate through the supergates of this truth table
    Sfm_LibForEachSuper( p, pObj, iFunc )
    {
        if ( Area >= pObj->Area )
            return;
    }
    for ( k = 0; k < nFanins; k++ )
        InvPerm[Perm[k]] = k;
    // create new object
    if ( p->nObjs == p->nObjsAlloc )
    {
        int nObjsAlloc = 2 * p->nObjsAlloc;
        p->pObjs = ABC_REALLOC( Sfm_Fun_t, p->pObjs, nObjsAlloc );
        memset( p->pObjs + p->nObjsAlloc, 0, sizeof(Sfm_Fun_t) * p->nObjsAlloc );
        p->nObjsAlloc = nObjsAlloc;
    }
    pObj = p->pObjs + p->nObjs;
    pObj->Area = Area;
    pObj->Next = Vec_IntEntry(&p->vLists, iFunc);
    Vec_IntWriteEntry( &p->vLists, iFunc, p->nObjs++ );
    Vec_IntAddToEntry( &p->vCounts, iFunc, 1 );
    // create gate
    assert( pCellBot->Id < 128 );
    pObj->pFansB[0] = (char)pCellBot->Id;
    for ( k = 0; k < (int)pCellBot->nFanins; k++ )
        pObj->pFansB[k+1] = InvPerm[k];
    if ( pCellTop == NULL )
        return;
    assert( pCellTop->Id < 128 );
    pObj->pFansT[0] = (char)pCellTop->Id;
    for ( i = 0; i < (int)pCellTop->nFanins; i++ )
        pObj->pFansT[i+1] = (char)(i == InTop ? 16 : InvPerm[k++]);
    assert( k == nFanins );
}
Sfm_Lib_t * Sfm_LibPrepare( int nVars, int fTwo, int fVerbose )
{
    abctime clk = Abc_Clock();
    Sfm_Lib_t * p = Sfm_LibStart( nVars );
    Mio_Cell2_t * pCell1, * pCell2, * pLimit;
    int * pPerm[7], * Perm1, * Perm2, Perm[6];
    int nPerms[7], i, f, n;
    Vec_Int_t * vUseful;
    word tTemp1, tCur;
    char pRes[1000];
    assert( nVars <= 6 );
    // precompute gates
    p->pCells = Mio_CollectRootsNewDefault2( nVars, &p->nCells, 0 );
    pLimit = p->pCells + p->nCells;
    // find useful ones
    vUseful = Vec_IntStart( p->nCells );
//    vUseful = Vec_IntStartFull( p->nCells );
    for ( pCell1 = p->pCells + 4; pCell1 < pLimit; pCell1++ )
    {
        word uTruth = pCell1->uTruth;
        if ( Dau_DsdDecompose(&uTruth, pCell1->nFanins, 0, 0, pRes) <= 3 )
            Vec_IntWriteEntry( vUseful, pCell1 - p->pCells, 1 );
        else
            printf( "Skipping gate \"%s\" with non-DSD function %s\n", pCell1->pName, pRes );
    }
    // generate permutations
    for ( i = 2; i <= nVars; i++ )
        pPerm[i] = Extra_PermSchedule( i );
    for ( i = 2; i <= nVars; i++ )
        nPerms[i] = Extra_Factorial( i );
    // add single cells
    for ( pCell1 = p->pCells + 4; pCell1 < pLimit; pCell1++ )
    if ( Vec_IntEntry(vUseful, pCell1 - p->pCells) )
    {
        int nFanins = pCell1->nFanins;
        assert( nFanins >= 2 && nFanins <= 6 );
        for ( i = 0; i < nFanins; i++ )
            Perm[i] = i;
        // permute truth table
        tCur = tTemp1 = pCell1->uTruth;
        for ( n = 0; n < nPerms[nFanins]; n++ )
        {
            Sfm_LibPrepareAdd( p, tCur, Perm, nFanins, pCell1, NULL, -1 );
            // update
            tCur = Abc_Tt6SwapAdjacent( tCur, pPerm[nFanins][n] );
            Perm1 = Perm + pPerm[nFanins][n];
            Perm2 = Perm1 + 1;
            ABC_SWAP( int, *Perm1, *Perm2 );
        }
        assert( tTemp1 == tCur );
    }
    // add double cells
    if ( fTwo )
    for ( pCell1 = p->pCells + 4; pCell1 < pLimit; pCell1++ )
    if ( Vec_IntEntry(vUseful, pCell1 - p->pCells) )
    for ( pCell2 = p->pCells + 4; pCell2 < pLimit; pCell2++ )
    if ( Vec_IntEntry(vUseful, pCell2 - p->pCells) )
    if ( (int)pCell1->nFanins + (int)pCell2->nFanins <= nVars + 1 )
    for ( f = 0; f < (int)pCell2->nFanins; f++ )
    {
        int nFanins = pCell1->nFanins + pCell2->nFanins - 1;
        assert( nFanins >= 2 && nFanins <= nVars );
        for ( i = 0; i < nFanins; i++ )
            Perm[i] = i;
        // permute truth table
        tCur = tTemp1 = Sfm_LibTruthTwo( pCell1, pCell2, f );
        for ( n = 0; n < nPerms[nFanins]; n++ )
        {
            Sfm_LibPrepareAdd( p, tCur, Perm, nFanins, pCell1, pCell2, f );
            // update
            tCur = Abc_Tt6SwapAdjacent( tCur, pPerm[nFanins][n] );
            Perm1 = Perm + pPerm[nFanins][n];
            Perm2 = Perm1 + 1;
            ABC_SWAP( int, *Perm1, *Perm2 );
        }
        assert( tTemp1 == tCur );
    }
    // cleanup
    for ( i = 2; i <= nVars; i++ )
        ABC_FREE( pPerm[i] );
    Vec_IntFree( vUseful );
    if ( fVerbose )
    {
        printf( "Library processing: Var = %d.  Cells = %d.  Func = %6d.  Obj = %8d.  Ave = %8.2f  ", nVars, p->nCells, Vec_MemEntryNum(p->vTtMem), p->nObjs, 1.0*p->nObjs/Vec_MemEntryNum(p->vTtMem) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    return p;
}
void Sfm_LibPrintGate( Mio_Cell2_t * pCell, char * pFanins, Mio_Cell2_t * pCell2, char * pFanins2 )
{
    int k;
    printf( " %s(", pCell->pName );
    for ( k = 0; k < (int)pCell->nFanins; k++ )
        if ( pFanins[k] == (char)16 )
            Sfm_LibPrintGate( pCell2, pFanins2, NULL, NULL );
        else
            printf( " %c", 'a' + pFanins[k] );
    printf( " )" );
}
void Sfm_LibPrintObj( Sfm_Lib_t * p, Sfm_Fun_t * pObj )
{
    Mio_Cell2_t * pCellB = p->pCells + (int)pObj->pFansB[0];
    Mio_Cell2_t * pCellT = p->pCells + (int)pObj->pFansT[0];
    int nFanins = pCellB->nFanins + (pCellT == p->pCells ? 0 : pCellT->nFanins);
    printf( "     Area = %6.2f  Fanins = %d  ", MIO_NUMINV*pObj->Area, nFanins );
    if ( pCellT == p->pCells )
        Sfm_LibPrintGate( pCellB, pObj->pFansB + 1, NULL, NULL );
    else
        Sfm_LibPrintGate( pCellT, pObj->pFansT + 1, pCellB, pObj->pFansB + 1 );
    printf( "\n" );
}
void Sfm_LibPrint( Sfm_Lib_t * p )
{
    word * pTruth; Sfm_Fun_t * pObj; int iFunc; 
    Vec_MemForEachEntry( p->vTtMem, pTruth, iFunc )
    {
        if ( iFunc < 2 ) 
            continue;
        //if ( iFunc % 10000 )
        //    continue;
        printf( "%d : Count = %d   ", iFunc, Vec_IntEntry(&p->vCounts, iFunc) );
        Dau_DsdPrintFromTruth( pTruth, Abc_TtSupportSize(pTruth, 6) );
        Sfm_LibForEachSuper( p, pObj, iFunc )
            Sfm_LibPrintObj( p, pObj );
    }
}
void Sfm_LibTest( int nVars, int fTwo, int fVerbose )
{
    Sfm_Lib_t * p = Sfm_LibPrepare( nVars, fTwo, 1 );
    if ( fVerbose )
        Sfm_LibPrint( p );
    Sfm_LibStop( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_LibImplement( Sfm_Lib_t * p, word uTruth, int * pFanins, int nFanins, int AreaMffc, Vec_Int_t * vGates, Vec_Wec_t * vFanins )
{
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen();
    Mio_Gate_t * pGate;
    Mio_Cell2_t * pCellB, * pCellT;
    Vec_Int_t * vLevel;
    Sfm_Fun_t * pObj, * pObjMin = NULL;
    int i, iFunc;
    if ( uTruth == 0 || uTruth == ~(word)0 )
    {
        assert( nFanins == 0 );
        pGate = uTruth ? Mio_LibraryReadConst1(pLib) : Mio_LibraryReadConst0(pLib);
        Vec_IntPush( vGates, Mio_GateReadValue(pGate) );
        vLevel = Vec_WecPushLevel( vFanins );
        return 1;
    }
    if ( uTruth == s_Truths6[0] || uTruth == ~s_Truths6[0] )
    {
        assert( nFanins == 1 );
        pGate = uTruth == s_Truths6[0] ? Mio_LibraryReadBuf(pLib) : Mio_LibraryReadInv(pLib);
        Vec_IntPush( vGates, Mio_GateReadValue(pGate) );
        vLevel = Vec_WecPushLevel( vFanins );
        Vec_IntPush( vLevel, pFanins[0] );
        return 1;
    }
    // look for gate
    iFunc = *Vec_MemHashLookup( p->vTtMem,  &uTruth );
    if ( iFunc == -1 )
        return -1;
    Sfm_LibForEachSuper( p, pObj, iFunc )
        if ( !pObjMin || pObjMin->Area > pObj->Area )
            pObjMin = pObj;
    if ( pObjMin == NULL || pObjMin->Area >= AreaMffc )
        return -1;
    // get the gates
    pCellB = p->pCells + (int)pObjMin->pFansB[0];
    pCellT = p->pCells + (int)pObjMin->pFansT[0];
    // create bottom gate
    pGate = Mio_LibraryReadGateByName( pLib, pCellB->pName, NULL );
    Vec_IntPush( vGates, Mio_GateReadValue(pGate) );
    vLevel = Vec_WecPushLevel( vFanins );
    for ( i = 0; i < (int)pCellB->nFanins; i++ )
        Vec_IntPush( vLevel, pFanins[(int)pObjMin->pFansB[i+1]] );
    if ( pCellT == p->pCells )
        return 1;
    // create top gate
    pGate = Mio_LibraryReadGateByName( pLib, pCellT->pName, NULL );
    Vec_IntPush( vGates, Mio_GateReadValue(pGate) );
    vLevel = Vec_WecPushLevel( vFanins );
    for ( i = 0; i < (int)pCellT->nFanins; i++ )
        if ( pObjMin->pFansT[i+1] == (char)16 )
            Vec_IntPush( vLevel, Vec_WecSize(vFanins)-2 );
        else
            Vec_IntPush( vLevel, pFanins[(int)pObjMin->pFansT[i+1]] );
    return 2;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

