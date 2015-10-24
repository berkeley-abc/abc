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
    int             fDelay;        // uses delay profile
    int             nObjs;         // object count
    int             nObjsAlloc;    // object count
    Sfm_Fun_t *     pObjs;         // objects  
    Vec_Mem_t *     vTtMem;        // truth tables
    Vec_Int_t       vLists;        // lists of funcs for each truth table
    Vec_Int_t       vCounts;       // counters of functions for each truth table
    Vec_Int_t       vProfs;        // area/delay profiles
    Vec_Int_t       vStore;        // storage for area/delay profiles
    Vec_Int_t       vTemp;         // temporary storage for candidates
    int             nObjSkipped;
    int             nObjRemoved;
};

static inline Sfm_Fun_t * Sfm_LibFun( Sfm_Lib_t * p, int i )              { return i == -1 ? NULL : p->pObjs + i; }
static inline int         Sfm_LibFunId( Sfm_Lib_t * p, Sfm_Fun_t * pFun ) { return pFun - p->pObjs;               }

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
    word uTruthGate = Vec_WrdEntry( vFuncs, iGate );
    word uTruthFlip = Abc_Tt6Flip( uTruthGate, iFanin ); 
    word uTruth, uTruthSwap;  int i;
    assert( iFanin >= 0 && iFanin < nFanins );
    if ( piFaninNew ) *piFaninNew = iFanin;
    Vec_WrdForEachEntry( vFuncs, uTruth, i )
        if ( uTruth == uTruthFlip )
            return i;
    if ( iFanin-1 >= 0 )
    {
        if ( piFaninNew ) *piFaninNew = iFanin-1;
        uTruthSwap = Abc_Tt6SwapAdjacent( uTruthFlip, iFanin-1 );
        Vec_WrdForEachEntry( vFuncs, uTruth, i )
            if ( uTruth == uTruthSwap )
                return i;
    }
    if ( iFanin+1 < nFanins )
    {
        if ( piFaninNew ) *piFaninNew = iFanin+1;
        uTruthSwap = Abc_Tt6SwapAdjacent( uTruthFlip, iFanin );
        Vec_WrdForEachEntry( vFuncs, uTruth, i )
            if ( uTruth == uTruthSwap )
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
Sfm_Lib_t * Sfm_LibStart( int nVars, int fDelay )
{
    Sfm_Lib_t * p = ABC_CALLOC( Sfm_Lib_t, 1 );
    p->vTtMem = Vec_MemAllocForTT( nVars, 0 );   
    Vec_IntGrow( &p->vLists,  (1 << 16) );
    Vec_IntGrow( &p->vCounts, (1 << 16) );
    Vec_IntFill( &p->vLists,  2, -1 );
    Vec_IntFill( &p->vCounts, 2, -1 );
    p->nObjsAlloc = (1 << 16);
    p->pObjs = ABC_CALLOC( Sfm_Fun_t, p->nObjsAlloc );
    p->fDelay = fDelay;
    if ( fDelay ) Vec_IntGrow( &p->vProfs,  (1 << 16) );
    if ( fDelay ) Vec_IntGrow( &p->vStore,  (1 << 18) );
    Vec_IntGrow( &p->vTemp, 16 );
    return p;
}
void Sfm_LibStop( Sfm_Lib_t * p )
{
    Vec_MemHashFree( p->vTtMem );
    Vec_MemFree( p->vTtMem );
    Vec_IntErase( &p->vLists );
    Vec_IntErase( &p->vCounts );
    Vec_IntErase( &p->vProfs );
    Vec_IntErase( &p->vStore );
    Vec_IntErase( &p->vTemp );
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
static inline void Sfm_LibCellProfile( Mio_Cell2_t * pCellBot, Mio_Cell2_t * pCellTop, int InTop, int nFanins, int * Perm, int * pProf )
{
    int i, DelayAdd = (int)(pCellTop ? pCellTop->Delays[InTop] : 0);
    for ( i = 0; i < nFanins; i++ )
        if ( Perm[i] < (int)pCellBot->nFanins )
            pProf[i] = (int)pCellBot->Delays[Perm[i]] + DelayAdd;
        else if ( Perm[i] < (int)pCellBot->nFanins + InTop )
            pProf[i] = (int)pCellTop->Delays[Perm[i] - (int)pCellBot->nFanins];
        else // if ( Perm[i] >= (int)pCellBot->nFanins + InTop )
            pProf[i] = (int)pCellTop->Delays[Perm[i] - (int)pCellBot->nFanins + 1];
}
static inline int Sfm_LibNewIsContained( Sfm_Fun_t * pObj, int * pProf, int Area, int * pProfNew, int nFanins )
{
    int k;
    if ( Area < pObj->Area )
        return 0;
    for ( k = 0; k < nFanins; k++ )
        if ( pProfNew[k] < pProf[k] )
            return 0;
    return 1;
}
static inline int Sfm_LibNewContains( Sfm_Fun_t * pObj, int * pProf, int Area, int * pProfNew, int nFanins )
{
    int k;
    if ( Area > pObj->Area )
        return 0;
    for ( k = 0; k < nFanins; k++ )
        if ( pProfNew[k] > pProf[k] )
            return 0;
    return 1;
}
void Sfm_LibPrepareAdd( Sfm_Lib_t * p, word uTruth, int * Perm, int nFanins, Mio_Cell2_t * pCellBot, Mio_Cell2_t * pCellTop, int InTop )
{
    Sfm_Fun_t * pObj;
    int InvPerm[6], Profile[6];
    int Area = (int)pCellBot->Area + (pCellTop ? (int)pCellTop->Area : 0);
    int i, k, Id, Prev, Offset, * pProf, iFunc = Vec_MemHashInsert( p->vTtMem, &uTruth );
    if ( iFunc == Vec_IntSize(&p->vLists) )
    {
        Vec_IntPush( &p->vLists, -1 );
        Vec_IntPush( &p->vCounts, 0 );
    }
    assert( pCellBot != NULL );
    // iterate through the supergates of this truth table
    if ( p->fDelay )
    {
        assert( Vec_IntSize(&p->vProfs) == p->nObjs );
        Sfm_LibCellProfile( pCellBot, pCellTop, InTop, nFanins, Perm, Profile );
        // check if new one is contained in old ones
        Vec_IntClear( &p->vTemp );
        Sfm_LibForEachSuper( p, pObj, iFunc )
        {
            Vec_IntPush( &p->vTemp, Sfm_LibFunId(p, pObj) );
            Offset = Vec_IntEntry( &p->vProfs, Sfm_LibFunId(p, pObj) );
            pProf  = Vec_IntEntryP( &p->vStore, Offset );
            if ( Sfm_LibNewIsContained(pObj, pProf, Area, Profile, nFanins) )
            {
                p->nObjSkipped++;
                return;
            }
        }
        // check if old ones are contained in new one
        k = 0;
        Vec_IntForEachEntry( &p->vTemp, Id, i )
        {
            Offset = Vec_IntEntry( &p->vProfs, Id );
            pProf  = Vec_IntEntryP( &p->vStore, Offset );
            if ( !Sfm_LibNewContains(Sfm_LibFun(p, Id), pProf, Area, Profile, nFanins) )
                Vec_IntWriteEntry( &p->vTemp, k++, Id );
            else
                p->nObjRemoved++;
        }
        if ( k < i ) // change
        {
            if ( k == 0 )
                Vec_IntWriteEntry( &p->vLists, iFunc, -1 );
            else
            {
                Vec_IntShrink( &p->vTemp, k );
                Prev = Vec_IntEntry(&p->vTemp, 0);
                Vec_IntWriteEntry( &p->vLists, iFunc, Prev );
                Vec_IntForEachEntryStart( &p->vTemp, Id, i, 1 )
                {
                    Sfm_LibFun(p, Prev)->Next = Id;
                    Prev = Id;
                }
                Sfm_LibFun(p, Prev)->Next = -1;
            }
        }
    }
    else
    {
        Sfm_LibForEachSuper( p, pObj, iFunc )
        {
            if ( Area >= pObj->Area )
                return;
        }
    }
    for ( k = 0; k < nFanins; k++ )
        InvPerm[Perm[k]] = k;
    // create delay profile
    if ( p->fDelay )
    {
        Vec_IntPush( &p->vProfs, Vec_IntSize(&p->vStore) );
        for ( k = 0; k < nFanins; k++ )
            Vec_IntPush( &p->vStore, Profile[k] );
    }
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
Sfm_Lib_t * Sfm_LibPrepare( int nVars, int fTwo, int fDelay, int fVerbose )
{
    abctime clk = Abc_Clock();
    Sfm_Lib_t * p = Sfm_LibStart( nVars, fDelay );
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
        printf( "Library processing: Var = %d. Cell = %d.  Fun = %d. Obj = %d. Ave = %.2f.  Skip = %d. Rem = %d.  ", 
            nVars, p->nCells, Vec_MemEntryNum(p->vTtMem)-2, 
            p->nObjs-p->nObjRemoved, 1.0*(p->nObjs-p->nObjRemoved)/(Vec_MemEntryNum(p->vTtMem)-2), 
            p->nObjSkipped, p->nObjRemoved );
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
    int i, nFanins = pCellB->nFanins + (pCellT == p->pCells ? 0 : pCellT->nFanins - 1);
    printf( "     Area = %6.2f  Fanins = %d  ", MIO_NUMINV*pObj->Area, nFanins );
    if ( pCellT == p->pCells )
        Sfm_LibPrintGate( pCellB, pObj->pFansB + 1, NULL, NULL );
    else
        Sfm_LibPrintGate( pCellT, pObj->pFansT + 1, pCellB, pObj->pFansB + 1 );
    // get hold of delay info
    if ( p->fDelay )
    {
        int Offset  = Vec_IntEntry( &p->vProfs, Sfm_LibFunId(p, pObj) );
        int * pProf = Vec_IntEntryP( &p->vStore, Offset );
        for ( i = 0; i < nFanins; i++ )
            printf( "%6.2f ", MIO_NUMINV*pProf[i] );
    }
    printf( "\n" );
}
void Sfm_LibPrint( Sfm_Lib_t * p )
{
    word * pTruth; Sfm_Fun_t * pObj; int iFunc, nSupp; 
    Vec_MemForEachEntry( p->vTtMem, pTruth, iFunc )
    {
        if ( iFunc < 2 ) 
            continue;
        nSupp = Abc_TtSupportSize(pTruth, 6);
        if ( nSupp > 3 )
            continue;        
        //if ( iFunc % 10000 )
        //    continue;
        printf( "%d : Count = %d   ", iFunc, Vec_IntEntry(&p->vCounts, iFunc) );
        Dau_DsdPrintFromTruth( pTruth, nSupp );
        Sfm_LibForEachSuper( p, pObj, iFunc )
            Sfm_LibPrintObj( p, pObj );
    }
}
void Sfm_LibTest()
{
    Sfm_Lib_t * p;
    int fVerbose = 1;
    if ( Abc_FrameReadLibGen() == NULL )
    {
        printf( "There is no current library.\n" );
        return;
    }
    p = Sfm_LibPrepare( 6, 1, 1, fVerbose );
    //if ( fVerbose )
    //    Sfm_LibPrint( p );
    Sfm_LibStop( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_LibFindMatches( Sfm_Lib_t * p, word uTruth, int * pFanins, int nFanins, Vec_Ptr_t * vGates, Vec_Ptr_t * vFans )
{
    Mio_Cell2_t * pCellB, * pCellT;
    Sfm_Fun_t * pObj;
    int iFunc;
    Vec_PtrClear( vGates );
    Vec_PtrClear( vFans );
    // look for gate
    assert( uTruth != 0 && uTruth != ~(word)0 && uTruth != s_Truths6[0] && uTruth != ~s_Truths6[0] );
    iFunc = *Vec_MemHashLookup( p->vTtMem,  &uTruth );
    if ( iFunc == -1 )
        return 0;
    // collect matches
    Sfm_LibForEachSuper( p, pObj, iFunc )
    {
        pCellB = p->pCells + (int)pObj->pFansB[0];
        pCellT = p->pCells + (int)pObj->pFansT[0];
        Vec_PtrPush( vGates, pCellB->pMioGate );
        Vec_PtrPush( vGates, pCellT == p->pCells ? NULL : pCellT->pMioGate );
        Vec_PtrPush( vFans, pObj->pFansB + 1 );
        Vec_PtrPush( vFans, pCellT == p->pCells ? NULL : pObj->pFansT + 1 );
    }
    return Vec_PtrSize(vGates) / 2;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_LibAddNewGates( Sfm_Lib_t * p, int * pFanins, Mio_Gate_t * pGateB, Mio_Gate_t * pGateT, char * pFansB, char * pFansT, Vec_Int_t * vGates, Vec_Wec_t * vFanins )
{
    Vec_Int_t * vLevel;
    int i, nFanins;
    // create bottom gate
    Vec_IntPush( vGates, Mio_GateReadValue(pGateB) );
    vLevel  = Vec_WecPushLevel( vFanins );
    nFanins = Mio_GateReadPinNum( pGateB );
    for ( i = 0; i < nFanins; i++ )
        Vec_IntPush( vLevel, pFanins[(int)pFansB[i]] );
    if ( pGateT == NULL )
        return 1;
    // create top gate
    Vec_IntPush( vGates, Mio_GateReadValue(pGateT) );
    vLevel  = Vec_WecPushLevel( vFanins );
    nFanins = Mio_GateReadPinNum( pGateT );
    for ( i = 0; i < nFanins; i++ )
        if ( pFansT[i] == (char)16 )
            Vec_IntPush( vLevel, Vec_WecSize(vFanins)-2 );
        else
            Vec_IntPush( vLevel, pFanins[(int)pFansT[i]] );
    return 2;
}
int Sfm_LibImplement( Sfm_Lib_t * p, word uTruth, int * pFanins, int nFanins, int AreaMffc, Vec_Int_t * vGates, Vec_Wec_t * vFanins, int fZeroCost )
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
    if ( pObjMin == NULL || (fZeroCost ? pObjMin->Area > AreaMffc : pObjMin->Area >= AreaMffc) )
        return -1;
    // get the gates
    pCellB = p->pCells + (int)pObjMin->pFansB[0];
    pCellT = p->pCells + (int)pObjMin->pFansT[0];
    // create bottom gate
    pGate = Mio_LibraryReadGateByName( pLib, pCellB->pName, NULL );
    assert( pGate == pCellB->pMioGate );
    Vec_IntPush( vGates, Mio_GateReadValue(pGate) );
    vLevel = Vec_WecPushLevel( vFanins );
    for ( i = 0; i < (int)pCellB->nFanins; i++ )
        Vec_IntPush( vLevel, pFanins[(int)pObjMin->pFansB[i+1]] );
    if ( pCellT == p->pCells )
        return 1;
    // create top gate
    pGate = Mio_LibraryReadGateByName( pLib, pCellT->pName, NULL );
    assert( pGate == pCellT->pMioGate );
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

