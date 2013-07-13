/**CFile****************************************************************

  FileName    [mpmMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Configurable technology mapper.]

  Synopsis    [Mapping algorithm.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 1, 2013.]

  Revision    [$Id: mpmMap.c,v 1.00 2013/06/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mpmInt.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/*
        // check special cases
        if ( fUseFunc )
        {
            pCut0 = p->pCuts[0][0];  pCut1 = p->pCuts[1][0];
            if ( pCut0->iFunc < 2 || pCut1->iFunc < 2 )
            {
                assert( Mig_ObjIsAnd(pObj) );
                if (  Abc_LitNotCond(pCut0->iFunc, Mig_ObjFaninC0(pObj)) == 0 ||
                      Abc_LitNotCond(pCut1->iFunc, Mig_ObjFaninC1(pObj)) == 0 ) // set the resulting cut to 0
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCreateZero( p, pObj );
                else if ( Abc_LitNotCond(pCut0->iFunc, Mig_ObjFaninC0(pObj)) == 1 ) // set the resulting set to be that of Fanin1
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCopySet( p, Mig_ObjFanin1(pObj), 0 );
                else if ( Abc_LitNotCond(pCut1->iFunc, Mig_ObjFaninC1(pObj)) == 1 ) // set the resulting set to be that of Fanin0
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCopySet( p, Mig_ObjFanin0(pObj), 0 );
                else assert( 0 );
                goto finish;
            }
        }
            // compute cut function
            if ( fUseFunc )
            {
                extern int Mpm_FuncCompute( void * p, int iDsd0, int iDsd1, Vec_Str_t * vShared, int * pPerm, int * pnLeaves );
                int nLeavesOld = p->pCutTemp->nLeaves;
                int nLeaves    = p->pCutTemp->nLeaves;
                iDsd0 = Abc_LitNotCond( pCut0->iFunc, Mig_ObjFaninC0(pObj) );
                iDsd1 = Abc_LitNotCond( pCut1->iFunc, Mig_ObjFaninC1(pObj) );
                if ( iDsd0 > iDsd1 )
                {
                    ABC_SWAP( int, iDsd0, iDsd1 );
                    ABC_SWAP( Mpm_Cut_t *, pCut0, pCut1 );
                }
                // compute functionality and filter cuts dominated by support-reduced cuts
                p->pCutTemp->iFunc = Mpm_FuncCompute( p->pManDsd, iDsd0, iDsd1, &p->vObjShared, p->pPerm, &nLeaves );
                Mpm_ObjUpdateCut( p->pCutTemp, p->pPerm, nLeaves );
                // consider filtering based on functionality
                if ( nLeaves == 0 ) // derived const cut
                {
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCreateZero( p, pObj );
                    goto finish;
                }
                if ( nLeaves == 1 ) // derived unit cut
                {
                    pFanin = Mig_ManObj( p->pMig, Abc_Lit2Var(p->pCutTemp->pLeaves[0]) );
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCopySet( p, pFanin, Abc_LitIsCompl(p->pCutTemp->pLeaves[0]) );
                    goto finish;
                }
                if ( nLeaves < nLeavesOld ) // reduced support of the cut
                {
                    ArrTime = Mpm_CutGetArrTime( p, p->pCutTemp );
                    if ( ArrTime > pMapObj->mRequired )
                        continue;
                }
            }
*/


/**Function*************************************************************

  Synopsis    [Cut manipulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Mpm_CutAlloc( Mpm_Man_t * p, int nLeaves, Mpm_Cut_t ** ppCut )  
{ 
    int hHandle = Mmr_StepFetch( p->pManCuts, Mpm_CutWordNum(nLeaves) );
    *ppCut      = (Mpm_Cut_t *)Mmr_StepEntry( p->pManCuts, hHandle );
    (*ppCut)->nLeaves  = nLeaves;
    (*ppCut)->hNext    = 0;
    (*ppCut)->fUseless = 0;
    (*ppCut)->fCompl   = 0;
    return hHandle;
}
static inline int Mpm_CutCreateZero( Mpm_Man_t * p )  
{ 
    Mpm_Cut_t * pCut;
    int hCut = Mpm_CutAlloc( p, 0, &pCut );
    pCut->iFunc      = 0; // const0
    return hCut;
}
static inline int Mpm_CutCreateUnit( Mpm_Man_t * p, int Id )  
{ 
    Mpm_Cut_t * pCut;
    int hCut = Mpm_CutAlloc( p, 1, &pCut );
    pCut->iFunc      = Abc_Var2Lit( p->funcVar0, 0 ); // var
    pCut->pLeaves[0] = Abc_Var2Lit( Id, 0 );
    return hCut;
}
static inline int Mpm_CutCreate( Mpm_Man_t * p, Mpm_Cut_t * pUni, Mpm_Cut_t ** ppCut )  
{ 
    int hCutNew = Mpm_CutAlloc( p, pUni->nLeaves, ppCut );
    (*ppCut)->iFunc    = pUni->iFunc;
    (*ppCut)->fCompl   = pUni->fCompl;
    (*ppCut)->fUseless = pUni->fUseless;
    (*ppCut)->nLeaves  = pUni->nLeaves;
    memcpy( (*ppCut)->pLeaves, pUni->pLeaves, sizeof(int) * pUni->nLeaves );
    return hCutNew;
}
static inline int Mpm_CutDup( Mpm_Man_t * p, Mpm_Cut_t * pCut, int fCompl )  
{ 
    Mpm_Cut_t * pCutNew;
    int hCutNew = Mpm_CutAlloc( p, pCut->nLeaves, &pCutNew );
    pCutNew->iFunc    = Abc_LitNotCond( pCut->iFunc, fCompl );
    pCutNew->fUseless = pCut->fUseless;
    pCutNew->nLeaves  = pCut->nLeaves;
    memcpy( pCutNew->pLeaves, pCut->pLeaves, sizeof(int) * pCut->nLeaves );
    return hCutNew;
}
static inline int Mpm_CutCopySet( Mpm_Man_t * p, Mig_Obj_t * pObj, int fCompl )  
{
    Mpm_Cut_t * pCut;
    int hCut, iList = 0, * pList = &iList;
    Mpm_ObjForEachCut( p, pObj, hCut, pCut )
    {
        *pList = Mpm_CutDup( p, pCut, fCompl );
        pList = &Mpm_CutFetch( p, *pList )->hNext;
    }
    *pList = 0;
    return iList;
}
/*
static inline void Mpm_CutRef( Mpm_Man_t * p, int * pLeaves, int nLeaves )  
{
    int i;
    for ( i = 0; i < nLeaves; i++ )
        Mig_ManObj( p->pMig, Abc_Lit2Var(pLeaves[i]) )->nMapRefs++;
}
static inline void Mpm_CutDeref( Mpm_Man_t * p, int * pLeaves, int nLeaves )  
{
    int i;
    for ( i = 0; i < nLeaves; i++ )
        Mig_ManObj( p->pMig, Abc_Lit2Var(pLeaves[i]) )->nMapRefs--;
}
*/
static inline void Mpm_CutPrint( Mpm_Cut_t * pCut )  
{ 
    int i;
    printf( "%d : { ", pCut->nLeaves );
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        printf( "%d ", pCut->pLeaves[i] );
    printf( "}\n" );
}
static inline void Mpm_CutPrintAll( Mpm_Man_t * p )  
{ 
    int i;
    for ( i = 0; i < p->nCutStore; i++ )
    {
        printf( "%2d : ", i );
        Mpm_CutPrint( &p->pCutStore[i]->pCut );
    }
}
static inline int Mpm_ManSetIsSmaller( Mpm_Man_t * p, Mpm_Cut_t * pCut, int nTotal ) // check if pCut is contained in the current one (p->pCutTemp)
{
    int i, Index;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
    {
        Index = (int)p->pObjPres[Abc_Lit2Var(pCut->pLeaves[i])];
        if ( Index == 0xFF )
            return 0;
//        assert( Index < nTotal );
    }
    return 1;
}
static inline int Mpm_ManSetIsBigger( Mpm_Man_t * p, Mpm_Cut_t * pCut, int nTotal ) // check if pCut contains the current one (p->pCutTemp)
{
    int i, Index, Counter = 0;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
    {
        Index = (int)p->pObjPres[Abc_Lit2Var(pCut->pLeaves[i])];
        if ( Index == 0xFF )
            continue;
//        assert( Index < nTotal );
        Counter++;
    }
    return (int)(Counter == nTotal);
}

/**Function*************************************************************

  Synopsis    [Cut attibutes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Mpm_CutGetSign( Mpm_Cut_t * pCut )  
{
    int i, iLeaf;
    word uSign = 0;
    Mpm_CutForEachLeafId( pCut, iLeaf, i )
        uSign |= ((word)1 << (iLeaf & 0x3F));
    return uSign;
}
static inline int Mpm_CutGetArrTime( Mpm_Man_t * p, Mpm_Cut_t * pCut )  
{
    int * pmTimes = Vec_IntArray( &p->vTimes );
    int * pDelays = p->pLibLut->pLutDelays[pCut->nLeaves];
    int i, iLeaf, ArrTime = 0;
    Mpm_CutForEachLeafId( pCut, iLeaf, i )
        ArrTime = Abc_MaxInt( ArrTime, pmTimes[iLeaf] + pDelays[i] );
    return ArrTime;
}
static inline Mpm_Uni_t * Mpm_CutSetupInfo( Mpm_Man_t * p, Mpm_Cut_t * pCut, int ArrTime )  
{
    int * pMigRefs = Vec_IntArray( &p->vMigRefs );
    int * pMapRefs = Vec_IntArray( &p->vMapRefs );
    int * pEstRefs = Vec_IntArray( &p->vEstRefs );
    int * pmArea   = Vec_IntArray( &p->vAreas );
    int * pmEdge   = Vec_IntArray( &p->vEdges );
    int i, iLeaf;

    Mpm_Uni_t * pUnit = (Mpm_Uni_t *)Vec_PtrEntryLast(&p->vFreeUnits);
    if ( &pUnit->pCut != pCut )
    {
        pUnit->pCut.iFunc   = pCut->iFunc;
        pUnit->pCut.fCompl  = pCut->fCompl;
        pUnit->pCut.fUseless= pCut->fUseless;
        pUnit->pCut.nLeaves = pCut->nLeaves;
        memcpy( pUnit->pCut.pLeaves, pCut->pLeaves, sizeof(int) * pCut->nLeaves );
    }

    pUnit->mTime    = ArrTime;
    pUnit->mArea    = p->pLibLut->pLutAreas[pCut->nLeaves];
    pUnit->mEdge    = MPM_UNIT_EDGE * pCut->nLeaves;
    pUnit->mAveRefs = 0;
    pUnit->Cost     = 0;
    pUnit->uSign    = 0;
    Mpm_CutForEachLeafId( pCut, iLeaf, i )
    {
        if ( p->fMainRun && pMapRefs[iLeaf] == 0 ) // not used in the mapping
        {
            pUnit->mArea += pmArea[iLeaf];
            pUnit->mEdge += pmEdge[iLeaf];
        }
        else
        {
            assert( pEstRefs[iLeaf] > 0 );
            pUnit->mArea += MPM_UNIT_REFS * pmArea[iLeaf] / pEstRefs[iLeaf];
            pUnit->mEdge += MPM_UNIT_REFS * pmEdge[iLeaf] / pEstRefs[iLeaf];
            pUnit->mAveRefs += p->fMainRun ? pMapRefs[iLeaf] : pMigRefs[iLeaf];
        }
        pUnit->uSign |= ((word)1 << (iLeaf & 0x3F));
    }
    pUnit->mAveRefs = pUnit->mAveRefs * MPM_UNIT_EDGE / Abc_MaxInt(pCut->nLeaves, 1);
    return pUnit;
}

/**Function*************************************************************

  Synopsis    [Cut translation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// compares cut against those present in the store
int Mpm_ObjAddCutToStore( Mpm_Man_t * p, Mpm_Cut_t * pCut, int ArrTime )
{
    int fEnableContainment = 1;
    Mpm_Uni_t * pUnit, * pUnitNew;
    int k, iPivot, last;
    // create new unit
#ifdef MIG_RUNTIME
    abctime clk;
clk = Abc_Clock();
#endif
    pUnitNew = Mpm_CutSetupInfo( p, pCut, ArrTime );
#ifdef MIG_RUNTIME
p->timeEval += Abc_Clock() - clk;
#endif
    // special case when the cut store is empty
    if ( p->nCutStore == 0 )
    {
        p->pCutStore[p->nCutStore++] = pUnitNew;
        Vec_PtrPop( &p->vFreeUnits );
        return 1;
    }
    // special case when the cut store is full and last cut is better than new cut
    if ( p->nCutStore == p->nNumCuts-1 && p->pCutCmp(pUnitNew, p->pCutStore[p->nCutStore-1]) > 0 )
        return 0;

    // find place of the given cut in the store
    assert( p->nCutStore <= p->nNumCuts );
    for ( iPivot = p->nCutStore - 1; iPivot >= 0; iPivot-- )
        if ( p->pCutCmp(pUnitNew, p->pCutStore[iPivot]) > 0 ) // iPivot-th cut is better than new cut
            break;

    if ( fEnableContainment )
    {
#ifdef MIG_RUNTIME
clk = Abc_Clock();
#endif
        // filter this cut using other cuts
        for ( k = 0; k <= iPivot; k++ )
        {
            pUnit = p->pCutStore[k];
            if ( pUnitNew->pCut.nLeaves >= pUnit->pCut.nLeaves && 
                (pUnitNew->uSign & pUnit->uSign) == pUnit->uSign && 
                 Mpm_ManSetIsSmaller(p, &pUnit->pCut, pUnitNew->pCut.nLeaves) )
            {
#ifdef MIG_RUNTIME
p->timeCompare += Abc_Clock() - clk;
#endif
                return 0;
            }
        }
    }

    // special case when the best cut is useless while the new cut is not
    if ( p->pCutStore[0]->pCut.fUseless && !pUnitNew->pCut.fUseless )
        iPivot = -1;

    // add the cut to storage
    assert( pUnitNew == (Mpm_Uni_t *)Vec_PtrEntryLast(&p->vFreeUnits) );
    Vec_PtrPop( &p->vFreeUnits );

    // insert this cut at location iPivot
    iPivot++;
    for ( k = p->nCutStore++; k > iPivot; k-- )
        p->pCutStore[k] = p->pCutStore[k-1];
    p->pCutStore[iPivot] = pUnitNew;

    if ( fEnableContainment )
    {
        // filter other cuts using this cut
        for ( k = last = iPivot+1; k < p->nCutStore; k++ )
        {
            pUnit = p->pCutStore[k];
            if ( pUnitNew->pCut.nLeaves <= pUnit->pCut.nLeaves && 
                (pUnitNew->uSign & pUnit->uSign) == pUnitNew->uSign && 
                 Mpm_ManSetIsBigger(p, &pUnit->pCut, pUnitNew->pCut.nLeaves) )
            {
                Vec_PtrPush( &p->vFreeUnits, pUnit );
                continue;
            }
            p->pCutStore[last++] = p->pCutStore[k];
        }
        p->nCutStore = last;
#ifdef MIG_RUNTIME
p->timeCompare += Abc_Clock() - clk;
#endif
    }

    // remove the last cut if too many
    if ( p->nCutStore == p->nNumCuts )
        Vec_PtrPush( &p->vFreeUnits, p->pCutStore[--p->nCutStore] );
    assert( p->nCutStore < p->nNumCuts );
    return 1;
}
// create storage from cuts at the node
void Mpm_ObjAddChoiceCutsToStore( Mpm_Man_t * p, Mig_Obj_t * pObj, int ReqTime )
{
    Mpm_Cut_t * pCut;
    int hCut, hNext, ArrTime;
    assert( p->nCutStore == 0 );
    assert( Vec_PtrSize(&p->vFreeUnits) == p->nNumCuts + 1 );
    Mpm_ObjForEachCutSafe( p, pObj, hCut, pCut, hNext )
    {
        ArrTime = Mpm_CutGetArrTime( p, pCut );
        if ( ArrTime > ReqTime )
            continue;
        Mpm_ObjAddCutToStore( p, pCut, ArrTime );
        Mmr_StepRecycle( p->pManCuts, hCut );
    }
}
// create cuts at the node from storage
void Mpm_ObjTranslateCutsFromStore( Mpm_Man_t * p, Mig_Obj_t * pObj, int fAddUnit )
{
    Mpm_Cut_t * pCut = NULL;
    Mpm_Uni_t * pUnit;
    int i, *pList = Mpm_ObjCutListP( p, pObj );
    assert( p->nCutStore > 0 && p->nCutStore <= p->nNumCuts );
    assert( *pList == 0 );
    // translate cuts
    for ( i = 0; i < p->nCutStore; i++ )
    {
        pUnit  = p->pCutStore[i];
        *pList = Mpm_CutCreate( p, &pUnit->pCut, &pCut );
        pList  = &pCut->hNext;
        Vec_PtrPush( &p->vFreeUnits, pUnit );
    }
    if ( p->nCutStore == 1 && pCut->nLeaves < 2 )
        fAddUnit = 0;
    *pList = fAddUnit ? Mpm_CutCreateUnit( p, Mig_ObjId(pObj) ) : 0;
    assert( Vec_PtrSize(&p->vFreeUnits) == p->nNumCuts + 1 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Mpm_ObjUpdateCut( Mpm_Cut_t * pCut, int * pPerm, int nLeaves )
{
    int i;
    assert( nLeaves <= (int)pCut->nLeaves );
    for ( i = 0; i < nLeaves; i++ )
        pPerm[i] = Abc_LitNotCond( pCut->pLeaves[Abc_Lit2Var(pPerm[i])], Abc_LitIsCompl(pPerm[i]) );
    memcpy( pCut->pLeaves, pPerm, sizeof(int) * nLeaves );
    pCut->nLeaves = nLeaves;
}
static inline void Mpm_ObjRecycleCuts( Mpm_Man_t * p, Mig_Obj_t * pObj )
{
    Mpm_Cut_t * pCut;
    int hCut, hNext;
    Mpm_ObjForEachCutSafe( p, pObj, hCut, pCut, hNext )
        Mmr_StepRecycle( p->pManCuts, hCut );
    Mpm_ObjSetCutList( p, pObj, 0 );
}
static inline void Mpm_ObjDerefFaninCuts( Mpm_Man_t * p, Mig_Obj_t * pObj )
{
    Mig_Obj_t * pFanin;
    int i;
    Mig_ObjForEachFanin( pObj, pFanin, i )
        if ( Mig_ObjIsNode(pFanin) && Mig_ObjMigRefDec(p, pFanin) == 0 )
            Mpm_ObjRecycleCuts( p, pFanin );
    if ( Mig_ObjSiblId(pObj) )
        Mpm_ObjRecycleCuts( p, Mig_ObjSibl(pObj) );
    if ( Mig_ObjMigRefNum(p, pObj) == 0 )
        Mpm_ObjRecycleCuts( p, pObj );
}
static inline void Mpm_ObjCollectFaninsAndSigns( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )
{
    Mpm_Cut_t * pCut;
    int hCut, nCuts = 0;
    Mpm_ObjForEachCut( p, pObj, hCut, pCut )
    {
        p->pCuts[i][nCuts] = pCut;
        p->pSigns[i][nCuts++] = Mpm_CutGetSign( pCut );
    }
    p->nCuts[i] = nCuts;
}
static inline void Mpm_ObjPrepareFanins( Mpm_Man_t * p, Mig_Obj_t * pObj )
{
    Mig_Obj_t * pFanin;
    int i;
    Mig_ObjForEachFanin( pObj, pFanin, i )
        Mpm_ObjCollectFaninsAndSigns( p, pFanin, i );
}

/**Function*************************************************************

  Synopsis    [Cut enumeration.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Mpm_ObjDeriveCut( Mpm_Man_t * p, Mpm_Cut_t ** pCuts, Mpm_Cut_t * pCut )
{
    int i, c, iObj;
    // clean present objects
//    Vec_IntForEachEntry( &p->vObjPresUsed, iObj, i )
//        p->pObjPres[iObj] = (unsigned char)0xFF; 
    for ( i = 0; i < p->vObjPresUsed.nSize; i++ )
        p->pObjPres[p->vObjPresUsed.pArray[i]] = (unsigned char)0xFF;
    Vec_IntClear(&p->vObjPresUsed);   
    Vec_StrClear(&p->vObjShared);   
    // check present objects
//    for ( i = 0; i < Mig_ManObjNum(p->pMig); i++ )
//        assert( p->pObjPres[i] == (unsigned char)0xFF );
    // base cut
    pCut->nLeaves = 0;
    for ( i = 0; i < (int)pCuts[0]->nLeaves; i++ )
    {
        iObj = Abc_Lit2Var(pCuts[0]->pLeaves[i]);
        Vec_IntPush( &p->vObjPresUsed, iObj );
        p->pObjPres[iObj] = pCut->nLeaves;        
        pCut->pLeaves[pCut->nLeaves++] = pCuts[0]->pLeaves[i];
    }
    // remaining cuts
    for ( c = 1; pCuts[c] && c < 3; c++ )
    {
        for ( i = 0; i < (int)pCuts[c]->nLeaves; i++ )
        {
            iObj = Abc_Lit2Var(pCuts[c]->pLeaves[i]);
            if ( p->pObjPres[iObj] != (unsigned char)0xFF )
                continue;
            if ( (int)pCut->nLeaves == p->nLutSize )
                return 0;
            Vec_IntPush( &p->vObjPresUsed, iObj );
            p->pObjPres[iObj] = pCut->nLeaves;        
            pCut->pLeaves[pCut->nLeaves++] = pCuts[c]->pLeaves[i];
        }
    }
    pCut->hNext    = 0;
    pCut->iFunc    = 0;  pCut->iFunc = ~pCut->iFunc;
    pCut->fUseless = 0;
    pCut->fCompl   = 0;
    assert( pCut->nLeaves > 0 );
    p->nCutsMerged++;
    if ( p->pPars->fUseTruth )
        Vec_IntSelectSort( pCut->pLeaves, pCut->nLeaves );
    return 1;
}

static inline int Mpm_ManDeriveCutNew( Mpm_Man_t * p, Mig_Obj_t * pObj, Mpm_Cut_t ** pCuts, int Required )
{
    Mpm_Uni_t * pUnit = (Mpm_Uni_t *)Vec_PtrEntryLast( &p->vFreeUnits );
    Mpm_Cut_t * pCut = &pUnit->pCut;
    int ArrTime;
#ifdef MIG_RUNTIME
abctime clk = clock();
#endif

    if ( !Mpm_ObjDeriveCut( p, pCuts, pCut ) )
    {
#ifdef MIG_RUNTIME
p->timeMerge += clock() - clk;
#endif
        return 1;
    }

    // derive truth table
    if ( p->pPars->fUseTruth )
        Mpm_CutComputeTruth6( p, pCut, pCuts[0], pCuts[1], pCuts[2], Mig_ObjFaninC0(pObj), Mig_ObjFaninC1(pObj), Mig_ObjFaninC2(pObj), Mig_ObjNodeType(pObj) ); 

#ifdef MIG_RUNTIME
p->timeMerge += clock() - clk;
clk = clock();
#endif
    ArrTime = Mpm_CutGetArrTime( p, pCut );
#ifdef MIG_RUNTIME
p->timeEval += clock() - clk;
#endif

    if ( p->fMainRun && ArrTime > Required )
        return 1;

#ifdef MIG_RUNTIME
clk = Abc_Clock();
#endif
    Mpm_ObjAddCutToStore( p, pCut, ArrTime );
#ifdef MIG_RUNTIME
p->timeStore += Abc_Clock() - clk;
#endif

    return 1;
    // return 0 if const or buffer cut is derived - reset all cuts to contain only one
}
int Mpm_ManDeriveCuts( Mpm_Man_t * p, Mig_Obj_t * pObj )
{
//    static int Flag = 0;
    Mpm_Cut_t * pCuts[3];
    int Required = Mpm_ObjRequired( p, pObj );
    int hCutBest = Mpm_ObjCutBest( p, pObj );
    int c0, c1, c2;
    p->nCutStore = 0;

#ifdef MIG_RUNTIME
    abctime clk;
#endif
    assert( Vec_PtrSize( &p->vFreeUnits ) == p->nNumCuts + 1 );
    assert( Mpm_ObjCutList(p, pObj) == 0 );
    if ( hCutBest > 0 ) // cut list is assigned
    {
        Mpm_Cut_t * pCut = Mpm_ObjCutBestP( p, pObj ); 
        int Times = Mpm_CutGetArrTime( p, pCut );
        assert( pCut->hNext == 0 );
        if ( Times > Required )
            printf( "Arrival time (%d) exceeds required time (%d) at object %d.\n", Times, Required, Mig_ObjId(pObj) );
        if ( p->fMainRun )
            Mpm_ObjAddCutToStore( p, pCut, Times );
        else
            Mpm_ObjSetTime( p, pObj, Times );
    }
    // start storage with choice cuts
    if ( p->pMig->vSibls.nSize && Mig_ObjSiblId(pObj) )
        Mpm_ObjAddChoiceCutsToStore( p, Mig_ObjSibl(pObj), Required );
    // compute signatures for fanin cuts
#ifdef MIG_RUNTIME
clk = Abc_Clock();
#endif
    Mpm_ObjPrepareFanins( p, pObj );
#ifdef MIG_RUNTIME
p->timeFanin += Abc_Clock() - clk;
#endif
    // compute cuts in the internal storage
#ifdef MIG_RUNTIME
clk = Abc_Clock();
#endif
    if ( Mig_ObjIsNode2(pObj) )
    {
        // go through cut pairs
        pCuts[2] = NULL;
        for ( c0 = 0; c0 < p->nCuts[0] && (pCuts[0] = p->pCuts[0][c0]); c0++ )
        for ( c1 = 0; c1 < p->nCuts[1] && (pCuts[1] = p->pCuts[1][c1]); c1++ )
            if ( Abc_TtCountOnes(p->pSigns[0][c0] | p->pSigns[1][c1]) <= p->nLutSize )
                if ( !Mpm_ManDeriveCutNew( p, pObj, pCuts, Required ) )
                    goto finish;
    }
    else if ( Mig_ObjIsNode3(pObj) )
    {
        // go through cut triples
        for ( c0 = 0; c0 < p->nCuts[0] && (pCuts[0] = p->pCuts[0][c0]); c0++ )
        for ( c1 = 0; c1 < p->nCuts[1] && (pCuts[1] = p->pCuts[1][c1]); c1++ )
        for ( c2 = 0; c2 < p->nCuts[2] && (pCuts[2] = p->pCuts[2][c2]); c2++ )
            if ( Abc_TtCountOnes(p->pSigns[0][c0] | p->pSigns[1][c1] | p->pSigns[2][c2]) <= p->nLutSize )
                if ( !Mpm_ManDeriveCutNew( p, pObj, pCuts, Required ) )
                    goto finish;
    }
    else assert( 0 );
#ifdef MIG_RUNTIME
p->timeDerive += Abc_Clock() - clk;
#endif
finish:
    // transform internal storage into regular cuts
//    if ( Flag == 0 && p->nCutStore == p->nNumCuts - 1 )
//        Flag = 1, Mpm_CutPrintAll( p );
//    printf( "%d ", p->nCutStore );
    // save best cut
    assert( p->nCutStore > 0 );
    if ( p->pCutStore[0]->mTime <= Required )
    {
        Mpm_Cut_t * pCut;
        if ( hCutBest )
            Mmr_StepRecycle( p->pManCuts, hCutBest );
        hCutBest = Mpm_CutCreate( p, &p->pCutStore[0]->pCut, &pCut );
        Mpm_ObjSetCutBest( p, pObj, hCutBest );
        Mpm_ObjSetTime( p, pObj, p->pCutStore[0]->mTime );
        Mpm_ObjSetArea( p, pObj, p->pCutStore[0]->mArea );
        Mpm_ObjSetEdge( p, pObj, p->pCutStore[0]->mEdge );
//        if ( pCut->nLeaves < 1 )
//            printf( "%d ", pCut->nLeaves );
    }
    else assert( !p->fMainRun );
    assert( hCutBest > 0 );
    // transform internal storage into regular cuts
    Mpm_ObjTranslateCutsFromStore( p, pObj, Mig_ObjRefNum(pObj) > 0 );
    // dereference fanin cuts and reference node
    Mpm_ObjDerefFaninCuts( p, pObj );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Required times.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Mpm_ManFindArrivalMax( Mpm_Man_t * p )
{
    int * pmTimes = Vec_IntArray( &p->vTimes );
    Mig_Obj_t * pObj;
    int i, ArrMax = 0;
    Mig_ManForEachCo( p->pMig, pObj, i )
        ArrMax = Abc_MaxInt( ArrMax, pmTimes[ Mig_ObjFaninId0(pObj) ] );
    return ArrMax;
}
static inline void Mpm_ManFinalizeRound( Mpm_Man_t * p )
{
    int * pMapRefs  = Vec_IntArray( &p->vMapRefs );
    int * pRequired = Vec_IntArray( &p->vRequireds );
    Mig_Obj_t * pObj;
    Mpm_Cut_t * pCut;
    int * pDelays;
    int i, iLeaf;
    p->GloArea = 0;
    p->GloEdge = 0;
    p->GloRequired = Mpm_ManFindArrivalMax(p);
    Mpm_ManCleanMapRefs( p );
    Mpm_ManCleanRequired( p );
    Mig_ManForEachObjReverse( p->pMig, pObj )
    {
        if ( Mig_ObjIsCo(pObj) )
        {
            pRequired[Mig_ObjFaninId0(pObj)] = p->GloRequired;
            pMapRefs [Mig_ObjFaninId0(pObj)]++;
        }
        else if ( Mig_ObjIsNode(pObj) )
        {
            int Required = pRequired[Mig_ObjId(pObj)];
            assert( Required > 0 );
            if ( pMapRefs[Mig_ObjId(pObj)] > 0 )
            {
                pCut = Mpm_ObjCutBestP( p, pObj );
                pDelays = p->pLibLut->pLutDelays[pCut->nLeaves];
                Mpm_CutForEachLeafId( pCut, iLeaf, i )
                {
                    pRequired[iLeaf] = Abc_MinInt( pRequired[iLeaf], Required - pDelays[i] );
                    pMapRefs [iLeaf]++;
                }
                p->GloArea += p->pLibLut->pLutAreas[pCut->nLeaves];
                p->GloEdge += pCut->nLeaves;
            }
        }
        else if ( Mig_ObjIsBuf(pObj) )
        {
        }
    }
    p->GloArea /= MPM_UNIT_AREA;
}
static inline void Mpm_ManComputeEstRefs( Mpm_Man_t * p )
{
    int * pMapRefs  = Vec_IntArray( &p->vMapRefs );
    int * pEstRefs  = Vec_IntArray( &p->vEstRefs );
    int i;
    assert( p->fMainRun );
//  pObj->EstRefs = (float)((2.0 * pObj->EstRefs + pObj->nRefs) / 3.0);
    for ( i = 0; i < Mig_ManObjNum(p->pMig); i++ )
        pEstRefs[i] = (1 * pEstRefs[i] + MPM_UNIT_REFS * pMapRefs[i]) / 2;
}

/**Function*************************************************************

  Synopsis    [Cut comparison.]

  Description [Returns positive number if new one is better than old one.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mpm_CutCompareDelay( Mpm_Uni_t * pOld, Mpm_Uni_t * pNew )
{
    if ( pOld->mTime        != pNew->mTime         ) return pOld->mTime        - pNew->mTime;
    if ( pOld->pCut.nLeaves != pNew->pCut.nLeaves  ) return pOld->pCut.nLeaves - pNew->pCut.nLeaves;
    if ( pOld->mArea        != pNew->mArea         ) return pOld->mArea        - pNew->mArea;
    if ( pOld->mEdge        != pNew->mEdge         ) return pOld->mEdge        - pNew->mEdge;
    return 0;
}
int Mpm_CutCompareDelay2( Mpm_Uni_t * pOld, Mpm_Uni_t * pNew )
{
    if ( pOld->mTime        != pNew->mTime         ) return pOld->mTime        - pNew->mTime;
    if ( pOld->mArea        != pNew->mArea         ) return pOld->mArea        - pNew->mArea;
    if ( pOld->mEdge        != pNew->mEdge         ) return pOld->mEdge        - pNew->mEdge;
    if ( pOld->pCut.nLeaves != pNew->pCut.nLeaves  ) return pOld->pCut.nLeaves - pNew->pCut.nLeaves;
    return 0;
}
int Mpm_CutCompareArea( Mpm_Uni_t * pOld, Mpm_Uni_t * pNew )
{
    if ( pOld->mArea        != pNew->mArea         ) return pOld->mArea        - pNew->mArea;
    if ( pOld->pCut.nLeaves != pNew->pCut.nLeaves  ) return pOld->pCut.nLeaves - pNew->pCut.nLeaves;
    if ( pOld->mEdge        != pNew->mEdge         ) return pOld->mEdge        - pNew->mEdge;
    if ( pOld->mAveRefs     != pNew->mAveRefs      ) return pOld->mAveRefs     - pNew->mAveRefs;
    if ( pOld->mTime        != pNew->mTime         ) return pOld->mTime        - pNew->mTime;
    return 0;
}
int Mpm_CutCompareArea2( Mpm_Uni_t * pOld, Mpm_Uni_t * pNew )
{
    if ( pOld->mArea        != pNew->mArea         ) return pOld->mArea        - pNew->mArea;
    if ( pOld->mEdge        != pNew->mEdge         ) return pOld->mEdge        - pNew->mEdge;
    if ( pOld->mAveRefs     != pNew->mAveRefs      ) return pOld->mAveRefs     - pNew->mAveRefs;
    if ( pOld->pCut.nLeaves != pNew->pCut.nLeaves  ) return pOld->pCut.nLeaves - pNew->pCut.nLeaves;
    if ( pOld->mTime        != pNew->mTime         ) return pOld->mTime        - pNew->mTime;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Technology mapping experiment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mpm_ManPrepare( Mpm_Man_t * p )
{
    Mig_Obj_t * pObj;
    int i, hCut;
    Mig_ManForEachCi( p->pMig, pObj, i )
    {
        hCut = Mpm_CutCreateUnit( p, Mig_ObjId(pObj) );
        Mpm_ObjSetCutBest( p, pObj, hCut );
        Mpm_ObjSetCutList( p, pObj, hCut );
    }
    Mig_ManForEachCand( p->pMig, pObj )
        Mpm_ObjSetEstRef( p, pObj, MPM_UNIT_REFS * Mig_ObjRefNum(pObj) );
}
void Mpm_ManPerformRound( Mpm_Man_t * p )
{
    Mig_Obj_t * pObj;
    abctime clk = Abc_Clock();
    p->nCutsMerged = 0;
    Mpm_ManSetMigRefs( p );
    Mig_ManForEachNode( p->pMig, pObj )
        Mpm_ManDeriveCuts( p, pObj );
    Mpm_ManFinalizeRound( p );
    printf( "Del =%5d.  Ar =%8d.  Edge =%8d.  Cut =%10d. Max =%10d.  Tru =%6d. Small =%5d. ", 
        p->GloRequired, p->GloArea, p->GloEdge, 
        p->nCutsMerged, p->pManCuts->nEntriesMax, 
        p->vTtMem ? p->vTtMem->nEntries : 0, p->nSmallSupp );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}
void Mpm_ManPerform( Mpm_Man_t * p )
{
    p->pCutCmp = Mpm_CutCompareDelay;
    Mpm_ManPerformRound( p );
    
    p->pCutCmp = Mpm_CutCompareDelay2;
    Mpm_ManPerformRound( p );
    
    p->pCutCmp = Mpm_CutCompareArea;
    Mpm_ManPerformRound( p );   

    p->fMainRun = 1;

    p->pCutCmp = Mpm_CutCompareArea;
    Mpm_ManComputeEstRefs( p );
    Mpm_ManPerformRound( p );

    p->pCutCmp = Mpm_CutCompareArea2;
    Mpm_ManComputeEstRefs( p );
    Mpm_ManPerformRound( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

