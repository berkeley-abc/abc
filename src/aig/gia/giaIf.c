/**CFile****************************************************************

  FileName    [giaMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Manipulation of mapping associated with the AIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaMap.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "aig/aig/aig.h"
#include "map/if/if.h"
#include "bool/kit/kit.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Kit_TruthToGia( Gia_Man_t * pMan, unsigned * pTruth, int nVars, Vec_Int_t * vMemory, Vec_Int_t * vLeaves, int fHash );
extern int Abc_RecToGia2( Gia_Man_t * pMan, If_Man_t * pIfMan, If_Cut_t * pCut, If_Obj_t * pIfObj, Vec_Int_t * vLeaves, int fHash );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetIfParsDefault( void * pp )
{
    If_Par_t * pPars = (If_Par_t *)pp;
//    extern void * Abc_FrameReadLibLut();
    If_Par_t * p = (If_Par_t *)pPars;
    // set defaults
    memset( p, 0, sizeof(If_Par_t) );
    // user-controlable paramters
    p->nLutSize    = -1;
//    p->nLutSize    =  6;
    p->nCutsMax    =  8;
    p->nFlowIters  =  1;
    p->nAreaIters  =  2;
    p->DelayTarget = -1;
    p->Epsilon     =  (float)0.005;
    p->fPreprocess =  1;
    p->fArea       =  0;
    p->fFancy      =  0;
    p->fExpRed     =  1; ////
    p->fLatchPaths =  0;
    p->fEdge       =  1;
    p->fPower      =  0;
    p->fCutMin     =  0;
    p->fSeqMap     =  0;
    p->fVerbose    =  0;
    p->pLutStruct  =  NULL;
    // internal parameters
    p->fTruth      =  0;
    p->nLatchesCi  =  0;
    p->nLatchesCo  =  0;
    p->fLiftLeaves =  0;
    p->fUseCoAttrs =  1;   // use CO attributes
    p->pLutLib     =  NULL;
    p->pTimesArr   =  NULL; 
    p->pTimesArr   =  NULL;   
    p->pFuncCost   =  NULL;   
}


/**Function*************************************************************

  Synopsis    [Prints mapping statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManLutFaninCount( Gia_Man_t * p )
{
    int i, Counter = 0;
    Gia_ManForEachLut( p, i )
        Counter += Gia_ObjLutSize(p, i);
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Prints mapping statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManLutSizeMax( Gia_Man_t * p )
{
    int i, nSizeMax = -1;
    Gia_ManForEachLut( p, i )
        nSizeMax = Abc_MaxInt( nSizeMax, Gia_ObjLutSize(p, i) );
    return nSizeMax;
}

/**Function*************************************************************

  Synopsis    [Prints mapping statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManLutNum( Gia_Man_t * p )
{
    int i, Counter = 0;
    Gia_ManForEachLut( p, i )
        Counter ++;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Prints mapping statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManLutLevel( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, k, iFan, Level;
    int * pLevels = ABC_CALLOC( int, Gia_ManObjNum(p) );
    Gia_ManForEachLut( p, i )
    {
        Level = 0;
        Gia_LutForEachFanin( p, i, iFan, k )
            if ( Level < pLevels[iFan] )
                Level = pLevels[iFan];
        pLevels[i] = Level + 1;
    }
    Level = 0;
    Gia_ManForEachCo( p, pObj, k )
        if ( Level < pLevels[Gia_ObjFaninId0p(p, pObj)] )
            Level = pLevels[Gia_ObjFaninId0p(p, pObj)];
    ABC_FREE( pLevels );
    return Level;
}

/**Function*************************************************************

  Synopsis    [Assigns levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetRefsMapped( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i, k, iFan;
    ABC_FREE( p->pRefs );
    p->pRefs = ABC_CALLOC( int, Gia_ManObjNum(p) );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ObjRefInc( p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachLut( p, i )
        Gia_LutForEachFanin( p, i, iFan, k )
            Gia_ObjRefInc( p, Gia_ManObj(p, iFan) );
}

/**Function*************************************************************

  Synopsis    [Prints mapping statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintMappingStats( Gia_Man_t * p )
{
    int * pLevels;
    int i, k, iFan, nLutSize = 0, nLuts = 0, nFanins = 0, LevelMax = 0;
    if ( !p->pMapping )
        return;
    pLevels = ABC_CALLOC( int, Gia_ManObjNum(p) );
    Gia_ManForEachLut( p, i )
    {
        nLuts++;
        nFanins += Gia_ObjLutSize(p, i);
        nLutSize = Abc_MaxInt( nLutSize, Gia_ObjLutSize(p, i) );
        Gia_LutForEachFanin( p, i, iFan, k )
            pLevels[i] = Abc_MaxInt( pLevels[i], pLevels[iFan] );
        pLevels[i]++;
        LevelMax = Abc_MaxInt( LevelMax, pLevels[i] );
    }
    ABC_FREE( pLevels );
    Abc_Print( 1, "mapping (K=%d)  :  ", nLutSize );
    Abc_Print( 1, "lut =%7d  ", nLuts );
    Abc_Print( 1, "edge =%8d  ", nFanins );
    Abc_Print( 1, "lev =%5d  ", LevelMax );
    Abc_Print( 1, "mem =%5.2f MB", 4.0*(Gia_ManObjNum(p) + 2*nLuts + nFanins)/(1<<20) );
    Abc_Print( 1, "\n" );
}



/**Function*************************************************************

  Synopsis    [Converts GIA into IF manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline If_Obj_t * If_ManFanin0Copy( If_Man_t * pIfMan, Gia_Obj_t * pObj ) { return If_NotCond( If_ManObj(pIfMan, Gia_ObjValue(Gia_ObjFanin0(pObj))), Gia_ObjFaninC0(pObj) ); }
static inline If_Obj_t * If_ManFanin1Copy( If_Man_t * pIfMan, Gia_Obj_t * pObj ) { return If_NotCond( If_ManObj(pIfMan, Gia_ObjValue(Gia_ObjFanin1(pObj))), Gia_ObjFaninC1(pObj) ); }
If_Man_t * Gia_ManToIf( Gia_Man_t * p, If_Par_t * pPars )
{
    If_Man_t * pIfMan;
    If_Obj_t * pIfObj;
    Gia_Obj_t * pObj;
    int i;
    // create levels with choices
    Gia_ManChoiceLevel( p );
    // mark representative nodes
    Gia_ManMarkFanoutDrivers( p );
    // start the mapping manager and set its parameters
    pIfMan = If_ManStart( pPars );
    pIfMan->pName = Abc_UtilStrsav( Gia_ManName(p) );
    // print warning about excessive memory usage
    if ( 1.0 * Gia_ManObjNum(p) * pIfMan->nObjBytes / (1<<30) > 1.0 )
        printf( "Warning: The mapper will allocate %.1f GB for to represent the subject graph with %d AIG nodes.\n", 
            1.0 * Gia_ManObjNum(p) * pIfMan->nObjBytes / (1<<30), Gia_ManObjNum(p) );
    // load the AIG into the mapper
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = If_ObjId( If_ManConst1(pIfMan) );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            pIfObj = If_ManCreateAnd( pIfMan, If_ManFanin0Copy(pIfMan, pObj), If_ManFanin1Copy(pIfMan, pObj) );
        else if ( Gia_ObjIsCi(pObj) )
        {
            pIfObj = If_ManCreateCi( pIfMan );
            If_ObjSetLevel( pIfObj, Gia_ObjLevel(p, pObj) );
//            Abc_Print( 1, "pi%d=%d\n ", If_ObjId(pIfObj), If_ObjLevel(pIfObj) );
            if ( pIfMan->nLevelMax < (int)pIfObj->Level )
                pIfMan->nLevelMax = (int)pIfObj->Level;
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            pIfObj = If_ManCreateCo( pIfMan, If_NotCond( If_ManFanin0Copy(pIfMan, pObj), Gia_ObjIsConst0(Gia_ObjFanin0(pObj))) );
//            Abc_Print( 1, "po%d=%d\n ", If_ObjId(pIfObj), If_ObjLevel(pIfObj) );
        }
        else assert( 0 );
        assert( i == If_ObjId(pIfObj) );
        Gia_ObjSetValue( pObj, If_ObjId(pIfObj) );
        // set up the choice node
        if ( Gia_ObjSibl(p, i) && pObj->fMark0 )
        {
            Gia_Obj_t * pSibl, * pPrev;
            for ( pPrev = pObj, pSibl = Gia_ObjSiblObj(p, i); pSibl; pPrev = pSibl, pSibl = Gia_ObjSiblObj(p, Gia_ObjId(p, pSibl)) )
                If_ObjSetChoice( If_ManObj(pIfMan, Gia_ObjValue(pObj)), If_ManObj(pIfMan, Gia_ObjValue(pSibl)) );
            If_ManCreateChoice( pIfMan, If_ManObj(pIfMan, Gia_ObjValue(pObj)) );
            pPars->fExpRed = 0;
        }
//        assert( If_ObjLevel(pIfObj) == Gia_ObjLevel(pNode) );
    }
    Gia_ManCleanMark0( p );
    return pIfMan;
}


/**Function*************************************************************

  Synopsis    [Derives node's AIG after SOP balancing]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManNodeIfSopToGiaInt( Gia_Man_t * pNew, Vec_Wrd_t * vAnds, int nVars, Vec_Int_t * vLeaves, int fHash )
{
    Vec_Int_t * vResults;
    int iRes0, iRes1, iRes = -1;
    If_And_t This;
    word Entry;
    int i;
    if ( Vec_WrdSize(vAnds) == 0 )
        return 0;
    if ( Vec_WrdSize(vAnds) == 1 && Vec_WrdEntry(vAnds,0) == 0 )
        return 1;
    vResults = Vec_IntAlloc( Vec_WrdSize(vAnds) );
    for ( i = 0; i < nVars; i++ )
        Vec_IntPush( vResults, Vec_IntEntry(vLeaves, i) );
    Vec_WrdForEachEntryStart( vAnds, Entry, i, nVars )
    {
        This  = If_WrdToAnd( Entry );
        iRes0 = Abc_LitNotCond( Vec_IntEntry(vResults, This.iFan0), This.fCompl0 ); 
        iRes1 = Abc_LitNotCond( Vec_IntEntry(vResults, This.iFan1), This.fCompl1 ); 
        if ( fHash )
            iRes  = Gia_ManHashAnd( pNew, iRes0, iRes1 );
        else
            iRes  = Gia_ManAppendAnd( pNew, iRes0, iRes1 );
        Vec_IntPush( vResults, iRes );
    }
    Vec_IntFree( vResults );
    return Abc_LitNotCond( iRes, This.fCompl );
}
int Gia_ManNodeIfSopToGia( Gia_Man_t * pNew, If_Man_t * p, If_Cut_t * pCut, Vec_Int_t * vLeaves, int fHash )
{
    int iResult;
    Vec_Wrd_t * vArray;
    vArray  = If_CutDelaySopArray( p, pCut );
    iResult = Gia_ManNodeIfSopToGiaInt( pNew, vArray, If_CutLeaveNum(pCut), vLeaves, fHash );
//    Vec_WrdFree( vArray );
    return iResult;
}

/**Function*************************************************************

  Synopsis    [Recursively derives the local AIG for the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManNodeIfToGia_rec( Gia_Man_t * pNew, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Ptr_t * vVisited, int fHash )
{
    If_Cut_t * pCut;
    If_Obj_t * pTemp;
    int iFunc, iFunc0, iFunc1;
    // get the best cut
    pCut = If_ObjCutBest(pIfObj);
    // if the cut is visited, return the result
    if ( If_CutDataInt(pCut) )
        return If_CutDataInt(pCut);
    // mark the node as visited
    Vec_PtrPush( vVisited, pCut );
    // insert the worst case
    If_CutSetDataInt( pCut, ~0 );
    // skip in case of primary input
    if ( If_ObjIsCi(pIfObj) )
        return If_CutDataInt(pCut);
    // compute the functions of the children
    for ( pTemp = pIfObj; pTemp; pTemp = pTemp->pEquiv )
    {
        iFunc0 = Gia_ManNodeIfToGia_rec( pNew, pIfMan, pTemp->pFanin0, vVisited, fHash );
        if ( iFunc0 == ~0 )
            continue;
        iFunc1 = Gia_ManNodeIfToGia_rec( pNew, pIfMan, pTemp->pFanin1, vVisited, fHash );
        if ( iFunc1 == ~0 )
            continue;
        // both branches are solved
        if ( fHash )
            iFunc = Gia_ManHashAnd( pNew, Abc_LitNotCond(iFunc0, pTemp->fCompl0), Abc_LitNotCond(iFunc1, pTemp->fCompl1) ); 
        else
            iFunc = Gia_ManAppendAnd( pNew, Abc_LitNotCond(iFunc0, pTemp->fCompl0), Abc_LitNotCond(iFunc1, pTemp->fCompl1) ); 
        if ( pTemp->fPhase != pIfObj->fPhase )
            iFunc = Abc_LitNot(iFunc);
        If_CutSetDataInt( pCut, iFunc );
        break;
    }
    return If_CutDataInt(pCut);
}
int Gia_ManNodeIfToGia( Gia_Man_t * pNew, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Int_t * vLeaves, int fHash )
{
    If_Cut_t * pCut;
    If_Obj_t * pLeaf;
    int i, iRes;
    // get the best cut
    pCut = If_ObjCutBest(pIfObj);
    assert( pCut->nLeaves > 1 );
    // set the leaf variables
    If_CutForEachLeaf( pIfMan, pCut, pLeaf, i )
        If_CutSetDataInt( If_ObjCutBest(pLeaf), Vec_IntEntry(vLeaves, i) );
    // recursively compute the function while collecting visited cuts
    Vec_PtrClear( pIfMan->vTemp );
    iRes = Gia_ManNodeIfToGia_rec( pNew, pIfMan, pIfObj, pIfMan->vTemp, fHash ); 
    if ( iRes == ~0 )
    {
        Abc_Print( -1, "Gia_ManNodeIfToGia(): Computing local AIG has failed.\n" );
        return ~0;
    }
    // clean the cuts
    If_CutForEachLeaf( pIfMan, pCut, pLeaf, i )
        If_CutSetDataInt( If_ObjCutBest(pLeaf), 0 );
    Vec_PtrForEachEntry( If_Cut_t *, pIfMan->vTemp, pCut, i )
        If_CutSetDataInt( pCut, 0 );
    return iRes;
}

/**Function*************************************************************

  Synopsis    [Converts IF into GIA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFromIf( If_Man_t * pIfMan )
{
    int fHash = 0;
    Gia_Man_t * pNew;
    If_Obj_t * pIfObj, * pIfLeaf;
    If_Cut_t * pCutBest;
    Vec_Int_t * vLeaves;
    Vec_Int_t * vCover;
    unsigned * pTruth;
    int Counter, iOffset, nItems = 0;
    int i, k, w, GiaId;
    // create new manager
    pNew = Gia_ManStart( If_ManObjNum(pIfMan) );
    Gia_ManHashAlloc( pNew );
    // iterate through nodes used in the mapping
    vCover = Vec_IntAlloc( 1 << 16 );
    vLeaves = Vec_IntAlloc( 16 );
    If_ManCleanCutData( pIfMan );
    If_ManForEachObj( pIfMan, pIfObj, i )
    {
        if ( pIfObj->nRefs == 0 && !If_ObjIsTerm(pIfObj) )
            continue;
        if ( If_ObjIsAnd(pIfObj) )
        {
            pCutBest = If_ObjCutBest( pIfObj );
            // collect leaves of the best cut
            Vec_IntClear( vLeaves );
            If_CutForEachLeaf( pIfMan, pCutBest, pIfLeaf, k )
                Vec_IntPush( vLeaves, pIfLeaf->iCopy );
            // get the functionality
            if ( pIfMan->pPars->pLutStruct )
                pIfObj->iCopy = Kit_TruthToGia( pNew, If_CutTruth(pCutBest), If_CutLeaveNum(pCutBest), vCover, vLeaves, fHash );
            else if ( pIfMan->pPars->fDelayOpt )
                pIfObj->iCopy = Gia_ManNodeIfSopToGia( pNew, pIfMan, pCutBest, vLeaves, fHash );
            else if ( pIfMan->pPars->fUserRecLib )
                pIfObj->iCopy = Abc_RecToGia2( pNew, pIfMan, pCutBest, pIfObj, vLeaves, fHash );
            else
                pIfObj->iCopy = Gia_ManNodeIfToGia( pNew, pIfMan, pIfObj, vLeaves, fHash );
            // complement the node if the TT was used and the cut was complemented
            if ( pIfMan->pPars->pLutStruct )
                pIfObj->iCopy = Abc_LitNotCond( pIfObj->iCopy, pCutBest->fCompl );
            // count entries in the mapping array
            nItems += 2 + If_CutLeaveNum( pCutBest );
        }
        else if ( If_ObjIsCi(pIfObj) )
            pIfObj->iCopy = Gia_ManAppendCi(pNew);
        else if ( If_ObjIsCo(pIfObj) )
            pIfObj->iCopy = Gia_ManAppendCo( pNew, Abc_LitNotCond(If_ObjFanin0(pIfObj)->iCopy, If_ObjFaninC0(pIfObj)) );
        else if ( If_ObjIsConst1(pIfObj) )
        {
            pIfObj->iCopy = 1;
            nItems += 2; 
        }
        else assert( 0 );
    }
    Vec_IntFree( vCover );
    Vec_IntFree( vLeaves );
    Gia_ManHashStop( pNew );

    // GIA after mapping with choices may end up with dangling nodes
    // which participate as leaves of some cuts used in the mapping
    // such nodes are marked here and skipped when mapping is derived
    Counter = Gia_ManMarkDangling(pNew);
//    if ( pIfMan->pPars->fVerbose && Counter )
    if ( Counter )
        printf( "GIA after mapping has %d dangling nodes.\n", Counter );

    // create mapping
    iOffset = Gia_ManObjNum(pNew);
    pNew->pMapping = ABC_CALLOC( int, iOffset + nItems );
    assert( pNew->vTruths == NULL );
    if ( pIfMan->pPars->pLutStruct )
        pNew->vTruths = Vec_IntAlloc( 1000 );
    If_ManForEachObj( pIfMan, pIfObj, i )
    {
        if ( pIfObj->nRefs == 0 && !If_ObjIsTerm(pIfObj) )
            continue;
        if ( If_ObjIsAnd(pIfObj) )
        { 
            GiaId = Abc_Lit2Var( pIfObj->iCopy );
            if ( !Gia_ObjIsAnd(Gia_ManObj(pNew, GiaId)) ) // skip trivial node
                continue;
            assert( Gia_ObjIsAnd(Gia_ManObj(pNew, GiaId)) );
            if ( !Gia_ManObj(pNew, GiaId)->fMark0 ) // skip dangling node
                continue;
            // get the best cut
            pCutBest = If_ObjCutBest( pIfObj );
            // copy the truth tables
            pTruth = NULL;
            if ( pNew->vTruths )
            { 
                // copy truth table
                for ( w = 0; w < pIfMan->nTruthWords; w++ )
                    Vec_IntPush( pNew->vTruths, If_CutTruth(pCutBest)[w] );
                pTruth = (unsigned *)(Vec_IntArray(pNew->vTruths) + Vec_IntSize(pNew->vTruths) - pIfMan->nTruthWords);
                // complement 
                if ( pCutBest->fCompl ^ Abc_LitIsCompl(pIfObj->iCopy) )
                    for ( w = 0; w < pIfMan->nTruthWords; w++ )
                        pTruth[w] = ~pTruth[w];
            }
            // create node
            pNew->pMapping[GiaId]     = iOffset;
            pNew->pMapping[iOffset++] = If_CutLeaveNum(pCutBest);
            If_CutForEachLeaf( pIfMan, pCutBest, pIfLeaf, k )
            {
                int FaninId = Abc_Lit2Var(pIfLeaf->iCopy);
                if ( pTruth && Abc_LitIsCompl(pIfLeaf->iCopy) )
                    Kit_TruthChangePhase( pTruth, If_CutLeaveNum(pCutBest), k );
                if ( !Gia_ManObj(pNew, FaninId)->fMark0 ) // skip dangling node
                {
                    // update truth table
                    if ( pTruth )
                    {
                        extern void If_CluSwapVars( word * pTruth, int nVars, int * V2P, int * P2V, int iVar, int jVar );
                        if ( If_CutLeaveNum(pCutBest) >= 6 )
                            If_CluSwapVars( (word*)pTruth, If_CutLeaveNum(pCutBest), NULL, NULL, k, If_CutLeaveNum(pCutBest)-1 );
                        else
                        {
                            word Truth = ((word)pTruth[0] << 32) | (word)pTruth[0];
                            If_CluSwapVars( &Truth, 6, NULL, NULL, k, If_CutLeaveNum(pCutBest)-1 );
                            pTruth[0] = (Truth & 0xFFFFFFFF);
                        }
                    }
                    pNew->pMapping[iOffset-k-1]--;
                    continue;
                }
                assert( FaninId < GiaId );
                pNew->pMapping[iOffset++] = FaninId;
            }
            pNew->pMapping[iOffset++] = GiaId;
        }
        else if ( If_ObjIsConst1(pIfObj) )
        {
            // create node
            pNew->pMapping[0] = iOffset;
            pNew->pMapping[iOffset++] = 0;
            pNew->pMapping[iOffset++] = 0;
/*
            if ( pNew->vTruths )
            {
                printf( "%d ", nLeaves );
                for ( w = 0; w < pIfMan->nTruthWords; w++ )
                    Vec_IntPush( pNew->vTruths, 0 );
            }
*/
        }
    }
    Gia_ManCleanMark0( pNew );
//    assert( iOffset == Gia_ManObjNum(pNew) + nItems );
    if ( pIfMan->pManTim )
        pNew->pManTime = Tim_ManDup( pIfMan->pManTim, 0 );
    // verify that COs have mapping
    {
        Gia_Obj_t * pObj;
        Gia_ManForEachCo( pNew, pObj, i )
        {
            if ( Gia_ObjIsAnd(Gia_ObjFanin0(pObj)) )
                assert( pNew->pMapping[Gia_ObjFaninId0p(pNew, pObj)] != 0 );
        }
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Interface of LUT mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManPerformMapping( Gia_Man_t * p, void * pp )
{
    Gia_Man_t * pNew;
    If_Man_t * pIfMan;
    If_Par_t * pPars = (If_Par_t *)pp;
    // set the arrival times
    assert( pPars->pTimesArr == NULL );
    pPars->pTimesArr = ABC_ALLOC( float, Gia_ManCiNum(p) );
    memset( pPars->pTimesArr, 0, sizeof(float) * Gia_ManCiNum(p) );
    // translate into the mapper
    pIfMan = Gia_ManToIf( p, pPars );    
    if ( pIfMan == NULL )
        return NULL;
    if ( p->pManTime )
        pIfMan->pManTim = Tim_ManDup( (Tim_Man_t *)p->pManTime, 0 );
    if ( !If_ManPerformMapping( pIfMan ) )
    {
        If_ManStop( pIfMan );
        return NULL;
    }
    // transform the result of mapping into the new network
    pNew = Gia_ManFromIf( pIfMan );
    If_ManStop( pIfMan );
    // transfer name
    assert( pNew->pName == NULL );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    // unmap in case of SOP balancing
//    if ( pIfMan->pPars->fDelayOpt )
//        Vec_IntFreeP( &pNew->vMapping );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

