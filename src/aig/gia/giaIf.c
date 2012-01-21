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
#include "src/aig/aig/aig.h"
#include "src/map/if/if.h"
#include "src/opt/dar/dar.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetIfParsDefault( If_Par_t * pPars )
{
//    extern void * Abc_FrameReadLibLut();
    // set defaults
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
//    pPars->nLutSize    = -1;
    pPars->nLutSize    =  6;
    pPars->nCutsMax    =  8;
    pPars->nFlowIters  =  1;
    pPars->nAreaIters  =  2;
    pPars->DelayTarget = -1;
    pPars->Epsilon     =  (float)0.005;
    pPars->fPreprocess =  1;
    pPars->fArea       =  0;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  1; ////
    pPars->fLatchPaths =  0;
    pPars->fEdge       =  1;
    pPars->fPower      =  0;
    pPars->fCutMin     =  0;
    pPars->fSeqMap     =  0;
    pPars->fVerbose    =  0;
    // internal parameters
    pPars->fTruth      =  0;
    pPars->nLatches    =  0;
    pPars->fLiftLeaves =  0;
//    pPars->pLutLib     =  Abc_FrameReadLibLut();
    pPars->pLutLib     =  NULL;
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->pFuncCost   =  NULL;   
}

/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Man_t * Gia_ManToIf( Gia_Man_t * p, If_Par_t * pPars, Vec_Ptr_t * vAigToIf )
{
//    extern Vec_Int_t * SGia_ManComputeSwitchProbs( Gia_Man_t * p, int nFrames, int nPref, int fProbOne );
//    Vec_Int_t * vSwitching = NULL, * vSwitching2 = NULL;
//    float * pSwitching, * pSwitching2;
    If_Man_t * pIfMan;
    If_Obj_t * pIfObj;
    Gia_Obj_t * pNode;
    int i, clk = clock();
    Gia_ManLevelNum( p );
//    assert( p->pReprs == NULL );
/*
    // set the number of registers (switch activity will be combinational)
    Gia_ManSetRegNum( p, 0 );
    if ( pPars->fPower )
    {
        vSwitching  = SGia_ManComputeSwitchProbs( p, 48, 16, 0 );
        if ( pPars->fVerbose )
        {
            ABC_PRT( "Computing switching activity", clock() - clk );
        }
        pSwitching  = (float *)vSwitching->pArray;
        vSwitching2 = Vec_IntStart( Gia_ManObjNumMax(p) );
        pSwitching2 = (float *)vSwitching2->pArray;
    }
*/
    // start the mapping manager and set its parameters
    pIfMan = If_ManStart( pPars );
//    pIfMan->vSwitching = vSwitching2;
    // load the AIG into the mapper
    Gia_ManCreateRefs( p );
    Gia_ManForEachObj( p, pNode, i )
    {
        if ( Gia_ObjIsAnd(pNode) )
            pIfObj = If_ManCreateAnd( pIfMan, 
                If_NotCond( (If_Obj_t *)Vec_PtrEntry(vAigToIf, Gia_ObjFaninId0(pNode, i)), Gia_ObjFaninC0(pNode) ), 
                If_NotCond( (If_Obj_t *)Vec_PtrEntry(vAigToIf, Gia_ObjFaninId1(pNode, i)), Gia_ObjFaninC1(pNode) ) );
        else if ( Gia_ObjIsCi(pNode) )
        {
            pIfObj = If_ManCreateCi( pIfMan );
            If_ObjSetLevel( pIfObj, Gia_ObjLevel(p,pNode) );
//            Abc_Print( 1, "pi=%d ", pIfObj->Level );
            if ( pIfMan->nLevelMax < (int)pIfObj->Level )
                pIfMan->nLevelMax = (int)pIfObj->Level;
        }
        else if ( Gia_ObjIsCo(pNode) )
        {
            pIfObj = If_ManCreateCo( pIfMan, If_NotCond( (If_Obj_t *)Vec_PtrEntry(vAigToIf, Gia_ObjFaninId0(pNode, i)), Gia_ObjFaninC0(pNode) ) );
//            Abc_Print( 1, "po=%d ", pIfObj->Level );
        }
        else if ( Gia_ObjIsConst0(pNode) )
            pIfObj = If_Not(If_ManConst1( pIfMan ));
        else // add the node to the mapper
            assert( 0 );
        // save the result
        assert( Vec_PtrEntry(vAigToIf, i) == NULL );
        Vec_PtrWriteEntry( vAigToIf, i, pIfObj );
//        if ( vSwitching2 )
//            pSwitching2[pIfObj->Id] = pSwitching[pNode->Id];    
        // set up the choice node
/*
//        if ( p->pReprs && p->pNexts && Gia_ObjIsHead( p, i ) )
        if ( p->pNexts && Gia_ObjNext(p, i) && Gia_ObjRefsId(p, i) )
        {
            int iPrev, iFanin;
            pIfMan->nChoices++;
            for ( iPrev = i, iFanin = Gia_ObjNext(p, i); iFanin; iPrev = iFanin, iFanin = Gia_ObjNext(p, iFanin) )
                If_ObjSetChoice( Vec_PtrEntry(vAigToIf,iPrev), Vec_PtrEntry(vAigToIf,iFanin) );
            If_ManCreateChoice( pIfMan, Vec_PtrEntry(vAigToIf,i) );
        }
*/
/*        // set up the choice node
        if ( Gia_ObjIsChoice( p, pNode ) )
        {
            pIfMan->nChoices++;
            for ( pPrev = pNode, pFanin = Gia_ObjEquiv(p, pNode); pFanin; pPrev = pFanin, pFanin = Gia_ObjEquiv(p, pFanin) )
                If_ObjSetChoice( pPrev->pData, pFanin->pData );
            If_ManCreateChoice( pIfMan, pNode->pData );
        }
//        assert( If_ObjLevel(pIfObj) == Gia_ObjLevel(pNode) );
*/
    }
//    if ( vSwitching )
//        Vec_IntFree( vSwitching );
    return pIfMan;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Gia_ManFromIf( If_Man_t * pIfMan, Gia_Man_t * p, Vec_Ptr_t * vAigToIf )
{
    int * pMapping, iOffset;
    Vec_Ptr_t * vIfToAig;
    Gia_Obj_t * pObj, * pObjRepr;
    If_Obj_t * pIfObj;
    If_Cut_t * pCutBest;
    int i, k, j, nLeaves, * ppLeaves;
    int nItems = 0;
    assert( Gia_ManCiNum(p) == If_ManCiNum(pIfMan) );
    assert( Gia_ManCoNum(p) == If_ManCoNum(pIfMan) );
    assert( Gia_ManAndNum(p) == If_ManAndNum(pIfMan) );
    // create mapping of IF to AIG
    vIfToAig = Vec_PtrStart( If_ManObjNum(pIfMan) );
    Gia_ManForEachObj( p, pObj, i )
    {
        pIfObj = (If_Obj_t *)Vec_PtrEntry( vAigToIf, i );
        Vec_PtrWriteEntry( vIfToAig, pIfObj->Id, pObj );
        if ( !Gia_ObjIsAnd(pObj) || pIfObj->nRefs == 0 )
            continue;
        nItems += 2 + If_CutLeaveNum( If_ObjCutBest(pIfObj) );
    }
    // construct the network
    pMapping = ABC_CALLOC( int, Gia_ManObjNum(p) + nItems );
    iOffset = Gia_ManObjNum(p);
    Gia_ManForEachObj( p, pObj, i )
    {
        pIfObj = (If_Obj_t *)Vec_PtrEntry( vAigToIf, i );
        if ( !Gia_ObjIsAnd(pObj) || pIfObj->nRefs == 0 )
            continue;
        pCutBest = If_ObjCutBest( pIfObj );
        nLeaves  = If_CutLeaveNum( pCutBest ); 
        ppLeaves = If_CutLeaves( pCutBest );
        // create node
        k = iOffset;
        pMapping[k++] = nLeaves;
        for ( j = 0; j < nLeaves; j++ )
        {
            pObjRepr = (Gia_Obj_t *)Vec_PtrEntry( vIfToAig, ppLeaves[j] );
            pMapping[k++] = Gia_ObjId( p, pObjRepr );
        }
        pMapping[k++] = i;
        pMapping[i] = iOffset;
        iOffset = k;
    }
    assert( iOffset <= Gia_ManObjNum(p) + nItems );
    Vec_PtrFree( vIfToAig );
//    pNtk->pManTime = Tim_ManDup( pIfMan->pManTim, 0 );
    return pMapping;
}

/**Function*************************************************************

  Synopsis    [Interface with the FPGA mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_MappingIf( Gia_Man_t * p, If_Par_t * pPars )
{
    If_Man_t * pIfMan;
    Vec_Ptr_t * vAigToIf;
    // set the arrival times
    pPars->pTimesArr = ABC_ALLOC( float, Gia_ManCiNum(p) );
    memset( pPars->pTimesArr, 0, sizeof(float) * Gia_ManCiNum(p) );
    // translate into the mapper
    vAigToIf = Vec_PtrStart( Gia_ManObjNum(p) );
    pIfMan = Gia_ManToIf( p, pPars, vAigToIf );    
    if ( pIfMan == NULL )
    {
        Vec_PtrFree( vAigToIf );
        return 0;
    }
//    pIfMan->pManTim = Tim_ManDup( pManTime, 0 );
    if ( !If_ManPerformMapping( pIfMan ) )
    {
        Vec_PtrFree( vAigToIf );
        If_ManStop( pIfMan );
        return 0;
    }
    // transform the result of mapping into the new network
    ABC_FREE( p->pMapping );
    p->pMapping = Gia_ManFromIf( pIfMan, p, vAigToIf );
//    if ( pPars->fBidec && pPars->nLutSize <= 8 )
//        Gia_ManBidecResyn( pNtk, 0 );
    If_ManStop( pIfMan );
    Vec_PtrFree( vAigToIf );
    return 1;
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
    Abc_Print( 1, "mem =%5.2f Mb", 4.0*(Gia_ManObjNum(p) + 2*nLuts + nFanins)/(1<<20) );
    Abc_Print( 1, "\n" );
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

  Synopsis    [Prints NPN class statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintNpnClasses( Gia_Man_t * p )
{
    extern char ** Kit_DsdNpn4ClassNames();
    char ** pNames = Kit_DsdNpn4ClassNames();
    Vec_Int_t * vLeaves, * vTruth, * vVisited;
    int * pLutClass, ClassCounts[222] = {0};
    int i, k, iFan, Class, OtherClasses, OtherClasses2, nTotal, Counter, Counter2;
    unsigned * pTruth;
    assert( p->pMapping != NULL );
    assert(  Gia_ManLutSizeMax( p ) <= 4 );
    vLeaves   = Vec_IntAlloc( 100 );
    vVisited  = Vec_IntAlloc( 100 );
    vTruth    = Vec_IntAlloc( (1<<16) );
    pLutClass = ABC_CALLOC( int, Gia_ManObjNum(p) );
    Gia_ManCleanTruth( p );
    Gia_ManForEachLut( p, i )
    {
        if ( Gia_ObjLutSize(p,i) > 4 )
            continue;
        Vec_IntClear( vLeaves );
        Gia_LutForEachFanin( p, i, iFan, k )
            Vec_IntPush( vLeaves, iFan );
        for ( ; k < 4; k++ )
            Vec_IntPush( vLeaves, 0 );
        pTruth = Gia_ManConvertAigToTruth( p, Gia_ManObj(p, i), vLeaves, vTruth, vVisited );
        Class = Dar_LibReturnClass( *pTruth );
        ClassCounts[ Class ]++;
        pLutClass[i] = Class;
    }
    Vec_IntFree( vLeaves );
    Vec_IntFree( vTruth );
    Vec_IntFree( vVisited );
    Vec_IntFreeP( &p->vTruths );
    nTotal = 0;
    for ( i = 0; i < 222; i++ )
        nTotal += ClassCounts[i];
    Abc_Print( 1, "NPN CLASS STATISTICS (for %d LUT4 present in the current mapping):\n", nTotal );
    OtherClasses = 0;
    for ( i = 0; i < 222; i++ )
    {
        if ( ClassCounts[i] == 0 )
            continue;
        if ( 100.0 * ClassCounts[i] / (nTotal+1) < 0.1 ) // do not show anything below 0.1 percent
            continue;
        OtherClasses += ClassCounts[i];
        Abc_Print( 1, "Class %3d :  Count = %6d   (%7.2f %%)   %s\n", 
            i, ClassCounts[i], 100.0 * ClassCounts[i] / (nTotal+1), pNames[i] );
    }
    OtherClasses = nTotal - OtherClasses;
    Abc_Print( 1, "Other     :  Count = %6d   (%7.2f %%)\n", 
        OtherClasses, 100.0 * OtherClasses / (nTotal+1) );
    // count the number of LUTs that have MUX function and two fanins with MUX functions
    OtherClasses = OtherClasses2 = 0;
    ABC_FREE( p->pRefs );
    Gia_ManSetRefsMapped( p );
    Gia_ManForEachLut( p, i )
    {
        if ( pLutClass[i] != 109 )
            continue;
        Counter = Counter2 = 0;
        Gia_LutForEachFanin( p, i, iFan, k )
        {
            Counter  += (pLutClass[iFan] == 109);
            Counter2 += (pLutClass[iFan] == 109) && (Gia_ObjRefsId(p, iFan) == 1);
        }
        OtherClasses  += (Counter > 1);
        OtherClasses2 += (Counter2 > 1);
//            Abc_Print( 1, "%d -- ", pLutClass[i] );
//            Gia_LutForEachFanin( p, i, iFan, k )
//                Abc_Print( 1, "%d ", pLutClass[iFan] );
//            Abc_Print( 1, "\n" );
    }
    ABC_FREE( p->pRefs );
    Abc_Print( 1, "Approximate number of 4:1 MUX structures: All = %6d  (%7.2f %%)  MFFC = %6d  (%7.2f %%)\n", 
        OtherClasses,  100.0 * OtherClasses  / (nTotal+1),
        OtherClasses2, 100.0 * OtherClasses2 / (nTotal+1) );
    ABC_FREE( pLutClass );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

