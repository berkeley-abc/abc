/**CFile****************************************************************

  FileName    [abcIf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface with the FPGA mapping package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: abcIf.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "src/base/abc/abc.h"
#include "src/base/main/main.h"
#include "src/map/if/if.h"
#include "src/bool/kit/kit.h"
#include "src/aig/aig/aig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern If_Man_t *  Abc_NtkToIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
static Abc_Ntk_t * Abc_NtkFromIf( If_Man_t * pIfMan, Abc_Ntk_t * pNtk );
extern Abc_Obj_t * Abc_NodeFromIf_rec( Abc_Ntk_t * pNtkNew, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Int_t * vCover );
static Hop_Obj_t * Abc_NodeIfToHop( Hop_Man_t * pHopMan, If_Man_t * pIfMan, If_Obj_t * pIfObj );
static Vec_Ptr_t * Abc_NtkFindGoodOrder( Abc_Ntk_t * pNtk );

extern void Abc_NtkBddReorder( Abc_Ntk_t * pNtk, int fVerbose );
extern void Abc_NtkBidecResyn( Abc_Ntk_t * pNtk, int fVerbose );

extern void Abc_NtkCollectPoDrivers( If_Man_t * p, Abc_Ntk_t * pNtk );
extern void Abc_NtkCreateChoiceDrivers( If_Man_t * p );
extern void Abc_NtkFreePoDrivers( If_Man_t * p, Abc_Ntk_t * pNtk );
extern void Abc_NtkRecreatePoDrivers( If_Man_t * p, Abc_Ntk_t * pNtkNew );
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Interface with the FPGA mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkIfComputeSwitching( Abc_Ntk_t * pNtk, If_Man_t * pIfMan )
{
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    extern Vec_Int_t * Saig_ManComputeSwitchProbs( Aig_Man_t * p, int nFrames, int nPref, int fProbOne );
    Vec_Int_t * vSwitching;
    float * pSwitching;
    Abc_Obj_t * pObjAbc;
    Aig_Obj_t * pObjAig;
    Aig_Man_t * pAig;
    If_Obj_t * pObjIf;
    int i, clk = clock();
    // map IF objects into old network
    Abc_NtkForEachObj( pNtk, pObjAbc, i )
        if ( (pObjIf = (If_Obj_t *)pObjAbc->pTemp) )
            pObjIf->pCopy = pObjAbc;
    // map network into an AIG
    pAig = Abc_NtkToDar( pNtk, 0, 0 );
    vSwitching = Saig_ManComputeSwitchProbs( pAig, 48, 16, 0 );
    pSwitching = (float *)vSwitching->pArray;
    Abc_NtkForEachObj( pNtk, pObjAbc, i )
        if ( (pObjAig = (Aig_Obj_t *)pObjAbc->pTemp) )
        {
            pObjAbc->dTemp = pSwitching[pObjAig->Id];
            // J. Anderson and F. N. Najm, “Power-Aware Technology Mapping for LUT-Based FPGAs,
            // IEEE Intl. Conf. on Field-Programmable Technology, 2002.
//            pObjAbc->dTemp = (1.55 + 1.05 / (float) Abc_ObjFanoutNum(pObjAbc)) * pSwitching[pObjAig->Id];
        }
    Vec_IntFree( vSwitching );
    Aig_ManStop( pAig );
    // compute switching for the IF objects
    assert( pIfMan->vSwitching == NULL );
    pIfMan->vSwitching = Vec_IntStart( If_ManObjNum(pIfMan) );
    pSwitching = (float *)pIfMan->vSwitching->pArray;
    If_ManForEachObj( pIfMan, pObjIf, i )
        if ( (pObjAbc = (Abc_Obj_t *)pObjIf->pCopy) )
            pSwitching[i] = pObjAbc->dTemp;
if ( pIfMan->pPars->fVerbose )
{
    ABC_PRT( "Computing switching activity", clock() - clk );
}
}

/**Function*************************************************************

  Synopsis    [Interface with the FPGA mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars )
{
    Abc_Ntk_t * pNtkNew;
    If_Man_t * pIfMan;

    assert( Abc_NtkIsStrash(pNtk) );

    // get timing information
    pPars->pTimesArr = Abc_NtkGetCiArrivalFloats(pNtk);
    pPars->pTimesReq = NULL;

    // set the latch paths
    if ( pPars->fLatchPaths && pPars->pTimesArr )
    {
        int c;
        for ( c = 0; c < Abc_NtkPiNum(pNtk); c++ )
            pPars->pTimesArr[c] = -ABC_INFINITY;
    }

    // create FPGA mapper
    pIfMan = Abc_NtkToIf( pNtk, pPars );    
    if ( pIfMan == NULL )
        return NULL;
    if ( pPars->fPower )
        Abc_NtkIfComputeSwitching( pNtk, pIfMan );

    // perform FPGA mapping
    if ( pPars->fEnableRealPos )
        Abc_NtkCollectPoDrivers( pIfMan, pNtk );
    Abc_NtkCreateChoiceDrivers( pIfMan );
    if ( !If_ManPerformMapping( pIfMan ) )
    {
        Abc_NtkFreePoDrivers( pIfMan, pNtk );
        If_ManStop( pIfMan );
        return NULL;
    }
    Abc_NtkFreePoDrivers( pIfMan, pNtk );

    // transform the result of mapping into the new network
    pNtkNew = Abc_NtkFromIf( pIfMan, pNtk );
    if ( pNtkNew == NULL )
        return NULL;
    If_ManStop( pIfMan );
    if ( pPars->fBidec && pPars->nLutSize <= 8 )
        Abc_NtkBidecResyn( pNtkNew, 0 );

    // duplicate EXDC
    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkDup( pNtk->pExdc );
    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkIf: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Man_t * Abc_NtkToIf( Abc_Ntk_t * pNtk, If_Par_t * pPars )
{
    ProgressBar * pProgress;
    If_Man_t * pIfMan;
    Abc_Obj_t * pNode, * pFanin, * pPrev;
    Vec_Ptr_t * vNodes;
    int i;

    assert( Abc_NtkIsStrash(pNtk) );
//    vNodes = Abc_NtkFindGoodOrder( pNtk );
    vNodes = Abc_AigDfs( pNtk, 0, 0 );

    // start the mapping manager and set its parameters
    pIfMan = If_ManStart( pPars );

    // print warning about excessive memory usage
    if ( 1.0 * Abc_NtkObjNum(pNtk) * pIfMan->nObjBytes / (1<<30) > 1.0 )
        printf( "Warning: The mapper will allocate %.1f Gb for to represent the subject graph with %d AIG nodes.\n", 
            1.0 * Abc_NtkObjNum(pNtk) * pIfMan->nObjBytes / (1<<30), Abc_NtkObjNum(pNtk) );

    // create PIs and remember them in the old nodes
    Abc_NtkCleanCopy( pNtk );
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)If_ManConst1( pIfMan );
    Abc_NtkForEachCi( pNtk, pNode, i )
    {
        pNode->pCopy = (Abc_Obj_t *)If_ManCreateCi( pIfMan );
//printf( "AIG CI %2d -> IF CI %2d\n", pNode->Id, ((If_Obj_t *)pNode->pCopy)->Id );
    }

    // load the AIG into the mapper
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkObjNumMax(pNtk) );
//    Abc_AigForEachAnd( pNtk, pNode, i )
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, "Initial" );
        // add the node to the mapper
        pNode->pCopy = (Abc_Obj_t *)If_ManCreateAnd( pIfMan, 
            If_NotCond( (If_Obj_t *)Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) ), 
            If_NotCond( (If_Obj_t *)Abc_ObjFanin1(pNode)->pCopy, Abc_ObjFaninC1(pNode) ) );
        // set up the choice node
        if ( Abc_AigNodeIsChoice( pNode ) )
        {
            pIfMan->nChoices++;
            for ( pPrev = pNode, pFanin = (Abc_Obj_t *)pNode->pData; pFanin; pPrev = pFanin, pFanin = (Abc_Obj_t *)pFanin->pData )
                If_ObjSetChoice( (If_Obj_t *)pPrev->pCopy, (If_Obj_t *)pFanin->pCopy );
            If_ManCreateChoice( pIfMan, (If_Obj_t *)pNode->pCopy );
        }
//printf( "AIG node %2d -> IF node %2d\n", pNode->Id, ((If_Obj_t *)pNode->pCopy)->Id );
    }
    Extra_ProgressBarStop( pProgress );
    Vec_PtrFree( vNodes );

    // set the primary outputs without copying the phase
    Abc_NtkForEachCo( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)If_ManCreateCo( pIfMan, If_NotCond( (If_Obj_t *)Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) ) );
    return pIfMan;
}


/**Function*************************************************************

  Synopsis    [Box mapping procedures.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_MapBoxSetPrevNext( Vec_Ptr_t * vDrivers, Vec_Int_t * vMapIn, Vec_Int_t * vMapOut, int Id )
{
    Abc_Obj_t * pNode;
    pNode = (Abc_Obj_t *)Vec_PtrEntry(vDrivers, Id+2);
    Vec_IntWriteEntry( vMapIn, Abc_ObjId(Abc_ObjFanin0(pNode)), Id );
    pNode = (Abc_Obj_t *)Vec_PtrEntry(vDrivers, Id+4);
    Vec_IntWriteEntry( vMapOut, Abc_ObjId(Abc_ObjFanin0(pNode)), Id );
}
static inline int Abc_MapBox2Next( Vec_Ptr_t * vDrivers, Vec_Int_t * vMapIn, Vec_Int_t * vMapOut, int Id )
{
    Abc_Obj_t * pNode = (Abc_Obj_t *)Vec_PtrEntry(vDrivers, Id+4);
    return Vec_IntEntry( vMapIn, Abc_ObjId(Abc_ObjFanin0(pNode)) );
}
static inline int Abc_MapBox2Prev( Vec_Ptr_t * vDrivers, Vec_Int_t * vMapIn, Vec_Int_t * vMapOut, int Id )
{
    Abc_Obj_t * pNode = (Abc_Obj_t *)Vec_PtrEntry(vDrivers, Id+2);
    return Vec_IntEntry( vMapOut, Abc_ObjId(Abc_ObjFanin0(pNode)) );
}

/**Function*************************************************************

  Synopsis    [Creates the mapped network.]

  Description [Assuming the copy field of the mapped nodes are NULL.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromIf( If_Man_t * pIfMan, Abc_Ntk_t * pNtk )
{
    ProgressBar * pProgress;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pNodeNew;
    Vec_Int_t * vCover;
    int i, nDupGates;
    // create the new network
    if ( pIfMan->pPars->fUseBdds || pIfMan->pPars->fUseCnfs || pIfMan->pPars->fUseMv )
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_BDD );
    else if ( pIfMan->pPars->fUseSops )
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    else
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_AIG );
    // prepare the mapping manager
    If_ManCleanNodeCopy( pIfMan );
    If_ManCleanCutData( pIfMan );
    // make the mapper point to the new network
    If_ObjSetCopy( If_ManConst1(pIfMan), Abc_NtkCreateNodeConst1(pNtkNew) );
    Abc_NtkForEachCi( pNtk, pNode, i )
        If_ObjSetCopy( If_ManCi(pIfMan, i), pNode->pCopy );

    // process the nodes in topological order
    vCover = Vec_IntAlloc( 1 << 16 );
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, "Final" );
        pNodeNew = Abc_NodeFromIf_rec( pNtkNew, pIfMan, If_ObjFanin0(If_ManCo(pIfMan, i)), vCover );
        pNodeNew = Abc_ObjNotCond( pNodeNew, If_ObjFaninC0(If_ManCo(pIfMan, i)) );
        Abc_ObjAddFanin( pNode->pCopy, pNodeNew );
    }
    Extra_ProgressBarStop( pProgress );
    Vec_IntFree( vCover );

    // update PO drivers
    if ( pIfMan->pPars->fEnableRealPos )
        Abc_NtkRecreatePoDrivers( pIfMan, pNtkNew );

    // remove the constant node if not used
    pNodeNew = (Abc_Obj_t *)If_ObjCopy( If_ManConst1(pIfMan) );
    if ( Abc_ObjFanoutNum(pNodeNew) == 0 && !Abc_ObjIsNone(pNodeNew) )
        Abc_NtkDeleteObj( pNodeNew );
    // minimize the node
    if ( pIfMan->pPars->fUseBdds || pIfMan->pPars->fUseCnfs || pIfMan->pPars->fUseMv )
        Abc_NtkSweep( pNtkNew, 0 );
    if ( pIfMan->pPars->fUseBdds )
        Abc_NtkBddReorder( pNtkNew, 0 );
    // decouple the PO driver nodes to reduce the number of levels
    nDupGates = Abc_NtkLogicMakeSimpleCos( pNtkNew, !pIfMan->pPars->fUseBuffs );
    if ( nDupGates && pIfMan->pPars->fVerbose && !Abc_FrameReadFlag("silentmode") )
    {
        if ( pIfMan->pPars->fUseBuffs )
            printf( "Added %d buffers/inverters to decouple the CO drivers.\n", nDupGates );
        else
            printf( "Duplicated %d gates to decouple the CO drivers.\n", nDupGates );
    }
    return pNtkNew;
}


/**Function*************************************************************

  Synopsis    [Inserts the entry while sorting them by delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NodeTruthToHopInt( Hop_Man_t * pMan, Vec_Wrd_t * vAnds, int nVars )
{
    Vec_Ptr_t * vResults;
    Hop_Obj_t * pRes0, * pRes1, * pRes;
    If_And_t This;
    word Entry;
    int i;
    if ( Vec_WrdSize(vAnds) == 0 )
        return Hop_ManConst0(pMan);
    if ( Vec_WrdSize(vAnds) == 1 && Vec_WrdEntry(vAnds,0) == 0 )
        return Hop_ManConst1(pMan);
    vResults = Vec_PtrAlloc( Vec_WrdSize(vAnds) );
    for ( i = 0; i < nVars; i++ )
        Vec_PtrPush( vResults, Hop_IthVar(pMan, i) );
    Vec_WrdForEachEntryStart( vAnds, Entry, i, nVars )
    {
        This  = If_WrdToAnd( Entry );
        pRes0 = Hop_NotCond( (Hop_Obj_t *)Vec_PtrEntry(vResults, This.iFan0), This.fCompl0 ); 
        pRes1 = Hop_NotCond( (Hop_Obj_t *)Vec_PtrEntry(vResults, This.iFan1), This.fCompl1 ); 
        pRes  = Hop_And( pMan, pRes0, pRes1 );
        Vec_PtrPush( vResults, pRes );
/*
        printf( "fan0 = %c%d  fan1 = %c%d  Del = %d\n", 
            This.fCompl0? '-':'+', This.iFan0, 
            This.fCompl1? '-':'+', This.iFan1, 
            This.Delay );
*/
    }
    Vec_PtrFree( vResults );
    return Hop_NotCond( pRes, This.fCompl );
}

/**Function*************************************************************

  Synopsis    [Creates the mapped network.]

  Description [Assuming the copy field of the mapped nodes are NULL.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NodeTruthToHop( Hop_Man_t * pMan, If_Man_t * p, If_Cut_t * pCut )
{
    Hop_Obj_t * pResult;
    Vec_Wrd_t * vArray;
    vArray  = If_CutDelaySopArray( p, pCut );
    pResult = Abc_NodeTruthToHopInt( pMan, vArray, If_CutLeaveNum(pCut) );
//    Vec_WrdFree( vArray );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Derive one node after FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeFromIf_rec( Abc_Ntk_t * pNtkNew, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Int_t * vCover )
{
    Abc_Obj_t * pNodeNew;
    If_Cut_t * pCutBest;
    If_Obj_t * pIfLeaf;
    int i;
    // return if the result if known
    pNodeNew = (Abc_Obj_t *)If_ObjCopy( pIfObj );
    if ( pNodeNew )
        return pNodeNew;
    assert( pIfObj->Type == IF_AND );
    // get the parameters of the best cut
    // create a new node 
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    pCutBest = If_ObjCutBest( pIfObj );
//    printf( "%d 0x%02X %d\n", pCutBest->nLeaves, 0xff & *If_CutTruth(pCutBest), pIfMan->pPars->pFuncCost(pCutBest) );
//    if ( pIfMan->pPars->pLutLib && pIfMan->pPars->pLutLib->fVarPinDelays )
    if ( !pIfMan->pPars->fDelayOpt && !pIfMan->pPars->pLutStruct && !pIfMan->pPars->fUserRecLib )
        If_CutRotatePins( pIfMan, pCutBest );
    if ( pIfMan->pPars->fUseCnfs || pIfMan->pPars->fUseMv )
    {
        If_CutForEachLeafReverse( pIfMan, pCutBest, pIfLeaf, i )
            Abc_ObjAddFanin( pNodeNew, Abc_NodeFromIf_rec(pNtkNew, pIfMan, pIfLeaf, vCover) );
    }
    else
    {
        If_CutForEachLeaf( pIfMan, pCutBest, pIfLeaf, i )
            Abc_ObjAddFanin( pNodeNew, Abc_NodeFromIf_rec(pNtkNew, pIfMan, pIfLeaf, vCover) );
    }
    // set the level of the new node
    pNodeNew->Level = Abc_ObjLevelNew( pNodeNew );
    // derive the function of this node
    if ( pIfMan->pPars->fTruth )
    {
        if ( pIfMan->pPars->fUseBdds )
        { 
            // transform truth table into the BDD 
            pNodeNew->pData = Kit_TruthToBdd( (DdManager *)pNtkNew->pManFunc, If_CutTruth(pCutBest), If_CutLeaveNum(pCutBest), 0 );  Cudd_Ref((DdNode *)pNodeNew->pData); 
        }
        else if ( pIfMan->pPars->fUseCnfs || pIfMan->pPars->fUseMv )
        { 
            // transform truth table into the BDD 
            pNodeNew->pData = Kit_TruthToBdd( (DdManager *)pNtkNew->pManFunc, If_CutTruth(pCutBest), If_CutLeaveNum(pCutBest), 1 );  Cudd_Ref((DdNode *)pNodeNew->pData); 
        }
        else if ( pIfMan->pPars->fUseSops ) 
        {
            // transform truth table into the SOP
            int RetValue = Kit_TruthIsop( If_CutTruth(pCutBest), If_CutLeaveNum(pCutBest), vCover, 1 );
            assert( RetValue == 0 || RetValue == 1 );
            // check the case of constant cover
            if ( Vec_IntSize(vCover) == 0 || (Vec_IntSize(vCover) == 1 && Vec_IntEntry(vCover,0) == 0) )
            {
                assert( RetValue == 0 );
                pNodeNew->pData = Abc_SopCreateAnd( (Mem_Flex_t *)pNtkNew->pManFunc, If_CutLeaveNum(pCutBest), NULL );
                pNodeNew = (Vec_IntSize(vCover) == 0) ? Abc_NtkCreateNodeConst0(pNtkNew) : Abc_NtkCreateNodeConst1(pNtkNew);
            }
            else
            {
                // derive the AIG for that tree
                pNodeNew->pData = Abc_SopCreateFromIsop( (Mem_Flex_t *)pNtkNew->pManFunc, If_CutLeaveNum(pCutBest), vCover );
                if ( RetValue )
                    Abc_SopComplement( (char *)pNodeNew->pData );
            }
        }
        else if ( pIfMan->pPars->fDelayOpt )
        {
            extern Hop_Obj_t * Abc_NodeTruthToHop( Hop_Man_t * pMan, If_Man_t * pIfMan, If_Cut_t * pCut );
            pNodeNew->pData = Abc_NodeTruthToHop( (Hop_Man_t *)pNtkNew->pManFunc, pIfMan, pCutBest );
        }
        else if ( pIfMan->pPars->fUserRecLib )
        {
            extern Hop_Obj_t * Abc_RecToHop( Hop_Man_t * pMan, If_Man_t * pIfMan, If_Cut_t * pCut, If_Obj_t * pIfObj );
            pNodeNew->pData = Abc_RecToHop( (Hop_Man_t *)pNtkNew->pManFunc, pIfMan, pCutBest, pIfObj);
        }
        else
        {
            extern Hop_Obj_t * Kit_TruthToHop( Hop_Man_t * pMan, unsigned * pTruth, int nVars, Vec_Int_t * vMemory );
            pNodeNew->pData = Kit_TruthToHop( (Hop_Man_t *)pNtkNew->pManFunc, If_CutTruth(pCutBest), If_CutLeaveNum(pCutBest), vCover );
        }
        // complement the node if the cut was complemented
        if ( pCutBest->fCompl )
            Abc_NodeComplement( pNodeNew );
    }
    else
    {
        pNodeNew->pData = Abc_NodeIfToHop( (Hop_Man_t *)pNtkNew->pManFunc, pIfMan, pIfObj );
    }
    If_ObjSetCopy( pIfObj, pNodeNew );
/*
printf( "%3d : Delay = %d  Cutsize = %d\n", pNodeNew->Id, (int)pCutBest->Delay, pCutBest->nLeaves );
{
    Abc_Obj_t * pFanin;
    int i;
Abc_ObjForEachFanin( pNodeNew, pFanin, i )
printf( "fanin%d = %2d\n", i, pFanin->Id );
}
*/
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Recursively derives the truth table for the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NodeIfToHop_rec( Hop_Man_t * pHopMan, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Ptr_t * vVisited )
{
    If_Cut_t * pCut;
    Hop_Obj_t * gFunc, * gFunc0, * gFunc1;
    // get the best cut
    pCut = If_ObjCutBest(pIfObj);
    // if the cut is visited, return the result
    if ( If_CutData(pCut) )
        return (Hop_Obj_t *)If_CutData(pCut);
    // compute the functions of the children
    gFunc0 = Abc_NodeIfToHop_rec( pHopMan, pIfMan, pIfObj->pFanin0, vVisited );
    gFunc1 = Abc_NodeIfToHop_rec( pHopMan, pIfMan, pIfObj->pFanin1, vVisited );
    // get the function of the cut
    gFunc  = Hop_And( pHopMan, Hop_NotCond(gFunc0, pIfObj->fCompl0), Hop_NotCond(gFunc1, pIfObj->fCompl1) );  
    assert( If_CutData(pCut) == NULL );
    If_CutSetData( pCut, gFunc );
    // add this cut to the visited list
    Vec_PtrPush( vVisited, pCut );
    return gFunc;
}


/**Function*************************************************************

  Synopsis    [Recursively derives the truth table for the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NodeIfToHop2_rec( Hop_Man_t * pHopMan, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Ptr_t * vVisited )
{
    If_Cut_t * pCut;
    If_Obj_t * pTemp;
    Hop_Obj_t * gFunc, * gFunc0, * gFunc1;
    // get the best cut
    pCut = If_ObjCutBest(pIfObj);
    // if the cut is visited, return the result
    if ( If_CutData(pCut) )
        return (Hop_Obj_t *)If_CutData(pCut);
    // mark the node as visited
    Vec_PtrPush( vVisited, pCut );
    // insert the worst case
    If_CutSetData( pCut, (void *)1 );
    // skip in case of primary input
    if ( If_ObjIsCi(pIfObj) )
        return (Hop_Obj_t *)If_CutData(pCut);
    // compute the functions of the children
    for ( pTemp = pIfObj; pTemp; pTemp = pTemp->pEquiv )
    {
        gFunc0 = Abc_NodeIfToHop2_rec( pHopMan, pIfMan, pTemp->pFanin0, vVisited );
        if ( gFunc0 == (void *)1 )
            continue;
        gFunc1 = Abc_NodeIfToHop2_rec( pHopMan, pIfMan, pTemp->pFanin1, vVisited );
        if ( gFunc1 == (void *)1 )
            continue;
        // both branches are solved
        gFunc = Hop_And( pHopMan, Hop_NotCond(gFunc0, pTemp->fCompl0), Hop_NotCond(gFunc1, pTemp->fCompl1) ); 
        if ( pTemp->fPhase != pIfObj->fPhase )
            gFunc = Hop_Not(gFunc);
        If_CutSetData( pCut, gFunc );
        break;
    }
    return (Hop_Obj_t *)If_CutData(pCut);
}

/**Function*************************************************************

  Synopsis    [Derives the truth table for one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NodeIfToHop( Hop_Man_t * pHopMan, If_Man_t * pIfMan, If_Obj_t * pIfObj )
{
    If_Cut_t * pCut;
    Hop_Obj_t * gFunc;
    If_Obj_t * pLeaf;
    int i;
    // get the best cut
    pCut = If_ObjCutBest(pIfObj);
    assert( pCut->nLeaves > 1 );
    // set the leaf variables
    If_CutForEachLeaf( pIfMan, pCut, pLeaf, i )
        If_CutSetData( If_ObjCutBest(pLeaf), Hop_IthVar(pHopMan, i) );
    // recursively compute the function while collecting visited cuts
    Vec_PtrClear( pIfMan->vTemp );
    gFunc = Abc_NodeIfToHop2_rec( pHopMan, pIfMan, pIfObj, pIfMan->vTemp ); 
    if ( gFunc == (void *)1 )
    {
        printf( "Abc_NodeIfToHop(): Computing local AIG has failed.\n" );
        return NULL;
    }
//    printf( "%d ", Vec_PtrSize(p->vTemp) );
    // clean the cuts
    If_CutForEachLeaf( pIfMan, pCut, pLeaf, i )
        If_CutSetData( If_ObjCutBest(pLeaf), NULL );
    Vec_PtrForEachEntry( If_Cut_t *, pIfMan->vTemp, pCut, i )
        If_CutSetData( pCut, NULL );
    return gFunc;
}


/**Function*************************************************************

  Synopsis    [Comparison for two nodes with the flow.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjCompareFlow( Abc_Obj_t ** ppNode0, Abc_Obj_t ** ppNode1 )
{
    float Flow0 = Abc_Int2Float((int)(ABC_PTRINT_T)(*ppNode0)->pCopy);
    float Flow1 = Abc_Int2Float((int)(ABC_PTRINT_T)(*ppNode1)->pCopy);
    if ( Flow0 > Flow1 )
        return -1;
    if ( Flow0 < Flow1 )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Orders AIG nodes so that nodes from larger cones go first.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFindGoodOrder_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    if ( !Abc_ObjIsNode(pNode) )
        return;
    assert( Abc_ObjIsNode( pNode ) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // visit the transitive fanin of the node
    Abc_NtkFindGoodOrder_rec( Abc_ObjFanin0(pNode), vNodes );
    Abc_NtkFindGoodOrder_rec( Abc_ObjFanin1(pNode), vNodes );
    // add the node after the fanins have been added
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Orders AIG nodes so that nodes from larger cones go first.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkFindGoodOrder( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes, * vCos;
    Abc_Obj_t * pNode, * pFanin0, * pFanin1;
    float Flow0, Flow1;
    int i;

    // initialize the flow
    Abc_AigConst1(pNtk)->pCopy = NULL;
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->pCopy = NULL;
    // compute the flow
    Abc_AigForEachAnd( pNtk, pNode, i )
    {
        pFanin0 = Abc_ObjFanin0(pNode);
        pFanin1 = Abc_ObjFanin1(pNode);
        Flow0 = Abc_Int2Float((int)(ABC_PTRINT_T)pFanin0->pCopy)/Abc_ObjFanoutNum(pFanin0);
        Flow1 = Abc_Int2Float((int)(ABC_PTRINT_T)pFanin1->pCopy)/Abc_ObjFanoutNum(pFanin1);
        pNode->pCopy = (Abc_Obj_t *)(ABC_PTRINT_T)Abc_Float2Int(Flow0 + Flow1+(float)1.0);
    }
    // find the flow of the COs
    vCos = Vec_PtrAlloc( Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        pNode->pCopy = Abc_ObjFanin0(pNode)->pCopy;
//        pNode->pCopy = (Abc_Obj_t *)Abc_Float2Int((float)Abc_ObjFanin0(pNode)->Level);
        Vec_PtrPush( vCos, pNode );
    }

    // sort nodes in the increasing order of the flow
    qsort( (Abc_Obj_t **)Vec_PtrArray(vCos), Abc_NtkCoNum(pNtk), 
        sizeof(Abc_Obj_t *), (int (*)(const void *, const void *))Abc_ObjCompareFlow );
    // verify sorting
    pFanin0 = (Abc_Obj_t *)Vec_PtrEntry(vCos, 0);
    pFanin1 = (Abc_Obj_t *)Vec_PtrEntryLast(vCos);
    assert( Abc_Int2Float((int)(ABC_PTRINT_T)pFanin0->pCopy) >= Abc_Int2Float((int)(ABC_PTRINT_T)pFanin1->pCopy) );

    // collect the nodes in the topological order from the new array
    Abc_NtkIncrementTravId( pNtk );
    vNodes = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vCos, pNode, i )
    {
        Abc_NtkFindGoodOrder_rec( Abc_ObjFanin0(pNode), vNodes );
//        printf( "%.2f ", Abc_Int2Float((int)pNode->pCopy) );
    }
    Vec_PtrFree( vCos );
    return vNodes;
}


/**Function*************************************************************

  Synopsis    [Sets PO drivers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMarkMux( Abc_Obj_t * pDriver, Abc_Obj_t ** ppNode1, Abc_Obj_t ** ppNode2 )
{
    Abc_Obj_t * pNodeC, * pNodeT, * pNodeE;
    If_Obj_t * pIfObj;

    *ppNode1 = NULL;
    *ppNode2 = NULL;
    if ( pDriver == NULL )
        return;
    if ( !Abc_NodeIsMuxType(pDriver) )
        return;

    pNodeC = Abc_NodeRecognizeMux( pDriver, &pNodeT, &pNodeE );

    pIfObj = If_Regular( (If_Obj_t *)Abc_ObjFanin0(pDriver)->pCopy );
    if ( If_ObjIsAnd(pIfObj) )
        pIfObj->fSkipCut = 1;
    pIfObj = If_Regular( (If_Obj_t *)Abc_ObjFanin1(pDriver)->pCopy );
    if ( If_ObjIsAnd(pIfObj) )
        pIfObj->fSkipCut = 1;

    pIfObj = If_Regular( (If_Obj_t *)Abc_ObjRegular(pNodeC)->pCopy );
    if ( If_ObjIsAnd(pIfObj) )
        pIfObj->fSkipCut = 1;

/*
    pIfObj = If_Regular( (If_Obj_t *)Abc_ObjRegular(pNodeT)->pCopy );
    if ( If_ObjIsAnd(pIfObj) )
        pIfObj->fSkipCut = 1;
    pIfObj = If_Regular( (If_Obj_t *)Abc_ObjRegular(pNodeE)->pCopy );
    if ( If_ObjIsAnd(pIfObj) )
        pIfObj->fSkipCut = 1;
*/
    *ppNode1 = Abc_ObjRegular(pNodeC);
    *ppNode2 = Abc_ObjRegular(pNodeT);
}

/**Function*************************************************************

  Synopsis    [Sets PO drivers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCollectPoDrivers( If_Man_t * p, Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vTemp;
    Abc_Obj_t * pObj, * pDriver;
    If_Obj_t * pIfObj;
    int i, g, nGroups;
    if ( pNtk->nRealPos == 0 )
    {
        if ( !Abc_FrameReadFlag("silentmode") )
            printf( "PO drivers are not defined.\n" );
        return;
    }
    if ( (Abc_NtkPoNum(pNtk) - pNtk->nRealPos) % 5 != 0 )
    {
        if ( !Abc_FrameReadFlag("silentmode") )
            printf( "PO drivers are not divisible by 5.\n" );
        return;
    }
    nGroups = (Abc_NtkPoNum(pNtk) - pNtk->nRealPos) / 5;
    if ( !Abc_FrameReadFlag("silentmode") )
        printf( "Processing %d groups of PO drivers.\n", nGroups );
    // mark the drivers (0 a   1 b   2 c   3 s   4 c)
    assert( p->pDriverCuts == NULL );
    p->pDriverCuts = ABC_CALLOC( Vec_Int_t *, If_ManObjNum(p) );
    for ( g = 0; g < nGroups; g++ )
    {
        // collect inputs
        vTemp = Vec_IntAlloc( 3 );
        for ( i = 0; i < 3; i++ )
        {
            pObj   = Abc_NtkPo( pNtk, pNtk->nRealPos + g * 5 + i );
            pIfObj = If_Regular( ((If_Obj_t *)pObj->pCopy)->pFanin0 );
            Vec_IntPush( vTemp, pIfObj->Id );
        }
//        Vec_IntSort( vTemp, 0 );
        // find output node
        pObj   = Abc_NtkPo( pNtk, pNtk->nRealPos + g * 5 + 3 );
        pIfObj = If_Regular( ((If_Obj_t *)pObj->pCopy)->pFanin0 );
        if ( !If_ObjIsConst1(pIfObj) && p->pDriverCuts[pIfObj->Id] == NULL )
            p->pDriverCuts[pIfObj->Id] = Vec_IntDup( vTemp );
        // find output node
        pObj   = Abc_NtkPo( pNtk, pNtk->nRealPos + g * 5 + 4 );
        pIfObj = If_Regular( ((If_Obj_t *)pObj->pCopy)->pFanin0 );
        if ( !If_ObjIsConst1(pIfObj) && p->pDriverCuts[pIfObj->Id] == NULL )
        {
            p->pDriverCuts[pIfObj->Id] = Vec_IntDup( vTemp );
            pIfObj->fDriver = 1;
//            printf( "%d ", pIfObj->Id );
        }
        Vec_IntFree( vTemp );
    }
//    printf( "\n" );
    return;

    // highlight inner logic
    for ( i = pNtk->nRealPos; i <  Abc_NtkPoNum(pNtk); i += 5 )
    {
        Abc_Obj_t * pNode1, * pNode2;

        pObj = Abc_NtkPo( pNtk, i + 4 );
        pDriver = Abc_ObjFanin0( pObj );
        Abc_NtkMarkMux( pDriver, &pNode1, &pNode2 );

/*
        pObj = Abc_NtkPo( pNtk, i + 3 );
        pDriver = Abc_ObjFanin0( pObj );
        Abc_NtkMarkMux( pDriver, &pNode1, &pNode2 );
        if ( pNode1 == NULL )
            continue;

        assert( Abc_ObjRegular(pNode1) != Abc_ObjRegular(pNode2) );
//        Abc_NtkMarkMux( pNode1, &pNode1, &pNode2 );
//        Abc_NtkMarkMux( pNode2, &pNode1, &pNode2 );
*/
    }

/*
    {
        Vec_Int_t * vInfo;
        int i, k, numPo;

        Vec_VecForEachLevelInt( pNtk->vRealPos, vInfo, i )
        {
            numPo = Vec_IntEntry( vInfo, 0 );
            pObj = Abc_NtkPo( pNtk, numPo+2 );
            pDriver = Abc_ObjFanin0( pObj );
            pIfObj = If_Regular( (If_Obj_t *)pDriver->pCopy );
            pIfObj->fSkipCut = 0;

            numPo = Vec_IntEntryLast( vInfo );
            pObj = Abc_NtkPo( pNtk, numPo+4 );
            pDriver = Abc_ObjFanin0( pObj );
            pIfObj = If_Regular( (If_Obj_t *)pDriver->pCopy );
            pIfObj->fSkipCut = 0;

            Vec_IntForEachEntry( vInfo, numPo, k )
            {
                pObj = Abc_NtkPo( pNtk, numPo+0 );
                pDriver = Abc_ObjFanin0( pObj );
                pIfObj = If_Regular( (If_Obj_t *)pDriver->pCopy );
                pIfObj->fSkipCut = 0;

                pObj = Abc_NtkPo( pNtk, numPo+1 );
                pDriver = Abc_ObjFanin0( pObj );
                pIfObj = If_Regular( (If_Obj_t *)pDriver->pCopy );
                pIfObj->fSkipCut = 0;

                pObj = Abc_NtkPo( pNtk, numPo+2 );
                pDriver = Abc_ObjFanin0( pObj );
                pIfObj = If_Regular( (If_Obj_t *)pDriver->pCopy );
                pIfObj->fSkipCut = 0;

                pObj = Abc_NtkPo( pNtk, numPo+3 );
                pDriver = Abc_ObjFanin0( pObj );
                pIfObj = If_Regular( (If_Obj_t *)pDriver->pCopy );
                pIfObj->fSkipCut = 0;
            }
        }
    }
*/
}


/**Function*************************************************************

  Synopsis    [Frees PO drivers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCreateChoiceDrivers( If_Man_t * p )
{
    Vec_Int_t * vVec;
    If_Obj_t * pObj, * pTemp;
    int i, Counter = 0;
    if ( p->pDriverCuts == NULL )
        return;
    If_ManForEachNode( p, pObj, i )
    {
        // skip non-choice nodes
        if ( pObj->pEquiv == NULL || pObj->nRefs == 0 )
            continue;
        // find driver cut
        vVec = NULL;
        for ( pTemp = pObj; pTemp; pTemp = pTemp->pEquiv )
            if ( p->pDriverCuts[pTemp->Id] != NULL )
            {
                vVec = Vec_IntDup( p->pDriverCuts[pTemp->Id] );
                break;
            }
        if ( vVec == NULL )
            continue;
        // transfer driver cut to the root node
        for ( pTemp = pObj; pTemp; pTemp = pTemp->pEquiv )
        {
            Vec_IntFreeP( &p->pDriverCuts[pTemp->Id] );
            p->pDriverCuts[pTemp->Id] = Vec_IntDup( vVec );
        }
        Vec_IntFree( vVec );
        Counter++;
    }
//    printf( "Choice driver cut updates = %d.\n", Counter );
}

/**Function*************************************************************

  Synopsis    [Frees PO drivers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFreePoDrivers( If_Man_t * p, Abc_Ntk_t * pNtk )
{
    If_Obj_t * pObj;
    If_Cut_t * pCut;
    int i;
    if ( p->pDriverCuts == NULL )
        return;
    pNtk->nRealDelay = p->RequiredGlo;
    if ( !Abc_FrameReadFlag("silentmode") )
        printf( "Actual delay after mapping = %.2f\n", p->RequiredGlo );
    assert( Abc_NtkPoNum(pNtk) == If_ManCoNum(p) - Abc_NtkLatchNum(pNtk) );
    // print the cut sizes of the drivers
    for ( i = pNtk->nRealPos; i <  Abc_NtkPoNum(pNtk); i += 5 )
    {
        pObj = If_ManCo( p, i + 4 );
        pObj = If_Regular(pObj->pFanin0);
        if ( !pObj->fDriver )
            continue;
        pCut = If_ObjCutBest(pObj);
//        printf( "%d(%d) ", pObj->Id, pCut->nLeaves );
    }
//    printf( "\n" );
    for ( i = 0; i < If_ManObjNum(p); i++ )
        Vec_IntFreeP( &p->pDriverCuts[i] );
    ABC_FREE( p->pDriverCuts );
}


/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkIfCheckTfi_rec( Abc_Obj_t * pNode, Abc_Obj_t * pOld )
{
    Abc_Obj_t * pFanin;
    int k;
    if ( pNode == NULL )
        return 0;
    if ( pNode == pOld )
        return 1;
    // check the trivial cases
    if ( Abc_ObjIsCi(pNode) )
        return 0; 
    assert( Abc_ObjIsNode(pNode) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return 0;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // check the children
    Abc_ObjForEachFanin( pNode, pFanin, k )
        if ( Abc_NtkIfCheckTfi_rec( pFanin, pOld ) )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkIfCheckTfi( Abc_Ntk_t * pNtk, Abc_Obj_t * pOld, Abc_Obj_t * pNew )
{
    assert( !Abc_ObjIsComplement(pOld) );
    assert( !Abc_ObjIsComplement(pNew) );
    Abc_NtkIncrementTravId(pNtk);
    return Abc_NtkIfCheckTfi_rec( pNew, pOld );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkIfCheckRealNodes( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i, iNode;
    for ( i = pNtk->nRealPos; i < Abc_NtkPoNum(pNtk); i += 5 )
    {
        iNode = Vec_IntEntry( pNtk->vRealNodes, i+3 - pNtk->nRealPos );
        pObj = Abc_NtkObj( pNtk, iNode );
        assert( Abc_ObjFaninNum(pObj) == 2 );

        iNode = Vec_IntEntry( pNtk->vRealNodes, i+4 - pNtk->nRealPos );
        pObj = Abc_NtkObj( pNtk, iNode );
        assert( Abc_ObjFaninNum(pObj) == 3 );
    }
}

/**Function*************************************************************

  Synopsis    [Restores the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecreatePoDrivers( If_Man_t * p, Abc_Ntk_t * pNtkNew )
{
    Abc_Obj_t * pNode, * pExor, * pObj, * pFanin, * pFaninNew;
    Vec_Ptr_t * vDrivers, * vDriversNew, * vFanins;
    Vec_Int_t * vInfo, * vNodeMap, * vDriverInvs;
    int i, k, numPo, nRealLuts, fCompl;
    float RealLutArea;
    if ( pNtkNew->vRealPos == NULL )
    {
        if ( !Abc_FrameReadFlag("silentmode") )
            printf( "Missing key information.\n" );
        return;
    }

    assert( pNtkNew->vRealNodes == NULL );
    // create drivers
    vDrivers = Vec_PtrStart( pNtkNew->nRealPos );
    vDriverInvs = Vec_IntStart( pNtkNew->nRealPos );
    pNtkNew->vRealNodes = Vec_IntAlloc( Abc_NtkPoNum(pNtkNew) - pNtkNew->nRealPos );
    for ( i = pNtkNew->nRealPos; i < Abc_NtkPoNum(pNtkNew); i++ )
    {
        pObj = Abc_NtkPo( pNtkNew, i );
        if ( Abc_ObjFaninC0(pObj) )
            pNode = Abc_NtkCreateNodeInv( pNtkNew, Abc_ObjFanin0(pObj) );
        else
            pNode = Abc_NtkCreateNodeBuf( pNtkNew, Abc_ObjFanin0(pObj) );
//        if ( i % 5 == 4 )
//            printf( "%d", Abc_ObjFaninC0(pObj) );
        Vec_PtrPush( vDrivers, pNode );
        Vec_IntPush( vDriverInvs, Abc_ObjFaninC0(pObj) );
        Vec_IntPush( pNtkNew->vRealNodes, Abc_ObjId(pNode) );
    }
    assert( Vec_PtrSize( vDrivers ) == Abc_NtkPoNum( pNtkNew ) );

    // create new logic
    vFanins = Vec_PtrAlloc( 2 );
    vDriversNew = Vec_PtrStart( Abc_NtkPoNum(pNtkNew) );
    Vec_VecForEachLevelInt( pNtkNew->vRealPos, vInfo, i )
    {
        // find complemented attribute
        numPo  = Vec_IntEntry( vInfo, 0 );
        fCompl = (strstr( Abc_ObjName(Abc_NtkPo(pNtkNew, numPo)), "SUB" ) != NULL);
        // consider parts
        Vec_IntForEachEntry( vInfo, numPo, k )
        {
            // update input
            if ( k > 0 )
                Vec_PtrWriteEntry( vDriversNew, numPo+2, pNode );
            // create first XOR
            Vec_PtrClear( vFanins );
            Vec_PtrPush( vFanins, (Abc_Obj_t *)Vec_PtrEntry(vDrivers, numPo+0) );
            Vec_PtrPush( vFanins, (Abc_Obj_t *)Vec_PtrEntry(vDrivers, numPo+1) );
            pExor = Abc_NtkCreateNodeExor( pNtkNew, vFanins );
            // update polarity
            pExor->pData = Hop_NotCond( (Hop_Obj_t *)pExor->pData, fCompl );
            // create second XOR
            Vec_PtrClear( vFanins );
            Vec_PtrPush( vFanins, pExor );
            Vec_PtrPush( vFanins, (Abc_Obj_t *)Vec_PtrEntry(vDrivers, numPo+2) ); 
            pNode = Abc_NtkCreateNodeExor( pNtkNew, vFanins );
            // update pointers
            Vec_PtrWriteEntry( vDriversNew, numPo+3, pNode );
            Vec_IntWriteEntry( pNtkNew->vRealNodes, numPo+3 - pNtkNew->nRealPos, Abc_ObjId(pNode) );
            // create MUX
            pNode = Abc_NtkCreateNodeMux( pNtkNew, pExor, 
                (Abc_Obj_t *)Vec_PtrEntry(vDrivers, numPo+2), 
                (Abc_Obj_t *)Vec_PtrEntry(vDrivers, numPo+(fCompl ? 0 : 1)) );
            // update pointers
            Vec_PtrWriteEntry( vDriversNew, numPo+4, pNode );
            Vec_IntWriteEntry( pNtkNew->vRealNodes, numPo+4 - pNtkNew->nRealPos, Abc_ObjId(pNode) );
        }
    }
    Vec_PtrFree( vFanins );

    Abc_NtkIfCheckRealNodes( pNtkNew );

    // map internal nodes into PO numbers
    vNodeMap = Vec_IntStartFull( Abc_NtkObjNumMax(pNtkNew) );
    Vec_VecForEachLevelInt( pNtkNew->vRealPos, vInfo, i )
    Vec_IntForEachEntryReverse( vInfo, numPo, k )
    {
        pObj = Abc_NtkPo( pNtkNew, numPo+3 );
        Vec_IntWriteEntry( vNodeMap, Abc_ObjId( Abc_ObjFanin0(pObj) ), numPo+3 );

        // update the PO pointer
//        if ( Abc_ObjFaninC0(pObj) )
//            Abc_ObjXorFaninC( pObj, 0 );
//       Abc_ObjPatchFanin( pObj, Abc_ObjFanin0(pObj), Vec_PtrEntry(vDriversNew, numPo+3) );

        pObj = Abc_NtkPo( pNtkNew, numPo+4 );
        Vec_IntWriteEntry( vNodeMap, Abc_ObjId( Abc_ObjFanin0(pObj) ), numPo+4 );

        // update the PO pointer
//        if ( Abc_ObjFaninC0(pObj) )
//            Abc_ObjXorFaninC( pObj, 0 );
//        Abc_ObjPatchFanin( pObj, Abc_ObjFanin0(pObj), Vec_PtrEntry(vDriversNew, numPo+4) );

    }

    // replace logic
    Abc_NtkForEachObj( pNtkNew, pObj, i )
    {
//        if ( Abc_ObjIsPo(pObj) )
//            continue;
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            if ( !Abc_ObjIsNode(pFanin) || Abc_ObjFaninNum(pFanin) == 0 )
                continue;
            numPo = Vec_IntEntry( vNodeMap, Abc_ObjId(pFanin) );
            if ( numPo == ~0 )
                continue;
            // get the node and the complemented bit
            pFaninNew = (Abc_Obj_t *)Vec_PtrEntry( vDriversNew, numPo );
            fCompl    = Vec_IntEntry( vDriverInvs, numPo );
            if ( fCompl )
                pFaninNew = Abc_NtkCreateNodeInv( pNtkNew, pFaninNew );
//            else
//                pFaninNew = Abc_NtkCreateNodeBuf( pNtkNew, pFaninNew );

            if ( !Abc_NtkIfCheckTfi( pNtkNew, pObj, pFaninNew ) )
                Abc_ObjPatchFanin( pObj, pFanin, pFaninNew );
        }
    }    

    // sweep
    Abc_NtkCleanupNodes( pNtkNew, vDriversNew, 0 );

    // make sure that all vDriversNew are still present
    {
        Abc_Obj_t * pObj;
        int i;
        Vec_PtrForEachEntry( Abc_Obj_t *, vDriversNew, pObj, i )
            if ( pObj && Abc_ObjIsNone(pObj) )
                assert( 0 );
    }

    Vec_PtrFree( vDrivers );
    Vec_PtrFree( vDriversNew );
    Vec_IntFree( vNodeMap );
    Vec_IntFree( vDriverInvs );

    // count non-trivial LUTs nodes
    nRealLuts   = -2 * Vec_VecSizeSize(pNtkNew->vRealPos);
    RealLutArea = -(p->pPars->pLutLib ? p->pPars->pLutLib->pLutAreas[2] + p->pPars->pLutLib->pLutAreas[3] : 2.0) * Vec_VecSizeSize(pNtkNew->vRealPos);
    Abc_NtkForEachNode( pNtkNew, pNode, i )
        if ( Abc_ObjFaninNum(pNode) > 1 )
        {
            nRealLuts++;
            RealLutArea += p->pPars->pLutLib->pLutAreas[Abc_ObjFaninNum(pNode)];
        }
    if ( !Abc_FrameReadFlag("silentmode") )
        printf( "The number of real LUTs = %d.  Real LUT area = %.2f.\n", nRealLuts, RealLutArea );
    pNtkNew->nRealLuts = nRealLuts;
    pNtkNew->nRealArea = RealLutArea;

    Abc_NtkIfCheckRealNodes( pNtkNew );

}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

