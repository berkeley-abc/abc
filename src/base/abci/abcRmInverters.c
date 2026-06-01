/**CFile****************************************************************

  FileName    [abcRmInverters.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Remove/Redistribute inverted edges on AIG nodes.]

  Author      [Jingren Wang]
  
  Affiliation [HKUST(GZ)]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRmInverters.c,v 1.00 2005/06/20 00:00:00 jingren Exp $]

***********************************************************************/

#include "aig/aig/aig.h"
#include "base/abc/abc.h"
#include "misc/util/abc_global.h"
#include "misc/vec/vecInt.h"
#include "misc/vec/vecPtr.h"
#include "opt/cut/cut.h"

ABC_NAMESPACE_IMPL_START

#define RDINV_SIM_SIZE 100

static unsigned int uMask[] = { 0x1, 0x3, 0xF, 0xFF, 0xFFFF, 0xFFFFFFFF };

extern void Abc_NtkMarkCriticalNodes( Abc_Ntk_t * pNtk );

/**Function*************************************************************

  Synopsis    [Collect cut leaves into a Vec_Ptr.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Ptr_t * Abc_RdInvCollectCutLeaves( Abc_Ntk_t * pNtk, Cut_Cut_t * pCut )
{
    Vec_Ptr_t * vLeaves = Vec_PtrAlloc( pCut->nLeaves );
    for ( int li = 0; li < pCut->nLeaves; li++ )
        Vec_PtrPush( vLeaves, Abc_NtkObj(pNtk, Cut_CutReadLeaves(pCut)[li]) );
    return vLeaves;
}

/**Function*************************************************************

  Synopsis    [Detect if function is self-dual.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
int AbcRmInvHasSelfDual( unsigned int uTruth, int fPhaseOri, unsigned int uTruthFlipped, int fPhaseFlipped, unsigned int uMsk )
{
    return (uTruth == uTruthFlipped && (fPhaseOri ^ fPhaseFlipped) == 1) ||
           (uTruth == (~uTruthFlipped & uMsk) && fPhaseOri == fPhaseFlipped);
}

/**Function*************************************************************

  Synopsis    [Detect if function is self-anti-dual.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
int AbcRmInvHasSelfAntiDual( unsigned int uTruth, int fPhaseOri, unsigned int uTruthFlipped, int fPhaseFlipped, unsigned int uMsk )
{
    return (uTruth == uTruthFlipped && fPhaseOri == fPhaseFlipped) ||
           (uTruth == (~uTruthFlipped & uMsk) && (fPhaseOri ^ fPhaseFlipped) == 1);
}

/**Function*************************************************************

  Synopsis    [Collect MFFC with support variables and internal nodes.]

  Description []
                
  SideEffects []

  SeeAlso     [abcMffc.c]

***********************************************************************/
void Abc_NodeMffcConeSuppCollect( Abc_Obj_t * pNode, Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp, int iVerbose )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NodeDeref_rec( pNode );
    Abc_NodeMffcConeSupp( pNode, vCone, vSupp );
    Abc_NodeRef_rec( pNode );
    if ( iVerbose )
    {
        printf( "Node = %6s : Supp = %3d  Cone = %3d  (", 
            Abc_ObjName(pNode), Vec_PtrSize(vSupp), Vec_PtrSize(vCone) );
        Vec_PtrForEachEntry( Abc_Obj_t *, vCone, pObj, i )
            printf( " %s", Abc_ObjName(pObj) );
        printf( " )\n" );
        printf("vSupp = (");
        Vec_PtrForEachEntry( Abc_Obj_t *, vSupp, pObj, i )
            printf( " %s", Abc_ObjName(pObj) );
        printf( " )\n" );
    }
}

/**Function*************************************************************

  Synopsis    [Get inverter count on support variables for self-anti-dual case.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRmInverterCountInvRatioSelfAntiDual( Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp, int * nLocalInv, int * nLocalInvOnCritical, int * nLocalNonInvOnCritical, int * nLocalSup )
{
    Abc_Obj_t * pObj, * pFanin;
    int i_cone, i_fanin;
    Vec_PtrForEachEntry( Abc_Obj_t *, vCone, pObj, i_cone )
    {
        Abc_ObjForEachFanin( pObj, pFanin, i_fanin )
        {
            if ( Vec_PtrFind(vSupp, pFanin) < 0 )
                continue;
            if ( (i_fanin == 0 && pObj->fCompl0) || (i_fanin == 1 && pObj->fCompl1) )
                (*nLocalInv)++;
            if ( (i_fanin == 0 && pObj->fCompl0 && pFanin->fMarkA) || (i_fanin == 1 && pObj->fCompl1 && pFanin->fMarkA) )
                (*nLocalInvOnCritical)++;
            if ( (i_fanin == 0 && !pObj->fCompl0 && pFanin->fMarkA) || (i_fanin == 1 && !pObj->fCompl1 && pFanin->fMarkA) )
                (*nLocalNonInvOnCritical)++;
            (*nLocalSup)++;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Get inverter count on support variables for self-dual case.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRmInverterCountInvRatioSelfDual( Abc_Obj_t * pNode, Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp, int * nLocalInv, int * nLocalInvOnCritical, int * nLocalNonInvOnCritical, int * nLocalSup )
{
    Abc_Obj_t * pFanout;
    int i;
    Abc_NtkRmInverterCountInvRatioSelfAntiDual( vCone, vSupp, nLocalInv, nLocalInvOnCritical, nLocalNonInvOnCritical, nLocalSup );
    Abc_ObjForEachFanout( pNode, pFanout, i )
    {
        int fCompl = (Abc_ObjFanin0(pFanout) == pNode) ? pFanout->fCompl0 : pFanout->fCompl1;
        *nLocalInv += fCompl;
        int fIsCritical = (Abc_ObjFanin0(pFanout) == pNode)
            ? (Abc_ObjFanin0(pFanout)->fMarkA == 1)
            : (Abc_ObjFanin1(pFanout)->fMarkA == 1);
        if ( fCompl && fIsCritical )
            (*nLocalInvOnCritical)++;
        else if ( !fCompl && fIsCritical )
            (*nLocalNonInvOnCritical)++;
        (*nLocalSup)++;
    }
}

/**Function*************************************************************

  Synopsis    [Flip inverters on self-anti-dual function.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRmInverterFlipInvSelfAntiDual( Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp )
{
    Abc_Obj_t * pObj, * pFanin;
    int i_cone, i_fanin;
    Vec_PtrForEachEntry( Abc_Obj_t *, vCone, pObj, i_cone )
    {
        Abc_ObjForEachFanin( pObj, pFanin, i_fanin )
        {
            if ( Vec_PtrFind(vSupp, pFanin) < 0 )
                continue;
            if ( i_fanin == 0 )
                pObj->fCompl0 ^= 1;
            else if ( i_fanin == 1 )
                pObj->fCompl1 ^= 1;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Flip inverters on self-dual function.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRmInverterFlipInvSelfDual( Abc_Obj_t * pNode, Vec_Ptr_t * vCone, Vec_Ptr_t * vSupp )
{
    Abc_Obj_t * pFanout;
    int i;
    Abc_NtkRmInverterFlipInvSelfAntiDual( vCone, vSupp );
    Abc_ObjForEachFanout( pNode, pFanout, i )
    {
        Abc_ObjFanin0(pFanout) == pNode ? (pFanout->fCompl0 ^= 1) : (pFanout->fCompl1 ^= 1);
    }
}

/**Function*************************************************************

  Synopsis    [Simulate AIG nodes and compute truth tables.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ManResubSimulateComp( Vec_Ptr_t * vDivs, int nLeaves, Vec_Ptr_t * vSims, int nLeavesMax, int nWords )
{
    Abc_Obj_t * pObj;
    unsigned * puData0, * puData1, * puData;
    int i, k;
    assert( Vec_PtrSize(vDivs) - nLeaves <= Vec_PtrSize(vSims) - nLeavesMax );
    Vec_PtrForEachEntry( Abc_Obj_t *, vDivs, pObj, i )
    {
        if ( i < nLeaves )
        {
            pObj->pDataComp = Vec_PtrEntry( vSims, i );
            continue;
        }
        pObj->pDataComp = Vec_PtrEntry( vSims, i - nLeaves + nLeavesMax );
        puData  = (unsigned *)pObj->pDataComp;
        puData0 = (unsigned *)Abc_ObjFanin0(pObj)->pDataComp;
        puData1 = (unsigned *)Abc_ObjFanin1(pObj)->pDataComp;
        if ( Abc_ObjFaninC0(pObj) && Abc_ObjFaninC1(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & ~puData1[k];
        else if ( Abc_ObjFaninC0(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & puData1[k];
        else if ( Abc_ObjFaninC1(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & ~puData1[k];
        else 
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & puData1[k];
    }
    Vec_PtrForEachEntry( Abc_Obj_t *, vDivs, pObj, i )
    {
        puData = (unsigned *)pObj->pDataComp;
        pObj->fPhase = (puData[0] & 1);
        if ( pObj->fPhase )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData[k];
    }
}

/**Function*************************************************************

  Synopsis    [Clean pDataComp on cone nodes.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCleanDataComp( Vec_Ptr_t * vCone )
{
    Abc_Obj_t * pObj;
    int i;
    Vec_PtrForEachEntry( Abc_Obj_t *, vCone, pObj, i )
        pObj->pDataComp = NULL;
}

/**Function*************************************************************

  Synopsis    [Simulate a cut to extract truth + phase for one polarity.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void AbcRmInvSimCuts( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, Cut_Cut_t * pCut, int nMaxLeaves, unsigned int * uNodeVal, int * fPhaseFlipped, unsigned int * pInfo, Vec_Ptr_t * vSims )
{
    Abc_Obj_t * pObj;
    int nVar = pCut->nLeaves;
    int nBits  = (1 << nVar);
    int nWords = (nBits <= 32) ? 1 : (nBits / 32);

    Vec_Ptr_t * vCone = Vec_PtrAlloc( pCut->nLeaves + 16 );
    Vec_Ptr_t * vSup  = Vec_PtrAlloc( pCut->nLeaves );
    for ( int li = 0; li < pCut->nLeaves; li++ )
    {
        pObj = Abc_NtkObj( pNtk, Cut_CutReadLeaves(pCut)[li] );
        Vec_PtrPush( vSup, pObj );
        Vec_PtrPush( vCone, pObj );
    }
    assert( Vec_PtrSize(vSup) == pCut->nLeaves );

    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkDfsSup_rec( pNode, vCone, vSup, 0 );
    assert( Vec_PtrSize(vCone) > pCut->nLeaves );

    Vec_Int_t * vPh = Vec_IntAlloc( Vec_PtrSize(vCone) );
    Abc_Obj_t * pEntry;
    int iPh;
    Vec_PtrForEachEntry( Abc_Obj_t *, vCone, pEntry, iPh )
        Vec_IntPush( vPh, pEntry->fPhase );

    Abc_ManResubSimulateComp( vCone, nVar, vSims, nMaxLeaves, nWords );
    unsigned int uNode = (*((unsigned int *)(pNode->pDataComp)));
    *uNodeVal = uNode & uMask[nVar];
    *fPhaseFlipped = pNode->fPhase;

    Abc_NtkCleanDataComp( vCone );

    Vec_PtrForEachEntry( Abc_Obj_t *, vCone, pEntry, iPh )
        pEntry->fPhase = Vec_IntEntry( vPh, iPh );

    Vec_IntFree( vPh );
    Vec_PtrFree( vCone );
    Vec_PtrFree( vSup );
}

/**Function*************************************************************

  Synopsis    [Compute original and flipped truth/phase pair for a cut.]

  Description [Allocates and frees simulation arrays internally.
               Returns 1 on success, 0 if cut is too large.]
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_RdInvComputeTruthPair( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, Cut_Cut_t * pCut,
    unsigned * uTruthOri, int * fPhaseOri,
    unsigned * uTruthFlipped, int * fPhaseFlipped )
{
    int nVar   = pCut->nLeaves;
    int nBits  = (1 << nVar);
    int nWords = (nBits <= 32) ? 1 : (nBits / 32);
    int in, k;

    Vec_Ptr_t * vSims = Vec_PtrAlloc( RDINV_SIM_SIZE );
    unsigned int *pInfo = ABC_ALLOC( unsigned, nWords * (RDINV_SIM_SIZE + 1) );
    for ( in = 0; in < RDINV_SIM_SIZE; in++ )
        Vec_PtrPush( vSims, pInfo + in * nWords );

    for ( k = 0; k < nVar; k++ )
    {
        unsigned * pData = (unsigned *)vSims->pArray[k];
        Abc_InfoClear( pData, nWords );
        for ( in = 0; in < nBits; in++ )
            if ( in & (1 << k) )
                pData[in >> 5] |= (1 << (in & 31));
    }
    AbcRmInvSimCuts( pNtk, pNode, pCut, 5, uTruthOri, fPhaseOri, pInfo, vSims );
    Vec_PtrFree( vSims );
    ABC_FREE( pInfo );

    vSims = Vec_PtrAlloc( RDINV_SIM_SIZE );
    pInfo = ABC_ALLOC( unsigned, nWords * (RDINV_SIM_SIZE + 1) );
    for ( in = 0; in < RDINV_SIM_SIZE; in++ )
        Vec_PtrPush( vSims, pInfo + in * nWords );

    for ( k = 0; k < nVar; k++ )
    {
        unsigned * pData = (unsigned *)vSims->pArray[k];
        Abc_InfoClear( pData, nWords );
        for ( in = 0; in < nBits; in++ )
            if ( !(in & (1 << k)) )
                pData[in >> 5] |= (1 << (in & 31));
    }
    AbcRmInvSimCuts( pNtk, pNode, pCut, 5, uTruthFlipped, fPhaseFlipped, pInfo, vSims );
    Vec_PtrFree( vSims );
    ABC_FREE( pInfo );

    assert( (*uTruthOri & uMask[nVar]) == *uTruthOri );
    assert( (*uTruthFlipped & uMask[nVar]) == *uTruthFlipped );
}

/**Function*************************************************************

  Synopsis    [Check if cut is self-dual.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRmInvCutIsSelfDual( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, Cut_Cut_t * pCut )
{
    unsigned uTruthOri, uTruthFlipped;
    int fPhaseOri, fPhaseFlipped;
    Abc_RdInvComputeTruthPair( pNtk, pNode, pCut, &uTruthOri, &fPhaseOri, &uTruthFlipped, &fPhaseFlipped );
    return AbcRmInvHasSelfDual( uTruthOri, fPhaseOri, uTruthFlipped, fPhaseFlipped, uMask[pCut->nLeaves] );
}

/**Function*************************************************************

  Synopsis    [Check if cut is self-anti-dual.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRmInvCutIsSelfAntiDual( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, Cut_Cut_t * pCut )
{
    unsigned uTruthOri, uTruthFlipped;
    int fPhaseOri, fPhaseFlipped;
    Abc_RdInvComputeTruthPair( pNtk, pNode, pCut, &uTruthOri, &fPhaseOri, &uTruthFlipped, &fPhaseFlipped );
    return AbcRmInvHasSelfAntiDual( uTruthOri, fPhaseOri, uTruthFlipped, fPhaseFlipped, uMask[pCut->nLeaves] );
}

/**Function*************************************************************

  Synopsis    [Get valid cuts of self-dual and self-anti-dual.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void AbcRmInvAvaCuts( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, Cut_Man_t * pCutMan, Vec_Ptr_t * vASDCuts, Vec_Ptr_t * vASADCuts, int iVerbose )
{
    int nCuts = 0;
    Vec_Ptr_t * vCutsPreSD  = Vec_PtrAlloc( 16 );
    Vec_Ptr_t * vCutsPreSAD = Vec_PtrAlloc( 16 );
    Cut_Cut_t * pCut;
    pCut = (Cut_Cut_t *)Abc_NodeGetCutsRecursive( pCutMan, pNode, 0, 1 );
    if ( pCut == NULL )
    {
        printf("Warning: Abc_NodeGetCutsRecursive returned NULL for node %d\n", Abc_ObjId(pNode));
        Vec_PtrFree( vCutsPreSD );
        Vec_PtrFree( vCutsPreSAD );
        return;
    }
    for ( pCut = pCut->pNext; pCut; pCut = pCut->pNext )
    {
        if ( Abc_NtkRmInvCutIsSelfDual(pNtk, pNode, pCut) )
            Vec_PtrPush( vCutsPreSD, pCut );
        if ( Abc_NtkRmInvCutIsSelfAntiDual(pNtk, pNode, pCut) )
            Vec_PtrPush( vCutsPreSAD, pCut );
        nCuts++;
    }
    Vec_PtrCopy( vASADCuts, vCutsPreSAD );
    Vec_PtrCopy( vASDCuts, vCutsPreSD );
    if ( iVerbose )
    {
        printf("    %d cuts have been found and processed.\n", nCuts);
        printf("    Retrieved %d(%d) of cuts in self-anti-dual and %d(%d) of cuts in self-dual.\n",
            Vec_PtrSize(vASADCuts), Vec_PtrSize(vCutsPreSAD),
            Vec_PtrSize(vASDCuts), Vec_PtrSize(vCutsPreSD));
    }
    Vec_PtrFree( vCutsPreSD );
    Vec_PtrFree( vCutsPreSAD );
}

/**Function*************************************************************

  Synopsis    [Show cut structure for verbose output.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_RmInvShowCutStructure( Abc_Ntk_t * pNtk, Abc_Obj_t * pRoot, Cut_Cut_t * pCut )
{
    Vec_Ptr_t * vCone = Vec_PtrAlloc( pCut->nLeaves + 16 );
    Vec_Ptr_t * vSup  = Abc_RdInvCollectCutLeaves( pNtk, pCut );
    int li;
    for ( li = 0; li < pCut->nLeaves; li++ )
        Vec_PtrPush( vCone, Abc_NtkObj(pNtk, Cut_CutReadLeaves(pCut)[li]) );
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkDfsSup_rec( pRoot, vCone, vSup, 1 );
    Vec_PtrFree( vSup );
    Vec_PtrFree( vCone );
}

/**Function*************************************************************

  Synopsis    [Retrieve max level slack.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void AbcRmInvFetchMaxLSlack( Abc_Ntk_t * pNtk, int * iLSM )
{
    int i = 0;
    Abc_Obj_t * pNode;
    Vec_Int_t * vLS = Vec_IntAlloc( Abc_NtkNodeNum(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        int item = Abc_ObjRequiredLevel(pNode) - pNode->Level;
        Vec_IntPush( vLS, item );
    }
    Vec_IntSort( vLS, 1 );
    assert( Vec_IntEntry(vLS, 0) >= Vec_IntEntry(vLS, Vec_IntSize(vLS) - 1) );
    *iLSM = Vec_IntEntry( vLS, 0 );
    Vec_IntFree( vLS );
}

/**Function*********************************************************

  Synopsis    [Retrieve critical and near-critical edges count.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void AbcRmInvCollectNCE( Abc_Ntk_t * pNtk, int iThreshold, int * iCount )
{
    Abc_Obj_t * pNode, * pFanin, * pPo;
    int i, j, k;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_ObjRequiredLevel(pNode) - pNode->Level <= iThreshold )
        {
            Abc_ObjForEachFanin( pNode, pFanin, j )
            {
                *iCount += (j == 0) ? pNode->fCompl0 : pNode->fCompl1;
            }
        }
    }
    Abc_NtkForEachPo( pNtk, pPo, k )
    {
        Abc_Obj_t * pNodeToPo = Abc_ObjFanin0(pPo);
        if ( pPo->fCompl0 && Abc_ObjIsNode(pNodeToPo) && (Abc_ObjRequiredLevel(pNodeToPo) - pNodeToPo->Level <= iThreshold) )
            (*iCount)++;
    }
}

/**Function*************************************************************

  Synopsis    [Use markB to record level slack, markA for critical flag.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMarkCriticalNodesScale( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, Counter = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_ObjRequiredLevel(pNode) - pNode->Level <= 1 )
        {
            pNode->fMarkA = 1;
            pNode->fMarkB = Abc_ObjRequiredLevel(pNode) - pNode->Level;
            Counter++;
        }
    }
    printf( "The number of nodes on the critical paths = %6d  (%5.2f %%)\n", Counter, 100.0 * Counter / Abc_NtkNodeNum(pNtk) );
}

/**Function*************************************************************

  Synopsis    [Record sum of slack with inverted edges.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCollectInvRelatedSlack( Abc_Ntk_t * pNtk, int * invSlack )
{
    Abc_Obj_t * pNode, * pFanin;
    int i, j;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Abc_ObjForEachFanin( pNode, pFanin, j )
        {
            if ( j == 0 && pNode->fCompl0 == 1 )
                (*invSlack) += pFanin->fMarkB;
            if ( j == 1 && pNode->fCompl1 == 1 )
                (*invSlack) += pFanin->fMarkB;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Process cuts: evaluate gain condition and flip if beneficial.]

  Description [Shared logic for self-anti-dual and self-dual cut processing.
               fIsSelfDual=0 treats SAD; fIsSelfDual=1 treats SD.]
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_RdInvProcessCuts( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode,
    Vec_Ptr_t * vCone, Vec_Ptr_t * vCuts, int fIsSelfDual,
    int * nCountCritical, int * nCountNonCritical, int * nCount, int iVerbose )
{
    Cut_Cut_t * pCut;
    int i;
    Vec_PtrForEachEntry( Cut_Cut_t *, vCuts, pCut, i )
    {
        int nLocalInv = 0;
        int nLocalSup = 0;
        int nLocalInvOnCritical = 0;
        int nLocalNonInvOnCritical = 0;

        Vec_Ptr_t * vSupCuts = Abc_RdInvCollectCutLeaves( pNtk, pCut );

        if ( fIsSelfDual )
            Abc_NtkRmInverterCountInvRatioSelfDual( pNode, vCone, vSupCuts, &nLocalInv, &nLocalInvOnCritical, &nLocalNonInvOnCritical, &nLocalSup );
        else
            Abc_NtkRmInverterCountInvRatioSelfAntiDual( vCone, vSupCuts, &nLocalInv, &nLocalInvOnCritical, &nLocalNonInvOnCritical, &nLocalSup );

        int fCheckCritical    = (nLocalInvOnCritical > nLocalNonInvOnCritical);
        int fCheckNonCritical = (nLocalInvOnCritical == 0 && nLocalNonInvOnCritical == 0 && nLocalSup > 0 && (float)nLocalInv / nLocalSup >= 0.5);

        if ( fCheckCritical || fCheckNonCritical )
        {
            if ( fCheckCritical )
                (*nCountCritical)++;
            if ( fCheckNonCritical )
                (*nCountNonCritical)++;

            if ( iVerbose )
                Abc_RmInvShowCutStructure( pNtk, pNode, pCut );

            if ( fIsSelfDual )
                Abc_NtkRmInverterFlipInvSelfDual( pNode, vCone, vSupCuts );
            else
                Abc_NtkRmInverterFlipInvSelfAntiDual( vCone, vSupCuts );

            (*nCount)++;
        }
        Vec_PtrFree( vSupCuts );
    }
}

/**Function*************************************************************

  Synopsis    [Gain-based inverter removal.]

  Description []
                
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRmInverter( Abc_Ntk_t * pNtk, int iVerbose )
{
    int i;
    Abc_Obj_t * pNode, * pObj;

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        printf("Error: Abc_NtkRmInverter requires a strashed AIG network.\n");
        printf("Current network type: %d\n", pNtk->ntkType);
        return;
    }
    if ( iVerbose )
    {
        printf("Processing strashed AIG network with %d nodes, %d PIs, %d POs\n",
            Abc_NtkNodeNum(pNtk), Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk));
        printf("Network level: %d\n", Abc_NtkLevel(pNtk));
    }

    Abc_NtkStartReverseLevels( pNtk, 0 );
    Abc_NtkMarkCriticalNodesScale( pNtk );

    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_AigNodeIsChoice(pNode) )
        {
            Abc_Obj_t * pCurTempNode = (Abc_Obj_t *)pNode->pData;
            while ( pCurTempNode != NULL )
            {
                pCurTempNode->fMarkA = 1;
                pCurTempNode->fMarkB = pNode->fMarkB;
                pCurTempNode = (Abc_Obj_t *)pCurTempNode->pData;
            }
        }
    }

    int iNCEBefore = 0;
    int iNCEAfter = 0;
    int invSlackBefore = 0;
    int invSlackAfter = 0;
    int iLSM = 0;
    AbcRmInvFetchMaxLSlack( pNtk, &iLSM );
    int iThreshold = iLSM;
    AbcRmInvCollectNCE( pNtk, iThreshold, &iNCEBefore );
    Abc_NtkCollectInvRelatedSlack( pNtk, &invSlackBefore );

    int nCountCriticalSAD = 0;
    int nCountNonCriticalSAD = 0;
    int nCountSAD = 0;
    int nCountCriticalSD = 0;
    int nCountNonCriticalSD = 0;
    int nCountSD = 0;
    int nTotalNodes = Abc_NtkNodeNum(pNtk);
    int nProcessed = 0;

    {
        Cut_Man_t * pCutMan;
        Cut_Params_t Params, * pParams = &Params;
        memset( pParams, 0, sizeof(Cut_Params_t) );
        pParams->nVarsMax  = 5;
        pParams->nKeepMax  = 250;
        pParams->fTruth    = 1;
        pParams->fFilter   = 1;
        pParams->fSeq      = 0;
        pParams->fLocal    = 0;
        pParams->fGlobal   = 0;
        pParams->fTree     = 1;
        pParams->fDrop     = 0;
        pParams->fVerbose  = 1;
        pParams->nIdsMax   = Abc_NtkObjNumMax( pNtk );
        pCutMan = Cut_ManStart( pParams );

        int j_ci;
        Abc_NtkForEachCi( pNtk, pObj, j_ci )
            if ( Abc_ObjFanoutNum(pObj) > 0 )
                Cut_NodeSetTriv( pCutMan, pObj->Id );

        Abc_NtkForEachNode( pNtk, pNode, i )
        {
            if ( Abc_ObjFanoutNum(pNode) == 1 && pNode->pData != NULL )
                continue;

            Vec_Ptr_t * vCone = Vec_PtrAlloc( 16 );
            Vec_Ptr_t * vSupp = Vec_PtrAlloc( 16 );

            if ( iVerbose )
                printf("\n\n\n");

            Abc_NodeMffcConeSuppCollect( pNode, vCone, vSupp, iVerbose );

            int i_sup;
            Vec_PtrForEachEntryReverse( Abc_Obj_t *, vSupp, pObj, i_sup )
                Vec_PtrInsert( vCone, 0, pObj );

            if ( iVerbose )
                printf("Support var size %d, internal node size %d\n", Vec_PtrSize(vSupp), Vec_PtrSize(vCone));

            Vec_Ptr_t * vASDCuts  = Vec_PtrAlloc( 16 );
            Vec_Ptr_t * vASADCuts = Vec_PtrAlloc( 16 );

            AbcRmInvAvaCuts( pNtk, pNode, pCutMan, vASDCuts, vASADCuts, iVerbose );

            int nSADBefore = nCountSAD;
            Abc_RdInvProcessCuts( pNtk, pNode, vCone, vASADCuts, 0,
                &nCountCriticalSAD, &nCountNonCriticalSAD, &nCountSAD, iVerbose );

            int nSDBefore = nCountSD;
            Abc_RdInvProcessCuts( pNtk, pNode, vCone, vASDCuts, 1,
                &nCountCriticalSD, &nCountNonCriticalSD, &nCountSD, iVerbose );

            if ( nCountSAD > nSADBefore || nCountSD > nSDBefore )
                nProcessed++;

            Vec_PtrFree( vASADCuts );
            Vec_PtrFree( vASDCuts );
            Vec_PtrFree( vCone );
            Vec_PtrFree( vSupp );
        }
        Cut_ManStop( pCutMan );
    }

    AbcRmInvCollectNCE( pNtk, iThreshold, &iNCEAfter );
    Abc_NtkCollectInvRelatedSlack( pNtk, &invSlackAfter );

    if ( iVerbose )
    {
        printf("=====Statistics about invNum with Threshold %d=====\n", iThreshold);
        printf("Before %d   After %d    Gain %d \n", iNCEBefore, iNCEAfter, iNCEBefore - iNCEAfter);
        if ( iNCEAfter > 0 || iNCEBefore > 0 )
            printf("=====Statistics about edges that ease on slack=====\n"
                   "Ease Gain %f \n", (float)invSlackAfter / (iNCEAfter ? iNCEAfter : 1) - (float)invSlackBefore / (iNCEBefore ? iNCEBefore : 1));
    }

    Abc_NtkStopReverseLevels( pNtk );
    Abc_NtkCleanMarkAB( pNtk );

    assert( nCountCriticalSAD + nCountNonCriticalSAD == nCountSAD );
    assert( nCountCriticalSD + nCountNonCriticalSD == nCountSD );

    printf("Total %d self-anti-dual functions", nCountSAD);
    if ( nCountSAD > 0 )
        printf(", Critical(%f), Non-critical(%f)", (float)nCountCriticalSAD / nCountSAD, (float)nCountNonCriticalSAD / nCountSAD);
    printf(" / %d self-dual are modified", nCountSD);
    if ( nCountSD > 0 )
        printf(", Critical(%f), Non-critical(%f)", (float)nCountCriticalSD / nCountSD, (float)nCountNonCriticalSD / nCountSD);
    printf(". Total process rate %f\n", nTotalNodes > 0 ? (float)nProcessed / nTotalNodes : 0.0f);
}

ABC_NAMESPACE_IMPL_END
