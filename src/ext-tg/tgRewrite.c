#include "tgLog.h"
/**CFile****************************************************************

  FileName    [tgRewrite.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Placement-aware copy of ABC's DAG-aware AIG rewriting pass.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRewrite.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "tgVisit.h"
#include "base/abc/abc.h"
#include "opt/rwr/rwr.h"
#include "bool/dec/dec.h"

#include "tgEvaluate.h"

#include "tgPlace.h"

ABC_NAMESPACE_IMPL_START
static Rwr_Man_t *s_RewriteManager = NULL;
void Tg_ClearRewriteCache(void)
{
    if (s_RewriteManager)
        Rwr_ManStop(s_RewriteManager);
    s_RewriteManager = NULL;
}

static const unsigned char *coRwMask = 0;
static int coRwLimit = 0;
void Tg_RwSetMask(const unsigned char *mask, int limit)
{
    coRwMask = mask;
    coRwLimit = limit;
}

/* online priority-bucket filter.  Roots are visited in the normal ID order;
   a root is skipped when its tension-priority bucket has a Laplace-smoothed commit
   rate below rho times the pass's overall smoothed rate. */
static const unsigned char *coRwBucket = 0;
static int coRwBucketSize = 0, coRwBuckets = 0;
static double coRwBucketRho = 0;
static unsigned char *coRwAttempted = 0;
static int coRwBucketSkipped = 0, coRwBucketClosed = 0;
void Tg_RwSetBuckets(const unsigned char *bucket, int size, int buckets, double rho,
                     unsigned char *attempted)
{
    coRwBucket = bucket;
    coRwBucketSize = size;
    coRwBuckets = buckets;
    coRwBucketRho = rho;
    coRwAttempted = attempted;
    coRwBucketSkipped = 0;
    coRwBucketClosed = 0;
}
int Tg_RwBucketStats(int *closed)
{
    if (closed)
        *closed = coRwBucketClosed;
    return coRwBucketSkipped;
}

extern int TgEval_RwrNodeRewrite(Rwr_Man_t *, Cut_Man_t *, Abc_Obj_t *, int, int, int);

/*
    The ideas realized in this package are inspired by the paper:
    Per Bjesse, Arne Boralv, "DAG-aware circuit compression for
    formal verification", Proc. ICCAD 2004, pp. 42-49.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Cut_Man_t *Abc_NtkStartCutManForRewrite(Abc_Ntk_t *pNtk);

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs incremental rewriting of the AIG.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int TgEval_NtkRewrite(Abc_Ntk_t *pNtk, int fUpdateLevel, int fUseZeros, int fVerbose,
                      int fVeryVerbose, int fPlaceEnable)
{
    extern int Dec_GraphUpdateNetwork(Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int fUpdateLevel,
                                      int nGain);
    ProgressBar *pProgress;
    Cut_Man_t *pManCut;
    Rwr_Man_t *pManRwr;
    Abc_Obj_t *pNode;
    //    Vec_Ptr_t * vAddedCells = NULL, * vUpdatedNets = NULL;
    Dec_Graph_t *pGraph;
    int i, nNodes, nGain, fCompl, RetValue = 1;
    abctime clk, clkStart = Abc_Clock();

    assert(Abc_NtkIsStrash(pNtk));
    if (fPlaceEnable && !Tg_ManHasPlacement(pNtk))
    {
        Abc_Print(-1, "pa_rw: run pa_place on the current AIG first.\n");
        return -1;
    }
    // cleanup the AIG
    Abc_AigCleanup((Abc_Aig_t *)pNtk->pManFunc);
    if (fPlaceEnable && !Tg_ManBeginPass(pNtk))
    {
        Abc_Print(-1, "pa_rw: AIG cleanup changed the placed graph; rerun pa_place.\n");
        return -1;
    }
    if (fPlaceEnable && !TgEval_ManPrepareTimingPass(pNtk))
    {
        Abc_Print(-1, "pa_rw -t: could not initialize timing from placement.\n");
        Tg_ManEndPass(pNtk);
        return -1;
    }
    /*
        {
            Vec_Vec_t * vParts;
            vParts = Abc_NtkPartitionSmart( pNtk, 50, 1 );
            Vec_VecFree( vParts );
        }
    */

    // start placement package
    //    if ( fPlaceEnable )
    //    {
    //        Abc_PlaceBegin( pNtk );
    //        vAddedCells = Abc_AigUpdateStart( pNtk->pManFunc, &vUpdatedNets );
    //    }

    // start the rewriting manager
    /* reuse one rewriting manager across passes.  Its forest and class
       tables do not depend on the network; per-pass fields are verbose-only
       statistics and monotonic traversal IDs. */

    const int reuseRewriteManager = ((char *)"1") != NULL;
    if (reuseRewriteManager && s_RewriteManager)
        pManRwr = s_RewriteManager;
    else
    {
        pManRwr = Rwr_ManStart(0);
        s_RewriteManager = pManRwr;
    }
    if (pManRwr == NULL)
    {
        if (fPlaceEnable)
            Tg_ManEndPass(pNtk);
        return 0;
    }
    // compute the reverse levels if level update is requested
    if (fUpdateLevel)
        Abc_NtkStartReverseLevels(pNtk, 0);
    // start the cut manager
    clk = Abc_Clock();
    pManCut = Abc_NtkStartCutManForRewrite(pNtk);
    Rwr_ManAddTimeCuts(pManRwr, Abc_Clock() - clk);
    pNtk->pManCut = pManCut;

    if (fVeryVerbose)
        Rwr_ScoresClean(pManRwr);

    // resynthesize each node once
    int coVisitCount = 0;
    const int *coVisitOrder = Tg_ReadVisitOrder(&coVisitCount);
    int bucketN[256] = {0}, bucketK[256] = {0}, bucketClosed[256] = {0}, bucketAllN = 0,
        bucketAllK = 0, bucketCurrent = -1;

    pManRwr->nNodesBeg = Abc_NtkNodeNum(pNtk);
    nNodes = Abc_NtkObjNumMax(pNtk);
    pProgress = Extra_ProgressBarStart(stdout, nNodes);
    Tg_NtkForEachVisit(pNtk, pNode, i, coVisitOrder, coVisitCount)
    {
        Extra_ProgressBarUpdate(pProgress, i, NULL);
        if (coRwMask && (pNode->Id >= coRwLimit || !coRwMask[pNode->Id]))
            continue;
        // stop if all nodes have been tried once
        if (i >= nNodes)
            break;
        // skip persistant nodes
        if (Abc_NodeIsPersistant(pNode))
            continue;
        // skip the nodes with many fanouts
        if (Abc_ObjFanoutNum(pNode) > 1000)
            continue;
        bucketCurrent = -1;
        if (coRwBucket && pNode->Id < coRwBucketSize)
        {
            bucketCurrent = coRwBucket[pNode->Id];
            if (bucketCurrent >= coRwBuckets || bucketClosed[bucketCurrent])
            {
                ++coRwBucketSkipped;
                continue;
            }
            if (coRwAttempted)
                coRwAttempted[pNode->Id] = 1;
        }

        // for each cut, try to resynthesize it
        nGain =
            TgEval_RwrNodeRewrite(pManRwr, pManCut, pNode, fUpdateLevel, fUseZeros, fPlaceEnable);
        if (bucketCurrent >= 0)
        {
            int bc = bucketCurrent;
            ++bucketN[bc];
            ++bucketAllN;
            if (!(fPlaceEnable ? nGain == -ABC_INFINITY
                               : !(nGain > 0 || (nGain == 0 && fUseZeros))))
            {
                ++bucketK[bc];
                ++bucketAllK;
            }
            /* close the bucket when its smoothed rate falls below rho x overall smoothed rate */
            if ((bucketK[bc] + 1.0) / (bucketN[bc] + 2.0) <
                coRwBucketRho * (bucketAllK + 1.0) / (bucketAllN + 2.0))
            {
                bucketClosed[bc] = 1;
                ++coRwBucketClosed;
            }
            bucketCurrent = -1; /* commit counted here, not again below */
        }
        if (fPlaceEnable ? nGain == -ABC_INFINITY : !(nGain > 0 || (nGain == 0 && fUseZeros)))
            continue;
        // if we end up here, a rewriting step is accepted

        // get hold of the new subgraph to be added to the AIG
        pGraph = (Dec_Graph_t *)Rwr_ManReadDecs(pManRwr);
        fCompl = Rwr_ManReadCompl(pManRwr);

        // complement the FF if needed
        if (fCompl)
            Dec_GraphComplement(pGraph);
        clk = Abc_Clock();
        if (!(fPlaceEnable
                  ? TgEval_ManCommitCandidate(pNode, pGraph, pManRwr->vFanins, fUpdateLevel, nGain)
                  : Dec_GraphUpdateNetwork(pNode, pGraph, fUpdateLevel, nGain)))
        {
            RetValue = -1;
            break;
        }
        if (bucketCurrent >= 0)
        {
            ++bucketK[bucketCurrent];
            ++bucketAllK;
        }

        Rwr_ManAddTimeUpdate(pManRwr, Abc_Clock() - clk);
        if (fCompl)
            Dec_GraphComplement(pGraph);

        // use the array of changed nodes to update placement
        //        if ( fPlaceEnable )
        //            Abc_PlaceUpdate( vAddedCells, vUpdatedNets );
    }
    Extra_ProgressBarStop(pProgress);
    Rwr_ManAddTimeTotal(pManRwr, Abc_Clock() - clkStart);
    // print stats
    pManRwr->nNodesEnd = Abc_NtkNodeNum(pNtk);
    if (fVerbose)
        Rwr_ManPrintStats(pManRwr);
    //        Rwr_ManPrintStatsFile( pManRwr );
    if (fVeryVerbose)
        Rwr_ScoresReport(pManRwr);
    // delete the managers

    Cut_ManStop(pManCut);
    pNtk->pManCut = NULL;

    // start placement package
    //    if ( fPlaceEnable )
    //    {
    //        Abc_PlaceEnd( pNtk );
    //        Abc_AigUpdateStop( pNtk->pManFunc );
    //    }

    // put the nodes into the DFS order and reassign their IDs
    if (fPlaceEnable && !Tg_ManBeginEdit(pNtk))
        RetValue = -1;
    {
        //        abctime clk = Abc_Clock();
        if (!Tg_InFlight())
            Abc_NtkReassignIds(pNtk);
        //        ABC_PRT( "time", Abc_Clock() - clk );
    }
    if (fPlaceEnable && RetValue >= 0 && !Tg_ManFinishEdit(pNtk))
        RetValue = -1;
    if (fPlaceEnable && RetValue >= 0 && !Tg_ManEndPass(pNtk))
        RetValue = -1;
    if (fPlaceEnable && RetValue < 0)
        Tg_ManClearPlacement();
    //    Abc_AigCheckFaninOrder( pNtk->pManFunc );
    // fix the levels
    if (RetValue >= 0)
    {
        if (fUpdateLevel)
            Abc_NtkStopReverseLevels(pNtk);
        else
            Abc_NtkLevel(pNtk);
        // check
        if (!Abc_NtkCheck(pNtk))
        {
            printf("TgEval_NtkRewrite: The network check has failed.\n");
            return 0;
        }
    }
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Starts the cut manager for rewriting.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Man_t *Abc_NtkStartCutManForRewrite(Abc_Ntk_t *pNtk)
{
    static ABC_THREAD_LOCAL Cut_Params_t Params;
    Cut_Params_t *pParams = &Params;
    Cut_Man_t *pManCut;
    Abc_Obj_t *pObj;
    int i;
    // start the cut manager
    memset(pParams, 0, sizeof(Cut_Params_t));
    pParams->nVarsMax = 4;   // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax = 250; // the max number of cuts kept at a node
    pParams->fTruth = 1;     // compute truth tables
    pParams->fFilter = 1;    // filter dominated cuts
    pParams->fSeq = 0;       // compute sequential cuts
    pParams->fDrop = 0;      // drop cuts on the fly
    pParams->fVerbose = 0;   // the verbosiness flag
    pParams->nIdsMax = Abc_NtkObjNumMax(pNtk);
    pManCut = Cut_ManStart(pParams);
    if (pParams->fDrop)
        Cut_ManSetFanoutCounts(pManCut, Abc_NtkFanoutCounts(pNtk));
    // set cuts for PIs
    Abc_NtkForEachCi(pNtk, pObj, i) if (Abc_ObjFanoutNum(pObj) > 0)
        Cut_NodeSetTriv(pManCut, pObj->Id);
    return pManCut;
}

ABC_NAMESPACE_IMPL_END
