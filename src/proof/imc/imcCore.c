/**CFile****************************************************************

  FileName    [imcCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [McMillan reachability with frontier interpolation.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcCore.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

// Acknowledgements: We thank Niklas Een for his interpolation-based model
// checker (,imc) in the ZZ/Bip framework. Its implementation was studied
// during the development of ABC's &int, especially the separation of
// frontier image computation from incremental induction checking and
// the organization of forward and backward interpolation. ZZ's ,imc
// also served as a comparison baseline in our benchmark experiments.
// ZZ project: https://github.com/berkeley-abc/abc-zz

#include "imcInt.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Imc_Trans_t_ Imc_Trans_t;
struct Imc_Trans_t_
{
    Aig_Man_t * pAig;
    Cnf_Dat_t * pCnf;
    Vec_Int_t * vStart, * vCount;
    Vec_Int_t * vPis, * vRos, * vRis;
    int iBad;
    int fInitialUnsat;     // reuse a completed check of the zero initial state
};

typedef struct Imc_Phase_t_ Imc_Phase_t;
struct Imc_Phase_t_
{
    int nFrontMax;         // frontier gate; zero for the main search
    int fResume;           // retain concrete state across cooperative turns
    int nProbeQueries, nProbeConflicts;
    int fCostProbe;        // bound one image by the preceding work
    int fHoudOnly;         // invariant discovery without interpolation
    int fLimitAbstract;    // reserve concrete time for actual abstraction
};

/**Function*************************************************************

  Synopsis    [Initializes the work limits of one portfolio phase.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_ManPhaseSet( Imc_Phase_t * p, int nQueries, int nConflicts, int nFrontMax )
{
    memset( p, 0, sizeof(Imc_Phase_t) );
    p->nProbeQueries = nQueries;
    p->nProbeConflicts = nConflicts;
    p->nFrontMax = nFrontMax;
}

typedef struct Imc_Run_t_ Imc_Run_t;
struct Imc_Run_t_
{
    Gia_Man_t * pSource;    // source identity; replaced after sequential sweeping
    Gia_Man_t * pDelayed;   // cached one-cycle delay of an input-dependent bad
    Imc_Trans_t Trans[2];   // original and delayed transition CNFs
    int fBadInputs;
    int fPredAfterInit;     // classification required constant-successor cofactoring
    Imc_Search_t * pSearch[2];
    int nResumeFrames[2];  // last depth in each search direction
    int fAbstractUsed;      // last direct phase constructed an abstract interface
    const char * pSolvedPhase; // phase producing the independently checked result
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the shared frontier work limit for forward probes and tail turns.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManFrontierWorkLimit( Gia_Man_t * pGia )
{
    return Abc_MaxInt( 2048, 16 * Abc_MinInt(1024, Gia_ManRegNum(pGia)) );
}

/**Function*************************************************************

  Synopsis    [Sets the default interpolation parameters.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_ManSetDefaultParams( Imc_Par_t * p )
{
    memset( p, 0, sizeof(Imc_Par_t) );
    p->fPortfolio = 1;
    p->fUseMiniSat = 0;
    p->fBackward = 1;
    p->fDual = 0;
    p->fGrowFrames = 1;
    p->fSimulate = 1;
    p->fResetPrefix = 1;
    p->fSeqSweep = 1;
    p->fWeaken = 0;
    p->fAbstract = 1;
    p->iFrame = -1;
}

/**Function*************************************************************

  Synopsis    [Releases the cached transition AIG, CNF, and variable maps.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_ManClearTrans( Imc_Trans_t * p )
{
    if ( p->pCnf ) Cnf_DataFree( p->pCnf );
    if ( p->pAig ) Aig_ManStop( p->pAig );
    Vec_IntFreeP( &p->vStart );
    Vec_IntFreeP( &p->vCount );
    Vec_IntFreeP( &p->vPis );
    Vec_IntFreeP( &p->vRos );
    Vec_IntFreeP( &p->vRis );
    memset( p, 0, sizeof(Imc_Trans_t) );
}

/**Function*************************************************************

  Synopsis    [Releases the searches and transition caches of one run.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_ManClearRun( Imc_Run_t * pRun )
{
    if ( pRun->pSearch[0] ) Imc_ManSearchStop( pRun->pSearch[0] );
    if ( pRun->pSearch[1] ) Imc_ManSearchStop( pRun->pSearch[1] );
    pRun->pSearch[0] = pRun->pSearch[1] = NULL;
    Imc_ManClearTrans( &pRun->Trans[0] );
    Imc_ManClearTrans( &pRun->Trans[1] );
    Gia_ManStopP( &pRun->pDelayed );
    pRun->pSource = NULL;
    pRun->fBadInputs = 0;
    // Sweeping preserves bounded behavior from Init. Retain both search
    // depths when replacing transition data; each new search checks its base.
}

/**Function*************************************************************

  Synopsis    [Builds the transition CNF and its input and register maps.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_ManPrepareTrans( Imc_Trans_t * p, Gia_Man_t * pGia )
{
    int i;
    if ( p->pCnf )
        return;
    p->pAig = Gia_ManToAigSimple( pGia );
    Aig_ManSetRegNum( p->pAig, 0 );
    p->pCnf = Cnf_Derive( p->pAig, Aig_ManCoNum(p->pAig) );
    Imc_CnfMap( p->pCnf, &p->vStart, &p->vCount );
    p->vPis = Vec_IntAlloc( Gia_ManPiNum(pGia) );
    p->vRos = Vec_IntAlloc( Gia_ManRegNum(pGia) );
    p->vRis = Vec_IntAlloc( Gia_ManRegNum(pGia) );
    for ( i = 0; i < Gia_ManPiNum(pGia); i++ )
        Vec_IntPush( p->vPis, p->pCnf->pVarNums[Aig_ManCi(p->pAig, i)->Id] );
    for ( i = 0; i < Gia_ManRegNum(pGia); i++ )
    {
        Vec_IntPush( p->vRos, p->pCnf->pVarNums[Aig_ManCi(p->pAig, Gia_ManPiNum(pGia)+i)->Id] );
        Vec_IntPush( p->vRis, p->pCnf->pVarNums[Aig_ManCo(p->pAig, i+1)->Id] );
    }
    p->iBad = p->pCnf->pVarNums[Aig_ManCo(p->pAig, 0)->Id];
}

/**Function*************************************************************

  Synopsis    [Builds the initial frontier for the selected search direction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_ManInitial( Gia_Man_t * pGia, int fBackward )
{
    int nRegs = Gia_ManRegNum(pGia);
    Gia_Man_t * p = Gia_ManStart( 2 * nRegs + 10 );
    Gia_Obj_t * pObj;
    int i, Lit = 1;
    Gia_ManHashStart( p );
    for ( i = 0; i < nRegs; i++ )
    {
        int Ci = Gia_ManAppendCi( p );
        Lit = fBackward ? Ci : Gia_ManHashAnd(p, Lit, Abc_LitNot(Ci));
    }
    if ( fBackward )
    {
        Gia_ManConst0(pGia)->Value = 0;
        Gia_ManForEachPi( pGia, pObj, i )
            pObj->Value = 0;
        Gia_ManForEachRo( pGia, pObj, i )
            pObj->Value = Gia_Obj2Lit( p, Gia_ManCi(p, i) );
        Gia_ManForEachAnd( pGia, pObj, i )
            pObj->Value = Gia_ManHashAnd( p, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Lit = Gia_ObjFanin0Copy( Gia_ManPo(pGia, 0) );
    }
    Gia_ManAppendCo( p, Lit );
    Gia_ManHashStop( p );
    {
        Gia_Man_t * pResult = Gia_ManCleanup( p );
        Gia_ManStop( p );
        return pResult;
    }
}

/**Function*************************************************************

  Synopsis    [Checks whether the bad output depends on primary inputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManBadHasInputs( Gia_Man_t * pGia )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManConst0(pGia)->Value = 0;
    Gia_ManForEachPi( pGia, pObj, i )
        pObj->Value = 1;
    Gia_ManForEachRo( pGia, pObj, i )
        pObj->Value = 0;
    Gia_ManForEachAnd( pGia, pObj, i )
        pObj->Value = Gia_ObjFanin0(pObj)->Value | Gia_ObjFanin1(pObj)->Value;
    return Gia_ObjFanin0(Gia_ManPo(pGia, 0))->Value != 0;
}


/**Function*************************************************************

  Synopsis    [Combines frontiers by union, intersection, or difference.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_ManCombine( Gia_Man_t * pFront, Gia_Man_t * pReached, int fDifference )
{
    Gia_Man_t * p = Gia_ManStart( Gia_ManObjNum(pFront) + (pReached ? Gia_ManObjNum(pReached) : 0) );
    Gia_Man_t * pInputs[2] = { pFront, pReached }, * pResult;
    Gia_Obj_t * pObj;
    int i, k, Lits[2] = { 0, 0 };
    Gia_ManHashStart( p );
    Gia_ManForEachCi( pFront, pObj, i )
        Gia_ManAppendCi( p );
    for ( k = 0; k < 2 && pInputs[k]; k++ )
    {
        Gia_Man_t * pInput = pInputs[k];
        Gia_ManConst0(pInput)->Value = 0;
        Gia_ManForEachCi( pInput, pObj, i )
            pObj->Value = Gia_Obj2Lit( p, Gia_ManCi(p, i) );
        Gia_ManForEachAnd( pInput, pObj, i )
            pObj->Value = Gia_ManHashAnd( p, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Lits[k] = Gia_ObjFanin0Copy( Gia_ManCo(pInput, 0) );
    }
    Gia_ManAppendCo( p, fDifference == 2 ? Gia_ManHashAnd(p, Lits[0], Lits[1]) :
        fDifference ? Gia_ManHashAnd(p, Lits[0], Abc_LitNot(Lits[1])) : Gia_ManHashOr(p, Lits[0], Lits[1]) );
    Gia_ManHashStop( p );
    pResult = Gia_ManCleanup( p );
    Gia_ManStop( p );
    return pResult;
}

// Keep the accumulated union hashed across images. Independent invariant
// checking needs its output only at closure; rebuilding the whole prefix
// after every image would copy the same nodes quadratically.
/**Function*************************************************************

  Synopsis    [Adds a frontier to the persistent hashed reached-state union.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_ManAccumulate( Gia_Man_t * pReached, Gia_Man_t * pFront, int * pLit )
{
    Gia_Obj_t * pObj;
    int i;
    if ( pReached == NULL )
    {
        pReached = Gia_ManStart( Gia_ManObjNum(pFront) );
        Gia_ManHashStart( pReached );
        Gia_ManForEachCi( pFront, pObj, i )
            Gia_ManAppendCi( pReached );
        *pLit = 0;
    }
    Gia_ManConst0(pFront)->Value = 0;
    Gia_ManForEachCi( pFront, pObj, i )
        pObj->Value = Gia_Obj2Lit( pReached, Gia_ManCi(pReached, i) );
    Gia_ManForEachAnd( pFront, pObj, i )
        pObj->Value = Gia_ManHashAnd( pReached, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    *pLit = Gia_ManHashOr( pReached, *pLit, Gia_ObjFanin0Copy(Gia_ManCo(pFront, 0)) );
    return pReached;
}

static void Imc_ManSearchClear( Imc_Search_t * pSearch );

/**Function*************************************************************

  Synopsis    [Chooses the next bounded depth without exceeding its limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManSearchNextFrame( Imc_Search_t * pSearch )
{
    Imc_Par_t * pPars = &pSearch->Pars;
    int Frame = pSearch->nFrames, Step = Abc_MaxInt(1, pSearch->nImages);
    if ( Frame > INT_MAX / 2 || (pPars->nFrameMax && Frame >= pPars->nFrameMax) )
        return 0;
    if ( !pPars->fBackward )
    {
        if ( !pSearch->fFineFrames ) Step = Frame;
        else if ( Frame >= 8 ) Step = Abc_MaxInt((Frame + 3) / 4, Abc_MinInt(Frame, Step));
        else if ( pSearch->Man.iPredClass == 1 ) Step = Frame < 5 ? 1 : 8 - Frame;
    }
    Frame += pPars->fGrowFrames ? Abc_MinInt(Frame, Step) : 1;
    return pPars->nFrameMax ? Abc_MinInt(Frame, pPars->nFrameMax) : Frame;
}

/**Function*************************************************************

  Synopsis    [Grows a suspended query's conflict budget with saturation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManSearchGrowBudget( int Limit )
{
    if ( Limit <= 0 ) return 4096;
    return Limit >= INT_MAX / 2 ? INT_MAX : 2 * Limit;
}

/**Function*************************************************************

  Synopsis    [Checks whether a retained search can continue within its frontier limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManSearchCanContinue( Imc_Search_t * pSearch )
{
    return pSearch && !pSearch->fDone &&
        (pSearch->Stage == 0 || (pSearch->pFront &&
         (!pSearch->nFrontMax || Gia_ManAndNum(pSearch->pFront) <= pSearch->nFrontMax)));
}

/**Function*************************************************************

  Synopsis    [Selects a productive search with at least one turn in four for each direction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManScheduleNext( Imc_Sched_t * p, int First, int fDone0, int fDone1 )
{
    if ( fDone0 && fDone1 ) return -1;
    if ( fDone0 || fDone1 ) return fDone0;
    if ( p->Last < 0 ) return First;
    if ( p->nConsecutive >= 3 ) return !p->Last;
    if ( p->Scores[0] != p->Scores[1] ) return p->Scores[1] > p->Scores[0];
    return !p->Last;
}

/**Function*************************************************************

  Synopsis    [Scores completed depth growth and stable or shrinking image chains.]

  Description [Conflict counts from different solvers are not comparable.
  Scores measure structural progress without weighting query cost.
  A pending query earns no progress credit, but receives a turn at least
  every fourth selection and retains its growing conflict allowance.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_ManScheduleUpdate( Imc_Sched_t * p, int Dir, Imc_Search_t * pSearch, int Frames, int Images, int Front )
{
    int Score = 0;
    if ( pSearch && !pSearch->fDone )
    {
        if ( pSearch->nFrames > Frames ) Score = 2;
        else if ( pSearch->nImages > Images )
        {
            int Size = pSearch->pFront ? Gia_ManAndNum(pSearch->pFront) : 0;
            Score = Front > 0 && Size < Front ? 3 : Front > 0 && (word)Size * 4 <= (word)Front * 5 ? 2 : 1;
        }
    }
    p->Scores[Dir] = Score;
    p->nConsecutive = Dir == p->Last ? p->nConsecutive + 1 : 1;
    p->Last = Dir;
}

/**Function*************************************************************

  Synopsis    [Checks that retained search state matches the circuit and engine options.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManSearchCompatible( Imc_Search_t * pSearch, Gia_Man_t * pGia, Imc_Par_t * b )
{
    Imc_Par_t * a = &pSearch->Pars;
    return pSearch->Man.pGia == pGia &&
        a->fUseMiniSat == b->fUseMiniSat && a->fBackward == b->fBackward &&
        a->fDual == b->fDual && a->fInductive == b->fInductive &&
        a->fPudlak == b->fPudlak && a->fUseDelta == b->fUseDelta &&
        a->fGrowFrames == b->fGrowFrames && a->fSweep == b->fSweep &&
        a->fAutoItp == b->fAutoItp && a->fCompose == b->fCompose &&
        a->fPreprocess == b->fPreprocess && a->fIncremental == b->fIncremental &&
        a->fResetPrefix == b->fResetPrefix && a->fMinimize == b->fMinimize &&
        a->fWeaken == b->fWeaken && a->fPredicates == b->fPredicates &&
        a->fAbstract == b->fAbstract && a->fCheck == b->fCheck &&
        a->fPortfolio == b->fPortfolio && a->nBddMax == b->nBddMax &&
        a->nFrameMax == b->nFrameMax && a->nConfLimit == b->nConfLimit &&
        a->nTimeOut == b->nTimeOut;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if proved, 0 with a checked CEX, or -1 if unknown.]

  Description [Forward frontiers overapproximate successors of Init;
  backward frontiers overapproximate predecessors of Bad. Their union
  closes either by containment or by a transition-based induction check.
  A satisfiable image query is a real CEX only for the starting frontier;
  otherwise the bounded part is extended and interpolation restarts.]

  SideEffects [Stores a counterexample in pGia->pCexSeq.]

  SeeAlso     []

***********************************************************************/
// Suspend only between complete encoding operations, or inside a SAT query
// whose exact assumptions and proof stream are retained. No local wall clock
// discards an unfinished image chain in this cooperative search.
int Imc_ManSearchRun( Imc_Search_t * pSearch, int nQueries, int nConflicts )
{
    Imc_Man_t * p = &pSearch->Man;
    Imc_Par_t * pPars = p->pPars;
    Gia_Man_t * pNext;
    int Status, NextFrame, Queries = 0, Result = -1;
    word ConfStart = p->nConflicts;
    if ( pSearch->fDone ) return -1;
    for ( ; ; )
    {
        if ( Imc_ManCheckStop(p->TimeStop) )
            break;
        if ( pPars->nFrameMax && pSearch->nFrames > pPars->nFrameMax )
            break;
        if ( (nQueries && Queries >= nQueries) ||
             (nConflicts && p->nConflicts - ConfStart >= (word)nConflicts) )
            return -1;
        p->nQueryConfLimit = nConflicts ? nConflicts - (int)(p->nConflicts - ConfStart) : 0;
        if ( pSearch->Stage == 0 )
        {
            if ( !Imc_ManBuildSuffix(p, pSearch->nFrames) )
                break;
            Imc_ManIndStart( p );
            Gia_ManStopP( &pSearch->pReached );
            Gia_ManStopP( &pSearch->pFront );
            pSearch->pFront = Imc_ManInitial( p->pGia, pPars->fBackward );
            if ( p->pInvariant )
            {
                pNext = Imc_ManCombine( pSearch->pFront, p->pInvariant, 2 );
                Gia_ManStop( pSearch->pFront );
                pSearch->pFront = pNext;
            }
            pSearch->nImages = 0;
            pSearch->Stage = 1;
        }
        if ( pSearch->Stage == 1 )
        {
            if ( !p->fIndPending ) Imc_ManSetFront( p, pSearch->pFront );
            Status = Imc_ManIndCheck( p );
            Queries++;
            pSearch->nSteps++;
            if ( Status == l_Undef )
            {
                if ( p->fIndPending ) return -1;
                break;
            }
            if ( pPars->fUseDelta && pSearch->pReached && Status != l_False )
            {
                pSearch->pDelta = Imc_ManCombine( pSearch->pFront, pSearch->pReached, 1 );
                Imc_ManSetFront( p, pSearch->pDelta );
            }
            if ( pPars->fUseDelta )
            {
                pNext = Imc_ManCombine( pSearch->pFront, pSearch->pReached, 0 );
                Gia_ManStopP( &pSearch->pReached );
                pSearch->pReached = pNext;
            }
            else if ( pPars->fCheck || pPars->fAbstract )
                pSearch->pReached = Imc_ManAccumulate( pSearch->pReached, pSearch->pFront, &pSearch->iReached );
            if ( Status == l_False )
            {
                if ( pSearch->pReached && !pPars->fUseDelta )
                {
                    Gia_ManAppendCo( pSearch->pReached, pSearch->iReached );
                    Gia_ManHashStop( pSearch->pReached );
                    pNext = Gia_ManCleanup( pSearch->pReached );
                    Gia_ManStop( pSearch->pReached );
                    pSearch->pReached = pNext;
                }
                if ( p->pInvariant && pPars->fBackward )
                {
                    pNext = Imc_ManCombine( p->pInvariant, pSearch->pReached, 1 );
                    pPars->fBackward = 0;
                    Result = Imc_ManCheckInvariant( p, pNext ) ? 1 : -1;
                    pPars->fBackward = 1;
                    Gia_ManStop( pNext );
                }
                else
                    Result = (!pPars->fCheck && !pPars->fAbstract) || Imc_ManCheckInvariant(p, pSearch->pReached) ? 1 : -1;
                break;
            }
            if ( pSearch->nImages && pSearch->nFrontMax && Gia_ManAndNum(pSearch->pFront) > pSearch->nFrontMax )
            {
                pSearch->Stage = 2;
                return -1;
            }
            pSearch->Stage = 2;
            continue;
        }
        if ( pSearch->fCostProbe && pSearch->nImages )
        {
            word Limit = 4 * p->nConflicts;
            int Cap = (int)Abc_MinWord(100000, Abc_MaxWord(512, Limit));
            if ( !p->nQueryConfLimit || Cap < p->nQueryConfLimit ) p->nQueryConfLimit = Cap;
        }
        pNext = Imc_ManImage( p, pSearch->pDelta ? pSearch->pDelta : pSearch->pFront,
            pSearch->nFrames, pSearch->nImages == 0, &Status );
        Queries++;
        pSearch->nSteps++;
        if ( Status == l_Undef && p->Image.fPending )
            return -1;
        Gia_ManStopP( &pSearch->pDelta );
        if ( pNext && p->pInvariant )
        {
            Gia_Man_t * pTemp = Imc_ManCombine( pNext, p->pInvariant, 2 );
            Gia_ManStop( pNext );
            pNext = pTemp;
        }
        if ( pPars->fVerbose )
        {
            Abc_Print( 1, "IMC: frame = %d  image = %d  ands = %d  ", pSearch->nFrames, pSearch->nImages, pNext ? Gia_ManAndNum(pNext) : 0 );
            Abc_PrintTime( 1, "Time", Abc_Clock() - p->timeTotal );
        }
        Gia_ManStopP( &pSearch->pFront );
        pSearch->pFront = pNext;
        if ( Status == l_Undef )
        {
            if ( !p->fRefined ) break;
            p->fRefined = 0;
            pSearch->nFrames = 1;
            pSearch->Stage = 0;
            continue;
        }
        if ( Status == l_True )
        {
            if ( pSearch->nImages == 0 )
            {
                Result = 0;
                break;
            }
            NextFrame = Imc_ManSearchNextFrame( pSearch );
            if ( NextFrame == 0 )
                break;
            pSearch->nFrames = NextFrame;
            pSearch->Stage = 0;
            continue;
        }
        pPars->iFrame = Abc_MaxInt( pPars->iFrame, pSearch->nFrames + pSearch->nImages );
        pSearch->nImages++;
        pSearch->Stage = 1;
    }
    pSearch->fDone = 1;
    Imc_ManSearchClear( pSearch );
    return Result;
}

// Keep only the terminal result and diagnostic counters until the run ends.
// The transition objects are borrowed from the run and are released there.
/**Function*************************************************************

  Synopsis    [Releases the heavy state owned by a retained search.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_ManSearchClear( Imc_Search_t * pSearch )
{
    Imc_Man_t * p = &pSearch->Man;
    Imc_ManUnrollStop( p );
    Gia_ManStopP( &pSearch->pDelta );
    Vec_IntFreeP( &p->vSuffixClauses );
    Vec_IntFreeP( &p->vSuffixMap );
    Gia_ManStopP( &pSearch->pReached );
    Gia_ManStopP( &pSearch->pFront );
    Gia_ManStopP( &p->pPred );
    Gia_ManStopP( &p->pInvariant );
    Imc_ManImageStop( p );
    if ( p->Ind.pSat )
        sat_solver_delete( p->Ind.pSat );
    p->Ind.pSat = NULL;
    p->fIndPending = 0;
    Vec_StrFreeP( &p->Ind.vLoaded );
    Vec_IntFreeP( &p->vMapB );
    Vec_IntFreeP( &p->vFrontVars );
    Vec_IntFreeP( &p->vFrontUsed );
    Vec_IntFreeP( &p->vSharedUsed );
    Vec_IntFreeP( &p->vCnfStartB );
    Vec_IntFreeP( &p->vCnfCountB );
    Vec_IntFreeP( &p->vPrefix );
    Vec_IntFreeP( &p->vResets );
    Vec_IntFreeP( &p->vStates );
    if ( p->pCnfF )
        Cnf_DataFree( p->pCnfF );
    p->pCnfF = NULL;
    Vec_IntFreeP( &p->vImagePis );
    Vec_IntFreeP( &p->vImageBad );
    if ( p->pCnfB )
        Cnf_DataFree( p->pCnfB );
    p->pCnfB = NULL;
}

/**Function*************************************************************

  Synopsis    [Releases a retained search and its manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_ManSearchStop( Imc_Search_t * pSearch )
{
    Imc_ManSearchClear( pSearch );
    ABC_FREE( pSearch );
}

// Initialize a search once. Return 2 when its image loop is ready, or a
// terminal result from initial-state checking and predicate induction.
/**Function*************************************************************

  Synopsis    [Prepares a search and handles initial-state and predicate checks.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManSearchStart( Imc_Search_t * pSearch, Gia_Man_t * pGia, Imc_Par_t * pPars,
    abctime TimeStart, abctime TimeLimit, int iPredClass, Imc_Run_t * pRun, const Imc_Phase_t * pPhase )
{
    Imc_Man_t * p = &pSearch->Man;
    Imc_Trans_t * pTrans = &pRun->Trans[pGia == pRun->pDelayed];
    int Status, Result = -1;
    abctime TimeSetup = Abc_Clock(), TimeHoud = 0;
    pSearch->nSliceConflicts = 4096;
    pSearch->Pars = *pPars;
    pPars = &pSearch->Pars;
    pSearch->nFrames = pPhase->fResume ? Abc_MaxInt(1, pRun->nResumeFrames[pPars->fBackward]) : 1;
    // Reset prefixes cover every shorter trace. Input-heavy transitions
    // benefit from amortizing their encoding over a larger first bound.
    if ( pPars->fPortfolio && !pPhase->fResume && pPars->fUseMiniSat && pPars->fBackward &&
         pPars->fResetPrefix && !pPars->fAbstract && !iPredClass && Gia_ManAndNum(pGia) >= 16384 &&
         (word)Gia_ManPiNum(pGia) > 4 * (word)Gia_ManRegNum(pGia) )
        pSearch->nFrames = pPars->nFrameMax ? Abc_MinInt(8, pPars->nFrameMax) : 8;
    // A spurious trace supplies the useful extension length in every
    // class. Above depth eight, keep both the image count and the minimum
    // quarter-depth step; large image chains can still double the bound.
    pSearch->fFineFrames = pPars->fPortfolio && !pPars->fBackward;
    pSearch->nFrontMax = pPhase->nFrontMax;
    pSearch->fCostProbe = pPhase->fCostProbe;
    p->pGia = pGia;
    // Chunked mapping pays off for larger transitions and recorded state.
    // Compact unrollings retain whole-cone mapping across depth changes.
    p->fExtendUnroll = iPredClass != 0 || Gia_ManAndNum(pGia) >= 16384;
    p->pPars = pPars;
    p->iPredClass = iPredClass;
    p->timeTotal = TimeStart;
    p->TimeStop = pPars->nTimeOut ? p->timeTotal + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    if ( TimeLimit && (!p->TimeStop || TimeLimit < p->TimeStop) )
        p->TimeStop = TimeLimit;
    pPars->iFrame = -1;
    pRun->fAbstractUsed = 0;
    Abc_CexFreeP( &pGia->pCexSeq );
    if ( Gia_ManPoNum(pGia) != 1 || pGia->nConstrs )
    {
        Abc_Print( -1, "IMC requires one property with folded constraints.\n" );
        return Result;
    }
    if ( pPars->fVerbose )
        Abc_Print( 1, "IMC: Engine = %s %s, abstraction = %d, predicate class = %d.\n",
            pPars->fBackward ? "backward" : "forward", pPars->fUseMiniSat ? "MiniSat" : "CaDiCaL",
            pPars->fAbstract, iPredClass );
    Imc_ManPrepareTrans( pTrans, pGia );
    // Phase managers borrow immutable transition data from the run cache.
    p->pAig = pTrans->pAig;
    p->pCnf = pTrans->pCnf;
    p->vCnfStart = pTrans->vStart;
    p->vCnfCount = pTrans->vCount;
    p->vPis = pTrans->vPis;
    p->vRos = pTrans->vRos;
    p->vRis = pTrans->vRis;
    p->iBad = pTrans->iBad;
    if ( pPars->fPredicates || pPars->fAbstract )
    {
        p->pPred = Imc_ManFindPredicates( pGia, p->TimeStop, pPars->fAbstract, iPredClass, pRun->fPredAfterInit );
        if ( pPars->fVerbose && p->pPred )
            Abc_Print( 1, "IMC: Exposing %d shared state predicates.\n", Gia_ManCoNum(p->pPred) );
        pRun->fAbstractUsed = pPars->fAbstract && (!pPars->fBackward || pPars->fResetPrefix) && p->pPred != NULL;
        // Linear templates are useful with a compact word vocabulary.
        // End this abstraction phase when its vocabulary is too large.
        if ( pPars->fAbstract && p->pPred && Gia_ManCoNum(p->pPred) > 256 && iPredClass == 2 )
            return Result;
        // Account for transition cost as well as vocabulary size. The full
        // abstraction phase can still use an expensive predicate set.
        if ( pPhase->fHoudOnly && p->pPred &&
             (word)Abc_MaxInt(1, Gia_ManAndNum(pGia)) * Gia_ManCoNum(p->pPred) > (1u << 20) )
            return Result;
    }
    if ( pPhase->fLimitAbstract && pRun->fAbstractUsed && p->TimeStop )
    {
        abctime Now = Abc_Clock();
        abctime Remaining = p->TimeStop > Now ? p->TimeStop - Now : 0;
        p->TimeStop = Now + (Remaining / 2 < 30 * (abctime)CLOCKS_PER_SEC ? Remaining / 2 : 30 * (abctime)CLOCKS_PER_SEC);
        if ( pPars->fVerbose )
            Abc_Print( 1, "IMC: Abstract slice budget = %.6f s.\n", (double)(p->TimeStop - Now) / CLOCKS_PER_SEC );
    }
    TimeSetup = Abc_Clock() - TimeSetup;
    if ( pPars->fVerbose )
        Abc_Print( 1, "IMC: Setup wall = %.6f s; abstract interface = %d.\n", (double)TimeSetup / CLOCKS_PER_SEC, pRun->fAbstractUsed );
    Status = pTrans->fInitialUnsat ? l_False : Imc_ManCheckInitial( p );
    pTrans->fInitialUnsat = Status == l_False;
    if ( Status == l_True )
    {
        pPars->iFrame = 0;
        Result = 0;
        return Result;
    }
    if ( Status == l_Undef )
        return Result;
    pPars->iFrame = 0;
    if ( Gia_ManRegNum(pGia) == 0 )
    {
        Result = 1;
        return Result;
    }
    // Full predicate induction also needs a structural work gate. A large
    // transition can spend its entire search allowance on cheap conflicts
    // without producing a restriction strong enough to prove safety.
    if ( pPars->fAbstract && p->pPred && (!pPars->fPortfolio ||
         (word)Gia_ManAndNum(pGia) * Gia_ManCoNum(p->pPred) <= (1u << 22)) )
    {
        int fSafe = 0;
        Gia_Man_t * pInvariant;
        TimeHoud = Abc_Clock();
        p->nHouConfMax = !pPhase->fHoudOnly && !pPhase->nProbeQueries ? 0 :
            (word)Gia_ManAndNum(pGia) * Gia_ManCoNum(p->pPred) <= (1u << 20) ? 100000 : 32768;
        pInvariant = Imc_ManPredicateInvariant( p, &fSafe );
        TimeHoud = Abc_Clock() - TimeHoud;
        if ( pPars->fVerbose )
            Abc_Print( 1, "IMC: Houdini wall = %.6f s; safe = %d.\n", (double)TimeHoud / CLOCKS_PER_SEC, fSafe );
        if ( pInvariant )
        {
            int fBackward = pPars->fBackward;
            pPars->fBackward = 0;
            if ( fSafe )
                Result = Imc_ManCheckInvariant( p, pInvariant ) ? 1 : -1;
            else if ( Imc_ManCheckInductive(p, pInvariant) )
            {
                p->pInvariant = pInvariant;
                pInvariant = NULL;
            }
            pPars->fBackward = fBackward;
            Gia_ManStopP( &pInvariant );
            if ( Result == 1 )
                return Result;
        }
    }
    if ( pPhase->fHoudOnly )
        return Result;
    return 2;
}

/**Function*************************************************************

  Synopsis    [Starts or resumes interpolation within the current phase limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManPerformInt( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart,
    abctime TimeLimit, int iPredClass, Imc_Run_t * pRun, const Imc_Phase_t * pPhase )
{
    Imc_Search_t * pSearch = pPhase->fResume ? pRun->pSearch[pPars->fBackward] : NULL;
    Imc_Par_t * pReport = pPars;
    Imc_Man_t * p;
    int Result = 2, fSearched = 0, nSliceQueries = 4;
    if ( pSearch && !Imc_ManSearchCompatible(pSearch, pGia, pPars) )
    {
        if ( pPars->fVerbose )
            Abc_Print( 1, "IMC: Restarting retained search after source or settings changed.\n" );
        Imc_ManSearchStop( pSearch );
        pRun->pSearch[pPars->fBackward] = pSearch = NULL;
    }
    if ( pSearch == NULL )
    {
        pSearch = ABC_CALLOC( Imc_Search_t, 1 );
        Result = Imc_ManSearchStart(pSearch, pGia, pPars, TimeStart, TimeLimit, iPredClass, pRun, pPhase);
    }
    else if ( pPars->fVerbose )
        Abc_Print( 1, "IMC: Resuming %s at depth %d, image %d, stage %d.\n",
            pPars->fBackward ? "backward" : "forward", pSearch->nFrames, pSearch->nImages, pSearch->Stage );
    p = &pSearch->Man;
    pPars = &pSearch->Pars;
    pSearch->nFrontMax = pPhase->nFrontMax;
    pSearch->fCostProbe = pPhase->fCostProbe;
    pPars->fVerbose = pReport->fVerbose;
    if ( Result == 2 )
    {

        fSearched = 1;
        // Forward word/state searches often have many inexpensive images.
        // Their conflict budget still bounds each turn while allowing several
        // such images before handing control to the other direction.
        // A tail has no frontier cutoff, but a large class-0 image must
        // still yield after a short batch. Use the forward probe's
        // structural work gate instead of treating an unlimited search
        // as permission to run a long batch of expensive image queries.
        if ( !pPars->fBackward && (iPredClass || (pSearch->nImages >= 8 &&
             pSearch->pFront && Gia_ManAndNum(pSearch->pFront) <= Imc_ManFrontierWorkLimit(pGia))) )
            nSliceQueries = 16;
        Result = Imc_ManSearchRun( pSearch, pPhase->nProbeQueries ? pPhase->nProbeQueries :
            pPhase->fResume ? nSliceQueries : 0,
            pPhase->nProbeQueries ? pPhase->nProbeConflicts : pPhase->fResume ? pSearch->nSliceConflicts : 0 );
    }
    if ( !pPars->fAbstract && !pPars->fPredicates )
        pRun->nResumeFrames[pPars->fBackward] = Abc_MaxInt(pRun->nResumeFrames[pPars->fBackward], pSearch->nFrames);
    pReport->iFrame = pPars->iFrame;
    if ( pPars->fVerbose )
    {
        Abc_PrintTime( 1, "Image SAT cumulative", p->timeSat );
        Abc_PrintTime( 1, "Interpolation cumulative", p->timeItp );
        Abc_PrintTime( 1, "Induction cumulative", p->timeInd );
        Abc_Print( 1, "IMC: Cumulative conflicts = %llu; MiniSat visits = %llu; raw interpolant nodes = %llu.\n",
            (unsigned long long)p->nConflicts, (unsigned long long)p->nSatVisits, (unsigned long long)p->nItpNodes );
    }
    if ( pPhase->fResume )
    {
        int fPending = p->Image.fPending || p->fIndPending;
        if ( !fSearched )
        {
            pSearch->fDone = 1;
            Imc_ManSearchClear( pSearch );
        }
        if ( !fPending ) pSearch->nSliceConflicts = 4096;
        else if ( !pPhase->nProbeQueries )
            pSearch->nSliceConflicts = Imc_ManSearchGrowBudget( pSearch->nSliceConflicts );
        pRun->pSearch[pPars->fBackward] = pSearch;
    }
    else
        Imc_ManSearchStop( pSearch );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Makes bad a state predicate and checks the original CEX.]

  Description [Backward images start from a state set. A fresh register
  delays the property by one cycle, allowing arbitrary input-dependent
  bad outputs without existential quantification or a change in safety.]

  SideEffects [Stores a counterexample in pGia->pCexSeq.]

  SeeAlso     []

***********************************************************************/
static int Imc_ManPerformCoreRun( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, abctime TimeLimit, int iPredClass, Imc_Run_t * pRun, const Imc_Phase_t * pPhase )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Abc_Cex_t * pCex;
    int i, iBad, Result, nBits;
    Abc_CexFreeP( &pGia->pCexSeq );
    pPars->iFrame = -1;
    if ( Imc_ManCheckStop(TimeLimit) )
        return -1;
    if ( pRun->pSource != pGia )
    {
        Imc_ManClearRun( pRun );
        pRun->pSource = pGia;
        pRun->fBadInputs = Gia_ManPoNum(pGia) == 1 && Imc_ManBadHasInputs(pGia);
    }
    if ( !pPars->fBackward || Gia_ManPoNum(pGia) != 1 || pGia->nConstrs )
        return Imc_ManPerformInt( pGia, pPars, TimeStart, TimeLimit, iPredClass, pRun, pPhase );
    if ( !pRun->fBadInputs )
        return Imc_ManPerformInt( pGia, pPars, TimeStart, TimeLimit, iPredClass, pRun, pPhase );
    Abc_CexFreeP( &pGia->pCexSeq );
    pNew = pRun->pDelayed;
    if ( pNew == NULL )
    {
        pNew = Gia_ManStart( Gia_ManObjNum(pGia) + 2 );
        Gia_ManConst0(pGia)->Value = 0;
        Gia_ManForEachCi( pGia, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
        iBad = Gia_ManAppendCi( pNew );
        Gia_ManForEachAnd( pGia, pObj, i )
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Gia_ManAppendCo( pNew, iBad );
        Gia_ManForEachRi( pGia, pObj, i )
            Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(Gia_ManPo(pGia, 0)) );
        Gia_ManSetRegNum( pNew, Gia_ManRegNum(pGia) + 1 );
        pRun->pDelayed = pNew;
    }
    Result = Imc_ManPerformInt( pNew, pPars, TimeStart, TimeLimit, iPredClass, pRun, pPhase );
    if ( Result == 0 )
    {
        assert( pNew->pCexSeq && pNew->pCexSeq->iFrame > 0 );
        pCex = Abc_CexAlloc( Gia_ManRegNum(pGia), Gia_ManPiNum(pGia), pNew->pCexSeq->iFrame );
        pCex->iPo = 0;
        pCex->iFrame = pNew->pCexSeq->iFrame - 1;
        nBits = pNew->pCexSeq->iFrame * pCex->nPis;
        for ( i = 0; i < nBits; i++ )
            if ( Imc_CexHasBit(pNew->pCexSeq->pData, pNew->pCexSeq->nRegs + i) )
                Imc_CexSetBit( pCex->pData, pCex->nRegs + i );
        if ( Gia_ManVerifyCex(pGia, pCex, 0) )
            pGia->pCexSeq = pCex;
        else
        {
            Abc_Print( -1, "IMC: Original counterexample verification failed.\n" );
            Abc_CexFree( pCex );
            Result = -1;
        }
    }
    pPars->iFrame = Abc_MaxInt( -1, pPars->iFrame - 1 );
    return Result;
}

// Each phase owns its local frame counter, including a possible delayed
// bad register. Publish the maximum after mapping back to original frames.
/**Function*************************************************************

  Synopsis    [Runs a phase while preserving the maximum checked frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManPerformCore( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, abctime TimeLimit, int iPredClass, Imc_Run_t * pRun, const Imc_Phase_t * pPhase )
{
    int iFrame = pPars->iFrame;
    int Result = Imc_ManPerformCoreRun( pGia, pPars, TimeStart, TimeLimit, iPredClass, pRun, pPhase );
    pPars->iFrame = Abc_MaxInt( iFrame, pPars->iFrame );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Reports phase timing and records the phase that solved the property.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManPhaseReport( Imc_Par_t * pPars, Imc_Run_t * pRun, const char * pName, abctime Start, int Result )
{
    if ( pPars->fVerbose )
        Abc_Print( 1, "IMC: Phase %s wall = %.6f s; result = %d.\n", pName, (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC, Result );
    if ( Result >= 0 )
        pRun->pSolvedPhase = pName;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Runs and reports one named interpolation phase.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManPhaseCore( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, abctime TimeLimit, int iPredClass, Imc_Run_t * pRun, const Imc_Phase_t * pPhase, const char * pName )
{
    abctime Start = Abc_Clock();
    int Result;
    if ( pPars->fVerbose )
        Abc_Print( 1, "IMC: Beginning phase %s.\n", pName );
    Result = Imc_ManPerformCore( pGia, pPars, TimeStart, TimeLimit, iPredClass, pRun, pPhase );
    return Imc_ManPhaseReport( pPars, pRun, pName, Start, Result );
}

/**Function*************************************************************

  Synopsis    [Runs guided simulation using the cached transition encoding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManRunWalk( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, Imc_Run_t * pRun, abctime Budget )
{
    if ( pRun->pSource != pGia )
    {
        Imc_ManClearRun( pRun );
        pRun->pSource = pGia;
        pRun->fBadInputs = Imc_ManBadHasInputs( pGia );
    }
    Imc_ManPrepareTrans( &pRun->Trans[0], pGia );
    {
        abctime Start = Abc_Clock();
        int Result = Imc_ManWalkCached( pGia, pPars, TimeStart, Budget, pRun->Trans[0].pAig, pRun->Trans[0].pCnf );
        Imc_ManPhaseReport( pPars, pRun, "walk", Start, Result ? 0 : -1 );
        return Result;
    }
}

/**Function*************************************************************

  Synopsis    [Schedules simulation, preprocessing, and retained interpolation searches.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManPerformRun( Gia_Man_t * pGia, Imc_Par_t * pPars, Imc_Run_t * pRun )
{
    abctime TimeStart = Abc_Clock(), PhaseStart;
    abctime TimeStop = pPars->nTimeOut ? TimeStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    Gia_Man_t * pNew = NULL, * pWork = pGia;
    Imc_Par_t Probe = *pPars;
    Imc_Phase_t Phase;
    Imc_Sched_t Schedule = { {0, 0}, -1, 0 };
    int iPredClass = 0, i, Round, Result = -1;
    int fWalk = pPars->fPortfolio && pPars->fSimulate && Gia_ManPiNum(pGia) > Gia_ManRegNum(pGia) && Gia_ManRegNum(pGia);
    Imc_ManPhaseSet(&Phase, 0, 0, 0);
    Abc_CexFreeP( &pGia->pCexSeq );
    pPars->iFrame = -1;
    if ( Gia_ManXorNum(pGia) || Gia_ManMuxNum(pGia) || Gia_ManBufNum(pGia) )
    {
        Abc_Print( -1, "IMC requires an AND-inverter graph without explicit XOR, MUX, or buffer nodes.\n" );
        return -1;
    }
    if ( Gia_ManPoNum(pGia) != 1 || pGia->nConstrs )
        return Imc_ManPhaseCore( pGia, pPars, TimeStart, 0, iPredClass, pRun, &Phase, "direct" );
    if ( pPars->fAbstract || pPars->fPredicates )
        iPredClass = Imc_ManPredicateClass( pGia, &pRun->fPredAfterInit );
    if ( pPars->fSimulate )
    {
        Imc_Par_t Sim = *pPars;
        if ( pPars->fPortfolio && (!Sim.nFrameMax || Sim.nFrameMax > 15) ) Sim.nFrameMax = 15;
        PhaseStart = Abc_Clock();
        Result = Imc_ManSimulate( pGia, &Sim, pPars->fPortfolio ? TimeStart : PhaseStart, pPars->fPortfolio ? 0 : CLOCKS_PER_SEC / 10 ) ? 0 : -1;
        pPars->iFrame = Abc_MaxInt(pPars->iFrame, Sim.iFrame);
        Imc_ManPhaseReport( pPars, pRun, "simulation", PhaseStart, Result );
        if ( Result >= 0 ) goto finish;
    }
    if ( pPars->fPortfolio )
    {
        Probe.fAbstract = Probe.fPredicates = 0;
        Probe.fBackward = 0;
        Probe.fUseMiniSat = 1;
        Probe.fInductive = iPredClass == 1;
        Imc_ManPhaseSet( &Phase, Gia_ManAndNum(pGia) < 16384 ? 64 : 16, 256, 512 );
        Phase.fResume = 1;
        Result = Imc_ManPhaseCore( pGia, &Probe, TimeStart, TimeStop, iPredClass, pRun, &Phase, "quick-forward" );
        pPars->iFrame = Abc_MaxInt(pPars->iFrame, Probe.iFrame);
        if ( Result >= 0 ) goto finish;
        if ( pPars->fSimulate )
        {
            PhaseStart = Abc_Clock();
            Result = Imc_ManSimulate( pGia, pPars, TimeStart, 0 ) ? 0 : -1;
            Imc_ManPhaseReport( pPars, pRun, "deep-simulation", PhaseStart, Result );
            if ( Result >= 0 ) goto finish;
        }
    }
    if ( fWalk && Gia_ManAndNum(pGia) / Gia_ManRegNum(pGia) > 128 )
    {
        fWalk = 0;
        if ( Imc_ManRunWalk(pGia, pPars, TimeStart, pRun, 0) )
        {
            Result = 0;
            goto finish;
        }
    }
    // Try the short backward probe before paying for a sequential sweep.
    if ( pPars->fPortfolio )
    {
        Probe = *pPars;
        Probe.fAbstract = Probe.fPredicates = 0;
        Probe.fUseMiniSat = 0;
        Probe.fPudlak = Probe.fPreprocess = !iPredClass && Gia_ManAndNum(pGia) < 16384;
        Imc_ManPhaseSet( &Phase, 16, 512, 0 );
        Result = Imc_ManPhaseCore( pGia, &Probe, TimeStart, TimeStop, iPredClass, pRun, &Phase, "backward-cadical-probe" );
        pPars->iFrame = Abc_MaxInt(pPars->iFrame, Probe.iFrame);
        if ( Result >= 0 ) goto finish;
    }
    if ( pPars->fSeqSweep && Gia_ManRegNum(pGia) && !pPars->fPortfolio )
    {
        PhaseStart = Abc_Clock();
        pNew = Imc_ManSeqSweep( pGia, pPars, TimeStart );
        pWork = pNew ? pNew : pGia;
        Imc_ManPhaseReport( pPars, pRun, "sequential-sweep", PhaseStart, -1 );
    }
    if ( pPars->fPortfolio )
    {
        if ( pPars->fAbstract && iPredClass == 1 )
        {
            Imc_ManPhaseSet( &Phase, 16, 512, 0 );
            Phase.fHoudOnly = 1;
            Result = Imc_ManPhaseCore( pWork, pPars, TimeStart,
                TimeStop, iPredClass, pRun, &Phase, "early-houdini" );
            if ( Result >= 0 ) goto finish;
        }
        Probe.fBackward = 0;
        Probe.fUseMiniSat = 1;
        Probe.fPudlak = Probe.fPreprocess = 0;
        Probe.fInductive = iPredClass == 1;
        Imc_ManPhaseSet( &Phase, Gia_ManAndNum(pWork) >= 65536 ? 16 : 128,
            Gia_ManAndNum(pWork) >= 65536 ? 512 : 4096,
            Imc_ManFrontierWorkLimit(pWork) );
        Phase.fCostProbe = 1;
        Phase.fResume = 1;
        Result = Imc_ManPhaseCore( pWork, &Probe, TimeStart, TimeStop, iPredClass, pRun, &Phase, "forward-minisat-probe" );
        // Continue a paused probe whose frontier still fits its work gate
        // before paying for another engine or predicate discovery.
        if ( Result < 0 && Imc_ManSearchCanContinue(pRun->pSearch[0]) )
        {
            Phase.nProbeConflicts *= 2;
            Result = Imc_ManPhaseCore( pWork, &Probe, TimeStart, TimeStop, iPredClass, pRun, &Phase, "forward-chain-probe" );
        }
        pPars->iFrame = Abc_MaxInt(pPars->iFrame, Probe.iFrame);
        if ( Result >= 0 ) goto finish;
        // Preserve predicate vocabularies until the original transition
        // has been tried by induction and both interpolation directions.
        if ( pPars->fSeqSweep && !iPredClass && Gia_ManRegNum(pGia) && Gia_ManAndNum(pGia) < 65536 )
        {
            PhaseStart = Abc_Clock();
            pNew = Imc_ManSeqSweep( pGia, pPars, TimeStart );
            pWork = pNew ? pNew : pGia;
            Imc_ManPhaseReport( pPars, pRun, "sequential-sweep", PhaseStart, -1 );
        }
        Probe.fBackward = 1;
        Probe.fInductive = 1;
        Imc_ManPhaseSet( &Phase, 64, 2048, 0 );
        Phase.fCostProbe = 1;
        Result = Imc_ManPhaseCore( pWork, &Probe, TimeStart, TimeStop, iPredClass, pRun, &Phase, "backward-minisat-probe" );
        pPars->iFrame = Abc_MaxInt(pPars->iFrame, Probe.iFrame);
        if ( Result >= 0 ) goto finish;
        if ( pPars->fAbstract && iPredClass )
        {
            Imc_ManPhaseSet( &Phase, 64, 16384, 0 );
            Result = Imc_ManPhaseCore( pWork, pPars, TimeStart, TimeStop, iPredClass, pRun, &Phase, "predicate-abstraction" );
            if ( Result >= 0 ) goto finish;
        }
        if ( fWalk && Imc_ManRunWalk(pWork, pPars, TimeStart, pRun, 0) )
        {
            Result = 0;
            goto finish;
        }
        if ( pPars->fSeqSweep && !iPredClass && Gia_ManRegNum(pGia) && Gia_ManAndNum(pGia) >= 65536 )
        {
            PhaseStart = Abc_Clock();
            pNew = Imc_ManSeqSweep( pGia, pPars, TimeStart );
            pWork = pNew ? pNew : pGia;
            Imc_ManPhaseReport( pPars, pRun, "sequential-sweep", PhaseStart, -1 );
        }
        // Retain each frontier, unrolling and solver across cooperative
        // slices. Only the global deadline interrupts proof construction.
        Imc_ManPhaseSet( &Phase, 0, 0, 0 );
        Phase.fResume = 1;
        for ( Round = 0; !Imc_ManCheckStop(TimeStop); Round++ )
        {
            Imc_Search_t * pSearch;
            int Frames, Images, Front;
            if ( pRun->pSource && pRun->pSource != pWork )
            {
                Imc_ManClearRun(pRun);
                memset(&Schedule, 0, sizeof(Schedule));
                Schedule.Last = -1;
            }
            Probe = *pPars;
            Probe.fAbstract = Probe.fPredicates = 0;
            Probe.fBackward = Imc_ManScheduleNext(&Schedule, iPredClass == 0,
                pRun->pSearch[0] && pRun->pSearch[0]->fDone,
                pRun->pSearch[1] && pRun->pSearch[1]->fDone);
            if ( Probe.fBackward < 0 ) break;
            pSearch = pRun->pSearch[Probe.fBackward];
            Frames = pSearch ? pSearch->nFrames : 0;
            Images = pSearch ? pSearch->nImages : 0;
            Front = pSearch && pSearch->pFront ? Gia_ManAndNum(pSearch->pFront) : 0;
            Probe.fUseMiniSat = !Probe.fBackward;
            Probe.fPudlak = Probe.fPreprocess = Probe.fBackward;
            // Both Pudlak polarities can have different AIG sizes. Keep
            // both without paying for the McMillan folds on each image.
            Probe.fAutoItp = Probe.fBackward ? 2 : 0;
            Probe.fCompose = Probe.fBackward && !iPredClass && Gia_ManAndNum(pWork) < 16384;
            // The backward probe tries transition induction. The tail uses
            // containment, retaining a distinct search configuration.
            Probe.fInductive = !Probe.fBackward && iPredClass == 1;
            Result = Imc_ManPhaseCore( pWork, &Probe, TimeStart, TimeStop, iPredClass, pRun, &Phase,
                Probe.fBackward ? "tail-backward-pudlak" : "tail-forward" );
            Imc_ManScheduleUpdate(&Schedule, Probe.fBackward, pRun->pSearch[Probe.fBackward], Frames, Images, Front);
            pPars->iFrame = Abc_MaxInt(pPars->iFrame, Probe.iFrame);
            if ( Result >= 0 ) goto finish;
            if ( Round == 1 && iPredClass && pPars->fSeqSweep && Gia_ManRegNum(pGia) )
            {
                PhaseStart = Abc_Clock();
                pNew = Imc_ManSeqSweep( pGia, pPars, TimeStart );
                pWork = pNew ? pNew : pGia;
                Imc_ManPhaseReport( pPars, pRun, "sequential-sweep", PhaseStart, -1 );
            }
        }
        goto finish;
    }
    // Explicit options retain the selected backend and direction. Split
    // a finite budget only after an actual abstract interface is built.
    Imc_ManPhaseSet( &Phase, 0, 0, 0 );
    Phase.fLimitAbstract = 1;
    pRun->fAbstractUsed = 0;
    Result = Imc_ManPhaseCore( pWork, pPars, TimeStart, 0, iPredClass, pRun, &Phase, "main" );
    if ( Result < 0 && pRun->fAbstractUsed )
    {
        pPars->fAbstract = 0;
        Result = Imc_ManPhaseCore( pWork, pPars, TimeStart, 0, iPredClass, pRun, &Phase, "concrete-fallback" );
    }
finish:
    if ( pNew && Result == 0 )
    {
        Abc_Cex_t * pCex = Abc_CexAlloc( Gia_ManRegNum(pGia), Gia_ManPiNum(pGia), pNew->pCexSeq->iFrame + 1 );
        pCex->iPo = 0;
        pCex->iFrame = pNew->pCexSeq->iFrame;
        assert( pCex->nPis == pNew->pCexSeq->nPis );
        for ( i = 0; i < pCex->nPis * (pCex->iFrame + 1); i++ )
            if ( Imc_CexHasBit(pNew->pCexSeq->pData, pNew->pCexSeq->nRegs + i) )
                Imc_CexSetBit( pCex->pData, pCex->nRegs + i );
        if ( Gia_ManVerifyCex(pGia, pCex, 0) )
            pGia->pCexSeq = pCex;
        else
        {
            Abc_Print( -1, "IMC: Counterexample verification after preprocessing failed.\n" );
            Abc_CexFree( pCex );
            Result = -1;
        }
    }
    Gia_ManStopP( &pNew );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Rejects unsupported combinations of interpolation options.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManCheckParams( Imc_Par_t * p )
{
    if ( (p->fUseMiniSat && (p->fPudlak || p->fIncremental || p->fPreprocess || p->fAutoItp || p->fMinimize)) ||
         (p->fIncremental && (p->fAutoItp || p->fMinimize)) )
    {
        Abc_Print( -1, "IMC: Unsupported options: -m excludes -p/-l/-u/-a/-j; -l excludes -a/-j.\n" );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks one safety property and reports a verified result or undecided.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManPerformEntry( Gia_Man_t * pGia, Imc_Par_t * pPars )
{
    Imc_Par_t Pars = *pPars;
    Imc_Run_t Run;
    abctime TimeStart = Abc_Clock();
    int Result;
    memset( &Run, 0, sizeof(Run) );
    if ( !Imc_ManCheckParams(&Pars) )
    {
        pPars->iFrame = -1;
        return -1;
    }
    // Honor explicit algorithm choices from C callers as well as the CLI.
    if ( Pars.fUseMiniSat || !Pars.fBackward || Pars.fDual || Pars.fInductive || Pars.fPudlak ||
         Pars.fUseDelta || !Pars.fGrowFrames || Pars.fSweep || Pars.fAutoItp || Pars.fCompose ||
         Pars.fPreprocess || Pars.fIncremental || !Pars.fResetPrefix || Pars.fMinimize ||
         Pars.fWeaken || Pars.fPredicates || !Pars.fAbstract || Pars.nFrameMax || Pars.nConfLimit || Pars.nBddMax )
        Pars.fPortfolio = 0;
    Result = Imc_ManPerformRun( pGia, &Pars, &Run );
    if ( Result >= 0 && Pars.fVerbose && Run.pSolvedPhase )
        Abc_Print( 1, "IMC: Solved by phase %s.\n", Run.pSolvedPhase );
    Imc_ManClearRun( &Run );
    pPars->iFrame = Pars.iFrame;
    Abc_Print( 1, "IMC: %s.  ", Result == 1 ? "Property proved" : Result == 0 ? "Property disproved" : "Undecided" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - TimeStart );
    return Result;
}

typedef struct Imc_Stop_t_ Imc_Stop_t;
struct Imc_Stop_t_
{
    int (*pFuncStop)(void *);
    void * pData;
    int fStopped;
};
#if ABC_HAS_THREAD_LOCAL
static ABC_THREAD_LOCAL Imc_Stop_t * s_pImcStop = NULL;
#endif

/**Function*************************************************************

  Synopsis    [Checks a local deadline and an optional scoped cancellation.]

  Description [The callback is latched for one invocation.]

  SideEffects []

  SeeAlso     [Imc_ManPerformWithStop]

***********************************************************************/
int Imc_ManCheckStop( abctime TimeStop )
{
    int Stop = TimeStop && Abc_Clock() >= TimeStop;
#if ABC_HAS_THREAD_LOCAL
    if ( s_pImcStop )
    {
        if ( !s_pImcStop->fStopped && s_pImcStop->pFuncStop )
            s_pImcStop->fStopped = s_pImcStop->pFuncStop( s_pImcStop->pData );
        Stop |= s_pImcStop->fStopped;
    }
#endif
    return Stop;
}

/**Function*************************************************************

  Synopsis    [Tests whether this invocation requested a SAT callback.]

  Description []

  SideEffects []

  SeeAlso     [Imc_ManStopId]

***********************************************************************/
int Imc_ManStopActive( void )
{
#if ABC_HAS_THREAD_LOCAL
    return s_pImcStop && s_pImcStop->pFuncStop;
#else
    return 0;
#endif
}

/**Function*************************************************************

  Synopsis    [Adapts scoped cancellation to the classic SAT interface.]

  Description []

  SideEffects []

  SeeAlso     [Imc_ManCheckStop]

***********************************************************************/
int Imc_ManStopId( int RunId )
{
    (void)RunId;
    return Imc_ManCheckStop( 0 );
}

/**Function*************************************************************

  Synopsis    [Runs interpolation with invocation-local cancellation.]

  Description [Nested invocations restore the previous thread-local scope.
  A platform without thread-local storage rejects an optional callback.]

  SideEffects [Updates the verification result and counterexample.]

  SeeAlso     [Imc_ManPerform]

***********************************************************************/
int Imc_ManPerformWithStop( Gia_Man_t * pGia, Imc_Par_t * pPars,
    int (*pFuncStop)(void *), void * pStopData )
{
    int Result;
#if ABC_HAS_THREAD_LOCAL
    Imc_Stop_t Stop = { pFuncStop, pStopData, 0 }, * pPrevious = s_pImcStop;
    s_pImcStop = &Stop;
    if ( Imc_ManCheckStop(0) )
    {
        if ( pGia ) Abc_CexFreeP( &pGia->pCexSeq );
        pPars->iFrame = -1;
        Result = -1;
    }
    else Result = Imc_ManPerformEntry( pGia, pPars );
    s_pImcStop = pPrevious;
#else
    (void)pStopData;
    if ( pFuncStop )
    {
        if ( pGia ) Abc_CexFreeP( &pGia->pCexSeq );
        pPars->iFrame = -1;
        return -1;
    }
    Result = Imc_ManPerformEntry( pGia, pPars );
#endif
    return Result;
}

/**Function*************************************************************

  Synopsis    [Runs interpolation with the established standalone settings.]

  Description []

  SideEffects []

  SeeAlso     [Imc_ManPerformWithStop]

***********************************************************************/
int Imc_ManPerform( Gia_Man_t * pGia, Imc_Par_t * pPars )
{
    return Imc_ManPerformWithStop( pGia, pPars, NULL, NULL );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
