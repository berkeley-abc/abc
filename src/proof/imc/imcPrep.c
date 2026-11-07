/**CFile****************************************************************

  FileName    [imcPrep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [Bounded sequential equivalence preprocessing.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcPrep.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "imcInt.h"
#include "proof/cec/cec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks the sequential-sweep deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_SeqSweepStop( void * pData )
{
    return *(abctime *)pData && Abc_Clock() >= *(abctime *)pData;
}

/**Function*************************************************************

  Synopsis    [Checks the structural work gate for sequential sweeping.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManSeqSweepAllowed( int nAnds, int nRegs )
{
    return nRegs > 0 && (word)nAnds * nRegs <= (1u << 26);
}

/**Function*************************************************************

  Synopsis    [Checks whether a completed sweep gives a sufficient reduction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManSeqSweepUseful( int nAnds, int nRegs, int nNewAnds, int nNewRegs )
{
    return nAnds ? 20 * (word)nNewAnds <= 19 * (word)nAnds : nNewRegs < nRegs;
}

/**Function*************************************************************

  Synopsis    [Returns a reduced sequential AIG after completed induction.]

  Description [The correspondence engine must finish both its base and
  inductive refinement checks. Partial candidates are discarded when the
  budget expires. The returned AIG preserves all original primary inputs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_ManSeqSweep( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart )
{
    extern Gia_Man_t * Gia_ManCorrReduce( Gia_Man_t * pGia );
    Cec_ParCor_t Pars;
    Gia_Man_t * pWork, * pNew = NULL, * pTemp;
    abctime TimeStop = pPars->nTimeOut ? TimeStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    // Wide state vectors make repeated correspondence simulation expensive
    // even when SAT reports almost no conflicts. Gate this optional phase by
    // transition/state work before constructing its speculative unrollings.
    if ( !Imc_ManSeqSweepAllowed(Gia_ManAndNum(pGia), Gia_ManRegNum(pGia)) )
    {
        if ( pPars->fVerbose )
            Abc_Print( 1, "IMC: Skipping sweep with a large transition/state product.\n" );
        return NULL;
    }
    if ( Imc_SeqSweepStop(&TimeStop) )
        return NULL;
    pWork = Gia_ManDup( pGia );
    Cec_ManCorSetDefaultParams( &Pars );
    Pars.nProcs = 1;
    Pars.nBTLimit = 100;
    Pars.nConfTotal = 20000;
    Pars.nWorkLimit = 1u << 26;
    Pars.nStepsMax = 64;
    Pars.pFunc = (void *)Imc_SeqSweepStop;
    Pars.pData = &TimeStop;
    if ( Cec_ManLSCorrespondenceClasses(pWork, &Pars) && Pars.fCompleted )
    {
        pTemp = Gia_ManCorrReduce( pWork );
        pNew = Gia_ManSeqCleanup( pTemp );
        Gia_ManStop( pTemp );
    }
    if ( pPars->fVerbose )
    {
        Abc_Print( 1, "IMC: Sweep conflicts = %lld; rounds = %d; structural work = %llu; work limit reached = %d.\n",
            Pars.nConfUsed, Pars.nRoundsDone, (unsigned long long)Pars.nWorkUsed, Pars.fWorkStop );
        Abc_Print( 1, "IMC: Sequential sweeping %s (%d -> %d ANDs, %d -> %d registers).\n",
            Pars.fCompleted ? "completed" : "discarded incomplete candidates",
            Gia_ManAndNum(pGia), Gia_ManAndNum(pNew ? pNew : pGia), Gia_ManRegNum(pGia), Gia_ManRegNum(pNew ? pNew : pGia) );
    }
    // A marginal reduction invalidates useful search state and CNF caches.
    // Require a five-percent AND reduction, or fewer registers without ANDs.
    if ( pNew && !Imc_ManSeqSweepUseful(Gia_ManAndNum(pGia), Gia_ManRegNum(pGia),
         Gia_ManAndNum(pNew), Gia_ManRegNum(pNew)) )
    {
        if ( pPars->fVerbose )
            Abc_Print( 1, "IMC: Keeping original transition after marginal sweep.\n" );
        Gia_ManStopP( &pNew );
    }
    Gia_ManStop( pWork );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
