/**CFile****************************************************************

  FileName    [imcSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [Bounded bit-parallel search for concrete counterexamples.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcSim.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "imcInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Advances the deterministic word-sized simulation generator.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Imc_SimRandom( word * pSeed )
{
    *pSeed ^= *pSeed << 13;
    *pSeed ^= *pSeed >> 7;
    *pSeed ^= *pSeed << 17;
    return *pSeed;
}

/**Function*************************************************************

  Synopsis    [Generates structured or random input patterns for one simulation word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
word Imc_ManSimInput( int iPi, int iFrame, int iWord, word * pSeed )
{
    word Result = 0;
    int k, nBits = iWord < 2 ? 32 : 64;
    int iBit = iPi % nBits, iGroup = iPi / nBits;
    if ( iWord == 4 )
        return Imc_SimRandom( pSeed );
    if ( iWord == 5 )
        return (iPi & 31) < 8 ? Imc_SimRandom(pSeed) : 0;
    if ( iWord & 1 )
        iBit = nBits - 1 - iBit;
    // Small signed integers in either bit order complement uniform
    // random patterns on bit-blasted software inputs. No input names
    // or benchmark-specific information are needed.
    for ( k = 0; k < 64; k++ )
    {
        int Value = ((k * (2 * iGroup + 1) + 7 * iGroup + 3 * iFrame) & 63) - 16;
        if ( (((word)(ABC_INT64_T)Value) >> iBit) & 1 )
            Result |= (word)1 << k;
    }
    return Result;
}

// The small-integer patterns have only 32 multipliers and 64 offsets.
// Cache their seven distinct bit planes locally for this simulation run.
/**Function*************************************************************

  Synopsis    [Reuses cached bit planes of structured simulation patterns.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Imc_SimInputCached( int iPi, int iFrame, int iWord, word * pSeed, word * pCache, char * pReady )
{
    int nBits, iBit, iGroup, Mult, Offset, Key, k, b;
    word * pPlanes;
    if ( iWord >= 4 )
        return Imc_ManSimInput( iPi, iFrame, iWord, pSeed );
    nBits = iWord < 2 ? 32 : 64;
    iBit = iPi % nBits;
    iGroup = iPi / nBits;
    if ( iWord & 1 )
        iBit = nBits - 1 - iBit;
    Mult = (2 * iGroup + 1) & 63;
    Offset = (7 * iGroup + 3 * iFrame) & 63;
    Key = (Mult / 2) * 64 + Offset;
    pPlanes = pCache + 7 * Key;
    if ( !pReady[Key] )
    {
        for ( k = 0; k < 64; k++ )
        {
            unsigned Value = (unsigned)(((k * Mult + Offset) & 63) - 16);
            for ( b = 0; b < 7; b++ )
                if ( (Value >> b) & 1 )
                    pPlanes[b] |= (word)1 << k;
        }
        pReady[Key] = 1;
    }
    return pPlanes[Abc_MinInt(iBit, 6)];
}

/**Function*************************************************************

  Synopsis    [Returns 1 only after independently checking a concrete CEX.]

  Description [Simulates 384 traces within work, frame and caller deadlines.
  Simulation cannot establish safety and does not change the proof state.]

  SideEffects [Stores a counterexample in pGia->pCexSeq.]

  SeeAlso     []

***********************************************************************/
int Imc_ManSimulate( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, abctime Budget )
{
    const int nWords = 6;
    int nFrames;
    int nPis = Gia_ManPiNum(pGia), i, f, w, k, Result = 0;
    abctime TimeStop = Budget ? TimeStart + Budget :
        pPars->nTimeOut ? TimeStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    word Seed = ABC_CONST(0x9e3779b97f4a7c15);
    word * pSim, * pHistory, * pOut, * pIn0, * pIn1, * pCache;
    char * pReady;
    Gia_Obj_t * pObj;
    if ( Gia_ManObjNum(pGia) > 2000000 || nPis > 100000 || (Imc_ManCheckStop(TimeStop)) )
        return 0;
    // Small circuits can explore deeper traces within the same work and
    // time budget. Seed history uses only one word per frame.
    // Keep enough depth for short software loops even on a wide transition.
    // The separate first pass still applies its explicit 15-frame limit.
    nFrames = Abc_MaxInt( 64, Abc_MinInt(4096, (1 << 24) / (nWords * Gia_ManObjNum(pGia))) );
    if ( pPars->nFrameMax )
        nFrames = Abc_MinInt( nFrames - 1, pPars->nFrameMax ) + 1;
    pSim = ABC_CALLOC( word, (size_t)Gia_ManObjNum(pGia) * nWords );
    pHistory = ABC_ALLOC( word, nFrames );
    pCache = ABC_CALLOC( word, 32 * 64 * 7 );
    pReady = ABC_CALLOC( char, 32 * 64 );
    for ( f = 0; f < nFrames && (!Imc_ManCheckStop(TimeStop)); f++ )
    {
        // Deterministic input patterns can be regenerated from one seed.
        // Wide designs therefore retain all frames without a PI history.
        pHistory[f] = Seed;
        Gia_ManForEachPi( pGia, pObj, i )
        {
            pOut = pSim + Gia_ObjId(pGia, pObj) * nWords;
            for ( w = 0; w < nWords; w++ )
                pOut[w] = Imc_SimInputCached(i, f, w, &Seed, pCache, pReady);
        }
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            word Mask0 = Gia_ObjFaninC0(pObj) ? ~(word)0 : 0;
            word Mask1 = Gia_ObjFaninC1(pObj) ? ~(word)0 : 0;
            pOut = pSim + i * nWords;
            pIn0 = pSim + Gia_ObjFaninId0p(pGia, pObj) * nWords;
            pIn1 = pSim + Gia_ObjFaninId1p(pGia, pObj) * nWords;
            for ( w = 0; w < nWords; w++ )
                pOut[w] = (pIn0[w] ^ Mask0) & (pIn1[w] ^ Mask1);
        }
        // Compute every CO before overwriting any current-state value.
        Gia_ManForEachCo( pGia, pObj, i )
        {
            word Mask = Gia_ObjFaninC0(pObj) ? ~(word)0 : 0;
            pOut = pSim + Gia_ObjId(pGia, pObj) * nWords;
            pIn0 = pSim + Gia_ObjFaninId0p(pGia, pObj) * nWords;
            for ( w = 0; w < nWords; w++ )
                pOut[w] = pIn0[w] ^ Mask;
        }
        pOut = pSim + Gia_ObjId(pGia, Gia_ManPo(pGia, 0)) * nWords;
        for ( w = 0; w < nWords; w++ )
            if ( pOut[w] )
            {
                Abc_Cex_t * pCex = Abc_CexAlloc( Gia_ManRegNum(pGia), nPis, f + 1 );
                int t;
                for ( k = 0; !((pOut[w] >> k) & 1); k++ ) {}
                pCex->iPo = 0;
                pCex->iFrame = f;
                for ( t = 0; t <= f; t++ )
                {
                    int Word;
                    Seed = pHistory[t];
                    for ( i = 0; i < nPis; i++ )
                        for ( Word = 0; Word < nWords; Word++ )
                        {
                            word Input = Imc_SimInputCached( i, t, Word, &Seed, pCache, pReady );
                            if ( Word == w && ((Input >> k) & 1) )
                                Imc_CexSetBit( pCex->pData, pCex->nRegs + t * nPis + i );
                        }
                }
                if ( Gia_ManVerifyCex(pGia, pCex, 0) )
                {
                    pGia->pCexSeq = pCex;
                    pPars->iFrame = Abc_MaxInt( pPars->iFrame, f );
                    Result = 1;
                }
                else
                {
                    Abc_Print( -1, "IMC: Simulated counterexample verification failed.\n" );
                    Abc_CexFree( pCex );
                }
                goto finish;
            }
        Gia_ManForEachRo( pGia, pObj, i )
            memcpy( pSim + Gia_ObjId(pGia, pObj) * nWords,
                    pSim + Gia_ObjId(pGia, Gia_ManRi(pGia, i)) * nWords, sizeof(word) * nWords );
    }
finish:
    ABC_FREE( pReady );
    ABC_FREE( pCache );
    ABC_FREE( pSim );
    ABC_FREE( pHistory );
    return Result;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
