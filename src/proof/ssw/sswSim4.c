/**CFile****************************************************************

  FileName    [sswSim4.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential simulation.]

  Synopsis    [Rarity-guided simulation with seeded bounded model checking.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 11, 2026.]

  Revision    [$Id: sswSim4.c,v 1.00 2026/11/11 00:00:00 Exp $]

  Description [Uses ideas from Nalla et al., "The Art of Semi-Formal Bug
  Hunting", ICCAD 2016: historical rare-state selection, structural state
  partitions, short symbolic searches, internal targets, and pattern reuse.
  Every saved state has a concrete path from the initial state. Bounded
  search from a saved state can find a bug but cannot establish safety.]

***********************************************************************/

#include "sswSim4.h"
#include "sat/bmc/bmc.h"
#include "opt/abs2/abs2.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ssw_Sim4Man_t_ Ssw_Sim4Man_t;
typedef struct Ssw_Sim4Node_t_ Ssw_Sim4Node_t;
typedef struct Ssw_Sim4Pat_t_ Ssw_Sim4Pat_t;
enum { SIM4_GATE, SIM4_PARTITION, SIM4_RELATION };
struct Ssw_Sim4Pat_t_
{
    Abc_Cex_t * pCex;
    Abc_Cex_t * pCare;
    int nRefs;
    size_t nBytes;
};
struct Ssw_Sim4Node_t_
{
    Ssw_Sim4Node_t * pParent;
    Ssw_Sim4Pat_t * pPattern;
    word * pState;
    word Seed;
    word Hash;
    double Score;
    int nRefs, nDepth, nFrames, iPattern, nWords, nTried, fExact;
};
struct Ssw_Sim4Man_t_
{
    Gia_Man_t * pOriginal;
    Gia_Man_t * pGia;
    Ssw_ParSim4_t * pPars;
    word * pSim;
    word * pStates;
    unsigned * pCounts;
    unsigned char * pSeen;
    unsigned char * pMisses;
    unsigned char * pRareMisses;
    unsigned char * pPhase;
    word * pSignatures;
    int * pOrder;
    double * pScores;
    double * pWeights;
    Ssw_Sim4Node_t ** pPool;
    Ssw_Sim4Node_t ** pSeeds;
    Ssw_Sim4Pat_t * pPatterns[4];
    Ssw_Sim4Pat_t ** pActivePatterns;
    word Seed;
    abctime Start, Deadline, ProbeDeadline;
    double Memory;
    double BestRate;
    int nSavedPatterns, nWordsMax, BestWords, fWidthDone;
    int nWords, nPatterns, nRegWords, nGroups, nPool, fStopped;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets single-worker semiformal search defaults.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_Sim4SetDefaultParams( Ssw_ParSim4_t * pPars )
{
    memset( pPars, 0, sizeof(*pPars) );
    pPars->nTimeOut = 60;
    pPars->nWords = 64;
    pPars->nFrames = 128;
    pPars->nBmcFrames = 16;
    pPars->nBmcTime = 1000;
    pPars->nMemoryLimit = 512;
    pPars->nSeed = 1;
    pPars->fLighthouses = pPars->fPatterns = 1;
    pPars->iFrame = -1;
}

/**Function*************************************************************

  Synopsis    [Latches the invocation's cancellation request.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ssw_Sim4Stop( void * pData )
{
    Ssw_Sim4Man_t * p = (Ssw_Sim4Man_t *)pData;
    if ( !p->fStopped )
        p->fStopped = (p->Deadline && Abc_Clock() >= p->Deadline) ||
            (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->pStopData));
    return p->fStopped;
}

/**Function*************************************************************

  Synopsis    [Bounds one symbolic probe without stopping later simulation.]

  Description []

  SideEffects []

  SeeAlso     [Ssw_Sim4Stop]

***********************************************************************/
static int Ssw_Sim4ProbeStop( void * pData )
{
    Ssw_Sim4Man_t * p = (Ssw_Sim4Man_t *)pData;
    return Ssw_Sim4Stop(p) || Abc_Clock() >= p->ProbeDeadline;
}

/**Function*************************************************************

  Synopsis    [Checks private allocations before committing them.]

  Description []

  SideEffects [Latches an exhausted memory budget.]

  SeeAlso     []

***********************************************************************/
static int Ssw_Sim4Memory( Ssw_Sim4Man_t * p, double Extra )
{
    if ( p->Memory + Extra <= (double)p->pPars->nMemoryLimit * (1 << 20) ) return 1;
    p->pPars->fMemoryLimit = p->fStopped = 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Generates independently reproducible simulation words.]

  Description [Unsigned arithmetic intentionally wraps at the word boundary.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Ssw_Sim4Random( word x )
{
    x += ABC_CONST(0x9e3779b97f4a7c15);
    x = (x ^ (x >> 30)) * ABC_CONST(0xbf58476d1ce4e5b9);
    x = (x ^ (x >> 27)) * ABC_CONST(0x94d049bb133111eb);
    return x ^ (x >> 31);
}

/**Function*************************************************************

  Synopsis    [Reconstructs an input word, including optional pattern reuse.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Ssw_Sim4Word( word Seed, int Frame, int Input, int Word, int nPis,
    int nWords, Ssw_Sim4Pat_t * pPattern )
{
    word Value = Ssw_Sim4Random( Seed + ((word)Frame * nPis + Input) * nWords + Word );
    if ( pPattern && Frame <= pPattern->pCex->iFrame )
    {
        int Bit = Abc_InfoHasBit( pPattern->pCex->pData, Frame * nPis + Input );
        int Flip = nPis ? (int)(Ssw_Sim4Random(Seed + (word)Frame * nWords + Word) % nPis) : -1;
        // Preserve every care bit and one exact copy of the complete segment.
        if ( pPattern->pCare )
            Value = Abc_InfoHasBit(pPattern->pCare->pData, Frame * nPis + Input) ?
                (Bit ? ~(word)0 : 0) : (Value & ~(word)1) | (word)Bit;
        else
            Value = (Bit ? ~(word)0 : 0) ^ (Input == Flip ? Value & ~(word)1 : 0);
    }
    return Value;
}

/**Function*************************************************************

  Synopsis    [Releases a reference to a symbolic input pattern.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ssw_Sim4PatternDrop( Ssw_Sim4Man_t * p, Ssw_Sim4Pat_t * pPattern )
{
    if ( !pPattern || --pPattern->nRefs ) return;
    p->Memory -= pPattern->nBytes;
    Abc_CexFree( pPattern->pCex );
    Abc_CexFreeP( &pPattern->pCare );
    ABC_FREE( pPattern );
}

/**Function*************************************************************

  Synopsis    [Releases unreachable path segments without recursive calls.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ssw_Sim4NodeDrop( Ssw_Sim4Man_t * p, Ssw_Sim4Node_t * pNode )
{
    while ( pNode && --pNode->nRefs == 0 )
    {
        Ssw_Sim4Node_t * pParent = pNode->pParent;
        Ssw_Sim4PatternDrop( p, pNode->pPattern );
        p->Memory -= sizeof(*pNode) + (double)p->nRegWords * sizeof(word);
        ABC_FREE( pNode );
        pNode = pParent;
    }
}

/**Function*************************************************************

  Synopsis    [Scores a state using saturated eight-bit partition counts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Ssw_Sim4Score( Ssw_Sim4Man_t * p, word * pState )
{
    double Score = 0;
    int g;
    for ( g = 0; g < p->nGroups; g++ )
    {
        unsigned Value = (unsigned)((pState[g >> 3] >> (8 * (g & 7))) & 255);
        Score += p->pWeights[p->pCounts[(size_t)256 * g + Value]];
    }
    return Score;
}

/**Function*************************************************************

  Synopsis    [Retains a rare reachable state and its concrete path.]

  Description [The caller owns the simulation and pattern references.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Ssw_Sim4Node_t * Ssw_Sim4Save( Ssw_Sim4Man_t * p, word * pState,
    Ssw_Sim4Node_t * pParent, word Seed, int Frames, int Pattern, Ssw_Sim4Pat_t * pInputs, int fExact )
{
    Ssw_Sim4Node_t * pNode;
    size_t Bytes = sizeof(*pNode) + (size_t)p->nRegWords * sizeof(word);
    int Depth = pParent ? pParent->nDepth : 0, i;
    if ( Depth > INT_MAX - Frames - 1 ) { p->fStopped = 1; return NULL; }
    if ( !Ssw_Sim4Memory(p, (double)Bytes) ) return NULL;
    pNode = (Ssw_Sim4Node_t *)ABC_CALLOC( char, Bytes );
    p->Memory += Bytes;
    pNode->pState = (word *)(pNode + 1);
    memcpy( pNode->pState, pState, (size_t)p->nRegWords * sizeof(word) );
    pNode->pParent = pParent;
    if ( pParent ) pParent->nRefs++;
    pNode->pPattern = pInputs;
    if ( pInputs ) pInputs->nRefs++;
    pNode->nRefs = 1;
    pNode->Seed = Seed;
    pNode->nDepth = Depth + Frames;
    pNode->nFrames = Frames;
    pNode->iPattern = Pattern;
    pNode->nWords = p->nWords;
    pNode->fExact = fExact;
    pNode->Score = Ssw_Sim4Score( p, pState );
    for ( i = 0; i < p->nRegWords; i++ )
        pNode->Hash ^= Ssw_Sim4Random( pState[i] + i );
    if ( p->pPars->nStatesSaved < INT_MAX ) p->pPars->nStatesSaved++;
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Chooses a pool slot while avoiding duplicate concrete states.]

  Description [Uses full equality after the hash comparison.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ssw_Sim4PoolSlot( Ssw_Sim4Man_t * p, word * pState, double Score, int fForce )
{
    word Hash = 0;
    int i, Worst = 0;
    for ( i = 0; i < p->nRegWords; i++ ) Hash ^= Ssw_Sim4Random( pState[i] + i );
    for ( i = 0; i < p->nPool; i++ )
    {
        if ( Hash == p->pPool[i]->Hash &&
             !memcmp(pState, p->pPool[i]->pState, (size_t)p->nRegWords * sizeof(word)) ) return -1;
        if ( p->pPool[i]->Score < p->pPool[Worst]->Score ) Worst = i;
    }
    if ( p->nPool < p->nWords ) return p->nPool;
    return fForce || Score > p->pPool[Worst]->Score ? Worst : -1;
}

/**Function*************************************************************

  Synopsis    [Transposes a block using the existing rarity simulator's scheme.]

  Description []

  SideEffects []

  SeeAlso     [transpose64]

***********************************************************************/
static void Ssw_Sim4Transpose( word A[64] )
{
    word m = ABC_CONST(0x00000000ffffffff), t;
    int j, k;
    for ( j = 32; j; j >>= 1, m ^= m << j )
        for ( k = 0; k < 64; k = (k + j + 1) & ~j )
        {
            t = (A[k] ^ (A[k+j] >> j)) & m;
            A[k] ^= t;
            A[k+j] ^= t << j;
        }
}

/**Function*************************************************************

  Synopsis    [Updates rarity coverage and saves states from any timestep.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ssw_Sim4Coverage( Ssw_Sim4Man_t * p, word Seed, int Frame )
{
    Gia_Obj_t * pRi;
    word M[64];
    int w, r, i, k, g, nNew = 0;
    for ( w = 0; w < p->nWords; w++ )
    for ( r = 0; r < p->nRegWords; r++ )
    {
        if ( Ssw_Sim4Stop(p) ) return nNew;
        for ( i = 0; i < 64; i++ )
        {
            int Index = r * 64 + 63 - i;
            if ( Index >= Gia_ManRegNum(p->pGia) ) { M[i] = 0; continue; }
            pRi = Gia_ManRi( p->pGia, p->pOrder[Index] );
            M[i] = p->pSim[(size_t)Gia_ObjId(p->pGia, pRi) * p->nWords + w];
        }
        Ssw_Sim4Transpose( M );
        for ( i = 0; i < 64; i++ ) p->pStates[(size_t)(w * 64 + 63 - i) * p->nRegWords + r] = M[i];
    }
    for ( k = 0; k < p->nPatterns; k++ )
    {
        word * pState = p->pStates + (size_t)k * p->nRegWords;
        if ( !(k & 31) && Ssw_Sim4Stop(p) ) return nNew;
        for ( g = 0; g < p->nGroups; g++ )
        {
            unsigned Value = (unsigned)((pState[g >> 3] >> (8 * (g & 7))) & 255);
            unsigned * pCount = p->pCounts + (size_t)256 * g + Value;
            nNew += *pCount == 0;
            if ( *pCount < 65536 ) (*pCount)++;
        }
    }
    for ( k = 0; k < p->nPatterns; k++ )
    {
        if ( !(k & 31) && Ssw_Sim4Stop(p) ) return nNew;
        p->pScores[k] = Ssw_Sim4Score( p, p->pStates + (size_t)k * p->nRegWords );
    }
    for ( i = 0; i < p->nPool; i++ ) p->pPool[i]->Score = Ssw_Sim4Score( p, p->pPool[i]->pState );
    for ( w = 0; w < p->nWords; w++ )
    {
        int Best = w * 64, Slot;
        Ssw_Sim4Node_t * pNode;
        word * pState;
        for ( k = Best + 1; k < (w + 1) * 64; k++ )
            if ( p->pScores[k] > p->pScores[Best] ) Best = k;
        pState = p->pStates + (size_t)Best * p->nRegWords;
        Slot = Ssw_Sim4PoolSlot( p, pState, p->pScores[Best], 0 );
        if ( Slot < 0 ) continue;
        pNode = Ssw_Sim4Save( p, pState, p->pSeeds[w], Seed, Frame + 1, Best, p->pActivePatterns[w], 0 );
        if ( !pNode ) return nNew;
        if ( Slot == p->nPool ) p->nPool++;
        else Ssw_Sim4NodeDrop( p, p->pPool[Slot] );
        p->pPool[Slot] = pNode;
    }
    return nNew;
}

/**Function*************************************************************

  Synopsis    [Reconstructs all input segments back to the initial state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abc_Cex_t * Ssw_Sim4Trace( Ssw_Sim4Man_t * p, Ssw_Sim4Node_t * pNode, int Output )
{
    Abc_Cex_t * pCex;
    Ssw_Sim4Node_t * pNext;
    ABC_INT64_T Bits = (ABC_INT64_T)Gia_ManPiNum(p->pGia) * pNode->nDepth + Gia_ManRegNum(p->pOriginal);
    int i, f, nPis = Gia_ManPiNum(p->pGia);
    if ( Bits > INT_MAX - 32 )
    {
        Abc_Print( 1, "Warning: &sim4 found a trace exceeding the counterexample representation limit.\n" );
        return NULL;
    }
    pCex = Abc_CexAlloc( Gia_ManRegNum(p->pOriginal), nPis, pNode->nDepth );
    pCex->iFrame = pNode->nDepth - 1;
    pCex->iPo = Output;
    for ( pNext = pNode; pNext; pNext = pNext->pParent )
    for ( f = 0; f < pNext->nFrames; f++ )
    {
        int Offset = pCex->nRegs + (pNext->nDepth - pNext->nFrames + f) * nPis;
        for ( i = 0; i < nPis; i++ )
        {
            int Bit;
            if ( pNext->fExact ) Bit = Abc_InfoHasBit( pNext->pPattern->pCex->pData, f * nPis + i );
            else Bit = (int)((Ssw_Sim4Word(pNext->Seed, f, i, pNext->iPattern >> 6, nPis,
                pNext->nWords, pNext->pPattern) >> (pNext->iPattern & 63)) & 1);
            if ( Bit ) Abc_InfoSetBit( pCex->pData, Offset + i );
        }
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Finishes checking a found trace even after search cancellation.]

  Description []

  SideEffects []

  SeeAlso     [Gia_ManVerifyCex]

***********************************************************************/
static int Ssw_Sim4Verify( Ssw_Sim4Man_t * p, Abc_Cex_t * pCex )
{
    Gia_Man_t * pGia = p->pOriginal;
    Gia_Obj_t * pObj, * pRi;
    unsigned char * pValues;
    int f, i, Result = 0;
    if ( pCex->iPo < 0 || pCex->iPo >= Gia_ManPoNum(pGia) ) return 0;
    pValues = ABC_CALLOC( unsigned char, Gia_ManObjNum(pGia) );
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        Gia_ManForEachPi( pGia, pObj, i )
            pValues[Gia_ObjId(pGia, pObj)] =
                (unsigned char)Abc_InfoHasBit( pCex->pData, pCex->nRegs + f * pCex->nPis + i );
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            pValues[i] = (pValues[Gia_ObjFaninId0(pObj, i)] ^ Gia_ObjFaninC0(pObj)) &
                         (pValues[Gia_ObjFaninId1(pObj, i)] ^ Gia_ObjFaninC1(pObj));
        }
        if ( f == pCex->iFrame )
        {
            pObj = Gia_ManPo( pGia, pCex->iPo );
            Result = pValues[Gia_ObjFaninId0p(pGia, pObj)] ^ Gia_ObjFaninC0(pObj);
            break;
        }
        Gia_ManForEachRi( pGia, pObj, i )
            pValues[Gia_ObjId(pGia, pObj)] = pValues[Gia_ObjFaninId0p(pGia, pObj)] ^ Gia_ObjFaninC0(pObj);
        Gia_ManForEachRiRo( pGia, pRi, pObj, i )
            pValues[Gia_ObjId(pGia, pObj)] = pValues[Gia_ObjId(pGia, pRi)];
    }
    ABC_FREE( pValues );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Publishes only a replayed concrete counterexample.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ssw_Sim4Publish( Ssw_Sim4Man_t * p, Ssw_Sim4Node_t * pNode, int Output )
{
    abctime Start = Abc_Clock();
    Abc_Cex_t * pCex = Ssw_Sim4Trace( p, pNode, Output );
    if ( !pCex ) return 0;
    if ( !Ssw_Sim4Verify(p, pCex) )
    {
        Abc_Print( 1, "Warning: &sim4 rejected a counterexample during original-graph replay.\n" );
        Abc_CexFree( pCex );
        return 0;
    }
    p->pOriginal->pCexSeq = pCex;
    p->pPars->iFrame = pCex->iFrame;
    p->pPars->timeReplay += Abc_Clock() - Start;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Simulates one bit-parallel timestep and records gate activity.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ssw_Sim4Frame( Ssw_Sim4Man_t * p, word Seed, int Frame )
{
    Gia_Obj_t * pObj;
    int i, w;
    Gia_ManForEachPi( p->pGia, pObj, i )
        for ( w = 0; w < p->nWords; w++ )
            p->pSim[(size_t)Gia_ObjId(p->pGia, pObj) * p->nWords + w] =
                Ssw_Sim4Word( Seed, Frame, i, w, Gia_ManPiNum(p->pGia), p->nWords, p->pActivePatterns[w] );
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        word * pOut = p->pSim + (size_t)i * p->nWords;
        word * pIn0 = p->pSim + (size_t)Gia_ObjFaninId0(pObj, i) * p->nWords;
        word * pIn1 = p->pSim + (size_t)Gia_ObjFaninId1(pObj, i) * p->nWords;
        word Flip0 = Gia_ObjFaninC0(pObj) ? ~(word)0 : 0;
        word Flip1 = Gia_ObjFaninC1(pObj) ? ~(word)0 : 0;
        if ( !(i & 1023) && Ssw_Sim4Stop(p) ) return 0;
        if ( !(Frame & 3) )
        {
            word All = ~(word)0, Any = 0, Signature;
            if ( !p->pSeen[i] ) p->pPhase[i] = (unsigned char)((pIn0[0] ^ Flip0) & (pIn1[0] ^ Flip1) & 1);
            for ( w = 0; w < p->nWords; w++ )
            {
                word Value = pOut[w] = (pIn0[w] ^ Flip0) & (pIn1[w] ^ Flip1);
                All &= Value;
                Any |= Value;
            }
            Signature = pOut[(Frame / 4) % p->nWords] ^ (p->pPhase[i] ? ~(word)0 : 0);
            p->pSignatures[i] = Ssw_Sim4Random( p->pSignatures[i] ^ Signature );
            p->pSeen[i] |= (unsigned char)((All != ~(word)0) | ((Any != 0) << 1));
        }
        else
            for ( w = 0; w < p->nWords; w++ ) pOut[w] = (pIn0[w] ^ Flip0) & (pIn1[w] ^ Flip1);
    }
    Gia_ManForEachCo( p->pGia, pObj, i )
    {
        word * pOut = p->pSim + (size_t)Gia_ObjId(p->pGia, pObj) * p->nWords;
        word * pIn = p->pSim + (size_t)Gia_ObjFaninId0p(p->pGia, pObj) * p->nWords;
        word Flip = Gia_ObjFaninC0(pObj) ? ~(word)0 : 0;
        for ( w = 0; w < p->nWords; w++ ) pOut[w] = pIn[w] ^ Flip;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Runs a simulation block from the retained historical states.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ssw_Sim4Simulate( Ssw_Sim4Man_t * p, int Round, int * pnNew )
{
    Gia_Obj_t * pObj, * pRi;
    word Seed = p->Seed = Ssw_Sim4Random( p->Seed );
    int f, r, i, w, Result = 0;
    for ( w = 0; w < p->nWords; w++ )
    {
        p->pActivePatterns[w] = p->nSavedPatterns && w % 4 != 3 ?
            p->pPatterns[(w + Round) % p->nSavedPatterns] : NULL;
        p->pSeeds[w] = p->nPool && (p->nWords == 1 || w || Round % 4) ? p->pPool[w % p->nPool] : NULL;
        if ( p->pSeeds[w] ) p->pSeeds[w]->nRefs++;
    }
    // Count each selected starting state so historical states do not remain artificially rare.
    for ( w = 0; w < p->nWords; w++ )
    if ( p->pSeeds[w] )
        for ( i = 0; i < p->nGroups; i++ )
        {
            unsigned Value = (unsigned)((p->pSeeds[w]->pState[i >> 3] >> (8 * (i & 7))) & 255);
            unsigned * pCount = p->pCounts + (size_t)256 * i + Value;
            *pCount = Abc_MinInt( 65536, *pCount + 64 );
        }
    for ( r = 0; r < Gia_ManRegNum(p->pGia); r++ )
    {
        word * pReg = p->pSim + (size_t)Gia_ObjId(p->pGia, Gia_ManRo(p->pGia, p->pOrder[r])) * p->nWords;
        for ( w = 0; w < p->nWords; w++ )
            pReg[w] = p->pSeeds[w] && ((p->pSeeds[w]->pState[r >> 6] >> (r & 63)) & 1) ? ~(word)0 : 0;
    }
    for ( f = 0; f < p->pPars->nFrames && !Ssw_Sim4Stop(p); f++ )
    {
        if ( !Ssw_Sim4Frame(p, Seed, f) ) break;
        Gia_ManForEachPo( p->pGia, pObj, i )
        for ( w = 0; w < p->nWords; w++ )
        {
            word Value = p->pSim[(size_t)Gia_ObjId(p->pGia, pObj) * p->nWords + w];
            if ( Value )
            {
                Ssw_Sim4Node_t Hit;
                int Bit = 0;
                while ( !((Value >> Bit) & 1) ) Bit++;
                memset( &Hit, 0, sizeof(Hit) );
                Hit.pParent = p->pSeeds[w];
                Hit.pPattern = p->pActivePatterns[w];
                Hit.Seed = Seed;
                Hit.nFrames = f + 1;
                if ( Hit.pParent && Hit.pParent->nDepth > INT_MAX - Hit.nFrames )
                {
                    Abc_Print( 1, "Warning: &sim4 reached the trace depth representation limit.\n" );
                    p->fStopped = 1;
                    goto finish;
                }
                Hit.nDepth = Hit.nFrames + (Hit.pParent ? Hit.pParent->nDepth : 0);
                Hit.iPattern = w * 64 + Bit;
                Hit.nWords = p->nWords;
                Result = Ssw_Sim4Publish( p, &Hit, i );
                goto finish;
            }
        }
        if ( !(f & 3) || f + 1 == p->pPars->nFrames )
            *pnNew += Ssw_Sim4Coverage( p, Seed, f );
        Gia_ManForEachRiRo( p->pGia, pRi, pObj, i )
            memcpy( p->pSim + (size_t)Gia_ObjId(p->pGia, pObj) * p->nWords,
                    p->pSim + (size_t)Gia_ObjId(p->pGia, pRi) * p->nWords, (size_t)p->nWords * sizeof(word) );
        if ( p->pPars->nFramesDone < INT_MAX ) p->pPars->nFramesDone++;
    }
finish:
    for ( w = 0; w < p->nWords; w++ )
    {
        Ssw_Sim4NodeDrop( p, p->pSeeds[w] );
        p->pSeeds[w] = NULL;
    }
    return Result;
}

/**Function*************************************************************

  Synopsis    [Builds a zero-initialized symbolic model of a reachable state.]

  Description [A selector chooses one of up to four reachable starting states.
  Its first-frame values become constants when all selected states agree.
  A single state uses phase encoding without adding selectors or a register.]

  SideEffects [Uses scratch values only on the private simulation graph.]

  SeeAlso     [Gia_ManDupFlip]

***********************************************************************/
static Gia_Man_t * Ssw_Sim4Model( Ssw_Sim4Man_t * p, Ssw_Sim4Node_t ** ppSeeds,
    int nSeeds, Vec_Int_t * vTargets )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    unsigned * pInit;
    int i, k, Lit, Select[2], Ready = 0, nSelect = nSeeds > 2 ? 2 : nSeeds > 1;
    if ( !Ssw_Sim4Memory(p, 64.0 * Gia_ManObjNum(p->pGia)) ) return NULL;
    pInit = ABC_CALLOC( unsigned, Abc_BitWordNum(Gia_ManRegNum(p->pGia)) + 1 );
    if ( nSeeds == 1 && ppSeeds[0] )
        for ( i = 0; i < Gia_ManRegNum(p->pGia); i++ )
            if ( (ppSeeds[0]->pState[i >> 6] >> (i & 63)) & 1 ) Abc_InfoSetBit( pInit, p->pOrder[i] );
    pNew = Gia_ManStart( Gia_ManObjNum(p->pGia) + 16 );
    pNew->pName = Abc_UtilStrsav( p->pGia->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p->pGia)->Value = 0;
    Gia_ManForEachPi( p->pGia, pObj, i ) pObj->Value = Gia_ManAppendCi( pNew );
    for ( i = 0; i < nSelect; i++ ) Select[i] = Gia_ManAppendCi( pNew );
    Gia_ManForEachRo( p->pGia, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew ) ^ Abc_InfoHasBit(pInit, i);
    if ( nSelect ) Ready = Gia_ManAppendCi( pNew );
    for ( i = 0; nSelect && i < Gia_ManRegNum(p->pGia); i++ )
    {
        int Values[4];
        for ( k = 0; k < (1 << nSelect); k++ )
        {
            Ssw_Sim4Node_t * pSeed = ppSeeds[k % nSeeds];
            Values[k] = pSeed && ((pSeed->pState[i >> 6] >> (i & 63)) & 1);
        }
        Lit = Gia_ManHashMux( pNew, Select[0], Values[1], Values[0] );
        if ( nSelect == 2 )
            Lit = Gia_ManHashMux( pNew, Select[1],
                Gia_ManHashMux(pNew, Select[0], Values[3], Values[2]), Lit );
        pObj = Gia_ManRo( p->pGia, p->pOrder[i] );
        pObj->Value = Gia_ManHashMux( pNew, Ready, pObj->Value, Lit );
    }
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        if ( !(i & 1023) && Ssw_Sim4ProbeStop(p) ) { Gia_ManStop(pNew); ABC_FREE(pInit); return NULL; }
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    if ( !Vec_IntSize(vTargets) )
        Gia_ManForEachPo( p->pGia, pObj, i ) Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    for ( i = 0; i < Vec_IntSize(vTargets); i += 3 )
    {
        int Type = Vec_IntEntry(vTargets, i), Arg = Vec_IntEntry(vTargets, i+1);
        int Other = Vec_IntEntry(vTargets, i+2);
        if ( Type == SIM4_PARTITION )
        {
            Lit = 1;
            for ( k = 0; k < 8 && 8 * Arg + k < Gia_ManRegNum(p->pGia); k++ )
                Lit = Gia_ManHashAnd( pNew, Lit,
                    Gia_ManRo(p->pGia, p->pOrder[8 * Arg + k])->Value ^ !((Other >> k) & 1) );
        }
        else
        {
            Lit = Gia_ManObj(p->pGia, Abc_Lit2Var(Arg))->Value ^ Abc_LitIsCompl(Arg);
            if ( Type == SIM4_RELATION )
                Lit = Gia_ManHashXor( pNew, Lit,
                    Gia_ManObj(p->pGia, Abc_Lit2Var(Other))->Value ^ Abc_LitIsCompl(Other) );
        }
        Gia_ManAppendCo( pNew, Lit );
    }
    Gia_ManForEachRi( p->pGia, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) ^ Abc_InfoHasBit(pInit, i) );
    if ( nSelect ) Gia_ManAppendCo( pNew, 1 );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p->pGia) + (nSelect != 0) );
    Gia_ManHashStop( pNew );
    ABC_FREE( pInit );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Stores a symbolic input segment independently of its model.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abc_Cex_t * Ssw_Sim4Inputs( Abc_Cex_t * pCex, int nPis )
{
    Abc_Cex_t * pNew = Abc_CexAlloc( 0, nPis, pCex->iFrame + 1 );
    int f, i;
    pNew->iFrame = pCex->iFrame;
    for ( f = 0; f <= pCex->iFrame; f++ )
        for ( i = 0; i < nPis; i++ )
            if ( Abc_InfoHasBit(pCex->pData, pCex->nRegs + f * pCex->nPis + i) )
                Abc_InfoSetBit( pNew->pData, f * nPis + i );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Retains only original input bits from a concrete symbolic hit.]

  Description [Selector inputs choose a saved parent and are not replayed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Ssw_Sim4Pat_t * Ssw_Sim4Pattern( Ssw_Sim4Man_t * p, Abc_Cex_t * pCex )
{
    Ssw_Sim4Pat_t * pPattern;
    size_t Bytes = sizeof(*pPattern) + sizeof(*pCex) + (size_t)Abc_BitWordNum(pCex->nBits) * sizeof(unsigned);
    // A concrete symbolic hit is replayed even when the search budget is exhausted.
    pPattern = ABC_CALLOC( Ssw_Sim4Pat_t, 1 );
    pPattern->pCex = Ssw_Sim4Inputs( pCex, Gia_ManPiNum(p->pGia) );
    pPattern->nRefs = 1;
    pPattern->nBytes = Bytes;
    p->Memory += Bytes;
    return pPattern;
}

/**Function*************************************************************

  Synopsis    [Replays a symbolic suffix and extracts its final concrete state.]

  Description [Also checks original properties encountered during replay.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ssw_Sim4Replay( Ssw_Sim4Man_t * p, Ssw_Sim4Node_t * pSeed,
    Ssw_Sim4Pat_t * pPattern, word * pState, int * pOutput )
{
    Gia_Man_t * pGia = p->pGia;
    Gia_Obj_t * pObj, * pRi;
    unsigned char * pValues = ABC_CALLOC( unsigned char, Gia_ManObjNum(pGia) );
    int i, f, nFrames = pPattern->pCex->iFrame + 1;
    *pOutput = -1;
    for ( i = 0; i < Gia_ManRegNum(pGia); i++ )
        pValues[Gia_ObjId(pGia, Gia_ManRo(pGia, p->pOrder[i]))] =
            pSeed && ((pSeed->pState[i >> 6] >> (i & 63)) & 1);
    for ( f = 0; f < nFrames; f++ )
    {
        Gia_ManForEachPi( pGia, pObj, i )
            pValues[Gia_ObjId(pGia, pObj)] =
                (unsigned char)Abc_InfoHasBit( pPattern->pCex->pData, f * Gia_ManPiNum(pGia) + i );
        Gia_ManForEachAnd( pGia, pObj, i )
            pValues[i] = (pValues[Gia_ObjFaninId0(pObj, i)] ^ Gia_ObjFaninC0(pObj)) &
                         (pValues[Gia_ObjFaninId1(pObj, i)] ^ Gia_ObjFaninC1(pObj));
        Gia_ManForEachPo( pGia, pObj, i )
            if ( pValues[Gia_ObjFaninId0p(pGia, pObj)] ^ Gia_ObjFaninC0(pObj) )
            {
                *pOutput = i;
                break;
            }
        Gia_ManForEachRi( pGia, pObj, i )
            pValues[Gia_ObjId(pGia, pObj)] = pValues[Gia_ObjFaninId0p(pGia, pObj)] ^ Gia_ObjFaninC0(pObj);
        Gia_ManForEachRiRo( pGia, pRi, pObj, i )
            pValues[Gia_ObjId(pGia, pObj)] = pValues[Gia_ObjId(pGia, pRi)];
        if ( *pOutput >= 0 ) { nFrames = f + 1; break; }
    }
    memset( pState, 0, (size_t)p->nRegWords * sizeof(word) );
    for ( i = 0; i < Gia_ManRegNum(pGia); i++ )
        if ( pValues[Gia_ObjId(pGia, Gia_ManRo(pGia, p->pOrder[i]))] )
            pState[i >> 6] |= (word)1 << (i & 63);
    ABC_FREE( pValues );
    return nFrames;
}

/**Function*************************************************************

  Synopsis    [Alternates untoggled gates, rare state values, and simulated relations.]

  Description [Relations are candidates only. Refuting one yields a concrete
  input segment; failing to refute it never establishes an invariant.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Ssw_Sim4Targets( Ssw_Sim4Man_t * p )
{
    Vec_Int_t * vTargets = Vec_IntAlloc( 12 );
    int i, k, Type = (p->pPars->nRounds / 2) % 3;
    if ( !p->pPars->fLighthouses || !(p->pPars->nRounds & 1) ) return vTargets;
    if ( Type == SIM4_PARTITION )
        for ( i = 0; i < p->nGroups && Vec_IntSize(vTargets) < 12; i++ )
        {
            int Group = (i + p->pPars->nRounds / 6) % p->nGroups, Best = -1;
            int Count = 1 << Abc_MinInt( 8, Gia_ManRegNum(p->pGia) - 8 * Group );
            if ( Ssw_Sim4ProbeStop(p) ) break;
            for ( k = 0; k < Count; k++ )
                if ( p->pRareMisses[256 * Group + k] < 3 &&
                     (Best < 0 || p->pCounts[256 * Group + k] < p->pCounts[256 * Group + Best]) ) Best = k;
            if ( Best < 0 ) continue;
            Vec_IntPushThree( vTargets, SIM4_PARTITION, Group, Best );
        }
    if ( Type == SIM4_RELATION )
    {
        int Size = 1, * pTable;
        while ( Size < Gia_ManObjNum(p->pGia) && Size < (1 << 28) ) Size <<= 1;
        pTable = ABC_FALLOC( int, Size );
        for ( i = Gia_ManObjNum(p->pGia) - 1; i > 0 && Vec_IntSize(vTargets) < 12; i-- )
        {
            int Slot, Other;
            if ( !(i & 1023) && Ssw_Sim4ProbeStop(p) ) break;
            if ( !Gia_ObjIsAnd(Gia_ManObj(p->pGia, i)) || p->pSeen[i] != 3 || p->pMisses[i] >= 3 ) continue;
            Slot = (int)(p->pSignatures[i] & (Size - 1));
            Other = pTable[Slot];
            if ( Other >= 0 && p->pSignatures[i] == p->pSignatures[Other] )
                Vec_IntPushThree( vTargets, SIM4_RELATION,
                    Abc_Var2Lit(i, p->pPhase[i]), Abc_Var2Lit(Other, p->pPhase[Other]) );
            else pTable[Slot] = i;
        }
        ABC_FREE( pTable );
    }
    if ( !Vec_IntSize(vTargets) )
        for ( i = Gia_ManObjNum(p->pGia) - 1; i > 0 && Vec_IntSize(vTargets) < 12; i-- )
        {
            if ( !(i & 1023) && Ssw_Sim4ProbeStop(p) ) break;
            if ( Gia_ObjIsAnd(Gia_ManObj(p->pGia, i)) && p->pSeen[i] &&
                 p->pSeen[i] != 3 && p->pMisses[i] < 3 )
                Vec_IntPushThree( vTargets, SIM4_GATE, Abc_Var2Lit(i, p->pSeen[i] == 2), 0 );
        }
    return vTargets;
}

/**Function*************************************************************

  Synopsis    [Runs a short symbolic search from a retained reachable state.]

  Description [A failed search never proves the original property.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ssw_Sim4Probe( Ssw_Sim4Man_t * p )
{
    Gia_Man_t * pModel;
    Vec_Int_t * vTargets;
    Ssw_Sim4Node_t * pSeed = NULL, * pNode, * pSeeds[4];
    Ssw_Sim4Pat_t * pPattern;
    Bmc_GiaPar_t Pars;
    word * pState;
    abctime Start = Abc_Clock(), Budget;
    int i, k, Id, Status, Result = 0, Output, Frames, Slot, Available, nSeeds = 0;
    if ( !p->pPars->nBmcFrames || Ssw_Sim4Stop(p) ) return 0;
    Budget = CLOCKS_PER_SEC / 20 + p->pPars->timeSimulation / 3 - p->pPars->timeBmc;
    if ( Budget < CLOCKS_PER_SEC / 200 ) return 0;
    if ( Budget > (abctime)p->pPars->nBmcTime * CLOCKS_PER_SEC / 1000 )
        Budget = (abctime)p->pPars->nBmcTime * CLOCKS_PER_SEC / 1000;
    while ( nSeeds < Abc_MinInt(4, p->nPool) )
    {
        pSeed = NULL;
        for ( i = 0; i < p->nPool; i++ )
        {
            for ( k = 0; k < nSeeds; k++ ) if ( pSeeds[k] == p->pPool[i] ) break;
            if ( k < nSeeds ) continue;
            if ( !pSeed || p->pPool[i]->nTried < pSeed->nTried ||
                 (p->pPool[i]->nTried == pSeed->nTried && p->pPool[i]->Score > pSeed->Score) )
                pSeed = p->pPool[i];
        }
        pSeed->nTried++;
        pSeeds[nSeeds++] = pSeed;
    }
    if ( !nSeeds ) pSeeds[nSeeds++] = NULL;
    p->ProbeDeadline = Start + Budget;
    if ( p->Deadline && p->ProbeDeadline > p->Deadline ) p->ProbeDeadline = p->Deadline;
    vTargets = Ssw_Sim4Targets( p );
    pModel = Ssw_Sim4Model( p, pSeeds, nSeeds, vTargets );
    if ( !pModel )
    {
        p->pPars->timeBmc += Abc_Clock() - Start;
        Vec_IntFree( vTargets );
        return 0;
    }
    Available = p->pPars->nMemoryLimit - (int)((p->Memory + 64.0 * Gia_ManObjNum(pModel)) / (1 << 20));
    Status = -1;
    if ( Available >= 16 && !Ssw_Sim4ProbeStop(p) )
    {
        p->pPars->nBmcCalls++;
        if ( p->pPars->fUseGlucose && Gia_ManRegNum(pModel) )
        {
            Bmc_AndPar_t GPars;
            int MaxFrames = (int)((double)Available * (1 << 20) / (192.0 * Gia_ManObjNum(pModel)));
            memset( &GPars, 0, sizeof(GPars) );
            GPars.nFramesMax = Abc_MinInt( p->pPars->nBmcFrames, MaxFrames );
            GPars.nFramesAdd = 1;
            GPars.nProcs = 1;
            GPars.fUseGlucose = GPars.fNotVerbose = 1;
            if ( GPars.nFramesMax > 0 )
                Status = Bmcg_ManPerformWithStop( pModel, &GPars, Ssw_Sim4ProbeStop, p );
        }
        else
        {
            Bmc_GiaSetDefaultParams( &Pars );
            // Retain positive initial polarity for short seeded queries.
            Pars.fPhase = 1;
            Pars.nFramesMax = p->pPars->nBmcFrames;
            Pars.nMemoryLimit = Available;
            Pars.TimeToStop = p->ProbeDeadline;
            Pars.pFuncStop = Ssw_Sim4ProbeStop;
            Pars.pStopData = p;
            Pars.fSilent = 1;
            Status = Bmc_GiaPerform( pModel, &Pars );
        }
    }
    if ( Status != 0 || !pModel->pCexSeq )
    {
        for ( i = 0; i < Vec_IntSize(vTargets); i += 3 )
        {
            int Type = Vec_IntEntry(vTargets, i), Arg = Vec_IntEntry(vTargets, i+1);
            if ( Type == SIM4_PARTITION ) p->pRareMisses[256 * Arg + Vec_IntEntry(vTargets, i+2)]++;
            else p->pMisses[Abc_Lit2Var(Arg)]++;
        }
        goto finish;
    }
    Id = 0;
    for ( i = Gia_ManPiNum(p->pGia); i < pModel->pCexSeq->nPis; i++ )
        if ( Abc_InfoHasBit(pModel->pCexSeq->pData, pModel->pCexSeq->nRegs + i) )
            Id |= 1 << (i - Gia_ManPiNum(p->pGia));
    pSeed = pSeeds[Id % nSeeds];
    pPattern = Ssw_Sim4Pattern( p, pModel->pCexSeq );
    if ( !pPattern ) goto finish;
    pState = ABC_CALLOC( word, p->nRegWords );
    Frames = Ssw_Sim4Replay( p, pSeed, pPattern, pState, &Output );
    if ( !Frames ) { ABC_FREE(pState); Ssw_Sim4PatternDrop(p, pPattern); goto finish; }
    if ( pSeed && pSeed->nDepth > INT_MAX - Frames )
    {
        Abc_Print( 1, "Warning: &sim4 reached the trace depth representation limit.\n" );
        p->fStopped = 1;
        ABC_FREE( pState );
        Ssw_Sim4PatternDrop( p, pPattern );
        goto finish;
    }
    pNode = NULL;
    if ( Output >= 0 )
    {
        Ssw_Sim4Node_t Hit;
        memset( &Hit, 0, sizeof(Hit) );
        Hit.pParent = pSeed;
        Hit.pPattern = pPattern;
        Hit.nFrames = Frames;
        Hit.nDepth = Frames + (pSeed ? pSeed->nDepth : 0);
        Hit.fExact = 1;
        Result = Ssw_Sim4Publish( p, &Hit, Output );
    }
    else pNode = Ssw_Sim4Save( p, pState, pSeed, 0, Frames, 0, pPattern, 1 );
    if ( pNode )
    {
        p->pPars->nBmcHits++;
        Slot = Ssw_Sim4PoolSlot( p, pState, pNode->Score, 1 );
        if ( Slot >= 0 )
        {
            if ( Slot == p->nPool ) p->nPool++;
            else Ssw_Sim4NodeDrop( p, p->pPool[Slot] );
            p->pPool[Slot] = pNode;
            pNode = NULL;
        }
        if ( p->pPars->fPatterns )
        {
            if ( !Ssw_Sim4Stop(p) &&
                 (double)Gia_ManObjNum(pModel) * (pModel->pCexSeq->iFrame + 1) < 2000000 )
            {
                Abc_Cex_t * pCare = Bmc_CexCareMinimizeAig( pModel, Gia_ManPiNum(pModel),
                    pModel->pCexSeq, 1, 0, 0 );
                if ( pCare )
                {
                    size_t Bytes;
                    pPattern->pCare = Ssw_Sim4Inputs( pCare, Gia_ManPiNum(p->pGia) );
                    Abc_CexFree( pCare );
                    Bytes = sizeof(Abc_Cex_t) + (size_t)Abc_BitWordNum(pPattern->pCare->nBits) * sizeof(unsigned);
                    pPattern->nBytes += Bytes;
                    p->Memory += Bytes;
                }
            }
            if ( p->nSavedPatterns == 4 ) Ssw_Sim4PatternDrop( p, p->pPatterns[3] );
            else p->nSavedPatterns++;
            for ( i = p->nSavedPatterns - 1; i > 0; i-- ) p->pPatterns[i] = p->pPatterns[i-1];
            p->pPatterns[0] = pPattern;
            pPattern->nRefs++;
        }
    }
    Ssw_Sim4NodeDrop( p, pNode );
    ABC_FREE( pState );
    Ssw_Sim4PatternDrop( p, pPattern );
finish:
    p->pPars->timeBmc += Abc_Clock() - Start;
    Gia_ManStop( pModel );
    Vec_IntFree( vTargets );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Groups state variables by backward traversal from properties.]

  Description [Changes traversal ties between trials and periodically shuffles.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ssw_Sim4Partition( Ssw_Sim4Man_t * p )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 1000 );
    unsigned char * pVisited = ABC_CALLOC( unsigned char, Gia_ManObjNum(p->pGia) );
    Gia_Obj_t * pObj;
    int i, Id, Count = 0;
    Gia_ManForEachPo( p->pGia, pObj, i ) Vec_IntPush( vStack, Gia_ObjFaninId0p(p->pGia, pObj) );
    while ( Vec_IntSize(vStack) )
    {
        if ( Ssw_Sim4Stop(p) ) break;
        Id = Vec_IntPop( vStack );
        if ( pVisited[Id] ) continue;
        pVisited[Id] = 1;
        pObj = Gia_ManObj( p->pGia, Id );
        if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            p->pOrder[Count++] = Gia_ObjCioId(pObj) - Gia_ManPiNum(p->pGia);
            Vec_IntPush( vStack, Gia_ObjFaninId0p(p->pGia, Gia_ObjRoToRi(p->pGia, pObj)) );
        }
        else if ( Gia_ObjIsAnd(pObj) )
        {
            int First = (int)(Ssw_Sim4Random(p->Seed + Id) & 1);
            Vec_IntPush( vStack, First ? Gia_ObjFaninId0(pObj, Id) : Gia_ObjFaninId1(pObj, Id) );
            Vec_IntPush( vStack, First ? Gia_ObjFaninId1(pObj, Id) : Gia_ObjFaninId0(pObj, Id) );
        }
    }
    Gia_ManForEachRo( p->pGia, pObj, i )
        if ( !pVisited[Gia_ObjId(p->pGia, pObj)] ) p->pOrder[Count++] = i;
    if ( !p->fStopped ) assert( Count == Gia_ManRegNum(p->pGia) );
    if ( p->pPars->nRestarts % 4 == 3 )
        for ( i = Count - 1; i > 0; i-- )
        {
            int Other = (int)(Ssw_Sim4Random(p->Seed + i) % (i + 1));
            ABC_SWAP( int, p->pOrder[i], p->pOrder[Other] );
        }
    ABC_FREE( pVisited );
    Vec_IntFree( vStack );
}

/**Function*************************************************************

  Synopsis    [Repartitions state variables while retaining historical concrete paths.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ssw_Sim4Restart( Ssw_Sim4Man_t * p )
{
    int * pOld = ABC_ALLOC( int, Gia_ManRegNum(p->pGia) + 1 );
    int * pInverse = ABC_ALLOC( int, Gia_ManRegNum(p->pGia) + 1 );
    word * pState = ABC_CALLOC( word, p->nRegWords );
    int i, k;
    memcpy( pOld, p->pOrder, (size_t)Gia_ManRegNum(p->pGia) * sizeof(int) );
    memset( p->pCounts, 0, (size_t)256 * p->nGroups * sizeof(unsigned) );
    memset( p->pRareMisses, 0, (size_t)256 * p->nGroups );
    p->pPars->nRestarts++;
    Ssw_Sim4Partition( p );
    for ( i = 0; i < Gia_ManRegNum(p->pGia); i++ ) pInverse[p->pOrder[i]] = i;
    for ( k = 0; k < p->nPool; k++ )
    {
        Ssw_Sim4Node_t * pNode = p->pPool[k];
        memset( pState, 0, (size_t)p->nRegWords * sizeof(word) );
        for ( i = 0; i < Gia_ManRegNum(p->pGia); i++ )
            if ( (pNode->pState[i >> 6] >> (i & 63)) & 1 )
            {
                int Index = pInverse[pOld[i]];
                pState[Index >> 6] |= (word)1 << (Index & 63);
            }
        memcpy( pNode->pState, pState, (size_t)p->nRegWords * sizeof(word) );
        pNode->Hash = 0;
        for ( i = 0; i < p->nRegWords; i++ ) pNode->Hash ^= Ssw_Sim4Random( pState[i] + i );
        pNode->Score = Ssw_Sim4Score( p, pState );
    }
    ABC_FREE( pOld );
    ABC_FREE( pInverse );
    ABC_FREE( pState );
}

/**Function*************************************************************

  Synopsis    [Tunes simulation width using measured state throughput.]

  Description [Trials grow to the caller's cap. Stored traces retain their
  original word count, so changing the active width preserves replay.]

  SideEffects [May release the least rare entries when reducing the width.]

  SeeAlso     [Ssw_Sim4Simulate]

***********************************************************************/
static void Ssw_Sim4TuneWidth( Ssw_Sim4Man_t * p, abctime Elapsed )
{
    double Rate;
    int Next, i, Worst;
    if ( p->fWidthDone || Elapsed <= 0 || (p->pPars->nRounds & 1) ) return;
    Rate = (double)p->nWords * p->pPars->nFrames / Elapsed;
    if ( Rate > p->BestRate * 1.02 )
    {
        p->BestRate = Rate;
        p->BestWords = p->nWords;
        Next = Abc_MinInt( p->nWordsMax, 2 * p->nWords );
        if ( Next == p->nWords ) p->fWidthDone = 1;
    }
    else
    {
        Next = p->BestWords;
        p->fWidthDone = 1;
    }
    while ( p->nPool > Next )
    {
        Worst = 0;
        for ( i = 1; i < p->nPool; i++ )
            if ( p->pPool[i]->Score < p->pPool[Worst]->Score ) Worst = i;
        Ssw_Sim4NodeDrop( p, p->pPool[Worst] );
        p->pPool[Worst] = p->pPool[--p->nPool];
    }
    if ( p->nWords != Next )
        memset( p->pSim, 0, (size_t)Gia_ManObjNum(p->pGia) * p->nWordsMax * sizeof(word) );
    p->nWords = Next;
    p->nPatterns = 64 * Next;
    p->pPars->nWordsUsed = Next;
}

/**Function*************************************************************

  Synopsis    [Runs the bounded semiformal search on privately owned data.]

  Description [Returns zero for a checked counterexample, minus one when
  no bug was found, and minus two for unsupported input or parameters.]

  SideEffects [Replaces the input graph's counterexample and fills statistics.]

  SeeAlso     []

***********************************************************************/
int Ssw_Sim4Perform( Gia_Man_t * pGia, Ssw_ParSim4_t * pPars )
{
    Ssw_Sim4Man_t Man, * p = &Man;
    double Fixed, PerWord;
    int Result = -1, i, Stalls = 0;
    if ( !pGia || !pPars || pPars->nTimeOut < 1 || pPars->nTimeOut > 86400 ||
         pPars->nWords < 1 || pPars->nWords > 1024 || pPars->nFrames < 1 || pPars->nFrames > 1000000 ||
         pPars->nBmcFrames < 0 || pPars->nBmcFrames > 1024 || pPars->nBmcTime < 1 ||
         pPars->nBmcTime > 60000 || pPars->nMemoryLimit < 16 || pPars->nMemoryLimit > 65536 ||
         pPars->nSeed < 0 || pPars->nRoundsMax < 0 || pGia->nConstrs || !Abs2_ManCheckZeroInit(pGia) ||
         Gia_ManHasChoices(pGia) || pGia->pMuxes || Gia_ManXorNum(pGia) ||
         Gia_ManBufNum(pGia) || Gia_ManBoxNum(pGia) ) return -2;
    memset( p, 0, sizeof(*p) );
    p->pOriginal = pGia;
    p->pPars = pPars;
    p->Start = Abc_Clock();
    p->Deadline = p->Start + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC;
    if ( pPars->TimeToStop && pPars->TimeToStop < p->Deadline ) p->Deadline = pPars->TimeToStop;
    p->Seed = Ssw_Sim4Random( (word)pPars->nSeed );
    pPars->nRounds = pPars->nBmcCalls = pPars->nBmcHits = pPars->nRestarts = 0;
    pPars->nFramesDone = pPars->nStatesSaved = pPars->fMemoryLimit = pPars->nWordsUsed = 0;
    pPars->iFrame = -1;
    pPars->timeSimulation = pPars->timeBmc = pPars->timeReplay = 0;
    Abc_CexFreeP( &pGia->pCexSeq );
    if ( Ssw_Sim4Stop(p) ) goto finish;
    p->nRegWords = Abc_MaxInt( 1, (Gia_ManRegNum(pGia) + 63) / 64 );
    p->nGroups = (Gia_ManRegNum(pGia) + 7) / 8;
    Fixed = (double)(2 << 20) + 96.0 * Gia_ManObjNum(pGia) + 4.0 * Gia_ManRegNum(pGia) +
        (double)p->nGroups * 256 * (sizeof(unsigned) + 1);
    PerWord = 8.0 * Gia_ManObjNum(pGia) + 64.0 * p->nRegWords * sizeof(word) + 64.0 * sizeof(double) + 32;
    p->nWords = pPars->nWords;
    while ( p->nWords > 1 && Fixed + p->nWords * PerWord > .7 * pPars->nMemoryLimit * (1 << 20) )
        p->nWords /= 2;
    if ( !Ssw_Sim4Memory(p, Fixed + p->nWords * PerWord) ) goto finish;
    p->Memory = Fixed + p->nWords * PerWord;
    p->nPatterns = 64 * p->nWords;
    pPars->nWordsUsed = p->nWords;
    p->pGia = Gia_ManDupNormalize( pGia, 1 );
    p->pSim = ABC_CALLOC( word, (size_t)Gia_ManObjNum(p->pGia) * p->nWords );
    p->pStates = ABC_CALLOC( word, (size_t)p->nPatterns * p->nRegWords );
    p->pCounts = ABC_CALLOC( unsigned, (size_t)256 * p->nGroups + 1 );
    p->pSeen = ABC_CALLOC( unsigned char, Gia_ManObjNum(p->pGia) );
    p->pMisses = ABC_CALLOC( unsigned char, Gia_ManObjNum(p->pGia) );
    p->pRareMisses = ABC_CALLOC( unsigned char, (size_t)256 * p->nGroups + 1 );
    p->pPhase = ABC_CALLOC( unsigned char, Gia_ManObjNum(p->pGia) );
    p->pSignatures = ABC_CALLOC( word, Gia_ManObjNum(p->pGia) );
    p->pOrder = ABC_ALLOC( int, Gia_ManRegNum(p->pGia) + 1 );
    p->pScores = ABC_CALLOC( double, p->nPatterns );
    p->pWeights = ABC_ALLOC( double, 65537 );
    for ( i = 0; i <= 65536; i++ ) p->pWeights[i] = 1.0 / ((1.0 + i) * (1.0 + i));
    p->pPool = ABC_CALLOC( Ssw_Sim4Node_t *, p->nWords );
    p->pSeeds = ABC_CALLOC( Ssw_Sim4Node_t *, p->nWords );
    p->pActivePatterns = ABC_CALLOC( Ssw_Sim4Pat_t *, p->nWords );
    p->nWordsMax = p->nWords;
    p->nWords = p->BestWords = Abc_MinInt( p->nWords, 16 );
    p->nPatterns = 64 * p->nWords;
    pPars->nWordsUsed = p->nWords;
    Ssw_Sim4Partition( p );
    if ( Ssw_Sim4Probe(p) ) { Result = 0; goto finish; }
    while ( !Ssw_Sim4Stop(p) && (!pPars->nRoundsMax || pPars->nRounds < pPars->nRoundsMax) )
    {
        int New = 0, Hit;
        abctime Start = Abc_Clock(), Elapsed;
        Hit = Ssw_Sim4Simulate( p, pPars->nRounds, &New );
        Elapsed = Abc_Clock() - Start;
        pPars->timeSimulation += Elapsed;
        if ( Hit ) { Result = 0; break; }
        pPars->nRounds++;
        if ( !Ssw_Sim4Stop(p) ) Ssw_Sim4TuneWidth( p, Elapsed );
        if ( Ssw_Sim4Probe(p) ) { Result = 0; break; }
        Stalls = New ? 0 : Stalls + 1;
        if ( pPars->fVerbose )
            Abc_Print( 1, "Sim4: round=%d pool=%d new=%d bmc=%d hits=%d time=%.3f sec\n",
                pPars->nRounds, p->nPool, New, pPars->nBmcCalls, pPars->nBmcHits,
                (double)(Abc_Clock() - p->Start) / CLOCKS_PER_SEC );
        if ( Stalls == 16 ) { Ssw_Sim4Restart(p); Stalls = 0; }
    }
finish:
    for ( i = 0; i < p->nPool; i++ ) Ssw_Sim4NodeDrop( p, p->pPool[i] );
    for ( i = 0; i < p->nSavedPatterns; i++ ) Ssw_Sim4PatternDrop( p, p->pPatterns[i] );
    Gia_ManStopP( &p->pGia );
    ABC_FREE( p->pSim );
    ABC_FREE( p->pStates );
    ABC_FREE( p->pCounts );
    ABC_FREE( p->pSeen );
    ABC_FREE( p->pMisses );
    ABC_FREE( p->pRareMisses );
    ABC_FREE( p->pPhase );
    ABC_FREE( p->pSignatures );
    ABC_FREE( p->pOrder );
    ABC_FREE( p->pScores );
    ABC_FREE( p->pWeights );
    ABC_FREE( p->pActivePatterns );
    ABC_FREE( p->pPool );
    ABC_FREE( p->pSeeds );
    if ( pPars->fVerbose )
        Abc_Print( 1, "Sim4: simulation=%.3f bmc=%.3f replay=%.3f sec words=%d saved=%d\n",
            (double)pPars->timeSimulation / CLOCKS_PER_SEC, (double)pPars->timeBmc / CLOCKS_PER_SEC,
            (double)pPars->timeReplay / CLOCKS_PER_SEC, pPars->nWordsUsed, pPars->nStatesSaved );
    if ( !pPars->fSilent )
    {
        Abc_Print( 1, "Problem \"%s\" is %s", pGia->pName ? pGia->pName : "network",
            Result == 0 ? "SATISFIABLE (solved by sim4)" : "UNDECIDED" );
        Abc_Print( 1, ". Time = %.6f sec\n", (double)(Abc_Clock() - p->Start) / CLOCKS_PER_SEC );
    }
    return Result;
}

ABC_NAMESPACE_IMPL_END
