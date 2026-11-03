/**CFile****************************************************************

  FileName    [bmcCasDec2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Backward decomposition into single-rail LUT cascades without SAT.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 3, 2026.]

  Revision    [$Id: bmcCasDec2.c,v 1.00 2026/11/03 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include <errno.h>
#include <limits.h>
#include <ctype.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Incomplete-function decomposition follows the information-partition view
// of Rawski, Jozwiak and Luba (1999, input support selection). Here a rail
// retains only distinctions needed after the selected last-stage PI group.
// The beam and its scores are heuristics, not lower bounds or UNSAT proofs.
#define CAS2_MAX_VARS 16
#define CAS2_MAX_NODES 64

typedef struct Bmc_Cas2Par_t_ Bmc_Cas2Par_t;
struct Bmc_Cas2Par_t_
{
    int nVars, nLutSize, nNodes, nBeam, nGroups, nTime, Seed;
    int fDump, fVerbose, fBatch, nLimit;
};

typedef struct Bmc_Cas2Res_t_ Bmc_Cas2Res_t;
struct Bmc_Cas2Res_t_
{
    int nNodes, fTimeout;
    double Time;
};

typedef struct Bmc_Cas2State_t_ Bmc_Cas2State_t;
struct Bmc_Cas2State_t_
{
    Bmc_Cas2State_t * pNext;             // successor residual, towards the output
    int nVars, Vars[CAS2_MAX_VARS];
    int nPis, Pis[CAS2_MAX_VARS];        // successor LUT: rail at pin zero
    word * pOn, * pOff;                 // disjoint care sets; other minterms are don't-cares
    unsigned char * pLut;
    word Hash, Score;
    int iHashNext;
};

typedef struct Bmc_Cas2Man_t_ Bmc_Cas2Man_t;
struct Bmc_Cas2Man_t_
{
    Bmc_Cas2Par_t * pPars;
    Vec_Ptr_t * vStates;
    int * pBins, nBins;
    abctime timeStop;
    unsigned Random;
    int fTimeout;
    word nGroups, nCandidates;
    word * pOn, * pOff, * pPackedOn, * pPackedOff;
    int * pParents, * pSaved, * pVotes, * pRoots, * pBalance;
    unsigned char * pType, * pPhase, * pPairs;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks the shared search deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Cas2Stop( Bmc_Cas2Man_t * p )
{
    return p->fTimeout |= p->timeStop && Abc_Clock() >= p->timeStop;
}

/**Function*************************************************************

  Synopsis    [Generates reproducible local tie-breaking choices.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Bmc_Cas2Random( Bmc_Cas2Man_t * p )
{
    p->Random ^= p->Random << 13;
    p->Random ^= p->Random >> 17;
    return p->Random ^= p->Random << 5;
}

/**Function*************************************************************

  Synopsis    [Allocates the per-command workspace shared by all PI groups.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Cas2Workspace( Bmc_Cas2Man_t * p, int fAlloc )
{
    int k, ns, nr, nw;
    if ( fAlloc )
    {
        if ( p->pPars->nVars <= p->pPars->nLutSize ) return;
        k = p->pPars->nLutSize-1;
        ns = 1 << k;
        nr = p->pPars->nVars-k;
        nw = Abc_TtWordNum(nr);
        p->pOn = ABC_ALLOC(word, ns*nw);
        p->pOff = ABC_ALLOC(word, ns*nw);
        p->pPackedOn = ABC_ALLOC(word, Abc_TtWordNum(p->pPars->nVars));
        p->pPackedOff = ABC_ALLOC(word, Abc_TtWordNum(p->pPars->nVars));
        p->pParents = ABC_ALLOC(int, ns);
        p->pSaved = ABC_ALLOC(int, ns);
        p->pVotes = ABC_ALLOC(int, ns);
        p->pRoots = ABC_ALLOC(int, ns);
        p->pBalance = ABC_ALLOC(int, ns);
        p->pType = ABC_ALLOC(unsigned char, ns);
        p->pPhase = ABC_ALLOC(unsigned char, ns);
        p->pPairs = ABC_ALLOC(unsigned char, k*ns);
    }
    else
    {
        ABC_FREE(p->pOn); ABC_FREE(p->pOff); ABC_FREE(p->pPackedOn); ABC_FREE(p->pPackedOff);
        ABC_FREE(p->pParents); ABC_FREE(p->pSaved); ABC_FREE(p->pVotes); ABC_FREE(p->pRoots);
        ABC_FREE(p->pBalance); ABC_FREE(p->pType); ABC_FREE(p->pPhase); ABC_FREE(p->pPairs);
    }
}

/**Function*************************************************************

  Synopsis    [Frees one search state without freeing its successor.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Cas2Free( Bmc_Cas2State_t * p )
{
    ABC_FREE(p->pOn);
    ABC_FREE(p->pOff);
    ABC_FREE(p->pLut);
    ABC_FREE(p);
}

// Bits outside the actual table are always zero, including for N < 6.
static inline word Bmc_Cas2Mask( int nVars ) { return nVars >= 6 ? ~(word)0 : (((word)1 << (1 << nVars))-1); }
static inline int Bmc_Cas2Equal( Bmc_Cas2State_t * p, Bmc_Cas2State_t * q )
{
    int nBytes = sizeof(word)*Abc_TtWordNum(p->nVars);
    return p->nVars == q->nVars && !memcmp(p->pOn, q->pOn, nBytes) && !memcmp(p->pOff, q->pOff, nBytes);
}

/**Function*************************************************************

  Synopsis    [Projects out inputs whose two partial cofactors are compatible.]

  Description [Merging care sets is essential: independently testing all
  inputs before projection would not be sound for incomplete functions.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Cas2Reduce( Bmc_Cas2State_t * p )
{
    int i, j, w, nw, Step, Good;
    word Mask;
    for ( i = p->nVars-1; i >= 0; --i )
    {
        nw = Abc_TtWordNum(p->nVars);
        Good = 1;
        if ( i < 6 )
        {
            Step = 1 << i;
            Mask = ~s_Truths6[i];
            for ( w = 0; w < nw; ++w )
                if ( ((p->pOn[w] & (p->pOff[w] >> Step)) |
                      (p->pOff[w] & (p->pOn[w] >> Step))) & Mask ) { Good = 0; break; }
        }
        else
        {
            Step = 1 << (i-6);
            for ( w = 0; w < nw; ++w )
                if ( !(w & Step) && ((p->pOn[w] & p->pOff[w | Step]) |
                                    (p->pOff[w] & p->pOn[w | Step])) ) { Good = 0; break; }
        }
        if ( !Good ) continue;
        // Move this variable last without changing the order of the others.
        for ( j = i; j < p->nVars-1; ++j )
        {
            Abc_TtSwapAdjacent(p->pOn, nw, j);
            Abc_TtSwapAdjacent(p->pOff, nw, j);
        }
        if ( p->nVars > 6 )
            for ( w = 0; w < nw/2; ++w )
                p->pOn[w] |= p->pOn[w+nw/2], p->pOff[w] |= p->pOff[w+nw/2];
        else
        {
            Step = 1 << (p->nVars-1);
            Mask = Bmc_Cas2Mask(p->nVars-1);
            p->pOn[0] = (p->pOn[0] | (p->pOn[0] >> Step)) & Mask;
            p->pOff[0] = (p->pOff[0] | (p->pOff[0] >> Step)) & Mask;
        }
        memmove(p->Vars+i, p->Vars+i+1, sizeof(int)*(p->nVars-i-1));
        p->nVars--;
    }
}

/**Function*************************************************************

  Synopsis    [Ranks residual information and computes a canonical hash.]

  Description [Input names are omitted from the hash. With free bindings,
  equal tables with the same variable positions have the same future
  synthesis problem. Permutations of these positions are not canonicalized.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Cas2Score( Bmc_Cas2State_t * p )
{
    int w, n = 1 << p->nVars, nw = Abc_TtWordNum(p->nVars), nOn = 0, nOff = 0;
    word Hash = ABC_CONST(1469598103934665603);
    for ( w = 0; w < nw; ++w )
    {
        nOn += Abc_TtCountOnes(p->pOn[w]);
        nOff += Abc_TtCountOnes(p->pOff[w]);
        Hash = (Hash ^ p->pOn[w]) * ABC_CONST(1099511628211);
        Hash = (Hash ^ p->pOff[w]) * ABC_CONST(1099511628211);
    }
    p->Hash = Hash ^ p->nVars;
    // Each on/off minterm pair must remain distinguishable; don't-cares
    // impose no distinction. Normalize this information quantity by n*n.
    // Support dominates the score. Products fit in 64 bits for N <= 16.
    p->Score = (word)p->nVars * 2000000 + (word)nOn*nOff*4000000/((word)n*n);
}

/**Function*************************************************************

  Synopsis    [Indexes a retained residual from a completed beam layer.]

  Description [Layers are visited in increasing depth. Only retained states
  are indexed: an evicted, unexplored candidate must not exclude a later one.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Cas2Remember( Bmc_Cas2Man_t * p, Bmc_Cas2State_t * pState )
{
    int Bin = (int)((pState->Hash ^ (pState->Hash >> 32)) & (p->nBins-1));
    pState->iHashNext = p->pBins[Bin];
    p->pBins[Bin] = Vec_PtrSize(p->vStates);
    Vec_PtrPush(p->vStates, pState);
}

/**Function*************************************************************

  Synopsis    [Retains distinct promising residuals in a bounded beam.]

  Description [Checks every retained earlier layer and the current beam.
  A hash match is followed by an exact comparison of both partial care sets.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Cas2Keep( Bmc_Cas2Man_t * p, Bmc_Cas2State_t ** ppBeam, int * pnBeam, Bmc_Cas2State_t * pNew )
{
    Bmc_Cas2State_t * pOld;
    int i, Pos;
    Bmc_Cas2Score(pNew);
    p->nCandidates++;
    for ( i = p->pBins[(pNew->Hash ^ (pNew->Hash >> 32)) & (p->nBins-1)]; i >= 0; i = pOld->iHashNext )
    {
        pOld = (Bmc_Cas2State_t *)Vec_PtrEntry(p->vStates, i);
        if ( pOld->Hash == pNew->Hash && Bmc_Cas2Equal(pOld, pNew) )
            { Bmc_Cas2Free(pNew); return; }
    }
    for ( i = 0; i < *pnBeam; ++i )
        if ( ppBeam[i]->Hash == pNew->Hash && Bmc_Cas2Equal(ppBeam[i], pNew) )
            { Bmc_Cas2Free(pNew); return; }
    for ( Pos = 0; Pos < *pnBeam && ppBeam[Pos]->Score <= pNew->Score; ++Pos ) {}
    if ( Pos == p->pPars->nBeam ) { Bmc_Cas2Free(pNew); return; }
    if ( *pnBeam == p->pPars->nBeam ) Bmc_Cas2Free(ppBeam[--*pnBeam]);
    for ( i = (*pnBeam)++; i > Pos; --i ) ppBeam[i] = ppBeam[i-1];
    ppBeam[Pos] = pNew;
}

/**Function*************************************************************

  Synopsis    [Finds a parity-labelled union-find root.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Cas2Root( int * pParents, int x )
{
    int r = x, Phase = 0, Next, Edge;
    while ( (pParents[r] >> 1) != r )
    {
        Phase ^= pParents[r] & 1;
        r = pParents[r] >> 1;
    }
    while ( x != r )
    {
        Next = pParents[x] >> 1;
        Edge = pParents[x] & 1;
        pParents[x] = 2*r + Phase;
        Phase ^= Edge;
        x = Next;
    }
    return r;
}

/**Function*************************************************************

  Synopsis    [Adds an equality or inequality between slice orientations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Cas2Join( int * pParents, int a, int b, int Phase )
{
    int ra = Bmc_Cas2Root(pParents, a), rb = Bmc_Cas2Root(pParents, b);
    Phase ^= (pParents[a] ^ pParents[b]) & 1;
    if ( ra == rb ) return Phase == 0;
    if ( ra < rb ) pParents[rb] = 2*ra + Phase;
    else          pParents[ra] = 2*rb + Phase;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Peels a last LUT for one freely selected primary-input group.]

  Description [For each assignment to its PI group, a nonconstant cofactor
  must pass or invert the previous rail. A constant cofactor can ignore it,
  leaving no predecessor constraint. Parity equations choose orientations
  that permit deleting inputs. Component orientations and variable orders
  explore different residual functions without calling a SAT solver.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Cas2Group( Bmc_Cas2Man_t * p, Bmc_Cas2State_t * pState, unsigned Mask,
    Bmc_Cas2State_t ** ppBeam, int * pnBeam )
{
    Bmc_Cas2State_t * pNew;
    int S[CAS2_MAX_VARS], R[CAS2_MAX_VARS], Order[CAS2_MAX_VARS];
    int Perm[CAS2_MAX_VARS], SwapA[CAS2_MAX_VARS], SwapB[CAS2_MAX_VARS], nSwaps = 0, nWords;
    int k = 0, nr = 0, ns, nw, i, j, s, t, r, w, Mode, a, Good, Same, Diff;
    int * pParents, * pSaved, * pVotes, * pRoots;
    unsigned char * pType, * pPhase;
    word * pOn, * pOff, * pA, * pB, * pC, * pD;
    word On, Off, Care;
    for ( i = 0; i < pState->nVars; ++i )
        if ( Mask & (1u << i) ) S[k++] = i;
        else                   R[nr++] = i;
    ns = 1 << k;
    nw = Abc_TtWordNum(nr);
    nWords = Abc_TtWordNum(pState->nVars);
    pOn = p->pOn; pOff = p->pOff;
    pParents = p->pParents; pSaved = p->pSaved; pVotes = p->pVotes; pRoots = p->pRoots;
    pType = p->pType; pPhase = p->pPhase;
    memcpy(p->pPackedOn, pState->pOn, sizeof(word)*nWords);
    memcpy(p->pPackedOff, pState->pOff, sizeof(word)*nWords);
    // Put the complementary variables first, making each slice contiguous.
    for ( i = 0; i < pState->nVars; ++i ) Perm[i] = i;
    for ( i = 0; i < pState->nVars; ++i )
    {
        a = i < nr ? R[i] : S[i-nr];
        for ( j = i; Perm[j] != a; ++j ) {}
        if ( j == i ) continue;
        Abc_TtSwapVars(p->pPackedOn, pState->nVars, i, j);
        Abc_TtSwapVars(p->pPackedOff, pState->nVars, i, j);
        SwapA[nSwaps] = i; SwapB[nSwaps++] = j;
        Perm[j] = Perm[i]; Perm[i] = a;
    }
    for ( s = 0; s < ns; ++s )
    {
        pA = pOn+s*nw; pB = pOff+s*nw;
        if ( nr >= 6 )
        {
            memcpy(pA, p->pPackedOn+s*nw, sizeof(word)*nw);
            memcpy(pB, p->pPackedOff+s*nw, sizeof(word)*nw);
        }
        else
        {
            r = s << nr;
            pA[0] = (p->pPackedOn[r >> 6] >> (r & 63)) & Bmc_Cas2Mask(nr);
            pB[0] = (p->pPackedOff[r >> 6] >> (r & 63)) & Bmc_Cas2Mask(nr);
        }
        On = Off = 0;
        p->pBalance[s] = 0;
        for ( w = 0; w < nw; ++w )
        {
            On |= pA[w]; Off |= pB[w];
            p->pBalance[s] += Abc_TtCountOnes(pA[w])-Abc_TtCountOnes(pB[w]);
        }
        pType[s] = (On != 0)*2 + (Off != 0);
        if ( pType[s] != 3 )
        {
            memset(pA, 0, sizeof(word)*nw); memset(pB, 0, sizeof(word)*nw);
            p->pBalance[s] = 0;
        }
    }
    // Pair constraints depend on the group, not on the orientation mode.
    for ( i = 0; i < k; ++i )
        for ( s = 0; s < ns; ++s )
            if ( !(s & (1 << i)) )
            {
                t = s | (1 << i);
                pA = pOn+s*nw; pB = pOff+s*nw;
                pC = pOn+t*nw; pD = pOff+t*nw;
                Same = Diff = 0;
                for ( w = 0; w < nw; ++w )
                {
                    Same |= (pA[w] & pC[w]) != 0 || (pB[w] & pD[w]) != 0;
                    Diff |= (pA[w] & pD[w]) != 0 || (pB[w] & pC[w]) != 0;
                    if ( Same && Diff ) break;
                }
                p->pPairs[i*ns+s] = Same | (Diff << 1);
            }
    for ( Mode = 0; Mode < 4; ++Mode )
    {
        for ( s = 0; s < ns; ++s ) pParents[s] = 2*s;
        for ( i = 0; i < k; ++i ) Order[i] = Mode & 1 ? k-1-i : i;
        if ( Mode >= 2 )
            for ( i = k-1; i > 0; --i )
            {
                j = Bmc_Cas2Random(p) % (i+1);
                a = Order[j]; Order[j] = Order[i]; Order[i] = a;
            }
        for ( j = 0; j < k; ++j )
        {
            i = Order[j];
            memcpy(pSaved, pParents, sizeof(int)*ns);
            Good = 1;
            for ( s = 0; s < ns && Good; ++s )
                if ( !(s & (1 << i)) )
                {
                    t = s | (1 << i);
                    Same = p->pPairs[i*ns+s] & 1;
                    Diff = p->pPairs[i*ns+s] >> 1;
                    if ( Same && Diff ) Good = 0;
                    else if ( Same || Diff ) Good = Bmc_Cas2Join(pParents, s, t, Diff);
                }
            if ( !Good ) memcpy(pParents, pSaved, sizeof(int)*ns);
        }
        memset(pVotes, 0, sizeof(int)*ns);
        for ( s = 0; s < ns; ++s )
        {
            r = pRoots[s] = Bmc_Cas2Root(pParents, s);
            pPhase[s] = pParents[s] & 1;
            a = p->pBalance[s];
            pVotes[r] += pPhase[s] ? -a : a;
        }
        for ( s = 0; s < ns; ++s )
            if ( pRoots[s] == s )
            {
                if ( Mode == 3 ) pVotes[s] = (Bmc_Cas2Random(p) & 1) != 0;
                else             pVotes[s] = pVotes[s] > 0;
            }
        pNew = ABC_CALLOC(Bmc_Cas2State_t, 1);
        pNew->pNext = pState;
        pNew->nVars = pState->nVars;
        memcpy(pNew->Vars, pState->Vars, sizeof(int)*pState->nVars);
        pNew->pOn = ABC_CALLOC(word, nWords);
        pNew->pOff = ABC_CALLOC(word, nWords);
        pNew->pLut = ABC_CALLOC(unsigned char, 2*ns);
        pNew->nPis = k;
        for ( i = 0; i < k; ++i ) pNew->Pis[i] = pState->Vars[S[i]];
        for ( s = 0; s < ns; ++s )
        {
            a = pPhase[s] ^ pVotes[pRoots[s]];
            if ( pType[s] != 3 )
            {
                pNew->pLut[2*s] = pNew->pLut[2*s+1] = pType[s] == 2;
                continue;
            }
            pNew->pLut[2*s] = a;
            pNew->pLut[2*s+1] = a ^ 1;
            pA = a ? pOff+s*nw : pOn+s*nw;
            pB = a ? pOn+s*nw : pOff+s*nw;
            if ( nr >= 6 )
            {
                memcpy(pNew->pOn+s*nw, pA, sizeof(word)*nw);
                memcpy(pNew->pOff+s*nw, pB, sizeof(word)*nw);
            }
            else
            {
                r = s << nr;
                pNew->pOn[r >> 6] |= pA[0] << (r & 63);
                pNew->pOff[r >> 6] |= pB[0] << (r & 63);
            }
        }
        for ( i = nSwaps-1; i >= 0; --i )
        {
            Abc_TtSwapVars(pNew->pOn, pNew->nVars, SwapA[i], SwapB[i]);
            Abc_TtSwapVars(pNew->pOff, pNew->nVars, SwapA[i], SwapB[i]);
        }
        Bmc_Cas2Reduce(pNew);
        // Complementing a residual and its outgoing rail pin is harmless.
        nw = Abc_TtWordNum(pNew->nVars);
        for ( w = 0; w < nw && !(pNew->pOn[w] | pNew->pOff[w]); ++w ) {}
        if ( w < nw )
        {
            Care = pNew->pOn[w] | pNew->pOff[w];
            if ( pNew->pOn[w] & (Care & (0-Care)) )
            {
                pA = pNew->pOn; pNew->pOn = pNew->pOff; pNew->pOff = pA;
                for ( s = 0; s < ns; ++s )
                {
                    a = pNew->pLut[2*s]; pNew->pLut[2*s] = pNew->pLut[2*s+1]; pNew->pLut[2*s+1] = a;
                }
            }
        }
        nw = Abc_TtWordNum(nr);
        Bmc_Cas2Keep(p, ppBeam, pnBeam, pNew);
        if ( *pnBeam && ppBeam[0]->nVars <= p->pPars->nLutSize ) break;
    }
    p->nGroups++;
}

/**Function*************************************************************

  Synopsis    [Checks the complete cascade on every original input assignment.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Cas2Verify( Bmc_Cas2State_t * pResult, word * pTruth, int nVars )
{
    Bmc_Cas2State_t * p;
    int x, i, Address, Value;
    for ( x = 0; x < (1 << nVars); ++x )
    {
        Address = 0;
        for ( i = 0; i < pResult->nVars; ++i ) Address |= ((x >> pResult->Vars[i]) & 1) << i;
        Value = Abc_TtGetBit(pResult->pOn, Address);
        for ( p = pResult; p->pNext; p = p->pNext )
        {
            Address = Value;
            for ( i = 0; i < p->nPis; ++i ) Address |= ((x >> p->Pis[i]) & 1) << (i+1);
            Value = p->pLut[Address];
        }
        if ( Value != Abc_TtGetBit(pTruth, x) ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prints the independently checked LUT truth tables and bindings.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Cas2Print( Bmc_Cas2State_t * pResult, int nVars, int K )
{
    Bmc_Cas2State_t * p;
    int i, m, nNodes = 1;
    for ( p = pResult; p->pNext; p = p->pNext ) nNodes++;
    printf("Realization of given %d-input function using %d LUTs of at most %d inputs:\n", nVars, nNodes, K);
    printf("r0 = %d'b", 1 << pResult->nVars);
    for ( m = (1 << pResult->nVars)-1; m >= 0; --m ) printf("%d", Abc_TtGetBit(pResult->pOn, m));
    printf("(");
    for ( i = pResult->nVars-1; i >= 0; --i ) printf(" x%d", pResult->Vars[i]);
    printf(" )\n");
    for ( p = pResult, nNodes = 1; p->pNext; p = p->pNext, nNodes++ )
    {
        printf("r%d = %d'b", nNodes, 1 << (p->nPis+1));
        for ( m = (1 << (p->nPis+1))-1; m >= 0; --m ) printf("%d", p->pLut[m]);
        printf("(");
        for ( i = p->nPis-1; i >= 0; --i ) printf(" x%d", p->Pis[i]);
        printf(" r%d )\n", nNodes-1);
    }
}

/**Function*************************************************************

  Synopsis    [Writes the verified cascade as BLIF and portable Verilog.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Cas2Dump( Bmc_Cas2State_t * pResult, word * pTruth, int nVars, int K )
{
    Bmc_Cas2State_t * p = pResult;
    FILE * pBlif, * pVerilog;
    char Base[96], Name[112];
    word Hash = ABC_CONST(1469598103934665603);
    int i, j, m, n, Bit, nNodes = 1, Good;
    for ( i = 0; i < Abc_TtWordNum(nVars); ++i ) Hash = (Hash ^ pTruth[i])*ABC_CONST(1099511628211);
    for ( p = pResult; p->pNext; p = p->pNext ) nNodes++;
    snprintf(Base, sizeof(Base), "lutcasdec2_N%d_K%d_M%d_%016llx", nVars, K, nNodes, (unsigned long long)Hash);
    snprintf(Name, sizeof(Name), "%s.blif", Base);
    pBlif = fopen(Name, "w");
    if ( !pBlif ) { Abc_Print(-1, "Cannot create %s.\n", Name); return 0; }
    snprintf(Name, sizeof(Name), "%s.v", Base);
    pVerilog = fopen(Name, "w");
    if ( !pVerilog ) { fclose(pBlif); Abc_Print(-1, "Cannot create %s.\n", Name); return 0; }
    fprintf(pBlif, ".model lutcasdec2\n.inputs");
    fprintf(pVerilog, "module lutcasdec2 (");
    for ( i = 0; i < nVars; ++i )
    {
        fprintf(pBlif, " x%d", i);
        fprintf(pVerilog, "x%d, ", i);
    }
    fprintf(pBlif, "\n.outputs y\n");
    fprintf(pVerilog, "y);\ninput ");
    for ( i = 0; i < nVars; ++i ) fprintf(pVerilog, "%sx%d", i ? ", " : "", i);
    fprintf(pVerilog, ";\noutput y;\n");
    p = pResult;
    for ( j = 0; j < nNodes; ++j )
    {
        n = j ? p->nPis+1 : pResult->nVars;
        fprintf(pBlif, ".names");
        if ( j ) fprintf(pBlif, " r%d", j-1);
        for ( i = (j != 0); i < n; ++i )
            fprintf(pBlif, " x%d", j ? p->Pis[i-1] : pResult->Vars[i]);
        fprintf(pBlif, " r%d\n", j);
        for ( m = 0; m < (1 << n); ++m )
        {
            Bit = j ? p->pLut[m] : Abc_TtGetBit(pResult->pOn, m);
            if ( !Bit ) continue;
            for ( i = 0; i < n; ++i ) fprintf(pBlif, "%d", (m >> i) & 1);
            fprintf(pBlif, "%s1\n", n ? " " : "");
        }
        fprintf(pVerilog, "wire r%d;\nlocalparam [%d:0] lut%d = %d'b", j, (1 << n)-1, j, 1 << n);
        for ( m = (1 << n)-1; m >= 0; --m ) fprintf(pVerilog, "%d", j ? p->pLut[m] : Abc_TtGetBit(pResult->pOn, m));
        fprintf(pVerilog, ";\nassign r%d = lut%d[", j, j);
        if ( !n ) fprintf(pVerilog, "0");
        else
        {
            fprintf(pVerilog, "{");
            for ( i = n-1; i >= (j != 0); --i )
                fprintf(pVerilog, "%sx%d", i == n-1 ? "" : ", ", j ? p->Pis[i-1] : pResult->Vars[i]);
            if ( j ) fprintf(pVerilog, "%sr%d", n > 1 ? ", " : "", j-1);
            fprintf(pVerilog, "}");
        }
        fprintf(pVerilog, "];\n");
        if ( j ) p = p->pNext;
    }
    fprintf(pBlif, ".names r%d y\n1 1\n.end\n", nNodes-1);
    fprintf(pVerilog, "assign y = r%d;\nendmodule\n", nNodes-1);
    Good = !ferror(pBlif) && !ferror(pVerilog);
    if ( fclose(pBlif) ) Good = 0;
    if ( fclose(pVerilog) ) Good = 0;
    if ( !Good ) Abc_Print(-1, "Error writing cascade files.\n");
    else printf("Written %s.blif and %s.v.\n", Base, Base);
    return Good;
}

/**Function*************************************************************

  Synopsis    [Searches successive residual layers, retaining a bounded beam.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Cas2Run( Bmc_Cas2Par_t * pPars, word * pTruth, Bmc_Cas2Res_t * pRes )
{
    Bmc_Cas2Man_t Man, * p = &Man;
    Bmc_Cas2State_t ** ppBeam, ** ppNext, ** ppTemp, * pState, * pResult = NULL;
    int i, j, m, nBeam = 1, nNext, Depth, Ret = 0, nGroups, nAll, k, fNodeLimit = 0;
    unsigned Mask, Limit, Low, Next;
    abctime clk = Abc_Clock();
    memset(p, 0, sizeof(*p));
    memset(pRes, 0, sizeof(*pRes));
    p->pPars = pPars;
    p->Random = (unsigned)pPars->Seed ^ 0x9e3779b9u;
    if ( !p->Random ) p->Random = 1;
    p->timeStop = pPars->nTime ? clk + (abctime)pPars->nTime*CLOCKS_PER_SEC : 0;
    p->vStates = Vec_PtrAlloc(64);
    for ( p->nBins = 16; p->nBins < 2*pPars->nBeam*pPars->nNodes; p->nBins *= 2 ) {}
    p->pBins = ABC_ALLOC(int, p->nBins);
    for ( i = 0; i < p->nBins; ++i ) p->pBins[i] = -1;
    Bmc_Cas2Workspace(p, 1);
    ppBeam = ABC_ALLOC(Bmc_Cas2State_t *, pPars->nBeam);
    ppNext = ABC_ALLOC(Bmc_Cas2State_t *, pPars->nBeam);
    pState = ABC_CALLOC(Bmc_Cas2State_t, 1);
    pState->nVars = pPars->nVars;
    for ( i = 0; i < pState->nVars; ++i ) pState->Vars[i] = i;
    m = Abc_TtWordNum(pState->nVars);
    pState->pOn = ABC_ALLOC(word, m);
    pState->pOff = ABC_ALLOC(word, m);
    for ( i = 0; i < m; ++i ) pState->pOn[i] = pTruth[i], pState->pOff[i] = ~pTruth[i];
    pState->pOn[m-1] &= Bmc_Cas2Mask(pState->nVars);
    pState->pOff[m-1] &= Bmc_Cas2Mask(pState->nVars);
    Bmc_Cas2Reduce(pState);
    Bmc_Cas2Score(pState);
    ppBeam[0] = pState;
    Bmc_Cas2Remember(p, pState);
    for ( Depth = 1; Depth <= pPars->nNodes && !Bmc_Cas2Stop(p); ++Depth )
    {
        if ( ppBeam[0]->nVars <= pPars->nLutSize ) { pResult = ppBeam[0]; break; }
        if ( Depth == pPars->nNodes ) { fNodeLimit = 1; break; }
        nNext = 0;
        for ( i = 0; i < nBeam && !Bmc_Cas2Stop(p); ++i )
        {
            pState = ppBeam[i];
            k = pPars->nLutSize-1;
            Limit = 1u << pState->nVars;
            nAll = 1;
            for ( j = 1; j <= k; ++j ) nAll = nAll*(pState->nVars-j+1)/j;
            nGroups = 0;
            for ( Mask = (1u << k)-1; Mask < Limit && !Bmc_Cas2Stop(p); Mask = Next )
            {
                Low = Mask & (0u-Mask);
                Next = Mask+Low;
                Next |= ((Next ^ Mask) >> 2)/Low;
                // Reservoir-style acceptance bounds work for larger supports.
                if ( (unsigned)(Bmc_Cas2Random(p) % nAll--) >= (unsigned)(pPars->nGroups-nGroups) ) continue;
                Bmc_Cas2Group(p, pState, Mask, ppNext, &nNext);
                if ( ++nGroups == pPars->nGroups || (nNext && ppNext[0]->nVars <= pPars->nLutSize) ) break;
            }
            if ( nNext && ppNext[0]->nVars <= pPars->nLutSize ) break;
        }
        for ( i = 0; i < nNext; ++i ) Bmc_Cas2Remember(p, ppNext[i]);
        if ( !nNext ) break;
        ppTemp = ppBeam; ppBeam = ppNext; ppNext = ppTemp; nBeam = nNext;
        if ( pPars->fVerbose && !pPars->fBatch )
            printf("Backward layer %d: %d residuals, best support %d, groups %llu.\n",
                Depth, nBeam, ppBeam[0]->nVars, (unsigned long long)p->nGroups);
        if ( ppBeam[0]->nVars <= pPars->nLutSize ) { pResult = ppBeam[0]; break; }
    }
    if ( pResult && !Bmc_Cas2Verify(pResult, pTruth, pPars->nVars) )
    {
        Abc_Print(-1, "Internal error: cascade verification failed.\n");
        Ret = 1;
    }
    else if ( pResult )
    {
        for ( pState = pResult; pState; pState = pState->pNext ) pRes->nNodes++;
        if ( !pPars->fBatch )
        {
            Bmc_Cas2Print(pResult, pPars->nVars, pPars->nLutSize);
            printf("Verified exhaustively. Heuristic solution; minimum not proved.\n");
        }
        if ( pPars->fDump && !Bmc_Cas2Dump(pResult, pTruth, pPars->nVars, pPars->nLutSize) ) Ret = 1;
    }
    else if ( !pPars->fBatch ) printf("UNKNOWN: %s; no cascade found within the search budget.\n", p->fTimeout ? "time limit" : fNodeLimit ? "LUT-count limit" : "beam exhausted");
    pRes->Time = (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC;
    pRes->fTimeout = p->fTimeout;
    if ( !pPars->fBatch )
        printf("Search: %llu groups, %llu residuals. Total runtime = %.6f sec\n",
            (unsigned long long)p->nGroups, (unsigned long long)p->nCandidates, pRes->Time);
    Vec_PtrForEachEntry(Bmc_Cas2State_t *, p->vStates, pState, i) Bmc_Cas2Free(pState);
    Vec_PtrFree(p->vStates);
    ABC_FREE(p->pBins);
    Bmc_Cas2Workspace(p, 0);
    ABC_FREE(ppBeam); ABC_FREE(ppNext);
    return Ret;
}

/**Function*************************************************************

  Synopsis    [Reads one hexadecimal truth table, inferring its input count.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word * Bmc_Cas2ReadHex( char * pHex, int * pnVars )
{
    word * pTruth;
    int i, n;
    if ( pHex[0] == '0' && (pHex[1] == 'x' || pHex[1] == 'X') ) pHex += 2;
    n = (int)strlen(pHex);
    if ( n < 1 || n > (1 << (CAS2_MAX_VARS-2)) || (n & (n-1)) )
        { Abc_Print(-1, "Expected 2^(N-2) hexadecimal digits, N in 2..16.\n"); return NULL; }
    for ( i = 0; i < n; ++i )
        if ( !Abc_TtIsHexDigit(pHex[i]) )
            { Abc_Print(-1, "Truth table contains a non-hexadecimal digit.\n"); return NULL; }
    *pnVars = 2 + (n == 1 ? 0 : Abc_Base2Log(n));
    pTruth = ABC_CALLOC(word, Abc_TtWordNum(*pnVars));
    Abc_TtReadHex(pTruth, pHex);
    return pTruth;
}

/**Function*************************************************************

  Synopsis    [Synthesizes a text file of truth tables and reports totals.]

  Description [Streams one hexadecimal table per line, as in lutcasdec -F.
  Widths are inferred independently. Blank lines and # comments are skipped.
  A search failure is UNKNOWN; malformed input or an internal error aborts.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc_Cas2File( Bmc_Cas2Par_t * pPars, char * pFileName )
{
    FILE * pFile = fopen(pFileName, "r");
    char * pBuffer, * pHex, * pEnd, * pTail;
    int nSize = (1 << (CAS2_MAX_VARS-2))+256, i, Ret = 0;
    word Line = 0, nFuncs = 0, nSolved = 0, nTotal = 0, nTimeouts = 0;
    word Hist[CAS2_MAX_NODES+1] = {0}, * pTruth;
    double Time = 0;
    Bmc_Cas2Res_t Res;
    if ( !pFile ) { Abc_Print(-1, "Cannot open truth-table file %s.\n", pFileName); return 1; }
    pBuffer = ABC_ALLOC(char, nSize);
    pPars->fBatch = 1;
    printf("Considering truth tables from %s (K=%d, M=%d, B=%d, G=%d).\n",
        pFileName, pPars->nLutSize, pPars->nNodes, pPars->nBeam, pPars->nGroups);
    while ( (!pPars->nLimit || nFuncs < (word)pPars->nLimit) && fgets(pBuffer, nSize, pFile) )
    {
        Line++;
        if ( strlen(pBuffer) == (size_t)nSize-1 && !strchr(pBuffer, '\n') )
            { Abc_Print(-1, "Input line is too long.\n"); Ret = 1; break; }
        for ( pHex = pBuffer; isspace((unsigned char)*pHex); ++pHex ) {}
        if ( !*pHex || *pHex == '#' ) continue;
        for ( pEnd = pHex; *pEnd && !isspace((unsigned char)*pEnd); ++pEnd ) {}
        pTail = pEnd;
        while ( isspace((unsigned char)*pTail) ) pTail++;
        if ( *pTail && *pTail != '#' )
            { Abc_Print(-1, "Expected one truth table per line.\n"); Ret = 1; break; }
        *pEnd = 0;
        pTruth = Bmc_Cas2ReadHex(pHex, &pPars->nVars);
        if ( !pTruth ) { Ret = 1; break; }
        Ret = Bmc_Cas2Run(pPars, pTruth, &Res);
        ABC_FREE(pTruth);
        if ( Ret ) break;
        nFuncs++;
        Time += Res.Time;
        if ( Res.nNodes ) nSolved++, nTotal += Res.nNodes, Hist[Res.nNodes]++;
        else nTimeouts += Res.fTimeout;
        if ( pPars->fVerbose )
            printf("Function %llu (line %llu): N=%d LUTs=%d %s Time=%.6f sec\n",
                (unsigned long long)nFuncs, (unsigned long long)Line, pPars->nVars, Res.nNodes,
                Res.nNodes ? "verified" : "UNKNOWN", Res.Time);
    }
    if ( ferror(pFile) ) { Abc_Print(-1, "Error reading truth-table file.\n"); Ret = 1; }
    if ( Ret ) Abc_Print(-1, "Stopped at %s:%llu; the totals below are partial.\n", pFileName, (unsigned long long)Line);
    else if ( !nFuncs ) { Abc_Print(-1, "No truth tables found in %s.\n", pFileName); Ret = 1; }
    for ( i = 1; i <= CAS2_MAX_NODES; ++i )
        if ( Hist[i] ) printf("%2d LUTs: %llu functions\n", i, (unsigned long long)Hist[i]);
    printf("Batch: functions=%llu solved=%llu unknown=%llu timeouts=%llu LUTs=%llu average=%.3f Time=%.6f sec\n",
        (unsigned long long)nFuncs, (unsigned long long)nSolved, (unsigned long long)(nFuncs-nSolved),
        (unsigned long long)nTimeouts, (unsigned long long)nTotal, nSolved ? (double)nTotal/nSolved : 0.0, Time);
    printf("LUT totals and average count verified solutions only; UNKNOWN does not prove nonexistence.\n");
    ABC_FREE(pBuffer);
    fclose(pFile);
    return Ret;
}

/**Function*************************************************************

  Synopsis    [Prints command usage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc_Cas2Usage( void )
{
    Abc_Print(-2, "usage: lutcasdec2 [-KMBGTSL <num>] [-F file] [-Y string] [-dvh] [hex]\n");
    Abc_Print(-2, "          heuristic backward single-rail LUT cascade decomposition without SAT\n");
    Abc_Print(-2, " -K <num> : maximum LUT inputs, at least 2 [default = 6]\n");
    Abc_Print(-2, " -M <num> : maximum LUT count, 1..64 [default = 64]\n");
    Abc_Print(-2, " -B <num> : retained residuals per layer, 1..256 [default = 16]\n");
    Abc_Print(-2, " -G <num> : PI groups tried per residual, 1..65536 [default = 512]\n");
    Abc_Print(-2, " -T <num> : total search time limit in seconds [default = 0: unlimited]\n");
    Abc_Print(-2, " -S <num> : reproducible search seed [default = 0]\n");
    Abc_Print(-2, " -F <file>: text file of hex truth tables, one per line (optional 0x)\n");
    Abc_Print(-2, " -L <num> : maximum functions to read with -F [default = 0: all]\n");
    Abc_Print(-2, " -Y <str> : symmetric function, values at weights 0..N\n");
    Abc_Print(-2, " -d       : export verified lutcasdec2_*.blif and portable Verilog .v\n");
    Abc_Print(-2, " -v       : print search progress; with -F, print one result per function\n");
    Abc_Print(-2, " -h       : print this help\n");
    Abc_Print(-2, " [hex]    : truth table; without hex/-Y use the current combinational network\n");
    Abc_Print(-2, " Supports 2..16 PIs. K is not limited to 6 or 8; unused pins are omitted.\n");
    Abc_Print(-2, " Input bindings are free. Later LUTs use one rail and at most K-1 PIs.\n");
    Abc_Print(-2, " Every result is verified; failure is UNKNOWN, never an UNSAT proof.\n");
    Abc_Print(-2, " File mode infers N per line and applies -T separately to each function.\n");
}

/**Function*************************************************************

  Synopsis    [Implements lutcasdec2, leaving the current network unchanged.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLutCasDec2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern char * Abc_NtkReadTruth( Abc_Ntk_t * pNtk );
    Bmc_Cas2Par_t Pars, * p = &Pars;
    Bmc_Cas2Res_t Res;
    Abc_Ntk_t * pNtk, * pAig;
    char * pOwned = NULL, * pHex = NULL, * pSym = NULL, * pFile = NULL, * pEnd;
    word * pTruth = NULL;
    long Value;
    int c, i, Ret = 1;
    memset(p, 0, sizeof(*p));
    p->nLutSize = 6; p->nNodes = 64; p->nBeam = 16; p->nGroups = 512;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "KMBGTSLFYdvh")) != EOF )
    {
        switch ( c )
        {
        case 'K': case 'M': case 'B': case 'G': case 'T': case 'S': case 'L':
            if ( globalUtilOptind >= argc ) { Abc_Print(-1, "Option -%c needs an integer.\n", c); goto finish; }
            errno = 0;
            Value = strtol(argv[globalUtilOptind++], &pEnd, 10);
            if ( errno || *pEnd || pEnd == argv[globalUtilOptind-1] || Value < 0 || Value > INT_MAX )
                { Abc_Print(-1, "Invalid nonnegative integer for -%c.\n", c); goto finish; }
            if      ( c == 'K' ) p->nLutSize = (int)Value;
            else if ( c == 'M' ) p->nNodes = (int)Value;
            else if ( c == 'B' ) p->nBeam = (int)Value;
            else if ( c == 'G' ) p->nGroups = (int)Value;
            else if ( c == 'T' ) p->nTime = (int)Value;
            else if ( c == 'L' ) p->nLimit = (int)Value;
            else                p->Seed = (int)Value;
            break;
        case 'F':
            if ( globalUtilOptind >= argc ) { Abc_Print(-1, "Option -F needs a file name.\n"); goto finish; }
            pFile = argv[globalUtilOptind++]; break;
        case 'Y':
            if ( globalUtilOptind >= argc ) { Abc_Print(-1, "Option -Y needs a string.\n"); goto finish; }
            pSym = argv[globalUtilOptind++]; break;
        case 'v': p->fVerbose ^= 1; break;
        case 'd': p->fDump ^= 1; break;
        case 'h': Bmc_Cas2Usage(); Ret = 0; goto finish;
        default: Bmc_Cas2Usage(); goto finish;
        }
    }
    if ( argc > globalUtilOptind+1 || (argc > globalUtilOptind && (pSym || pFile)) || (pFile && pSym) )
        { Abc_Print(-1, "Expected one truth table, -Y, -F, or the current network.\n"); goto finish; }
    if ( p->nLimit && !pFile )
        { Abc_Print(-1, "Option -L requires -F.\n"); goto finish; }
    if ( p->nLutSize < 2 || p->nNodes < 1 || p->nNodes > CAS2_MAX_NODES ||
         p->nBeam < 1 || p->nBeam > 256 || p->nGroups < 1 || p->nGroups > 65536 )
        { Abc_Print(-1, "Require K >= 2, M in 1..64, B in 1..256, G in 1..65536.\n"); goto finish; }
    if ( pFile ) { Ret = Bmc_Cas2File(p, pFile); goto finish; }
    if ( argc > globalUtilOptind ) pHex = argv[globalUtilOptind];
    if ( pSym )
    {
        p->nVars = (int)strlen(pSym)-1;
        if ( p->nVars < 2 || p->nVars > CAS2_MAX_VARS )
            { Abc_Print(-1, "Require 3..17 binary symmetric-function values.\n"); goto finish; }
        for ( i = 0; i <= p->nVars; ++i )
            if ( pSym[i] != '0' && pSym[i] != '1' )
                { Abc_Print(-1, "Symmetric-function values must be 0 or 1.\n"); goto finish; }
        pTruth = Abc_TtSymFunGenerate(pSym, p->nVars);
    }
    else
    {
        if ( !pHex )
        {
            pNtk = Abc_FrameReadNtk(pAbc);
            if ( !pNtk || Abc_NtkLatchNum(pNtk) || Abc_NtkCoNum(pNtk) != 1 ||
                 Abc_NtkCiNum(pNtk) < 2 || Abc_NtkCiNum(pNtk) > CAS2_MAX_VARS )
                { Abc_Print(-1, "Provide hex/-Y or a combinational single-output network with 2..16 PIs.\n"); goto finish; }
            pAig = Abc_NtkIsStrash(pNtk) ? pNtk : Abc_NtkStrash(pNtk, 0, 0, 0);
            if ( !pAig ) { Abc_Print(-1, "Could not strash the network.\n"); goto finish; }
            pHex = pOwned = Abc_NtkReadTruth(pAig);
            if ( pAig != pNtk ) Abc_NtkDelete(pAig);
            if ( !pHex ) { Abc_Print(-1, "Could not derive the truth table.\n"); goto finish; }
        }
        pTruth = Bmc_Cas2ReadHex(pHex, &p->nVars);
        if ( !pTruth ) goto finish;
    }
    Ret = Bmc_Cas2Run(p, pTruth, &Res);
finish:
    ABC_FREE(pOwned);
    ABC_FREE(pTruth);
    return Ret;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
