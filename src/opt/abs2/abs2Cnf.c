/**CFile****************************************************************

  FileName    [abs2Cnf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Incremental flop abstraction.]

  Synopsis    [Bounded resolution cuts for the abstraction unrolling.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 21, 2026.]

  Revision    [$Id: abs2Cnf.c,v 1.00 2026/10/21 00:00:00 alanmi Exp $]

  Reference   [Niklas Een's ZZ/Bip/Common/Clausify.cc, qClausify/tryElim.]

  Copyright (c) 2010-2014 The Regents of the University of California

  Permission is hereby granted, free of charge, to any person obtaining
  a copy of this software and associated documentation files (the
  "Software"), to deal in the Software without restriction, including
  without limitation the rights to use, copy, modify, merge, publish,
  distribute, sublicense, and/or sell copies of the Software, and to
  permit persons to whom the Software is furnished to do so, subject to
  the following conditions:

  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

***********************************************************************/

#include "abs2.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

#define ABS2_CNF_VARS 32
#define ABS2_CNF_CLAUSES 150
#define ABS2_CNF_DEF 6
#define ABS2_CNF_TRIALS 64
#define ABS2_CNF_REMOVED (~(word)0)

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Exchanges positive and negative literal masks.]

  Description [Low/high halves encode positive/negative literals. This also keeps the
  complete local scratch space bounded independently of circuit depth.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Abs2_CnfFlip( word C ) { return (C << 32) | (C >> 32); }

/**Function*************************************************************

  Synopsis    [Checks whether a packed clause contains opposite literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_CnfTautology( word C ) { return ((unsigned)C & (unsigned)(C >> 32)) != 0; }

/**Function*************************************************************

  Synopsis    [Returns the variables occurring in a packed CNF.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Abs2_CnfSupport( word * pCnf, int nClauses )
{
    word All = 0;
    int i;
    for ( i = 0; i < nClauses; ++i ) All |= pCnf[i];
    return (unsigned)All | (unsigned)(All >> 32);
}

/**Function*************************************************************

  Synopsis    [Returns the first occupied variable slot.]

  Description [Preserve ascending slot order while skipping unused slots.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abs2_CnfFirst( unsigned Bits )
{
    assert(Bits);
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_ctz(Bits);
#else
    return Abc_Tt6FirstBit((word)Bits);
#endif
}

/**Function*************************************************************

  Synopsis    [Finds or allocates a slot in a bounded local variable map.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_CnfVar( int Id, int * pIds, unsigned * pUsed )
{
    unsigned Bits;
    int i;
    for ( Bits = *pUsed; Bits; Bits &= Bits - 1 )
    {
        i = Abs2_CnfFirst(Bits);
        if ( pIds[i] == Id ) return i;
    }
    Bits = ~*pUsed;
    if ( !Bits ) return -1;
    i = Abs2_CnfFirst(Bits);
    *pUsed |= 1u << i;
    pIds[i] = Id;
    return i;
}

/**Function*************************************************************

  Synopsis    [Appends a packed clause as zero-terminated Gia literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abs2_CnfExportClause( word C, int * pIds, Vec_Int_t * vCnf )
{
    unsigned Bits = (unsigned)C | (unsigned)(C >> 32);
    for ( ; Bits; Bits &= Bits - 1 )
    {
        int i = Abs2_CnfFirst(Bits);
        if ( C & ((word)1 << i) ) Vec_IntPush(vCnf, pIds[i] << 1);
        if ( C & ((word)1 << (i + 32)) ) Vec_IntPush(vCnf, (pIds[i] << 1) | 1);
    }
    Vec_IntPush(vCnf, 0);
}

/**Function*************************************************************

  Synopsis    [Adds a non-tautological clause to a bounded local CNF.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_CnfClause( word * pCnf, int * pnClauses, int * pIds,
                         unsigned * pUsed, int a, int b, int c )
{
    int Lits[3], i, Var;
    word Clause = 0;
    Lits[0] = a; Lits[1] = b; Lits[2] = c;
    for ( i = 0; i < 3; ++i )
    {
        if ( !Lits[i] ) continue;
        if ( Lits[i] == 1 ) return 1;
        Var = Abs2_CnfVar(Lits[i] >> 1, pIds, pUsed);
        if ( Var < 0 ) return 0;
        Clause |= (word)1 << (Var + ((Lits[i] & 1) ? 32 : 0));
    }
    if ( !Abs2_CnfTautology(Clause) ) pCnf[(*pnClauses)++] = Clause;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Builds the full CNF definition of an AND or mux node.]

  Description [Every clause in this full definition contains its output variable.
  For every assignment to the fanins it admits exactly one output value.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_CnfDefinition( Gia_Man_t * pGia, int Id, int fMuxProp,
                              word * pCnf, int * pIds, unsigned * pUsed )
{
    Gia_Obj_t * pObj = Gia_ManObj(pGia, Id);
    int z = Id << 1, a, b, c, n = 0;
    assert(Gia_ObjIsAnd(pObj));
    if ( Gia_ObjIsMuxType(pObj) )
    {
        c = Gia_ObjRecognizeMuxLits(pGia, pObj, &a, &b);
        if ( !Abs2_CnfClause(pCnf, &n, pIds, pUsed, z, c ^ 1, a ^ 1) ||
             !Abs2_CnfClause(pCnf, &n, pIds, pUsed, z ^ 1, c ^ 1, a) ||
             !Abs2_CnfClause(pCnf, &n, pIds, pUsed, z, c, b ^ 1) ||
             !Abs2_CnfClause(pCnf, &n, pIds, pUsed, z ^ 1, c, b) ) return -1;
        if ( fMuxProp &&
             (!Abs2_CnfClause(pCnf, &n, pIds, pUsed, z, a ^ 1, b ^ 1) ||
              !Abs2_CnfClause(pCnf, &n, pIds, pUsed, z ^ 1, a, b)) ) return -1;
    }
    else
    {
        a = Gia_ObjFaninLit0p(pGia, pObj);
        b = Gia_ObjFaninLit1p(pGia, pObj);
        if ( !Abs2_CnfClause(pCnf, &n, pIds, pUsed, z ^ 1, a, 0) ||
             !Abs2_CnfClause(pCnf, &n, pIds, pUsed, z ^ 1, b, 0) ||
             !Abs2_CnfClause(pCnf, &n, pIds, pUsed, z, a ^ 1, b ^ 1) ) return -1;
    }
    assert(n <= ABS2_CNF_DEF);
    return n;
}

/**Function*************************************************************

  Synopsis    [Removes clauses marked as redundant.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_CnfCompact( word * pCnf, int n )
{
    int i, k = 0;
    for ( i = 0; i < n; ++i )
        if ( pCnf[i] != ABS2_CNF_REMOVED ) pCnf[k++] = pCnf[i];
    return k;
}

/**Function*************************************************************

  Synopsis    [Checks clause redundancy by unit propagation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_CnfRedundant( word * pCnf, int n, int Index )
{
    word False = pCnf[Index], Previous;
    int i;
    // Negate the tested clause and propagate all remaining clauses.
    do
    {
        Previous = False;
        for ( i = 0; i < n; ++i )
        {
            word Rest;
            if ( i == Index || pCnf[i] == ABS2_CNF_REMOVED ||
                 (pCnf[i] & Abs2_CnfFlip(False)) ) continue;
            Rest = pCnf[i] & ~False;
            if ( !Rest ) return 1;
            if ( !(Rest & (Rest - 1)) )
            {
                False |= Abs2_CnfFlip(Rest);
                if ( Abs2_CnfTautology(False) ) return 1;
            }
        }
    } while ( Previous != False );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Removes duplicate, subsumed and propagation-redundant clauses.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_CnfReduce( word * pCnf, int n, int (*pStop)(void *), void * pData )
{
    int i, j;
    for ( i = 0; i < n; ++i )
    {
        if ( !(i & 15) && pStop && pStop(pData) ) return -1;
        if ( pCnf[i] == ABS2_CNF_REMOVED ) continue;
        for ( j = 0; j < n; ++j )
        {
            word Diff;
            if ( i == j || pCnf[j] == ABS2_CNF_REMOVED ) continue;
            Diff = pCnf[i] & ~pCnf[j];
            if ( !Diff ) pCnf[j] = ABS2_CNF_REMOVED;
            else if ( !(Diff & (Diff - 1)) && (Abs2_CnfFlip(Diff) & pCnf[j]) )
                pCnf[j] &= ~Abs2_CnfFlip(Diff);
        }
    }
    n = Abs2_CnfCompact(pCnf, n);
    // Bound the cost of the stronger redundancy test. An over-budget trial
    // can always be rejected without changing the already accepted cut.
    if ( n > ABS2_CNF_CLAUSES ) return n;
    for ( i = 0; i < n; ++i )
    {
        if ( !(i & 15) && pStop && pStop(pData) ) return -1;
        if ( Abs2_CnfRedundant(pCnf, n, i) ) pCnf[i] = ABS2_CNF_REMOVED;
    }
    return Abs2_CnfCompact(pCnf, n);
}

/**Function*************************************************************

  Synopsis    [Replaces a small functional CNF with a smaller truth-table cover.]

  Description [Local resolution need not produce the smallest cover of the resulting
  function. For a small boundary, evaluate the existing CNF in parallel on
  all assignments, then accept a truth-table cover only if it has fewer
  clauses. Output variable zero is kept separate from the boundary variables.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_CnfMinimize( word * pCnf, int n, int * pIds, int nLeafMax )
{
    static const word Truths[6] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000)
    };
    int Slots[6], Cover[64], nLeaves = 0, nCover, i, j, Slot, Cube, Field;
    unsigned Used;
    word Allowed0 = ~(word)0, Allowed1 = ~(word)0, Result[64];
    if ( n <= 3 ) return n;
    Used = Abs2_CnfSupport(pCnf, n);
    assert(Used & 1);
    for ( i = 1; i < ABS2_CNF_VARS; ++i )
        if ( Used & (1u << i) )
        {
            if ( nLeaves == nLeafMax ) return n;
            Slots[nLeaves++] = i;
        }
    for ( i = 1; i < nLeaves; ++i )
    {
        Slot = Slots[i];
        for ( j = i; j && pIds[Slots[j-1]] > pIds[Slot]; --j ) Slots[j] = Slots[j-1];
        Slots[j] = Slot;
    }
    for ( i = 0; i < n; ++i )
    {
        word Clause = 0;
        for ( j = 0; j < nLeaves; ++j )
        {
            if ( pCnf[i] & ((word)1 << Slots[j]) ) Clause |= Truths[j];
            if ( pCnf[i] & ((word)1 << (Slots[j] + 32)) ) Clause |= ~Truths[j];
        }
        if ( !(pCnf[i] & (word)1) ) Allowed1 &= Clause;
        if ( !(pCnf[i] & ((word)1 << 32)) ) Allowed0 &= Clause;
    }
    // Check totality and uniqueness before treating the relation as a
    // Boolean function. Keep the original relation if this precondition fails.
    if ( Allowed0 != ~Allowed1 ) return n;
    nCover = Abc_Tt6Cnf(Allowed1, nLeaves, Cover);
    if ( nCover >= n ) return n;
    for ( i = 0; i < nCover; ++i )
    {
        Result[i] = 0;
        for ( j = 0, Cube = Cover[i]; j <= nLeaves; ++j, Cube >>= 2 )
        {
            Field = Cube & 3;
            if ( !Field ) continue;
            assert(Field != 3);
            Slot = j == nLeaves ? 0 : Slots[j];
            Result[i] |= (word)1 << (Slot + (Field == 2 ? 32 : 0));
        }
    }
    memcpy(pCnf, Result, sizeof(word) * nCover);
    return nCover;
}

/**Function*************************************************************

  Synopsis    [Builds a bounded resolution cut for an unrolled AND node.]

  Description [Return eliminated occurrences, or -1 if interrupted. Clauses are Gia
  literals separated by zero; constants are simplified before serialization.
  Unlike ZZ's definition stack and memo table, this grows one bounded root
  cut at a time. A shared gate is eligible only with zero clause growth.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs2_CnfResolve( Gia_Man_t * pGia, int Root, Vec_Int_t * vEncoded,
                    Vec_Int_t * vKeep, int Mode, int fMuxProp, Vec_Int_t * vCnf,
                    int * pnClausesSaved, int (*pStop)(void *), void * pData )
{
    word Main[ABS2_CNF_CLAUSES], Side[ABS2_CNF_DEF];
    word Result[ABS2_CNF_CLAUSES * (ABS2_CNF_DEF + 1)];
    int Ids[ABS2_CNF_VARS], TrialIds[ABS2_CNF_VARS], Tried[ABS2_CNF_TRIALS];
    int nMain, nSide, nResult, nTried = 0, nEliminated = 0, i, j, k, Best, Limit;
    unsigned Used = 1, TrialUsed;
    assert(Mode >= 1 && Mode <= 4);
    assert(Gia_ObjIsAnd(Gia_ManObj(pGia, Root)));
    if ( pnClausesSaved ) *pnClausesSaved = 0;
    Vec_IntClear(vCnf);
    // There is nothing to eliminate when both fanins already have complete
    // definitions. Preserve the general builder's literal and clause order,
    // including complemented fanins, without constructing its local tables.
    if ( !Gia_ObjIsMuxType(Gia_ManObj(pGia, Root)) )
    {
        int a = Gia_ObjFaninLit0p(pGia, Gia_ManObj(pGia, Root));
        int b = Gia_ObjFaninLit1p(pGia, Gia_ManObj(pGia, Root));
        if ( a >= 2 && b >= 2 && (a >> 1) != (b >> 1) &&
             Vec_IntEntry(vEncoded, a >> 1) && Vec_IntEntry(vEncoded, b >> 1) )
        {
            int z = Root << 1;
            int Lits[10] = { z ^ 1, a, 0, z ^ 1, b, 0, z, a ^ 1, b ^ 1, 0 };
            if ( pStop && pStop(pData) ) return -1;
            Vec_IntPushArray(vCnf, Lits, 10);
            return 0;
        }
    }
    memset(Ids, 0, sizeof(Ids));
    Ids[0] = Root;
    nMain = Abs2_CnfDefinition(pGia, Root, fMuxProp, Main, Ids, &Used);
    assert(nMain > 0);
    while ( nTried < ABS2_CNF_TRIALS )
    {
        word Pos, Neg, Pivot;
        if ( pStop && pStop(pData) ) return -1;
        Used = Abs2_CnfSupport(Main, nMain);
        assert(nMain > 0 && (Used & 1));
        Best = -1;
        for ( i = 1; i < ABS2_CNF_VARS; ++i )
        {
            if ( !(Used & (1u << i)) || Vec_IntEntry(vEncoded, Ids[i]) ||
                 !Gia_ObjIsAnd(Gia_ManObj(pGia, Ids[i])) ||
                 (Mode == 1 && Vec_IntEntry(vKeep, Ids[i])) ) continue;
            for ( k = 0; k < nTried; ++k ) if ( Tried[k] == Ids[i] ) break;
            if ( k != nTried ) continue;
            if ( Best < 0 || Ids[i] > Ids[Best] ) Best = i;
        }
        if ( Best < 0 ) break;
        Tried[nTried++] = Ids[Best];
        memcpy(TrialIds, Ids, sizeof(Ids));
        TrialUsed = Used;
        nSide = Abs2_CnfDefinition(pGia, Ids[Best], fMuxProp, Side, TrialIds, &TrialUsed);
        if ( nSide < 0 ) continue;
        Pos = (word)1 << Best;
        Neg = Pos << 32;
        Pivot = Pos | Neg;
        nResult = 0;
        for ( i = 0; i < nMain; ++i )
        {
            if ( !(Main[i] & Pivot) ) Result[nResult++] = Main[i];
            else for ( j = 0; j < nSide; ++j )
            {
                word C;
                assert(Side[j] & Pivot);
                if ( !((Main[i] & Pos) && (Side[j] & Neg)) &&
                     !((Main[i] & Neg) && (Side[j] & Pos)) ) continue;
                C = (Main[i] | Side[j]) & ~Pivot;
                if ( !Abs2_CnfTautology(C) ) Result[nResult++] = C;
            }
        }
        // The side is a total functional definition. Main/main resolvents
        // are implied by these cross-resolvents; side/side ones are tautologies.
        // This is substitution of that function, not arbitrary clause deletion.
        assert(nResult <= ABS2_CNF_CLAUSES * (ABS2_CNF_DEF + 1));
        nResult = Abs2_CnfReduce(Result, nResult, pStop, pData);
        if ( nResult < 0 ) return -1;
        Limit = nMain + (Vec_IntEntry(vKeep, Ids[Best]) ? 0 : nSide);
        if ( nResult > Limit || nResult > ABS2_CNF_CLAUSES ) continue;
        memcpy(Ids, TrialIds, sizeof(Ids));
        memcpy(Main, Result, sizeof(word) * nResult);
        nMain = nResult;
        ++nEliminated;
    }
    assert(nMain > 0 && (Abs2_CnfSupport(Main, nMain) & 1));
    if ( Mode >= 3 )
    {
        nResult = Abs2_CnfMinimize(Main, nMain, Ids, Mode == 3 ? 4 : 6);
        if ( pnClausesSaved ) *pnClausesSaved = nMain - nResult;
        nMain = nResult;
    }
    for ( i = 0; i < nMain; ++i )
    {
        Abs2_CnfExportClause(Main[i], Ids, vCnf);
    }
    return nEliminated;
}

/**Function*************************************************************

  Synopsis    [Exports the complete local definition of an unrolled node.]

  Description [Initial full definition for the bottom-up encoder. Its boundary can later
  be replaced by already clausified child definitions, as in ZZ's qClausify.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs2_CnfStart( Gia_Man_t * pGia, int Root, int fMuxProp, Vec_Int_t * vCnf )
{
    word Cnf[ABS2_CNF_DEF];
    int Ids[ABS2_CNF_VARS] = {0}, n, i;
    unsigned Used = 1;
    Ids[0] = Root;
    n = Abs2_CnfDefinition(pGia, Root, fMuxProp, Cnf, Ids, &Used);
    assert(n > 0);
    Vec_IntClear(vCnf);
    for ( i = 0; i < n; ++i )
    {
        Abs2_CnfExportClause(Cnf[i], Ids, vCnf);
    }
}

/**Function*************************************************************

  Synopsis    [Substitutes a child definition without increasing the clause budget.]

  Description [Substitute a total functional child definition into its parent. Only the
  clauses mentioning Pivot participate; unaffected parent clauses retain
  their order. No input is changed unless the whole substitution is accepted.
  The 32-variable bound excludes Pivot, matching ZZ's local representation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs2_CnfCombine( Vec_Int_t * vMain, Vec_Int_t * vSide, int Pivot, int fKeep,
                     Vec_Int_t * vScratch, int (*pStop)(void *), void * pData )
{
    word Pos[ABS2_CNF_CLAUSES+15], Neg[ABS2_CNF_CLAUSES+15];
    word Res[ABS2_CNF_CLAUSES*15];
    int Ids[ABS2_CNF_VARS] = {0};
    unsigned Used = 0;
    int nMain = 0, nSide = 0, nRest = 0, nPos = 0, nNeg = 0, nPosMain = 0, nNegMain = 0;
    int Which, Begin, End, i, j, Lit, Sign, Var, nRes = 0, Limit;
    Vec_Int_t * vCnf;
    Vec_IntForEachEntry(vMain, Lit, i) nMain += !Lit;
    Vec_IntForEachEntry(vSide, Lit, i) nSide += !Lit;
    if ( nMain > ABS2_CNF_CLAUSES || nSide > 15 ) return 0;
    Vec_IntClear(vScratch);
    for ( Which = 0; Which < 2; ++Which )
    {
        vCnf = Which ? vSide : vMain;
        for ( Begin = 0; Begin < Vec_IntSize(vCnf); Begin = End + 1 )
        {
            word C = 0;
            Sign = -1;
            for ( End = Begin; Vec_IntEntry(vCnf, End); ++End )
                if ( (Vec_IntEntry(vCnf, End) >> 1) == Pivot ) Sign = Vec_IntEntry(vCnf, End) & 1;
            if ( Sign < 0 )
            {
                assert(!Which); // A total definition cannot restrict its free boundary alone.
                Vec_IntPushArray(vScratch, Vec_IntArray(vCnf) + Begin, End - Begin + 1);
                ++nRest;
                continue;
            }
            for ( i = Begin; i < End; ++i )
            {
                Lit = Vec_IntEntry(vCnf, i);
                if ( (Lit >> 1) == Pivot ) continue;
                Var = Abs2_CnfVar(Lit >> 1, Ids, &Used);
                if ( Var < 0 ) return 0;
                C |= (word)1 << (Var + ((Lit & 1) ? 32 : 0));
            }
            if ( Sign ) Neg[nNeg++] = C;
            else Pos[nPos++] = C;
        }
        if ( !Which ) { nPosMain = nPos; nNegMain = nNeg; }
    }
    if ( pStop && pStop(pData) ) return -1;
    for ( i = 0; i < nPosMain; ++i )
        for ( j = nNegMain; j < nNeg; ++j )
        {
            word C = Pos[i] | Neg[j];
            if ( !Abs2_CnfTautology(C) ) Res[nRes++] = C;
        }
    for ( i = nPosMain; i < nPos; ++i )
        for ( j = 0; j < nNegMain; ++j )
        {
            word C = Pos[i] | Neg[j];
            if ( !Abs2_CnfTautology(C) ) Res[nRes++] = C;
        }
    assert(nRes <= ABS2_CNF_CLAUSES*15);
    nRes = Abs2_CnfReduce(Res, nRes, pStop, pData);
    if ( nRes < 0 ) return -1;
    Limit = nMain + (fKeep ? 0 : nSide);
    if ( nRest + nRes > Limit ) return 0;
    for ( i = 0; i < nRes; ++i )
    {
        Abs2_CnfExportClause(Res[i], Ids, vScratch);
    }
    Vec_IntClear(vMain);
    Vec_IntAppend(vMain, vScratch);
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
