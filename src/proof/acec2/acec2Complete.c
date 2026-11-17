/**CFile****************************************************************

  FileName    [acec2Complete.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Proposes missing low sum bits from surviving carry logic.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 12, 2026.]

  Revision    [$Id$]

***********************************************************************/

#include "acec2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Propagates a proposed arithmetic weight and polarity.]

  Description [Conflicting assignments are retained as unresolved evidence.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_CompleteAssign( Vec_Int_t * vRanks, Vec_Int_t * vPhase, Vec_Int_t * vQueue, int Lit, int Rank )
{
    int id = Lit >> 1;
    if ( !id || Rank < 0 || Vec_IntEntry(vRanks, id) >= 0 ) return;
    Vec_IntWriteEntry(vRanks, id, Rank); Vec_IntWriteEntry(vPhase, id, Lit & 1); Vec_IntPush(vQueue, id);
}

/**Function*************************************************************

  Synopsis    [Simulates newly appended gates on 256 independent cut patterns.]

  Description [Only filters proposals; it is not an equivalence proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_CompleteSim( Gia_Man_t * g, Vec_Wrd_t * vSim, word * pState )
{
    Gia_Obj_t * o;
    word value;
    int i, k;
    for ( i = Vec_WrdSize(vSim)/4; i < Gia_ManObjNum(g); i++ )
    {
        o = Gia_ManObj(g, i);
        for ( k = 0; k < 4; k++ )
        {
            value = 0;
            if ( Gia_ObjIsCi(o) )
            { value = Acec2_Random(pState); }
            else if ( Gia_ObjIsAnd(o) )
                value = Acec2_SimGate(g, i, vSim, 4, k);
            Vec_WrdPush(vSim, value);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Completes only unobserved positions of a proposed word.]

  Description [The retained outputs are unchanged. Cell identities and
  majority cuts suggest missing sum bits, but these suggestions are not
  trusted: a subsequent exact proof compares both completed words. Equality
  of completed words therefore proves every originally observed bit.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Acec2_CompleteWord( Acec2_Man_t * m, Vec_Int_t * vObserved, abctime Deadline, Vec_Int_t ** pvRules )
{
    Gia_Man_t * g = m->pGia, * q = NULL, * clean;
    Vec_Int_t * vRanks = Vec_IntStartFull(Gia_ManObjNum(g)), * vPhase = Vec_IntStart(Gia_ManObjNum(g));
    Vec_Int_t * vQueue = Vec_IntAlloc(1000), * vDone = Vec_IntStart(Vec_PtrSize(m->vCells));
    Vec_Int_t * vHead = Vec_IntStartFull(Gia_ManObjNum(g)), * vNext = Vec_IntStartFull(Vec_IntSize(m->vCarries)/6);
    Vec_Int_t * vXors = Vec_IntStartFull(Gia_ManObjNum(g));
    Vec_Int_t * vMap = Vec_IntStart(Gia_ManObjNum(g));
    Vec_Int_t * vBits = Vec_IntStartFull(Gia_ManCoNum(g)), * vScore = Vec_IntStartFull(Gia_ManCoNum(g));
    Vec_Wrd_t * vSim = Vec_WrdAlloc(1000);
    Vec_Wec_t * vRuleBits = Vec_WecStart(Gia_ManCoNum(g));
    Vec_Int_t * vRule;
    Gia_Obj_t * o;
    Acec2_Cell_t * cell;
    int i, j, k, id, owner, rank, phase, flip, sum, n, c, mask, value, ok, best, score, bestScore;
    int ins[3], chosen[3], changed = 0, missing = 0, * cut, ref, fCompl, carryLit = 0, kind = 0, truth, out, msk;
    word state = ABC_CONST(0xBF43AD92587106CE), a, b;
    assert(Vec_IntSize(vObserved) == Gia_ManCoNum(g));
    *pvRules = NULL;
    Vec_IntForEachEntry(vObserved, id, i) missing += id < 0;
    if ( !missing ) goto finish;
    q = Gia_ManStart(1000); Gia_ManHashAlloc(q);
    Gia_ManForEachCi(g, o, i) Vec_IntWriteEntry(vMap, Gia_ObjId(g, o), Gia_ManAppendCi(q));
    Gia_ManForEachAnd(g, o, i)
    {
        if ( Gia_ObjIsXor(o) || Gia_ObjIsMux(g, o) ) goto fail;
        if ( (i & 255) == 0 && ((Deadline && Abc_Clock() >= Deadline) || Acec2_Stopped(m)) ) goto fail;
        Vec_IntWriteEntry(vMap, i, Gia_ManHashAnd(q,
            Vec_IntEntry(vMap, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
            Vec_IntEntry(vMap, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o)));
    }
    Gia_ManForEachCo(g, o, i)
        if ( Vec_IntEntry(vObserved, i) >= 0 )
            Acec2_CompleteAssign(vRanks, vPhase, vQueue, Gia_ObjFaninLit0p(g, o), i);
    for ( i = 0; i < Vec_IntSize(m->vCarries)/6; i++ )
    {
        if ( Vec_IntEntry(m->vCarries, 6*i) != 3 ) continue;
        id = Vec_IntEntry(m->vCarries, 6*i+4);
        Vec_IntWriteEntry(vNext, i, Vec_IntEntry(vHead, id)); Vec_IntWriteEntry(vHead, id, i);
    }
    for ( i = 0; i < Vec_IntSize(m->vXors); i += 5 )
    {
        id = Vec_IntEntry(m->vXors, i+4) >> 1; j = Vec_IntEntry(vXors, id);
        if ( j < 0 || Vec_IntEntry(m->vXors, i) < Vec_IntEntry(m->vXors, j) ) Vec_IntWriteEntry(vXors, id, i);
    }
    for ( i = 0; i < Vec_IntSize(vQueue); i++ )
    {
        if ( (i & 255) == 0 && ((Deadline && Abc_Clock() >= Deadline) || Acec2_Stopped(m)) ) goto fail;
        id = Vec_IntEntry(vQueue, i); rank = Vec_IntEntry(vRanks, id); phase = Vec_IntEntry(vPhase, id);
        o = Gia_ManObj(g, id); if ( !Gia_ObjIsAnd(o) ) continue;
        owner = Vec_IntEntry(m->vOwner, id);
        if ( owner >= 0 )
        {
            cell = Acec2_Cell(m, owner/2);
            if ( Vec_IntEntry(vDone, owner/2) || rank < (owner & 1) ) continue;
            Vec_IntWriteEntry(vDone, owner/2, 1);
            rank -= owner & 1; flip = phase ^ (cell->Out[owner & 1] & 1);
            n = cell->nIns; kind = flip;
            for ( j = 0; j < n; j++ ) chosen[j] = cell->In[j] ^ flip;
            for ( j = 0; j < cell->nIns; j++ ) Acec2_CompleteAssign(vRanks, vPhase, vQueue, cell->In[j] ^ flip, rank);
            Acec2_CompleteAssign(vRanks, vPhase, vQueue, cell->Out[0] ^ flip, rank);
            Acec2_CompleteAssign(vRanks, vPhase, vQueue, cell->Out[1] ^ flip, rank+1);
            sum = Vec_IntEntry(vMap, cell->Out[0] >> 1) ^ (cell->Out[0] & 1) ^ flip;
            carryLit = Vec_IntEntry(vMap, cell->Out[1] >> 1) ^ (cell->Out[1] & 1) ^ flip;
            score = Abc_MaxInt(cell->Out[0] >> 1, cell->Out[1] >> 1);
        }
        else
        {
            j = Vec_IntEntry(vXors, id);
            if ( j >= 0 )
            {
                for ( k = 0; k < Vec_IntEntry(m->vXors, j); k++ )
                    Acec2_CompleteAssign(vRanks, vPhase, vQueue, 2*Vec_IntEntry(m->vXors, j+1+k), rank);
                continue;
            }
            if ( !rank ) continue;
            best = -1; bestScore = -1;
            for ( c = Vec_IntEntry(vHead, id); c >= 0; c = Vec_IntEntry(vNext, c) )
            {
                cut = Vec_IntEntryP(m->vCarries, 6*c);
                for ( mask = 0; mask < 8; mask++ )
                {
                    for ( k = 0; k < 8; k++ )
                    {
                        value = ((k ^ mask) & 1)+(((k ^ mask) >> 1) & 1)+(((k ^ mask) >> 2) & 1);
                        if ( (value >= 2) != (((cut[5] >> k) & 1) ^ phase) ) break;
                    }
                    if ( k == 8 ) break;
                }
                if ( mask == 8 ) continue;
                ok = 1; score = 0;
                for ( j = 0; j < 3; j++ )
                {
                    ins[j] = Abc_Var2Lit(cut[j+1], (mask >> j) & 1);
                    k = Vec_IntEntry(vRanks, cut[j+1]);
                    if ( k >= 0 && k != rank-1 ) ok = 0;
                    score += k == rank-1;
                }
                if ( ok && score > bestScore ) { bestScore = score; best = c; memcpy(chosen, ins, sizeof(chosen)); }
            }
            n = 3;
            if ( best < 0 )
            {
                if ( Gia_ObjIsCi(Gia_ObjFanin0(o)) && Gia_ObjIsCi(Gia_ObjFanin1(o)) ) continue;
                n = 2;
                chosen[0] = Gia_ObjFaninLit0(o, id) ^ phase; chosen[1] = Gia_ObjFaninLit1(o, id) ^ phase;
                for ( j = 0; j < 2; j++ )
                    if ( Vec_IntEntry(vRanks, chosen[j] >> 1) >= 0 && Vec_IntEntry(vRanks, chosen[j] >> 1) != rank-1 ) break;
                if ( j != 2 ) continue;
            }
            rank--; kind = phase; sum = n == 2 ? phase : 0;
            carryLit = Vec_IntEntry(vMap, id) ^ phase;
            for ( j = 0; j < n; j++ )
            {
                Acec2_CompleteAssign(vRanks, vPhase, vQueue, chosen[j], rank);
                sum = Gia_ManHashXor(q, sum, Vec_IntEntry(vMap, chosen[j] >> 1) ^ (chosen[j] & 1));
            }
            score = id;
        }
        if ( rank < Gia_ManCoNum(g) && Vec_IntEntry(vObserved, rank) < 0 && score > Vec_IntEntry(vScore, rank) )
        {
            Acec2_CompleteSim(q, vSim, &state);
            o = Gia_ManCo(g, rank); ref = Vec_IntEntry(vMap, Gia_ObjFaninId0p(g, o)) ^ Gia_ObjFaninC0(o); fCompl = 0;
            for ( k = 0; k < 4; k++ )
            {
                a = Vec_WrdEntry(vSim, 4*(sum >> 1)+k); if ( sum & 1 ) a = ~a;
                b = Vec_WrdEntry(vSim, 4*(ref >> 1)+k); if ( ref & 1 ) b = ~b;
                if ( !k ) fCompl = a != b;
                if ( (fCompl ? ~a : a) != b ) break;
            }
            if ( k == 4 )
            {
                Vec_IntWriteEntry(vBits, rank, sum ^ fCompl); Vec_IntWriteEntry(vScore, rank, score);
                vRule = Vec_WecEntry(vRuleBits, rank); Vec_IntClear(vRule); mask = 0;
                for ( j = 0; j < n; j++ )
                {
                    ins[j] = Vec_IntEntry(vMap, chosen[j] >> 1) ^ (chosen[j] & 1);
                    mask |= (ins[j] & 1) << j;
                }
                for ( out = 0; out < 2; out++ )
                {
                    truth = 0;
                    for ( msk = 0; msk < 8; msk++ )
                    {
                        value = 0;
                        for ( j = 0; j < n; j++ ) value += ((msk ^ mask) >> j) & 1;
                        value = out ? (n == 3 ? value >= 2 : kind ? value >= 1 : value == 2) : (value & 1) ^ (n == 2 && kind);
                        truth |= (value ^ ((out ? carryLit : sum) & 1)) << msk;
                    }
                    Vec_IntPush(vRule, n);
                    for ( j = 0; j < 3; j++ ) Vec_IntPush(vRule, j < n ? ins[j] >> 1 : 0);
                    Vec_IntPushTwo(vRule, (out ? carryLit : sum) >> 1, truth);
                }
            }
        }
    }
    Gia_ManForEachCo(g, o, i)
    {
        sum = Vec_IntEntry(vBits, i);
        changed += sum >= 0;
        if ( sum < 0 ) sum = Vec_IntEntry(vMap, Gia_ObjFaninId0p(g, o)) ^ Gia_ObjFaninC0(o);
        Gia_ManAppendCo(q, sum);
    }
    if ( !changed ) goto fail;
    if ( m->Pars.fVerbose ) Abc_Print(1, "Sum completion: recovered positions = %d / %d.\n", changed, missing);
    Gia_ManHashStop(q); clean = Gia_ManCleanup(q); *pvRules = Vec_IntAlloc(100);
    Vec_WecForEachLevel(vRuleBits, vRule, i)
        for ( c = 0; c < Vec_IntSize(vRule); c += 6 )
        {
            n = Vec_IntEntry(vRule, c); out = Gia_ManObj(q, Vec_IntEntry(vRule, c+4))->Value;
            if ( out < 0 || out < 2 ) continue;
            mask = 0;
            for ( j = 0; j < n; j++ )
            {
                ins[j] = Gia_ManObj(q, Vec_IntEntry(vRule, c+1+j))->Value;
                if ( ins[j] < 0 ) break;
                mask |= (ins[j] & 1) << j;
            }
            if ( j != n ) continue;
            truth = 0;
            for ( msk = 0; msk < 8; msk++ ) truth |= (((Vec_IntEntry(vRule, c+5) >> (msk ^ mask)) & 1) ^ (out & 1)) << msk;
            Vec_IntPush(*pvRules, n);
            for ( j = 0; j < 3; j++ ) Vec_IntPush(*pvRules, j < n ? ins[j] >> 1 : 0);
            Vec_IntPushTwo(*pvRules, out >> 1, truth);
        }
    Gia_ManStop(q); q = clean;
    goto finish;
fail:
    Gia_ManStop(q); q = NULL;
finish:
    Vec_IntFree(vRanks); Vec_IntFree(vPhase); Vec_IntFree(vQueue); Vec_IntFree(vDone); Vec_IntFree(vHead); Vec_IntFree(vNext);
    Vec_IntFree(vMap); Vec_IntFree(vBits); Vec_IntFree(vScore); Vec_WrdFree(vSim); Vec_IntFree(vXors); Vec_WecFree(vRuleBits);
    return q;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
