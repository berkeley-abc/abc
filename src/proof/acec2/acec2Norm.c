/**CFile****************************************************************

  FileName    [acec2Norm.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Alternates exact arithmetic matching and Boolean alignment.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 11, 2026.]

  Revision    [$Id$]

  Description [The low-column prefix of a region is replaceable when its
  boundary contains at most one bit of each weight below the prefix width.
  Checked identities give equality of the boundary word modulo 2^width,
  hence equality of every boundary bit in that prefix. Missing columns
  are zero. Higher roots and internal taps retain their original functions.
  Component proofs and Boolean operand proofs introduce exact aliases in
  private maps. Iterative reconstruction exposes downstream correspondence;
  the original structures remain available to the bounded template search.
  Only a completed context CEC proof certifies the remaining Boolean logic.]

***********************************************************************/

#include "acec2Int.h"
#include "misc/vec/vecHsh.h"
#include "proof/cec/cec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

typedef enum {
    ACEC2_ALIGN_OUTPUTS,
    ACEC2_ALIGN_OPERAND_CUTS,
    ACEC2_ALIGN_OPERAND_CONES,
    ACEC2_ALIGN_ALL_CUTS,
    ACEC2_ALIGN_ALL_CONES
} Acec2_AlignMode_t;

typedef struct Acec2_Align_t_ Acec2_Align_t;
struct Acec2_Align_t_ { Vec_Wrd_t * vPatterns; int nPatterns, nSweepGroup, nSweepLeft, fSweepPending, nChanged, nShared; };

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////



/**Function*************************************************************

  Synopsis    [Duplicates a node whose fanins have already been mapped.]

  Description [Native XORs and MUXes are converted to plain AIGs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_MapNode( Gia_Man_t * pGia, Gia_Man_t * pNew, Vec_Int_t * vMap, Gia_Obj_t * o, int Id )
{
    Gia_Obj_t * pCtrl, * pThen, * pElse;
    int a = Vec_IntEntry(vMap, Gia_ObjFaninId0(o, Id)) ^ Gia_ObjFaninC0(o);
    int b = Vec_IntEntry(vMap, Gia_ObjFaninId1(o, Id)) ^ Gia_ObjFaninC1(o);
    if ( Gia_ObjIsMux(pGia, o) )
    {
        int c = Vec_IntEntry(vMap, Gia_ObjFaninId2(pGia, Id)) ^ Gia_ObjFaninC2(pGia, o);
        return Gia_ManHashMux(pNew, c, b, a);
    }
    if ( Gia_ObjIsXor(o) ) return Gia_ManHashXor(pNew, a, b);
    // Canonicalize Boolean interfaces as well as arithmetic roots. In
    // particular MUX(c,~a,~b) is the complement of MUX(c,a,b); ordinary
    // AND hashing alone cannot expose this operand correspondence.
    if ( !Gia_ObjIsXor(Gia_ObjFanin0(o)) && !Gia_ObjIsXor(Gia_ObjFanin1(o)) &&
         !Gia_ObjIsMux(pGia, Gia_ObjFanin0(o)) && !Gia_ObjIsMux(pGia, Gia_ObjFanin1(o)) &&
         !Gia_ObjIsBuf(Gia_ObjFanin0(o)) && !Gia_ObjIsBuf(Gia_ObjFanin1(o)) && Gia_ObjIsMuxType(o) )
    {
        if ( Gia_ObjRecognizeExor(o, &pThen, &pElse) )
        {
            a = Vec_IntEntry(vMap, Gia_ObjId(pGia, Gia_Regular(pThen))) ^ Gia_IsComplement(pThen);
            b = Vec_IntEntry(vMap, Gia_ObjId(pGia, Gia_Regular(pElse))) ^ Gia_IsComplement(pElse);
            return Gia_ManHashXor(pNew, a, b);
        }
        pCtrl = Gia_ObjRecognizeMux(o, &pThen, &pElse);
        a = Vec_IntEntry(vMap, Gia_ObjId(pGia, Gia_Regular(pThen))) ^ Gia_IsComplement(pThen);
        b = Vec_IntEntry(vMap, Gia_ObjId(pGia, Gia_Regular(pElse))) ^ Gia_IsComplement(pElse);
        return Gia_ManHashMux(pNew, Vec_IntEntry(vMap, Gia_ObjId(pGia, Gia_Regular(pCtrl))) ^ Gia_IsComplement(pCtrl), a, b);
    }
    return Gia_ManHashAnd(pNew, a, b);
}

/**Function*************************************************************

  Synopsis    [Adds a small unsigned constant at a column, modulo the width.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_AddConstant( Vec_Int_t * vConst, int Rank, unsigned Carry )
{
    for ( ; Rank < Vec_IntSize(vConst) && Carry; Rank++ )
    {
        Carry += (unsigned)Vec_IntEntry(vConst, Rank);
        Vec_IntWriteEntry(vConst, Rank, Carry & 1);
        Carry >>= 1;
    }
}

/**Function*************************************************************

  Synopsis    [Cancels complementary terms and carries repeated terms.]

  Description [x + ~x = 1 and x + x = 2*x. Constants are kept outside the
  compressor tree, so they do not change its grouping of variable terms.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ReduceColumn( Vec_Wec_t * vCols, Vec_Int_t * vConst, int Rank )
{
    Vec_Int_t * v = Vec_WecEntry(vCols, Rank);
    int i, j, lit, pos, neg, pairs, count, kept = 0;
    if ( Vec_IntSize(v) > 1 ) Vec_IntSort(v, 0);
    for ( i = 0; i < Vec_IntSize(v); i = j )
    {
        lit = Vec_IntEntry(v, i); pos = neg = 0;
        for ( j = i; j < Vec_IntSize(v) && Abc_Lit2Var(Vec_IntEntry(v, j)) == Abc_Lit2Var(lit); j++ )
            if ( Abc_LitIsCompl(Vec_IntEntry(v, j)) ) neg++; else pos++;
        if ( lit < 2 ) { Acec2_AddConstant(vConst, Rank, (unsigned)neg); continue; }
        pairs = Abc_MinInt(pos, neg);
        Acec2_AddConstant(vConst, Rank, (unsigned)pairs);
        pos -= pairs; neg -= pairs;
        count = pos + neg;
        lit = Abc_Var2Lit(Abc_Lit2Var(lit), neg > 0);
        if ( Rank+1 < Vec_WecSize(vCols) )
            for ( pairs = 0; pairs < count/2; pairs++ ) Vec_WecPush(vCols, Rank+1, lit);
        if ( count & 1 ) Vec_IntWriteEntry(v, kept++, lit);
    }
    Vec_IntShrink(v, kept);
}

/**Function*************************************************************

  Synopsis    [Compresses one canonical column and propagates its carries.]

  Description [Returns the result literal, or -1 if interrupted or limited.
  Constants remain separate for the final addition. The same construction
  handles the discarded low column of a composed shifted product.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CompressColumn( Gia_Man_t * g, Vec_Wec_t * vCols, Vec_Int_t * vConst, Vec_Int_t * vNext,
                         int Rank, Acec2_Par_t * pPars, abctime Deadline, int nMaxObjs )
{
    Vec_Int_t * vCol = Vec_WecEntry(vCols, Rank);
    int j, a, b, c, sum, carry;
    for ( ;; )
    {
        if ( Gia_ManObjNum(g) >= nMaxObjs || Acec2_Stop(pPars, Deadline) ) return -1;
        Acec2_ReduceColumn(vCols, vConst, Rank);
        if ( Vec_IntSize(vCol) < 2 ) return Vec_IntSize(vCol) ? Vec_IntEntry(vCol, 0) : 0;
        Vec_IntClear(vNext);
        for ( j = 0; j < Vec_IntSize(vCol); )
        {
            a = Vec_IntEntry(vCol, j++);
            if ( j == Vec_IntSize(vCol) ) { Vec_IntPush(vNext, a); break; }
            b = Vec_IntEntry(vCol, j++);
            if ( j < Vec_IntSize(vCol) )
            {
                c = Vec_IntEntry(vCol, j++);
                sum = Gia_ManHashXor(g, Gia_ManHashXor(g, a, b), c); carry = Gia_ManHashMaj(g, a, b, c);
            }
            else { sum = Gia_ManHashXor(g, a, b); carry = Gia_ManHashAnd(g, a, b); }
            Vec_IntPush(vNext, sum);
            if ( Rank+1 < Vec_WecSize(vCols) ) Vec_WecPush(vCols, Rank+1, carry);
            if ( Gia_ManObjNum(g) >= nMaxObjs ) return -1;
        }
        Vec_IntClear(vCol); Vec_IntAppend(vCol, vNext);
    }
}

/**Function*************************************************************

  Synopsis    [Compresses columns and adds their constant correction word.]

  Description [The two normalization entry points share gate insertion
  order, cancellation checks, and the rule that no unfinished column commits.]

  SideEffects [Writes a private result vector only after each column finishes.]

  SeeAlso     []

***********************************************************************/
static int Acec2_ColumnsWord( Gia_Man_t * g, Vec_Wec_t * cols, Vec_Int_t * constants,
                              Vec_Int_t * next, Vec_Int_t * bits, Acec2_Par_t * pars,
                              abctime deadline, int nMaxObjs )
{
    int rank, sum, a, carry = 0;
    for ( rank = 0; rank < Vec_WecSize(cols); rank++ )
    {
        sum = Acec2_CompressColumn(g, cols, constants, next, rank, pars, deadline, nMaxObjs);
        if ( sum < 0 ) return 0;
        Vec_IntWriteEntry(bits, rank, sum);
    }
    for ( rank = 0; rank < Vec_WecSize(cols); rank++ )
    {
        a = Vec_IntEntry(bits, rank); sum = Gia_ManHashXor(g, a, carry);
        if ( Vec_IntEntry(constants, rank) ) { sum ^= 1; carry = Gia_ManHashOr(g, a, carry); }
        else carry = Gia_ManHashAnd(g, a, carry);
        Vec_IntWriteEntry(bits, rank, sum);
        if ( Gia_ManObjNum(g) >= nMaxObjs || Acec2_Stop(pars, deadline) ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Proposes one arithmetic bit per column for exact extraction.]

  Description [Later roots usually belong to the final adder. A top-column
  XOR tree can supply a sum without a carry. Coverage of the top roots
  selects its boundary before unrelated XOR fanout. These are only heuristics:
  the polynomial extractor proves the complete chosen word from the gates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_RegionWord( Acec2_Man_t * p, int Tree, int Width, abctime Deadline )
{
    Vec_Int_t * vRoots = Vec_WecEntry(p->vRoots, Tree), * vBits = Vec_IntStartFull(Width);
    Vec_Int_t * vWord = Vec_IntAlloc(2*Width), * vTop = Vec_IntAlloc(4);
    int i, j, lit, rank, count, unknown, id, fanin, bestCount = 1, bestUnknown = 0;
    Acec2_Word_t * word = Acec2_Word(p, Tree);
    if ( word && word->Width >= Width )
    {
        for ( i = 0; i < Width; i++ ) Vec_IntPushTwo(vWord, Vec_IntEntry(word->vBits, i), i);
        Vec_IntFree(vBits); Vec_IntFree(vTop);
        return vWord;
    }
    for ( i = 0; i < Vec_IntSize(vRoots); i += 2 )
    {
        lit = Vec_IntEntry(vRoots, i); rank = Vec_IntEntry(vRoots, i+1);
        if ( rank >= Width ) continue;
        if ( lit > Vec_IntEntry(vBits, rank) ) Vec_IntWriteEntry(vBits, rank, lit);
        if ( rank == Width-1 ) Vec_IntPush(vTop, Abc_Lit2Var(lit));
    }
    if ( Vec_IntSize(vTop) >= 2 )
    {
        Vec_Int_t * vKnown = Vec_IntStart(Gia_ManObjNum(p->pGia));
        Vec_Int_t * vUnknown = Vec_IntStart(Gia_ManObjNum(p->pGia));
        Vec_Bit_t * vIsRoot = Vec_BitStart(Gia_ManObjNum(p->pGia));
        Vec_IntForEachEntry(vTop, id, i) { Vec_IntWriteEntry(vKnown, id, 1); Acec2_BitWrite(vIsRoot, id, 1); }
        for ( i = 0; i < Vec_IntSize(p->vXors); i += 5 )
        {
            if ( (i % 5120) == 0 && Acec2_Stop(&p->Pars, Deadline) ) break;
            id = Abc_Lit2Var(Vec_IntEntry(p->vXors, i+4));
            if ( Vec_BitEntry(vIsRoot, id) ) continue;
            count = unknown = 0;
            for ( j = 0; j < Vec_IntEntry(p->vXors, i); j++ )
            {
                fanin = Vec_IntEntry(p->vXors, i+1+j);
                count += Vec_IntEntry(vKnown, fanin);
                unknown += Vec_IntEntry(vKnown, fanin) ? Vec_IntEntry(vUnknown, fanin) : 1;
            }
            count = Abc_MinInt(count, Vec_IntSize(vTop)); unknown = Abc_MinInt(unknown, 1000000);
            if ( !count || count < Vec_IntEntry(vKnown, id) ||
                 (count == Vec_IntEntry(vKnown, id) && unknown >= Vec_IntEntry(vUnknown, id)) ) continue;
            Vec_IntWriteEntry(vKnown, id, count); Vec_IntWriteEntry(vUnknown, id, unknown);
            if ( count < 2 || count < bestCount || (count == bestCount && unknown >= bestUnknown) ) continue;
            bestCount = count; bestUnknown = unknown; Vec_IntWriteEntry(vBits, Width-1, Abc_Var2Lit(id, 0));
        }
        Vec_IntFree(vKnown); Vec_IntFree(vUnknown); Vec_BitFree(vIsRoot);
    }
    Vec_IntForEachEntry(vBits, lit, rank) if ( lit >= 0 ) Vec_IntPushTwo(vWord, lit, rank);
    Vec_IntFree(vTop); Vec_IntFree(vBits);
    return vWord;
}

/**Function*************************************************************

  Synopsis    [Checks whether an expression uses the current shared cut.]

  Description [A private operand adder may need polynomial expansion before
  its expression matches a distributed product on the other side. Direct
  normalization must not bypass that expansion merely because both words
  have independent expression certificates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ExprOnFrontier( Acec2_Expr_t * e, Vec_Int_t * vMap, Vec_Int_t * vFrontier )
{
    Acec2_Product_t * p;
    int index, side, i, lit;
    if ( !vFrontier ) return 1;
    Vec_PtrForEachEntry(Acec2_Product_t *, e->vProducts, p, index)
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(p->vOperands[side], lit, i)
                if ( lit >= 2 && !Vec_IntEntry(vFrontier, Vec_IntEntry(vMap, lit >> 1) >> 1) ) return 0;
    for ( i = 0; i < Vec_IntSize(e->vAddends); i += 2 )
    {
        lit = Vec_IntEntry(e->vAddends, i);
        if ( lit >= 2 && !Vec_IntEntry(vFrontier, Vec_IntEntry(vMap, lit >> 1) >> 1) ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Skips arithmetic proofs whose entire boundary is already shared.]

  Description [The analysis and its alternatives remain available. Only
  reconstruction is skipped: it cannot add a new equality for these roots.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RegionShared( Acec2_Man_t * m, int Tree, Vec_Int_t * vMap, Vec_Int_t * vColors )
{
    Acec2_Word_t * w = Acec2_Word(m, Tree);
    Vec_Int_t * roots;
    int i, lit, pass;
    for ( pass = 0; pass < 1+(w != NULL); pass++ )
    {
        roots = pass ? w->vBits : Vec_WecEntry(m->vRoots, Tree);
        for ( i = 0; i < Vec_IntSize(roots); i += pass ? 1 : 2 )
        {
            lit = Vec_IntEntry(roots, i);
            if ( lit >= 2 && Vec_IntEntry(vColors, Vec_IntEntry(vMap, lit >> 1) >> 1) != 3 ) return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Constructs canonical prefix bits from original mapped leaves.]

  Description [The two source designs share one destination AIG. Orientation
  is chosen from destination literals, independently of source node ordering.
  The caller commits no replacement unless the whole prefix was constructed.
  Returning NULL retains the original region on a growth limit.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_NormalizeRegion( Gia_Man_t * pNew, Acec2_Man_t * p, int Tree,
                                        Vec_Int_t * vMap, Acec2_Par_t * pPars, abctime Deadline,
                                        int nMaxObjs, int * pFlip, Acec2_PolyCtx_t * pPoly, abctime PolyDeadline,
                                        int * pPolyStatus, int * pExprUsed, Vec_Int_t ** pvChosen, Vec_Int_t * vFrontier )
{
    int width = Vec_IntEntry(p->vPrefix, Tree), i, j, rank, lit, a, b, balance = 0, tie = 0, found = 0;
    Vec_Wec_t * vCols = Vec_WecStart(width);
    Vec_Int_t * vBits = Vec_IntStart(width), * vNext = Vec_IntAlloc(32), * vConst = Vec_IntStart(width);
    Vec_Int_t * vLeaves = Vec_WecEntry(p->vLeaves, Tree), * vCol, * vTree = Vec_WecEntry(p->vTrees, Tree);
    Acec2_Cell_t * pCell;
    Acec2_Word_t * word = Acec2_Word(p, Tree);
    Acec2_Expr_t * expr = Acec2_Expression(p, Tree);
    int exprUsed = 0, exprWidth = word ? word->Width : width;
    int recordId = Vec_IntEntry(p->vTreeRecord, Tree);
    Acec2_Record_t * record = recordId < 0 ? NULL : (Acec2_Record_t *)Vec_PtrEntry(p->vRecords, recordId);
    *pPolyStatus = 0; *pExprUsed = 0; *pvChosen = NULL;
    // Reuse the source certificate when its complete binary boundary is
    // available on the current proved frontier. No arithmetic re-detection
    // or new cross-design proof is needed for the same polynomial.
    if ( record && !record->vOutputMasks && !(pPars->nCecOptions & ACEC2_CEC_DEFER) && record->Prefix >= 2 &&
         record->Prefix == Abc_MinInt(Vec_IntEntry(p->vWidths, Tree), pPars->nMaxWidth) )
    {
        width = record->Prefix;
        Vec_WecFree(vCols); vCols = Vec_WecStart(width);
        Vec_IntFill(vConst, width, 0); Vec_IntFill(vBits, width, 0);
        if ( Acec2_RecordColumns(record, pNew, vMap, vFrontier, vCols, vConst, pPars, Deadline, nMaxObjs) )
        {
            *pvChosen = Vec_IntDup(record->vOutputs); exprUsed = 1; *pFlip = 0;
        }
        else
        {
            if ( Acec2_Stop(pPars, Deadline) || Gia_ManObjNum(pNew) >= nMaxObjs ) goto fail;
            width = Vec_IntEntry(p->vPrefix, Tree);
            Vec_WecFree(vCols); vCols = Vec_WecStart(width);
            Vec_IntFill(vConst, width, 0); Vec_IntFill(vBits, width, 0);
        }
    }
    // A complete binary boundary can consume the independent expression
    // directly. Partial boundaries still try the wider polynomial first.
    if ( !exprUsed && expr && exprWidth >= 2 && expr->Width >= exprWidth && Acec2_ExprOnFrontier(expr, vMap, vFrontier) &&
         exprWidth == Abc_MinInt(Vec_IntEntry(p->vWidths, Tree), pPars->nMaxWidth) )
    {
        width = exprWidth;
        Vec_WecFree(vCols); vCols = Vec_WecStart(width);
        Vec_IntFill(vConst, width, 0); Vec_IntFill(vBits, width, 0);
        if ( !Acec2_ExprColumns(p, expr, pNew, vMap, vCols, vConst, nMaxObjs, Deadline) ) goto fail;
        exprUsed = 1; *pFlip = 0;
        if ( word ) *pvChosen = Acec2_RegionWord(p, Tree, width, Deadline);
    }
    if ( !exprUsed && pPoly && Vec_IntEntry(p->vWidths, Tree) >= 2 && Vec_IntSize(vTree) >= 8 && !Acec2_Stop(pPars, PolyDeadline) )
    {
        width = Abc_MinInt(Vec_IntEntry(p->vWidths, Tree), pPars->nMaxWidth);
        *pvChosen = Acec2_RegionWord(p, Tree, width, PolyDeadline);
        Vec_WecFree(vCols); vCols = Vec_WecStart(width);
        Vec_IntFill(vConst, width, 0); Vec_IntFill(vBits, width, 0);
        *pPolyStatus = Acec2_PolyRegion(pPoly, Tree, *pvChosen, pNew, vCols, vConst, PolyDeadline, nMaxObjs, pFlip) ? 1 : -1;
        if ( *pPolyStatus < 0 && !word && Vec_IntEntry(p->vPrefix, Tree) >= 2 && Vec_IntEntry(p->vPrefix, Tree) < width )
        {
            Vec_IntFreeP(pvChosen); width = Vec_IntEntry(p->vPrefix, Tree);
            *pvChosen = Acec2_RegionWord(p, Tree, width, PolyDeadline);
            Vec_WecFree(vCols); vCols = Vec_WecStart(width);
            Vec_IntFill(vConst, width, 0); Vec_IntFill(vBits, width, 0);
            *pPolyStatus = Acec2_PolyRegion(pPoly, Tree, *pvChosen, pNew, vCols, vConst, PolyDeadline, nMaxObjs, pFlip) ? 1 : -1;
        }
        if ( *pPolyStatus < 0 )
        {
            Vec_IntFreeP(pvChosen); width = Vec_IntEntry(p->vPrefix, Tree);
            Vec_WecFree(vCols); vCols = Vec_WecStart(width);
            Vec_IntFill(vConst, width, 0); Vec_IntFill(vBits, width, 0);
        }
    }
    if ( word && *pPolyStatus != 1 && !exprUsed )
    {
        Vec_IntFreeP(pvChosen); width = word->Width;
        *pvChosen = Acec2_RegionWord(p, Tree, width, Deadline);
        Vec_WecFree(vCols); vCols = Vec_WecStart(width);
        Vec_IntFill(vConst, width, 0); Vec_IntFill(vBits, width, 0);
    }
    if ( !width ) goto fail;
    if ( *pPolyStatus != 1 && !exprUsed && expr && expr->Width >= width )
    {
        if ( !Acec2_ExprColumns(p, expr, pNew, vMap, vCols, vConst, nMaxObjs, Deadline) ) goto fail;
        exprUsed = 1; *pFlip = 0;
    }
    if ( *pPolyStatus != 1 && !exprUsed )
    {
        for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
        {
            rank = Vec_IntEntry(vLeaves, i+1);
            if ( rank >= width ) continue;
            lit = Vec_IntEntry(vLeaves, i);
            lit = Vec_IntEntry(vMap, Abc_Lit2Var(lit)) ^ Abc_LitIsCompl(lit);
            Vec_WecPush(vCols, rank, lit);
            balance += Abc_LitIsCompl(lit) ? -1 : 1;
        }
        // Break a phase-count tie by the first unequal polarity multiplicity.
        for ( rank = 0; rank < width && !found; rank++ )
        {
            vCol = Vec_WecEntry(vCols, rank);
            if ( Vec_IntSize(vCol) > 1 ) Vec_IntSort(vCol, 0);
            for ( i = 0; i < Vec_IntSize(vCol) && !found; i = j )
            {
                lit = Vec_IntEntry(vCol, i); a = b = 0;
                for ( j = i; j < Vec_IntSize(vCol) && Abc_Lit2Var(Vec_IntEntry(vCol, j)) == Abc_Lit2Var(lit); j++ )
                    if ( Abc_LitIsCompl(Vec_IntEntry(vCol, j)) ) b++; else a++;
                if ( a != b ) { tie = b > a; found = 1; }
            }
        }
        // A certified word is the sum of the original weighted roots. Their
        // simultaneous complement is not generally a complemented word.
        *pFlip = !word && (balance < 0 || (balance == 0 && tie));
        if ( *pFlip )
            Vec_WecForEachLevel(vCols, vCol, rank)
                Vec_IntForEachEntry(vCol, lit, i) Vec_IntWriteEntry(vCol, i, lit ^ 1);
        Vec_IntForEachEntry(vTree, i, j)
        {
            pCell = Acec2_Cell(p, i);
            if ( pCell->nIns == 2 && (pCell->Phase ^ *pFlip) && pCell->Rank < width )
                Acec2_AddConstant(vConst, pCell->Rank, 1);
        }
    }
    if ( !Acec2_ColumnsWord(pNew, vCols, vConst, vNext, vBits, pPars, Deadline, nMaxObjs) ) goto fail;
    *pExprUsed = exprUsed;
    Vec_WecFree(vCols); Vec_IntFree(vNext); Vec_IntFree(vConst);
    return vBits;
fail:
    Vec_IntFreeP(pvChosen);
    Vec_WecFree(vCols); Vec_IntFree(vNext); Vec_IntFree(vConst); Vec_IntFree(vBits);
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Normalizes a checked alternative boundary without changing its cut.]

  Description [A retained cell partition or counter composition can have a
  complete binary prefix even when a larger shared region does not. Its
  independently checked polynomial supplies the same canonical compressor
  construction as the main regions. Only cross-design matches are committed
  by the caller. For a masked record these bits are decoded arithmetic
  values; the caller must apply each source mask before replacing a node.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_NormalizeRecord( Gia_Man_t * g, Acec2_Record_t * r, Vec_Int_t * vMap,
                                         Acec2_Par_t * pPars, abctime Deadline, int nMaxObjs, int * pFlip )
{
    int width = Abc_MinInt(r->Prefix, pPars->nMaxWidth), rank, i, j, lit, a, balance = 0;
    Vec_Wec_t * cols = Vec_WecStart(width);
    Vec_Int_t * constants = Vec_IntStart(width), * bits = Vec_IntStart(width), * next = Vec_IntAlloc(32), * v;
    if ( (pPars->nCecOptions & ACEC2_CEC_DEFER) && r->Word < 0 && !r->Compose && !r->Extend && !r->pProductReference && !r->fPolynomial )
    {
        // Preserve the checked literal interface before expanding its gates.
        // Equal cut functions may already be shared even when their source
        // fanins have different decompositions in the two designs.
        for ( i = 0; i < Vec_IntSize(r->vTerms); i += 2 )
        {
            lit = Vec_IntEntry(r->vTerms, i); rank = Vec_IntEntry(r->vTerms, i+1);
            if ( rank < width ) Vec_WecPush(cols, rank, Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1));
        }
        Vec_IntForEachEntry(r->vConstants, rank, i) Acec2_AddConstant(constants, rank, 1);
    }
    else if ( !Acec2_RecordColumns(r, g, vMap, NULL, cols, constants, pPars, Deadline, nMaxObjs) ) goto fail;
    Vec_WecForEachLevel(cols, v, rank)
        Vec_IntForEachEntry(v, lit, i) balance += (lit & 1) ? -1 : 1;
    *pFlip = balance < 0;
    if ( *pFlip )
    {
        for ( rank = 0; rank < width; rank++ ) Vec_IntWriteEntry(constants, rank, !Vec_IntEntry(constants, rank));
        Vec_WecForEachLevel(cols, v, rank)
            Vec_IntForEachEntry(v, lit, i)
            {
                Vec_IntWriteEntry(v, i, lit ^ 1);
                for ( j = rank; j < width; j++ )
                {
                    a = Vec_IntEntry(constants, j); Vec_IntWriteEntry(constants, j, a ^ 1);
                    if ( a ) break;
                }
            }
    }
    if ( !Acec2_ColumnsWord(g, cols, constants, next, bits, pPars, Deadline, nMaxObjs) ) goto fail;
    Vec_WecFree(cols); Vec_IntFree(constants); Vec_IntFree(next); return bits;
fail:
    Vec_WecFree(cols); Vec_IntFree(constants); Vec_IntFree(next); Vec_IntFree(bits); return NULL;
}

/**Function*************************************************************

  Synopsis    [Applies an output's explicit XOR mask in the destination GIA.]

  Description [XOR masking is its own inverse. Use the same operation when
  decoding source roots and re-encoding normalized arithmetic bits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordApplyMask( Gia_Man_t * g, Acec2_Record_t * r, Vec_Int_t * map, int Occurrence, int Lit )
{
    int mask;
    if ( !r->vOutputMasks ) return Lit;
    mask = Vec_IntEntry(r->vOutputMasks, Occurrence);
    return Gia_ManHashXor(g, Lit, Vec_IntEntry(map, mask >> 1) ^ (mask & 1));
}

/**Function*************************************************************

  Synopsis    [Finds shared operand bits at two-input partial-product leaves.]

  Description [This is a conservative structural heuristic, not a proof of
  multiplication. Each selected node is kept as an independent Boolean
  variable; exact polynomial substitution establishes every replacement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_OperandFrontier( Gia_Man_t * pNew, Acec2_Man_t ** pMans, Vec_Int_t ** vMaps, abctime Deadline, int fAddends )
{
    Vec_Int_t * vColors = Vec_IntStart(Gia_ManObjNum(pNew)), * vFrontier = Vec_IntStart(Gia_ManObjNum(pNew)), * vLeaves;
    Vec_Int_t * vDegree = Vec_IntStart(Gia_ManObjNum(pNew));
    Vec_Wrd_t * vPairs = Vec_WrdAlloc(100);
    Gia_Obj_t * o;
    int side, i, tree, lit, id, a, b;
    word pair;
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(vMaps[side], lit, i)
        {
            id = Abc_Lit2Var(lit);
            Vec_IntWriteEntry(vColors, id, Vec_IntEntry(vColors, id) | (1 << side));
        }
    Gia_ManForEachCi(pNew, o, i) Vec_IntWriteEntry(vFrontier, Gia_ObjId(pNew, o), 1);
    for ( side = 0; side < 2; side++ )
    {
        if ( !pMans[side] ) continue;
        Vec_WecForEachLevel(pMans[side]->vLeaves, vLeaves, tree)
            for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
            {
                id = Abc_Lit2Var(Vec_IntEntry(vLeaves, i)); o = Gia_ManObj(pMans[side]->pGia, id);
                if ( !Gia_ObjIsAnd(o) || Gia_ObjIsXor(o) || Gia_ObjIsMux(pMans[side]->pGia, o) ) continue;
                a = Abc_Lit2Var(Vec_IntEntry(vMaps[side], Gia_ObjFaninId0(o, id)));
                b = Abc_Lit2Var(Vec_IntEntry(vMaps[side], Gia_ObjFaninId1(o, id)));
                if ( Vec_IntEntry(vColors, a) != 3 || Vec_IntEntry(vColors, b) != 3 ) continue;
                if ( a > b ) ABC_SWAP(int, a, b);
                Vec_WrdPush(vPairs, ((word)(unsigned)a << 32) | (unsigned)b);
            }
    }
    Vec_WrdUniqify(vPairs);
    Vec_WrdForEachEntry(vPairs, pair, i)
    {
        a = (int)(pair >> 32); b = (int)(pair & 0xFFFFFFFF);
        Vec_IntAddToEntry(vDegree, a, 1); Vec_IntAddToEntry(vDegree, b, 1);
    }
    // Multiplication fans each operand bit into several different products.
    // A neighbour of such a bit may occur only once in a truncated product.
    Vec_WrdForEachEntry(vPairs, pair, i)
    {
        a = (int)(pair >> 32); b = (int)(pair & 0xFFFFFFFF);
        if ( Vec_IntEntry(vDegree, a) < 3 && Vec_IntEntry(vDegree, b) < 3 ) continue;
        Vec_IntWriteEntry(vFrontier, a, 1); Vec_IntWriteEntry(vFrontier, b, 1);
    }
    // Other shared leaves are addends, controls, or results of earlier logic.
    // Keep these as independent cut signals instead of expanding their muxes
    // and comparisons into the multiplier polynomial. Partial products must
    // still expand to their operand bits, whose encodings may differ.
    for ( side = 0; fAddends && side < 2; side++ )
    {
        if ( !pMans[side] ) continue;
        Vec_WecForEachLevel(pMans[side]->vLeaves, vLeaves, tree)
            for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
            {
                id = Abc_Lit2Var(Vec_IntEntry(vLeaves, i)); o = Gia_ManObj(pMans[side]->pGia, id);
                lit = Abc_Lit2Var(Vec_IntEntry(vMaps[side], id));
                if ( !lit || Vec_IntEntry(vColors, lit) != 3 ) continue;
                if ( Gia_ObjIsAnd(o) && !Gia_ObjIsXor(o) && !Gia_ObjIsMux(pMans[side]->pGia, o) )
                {
                    a = Abc_Lit2Var(Vec_IntEntry(vMaps[side], Gia_ObjFaninId0(o, id)));
                    b = Abc_Lit2Var(Vec_IntEntry(vMaps[side], Gia_ObjFaninId1(o, id)));
                    if ( Vec_IntEntry(vColors, a) == 3 && Vec_IntEntry(vColors, b) == 3 &&
                        (Vec_IntEntry(vDegree, a) >= 3 || Vec_IntEntry(vDegree, b) >= 3) ) continue;
                }
                Vec_IntWriteEntry(vFrontier, lit, 1);
            }
    }
    // Recover operand bits used only by truncated top-column XOR trees.
    // Stop tracing at existing arithmetic roots; their interior ANDs are
    // carry logic and must not be mistaken for additional partial products.
    for ( side = 0; side < 2; side++ )
    {
        Acec2_Man_t * m = pMans[side];
        Vec_Int_t * vXor, * vSeen, * vStop, * vStack, * vRoots, * vWord;
        int k, nTop, width, cut;
        if ( !m ) continue;
        vXor = Vec_IntStartFull(Gia_ManObjNum(m->pGia)); vSeen = Vec_IntStart(Gia_ManObjNum(m->pGia));
        vStop = Vec_IntStart(Gia_ManObjNum(m->pGia)); vStack = Vec_IntAlloc(100);
        for ( i = 0; i < Vec_IntSize(m->vXors); i += 5 )
            if ( Vec_IntEntry(m->vXors, i) == 2 ) Vec_IntWriteEntry(vXor, Abc_Lit2Var(Vec_IntEntry(m->vXors, i+4)), i);
        Vec_WecForEachLevel(m->vRoots, vRoots, tree)
        {
            width = Vec_IntEntry(m->vWidths, tree); nTop = 0;
            if ( width > m->Pars.nMaxWidth ) continue;
            if ( Acec2_Stop(&m->Pars, Deadline) ) break;
            for ( i = 0; i < Vec_IntSize(vRoots); i += 2 )
                if ( Vec_IntEntry(vRoots, i+1) == width-1 )
                { Vec_IntWriteEntry(vStop, Abc_Lit2Var(Vec_IntEntry(vRoots, i)), tree+1); nTop++; }
            if ( nTop < 4 || Vec_IntSize(Vec_WecEntry(m->vTrees, tree)) < 8 ) continue;
            vWord = Acec2_RegionWord(m, tree, width, Deadline);
            Vec_IntClear(vStack); Vec_IntPush(vStack, Abc_Lit2Var(Vec_IntEntry(vWord, Vec_IntSize(vWord)-2)));
            Vec_IntFree(vWord);
            while ( Vec_IntSize(vStack) )
            {
                id = Vec_IntPop(vStack);
                if ( Vec_IntEntry(vSeen, id) == tree+1 || Vec_IntEntry(vStop, id) == tree+1 ) continue;
                Vec_IntWriteEntry(vSeen, id, tree+1); cut = Vec_IntEntry(vXor, id);
                if ( cut >= 0 )
                {
                    for ( k = 1; k <= 2; k++ ) Vec_IntPush(vStack, Vec_IntEntry(m->vXors, cut+k));
                    continue;
                }
                o = Gia_ManObj(m->pGia, id);
                if ( !Gia_ObjIsAnd(o) || Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) continue;
                a = Abc_Lit2Var(Vec_IntEntry(vMaps[side], Gia_ObjFaninId0(o, id)));
                b = Abc_Lit2Var(Vec_IntEntry(vMaps[side], Gia_ObjFaninId1(o, id)));
                if ( Vec_IntEntry(vColors, a) == 3 && Vec_IntEntry(vColors, b) == 3 &&
                    (Vec_IntEntry(vDegree, a) >= 3 || Vec_IntEntry(vDegree, b) >= 3) )
                {
                    Vec_IntWriteEntry(vFrontier, a, 1); Vec_IntWriteEntry(vFrontier, b, 1);
                }
                else if ( fAddends )
                {
                    lit = Abc_Lit2Var(Vec_IntEntry(vMaps[side], id));
                    if ( Vec_IntEntry(vColors, lit) == 3 ) Vec_IntWriteEntry(vFrontier, lit, 1);
                }
            }
        }
        Vec_IntFree(vXor); Vec_IntFree(vSeen); Vec_IntFree(vStop); Vec_IntFree(vStack);
    }
    Vec_WrdFree(vPairs); Vec_IntFree(vDegree); Vec_IntFree(vColors);
    return vFrontier;
}

/**Function*************************************************************

  Synopsis    [Finds input logic independent of unresolved large arithmetic regions.]

  Description [Shared functions terminate the dependency. These marks only
  schedule Boolean proofs and do not assert any arithmetic identity.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Bit_t * Acec2_OperandBlocked( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vColors )
{
    Vec_Bit_t * vBlocked = Vec_BitStart(Gia_ManObjNum(m->pGia));
    Gia_Obj_t * o;
    Acec2_Cell_t * c;
    int i, k, lit, blocked;
    Vec_PtrForEachEntry(Acec2_Cell_t *, m->vCells, c, i)
        if ( Vec_IntSize(Vec_WecEntry(m->vTrees, c->Tree)) >= 64 )
            for ( k = 0; k < 2; k++ ) Acec2_BitWrite(vBlocked, c->Out[k] >> 1, 1);
    Gia_ManForEachAnd(m->pGia, o, i)
    {
        lit = Vec_IntEntry(vMap, i);
        if ( Vec_IntEntry(vColors, lit >> 1) == 3 ) { Acec2_BitWrite(vBlocked, i, 0); continue; }
        blocked = Vec_BitEntry(vBlocked, i) || Vec_BitEntry(vBlocked, Gia_ObjFaninId0(o, i)) || Vec_BitEntry(vBlocked, Gia_ObjFaninId1(o, i));
        if ( Gia_ObjIsMux(m->pGia, o) ) blocked |= Vec_BitEntry(vBlocked, Gia_ObjFaninId2(m->pGia, i));
        Acec2_BitWrite(vBlocked, i, blocked != 0);
    }
    return vBlocked;
}

/**Function*************************************************************

  Synopsis    [Cuts proved shared functions from a local operand proof.]

  Description [Every cut becomes an independent input. A correspondence
  proved in this stronger model is valid after substituting the original
  functions. Unhashed copying keeps an unambiguous original ID for every
  retained node, including the new cut inputs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_OperandAbstract( Gia_Man_t * pCopy, Vec_Int_t * vColors,
                                        Vec_Int_t ** vOriginals, Vec_Int_t ** vMaps, Vec_Int_t ** pvOrig )
{
    Gia_Man_t * p = Gia_ManStart(1000), * pClean;
    Gia_Obj_t * o;
    Vec_Bit_t * vUsed = Vec_BitStart(Gia_ManObjNum(pCopy));
    Vec_Int_t * vMap = Vec_IntStart(Gia_ManObjNum(pCopy)), * vIds = Vec_IntAlloc(1000);
    Vec_Int_t * vCuts = Vec_IntStartFull(Gia_ManObjNum(pCopy)), * vCis = Vec_IntStartFull(Gia_ManObjNum(pCopy));
    int i, side, lit, old, cut, nObjs;
    Vec_IntForEachEntry(vColors, lit, i)
        if ( lit == 3 ) Vec_IntWriteEntry(vCuts, i, 2*i);
    // An original operand cone may still contain an earlier multiplier
    // whose current result is already shared. All proved forms of that
    // result must use the same free cut input, with their exact phases.
    if ( vOriginals )
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(vMaps[side], lit, i)
                if ( Vec_IntEntry(vColors, lit >> 1) == 3 )
                {
                    old = Vec_IntEntry(vOriginals[side], i);
                    Vec_IntWriteEntry(vCuts, old >> 1, lit ^ (old & 1));
                }
    Vec_IntPush(vIds, 0);
    Vec_IntWriteEntry(vCis, 0, 0);
    Gia_ManForEachCo(pCopy, o, i) Acec2_BitWrite(vUsed, Gia_ObjFaninId0p(pCopy, o), 1);
    for ( i = Gia_ManObjNum(pCopy)-1; i > 0; i-- )
    {
        o = Gia_ManObj(pCopy, i);
        if ( !Vec_BitEntry(vUsed, i) || !Gia_ObjIsAnd(o) || Vec_IntEntry(vCuts, i) >= 0 ) continue;
        Acec2_BitWrite(vUsed, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(vUsed, Gia_ObjFaninId1(o, i), 1);
    }
    Gia_ManForEachCi(pCopy, o, i)
    {
        lit = Gia_ManAppendCi(p); Vec_IntPush(vIds, Gia_ObjId(pCopy, o));
        Vec_IntWriteEntry(vMap, Gia_ObjId(pCopy, o), lit);
        Vec_IntWriteEntry(vCis, Gia_ObjId(pCopy, o), lit);
    }
    Gia_ManForEachAnd(pCopy, o, i)
        if ( Vec_BitEntry(vUsed, i) && (cut = Vec_IntEntry(vCuts, i)) >= 0 )
        {
            if ( Vec_IntEntry(vCis, cut >> 1) < 0 )
            { Vec_IntWriteEntry(vCis, cut >> 1, Gia_ManAppendCi(p)); Vec_IntPush(vIds, cut >> 1); }
            Vec_IntWriteEntry(vMap, i, Vec_IntEntry(vCis, cut >> 1) ^ (cut & 1));
        }
    Gia_ManForEachAnd(pCopy, o, i)
    {
        if ( !Vec_BitEntry(vUsed, i) || Vec_IntEntry(vCuts, i) >= 0 ) continue;
        nObjs = Gia_ManObjNum(p);
        lit = Gia_ManAppendAnd2(p, Vec_IntEntry(vMap, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
                                 Vec_IntEntry(vMap, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o));
        Vec_IntWriteEntry(vMap, i, lit);
        if ( Gia_ManObjNum(p) != nObjs ) Vec_IntPush(vIds, i);
    }
    Gia_ManForEachCo(pCopy, o, i)
    { Gia_ManAppendCo(p, Vec_IntEntry(vMap, Gia_ObjFaninId0p(pCopy, o)) ^ Gia_ObjFaninC0(o)); Vec_IntPush(vIds, -1); }
    pClean = Gia_ManCleanup(p);
    *pvOrig = Vec_IntStartFull(Gia_ManObjNum(pClean)); Vec_IntWriteEntry(*pvOrig, 0, 0);
    Gia_ManForEachObj(p, o, i)
        if ( !Gia_ObjIsCo(o) && ~o->Value ) Vec_IntWriteEntry(*pvOrig, o->Value >> 1, Vec_IntEntry(vIds, i));
    Vec_IntFree(vCuts); Vec_IntFree(vCis);
    Vec_BitFree(vUsed); Vec_IntFree(vMap); Vec_IntFree(vIds); Gia_ManStop(p);
    return pClean;
}

/**Function*************************************************************

  Synopsis    [Proposes cross-design operand pairs using private simulation.]

  Description [Only candidate outputs are selected here. All returned pairs,
  including constant candidates, still require a Boolean proof before they
  can change the reconstruction maps.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_OperandPairs( Gia_Man_t * p, Vec_Int_t * vBounds, int nOperands, int nLookup, Vec_Int_t * vColors, Acec2_Align_t * pAlign )
{
    if ( Gia_ManCiNum(p) > ABC_INT_MAX/8 || Vec_IntSize(vBounds) > ABC_INT_MAX/8 )
        return Vec_IntAlloc(0);
    Vec_Wrd_t * vSim = Vec_WrdStart(Gia_ManObjNum(p)), * vKeys;
    Vec_Int_t * vIds, * vFirst = Vec_IntStartFull(2*Vec_IntSize(vBounds)), * vPairs = Vec_IntAlloc(100);
    Vec_Bit_t * vPhase = Vec_BitStart(Gia_ManObjNum(p));
    Gia_Obj_t * o;
    word state = ABC_CONST(0x218B5A4F2D7639C1), a, b;
    int i, w, nWords, lit, id, side, ref, other, nonzero;
    if ( !pAlign->vPatterns )
    {
        pAlign->vPatterns = Vec_WrdStart(8*Gia_ManCiNum(p)); pAlign->nPatterns = 64;
        Gia_ManForEachCi(p, o, i)
        {
            Acec2_Random(&state);
            Vec_WrdWriteEntry(pAlign->vPatterns, 8*i, state & ~(word)1);
        }
    }
    nWords = Abc_MinInt(8, (pAlign->nPatterns+63)/64);
    vKeys = Vec_WrdStart(nWords*Vec_IntSize(vBounds));
    for ( w = 0; w < nWords; w++ )
    {
        Gia_ManForEachCi(p, o, i) Vec_WrdWriteEntry(vSim, Gia_ObjId(p, o), Vec_WrdEntry(pAlign->vPatterns, 8*i+w));
        Gia_ManForEachAnd(p, o, i)
        {
            a = Vec_WrdEntry(vSim, Gia_ObjFaninId0(o, i)); b = Vec_WrdEntry(vSim, Gia_ObjFaninId1(o, i));
            a = (Gia_ObjFaninC0(o) ? ~a : a) & (Gia_ObjFaninC1(o) ? ~b : b);
            Vec_WrdWriteEntry(vSim, i, a);
            if ( !w ) Acec2_BitWrite(vPhase, i, (int)(a & 1));
        }
        if ( !w ) Gia_ManForEachCi(p, o, i) Acec2_BitWrite(vPhase, Gia_ObjId(p, o), 0);
        Vec_IntForEachEntry(vBounds, lit, i)
        {
            a = Vec_WrdEntry(vSim, lit >> 1);
            Vec_WrdWriteEntry(vKeys, nWords*i+w, Vec_BitEntry(vPhase, lit >> 1) ? ~a : a);
        }
    }
    vIds = Hsh_WrdManHashArray(vKeys, nWords);
    Vec_IntForEachEntry(vBounds, lit, i)
    {
        if ( i >= nLookup ) continue;
        id = Vec_IntEntry(vIds, i); side = Vec_IntEntry(vColors, lit >> 1) == 2;
        if ( Vec_IntEntry(vFirst, 2*id+side) < 0 ) Vec_IntWriteEntry(vFirst, 2*id+side, i);
    }
    Vec_IntForEachEntry(vBounds, lit, i)
    {
        lit = (lit & ~1) ^ Vec_BitEntry(vPhase, lit >> 1); nonzero = 0;
        for ( w = 0; w < nWords; w++ ) nonzero |= Vec_WrdEntry(vKeys, nWords*i+w) != 0;
        if ( !nonzero )
        {
            if ( i < nOperands || i >= nLookup ) Vec_IntPushTwo(vPairs, 0, lit);
            continue;
        }
        if ( i >= nOperands ) continue;
        id = Vec_IntEntry(vIds, i); side = Vec_IntEntry(vColors, lit >> 1) == 2;
        other = Vec_IntEntry(vFirst, 2*id+!side);
        if ( other < 0 || (other < nOperands && other < i) ) continue;
        ref = Vec_IntEntry(vBounds, other); ref = (ref & ~1) ^ Vec_BitEntry(vPhase, ref >> 1);
        Vec_IntPushTwo(vPairs, side ? ref : lit, side ? lit : ref);
    }
    Vec_BitFree(vPhase); Vec_WrdFree(vSim); Vec_WrdFree(vKeys); Vec_IntFree(vIds); Vec_IntFree(vFirst);
    return vPairs;
}

/**Function*************************************************************

  Synopsis    [Proves arithmetic constant candidates without speculation.]

  Description [A direct cone query avoids refining irrelevant speculative
  classes before a small constant identity can be proved. Only outputs
  changed to zero by the existing SAT engine are returned for merging.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_ProveConstants( Gia_Man_t * p, Vec_Int_t * vPairs, Acec2_Par_t * pPars, abctime Deadline, Acec2_Align_t * pAlign )
{
    Gia_Man_t * pCopy, * pClean, * pReduced;
    Vec_Int_t * vLits = Vec_IntAlloc(100), * vProved = Vec_IntAlloc(100);
    Cec_ParSat_t Pars;
    Cec_ParLimit_t Limits;
    int i, j, lit, bit, slot, nRefined = 0;
    Abc_Cex_t * pCex;
    word mask, value;
    abctime clk = Abc_Clock();
    for ( i = 0; i < Vec_IntSize(vPairs); i += 2 )
        if ( !Vec_IntEntry(vPairs, i) ) Vec_IntPush(vLits, Vec_IntEntry(vPairs, i+1));
    if ( !Vec_IntSize(vLits) || Acec2_Stop(pPars, Deadline) ) { Vec_IntFree(vLits); return vProved; }
    assert(!Gia_ManCoNum(p));
    pCopy = Gia_ManDup(p);
    Vec_IntForEachEntry(vLits, lit, i) Gia_ManAppendCo(pCopy, lit);
    pClean = Gia_ManCleanup(pCopy); Gia_ManStop(pCopy);
    Cec_ManSatSetDefaultParams(&Pars); Pars.nBTLimit = 100; Pars.fCheckMiter = 0; Pars.fSaveCexes = pAlign != NULL;
    Limits.TimeToStop = Deadline;
    Limits.RunId = pPars->RunId; Limits.pFuncStop = pPars->pFuncStop; Limits.pCancelled = pPars->pCancelled; Pars.pLimits = &Limits;
    pReduced = Cec_ManSatSolving(pClean, &Pars, 1);
    if ( pReduced )
        Vec_IntForEachEntry(vLits, lit, i)
            if ( !Gia_ObjFaninLit0p(pReduced, Gia_ManCo(pReduced, i)) ) Vec_IntPush(vProved, lit >> 1);
    if ( pAlign && pReduced && pReduced->vSeqModelVec )
        Vec_PtrForEachEntry(Abc_Cex_t *, pReduced->vSeqModelVec, pCex, i)
        {
            if ( (ABC_PTRUINT_T)pCex <= 1 ) continue;
            assert(!pCex->nRegs && pCex->nPis == Gia_ManCiNum(p));
            bit = 64+(pAlign->nPatterns++-64)%448; slot = bit/64; mask = (word)1 << (bit & 63);
            for ( j = 0; j < Gia_ManCiNum(p); j++ )
            {
                value = Vec_WrdEntry(pAlign->vPatterns, 8*j+slot) & ~mask;
                if ( Abc_InfoHasBit(pCex->pData, j) ) value |= mask;
                Vec_WrdWriteEntry(pAlign->vPatterns, 8*j+slot, value);
            }
            nRefined++;
        }
    if ( pPars->fVerbose ) Abc_Print(1, "Arithmetic constants: proved = %d / %d, refinement patterns = %d, time = %.3f sec.\n",
        Vec_IntSize(vProved), Vec_IntSize(vLits), nRefined, (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    if ( pReduced ) Gia_ManStop(pReduced);
    Gia_ManStop(pClean); Vec_IntFree(vLits);
    return vProved;
}

/**Function*************************************************************

  Synopsis    [Copies a small group of operand cones with original IDs.]

  Description [All inputs retain their interface positions. The iterative
  traversal avoids a recursion limit on deep Boolean control logic.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_OperandCone( Gia_Man_t * p, int * pPos, int Count, Vec_Int_t ** pvOrig )
{
    Gia_Man_t * q = Gia_ManStart(1000);
    Vec_Bit_t * vUsed = Vec_BitStart(Gia_ManObjNum(p));
    Vec_Int_t * vMap = Vec_IntStart(Gia_ManObjNum(p)), * vOrig = Vec_IntAlloc(1000);
    Gia_Obj_t * o;
    int i, lit;
    Vec_IntPush(vOrig, 0);
    for ( i = 0; i < Count; i++ )
        Acec2_BitWrite(vUsed, Gia_ObjFaninId0p(p, Gia_ManCo(p, pPos[i])), 1);
    for ( i = Gia_ManObjNum(p)-1; i > 0; i-- )
    {
        o = Gia_ManObj(p, i);
        if ( !Vec_BitEntry(vUsed, i) || !Gia_ObjIsAnd(o) ) continue;
        Acec2_BitWrite(vUsed, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(vUsed, Gia_ObjFaninId1(o, i), 1);
    }
    Gia_ManForEachCi(p, o, i)
    {
        lit = Gia_ManAppendCi(q); Vec_IntWriteEntry(vMap, Gia_ObjId(p, o), lit); Vec_IntPush(vOrig, Gia_ObjId(p, o));
    }
    Gia_ManForEachAnd(p, o, i)
    {
        if ( !Vec_BitEntry(vUsed, i) ) continue;
        lit = Gia_ManAppendAnd(q, Vec_IntEntry(vMap, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
                                 Vec_IntEntry(vMap, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o));
        Vec_IntWriteEntry(vMap, i, lit); Vec_IntPush(vOrig, i);
    }
    for ( i = 0; i < Count; i++ )
    {
        o = Gia_ManCo(p, pPos[i]); Gia_ManAppendCo(q, Vec_IntEntry(vMap, Gia_ObjFaninId0p(p, o)) ^ Gia_ObjFaninC0(o));
        Vec_IntPush(vOrig, -1);
    }
    Vec_BitFree(vUsed); Vec_IntFree(vMap); *pvOrig = vOrig;
    return q;
}

/**Function*************************************************************

  Synopsis    [Sweeps small operand groups without hard cones starving easy ones.]

  Description [Only accepted Boolean correspondences are transferred. A
  rotating group index lets subsequent arithmetic passes revisit unfinished
  local proofs under the same overall deadline.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_SweepOperandGroups( Gia_Man_t * p, Cec_ParFra_t * pPars, Acec2_Align_t * pAlign )
{
    Cec_ParFra_t Pars;
    Cec_ParLimit_t Limits;
    Gia_Man_t * pPart, * pReduced;
    Vec_Int_t * vOrig, * vLevels = Vec_IntStart(Gia_ManObjNum(p));
    Vec_Wrd_t * vOrder = Vec_WrdAlloc(Gia_ManCoNum(p)/2);
    Gia_Obj_t * o;
    int nGroups = (Gia_ManCoNum(p)+31)/32, group, first, count, i, a, b, pos[32];
    abctime clk;
    assert(!(Gia_ManCoNum(p) & 1));
    Gia_ManForEachAnd(p, o, i)
        Vec_IntWriteEntry(vLevels, i, 1+Abc_MaxInt(Vec_IntEntry(vLevels, Gia_ObjFaninId0(o, i)), Vec_IntEntry(vLevels, Gia_ObjFaninId1(o, i))));
    for ( i = 0; i < Gia_ManCoNum(p); i += 2 )
    {
        a = Vec_IntEntry(vLevels, Gia_ObjFaninId0p(p, Gia_ManCo(p, i)));
        b = Vec_IntEntry(vLevels, Gia_ObjFaninId0p(p, Gia_ManCo(p, i+1)));
        Vec_WrdPush(vOrder, ((word)(unsigned)Abc_MaxInt(a, b) << 32) | (unsigned)i);
    }
    if ( Vec_WrdSize(vOrder) > 1 ) Vec_WrdSort(vOrder, 0);
    Vec_IntFree(vLevels);
    Vec_IntFreeP(&p->vIdsEquiv); p->vIdsEquiv = Vec_IntAlloc(1000);
    if ( !pAlign->nSweepLeft || pAlign->nSweepLeft > nGroups ) pAlign->nSweepLeft = nGroups;
    while ( pAlign->nSweepLeft )
    {
        if ( Cec_ManIsStopped(pPars->pLimits) ) break;
        group = pAlign->nSweepGroup % nGroups; pAlign->nSweepGroup = group+1; pAlign->nSweepLeft--;
        first = 32*group; clk = Abc_Clock();
        count = Abc_MinInt(32, Gia_ManCoNum(p)-first);
        for ( i = 0; i < count; i += 2 )
        { pos[i] = (int)(unsigned)Vec_WrdEntry(vOrder, (first+i)/2); pos[i+1] = pos[i]+1; }
        pPart = Acec2_OperandCone(p, pos, count, &vOrig);
        Pars = *pPars; Pars.fVerbose = 0;
        memset(&Limits, 0, sizeof(Limits));
        if ( pPars->pLimits ) Limits = *pPars->pLimits;

        Pars.pLimits = &Limits;
        pReduced = Cec_ManSatSweeping(pPart, &Pars, 1);
        if ( pReduced ) Gia_ManStop(pReduced);
        if ( pPart->vIdsEquiv )
            for ( i = 0; i < Vec_IntSize(pPart->vIdsEquiv); i += 2 )
            {
                a = Vec_IntEntry(vOrig, Vec_IntEntry(pPart->vIdsEquiv, i));
                b = Vec_IntEntry(vOrig, Vec_IntEntry(pPart->vIdsEquiv, i+1));
                assert(a >= 0 && b >= 0); Vec_IntPushTwo(p->vIdsEquiv, a, b);
            }
        if ( pPars->fVerbose ) Abc_Print(1, "  Operand group %d/%d: ANDs = %d, proved pairs = %d, time = %.3f sec.\n",
            group+1, nGroups, Gia_ManAndNum(pPart), pPart->vIdsEquiv ? Vec_IntSize(pPart->vIdsEquiv)/2 : 0, (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
        Vec_IntFree(vOrig); Gia_ManStop(pPart);
    }
    pAlign->fSweepPending = pAlign->nSweepLeft > 0;
    Vec_WrdFree(vOrder);
}

/**Function*************************************************************

  Synopsis    [Aligns internal signals using proved CEC correspondences.]

  Description [Sweeping uses a private, cleaned dual-output AIG. Only proved
  equivalences are projected back into the shared construction. Original
  adder structures remain available to detection; representatives have lower
  IDs, and a complete mapping is built before any replacement is committed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_AlignOperands( Gia_Man_t * pNew, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                                Vec_Int_t * vOutputs, Acec2_Par_t * pPars, abctime Deadline, int nMaxObjs, Acec2_AlignMode_t Mode, Acec2_Man_t ** pMans, Vec_Int_t ** vOriginals, Acec2_Align_t * pAlign )
{
    Gia_Man_t * pCopy, * pClean, * pReduced;
    Gia_Obj_t * o;
    Cec_ParFra_t Pars;
    Cec_ParLimit_t Limits;
    Vec_Int_t * vOrig, * vRep, * vMap, * vColors = NULL, * vConstants = NULL, * vNow = NULL, * vRaw = NULL;
    Vec_Bit_t * vClass, * vNeeded;
    int nObjs = Gia_ManObjNum(pNew), i, k, side, a, b, next, lit, nPairs = 0, changed = 0, failed = 0, fPairedInputs = 0;
    int nSharedBefore = 0, nSharedAfter = 0;
    abctime clk = Abc_Clock();
    if ( pAlign ) pAlign->nChanged = pAlign->nShared = 0;
    if ( Acec2_Stop(pPars, Deadline) || nObjs >= nMaxObjs ) return 0;
    for ( i = 0; i < Vec_IntSize(vOutputs)/2; i++ )
        if ( Vec_IntEntry(vOutputs, i) != Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs)/2+i) ) break;
    if ( i == Vec_IntSize(vOutputs)/2 ) return 0;
    pCopy = Gia_ManDup(pNew);
    assert(Gia_ManObjNum(pCopy) == nObjs);
    if ( Mode >= ACEC2_ALIGN_ALL_CUTS && vOriginals )
    {
        // Both original and reconstructed operand forms are exact. An
        // original Boolean cone can remain much easier after unrelated
        // arithmetic rewrites change its current implementation.
        vNow = Vec_IntStartNatural(nObjs); vRaw = Vec_IntStartFull(nObjs);
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(vMaps[side], lit, i)
            {
                a = Vec_IntEntry(vOriginals[side], i);
                Vec_IntWriteEntry(vNow, a >> 1, lit >> 1);
                b = a ^ (lit & 1);
                if ( Vec_IntEntry(vRaw, lit >> 1) < 0 || b < Vec_IntEntry(vRaw, lit >> 1) ) Vec_IntWriteEntry(vRaw, lit >> 1, b);
            }
    }
    if ( Mode && pMans )
    {
        Vec_Bit_t * vSeen = Vec_BitStart(nObjs);
        Vec_Bit_t * vBlocked[2];
        Vec_Int_t * vLeaves, * vBounds = Vec_IntAlloc(100), * vPairs;
        int tree, id, input, value, fanin, nOperands, nLookup, nPatterns;
        // Focus the later sweeps on logic feeding partial products. Whole
        // output cones can spend their budget inside the very multipliers
        // whose operand correspondence this stage is meant to establish.
        vColors = Vec_IntStart(nObjs);
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(vMaps[side], value, i)
                Vec_IntWriteEntry(vColors, value >> 1, Vec_IntEntry(vColors, value >> 1) | (1 << side));
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(vMaps[side], value, i)
                nSharedBefore += Vec_IntEntry(vColors, value >> 1) == 3;
        for ( side = 0; side < 2; side++ ) vBlocked[side] = Acec2_OperandBlocked(pMans[side], vMaps[side], vColors);
        for ( side = 0; side < 2; side++ )
            Vec_WecForEachLevel(pMans[side]->vLeaves, vLeaves, tree)
                for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
                {
                    id = Vec_IntEntry(vLeaves, i) >> 1; o = Gia_ManObj(pMans[side]->pGia, id);
                    if ( !Gia_ObjIsAnd(o) || Gia_ObjIsXor(o) || Gia_ObjIsMux(pMans[side]->pGia, o) || Gia_ObjIsMuxType(o) ) continue;
                    for ( input = 0; input < 2; input++ )
                    {
                        fanin = input ? Gia_ObjFaninId1(o, id) : Gia_ObjFaninId0(o, id);
                        if ( Mode <= ACEC2_ALIGN_OPERAND_CONES && Vec_BitEntry(vBlocked[side], fanin) ) continue;
                        value = Vec_IntEntry(vMaps[side], fanin);
                        if ( (value >> 1) <= Gia_ManCiNum(pNew) || Vec_IntEntry(vColors, value >> 1) == 3 || Vec_BitEntry(vSeen, value >> 1) ) continue;
                        Acec2_BitWrite(vSeen, value >> 1, 1); Vec_IntPush(vBounds, value);
                    }
                }
        nOperands = Vec_IntSize(vBounds);
        // A Booth operand need not directly feed a detected partial product.
        // Permit an operand proposal from either architecture to find its
        // counterpart anywhere in the other side. Only operand-anchored pairs
        // become proof targets; the lookup pool does not add unrelated queries.
        for ( side = 0; side < 2; side++ )
            Gia_ManForEachAnd(pMans[side]->pGia, o, id)
            {
                if ( Mode <= ACEC2_ALIGN_OPERAND_CONES && Vec_BitEntry(vBlocked[side], id) ) continue;
                value = Vec_IntEntry(vMaps[side], id);
                if ( (value >> 1) <= Gia_ManCiNum(pNew) || Vec_IntEntry(vColors, value >> 1) == 3 || Vec_BitEntry(vSeen, value >> 1) ) continue;
                Acec2_BitWrite(vSeen, value >> 1, 1); Vec_IntPush(vBounds, value);
            }
        nLookup = Vec_IntSize(vBounds);
        Vec_BitFill(vSeen, nObjs, 0);
        for ( i = 0; i < nOperands; i++ ) Acec2_BitWrite(vSeen, Vec_IntEntry(vBounds, i) >> 1, 1);
        // Shifted Booth encodings can retain redundant zero sum bits. These
        // are useful local proof targets even when no later partial product
        // consumes them. Include parity boundaries as constant proposals;
        // nonconstant additions to this list are ignored by the filter.
        for ( side = 0; side < 2; side++ )
            for ( i = 0; i < Vec_IntSize(pMans[side]->vXors); i += 5 )
            {
                id = Vec_IntEntry(pMans[side]->vXors, i+4) >> 1;
                value = Vec_IntEntry(vMaps[side], id);
                if ( (value >> 1) <= Gia_ManCiNum(pNew) || Vec_IntEntry(vColors, value >> 1) == 3 || Vec_BitEntry(vSeen, value >> 1) ) continue;
                Acec2_BitWrite(vSeen, value >> 1, 1); Vec_IntPush(vBounds, value);
            }
        vPairs = Acec2_OperandPairs(pNew, vBounds, nOperands, nLookup, vColors, pAlign); nPatterns = pAlign->nPatterns;
        vConstants = Acec2_ProveConstants(pNew, vPairs, pPars, Deadline, pAlign);
        if ( pAlign->nPatterns != nPatterns )
        { Vec_IntFree(vPairs); vPairs = Acec2_OperandPairs(pNew, vBounds, nOperands, nLookup, vColors, pAlign); }
        // Failed constant proposals must not enlarge the operand sweep
        // with unrelated cones. They already received a direct SAT query.
        for ( i = 0; i < Vec_IntSize(vPairs); i += 2 )
            if ( Vec_IntEntry(vPairs, i) )
            {
                a = Vec_IntEntry(vPairs, i); b = Vec_IntEntry(vPairs, i+1);
                Gia_ManAppendCo(pCopy, a); Gia_ManAppendCo(pCopy, b);
                if ( vRaw && Vec_IntEntry(vRaw, a >> 1) >= 0 && Vec_IntEntry(vRaw, b >> 1) >= 0 )
                {
                    int rawA = Vec_IntEntry(vRaw, a >> 1) ^ (a & 1), rawB = Vec_IntEntry(vRaw, b >> 1) ^ (b & 1);
                    if ( rawA != a || rawB != b ) { Gia_ManAppendCo(pCopy, rawA); Gia_ManAppendCo(pCopy, rawB); }
                }
            }
        fPairedInputs = Gia_ManCoNum(pCopy) != 0;
        Vec_IntFree(vBounds); Vec_IntFree(vPairs);
        Vec_BitFree(vSeen); Vec_BitFree(vBlocked[0]); Vec_BitFree(vBlocked[1]);
    }
    if ( Mode && pMans && !Gia_ManCoNum(pCopy) && !Vec_IntSize(vConstants) )
    { Vec_IntFree(vConstants); Vec_IntFree(vColors); Vec_IntFreeP(&vNow); Vec_IntFreeP(&vRaw); Gia_ManStop(pCopy); return 0; }
    if ( !Gia_ManCoNum(pCopy) && !(Mode && pMans) )
    for ( i = 0; i < Vec_IntSize(vOutputs)/2; i++ )
    {
        Gia_ManAppendCo(pCopy, Vec_IntEntry(vOutputs, i));
        Gia_ManAppendCo(pCopy, Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs)/2+i));
    }
    if ( vColors && (Mode == ACEC2_ALIGN_OPERAND_CUTS || Mode == ACEC2_ALIGN_ALL_CUTS) )
        pClean = Acec2_OperandAbstract(pCopy, vColors, Mode == ACEC2_ALIGN_ALL_CUTS ? vOriginals : NULL, vMaps, &vOrig);
    else
    {
        pClean = Gia_ManCleanup(pCopy);
        vOrig = Vec_IntStartFull(Gia_ManObjNum(pClean)); Vec_IntWriteEntry(vOrig, 0, 0);
        for ( i = 1; i < nObjs; i++ )
            if ( ~Gia_ManObj(pCopy, i)->Value )
                Vec_IntWriteEntry(vOrig, Abc_Lit2Var(Gia_ManObj(pCopy, i)->Value), i);
    }
    Vec_IntFreeP(&vColors);
    Cec_ManFraSetDefaultParams(&Pars);
    Pars.nBTLimit = Mode ? 1000 : 100;
    Pars.nItersMax = Mode ? 8 : 2; Pars.nWords = 4; Pars.nRounds = 8;
    // Later rounds also prove same-side constants and internal identities.
    // Restricting every round to cross-design pairs can leave the redundant
    // constant carries of shifted Booth products unresolved.
    Pars.fDualOut = Mode == ACEC2_ALIGN_OUTPUTS || fPairedInputs; Pars.fCheckMiter = 0; Pars.fUseOrigIds = 1; Pars.fUseProvedIds = 1; Pars.fSatSweeping = Mode == ACEC2_ALIGN_OUTPUTS;
    Pars.fVerbose = pPars->fVerbose;
    Limits.TimeToStop = Deadline;
    Limits.RunId = pPars->RunId; Limits.pFuncStop = pPars->pFuncStop; Limits.pCancelled = pPars->pCancelled; Pars.pLimits = &Limits;
    pReduced = NULL;
    if ( !vConstants || !Vec_IntSize(vConstants) )
    {
        if ( Mode >= ACEC2_ALIGN_ALL_CUTS && fPairedInputs && Gia_ManCoNum(pClean) > 64 ) Acec2_SweepOperandGroups(pClean, &Pars, pAlign);
        else pReduced = Cec_ManSatSweeping(pClean, &Pars, 1);
    }
    if ( pReduced ) Gia_ManStop(pReduced);
    vRep = Vec_IntStartNatural(nObjs); vMap = Vec_IntStart(nObjs); vClass = Vec_BitStart(nObjs); vNeeded = Vec_BitStart(nObjs);
    if ( vConstants )
        Vec_IntForEachEntry(vConstants, a, i)
            if ( a && Vec_IntEntry(vRep, a) ) { Vec_IntWriteEntry(vRep, a, 0); nPairs++; }
    Vec_IntFreeP(&vConstants);
    if ( pClean->vIdsEquiv )
        for ( i = 0; i < Vec_IntSize(pClean->vIdsEquiv); i += 2 )
        {
            a = Vec_IntEntry(vOrig, Vec_IntEntry(pClean->vIdsEquiv, i));
            b = Vec_IntEntry(vOrig, Vec_IntEntry(pClean->vIdsEquiv, i+1));
            if ( a < 0 || b < 0 ) continue;
            if ( vNow ) { a = Vec_IntEntry(vNow, a); b = Vec_IntEntry(vNow, b); }
            while ( a != Vec_IntEntry(vRep, a) ) a = Vec_IntEntry(vRep, a);
            while ( b != Vec_IntEntry(vRep, b) ) b = Vec_IntEntry(vRep, b);
            if ( a == b ) continue;
            Vec_IntWriteEntry(vRep, Abc_MaxInt(a, b), Abc_MinInt(a, b)); nPairs++;
        }
    if ( nPairs )
    {
        // Old normalized alternatives remain available for template lookup,
        // but need not be duplicated by every Boolean alignment. Rebuild
        // only the current mappings and their proved representatives.
        for ( side = 0; side < 2; side++ )
        {
            Vec_IntForEachEntry(vMaps[side], lit, i) Acec2_BitWrite(vNeeded, lit >> 1, 1);
            Vec_IntForEachEntry(vReplaces[side], lit, i) if ( lit >= 0 ) Acec2_BitWrite(vNeeded, lit >> 1, 1);
        }
        Vec_IntForEachEntry(vOutputs, lit, i) Acec2_BitWrite(vNeeded, lit >> 1, 1);
        for ( i = nObjs-1; i > 0; i-- )
        {
            if ( !Vec_BitEntry(vNeeded, i) ) continue;
            Acec2_BitWrite(vNeeded, Vec_IntEntry(vRep, i), 1);
            o = Gia_ManObj(pCopy, i);
            if ( !Gia_ObjIsAnd(o) ) continue;
            Acec2_BitWrite(vNeeded, Gia_ObjFaninId0(o, i), 1);
            Acec2_BitWrite(vNeeded, Gia_ObjFaninId1(o, i), 1);
        }
        Gia_ManSetPhase(pCopy);
        for ( i = 0; i < nObjs; i++ )
        {
            a = i;
            while ( a != Vec_IntEntry(vRep, a) ) a = Vec_IntEntry(vRep, a);
            for ( k = i; k != a; k = next )
            { next = Vec_IntEntry(vRep, k); Vec_IntWriteEntry(vRep, k, a); }
            if ( !Vec_BitEntry(vNeeded, i) ) { Vec_IntWriteEntry(vMap, i, 2*i); continue; }
            o = Gia_ManObj(pCopy, i);
            if ( a != i )
            {
                Acec2_BitWrite(vClass, a, 1);
                lit = Vec_IntEntry(vMap, a) ^ o->fPhase ^ Gia_ManObj(pCopy, a)->fPhase;
            }
            else if ( !Gia_ObjIsAnd(o) ) lit = Abc_Var2Lit(i, 0);
            else lit = Gia_ManHashAnd(pNew,
                Vec_IntEntry(vMap, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
                Vec_IntEntry(vMap, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o));
            Vec_IntWriteEntry(vMap, i, lit);
            if ( (i & 255) == 0 && (Gia_ManObjNum(pNew) >= nMaxObjs || Acec2_Stop(pPars, Deadline)) )
            { failed = 1; break; }
        }
        if ( !failed )
        {
            for ( side = 0; side < 2; side++ )
            {
                Vec_IntForEachEntry(vMaps[side], lit, i)
                {
                    a = Vec_IntEntry(vMap, Abc_Lit2Var(lit)) ^ Abc_LitIsCompl(lit);
                    // Pin the representative as well as its other members.
                    // Otherwise the next arithmetic rebuild can change that
                    // representative's structure and undo the proved sharing.
                    if ( Vec_BitEntry(vClass, Vec_IntEntry(vRep, Abc_Lit2Var(lit))) )
                        Vec_IntWriteEntry(vReplaces[side], i, lit);
                    changed += a != lit; Vec_IntWriteEntry(vMaps[side], i, a);
                }
                Vec_IntForEachEntry(vReplaces[side], lit, i)
                    if ( lit >= 0 ) Vec_IntWriteEntry(vReplaces[side], i, Vec_IntEntry(vMap, Abc_Lit2Var(lit)) ^ Abc_LitIsCompl(lit));
            }
            Vec_IntForEachEntry(vOutputs, lit, i)
                Vec_IntWriteEntry(vOutputs, i, Vec_IntEntry(vMap, Abc_Lit2Var(lit)) ^ Abc_LitIsCompl(lit));
        }
    }
    if ( changed && Mode && pMans )
    {
        vColors = Vec_IntStart(Gia_ManObjNum(pNew));
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(vMaps[side], lit, i)
                Vec_IntWriteEntry(vColors, lit >> 1, Vec_IntEntry(vColors, lit >> 1) | (1 << side));
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(vMaps[side], lit, i)
                nSharedAfter += Vec_IntEntry(vColors, lit >> 1) == 3;
        Vec_IntFree(vColors);
    }
    if ( pPars->fVerbose )
        Abc_Print(1, "Operand alignment: cone ANDs = %d, boundaries = %d, SAT-proved pairs = %d, remapped signals = %d, new shared signals = %d, time = %.3f sec.\n",
            Gia_ManAndNum(pClean), Gia_ManCoNum(pClean), nPairs, changed, Abc_MaxInt(0, nSharedAfter-nSharedBefore), (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    Vec_BitFree(vNeeded); Vec_BitFree(vClass); Vec_IntFree(vRep); Vec_IntFree(vMap); Vec_IntFree(vOrig);
    Vec_IntFreeP(&vNow); Vec_IntFreeP(&vRaw); Gia_ManStop(pCopy); Gia_ManStop(pClean);
    if ( changed && pAlign && (!Mode || nSharedAfter > nSharedBefore) )
    {
        // New equalities simplify the shallow groups and their successors.
        // Restart from these dependencies before revisiting harder cones.
        pAlign->nSweepGroup = pAlign->nSweepLeft = pAlign->fSweepPending = 0;
    }
    if ( pAlign ) { pAlign->nChanged = changed; pAlign->nShared = Abc_MaxInt(0, nSharedAfter-nSharedBefore); }
    return changed || (Mode >= ACEC2_ALIGN_ALL_CUTS && pAlign && pAlign->fSweepPending);
}

/**Function*************************************************************

  Synopsis    [Discards obsolete reconstruction alternatives between passes.]

  Description [The original structural prefix keeps its IDs, preserving
  template search keys. Current maps, pinned proofs and output cones remain
  live. All remapping is committed only after the private copy is complete.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_CompactMiter( Gia_Man_t * p, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                                     Vec_Int_t * vOutputs, int nOriginal, Acec2_Par_t * pPars, abctime Deadline )
{
    Gia_Man_t * q = Gia_ManStart(1000);
    Vec_Bit_t * vUsed = Vec_BitStart(Gia_ManObjNum(p));
    Vec_Int_t * vMap = Vec_IntStartFull(Gia_ManObjNum(p)), * v;
    Gia_Obj_t * o;
    int side, kind, i, lit, failed = 0;
    assert(!Gia_ManCoNum(p));
    for ( i = 0; i < nOriginal; i++ ) Acec2_BitWrite(vUsed, i, 1);
    for ( side = 0; side < 2; side++ )
        for ( kind = 0; kind < 2; kind++ )
        {
            v = kind ? vReplaces[side] : vMaps[side];
            Vec_IntForEachEntry(v, lit, i) if ( lit >= 0 ) Acec2_BitWrite(vUsed, lit >> 1, 1);
        }
    Vec_IntForEachEntry(vOutputs, lit, i) Acec2_BitWrite(vUsed, lit >> 1, 1);
    for ( i = Gia_ManObjNum(p)-1; i >= nOriginal; i-- )
    {
        o = Gia_ManObj(p, i);
        if ( !Vec_BitEntry(vUsed, i) || !Gia_ObjIsAnd(o) ) continue;
        Acec2_BitWrite(vUsed, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(vUsed, Gia_ObjFaninId1(o, i), 1);
    }
    q->pName = Abc_UtilStrsav(p->pName); Gia_ManHashAlloc(q); Vec_IntWriteEntry(vMap, 0, 0);
    Gia_ManForEachCi(p, o, i) Vec_IntWriteEntry(vMap, Gia_ObjId(p, o), Gia_ManAppendCi(q));
    Gia_ManForEachAnd(p, o, i)
    {
        if ( (i & 255) == 0 && Acec2_Stop(pPars, Deadline) ) { failed = 1; break; }
        if ( !Vec_BitEntry(vUsed, i) ) continue;
        lit = Gia_ManHashAnd(q, Vec_IntEntry(vMap, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
                                Vec_IntEntry(vMap, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o));
        assert(i >= nOriginal || lit == 2*i); Vec_IntWriteEntry(vMap, i, lit);
    }
    if ( !failed )
    {
        for ( side = 0; side < 2; side++ )
            for ( kind = 0; kind < 2; kind++ )
            {
                v = kind ? vReplaces[side] : vMaps[side];
                Vec_IntForEachEntry(v, lit, i)
                    if ( lit >= 0 ) Vec_IntWriteEntry(v, i, Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1));
            }
        Vec_IntForEachEntry(vOutputs, lit, i) Vec_IntWriteEntry(vOutputs, i, Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1));
        if ( pPars->fVerbose ) Abc_Print(1, "Arithmetic compaction: ANDs = %d -> %d.\n", Gia_ManAndNum(p), Gia_ManAndNum(q));
    }
    Vec_IntFree(vMap); Vec_BitFree(vUsed);
    if ( failed ) { Gia_ManStop(q); return NULL; }
    return q;
}

/**Function*************************************************************

  Synopsis    [Detects a changed Boolean proof obligation by exact map comparison.]

  Description [The destination is append-only between compactions. Its
  source maps, pins and outputs identify the live
  proof obligation. Callers clear this state when node IDs are rebuilt.]

  SideEffects [Updates the caller-owned previous-obligation vector.]

  SeeAlso     []

***********************************************************************/
static int Acec2_ProbeFresh( Vec_Int_t * previous, Vec_Int_t ** maps, Vec_Int_t ** replaces,
                            Vec_Int_t * outputs, Acec2_Par_t * pars )
{
    Vec_Int_t * current, * vectors[5]; int i, changed;
    if ( !previous ) return 1;
    vectors[0] = maps[0]; vectors[1] = maps[1]; vectors[2] = replaces[0]; vectors[3] = replaces[1];
    vectors[4] = outputs;
    current = Vec_IntAlloc(Vec_IntSize(previous)); Vec_IntPush(current, pars->nBTLimit);
    for ( i = 0; i < 5; i++ ) { Vec_IntPush(current, Vec_IntSize(vectors[i])); Vec_IntAppend(current, vectors[i]); }
    changed = !Vec_IntEqual(previous, current);
    if ( changed ) { Vec_IntClear(previous); Vec_IntAppend(previous, current); }
    Vec_IntFree(current); return changed;
}

/**Function*************************************************************

  Synopsis    [Tests for recorded arithmetic obligations exhausted by effort.]

  Description [An empty fixed point does not justify increasing budgets.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_NeedsEffort( Acec2_Man_t * m, Acec2_PolyCtx_t * context )
{
    Vec_Int_t * cache; int i, kind, hits = 0, limits = 0;
    if ( !m ) return 0;
    if ( m->fPolyEffortLimit ) return 1;
    Acec2_PolyRegionReuse(context, &hits, &limits);
    if ( limits ) return 1;
    for ( kind = 0; kind < 2; kind++ )
    {
        cache = kind ? m->vCertificates : m->vFailedProofs;
        if ( !cache ) continue;
        for ( i = 0; i < Vec_IntSize(cache); i += 4 ) if ( Vec_IntEntry(cache, i) == 3 ) return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks current output mappings after a productive proof step.]

  Description [A bounded concrete check runs before further recognition.
  Only a complete Boolean proof terminates arithmetic discovery.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ProveOutputs( Gia_Man_t * pNew, Vec_Int_t * vOutputs, Vec_Int_t ** vMaps,
                               Vec_Int_t ** vReplaces,
                               Acec2_Par_t * pPars, abctime Deadline, int * pnNew, int fWide, Vec_Int_t * vPrevious, Acec2_NormStats_t * stats )
{
    Gia_Man_t * pTry, * pClean;
    Vec_Int_t * vPairs = NULL, * vOrig = NULL, * vMapped = NULL;
    int i, a, b, result, changed = 0;
    abctime clk = Abc_Clock();
    if ( Acec2_Stop(pPars, Deadline) ) return 0;
    if ( !Acec2_ProbeFresh(vPrevious, vMaps, vReplaces, vOutputs, pPars) ) return 0;
    stats->iPendingStep = 5;
    pTry = Gia_ManDup(pNew);
    for ( i = 0; i < Vec_IntSize(vOutputs)/2; i++ )
    {
        a = Vec_IntEntry(vOutputs, i); b = Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs)/2+i);
        Gia_ManAppendCo(pTry, a);
        Gia_ManAppendCo(pTry, b);
    }
    pClean = Gia_ManCleanup(pTry);
    {
        vPairs = Vec_IntAlloc(100); vMapped = Vec_IntAlloc(100);
        vOrig = Vec_IntStartFull(Gia_ManObjNum(pClean)); Vec_IntWriteEntry(vOrig, 0, 0);
        for ( i = 1; i < Gia_ManObjNum(pNew); i++ )
            if ( ~Gia_ManObj(pTry, i)->Value )
                Vec_IntWriteEntry(vOrig, Gia_ManObj(pTry, i)->Value >> 1, 2*i ^ (Gia_ManObj(pTry, i)->Value & 1));
    }
    Gia_ManStop(pTry);
    result = Acec2_ProveConcreteEx(pClean, pPars, Deadline, vPairs, fWide);
    if ( vPairs && Vec_IntSize(vPairs) && !Acec2_Stop(pPars, Deadline) )
    {
        for ( i = 0; i < Vec_IntSize(vPairs); i += 2 )
        {
            a = Vec_IntEntry(vPairs, i); b = Vec_IntEntry(vPairs, i+1);
            if ( Vec_IntEntry(vOrig, a >> 1) < 0 || Vec_IntEntry(vOrig, b >> 1) < 0 ) continue;
            Vec_IntPushTwo(vMapped, Vec_IntEntry(vOrig, a >> 1) ^ (a & 1), Vec_IntEntry(vOrig, b >> 1) ^ (b & 1));
        }
        for ( i = 0; i < Gia_ManCoNum(pClean); i += 2 )
            if ( Gia_ObjFaninLit0p(pClean, Gia_ManCo(pClean, i)) == Gia_ObjFaninLit0p(pClean, Gia_ManCo(pClean, i+1)) )
                Vec_IntPushTwo(vMapped, Vec_IntEntry(vOutputs, i/2), Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs)/2+i/2));
        changed = Acec2_AliasApply(pNew, vMaps, vReplaces, vOutputs, vMapped, pPars, Deadline);
        if ( changed > 0 ) *pnNew += changed;
        if ( pPars->fVerbose ) Abc_Print(1, "Retained concrete CEC proofs: pairs = %d, remapped signals = %d.\n", Vec_IntSize(vMapped)/2, Abc_MaxInt(0, changed));
    }
    if ( !result && changed != -2 && !Acec2_Stop(pPars, Deadline) ) result = Acec2_ProveContext(pClean, pPars, Deadline) == 1;
    Vec_IntFreeP(&vPairs); Vec_IntFreeP(&vMapped); Vec_IntFreeP(&vOrig);
    Gia_ManStop(pClean);
    stats->TimeCec += Abc_Clock()-clk;
    return changed == -2 ? -1 : result;
}

/**Function*************************************************************

  Synopsis    [Requests standalone certificates on the two source designs.]

  Description [Analysis shares the caller's cancellation and total budget.
  Completed records remain usable when later discovery reaches its limit.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ProfilePair( Gia_Man_t ** g, Acec2_Man_t ** sources, Acec2_Man_t ** profiles, Vec_Int_t * outputs, Acec2_Par_t * pars,
                               abctime Deadline, abctime Quantum, Acec2_NormStats_t * stats )
{
    Gia_Obj_t * o; Vec_Bit_t * focus; Vec_Int_t * region;
    int side, i, j, k, cell, touched, count = Vec_IntSize(outputs)/2;
    // The share was reserved at entry, before speculative work can consume
    // it. Keep source IDs, but recognize only fanins of still-open outputs.
    stats->fProfileTried = 1; stats->iPendingStep = 6;
    for ( side = 0; side < 2 && !Acec2_Stop(pars, Deadline); side++ )
    {
        abctime clk = Abc_Clock(), stop = clk+Quantum;
        if ( Deadline && stop > Deadline ) stop = Deadline;
        focus = Vec_BitStart(Gia_ManObjNum(g[side]));
        for ( i = 0; i < count; i++ )
            if ( Vec_IntEntry(outputs, i) != Vec_IntEntry(outputs, count+i) )
                Acec2_BitWrite(focus, Gia_ObjFaninId0p(g[side], Gia_ManCo(g[side], i)), 1);
        Gia_ManForEachAndReverse(g[side], o, i)
            if ( Vec_BitEntry(focus, i) )
            {
                Acec2_BitWrite(focus, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(focus, Gia_ObjFaninId1(o, i), 1);
                if ( Gia_ObjIsMux(g[side], o) ) Acec2_BitWrite(focus, Gia_ObjFaninId2(g[side], i), 1);
            }
        // Already matched sum bits can still be needed to recognize the
        // word containing an open carry. Keep complete source regions that
        // touch the open cone, then include the fanins of their other roots.
        if ( sources[side] )
            Vec_WecForEachLevel(sources[side]->vTrees, region, j)
            {
                touched = 0;
                Vec_IntForEachEntry(region, cell, k)
                {
                    Acec2_Cell_t * c = Acec2_Cell(sources[side], cell);
                    touched |= Vec_BitEntry(focus, c->Out[0] >> 1) || Vec_BitEntry(focus, c->Out[1] >> 1);
                }
                if ( !touched ) continue;
                Vec_IntForEachEntry(region, cell, k)
                {
                    Acec2_Cell_t * c = Acec2_Cell(sources[side], cell);
                    Acec2_BitWrite(focus, c->Out[0] >> 1, 1); Acec2_BitWrite(focus, c->Out[1] >> 1, 1);
                }
            }
        Gia_ManForEachAndReverse(g[side], o, i)
            if ( Vec_BitEntry(focus, i) )
            {
                stats->nProfileAnds[side]++;
                Acec2_BitWrite(focus, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(focus, Gia_ObjFaninId1(o, i), 1);
                if ( Gia_ObjIsMux(g[side], o) ) Acec2_BitWrite(focus, Gia_ObjFaninId2(g[side], i), 1);
            }
        profiles[side] = Acec2_AnalyzeFocused(g[side], pars, stop, focus);
        Vec_BitFree(focus);
        stats->TimeProfile[side] = Abc_Clock()-clk;
        if ( profiles[side] )
        {
            stats->nProfileRecords[side] = Vec_PtrSize(profiles[side]->vRecords);
            stats->fProfileLimited[side] = profiles[side]->fStopped;
        }
        if ( pars->fVerbose ) Abc_Print(1, "Standalone source analysis: side = %d, open-cone ANDs = %d, checked records = %d, stopped = %d, reserved = %.3f sec, time = %.3f sec.\n",
            side, stats->nProfileAnds[side], stats->nProfileRecords[side], stats->fProfileLimited[side],
            (double)Quantum/CLOCKS_PER_SEC, (double)stats->TimeProfile[side]/CLOCKS_PER_SEC);
    }
}

/**Function*************************************************************

  Synopsis    [Reserves ordinary CEC time after accounting for earlier checks.]

  Description [The total deadline never changes. Time already spent in the
  initial and in-loop Boolean checks counts toward the ordinary-CEC share.
  Newly proved arithmetic aliases permit another pass while retaining a
  tenth of the total budget for the final Boolean check.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static abctime Acec2_ArithmeticDeadline( Acec2_Par_t * pPars, abctime Deadline, abctime CecTime, int fProgress )
{
    abctime reserve;
    if ( !Deadline || !pPars->nTimeLimit ) return Deadline;
    reserve = (abctime)pPars->nTimeLimit*CLOCKS_PER_SEC/3;
    if ( CecTime < 0 ) CecTime = 0;
    if ( CecTime > reserve ) CecTime = reserve;
    reserve -= CecTime;
    if ( fProgress && reserve > (abctime)pPars->nTimeLimit*CLOCKS_PER_SEC/10 )
        reserve = (abctime)pPars->nTimeLimit*CLOCKS_PER_SEC/10;
    return Deadline-reserve;
}

/**Function*************************************************************

  Synopsis    [Normalizes checked regions and records into root proposals.]

  Description [Preserves round-robin region order across both sources. A
  failed attempt retains earlier proposals but does not commit replacements.]

  SideEffects [Appends private destination gates and root proposals.]

  SeeAlso     []

***********************************************************************/
static int Acec2_NormalizeComponents( Gia_Man_t * pNew, Acec2_Man_t ** pMans,
                                     Vec_Int_t ** vMaps, Vec_Int_t ** vInfo,
                                     Vec_Int_t * vOrigColors, Vec_Int_t * vFrontier,
                                     Acec2_PolyCtx_t ** pActive, Acec2_Par_t * pPars,
                                     abctime Deadline, abctime WorkDeadline, abctime PolyDeadline,
                                     int nMaxObjs, Acec2_NormStats_t * pStats )
{
    Vec_Int_t * vRoots, * vBits, * vChosen, * vReportRoots;
    int side, tree, i, k, lit, flip, polyStatus, exprUsed, failed = 0;
    int fRecordsOnly = (pPars->nCecOptions & ACEC2_CEC_RECORDS_ONLY) != 0;
    for ( tree = 0; !failed && !fRecordsOnly &&
          ((pMans[0] && tree < Vec_WecSize(pMans[0]->vRoots)) || (pMans[1] && tree < Vec_WecSize(pMans[1]->vRoots))); tree++ )
        for ( side = 0; side < 2 && !failed; side++ )
        {
            if ( !pMans[side] || tree >= Vec_WecSize(pMans[side]->vRoots) ) continue;
            // A one-sided reconstruction also serves as the independent
            // normalization-versus-original check; retain that operation.
            if ( pMans[0] && pMans[1] && Acec2_RegionShared(pMans[side], tree, vMaps[side], vOrigColors) ) continue;
            if ( (pPars->nCecOptions & ACEC2_CEC_DEFER) && !Acec2_Stop(pPars, WorkDeadline) )
                Acec2_FindExpression(pMans[side], tree);
            vRoots = Vec_WecEntry(pMans[side]->vRoots, tree);
            if ( !Vec_IntEntry(pMans[side]->vPrefix, tree) && !pActive[side] && !Acec2_Word(pMans[side], tree) ) continue;
            vBits = Acec2_NormalizeRegion(pNew, pMans[side], tree, vMaps[side], pPars, Deadline, nMaxObjs, &flip, pActive[side], PolyDeadline, &polyStatus, &exprUsed, &vChosen, vFrontier);
            pStats->nPolyTried[side] += polyStatus != 0; pStats->nPolyDone[side] += polyStatus == 1;
            pStats->nExpressions[side] += exprUsed;
            if ( !vBits )
            {
                pStats->nSkipped++;
                if ( Acec2_Stop(pPars, Deadline) ) { failed = 1; break; }
                continue;
            }
            pStats->nRegions++;
            vReportRoots = vChosen ? vChosen : vRoots;
            for ( k = 0; k < Vec_IntSize(vReportRoots); k += 2 )
            {
                i = Vec_IntEntry(vReportRoots, k+1);
                if ( i >= Vec_IntSize(vBits) ) continue;
                lit = Vec_IntEntry(vReportRoots, k);
                if ( lit < 2 ) continue;
                Vec_IntPushThree(vInfo[side], Abc_Lit2Var(lit), Vec_IntEntry(vBits, i) ^ Abc_LitIsCompl(lit) ^ flip, tree);
                pStats->nRoots[side]++;
            }
            Vec_IntFree(vBits); Vec_IntFreeP(&vChosen);
        }
    for ( side = 0; side < 2 && !failed; side++ )
        if ( pMans[side] )
        {
            Acec2_Record_t * r; int index, useful;
            Vec_PtrForEachEntry(Acec2_Record_t *, pMans[side]->vRecords, r, index)
            {
                if ( (!fRecordsOnly && (r->Tree >= 0 || r->Counter >= 0)) || r->Prefix < 2 ) continue;
                useful = 0;
                for ( k = 0; k < Vec_IntSize(r->vOutputs); k += 2 )
                {
                    lit = Vec_IntEntry(r->vOutputs, k);
                    if ( lit < 2 || Vec_IntEntry(r->vOutputs, k+1) >= r->Prefix ) continue;
                    useful |= Vec_IntEntry(vOrigColors, Vec_IntEntry(vMaps[side], lit >> 1) >> 1) != 3;
                }
                if ( !useful ) continue;
                vBits = Acec2_NormalizeRecord(pNew, r, vMaps[side], pPars, Deadline, nMaxObjs, &flip);
                if ( !vBits )
                {
                    pStats->nSkipped++;
                    if ( Acec2_Stop(pPars, Deadline) ) { failed = 1; break; }
                    continue;
                }
                pStats->nRegions++;
                for ( k = 0; k < Vec_IntSize(r->vOutputs); k += 2 )
                {
                    i = Vec_IntEntry(r->vOutputs, k+1); lit = Vec_IntEntry(r->vOutputs, k);
                    if ( lit < 2 || i >= Vec_IntSize(vBits) ) continue;
                    Vec_IntPushThree(vInfo[side], lit >> 1,
                        Acec2_RecordApplyMask(pNew, r, vMaps[side], k/2, Vec_IntEntry(vBits, i) ^ flip) ^ (lit & 1), -1);
                    pStats->nRoots[side]++;
                    if ( Gia_ManObjNum(pNew) >= nMaxObjs || Acec2_Stop(pPars, Deadline) ) { failed = 1; break; }
                }
                Vec_IntFree(vBits);
                if ( failed ) break;
            }
        }
    return !failed;
}

/**Function*************************************************************

  Synopsis    [Selects proved root proposals at the common Boolean interface.]

  Description [Paired reconstruction retains only roots that share a checked
  destination. Existing common interfaces keep their original mappings.]

  SideEffects [Updates private replacement maps and summary counters.]

  SeeAlso     []

***********************************************************************/
static void Acec2_SelectRoots( Gia_Man_t * pNew, Acec2_Man_t ** pMans,
                               Vec_Int_t ** vMaps, Vec_Int_t ** vInfo, Vec_Int_t ** vReplaces,
                               Vec_Int_t * vOrigColors, Acec2_Par_t * pPars, Acec2_NormStats_t * pStats )
{
    Vec_Int_t * vColors, * vUseful, * vReplace;
    int side, tree, i, k, lit, fPaired = pPars->fPaired && pMans[0] && pMans[1];
    vColors = Vec_IntStart(Gia_ManObjNum(pNew));
    for ( side = 0; side < 2; side++ )
        for ( k = 0; k < Vec_IntSize(vInfo[side]); k += 3 )
        {
            lit = Abc_Lit2Var(Vec_IntEntry(vInfo[side], k+1));
            Vec_IntWriteEntry(vColors, lit, Vec_IntEntry(vColors, lit) | (1 << side));
        }
    vUseful = Vec_IntStart(Gia_ManObjNum(pNew));
    for ( side = 0; side < 2; side++ )
        for ( k = 0; k < Vec_IntSize(vInfo[side]); k += 3 )
        {
            i = Vec_IntEntry(vInfo[side], k); lit = Vec_IntEntry(vInfo[side], k+1);
            if ( Vec_IntEntry(vOrigColors, Abc_Lit2Var(Vec_IntEntry(vMaps[side], i))) != 3 )
                Vec_IntWriteEntry(vUseful, Abc_Lit2Var(lit), 1);
        }
    for ( side = 0; side < 2; side++ )
    {
        if ( pPars->fVerbose && pMans[side] )
        {
            Vec_Int_t * vCounts = Vec_IntStart(3*Vec_WecSize(pMans[side]->vTrees));
            int shown = 0;
            for ( k = 0; k < Vec_IntSize(vInfo[side]); k += 3 )
            {
                tree = Vec_IntEntry(vInfo[side], k+2); lit = Vec_IntEntry(vInfo[side], k+1);
                if ( tree < 0 ) continue;
                Vec_IntAddToEntry(vCounts, 3*tree, 1);
                if ( Vec_IntEntry(vColors, Abc_Lit2Var(lit)) != 3 ) continue;
                Vec_IntAddToEntry(vCounts, 3*tree+1, 1);
                i = Vec_IntEntry(vInfo[side], k);
                if ( Vec_IntEntry(vOrigColors, Abc_Lit2Var(Vec_IntEntry(vMaps[side], i))) != 3 )
                    Vec_IntAddToEntry(vCounts, 3*tree+2, 1);
            }
            for ( tree = 0; tree < Vec_WecSize(pMans[side]->vTrees) && shown < 16; tree++ )
            {
                i = Vec_IntSize(Vec_WecEntry(pMans[side]->vTrees, tree));
                if ( i < 16 ) continue;
                Abc_Print(1, "  Arithmetic side %d region %d: cells = %d, cut prefix = %d, roots = %d, shared = %d, new = %d.\n",
                    side, tree, i, Vec_IntEntry(pMans[side]->vPrefix, tree), Vec_IntEntry(vCounts, 3*tree),
                    Vec_IntEntry(vCounts, 3*tree+1), Vec_IntEntry(vCounts, 3*tree+2));
                shown++;
            }
            Vec_IntFree(vCounts);
        }
        vReplace = vReplaces[side];
        for ( k = 0; k < Vec_IntSize(vInfo[side]); k += 3 )
        {
            i = Vec_IntEntry(vInfo[side], k); lit = Vec_IntEntry(vInfo[side], k+1);
            // Preserve an already proved common Boolean interface.
            if ( Vec_IntEntry(vOrigColors, Vec_IntEntry(vMaps[side], i) >> 1) == 3 ) continue;
            if ( Vec_IntEntry(vColors, Abc_Lit2Var(lit)) == 3 )
            {
                pStats->nMatched[side]++;
                pStats->nNew[side] += Vec_IntEntry(vReplace, i) != lit && Vec_IntEntry(vMaps[side], i) != lit;
            }
            else if ( fPaired ) continue;
            if ( fPaired && !Vec_IntEntry(vUseful, Abc_Lit2Var(lit)) ) continue;
            Vec_IntWriteEntry(vReplace, i, lit);
            pStats->nSelected[side]++;
        }
    }
    Vec_IntFree(vColors); Vec_IntFree(vUseful);
}

/**Function*************************************************************

  Synopsis    [Reconstructs proved arithmetic boundaries and the Boolean miter.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Acec2_BuildMiterBudget( Gia_Man_t * pGia0, Gia_Man_t * pGia1,
                                  Acec2_Man_t * p0, Acec2_Man_t * p1,
                                  Acec2_Par_t * pPars, abctime Deadline,
                                  abctime CecTime, Acec2_NormStats_t * pStats )
{
    Acec2_Par_t Pars = *pPars;
    int fCancelled = 0, * pSavedCancel[2], SavedTier[2];
    Gia_Man_t * pNew = Gia_ManStart(1000), * pClean, * pGias[2];
    Acec2_Man_t * pMans[2], * pProfiles[2] = {NULL, NULL};
    Acec2_RecordMatch_t * pRecordMatch[2] = {Acec2_RecordMatchStart(), Acec2_RecordMatchStart()};
    Acec2_Align_t Align;
    Acec2_Templ_t * pTemplates = Acec2_TemplateStart();
    Acec2_PolyCtx_t * pPoly[2] = {NULL, NULL}, * pActive[2] = {NULL, NULL};
    Vec_Int_t * vFrontier = NULL;
    abctime PolyDeadline, MacroDeadline, OperandDeadline = 0, WorkDeadline = 0;
    abctime clkStart = Abc_Clock(), stepClock, profileBefore, ProfileQuantum = 0, ProfileDue = 0;
    Vec_Int_t * vMaps[2], * vOriginals[2], * vInfo[2], * vReplaces[2], * vOutputs = Vec_IntAlloc(2*Gia_ManCoNum(pGia0));
    Vec_Int_t * vNextOutputs = Vec_IntAlloc(2*Gia_ManCoNum(pGia0));
    Vec_Int_t * vProbeStates[2] = {Vec_IntAlloc(0), Vec_IntAlloc(0)};
    Vec_Int_t * vMap, * vReplace, * vColors, * vOrigColors;
    Gia_Obj_t * o;
    int side, i, lit, round, nNewBefore = 0, nMaxObjs, nOriginal, nMacroNew = 0, nMacroWords, fResume = 0, effortTier = 0, tierPasses = 0;
    int proofStatus, nRecordsBefore, nSourceBefore, nSourceAfter, nSweeps = 0, failed = 0, fProofError = 0;
    int fRecordsOnly = (pPars->nCecOptions & ACEC2_CEC_RECORDS_ONLY) != 0;
    int fProfileTried = 0, fCheapTried = 0, fProgress, nMaxPasses = Deadline ? ABC_INT_MAX : 128;
    ABC_INT64_T nProofsBefore = 0, nProofs;
    ABC_INT64_T limit = 8*((ABC_INT64_T)Gia_ManObjNum(pGia0)+Gia_ManObjNum(pGia1))+1000;
    memset(pStats, 0, sizeof(Acec2_NormStats_t));
    pStats->iLastStage = 1;
    memset(&Align, 0, sizeof(Align));
    if ( !Pars.pCancelled ) Pars.pCancelled = &fCancelled;
    pPars = &Pars;
    nMaxObjs = limit > 0x3FFFFFFF ? 0x3FFFFFFF : (int)limit;
    WorkDeadline = Acec2_ArithmeticDeadline(pPars, Deadline, CecTime, 0);
    pGias[0] = pGia0; pGias[1] = pGia1; pMans[0] = p0; pMans[1] = p1;
    if ( p0 && p1 )
    {
        ProfileQuantum = Deadline ? (WorkDeadline > clkStart ? (WorkDeadline-clkStart)/4 : 0) : CLOCKS_PER_SEC;
        ProfileDue = Deadline ? WorkDeadline-2*ProfileQuantum : clkStart+2*CLOCKS_PER_SEC;
    }
    for ( side = 0; side < 2; side++ )
    {
        pSavedCancel[side] = pMans[side] ? pMans[side]->Pars.pCancelled : NULL;
        SavedTier[side] = pMans[side] ? pMans[side]->Pars.nCecPolyLimit : 0;
    }
    for ( side = 0; side < 2; side++ )
        if ( pMans[side] ) pMans[side]->Pars.pCancelled = pPars->pCancelled;
    pNew->pName = Abc_UtilStrsav((char *)"acec2"); Gia_ManHashAlloc(pNew);
    for ( i = 0; i < Gia_ManCiNum(pGia0); i++ ) Gia_ManAppendCi(pNew);
    for ( side = 0; side < 2; side++ )
    {
        vMaps[side] = Vec_IntStart(Gia_ManObjNum(pGias[side]));
        vInfo[side] = Vec_IntAlloc(100);
        vReplaces[side] = Vec_IntStartFull(Gia_ManObjNum(pGias[side]));
        if ( pMans[side] )
            for ( i = 0; i < Vec_IntSize(pMans[side]->vConstants); i += 2 )
                Vec_IntWriteEntry(vReplaces[side], Vec_IntEntry(pMans[side]->vConstants, i), Vec_IntEntry(pMans[side]->vConstants, i+1));
        Gia_ManForEachCi(pGias[side], o, i) Vec_IntWriteEntry(vMaps[side], Gia_ObjId(pGias[side], o), 2*(i+1));
        Gia_ManForEachAnd(pGias[side], o, i)
        {
            if ( (i & 255) == 0 && Acec2_Stop(pPars, Deadline) ) { failed = 1; break; }
            // Retain the original structural form for certified template
            // matching; checked constants are applied on the first rebuild.
            // Preserve plain AND structure here. Recognizing a mux/XOR can
            // cross an arithmetic operand boundary and hide a template that
            // is present in the original netlist. Later reconstruction still
            // canonicalizes interfaces; vOriginals retains this exact copy.
            lit = Gia_ObjIsXor(o) || Gia_ObjIsMux(pGias[side], o) ?
                Acec2_MapNode(pGias[side], pNew, vMaps[side], o, i) :
                Gia_ManHashAnd(pNew,
                    Vec_IntEntry(vMaps[side], Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
                    Vec_IntEntry(vMaps[side], Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o));
            Vec_IntWriteEntry(vMaps[side], i, lit);
        }
    }
    for ( side = 0; side < 2; side++ ) vOriginals[side] = Vec_IntDup(vMaps[side]);
    if ( !failed )
        for ( side = 0; side < 2; side++ )
            Gia_ManForEachCo(pGias[side], o, i)
                Vec_IntPush(vOutputs, Vec_IntEntry(vMaps[side], Gia_ObjFaninId0p(pGias[side], o)) ^ Gia_ObjFaninC0(o));
    pStats->nBefore = Gia_ManAndNum(pNew); nOriginal = Gia_ManObjNum(pNew);
    // A plain comparison already has its complete shared Boolean miter.
    // Avoid rebuilding both sources through empty arithmetic replacement maps.
    if ( !p0 && !p1 )
    { pStats->TimeSetup = Abc_Clock()-clkStart; round = 0; goto miter_ready; }
    // Retain the initial shared Boolean interfaces when rebuilding plain
    // gates. Their identity is structural and needs no arithmetic hypothesis.
    vColors = Vec_IntStart(Gia_ManObjNum(pNew));
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(vMaps[side], lit, i)
            Vec_IntWriteEntry(vColors, lit >> 1, Vec_IntEntry(vColors, lit >> 1) | (1 << side));
    for ( side = 0; side < 2; side++ )
        Gia_ManForEachAnd(pGias[side], o, i)
        {
            lit = Vec_IntEntry(vMaps[side], i);
            if ( Vec_IntEntry(vColors, lit >> 1) == 3 ) Vec_IntWriteEntry(vReplaces[side], i, lit);
        }
    Vec_IntFree(vColors);
    pStats->TimeSetup = Abc_Clock()-clkStart;
    PolyDeadline = WorkDeadline;
    for ( round = 0; round < nMaxPasses && !failed; round++ )
    {
        pStats->nPasses = round+1;
        nProofs = (ABC_INT64_T)pStats->nMacroBits+pStats->nRecordBits+pStats->nTruthBits;
        fProgress = nProofs > nProofsBefore; nProofsBefore = nProofs;
        WorkDeadline = Acec2_ArithmeticDeadline(pPars, Deadline, CecTime+pStats->TimeCec, fProgress);
        if ( fProgress && Deadline && pPars->fVerbose )
            Abc_Print(1, "Productive arithmetic pass: remaining final CEC reserve = %.3f sec.\n", (double)(Deadline-WorkDeadline)/CLOCKS_PER_SEC);
        // Every productive pass gets a concrete Boolean proof attempt.
        // Deterministic effort bounds individual attempts. The caller's
        // deadline also reserves work for source profiling and final CEC.
        if ( round && WorkDeadline && Abc_Clock() >= WorkDeadline )
        {
            pStats->fArithmeticBudget = 1;
            if ( pPars->fVerbose ) Abc_Print(1, "Arithmetic budget reached; retaining the last complete reconstruction for CEC.\n");
            break;
        }
        if ( round && fCheapTried && !nMacroNew && pStats->nNew[0]+pStats->nNew[1] == nNewBefore &&
             !fProfileTried && ProfileQuantum && Abc_Clock() >= ProfileDue )
        {
            fProfileTried = 1;
            Acec2_ProfilePair(pGias, pMans, pProfiles, vOutputs, pPars, WorkDeadline, ProfileQuantum, pStats);
        }
        stepClock = Abc_Clock(); pStats->iPendingStep = 1;
        if ( Gia_ManObjNum(pNew) > nMaxObjs/2 )
        {
            // Cached columns refer to destination literals. Reindexing the
            // destination invalidates them even if the source cut is stable.
            for ( side = 0; side < 2; side++ )
            {
                Acec2_PolyRegionReuse(pPoly[side], &pStats->nPolyReused[side], &pStats->nPolyLimits[side]);
                Acec2_PolyRegionStop(pPoly[side]); pPoly[side] = NULL;
            }
            pClean = Acec2_CompactMiter(pNew, vMaps, vReplaces, vOutputs, nOriginal, pPars, Deadline);
            if ( !pClean ) { failed = 1; break; }
            Gia_ManStop(pNew); pNew = pClean;
            Vec_IntClear(vProbeStates[0]); Vec_IntClear(vProbeStates[1]);
        }
        PolyDeadline = !fProfileTried && ProfileQuantum && (!WorkDeadline || ProfileDue < WorkDeadline) ? ProfileDue : WorkDeadline;
        {
            // New records need not change the Boolean miter. Give each
            // deterministic effort tier two passes, then advance recorded
            // unfinished obligations even while other discovery continues.
            if ( tierPasses >= 2 && effortTier < 8 &&
                 (Acec2_NeedsEffort(p0, pPoly[0]) || Acec2_NeedsEffort(p1, pPoly[1])) )
            { effortTier++; tierPasses = 0; pStats->nEffortEscalations++; }
            tierPasses++;
            pPars->nCecPolyLimit = 1024 << effortTier;
            pStats->nEffortTier = effortTier;
            for ( side = 0; side < 2; side++ ) if ( pMans[side] ) pMans[side]->Pars.nCecPolyLimit = pPars->nCecPolyLimit;
        }
        nNewBefore = pStats->nNew[0]+pStats->nNew[1];
        nRecordsBefore = (p0 ? Vec_PtrSize(p0->vRecords) : 0)+(p1 ? Vec_PtrSize(p1->vRecords) : 0);
        nSourceBefore = 0;
        for ( side = 0; side < 2; side++ )
            if ( pMans[side] ) for ( i = 0; i < ACEC2_SOURCE_QUEUES; i++ ) nSourceBefore += pMans[side]->nSourceWork[i];
        nMacroNew = 0;
        Vec_IntClear(vNextOutputs); Vec_IntClear(vInfo[0]); Vec_IntClear(vInfo[1]);
        vOrigColors = Vec_IntStart(Gia_ManObjNum(pNew));
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(vMaps[side], lit, i)
                Vec_IntWriteEntry(vOrigColors, lit >> 1, Vec_IntEntry(vOrigColors, lit >> 1) | (1 << side));
        pActive[0] = pActive[1] = NULL;
        if ( !fResume && !failed && pPars->fAlgebra && (p0 || p1) ) vFrontier = Acec2_OperandFrontier(pNew, pMans, vMaps, PolyDeadline, round != 1);
        if ( vFrontier && p0 && p1 && !nMacroNew )
        {
            pStats->iLastStage = 2;
            nMacroNew = Acec2_MatchRecordsStep(pMans, vMaps, vReplaces, fRecordsOnly ? NULL : vFrontier, pPars, WorkDeadline, &nMacroWords, pRecordMatch[0]);
            if ( nMacroNew < 0 ) failed = fProofError = 1;
            else
            {
                pStats->nRecordBits += nMacroNew; pStats->nRecordWords += nMacroWords;
                if ( pPars->fVerbose && nMacroNew ) Abc_Print(1, "Checked component records: words = %d, new bit equalities = %d.\n", nMacroWords, nMacroNew);
            }
        }
        if ( !failed && !nMacroNew && pProfiles[0] && pProfiles[1] )
        {
            nMacroNew = Acec2_MatchRecordsStep(pProfiles, vMaps, vReplaces, NULL, pPars, WorkDeadline, &nMacroWords, pRecordMatch[1]);
            if ( nMacroNew < 0 ) failed = fProofError = 1;
            else
            {
                pStats->nRecordBits += nMacroNew; pStats->nRecordWords += nMacroWords;
                pStats->nProfileBits += nMacroNew; pStats->nProfileWords += nMacroWords;
            }
        }
        if ( !failed && nMacroNew )
        {
            // Certificate propagation may append and remap destination nodes.
            // Refresh both boundary indexes before using the cached source
            // identities with these new mappings.
            Vec_IntFill(vOrigColors, Gia_ManObjNum(pNew), 0);
            for ( side = 0; side < 2; side++ )
                Vec_IntForEachEntry(vMaps[side], lit, i)
                    Vec_IntWriteEntry(vOrigColors, lit >> 1, Vec_IntEntry(vOrigColors, lit >> 1) | (1 << side));
            Vec_IntFreeP(&vFrontier);
            vFrontier = Acec2_OperandFrontier(pNew, pMans, vMaps, PolyDeadline, round != 1);
        }
        // Local identities use the already proved frontier. Product proposals
        // must not continually preempt them: these rewrites can expose the
        // product boundaries or prove the surrounding additions directly.
        pStats->TimeRecords += Abc_Clock()-stepClock;
        stepClock = Abc_Clock(); pStats->iPendingStep = 2;
        pStats->iLastStage = 1;
        for ( side = 0; side < 2 && !failed && !fResume && !fRecordsOnly; side++ )
            if ( pMans[side] && vFrontier && !Acec2_Stop(pPars, PolyDeadline) )
            {
                if ( pPoly[side] )
                {
                    if ( Acec2_PolyRegionUpdate(pPoly[side], vMaps[side], vFrontier) ) pActive[side] = pPoly[side];
                }
                else pActive[side] = pPoly[side] = Acec2_PolyRegionStart(pMans[side], vMaps[side], vFrontier);
            }
        if ( !failed && !fResume )
            failed = !Acec2_NormalizeComponents(pNew, pMans, vMaps, vInfo, vOrigColors,
                vFrontier, pActive, pPars, Deadline, WorkDeadline, PolyDeadline, nMaxObjs, pStats);
        Vec_IntFreeP(&vFrontier);
        if ( !failed ) Acec2_SelectRoots(pNew, pMans, vMaps, vInfo, vReplaces, vOrigColors, pPars, pStats);
        pStats->TimeLocal += Abc_Clock()-stepClock;
        stepClock = Abc_Clock(); profileBefore = pStats->TimeProfile[0]+pStats->TimeProfile[1]; pStats->iPendingStep = 3;
        if ( !failed && (!nMacroNew || round == 0) && pPars->fAlgebra && p0 && p1 && (round == 0 || round >= 2) )
        {
            MacroDeadline = Deadline;
            if ( WorkDeadline && WorkDeadline < MacroDeadline ) MacroDeadline = WorkDeadline;
            // Finish a bounded productive match before spending the reserved
            // profiling share. Interrupting it can hide later independent
            // products from the same pass and change the next frontier.
            // Rebuild promptly after bounded exact cut proofs expose new
            // interfaces. More expensive word proposals see those interfaces
            // in the next pass, rather than repeating work on obsolete cones.
            vFrontier = Acec2_OperandFrontier(pNew, pMans, vMaps, MacroDeadline, 0);
            i = fRecordsOnly ? 0 : Acec2_MatchTruth(pNew, pMans, vMaps, vReplaces, vFrontier, pPars, MacroDeadline);
            Vec_IntFree(vFrontier); vFrontier = NULL;
            nMacroNew += i; pStats->nTruthBits += i; nMacroWords = 0;
            if ( !nMacroNew && round != 0 )
            {
                pStats->iLastStage = 2;
                Acec2_MatchMode_t mode = fResume ? ACEC2_MATCH_PENDING : ACEC2_MATCH_ALL;
                if ( !fResume && !fProfileTried )
                {
                    if ( !fRecordsOnly )
                    {
                        fCheapTried = 1;
                        nMacroNew = Acec2_MatchProducts(pNew, pMans, vMaps, vOriginals, vReplaces,
                            pPars, MacroDeadline, ACEC2_MATCH_CHEAP, &nMacroWords, pTemplates);
                        if ( nMacroNew < 0 ) failed = fProofError = 1;
                        else { pStats->nMacroWords += nMacroWords; pStats->nMacroBits += nMacroNew; }
                    }
                    if ( !failed && !nMacroNew && !Acec2_Stop(pPars, WorkDeadline) )
                    {
                        fProfileTried = 1; Acec2_ProfilePair(pGias, pMans, pProfiles, vOutputs, pPars, WorkDeadline, ProfileQuantum, pStats);
                        MacroDeadline = WorkDeadline;
                        nMacroNew = Acec2_MatchRecordsStep(pProfiles, vMaps, vReplaces, NULL, pPars, MacroDeadline, &nMacroWords, pRecordMatch[1]);
                        if ( nMacroNew < 0 ) failed = fProofError = 1;
                        else
                        {
                            pStats->nRecordBits += nMacroNew; pStats->nRecordWords += nMacroWords;
                            pStats->nProfileBits += nMacroNew; pStats->nProfileWords += nMacroWords;
                        }
                    }
                    mode = ACEC2_MATCH_BOUNDARY;
                }
                if ( !failed && !nMacroNew )
                {
                    nMacroNew = Acec2_MatchProducts(pNew, pMans, vMaps, vOriginals, vReplaces, pPars, MacroDeadline, mode, &nMacroWords, pTemplates);
                    if ( nMacroNew < 0 ) failed = fProofError = 1;
                    else { pStats->nMacroWords += nMacroWords; pStats->nMacroBits += nMacroNew; }
                }
            }
        }
        pStats->TimeMatch += Abc_Clock()-stepClock-(pStats->TimeProfile[0]+pStats->TimeProfile[1]-profileBefore);
        stepClock = Abc_Clock(); pStats->iPendingStep = 4;
        if ( !failed && pPars->fAlgebra && p0 && p1 )
        {
            int update = Acec2_AliasUpdate(pNew, vMaps, vReplaces, pPars, Deadline);
            if ( update < 0 ) { failed = 1; fProofError = update == -2; }
        }
        for ( side = 0; side < 2 && !failed; side++ )
        {
            vReplace = vReplaces[side];
            vMap = Vec_IntStart(Gia_ManObjNum(pGias[side]));
            Gia_ManForEachCi(pGias[side], o, i) Vec_IntWriteEntry(vMap, Gia_ObjId(pGias[side], o), 2*(i+1));
            Gia_ManForEachAnd(pGias[side], o, i)
            {
                if ( (i & 255) == 0 && Acec2_Stop(pPars, Deadline) ) { failed = 1; break; }
                lit = Vec_IntEntry(vReplace, i);
                if ( lit < 0 )
                {
                    // Recognizing a mux/XOR may bypass its two internal ANDs.
                    // Preserve a proved cut on either of those nodes instead.
                    if ( !Gia_ObjIsXor(o) && !Gia_ObjIsMux(pGias[side], o) &&
                         (round >= 2 || Vec_IntEntry(vReplace, Gia_ObjFaninId0(o, i)) >= 0 || Vec_IntEntry(vReplace, Gia_ObjFaninId1(o, i)) >= 0) )
                        lit = Gia_ManHashAnd(pNew,
                            Vec_IntEntry(vMap, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
                            Vec_IntEntry(vMap, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o));
                    else lit = Acec2_MapNode(pGias[side], pNew, vMap, o, i);
                }
                Vec_IntWriteEntry(vMap, i, lit);
            }
            Gia_ManForEachCo(pGias[side], o, i)
                Vec_IntPush(vNextOutputs, Vec_IntEntry(vMap, Gia_ObjFaninId0p(pGias[side], o)) ^ Gia_ObjFaninC0(o));
            Vec_IntFree(vMaps[side]); vMaps[side] = vMap;
        }
        if ( !failed ) ABC_SWAP(Vec_Int_t *, vOutputs, vNextOutputs);
        Vec_IntFree(vOrigColors);
        pStats->TimeRebuild += Abc_Clock()-stepClock;
        if ( failed ) break;
        if ( pPars->fVerbose && (p0 || p1) )
            Abc_Print(1, "Normalization pass %d: %d newly shared roots.\n", round+1, pStats->nNew[0]+pStats->nNew[1]-nNewBefore);
        for ( i = 0; i < Vec_IntSize(vOutputs)/2; i++ )
            if ( Vec_IntEntry(vOutputs, i) != Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs)/2+i) ) break;
        if ( i == Vec_IntSize(vOutputs)/2 ) break;
        if ( !Vec_IntEqual(vOutputs, vNextOutputs) ||
             (p0 && p1 && Vec_PtrSize(p0->vRecords)+Vec_PtrSize(p1->vRecords) > nRecordsBefore) )
        {
            pStats->iLastStage = 3;
            proofStatus = Acec2_ProveOutputs(pNew, vOutputs, vMaps, vReplaces, pPars, WorkDeadline, &nMacroNew, 0, vProbeStates[0], pStats);
            if ( proofStatus < 0 ) { failed = fProofError = 1; break; }
            if ( proofStatus == 1 ) { pStats->fContextProved = 1; break; }
        }
        if ( pStats->nNew[0]+pStats->nNew[1] == nNewBefore && !nMacroNew )
        {
            nSourceAfter = 0;
            for ( side = 0; side < 2; side++ )
                if ( pMans[side] ) for ( i = 0; i < ACEC2_SOURCE_QUEUES; i++ ) nSourceAfter += pMans[side]->nSourceWork[i];
            // Independent source proofs can add records before their cut
            // signals correspond. Advancing a bounded source queue is also
            // progress: one unsuccessful proposal must not hide its next
            // candidate. Cache hits consume no work unit. The overall round
            // bound and reserved ordinary-CEC time remain in force.
            if ( p0 && p1 &&
                 (Vec_PtrSize(p0->vRecords)+Vec_PtrSize(p1->vRecords) > nRecordsBefore || nSourceAfter > nSourceBefore) )
            { fResume = 0; continue; }
            if ( round < 2 && pPars->fAlgebra && p0 && p1 ) continue;
            if ( failed || round == nMaxPasses-1 ) break;
            // Keep inexpensive output checks on productive passes. Broaden
            // sweeping when arithmetic stalls, retaining its proved internal
            // correspondences for the next arithmetic pass.
            if ( pPars->fSweep && p0 && p1 )
            {
                proofStatus = Acec2_ProveOutputs(pNew, vOutputs, vMaps, vReplaces, pPars, WorkDeadline, &nMacroNew, 1+Abc_MinInt(effortTier, 3), vProbeStates[1], pStats);
                if ( proofStatus < 0 ) { failed = fProofError = 1; break; }
                if ( proofStatus == 1 ) { pStats->fContextProved = 1; break; }
                if ( nMacroNew )
                {
                    Acec2_TemplateNewProofs(pTemplates);
                    fResume = 0;
                    continue;
                }
            }
            if ( !fRecordsOnly && pPars->fSweep && p0 && p1 && nSweeps < 3 )
            {
                Acec2_AlignMode_t mode = (Acec2_AlignMode_t)nSweeps++;
                // A small first sweep can prove no pair even when the later
                // operand-focused sweep can make progress. Its conflict or
                // iteration limit must not cancel the remaining searches.
                if ( Acec2_AlignOperands(pNew, vMaps, vReplaces, vOutputs, pPars, WorkDeadline, nMaxObjs, mode, pMans, vOriginals, &Align) && nSweeps == 3 && Align.nShared )
                    nSweeps = 2;
                if ( Align.nChanged ) Acec2_TemplateNewProofs(pTemplates);
                if ( Align.nChanged )
                {
                    proofStatus = Acec2_ProveOutputs(pNew, vOutputs, vMaps, vReplaces, pPars, WorkDeadline, &nMacroNew, 0, vProbeStates[0], pStats);
                    if ( proofStatus < 0 ) { failed = fProofError = 1; break; }
                    if ( proofStatus == 1 ) { pStats->fContextProved = 1; break; }
                }
                PolyDeadline = WorkDeadline;
                fResume = 0;
                continue;
            }
            // A full pass may exhaust its slice before reaching the shifted
            // templates. Give that stage its own pass before declaring a
            // fixed point; subsequent passes follow its recorded cursor.
            if ( !fRecordsOnly && pPars->fAlgebra && p0 && p1 && (!fResume || Acec2_TemplatePending(pTemplates, 0)) ) { fResume = 1; continue; }
            if ( !fRecordsOnly && pPars->fSweep && pPars->fAlgebra && p0 && p1 )
            {
                Gia_Man_t * pTry;
                if ( !OperandDeadline )
                    OperandDeadline = Deadline;
                if ( WorkDeadline && WorkDeadline < OperandDeadline ) OperandDeadline = WorkDeadline;
                if ( Acec2_Stop(pPars, OperandDeadline) ) break;
                // Give completed arithmetic matching and ordinary CEC a
                // chance before broadening Boolean operand proposals.
                pTry = Gia_ManDup(pNew);
                for ( i = 0; i < Vec_IntSize(vOutputs)/2; i++ )
                {
                    Gia_ManAppendCo(pTry, Vec_IntEntry(vOutputs, i));
                    Gia_ManAppendCo(pTry, Vec_IntEntry(vOutputs, Vec_IntSize(vOutputs)/2+i));
                }
                pClean = Gia_ManCleanup(pTry); Gia_ManStop(pTry);
                i = Acec2_ProveContext(pClean, pPars, OperandDeadline); Gia_ManStop(pClean);
                if ( i == 1 ) { pStats->fContextProved = 1; break; }
                i = Acec2_AlignOperands(pNew, vMaps, vReplaces, vOutputs, pPars, OperandDeadline, nMaxObjs, ACEC2_ALIGN_ALL_CUTS, pMans, vOriginals, &Align);
                if ( Align.nChanged ) Acec2_TemplateNewProofs(pTemplates);
                if ( Align.nChanged )
                {
                    proofStatus = Acec2_ProveOutputs(pNew, vOutputs, vMaps, vReplaces, pPars, WorkDeadline, &nMacroNew, 0, vProbeStates[0], pStats);
                    if ( proofStatus < 0 ) { failed = fProofError = 1; break; }
                    if ( proofStatus == 1 ) { pStats->fContextProved = 1; break; }
                }
                // A remapped same-side cone is not necessarily a new operand
                // correspondence. Do not let it repeatedly postpone the
                // concrete proof or restart the first group indefinitely.
                if ( !Align.nShared )
                    i |= Acec2_AlignOperands(pNew, vMaps, vReplaces, vOutputs, pPars, OperandDeadline, nMaxObjs, ACEC2_ALIGN_ALL_CONES, pMans, vOriginals, &Align);
                if ( Align.nChanged )
                {
                    proofStatus = Acec2_ProveOutputs(pNew, vOutputs, vMaps, vReplaces, pPars, WorkDeadline, &nMacroNew, 0, vProbeStates[0], pStats);
                    if ( proofStatus < 0 ) { failed = fProofError = 1; break; }
                    if ( proofStatus == 1 ) { pStats->fContextProved = 1; break; }
                }
                if ( i )
                {
                    if ( Align.nChanged ) Acec2_TemplateNewProofs(pTemplates);
                    nSweeps = 1; fResume = 0;
                    PolyDeadline = WorkDeadline;
                    continue;
                }
            }
            // A structural fixed point at a low proof budget is not an
            // exhausted arithmetic search. Retry unfinished obligations at
            // the next deterministic tier before handing the miter to CEC.
            if ( pPars->fAlgebra && p0 && p1 && effortTier < 8 &&
                 (Acec2_NeedsEffort(p0, pPoly[0]) || Acec2_NeedsEffort(p1, pPoly[1])) )
            {
                effortTier++; tierPasses = 0; pStats->nEffortEscalations++; fResume = 0;
                if ( pPars->fVerbose ) Abc_Print(1, "Arithmetic fixed point: increasing term budget to %d.\n", 1024 << effortTier);
                continue;
            }
            break;
        }
        if ( nMacroNew || pStats->nNew[0]+pStats->nNew[1] != nNewBefore ) Acec2_TemplateNewProofs(pTemplates);
        // A newly proved arithmetic boundary can make downstream operand
        // logic easy. Permit another focused/concrete alignment cycle even
        // when the initial three sweep attempts have already been used.
        if ( nSweeps >= 3 ) nSweeps = 1;
        fResume = 0;
    }
miter_ready:
    pStats->fPassLimit = round == nMaxPasses;
    pStats->TimeTotal = Abc_Clock()-clkStart;
    if ( WorkDeadline && Abc_Clock() >= WorkDeadline ) pStats->fArithmeticBudget = 1;
    if ( failed && !fProofError && !Acec2_Stop(pPars, Deadline) && Vec_IntSize(vOutputs) == 2*Gia_ManCoNum(pGia0) )
    {
        if ( pPars->fVerbose ) Abc_Print(1, "Reconstruction effort limit: retaining the last completed miter.\n");
        failed = 0;
    }
    if ( Acec2_Stop(pPars, Deadline) ) failed = 1;
    if ( !failed )
        for ( i = 0; i < Gia_ManCoNum(pGia0); i++ )
        {
            Gia_ManAppendCo(pNew, Vec_IntEntry(vOutputs, i));
            Gia_ManAppendCo(pNew, Vec_IntEntry(vOutputs, Gia_ManCoNum(pGia0)+i));
        }
    for ( side = 0; side < 2; side++ )
    {
        Acec2_PolyRegionReuse(pPoly[side], &pStats->nPolyReused[side], &pStats->nPolyLimits[side]);
        Acec2_PolyRegionStop(pPoly[side]);
        Acec2_Free(pProfiles[side]);
        Acec2_RecordMatchStop(pRecordMatch[side]);
        Vec_IntFree(vMaps[side]); Vec_IntFree(vOriginals[side]); Vec_IntFree(vInfo[side]); Vec_IntFree(vReplaces[side]);
    }
    for ( side = 0; side < 2; side++ )
        if ( pMans[side] )
        {
            pMans[side]->Pars.pCancelled = pSavedCancel[side];
            pMans[side]->Pars.nCecPolyLimit = SavedTier[side];
        }
    Vec_IntFree(vOutputs); Vec_IntFree(vNextOutputs); Vec_WrdFreeP(&Align.vPatterns); Acec2_TemplateStop(pTemplates);
    Vec_IntFree(vProbeStates[0]); Vec_IntFree(vProbeStates[1]);
    Gia_ManHashStop(pNew);
    if ( failed ) { Gia_ManStop(pNew); return NULL; }
    pClean = Gia_ManCleanup(pNew); Gia_ManStop(pNew);
    pStats->nAfter = Gia_ManAndNum(pClean);
    return pClean;
}

/**Function*************************************************************

  Synopsis    [Reconstructs a miter when no earlier ordinary-CEC probe was run.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Acec2_BuildMiterEx( Gia_Man_t * pGia0, Gia_Man_t * pGia1,
                              Acec2_Man_t * p0, Acec2_Man_t * p1,
                              Acec2_Par_t * pPars, abctime Deadline, Acec2_NormStats_t * pStats )
{
    return Acec2_BuildMiterBudget(pGia0, pGia1, p0, p1, pPars, Deadline, 0, pStats);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
