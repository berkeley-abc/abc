/**CFile****************************************************************

  FileName    [acec2Bdd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Bounded exact BDD proofs of extracted component pairs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 12, 2026.]

  Revision    [$Id$]

***********************************************************************/

#include "acec2Int.h"
#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Proves equal component outputs using a private BDD manager.]

  Description [The suggested CI order affects resources only. Canonical BDD
  equality is the proof. Unused CIs are excluded and fanout counts release
  intermediate functions. Without CUDD, this optional proof returns unknown.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ProveBddLimit( Gia_Man_t ** g, Vec_Int_t * vOrder, Acec2_Par_t * pPars, abctime Deadline,
                        Abc_Cex_t ** ppCex, int nLimit, int * pfLimited )
{
    if ( ppCex ) *ppCex = NULL;
    if ( pfLimited ) *pfLimited = 0;
    if ( !g || !g[0] || !g[1] || nLimit < 1 || Gia_ManCiNum(g[0]) != Gia_ManCiNum(g[1]) ||
         Gia_ManCoNum(g[0]) != Gia_ManCoNum(g[1]) || Acec2_Stop(pPars, Deadline) ) return -1;
#ifdef ABC_USE_CUDD
    DdManager * dd = NULL;
    DdNode * f, * a, * b;
    Vec_Ptr_t * vNodes[2] = {NULL, NULL};
    Vec_Int_t * vRefs[2] = {NULL, NULL};
    Vec_Int_t * vActive = Vec_IntStart(Gia_ManCiNum(g[0])), * vRanks = Vec_IntStartFull(Gia_ManCiNum(g[0]));
    Gia_Obj_t * o, * pFanin;
    int side, i, j, id, nActive = 0, rank = 0, result = -1, headroom, nBuilt = 0, limited = 0;
    for ( side = 0; side < 2; side++ )
    {
        vNodes[side] = Vec_PtrStart(Gia_ManObjNum(g[side])); vRefs[side] = Vec_IntStart(Gia_ManObjNum(g[side]));
        Gia_ManForEachObj1(g[side], o, i)
        {
            if ( !Gia_ObjIsAnd(o) && !Gia_ObjIsCo(o) ) continue;
            // Extracted components are plain AIGs.
            if ( Gia_ObjIsXor(o) || Gia_ObjIsMux(g[side], o) ) goto finish;
            for ( j = 0; j < (Gia_ObjIsCo(o) ? 1 : 2); j++ )
            {
                pFanin = j ? Gia_ObjFanin1(o) : Gia_ObjFanin0(o); id = Gia_ObjId(g[side], pFanin);
                Vec_IntAddToEntry(vRefs[side], id, 1);
                if ( Gia_ObjIsCi(pFanin) ) Vec_IntWriteEntry(vActive, Gia_ObjCioId(pFanin), 1);
            }
        }
    }
    Vec_IntForEachEntry(vActive, id, i) nActive += id;
    if ( nActive > 64 ) { limited = 1; goto finish; }
    if ( vOrder ) Vec_IntForEachEntry(vOrder, id, i)
        if ( id >= 0 && id < Vec_IntSize(vRanks) && Vec_IntEntry(vActive, id) && Vec_IntEntry(vRanks, id) < 0 )
            Vec_IntWriteEntry(vRanks, id, rank++);
    Vec_IntForEachEntry(vActive, id, i)
        if ( id && Vec_IntEntry(vRanks, i) < 0 ) Vec_IntWriteEntry(vRanks, i, rank++);
    dd = Cudd_Init(nActive, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    if ( !dd ) goto finish;
    Cudd_AutodynDisable(dd); Cudd_SetMaxLive(dd, nLimit); dd->TimeStop = Deadline;
    for ( side = 0; side < 2; side++ )
    {
        f = Cudd_ReadLogicZero(dd); Cudd_Ref(f); Vec_PtrWriteEntry(vNodes[side], 0, f);
        Gia_ManForEachCi(g[side], o, i)
        {
            if ( Vec_IntEntry(vRanks, i) < 0 ) continue;
            f = Cudd_bddIthVar(dd, Vec_IntEntry(vRanks, i)); Cudd_Ref(f);
            Vec_PtrWriteEntry(vNodes[side], Gia_ObjId(g[side], o), f);
        }
        Gia_ManForEachObj1(g[side], o, i)
        {
            if ( !Gia_ObjIsAnd(o) && !Gia_ObjIsCo(o) ) continue;
            if ( Acec2_Stop(pPars, Deadline) ) goto finish;
            a = Cudd_NotCond((DdNode *)Vec_PtrEntry(vNodes[side], Gia_ObjFaninId0(o, i)), Gia_ObjFaninC0(o));
            if ( Gia_ObjIsCo(o) ) f = a;
            else
            {
                b = Cudd_NotCond((DdNode *)Vec_PtrEntry(vNodes[side], Gia_ObjFaninId1(o, i)), Gia_ObjFaninC1(o));
                headroom = nLimit-(int)(dd->keys-dd->dead+dd->keysZ-dd->deadZ);
                if ( headroom < 0 ) { limited = 1; goto finish; }
                f = Cudd_bddAndLimit(dd, a, b, headroom);
                if ( !f ) { limited = Cudd_ReadErrorCode(dd) == CUDD_TOO_MANY_NODES; goto finish; }
            }
            Cudd_Ref(f); Vec_PtrWriteEntry(vNodes[side], i, f);
            nBuilt++;
            if ( dd->keys-dd->dead+dd->keysZ-dd->deadZ > (unsigned)nLimit ) { limited = 1; goto finish; }
            for ( j = 0; j < (Gia_ObjIsCo(o) ? 1 : 2); j++ )
            {
                id = j ? Gia_ObjFaninId1(o, i) : Gia_ObjFaninId0(o, i);
                Vec_IntAddToEntry(vRefs[side], id, -1);
                if ( Vec_IntEntry(vRefs[side], id) ) continue;
                f = (DdNode *)Vec_PtrEntry(vNodes[side], id); Cudd_RecursiveDeref(dd, f); Vec_PtrWriteEntry(vNodes[side], id, NULL);
            }
        }
    }
    result = 1;
    for ( i = 0; i < Gia_ManCoNum(g[0]); i++ )
    {
        a = (DdNode *)Vec_PtrEntry(vNodes[0], Gia_ObjId(g[0], Gia_ManCo(g[0], i)));
        b = (DdNode *)Vec_PtrEntry(vNodes[1], Gia_ObjId(g[1], Gia_ManCo(g[1], i)));
        if ( a == b ) continue;
        result = 0;
        if ( ppCex )
        {
            Vec_Int_t * vCube = Vec_IntStart(nActive);
            DdNode * at, * ae, * bt, * be;
            int ia, ib;
            while ( !Cudd_IsConstant(a) || !Cudd_IsConstant(b) )
            {
                ia = Cudd_IsConstant(a) ? ABC_INT_MAX : (int)Cudd_Regular(a)->index;
                ib = Cudd_IsConstant(b) ? ABC_INT_MAX : (int)Cudd_Regular(b)->index;
                id = Abc_MinInt(ia, ib);
                at = ia == id ? Cudd_NotCond(Cudd_T(Cudd_Regular(a)), Cudd_IsComplement(a)) : a;
                ae = ia == id ? Cudd_NotCond(Cudd_E(Cudd_Regular(a)), Cudd_IsComplement(a)) : a;
                bt = ib == id ? Cudd_NotCond(Cudd_T(Cudd_Regular(b)), Cudd_IsComplement(b)) : b;
                be = ib == id ? Cudd_NotCond(Cudd_E(Cudd_Regular(b)), Cudd_IsComplement(b)) : b;
                if ( at != bt ) { Vec_IntWriteEntry(vCube, id, 1); a = at; b = bt; }
                else { a = ae; b = be; }
            }
            assert(a != b);
            *ppCex = Abc_CexAlloc(0, Gia_ManCiNum(g[0]), 1); (*ppCex)->iPo = i;
            Vec_IntForEachEntry(vRanks, id, j) if ( id >= 0 && Vec_IntEntry(vCube, id) ) Abc_InfoSetBit((*ppCex)->pData, j);
            Vec_IntFree(vCube);
        }
        break;
    }
finish:
    if ( pfLimited && !Acec2_Stop(pPars, Deadline) ) *pfLimited = limited;
    if ( pPars->fVerbose && dd ) Abc_Print(1, "BDD proof: active inputs = %d, visited gates/outputs = %d, live nodes = %u, result = %d.\n",
        nActive, nBuilt, (unsigned)(dd->keys-dd->dead+dd->keysZ-dd->deadZ), result);
    for ( side = 0; side < 2; side++ )
    {
        if ( dd && vNodes[side] ) Vec_PtrForEachEntry(DdNode *, vNodes[side], f, i) if ( f ) Cudd_RecursiveDeref(dd, f);
        Vec_PtrFreeP(&vNodes[side]); Vec_IntFreeP(&vRefs[side]);
    }
    if ( dd ) Cudd_Quit(dd);
    Vec_IntFree(vActive); Vec_IntFree(vRanks);
    return result;
#else
    (void)g; (void)vOrder; (void)pPars; (void)Deadline;
    return -1;
#endif
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
