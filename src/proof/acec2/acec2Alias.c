/**CFile****************************************************************

  FileName    [acec2Alias.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Propagates completed equality proofs through private maps.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 13, 2026.]

  Revision    [$Id$]

  Description [Replacement entries must already have exact proofs. Their
  transitive closure preserves equalities when several components select
  different representatives. Rehashing propagates those equalities through
  retained proof logic as well as the original source cones.]

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

  Synopsis    [Joins one checked phased equality, detecting contradictions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_AliasJoin( Vec_Int_t * vParents, Vec_Bit_t * vUsed, int a, int b )
{
    a = Acec2_LitFind(vParents, a); b = Acec2_LitFind(vParents, b);
    if ( (a >> 1) == (b >> 1) )
    {
        if ( a == b ) return 0;
        Abc_Print(-1, "&acec2: internal proof error: contradictory proved equalities for literals %d and %d.\n", a, b);
        return -2;
    }
    if ( (a >> 1) > (b >> 1) ) ABC_SWAP(int, a, b);
    Vec_IntWriteEntry(vParents, b >> 1, a ^ (b & 1));
    Acec2_BitWrite(vUsed, a >> 1, 1);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Applies proved classes and returns the number of changed maps.]

  Description [A completed pass commits all maps together. A limit or
  cancellation returns -1 without changing any caller-owned map. An
  inconsistent proved class reports an internal proof error and returns -2.
  Gates appended during an incomplete pass are harmless unreferenced logic
  in the private destination. Count actual map changes, not proposed links,
  so repeated certificates do not postpone the remaining proof stages.]

  SideEffects [Updates private source/replacement maps after completion.]

  SeeAlso     []

***********************************************************************/
int Acec2_AliasApply( Gia_Man_t * g, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                      Vec_Int_t * vOutputs, Vec_Int_t * vPairs, Acec2_Par_t * pPars, abctime Deadline )
{
    Vec_Int_t * vParents = NULL, * vMap = NULL;
    Vec_Bit_t * vNeeded = NULL, * vUsed = NULL;
    Gia_Obj_t * o;
    ABC_INT64_T nMaxObjs;
    int nObjs, side, i, a, lit, root, added, changed = 0, joins = 0, result = -1;
    if ( !g || !vMaps || !vReplaces || !pPars || !Vec_IntSize(&g->vHTable) ) return -1;
    nObjs = Gia_ManObjNum(g);
    if ( vPairs && (Vec_IntSize(vPairs) & 1) ) return -1;
    if ( vPairs ) Vec_IntForEachEntry(vPairs, lit, i) if ( lit < 0 || (lit >> 1) >= nObjs ) return -1;
    if ( vOutputs ) Vec_IntForEachEntry(vOutputs, lit, i) if ( lit < 0 || (lit >> 1) >= nObjs ) return -1;
    for ( side = 0; side < 2; side++ )
    {
        if ( !vMaps[side] || !vReplaces[side] || Vec_IntSize(vMaps[side]) != Vec_IntSize(vReplaces[side]) ) return -1;
        Vec_IntForEachEntry(vMaps[side], lit, i)
        {
            a = Vec_IntEntry(vReplaces[side], i);
            if ( lit < 0 || (lit >> 1) >= nObjs || a < -1 || (a >= 0 && (a >> 1) >= nObjs) ) return -1;
        }
    }
    nMaxObjs = 8*((ABC_INT64_T)Vec_IntSize(vMaps[0])+Vec_IntSize(vMaps[1]))+1000;
    vParents = Vec_IntAlloc(nObjs); vMap = Vec_IntAlloc(nObjs);
    vNeeded = Vec_BitStart(nObjs); vUsed = Vec_BitStart(nObjs);
    for ( i = 0; i < nObjs; i++ ) Vec_IntPush(vParents, 2*i);
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(vReplaces[side], lit, i)
        {
            if ( (i & 1023) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
            if ( lit < 0 ) continue;
            added = Acec2_AliasJoin(vParents, vUsed, Vec_IntEntry(vMaps[side], i), lit);
            if ( added < 0 ) { result = added; goto finish; }
            joins += added;
        }
    if ( vPairs )
        for ( i = 0; i < Vec_IntSize(vPairs); i += 2 )
        {
            if ( (i & 1023) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
            added = Acec2_AliasJoin(vParents, vUsed, Vec_IntEntry(vPairs, i), Vec_IntEntry(vPairs, i+1));
            if ( added < 0 ) { result = added; goto finish; }
            joins += added;
        }
    for ( i = 0; i < nObjs; i++ )
    {
        lit = Vec_IntEntry(vParents, i); root = Vec_IntEntry(vParents, lit >> 1) ^ (lit & 1);
        Vec_IntWriteEntry(vParents, i, root);
        if ( Vec_BitEntry(vUsed, i) ) Acec2_BitWrite(vUsed, root >> 1, 1);
    }
    for ( side = 0; side < 2; side++ )
    {
        Vec_IntForEachEntry(vMaps[side], lit, i) Acec2_BitWrite(vNeeded, lit >> 1, 1);
        Vec_IntForEachEntry(vReplaces[side], lit, i) if ( lit >= 0 ) Acec2_BitWrite(vNeeded, lit >> 1, 1);
    }
    if ( vOutputs ) Vec_IntForEachEntry(vOutputs, lit, i) Acec2_BitWrite(vNeeded, lit >> 1, 1);
    for ( i = nObjs-1; i > 0; i-- )
    {
        if ( (i & 1023) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
        if ( !Vec_BitEntry(vNeeded, i) ) continue;
        root = Vec_IntEntry(vParents, i);
        if ( (root >> 1) != i ) { Acec2_BitWrite(vNeeded, root >> 1, 1); continue; }
        o = Gia_ManObj(g, i);
        if ( !Gia_ObjIsAnd(o) ) continue;
        Acec2_BitWrite(vNeeded, Gia_ObjFaninId0(o, i), 1);
        Acec2_BitWrite(vNeeded, Gia_ObjFaninId1(o, i), 1);
        if ( Gia_ObjIsMux(g, o) ) Acec2_BitWrite(vNeeded, Gia_ObjFaninId2(g, i), 1);
    }
    Vec_IntPush(vMap, 0);
    for ( i = 1; i < nObjs; i++ )
    {
        if ( (i & 1023) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
        if ( (ABC_INT64_T)Gia_ManObjNum(g) > nMaxObjs ) goto finish;
        root = Vec_IntEntry(vParents, i); o = Gia_ManObj(g, i);
        if ( !Vec_BitEntry(vNeeded, i) ) lit = 2*i;
        else if ( (root >> 1) != i ) lit = Vec_IntEntry(vMap, root >> 1) ^ (root & 1);
        else if ( !Gia_ObjIsAnd(o) ) lit = 2*i;
        else lit = Acec2_MapNode(g, g, vMap, o, i);
        Vec_IntPush(vMap, lit);
    }
    if ( Acec2_Stop(pPars, Deadline) ) goto finish;
    // No stop check inside this final commit: readers see either the old
    // maps or the completed pass, including pinned representatives.
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(vMaps[side], lit, i)
        {
            root = Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1); changed += root != lit;
            if ( root != lit || Vec_BitEntry(vUsed, Vec_IntEntry(vParents, lit >> 1) >> 1) )
                Vec_IntWriteEntry(vReplaces[side], i, root);
            else if ( Vec_IntEntry(vReplaces[side], i) >= 0 )
            {
                a = Vec_IntEntry(vReplaces[side], i);
                Vec_IntWriteEntry(vReplaces[side], i, Vec_IntEntry(vMap, a >> 1) ^ (a & 1));
            }
            Vec_IntWriteEntry(vMaps[side], i, root);
        }
    if ( vOutputs )
        Vec_IntForEachEntry(vOutputs, lit, i)
            Vec_IntWriteEntry(vOutputs, i, Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1));
    result = changed;
finish:
    if ( pPars->fVerbose && (joins || changed) )
        Abc_Print(1, "Proved alias propagation: classes = %d, changed source mappings = %d%s.\n", joins, changed, result < 0 ? ", incomplete" : "");
    Vec_IntFreeP(&vParents); Vec_IntFreeP(&vMap);
    if ( vNeeded ) Vec_BitFree(vNeeded);
    if ( vUsed ) Vec_BitFree(vUsed);
    return result;
}

/**Function*************************************************************

  Synopsis    [Propagates arithmetic replacements without extra Boolean pairs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_AliasUpdate( Gia_Man_t * g, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                       Acec2_Par_t * pPars, abctime Deadline )
{
    return Acec2_AliasApply(g, vMaps, vReplaces, NULL, NULL, pPars, Deadline);
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
