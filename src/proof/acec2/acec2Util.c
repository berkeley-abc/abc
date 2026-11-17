/**CFile****************************************************************

  FileName    [acec2Util.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Private graph, simulation, and reporting helpers.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 15, 2026.]

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

  Synopsis    [Compresses a private union forest and its optional potentials.]

  Description [Plain parents are object IDs; Delta and Flip are optional.
  Literal parents encode phase in bit zero, with -1 or a self literal at
  roots. The literal mode returns a phased representative. Other modes
  return an object ID and update the caller's weight and phase arrays.]

  SideEffects [Changes only the supplied private forest.]

  SeeAlso     []

***********************************************************************/
int Acec2_UnionFind( int * Parent, int * Delta, int * Flip, int x, int fLiteral )
{
    int root = x, d = 0, f = 0, next, oldD, oldF, result;
    while ( Parent[root] >= 0 && (Parent[root] >> fLiteral) != root )
    {
        d += Delta ? Delta[root] : 0;
        f ^= fLiteral ? Parent[root] & 1 : Flip ? Flip[root] : 0;
        root = Parent[root] >> fLiteral;
    }
    result = fLiteral ? 2*root+f : root;
    while ( Parent[x] >= 0 && (Parent[x] >> fLiteral) != x )
    {
        next = Parent[x] >> fLiteral; oldD = Delta ? Delta[x] : 0;
        oldF = fLiteral ? Parent[x] & 1 : Flip ? Flip[x] : 0;
        Parent[x] = fLiteral ? 2*root+f : root;
        if ( Delta ) Delta[x] = d;
        if ( Flip ) Flip[x] = f;
        d -= oldD; f ^= oldF; x = next;
    }
    return result;
}

/**Function*************************************************************

  Synopsis    [Copies a mapped gate without looking beyond its direct fanins.]

  Description [Cut boundaries remain free inputs even inside an AND-based
  XOR or mux pattern. Native XOR and mux nodes are expanded by hashing.]

  SideEffects [Appends to the private destination only.]

  SeeAlso     []

***********************************************************************/
int Acec2_CopyGate( Gia_Man_t * src, Gia_Man_t * dst, Vec_Int_t * map, int id )
{
    Gia_Obj_t * o = Gia_ManObj(src, id);
    int a = Vec_IntEntry(map, Gia_ObjFaninId0(o, id)) ^ Gia_ObjFaninC0(o);
    int b = Vec_IntEntry(map, Gia_ObjFaninId1(o, id)) ^ Gia_ObjFaninC1(o);
    if ( Gia_ObjIsMux(src, o) )
    {
        int c = Vec_IntEntry(map, Gia_ObjFaninId2(src, id)) ^ Gia_ObjFaninC2(src, o);
        return Gia_ManHashMux(dst, c, b, a);
    }
    return Gia_ObjIsXor(o) ? Gia_ManHashXor(dst, a, b) : Gia_ManHashAnd(dst, a, b);
}

/**Function*************************************************************

  Synopsis    [Copies the requested cone, stopping at already mapped nodes.]

  Description [The map contains destination literals or -1 for unknown
  nodes. Every required source input must be mapped by the caller. Roots
  are source literals. An optional topological order restricts traversal to
  an already indexed cut domain. The caller owns hashing and output creation.]

  SideEffects [Updates a private map and destination; leaves the source intact.]

  SeeAlso     []

***********************************************************************/
int Acec2_CopyCone( Gia_Man_t * src, Gia_Man_t * dst, Vec_Int_t * map, Vec_Int_t * roots, Vec_Int_t * order,
                     Acec2_Par_t * pars, abctime deadline )
{
    Vec_Bit_t * needed = Vec_BitStart(Gia_ManObjNum(src));
    Gia_Obj_t * o; int i, id, lit, k, success = 0, count = order ? Vec_IntSize(order) : Gia_ManObjNum(src);
    if ( pars && Acec2_Stop(pars, deadline) ) goto finish;
    Vec_IntForEachEntry(roots, lit, i) if ( lit >= 0 ) Acec2_BitWrite(needed, lit >> 1, 1);
    for ( i = count-1; i >= 0; i-- )
    {
        id = order ? Vec_IntEntry(order, i) : i;
        if ( pars && !(id & 1023) && Acec2_Stop(pars, deadline) ) goto finish;
        if ( !Vec_BitEntry(needed, id) || Vec_IntEntry(map, id) >= 0 ) continue;
        o = Gia_ManObj(src, id);
        if ( !Gia_ObjIsAnd(o) ) goto finish;
        for ( k = 0; k < Gia_ObjFaninNum(src, o); k++ )
            Acec2_BitWrite(needed, k == 2 ? Gia_ObjFaninId2(src, id) : k ? Gia_ObjFaninId1(o, id) : Gia_ObjFaninId0(o, id), 1);
    }
    for ( i = 0; i < count; i++ )
    {
        id = order ? Vec_IntEntry(order, i) : i;
        if ( pars && !(id & 1023) && Acec2_Stop(pars, deadline) ) goto finish;
        if ( Vec_BitEntry(needed, id) && Vec_IntEntry(map, id) < 0 )
            Vec_IntWriteEntry(map, id, Acec2_CopyGate(src, dst, map, id));
    }
    success = 1;
finish:
    Vec_BitFree(needed); return success;
}

/**Function*************************************************************

  Synopsis    [Writes integer list contents for text or JSON reports.]

  Description [The caller supplies delimiters outside the list.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_WriteList( FILE * f, Vec_Int_t * values, int Step, int Limit )
{
    int i, n = values ? Vec_IntSize(values)/Step : 0;
    for ( i = 0; i < n && (!Limit || i < Limit); i++ )
        fprintf(f, "%s%d", i ? "," : "", Vec_IntEntry(values, Step*i));
    if ( Limit && n > Limit ) fprintf(f, ",...,%d", Vec_IntEntry(values, Step*(n-1)));
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
