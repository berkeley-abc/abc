/**HFile****************************************************************

  FileName    [lmsXor.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation.]

  Synopsis    [Unit AND/XOR metrics over ordinary three-AND XOR patterns.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 5, 2026.]

  Revision    [$Id: lmsXor.h,v 1.00 2026/10/05 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__bool__lms__lmsXor_h
#define ABC__bool__lms__lmsXor_h

#include "aig/gia/gia.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// Recognize XOR or XNOR, regardless of input/output phase. Returned inputs
// are object IDs; their phases do not affect depth or gate count.
static inline int Lms_AigXorInputs( int nVars, const int * pFans, int Id, int * pa, int * pb )
{
    int a, b, c, d, e, f;
    if ( Id <= nVars ) return 0;
    a = pFans[2*(Id-nVars-1)]; b = pFans[2*(Id-nVars-1)+1];
    if ( !(a&1) || !(b&1) || (a>>1) <= nVars || (b>>1) <= nVars ) return 0;
    c = pFans[2*((a>>1)-nVars-1)]; d = pFans[2*((a>>1)-nVars-1)+1];
    e = pFans[2*((b>>1)-nVars-1)]; f = pFans[2*((b>>1)-nVars-1)+1];
    if ( (c>>1) == (d>>1) || !((c == (e^1) && d == (f^1)) || (c == (f^1) && d == (e^1))) ) return 0;
    *pa = c>>1; *pb = d>>1;
    return 1;
}
// Bounded generated graphs use IDs 0, inputs, then at most 128 AND nodes.
// Traverse the logical AND/XOR cover, not the physical AND cone. If a hidden
// product is also used separately, that separate use still pays for its AND.
static inline int Lms_AigXorMetrics( int nVars, const int * pFans, int nAnds,
    int Root, int * pDepths )
{
    int Depth[145], i, Id, a, b, Area = 0;
    assert(nVars <= 16 && nAnds <= 128 && (Root>>1) < nVars+1+nAnds);
    memset(Depth, -1, sizeof(Depth)); Depth[Root>>1] = 0;
    for ( i = nAnds-1; i >= 0; --i )
    {
        Id = nVars+1+i;
        if ( Depth[Id] < 0 ) continue;
        ++Area;
        if ( !Lms_AigXorInputs(nVars, pFans, Id, &a, &b) )
        { a = pFans[2*i]>>1; b = pFans[2*i+1]>>1; }
        Depth[a] = Abc_MaxInt(Depth[a], Depth[Id]+1);
        Depth[b] = Abc_MaxInt(Depth[b], Depth[Id]+1);
    }
    if ( pDepths ) for ( i = 0; i < nVars; ++i ) pDepths[i] = Depth[i+1];
    return Area;
}
static inline void Lms_GiaMetricFans( Gia_Obj_t * pObj, int fXor, Gia_Obj_t ** pa, Gia_Obj_t ** pb )
{
    if ( fXor && Gia_ObjRecognizeExor(pObj, pa, pb) )
    { *pa = Gia_Regular(*pa); *pb = Gia_Regular(*pb); }
    else { *pa = Gia_ObjFanin0(pObj); *pb = Gia_ObjFanin1(pObj); }
}

ABC_NAMESPACE_HEADER_END
#endif
