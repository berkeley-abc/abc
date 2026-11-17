/**CFile****************************************************************

  FileName    [acec2Tree.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Weighted region construction and read-only reporting.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 11, 2026.]

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

  Synopsis    [Initializes analysis and verification defaults.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_SetDefaultParams( Acec2_Par_t * p )
{
    memset( p, 0, sizeof(Acec2_Par_t) );
    p->nCuts = 16;
    p->nBTLimit = 1000;
    p->nMaxWidth = 4096;
    p->fAlgebra = 1;
    p->fNormalize = 1;
    p->fPaired = 1;
    p->fSweep = 1;
    p->nAnalysisLevel = 3;
    p->nCecOptions = ACEC2_CEC_SINGLE_USE | ACEC2_CEC_DEFER;
}

/**Function*************************************************************

  Synopsis    [Joins components only when their arithmetic weights agree.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_WeightUnion( int * Parent, int * Delta, int * Flip, int * Size, int a, int b, int d, int f )
{
    int ra = Acec2_WeightFind(Parent, Delta, Flip, a), rb = Acec2_WeightFind(Parent, Delta, Flip, b);
    int diff = d + Delta[a] - Delta[b], phase = f ^ Flip[a] ^ Flip[b];
    if ( ra == rb ) return diff == 0 && phase == 0;
    if ( Size[ra] < Size[rb] )
    {
        Parent[ra] = rb; Delta[ra] = -diff; Flip[ra] = phase; Size[rb] += Size[ra];
    }
    else
    {
        Parent[rb] = ra; Delta[rb] = diff; Flip[rb] = phase; Size[ra] += Size[rb];
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Orders cell depth evaluation by the earliest output.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_OrderCompare( const void * a, const void * b )
{
    const int * x = (const int *)a, * y = (const int *)b;
    if ( x[0] != y[0] ) return x[0] < y[0] ? -1 : 1;
    return x[1] < y[1] ? -1 : x[1] > y[1];
}

/**Function*************************************************************

  Synopsis    [Profiles parity DAGs using canonical XOR2 cuts.]

  Description [All exact alternative cuts remain available in the JSON report.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_BuildXors( Acec2_Man_t * p )
{
    int n = Gia_ManObjNum(p->pGia), i, j, k, id, leaf, root, old, group, size;
    Vec_Int_t * vNodes, * vLeaves, * vSinks;
    Vec_Int_t * vBest = Vec_IntStartFull(n);
    int * Parent = ABC_ALLOC(int, n), * Delta = ABC_CALLOC(int, n), * Flip = ABC_CALLOC(int, n);
    int * Size = ABC_ALLOC(int, n), * Depth = ABC_CALLOC(int, n);
    for ( i = 0; i < n; i++ ) { Parent[i] = i; Size[i] = 1; }
    for ( i = 0; i < Vec_IntSize(p->vXors); i += 5 )
    {
        id = Abc_Lit2Var(Vec_IntEntry(p->vXors, i+4));
        if ( !Depth[id] )
        {
            Depth[id] = -1;
        }
        if ( Vec_IntEntry(p->vXors, i) != 2 ) continue;
        old = Vec_IntEntry(vBest, id);
        if ( old < 0 || Vec_IntEntry(p->vXors, i+1) < Vec_IntEntry(p->vXors, old+1) ||
             (Vec_IntEntry(p->vXors, i+1) == Vec_IntEntry(p->vXors, old+1) && Vec_IntEntry(p->vXors, i+2) < Vec_IntEntry(p->vXors, old+2)) )
            Vec_IntWriteEntry(vBest, id, i);
    }
    for ( id = 0; id < n; id++ )
    {
        i = Vec_IntEntry(vBest, id);
        if ( i < 0 ) { Depth[id] = 0; continue; }
        Depth[id] = 1;
        for ( k = 0; k < 2; k++ )
        {
            leaf = Vec_IntEntry(p->vXors, i+1+k);
            if ( Vec_IntEntry(vBest, leaf) < 0 ) continue;
            Acec2_WeightUnion(Parent, Delta, Flip, Size, leaf, id, 0, 0);
            Depth[id] = Abc_MaxInt(Depth[id], Depth[leaf]+1);
        }
        p->nXorDepth = Abc_MaxInt(p->nXorDepth, Depth[id]);
    }
    for ( i = 0; i < n; i++ )
        if ( Depth[i] )
        {
            root = Acec2_WeightFind( Parent, Delta, Flip, i );
            if ( root == i ) p->nXorGroups++;
        }
    // Preserve the established XOR2 statistics above. The persistent networks
    // also include nodes for which only a three-input parity cut is available.
    p->vXorBest = vBest; p->vXorGroup = Vec_IntStartFull(n);
    for ( i = 0; i < n; i++ ) { Parent[i] = i; Size[i] = 1; Delta[i] = Flip[i] = Depth[i] = 0; }
    for ( id = 0; id < n; id++ )
    {
        if ( Vec_IntEntry(vBest, id) >= 0 ) continue;
        old = -1;
        for ( j = Vec_IntEntry(p->vXorFirst, id); j >= 0; j = Vec_IntEntry(p->vXorNext, j) )
        {
            i = 5*j;
            if ( old >= 0 )
            {
                for ( k = 1; k < 4; k++ )
                    if ( Vec_IntEntry(p->vXors, i+k) != Vec_IntEntry(p->vXors, old+k) ) break;
                if ( k == 4 || Vec_IntEntry(p->vXors, i+k) > Vec_IntEntry(p->vXors, old+k) ) continue;
            }
            old = i;
        }
        Vec_IntWriteEntry(vBest, id, old);
    }
    for ( id = 0; id < n; id++ )
    {
        i = Vec_IntEntry(vBest, id);
        if ( i < 0 ) continue;
        Depth[id] = 1; size = Vec_IntEntry(p->vXors, i);
        for ( k = 0; k < size; k++ )
        {
            leaf = Vec_IntEntry(p->vXors, i+1+k);
            if ( Vec_IntEntry(vBest, leaf) < 0 ) continue;
            Acec2_WeightUnion(Parent, Delta, Flip, Size, leaf, id, 0, 0);
            Depth[id] = Abc_MaxInt(Depth[id], Depth[leaf]+1);
        }
    }
    for ( id = 0; id < n; id++ )
    {
        if ( Vec_IntEntry(vBest, id) < 0 ) continue;
        root = Acec2_WeightFind(Parent, Delta, Flip, id);
        group = Vec_IntEntry(p->vXorGroup, root);
        if ( group < 0 )
        {
            group = Vec_WecSize(p->vXorNetworks);
            Vec_WecPushLevel(p->vXorNetworks); Vec_WecPushLevel(p->vXorLeaves); Vec_WecPushLevel(p->vXorSinks);
            Vec_IntPush(p->vXorDepths, 0); Vec_IntWriteEntry(p->vXorGroup, root, group);
        }
        Vec_IntWriteEntry(p->vXorGroup, id, group); Vec_WecPush(p->vXorNetworks, group, id);
        if ( Depth[id] > Vec_IntEntry(p->vXorDepths, group) ) Vec_IntWriteEntry(p->vXorDepths, group, Depth[id]);
    }
    memset(Size, 0, (size_t)n*sizeof(int));
    Vec_WecForEachLevel(p->vXorNetworks, vNodes, group)
    {
        vLeaves = Vec_WecEntry(p->vXorLeaves, group); vSinks = Vec_WecEntry(p->vXorSinks, group);
        Vec_IntForEachEntry(vNodes, id, j)
        {
            i = Vec_IntEntry(vBest, id); size = Vec_IntEntry(p->vXors, i);
            for ( k = 0; k < size; k++ )
            {
                leaf = Vec_IntEntry(p->vXors, i+1+k);
                if ( Vec_IntEntry(vBest, leaf) < 0 ) Vec_IntPush(vLeaves, leaf);
                else Size[leaf]++;
            }
        }
        Vec_IntUniqify(vLeaves);
        Vec_IntForEachEntry(vNodes, id, j) if ( !Size[id] ) Vec_IntPush(vSinks, id);
    }
    ABC_FREE( Parent ); ABC_FREE( Delta ); ABC_FREE( Flip ); ABC_FREE( Size ); ABC_FREE( Depth );
}

/**Function*************************************************************

  Synopsis    [Records one boundary of the selected arithmetic interpretation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_BoundaryPush( Acec2_Man_t * p, int Tree, int Direction,
                               int Lit, int Rank, int Reason, int Cell )
{
    Vec_Int_t * v = Vec_WecEntry(p->vBoundaries, Tree);
    Vec_IntPushThree(v, Direction, Lit, Rank); Vec_IntPushTwo(v, Reason, Cell);
    p->nBoundaries[Reason]++;
}

/**Function*************************************************************

  Synopsis    [Builds weighted regions and records uncancelled interfaces.]

  Description [Boundary reasons describe the selected interpretation. They
  neither assert that unrecognized logic is non-arithmetic nor authorize a
  replacement. Every weighted boundary still comes from checked identities.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_BuildTrees( Acec2_Man_t * p )
{
    int n = Vec_PtrSize(p->vCells), i, k, e, root, tree, phase, rank, width, good, prefix, rootsBelow, dest, fanin;
    int target, producer, diff, valid, reason, id;
    int * Parent = ABC_ALLOC(int, n), * Delta = ABC_CALLOC(int, n), * Flip = ABC_CALLOC(int, n);
    int * Size = ABC_ALLOC(int, n), * Map = ABC_ALLOC(int, n), * Min = ABC_ALLOC(int, n);
    Vec_Int_t * vUses = Vec_IntStart(2*n), * vOrder = Vec_IntAlloc(2*n);
    Vec_Wec_t * vConsumers = Vec_WecStart(2*n);
    Vec_Int_t * vStamp = Vec_IntStartFull(n), * vDelta = Vec_IntStart(n), * vFlip = Vec_IntStart(n);
    Vec_Int_t * vHaBalance = Vec_IntStart(n), * vLeafBalance = Vec_IntStart(n), * vOutside = Vec_IntStart(2*n);
    Vec_Int_t * vReasons = Vec_IntStartFull(3*n);
    Vec_Bit_t * vAlternative = Vec_BitStart(Gia_ManObjNum(p->pGia));
    Vec_Bit_t * vCo = Vec_BitStart(Gia_ManObjNum(p->pGia));
    Vec_Bit_t * vUsed = Vec_BitStart(Abc_MaxInt(1, 2*n));
    Vec_Int_t * vTree, * vRoots, * vHeights = Vec_IntAlloc(32);
    Acec2_Cell_t * c, * prod;
    Gia_Obj_t * o;
    Vec_PtrForEachEntry(Acec2_Cell_t *, p->vAlternatives, c, i)
        for ( k = 0; k < 2; k++ ) Acec2_BitWrite(vAlternative, c->Out[k] >> 1, 1);
    Gia_ManForEachCo(p->pGia, o, i) Acec2_BitWrite(vCo, Gia_ObjFaninId0p(p->pGia, o), 1);
    for ( i = 0; i < n; i++ ) { Parent[i] = i; Size[i] = 1; Map[i] = -1; Min[i] = 0; }
    Vec_IntFill( p->vEdges, 3*n, -1 );
    for ( i = 0; i < n; i++ )
    {
        c = Acec2_Cell(p, i);
        for ( k = 0; k < c->nIns; k++ )
        {
            e = Vec_IntEntry(p->vOwner, Abc_Lit2Var(c->In[k]));
            if ( e >= 0 )
            {
                Vec_IntAddToEntry(vUses, e, 1); Vec_WecPush(vConsumers, e, 3*i+k);
            }
        }
    }
    for ( i = 0; i < n; i++ )
    {
        c = Acec2_Cell(p, i);
        for ( k = 0; k < c->nIns; k++ )
        {
            e = Vec_IntEntry(p->vOwner, Abc_Lit2Var(c->In[k]));
            if ( e < 0 || Vec_IntEntry(vUses, e) != 1 ) continue;
            prod = Acec2_Cell(p, e/2);
            phase = Abc_LitIsCompl(c->In[k]) ^ Abc_LitIsCompl(prod->Out[e&1]);
            if ( !Acec2_WeightUnion(Parent, Delta, Flip, Size, e/2, i, e&1, phase) )
            {
                p->nRejected++;
                Vec_IntWriteEntry(vReasons, 3*i+k, ACEC2_BOUNDARY_CONFLICT);
                continue;
            }
            if ( !Vec_BitEntry(vUsed, e) )
            {
                Vec_IntWriteEntry( p->vEdges, 3*i+k, e );
                Acec2_BitWrite( vUsed, e, 1 );
            }
        }
    }
    // Establish single-use columns first. A shared signal can be reused at
    // several weights (for example, in a constant product). Join its users
    // only if the entire group admits one consistent weight and phase;
    // otherwise retain the producer boundary for every interpretation.
    for ( e = 0; e < 2*n; e++ )
    {
        if ( Vec_IntEntry(vUses, e) < 2 ) continue;
        if ( p->fSingleUse )
        {
            Vec_IntForEachEntry(Vec_WecEntry(vConsumers, e), target, k)
                Vec_IntWriteEntry(vReasons, target, ACEC2_BOUNDARY_SHARED_POLICY);
            continue;
        }
        producer = e/2; prod = Acec2_Cell(p, producer);
        root = Acec2_WeightFind(Parent, Delta, Flip, producer);
        Vec_IntWriteEntry(vStamp, root, e); Vec_IntWriteEntry(vDelta, root, 0); Vec_IntWriteEntry(vFlip, root, 0);
        valid = 1;
        Vec_IntForEachEntry(Vec_WecEntry(vConsumers, e), target, k)
        {
            i = target/3; c = Acec2_Cell(p, i);
            root = Acec2_WeightFind(Parent, Delta, Flip, i);
            diff = (e & 1) + Delta[producer] - Delta[i];
            phase = ((c->In[target%3] ^ prod->Out[e&1]) & 1) ^ Flip[producer] ^ Flip[i];
            if ( Vec_IntEntry(vStamp, root) == e &&
                 (Vec_IntEntry(vDelta, root) != diff || Vec_IntEntry(vFlip, root) != phase) )
            { valid = 0; break; }
            Vec_IntWriteEntry(vStamp, root, e); Vec_IntWriteEntry(vDelta, root, diff); Vec_IntWriteEntry(vFlip, root, phase);
        }
        if ( !valid )
        {
            p->nRejected += Vec_IntEntry(vUses, e);
            Vec_IntForEachEntry(Vec_WecEntry(vConsumers, e), target, k)
                Vec_IntWriteEntry(vReasons, target, ACEC2_BOUNDARY_CONFLICT);
            continue;
        }
        Vec_IntForEachEntry(Vec_WecEntry(vConsumers, e), target, k)
        {
            i = target/3; c = Acec2_Cell(p, i);
            phase = (c->In[target%3] ^ prod->Out[e&1]) & 1;
            valid = Acec2_WeightUnion(Parent, Delta, Flip, Size, producer, i, e&1, phase);
            assert(valid);
            if ( !Vec_BitEntry(vUsed, e) )
            {
                Vec_IntWriteEntry(p->vEdges, target, e); Acec2_BitWrite(vUsed, e, 1);
            }
            else Vec_IntWriteEntry(vReasons, target, ACEC2_BOUNDARY_REUSE);
        }
    }
    for ( i = 0; i < n; i++ )
    {
        root = Acec2_WeightFind( Parent, Delta, Flip, i );
        Min[root] = Abc_MinInt( Min[root], Delta[i] );
        c = Acec2_Cell(p, i);
        if ( c->nIns == 2 ) Vec_IntAddToEntry(vHaBalance, root, Flip[i] ? -1 : 1);
        for ( k = 0; k < c->nIns; k++ )
            if ( Vec_IntEntry(p->vEdges, 3*i+k) < 0 )
                Vec_IntAddToEntry(vLeafBalance, root, (Abc_LitIsCompl(c->In[k]) ^ Flip[i]) ? -1 : 1);
    }
    for ( i = 0; i < n; i++ )
    {
        root = Parent[i];
        if ( Map[root] < 0 )
        {
            Map[root] = Vec_WecSize(p->vTrees);
            Vec_WecPushLevel( p->vTrees ); Vec_WecPushLevel( p->vRoots );
            Vec_WecPushLevel( p->vLeaves ); Vec_WecPushLevel( p->vBias );
            Vec_WecPushLevel( p->vTaps );
            Vec_WecPushLevel( p->vBoundaries );
        }
        c = Acec2_Cell(p, i);
        phase = Vec_IntEntry(vHaBalance, root) < 0 ||
            (Vec_IntEntry(vHaBalance, root) == 0 && Vec_IntEntry(vLeafBalance, root) < 0);
        c->Tree = Map[root]; c->Rank = Delta[i]-Min[root]; c->Phase = Flip[i] ^ phase;
        Vec_WecPush( p->vTrees, c->Tree, i );
        Vec_IntPushTwo( vOrder, Abc_MinInt(Abc_Lit2Var(c->Out[0]), Abc_Lit2Var(c->Out[1])), i );
        if ( c->nIns == 2 && c->Phase ) Vec_WecPush(p->vBias, c->Tree, c->Rank);
        for ( k = 0; k < c->nIns; k++ )
            if ( Vec_IntEntry(p->vEdges, 3*i+k) < 0 )
            {
                Vec_IntPushTwo( Vec_WecEntry(p->vLeaves, c->Tree), c->In[k] ^ c->Phase, c->Rank );
                id = c->In[k] >> 1; reason = Vec_IntEntry(vReasons, 3*i+k);
                if ( reason < 0 )
                    reason = !id ? ACEC2_BOUNDARY_CONSTANT : Gia_ObjIsCi(Gia_ManObj(p->pGia, id)) ? ACEC2_BOUNDARY_INPUT :
                        Vec_BitEntry(vAlternative, id) ? ACEC2_BOUNDARY_ALTERNATIVE :
                        Vec_IntEntry(p->vXorFirst, id) >= 0 ? ACEC2_BOUNDARY_PARITY : ACEC2_BOUNDARY_LOGIC;
                if ( reason == ACEC2_BOUNDARY_LOGIC )
                {
                    Gia_Obj_t * obj = Gia_ManObj(p->pGia, id);
                    if ( Gia_ObjIsAnd(obj) && !Gia_ObjIsMux(p->pGia, obj) && !Gia_ObjIsXor(obj) && !Gia_ObjIsBuf(obj) &&
                         Gia_ObjIsCi(Gia_ObjFanin0(obj)) && Gia_ObjIsCi(Gia_ObjFanin1(obj)) ) reason = ACEC2_BOUNDARY_BIT_PRODUCT;
                }
                Acec2_BoundaryPush(p, c->Tree, 0, c->In[k] ^ c->Phase, c->Rank, reason, i);
            }
        for ( k = 0; k < 2; k++ )
            if ( !Vec_BitEntry(vUsed, 2*i+k) )
            {
                Vec_IntPushTwo( Vec_WecEntry(p->vRoots, c->Tree), c->Out[k] ^ c->Phase, c->Rank+k );
                reason = Vec_IntEntry(vUses, 2*i+k) ? ACEC2_BOUNDARY_OPEN_CONSUMER :
                    Vec_BitEntry(vCo, c->Out[k] >> 1) ? ACEC2_BOUNDARY_OUTPUT : ACEC2_BOUNDARY_NO_CONSUMER;
                Acec2_BoundaryPush(p, c->Tree, 1, c->Out[k] ^ c->Phase, c->Rank+k, reason, i);
            }
    }
    if ( n > 1 ) qsort( Vec_IntArray(vOrder), n, 2*sizeof(int), Acec2_OrderCompare );
    for ( i = 0; i < n; i++ )
    {
        e = Vec_IntEntry(vOrder, 2*i+1); c = Acec2_Cell(p, e); c->Depth = 1;
        for ( k = 0; k < c->nIns; k++ )
            if ( Vec_IntEntry(p->vEdges, 3*e+k) >= 0 )
                c->Depth = Abc_MaxInt(c->Depth, Acec2_Cell(p, Vec_IntEntry(p->vEdges, 3*e+k)/2)->Depth+1);
    }
    Vec_WecForEachLevel( p->vTrees, vTree, tree )
    {
        vRoots = Vec_WecEntry(p->vRoots, tree);
        width = 0;
        for ( k = 1; k < Vec_IntSize(vRoots); k += 2 ) width = Abc_MaxInt(width, Vec_IntEntry(vRoots, k)+1);
        Vec_IntFill( vHeights, width, 0 );
        for ( k = 1; k < Vec_IntSize(vRoots); k += 2 )
        {
            rank = Vec_IntEntry(vRoots, k);
            Vec_IntAddToEntry( vHeights, rank, 1 );
        }
        prefix = rootsBelow = 0;
        while ( prefix < width && prefix < p->Pars.nMaxWidth && Vec_IntEntry(vHeights, prefix) <= 1 )
            rootsBelow += Vec_IntEntry(vHeights, prefix++);
        if ( !rootsBelow ) prefix = 0;
        good = prefix == width && width > 0;
        Vec_IntPush( p->vWidths, width );
        Vec_IntPush( p->vNormal, good );
        Vec_IntPush( p->vPrefix, prefix );
        p->nNormal += good;
        p->nMulti += Vec_IntSize(vTree) > 1;
        p->nLargest = Abc_MaxInt(p->nLargest, Vec_IntSize(vTree));
        if ( good )
        {
            p->nNormalCells += Vec_IntSize(vTree);
            p->nLargestNormal = Abc_MaxInt(p->nLargestNormal, Vec_IntSize(vTree));
        }
        else if ( prefix )
        {
            p->nPrefix++;
            Vec_IntForEachEntry(vTree, e, k) p->nPrefixCells += Acec2_Cell(p, e)->Rank < prefix;
        }
    }
    // Algebraically cancelled signals can still have observable external taps.
    Gia_ManForEachObj1(p->pGia, o, i)
    {
        dest = Vec_IntEntry(p->vNodeCell, i);
        for ( k = 0; k < Gia_ObjFaninNum(p->pGia, o); k++ )
        {
            fanin = k == 2 ? Gia_ObjFaninId2(p->pGia, i) : k ? Gia_ObjFaninId1(o, i) : Gia_ObjFaninId0(o, i);
            e = Vec_IntEntry(p->vOwner, fanin);
            if ( e < 0 || !Vec_BitEntry(vUsed, e) ) continue;
            if ( dest < 0 || Acec2_Cell(p, dest)->Tree != Acec2_Cell(p, e/2)->Tree ) Vec_IntAddToEntry(vOutside, e, 1);
        }
    }
    for ( e = 0; e < 2*n; e++ )
        if ( Vec_IntEntry(vOutside, e) )
        {
            c = Acec2_Cell(p, e/2);
            Vec_IntPushThree(Vec_WecEntry(p->vTaps, c->Tree), c->Out[e&1] ^ c->Phase, c->Rank+(e&1), Vec_IntEntry(vOutside, e));
            p->nTaps++;
            Acec2_BoundaryPush(p, c->Tree, 2, c->Out[e&1] ^ c->Phase, c->Rank+(e&1), ACEC2_BOUNDARY_TAP, e/2);
        }
    Vec_IntFree(vReasons); Vec_BitFree(vAlternative); Vec_BitFree(vCo);
    Vec_WecFree(vConsumers); Vec_IntFree(vStamp); Vec_IntFree(vDelta); Vec_IntFree(vFlip);
    Vec_IntFree( vUses ); Vec_IntFree( vOrder ); Vec_IntFree( vHeights ); Vec_BitFree( vUsed );
    Vec_IntFree(vHaBalance); Vec_IntFree(vLeafBalance); Vec_IntFree(vOutside);
    ABC_FREE( Parent ); ABC_FREE( Delta ); ABC_FREE( Flip ); ABC_FREE( Size ); ABC_FREE( Map ); ABC_FREE( Min );
}

/**Function*************************************************************

  Synopsis    [Runs analysis with an absolute deadline shared by the caller.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Man_t * Acec2_AnalyzeInt( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline, int fProfile, Vec_Bit_t * vFocus, int fFocusedProfile )
{
    Acec2_Man_t * p;
    abctime clk = Abc_Clock(), stage;
    if ( !pGia || pPars->nCuts < 1 || pPars->nCuts > 64 || pPars->nMaxWidth < 1 || pPars->nTimeLimit < 0 ||
         pPars->nAnalysisLevel < 0 || pPars->nAnalysisLevel > 3 ) return NULL;
    p = ABC_CALLOC( Acec2_Man_t, 1 );
    p->pGia = pGia; p->Pars = *pPars; p->Deadline = Deadline;
    p->vFocus = vFocus ? Vec_BitDup(vFocus) : NULL;
    p->nCarryProbeLimit = Abc_MaxInt(128, Abc_MinInt(4096, Gia_ManAndNum(pGia)/16));
    p->nCarryConflictLimit = Abc_MaxInt(20000, p->nCarryProbeLimit*156);
    // Standalone profiling requests its selected recognition level.
    // CEC scheduling and the active proof tier do not restrict that request.
    if ( fProfile == 1 ) { p->Pars.nCecOptions = 0; p->Pars.nCecPolyLimit = 0; }
    if ( vFocus && !fFocusedProfile ) p->Pars.nCecPolyLimit = pPars->nCecPolyLimit > 0 ? pPars->nCecPolyLimit : 1024;
    p->fFast = (vFocus != NULL && !fFocusedProfile) || fProfile < 0 || (fProfile == 0 && (pPars->nCecOptions & ACEC2_CEC_DEFER));
    p->fSingleUse = fProfile != 1 && (pPars->nCecOptions & ACEC2_CEC_SINGLE_USE);
    if ( !p->Pars.pCancelled ) p->Pars.pCancelled = &p->fCancelled;
    p->vCells = Vec_PtrAlloc(100); p->vAlternatives = Vec_PtrAlloc(100);
    p->vDisjoint = Vec_IntAlloc(100);
    p->vProofs = Vec_PtrAlloc(16);
    p->vCellGates = Vec_WecAlloc(100); p->vAltGates = Vec_WecAlloc(100);
    p->vXors = Vec_IntAlloc(100); p->vConstants = Vec_IntAlloc(16); p->vCarries = Vec_IntAlloc(100);
    p->vVanish = Vec_IntAlloc(100);
    p->vXorFirst = Vec_IntStartFull(Gia_ManObjNum(pGia)); p->vXorNext = Vec_IntAlloc(100);
    p->vXorNetworks = Vec_WecAlloc(100); p->vXorLeaves = Vec_WecAlloc(100); p->vXorSinks = Vec_WecAlloc(100);
    p->vXorDepths = Vec_IntAlloc(100);
    p->vOwner = Vec_IntStartFull(Gia_ManObjNum(pGia)); p->vEdges = Vec_IntAlloc(100);
    p->vNodeCell = Vec_IntStartFull(Gia_ManObjNum(pGia)); p->vRefs = Vec_IntStart(Gia_ManObjNum(pGia));
    p->vTrees = Vec_WecAlloc(100); p->vLeaves = Vec_WecAlloc(100);
    p->vRoots = Vec_WecAlloc(100); p->vBias = Vec_WecAlloc(100);
    p->vTaps = Vec_WecAlloc(100);
    p->vBoundaries = Vec_WecAlloc(100);
    p->vWidths = Vec_IntAlloc(100); p->vNormal = Vec_IntAlloc(100);
    p->vPrefix = Vec_IntAlloc(100);
    p->vCounters = Vec_PtrAlloc(16);
    p->vRecords = Vec_PtrAlloc(16); p->vTreeRecord = Vec_IntAlloc(16);
    p->vWords = Vec_PtrAlloc(16); p->vTreeWord = Vec_IntAlloc(16);
    p->vExpressions = Vec_PtrAlloc(16); p->vTreeExpression = Vec_IntAlloc(16);
    {
        Gia_Obj_t * o; int i;
        Gia_ManForEachObj1(pGia, o, i)
        {
            if ( Gia_ObjIsAnd(o) || Gia_ObjIsCo(o) ) Vec_IntAddToEntry(p->vRefs, Gia_ObjFaninId0(o, i), 1);
            if ( Gia_ObjIsAnd(o) ) Vec_IntAddToEntry(p->vRefs, Gia_ObjFaninId1(o, i), 1);
            if ( Gia_ObjIsMux(pGia, o) ) Vec_IntAddToEntry(p->vRefs, Gia_ObjFaninId2(pGia, i), 1);
        }
    }
    stage = Abc_Clock(); Acec2_Detect( p ); p->TimeDetect = Abc_Clock()-stage;
    stage = Abc_Clock(); if ( fProfile > 0 && (!vFocus || fFocusedProfile) ) Acec2_FindCounters(p); p->TimeCounters = Abc_Clock()-stage;
    stage = Abc_Clock(); Acec2_BuildTrees( p ); p->TimeTrees = Abc_Clock()-stage;
    if ( fProfile > 0 && fProfile != 3 )
    {
        // Preserve completed cell certificates before optional word searches.
        // A later local deadline must not erase the earlier recognition.
        Vec_IntFill(p->vTreeWord, Vec_WecSize(p->vTrees), -1);
        Vec_IntFill(p->vTreeExpression, Vec_WecSize(p->vTrees), -1);
        stage = Abc_Clock(); Acec2_BuildRecordsBasic(p); p->TimeRecords = Abc_Clock()-stage;
        if ( p->Pars.nAnalysisLevel >= 1 )
        { stage = Abc_Clock(); Acec2_CloseWords(p); p->TimeWords = Abc_Clock()-stage; }
        else Vec_IntFill(p->vTreeWord, Vec_WecSize(p->vTrees), -1);
        if ( p->Pars.nAnalysisLevel >= 2 )
        { stage = Abc_Clock(); Acec2_FindExpressions(p); p->TimeExpressions = Abc_Clock()-stage; }
        else Vec_IntFill(p->vTreeExpression, Vec_WecSize(p->vTrees), -1);
        stage = Abc_Clock(); Acec2_BuildRecords( p ); p->TimeRecords += Abc_Clock()-stage;
        if ( p->Pars.nAnalysisLevel >= 1 )
        {
            int queries = 4;
            stage = Abc_Clock(); Acec2_EnrichMasked(p, vFocus, &queries); p->TimeRecords += Abc_Clock()-stage;
        }
        if ( p->Pars.nAnalysisLevel >= 3 )
        {
            int attempt, work;
            for ( attempt = 0; attempt < ACEC2_OUTPUT_POLICIES && !Acec2_Stopped(p); attempt++ )
            {
                work = 1; Acec2_EnrichPolynomial(p, &work);
                if ( work ) break;
            }
        }
    }
    else
    {
        Vec_IntFill(p->vTreeRecord, Vec_WecSize(p->vTrees), -1);
        Vec_IntFill(p->vTreeWord, Vec_WecSize(p->vTrees), -1);
        Vec_IntFill(p->vTreeExpression, Vec_WecSize(p->vTrees), -1);
        if ( fProfile < 0 || fProfile == 3 )
        {
            stage = Abc_Clock(); Acec2_BuildRecordsBasic(p); p->TimeRecords = Abc_Clock()-stage;
        }
    }
    Acec2_Stopped( p );
    p->Time = Abc_Clock() - clk;
    return p;
}

/**Function*************************************************************

  Synopsis    [Collects checked cells for internal algebraic proofs.]

  Description [Word closure and expression recognition are intentionally
  omitted. The caller already supplies the word being certified.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Man_t * Acec2_AnalyzeCec( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline )
{
    return Acec2_AnalyzeInt(pGia, pPars, Deadline, -1, NULL, 0);
}

/**Function*************************************************************

  Synopsis    [Collects source cells and counters without recursive word discovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Man_t * Acec2_AnalyzeSourceCells( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline )
{
    return Acec2_AnalyzeInt(pGia, pPars, Deadline, 3, NULL, 0);
}

/**Function*************************************************************

  Synopsis    [Collects inexpensive cells without requesting word recognition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Man_t * Acec2_AnalyzeCells( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline )
{
    return Acec2_AnalyzeInt(pGia, pPars, Deadline, 0, NULL, 0);
}

/**Function*************************************************************

  Synopsis    [Runs complete standalone arithmetic recognition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Man_t * Acec2_AnalyzeLimit( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline )
{
    return Acec2_AnalyzeInt(pGia, pPars, Deadline, 1, NULL, 0);
}

/**Function*************************************************************

  Synopsis    [Profiles an open source cone without changing source IDs.]

  Description [The caller supplies a fanin-closed set. Certificates retain
  original source literals and remain usable after the local deadline.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Man_t * Acec2_AnalyzeFocused( Gia_Man_t * pGia, Acec2_Par_t * pPars, abctime Deadline, Vec_Bit_t * vFocus )
{
    Acec2_Par_t Cheap = *pPars;
    Acec2_Man_t * checkpoint, * profile;
    abctime clk = Abc_Clock();
    if ( !pGia || !vFocus || Vec_BitSize(vFocus) < Gia_ManObjNum(pGia) ) return NULL;
    // Save the cheap exact cover first. Optional profiling then uses the
    // same recovery, cover and word stages as the standalone command.
    Cheap.nCecOptions = 0; Cheap.nAnalysisLevel = 0;
    checkpoint = Acec2_AnalyzeInt(pGia, &Cheap, Deadline, 3, vFocus, 0);
    if ( !checkpoint || Acec2_Stopped(checkpoint) ) return checkpoint;
    profile = Acec2_AnalyzeInt(pGia, pPars, Deadline, 1, vFocus, 1);
    if ( profile && Vec_PtrSize(profile->vRecords) )
    {
        Acec2_Free(checkpoint); profile->Time = Abc_Clock()-clk; return profile;
    }
    if ( profile ) checkpoint->fStopped |= profile->fStopped;
    Acec2_Free(profile); checkpoint->Time = Abc_Clock()-clk; return checkpoint;
}

/**Function*************************************************************

  Synopsis    [Analyzes a GIA without changing its structure or scratch.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Man_t * Acec2_Analyze( Gia_Man_t * pGia, Acec2_Par_t * pPars )
{
    return Acec2_AnalyzeLimit( pGia, pPars, pPars->nTimeLimit ? Abc_Clock()+(abctime)pPars->nTimeLimit*CLOCKS_PER_SEC : 0 );
}

/**Function*************************************************************

  Synopsis    [Releases a certified linear or product word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_WordFree( Acec2_Word_t * p )
{
    if ( !p ) return;
    Vec_IntFree(p->vTerms); Vec_IntFree(p->vConstants); Vec_IntFreeP(&p->vBits);
    Vec_IntFreeP(&p->vRollback);
    Vec_IntFreeP(&p->vSumProducts);
    Vec_IntFreeP(&p->vSourceCut);
    if ( p->pProduct )
    {
        Vec_IntFree(p->pProduct->vOperands[0]); Vec_IntFree(p->pProduct->vOperands[1]); ABC_FREE(p->pProduct);
    }
    ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Releases every object owned by an analysis instance.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_Free( Acec2_Man_t * p )
{
    Acec2_Cell_t * c; Acec2_Word_t * w; Acec2_Record_t * r; Acec2_Counter_t * counter; Acec2_Expr_t * e; Acec2_Proof_t * proof; Acec2_WordSim_t * domain; Acec2_Product_t * product; int i;
    if ( !p ) return;
    Vec_BitFreeP(&p->vFocus);
    Vec_PtrForEachEntry( Acec2_Cell_t *, p->vCells, c, i ) ABC_FREE( c );
    Vec_PtrForEachEntry( Acec2_Cell_t *, p->vAlternatives, c, i ) ABC_FREE( c );
    Vec_PtrFree(p->vAlternatives);
    Vec_PtrForEachEntry(Acec2_Proof_t *, p->vProofs, proof, i)
    {
        Vec_IntFreeP(&proof->vCut); Vec_IntFree(proof->vRoots); Vec_IntFreeP(&proof->vIdentity); Vec_IntFreeP(&proof->vChain);
        Vec_WecFreeP(&proof->vMonomials); Vec_WrdFreeP(&proof->vCoefficients); ABC_FREE(proof);
    }
    Vec_PtrFree(p->vProofs);
    Vec_WecFree(p->vCellGates); Vec_WecFree(p->vAltGates);
    Vec_IntFree(p->vXorFirst); Vec_IntFree(p->vXorNext);
    Vec_IntFreeP(&p->vXorBest); Vec_IntFreeP(&p->vXorGroup); Vec_IntFree(p->vXorDepths);
    Acec2_ParityFree(p->pParity);
    Acec2_CarryStop(p);
    Vec_IntFreeP(&p->vMaskCandidates);
    Vec_WecFree(p->vXorNetworks); Vec_WecFree(p->vXorLeaves); Vec_WecFree(p->vXorSinks);
    Vec_PtrFree(p->vCells); Vec_IntFree(p->vXors); Vec_IntFree(p->vConstants); Vec_IntFree(p->vCarries); Vec_IntFreeP(&p->vExtraRules); Vec_IntFree(p->vOwner); Vec_IntFree(p->vEdges);
    Vec_IntFree(p->vNodeCell); Vec_IntFree(p->vRefs); Vec_IntFree(p->vPrefix); Vec_WecFree(p->vTaps);
    Vec_WecFree(p->vBoundaries);
    Vec_IntFree(p->vVanish);
    Vec_IntFreeP(&p->vDisjoint);
    Vec_WecFree(p->vTrees); Vec_WecFree(p->vLeaves); Vec_WecFree(p->vRoots); Vec_WecFree(p->vBias);
    Vec_IntFree(p->vWidths); Vec_IntFree(p->vNormal);
    Vec_PtrForEachEntry(Acec2_Word_t *, p->vWords, w, i)
        Acec2_WordFree(w);
    Vec_PtrFree(p->vWords); Vec_IntFree(p->vTreeWord);
    Vec_PtrForEachEntry(Acec2_Record_t *, p->vRecords, r, i) Acec2_RecordFree(r);
    Vec_PtrFree(p->vRecords); Vec_IntFree(p->vTreeRecord);
    Acec2_GapStop(p);
    Vec_IntFreeP(&p->vProductProgress);
    if ( p->vSourceProducts )
    {
        Vec_PtrForEachEntry(Acec2_Product_t *, p->vSourceProducts, product, i)
        { Vec_IntFree(product->vOperands[0]); Vec_IntFree(product->vOperands[1]); ABC_FREE(product); }
        Vec_PtrFree(p->vSourceProducts);
    }
    if ( p->hSourceProducts ) Hsh_VecManStop(p->hSourceProducts);
    Vec_WecFreeP(&p->vSourceProductIds); Vec_IntFreeP(&p->vRegionStage);
    Vec_IntFreeP(&p->vRegionClasses);
    Vec_IntFreeP(&p->vRegionWord); Vec_IntFreeP(&p->vLinearProgress);
    Vec_WecFreeP(&p->vRegionWordQueues); Vec_IntFreeP(&p->vRecordWork);
    Vec_IntFreeP(&p->vExtended); Vec_IntFreeP(&p->vComposeTried);
    Vec_IntFreeP(&p->vWordProgress); Vec_IntFreeP(&p->vRegionRequests);
    Acec2_TruthCacheStop(p->pTruthCache);
    Acec2_CounterStop(p);
    if ( p->hCounterRegions ) Hsh_VecManStop(p->hCounterRegions);
    Vec_PtrForEachEntry(Acec2_Counter_t *, p->vCounters, counter, i)
    { Vec_IntFree(counter->vInputs); Vec_IntFree(counter->vOutputs); Vec_IntFree(counter->vGates); ABC_FREE(counter); }
    Vec_PtrFree(p->vCounters);
    if ( p->hFailedProofs ) Hsh_VecManStop(p->hFailedProofs);
    Vec_IntFreeP(&p->vFailedProofs);
    if ( p->hCertificates ) Hsh_VecManStop(p->hCertificates);
    Vec_IntFreeP(&p->vCertificates);
    if ( p->vWordSiblings ) Vec_WecFree(p->vWordSiblings);
    if ( p->hWordMap ) Hsh_Int1ManStop(p->hWordMap);
    Vec_IntFreeP(&p->vWordMap); Vec_IntFreeP(&p->vWordHeads); Vec_IntFreeP(&p->vWordNext);
    if ( p->vWordDomains )
    {
        Vec_PtrForEachEntry(Acec2_WordSim_t *, p->vWordDomains, domain, i) Acec2_WordSimStop(domain);
        Vec_PtrFree(p->vWordDomains);
    }
    Vec_PtrForEachEntry(Acec2_Expr_t *, p->vExpressions, e, i) Acec2_ExprFree(e);
    Vec_PtrFree(p->vExpressions); Vec_IntFree(p->vTreeExpression);
    Vec_IntFreeP(&p->vOperands[0]); Vec_IntFreeP(&p->vOperands[1]); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Names structural boundary decisions without inferring semantics.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static const char * Acec2_BoundaryName( int Reason )
{
    static const char * const Names[ACEC2_BOUNDARY_COUNT] = {
        "constant", "primary_input", "unselected_cell_alternative", "parity_without_selected_cell",
        "logic_without_selected_cell", "multiple_consumers_deferred", "weight_or_phase_conflict",
        "shared_use_retained", "primary_output", "no_selected_cell_consumer", "unresolved_cell_consumers", "external_tap", "input_bit_product"
    };
    return Reason >= 0 && Reason < ACEC2_BOUNDARY_COUNT ? Names[Reason] : "invalid";
}

/**Function*************************************************************

  Synopsis    [Tests whether any requested analysis encountered an effort cap.]

  Description [Absence of a recorded limit is not a completeness theorem.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_HasLimits( Acec2_Man_t * p )
{
    return p->fStorageLimit || p->nCutLimits || p->nPairLimits || p->nRecoveryLimits ||
        p->nXorExpansionLimits || p->nParitySetLimits || p->nParityPairLimits || p->nMaskLimits || p->nUnconfirmedCuts || p->nFunctionalLimits || p->nParityLimits ||
        p->nCounterLimits || p->nWordLimits || p->nWordPolyLimits || p->nRecordLimits || p->nWeightedLimits || p->nGapLimits || p->nGridLimits || p->nGridLowLimits || p->nGridLocalLimits || p->nGridPartitionLimits || p->nGridChainLimits ||
        p->nProductLimits || p->nProductLeafLimits || p->nSumLimits || p->nExprLimits || p->nPolyStatus < 0;
}

/**Function*************************************************************

  Synopsis    [Prints a bounded list of source literals without assuming a bus.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PrintLiterals( FILE * f, Vec_Int_t * v, int Step )
{
    fprintf(f, "["); Acec2_WriteList(f, v, Step, 6); fprintf(f, "]");
}

/**Function*************************************************************

  Synopsis    [Reports checked components separately from cell totals.]

  Description [Source literals are ordered only where a certificate supplies
  an operand order. The width is the modulus, and the binary prefix reports
  how much of the weighted identity is an observed result word.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PrintComponents( Acec2_Man_t * p, FILE * f, int fVerbose )
{
    Acec2_Record_t * r; Acec2_Product_t * product;
    int i, k, side, pass, primary, count = 0, products, cells, counters = 0, hidden = 0, fullWidth;
    // Show words and products before the smaller alternative identities, so
    // the default row limit cannot hide a recognized multiplier.
    for ( pass = 0; pass < 2; pass++ )
    Vec_PtrForEachEntry(Acec2_Record_t *, p->vRecords, r, i)
    {
        products = r->vFactors ? Vec_PtrSize(r->vFactors) : 0;
        fullWidth = Acec2_RecordFullProductWidth(r);
        cells = r->Tree >= 0 ? Vec_IntSize(Vec_WecEntry(p->vTrees, r->Tree)) : 0;
        primary = products || r->Word >= 0 || r->vOutputMasks || r->fPolynomial || (cells >= 2 && Vec_IntEntry(p->vTreeRecord, r->Tree) == i);
        if ( primary != (pass == 0) ) continue;
        if ( !primary && r->Counter < 0 && !r->Proof && !r->vParts ) continue;
        if ( !fVerbose && ((r->Counter >= 0 && counters++ >= 4) || count >= 32) ) { hidden++; continue; }
        count++;
        if ( count == 1 ) fprintf(f, "Components (source literals; overlapping alternatives retained):\n  ID  Type             Identity/binary bits  Cells  Status / outputs / operands\n");
        fprintf(f, "  %-3d %-16s %5d/%-5d          %-5d checked; %s; out=", i,
            products > 1 ? "sum_of_products" : products ? "product" : r->fPolynomial ? "polynomial_word" : r->Word >= 0 ? "adder_word" :
            r->vOutputMasks ? "masked_word" : r->Counter >= 0 ? "counter" : r->Proof ? "boundary_identity" : r->vParts ? "arithmetic_region" : "adder_region",
            r->Width, r->Prefix, cells, fullWidth > r->Width ? "product prefix; higher bits unproved" : r->Prefix == r->Width ? "word closed at stated modulus" : "weighted boundary open");
        Acec2_PrintLiterals(f, r->vOutputs, 2);
        if ( r->vOutputMasks ) { fprintf(f, " xor="); Acec2_PrintLiterals(f, r->vOutputMasks, 1); }
        if ( products )
            Vec_PtrForEachEntry(Acec2_Product_t *, r->vFactors, product, k)
            {
                fprintf(f, " %s", k ? "+ " : "operands=");
                for ( side = 0; side < 2; side++ )
                {
                    fprintf(f, "%s%s%d", side ? "*" : "", product->fSigned[side] ? "s" : "u", Vec_IntSize(product->vOperands[side]));
                    Acec2_PrintLiterals(f, product->vOperands[side], 1);
                }
                if ( product->Shift || product->fNeg ) fprintf(f, "(shift=%d,neg=%d)", product->Shift, product->fNeg);
            }
        else { fprintf(f, " cut="); Acec2_PrintLiterals(f, r->vCut, 1); }
        if ( products && r->FactorWidth != r->Width ) fprintf(f, " factors checked modulo 2^%d", r->FactorWidth);
        if ( fullWidth > r->Width ) fprintf(f, " untruncated product width=%d, unproved columns=%d..%d", fullWidth, r->Width, fullWidth-1);
        if ( products && Vec_WecSize(r->vResidual) ) fprintf(f, " + %d residual terms", Vec_WecSize(r->vResidual));
        fprintf(f, "\n");
    }
    if ( hidden ) fprintf(f, "  %d further component alternatives; use -v or -J for all records.\n", hidden);
    Acec2_PrintGapProducts(p, f, 0);
}

/**Function*************************************************************

  Synopsis    [Prints coverage, limits, and optionally every arithmetic region.]

  Description [Widths are relative weight spans, not inferred bus types.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_Print( Acec2_Man_t * p, FILE * pFile, int fVerbose )
{
    Vec_Int_t * vTree; Acec2_Cell_t * c; Acec2_Record_t * r;
    int i, k, id, fa, depth, records = 0, products = 0;
    Vec_PtrForEachEntry(Acec2_Record_t *, p->vRecords, r, i)
        if ( r->vFactors && Vec_PtrSize(r->vFactors) ) { records++; products += Vec_PtrSize(r->vFactors); }
    fprintf(pFile, "Arithmetic: XOR2 = %d. XOR3 = %d. XOR2 groups = %d. XOR2 depth = %d. Parity outside cells = %d.\n",
        p->nXor2, p->nXor3, p->nXorGroups, p->nXorDepth, p->nParityOnly);
    fprintf(pFile, "Adders: HA = %d. FA = %d. Regions = %d. Normalizable = %d. Covered ANDs = %d / %d.\n",
        p->nHadds, p->nFadds, Vec_WecSize(p->vTrees), p->nNormal, p->nCovered, Gia_ManAndNum(p->pGia));
    fprintf(pFile, "Certified region words = %d. Closure attempts = %d. SAT conflicts = %d. Closure limits = %d.\n",
        Vec_PtrSize(p->vWords), p->nWordAttempts, p->nWordConflicts, p->nWordLimits);
    fprintf(pFile, "Weighted product expressions = %d. Factored products = %d. Expression limits = %d.\n",
        Vec_PtrSize(p->vExpressions), p->nProducts, p->nExprLimits);
    fprintf(pFile, "Factored component records = %d. Product terms across records = %d (alternatives may overlap).\n", records, products);
    Acec2_PrintComponents(p, pFile, fVerbose);
    fprintf(pFile, "Regions: multi-cell = %d. Largest = %d cells. Fully normalizable = %d cells (largest %d). Prefixes = %d (%d low-column cells). Internal taps = %d.\n",
        p->nMulti, p->nLargest, p->nNormalCells, p->nLargestNormal, p->nPrefix, p->nPrefixCells, p->nTaps);
    fprintf(pFile, "Analysis: candidates = %d. Cuts = %d. Cut-limited nodes = %d. Pair-limited supports = %d. Rejected links = %d. %s Time = %.3f sec.\n",
        p->nCandidates, p->nCuts, p->nCutLimits, p->nPairLimits, p->nRejected,
        p->fStopped ? "Stopped; partial report." : "Finished; effort limits are reported separately.", (double)p->Time/CLOCKS_PER_SEC);
    fprintf(pFile, "Filtered %d candidates without an externally used carry.%s\n", p->nCarryFiltered,
        p->fStorageLimit ? " Cut storage limit reached." : "");
    fprintf(pFile, "Retained %d alternative cells outside the selected cover.\n", Vec_PtrSize(p->vAlternatives));
    if ( fVerbose ) fprintf(pFile, "Independent disjoint cover = %d cells.\n", Vec_IntSize(p->vDisjoint)/2);
    fprintf(pFile, "Stored %d parity networks with explicit cuts, leaves, and sinks.\n", Vec_WecSize(p->vXorNetworks));
    fprintf(pFile, "Exact parity forms = %d. Reassociated adder pairs = %d. Form/pair limits = %d/%d.\n",
        p->nParityForms, p->nParityPairs, p->nParitySetLimits, p->nParityPairLimits);
    if ( p->nMaskAttempts || p->nMaskLimits ) fprintf(pFile, "Masked word decoding: attempts = %d, checked source records = %d, effort limits = %d.\n",
        p->nMaskAttempts, p->nMaskRecords, p->nMaskLimits);
    fprintf(pFile, "Functional carry recovery: checked cells = %d, SAT proposals = %d, effort limits = %d.\n", p->nFunctionalCells, p->nFunctionalProbes, p->nFunctionalLimits);
    fprintf(pFile, "Functional parity recovery: checked cells = %d, SAT proposals = %d, effort limits = %d.\n", p->nParityCells, p->nParityProbes, p->nParityLimits);
    fprintf(pFile, "Independent product words: proved = %d, proposals = %d, limited = %d.\n", p->nProductWords, p->nProductAttempts, p->nProductLimits);
    if ( p->nCertificateRecords || p->nCertificateContext )
        fprintf(pFile, "Matcher product certificates: source records = %d, not imported = %d.\n", p->nCertificateRecords, p->nCertificateContext);
    if ( p->nStageRequests[1]+p->nStageRequests[2]+p->nStageRequests[3] )
    {
        fprintf(pFile, "On-demand recognition: word/product/expression requests = %d/%d/%d, new records = %d/%d/%d.\n",
            p->nStageRequests[1], p->nStageRequests[2], p->nStageRequests[3], p->nStageRecords[1], p->nStageRecords[2], p->nStageRecords[3]);
        fprintf(pFile, "On-demand work units: word/product/composition/product-sum = %d/%d/%d/%d.\n",
            p->nStageQueries[0], p->nStageQueries[1], p->nStageQueries[2], p->nStageQueries[3]);
    }
    if ( fVerbose )
        fprintf(pFile, "Analysis stages: detection = %.3f, counters = %.3f, regions = %.3f, words = %.3f, expressions = %.3f, records = %.3f sec.\n",
            (double)p->TimeDetect/CLOCKS_PER_SEC, (double)p->TimeCounters/CLOCKS_PER_SEC,
            (double)p->TimeTrees/CLOCKS_PER_SEC, (double)p->TimeWords/CLOCKS_PER_SEC,
            (double)p->TimeExpressions/CLOCKS_PER_SEC, (double)p->TimeRecords/CLOCKS_PER_SEC);
    if ( p->nRecoverySteps || p->nRecoveryLimits )
        fprintf(pFile, "Cut recovery: functions = %d. Fanout edges = %llu. Limited closures = %d.\n",
            p->nRecoveredCuts, (unsigned long long)p->nRecoverySteps, p->nRecoveryLimits);
    if ( p->nXorExpanded || p->nXorExpansionLimits )
        fprintf(pFile, "Parity composition: checked XOR3 cuts = %d. Limited passes = %d.\n", p->nXorExpanded, p->nXorExpansionLimits);
    if ( p->nCutCorrections || p->nUnconfirmedCuts )
        fprintf(pFile, "Independent cut checks: corrected tables = %llu. Unconfirmed arithmetic cuts = %llu.\n",
            (unsigned long long)p->nCutCorrections, (unsigned long long)p->nUnconfirmedCuts);
    if ( p->nPolyStatus )
        fprintf(pFile, "Polynomial: %s. Terms = %d. Peak = %d. Proved carry recurrences = %d.\n",
            p->nPolyStatus == 1 ? "complete" : "limited", p->nPolyTerms, p->nPolyPeak, p->nPolyCarries);
    if ( p->vOperands[0] )
        fprintf(pFile, "Proved full product: %s %d-bit x %s %d-bit -> %d output bits.\n",
            p->fPolySigned[0] ? "signed" : "unsigned", Vec_IntSize(p->vOperands[0]),
            p->fPolySigned[1] ? "signed" : "unsigned", Vec_IntSize(p->vOperands[1]), p->nPolyWidth);
    if ( p->nPolyRecords ) fprintf(pFile, "Whole-output polynomial source records = %d.\n", p->nPolyRecords);
    if ( p->nOutputPolyAttempts ) fprintf(pFile, "Bounded source output checks: attempts = %d, effort limits = %d.\n",
        p->nOutputPolyAttempts, p->nOutputPolyLimits);
    fprintf(pFile, "General counters = %d. Counter cut proposals = %d. Counter effort limits = %d. Checked records = %d.\n",
        Vec_PtrSize(p->vCounters), p->nCounterCuts, p->nCounterLimits, Vec_PtrSize(p->vRecords));
    if ( p->nCounterBridgeChecks ) fprintf(pFile, "Counter boundary extensions: cuts = %d, proved = %d.\n", p->nCounterBridgeChecks, p->nCounterBridges);
    if ( p->nCounterRequests ) fprintf(pFile, "On-demand counters: requests = %d, parity roots/extensions visited = %d, imported = %d.\n",
        p->nCounterRequests, p->nCounterWork, p->nCounterRecords);
    if ( p->nCarryRequests ) fprintf(pFile, "On-demand carries: requests = %d, work units = %d, imported records = %d, search %s.\n",
        p->nCarryRequests, p->nCarryWork, p->nCarryRecords, p->fCarryComplete ? "finished" : "pending");
    fprintf(pFile, "Record limits = %d. Product-leaf limits = %d. Requested stages %s.\n", p->nRecordLimits,
        p->nProductLeafLimits, p->fStopped ? "interrupted" : Acec2_HasLimits(p) ? "finished with effort limits" : "finished without reported effort limits");
    fprintf(pFile, "Region boundary reasons:");
    for ( i = 0; i < ACEC2_BOUNDARY_COUNT; i++ )
        if ( p->nBoundaries[i] ) fprintf(pFile, " %s=%d", Acec2_BoundaryName(i), p->nBoundaries[i]);
    fprintf(pFile, ".\n");
    if ( p->nWordPolyAttempts || p->nWordPolyHits )
        fprintf(pFile, "Word polynomial checks: attempts = %d, proved = %d, limited = %d, reused = %d.\n",
            p->nWordPolyAttempts, p->nWordPolyProved, p->nWordPolyLimits, p->nWordPolyHits);
    if ( p->nWordBoundaryAttempts )
        fprintf(pFile, "Word boundary checks: attempts = %d, proved = %d, partial prefixes = %d.\n", p->nWordBoundaryAttempts, p->nWordBoundaryProved, p->nWordBoundaryPrefixes);
    if ( p->nWordCecAttempts )
        fprintf(pFile, "Word boundary CEC: attempts = %d, proved = %d.\n", p->nWordCecAttempts, p->nWordCecProved);
    if ( p->nWeightedAttempts || p->nWeightedLimits )
        fprintf(pFile, "Weighted source checks: attempts = %d, proved = %d, limited = %d.\n", p->nWeightedAttempts, p->nWeightedProved, p->nWeightedLimits);
    if ( p->nWeightedTruthChecks )
        fprintf(pFile, "Exhaustive weighted checks: attempts = %d, proved = %d, disproved = %d, limited = %d.\n",
            p->nWeightedTruthChecks, p->nWeightedTruthProved, p->nWeightedTruthDisproved, p->nWeightedTruthLimits);
    if ( p->nGapGroups || p->nGapLimits )
        fprintf(pFile, "Boundary gaps: groups = %d, proposals = %d, improved boundaries = %d, limited = %d.\n", p->nGapGroups, p->nGapProposals, p->nGapClosed, p->nGapLimits);
    if ( p->nGridAttempts || p->nGridLimits )
        fprintf(pFile, "Operand-grid checks: attempts = %d, complete identities = %d, checked prefixes = %d, limited = %d.\n", p->nGridAttempts, p->nGridProved, p->nGridPrefixes, p->nGridLimits);
    if ( p->nGridProofHits || p->nGridProofCacheLimits )
        fprintf(pFile, "Product-grid proof cache: hits = %d, storage limits = %d.\n", p->nGridProofHits, p->nGridProofCacheLimits);
    if ( p->nGridLowAttempts )
        fprintf(pFile, "Product-grid partial runs: attempts = %d, proved = %d, limited = %d.\n", p->nGridLowAttempts, p->nGridLowProved, p->nGridLowLimits);
    if ( p->nGridLocalChecks || p->nGridLocalLimits )
        fprintf(pFile, "Product-grid local cuts: attempts = %d, proved = %d, limited = %d.\n", p->nGridLocalChecks, p->nGridLocalProved, p->nGridLocalLimits);
    if ( p->nGridPartitionAttempts || p->nGridPartitionLimits )
        fprintf(pFile, "Product-grid partitions: attempts = %d, checked pieces = %d, proved = %d, limited = %d.\n",
            p->nGridPartitionAttempts, p->nGridPartitionParts, p->nGridPartitionProved, p->nGridPartitionLimits);
    if ( !fVerbose ) return;
    Vec_WecForEachLevel(p->vTrees, vTree, i)
    {
        fa = depth = 0;
        Vec_IntForEachEntry(vTree, id, k)
        {
            c = Acec2_Cell(p, id); fa += c->nIns == 3; depth = Abc_MaxInt(depth, c->Depth);
        }
        fprintf(pFile, "  Region %d: HA = %d. FA = %d. Columns = %d. Depth = %d. Leaves = %d. Roots = %d. Prefix = %d. Internal taps = %d.\n",
            i, Vec_IntSize(vTree)-fa, fa, Vec_IntEntry(p->vWidths, i), depth,
            Vec_IntSize(Vec_WecEntry(p->vLeaves, i))/2, Vec_IntSize(Vec_WecEntry(p->vRoots, i))/2,
            Vec_IntEntry(p->vPrefix, i), Vec_IntSize(Vec_WecEntry(p->vTaps, i))/3);
        {
            int counts[ACEC2_BOUNDARY_COUNT] = {0}; Vec_Int_t * v = Vec_WecEntry(p->vBoundaries, i);
            for ( k = 3; k < Vec_IntSize(v); k += 5 ) counts[Vec_IntEntry(v, k)]++;
            fprintf(pFile, "    Boundaries:");
            for ( k = 0; k < ACEC2_BOUNDARY_COUNT; k++ ) if ( counts[k] ) fprintf(pFile, " %s=%d", Acec2_BoundaryName(k), counts[k]);
            fprintf(pFile, ".\n");
        }
    }
}

/**Function*************************************************************

  Synopsis    [Writes literal/weight pairs without platform-dependent formats.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_JsonPairs( FILE * f, Vec_Int_t * v )
{
    int k;
    fprintf(f, "[");
    for ( k = 0; k < Vec_IntSize(v); k += 2 ) fprintf(f, "%s[%d,%d]", k ? "," : "", Vec_IntEntry(v, k), Vec_IntEntry(v, k+1));
    fprintf(f, "]");
}

/**Function*************************************************************

  Synopsis    [Converts elapsed ticks without locale-dependent formatting.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned long long Acec2_Microseconds( abctime Time )
{
    return (unsigned long long)(Time/CLOCKS_PER_SEC)*1000000ULL +
        (unsigned long long)(Time%CLOCKS_PER_SEC)*1000000ULL/CLOCKS_PER_SEC;
}

/**Function*************************************************************

  Synopsis    [Exports the checked cells, parity cuts, and weighted regions.]

  Description [Literal encoding is 2*object_ID + complement. Weight is the
  exponent of two relative to the region's lowest selected cell column.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_WriteJson( Acec2_Man_t * p, FILE * f )
{
    Vec_Int_t * vTree, * v, * vHeights = Vec_IntAlloc(32);
    Acec2_Cell_t * c; Acec2_Word_t * w; Acec2_Expr_t * e; Acec2_Product_t * product; Acec2_Proof_t * proof;
    int i, k, j, id, depth, side;
    unsigned long long micros = Acec2_Microseconds(p->Time);
    fprintf(f, "{\n\"schema\":\"abc.acec2.v9\",\"complete\":%s,\"execution_complete\":%s,\"effort_limited\":%s,\"completeness_scope\":\"bounded search execution, not recognition completeness\",\"inputs\":%d,\"outputs\":%d,\"registers\":%d,\n",
        p->fStopped || Acec2_HasLimits(p) ? "false" : "true", p->fStopped ? "false" : "true",
        Acec2_HasLimits(p) ? "true" : "false", Gia_ManCiNum(p->pGia), Gia_ManCoNum(p->pGia), Gia_ManRegNum(p->pGia));
    fprintf(f, "\"parameters\":{\"cuts_per_node\":%d,\"max_width\":%d,\"time_limit_seconds\":%d,\"carry_pairs_per_sum\":128,\"analysis_level\":%d},\n",
        p->Pars.nCuts, p->Pars.nMaxWidth, p->Pars.nTimeLimit, p->Pars.nAnalysisLevel);
    fprintf(f, "\"stage_microseconds\":{\"detection\":%llu,\"counters\":%llu,\"regions\":%llu,\"initial_words\":%llu,\"initial_expressions\":%llu,\"record_enrichment\":%llu},\n",
        Acec2_Microseconds(p->TimeDetect), Acec2_Microseconds(p->TimeCounters), Acec2_Microseconds(p->TimeTrees),
        Acec2_Microseconds(p->TimeWords), Acec2_Microseconds(p->TimeExpressions), Acec2_Microseconds(p->TimeRecords));
    fprintf(f, "\"carry_statistics\":{\"proposals\":%d,\"recovered_cells\":%d,\"effort_limits\":%d,\"source_requests\":%d,\"source_work\":%d,\"imported_records\":%d,\"source_search_finished\":%s},\n",
        p->nFunctionalProbes, p->nFunctionalCells, p->nFunctionalLimits, p->nCarryRequests, p->nCarryWork,
        p->nCarryRecords, p->fCarryComplete ? "true" : "false");
    fprintf(f, "\"on_demand_stages\":[");
    for ( i = 0; i < 4; i++ ) fprintf(f, "%s{\"level\":%d,\"requests\":%d,\"new_records\":%d}", i ? "," : "", i, p->nStageRequests[i], p->nStageRecords[i]);
    fprintf(f, "],\n");
    fprintf(f, "\"on_demand_actions\":[");
    for ( i = 0; i < 4; i++ ) fprintf(f, "%s{\"action\":%d,\"visits\":%d,\"work_units\":%d}", i ? "," : "", i, p->nStageActions[i], p->nStageQueries[i]);
    fprintf(f, "],\n");
    fprintf(f, "\"cache_hits\":{\"product_certificates\":%d,\"boundary_proofs\":%d,\"simulation_domains\":%d},\n",
        p->nCertificateHits, p->nFailedProofHits, p->nWordDomainHits);
    fprintf(f, "\"cut_statistics\":{\"stored_record_bytes\":%u,\"duplicates_skipped\":%llu,\"dominated_skipped\":%llu,\"truth_evaluations\":%llu},\n",
        (unsigned)(4*sizeof(int)), (unsigned long long)p->nDuplicates,
        (unsigned long long)p->nDominated, (unsigned long long)p->nTruths);
    fprintf(f, "\"cut_checks\":{\"checked\":%llu,\"corrected\":%llu,\"unconfirmed\":%llu},\n",
        (unsigned long long)p->nCutChecks, (unsigned long long)p->nCutCorrections, (unsigned long long)p->nUnconfirmedCuts);
    fprintf(f, "\"cut_recovery\":{\"functions\":%d,\"fanout_edges\":%llu,\"limited_closures\":%d,\"edges_per_support\":4096,\"edges_per_object\":32,\"composed_xor3\":%d,\"composition_limited\":%d},\n",
        p->nRecoveredCuts, (unsigned long long)p->nRecoverySteps, p->nRecoveryLimits, p->nXorExpanded, p->nXorExpansionLimits);
    fprintf(f, "\"summary\":{\"xor2\":%d,\"xor3\":%d,\"parity_groups\":%d,\"parity_depth\":%d,\"half_adders\":%d,\"full_adders\":%d,\"regions\":%d,\"normalizable\":%d,\"covered_ands\":%d,\"ands\":%d,\"candidates\":%d,\"cuts\":%d,\"cut_limited_nodes\":%d,\"pair_limited_supports\":%d,\"rejected_links\":%d,\"microseconds\":%llu,",
        p->nXor2, p->nXor3, p->nXorGroups, p->nXorDepth, p->nHadds, p->nFadds,
        Vec_WecSize(p->vTrees), p->nNormal, p->nCovered, Gia_ManAndNum(p->pGia),
        p->nCandidates, p->nCuts, p->nCutLimits, p->nPairLimits, p->nRejected, micros);
    fprintf(f, "\"parity_outside_cells\":%d,\"carry_filtered_candidates\":%d,\"multi_cell_regions\":%d,\"largest_region\":%d,\"normalizable_cells\":%d,\"largest_normalizable_region\":%d,\"prefix_regions\":%d,\"prefix_cells\":%d,\"internal_taps\":%d,\"storage_limited\":%s,\"alternative_cells\":%d},\n",
        p->nParityOnly, p->nCarryFiltered, p->nMulti, p->nLargest, p->nNormalCells, p->nLargestNormal,
        p->nPrefix, p->nPrefixCells, p->nTaps, p->fStorageLimit ? "true" : "false", Vec_PtrSize(p->vAlternatives));
    fprintf(f, "\"functional_carries\":{\"checked\":%d,\"proposals\":%d,\"proposal_limit\":%d,\"conflict_limit\":%d,\"effort_limits\":%d},\n", p->nFunctionalCells, p->nFunctionalProbes, p->nCarryProbeLimit, p->nCarryConflictLimit, p->nFunctionalLimits);
    fprintf(f, "\"functional_parity\":{\"checked\":%d,\"proposals\":%d,\"proposal_limit\":128,\"conflict_limit\":20000,\"effort_limits\":%d},\n", p->nParityCells, p->nParityProbes, p->nParityLimits);
    fprintf(f, "\"exact_parity\":{\"forms\":%d,\"paired_cells\":%d,\"form_limits\":%d,\"pair_limits\":%d},\n",
        p->nParityForms, p->nParityPairs, p->nParitySetLimits, p->nParityPairLimits);
    fprintf(f, "\"masked_words\":{\"attempts\":%d,\"records\":%d,\"limits\":%d},\n", p->nMaskAttempts, p->nMaskRecords, p->nMaskLimits);
    fprintf(f, "\"output_polynomial_requests\":{\"attempts\":%d,\"effort_limits\":%d,\"skipped\":%s},\n",
        p->nOutputPolyAttempts, p->nOutputPolyLimits, p->nOutputPolySkipped ? "true" : "false");
    fprintf(f, "\"proofs\":[");
    Vec_PtrForEachEntry(Acec2_Proof_t *, p->vProofs, proof, i)
    {
        fprintf(f, "%s{\"id\":%d,\"method\":\"%s\",\"kind\":\"%s\",\"domain\":\"source\",\"support_cone_roots\":[", i ? "," : "", i, proof->Kind == 7 ? "exact_substitution" : (proof->Kind == 6 || proof->Kind == 8) ? "checked_grid_gaps" : proof->Kind == 5 ? "decoded_composition" : proof->Kind == 4 ? "exact_parity" : proof->Kind == 3 ? (proof->fExhaustive ? "exhaustive" : "cec") : "sat", proof->Kind == 8 ? "grid_expression" : proof->Kind == 7 ? "output_polynomial" : proof->Kind == 6 ? "product_grid" : proof->Kind == 5 ? "masked_identity" : proof->Kind == 4 ? "reassociated_adder" : proof->Kind == 3 ? "weighted_identity" : proof->Kind == 2 ? "sum_and_carry" : "carry");
        Acec2_WriteList(f, proof->vRoots, 1, 0);
        fprintf(f, "],\"support_cut_ids\":");
        if ( !proof->vCut ) fprintf(f, "null");
        else
        {
            fprintf(f, "[");
            Acec2_WriteList(f, proof->vCut, 1, 0);
            fprintf(f, "]");
        }
        fprintf(f, ",\"weighted_identity\":[");
        if ( proof->vIdentity ) Acec2_WriteList(f, proof->vIdentity, 1, 0);
        fprintf(f, "],\"half_adder_chain\":[");
        if ( proof->vChain ) Acec2_WriteList(f, proof->vChain, 1, 0);
        fprintf(f, "],\"carry_dependencies\":[%d,%d]}", proof->ChainProof[0]-1, proof->ChainProof[1]-1);
    }
    fprintf(f, "],\n\"cells\":[");
    Vec_PtrForEachEntry(Acec2_Cell_t *, p->vCells, c, i)
    {
        fprintf(f, "%s{\"id\":%d,\"type\":\"%s\",\"inputs\":[", i ? ",\n" : "", i, c->nIns == 3 ? "FA" : "HA");
        for ( k = 0; k < c->nIns; k++ ) fprintf(f, "%s%d", k ? "," : "", c->In[k]);
        fprintf(f, "],\"sum\":%d,\"carry\":%d,\"region\":%d,\"rank\":%d,\"phase\":%d,\"external_fanouts\":[%d,%d]",
            c->Out[0], c->Out[1], c->Tree, c->Rank, c->Phase, c->Ext[0], c->Ext[1]);
        fprintf(f, ",\"domain\":\"%s\",\"proof\":%d,\"covered_gates\":[", c->Proof ? "source" : "free_cut", c->Proof-1);
        Acec2_WriteList(f, Vec_WecEntry(p->vCellGates, i), 1, 0);
        fprintf(f, "]}");
    }
    fprintf(f, "],\n\"alternative_cells\":[");
    Vec_PtrForEachEntry(Acec2_Cell_t *, p->vAlternatives, c, i)
    {
        fprintf(f, "%s{\"id\":%d,\"type\":\"%s\",\"inputs\":[", i ? ",\n" : "", i, c->nIns == 3 ? "FA" : "HA");
        for ( k = 0; k < c->nIns; k++ ) fprintf(f, "%s%d", k ? "," : "", c->In[k]);
        fprintf(f, "],\"sum\":%d,\"carry\":%d,\"external_fanouts\":[%d,%d]",
            c->Out[0], c->Out[1], c->Ext[0], c->Ext[1]);
        fprintf(f, ",\"domain\":\"%s\",\"proof\":%d,\"covered_gates\":[", c->Proof ? "source" : "free_cut", c->Proof-1);
        Acec2_WriteList(f, Vec_WecEntry(p->vAltGates, i), 1, 0);
        fprintf(f, "]}");
    }
    fprintf(f, "],\n\"disjoint_cover\":"); Acec2_JsonPairs(f, p->vDisjoint);
    fprintf(f, ",\n\"regions\":[");
    Vec_WecForEachLevel(p->vTrees, vTree, i)
    {
        Acec2_Record_t * boundary;
        depth = 0;
        Vec_IntForEachEntry(vTree, id, k) depth = Abc_MaxInt(depth, Acec2_Cell(p, id)->Depth);
        fprintf(f, "%s{\"id\":%d,\"width\":%d,\"depth\":%d,\"normalizable\":%s,\"normalizable_prefix\":%d,\"cells\":[", i ? ",\n" : "", i,
            Vec_IntEntry(p->vWidths, i), depth, Vec_IntEntry(p->vNormal, i) ? "true" : "false", Vec_IntEntry(p->vPrefix, i));
        Acec2_WriteList(f, vTree, 1, 0);
        fprintf(f, "],\"leaves\":"); Acec2_JsonPairs(f, Vec_WecEntry(p->vLeaves, i));
        fprintf(f, ",\"roots\":"); Acec2_JsonPairs(f, Vec_WecEntry(p->vRoots, i));
        id = Acec2_GapRecord(p, Vec_IntEntry(p->vTreeRecord, i));
        boundary = id >= 0 ? (Acec2_Record_t *)Vec_PtrEntry(p->vRecords, id) : NULL;
        fprintf(f, ",\"recognized_boundary_record\":%d,\"recognized_roots\":", id);
        if ( boundary ) Acec2_JsonPairs(f, boundary->vOutputs); else fprintf(f, "[]");
        fprintf(f, ",\"recognized_terms\":");
        if ( boundary ) Acec2_JsonPairs(f, boundary->vTerms); else fprintf(f, "[]");
        fprintf(f, ",\"boundaries\":[");
        v = Vec_WecEntry(p->vBoundaries, i);
        for ( k = 0; k < Vec_IntSize(v); k += 5 )
            fprintf(f, "%s{\"direction\":\"%s\",\"literal\":%d,\"rank\":%d,\"reason\":\"%s\",\"cell\":%d}", k ? "," : "",
                Vec_IntEntry(v, k) == 0 ? "input" : Vec_IntEntry(v, k) == 1 ? "output" : "tap",
                Vec_IntEntry(v, k+1), Vec_IntEntry(v, k+2), Acec2_BoundaryName(Vec_IntEntry(v, k+3)), Vec_IntEntry(v, k+4));
        fprintf(f, "]");
        fprintf(f, ",\"internal_taps\":[");
        v = Vec_WecEntry(p->vTaps, i);
        for ( k = 0; k < Vec_IntSize(v); k += 3 )
            fprintf(f, "%s[%d,%d,%d]", k ? "," : "", Vec_IntEntry(v, k), Vec_IntEntry(v, k+1), Vec_IntEntry(v, k+2));
        fprintf(f, "]");
        fprintf(f, ",\"constant_columns\":[");
        v = Vec_WecEntry(p->vBias, i);
        Acec2_WriteList(f, v, 1, 0);
        fprintf(f, "],\"leaf_heights\":[");
        v = Vec_WecEntry(p->vLeaves, i);
        Vec_IntFill(vHeights, Vec_IntEntry(p->vWidths, i), 0);
        for ( k = 1; k < Vec_IntSize(v); k += 2 )
            if ( Vec_IntEntry(v, k) < Vec_IntSize(vHeights) ) Vec_IntAddToEntry(vHeights, Vec_IntEntry(v, k), 1);
        for ( j = 0; j < Vec_IntEntry(p->vWidths, i); j++ )
            fprintf(f, "%s%d", j ? "," : "", Vec_IntEntry(vHeights, j));
        fprintf(f, "]}");
    }
    fprintf(f, "],\n\"parity_cuts\":[");
    for ( i = 0; i < Vec_IntSize(p->vXors); i += 5 )
    {
        fprintf(f, "%s{\"output_literal\":%d,\"input_ids\":[", i ? "," : "", Vec_IntEntry(p->vXors, i+4));
        for ( k = 0; k < Vec_IntEntry(p->vXors, i); k++ ) fprintf(f, "%s%d", k ? "," : "", Vec_IntEntry(p->vXors, i+1+k));
        fprintf(f, "]}");
    }
    fprintf(f, "],\n\"xor_networks\":[");
    Vec_WecForEachLevel(p->vXorNetworks, v, i)
    {
        fprintf(f, "%s{\"id\":%d,\"depth\":%d,\"cut_indices\":[", i ? ",\n" : "", i, Vec_IntEntry(p->vXorDepths, i));
        Vec_IntForEachEntry(v, id, k) fprintf(f, "%s%d", k ? "," : "", Vec_IntEntry(p->vXorBest, id)/5);
        fprintf(f, "],\"leaf_ids\":[");
        Acec2_WriteList(f, Vec_WecEntry(p->vXorLeaves, i), 1, 0);
        fprintf(f, "],\"sink_ids\":[");
        Acec2_WriteList(f, Vec_WecEntry(p->vXorSinks, i), 1, 0);
        fprintf(f, "]}");
    }
    fprintf(f, "],\n\"word_closure\":{\"attempts\":%d,\"limited\":%d,\"sat_conflicts\":%d,\"conflict_limit_per_interface\":20000,\"refinement_limit\":16,\"counterexample_batch_limit\":64,",
        p->nWordAttempts, p->nWordLimits, p->nWordConflicts);
    fprintf(f, "\"polynomial\":{\"attempts\":%d,\"proved\":%d,\"limited\":%d,\"reused\":%d},",
        p->nWordPolyAttempts, p->nWordPolyProved, p->nWordPolyLimits, p->nWordPolyHits);
    fprintf(f, "\"boundary\":{\"attempts\":%d,\"proved\":%d,\"partial_prefixes\":%d},", p->nWordBoundaryAttempts, p->nWordBoundaryProved, p->nWordBoundaryPrefixes);
    fprintf(f, "\"boundary_cec\":{\"attempts\":%d,\"proved\":%d}},\n\"words\":[", p->nWordCecAttempts, p->nWordCecProved);
    Vec_PtrForEachEntry(Acec2_Word_t *, p->vWords, w, i)
    {
        fprintf(f, "%s{\"id\":%d,\"region\":%d,\"parent_record\":%d,\"width\":%d,\"rolled_cells\":%d,\"cut_terms\":", i ? ",\n" : "", i, w->Tree, w->Record, w->Width, w->nRolled);
        Acec2_JsonPairs(f, w->vTerms);
        fprintf(f, ",\"constant_columns\":[");
        Acec2_WriteList(f, w->vConstants, 1, 0);
        fprintf(f, "],\"result_literals\":[");
        Acec2_WriteList(f, w->vBits, 1, 0);
        fprintf(f, "],\"rollback_parts\":[");
        if ( w->vRollback )
            for ( k = 0; k < Vec_IntSize(w->vRollback); k += 4 )
                fprintf(f, "%s[%d,%d,%d,%d]", k ? "," : "", Vec_IntEntry(w->vRollback, k), Vec_IntEntry(w->vRollback, k+1),
                    Vec_IntEntry(w->vRollback, k+2), Vec_IntEntry(w->vRollback, k+3));
        fprintf(f, "],\"product_sum_reference\":[");
        if ( w->vSumProducts )
            for ( k = 0; k < Vec_IntSize(w->vSumProducts); k += 3 )
                fprintf(f, "%s[%d,%d,%d]", k ? "," : "", Vec_IntEntry(w->vSumProducts, k),
                    Vec_IntEntry(w->vSumProducts, k+1), Vec_IntEntry(w->vSumProducts, k+2));
        fprintf(f, "],\"reference_cut_literals\":[");
        if ( w->vSourceCut ) Acec2_WriteList(f, w->vSourceCut, 1, 0);
        fprintf(f, "],\"domain\":\"%s\",\"independent_linear_reference\":%s,\"polynomial_reference\":%s,\"product_reference\":",
            (w->fPolynomial || w->fSource) ? "source" : "free_cut", w->fIndependent ? "true" : "false", w->fPolynomial ? "true" : "false");
        if ( !w->pProduct ) fprintf(f, "null");
        else
        {
            fprintf(f, "{\"signed\":[%s,%s],\"operand_literals\":[", w->pProduct->fSigned[0] ? "true" : "false", w->pProduct->fSigned[1] ? "true" : "false");
            for ( side = 0; side < 2; side++ )
            {
                fprintf(f, "%s[", side ? "," : "");
                Acec2_WriteList(f, w->pProduct->vOperands[side], 1, 0);
                fprintf(f, "]");
            }
            fprintf(f, "]}");
        }
        fprintf(f, "}");
    }
    fprintf(f, "],\n\"product_word_certificates\":{\"proved\":%d,\"proposals\":%d,\"limited\":%d,\"proposal_limit\":64,\"source_queue_per_region\":128,\"source_queue_total\":4096,\"matcher_records\":%d,\"matcher_unstored\":%d},\n", p->nProductWords, p->nProductAttempts, p->nProductLimits, p->nCertificateRecords, p->nCertificateContext);
    fprintf(f, "\"product_sum_certificates\":{\"proved\":%d,\"proposals\":%d,\"limited\":%d,\"proposal_limit\":8},\n", p->nSumWords, p->nSumAttempts, p->nSumLimits);
    fprintf(f, "\"record_statistics\":{\"checked\":%d,\"effort_limits\":%d},\n", Vec_PtrSize(p->vRecords), p->nRecordLimits);
    fprintf(f, "\"weighted_source_checks\":{\"attempts\":%d,\"proved\":%d,\"limited\":%d},\n", p->nWeightedAttempts, p->nWeightedProved, p->nWeightedLimits);
    fprintf(f, "\"weighted_exhaustive_checks\":{\"attempts\":%d,\"proved\":%d,\"disproved\":%d,\"limited\":%d,\"max_active_inputs\":20,\"word_work_limit\":4000000},\n",
        p->nWeightedTruthChecks, p->nWeightedTruthProved, p->nWeightedTruthDisproved, p->nWeightedTruthLimits);
    fprintf(f, "\"boundary_gaps\":{\"groups\":%d,\"proposals\":%d,\"closed\":%d,\"limited\":%d,\"steps\":%lld},\n", p->nGapGroups, p->nGapProposals, p->nGapClosed, p->nGapLimits, (long long)p->nGapSteps);
    fprintf(f, "\"product_grid_checks\":{\"attempts\":%d,\"proved\":%d,\"prefixes\":%d,\"limited\":%d,\"cache_hits\":%d,\"cache_storage_limits\":%d},\n", p->nGridAttempts, p->nGridProved, p->nGridPrefixes, p->nGridLimits, p->nGridProofHits, p->nGridProofCacheLimits);
    fprintf(f, "\"product_grid_partial_runs\":{\"attempts\":%d,\"proved\":%d,\"limited\":%d},\n", p->nGridLowAttempts, p->nGridLowProved, p->nGridLowLimits);
    fprintf(f, "\"product_grid_local_cuts\":{\"attempts\":%d,\"proved\":%d,\"limited\":%d},\n", p->nGridLocalChecks, p->nGridLocalProved, p->nGridLocalLimits);
    fprintf(f, "\"product_grid_partitions\":{\"attempts\":%d,\"pieces\":%d,\"proved\":%d,\"limited\":%d,\"graph_work\":%llu},\n",
        p->nGridPartitionAttempts, p->nGridPartitionParts, p->nGridPartitionProved, p->nGridPartitionLimits, (unsigned long long)p->nGridPartitionWork);
    fprintf(f, "\"implicit_carry_chains\":{\"attempts\":%d,\"proved\":%d,\"steps\":%d,\"limits\":%d,\"discovery_work\":%llu},\n",
        p->nGridChainAttempts, p->nGridChainProved, p->nGridChainSteps, p->nGridChainLimits, (unsigned long long)p->nGridChainWork);
    fprintf(f, "\"unproved_product_candidates\":"); Acec2_PrintGapProducts(p, f, 1); fprintf(f, ",\n");
    fprintf(f, "\"expression_statistics\":{\"products\":%d,\"limited\":%d,\"product_leaf_limits\":%d,\"extra_leaves_per_region\":128},\n\"expressions\":[", p->nProducts, p->nExprLimits, p->nProductLeafLimits);
    Vec_PtrForEachEntry(Acec2_Expr_t *, p->vExpressions, e, i)
    {
        w = Acec2_Word(p, e->Tree);
        fprintf(f, "%s{\"region\":%d,\"width\":%d,\"word\":%d,\"word_width\":%d,\"products\":[", i ? ",\n" : "", e->Tree, e->Width,
            Vec_IntEntry(p->vTreeWord, e->Tree), w ? Abc_MinInt(w->Width, e->Width) : 0);
        Vec_PtrForEachEntry(Acec2_Product_t *, e->vProducts, product, j)
        {
            fprintf(f, "%s{\"shift\":%d,\"negated\":%s,\"signed\":[%s,%s],\"operand_literals\":[", j ? "," : "", product->Shift, product->fNeg ? "true" : "false",
                product->fSigned[0] ? "true" : "false", product->fSigned[1] ? "true" : "false");
            for ( side = 0; side < 2; side++ )
            {
                fprintf(f, "%s[", side ? "," : "");
                Acec2_WriteList(f, product->vOperands[side], 1, 0);
                fprintf(f, "]");
            }
            fprintf(f, "]}");
        }
        fprintf(f, "],\"addends\":"); Acec2_JsonPairs(f, e->vAddends);
        fprintf(f, ",\"constant_bits\":[");
        Acec2_WriteList(f, e->vConstant, 1, 0);
        fprintf(f, "]}");
    }
    fprintf(f, "],\n\"counter_statistics\":{\"cut_proposals\":%d,\"fanout_edges\":%d,\"effort_limits\":%d,\"boundary_extensions\":%d,\"boundary_proved\":%d,\"cut_input_limit\":6,\"proposal_limit\":%d,\"edge_limit\":%d,\"closure_node_limit\":512,\"source_requests\":%d,\"source_work\":%d,\"imported_records\":%d},\n\"general_counters\":", p->nCounterCuts, p->nCounterSteps, p->nCounterLimits, p->nCounterBridgeChecks, p->nCounterBridges, p->nCounterCutLimit, p->nCounterStepLimit, p->nCounterRequests, p->nCounterWork, p->nCounterRecords);
    Acec2_CountersWriteJson(p, f);
    fprintf(f, ",\n\"component_records\":"); Acec2_RecordWriteJson(p, f);
    fprintf(f, ",\n\"private_parity_relations\":[");
    for ( i = 0; i < Vec_IntSize(p->vVanish); i += 5 )
        fprintf(f, "%s[%d,%d,%d,%d,%d]", i ? "," : "", Vec_IntEntry(p->vVanish, i), Vec_IntEntry(p->vVanish, i+1),
            Vec_IntEntry(p->vVanish, i+2), Vec_IntEntry(p->vVanish, i+3), Vec_IntEntry(p->vVanish, i+4));
    fprintf(f, "]");
    fprintf(f, ",\n\"polynomial\":{\"status\":\"%s\",\"terms\":%d,\"peak\":%d,\"carry_recurrences\":%d,\"probes\":%d,\"source_records\":%d,\"product\":",
        p->nPolyStatus == 1 ? "complete" : p->nPolyStatus ? "limited" : "not_run", p->nPolyTerms, p->nPolyPeak, p->nPolyCarries, p->nPolyProbes, p->nPolyRecords);
    if ( !p->vOperands[0] ) fprintf(f, "null");
    else
    {
        fprintf(f, "{\"width\":%d,\"source_records\":%d,\"signed\":[%s,%s],\"operand_ci_indices\":[", p->nPolyWidth, p->nPolyRecords,
            p->fPolySigned[0] ? "true" : "false", p->fPolySigned[1] ? "true" : "false");
        for ( i = 0; i < 2; i++ )
        {
            fprintf(f, "%s[", i ? "," : "");
            Acec2_WriteList(f, p->vOperands[i], 1, 0);
            fprintf(f, "]");
        }
        fprintf(f, "]}");
    }
    fprintf(f, "}\n}\n");
    Vec_IntFree(vHeights);
    return !ferror(f);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
