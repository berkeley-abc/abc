/**************************************************************************************************
GipSAT -- C port of the GipSAT solver from the rIC3 model checker (https://github.com/gipsyh/rIC3),
ported from rIC3 v1.5.2-60-g4a97bec, src/gipsat/.
Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved.
Ported to C for ABC by Wish, 2026.

rIC3 is distributed under the GNU General Public License v3. This port is distributed as part of
ABC under the ABC license (see copyright.txt in the ABC root) with the explicit permission of the
rIC3 author.
**************************************************************************************************/

#include "gipsat.h"

ABC_NAMESPACE_IMPL_START

#define GIP_MARK_UNSEEN     0
#define GIP_MARK_SEEN       1
#define GIP_MARK_REMOVABLE  2
#define GIP_MARK_FAILED     3

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline int  Gip_Seen( Gip_Solver_t * p, int Lit )   { return p->pMark[Gip_LitVar(Lit)] != GIP_MARK_UNSEEN; }
static inline void Gip_See( Gip_Solver_t * p, int Lit )    { p->pMark[Gip_LitVar(Lit)] = GIP_MARK_SEEN; Vec_IntPush(p->vClear, Lit); }
static inline void Gip_MarkAs( Gip_Solver_t * p, int Lit, int m ) { p->pMark[Gip_LitVar(Lit)] = (char)m; Vec_IntPush(p->vClear, Lit); }
static inline void Gip_ClearMarks( Gip_Solver_t * p )
{
    int i, Lit;
    Vec_IntForEachEntry( p->vClear, Lit, i )
        p->pMark[Gip_LitVar(Lit)] = GIP_MARK_UNSEEN;
    Vec_IntClear( p->vClear );
}

/**Function*************************************************************

  Synopsis    [Checks whether a learnt literal is redundant.]

  Description [Iterative DFS over reason clauses with an explicit stack
  of (lit, resume index) pairs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Gip_SolverLitRedundant( Gip_Solver_t * p, int Lit )
{
    Vec_Int_t * vStack = p->vAnaStack;   // pairs (lit, idx)
    if ( p->pReason[Gip_LitVar(Lit)] == GIP_CREF_NONE )
        return 0;
    Vec_IntClear( vStack );
    Vec_IntPushTwo( vStack, Lit, 1 );
    while ( Vec_IntSize(vStack) > 0 )
    {
        int b = Vec_IntPop( vStack );
        int q = Vec_IntPop( vStack );
        int Cref = p->pReason[Gip_LitVar(q)];
        int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
        int nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
        int i, fDescend = 0;
        for ( i = b; i < nLits; i++ )
        {
            int l = pLits[i];
            int m = p->pMark[Gip_LitVar(l)];
            if ( p->pLevel[Gip_LitVar(l)] == 0 || m == GIP_MARK_SEEN || m == GIP_MARK_REMOVABLE )
                continue;
            if ( p->pReason[Gip_LitVar(l)] == GIP_CREF_NONE || m == GIP_MARK_FAILED )
            {
                int j;
                Vec_IntPushTwo( vStack, q, 0 );
                for ( j = 0; j < Vec_IntSize(vStack); j += 2 )
                {
                    int sl = Vec_IntEntry( vStack, j );
                    if ( p->pMark[Gip_LitVar(sl)] == GIP_MARK_UNSEEN )
                        Gip_MarkAs( p, sl, GIP_MARK_FAILED );
                }
                return 0;
            }
            Vec_IntPushTwo( vStack, q, i + 1 );
            Vec_IntPushTwo( vStack, l, 1 );
            fDescend = 1;
            break;
        }
        if ( fDescend )
            continue;
        if ( p->pMark[Gip_LitVar(q)] == GIP_MARK_UNSEEN )
            Gip_MarkAs( p, q, GIP_MARK_REMOVABLE );
    }
    return 1;
}

static void Gip_SolverMinimalLearnt( Gip_Solver_t * p, Vec_Int_t * vLearnt )
{
    int i, now = 1;
    for ( i = 1; i < Vec_IntSize(vLearnt); i++ )
        if ( !Gip_SolverLitRedundant(p, Vec_IntEntry(vLearnt, i)) )
            Vec_IntWriteEntry( vLearnt, now++, Vec_IntEntry(vLearnt, i) );
    Vec_IntShrink( vLearnt, now );
}

/**Function*************************************************************

  Synopsis    [1-UIP conflict analysis.]

  Description [Fills vLearnt (first literal is the asserting one, second
  has the max level) and returns the backtrack level.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverAnalyze( Gip_Solver_t * p, int Conflict, Vec_Int_t * vLearnt )
{
    int path = 0;
    int trailIdx = Vec_IntSize( p->vTrail ) - 1;
    int resolveLit = -1;
    int i, btl;
    Vec_IntClear( vLearnt );
    Vec_IntPush( vLearnt, 0 );   // placeholder for the asserting literal
    while ( 1 )
    {
        int * pLits, nLits, begin, tl;
        Gip_CdbBump( &p->Cdb, Conflict );
        pLits = Gip_ClaLits( &p->Cdb.Alloc, Conflict );
        nLits = Gip_ClaLen( &p->Cdb.Alloc, Conflict );
        begin = resolveLit != -1 ? 1 : 0;
        for ( i = begin; i < nLits; i++ )
        {
            int Lit = pLits[i];
            int Var = Gip_LitVar( Lit );
            if ( !Gip_Seen(p, Lit) && p->pLevel[Var] > 0 )
            {
                if ( Var != p->constrainAct )
                    Gip_VsidsBump( &p->Vsids, Var );
                p->pMark[Var] = GIP_MARK_SEEN;   // no clear-list push (cleared below)
                if ( p->pLevel[Var] >= (unsigned)Gip_SolverLevelOf(p) )
                    path++;
                else
                    Vec_IntPush( vLearnt, Lit );
            }
        }
        while ( !Gip_Seen(p, Vec_IntEntry(p->vTrail, trailIdx)) )
            trailIdx--;
        tl = Vec_IntEntry( p->vTrail, trailIdx );
        p->pMark[Gip_LitVar(tl)] = GIP_MARK_UNSEEN;
        resolveLit = tl;
        path--;
        if ( path == 0 )
            break;
        Conflict = p->pReason[Gip_LitVar(tl)];
    }
    Vec_IntWriteEntry( vLearnt, 0, Gip_LitNot(resolveLit) );
    for ( i = 0; i < Vec_IntSize(vLearnt); i++ )
        Vec_IntPush( p->vClear, Vec_IntEntry(vLearnt, i) );
    Gip_SolverMinimalLearnt( p, vLearnt );
    Gip_ClearMarks( p );
    // backtrack level = second-highest level; swap it into position 1
    if ( Vec_IntSize(vLearnt) == 1 )
        btl = 0;
    else
    {
        int maxIdx = 1;
        for ( i = 2; i < Vec_IntSize(vLearnt); i++ )
            if ( p->pLevel[Gip_LitVar(Vec_IntEntry(vLearnt, i))] >
                 p->pLevel[Gip_LitVar(Vec_IntEntry(vLearnt, maxIdx))] )
                maxIdx = i;
        {
            int t = Vec_IntEntry( vLearnt, 1 );
            Vec_IntWriteEntry( vLearnt, 1, Vec_IntEntry(vLearnt, maxIdx) );
            Vec_IntWriteEntry( vLearnt, maxIdx, t );
        }
        btl = (int)p->pLevel[Gip_LitVar(Vec_IntEntry(vLearnt, 1))];
    }
    return btl;
}

/**Function*************************************************************

  Synopsis    [Unsat core extraction when an assumption is falsified.]

  Description [Walks the trail backwards from the top to the first
  assumption position, collecting decision/assumption literals reachable
  from the falsified assumption.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverAnalyzeUnsatCore( Gip_Solver_t * p, int Lit )
{
    int i;
    Gip_LitSetClear( &p->UnsatCore );
    Gip_LitSetInsert( &p->UnsatCore, Lit );
    if ( Gip_SolverLevelOf(p) == 0 )
        return;
    Gip_See( p, Lit );
    for ( i = Vec_IntSize(p->vTrail) - 1; i >= Vec_IntEntry(p->vPosInTrail, 0); i-- )
    {
        int pl = Vec_IntEntry( p->vTrail, i );
        if ( !Gip_Seen(p, pl) )
            continue;
        if ( p->pReason[Gip_LitVar(pl)] != GIP_CREF_NONE )
        {
            int Cref = p->pReason[Gip_LitVar(pl)];
            int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
            int nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
            int j;
            for ( j = 1; j < nLits; j++ )
                if ( p->pLevel[Gip_LitVar(pLits[j])] > 0 )
                    Gip_See( p, pLits[j] );
        }
        else
            Gip_LitSetInsert( &p->UnsatCore, pl );
    }
    Gip_ClearMarks( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
