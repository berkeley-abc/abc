/**CFile****************************************************************

  FileName    [giaScmap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [SCMap: shared-cover technology mapping aware of buffering and sizing.]

  Description [Cuts and matches as in &nf; a seed cover built with fixed
  rise/fall arc costs (giaScmapSeed.h); an electrical model of the Liberty
  library (fitted arcs, each net's load through its best size and buffer
  tree); refinement of the cover over that model (giaScmapRefine.h); and,
  for -q, -r and -t, seed selection and windows measured after buffering
  (giaScmapQuality.h, giaScmapWindow.c). The cut enumeration and matching
  are derived from &nf (giaNf.c) by Alan Mishchenko.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 2026.]

  Revision    [$Id: giaScmap.c,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

// Preserve separately rounded timing costs. Fusing multiply-adds can change
// near-tied cover choices and their downstream sizing trajectories.
#if defined(__clang__)
#  pragma clang fp contract(off)
#elif defined(__GNUC__)
#  pragma GCC optimize ("fp-contract=off")
#elif defined(_MSC_VER)
#  pragma fp_contract(off)
#endif

#include <float.h>
#include "giaScmapInt.h"
#include "giaEdit.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"
#include "misc/util/utilTruth.h"
#include "base/main/main.h"
#include "misc/vec/vecMem.h"
#include "misc/vec/vecWec.h"
#include "map/scl/sclCon.h"
#include "map/scl/sclLib.h"
#include "map/scl/sclSize.h"

ABC_NAMESPACE_IMPL_START
typedef struct Scm_Par_t_ Scm_Par_t;
struct Scm_Par_t_
{
    int            fVerbose;           // -v
    int            fQuality;           // -q, -r, -t: rise/fall loads, larger budgets, both seeds refined
    float          SeedLoad;           // common-load seed: load in input capacitances (gain / 100)
    float          MapDelayTarget;     // -t: delay target in ps, zero otherwise
    float          ModelDelayTarget;   // -t: that target in the electrical model's units
    Scm_Qor_t      Quality;            // measured area and delay of the selected cover
};

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define SCM_LEAF_MAX  6               // cut leaves and cell pins
#define SCM_CUT_NUM   16              // cuts kept per node, the trivial cut included
#define SCM_NO_LEAF   31
#define SCM_NO_FUNC   0x3FFFFFF
#define SCM_EPSILON   0.001           // area-flow tolerance of the cut order
// Refinement treats a path as critical above this percentage of the delay target.
enum { SCM_CRITICAL_PCT = 80 };
// Rounds of the restructuring loop (in each of the two searches of -t).
enum { SCM_LOOP_ROUNDS = 3 };

typedef struct Scm_Cut_t_ Scm_Cut_t;
struct Scm_Cut_t_
{
    word            Sign;           // signature
    int             Delay;          // delay
    float           Flow;           // flow
    unsigned        iFunc   : 26;   // function (SCM_NO_FUNC)
    unsigned        Useless :  1;   // no cell matches the function
    unsigned        nLeaves :  5;   // leaf number (SCM_NO_LEAF)
    int             pLeaves[SCM_LEAF_MAX+1]; // leaves
};
typedef struct Scm_Cfg_t_ Scm_Cfg_t;
struct Scm_Cfg_t_
{
    unsigned        fCompl  :  1;   // complemented
    unsigned        Phase   :  7;   // match phase
    unsigned        Perm    : 24;   // match permutation
};
typedef struct Scm_Mat_t_ Scm_Mat_t;
struct Scm_Mat_t_
{
    unsigned        Gate    : 20;   // gate
    unsigned        CutH    : 10;   // cut handle
    unsigned        fCompl  :  1;   // an inverter on the other phase
    Scm_Cfg_t       Cfg;            // input literals
};
typedef struct Scm_Obj_t_ Scm_Obj_t;
struct Scm_Obj_t_
{
    Scm_Mat_t       M[2];           // the selected match of each phase
};
typedef struct Scm_Arc_t_ Scm_Arc_t;
struct Scm_Arc_t_
{
    // A fitted cell pin arc in ps and fF: delay = Delay0 + DelayLoad * load + DelaySlew * input slew,
    // output slew = Slew0 + SlewLoad * load. The mean of the two output transitions selects sizes
    // and buffer trees; the transitions themselves (Rf*, fall first) time the cover.
    float           Delay0;
    float           DelayLoad;
    float           DelaySlew;
    float           Slew0;
    float           SlewLoad;
    float           RfDelay0[2];
    float           RfDelayLoad[2];
    float           RfDelaySlew[2];
    float           RfSlew0[2];
    float           RfSlewLoad[2];
    unsigned char   TimingSense;
    unsigned char   fValid;
};
// A segment of a piecewise-linear function of the load: Offset + Slope * load on [Lo, Hi].
typedef struct Scm_Seg_t_ Scm_Seg_t;
struct Scm_Seg_t_
{
    float           Lo;
    float           Hi;
    float           Offset;
    float           Slope;
};
typedef struct Scm_Pwl_t_ Scm_Pwl_t;
struct Scm_Pwl_t_
{
    Scm_Seg_t *     pSegs;
    int             nSegs;
    int             nAlloc;
};
enum { SCM_FALL = 0, SCM_RISE = 1 };
// One path of a residual tail, per transition of its literal: Constant + SlewCoeff * slew, where Valid.
typedef struct Scm_RfLine_t_ Scm_RfLine_t;
struct Scm_RfLine_t_
{
    float           Constant[2];
    float           SlewCoeff[2];
    unsigned char   Valid[2];
};
// A residual tail: the delay from a literal to the outputs, the maximum over its paths.
typedef struct Scm_RfLines_t_ Scm_RfLines_t;
struct Scm_RfLines_t_
{
    Scm_RfLine_t *  pFans;
    int             nFans;
    int             nAlloc;
};

typedef struct Scm_Man_t_ Scm_Man_t;
struct Scm_Man_t_
{
    // Cuts, matches and the selected cover.
    Gia_Man_t *     pGia;
    Vec_Int_t *     vMappingOld;    // the cell mapping the GIA came with; restored unless a new cover is derived
    Scm_Par_t *     pPars;
    Vec_Mem_t *     vTtMem;         // cut functions
    Vec_Wec_t *     vTt2Match;      // per function: matching cells and configurations
    Mio_Cell2_t *   pCells;         // GENLIB cells: 0 and 1 constants, 2 buffer, 3 inverter
    int             nCells;
    Scm_Obj_t *     pObjs;          // per node: the selected matches
    Vec_Ptr_t       vPages;         // cut storage
    Vec_Int_t       vCutSets;       // per node: its cuts
    Vec_Int_t       vMapRefs;       // per literal: references in the cover
    Vec_Flt_t       vFlowRefs;      // per literal: area-flow references
    Vec_Flt_t       vCutFlows;
    Vec_Int_t       vCutDelays;
    Vec_Int_t       vBackup;
    int             iCur;
    word            InvAreaW;
    float           InvAreaF;

    // Liberty arcs, the electrical model and refinement state.
    SC_Lib *        pScl;
    int *           pSclCells;      // per cell: its Liberty cell, -1 if none
    float           AveInputCap;    // average family pin capacitance
    float           UnitDelay;      // the delay unit of the unit-delay blend
    float           AveSlew;        // the library's average slew: the input slew of size/buffer selection
    Scm_Pwl_t *     pEnvDelays;     // per cell pin and transition: delay at a load through its best size/buffer tree
    Scm_Pwl_t *     pEnvSlews;      // per cell and transition: output slew of the same choice
    Scm_Pwl_t *     pEnvCosts;      // per cell: extra area of that choice
    Scm_Arc_t *     pArcFits;       // per cell pin: the family-average arc, blended with the delay unit
    float *         pFamilyCaps;    // per Liberty cell pin: family-average capacitance
    Vec_Flt_t       vLoads;         // per literal: load
    float *         pArrMax;        // per literal: the later of its rise/fall arrivals
    float *         pSlewMax;       // per literal: the larger of its rise/fall slews
    Scm_RfPair_t *  pRfArrs;        // per literal: rise/fall arrivals
    Scm_RfPair_t *  pRfSlews;       // per literal: rise/fall slews
    Scm_RfPair_t *  pRfLoads;       // per literal: rise/fall loads (-q, -r, -t)
    Scm_RfPair_t *  pFamilyRfCaps;  // per Liberty cell pin: rise/fall family capacitances (-q, -r, -t)
    float           ModelDelay;     // the cover's delay in the electrical model

    // Size/buffer envelopes, built per cell on first use, and per-call caches.
    unsigned char * pEnvState;      // per cell: 0 not built, 1 built, 2 failed
    void *          pEnvBufs;       // Scm_BufferType_t array of the buffer family
    int             nEnvBufs;
    float           EnvCap;         // the buffer's input capacitance
    int             fEnvError;
    int             fUnitView;      // the GENLIB has unit delays (plain read_lib): every fixed arc costs one unit
    Scm_Arc_t *     pFitCache;      // per Liberty cell pin: its arc fitted on its own grid
    unsigned char * pFitState;      // 0 not computed, 1 fitted, 2 failed
    // Per-literal fanout, tail and arc-cache arrays of the last refinement
    // context, kept with their capacity for the next context of this call.
    struct Scm_Ctx_t_ * pCtxSpare;
};

static inline int           Scm_Cfg2Int( Scm_Cfg_t Mat )                       { union { int x; Scm_Cfg_t y; } v; v.y = Mat; return v.x;         }
static inline Scm_Cfg_t     Scm_Int2Cfg( int Int )                             { union { int x; Scm_Cfg_t y; } v; v.x = Int; return v.y;         }

static inline Scm_Obj_t *   Scm_ManObj( Scm_Man_t * p, int i )                 { return p->pObjs + i;                                            }
static inline Mio_Cell2_t * Scm_ManCell( Scm_Man_t * p, int i )                { return p->pCells + i;                                           }
static inline int *         Scm_ManCutSet( Scm_Man_t * p, int i )              { return (int *)Vec_PtrEntry(&p->vPages, i >> 16) + (i & 0xFFFF); }
static inline int           Scm_ObjCutSetId( Scm_Man_t * p, int i )            { return Vec_IntEntry( &p->vCutSets, i );                         }
static inline int *         Scm_ObjCutSet( Scm_Man_t * p, int i )              { return Scm_ManCutSet(p, Scm_ObjCutSetId(p, i));                 }
static inline int           Scm_ObjHasCuts( Scm_Man_t * p, int i )             { return (int)(Vec_IntEntry(&p->vCutSets, i) > 0);                }

static inline int           Scm_ObjCutUseless( Scm_Man_t * p, int TruthId )    { return (int)(TruthId >= Vec_WecSize(p->vTt2Match));             }

static inline float         Scm_ObjCutFlow( Scm_Man_t * p, int i )             { return Vec_FltEntry(&p->vCutFlows, i);                          }
static inline int           Scm_ObjCutDelay( Scm_Man_t * p, int i )            { return Vec_IntEntry(&p->vCutDelays, i);                         }
static inline void          Scm_ObjSetCutFlow( Scm_Man_t * p, int i, float a ) { Vec_FltWriteEntry(&p->vCutFlows, i, a);                         }
static inline void          Scm_ObjSetCutDelay( Scm_Man_t * p, int i, int d )  { Vec_IntWriteEntry(&p->vCutDelays, i, d);                        }

static inline int           Scm_ObjMapRefNum( Scm_Man_t * p, int i, int c )    { return Vec_IntEntry(&p->vMapRefs, Abc_Var2Lit(i,c));            }
static inline int           Scm_ObjMapRefInc( Scm_Man_t * p, int i, int c )    { return (*Vec_IntEntryP(&p->vMapRefs, Abc_Var2Lit(i,c)))++;      }
static inline int           Scm_ObjMapRefDec( Scm_Man_t * p, int i, int c )    { return --(*Vec_IntEntryP(&p->vMapRefs, Abc_Var2Lit(i,c)));      }
static inline float         Scm_ObjFlowRefs( Scm_Man_t * p, int i, int c )     { return Vec_FltEntry(&p->vFlowRefs, Abc_Var2Lit(i,c));           }

static inline Scm_Mat_t *   Scm_ObjMatch( Scm_Man_t * p, int i, int c )        { return &Scm_ManObj(p, i)->M[c];                                 }

static inline int           Scm_CutSize( int * pCut )                          { return pCut[0] & SCM_NO_LEAF;                                   }
static inline int           Scm_CutFunc( int * pCut )                          { return ((unsigned)pCut[0] >> 5);                                }
static inline int *         Scm_CutLeaves( int * pCut )                        { return pCut + 1;                                                }
static inline int           Scm_CutSetBoth( int n, int f )                     { return n | (f << 5);                                            }
static inline int           Scm_CutHandle( int * pCutSet, int * pCut )         { assert( pCut > pCutSet ); return pCut - pCutSet;                }
static inline int *         Scm_CutFromHandle( int * pCutSet, int h )          { assert( h > 0 ); return pCutSet + h;                            }

static inline int           Scm_CfgVar( Scm_Cfg_t Cfg, int i )                 { return (Cfg.Perm >> (i<<2)) & 15;                               }
static inline int           Scm_CfgCompl( Scm_Cfg_t Cfg, int i )               { return (Cfg.Phase >> i) & 1;                                    }

#define Scm_SetForEachCut( pList, pCut, i )                   for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += Scm_CutSize(pCut) + 1 )
#define Scm_CutForEachVarCompl( pCut, Cfg, iVar, fCompl, i )  for ( i = 0; i < Scm_CutSize(pCut) && (iVar = Scm_CutLeaves(pCut)[Scm_CfgVar(Cfg, i)]) && ((fCompl = Scm_CfgCompl(Cfg, i)), 1); i++ )

static void Scm_StoDelete( Scm_Man_t * p );
static void Scm_CtxFree( struct Scm_Ctx_t_ * pCtx );

/**Function*************************************************************

  Synopsis    [Returns the Liberty cell of a GENLIB cell, or NULL.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline SC_Cell * Scm_ManSclCell( Scm_Man_t * p, Mio_Cell2_t * pCell )
{
    int Id = p->pSclCells ? p->pSclCells[pCell->Id] : -1;
    return Id >= 0 ? SC_LibCell(p->pScl, Id) : NULL;
}

/**Function*************************************************************

  Synopsis    [Returns the fitted arc of a cell pin, or NULL.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Scm_Arc_t * Scm_ManArc( Scm_Man_t * p, Mio_Cell2_t * pCell, int iPin )
{
    if ( p->pArcFits == NULL || pCell->Id >= (unsigned)p->nCells || iPin < 0 || iPin >= SCM_LEAF_MAX )
        return NULL;
    return p->pArcFits + pCell->Id * SCM_LEAF_MAX + iPin;
}

/**Function*************************************************************

  Synopsis    [ABC normalizes the floating-point Liberty tables to ps/fF, but its
  integer table copies can retain the file's original units. Build
  private fixed-point tables from normalized floats for fitting. Never
  rewrite the shared library: other commands and concurrent library
  users own it. For a ps/fF library this preserves the existing fixed-
  point arithmetic.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManFitSurfaceStart( SC_Surface * pDst, SC_Surface * pSrc )
{
    Vec_Flt_t * pRow;
    int i, k;
    float Value;
    memset(pDst, 0, sizeof(*pDst));
    Vec_FltForEachEntry(&pSrc->vIndex0, Value, i)
        Vec_IntPush(&pDst->vIndex0I, Scl_Flt2Int(Value));
    Vec_FltForEachEntry(&pSrc->vIndex1, Value, i)
        Vec_IntPush(&pDst->vIndex1I, Scl_Flt2Int(Value));
    Vec_PtrForEachEntry(Vec_Flt_t *, &pSrc->vData, pRow, i)
    {
        Vec_Int_t * pFixed = Vec_IntAlloc(Vec_FltSize(pRow));
        Vec_PtrPush(&pDst->vDataI, pFixed);
        Vec_FltForEachEntry(pRow, Value, k)
            Vec_IntPush(pFixed, Scl_Flt2Int(Value));
    }
}

/**Function*************************************************************

  Synopsis    [Releases a copied timing table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManFitSurfaceStop( SC_Surface * pSurface )
{
    Vec_IntErase(&pSurface->vIndex0I);
    Vec_IntErase(&pSurface->vIndex1I);
    Vec_VecErase((Vec_Vec_t *)&pSurface->vDataI);
}

/**Function*************************************************************

  Synopsis    [Copies the delay and slew tables of a timing arc for fitting.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManFitTimingStart( SC_Timing * pDst, SC_Timing * pSrc )
{
    memset(pDst, 0, sizeof(*pDst));
    pDst->tsense = pSrc->tsense;
    Scm_ManFitSurfaceStart(&pDst->pCellRise, &pSrc->pCellRise);
    Scm_ManFitSurfaceStart(&pDst->pCellFall, &pSrc->pCellFall);
    Scm_ManFitSurfaceStart(&pDst->pRiseTrans, &pSrc->pRiseTrans);
    Scm_ManFitSurfaceStart(&pDst->pFallTrans, &pSrc->pFallTrans);
}

/**Function*************************************************************

  Synopsis    [Releases the copied tables of a timing arc.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManFitTimingStop( SC_Timing * pTime )
{
    Scm_ManFitSurfaceStop(&pTime->pCellRise);
    Scm_ManFitSurfaceStop(&pTime->pCellFall);
    Scm_ManFitSurfaceStop(&pTime->pRiseTrans);
    Scm_ManFitSurfaceStop(&pTime->pFallTrans);
}

/**Function*************************************************************

  Synopsis    [Solves least-squares normal equations by Gaussian elimination.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManFitSolve( double Mat[3][4], int nVars )
{
    int i, j, k, Pivot;
    double Temp, Scale;
    for ( k = 0; k < nVars; k++ )
    {
        Pivot = k;
        for ( i = k + 1; i < nVars; i++ )
            if ( fabs(Mat[i][k]) > fabs(Mat[Pivot][k]) )
                Pivot = i;
        if ( fabs(Mat[Pivot][k]) < 1.0e-18 )
            return 0;
        if ( Pivot != k )
            for ( j = k; j <= nVars; j++ )
                Temp = Mat[k][j], Mat[k][j] = Mat[Pivot][j], Mat[Pivot][j] = Temp;
        Scale = Mat[k][k];
        for ( j = k; j <= nVars; j++ )
            Mat[k][j] /= Scale;
        for ( i = 0; i < nVars; i++ )
            if ( i != k )
            {
                Scale = Mat[i][k];
                for ( j = k; j <= nVars; j++ )
                    Mat[i][j] -= Scale * Mat[k][j];
            }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds one sample to least-squares normal equations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Scm_ManFitAdd( double Mat[3][4], double * pX, double Y, int nVars )
{
    int i, k;
    for ( i = 0; i < nVars; i++ )
    {
        Mat[i][nVars] += pX[i] * Y;
        for ( k = 0; k < nVars; k++ )
            Mat[i][k] += pX[i] * pX[k];
    }
}

/**Function*************************************************************

  Synopsis    [A table whose fixed-point indices strictly increase: Scl_LibLookupI()
  at a grid point then returns the stored entry exactly, so its points
  can be read from the float table directly.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManSurfaceGridOk( SC_Surface * p )
{
    int i, n0 = Vec_FltSize(&p->vIndex0), n1 = Vec_FltSize(&p->vIndex1);
    if ( Vec_PtrSize(&p->vData) != n0 ) return 0;
    for ( i = 1; i < n0; i++ ) if ( Scl_Flt2Int(Vec_FltEntry(&p->vIndex0, i)) <= Scl_Flt2Int(Vec_FltEntry(&p->vIndex0, i-1)) ) return 0;
    for ( i = 1; i < n1; i++ ) if ( Scl_Flt2Int(Vec_FltEntry(&p->vIndex1, i)) <= Scl_Flt2Int(Vec_FltEntry(&p->vIndex1, i-1)) ) return 0;
    for ( i = 0; i < n0; i++ ) if ( Vec_FltSize((Vec_Flt_t *)Vec_PtrEntry(&p->vData, i)) != n1 ) return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if Scl_LibLookupI() can interpolate at every value of the axis.]

  Description [Scl_LibLookupI() divides by the width of the segment it
  selects; this repeats its selection for each value of the axis.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManFitAxisOk( Vec_Int_t * vIndex )
{
    int * pIndex = Vec_IntArray(vIndex), n = Vec_IntSize(vIndex), i, s;
    for ( i = 0; n > 1 && i < n; i++ )
    {
        for ( s = 1; s < n-1; s++ )
            if ( pIndex[s] > pIndex[i] )
                break;
        s--;
        if ( pIndex[s+1] == pIndex[s] ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds the table's grid points in ABC's fixed-point rounding to the
  normal equations of Value = c0 + c1 * Load (+ c2 * Slew if nVars ==
  3). fFixed reads a private fixed-point copy through Scl_LibLookupI();
  otherwise the float table is read directly. Returns 0 for a one-
  dimensional table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManFitSurfaceAdd( SC_Surface * p, int fFixed, double Mat[3][4], int nVars )
{
    int nSlews = fFixed ? Vec_IntSize(&p->vIndex0I) : Vec_FltSize(&p->vIndex0);
    int nLoads = fFixed ? Vec_IntSize(&p->vIndex1I) : Vec_FltSize(&p->vIndex1);
    int i, k;
    if ( !((nSlews == 1 && nLoads == 1) || (nSlews >= 2 && nLoads >= 2)) ) return 0;
    if ( fFixed )
    {
        // Scl_LibLookupI() needs a full grid and a nonzero width of every segment it selects
        if ( Vec_PtrSize(&p->vDataI) != nSlews ) return 0;
        for ( i = 0; i < nSlews; i++ )
            if ( Vec_IntSize((Vec_Int_t *)Vec_PtrEntry(&p->vDataI, i)) != nLoads ) return 0;
        if ( !Scm_ManFitAxisOk(&p->vIndex0I) || !Scm_ManFitAxisOk(&p->vIndex1I) ) return 0;
    }
    for ( i = 0; i < nSlews; i++ )
    for ( k = 0; k < nLoads; k++ )
    {
        double X[3];
        int Slew  = fFixed ? Vec_IntEntry(&p->vIndex0I, i) : Scl_Flt2Int(Vec_FltEntry(&p->vIndex0, i));
        int Load  = fFixed ? Vec_IntEntry(&p->vIndex1I, k) : Scl_Flt2Int(Vec_FltEntry(&p->vIndex1, k));
        int Value = fFixed ? Scl_LibLookupI(p, Slew, Load) : Scl_Flt2Int(Vec_FltEntry((Vec_Flt_t *)Vec_PtrEntry(&p->vData, i), k));
        X[0] = 1.0;
        X[1] = Scl_Int2Flt(Load);
        X[2] = Scl_Int2Flt(Slew);
        Scm_ManFitAdd(Mat, X, Scl_Int2Flt(Value), nVars);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Least-squares fit of one transition on its own characterized points:
  delay linear in load and input slew, output slew linear in load. A
  constant table gives a constant.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManFitTransition( SC_Surface * pDelay, SC_Surface * pSlew, int fFixed, float Fit[5] )
{
    double DelayMat[3][4] = {{0}}, SlewMat[3][4] = {{0}};
    int fConstDelay = fFixed ? Vec_IntSize(&pDelay->vIndex0I) == 1 && Vec_IntSize(&pDelay->vIndex1I) == 1 :
                               Vec_FltSize(&pDelay->vIndex0) == 1 && Vec_FltSize(&pDelay->vIndex1) == 1;
    int fConstSlew  = fFixed ? Vec_IntSize(&pSlew->vIndex0I) == 1 && Vec_IntSize(&pSlew->vIndex1I) == 1 :
                               Vec_FltSize(&pSlew->vIndex0) == 1 && Vec_FltSize(&pSlew->vIndex1) == 1;
    if ( !Scm_ManFitSurfaceAdd(pDelay, fFixed, DelayMat, 3) || !Scm_ManFitSurfaceAdd(pSlew, fFixed, SlewMat, 2) )
        return 0;
    if ( fConstDelay )
        Fit[0] = (float)DelayMat[0][3], Fit[1] = Fit[2] = 0.0f;
    else
    {
        if ( !Scm_ManFitSolve(DelayMat, 3) ) return 0;
        Fit[0] = (float)DelayMat[0][3], Fit[1] = (float)DelayMat[1][3], Fit[2] = (float)DelayMat[2][3];
    }
    if ( fConstSlew )
        Fit[3] = (float)SlewMat[0][2], Fit[4] = 0.0f;
    else
    {
        if ( !Scm_ManFitSolve(SlewMat, 2) ) return 0;
        Fit[3] = (float)SlewMat[0][2], Fit[4] = (float)SlewMat[1][2];
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Fits one cell pin's timing arc: each transition's tables on their own
  points; the mean of the two transitions selects sizes and buffer
  trees, the transitions themselves time the cover. A table with non-
  monotone fixed-point indices is read through a private fixed-point
  copy (ABC's integer tables may keep the file's units; the shared
  library is never rewritten).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManFitArc( SC_Cell * pCell, int iPin, Scm_Arc_t * pArc )
{
    SC_Timing * pTime = Scl_CellPinTime(pCell, iPin), Fixed, * pUse;
    float Rise[5], Fall[5];
    int fFixed, fOk, t;
    if ( pTime == NULL ) return 0;
    fFixed = !(Scm_ManSurfaceGridOk(&pTime->pCellRise) && Scm_ManSurfaceGridOk(&pTime->pRiseTrans) &&
               Scm_ManSurfaceGridOk(&pTime->pCellFall) && Scm_ManSurfaceGridOk(&pTime->pFallTrans));
    if ( fFixed ) Scm_ManFitTimingStart(&Fixed, pTime);
    pUse = fFixed ? &Fixed : pTime;
    fOk = Scm_ManFitTransition(&pUse->pCellRise, &pUse->pRiseTrans, fFixed, Rise) &&
          Scm_ManFitTransition(&pUse->pCellFall, &pUse->pFallTrans, fFixed, Fall);
    if ( fFixed ) Scm_ManFitTimingStop(&Fixed);
    if ( !fOk ) return 0;
    pArc->Delay0    = 0.5f * (Rise[0] + Fall[0]);
    pArc->DelayLoad = 0.5f * (Rise[1] + Fall[1]);
    pArc->DelaySlew = 0.5f * (Rise[2] + Fall[2]);
    pArc->Slew0     = 0.5f * (Rise[3] + Fall[3]);
    pArc->SlewLoad  = 0.5f * (Rise[4] + Fall[4]);
    pArc->TimingSense = pTime->tsense;
    for ( t = 0; t < 2; t++ )
    {
        float * a = t ? Rise : Fall;
        pArc->RfDelay0[t] = a[0]; pArc->RfDelayLoad[t] = a[1]; pArc->RfDelaySlew[t] = a[2];
        pArc->RfSlew0[t] = a[3]; pArc->RfSlewLoad[t] = a[4];
    }
    pArc->fValid = 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [The same (member, pin) own-grid fit feeds the family model, the
  size/buffer envelopes and the seed.]

  Description [Compute it once per mapping call; a cached copy is identical to
  recomputing into a zeroed arc.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManFitArcCached( Scm_Man_t * p, SC_Cell * pCell, int iPin, Scm_Arc_t * pArc )
{
    int Id;
    if ( p->pScl == NULL || iPin < 0 || iPin >= SCM_LEAF_MAX ) return Scm_ManFitArc(pCell, iPin, pArc);
    if ( p->pFitCache == NULL )
    {
        p->pFitCache = ABC_CALLOC(Scm_Arc_t, SC_LibCellNum(p->pScl) * SCM_LEAF_MAX);
        p->pFitState = ABC_CALLOC(unsigned char, SC_LibCellNum(p->pScl) * SCM_LEAF_MAX);
    }
    Id = pCell->Id * SCM_LEAF_MAX + iPin;
    if ( p->pFitState[Id] == 0 )
    {
        Scm_Arc_t Arc;
        memset(&Arc, 0, sizeof(Arc));
        p->pFitState[Id] = Scm_ManFitArc(pCell, iPin, &Arc) ? 1 : 2;
        p->pFitCache[Id] = Arc;
    }
    if ( p->pFitState[Id] == 2 ) return 0;
    *pArc = p->pFitCache[Id];
    return 1;
}

/**Function*************************************************************

  Synopsis    [Fits the family-average arc of a cell pin over the usable sizes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManFamilyArc( Scm_Man_t * p, SC_Cell * pCell, int iPin, Scm_Arc_t * pArc )
{
    int i, t, Count = 0;
    double Sums[5] = {0}, Rf[2][5] = {{0}};
    SC_Cell * pMember;

    // The buffer is modeled by its representative cell (fit, input capacitance and area);
    // a logic cell by the average of its family's fits.
    if ( pCell == Scm_ManSclCell(p, p->pCells + 2) )
        return Scm_ManFitArcCached(p, pCell, iPin, pArc);
    // Each usable family member has equal weight.  Fit its rise/fall delay
    // and transition tables on their own grids, then average coefficients.
    // This runs once before mapping; emitted cells and areas are unchanged.
    SC_RingForEachCell(pCell, pMember, i)
    {
        Scm_Arc_t Arc = {0};
        if ( pMember->fSkip ) continue;
        if ( !Scm_ManFitArcCached(p, pMember, iPin, &Arc) ) return 0;
        Sums[0] += Arc.Delay0;
        Sums[1] += Arc.DelayLoad;
        Sums[2] += Arc.DelaySlew;
        Sums[3] += Arc.Slew0;
        Sums[4] += Arc.SlewLoad;
        pArc->TimingSense = Arc.TimingSense;
        for ( t = 0; t < 2; t++ )
        {
            Rf[t][0] += Arc.RfDelay0[t];
            Rf[t][1] += Arc.RfDelayLoad[t];
            Rf[t][2] += Arc.RfDelaySlew[t];
            Rf[t][3] += Arc.RfSlew0[t];
            Rf[t][4] += Arc.RfSlewLoad[t];
        }
        Count++;
    }
    if ( Count == 0 ) return 0;
    pArc->Delay0 = (float)(Sums[0] / Count);
    pArc->DelayLoad = (float)(Sums[1] / Count);
    pArc->DelaySlew = (float)(Sums[2] / Count);
    pArc->Slew0 = (float)(Sums[3] / Count);
    pArc->SlewLoad = (float)(Sums[4] / Count);
    for ( t = 0; t < 2; t++ )
    {
        pArc->RfDelay0[t]    = Rf[t][0] / Count;
        pArc->RfDelayLoad[t] = Rf[t][1] / Count;
        pArc->RfDelaySlew[t] = Rf[t][2] / Count;
        pArc->RfSlew0[t]     = Rf[t][3] / Count;
        pArc->RfSlewLoad[t]  = Rf[t][4] / Count;
    }
    pArc->fValid = 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [The unit-delay blend: a quarter of every arc delay becomes a fixed
  library delay unit (Scm_ManUnitBlend), which regularizes the fitted
  arcs toward counting stages.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ArcBlendUnit( Scm_Arc_t * a, float Unit )
{
    int t;
    a->Delay0 = 0.75f * a->Delay0 + 0.25f * Unit;
    a->DelayLoad *= 0.75f;
    a->DelaySlew *= 0.75f;
    for ( t = 0; t < 2; t++ )
    {
        a->RfDelay0[t] = 0.75f * a->RfDelay0[t] + 0.25f * Unit;
        a->RfDelayLoad[t] *= 0.75f;
        a->RfDelaySlew[t] *= 0.75f;
    }
}

/**Function*************************************************************

  Synopsis    [The delay unit is the median arc delay at the average pin load and
  slew (library data only).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManUnitBlend( Scm_Man_t * p )
{
    float * pDelays, Unit;
    int i, k, n = 0;
    pDelays = ABC_ALLOC(float, p->nCells * SCM_LEAF_MAX);
    for ( i = 0; i < p->nCells; i++ )
        for ( k = 0; k < (int)p->pCells[i].nFanins; k++ )
        {
            Scm_Arc_t * pArc = Scm_ManArc(p, p->pCells + i, k);
            pDelays[n++] = Abc_MaxFloat(1.0e-3f, pArc->Delay0 +
                pArc->DelayLoad * p->AveInputCap + pArc->DelaySlew * p->AveSlew);
        }
    for ( i = 1; i < n; i++ )
    {
        float Value = pDelays[i];
        for ( k = i; k > 0 && pDelays[k-1] > Value; k-- )
            pDelays[k] = pDelays[k-1];
        pDelays[k] = Value;
    }
    assert(n > 0);
    Unit = n > 0 ? pDelays[n/2] : 1.0f;
    p->UnitDelay = Unit;
    ABC_FREE(pDelays);
    for ( i = 0; i < p->nCells; i++ )
        for ( k = 0; k < (int)p->pCells[i].nFanins; k++ )
            Scm_ArcBlendUnit( Scm_ManArc(p, p->pCells + i, k), Unit );
}

/**Function*************************************************************

  Synopsis    [Returns the family-average input capacitance of a Liberty cell pin.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Scm_ManCellPinCap( Scm_Man_t * p, SC_Cell * pCell, int iPin )
{
    return p->pFamilyCaps[pCell->Id * SCM_LEAF_MAX + iPin];
}

/**Function*************************************************************

  Synopsis    [Returns the family-average input capacitance of the inverter.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Scm_ManInvInputCap( Scm_Man_t * p )
{
    SC_Cell * pSclCell = Scm_ManSclCell( p, p->pCells + 3 );
    return pSclCell ? Scm_ManCellPinCap(p, pSclCell, 0) : 0.0;
}

/**Function*************************************************************

  Synopsis    [Checks that a match configuration uses every cut leaf once.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CfgIsCutPermutation( Scm_Cfg_t Cfg, int nFans )
{
    unsigned Seen = 0;
    int i, iVar;
    for ( i = 0; i < nFans; i++ )
    {
        iVar = Scm_CfgVar( Cfg, i );
        if ( iVar >= nFans || (Seen & (1u << iVar)) )
            return 0;
        Seen |= 1u << iVar;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks that the leaves of a cut precede its root.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CutLeavesAreValid( int * pFans, int nFans, int iRoot )
{
    int i;
    for ( i = 0; i < nFans; i++ )
        // A cut is topological: a leaf cannot be the root itself or a
        // later GIA object.  The latter would otherwise survive a mere
        // array-bounds check and can make the derived cell map cyclic.
        if ( pFans[i] < 0 || pFans[i] >= iRoot )
            return 0;
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static int Scm_ManEnvStart( Scm_Man_t * p );

/**Function*************************************************************

  Synopsis    [Recovers the gain of read_lib -G's GENLIB.]

  Description [read_lib -G derives every pin delay as the class-average delay at
  that gain and the library's average slew, written with two decimals. Returns
  the gain that reproduces every pin delay of the loaded GENLIB (an integer or a
  half, found by bisection on the inverter), or 0 if none does (a GENLIB read
  with read_genlib, or derived with an explicit slew).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
extern float Abc_SclComputeDelayClassPin( SC_Lib *, SC_Cell *, int, float, float );

/**Function*************************************************************

  Synopsis    [Computes a pin delay as read_lib -G writes it into the GENLIB.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManGenlibDelay( SC_Lib * pScl, SC_Cell * pCell, int iPin, float Slew, float Gain )
{
    char Buffer[64];
    double Delay;
    snprintf( Buffer, sizeof(Buffer), "%7.2f", Abc_SclComputeDelayClassPin(pScl, pCell, iPin, Slew, Gain) );
    Delay = atof( Buffer );
    return (int)(SCL_NUM/2 * Delay + SCL_NUM/2 * Delay);   // as Mio_Cell2_t iDelays from a GENLIB pin
}

/**Function*************************************************************

  Synopsis    [Recovers the gain of read_lib -G from the GENLIB delays; 0 if none
  fits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_ManGenlibGain( Scm_Man_t * p )
{
    SC_Cell * pInv = Scm_ManSclCell(p, p->pCells + 3);
    float Slew = p->AveSlew, Lo = 1, Hi = 10000, Mid, Gain;
    int Target = p->pCells[3].iDelays[0], i, k, n;
    if ( pInv == NULL || Scm_ManGenlibDelay(p->pScl, pInv, 0, Slew, Lo) > Target ||
         Scm_ManGenlibDelay(p->pScl, pInv, 0, Slew, Hi) < Target ) return 0;
    for ( n = 0; n < 64 && Hi - Lo > 0.01f; n++ )   // the smallest gain reaching the inverter's delay
    {
        Mid = 0.5f * (Lo + Hi);
        if ( Scm_ManGenlibDelay(p->pScl, pInv, 0, Slew, Mid) < Target ) Lo = Mid; else Hi = Mid;
    }
    for ( Gain = 0.5f * ceilf(2 * Lo); Gain <= Hi + 50; Gain += 0.5f )
    {
        if ( Scm_ManGenlibDelay(p->pScl, pInv, 0, Slew, Gain) > Target ) break;
        for ( i = 2; i < p->nCells; i++ )
        {
            SC_Cell * pCell = Scm_ManSclCell(p, p->pCells + i);
            if ( pCell == NULL || !p->pCells[i].nFanins ) continue;
            for ( k = 0; k < (int)p->pCells[i].nFanins; k++ )
                if ( Scm_ManGenlibDelay(p->pScl, pCell, k, Slew, Gain) != p->pCells[i].iDelays[k] ) break;
            if ( k < (int)p->pCells[i].nFanins ) break;
        }
        if ( i == p->nCells ) return Gain;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Starts the mapping manager: library, fitted arcs and cut storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Man_t * Scm_StoCreate( Gia_Man_t * pGia, Scm_Par_t * pPars )
{
    extern void Mf_ManSetFlowRefs( Gia_Man_t * p, Vec_Int_t * vRefs );
    Vec_Int_t * vFlowRefs;
    Scm_Man_t * p;
    SC_Cell * pSclCell, * pMember;
    float Gain = 0;
    int i, k, Entry, nPins = 0, nFailed = 0, nLits = 2 * Gia_ManObjNum(pGia);
    ABC_FREE( pGia->pRefs );
    if ( Gia_ManHasChoices(pGia) )
        Gia_ManSetPhase(pGia);
    p = ABC_CALLOC( Scm_Man_t, 1 );
    p->pGia     = pGia;
    // Set the incumbent mapping aside; Scm_StoDelete() restores it unless a new cover replaced it.
    p->vMappingOld = pGia->vCellMapping;
    pGia->vCellMapping = NULL;
    p->pPars    = pPars;
    p->pObjs    = ABC_CALLOC( Scm_Obj_t, Gia_ManObjNum(pGia) );
    p->iCur     = 2;
    Vec_PtrGrow( &p->vPages, 256 );
    Vec_IntFill( &p->vMapRefs,  2*Gia_ManObjNum(pGia), 0 );
    Vec_FltFill( &p->vFlowRefs, 2*Gia_ManObjNum(pGia), 0 );
    Vec_IntFill( &p->vCutSets,  Gia_ManObjNum(pGia), 0 );
    Vec_FltFill( &p->vCutFlows, Gia_ManObjNum(pGia), 0 );
    Vec_IntFill( &p->vCutDelays,Gia_ManObjNum(pGia), 0 );
    Vec_IntGrow( &p->vBackup, 1000 );
    vFlowRefs = Vec_IntAlloc(0);
    Mf_ManSetFlowRefs( pGia, vFlowRefs );
    Vec_IntForEachEntry( vFlowRefs, Entry, i )
    {
        Vec_FltWriteEntry( &p->vFlowRefs, 2*i,   Entry );
        Vec_FltWriteEntry( &p->vFlowRefs, 2*i+1, Entry );
    }
    Vec_IntFree(vFlowRefs);
    Mio_LibraryMatchesFetch( (Mio_Library_t *)Abc_FrameReadLibGen(),
        &p->vTtMem, &p->vTt2Match, &p->pCells, &p->nCells,
        0, 0, 0 );
    if ( p->pCells == NULL )
    {
        Scm_StoDelete(p);
        return NULL;
    }
    p->pScl = (SC_Lib *)Abc_FrameReadLibScl();
    if ( p->pScl == NULL )
    {
        Abc_Print( -1, "&scmap requires a Liberty library loaded with read_lib.\n" );
        Scm_StoDelete( p );
        return NULL;
    }
    p->AveSlew = Abc_SclComputeAverageSlew(p->pScl);
    p->pSclCells = ABC_ALLOC( int, p->nCells );
    p->pFamilyCaps = ABC_CALLOC(float, SC_LibCellNum(p->pScl) * SCM_LEAF_MAX);
    if ( pPars->fQuality )
        p->pFamilyRfCaps = ABC_CALLOC(Scm_RfPair_t, SC_LibCellNum(p->pScl) * SCM_LEAF_MAX);
    // family-average pin capacitances (-q weights each size by its inverse area); the buffer keeps its own
    for ( i = 0; i < p->nCells; i++ )
    {
        double Weight = 0, Caps[SCM_LEAF_MAX] = {0}, Fall[SCM_LEAF_MAX] = {0}, Rise[SCM_LEAF_MAX] = {0};
        p->pSclCells[i] = p->pCells[i].pName ?
            Abc_SclCellFind(p->pScl, p->pCells[i].pName) : -1;
        if ( p->pSclCells[i] < 0 )
            continue;
        pSclCell = SC_LibCell(p->pScl, p->pSclCells[i]);
        // A Liberty cell with other pins than the GENLIB cell is not a match; its arcs are reported below.
        if ( pSclCell->n_inputs != (int)p->pCells[i].nFanins )
        {
            p->pSclCells[i] = -1;
            continue;
        }
        assert(pSclCell->n_inputs <= SCM_LEAF_MAX);
        SC_RingForEachCell(pSclCell, pMember, k)
        {
            double W;
            if ( pMember->fSkip ) continue;
            W = pPars->fQuality && pMember->area > 0 ? 1.0 / pMember->area : 1.0;
            Weight += W;
            for ( Entry = 0; Entry < pMember->n_inputs; Entry++ )
            {
                Caps[Entry] += W * SC_CellPinCap(pMember, Entry);
                Fall[Entry] += W * SC_CellPin(pMember, Entry)->fall_cap;
                Rise[Entry] += W * SC_CellPin(pMember, Entry)->rise_cap;
            }
        }
        if ( Weight == 0 )
        {
            Scm_StoDelete(p);
            return NULL;
        }
        for ( Entry = 0; Entry < pSclCell->n_inputs; Entry++ )
            p->pFamilyCaps[pSclCell->Id * SCM_LEAF_MAX + Entry] =
                i == 2 ? SC_CellPinCap(pSclCell, Entry) : (float)(Caps[Entry] / Weight);
        if ( p->pFamilyRfCaps )
            for ( Entry = 0; Entry < pSclCell->n_inputs; Entry++ )
            {
                Scm_RfPair_t * pCap = p->pFamilyRfCaps + pSclCell->Id * SCM_LEAF_MAX + Entry;
                pCap->Value[0] = i == 2 ? SC_CellPin(pSclCell, Entry)->fall_cap : (float)(Fall[Entry] / Weight);
                pCap->Value[1] = i == 2 ? SC_CellPin(pSclCell, Entry)->rise_cap : (float)(Rise[Entry] / Weight);
            }
        for ( Entry = 0; Entry < pSclCell->n_inputs; Entry++ )
            p->AveInputCap += Scm_ManCellPinCap(p, pSclCell, Entry), nPins++;
    }
    p->AveInputCap /= Abc_MaxInt(1, nPins);
    if ( p->pSclCells[3] < 0 )
    {
        Abc_Print( -1, "&scmap cannot match inverter %s in the Liberty library.\n", p->pCells[3].pName );
        Scm_StoDelete( p );
        return NULL;
    }
    Vec_FltFill( &p->vLoads, nLits, 0.0f );
    p->pArcFits = ABC_CALLOC( Scm_Arc_t, p->nCells * SCM_LEAF_MAX );
    for ( i = 0; i < p->nCells; i++ )
    {
        Mio_Cell2_t * pMioCell = p->pCells + i;
        if ( pMioCell->nFanins == 0 )
            continue;
        pSclCell = Scm_ManSclCell(p, pMioCell);
        if ( pSclCell == NULL || pMioCell->nFanins != pSclCell->n_inputs )
        {
            nFailed += pMioCell->nFanins;
            continue;
        }
        for ( Entry = 0; Entry < (int)pMioCell->nFanins; Entry++ )
            nFailed += !Scm_ManFamilyArc(p, pSclCell, Entry, Scm_ManArc(p, pMioCell, Entry));
    }
    if ( nFailed )
    {
        Abc_Print( -1, "&scmap could not fit %d Liberty timing arcs.\n", nFailed );
        Scm_StoDelete( p );
        return NULL;
    }
    Scm_ManUnitBlend(p);
    if ( !Scm_ManEnvStart(p) )
    {
        Abc_Print( -1, "&scmap could not construct the buffered library responses.\n" );
        Scm_StoDelete( p );
        return NULL;
    }
    p->pArrMax = ABC_CALLOC( float, nLits );
    p->pSlewMax = ABC_CALLOC( float, nLits );
    // A GENLIB whose pins all have one delay (plain read_lib's unit-delay library) selects the unit view:
    // the fixed-arc seed costs are one unit and a single seed is built. read_lib -G keeps the gain view.
    p->fUnitView = 1;
    for ( i = 2; i < p->nCells && p->fUnitView; i++ )
        for ( k = 0; k < (int)p->pCells[i].nFanins; k++ )
            if ( p->pCells[i].iDelays[k] != p->pCells[3].iDelays[0] ) { p->fUnitView = 0; break; }
    // In the gain view the common-load seed uses read_lib -G's gain as its load ratio (2.5 for -G 250, and when
    // the gain is not recognized).
    if ( !p->fUnitView )
    {
        Gain = Scm_ManGenlibGain(p);
        if ( Gain > 0 ) pPars->SeedLoad = Gain / 100;
    }
    if ( pPars->fVerbose )
    {
        if ( p->fUnitView ) Abc_Print( 1, "SCMAP_VIEW unit-delay GENLIB: every fixed-arc cost is one unit, one seed\n" );
        else if ( Gain > 0 ) Abc_Print( 1, "SCMAP_VIEW gain %.1f GENLIB: common-load seed at %.3f input capacitances\n", Gain, pPars->SeedLoad );
        else Abc_Print( 1, "SCMAP_VIEW GENLIB gain not recognized: common-load seed at %.3f input capacitances\n", pPars->SeedLoad );
    }
    p->InvAreaW  = p->pCells[3].AreaW;
    p->InvAreaF  = p->pCells[3].AreaF;
    Scm_ObjMatch(p, 0, 0)->Gate = 0;
    Scm_ObjMatch(p, 0, 1)->Gate = 1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the mapping manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_StoDelete( Scm_Man_t * p )
{
    int i;
    // A failed run leaves the GIA with the mapping it came with.
    if ( p->pGia->vCellMapping == NULL )
        p->pGia->vCellMapping = p->vMappingOld;
    else
        Vec_IntFreeP( &p->vMappingOld );
    Scm_CtxFree( p->pCtxSpare );
    p->pCtxSpare = NULL;
    ABC_FREE( p->pFitCache );
    ABC_FREE( p->pFitState );
    ABC_FREE( p->pEnvState );
    ABC_FREE( p->pEnvBufs );
    Vec_PtrFreeData( &p->vPages );
    ABC_FREE( p->vPages.pArray );
    ABC_FREE( p->vMapRefs.pArray );
    ABC_FREE( p->vFlowRefs.pArray );
    ABC_FREE( p->vCutSets.pArray );
    ABC_FREE( p->vCutFlows.pArray );
    ABC_FREE( p->vCutDelays.pArray );
    ABC_FREE( p->vBackup.pArray );
    ABC_FREE( p->pSclCells );
    ABC_FREE( p->pFamilyCaps );
    ABC_FREE( p->pFamilyRfCaps );
    ABC_FREE( p->pArcFits );
    if ( p->pEnvCosts )
        for ( i = 0; i < p->nCells; i++ )
            ABC_FREE(p->pEnvCosts[i].pSegs);
    ABC_FREE(p->pEnvCosts);
    if ( p->pEnvDelays )
        for ( i = 0; i < 2*p->nCells*SCM_LEAF_MAX; i++ )
            ABC_FREE( p->pEnvDelays[i].pSegs );
    if ( p->pEnvSlews )
        for ( i = 0; i < 2*p->nCells; i++ )
            ABC_FREE( p->pEnvSlews[i].pSegs );
    ABC_FREE( p->pEnvDelays );
    ABC_FREE( p->pEnvSlews );
    ABC_FREE( p->pArrMax );
    ABC_FREE( p->pSlewMax );
    ABC_FREE( p->pRfArrs );
    ABC_FREE( p->pRfSlews );
    ABC_FREE( p->pRfLoads );
    ABC_FREE( p->vLoads.pArray );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Computes the function of a cut merged from two fanin cuts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CutComputeTruth6( Scm_Man_t * p, Scm_Cut_t * pCut0, Scm_Cut_t * pCut1, int fCompl0, int fCompl1, Scm_Cut_t * pCutR, int fIsXor )
{
    int nOldSupp = pCutR->nLeaves, truthId, fCompl; word t;
    word t0 = *Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(pCut0->iFunc));
    word t1 = *Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(pCut1->iFunc));
    if ( Abc_LitIsCompl(pCut0->iFunc) ^ fCompl0 ) t0 = ~t0;
    if ( Abc_LitIsCompl(pCut1->iFunc) ^ fCompl1 ) t1 = ~t1;
    t0 = Abc_Tt6Expand( t0, pCut0->pLeaves, pCut0->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    t1 = Abc_Tt6Expand( t1, pCut1->pLeaves, pCut1->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    t =  fIsXor ? t0 ^ t1 : t0 & t1;
    if ( (fCompl = (int)(t & 1)) ) t = ~t;
    pCutR->nLeaves = Abc_Tt6MinBase( &t, pCutR->pLeaves, pCutR->nLeaves );
    assert( (int)(t & 1) == 0 );
    truthId        = Vec_MemHashInsert(p->vTtMem, &t);
    pCutR->iFunc   = Abc_Var2Lit( truthId, fCompl );
    pCutR->Useless = Scm_ObjCutUseless( p, truthId );
    assert( (int)pCutR->nLeaves <= nOldSupp );
    return (int)pCutR->nLeaves < nOldSupp;
}

/**Function*************************************************************

  Synopsis    [Computes the function of a cut merged from three MUX fanin cuts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CutComputeTruthMux6( Scm_Man_t * p, Scm_Cut_t * pCut0, Scm_Cut_t * pCut1, Scm_Cut_t * pCutC, int fCompl0, int fCompl1, int fComplC, Scm_Cut_t * pCutR )
{
    int nOldSupp = pCutR->nLeaves, truthId, fCompl; word t;
    word t0 = *Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(pCut0->iFunc));
    word t1 = *Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(pCut1->iFunc));
    word tC = *Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(pCutC->iFunc));
    if ( Abc_LitIsCompl(pCut0->iFunc) ^ fCompl0 ) t0 = ~t0;
    if ( Abc_LitIsCompl(pCut1->iFunc) ^ fCompl1 ) t1 = ~t1;
    if ( Abc_LitIsCompl(pCutC->iFunc) ^ fComplC ) tC = ~tC;
    t0 = Abc_Tt6Expand( t0, pCut0->pLeaves, pCut0->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    t1 = Abc_Tt6Expand( t1, pCut1->pLeaves, pCut1->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    tC = Abc_Tt6Expand( tC, pCutC->pLeaves, pCutC->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    t = (tC & t1) | (~tC & t0);
    if ( (fCompl = (int)(t & 1)) ) t = ~t;
    pCutR->nLeaves = Abc_Tt6MinBase( &t, pCutR->pLeaves, pCutR->nLeaves );
    assert( (int)(t & 1) == 0 );
    truthId        = Vec_MemHashInsert(p->vTtMem, &t);
    pCutR->iFunc   = Abc_Var2Lit( truthId, fCompl );
    pCutR->Useless = Scm_ObjCutUseless( p, truthId );
    assert( (int)pCutR->nLeaves <= nOldSupp );
    return (int)pCutR->nLeaves < nOldSupp;
}

/**Function*************************************************************

  Synopsis    [Counts the ones in a 64-bit word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CutCountBits( word i )
{
    i = i - ((i >> 1) & 0x5555555555555555);
    i = (i & 0x3333333333333333) + ((i >> 2) & 0x3333333333333333);
    i = ((i + (i >> 4)) & 0x0F0F0F0F0F0F0F0F);
    return (i*(0x0101010101010101))>>56;
}

/**Function*************************************************************

  Synopsis    [Computes the signature of the leaves of a cut.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Scm_CutGetSign( int * pLeaves, int nLeaves )
{
    word Sign = 0; int i;
    for ( i = 0; i < nLeaves; i++ )
        Sign |= ((word)1) << (pLeaves[i] & 0x3F);
    return Sign;
}

/**Function*************************************************************

  Synopsis    [Creates the trivial cut of an object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CutCreateUnit( Scm_Cut_t * p, int i )
{
    p->Delay      = 0;
    p->Flow       = 0;
    p->iFunc      = 2;
    p->nLeaves    = 1;
    p->pLeaves[0] = i;
    p->Sign       = ((word)1) << (i & 0x3F);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Loads the stored cuts of an object, adding its trivial cut if
  requested.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_ManPrepareCuts( Scm_Cut_t * pCuts, Scm_Man_t * p, int iObj, int fAddUnit )
{
    if ( Scm_ObjHasCuts(p, iObj) )
    {
        Scm_Cut_t * pMfCut = pCuts;
        int i, * pCut, * pList = Scm_ObjCutSet(p, iObj);
        Scm_SetForEachCut( pList, pCut, i )
        {
            pMfCut->Delay   = 0;
            pMfCut->Flow    = 0;
            pMfCut->iFunc   = Scm_CutFunc( pCut );
            pMfCut->nLeaves = Scm_CutSize( pCut );
            pMfCut->Sign    = Scm_CutGetSign( pCut+1, Scm_CutSize(pCut) );
            pMfCut->Useless = Scm_ObjCutUseless( p, Abc_Lit2Var(pMfCut->iFunc) );
            memcpy( pMfCut->pLeaves, pCut+1, sizeof(int) * Scm_CutSize(pCut) );
            pMfCut++;
        }
        if ( fAddUnit && pCuts->nLeaves > 1 )
            return pList[0] + Scm_CutCreateUnit( pMfCut, iObj );
        return pList[0];
    }
    return Scm_CutCreateUnit( pCuts, iObj );
}

/**Function*************************************************************

  Synopsis    [Stores the cuts of an object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_ManSaveCuts( Scm_Man_t * p, Scm_Cut_t ** pCuts, int nCuts )
{
    int i, * pPlace, iCur, nInts = 1;
    for ( i = 0; i < nCuts; i++ )
        nInts += pCuts[i]->nLeaves + 1;
    if ( (p->iCur & 0xFFFF) + nInts > 0xFFFF )
        p->iCur = ((p->iCur >> 16) + 1) << 16;
    if ( Vec_PtrSize(&p->vPages) == (p->iCur >> 16) )
        Vec_PtrPush( &p->vPages, ABC_ALLOC(int, (1<<16)) );
    iCur = p->iCur; p->iCur += nInts;
    pPlace = Scm_ManCutSet( p, iCur );
    *pPlace++ = nCuts;
    for ( i = 0; i < nCuts; i++ )
    {
        *pPlace++ = Scm_CutSetBoth( pCuts[i]->nLeaves, pCuts[i]->iFunc );
        memcpy( pPlace, pCuts[i]->pLeaves, sizeof(int) * pCuts[i]->nLeaves );
        pPlace += pCuts[i]->nLeaves;
    }
    return iCur;
}
/**Function*************************************************************

  Synopsis    [Merges the sorted leaves of two cuts (three for a MUX).]

  Description [Returns 0 if the result exceeds SCM_LEAF_MAX leaves.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CutMergeOrder( Scm_Cut_t * pCut0, Scm_Cut_t * pCut1, Scm_Cut_t * pCut )
{
    int nSize0   = pCut0->nLeaves;
    int nSize1   = pCut1->nLeaves;
    int i, * pC0 = pCut0->pLeaves;
    int k, * pC1 = pCut1->pLeaves;
    int c, * pC  = pCut->pLeaves;
    // the case of the largest cut sizes
    if ( nSize0 == SCM_LEAF_MAX && nSize1 == SCM_LEAF_MAX )
    {
        for ( i = 0; i < nSize0; i++ )
        {
            if ( pC0[i] != pC1[i] )  return 0;
            pC[i] = pC0[i];
        }
        pCut->nLeaves = SCM_LEAF_MAX;
        pCut->iFunc = SCM_NO_FUNC;
        pCut->Sign = pCut0->Sign | pCut1->Sign;
        return 1;
    }
    // compare two cuts with different numbers
    i = k = c = 0;
    if ( nSize0 == 0 ) goto FlushCut1;
    if ( nSize1 == 0 ) goto FlushCut0;
    while ( 1 )
    {
        if ( c == SCM_LEAF_MAX ) return 0;
        if ( pC0[i] < pC1[k] )
        {
            pC[c++] = pC0[i++];
            if ( i >= nSize0 ) goto FlushCut1;
        }
        else if ( pC0[i] > pC1[k] )
        {
            pC[c++] = pC1[k++];
            if ( k >= nSize1 ) goto FlushCut0;
        }
        else
        {
            pC[c++] = pC0[i++]; k++;
            if ( i >= nSize0 ) goto FlushCut1;
            if ( k >= nSize1 ) goto FlushCut0;
        }
    }

FlushCut0:
    if ( c + nSize0 > SCM_LEAF_MAX + i ) return 0;
    while ( i < nSize0 )
        pC[c++] = pC0[i++];
    pCut->nLeaves = c;
    pCut->iFunc = SCM_NO_FUNC;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;

FlushCut1:
    if ( c + nSize1 > SCM_LEAF_MAX + k ) return 0;
    while ( k < nSize1 )
        pC[c++] = pC1[k++];
    pCut->nLeaves = c;
    pCut->iFunc = SCM_NO_FUNC;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Merges the leaves of three cuts; returns 0 if the result is too large.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CutMergeOrderMux( Scm_Cut_t * pCut0, Scm_Cut_t * pCut1, Scm_Cut_t * pCut2, Scm_Cut_t * pCut )
{
    int x0, i0 = 0, nSize0 = pCut0->nLeaves, * pC0 = pCut0->pLeaves;
    int x1, i1 = 0, nSize1 = pCut1->nLeaves, * pC1 = pCut1->pLeaves;
    int x2, i2 = 0, nSize2 = pCut2->nLeaves, * pC2 = pCut2->pLeaves;
    int xMin, c = 0, * pC  = pCut->pLeaves;
    while ( 1 )
    {
        x0 = (i0 == nSize0) ? ABC_INFINITY : pC0[i0];
        x1 = (i1 == nSize1) ? ABC_INFINITY : pC1[i1];
        x2 = (i2 == nSize2) ? ABC_INFINITY : pC2[i2];
        xMin = Abc_MinInt( Abc_MinInt(x0, x1), x2 );
        if ( xMin == ABC_INFINITY ) break;
        if ( c == SCM_LEAF_MAX ) return 0;
        pC[c++] = xMin;
        if (x0 == xMin) i0++;
        if (x1 == xMin) i1++;
        if (x2 == xMin) i2++;
    }
    pCut->nLeaves = c;
    pCut->iFunc = SCM_NO_FUNC;
    pCut->Sign = pCut0->Sign | pCut1->Sign | pCut2->Sign;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks whether the leaves of a cut are a subset of those of another.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_SetCutIsContainedOrder( Scm_Cut_t * pBase, Scm_Cut_t * pCut )
{
    int i, nSizeB = pBase->nLeaves;
    int k, nSizeC = pCut->nLeaves;
    if ( nSizeB == nSizeC )
    {
        for ( i = 0; i < nSizeB; i++ )
            if ( pBase->pLeaves[i] != pCut->pLeaves[i] )
                return 0;
        return 1;
    }
    assert( nSizeB > nSizeC );
    if ( nSizeC == 0 )
        return 1;
    for ( i = k = 0; i < nSizeB; i++ )
    {
        if ( pBase->pLeaves[i] > pCut->pLeaves[k] )
            return 0;
        if ( pBase->pLeaves[i] == pCut->pLeaves[k] )
        {
            if ( ++k == nSizeC )
                return 1;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks whether an earlier cut dominates the last cut.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_SetLastCutIsContained( Scm_Cut_t ** pCuts, int nCuts )
{
    int i;
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[i]->nLeaves <= pCuts[nCuts]->nLeaves && (pCuts[i]->Sign & pCuts[nCuts]->Sign) == pCuts[i]->Sign && Scm_SetCutIsContainedOrder(pCuts[nCuts], pCuts[i]) )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Removes the earlier cuts that the last cut dominates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_SetLastCutContainsArea( Scm_Cut_t ** pCuts, int nCuts )
{
    int i, k, fChanges = 0;
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[nCuts]->nLeaves < pCuts[i]->nLeaves && (pCuts[nCuts]->Sign & pCuts[i]->Sign) == pCuts[nCuts]->Sign && Scm_SetCutIsContainedOrder(pCuts[i], pCuts[nCuts]) )
            pCuts[i]->nLeaves = SCM_NO_LEAF, fChanges = 1;
    if ( !fChanges )
        return nCuts;
    for ( i = k = 0; i <= nCuts; i++ )
    {
        if ( pCuts[i]->nLeaves == SCM_NO_LEAF )
            continue;
        if ( k < i )
            ABC_SWAP( Scm_Cut_t *, pCuts[k], pCuts[i] )
        k++;
    }
    return k - 1;
}

/**Function*************************************************************

  Synopsis    [Orders cuts by usefulness, area flow, delay and size.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CutCompareArea( Scm_Cut_t * pCut0, Scm_Cut_t * pCut1 )
{
    if ( pCut0->Useless < pCut1->Useless )  return -1;
    if ( pCut0->Useless > pCut1->Useless )  return  1;
    if ( pCut0->Flow    < pCut1->Flow - SCM_EPSILON )  return -1;
    if ( pCut0->Flow    > pCut1->Flow + SCM_EPSILON )  return  1;
    if ( pCut0->Delay   < pCut1->Delay   )  return -1;
    if ( pCut0->Delay   > pCut1->Delay   )  return  1;
    if ( pCut0->nLeaves < pCut1->nLeaves )  return -1;
    if ( pCut0->nLeaves > pCut1->nLeaves )  return  1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Moves the last cut to its place in area order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Scm_SetSortByArea( Scm_Cut_t ** pCuts, int nCuts )
{
    int i;
    for ( i = nCuts; i > 0; i-- )
    {
        if ( Scm_CutCompareArea(pCuts[i - 1], pCuts[i]) < 0 )
            return;
        ABC_SWAP( Scm_Cut_t *, pCuts[i - 1], pCuts[i] )
    }
}

/**Function*************************************************************

  Synopsis    [Three of the fifteen nontrivial cut slots are reserved for shallow
  cuts; the other slots keep the cuts of least area flow.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CutDepthBetter( Scm_Cut_t * a, Scm_Cut_t * b )
{
    if ( a->Useless != b->Useless ) return a->Useless < b->Useless;
    if ( a->Delay != b->Delay ) return a->Delay < b->Delay;
    return Scm_CutCompareArea(a, b) < 0;
}

/**Function*************************************************************

  Synopsis    [Adds the last cut to the set, keeping area-efficient and shallow cuts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_SetAddCutStructure( Scm_Cut_t ** Cuts, int n, int Limit )
{
    Scm_Cut_t * pWorst;
    int j, Count, Best, AreaSlots;

    if ( !n ) return 1;
    Count = Scm_SetLastCutContainsArea(Cuts, n) + 1;
    // Retained cuts are in area order, so insert the new cut once.
    Scm_SetSortByArea(Cuts, Count - 1);
    if ( Count < Limit ) return Count;
    AreaSlots = (Limit - 1) - Abc_MaxInt(1, (Limit - 1) / 4);
    // Exactly one cut is dropped (Count == Limit). Selecting the remaining
    // depth slots one by one (earliest index wins ties) leaves the cut with
    // the worst depth rank and, among equals, the largest index. Find it in
    // one scan and move it to the end; the retained order is unchanged.
    assert( Count == Limit );
    Best = AreaSlots;
    for ( j = AreaSlots + 1; j < Count; j++ )
        if ( !Scm_CutDepthBetter(Cuts[j], Cuts[Best]) ) Best = j;
    pWorst = Cuts[Best];
    for ( j = Best; j + 1 < Count; j++ ) Cuts[j] = Cuts[j+1];
    Cuts[Count-1] = pWorst;
    return Limit - 1;
}

/**Function*************************************************************

  Synopsis    [Returns the area cost of a cut: its leaf count, or 0 below two leaves.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_CutArea( int nLeaves )
{
    if ( nLeaves < 2 )
        return 0;
    return nLeaves;
}

/**Function*************************************************************

  Synopsis    [Computes the delay and area flow of a cut.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Scm_CutParams( Scm_Man_t * p, Scm_Cut_t * pCut, float FlowRefs )
{
    int i, nLeaves = pCut->nLeaves;
    assert( nLeaves <= SCM_LEAF_MAX );
    pCut->Delay = 0;
    pCut->Flow  = 0;
    for ( i = 0; i < nLeaves; i++ )
    {
        pCut->Delay = Abc_MaxInt( pCut->Delay, Scm_ObjCutDelay(p, pCut->pLeaves[i]) );
        pCut->Flow += Scm_ObjCutFlow(p, pCut->pLeaves[i]);
    }
    pCut->Delay += (int)(nLeaves > 1);
    pCut->Flow = (pCut->Flow + Scm_CutArea(nLeaves)) / FlowRefs;
}

/**Function*************************************************************

  Synopsis    [Computes the priority cuts of a node and of its choices.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ObjMergeOrder( Scm_Man_t * p, int iObj )
{
    Scm_Cut_t pCuts0[SCM_CUT_NUM], pCuts1[SCM_CUT_NUM], pCuts[SCM_CUT_NUM], * pCutsR[SCM_CUT_NUM];
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    float dFlowRefs  = Scm_ObjFlowRefs(p, iObj, 0) + Scm_ObjFlowRefs(p, iObj, 1);
    int nCuts0   = Scm_ManPrepareCuts(pCuts0, p, Gia_ObjFaninId0(pObj, iObj), 1);
    int nCuts1   = Scm_ManPrepareCuts(pCuts1, p, Gia_ObjFaninId1(pObj, iObj), 1);
    int fComp0   = Gia_ObjFaninC0(pObj);
    int fComp1   = Gia_ObjFaninC1(pObj);
    int iSibl    = Gia_ObjSibl(p->pGia, iObj);
    Scm_Cut_t * pCut0, * pCut1, * pCut0Lim = pCuts0 + nCuts0, * pCut1Lim = pCuts1 + nCuts1;
    int i, nCutsR = 0;
    for ( i = 0; i < SCM_CUT_NUM; i++ )
        pCutsR[i] = pCuts + i;
    if ( iSibl )
    {
        Scm_Cut_t pCuts2[SCM_CUT_NUM];
        Gia_Obj_t * pObjE = Gia_ObjSiblObj(p->pGia, iObj);
        int fCompE = Gia_ObjPhase(pObj) ^ Gia_ObjPhase(pObjE);
        int nCuts2 = Scm_ManPrepareCuts(pCuts2, p, iSibl, 0);
        Scm_Cut_t * pCut2, * pCut2Lim = pCuts2 + nCuts2;
        for ( pCut2 = pCuts2; pCut2 < pCut2Lim; pCut2++ )
        {
            *pCutsR[nCutsR] = *pCut2;
            pCutsR[nCutsR]->iFunc = Abc_LitNotCond( pCutsR[nCutsR]->iFunc, fCompE );
            Scm_CutParams( p, pCutsR[nCutsR], dFlowRefs );
            nCutsR = Scm_SetAddCutStructure( pCutsR, nCutsR, SCM_CUT_NUM );
        }
    }
    if ( Gia_ObjIsMuxId(p->pGia, iObj) )
    {
        Scm_Cut_t pCuts2[SCM_CUT_NUM];
        int nCuts2  = Scm_ManPrepareCuts(pCuts2, p, Gia_ObjFaninId2(p->pGia, iObj), 1);
        int fComp2  = Gia_ObjFaninC2(p->pGia, pObj);
        Scm_Cut_t * pCut2, * pCut2Lim = pCuts2 + nCuts2;
        for ( pCut0 = pCuts0; pCut0 < pCut0Lim; pCut0++ )
        for ( pCut1 = pCuts1; pCut1 < pCut1Lim; pCut1++ )
        for ( pCut2 = pCuts2; pCut2 < pCut2Lim; pCut2++ )
        {
            if ( Scm_CutCountBits(pCut0->Sign | pCut1->Sign | pCut2->Sign) > SCM_LEAF_MAX )
                continue;
            if ( !Scm_CutMergeOrderMux(pCut0, pCut1, pCut2, pCutsR[nCutsR]) )
                continue;
            if ( Scm_SetLastCutIsContained(pCutsR, nCutsR) )
                continue;
            if ( Scm_CutComputeTruthMux6(p, pCut0, pCut1, pCut2, fComp0, fComp1, fComp2, pCutsR[nCutsR]) )
                pCutsR[nCutsR]->Sign = Scm_CutGetSign(pCutsR[nCutsR]->pLeaves, pCutsR[nCutsR]->nLeaves);
            Scm_CutParams( p, pCutsR[nCutsR], dFlowRefs );
            nCutsR = Scm_SetAddCutStructure( pCutsR, nCutsR, SCM_CUT_NUM );
        }
    }
    else
    {
        int fIsXor = Gia_ObjIsXor(pObj);
        for ( pCut0 = pCuts0; pCut0 < pCut0Lim; pCut0++ )
        for ( pCut1 = pCuts1; pCut1 < pCut1Lim; pCut1++ )
        {
            if ( (int)(pCut0->nLeaves + pCut1->nLeaves) > SCM_LEAF_MAX && Scm_CutCountBits(pCut0->Sign | pCut1->Sign) > SCM_LEAF_MAX )
                continue;
            if ( !Scm_CutMergeOrder(pCut0, pCut1, pCutsR[nCutsR]) )
                continue;
            if ( Scm_SetLastCutIsContained(pCutsR, nCutsR) )
                continue;
            if ( Scm_CutComputeTruth6(p, pCut0, pCut1, fComp0, fComp1, pCutsR[nCutsR], fIsXor) )
                pCutsR[nCutsR]->Sign = Scm_CutGetSign(pCutsR[nCutsR]->pLeaves, pCutsR[nCutsR]->nLeaves);
            Scm_CutParams( p, pCutsR[nCutsR], dFlowRefs );
            nCutsR = Scm_SetAddCutStructure( pCutsR, nCutsR, SCM_CUT_NUM );
        }
    }
    assert( nCutsR > 0 && nCutsR < SCM_CUT_NUM );
    // store the cutset; the node delay is the shallowest cut among the equally useful ones
    Scm_ObjSetCutFlow( p, iObj, pCutsR[0]->Flow );
    Scm_ObjSetCutDelay( p, iObj, pCutsR[0]->Delay );
    for ( i = 1; i < nCutsR; i++ )
        if ( pCutsR[i]->Useless == pCutsR[0]->Useless )
            Scm_ObjSetCutDelay(p, iObj, Abc_MinInt(Scm_ObjCutDelay(p, iObj), pCutsR[i]->Delay));
    *Vec_IntEntryP(&p->vCutSets, iObj) = Scm_ManSaveCuts(p, pCutsR, nCutsR);
}

/**Function*************************************************************

  Synopsis    [Cuts in topological order; a primary input has zero flow and delay.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManComputeCuts( Scm_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachAnd( p->pGia, pObj, i )
        Scm_ObjMergeOrder( p, i );
}

/**Function*************************************************************

  Synopsis    [Prints the mapping statistics of the input (-v).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManPrintInit( Scm_Man_t * p )
{
    int nChoices;
    if ( !p->pPars->fVerbose )
        return;
    nChoices = Gia_ManChoiceNum( p->pGia );
    Abc_Print( 1, "SCMAP_INPUT cells=%d functions=%d matches=%d ands=%d choices=%d\n", p->nCells,
        Vec_MemEntryNum(p->vTtMem), Vec_WecSizeSize(p->vTt2Match)/2, Gia_ManAndNum(p->pGia), nChoices );
}
/**Function*************************************************************

  Synopsis    [Exact area of a match.]

  Description [Dereferences (or references) the match and the cone it alone uses;
  returns the area freed (or added).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_MatchDeref_rec( Scm_Man_t * p, int i, int c, Scm_Mat_t * pM )
{
    word Area = 0;
    int k, iVar, fCompl, * pCut;
    if ( pM->fCompl )
    {
        assert( Scm_ObjMapRefNum(p, i, !c) > 0 );
        if ( !Scm_ObjMapRefDec(p, i, !c) )
            Area += Scm_MatchDeref_rec( p, i, !c, Scm_ObjMatch(p, i, !c) );
        return Area + p->InvAreaW;
    }
    if ( Scm_ObjCutSetId(p, i) == 0 )
        return 0;
    pCut = Scm_CutFromHandle( Scm_ObjCutSet(p, i), pM->CutH );
    Scm_CutForEachVarCompl( pCut, pM->Cfg, iVar, fCompl, k )
    {
        assert( Scm_ObjMapRefNum(p, iVar, fCompl) > 0 );
        if ( !Scm_ObjMapRefDec(p, iVar, fCompl) )
            Area += Scm_MatchDeref_rec( p, iVar, fCompl, Scm_ObjMatch(p, iVar, fCompl) );
    }
    return Area + Scm_ManCell(p, pM->Gate)->AreaW;
}

/**Function*************************************************************

  Synopsis    [References a match and its fanin cone; returns the area added.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_MatchRef_rec( Scm_Man_t * p, int i, int c, Scm_Mat_t * pM )
{
    word Area = 0;
    int k, iVar, fCompl, * pCut;
    if ( pM->fCompl )
    {
        assert( Scm_ObjMapRefNum(p, i, !c) >= 0 );
        if ( !Scm_ObjMapRefInc(p, i, !c) )
            Area += Scm_MatchRef_rec( p, i, !c, Scm_ObjMatch(p, i, !c) );
        return Area + p->InvAreaW;
    }
    if ( Scm_ObjCutSetId(p, i) == 0 )
        return 0;
    pCut = Scm_CutFromHandle( Scm_ObjCutSet(p, i), pM->CutH );
    Scm_CutForEachVarCompl( pCut, pM->Cfg, iVar, fCompl, k )
    {
        assert( Scm_ObjMapRefNum(p, iVar, fCompl) >= 0 );
        if ( !Scm_ObjMapRefInc(p, iVar, fCompl) )
            Area += Scm_MatchRef_rec( p, iVar, fCompl, Scm_ObjMatch(p, iVar, fCompl) );
    }
    return Area + Scm_ManCell(p, pM->Gate)->AreaW;
}

/**Function*************************************************************

  Synopsis    [Writes the selected cover as the cell mapping of the GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Scm_ManDeriveMapping( Scm_Man_t * p )
{
    Vec_Int_t * vMapping;
    Scm_Mat_t * pM;
    int i, k, c, Id, iVar, fCompl, * pCut;
    assert( p->pGia->vCellMapping == NULL );
    vMapping = Vec_IntAlloc( 4*Gia_ManObjNum(p->pGia) );
    Vec_IntFill( vMapping, 2*Gia_ManObjNum(p->pGia), 0 );
    // create CI inverters
    Gia_ManForEachCiId( p->pGia, Id, i )
    if ( Scm_ObjMapRefNum(p, Id, 1) )
        Vec_IntWriteEntry( vMapping, Abc_Var2Lit(Id, 1), -1 );
    // create internal nodes
    Gia_ManForEachAndId( p->pGia, i )
    {
        for ( c = 0; c < 2; c++ )
        if ( Scm_ObjMapRefNum(p, i, c) )
        {
            pM = Scm_ObjMatch( p, i, c );
            // remember inverter
            if ( pM->fCompl )
            {
                Vec_IntWriteEntry( vMapping, Abc_Var2Lit(i, c), -1 );
                continue;
            }
            pCut = Scm_CutFromHandle( Scm_ObjCutSet(p, i), pM->CutH );
            Vec_IntWriteEntry( vMapping, Abc_Var2Lit(i, c), Vec_IntSize(vMapping) );
            Vec_IntPush( vMapping, Scm_CutSize(pCut) );
            Scm_CutForEachVarCompl( pCut, pM->Cfg, iVar, fCompl, k )
                Vec_IntPush( vMapping, Abc_Var2Lit(iVar, fCompl) );
            Vec_IntPush( vMapping, pM->Gate );
        }
    }
    p->pGia->vCellMapping = vMapping;

    return p->pGia;
}


////////////////////////////////////////////////////////////////////////
///          ELECTRICAL MODEL, REFINEMENT CONTEXT AND TIMING         ///
////////////////////////////////////////////////////////////////////////

#define SCM_LOAD_INF  1.0e20f

typedef struct Scm_Cand_t_ Scm_Cand_t;
struct Scm_Cand_t_
{
    Scm_Mat_t       M;
    word            Area;           // exact area the match adds
};

typedef struct Scm_Fanouts_t_ Scm_Fanouts_t;
// The fanouts of a literal in the cover: the literals whose matches use it, and at which pin.
struct Scm_Fanouts_t_
{
    int *           pRoots;
    unsigned char * pPins;
    int             nRoots;
    int             nAlloc;
};

typedef struct Scm_ArcNode_t_ Scm_ArcNode_t;
typedef struct Scm_Ctx_t_ Scm_Ctx_t;
// A refinement context: the cover's fanouts and loads, residual tails, and the timing of the current trial.
struct Scm_Ctx_t_
{
    Scm_Fanouts_t * pFans;          // per literal: its fanouts in the cover
    Scm_RfLines_t * pTails;         // per literal: its residual tail
    double *        pLoadSums;      // per literal: load, accumulated in double
    double *        pRfLoadSums;    // per literal and transition: the same (-q, -r, -t)
    float *         pBufferAreas;   // per literal: modeled buffer-tree area of its net in AreaW units (repair only)
    word            BufferFreed;    // logic area freed by the match under repair
    float *         pTrialArrMax;   // per literal: the trial's timing
    float *         pTrialSlewMax;
    Scm_RfPair_t *  pTrialRfArrs;
    Scm_RfPair_t *  pTrialRfSlews;
    Scm_RfPair_t *  pTailBase;      // per literal: its tail's delay at its slew
    unsigned *      pTouched;       // per literal: epoch stamps
    unsigned *      pComputed;
    unsigned *      pConeSeen;
    unsigned *      pTailSeen;
    unsigned char * pTailValid;
    unsigned char * pIsPo;
    unsigned        Epoch;
    unsigned        ConeEpoch;
    unsigned        TailEpoch;
    unsigned        SeedEpoch;      // stamps for linear-time seed deduplication
    int *           pEdgePos;       // position of edge (root literal, pin) in its child's fanout list
    unsigned *      pSeedStamp;
    Vec_Int_t *     vSeedSort;
    Vec_Int_t *     vOldSeeds;      // literals whose match or load the removal of the old match changed
    Vec_Int_t *     vTrialSeeds;    // the same for the old and the trial match
    Vec_Int_t *     vAffected;      // literals timed by the last trial
    word *          pQueueBits[6];  // the timing queue: a bit set over literal order keys, one level per 6 bits
    int             nQueueLevels;
    Vec_Int_t *     vConeStack;
    Vec_Int_t *     vBoundary;
    Vec_Flt_t *     vBoundaryPriorities;
    Vec_Int_t *     vTailStack;
    Vec_Int_t *     vTailWork;
    Vec_Int_t *     vTailSort;
    Vec_Int_t *     pCollectSeeds;  // if not NULL, receives the literals that reference changes reach
    int             nLits;
    Scm_ArcNode_t ** pArcCache;     // per literal: the arcs of its match at its load
    int             fLiveTail;      // commits invalidate tails (the pruning walk's context)
    void *          pScorePrune;    // the search's Scm_Prune_t
    int             fScorePrune, ScorePruneCutoff, fScoreRejected;
    int             fFullPropagation; // propagate changed timing to affected outputs
    Vec_Int_t *     vScoreOutputs;  // outputs timed by the last trial (search only)
    int             fError;
};

/**Function*************************************************************

  Synopsis    [Checks whether two matches are the same.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Scm_MatSame( Scm_Mat_t * pA, Scm_Mat_t * pB )
{
    return pA->Gate == pB->Gate && pA->CutH == pB->CutH &&
        pA->fCompl == pB->fCompl && Scm_Cfg2Int(pA->Cfg) == Scm_Cfg2Int(pB->Cfg);
}

/**Function*************************************************************

  Synopsis    [Appends a segment to a piecewise-linear function of the load.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_PwlPush( Scm_Pwl_t * pPwl, float Lo, float Hi, float Offset, float Slope )
{
    Scm_Seg_t * pLast, * pSeg;
    if ( Hi <= Lo )
        return;
    if ( pPwl->nSegs )
    {
        pLast = pPwl->pSegs + pPwl->nSegs - 1;
        if ( pLast->Hi == Lo && pLast->Offset == Offset &&
             pLast->Slope == Slope )
        {
            pLast->Hi = Hi;
            return;
        }
    }
    if ( pPwl->nSegs == pPwl->nAlloc )
    {
        pPwl->nAlloc = pPwl->nAlloc ? 2 * pPwl->nAlloc : 4;
        pPwl->pSegs = ABC_REALLOC( Scm_Seg_t, pPwl->pSegs, pPwl->nAlloc );
    }
    pSeg = pPwl->pSegs + pPwl->nSegs++;
    pSeg->Lo = Lo;
    pSeg->Hi = Hi;
    pSeg->Offset = Offset;
    pSeg->Slope = Slope;
}

/**Function*************************************************************

  Synopsis    [Evaluates a piecewise-linear function at a load.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_PwlEval( Scm_Pwl_t * pPwl, float Load )
{
    int Lo = 0, Hi = pPwl->nSegs, Mid;
    Scm_Seg_t * pSeg;
    // An empty function belongs to a cell whose envelope could not be built;
    // fEnvError is set then, and the mapping is rejected.
    if ( pPwl->nSegs == 0 ) return 0.0f;
    Load = Abc_MaxFloat(0.0f, Load);
    while ( Lo + 1 < Hi )
    {
        Mid = (Lo + Hi) >> 1;
        if ( Load >= pPwl->pSegs[Mid].Lo ) Lo = Mid;
        else Hi = Mid;
    }
    pSeg = pPwl->pSegs + Lo;
    if ( Load > pSeg->Hi + 1.0e-3f && Lo + 1 < pPwl->nSegs )
        pSeg++;
    return pSeg->Offset + pSeg->Slope * Load;
}

/**Function*************************************************************

  Synopsis    [Checks that a piecewise-linear function is finite, contiguous and
  unbounded.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_PwlCheck( Scm_Pwl_t * pPwl )
{
    float Previous = 0.0f;
    int i;
    for ( i = 0; i < pPwl->nSegs; i++ )
    {
        Scm_Seg_t * pSeg = pPwl->pSegs + i;
        float Tol = 1.0e-4f * Abc_MaxFloat(1.0f, fabsf(Previous));
        if ( !isfinite(pSeg->Lo) || !isfinite(pSeg->Hi) ||
             !isfinite(pSeg->Offset) || !isfinite(pSeg->Slope) ||
             pSeg->Hi <= pSeg->Lo || fabsf(pSeg->Lo - Previous) > Tol )
            return 0;
        Previous = pSeg->Hi;
    }
    return pPwl->nSegs > 0 && Previous >= 0.5f * SCM_LOAD_INF;
}

static void Scm_ManEnsureEnvBuild( Scm_Man_t * p, Mio_Cell2_t * pCell );

/**Function*************************************************************

  Synopsis    [Builds the size/buffer envelopes of a cell on first use.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Scm_ManEnsureEnv( Scm_Man_t * p, Mio_Cell2_t * pCell )
{
    if ( p->pEnvState && !p->pEnvState[pCell->Id] ) Scm_ManEnsureEnvBuild( p, pCell );
}

/**Function*************************************************************

  Synopsis    [An arc at a load through the cell's size/buffer envelope: both output
  transitions use the size/tree selected at the envelope knot, and its
  output slew, shared by all pins, is taken at the same load as the
  delay.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Arc_t * Scm_ManArcAtLoad( Scm_Man_t * p, Mio_Cell2_t * pCell, int iPin, Scm_RfPair_t Load, Scm_Arc_t * pTemp )
{
    int t;
    Scm_ManEnsureEnv( p, pCell );
    *pTemp = *Scm_ManArc(p, pCell, iPin);
    for ( t = 0; t < 2; t++ )
    {
        pTemp->RfDelay0[t] = Scm_PwlEval(p->pEnvDelays + 2*(pCell->Id*SCM_LEAF_MAX + iPin) + t, Load.Value[t]);
        pTemp->RfDelayLoad[t] = 0;
        pTemp->RfSlew0[t] = Scm_PwlEval(p->pEnvSlews + 2*pCell->Id + t, Load.Value[t]);
        pTemp->RfSlewLoad[t] = 0;
    }
    return pTemp;
}

// A buffer size: its blended arc, input capacitance and area in AreaW units.
typedef struct Scm_BufferType_t_ Scm_BufferType_t;
struct Scm_BufferType_t_
{
    Scm_Arc_t       Arc;
    float           Cap, Area;
};

// Library preprocessing. Fit each physical logic-cell size on
// its own NLDM grid, then choose a shared size/tree for all arcs at each
// load sample. Preserve separate fall/rise responses of that same choice;
// do not independently select a size/tree for each transition. This models
// downstream sizing opportunity, not circuit STA.
// Family-average input caps remain an approximation: a chosen size is
// not fed back into sink caps. Sparse geometric knots define continuous
// monotone PWLs; the last secant is extrapolated. Virtual buffer trees
// charge delay and area but do not model ABC's sink grouping. Gain 9 is
// ABC buffer's default gain 3 squared for noninverting buffers.
typedef struct Scm_SizedType_t_ Scm_SizedType_t;
struct Scm_SizedType_t_
{
    Scm_Arc_t       Arcs[SCM_LEAF_MAX];
    float           ExtraArea;      // area beyond the representative size, in AreaW units
};

/**Function*************************************************************

  Synopsis    [Returns the worst output slew of a sized cell at a load.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_SizedSlew( Scm_SizedType_t * t, int nPins, float Load )
{
    float Slew = 0.0f;
    int k;
    for ( k = 0; k < nPins; k++ )
        Slew = Abc_MaxFloat(Slew, t->Arcs[k].Slew0 + t->Arcs[k].SlewLoad * Load);
    return Slew;
}

/**Function*************************************************************

  Synopsis    [Updates the envelopes with one sized cell and buffer tree at a load.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_SizedConsider( Scm_Man_t * p, Mio_Cell2_t * c, Scm_SizedType_t * t,
    float Root, float Extra, float Area, float * Best, float * BestArea,
    Scm_BufferType_t * buf, int depth, float RfDelays[2][SCM_LEAF_MAX], float RfSlew[2] )
{
    float Score = -FLT_MAX;
    int k, u;
    // The input-slew coefficient is the family's, in selection as in evaluation;
    // the intrinsic and load terms and the output slew are the size's.
    for ( k = 0; k < (int)c->nFanins; k++ )
        Score = Abc_MaxFloat(Score, t->Arcs[k].Delay0 + t->Arcs[k].DelayLoad * Root +
            Extra + Scm_ManArc(p, c, k)->DelaySlew * p->AveSlew);

    Area += t->ExtraArea;
    if ( Score > *Best || (Score == *Best && Area >= *BestArea) ) return;
    *Best = Score;
    *BestArea = Area;
    // the same size and tree for both transitions; a tree of depth d adds d buffers at gain 9
    for ( u = 0; u < 2; u++ )
    {
        float sr = 0, extra = 0;
        for ( k = 0; k < (int)c->nFanins; k++ )
            sr = Abc_MaxFloat(sr, t->Arcs[k].RfSlew0[u] + t->Arcs[k].RfSlewLoad[u]*Root);
        RfSlew[u] = sr;
        if ( buf )
        {
            float sb = Abc_MaxFloat(0, buf->Arc.RfSlew0[u] + buf->Arc.RfSlewLoad[u]*9*buf->Cap);
            float db = buf->Arc.RfDelay0[u] + buf->Arc.RfDelayLoad[u]*9*buf->Cap;
            extra = db + buf->Arc.RfDelaySlew[u]*sr + (depth-1)*(db + buf->Arc.RfDelaySlew[u]*sb);
            RfSlew[u] = sb;
        }
        for ( k = 0; k < (int)c->nFanins; k++ )
            RfDelays[u][k] = t->Arcs[k].RfDelay0[u] + t->Arcs[k].RfDelayLoad[u]*Root + extra;
    }
}

/**Function*************************************************************

  Synopsis    [Builds the delay, slew and cost envelopes of a cell over its sizes and
  buffer trees.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManSizedCellPwls( Scm_Man_t * p, Mio_Cell2_t * c, Scm_BufferType_t * Buffers, int nBuffers, float Cap )
{
    SC_Cell * rep = Scm_ManSclCell(p, c), * cell;
    Scm_SizedType_t * Types;
    float PrevLoad = 0, PrevArea = 0;
    float PrevRfD[2][SCM_LEAF_MAX] = {{0}}, PrevRfS[2] = {0};
    int nTypes = 0, i, j, k, t, b, u;
    if ( !rep || rep->area <= 0 ) return 0;
    SC_RingForEachCell(rep, cell, i) nTypes++;
    Types = ABC_CALLOC(Scm_SizedType_t, Abc_MaxInt(1, nTypes));
    nTypes = 0;
    SC_RingForEachCell(rep, cell, i)
    {
        Scm_SizedType_t * type = Types + nTypes;
        if ( cell->fSkip ) continue;
        for ( k = 0; k < (int)c->nFanins; k++ )
        {
            Scm_Arc_t * a = type->Arcs + k;
            if ( !Scm_ManFitArcCached(p, cell, k, a) ) { ABC_FREE(Types); return 0; }
            Scm_ArcBlendUnit( a, p->UnitDelay );
        }
        type->ExtraArea = c->AreaW * Abc_MaxFloat(0, cell->area / rep->area - 1.0f);
        nTypes++;
    }
    if ( !nTypes ) { ABC_FREE(Types); return 0; }
    // 15 load knots, 0 and Cap * 4^(j-2) for j = 1..14; the last segment extends to SCM_LOAD_INF
    for ( j = 0; j < 15; j++ )
    {
        float Load = j ? Cap * powf(4.0f, (float)j - 2.0f) : 0.0f;
        float Best = FLT_MAX, Area = FLT_MAX;
        float RfD[2][SCM_LEAF_MAX] = {{0}}, RfS[2] = {0};
        float Hi = j == 14 ? SCM_LOAD_INF : Load;
        for ( t = 0; t < nTypes; t++ )
        {
            Scm_SizedType_t * type = Types + t;
            Scm_SizedConsider(p, c, type, Load, 0, 0, &Best, &Area, NULL, 0, RfD, RfS);
            for ( b = 0; b < nBuffers; b++ )
            {
                Scm_BufferType_t * buf = Buffers + b;
                float Scale = 1.0f, Count = 0, Root = Load;
                float BufSlew = Abc_MaxFloat(0, buf->Arc.Slew0 + buf->Arc.SlewLoad * 9 * buf->Cap);
                float BufDelay = buf->Arc.Delay0 + buf->Arc.DelayLoad * 9 * buf->Cap;
                int Depth;
                // buffer trees of up to 16 levels, each dividing the load by the gain 9
                for ( Depth = 1; Depth <= 16 && Root > buf->Cap; Depth++ )
                {
                    float Extra;
                    Scale *= 9;
                    Root = Abc_MaxFloat(buf->Cap, Load / Scale);
                    Count += ceilf(Load / (Scale * buf->Cap));
                    Extra = BufDelay + buf->Arc.DelaySlew * Scm_SizedSlew(type, c->nFanins, Root) +
                        (Depth - 1) * (BufDelay + buf->Arc.DelaySlew * BufSlew);
                    Scm_SizedConsider(p, c, type, Root, Extra, Count * buf->Area,
                        &Best, &Area, buf, Depth, RfD, RfS);
                }
            }
        }
        Area = Abc_MaxFloat(Area, PrevArea);
        if ( j )
        {
            float Slope = (Area - PrevArea) / (Load - PrevLoad);
            Scm_PwlPush(p->pEnvCosts + c->Id, PrevLoad, Hi,
                PrevArea - Slope * PrevLoad, Slope);
        }
        for ( u = 0; u < 2; u++ )
        {
            for ( k = 0; k < (int)c->nFanins; k++ )
            {
                RfD[u][k] = Abc_MaxFloat(RfD[u][k], PrevRfD[u][k]);
                if ( j )
                {
                    float slope = (RfD[u][k] - PrevRfD[u][k]) / (Load - PrevLoad);
                    Scm_PwlPush(p->pEnvDelays + 2*(c->Id*SCM_LEAF_MAX + k) + u, PrevLoad, Hi, PrevRfD[u][k] - slope*PrevLoad, slope);
                }
                PrevRfD[u][k] = RfD[u][k];
            }
            RfS[u] = Abc_MaxFloat(RfS[u], PrevRfS[u]);
            if ( j )
            {
                float slope = (RfS[u] - PrevRfS[u]) / (Load - PrevLoad);
                Scm_PwlPush(p->pEnvSlews + 2*c->Id + u, PrevLoad, Hi, PrevRfS[u] - slope*PrevLoad, slope);
            }
            PrevRfS[u] = RfS[u];
        }
        PrevLoad = Load; PrevArea = Area;
    }
    ABC_FREE(Types);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares the buffer family of the envelopes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManEnvStart( Scm_Man_t * p )
{
    SC_Cell * pBuf = Scm_ManSclCell(p, p->pCells + 2);
    Scm_BufferType_t * Types;
    SC_Cell * pMember;
    float Cap;
    int i, nTypes = 0;
    if ( !pBuf ) return 0;
    Cap = Scm_ManCellPinCap(p, pBuf, 0);
    if ( Cap <= 0 ) return 0;
    Types = ABC_ALLOC(Scm_BufferType_t, SC_LibCellNum(p->pScl));
    SC_RingForEachCell(pBuf, pMember, i)
    {
        Scm_BufferType_t * b = Types + nTypes;
        if ( pMember->fSkip ) continue;
        memset(b, 0, sizeof(*b));
        if ( !Scm_ManFitArcCached(p, pMember, 0, &b->Arc) ) continue;
        b->Cap = SC_CellPinCap(pMember, 0);
        b->Area = p->pCells[2].AreaW * (pMember->area / pBuf->area);
        if ( b->Cap <= 0 || b->Area <= 0 ) continue;
        Scm_ArcBlendUnit( &b->Arc, p->UnitDelay );
        nTypes++;
    }
    if ( !nTypes ) { ABC_FREE(Types); return 0; }
    p->pEnvDelays = ABC_CALLOC(Scm_Pwl_t, 2*p->nCells*SCM_LEAF_MAX);
    p->pEnvSlews = ABC_CALLOC(Scm_Pwl_t, 2*p->nCells);
    p->pEnvCosts = ABC_CALLOC(Scm_Pwl_t, p->nCells);
    // Each cell's envelope depends only on library data and these buffer
    // types; build it on first use (identical values, any order).
    p->pEnvBufs = Types; p->nEnvBufs = nTypes; p->EnvCap = Cap;
    p->pEnvState = ABC_CALLOC(unsigned char, p->nCells);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Builds the envelopes of one cell and records whether this succeeded.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManEnsureEnvBuild( Scm_Man_t * p, Mio_Cell2_t * pCell )
{
    int i = pCell->Id, k, fOk;
    if ( !pCell->nFanins ) { p->pEnvState[i] = 1; return; }
    fOk = Scm_ManSizedCellPwls(p, pCell, (Scm_BufferType_t *)p->pEnvBufs, p->nEnvBufs, p->EnvCap);
    for ( k = 0; fOk && k < 2 * (int)pCell->nFanins; k++ )
        fOk = Scm_PwlCheck(p->pEnvDelays + 2 * i * SCM_LEAF_MAX + k);
    fOk = fOk && Scm_PwlCheck(p->pEnvSlews + 2 * i) && Scm_PwlCheck(p->pEnvSlews + 2 * i + 1) &&
          Scm_PwlCheck(p->pEnvCosts + i);
    p->pEnvState[i] = fOk ? 1 : 2;
    if ( !fOk )
    {
        p->fEnvError = 1;
        Abc_Print( 0, "&scmap cannot model Liberty cell \"%s\" over load (its area must be positive and its timing finite).\n",
            pCell->pName ? pCell->pName : "unknown" );
    }
}

/**Function*************************************************************

  Synopsis    [Appends a path to a residual tail.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_RfLinesPush( Scm_RfLines_t * pSet, Scm_RfLine_t Fan )
{
    if ( pSet->nFans == pSet->nAlloc )
    {
        pSet->nAlloc = pSet->nAlloc ? 2 * pSet->nAlloc : 4;
        pSet->pFans = ABC_REALLOC(Scm_RfLine_t, pSet->pFans, pSet->nAlloc);
    }
    pSet->pFans[pSet->nFans++] = Fan;
}

/**Function*************************************************************

  Synopsis    [Evaluates a residual tail at given rise/fall slews.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_RfPair_t Scm_RfLinesEval( Scm_RfLines_t * pSet, Scm_RfPair_t Slew )
{
    Scm_RfPair_t Tail = {{-FLT_MAX, -FLT_MAX}};
    int i, iPol;
    for ( i = 0; i < pSet->nFans; i++ )
        for ( iPol = SCM_FALL; iPol <= SCM_RISE; iPol++ )
            if ( pSet->pFans[i].Valid[iPol] )
            {
                // A separately rounded product (no fused multiply-add): near-tied choices on
                // deep networks depend on it.
                float SlewDelay = pSet->pFans[i].SlewCoeff[iPol] * Slew.Value[iPol];
                Tail.Value[iPol] = Abc_MaxFloat(Tail.Value[iPol],
                    pSet->pFans[i].Constant[iPol] + SlewDelay);
            }
    return Tail;
}

/**Function*************************************************************

  Synopsis    [Returns the larger value of a rise/fall pair.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Scm_ManRfPairMax( Scm_RfPair_t Pair )
{
    return Abc_MaxFloat(Pair.Value[SCM_FALL], Pair.Value[SCM_RISE]);
}

/**Function*************************************************************

  Synopsis    [Returns the rise/fall load of a literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_RfPair_t Scm_ManRfLoad( Scm_Man_t * p, int iLit )
{
    Scm_RfPair_t Load;
    if ( p->pRfLoads ) return p->pRfLoads[iLit];
    Load.Value[0] = Load.Value[1] = Vec_FltEntry(&p->vLoads, iLit);
    return Load;
}

/**Function*************************************************************

  Synopsis    [Returns the rise/fall input capacitance of a cell pin.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_RfPair_t Scm_ManRfPinCap( Scm_Man_t * p, Mio_Cell2_t * pCell, int k )
{
    SC_Cell * pSclCell = Scm_ManSclCell(p, pCell);
    SC_Pin * pPin = SC_CellPin(pSclCell, k);
    Scm_RfPair_t Cap;
    if ( p->pFamilyRfCaps ) return p->pFamilyRfCaps[pSclCell->Id * SCM_LEAF_MAX + k];
    Cap.Value[0] = pPin->fall_cap;
    Cap.Value[1] = pPin->rise_cap;
    return Cap;
}

/**Function*************************************************************

  Synopsis    [Collects the rise/fall load of every literal of the cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManCollectLoadsRf( Scm_Man_t * p, double * pLoads )
{
    Gia_Obj_t * pObj;
    int i, c, k, t, iVar, fCompl, nLits = 2 * Gia_ManObjNum(p->pGia), fAlloc = pLoads == NULL;
    if ( fAlloc ) pLoads = ABC_ALLOC(double, 2*nLits);
    // Match the incremental accumulator; round only when the timing model reads a load.
    memset(pLoads, 0, sizeof(double) * 2*nLits);
    Gia_ManForEachAnd(p->pGia, pObj, i)
    {
        for ( c = 0; c < 2; c++ )
        if ( Scm_ObjMapRefNum(p, i, c) )
        {
            Scm_Mat_t * pM = Scm_ObjMatch(p, i, c);
            if ( pM->fCompl )
            {
                Scm_RfPair_t Cap = Scm_ManRfPinCap(p, p->pCells + 3, 0);
                for ( t = 0; t < 2; t++ )
                    pLoads[2*Abc_Var2Lit(i, !c)+t] += Cap.Value[t];
            }
            else if ( pM->CutH )
            {
                Mio_Cell2_t * pCell = Scm_ManCell(p, pM->Gate);
                int * pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, i), pM->CutH);
                Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
                {
                    Scm_RfPair_t Cap = Scm_ManRfPinCap(p, pCell, k);
                    for ( t = 0; t < 2; t++ )
                        pLoads[2*Abc_Var2Lit(iVar, fCompl)+t] += Cap.Value[t];
                }
            }
        }
    }
    Gia_ManForEachCiId(p->pGia, i, c)
        if ( Scm_ObjMapRefNum(p, i, 1) )
        {
            Scm_RfPair_t Cap = Scm_ManRfPinCap(p, p->pCells + 3, 0);
            for ( t = 0; t < 2; t++ )
                pLoads[2*Abc_Var2Lit(i, 0)+t] += Cap.Value[t];
        }
    for ( i = 0; i < nLits; i++ )
        for ( t = 0; t < 2; t++ ) p->pRfLoads[i].Value[t] = (float)pLoads[2*i+t];
    if ( fAlloc ) ABC_FREE(pLoads);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Evaluates the delay of a fitted arc for one output transition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Scm_ManRfDelay( Scm_Arc_t * pArc, int iOut, float Load, float InSlew )
{
    return pArc->RfDelay0[iOut] + pArc->RfDelayLoad[iOut] * Load +
        pArc->RfDelaySlew[iOut] * InSlew;
}

/**Function*************************************************************

  Synopsis    [Evaluates the output slew of a fitted arc for one output transition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline float Scm_ManRfSlew( Scm_Arc_t * pArc, int iOut, float Load )
{
    return Abc_MaxFloat(0.0f,
        pArc->RfSlew0[iOut] + pArc->RfSlewLoad[iOut] * Load);
}

/**Function*************************************************************

  Synopsis    [Updates the rise/fall arrival and slew of an output with one input
  arc.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManRfArcAccumulate( Scm_Arc_t * pArc, Scm_RfPair_t Load,
    Scm_RfPair_t ChildArrival, Scm_RfPair_t ChildSlew,
    Scm_RfPair_t * pArrival, Scm_RfPair_t * pSlew )
{
    int iOut;
    for ( iOut = SCM_FALL; iOut <= SCM_RISE; iOut++ )
    {
        if ( pArc->TimingSense == sc_ts_Pos || pArc->TimingSense == sc_ts_Non )
            pArrival->Value[iOut] = Abc_MaxFloat(pArrival->Value[iOut],
                ChildArrival.Value[iOut] + Scm_ManRfDelay(pArc, iOut,
                    Load.Value[iOut], ChildSlew.Value[iOut]));
        if ( pArc->TimingSense == sc_ts_Neg || pArc->TimingSense == sc_ts_Non )
            pArrival->Value[iOut] = Abc_MaxFloat(pArrival->Value[iOut],
                ChildArrival.Value[!iOut] + Scm_ManRfDelay(pArc, iOut,
                    Load.Value[iOut], ChildSlew.Value[!iOut]));
        pSlew->Value[iOut] = Abc_MaxFloat(pSlew->Value[iOut],
            Scm_ManRfSlew(pArc, iOut, Load.Value[iOut]));
    }
}

/**Function*************************************************************

  Synopsis    [Returns the rise/fall output slew of a cell at a load through its
  envelope.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_RfPair_t Scm_ManRfCellSlew( Scm_Man_t * p, Mio_Cell2_t * pCell, Scm_RfPair_t Load )
{
    Scm_RfPair_t Result;
    int t;
    Scm_ManEnsureEnv(p, pCell);
    for ( t = 0; t < 2; t++ )
        Result.Value[t] = Abc_MaxFloat(0, Scm_PwlEval(p->pEnvSlews + 2*pCell->Id + t, Load.Value[t]));
    return Result;
}

/**Function*************************************************************

  Synopsis    [Computes the rise/fall arrivals and slews of the cover and its delay.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManTimeArrivals( Scm_Man_t * p )
{
    Gia_Obj_t * pObj;
    int nLits = 2 * Gia_ManObjNum(p->pGia), i, c, k, nBad = 0;
    Scm_RfPair_t * pArr = ABC_CALLOC(Scm_RfPair_t, nLits);
    Scm_RfPair_t * pSlew = ABC_CALLOC(Scm_RfPair_t, nLits);
    float ExactPo = 0.0f;
    assert(p->pRfArrs != NULL && p->pRfSlews != NULL);
    Gia_ManForEachCiId(p->pGia, i, c)
        if ( Scm_ObjMapRefNum(p, i, 1) )
        {
            int iLit = Abc_Var2Lit(i, 1);
            Scm_Arc_t Temp, * pArc = Scm_ManArcAtLoad(p, p->pCells + 3, 0, Scm_ManRfLoad(p, iLit), &Temp);
            Scm_RfPair_t Zero = {{0.0f, 0.0f}};
            pArr[iLit].Value[0] = pArr[iLit].Value[1] = -FLT_MAX;
            Scm_ManRfArcAccumulate(pArc,
                Scm_ManRfLoad(p, iLit), Zero, Zero,
                pArr + iLit, pSlew + iLit);
        }
    Gia_ManForEachAnd(p->pGia, pObj, i)
    {
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) )
            {
                int iLit = Abc_Var2Lit(i, c);
                Scm_Mat_t * pM = Scm_ObjMatch(p, i, c);
                Mio_Cell2_t * pCell;
                int * pCut, iVar, fCompl;
                Scm_RfPair_t Load;
                if ( pM->fCompl ) continue;
                pCell = Scm_ManCell(p, pM->Gate);
                Load = Scm_ManRfLoad(p, iLit);
                if ( pM->CutH == 0 || pCell->nFanins == 0 ) continue;
                pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, i), pM->CutH);
                if ( Scm_CutSize(pCut) != (int)pCell->nFanins ||
                     !Scm_CfgIsCutPermutation(pM->Cfg, Scm_CutSize(pCut)) )
                {
                    nBad++;
                    continue;
                }
                pArr[iLit].Value[0] = pArr[iLit].Value[1] = -FLT_MAX;
                Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
                {
                    Scm_Arc_t Temp, * pArc = Scm_ManArcAtLoad(p, pCell, k, Scm_ManRfLoad(p, iLit), &Temp);
                    int iChildLit = Abc_Var2Lit(iVar, fCompl);
                    if ( pArc == NULL || !pArc->fValid )
                    {
                        nBad++;
                        continue;
                    }
                    Scm_ManRfArcAccumulate(pArc, Load, pArr[iChildLit],
                        pSlew[iChildLit], pArr + iLit, pSlew + iLit);
                }
            }
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) &&
                 Scm_ObjMatch(p, i, c)->fCompl )
            {
                int iLit = Abc_Var2Lit(i, c);
                int iSrcLit = Abc_Var2Lit(i, !c);
                Scm_Arc_t Temp, * pArc = Scm_ManArcAtLoad(p, p->pCells + 3, 0, Scm_ManRfLoad(p, iLit), &Temp);
                pArr[iLit].Value[0] = pArr[iLit].Value[1] = -FLT_MAX;
                Scm_ManRfArcAccumulate(pArc,
                    Scm_ManRfLoad(p, iLit), pArr[iSrcLit],
                    pSlew[iSrcLit], pArr + iLit, pSlew + iLit);
            }
    }
    Gia_ManForEachCo(p->pGia, pObj, i)
        ExactPo = Abc_MaxFloat(ExactPo,
            Scm_ManRfPairMax(pArr[Gia_ObjFaninLit0p(p->pGia, pObj)]));
    for ( i = 0; i < nLits; i++ )
    {
        if ( !isfinite(pArr[i].Value[0]) || !isfinite(pArr[i].Value[1]) ||
             !isfinite(pSlew[i].Value[0]) || !isfinite(pSlew[i].Value[1]) )
            nBad++;
        p->pArrMax[i] = Scm_ManRfPairMax(pArr[i]);
        p->pSlewMax[i] = Scm_ManRfPairMax(pSlew[i]);
    }
    memcpy(p->pRfArrs, pArr, sizeof(Scm_RfPair_t) * nLits);
    memcpy(p->pRfSlews, pSlew, sizeof(Scm_RfPair_t) * nLits);
    p->ModelDelay = ExactPo;
    ABC_FREE(pArr);
    ABC_FREE(pSlew);
    return nBad == 0;
}

/**Function*************************************************************

  Synopsis    [Collects the load of every literal of the cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManCollectLoads( Scm_Man_t * p )
{
    Gia_Obj_t * pObj;
    int nLits = 2 * Gia_ManObjNum(p->pGia), i, c, iVar, fCompl, k;
    Vec_FltFill(&p->vLoads, nLits, 0.0f);
    Gia_ManForEachAnd(p->pGia, pObj, i)
    {
        for ( c = 0; c < 2; c++ )
        if ( Scm_ObjMapRefNum(p, i, c) )
        {
            Scm_Mat_t * pM = Scm_ObjMatch(p, i, c);
            Mio_Cell2_t * pCell;
            SC_Cell * pSclCell;
            int * pCut;
            if ( pM->fCompl )
            {
                if ( !Scm_ObjMapRefNum(p, i, !c) ) return 0;
                Vec_FltAddToEntry(&p->vLoads,
                    Abc_Var2Lit(i, !c), Scm_ManInvInputCap(p));
                continue;
            }
            pCell = Scm_ManCell(p, pM->Gate);
            pSclCell = Scm_ManSclCell(p, pCell);
            if ( pM->CutH <= 0 || (pCell->nFanins && pSclCell == NULL) )
                return 0;
            pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, i), pM->CutH);
            if ( Scm_CutSize(pCut) != (int)pCell->nFanins ||
                 !Scm_CfgIsCutPermutation(pM->Cfg, Scm_CutSize(pCut)) ) return 0;
            Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
            {
                if ( !Scm_ObjMapRefNum(p, iVar, fCompl) )
                    return 0;
                Vec_FltAddToEntry(&p->vLoads,
                    Abc_Var2Lit(iVar, fCompl),
                    Scm_ManCellPinCap(p, pSclCell, k));
            }
        }
    }
    Gia_ManForEachCiId(p->pGia, i, c)
        if ( Scm_ObjMapRefNum(p, i, 1) )
            Vec_FltAddToEntry(&p->vLoads, Abc_Var2Lit(i, 0), Scm_ManInvInputCap(p));
    return 1;
}

/**Function*************************************************************

  Synopsis    [Recomputes the loads and the timing of the whole cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManTimeCover( Scm_Man_t * p )
{
    if ( !Scm_ManCollectLoads(p) ) return 0;
    if ( p->pRfLoads && !Scm_ManCollectLoadsRf(p, NULL) ) return 0;
    return Scm_ManTimeArrivals(p);
}

/**Function*************************************************************

  Synopsis    [Appends a candidate match to a growing list.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CandPush( Scm_Cand_t ** ppList, int * pnList, int * pnAlloc, Scm_Mat_t * pM, word Area )
{
    if ( *pnList == *pnAlloc )
    {
        *pnAlloc = *pnAlloc ? 2 * *pnAlloc : 16;
        *ppList = ABC_REALLOC(Scm_Cand_t, *ppList, *pnAlloc);
    }
    (*ppList)[*pnList].M = *pM;
    (*ppList)[*pnList].Area = Area;
    (*pnList)++;
}

/**Function*************************************************************

  Synopsis    [Counts the exact area a match adds, stopping once it reaches a limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_ManAreaLimit_rec( Scm_Man_t * p, int i, int c, Scm_Mat_t * pM, word Limit )
{
    int k, v, phase, * pCut;
    word Area = pM->fCompl ? p->InvAreaW :
        (Scm_ObjCutSetId(p, i) ? Scm_ManCell(p, pM->Gate)->AreaW : 0);
    if ( Area >= Limit ) return Area;
    if ( pM->fCompl )
    {
        Vec_IntPush(&p->vBackup, Abc_Var2Lit(i, !c));
        if ( !Scm_ObjMapRefInc(p, i, !c) )
            Area += Scm_ManAreaLimit_rec(p, i, !c,
                Scm_ObjMatch(p, i, !c), Limit - Area);
        return Area;
    }
    if ( !Scm_ObjCutSetId(p, i) ) return Area;
    pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, i), pM->CutH);
    Scm_CutForEachVarCompl(pCut, pM->Cfg, v, phase, k)
    {
        Vec_IntPush(&p->vBackup, Abc_Var2Lit(v, phase));
        if ( !Scm_ObjMapRefInc(p, v, phase) )
            Area += Scm_ManAreaLimit_rec(p, v, phase,
                Scm_ObjMatch(p, v, phase), Limit - Area);
        if ( Area >= Limit ) break;
    }
    return Area;
}

/**Function*************************************************************

  Synopsis    [Returns the exact area a match adds, or at least Limit, keeping
  references unchanged.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_ManRefArea( Scm_Man_t * p, int i, int c, Scm_Mat_t * pM, word Limit )
{
    word Area;
    int Lit, k;

    // Exact pruning: once positive cell costs exhaust the removable
    // cone's area, this candidate cannot save area.  Roll back every
    // reference touched by the partial traversal before returning.
    Vec_IntClear(&p->vBackup);
    Area = Scm_ManAreaLimit_rec(p, i, c, pM, Limit);
    Vec_IntForEachEntry(&p->vBackup, Lit, k)
        Scm_ObjMapRefDec(p, Abc_Lit2Var(Lit), Abc_LitIsCompl(Lit));
    return Area;
}

/**Function*************************************************************

  Synopsis    [Collects the candidate matches of a node phase, optionally with their
  exact area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManCandidates( Scm_Man_t * p, int iObj, int c,
    Scm_Mat_t * pOld, word Freed, Scm_Cand_t ** ppList,
    int * pnList, int * pnAlloc, int fMeasureArea )
{
    int iCut, iMatch, Info, Offset, * pCut;
    int * pCutSet = Scm_ObjCutSet(p, iObj);
    Scm_SetForEachCut(pCutSet, pCut, iCut)
    {
        int nFans = Scm_CutSize(pCut);
        int iFuncLit = Scm_CutFunc(pCut);
        int fComplExt = Abc_LitIsCompl(iFuncLit);
        Vec_Int_t * vArr;
        if ( nFans == 0 )
        {
            Scm_Mat_t M = {0};
            M.Gate = c ^ (iFuncLit == 1);
            M.CutH = Scm_CutHandle(pCutSet, pCut);
            M.Cfg = Scm_Int2Cfg(0);
            if ( !Scm_MatSame(pOld, &M) )
            {
                word Area = fMeasureArea ? Scm_ManRefArea(p, iObj, c, &M, Freed) : 0;
                if ( Area < Freed )
                    Scm_CandPush(ppList, pnList, pnAlloc, &M, Area);
            }
            continue;
        }
        if ( !Scm_CutLeavesAreValid(Scm_CutLeaves(pCut), nFans, iObj) ||
             Abc_Lit2Var(iFuncLit) >= Vec_WecSize(p->vTt2Match) ) continue;
        vArr = Vec_WecEntry(p->vTt2Match, Abc_Lit2Var(iFuncLit));
        Vec_IntForEachEntryDouble(vArr, Info, Offset, iMatch)
        {
            Scm_Cfg_t Cfg = Scm_Int2Cfg(Offset);
            Mio_Cell2_t * pCell = Scm_ManCell(p, Info);
            SC_Cell * pSclCell = Scm_ManSclCell(p, pCell);
            Scm_Mat_t M = {0};
            int k, fValid = pSclCell != NULL;
            word Area;
            if ( (Cfg.fCompl ^ fComplExt) != c ||
                 nFans != (int)pCell->nFanins ||
                 !Scm_CfgIsCutPermutation(Cfg, nFans) ) continue;
            for ( k = 0; fValid && k < nFans; k++ )
            {
                Scm_Arc_t * pArc = Scm_ManArc(p, pCell, k);
                fValid = pArc != NULL && pArc->fValid;
            }
            if ( !fValid ) continue;
            Cfg.fCompl = 0;
            M.Gate = Info;
            M.CutH = Scm_CutHandle(pCutSet, pCut);
            M.Cfg = Cfg;
            if ( Scm_MatSame(pOld, &M) ) continue;

            Area = fMeasureArea ? Scm_ManRefArea(p, iObj, c, &M, Freed) : 0;
            if ( Area < Freed )
                Scm_CandPush(ppList, pnList, pnAlloc, &M, Area);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Frees a refinement context.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxFree( Scm_Ctx_t * pCtx )
{
    int i;
    if ( pCtx == NULL ) return;
    if ( pCtx->pFans )
        for ( i = 0; i < pCtx->nLits; i++ )
        {
            ABC_FREE(pCtx->pFans[i].pRoots);
            ABC_FREE(pCtx->pFans[i].pPins);
        }
    if ( pCtx->pTails )
        for ( i = 0; i < pCtx->nLits; i++ )
            ABC_FREE(pCtx->pTails[i].pFans);
    if (pCtx->pArcCache) {
        for (i=0;i<pCtx->nLits;i++) ABC_FREE(pCtx->pArcCache[i]);
        ABC_FREE(pCtx->pArcCache);
    }
    ABC_FREE(pCtx->pFans);
    ABC_FREE(pCtx->pTails);
    ABC_FREE(pCtx->pLoadSums);
    ABC_FREE(pCtx->pRfLoadSums);
    ABC_FREE(pCtx->pBufferAreas);
    ABC_FREE(pCtx->pTrialArrMax);
    ABC_FREE(pCtx->pTrialSlewMax);
    ABC_FREE(pCtx->pTrialRfArrs);
    ABC_FREE(pCtx->pTrialRfSlews);
    ABC_FREE(pCtx->pTailBase);
    ABC_FREE(pCtx->pTouched);
    ABC_FREE(pCtx->pComputed);
    ABC_FREE(pCtx->pConeSeen);
    ABC_FREE(pCtx->pTailSeen);
    ABC_FREE(pCtx->pTailValid);
    ABC_FREE(pCtx->pIsPo);
    Vec_IntFreeP(&pCtx->vOldSeeds);
    Vec_IntFreeP(&pCtx->vTrialSeeds);
    ABC_FREE(pCtx->pSeedStamp);
    ABC_FREE(pCtx->pEdgePos);
    Vec_IntFreeP(&pCtx->vSeedSort);
    Vec_IntFreeP(&pCtx->vAffected);
    Vec_IntFreeP(&pCtx->vScoreOutputs);
    for ( i = 0; i < pCtx->nQueueLevels; i++ )
        ABC_FREE(pCtx->pQueueBits[i]);
    Vec_IntFreeP(&pCtx->vConeStack);
    Vec_IntFreeP(&pCtx->vBoundary);
    Vec_FltFreeP(&pCtx->vBoundaryPriorities);
    Vec_IntFreeP(&pCtx->vTailStack);
    Vec_IntFreeP(&pCtx->vTailWork);
    Vec_IntFreeP(&pCtx->vTailSort);
    ABC_FREE(pCtx);
}

static void Scm_ArcCacheInvalidate( Scm_ArcNode_t ** pCache, int nLits );

/**Function*************************************************************

  Synopsis    [Frees a context but keeps its per-literal fanout, tail-line and arc-
  cache arrays, with their capacity, for the next context of the same
  manager. Scm_CtxStart empties them before use, so no stale entry is
  read.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxRecycle( Scm_Man_t * p, Scm_Ctx_t * pCtx )
{
    Scm_Ctx_t * pSpare;
    if ( pCtx == NULL ) return;
    Scm_CtxFree( p->pCtxSpare );
    pSpare = ABC_CALLOC( Scm_Ctx_t, 1 );
    pSpare->nLits = pCtx->nLits;
    pSpare->pFans = pCtx->pFans;               pCtx->pFans = NULL;
    pSpare->pTails = pCtx->pTails; pCtx->pTails = NULL;
    pSpare->pArcCache = pCtx->pArcCache;       pCtx->pArcCache = NULL;
    p->pCtxSpare = pSpare;
    Scm_CtxFree( pCtx );
}

/**Function*************************************************************

  Synopsis    [Adds or removes a fanout edge of a literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxFanEdit( Scm_Ctx_t * pCtx, int iChildLit, int iRootLit, int iPin, int Sign )
{
    Scm_Fanouts_t * pSet = pCtx->pFans + iChildLit;
    int k;
    if ( Sign > 0 )
    {
        if ( pSet->nRoots == pSet->nAlloc )
        {
            pSet->nAlloc = pSet->nAlloc ? 2 * pSet->nAlloc : 4;
            pSet->pRoots = ABC_REALLOC(int, pSet->pRoots, pSet->nAlloc);
            pSet->pPins = ABC_REALLOC(unsigned char, pSet->pPins,
                pSet->nAlloc);
        }
        pSet->pRoots[pSet->nRoots] = iRootLit;
        pSet->pPins[pSet->nRoots] = iPin;
        if ( pCtx->pEdgePos ) pCtx->pEdgePos[iRootLit * SCM_LEAF_MAX + iPin] = pSet->nRoots;
        pSet->nRoots++;
        return;
    }
    // An edge (root, pin) occurs once in its child's list, so the indexed
    // removal reproduces the scan below (same slot, same swap with the last).
    if ( pCtx->pEdgePos )
    {
        k = pCtx->pEdgePos[iRootLit * SCM_LEAF_MAX + iPin];
        if ( k >= 0 && k < pSet->nRoots && pSet->pRoots[k] == iRootLit && pSet->pPins[k] == iPin )
        {
            pSet->pRoots[k] = pSet->pRoots[--pSet->nRoots];
            pSet->pPins[k] = pSet->pPins[pSet->nRoots];
            if ( k < pSet->nRoots )
                pCtx->pEdgePos[pSet->pRoots[k] * SCM_LEAF_MAX + pSet->pPins[k]] = k;
            return;
        }
    }
    for ( k = 0; k < pSet->nRoots; k++ )
        if ( pSet->pRoots[k] == iRootLit &&
             pSet->pPins[k] == iPin )
        {
            pSet->pRoots[k] = pSet->pRoots[--pSet->nRoots];
            pSet->pPins[k] = pSet->pPins[pSet->nRoots];
            if ( pCtx->pEdgePos && k < pSet->nRoots )
                pCtx->pEdgePos[pSet->pRoots[k] * SCM_LEAF_MAX + pSet->pPins[k]] = k;
            return;
        }
    pCtx->fError = 1;
}

/**Function*************************************************************

  Synopsis    [Adds or removes a fanout edge and its pin load.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxEdgeEdit( Scm_Man_t * p, Scm_Ctx_t * pCtx,
    int iChildLit, int iRootLit, int iPin, float Cap, int Sign, int fInitial )
{
    Scm_CtxFanEdit(pCtx, iChildLit, iRootLit, iPin, Sign);
    if ( fInitial ) return;
    // Trials remove and restore the same pin loads many times: the sums are kept in double
    // (float add/subtract would drift) and rounded only where the model reads them.
    pCtx->pLoadSums[iChildLit] += (double)Sign * (double)Cap;
    Vec_FltWriteEntry(&p->vLoads, iChildLit,
        (float)pCtx->pLoadSums[iChildLit]);
    if ( pCtx->pCollectSeeds )
        Vec_IntPush(pCtx->pCollectSeeds, iChildLit),
        Vec_IntPush(pCtx->pCollectSeeds, iRootLit);
}

/**Function*************************************************************

  Synopsis    [Adds or removes the fanout edges and pin loads of a match.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxMatchEdit( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iObj, int c, Scm_Mat_t * pM, int Sign, int fInitial )
{
    int iRootLit = Abc_Var2Lit(iObj, c), iVar, fCompl, k, * pCut;
    Mio_Cell2_t * pCell;
    SC_Cell * pSclCell;
    if ( !fInitial && pCtx->pCollectSeeds )
        Vec_IntPush(pCtx->pCollectSeeds, iRootLit);
    if ( pM->fCompl )
    {
        if ( pCtx->pRfLoadSums && !fInitial )
        {
            Scm_RfPair_t Cap = Scm_ManRfPinCap(p, p->pCells + 3, 0);
            int t, iLit = Abc_Var2Lit(iObj, !c);
            for ( t = 0; t < 2; t++ )
            {
                pCtx->pRfLoadSums[2*iLit+t] += (double)Sign * Cap.Value[t];
                p->pRfLoads[iLit].Value[t] = (float)pCtx->pRfLoadSums[2*iLit+t];
            }
        }
        Scm_CtxEdgeEdit(p, pCtx, Abc_Var2Lit(iObj, !c),
            iRootLit, 0, Scm_ManInvInputCap(p), Sign, fInitial);
        return;
    }
    if ( Scm_ObjCutSetId(p, iObj) == 0 ) return;
    pCell = Scm_ManCell(p, pM->Gate);
    if ( pCell->nFanins == 0 ) return;
    pSclCell = Scm_ManSclCell(p, pCell);
    if ( pSclCell == NULL || pM->CutH <= 0 )
    {
        pCtx->fError = 1;
        return;
    }
    pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
    if ( Scm_CutSize(pCut) != (int)pCell->nFanins ||
         !Scm_CfgIsCutPermutation(pM->Cfg, Scm_CutSize(pCut)) )
    {
        pCtx->fError = 1;
        return;
    }
    Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
    {
        if ( pCtx->pRfLoadSums && !fInitial )
        {
            Scm_RfPair_t Cap = Scm_ManRfPinCap(p, pCell, k);
            int t, iLit = Abc_Var2Lit(iVar, fCompl);
            for ( t = 0; t < 2; t++ )
            {
                pCtx->pRfLoadSums[2*iLit+t] += (double)Sign * Cap.Value[t];
                p->pRfLoads[iLit].Value[t] = (float)pCtx->pRfLoadSums[2*iLit+t];
            }
        }
        Scm_CtxEdgeEdit(p, pCtx, Abc_Var2Lit(iVar, fCompl),
            iRootLit, k, Scm_ManCellPinCap(p, pSclCell, k), Sign, fInitial);
    }
}

/**Function*************************************************************

  Synopsis    [A hierarchy of nonempty 64-bit words is a bounded integer priority
  queue.]

  Description [AIG IDs already give the topological order, so comparisons and
  repeated match lookups are unnecessary during propagation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxQueueStart( Scm_Ctx_t * pCtx, unsigned nKeys )
{
    unsigned nWords;
    do
    {
        nWords = (nKeys - 1) / 64 + 1;
        assert(pCtx->nQueueLevels < 6);
        pCtx->pQueueBits[pCtx->nQueueLevels++] = ABC_CALLOC(word, nWords);
        nKeys = nWords;
    }
    while ( nWords > 1 );
}

/**Function*************************************************************

  Synopsis    [Checks whether the timing queue is not empty.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxQueueHas( Scm_Ctx_t * pCtx )
{
    return pCtx->pQueueBits[pCtx->nQueueLevels - 1][0] != 0;
}

/**Function*************************************************************

  Synopsis    [Inserts an order key into the timing queue.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxQueuePush( Scm_Ctx_t * pCtx, unsigned Key )
{
    int Level;
    for ( Level = 0; Level < pCtx->nQueueLevels; Level++, Key >>= 6 )
    {
        word * pWord = pCtx->pQueueBits[Level] + (Key >> 6);
        word Old = *pWord;
        *pWord |= (word)1 << (Key & 63);
        if ( Old ) break;
    }
}

/**Function*************************************************************

  Synopsis    [Removes the smallest order key from the timing queue.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Scm_CtxQueuePop( Scm_Ctx_t * pCtx )
{
    unsigned Key = 0, Result;
    int Level;
    assert(Scm_CtxQueueHas(pCtx));
    for ( Level = pCtx->nQueueLevels - 1; Level >= 0; Level-- )
    {
        word Bits = pCtx->pQueueBits[Level][Key];
#if defined(__GNUC__) || defined(__clang__)
        Key = 64 * Key + __builtin_ctzll(Bits);
#else
        Key = 64 * Key + Abc_Tt6FirstBit(Bits);
#endif
    }
    Result = Key;
    for ( Level = 0; Level < pCtx->nQueueLevels; Level++, Key >>= 6 )
    {
        word * pWord = pCtx->pQueueBits[Level] + (Key >> 6);
        *pWord &= ~((word)1 << (Key & 63));
        if ( *pWord ) break;
    }
    return Result;
}

/**Function*************************************************************

  Synopsis    [Returns the modeled buffer-tree area of the net of a literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_ManBufferArea( Scm_Man_t * p, int Lit )
{
    int Obj = Abc_Lit2Var(Lit), c = Abc_LitIsCompl(Lit);
    Scm_Mat_t * pM;
    Mio_Cell2_t * pCell;
    if ( !Scm_ObjMapRefNum(p, Obj, c) || !Obj ||
         (Gia_ObjIsCi(Gia_ManObj(p->pGia, Obj)) && !c) ) return 0.0f;
    pM = Scm_ObjMatch(p, Obj, c);
    pCell = pM->fCompl ? p->pCells + 3 : Scm_ManCell(p, pM->Gate);
    if ( !pCell->nFanins ) return 0.0f;
    if ( p->pEnvCosts )
    {
        Scm_ManEnsureEnv(p, pCell);
        return Scm_PwlEval(p->pEnvCosts + pCell->Id,
            Vec_FltEntry(&p->vLoads, Lit));
    }
    return 0.0f;
}

/**Function*************************************************************

  Synopsis    [Only changed implementations and loads can change virtual buffer area.]

  Description [Count shared boundary nets once, including nets that disappear
  entirely. Same result as Vec_IntUniqify() (ascending, unique) for
  literal vectors: stamp-based deduplication, then an LSD radix sort of
  the unique entries. Called for every repair candidate; qsort dominated
  runtime on wide nets.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxSeedsUniqify( Scm_Ctx_t * pCtx, Vec_Int_t * vSeeds )
{
    int nSize = Vec_IntSize(vSeeds), i, k, Pass, Lit, * pSrc, * pDst, nBits;
    int Counts[2048];
    if ( nSize < 2 ) return;
    if ( ++pCtx->SeedEpoch == 0 )
    {
        memset(pCtx->pSeedStamp, 0, sizeof(unsigned) * pCtx->nLits);
        pCtx->SeedEpoch = 1;
    }
    for ( i = k = 0; i < nSize; i++ )
    {
        Lit = Vec_IntEntry(vSeeds, i);
        assert( Lit >= 0 && Lit < pCtx->nLits );
        if ( pCtx->pSeedStamp[Lit] == pCtx->SeedEpoch ) continue;
        pCtx->pSeedStamp[Lit] = pCtx->SeedEpoch;
        Vec_IntWriteEntry(vSeeds, k++, Lit);
    }
    Vec_IntShrink(vSeeds, k);
    if ( k < 2 ) return;
    if ( k <= 32 )
    {
        int * a = Vec_IntArray(vSeeds), j, x;
        for ( i = 1; i < k; i++ )
        {
            for ( x = a[i], j = i; j > 0 && a[j-1] > x; j-- ) a[j] = a[j-1];
            a[j] = x;
        }
        return;
    }
    Vec_IntGrow(pCtx->vSeedSort, k);
    pCtx->vSeedSort->nSize = k;
    pSrc = Vec_IntArray(vSeeds);
    pDst = Vec_IntArray(pCtx->vSeedSort);
    nBits = Abc_Base2Log(pCtx->nLits);
    for ( Pass = 0; 11*Pass < nBits; Pass++ )
    {
        int Shift = 11 * Pass, nBins = 1 << Abc_MinInt(11, nBits-Shift), Sum = 0, c;
        memset(Counts, 0, sizeof(int) * nBins);
        for ( i = 0; i < k; i++ ) Counts[((unsigned)pSrc[i] >> Shift) & (nBins - 1)]++;
        for ( i = 0; i < nBins; i++ ) c = Counts[i], Counts[i] = Sum, Sum += c;
        for ( i = 0; i < k; i++ ) pDst[Counts[((unsigned)pSrc[i] >> Shift) & (nBins - 1)]++] = pSrc[i];
        { int * t = pSrc; pSrc = pDst; pDst = t; }
    }
    if ( pSrc != Vec_IntArray(vSeeds) )
        memcpy(Vec_IntArray(vSeeds), pSrc, sizeof(int) * k);
}

/**Function*************************************************************

  Synopsis    [Sums the change of modeled buffer area over the literals a trial
  changed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Scm_CtxBufferAreaDelta( Scm_Man_t * p, Scm_Ctx_t * pCtx, int fCommit )
{
    double Delta = 0.0;
    int i, Lit;
    Scm_CtxSeedsUniqify(pCtx, pCtx->vTrialSeeds);
    Vec_IntForEachEntry(pCtx->vTrialSeeds, Lit, i)
    {
        float Area = Scm_ManBufferArea(p, Lit);
        Delta += (double)Area - pCtx->pBufferAreas[Lit];
        if ( fCommit ) pCtx->pBufferAreas[Lit] = Area;
    }
    return Delta;
}

/**Function*************************************************************

  Synopsis    [Starts a refinement context for the current cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Ctx_t * Scm_CtxStart( Scm_Man_t * p, int fBufferAreas )
{
    Gia_Obj_t * pObj;
    Scm_Ctx_t * pCtx, * pSpare;
    int i, c;
    pCtx = ABC_CALLOC(Scm_Ctx_t, 1);
    pCtx->nLits = 2 * Gia_ManObjNum(p->pGia);
    // Reuse the previous context's per-literal arrays (Scm_CtxRecycle),
    // emptied: no fanout or tail line, every arc-cache entry invalid.
    pSpare = p->pCtxSpare && p->pCtxSpare->nLits == pCtx->nLits ? p->pCtxSpare : NULL;
    if ( pSpare ) p->pCtxSpare = NULL;
    if ( pSpare && pSpare->pArcCache )
    {
        pCtx->pArcCache = pSpare->pArcCache; pSpare->pArcCache = NULL;
        Scm_ArcCacheInvalidate( pCtx->pArcCache, pCtx->nLits );
    }
    else
        pCtx->pArcCache = ABC_CALLOC(Scm_ArcNode_t *, pCtx->nLits);
    if ( pSpare && pSpare->pFans )
    {
        pCtx->pFans = pSpare->pFans; pSpare->pFans = NULL;
        for ( i = 0; i < pCtx->nLits; i++ ) pCtx->pFans[i].nRoots = 0;
    }
    else
        pCtx->pFans = ABC_CALLOC(Scm_Fanouts_t, pCtx->nLits);
    pCtx->pLoadSums = ABC_ALLOC(double, pCtx->nLits);
    if ( p->pRfLoads )
    {
        pCtx->pRfLoadSums = ABC_ALLOC(double, 2*pCtx->nLits);
        Scm_ManCollectLoadsRf(p, pCtx->pRfLoadSums);
    }
    // the cheap repair vetoes candidates whose modeled buffer area exceeds the area they free
    if ( fBufferAreas )
    {
        pCtx->pBufferAreas = ABC_ALLOC(float, pCtx->nLits);
        for ( i = 0; i < pCtx->nLits; i++ )
            pCtx->pBufferAreas[i] = Scm_ManBufferArea(p, i);
    }
    pCtx->pTrialArrMax = ABC_ALLOC(float, pCtx->nLits);
    pCtx->pTrialSlewMax = ABC_ALLOC(float, pCtx->nLits);
    pCtx->pTouched = ABC_CALLOC(unsigned, pCtx->nLits);
    pCtx->pComputed = ABC_CALLOC(unsigned, pCtx->nLits);
    pCtx->vOldSeeds = Vec_IntAlloc(128);
    pCtx->vTrialSeeds = Vec_IntAlloc(128);
    pCtx->vAffected = Vec_IntAlloc(128);
    pCtx->pSeedStamp = ABC_CALLOC(unsigned, pCtx->nLits);
    pCtx->pEdgePos = ABC_FALLOC(int, pCtx->nLits * SCM_LEAF_MAX);
    pCtx->vSeedSort = Vec_IntAlloc(128);
    Scm_CtxQueueStart(pCtx, 2u * (unsigned)pCtx->nLits);
    if ( pSpare && pSpare->pTails )
    {
        pCtx->pTails = pSpare->pTails; pSpare->pTails = NULL;
        for ( i = 0; i < pCtx->nLits; i++ ) pCtx->pTails[i].nFans = 0;
    }
    else
        pCtx->pTails = ABC_CALLOC(Scm_RfLines_t, pCtx->nLits);
    pCtx->pTrialRfArrs = ABC_ALLOC(Scm_RfPair_t, pCtx->nLits);
    pCtx->pTrialRfSlews = ABC_ALLOC(Scm_RfPair_t, pCtx->nLits);
    pCtx->pTailBase = ABC_ALLOC(Scm_RfPair_t, pCtx->nLits);
    Scm_CtxFree( pSpare );   // arrays this context does not use
    pCtx->pConeSeen = ABC_CALLOC(unsigned, pCtx->nLits);
    pCtx->pTailSeen = ABC_CALLOC(unsigned, pCtx->nLits);
    pCtx->pTailValid = ABC_CALLOC(unsigned char, pCtx->nLits);
    pCtx->pIsPo = ABC_CALLOC(unsigned char, pCtx->nLits);
    pCtx->vConeStack = Vec_IntAlloc(128);
    pCtx->vBoundary = Vec_IntAlloc(128);
    pCtx->vBoundaryPriorities = Vec_FltAlloc(128);
    pCtx->vTailStack = Vec_IntAlloc(128);
    pCtx->vTailWork = Vec_IntAlloc(128);
    pCtx->vTailSort = Vec_IntAlloc(128);
    Gia_ManForEachCo(p->pGia, pObj, i)
        pCtx->pIsPo[Gia_ObjFaninLit0p(p->pGia, pObj)] = 1;
    for ( i = 0; i < pCtx->nLits; i++ )
        pCtx->pLoadSums[i] = Vec_FltEntry(&p->vLoads, i);
    Gia_ManForEachCiId(p->pGia, i, c)
        if ( Scm_ObjMapRefNum(p, i, 1) )
            Scm_CtxMatchEdit(p, pCtx, i, 1,
                Scm_ObjMatch(p, i, 1), 1, 1);
    Gia_ManForEachAnd(p->pGia, pObj, i)
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) )
                Scm_CtxMatchEdit(p, pCtx, i, c,
                    Scm_ObjMatch(p, i, c), 1, 1);
    if ( pCtx->fError )
    {
        Scm_CtxFree(pCtx);
        return NULL;
    }
    return pCtx;
}

/**Function*************************************************************

  Synopsis    [Dereferences a match and its cone in a context; returns the area
  freed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_CtxDeref_rec( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iObj, int c, Scm_Mat_t * pM )
{
    word Area = 0;
    int iVar, fCompl, k, * pCut;
    Scm_CtxMatchEdit(p, pCtx, iObj, c, pM, -1, 0);
    if ( pM->fCompl )
    {
        assert(Scm_ObjMapRefNum(p, iObj, !c) > 0);
        if ( !Scm_ObjMapRefDec(p, iObj, !c) )
            Area += Scm_CtxDeref_rec(p, pCtx, iObj, !c,
                Scm_ObjMatch(p, iObj, !c));
        return Area + p->InvAreaW;
    }
    if ( Scm_ObjCutSetId(p, iObj) == 0 ) return 0;
    pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
    Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
    {
        assert(Scm_ObjMapRefNum(p, iVar, fCompl) > 0);
        if ( !Scm_ObjMapRefDec(p, iVar, fCompl) )
            Area += Scm_CtxDeref_rec(p, pCtx, iVar, fCompl,
                Scm_ObjMatch(p, iVar, fCompl));
    }
    return Area + Scm_ManCell(p, pM->Gate)->AreaW;
}

/**Function*************************************************************

  Synopsis    [References a match and its cone in a context; returns the area added.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_CtxRef_rec( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iObj, int c, Scm_Mat_t * pM )
{
    word Area = 0;
    int iVar, fCompl, k, * pCut;
    Scm_CtxMatchEdit(p, pCtx, iObj, c, pM, 1, 0);
    if ( pM->fCompl )
    {
        if ( !Scm_ObjMapRefInc(p, iObj, !c) )
            Area += Scm_CtxRef_rec(p, pCtx, iObj, !c,
                Scm_ObjMatch(p, iObj, !c));
        return Area + p->InvAreaW;
    }
    if ( Scm_ObjCutSetId(p, iObj) == 0 ) return 0;
    pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
    Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
        if ( !Scm_ObjMapRefInc(p, iVar, fCompl) )
            Area += Scm_CtxRef_rec(p, pCtx, iVar, fCompl,
                Scm_ObjMatch(p, iVar, fCompl));
    return Area + Scm_ManCell(p, pM->Gate)->AreaW;
}

/**Function*************************************************************

  Synopsis    [Reads the trial or committed rise/fall arrival and slew of a literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxReadState( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iLit, Scm_RfPair_t * pArrival, Scm_RfPair_t * pSlew )
{
    if ( pCtx->pTouched[iLit] == pCtx->Epoch )
    {
        if ( pCtx->pComputed[iLit] != pCtx->Epoch ) return 0;
        *pArrival = pCtx->pTrialRfArrs[iLit];
        *pSlew = pCtx->pTrialRfSlews[iLit];
    }
    else
    {
        *pArrival = p->pRfArrs[iLit];
        *pSlew = p->pRfSlews[iLit];
    }
    return 1;
}

// The arc cache: for each literal, its selected match's input literals and arc coefficients
// at the literal's load (not its arrivals). The key is the match and both transition loads,
// so a trial, a restore or a phase change never reuses stale coefficients.
typedef struct Scm_ArcEdge_t_ Scm_ArcEdge_t;
struct Scm_ArcEdge_t_
{
    int            child, sense;
    float          delay[2];   // per output transition: delay at the load, before the slew term
    float          slope[2];   // per output transition: delay per unit of input slew
};
struct Scm_ArcNode_t_
{
    int            gate, cut, cfg, inv, valid, n;
    Scm_RfPair_t   load, slew;
    Scm_ArcEdge_t  edges[SCM_LEAF_MAX];
};

/**Function*************************************************************

  Synopsis    [A recycled entry behaves as a fresh one: Scm_ArcNodeGet rebuilds any
  invalid entry, and Scm_ArcNodeBuild writes every field that is read
  afterwards.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ArcCacheInvalidate( Scm_ArcNode_t ** pCache, int nLits )
{
    int i;
    for ( i = 0; i < nLits; i++ )
        if ( pCache[i] ) pCache[i]->valid = 0;
}

/**Function*************************************************************

  Synopsis    [Caches the arcs of the match of a literal at its load.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ArcNodeBuild( Scm_Man_t * p, Scm_ArcNode_t * node, int lit, Scm_Mat_t * m, Scm_RfPair_t load )
{
    int obj = lit >> 1, k, t, * cut;
    Mio_Cell2_t * cell;
    Gia_Obj_t * o = Gia_ManObj(p->pGia, obj);
    node->valid = 0;
    node->n = 0;
    node->slew.Value[0] = node->slew.Value[1] = 0;
    if ( !obj || (Gia_ObjIsCi(o) && !(lit & 1)) ) goto done;
    cell = m->fCompl ? p->pCells + 3 : Scm_ManCell(p, m->Gate);
    if ( !m->fCompl && (!m->CutH || !cell->nFanins) ) goto done;
    cut = m->fCompl ? NULL : Scm_CutFromHandle(Scm_ObjCutSet(p, obj), m->CutH);
    if ( cell->nFanins > SCM_LEAF_MAX || (!m->fCompl &&
         (Scm_CutSize(cut) != (int)cell->nFanins || !Scm_CfgIsCutPermutation(m->Cfg, Scm_CutSize(cut)))) ) return 0;
    node->n = cell->nFanins;
    for ( k = 0; k < node->n; k++ )
    {
        Scm_ArcEdge_t * e = node->edges + k;
        Scm_Arc_t tmp, * arc = Scm_ManArcAtLoad(p, cell, k, load, &tmp);
        if ( !arc || !arc->fValid ) return 0;
        e->child = m->fCompl ? (lit ^ 1) : Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m->Cfg, k)], Scm_CfgCompl(m->Cfg, k));
        e->sense = arc->TimingSense;
        for ( t = 0; t < 2; t++ )
        {
            e->delay[t] = arc->RfDelay0[t] + arc->RfDelayLoad[t] * load.Value[t];
            e->slope[t] = arc->RfDelaySlew[t];
            node->slew.Value[t] = Abc_MaxFloat(node->slew.Value[t], Scm_ManRfSlew(arc, t, load.Value[t]));
        }
    }
done:
    node->gate = m->Gate;
    node->cut = m->CutH;
    node->cfg = Scm_Cfg2Int(m->Cfg);
    node->inv = m->fCompl;
    node->load = load;
    node->valid = 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the cached arcs of the match of a literal, rebuilding them if
  stale.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_ArcNode_t * Scm_ArcNodeGet( Scm_Man_t * p, Scm_Ctx_t * pCtx, int obj, int phase )
{
    int lit = 2*obj + phase;
    Scm_Mat_t * m = Scm_ObjMatch(p, obj, phase);
    Scm_RfPair_t load = Scm_ManRfLoad(p, lit);
    Scm_ArcNode_t * node = pCtx->pArcCache[lit];
    if ( !node ) node = pCtx->pArcCache[lit] = ABC_CALLOC(Scm_ArcNode_t, 1);
    if ( !node->valid || node->gate != (int)m->Gate || node->cut != m->CutH ||
         node->cfg != Scm_Cfg2Int(m->Cfg) || node->inv != (int)m->fCompl ||
         node->load.Value[0] != load.Value[0] || node->load.Value[1] != load.Value[1] )
        if ( !Scm_ArcNodeBuild(p, node, lit, m, load) ) return NULL;
    return node;
}

/**Function*************************************************************

  Synopsis    [Times one literal from its leaves' trial or committed timing.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxEvalLit( Scm_Man_t * p, Scm_Ctx_t * pCtx, int obj, int phase )
{
    int lit = 2*obj + phase, k, t;
    Scm_RfPair_t arr = {{0, 0}};
    Scm_ArcNode_t * node = Scm_ArcNodeGet(p, pCtx, obj, phase);
    if ( !node ) return 0;
    if ( node->n ) arr.Value[0] = arr.Value[1] = -FLT_MAX;
    for ( k = 0; k < node->n; k++ )
    {
        Scm_ArcEdge_t * e = node->edges + k;
        Scm_RfPair_t a, s;
        if ( !Scm_CtxReadState(p, pCtx, e->child, &a, &s) ) return 0;
        for ( t = 0; t < 2; t++ )
        {
            if ( e->sense == sc_ts_Pos || e->sense == sc_ts_Non )
                arr.Value[t] = Abc_MaxFloat(arr.Value[t], a.Value[t] + (e->delay[t] + e->slope[t]*s.Value[t]));
            if ( e->sense == sc_ts_Neg || e->sense == sc_ts_Non )
                arr.Value[t] = Abc_MaxFloat(arr.Value[t], a.Value[!t] + (e->delay[t] + e->slope[t]*s.Value[!t]));
        }
    }
    if ( !isfinite(arr.Value[0]) || !isfinite(arr.Value[1]) ||
         !isfinite(node->slew.Value[0]) || !isfinite(node->slew.Value[1]) ) return 0;
    pCtx->pTrialRfArrs[lit] = arr;
    pCtx->pTrialRfSlews[lit] = node->slew;
    pCtx->pTrialArrMax[lit] = Scm_ManRfPairMax(arr);
    pCtx->pTrialSlewMax[lit] = Scm_ManRfPairMax(node->slew);
    pCtx->pComputed[lit] = pCtx->Epoch;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the topological order key of a literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_ManOrderKey( Scm_Man_t * p, int iLit )
{
    int iObj = Abc_Lit2Var(iLit), c = Abc_LitIsCompl(iLit);
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    int fInv = (iObj == 0 || Gia_ObjIsCi(pObj)) ? c :
        !!Scm_ObjMatch(p, iObj, c)->fCompl;
    return 2 * iObj + fInv;
}

/**Function*************************************************************

  Synopsis    [Queues a referenced literal for retiming once per epoch.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxQueueLit( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iLit )
{
    if ( pCtx->pTouched[iLit] == pCtx->Epoch ||
         !Scm_ObjMapRefNum(p, Abc_Lit2Var(iLit), Abc_LitIsCompl(iLit)) )
        return;
    pCtx->pTouched[iLit] = pCtx->Epoch;
    // Bit 0 preserves the literal phase; bit 1 places an inverter after
    // its direct phase even when the direct phase is complemented.
    Scm_CtxQueuePush(pCtx,
        2u * (unsigned)Scm_ManOrderKey(p, iLit) + Abc_LitIsCompl(iLit));
}

// Required-time pruning of a search trial. For the acceptance bound, a lazy backward walk
// over the committed cover gives each literal the latest rise/fall arrival from which no
// path exceeds the bound. Beyond a trial's last changed literal, arc delays are fixed as
// long as the slew is unchanged, so a changed arrival beyond its bound proves that the
// trial misses the bound: timing stops and the trial is rejected.
typedef struct Scm_Prune_t_ Scm_Prune_t;
struct Scm_Prune_t_
{
    Scm_Ctx_t      shadow;     // the search context, with its own tail-valid marks for this walk
    Scm_RfPair_t * required;   // per literal: the latest arrival meeting the bound
    Vec_Int_t *    dfs;
    float          threshold;  // the bound
};

/**Function*************************************************************

  Synopsis    [The largest float x with float(x + cost) <= required: start at the
  upper edge of the rounding bin in double (subtracting at zero would
  cancel), then check the float sum.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_PruneBack( float required, float cost )
{
    double edge;
    float x;
    if ( required == FLT_MAX ) return FLT_MAX;
    edge = ((double)required + (double)nextafterf(required, INFINITY)) * 0.5;
    x = (float)(edge - (double)cost);
    while ( (float)(x + cost) > required )
        x = nextafterf(x, -INFINITY);
    while ( isfinite(nextafterf(x, INFINITY)) && (float)(nextafterf(x, INFINITY) + cost) <= required )
        x = nextafterf(x, INFINITY);
    return x;
}

/**Function*************************************************************

  Synopsis    [Starts the private context of the pruning walk.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_Prune_t * Scm_PruneStart( Scm_Ctx_t * pCtx, double threshold )
{
    Scm_Prune_t * r = ABC_CALLOC(Scm_Prune_t, 1);
    r->shadow = *pCtx;
    r->shadow.fLiveTail = 1;
    r->shadow.pTailValid = ABC_CALLOC(unsigned char, pCtx->nLits);
    r->shadow.vTailStack = Vec_IntAlloc(128);
    r->dfs = Vec_IntAlloc(128);
    r->required = ABC_ALLOC(Scm_RfPair_t, pCtx->nLits);
    r->threshold = (float)threshold;
    if ( (double)r->threshold > threshold ) r->threshold = nextafterf(r->threshold, -INFINITY);
    return r;
}

/**Function*************************************************************

  Synopsis    [Stops the private context of the pruning walk.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_PruneStop( Scm_Prune_t * r )
{
    if ( !r ) return;
    ABC_FREE( r->shadow.pTailValid );
    Vec_IntFree( r->shadow.vTailStack );
    Vec_IntFree( r->dfs );
    ABC_FREE( r->required );
    ABC_FREE( r );
}

/**Function*************************************************************

  Synopsis    [The required time of a literal and, depth first, of its fanouts (the
  arc cache gives the arcs).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_PruneBuild( Scm_Man_t * p, Scm_Prune_t * r, int lit )
{
    Scm_Ctx_t * c = &r->shadow;
    if ( c->pTailValid[lit] ) return 1;
    Vec_IntClear( r->dfs );
    Vec_IntPush( r->dfs, lit );
    Vec_IntPush( r->dfs, 0 );
    while ( Vec_IntSize(r->dfs) )
    {
        int n = Vec_IntSize(r->dfs), x = Vec_IntEntry(r->dfs, n-2), j = Vec_IntEntry(r->dfs, n-1), out, in;
        Scm_Fanouts_t * fans = c->pFans + x;
        Scm_RfPair_t req = {{FLT_MAX, FLT_MAX}}, slew = p->pRfSlews[x];
        if ( j < fans->nRoots )
        {
            int y = fans->pRoots[j];
            Vec_IntWriteEntry( r->dfs, n-1, j+1 );
            if ( !c->pTailValid[y] )
            {
                Vec_IntPush( r->dfs, y );
                Vec_IntPush( r->dfs, 0 );
            }
            continue;
        }
        if ( c->pIsPo[x] ) req.Value[0] = req.Value[1] = r->threshold;
        for ( j = 0; j < fans->nRoots; j++ )
        {
            int y = fans->pRoots[j], pin = fans->pPins[j];
            Scm_ArcNode_t * node = Scm_ArcNodeGet(p, c, y >> 1, y & 1);
            Scm_ArcEdge_t * edge;
            if ( !node || pin < 0 || pin >= node->n || node->edges[pin].child != x ) return 0;
            edge = node->edges + pin;
            for ( out = 0; out < 2; out++ )
                for ( in = 0; in < 2; in++ )
                {
                    float cost;
                    if ( edge->sense != sc_ts_Non && !(edge->sense == sc_ts_Pos && in == out) && !(edge->sense == sc_ts_Neg && in != out) ) continue;
                    cost = edge->delay[out] + edge->slope[out]*slew.Value[in];
                    if ( !isfinite(cost) ) return 0;
                    // a bound that already satisfies this edge cannot be tightened by it
                    if ( (float)(req.Value[in] + cost) > r->required[y].Value[out] )
                        req.Value[in] = fminf(req.Value[in], Scm_PruneBack(r->required[y].Value[out], cost));
                }
        }
        r->required[x] = req;
        c->pTailValid[x] = 1;
        Vec_IntPop( r->dfs );
        Vec_IntPop( r->dfs );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Whether timing can stop at a changed literal: 1 with
  pCtx->fScoreRejected set rejects the trial.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxPruneSkip( Scm_Man_t * p, Scm_Ctx_t * pCtx, int lit )
{
    Scm_Prune_t * r = (Scm_Prune_t *)pCtx->pScorePrune;
    int t;
    if ( !pCtx->fScorePrune || !r || (lit >> 1) <= pCtx->ScorePruneCutoff ) return 0;
    // a changed slew changes the delays beyond this literal
    for ( t = 0; t < 2; t++ )
        if ( p->pRfSlews[lit].Value[t] != pCtx->pTrialRfSlews[lit].Value[t] ) return 0;
    if ( !Scm_PruneBuild(p, r, lit) ) { pCtx->fError = 1; return 0; }
    for ( t = 0; t < 2; t++ )
        if ( pCtx->pTrialRfArrs[lit].Value[t] > r->required[lit].Value[t] )
        {
            pCtx->fScoreRejected = 1;
            return 1;
        }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Times the literals a trial changed and their affected fanouts.]

  Description [Starts from the trial's changed matches and loads (the
  trial seeds) in topological order (AIG IDs; a direct phase before its
  inverter). Literals above iMaxObj are not timed: a repair trial or a screen
  needs arrivals only up to its root, the residual tails stand for the rest.
  Without full propagation only the seeds are retimed. A fanout is visited
  only if a literal's arrival or slew changed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxTimeLocal( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iMaxObj )
{
    int i, iLit, j;
    if ( pCtx->fError ) return 0;
    ++pCtx->Epoch;
    assert( pCtx->Epoch != 0 );
    Vec_IntClear( pCtx->vAffected );
    if ( pCtx->vScoreOutputs ) Vec_IntClear( pCtx->vScoreOutputs );
    // normally empty; discards the unfinished work of a rejected trial
    while ( Scm_CtxQueueHas(pCtx) ) Scm_CtxQueuePop(pCtx);
    Vec_IntForEachEntry( pCtx->vTrialSeeds, iLit, i )
        if ( Abc_Lit2Var(iLit) <= iMaxObj )
            Scm_CtxQueueLit( p, pCtx, iLit );
    while ( Scm_CtxQueueHas(pCtx) )
    {
        Scm_Fanouts_t * pFans;
        unsigned Key = Scm_CtxQueuePop(pCtx);
        iLit = Abc_Var2Lit(Key >> 2, Key & 1);
        if ( !Scm_CtxEvalLit(p, pCtx, Abc_Lit2Var(iLit), Abc_LitIsCompl(iLit)) ) return 0;
        Vec_IntPush( pCtx->vAffected, iLit );
        if ( pCtx->vScoreOutputs && pCtx->pIsPo[iLit] ) Vec_IntPush( pCtx->vScoreOutputs, iLit );
        if ( !pCtx->fFullPropagation ) continue;
        if ( pCtx->pTrialRfArrs[iLit].Value[0] == p->pRfArrs[iLit].Value[0] &&
             pCtx->pTrialRfArrs[iLit].Value[1] == p->pRfArrs[iLit].Value[1] &&
             pCtx->pTrialRfSlews[iLit].Value[0] == p->pRfSlews[iLit].Value[0] &&
             pCtx->pTrialRfSlews[iLit].Value[1] == p->pRfSlews[iLit].Value[1] ) continue;
        if ( Scm_CtxPruneSkip(p, pCtx, iLit) )
        {
            if ( !pCtx->fScoreRejected ) continue;
            while ( Scm_CtxQueueHas(pCtx) ) Scm_CtxQueuePop(pCtx);
            return 1;
        }
        if ( pCtx->fError ) return 0;
        pFans = pCtx->pFans + iLit;
        for ( j = 0; j < pFans->nRoots; j++ )
        {
            int iRootLit = pFans->pRoots[j];
            if ( !Scm_ObjMapRefNum(p, Abc_Lit2Var(iRootLit), Abc_LitIsCompl(iRootLit)) ) return 0;
            if ( Abc_Lit2Var(iRootLit) <= iMaxObj )
                Scm_CtxQueueLit( p, pCtx, iRootLit );
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the committed rise/fall output slew of a literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Scm_RfPair_t Scm_ManBaseSlew( Scm_Man_t * p, int iLit )
{
    int iObj = Abc_Lit2Var(iLit), c = Abc_LitIsCompl(iLit);
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    Scm_Mat_t * pM;
    Scm_RfPair_t Zero = {{0.0f, 0.0f}};
    if ( iObj == 0 || (Gia_ObjIsCi(pObj) && !c) ) return Zero;
    pM = Scm_ObjMatch(p, iObj, c);
    if ( !pM->fCompl && Scm_ObjCutSetId(p, iObj) == 0 ) return Zero;
    if ( !pM->fCompl && Scm_ManCell(p, pM->Gate)->nFanins == 0 ) return Zero;
    return Scm_ManRfCellSlew(p,
        pM->fCompl ? p->pCells + 3 : Scm_ManCell(p, pM->Gate),
        Scm_ManRfLoad(p, iLit));
}

/**Function*************************************************************

  Synopsis    [Sorts the literals whose tails are rebuilt by order key (radix sort).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxTailSort( Scm_Ctx_t * pCtx )
{
    int Counts[2048], Pos[2048];
    int * pSrc = Vec_IntArray(pCtx->vTailWork);
    int * pDst;
    int nSize = Vec_IntSize(pCtx->vTailWork), Pass, i, k;
    if ( nSize < 2 ) return;
    Vec_IntGrow(pCtx->vTailSort, nSize);
    pCtx->vTailSort->nSize = nSize;
    pDst = Vec_IntArray(pCtx->vTailSort);
    for ( Pass = 0; Pass < 3; Pass++ )
    {
        int Shift = 11 * Pass;
        int nBins = Pass == 2 ? 1024 : 2048;
        memset(Counts, 0, sizeof(int) * nBins);
        for ( i = 0; i < nSize; i++ )
            Counts[((unsigned)pSrc[i] >> Shift) & (nBins - 1)]++;
        Pos[0] = 0;
        for ( k = 1; k < nBins; k++ )
            Pos[k] = Pos[k-1] + Counts[k-1];
        for ( i = 0; i < nSize; i++ )
        {
            unsigned Key = ((unsigned)pSrc[i] >> Shift) & (nBins - 1);
            pDst[Pos[Key]++] = pSrc[i];
        }
        { int * pTemp = pSrc; pSrc = pDst; pDst = pTemp; }
    }
    if ( pSrc != Vec_IntArray(pCtx->vTailWork) )
    {
        memcpy(Vec_IntArray(pCtx->vTailWork), pSrc, sizeof(int) * nSize);
        pSrc = Vec_IntArray(pCtx->vTailWork);
    }
    for ( i = 0; i < nSize/2; i++ )
    {
        int Temp = pSrc[i];
        pSrc[i] = pSrc[nSize-1-i];
        pSrc[nSize-1-i] = Temp;
    }
}

/**Function*************************************************************

  Synopsis    [Adds the paths through one arc to a residual tail.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_RfLinesAddArc( Scm_RfLines_t * pSet, Scm_Arc_t * pArc, Scm_RfPair_t Load, Scm_RfPair_t ParentTail )
{
    Scm_RfLine_t Fan;
    int iOut;
    if ( pArc->TimingSense == sc_ts_Pos || pArc->TimingSense == sc_ts_Non )
    {
        memset(&Fan, 0, sizeof(Fan));
        for ( iOut = SCM_FALL; iOut <= SCM_RISE; iOut++ )
        {
            Fan.Valid[iOut] = 1;
            Fan.Constant[iOut] = pArc->RfDelay0[iOut] +
                pArc->RfDelayLoad[iOut] * Load.Value[iOut] + ParentTail.Value[iOut];
            Fan.SlewCoeff[iOut] = pArc->RfDelaySlew[iOut];
        }
        Scm_RfLinesPush(pSet, Fan);
    }
    if ( pArc->TimingSense == sc_ts_Neg || pArc->TimingSense == sc_ts_Non )
    {
        memset(&Fan, 0, sizeof(Fan));
        for ( iOut = SCM_FALL; iOut <= SCM_RISE; iOut++ )
        {
            int iIn = !iOut;
            Fan.Valid[iIn] = 1;
            Fan.Constant[iIn] = pArc->RfDelay0[iOut] +
                pArc->RfDelayLoad[iOut] * Load.Value[iOut] + ParentTail.Value[iOut];
            Fan.SlewCoeff[iIn] = pArc->RfDelaySlew[iOut];
        }
        Scm_RfLinesPush(pSet, Fan);
    }
}

/**Function*************************************************************

  Synopsis    [Builds the residual tails of both phases of a node.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxTailBuildObj( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iObj )
{
    int Pass, c, j;
    for ( Pass = 1; Pass >= 0; Pass-- )
        for ( c = 0; c < 2; c++ )
        {
            Scm_RfLines_t * pLines;
            Scm_Fanouts_t * pFans;
            int iLit = Abc_Var2Lit(iObj, c);
            if ( pCtx->pTailSeen[iLit] != pCtx->TailEpoch ||
                 pCtx->pTailValid[iLit] ||
                 (Scm_ManOrderKey(p, iLit) & 1) != Pass ) continue;
            pLines = pCtx->pTails + iLit;
            pLines->nFans = 0;
            if ( pCtx->pIsPo[iLit] )
            {
                Scm_RfLine_t Fan;
                memset(&Fan, 0, sizeof(Fan));
                Fan.Valid[0] = Fan.Valid[1] = 1;
                Scm_RfLinesPush(pLines, Fan);
            }
            pFans = pCtx->pFans + iLit;
            for ( j = 0; j < pFans->nRoots; j++ )
            {
                int iFanLit = pFans->pRoots[j];
                Scm_Mat_t * pM = Scm_ObjMatch(p,
                    Abc_Lit2Var(iFanLit), Abc_LitIsCompl(iFanLit));
                Mio_Cell2_t * pCell = pM->fCompl ? p->pCells + 3 :
                    Scm_ManCell(p, pM->Gate);
                Scm_Arc_t Temp, * pArc = Scm_ManArcAtLoad(p, pCell, pFans->pPins[j], Scm_ManRfLoad(p, iFanLit), &Temp);
                if ( !pCtx->pTailValid[iFanLit] || pArc == NULL ||
                     !pArc->fValid ) return 0;
                if ( pCtx->pTailBase[iFanLit].Value[0] == -FLT_MAX &&
                     pCtx->pTailBase[iFanLit].Value[1] == -FLT_MAX )
                    continue;
                Scm_RfLinesAddArc(pLines, pArc,
                    Scm_ManRfLoad(p, iFanLit),
                    pCtx->pTailBase[iFanLit]);
            }
            pCtx->pTailBase[iLit] = Scm_RfLinesEval(pLines,
                Scm_ManBaseSlew(p, iLit));
            pCtx->pTailValid[iLit] = 1;
        }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Builds the residual tails needed by a literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxTailBuild( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iStartLit )
{
    int i, j, iLit, iObj;
    if ( pCtx->pTailValid[iStartLit] ) return 1;
    ++pCtx->TailEpoch;
    assert(pCtx->TailEpoch != 0);
    Vec_IntClear(pCtx->vTailStack);
    Vec_IntClear(pCtx->vTailWork);
    Vec_IntPush(pCtx->vTailStack, iStartLit);
    pCtx->pTailSeen[iStartLit] = pCtx->TailEpoch;
    while ( Vec_IntSize(pCtx->vTailStack) )
    {
        Scm_Fanouts_t * pFans;
        iLit = Vec_IntPop(pCtx->vTailStack);
        if ( pCtx->pTailValid[iLit] ) continue;
        Vec_IntPush(pCtx->vTailWork, iLit);
        pFans = pCtx->pFans + iLit;
        for ( j = 0; j < pFans->nRoots; j++ )
        {
            int iFanLit = pFans->pRoots[j];
            if ( !Scm_ObjMapRefNum(p, Abc_Lit2Var(iFanLit),
                    Abc_LitIsCompl(iFanLit)) ) return 0;
            if ( pCtx->pTailValid[iFanLit] ||
                 pCtx->pTailSeen[iFanLit] == pCtx->TailEpoch ) continue;
            pCtx->pTailSeen[iFanLit] = pCtx->TailEpoch;
            Vec_IntPush(pCtx->vTailStack, iFanLit);
        }
    }
    Scm_CtxTailSort(pCtx);
    // Fanout edges increase AIG IDs.  At one ID an inverter's tail must
    // precede the direct phase's tail, the reverse of forward STA order.
    for ( i = 0; i < Vec_IntSize(pCtx->vTailWork); )
    {
        iObj = Abc_Lit2Var(Vec_IntEntry(pCtx->vTailWork, i));
        if ( !Scm_CtxTailBuildObj(p, pCtx, iObj) ) return 0;
        while ( i < Vec_IntSize(pCtx->vTailWork) &&
                Abc_Lit2Var(Vec_IntEntry(pCtx->vTailWork, i)) == iObj )
            i++;
    }
    return pCtx->pTailValid[iStartLit];
}

/**Function*************************************************************

  Synopsis    [Evaluates the residual tail of a literal at its committed slew.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxTailRefresh( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iRootLit )
{
    Scm_RfLines_t * pLinesRf = pCtx->pTails + iRootLit;
    Scm_RfPair_t TailRf;
    if ( !pCtx->pTailValid[iRootLit] || pLinesRf->nFans == 0 ) return 0;
    TailRf = Scm_RfLinesEval(pLinesRf,
        Scm_ManBaseSlew(p, iRootLit));
    if ( (TailRf.Value[0] == -FLT_MAX && TailRf.Value[1] == -FLT_MAX) ||
         !isfinite(TailRf.Value[0]) || !isfinite(TailRf.Value[1]) )
        return 0;
    pCtx->pTailBase[iRootLit] = TailRf;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Invalidates the residual tails that a committed edit affects.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxTailInvalidate( Scm_Man_t * p, Scm_Ctx_t * pCtx, Vec_Int_t * vSeeds, int iSkipLit )
{
    int i, iLit, iVar, fCompl, k, * pCut;
    // Only a context with live tails (the pruning walk) invalidates the tails of a committed
    // edit's literals and their transitive fanins; the repair keeps its round-start tails.
    if ( !pCtx->fLiveTail ) return;
    Vec_IntClear(pCtx->vTailStack);
    Vec_IntForEachEntry(vSeeds, iLit, i)
    {
        if ( iLit == iSkipLit ) continue;
        if ( !pCtx->pTailValid[iLit] ) continue;
        pCtx->pTailValid[iLit] = 0;
        if ( Scm_ObjMapRefNum(p, Abc_Lit2Var(iLit),
                Abc_LitIsCompl(iLit)) )
            Vec_IntPush(pCtx->vTailStack, iLit);
    }
    while ( Vec_IntSize(pCtx->vTailStack) )
    {
        Scm_Mat_t * pM;
        int iObj, c;
        iLit = Vec_IntPop(pCtx->vTailStack);
        iObj = Abc_Lit2Var(iLit);
        c = Abc_LitIsCompl(iLit);
        pM = Scm_ObjMatch(p, iObj, c);
        if ( pM->fCompl )
        {
            int iChildLit = Abc_Var2Lit(iObj, !c);
            if ( pCtx->pTailValid[iChildLit] )
            {
                pCtx->pTailValid[iChildLit] = 0;
                Vec_IntPush(pCtx->vTailStack, iChildLit);
            }
            continue;
        }
        if ( Scm_ObjCutSetId(p, iObj) == 0 || pM->CutH <= 0 )
            continue;
        pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
        Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
        {
            int iChildLit = Abc_Var2Lit(iVar, fCompl);
            if ( !pCtx->pTailValid[iChildLit] ) continue;
            pCtx->pTailValid[iChildLit] = 0;
            Vec_IntPush(pCtx->vTailStack, iChildLit);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Collects the literals whose timing a candidate edit changes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxConeCollect( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iRootLit, Scm_Mat_t * pCandidate )
{
    int iLit, iObj, c, iVar, fCompl, k, * pCut, i;
    ++pCtx->ConeEpoch;
    assert(pCtx->ConeEpoch != 0);
    Vec_IntClear(pCtx->vConeStack);
    Vec_IntClear(pCtx->vBoundary);
    Vec_IntPush(pCtx->vConeStack, iRootLit);
    while ( Vec_IntSize(pCtx->vConeStack) )
    {
        Scm_Mat_t * pM;
        iLit = Vec_IntPop(pCtx->vConeStack);
        if ( pCtx->pConeSeen[iLit] == pCtx->ConeEpoch ) continue;
        pCtx->pConeSeen[iLit] = pCtx->ConeEpoch;
        iObj = Abc_Lit2Var(iLit);
        c = Abc_LitIsCompl(iLit);
        if ( iLit != iRootLit && Scm_ObjMapRefNum(p, iObj, c) )
        {
            Vec_IntPush(pCtx->vBoundary, iLit);
            continue;
        }
        pM = iLit == iRootLit ? pCandidate : Scm_ObjMatch(p, iObj, c);
        if ( pM->fCompl )
        {
            Vec_IntPush(pCtx->vConeStack, Abc_Var2Lit(iObj, !c));
            continue;
        }
        if ( Scm_ObjCutSetId(p, iObj) == 0 ) continue;
        if ( pM->CutH <= 0 ) return 0;
        pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
        Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
            Vec_IntPush(pCtx->vConeStack, Abc_Var2Lit(iVar, fCompl));
    }
    // An old shared leaf may lose its old root fanout even when the trial
    // candidate does not reuse it.  Its external paths still need a check.
    Vec_IntForEachEntry(pCtx->vOldSeeds, iLit, i)
        if ( iLit != iRootLit &&
             pCtx->pConeSeen[iLit] != pCtx->ConeEpoch &&
             Scm_ObjMapRefNum(p, Abc_Lit2Var(iLit),
                 Abc_LitIsCompl(iLit)) )
        {
            pCtx->pConeSeen[iLit] = pCtx->ConeEpoch;
            Vec_IntPush(pCtx->vBoundary, iLit);
        }
    // Build the root residual tail now.  Boundary tails are constructed
    // lazily during timing, after a root rejection has been ruled out.
    if ( !Scm_CtxTailBuild(p, pCtx, iRootLit) ||
         pCtx->pTails[iRootLit].nFans == 0 ) return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the priority of a boundary literal: its arrival plus its tail.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Scm_CtxBoundaryPriority( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iLit )
{
    Scm_RfPair_t ArrivalRf, SlewRf, TailRf;
    if ( !Scm_CtxReadState(p, pCtx, iLit, &ArrivalRf, &SlewRf) ) return -FLT_MAX;
    // Boundary order affects work only; the feasibility check builds and uses the exact tail.
    // A literal mapped after the round started has no tail yet: its arrival ranks it.
    if ( !pCtx->pTails[iLit].nFans )
        return Scm_ManRfPairMax(ArrivalRf);
    TailRf = Scm_RfLinesEval(pCtx->pTails + iLit, SlewRf);
    return Abc_MaxFloat(ArrivalRf.Value[0] + TailRf.Value[0],
        ArrivalRf.Value[1] + TailRf.Value[1]);
}

/**Function*************************************************************

  Synopsis    [Orders the boundary literals by priority.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxBoundaryOrder( Scm_Man_t * p, Scm_Ctx_t * pCtx )
{
    int i, j, k, Temp, nSize = Vec_IntSize(pCtx->vBoundary);
    int * pArray = Vec_IntArray(pCtx->vBoundary);
    float * pPriorities;
    // Each priority is evaluated once; the selection sort keeps a stable tie order.
    Vec_FltGrow(pCtx->vBoundaryPriorities, nSize);
    pPriorities = Vec_FltArray(pCtx->vBoundaryPriorities);
    for ( i = 0; i < nSize; i++ )
        pPriorities[i] = Scm_CtxBoundaryPriority(p, pCtx, pArray[i]);
    for ( i = 0; i + 1 < nSize; i++ )
    {
        float Best = pPriorities[i], TempPriority;
        for ( k = i, j = i + 1; j < nSize; j++ )
        {
            float This = pPriorities[j];
            if ( This > Best ) Best = This, k = j;
        }
        if ( k == i ) continue;
        Temp = pArray[i];
        pArray[i] = pArray[k];
        pArray[k] = Temp;
        TempPriority = pPriorities[i];
        pPriorities[i] = pPriorities[k];
        pPriorities[k] = TempPriority;
    }
}

/**Function*************************************************************

  Synopsis    [Times a trial over its cone and the boundary tails; returns its delay.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxTimeTail( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iRootLit, float Target, float * pDelay )
{
    int i, iLit;
    float Delay = 0.0f;
    Scm_RfPair_t Arrival, Slew, Tail;
    // Load changes can reach another boundary through retained nodes.
    // Re-time their selected fanout closure, not only the explicit cone.
    // The reverse sweep needs arrivals only up to this root; residual
    // tails represent the remaining paths to outputs.
    if ( !Scm_CtxTimeLocal(p, pCtx, Abc_Lit2Var(iRootLit)) )
        return 0;
    if ( !Scm_CtxReadState(p, pCtx, iRootLit,
            &Arrival, &Slew) ) return 0;
    Tail = Scm_RfLinesEval(pCtx->pTails + iRootLit, Slew);
    if ( Tail.Value[0] != -FLT_MAX )
        Delay = Abc_MaxFloat(Delay, Arrival.Value[0] + Tail.Value[0]);
    if ( Tail.Value[1] != -FLT_MAX )
        Delay = Abc_MaxFloat(Delay, Arrival.Value[1] + Tail.Value[1]);
    if ( Delay > Target + 1.0e-3f )
    {
        *pDelay = Delay;
        return isfinite(Delay);
    }
    if ( Vec_IntSize(pCtx->vBoundary) > 1 )
        Scm_CtxBoundaryOrder(p, pCtx);
    Vec_IntForEachEntry(pCtx->vBoundary, iLit, i)
    {
        if ( !Scm_CtxTailBuild(p, pCtx, iLit) ||
             pCtx->pTails[iLit].nFans == 0 ||
             !Scm_CtxReadState(p, pCtx, iLit, &Arrival, &Slew) )
            return 0;
        Tail = Scm_RfLinesEval(pCtx->pTails + iLit, Slew);
        if ( Tail.Value[0] != -FLT_MAX )
            Delay = Abc_MaxFloat(Delay, Arrival.Value[0] + Tail.Value[0]);
        if ( Tail.Value[1] != -FLT_MAX )
            Delay = Abc_MaxFloat(Delay, Arrival.Value[1] + Tail.Value[1]);
        if ( Delay > Target + 1.0e-3f ) break;
    }
    *pDelay = Delay;
    return isfinite(Delay);
}

/**Function*************************************************************

  Synopsis    [Commits the trial timing of the evaluated literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_CtxCommit( Scm_Man_t * p, Scm_Ctx_t * pCtx )
{
    int i, iLit;
    // Commits the trial timing of the evaluated literals. Unchanged reconvergent paths keep
    // their cached arrivals; each round ends with a full retiming of the cover.
    Vec_IntForEachEntry(pCtx->vAffected, iLit, i)
        if ( pCtx->pComputed[iLit] == pCtx->Epoch )
        {
            p->pArrMax[iLit] = pCtx->pTrialArrMax[iLit];
            p->pSlewMax[iLit] = pCtx->pTrialSlewMax[iLit];
            p->pRfArrs[iLit] = pCtx->pTrialRfArrs[iLit];
            p->pRfSlews[iLit] = pCtx->pTrialRfSlews[iLit];
        }
}

/**Function*************************************************************

  Synopsis    [Replaces the match of a node phase by a candidate in the context.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxApply( Scm_Man_t * p, Scm_Ctx_t * pCtx, int iObj, int c, Scm_Cand_t * pCand )
{
    word Added;
    Vec_IntClear(pCtx->vTrialSeeds);
    Vec_IntAppend(pCtx->vTrialSeeds, pCtx->vOldSeeds);
    pCtx->pCollectSeeds = pCtx->vTrialSeeds;
    Added = Scm_CtxRef_rec(p, pCtx, iObj, c, &pCand->M);
    pCtx->pCollectSeeds = NULL;
    assert(Added == pCand->Area);
    *Scm_ObjMatch(p, iObj, c) = pCand->M;
    if ( pCtx->fError ) return -1;
    if ( !Scm_CtxTimeLocal(p, pCtx, iObj) )
        pCtx->fError = 1;
    else
        Scm_CtxCommit(p, pCtx);
    if ( pCtx->fError || !Scm_CtxTailRefresh(p, pCtx, Abc_Var2Lit(iObj, c)) )
    {
        pCtx->fError = 1;
        return -1;
    }
    if ( pCtx->pBufferAreas ) Scm_CtxBufferAreaDelta(p, pCtx, 1);
    return 2;
}

/**Function*************************************************************

  Synopsis    [Evaluates a candidate match and restores the cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Scm_CtxTry( Scm_Man_t * p,
    Scm_Ctx_t * pCtx, int iObj, int c, Scm_Mat_t * pOld,
    Scm_Cand_t * pCand, float Target, float * pDelay )
{
    Scm_Mat_t * pSelected = Scm_ObjMatch(p, iObj, c);
    Scm_Mat_t Candidate = pCand->M;
    word Added, Removed;
    int fTimingOkay;
    *pDelay = FLT_MAX;
    if ( !Scm_CtxConeCollect(p, pCtx, Abc_Var2Lit(iObj, c), &Candidate) )
        return -1;
    Vec_IntClear(pCtx->vTrialSeeds);
    Vec_IntAppend(pCtx->vTrialSeeds, pCtx->vOldSeeds);
    pCtx->pCollectSeeds = pCtx->vTrialSeeds;
    Added = Scm_CtxRef_rec(p, pCtx, iObj, c, &Candidate);
    pCtx->pCollectSeeds = NULL;
    assert(Added == pCand->Area);
    *pSelected = Candidate;
    // the modeled buffer area of the edited nets must not exceed the logic area the old match frees
    fTimingOkay = (pCtx->pBufferAreas &&
        (double)Added + Scm_CtxBufferAreaDelta(p, pCtx, 0) > (double)pCtx->BufferFreed + 1.0e-3) ? 0 :
        Scm_CtxTimeTail(p, pCtx, Abc_Var2Lit(iObj, c), Target, pDelay);
    *pSelected = *pOld;
    Removed = Scm_CtxDeref_rec(p, pCtx, iObj, c, &Candidate);
    assert(Removed == Added);
    if ( pCtx->fError )
        return -1;
    return fTimingOkay && *pDelay <= Target + 1.0e-3f;
}

/**Function*************************************************************

  Synopsis    [Logic area of the current cover in GENLIB units: every referenced
  cell, including inverters.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_ManCoverArea( Scm_Man_t * p )
{
    Gia_Obj_t * pObj;
    word Area = 0;
    int i, c;
    Gia_ManForEachAnd( p->pGia, pObj, i )
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) )
            {
                Scm_Mat_t * pM = Scm_ObjMatch(p, i, c);
                Area += pM->fCompl ? p->InvAreaW : Scm_ManCell(p, pM->Gate)->AreaW;
            }
    Gia_ManForEachCiId( p->pGia, i, c )
        if ( Scm_ObjMapRefNum(p, i, 1) )
            Area += p->InvAreaW;
    return Area;
}

/**Function*************************************************************

  Synopsis    [Sets the default mapping parameters.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Scm_ManSetDefaultPars( Scm_Par_t * pPars )
{
    memset( pPars, 0, sizeof(*pPars) );
    pPars->SeedLoad = 2.5f;   // gain 250, unless read_lib -G's gain is recovered from the GENLIB
}

#include "giaScmapSeed.h"
#include "giaScmapRefine.h"

#include "giaScmapQuality.h"

/**Function*************************************************************

  Synopsis    [Maps with the seeds, the refinement and, for quality, seed selection.]

  Description [Returns the mapped GIA with the input's timing, or NULL.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Scm_ManPerformMapping( Gia_Man_t * pGia, Scm_Par_t * pPars )
{
    Gia_Man_t * pNew = NULL;
    Scm_Man_t * p;
    Scm_Obj_t * pSaveObjs[2] = {0};
    int * pSaveRefs[2] = {0};
    float * pSaveFlow[2] = {0};
    float * pFlow0, Delay[2] = {0};
    long long Area[2] = {0};
    int m, nSeeds, Best = -1, fOk = 1, nObjs = Gia_ManObjNum(pGia), nLits = 2 * nObjs;
    if ( pGia->pManTime || pGia->vInArrs || Gia_ManBufNum(pGia) || Scl_ConIsRunning() )
    {
        Abc_Print(-1, "&scmap requires a GIA without boxes, buffers or explicit input timing.\n");
        return NULL;
    }
    p = Scm_StoCreate(pGia, pPars);
    if ( !p ) return NULL;
    Scm_ManPrintInit(p);
    Scm_ManComputeCuts(p);
    nSeeds = p->fUnitView ? 1 : 2;
    pFlow0 = ABC_ALLOC(float, nLits);
    memcpy(pFlow0, Vec_FltArray(&p->vFlowRefs), sizeof(float) * nLits);
    p->pRfArrs = ABC_CALLOC(Scm_RfPair_t, nLits);
    p->pRfSlews = ABC_CALLOC(Scm_RfPair_t, nLits);
    if ( pPars->fQuality )
        p->pRfLoads = ABC_CALLOC(Scm_RfPair_t, nLits);
    for ( m = 0; fOk && m < nSeeds; m++ )
    {
        if ( m > 0 )
        {
            Vec_IntFill(&p->vMapRefs, nLits, 0);
            memcpy(Vec_FltArray(&p->vFlowRefs), pFlow0, sizeof(float) * nLits);
            memset(p->pObjs, 0, sizeof(Scm_Obj_t) * nObjs);
            Scm_ObjMatch(p, 0, 0)->Gate = 0;
            Scm_ObjMatch(p, 0, 1)->Gate = 1;
        }
        // a cell of the cover without a load model ends the run here
        if ( !Scm_ManSeedBuild(p, m, 0) || !Scm_ManTimeCover(p) || p->fEnvError ) { fOk = 0; break; }
        Delay[m] = p->ModelDelay;
        Area[m] = (long long)Scm_ManCoverArea(p);
        if ( pPars->fVerbose )
            Abc_Print(1, "SCMAP_SEED seed=%d delay=%.6f area=%lld\n", m, Delay[m], Area[m]);
        pSaveObjs[m] = ABC_ALLOC(Scm_Obj_t, nObjs);
        memcpy(pSaveObjs[m], p->pObjs, sizeof(Scm_Obj_t) * nObjs);
        pSaveRefs[m] = ABC_ALLOC(int, nLits);
        memcpy(pSaveRefs[m], Vec_IntArray(&p->vMapRefs), sizeof(int) * nLits);
        pSaveFlow[m] = ABC_ALLOC(float, nLits);
        memcpy(pSaveFlow[m], Vec_FltArray(&p->vFlowRefs), sizeof(float) * nLits);
    }
    if ( fOk )
    {
        // the seed of least model delay, then area, within the logic area of seed 0
        for ( m = 0; m < nSeeds; m++ )
            if ( Area[m] <= Area[0] && (Best < 0 || Delay[m] < Delay[Best] ||
                 (Delay[m] == Delay[Best] && Area[m] < Area[Best])) ) Best = m;
        if ( Best != nSeeds - 1 )   // the last seed built is the current cover
        {
            memcpy(p->pObjs, pSaveObjs[Best], sizeof(Scm_Obj_t) * nObjs);
            memcpy(Vec_IntArray(&p->vMapRefs), pSaveRefs[Best], sizeof(int) * nLits);
            memcpy(Vec_FltArray(&p->vFlowRefs), pSaveFlow[Best], sizeof(float) * nLits);
        }
        // retime the selected seed, then refine it
        if ( !Scm_ManTimeCover(p) || !Scm_ManRefineCover(p) ) fOk = 0;
        if ( fOk && pPars->fQuality )
        {
            Scm_Qor_t Bound = {0};
            if ( pPars->MapDelayTarget > 0 )
            {
                fOk = Scm_ManSelectSeed(p, NULL, NULL, pFlow0, Best, &Bound);
                if ( fOk && nSeeds > 1 ) fOk = Scm_ManSelectSeed(p, NULL, NULL, pFlow0, 1-Best, &Bound);
            }
            else if ( nSeeds > 1 )
                fOk = Scm_ManSelectSeed(p, pSaveObjs[1-Best], pSaveRefs[1-Best], pSaveFlow[1-Best], 1-Best, &Bound);
        }
        if ( fOk && pPars->fVerbose )
            Abc_Print(1, "SCMAP_SELECTED delay=%.3f area=%lld\n", p->ModelDelay, (long long)Scm_ManCoverArea(p));
    }
    for ( m = 0; m < 2; m++ )
    {
        ABC_FREE(pSaveObjs[m]); ABC_FREE(pSaveRefs[m]); ABC_FREE(pSaveFlow[m]);
    }
    ABC_FREE(pFlow0);
    if ( p->fEnvError ) fOk = 0;
    if ( fOk ) pNew = Scm_ManDeriveMapping(p);
    else Abc_Print(-1, "&scmap: seed or cover repair failed.\n");
    Scm_StoDelete(p);
    if ( pNew == NULL ) return NULL;
    Gia_ManTransferTiming(pNew, pGia);
    // the mapped graph no longer needs the choice alternatives
    ABC_FREE(pNew->pReprs);
    ABC_FREE(pNew->pNexts);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Fast mapping (&scmap without -q, -r, -t).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManScmap( Gia_Man_t * pGia, int fVerbose )
{
    Scm_Par_t Pars;
    Scm_ManSetDefaultPars( &Pars );
    Pars.fVerbose = fVerbose;
    return Scm_ManPerformMapping( pGia, &Pars );
}

/**Function*************************************************************

  Synopsis    [Builds construction-proved synthesis choices before mapping.]

  Description [As &nf3 does by default: an ordinary untimed AIG without
  choices, XOR, MUX or buffer objects gets the choices of
  Gia_ManDch2Construct, which keeps logic levels. Returns NULL for any
  other input, or if construction fails; that input is mapped as given.
  The caller owns a returned manager.]

  SideEffects []

  SeeAlso     [Nf3_ManPerformMapping]

***********************************************************************/
Gia_Man_t * Gia_ManScmapChoices( Gia_Man_t * pGia, int fVerbose )
{
    if ( pGia->pManTime || Gia_ManHasChoices(pGia) || Gia_ManXorNum(pGia) || Gia_ManMuxNum(pGia) ||
         Gia_ManBufNum(pGia) || pGia->fGiaSimple || pGia->vCiArrs || pGia->vInArrs || pGia->vCoReqs || pGia->vOutReqs )
        return NULL;
    return Gia_ManDch2Construct( pGia, 1, fVerbose );
}

/**Function*************************************************************

  Synopsis    [Checks the input and library requirements of quality mapping.]

  Description []

  SideEffects []

  SeeAlso     [Scm_ManQualityMappingInt]

***********************************************************************/
static int Scm_ManQualityCheck( Gia_Man_t * pGia )
{
    if ( pGia == NULL || !Gia_ManCoNum(pGia) || Gia_ManRegNum(pGia) || pGia->pManTime || Gia_ManBufNum(pGia) ||
         pGia->vInArrs || pGia->vOutReqs || pGia->vCiArrs || pGia->vCoReqs || Scl_ConIsRunning() )
    {
        Abc_Print(-1, "&scmap requires outputs and an unboxed combinational AIG without explicit timing.\n");
        return 0;
    }
    if ( !Abc_FrameReadLibGen() || !Abc_FrameReadLibScl() )
    {
        Abc_Print(-1, "&scmap requires a Liberty library loaded with read_lib.\n");
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Maps with refined seeds and electrically scored windows.]

  Description [The input is retained when a distinct manager is returned.
  Candidates are measured on private networks; the returned cover is unsized.]

  SideEffects [Uses the input scratch values and mapping fields.]

  SeeAlso     [Scm_ManRemapSearch]

***********************************************************************/
static Gia_Man_t * Scm_ManQualityMappingInt( Gia_Man_t * pGia, float DelayTarget, int fVerbose, Scm_Qor_t * pQor )
{
    Scm_Par_t Pars;
    Gia_Man_t * pMapped, * pNew;
    if ( pQor ) memset(pQor, 0, sizeof(*pQor));
    if ( !Scm_ManQualityCheck(pGia) ) return NULL;
    Scm_ManSetDefaultPars(&Pars);
    Pars.fQuality = 1;
    Pars.MapDelayTarget = DelayTarget;
    Pars.fVerbose = fVerbose;
    pMapped = Scm_ManPerformMapping(pGia, &Pars);
    if ( pMapped == NULL ) return NULL;
    pNew = Scm_ManWindowSearch(pMapped, &Pars.Quality, DelayTarget, fVerbose);
    if ( pNew == NULL )
    {
        Abc_Print(0, "SCMap: window refinement failed; retaining the refined seed.\n");
        pNew = pMapped;
    }
    if ( pMapped != pGia && pMapped != pNew ) Gia_ManStop(pMapped);
    if ( pQor ) *pQor = Pars.Quality;
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Strashes a cover into an AIG.]

  Description [The result carries the cover's metadata; the cover is not
  changed.]

  SideEffects [Uses input scratch fields.]

  SeeAlso     [Scm_ManRemapChoices]

***********************************************************************/
static Gia_Man_t * Scm_ManCoverAig( Gia_Man_t * pGia )
{
    Gia_Man_t * pRaw, * pCopy;
    // strash the logic of the selected cells, which can differ structurally from the mapped AIG
    Abc_Ntk_t * pNtk = Abc_NtkFromCellMappedGia(pGia, 0), * pStrash;
    if ( !pNtk ) return NULL;
    pStrash = Abc_NtkStrash(pNtk, 0, 1, 0);
    Abc_NtkDelete(pNtk);
    if ( !pStrash ) return NULL;
    pRaw = Abc_NtkStrashToGia(pStrash);
    Abc_NtkDelete(pStrash);
    if ( !pRaw ) return NULL;
    pCopy = Gia_ManDupNormalize(pRaw, 0);
    Gia_ManStop(pRaw);
    if ( pCopy ) Gie_ManDupMetadata(pCopy, pGia);
    return pCopy;
}

/**Function*************************************************************

  Synopsis    [Regenerates choices from a cover.]

  Description [A non-NULL pLink is another cover's AIG of the same function.
  It joins the cover and its rewrites as a choice snapshot, related to them
  by simulation and SAT, so the next mapping can mix both covers. Without
  pLink, or if linking fails, the choices come from the rewrites alone.]

  SideEffects [Uses input scratch fields.]

  SeeAlso     [Scm_ManRemapSearch]

***********************************************************************/
static Gia_Man_t * Scm_ManRemapChoices( Gia_Man_t * pGia, Gia_Man_t * pLink )
{
    Gia_Man_t * pCopy = Scm_ManCoverAig(pGia), * pChoices = NULL;
    if ( !pCopy ) return NULL;
    if ( pLink ) pChoices = Gia_ManDch2ConstructWith(pCopy, pLink, 1, 0);
    if ( !pChoices ) pChoices = Gia_ManDch2Construct(pCopy, 1, 0);
    Gia_ManStop(pCopy);
    return pChoices;
}

/**Function*************************************************************

  Synopsis    [Maps, then keeps remapping improvements at the measured endpoint.]

  Description [Each round remaps choices regenerated from the incumbent
  cover's DC3 rewrites, with pLink linked in when non-NULL; the next round,
  up to SCM_LOOP_ROUNDS, runs only if the remapped cover was kept.]

  SideEffects [Uses input scratch fields; never frees the input.]

  SeeAlso     [Gia_ManScmapTarget]

***********************************************************************/
static Gia_Man_t * Scm_ManRemapSearch( Gia_Man_t * pGia, float Target, int fVerbose, Scm_Qor_t * pQor, Gia_Man_t * pLink )
{
    Gia_Man_t * pBest = Scm_ManQualityMappingInt(pGia, Target, fVerbose, pQor);
    double AreaLimit;
    int r;
    if ( !pBest || !Gia_ManCiNum(pBest) || !Gia_ManAndNum(pBest) ) return pBest;
    if ( !pQor->fValid )
        pQor->fValid = Scm_WinModelLookahead(pBest, &pQor->Area, &pQor->Delay);
    if ( !pQor->fValid ) return pBest;
    AreaLimit = 1.03 * pQor->Area;
    for ( r = 0; r < SCM_LOOP_ROUNDS; r++ )
    {
        Gia_Man_t * pChoices = Scm_ManRemapChoices(pBest, pLink), * pCand;
        Scm_Qor_t Trial;
        int Keep;
        if ( !pChoices ) break;
        pCand = Scm_ManQualityMappingInt(pChoices, Target, fVerbose, &Trial);
        if ( pChoices != pCand ) Gia_ManStop(pChoices);
        if ( !pCand ) break;
        if ( !Trial.fValid ) Trial.fValid = Scm_WinModelLookahead(pCand, &Trial.Area, &Trial.Delay);
        Keep = Trial.fValid && Trial.Area <= AreaLimit && (Target > 0 ?
            Scm_QorRankBetter(&Trial, pQor, Target) :
            Trial.Delay <= pQor->Delay && Trial.Area * Trial.Delay < .999 * pQor->Area * pQor->Delay &&
            Scm_QorRankBetter(&Trial, pQor, 0));
        if ( fVerbose ) Abc_Print(1, "SCMAP_ITERATE round=%d kept=%d old_area=%.9g area=%.9g old_delay=%.9g delay=%.9g\n",
            r, Keep, pQor->Area, Trial.Area, pQor->Delay, Trial.Delay);
        if ( !Keep ) { Gia_ManStop(pCand); break; }
        if ( pBest != pGia ) Gia_ManStop(pBest);
        pBest = pCand;
        *pQor = Trial;
    }
    return pBest;
}

/**Function*************************************************************

  Synopsis    [Recovers area against an adaptive delay target (-t).]

  Description [Runs the untargeted search with the loop, then a targeted
  search toward max(DelayFloor, untargeted delay + 0.01 ps) that never
  excludes the untargeted cover; a zero floor keeps the untargeted delay.
  The targeted search is driven by the untargeted cover: it starts from that
  cover's remap choices instead of the input choices and links the cover's
  AIG into the choices of every loop round. Returns an unsized mapping.]

  SideEffects [Uses input scratch fields; never frees the input.]

  SeeAlso     [Gia_ManScmapQuality]

***********************************************************************/
Gia_Man_t * Gia_ManScmapTarget( Gia_Man_t * pGia, float DelayFloor, int fVerbose )
{
    Scm_Qor_t Base, Trial;
    Gia_Man_t * pCopy, * pBase, * pTrial, * pLink, * pStart;
    float Target;
    int Keep;
    if ( !isfinite(DelayFloor) || DelayFloor < 0 || !Scm_ManQualityCheck(pGia) ) return NULL;
    pCopy = Gia_ManDup(pGia);
    Gie_ManDupMetadata(pCopy, pGia);
    pBase = Scm_ManRemapSearch(pCopy, 0, fVerbose, &Base, NULL);
    if ( pBase != pCopy ) Gia_ManStop(pCopy);
    if ( !pBase || !Gia_ManCiNum(pBase) || !Gia_ManAndNum(pBase) ) return pBase;
    if ( !Base.fValid )
    {
        Abc_Print(-1, "SCMap: cannot establish the untargeted delay for adaptive recovery.\n");
        Gia_ManStop(pBase);
        return NULL;
    }
    Target = fmaxf(DelayFloor, Base.Delay + .01f);
    if ( fVerbose ) Abc_Print(1, "SCMAP_AUTO_TARGET floor=%.9g untargeted_delay=%.9g target=%.9g\n",
        DelayFloor, Base.Delay, Target);
    pLink = Scm_ManCoverAig(pBase);
    pStart = Scm_ManRemapChoices(pBase, NULL);
    pTrial = Scm_ManRemapSearch(pStart ? pStart : pGia, Target, fVerbose, &Trial, pLink);
    if ( pLink ) Gia_ManStop(pLink);
    if ( pStart && pTrial == pStart ) pStart = NULL;   // the search returned its input
    if ( pStart ) Gia_ManStop(pStart);
    Keep = pTrial && Trial.fValid && Scm_QorRankBetter(&Trial, &Base, Target);
    if ( Keep && Base.Delay > 0 && Base.Delay <= Target && Trial.Delay > Base.Delay && Trial.Delay <= Target )
        Keep = Trial.Area * pow((double)Trial.Delay / Base.Delay, .125) < Base.Area;
    if ( fVerbose ) Abc_Print(1, "SCMAP_TARGET_SELECT untargeted=%d base_area=%.9g base_delay=%.9g trial_area=%.9g trial_delay=%.9g\n",
        !Keep, Base.Area, Base.Delay, Trial.Area, Trial.Delay);
    if ( Keep ) { Gia_ManStop(pBase); return pTrial; }
    if ( pTrial && pTrial != pGia ) Gia_ManStop(pTrial);
    return pBase;
}

/**Function*************************************************************

  Synopsis    [Selects refined seeds and searches electrical windows (-q, -r).]

  Description [fLoop adds the restructuring loop (-r). The returned cover
  is unsized. The input is not freed.]

  SideEffects [Uses the input scratch values and mapping fields.]

  SeeAlso     [Gia_ManScmapTarget]

***********************************************************************/
Gia_Man_t * Gia_ManScmapQuality( Gia_Man_t * pGia, int fLoop, int fVerbose )
{
    Scm_Qor_t Qor;
    if ( !fLoop )
        return Scm_ManQualityMappingInt(pGia, 0, fVerbose, NULL);
    return Scm_ManRemapSearch(pGia, 0, fVerbose, &Qor, NULL);
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
