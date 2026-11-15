/**CFile****************************************************************

  FileName    [giaScmap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [SCMap: electrical modeling and bounded shared-cover refinement.]

  Origin      [Derived from ABC standard-cell mapping by Alan Mishchenko.]

  Affiliation [UC Berkeley]

***********************************************************************/

/* Preserve separately rounded timing costs. Fusing multiply-adds can change
   near-tied cover choices and their downstream sizing trajectories. */
#if defined(__clang__)
#  pragma clang fp contract(off)
#elif defined(__GNUC__)
#  pragma GCC optimize ("fp-contract=off")
#elif defined(_MSC_VER)
#  pragma fp_contract(off)
#endif

#include <float.h>
#include <limits.h>
#include "giaScmap.h"
#include "giaScmapInt.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"
#include "misc/util/utilTruth.h"
#include "misc/extra/extra.h"
#include "base/main/main.h"
#include "misc/vec/vecMem.h"
#include "misc/vec/vecWec.h"
#include "opt/dau/dau.h"
#include "opt/sfm/sfm.h"
#include "misc/util/utilNam.h"
#include "map/scl/sclCon.h"
#include "map/scl/sclLib.h"
#include "map/scl/sclSize.h"
#include "misc/tim/tim.h"

#ifdef _MSC_VER
#  include <intrin.h>
#  define __builtin_popcount __popcnt
#endif

ABC_NAMESPACE_IMPL_START
typedef struct Scm_Par_t_ Scm_Par_t;
struct Scm_Par_t_
{
    /* Cut enumeration and diagnostic controls. */
    int            nLutSize;
    int            nCutNum;
    int            fVerbose;
    int            fVeryVerbose;
    word           Delay;
    word           Area;
    word           Edge;
    /* Mapping statistics. */
    int            MapDelay;
    float          MapAreaF;
    float          MapDelayTarget;

    /* Electrical model and refinement configuration. */
    int            nPaperAffineElaCritical;
    int            fUseRiseFallAll;
    int            nSeedMode;          // 0: gain-scaled transition costs; 1: common-load family costs
    int            fQuality;           // refine both seeds and use electrical window search
};

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define NF_LEAF_MAX  6
#define NF_CUT_MAX  32
#define NF_NO_LEAF  31
#define NF_NO_FUNC  0x3FFFFFF
#define NF_EPSILON  0.001

typedef struct Scm_Cut_t_ Scm_Cut_t;
struct Scm_Cut_t_
{
    word            Sign;           // signature
    int             Delay;          // delay
    float           Flow;           // flow
    unsigned        iFunc   : 26;   // function (NF_NO_FUNC)
    unsigned        Useless :  1;   // function
    unsigned        nLeaves :  5;   // leaf number (NF_NO_LEAF)
    int             pLeaves[NF_LEAF_MAX+1]; // leaves
};
typedef struct Scm_Cfg_t_ Scm_Cfg_t;
struct Scm_Cfg_t_
{
    unsigned        fCompl  :  1;   // complemented
    unsigned        Phase   :  7;   // match phase
    unsigned        Perm    : 24;   // match permutation
};
/* Integer arrival is legacy metadata in the affine/paired mapper. All
   timing decisions use the original floating-point arrival arrays. Keep this
   compatibility field finite and conversion-defined for slow/deep networks. */
static inline int Scm_AffArrivalRecord( double Arrival )
{
    if ( Arrival <= 0.0 ) return 0;
    if ( Arrival >= (double)(SCL_INFINITY-1) / SCL_NUM ) return SCL_INFINITY-1;
    return (int)(Arrival * SCL_NUM);
}

typedef struct Scm_Mat_t_ Scm_Mat_t;
struct Scm_Mat_t_
{
    unsigned        Gate    : 20;   // gate
    unsigned        CutH    : 10;   // cut handle
    unsigned        fCompl  :  1;   // complemented
    unsigned        fBest   :  1;   // best cut
    Scm_Cfg_t        Cfg;            // input literals
    int             D;              // delay
    float           F;              // area
};
typedef struct Scm_Obj_t_ Scm_Obj_t;
struct Scm_Obj_t_
{
    Scm_Mat_t        M[2][2];         // del/area (2x)
};
typedef struct Scm_LinArc_t_ Scm_LinArc_t;
struct Scm_LinArc_t_
{
    /* Scalar timing surrogate for one cell/input-pin arc.  All values use
       ABC's normalized ps/fF units, while mapper timing values remain in
       SCL_NUM fixed-point units at the call boundary. */
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
typedef struct Scm_LinSlewPwl_t_ Scm_LinSlewPwl_t;
struct Scm_LinSlewPwl_t_
{
    /* Exact upper envelope of the fitted per-pin load-only slew lines for
       one cell.  Segment i applies for Load >= Start[i].  The zero line is
       included while building the envelope, so this also reproduces the
       per-arc non-negative clamp without a special case at lookup time. */
    float           Start[NF_LEAF_MAX+1];
    float           Offset[NF_LEAF_MAX+1];
    float           Slope[NF_LEAF_MAX+1];
    unsigned char   nSegs;
};
typedef struct Scm_PaperArc_t_ Scm_PaperArc_t;
struct Scm_PaperArc_t_
{
    float           Delay0;
    float           DelayLoad;
    unsigned char   fValid;
};
typedef struct Scm_PaperSeg_t_ Scm_PaperSeg_t;
struct Scm_PaperSeg_t_
{
    float           Lo;
    float           Hi;
    float           Offset;
    float           Slope;
    Scm_Mat_t        M;              // witness cell/cut/config for this piece
};
typedef struct Scm_PaperPwl_t_ Scm_PaperPwl_t;
struct Scm_PaperPwl_t_
{
    Scm_PaperSeg_t * pSegs;
    int             nSegs;
    int             nAlloc;
};
typedef struct Scm_AffSeg_t_ Scm_AffSeg_t;
struct Scm_AffSeg_t_
{
    float           Lo;
    float           Hi;
    float           Offset;
    float           Slope;
};
typedef struct Scm_AffShared_t_ Scm_AffShared_t;
typedef struct Scm_AffPwl_t_ Scm_AffPwl_t;
struct Scm_AffPwl_t_
{
    Scm_AffSeg_t *   pSegs;
    int             nSegs;
    int             nAlloc;
    Scm_AffShared_t * pShared; // optional max of shared library pin curves
};
struct Scm_AffShared_t_
{
    Scm_AffPwl_t *   pPins; // borrowed immutable library curves
    float           Offsets[NF_LEAF_MAX];
    int             nPins;
};
typedef struct Scm_AffMatch_t_ Scm_AffMatch_t;
struct Scm_AffMatch_t_
{
    Scm_AffPwl_t     Arrival;
    Scm_Mat_t        M;
    float           BufferFlow;    // root virtual-buffer area included in Flow, new search only
    float           Flow;          // area of the same forward timing witness tree
    unsigned char   fSource;       // timing source (constant/PI), not a mapped cell
    unsigned char   fAnchor;       // exact preceding-cover implementation; pruning must retain it
    unsigned char   fAreaWitness;  // required-feasible area-oriented child choices
    unsigned char   ChildWitness[NF_LEAF_MAX]; // indices in already-final child full sets
};
typedef struct Scm_AffSet_t_ Scm_AffSet_t;
struct Scm_AffSet_t_
{
    Scm_AffMatch_t * pMatches;
    int             nMatches;
    int             nAlloc;
};
typedef struct Scm_AffFan_t_ Scm_AffFan_t;
struct Scm_AffFan_t_
{
    float           Constant;      // arc a+b*Lparent plus selected parent's tail
    float           SlewCoeff;     // arc coefficient multiplying this source's slew
};
typedef struct Scm_AffFanSet_t_ Scm_AffFanSet_t;
struct Scm_AffFanSet_t_
{
    Scm_AffFan_t *   pFans;
    int             nFans;
    int             nAlloc;
};
enum { NF_RF_FALL = 0, NF_RF_RISE = 1 };
typedef struct Scm_RfPair_t_ Scm_RfPair_t;
struct Scm_RfPair_t_
{
    float           Value[2];
};
typedef struct Scm_RfFan_t_ Scm_RfFan_t;
struct Scm_RfFan_t_
{
    float           Constant[2];
    float           SlewCoeff[2];
    unsigned char   Valid[2];
};
typedef struct Scm_RfFanSet_t_ Scm_RfFanSet_t;
struct Scm_RfFanSet_t_
{
    Scm_RfFan_t *   pFans;
    int             nFans;
    int             nAlloc;
};
typedef struct Scm_AffHistEdge_t_ Scm_AffHistEdge_t;
struct Scm_AffHistEdge_t_
{
    int             RootLit;
    float           Cap;
};
typedef struct Scm_AffHistSet_t_ Scm_AffHistSet_t;
struct Scm_AffHistSet_t_
{
    Scm_AffHistEdge_t * pEdges;
    int             nEdges;
    int             nAlloc;
};
typedef struct Scm_PotLoad_t_ Scm_PotLoad_t;
struct Scm_PotLoad_t_
{
    int             SrcLit;        // source literal receiving this potential load
    int             RootLit;       // potential fanout root literal
    float           Sum;           // sum of its match-induced pin loads
    float           Min;           // minimum nonzero candidate contribution at this root
    float           Max;           // maximum candidate contribution at this root
    float           CoeffSum;      // sum of affine input-slew coefficients for these candidates
    float           CoeffMin;
    float           CoeffMax;
    int             Count;         // matches at this root that actually use SrcLit
};

typedef struct Scm_Man_t_ Scm_Man_t;
struct Scm_Man_t_
{
    // Original &scmap state.  Keep this prefix aligned with upstream.
    Gia_Man_t *     pGia;
    Tim_Man_t *     pManTim;
    Scm_Par_t *      pPars;
    Vec_Mem_t *     vTtMem;
    Vec_Wec_t *     vTt2Match;
    Mio_Cell2_t *   pCells;
    int             nCells;
    Scm_Obj_t *      pNfObjs;
    Vec_Ptr_t       vPages;
    Vec_Int_t       vCutSets;
    Vec_Int_t       vMapRefs;
    Vec_Flt_t       vFlowRefs;
    Vec_Int_t       vRequired;
    Vec_Flt_t       vCutFlows;
    Vec_Int_t       vCutDelays;
    Vec_Int_t       vBackup;
    int             iCur;
    int             Iter;
    int             fUseEla;
    int             nInvs;
    int             InvDelayI;
    word            InvAreaW;
    float           InvAreaF;

    // Opt-in paper (-G) and affine (-X/-W/-A) mapper state.
    SC_Lib *        pScl;
    int *           pSclCells;
    float           AveInputCap;
    float           BufferUnitDelay; // library scale for physical buffer fits
    float           BufferRefSlew; // library-only context for virtual buffer-tree selection
    Scm_AffPwl_t * pBufferRfDelays;
    Scm_AffPwl_t * pBufferRfSlews;
    Scm_AffPwl_t * pBufferDelays; // shared library PWLs, one per cell pin
    Scm_AffPwl_t *  pBufferSlews;
    Scm_AffPwl_t *  pBufferCosts;
    Scm_LinArc_t *   pLinearArcs;
    Scm_LinSlewPwl_t * pLinearSlewPwls;
    float *         pAffineCaps; // private surrogate caps indexed by Liberty cell/pin; NULL uses physical caps
    int             nLinearSkipped;
    Scm_PaperArc_t * pPaperArcs;
    Scm_PaperPwl_t * pPaperDirectPwls;
    Scm_PaperPwl_t * pPaperPwls;
    Vec_Flt_t       vPaperLiveLoads;
    Vec_Flt_t       vPaperExpectedLoads;
    Vec_Int_t       vPaperMatchCounts;
    Vec_Wec_t *     vPaperPotRefs;
    Vec_Wec_t *     vPaperRootRefs;
    Vec_Int_t       vBackRootResolved;
    Scm_PotLoad_t *  pPaperPotLoads;
    int             nPaperPotLoads;
    int             nPaperPotAlloc;
    Scm_AffSet_t *   pAffDirect;
    Scm_AffSet_t *   pAffFull;
    Scm_AffFanSet_t * pAffFanouts;
    float *         pAffTails;
    float *         pAffSlews;
    float *         pAffLoadProbes;
    float *         pAffCoeffProbes;
    float *         pAffExactArrs;
    float *         pAffExactSlews;
    Scm_RfPair_t *  pAffExactRfArrs;
    Scm_RfPair_t *  pAffExactRfSlews;
    Scm_RfPair_t *  pAllRfLoads;
    Scm_RfPair_t *  pFamilyCapsRf;
    float *         pAffResiduals;
    Scm_Obj_t *      pAffPrev;
    int *           pAffPrevRefs;
    float *         pAffPrevLoads;
    float *         pAffEverLoads;
    unsigned char * pAffEverSeen;
    Scm_AffHistSet_t * pAffHistCurrent;
    Scm_AffHistSet_t * pAffHistSaved;
    Vec_Flt_t       vAffCalLoads;
    int             fAffLoadCalActive;
    float           AffExactDelay;
    int             fAffRefineActive;
    int             fAffAreaActive;
    float           AffAreaTarget;
    float           AffSlewCoeffMin;
    float           AffSlewCoeffMax;

    // Original statistics.
    abctime         clkStart;
    double          CutCount[6];
    int             nCutUseAll;
    // SCMap size/buffer envelopes are built per cell on first use (lazy).
    unsigned char * pEnvState;      // per Mio cell: 0 not built, 1 built, 2 failed
    void *          pEnvBufs;       // Scm_BufferType_t array of the buffer family
    int             nEnvBufs;
    float           EnvCap;
    int             fEnvError;
    // Per-call cache of own-grid arc fits, indexed by Liberty cell x pin.
    Scm_LinArc_t *  pFitCache;
    unsigned char * pFitState;      // 0 not computed, 1 fitted, 2 failed
};

static inline int          Scm_Cfg2Int( Scm_Cfg_t Mat )                                { union { int x; Scm_Cfg_t y; } v; v.y = Mat; return v.x;           }
static inline Scm_Cfg_t     Scm_Int2Cfg( int Int )                                     { union { int x; Scm_Cfg_t y; } v; v.x = Int; return v.y;           }

static inline Scm_Obj_t *   Scm_ManObj( Scm_Man_t * p, int i )                          { return p->pNfObjs + i;                                           }
static inline Mio_Cell2_t* Scm_ManCell( Scm_Man_t * p, int i )                         { return p->pCells + i;                                            }
static inline int *        Scm_ManCutSet( Scm_Man_t * p, int i )                       { return (int *)Vec_PtrEntry(&p->vPages, i >> 16) + (i & 0xFFFF);  }
static inline int          Scm_ObjCutSetId( Scm_Man_t * p, int i )                     { return Vec_IntEntry( &p->vCutSets, i );                          }
static inline int *        Scm_ObjCutSet( Scm_Man_t * p, int i )                       { return Scm_ManCutSet(p, Scm_ObjCutSetId(p, i));                    }
static inline int          Scm_ObjHasCuts( Scm_Man_t * p, int i )                      { return (int)(Vec_IntEntry(&p->vCutSets, i) > 0);                 }

static inline int          Scm_ObjCutUseless( Scm_Man_t * p, int TruthId )             { return (int)(TruthId >= Vec_WecSize(p->vTt2Match));              }

static inline float        Scm_ObjCutFlow( Scm_Man_t * p, int i )                      { return Vec_FltEntry(&p->vCutFlows, i);                           }
static inline int          Scm_ObjCutDelay( Scm_Man_t * p, int i )                     { return Vec_IntEntry(&p->vCutDelays, i);                          }
static inline void         Scm_ObjSetCutFlow( Scm_Man_t * p, int i, float a )          { Vec_FltWriteEntry(&p->vCutFlows, i, a);                          }
static inline void         Scm_ObjSetCutDelay( Scm_Man_t * p, int i, int d )           { Vec_IntWriteEntry(&p->vCutDelays, i, d);                         }

static inline int          Scm_ObjMapRefNum( Scm_Man_t * p, int i, int c )             { return Vec_IntEntry(&p->vMapRefs, Abc_Var2Lit(i,c));             }
static inline int          Scm_ObjMapRefInc( Scm_Man_t * p, int i, int c )             { return (*Vec_IntEntryP(&p->vMapRefs, Abc_Var2Lit(i,c)))++;       }
static inline int          Scm_ObjMapRefDec( Scm_Man_t * p, int i, int c )             { return --(*Vec_IntEntryP(&p->vMapRefs, Abc_Var2Lit(i,c)));       }
static inline float        Scm_ObjFlowRefs( Scm_Man_t * p, int i, int c )              { return Vec_FltEntry(&p->vFlowRefs, Abc_Var2Lit(i,c));            }

static inline Scm_Mat_t *   Scm_ObjMatchD( Scm_Man_t * p, int i, int c )                { return &Scm_ManObj(p, i)->M[c][0];                                }
static inline Scm_Mat_t *   Scm_ObjMatchA( Scm_Man_t * p, int i, int c )                { return &Scm_ManObj(p, i)->M[c][1];                                }

static inline int          Scm_CutSize( int * pCut )                                  { return pCut[0] & NF_NO_LEAF;                                     }
static inline int          Scm_CutFunc( int * pCut )                                  { return ((unsigned)pCut[0] >> 5);                                 }
static inline int *        Scm_CutLeaves( int * pCut )                                { return pCut + 1;                                                 }
static inline int          Scm_CutSetBoth( int n, int f )                             { return n | (f << 5);                                             }
static inline int          Scm_CutIsTriv( int * pCut, int i )                         { return Scm_CutSize(pCut) == 1 && pCut[1] == i;                    }
static inline int          Scm_CutHandle( int * pCutSet, int * pCut )                 { assert( pCut > pCutSet ); return pCut - pCutSet;                 }
static inline int *        Scm_CutFromHandle( int * pCutSet, int h )                  { assert( h > 0 ); return pCutSet + h;                             }

static inline int          Scm_CfgVar( Scm_Cfg_t Cfg, int i )                          { return (Cfg.Perm >> (i<<2)) & 15;                                }
static inline int          Scm_CfgCompl( Scm_Cfg_t Cfg, int i )                        { return (Cfg.Phase >> i) & 1;                                     }

#define Scm_SetForEachCut( pList, pCut, i )                   for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += Scm_CutSize(pCut) + 1 )
#define Scm_CutForEachVarCompl( pCut, Cfg, iVar, fCompl, i )  for ( i = 0; i < Scm_CutSize(pCut) && (iVar = Scm_CutLeaves(pCut)[Scm_CfgVar(Cfg, i)]) && ((fCompl = Scm_CfgCompl(Cfg, i)), 1); i++ )
#define Scm_CfgForEachVarCompl( Cfg, Size, iVar, fCompl, i )  for ( i = 0; i < Size && ((iVar = Scm_CfgVar(Cfg, i)), 1) && ((fCompl = Scm_CfgCompl(Cfg, i)), 1); i++ )

static void Scm_StoDelete( Scm_Man_t * p );
static void Scm_ManUpdateStats( Scm_Man_t * p );
static inline SC_Cell * Scm_ManSclCell( Scm_Man_t * p, Mio_Cell2_t * pCell )
{
    int Id = p->pSclCells ? p->pSclCells[pCell->Id] : -1;
    return Id >= 0 ? SC_LibCell(p->pScl, Id) : NULL;
}

static inline Scm_LinArc_t * Scm_ManLinearArc( Scm_Man_t * p, Mio_Cell2_t * pCell, int iPin )
{
    if ( p->pLinearArcs == NULL || pCell->Id >= (unsigned)p->nCells || iPin < 0 || iPin >= NF_LEAF_MAX )
        return NULL;
    return p->pLinearArcs + pCell->Id * NF_LEAF_MAX + iPin;
}

/* ABC normalizes the floating-point Liberty tables to ps/fF, but its
   integer table copies can retain the file's original units. Build private
   fixed-point tables from normalized floats for fitting. Never rewrite the
   shared library: other commands and concurrent library users own it.
   For a ps/fF library this preserves the existing fixed-point arithmetic. */
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

static void Scm_ManFitSurfaceStop( SC_Surface * pSurface )
{
    Vec_IntErase(&pSurface->vIndex0I);
    Vec_IntErase(&pSurface->vIndex1I);
    Vec_VecErase((Vec_Vec_t *)&pSurface->vDataI);
}

static void Scm_ManFitTimingStart( SC_Timing * pDst, SC_Timing * pSrc )
{
    memset(pDst, 0, sizeof(*pDst));
    pDst->tsense = pSrc->tsense;
    Scm_ManFitSurfaceStart(&pDst->pCellRise, &pSrc->pCellRise);
    Scm_ManFitSurfaceStart(&pDst->pCellFall, &pSrc->pCellFall);
    Scm_ManFitSurfaceStart(&pDst->pRiseTrans, &pSrc->pRiseTrans);
    Scm_ManFitSurfaceStart(&pDst->pFallTrans, &pSrc->pFallTrans);
}

static void Scm_ManFitTimingStop( SC_Timing * pTime )
{
    Scm_ManFitSurfaceStop(&pTime->pCellRise);
    Scm_ManFitSurfaceStop(&pTime->pCellFall);
    Scm_ManFitSurfaceStop(&pTime->pRiseTrans);
    Scm_ManFitSurfaceStop(&pTime->pFallTrans);
}

static inline int Scm_ManLinearSurfaceUsable( SC_Surface * pSurface )
{
    int nSlew = Vec_IntSize(&pSurface->vIndex0I);
    int nLoad = Vec_IntSize(&pSurface->vIndex1I);
    /* Scl_LibLookupI itself supports a constant surface and normal 2-D
       tables.  One-dimensional tables are not generated by this ASAP7
       library and are deliberately left on the exact fallback path. */
    return (nSlew == 1 && nLoad == 1) || (nSlew >= 2 && nLoad >= 2);
}

static int Scm_ManLinearSolve( double Mat[3][4], int nVars )
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

static inline void Scm_ManLinearFitAdd( double Mat[3][4], double * pX, double Y, int nVars )
{
    int i, k;
    for ( i = 0; i < nVars; i++ )
    {
        Mat[i][nVars] += pX[i] * Y;
        for ( k = 0; k < nVars; k++ )
            Mat[i][k] += pX[i] * pX[k];
    }
}

static int Scm_ManLinearArcFitRfOne( SC_Surface * pDelay, SC_Surface * pSlew,
    float * pDelay0, float * pDelayLoad, float * pDelaySlew,
    float * pSlew0, float * pSlewLoad )
{
    double DelayMat[3][4] = {{0}}, SlewMat[3][4] = {{0}};
    double XDelay[3], XSlew[2];
    int * pSlews, * pLoads, nSlews, nLoads, i, k;
    if ( !Scm_ManLinearSurfaceUsable(pDelay) ||
         !Scm_ManLinearSurfaceUsable(pSlew) )
        return 0;
    nSlews = Vec_IntSize(&pDelay->vIndex0I);
    nLoads = Vec_IntSize(&pDelay->vIndex1I);
    pSlews = Vec_IntArray(&pDelay->vIndex0I);
    pLoads = Vec_IntArray(&pDelay->vIndex1I);
    for ( i = 0; i < nSlews; i++ )
    for ( k = 0; k < nLoads; k++ )
    {
        XDelay[0] = 1.0;
        XDelay[1] = Scl_Int2Flt(pLoads[k]);
        XDelay[2] = Scl_Int2Flt(pSlews[i]);
        Scm_ManLinearFitAdd(DelayMat, XDelay,
            Scl_Int2Flt(Scl_LibLookupI(pDelay, pSlews[i], pLoads[k])), 3);
    }
    nSlews = Vec_IntSize(&pSlew->vIndex0I);
    nLoads = Vec_IntSize(&pSlew->vIndex1I);
    pSlews = Vec_IntArray(&pSlew->vIndex0I);
    pLoads = Vec_IntArray(&pSlew->vIndex1I);
    for ( i = 0; i < nSlews; i++ )
    for ( k = 0; k < nLoads; k++ )
    {
        XSlew[0] = 1.0;
        XSlew[1] = Scl_Int2Flt(pLoads[k]);
        Scm_ManLinearFitAdd(SlewMat, XSlew,
            Scl_Int2Flt(Scl_LibLookupI(pSlew, pSlews[i], pLoads[k])), 2);
    }
    if ( Vec_IntSize(&pDelay->vIndex0I) == 1 &&
         Vec_IntSize(&pDelay->vIndex1I) == 1 )
    {
        *pDelay0 = (float)DelayMat[0][3];
        *pDelayLoad = *pDelaySlew = 0.0f;
    }
    else
    {
        if ( !Scm_ManLinearSolve(DelayMat, 3) ) return 0;
        *pDelay0 = (float)DelayMat[0][3];
        *pDelayLoad = (float)DelayMat[1][3];
        *pDelaySlew = (float)DelayMat[2][3];
    }
    if ( Vec_IntSize(&pSlew->vIndex0I) == 1 &&
         Vec_IntSize(&pSlew->vIndex1I) == 1 )
    {
        *pSlew0 = (float)SlewMat[0][2];
        *pSlewLoad = 0.0f;
    }
    else
    {
        if ( !Scm_ManLinearSolve(SlewMat, 2) ) return 0;
        *pSlew0 = (float)SlewMat[0][2];
        *pSlewLoad = (float)SlewMat[1][2];
    }
    return 1;
}

/* Fit each transition/table on its own characterized points. SCMap's
   library size/tree selector use the mean. SCMap repair retains both fits,
   including buffer arcs, and routes transitions by the Liberty timing sense.
   Output slew remains load-only; mapping reuses these preprocessing fits. */
static int Scm_ManLinearArcFitOwnGridTables( SC_Timing * pTime, Scm_LinArc_t * pArc )
{
    Scm_LinArc_t Rise = {0}, Fall = {0};
    if ( pTime == NULL ||
         !Scm_ManLinearArcFitRfOne(&pTime->pCellRise, &pTime->pRiseTrans,
             &Rise.Delay0, &Rise.DelayLoad, &Rise.DelaySlew,
             &Rise.Slew0, &Rise.SlewLoad) ||
         !Scm_ManLinearArcFitRfOne(&pTime->pCellFall, &pTime->pFallTrans,
             &Fall.Delay0, &Fall.DelayLoad, &Fall.DelaySlew,
             &Fall.Slew0, &Fall.SlewLoad) )
        return 0;
    pArc->Delay0    = 0.5f * (Rise.Delay0    + Fall.Delay0);
    pArc->DelayLoad = 0.5f * (Rise.DelayLoad + Fall.DelayLoad);
    pArc->DelaySlew = 0.5f * (Rise.DelaySlew + Fall.DelaySlew);
    pArc->Slew0     = 0.5f * (Rise.Slew0     + Fall.Slew0);
    pArc->SlewLoad  = 0.5f * (Rise.SlewLoad  + Fall.SlewLoad);
    pArc->TimingSense = pTime->tsense;
    for (int t=0;t<2;t++) {
        Scm_LinArc_t *a=t?&Rise:&Fall;
        pArc->RfDelay0[t]=a->Delay0; pArc->RfDelayLoad[t]=a->DelayLoad;
        pArc->RfDelaySlew[t]=a->DelaySlew;
        pArc->RfSlew0[t]=a->Slew0; pArc->RfSlewLoad[t]=a->SlewLoad;

    }
    pArc->fValid = 1;
    return 1;
}

/* Fast path of the own-grid fit, reading the floating-point Liberty tables
   directly. With strictly increasing fixed-point indices, Scl_LibLookupI() at
   a grid point returns the stored fixed-point entry exactly (zero or full
   interpolation fractions), so this reproduces the fixed-point copy + lookup
   path bit for bit. Returns -1 when that precondition does not hold. */
static int Scm_ManSurfaceGridOk( SC_Surface * p )
{
    int i, n0 = Vec_FltSize(&p->vIndex0), n1 = Vec_FltSize(&p->vIndex1);
    if ( Vec_PtrSize(&p->vData) != n0 ) return 0;
    for ( i = 1; i < n0; i++ ) if ( Scl_Flt2Int(Vec_FltEntry(&p->vIndex0, i)) <= Scl_Flt2Int(Vec_FltEntry(&p->vIndex0, i-1)) ) return 0;
    for ( i = 1; i < n1; i++ ) if ( Scl_Flt2Int(Vec_FltEntry(&p->vIndex1, i)) <= Scl_Flt2Int(Vec_FltEntry(&p->vIndex1, i-1)) ) return 0;
    for ( i = 0; i < n0; i++ ) if ( Vec_FltSize((Vec_Flt_t *)Vec_PtrEntry(&p->vData, i)) != n1 ) return 0;
    return 1;
}
static int Scm_ManLinearArcFitRfOneFlt( SC_Surface * pDelay, SC_Surface * pSlew,
    float * pDelay0, float * pDelayLoad, float * pDelaySlew,
    float * pSlew0, float * pSlewLoad )
{
    double DelayMat[3][4] = {{0}}, SlewMat[3][4] = {{0}};
    double XDelay[3], XSlew[2];
    int nS, nL, i, k;
    nS = Vec_FltSize(&pDelay->vIndex0); nL = Vec_FltSize(&pDelay->vIndex1);
    if ( !((nS == 1 && nL == 1) || (nS >= 2 && nL >= 2)) ) return 0;
    for ( i = 0; i < nS; i++ )
    for ( k = 0; k < nL; k++ )
    {
        XDelay[0] = 1.0;
        XDelay[1] = Scl_Int2Flt(Scl_Flt2Int(Vec_FltEntry(&pDelay->vIndex1, k)));
        XDelay[2] = Scl_Int2Flt(Scl_Flt2Int(Vec_FltEntry(&pDelay->vIndex0, i)));
        Scm_ManLinearFitAdd(DelayMat, XDelay,
            Scl_Int2Flt(Scl_Flt2Int(Vec_FltEntry((Vec_Flt_t *)Vec_PtrEntry(&pDelay->vData, i), k))), 3);
    }
    {
        int nS2 = Vec_FltSize(&pSlew->vIndex0), nL2 = Vec_FltSize(&pSlew->vIndex1);
        if ( !((nS2 == 1 && nL2 == 1) || (nS2 >= 2 && nL2 >= 2)) ) return 0;
        for ( i = 0; i < nS2; i++ )
        for ( k = 0; k < nL2; k++ )
        {
            XSlew[0] = 1.0;
            XSlew[1] = Scl_Int2Flt(Scl_Flt2Int(Vec_FltEntry(&pSlew->vIndex1, k)));
            Scm_ManLinearFitAdd(SlewMat, XSlew,
                Scl_Int2Flt(Scl_Flt2Int(Vec_FltEntry((Vec_Flt_t *)Vec_PtrEntry(&pSlew->vData, i), k))), 2);
        }
        if ( nS == 1 && nL == 1 )
        {
            *pDelay0 = (float)DelayMat[0][3];
            *pDelayLoad = *pDelaySlew = 0.0f;
        }
        else
        {
            if ( !Scm_ManLinearSolve(DelayMat, 3) ) return 0;
            *pDelay0 = (float)DelayMat[0][3];
            *pDelayLoad = (float)DelayMat[1][3];
            *pDelaySlew = (float)DelayMat[2][3];
        }
        if ( nS2 == 1 && nL2 == 1 )
        {
            *pSlew0 = (float)SlewMat[0][2];
            *pSlewLoad = 0.0f;
        }
        else
        {
            if ( !Scm_ManLinearSolve(SlewMat, 2) ) return 0;
            *pSlew0 = (float)SlewMat[0][2];
            *pSlewLoad = (float)SlewMat[1][2];
        }
    }
    return 1;
}

static int Scm_ManLinearArcFitOwnGrid( SC_Cell * pCell, int iPin,
    Scm_LinArc_t * pArc )
{
    SC_Timing * pTime = Scl_CellPinTime(pCell, iPin), Fixed;
    int Result;
    if ( pTime == NULL ) return 0;
    if ( Scm_ManSurfaceGridOk(&pTime->pCellRise) && Scm_ManSurfaceGridOk(&pTime->pRiseTrans) &&
         Scm_ManSurfaceGridOk(&pTime->pCellFall) && Scm_ManSurfaceGridOk(&pTime->pFallTrans) )
    {
        Scm_LinArc_t Rise = {0}, Fall = {0};
        if ( !Scm_ManLinearArcFitRfOneFlt(&pTime->pCellRise, &pTime->pRiseTrans,
                 &Rise.Delay0, &Rise.DelayLoad, &Rise.DelaySlew, &Rise.Slew0, &Rise.SlewLoad) ||
             !Scm_ManLinearArcFitRfOneFlt(&pTime->pCellFall, &pTime->pFallTrans,
                 &Fall.Delay0, &Fall.DelayLoad, &Fall.DelaySlew, &Fall.Slew0, &Fall.SlewLoad) )
            return 0;
        pArc->Delay0    = 0.5f * (Rise.Delay0    + Fall.Delay0);
        pArc->DelayLoad = 0.5f * (Rise.DelayLoad + Fall.DelayLoad);
        pArc->DelaySlew = 0.5f * (Rise.DelaySlew + Fall.DelaySlew);
        pArc->Slew0     = 0.5f * (Rise.Slew0     + Fall.Slew0);
        pArc->SlewLoad  = 0.5f * (Rise.SlewLoad  + Fall.SlewLoad);
        pArc->TimingSense = pTime->tsense;
        for ( int t = 0; t < 2; t++ )
        {
            Scm_LinArc_t * a = t ? &Rise : &Fall;
            pArc->RfDelay0[t] = a->Delay0; pArc->RfDelayLoad[t] = a->DelayLoad;
            pArc->RfDelaySlew[t] = a->DelaySlew;
            pArc->RfSlew0[t] = a->Slew0; pArc->RfSlewLoad[t] = a->SlewLoad;
        }
        pArc->fValid = 1;
        return 1;
    }
    Scm_ManFitTimingStart(&Fixed, pTime);
    Result = Scm_ManLinearArcFitOwnGridTables(&Fixed, pArc);
    Scm_ManFitTimingStop(&Fixed);
    return Result;
}

/* The same (member, pin) own-grid fit feeds the family model, the size/buffer
   envelopes and the seed. Compute it once per mapping call; a cached copy is
   identical to recomputing into a zeroed arc. */
static int Scm_ManFitOwnGridCached( Scm_Man_t * p, SC_Cell * pCell, int iPin, Scm_LinArc_t * pArc )
{
    int Id;
    if ( p->pScl == NULL || iPin < 0 || iPin >= NF_LEAF_MAX ) return Scm_ManLinearArcFitOwnGrid(pCell, iPin, pArc);
    if ( p->pFitCache == NULL )
    {
        p->pFitCache = ABC_CALLOC(Scm_LinArc_t, SC_LibCellNum(p->pScl) * NF_LEAF_MAX);
        p->pFitState = ABC_CALLOC(unsigned char, SC_LibCellNum(p->pScl) * NF_LEAF_MAX);
    }
    Id = pCell->Id * NF_LEAF_MAX + iPin;
    if ( p->pFitState[Id] == 0 )
    {
        Scm_LinArc_t Arc;
        memset(&Arc, 0, sizeof(Arc));
        p->pFitState[Id] = Scm_ManLinearArcFitOwnGrid(pCell, iPin, &Arc) ? 1 : 2;
        p->pFitCache[Id] = Arc;
    }
    if ( p->pFitState[Id] == 2 ) return 0;
    *pArc = p->pFitCache[Id];
    return 1;
}

static int Scm_ManAffineModelArc( Scm_Man_t * p, SC_Cell * pCell,
    int iPin, Scm_LinArc_t * pArc )
{
    int i, Count = 0;
    double Sums[5] = {0}, Rf[2][5]={{0}};
    SC_Cell * pMember;

    /* SCMap uses one physical buffer consistently for
       its fit, input capacitance and area.  Logic cells retain the
       family-average model. */
    if ( (12 == 12) &&
         pCell == Scm_ManSclCell(p, p->pCells + 2) )
        return Scm_ManFitOwnGridCached(p, pCell, iPin, pArc);
    /* Each usable family member has equal weight.  Fit its rise/fall delay
       and transition tables on their own grids, then average coefficients.
       This runs once before mapping; emitted cells and areas are unchanged. */
    SC_RingForEachCell(pCell, pMember, i)
    {
        Scm_LinArc_t Arc = {0};
        if ( pMember->fSkip ) continue;
        if ( !Scm_ManFitOwnGridCached(p, pMember, iPin, &Arc) ) return 0;
        Sums[0] += Arc.Delay0;
        Sums[1] += Arc.DelayLoad;
        Sums[2] += Arc.DelaySlew;
        Sums[3] += Arc.Slew0;
        Sums[4] += Arc.SlewLoad;
        pArc->TimingSense=Arc.TimingSense;
        for(int t=0;t<2;t++) {
            Rf[t][0]+=Arc.RfDelay0[t]; Rf[t][1]+=Arc.RfDelayLoad[t];
            Rf[t][2]+=Arc.RfDelaySlew[t]; Rf[t][3]+=Arc.RfSlew0[t]; Rf[t][4]+=Arc.RfSlewLoad[t];
        }
        Count++;
    }
    if ( Count == 0 ) return 0;
    pArc->Delay0 = (float)(Sums[0] / Count);
    pArc->DelayLoad = (float)(Sums[1] / Count);
    pArc->DelaySlew = (float)(Sums[2] / Count);
    pArc->Slew0 = (float)(Sums[3] / Count);
    pArc->SlewLoad = (float)(Sums[4] / Count);
    for(int t=0;t<2;t++) {
        pArc->RfDelay0[t]=Rf[t][0]/Count; pArc->RfDelayLoad[t]=Rf[t][1]/Count;
        pArc->RfDelaySlew[t]=Rf[t][2]/Count;
        pArc->RfSlew0[t]=Rf[t][3]/Count; pArc->RfSlewLoad[t]=Rf[t][4]/Count;
    }
    pArc->fValid = 1;
    return 1;
}

static void Scm_ManAffineUnitBlend( Scm_Man_t * p )
{
    float * pDelays, Unit, Weight = 0.25f;
    float Slew;
    int i, k, n = 0;

    Slew = Abc_SclComputeAverageSlew(p->pScl);
    pDelays = ABC_ALLOC(float, p->nCells * NF_LEAF_MAX);
    for ( i = 0; i < p->nCells; i++ )
        for ( k = 0; k < (int)p->pCells[i].nFanins; k++ )
        {
            Scm_LinArc_t * pArc = Scm_ManLinearArc(p, p->pCells + i, k);
            pDelays[n++] = Abc_MaxFloat(1.0e-3f, pArc->Delay0 +
                pArc->DelayLoad * p->AveInputCap + pArc->DelaySlew * Slew);
        }
    /* A library-only scale gives the unit term ps units.  No circuit
       timing, benchmark result, or stime measurement enters this value. */
    for ( i = 1; i < n; i++ )
    {
        float Value = pDelays[i];
        for ( k = i; k > 0 && pDelays[k-1] > Value; k-- )
            pDelays[k] = pDelays[k-1];
        pDelays[k] = Value;
    }
    assert(n > 0);
    Unit = pDelays[n/2];
    p->BufferUnitDelay = Unit;
    ABC_FREE(pDelays);
    for ( i = 0; i < p->nCells; i++ )
        for ( k = 0; k < (int)p->pCells[i].nFanins; k++ )
        {
            Scm_LinArc_t * pArc = Scm_ManLinearArc(p, p->pCells + i, k);
            pArc->Delay0 = (1.0f - Weight) * pArc->Delay0 + Weight * Unit;
            pArc->DelayLoad *= 1.0f - Weight;
            pArc->DelaySlew *= 1.0f - Weight;
            for(int t=0;t<2;t++) {
                pArc->RfDelay0[t]=(1-Weight)*pArc->RfDelay0[t]+Weight*Unit;
                pArc->RfDelayLoad[t]*=1-Weight; pArc->RfDelaySlew[t]*=1-Weight;
            }
        }
    if ( p->pPars->fVerbose )
        Abc_Print(1, "Affine unit blend: 25 percent, unit %.4f ps.\n", Unit);
}

static int Scm_ManLinearSlewPwlFit( Scm_Man_t * p, Mio_Cell2_t * pCell,
    Scm_LinSlewPwl_t * pPwl )
{
    typedef struct Scm_LinLine_t_ Scm_LinLine_t;
    struct Scm_LinLine_t_ { double Offset, Slope, Start; };
    Scm_LinLine_t Lines[NF_LEAF_MAX+1], Unique[NF_LEAF_MAX+1], Hull[NF_LEAF_MAX+1], Temp;
    int i, k, nLines = 1, nUnique = 0, nHull = 0;
    memset( pPwl, 0, sizeof(*pPwl) );
    /* The zero line is required because Scm_ManLinearSlew() clamps every
       pin result at zero before the match-level maximum is taken. */
    Lines[0].Offset = Lines[0].Slope = 0.0;
    for ( i = 0; i < (int)pCell->nFanins; i++ )
    {
        Scm_LinArc_t * pArc = Scm_ManLinearArc( p, pCell, i );
        if ( pArc == NULL || !pArc->fValid )
            return 0;
        Lines[nLines].Offset = pArc->Slew0;
        Lines[nLines].Slope  = pArc->SlewLoad;
        nLines++;
    }
    /* Sort by slope, retaining only the highest intercept among parallel
       lines.  The maximum envelope then visits lines in this slope order. */
    for ( i = 0; i < nLines; i++ )
    for ( k = i + 1; k < nLines; k++ )
        if ( Lines[k].Slope < Lines[i].Slope ||
            (Lines[k].Slope == Lines[i].Slope && Lines[k].Offset > Lines[i].Offset) )
            Temp = Lines[i], Lines[i] = Lines[k], Lines[k] = Temp;
    for ( i = 0; i < nLines; i++ )
    {
        if ( nUnique && Lines[i].Slope == Unique[nUnique-1].Slope )
            continue;
        Unique[nUnique++] = Lines[i];
    }
    for ( i = 0; i < nUnique; i++ )
    {
        Scm_LinLine_t Cur = Unique[i];
        double Cross = -FLT_MAX;
        while ( nHull )
        {
            Scm_LinLine_t * pLast = Hull + nHull - 1;
            /* Parallel lines were removed above. */
            Cross = (pLast->Offset - Cur.Offset) / (Cur.Slope - pLast->Slope);
            if ( nHull == 1 || Cross > pLast->Start )
                break;
            nHull--;
        }
        Cur.Start = nHull ? Cross : -FLT_MAX;
        Hull[nHull++] = Cur;
    }
    assert( nHull > 0 && nHull <= NF_LEAF_MAX + 1 );
    for ( i = 0; i < nHull; i++ )
    {
        pPwl->Start[i]  = (float)Hull[i].Start;
        pPwl->Offset[i] = (float)Hull[i].Offset;
        pPwl->Slope[i]  = (float)Hull[i].Slope;
    }
    pPwl->nSegs = (unsigned char)nHull;
    return 1;
}

static inline float Scm_ManCellPinCap( Scm_Man_t * p, SC_Cell * pCell, int iPin )
{
    if ( p->pAffineCaps ) return p->pAffineCaps[pCell->Id * NF_LEAF_MAX + iPin];
    return SC_CellPinCap(pCell, iPin);
}

static inline float Scm_ManInvInputCap( Scm_Man_t * p )
{
    SC_Cell * pSclCell = Scm_ManSclCell( p, p->pCells + 3 );
    return pSclCell ? Scm_ManCellPinCap(p, pSclCell, 0) : 0.0;
}

static inline int          Scm_CfgIsCutPermutation( Scm_Cfg_t Cfg, int nFans )
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

static inline int          Scm_CutLeavesAreValid( int * pFans, int nFans, int iRoot )
{
    int i;
    for ( i = 0; i < nFans; i++ )
        /* A cut is topological: a leaf cannot be the root itself or a
           later GIA object.  The latter would otherwise survive a mere
           array-bounds check and can make the derived cell map cyclic. */
        if ( pFans[i] < 0 || pFans[i] >= iRoot )
            return 0;
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static int Scm_ManAffBufferPwlsStart( Scm_Man_t * p );

static Scm_Man_t * Scm_StoCreate( Gia_Man_t * pGia, Scm_Par_t * pPars )
{
    extern void Mf_ManSetFlowRefs( Gia_Man_t * p, Vec_Int_t * vRefs );
    Vec_Int_t * vFlowRefs;
    Scm_Man_t * p;
    int i, Entry;
    assert( pPars->nCutNum > 1  && pPars->nCutNum <= NF_CUT_MAX );
    assert( pPars->nLutSize > 1 && pPars->nLutSize <= NF_LEAF_MAX );
    ABC_FREE( pGia->pRefs );
    Vec_IntFreeP( &pGia->vCellMapping );
    if ( Gia_ManHasChoices(pGia) )
        Gia_ManSetPhase(pGia);
    p = ABC_CALLOC( Scm_Man_t, 1 );
    p->clkStart = Abc_Clock();
    p->pGia     = pGia;
    p->pManTim  = (Tim_Man_t *)pGia->pManTime;
    p->pPars    = pPars;
    p->pNfObjs  = ABC_CALLOC( Scm_Obj_t, Gia_ManObjNum(pGia) );
    p->iCur     = 2;
    Vec_PtrGrow( &p->vPages, 256 );
    Vec_IntFill( &p->vMapRefs,  2*Gia_ManObjNum(pGia), 0 );
    Vec_FltFill( &p->vFlowRefs, 2*Gia_ManObjNum(pGia), 0 );
    Vec_IntFill( &p->vRequired, 2*Gia_ManObjNum(pGia), SCL_INFINITY );
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
        return NULL;

    {
        SC_Cell * pSclCell;
        int nPins = 0, nLits = 2 * Gia_ManObjNum(pGia);
        p->pScl = (SC_Lib *)Abc_FrameReadLibScl();
        if ( p->pScl == NULL )
        {
            Abc_Print( -1, "&scmap -G/-X requires a Liberty library loaded with read_lib.\n" );
            Scm_StoDelete( p );
            return NULL;
        }

            p->BufferRefSlew = Abc_SclComputeAverageSlew(p->pScl);
        p->pSclCells = ABC_ALLOC( int, p->nCells );

            p->pAffineCaps = ABC_CALLOC(float, SC_LibCellNum(p->pScl) * NF_LEAF_MAX);
        if ( pPars->fQuality )
            p->pFamilyCapsRf = ABC_CALLOC(Scm_RfPair_t, SC_LibCellNum(p->pScl) * NF_LEAF_MAX);
        for ( i = 0; i < p->nCells; i++ )
        {
            p->pSclCells[i] = p->pCells[i].pName ?
                Abc_SclCellFind(p->pScl, p->pCells[i].pName) : -1;
            if ( p->pSclCells[i] < 0 )
                continue;
            pSclCell = SC_LibCell(p->pScl, p->pSclCells[i]);
            if ( p->pAffineCaps )
            {
                SC_Cell * pMember;
                int k, Count = 0;
                double Caps[NF_LEAF_MAX] = {0}, Fall[NF_LEAF_MAX] = {0}, Rise[NF_LEAF_MAX] = {0};
                assert(pSclCell->n_inputs <= NF_LEAF_MAX);
                SC_RingForEachCell(pSclCell, pMember, k)
                {
                    if ( pMember->fSkip ) continue;
                    for ( Entry = 0; Entry < pMember->n_inputs; Entry++ )
                    {
                        Caps[Entry] += SC_CellPinCap(pMember, Entry);
                        Fall[Entry] += SC_CellPin(pMember, Entry)->fall_cap;
                        Rise[Entry] += SC_CellPin(pMember, Entry)->rise_cap;
                    }
                    Count++;
                }
                if ( Count == 0 )
                {
                    Scm_StoDelete(p);
                    return NULL;
                }
                for ( Entry = 0; Entry < pSclCell->n_inputs; Entry++ )
                    p->pAffineCaps[pSclCell->Id * NF_LEAF_MAX + Entry] =
                        ((12 == 12) && i == 2) ?
                        SC_CellPinCap(pSclCell, Entry) : (float)(Caps[Entry] / Count);
                if ( p->pFamilyCapsRf )
                    for ( Entry = 0; Entry < pSclCell->n_inputs; Entry++ )
                    {
                        Scm_RfPair_t * pCap = p->pFamilyCapsRf + pSclCell->Id * NF_LEAF_MAX + Entry;
                        pCap->Value[0] = i == 2 ? SC_CellPin(pSclCell, Entry)->fall_cap : (float)(Fall[Entry] / Count);
                        pCap->Value[1] = i == 2 ? SC_CellPin(pSclCell, Entry)->rise_cap : (float)(Rise[Entry] / Count);
                    }
            }
            for ( Entry = 0; Entry < pSclCell->n_inputs; Entry++ )
                p->AveInputCap += Scm_ManCellPinCap(p, pSclCell, Entry), nPins++;
        }
        p->AveInputCap /= Abc_MaxInt(1, nPins);
        if ( p->pSclCells[3] < 0 )
        {
            Abc_Print( -1, "&scmap -G/-X cannot match inverter %s in the Liberty library.\n",
                p->pCells[3].pName );
            Scm_StoDelete( p );
            return NULL;
        }
        Vec_FltFill( &p->vPaperLiveLoads, nLits, 0.0f );
        Vec_FltFill( &p->vPaperExpectedLoads, nLits, 0.0f );
        Vec_IntFill( &p->vPaperMatchCounts, nLits, 0 );
        p->vPaperPotRefs = Vec_WecStart( nLits );

        {
            p->pLinearArcs = ABC_CALLOC( Scm_LinArc_t, p->nCells * NF_LEAF_MAX );
            p->pLinearSlewPwls = ABC_CALLOC( Scm_LinSlewPwl_t, p->nCells );

            for ( i = 0; i < p->nCells; i++ )
            {
                Mio_Cell2_t * pMioCell = p->pCells + i;
                if ( pMioCell->nFanins == 0 )
                    continue;
                pSclCell = Scm_ManSclCell(p, pMioCell);
                if ( pSclCell == NULL || pMioCell->nFanins != pSclCell->n_inputs )
                {
                    p->nLinearSkipped += pMioCell->nFanins;
                    continue;
                }
                for ( Entry = 0; Entry < (int)pMioCell->nFanins; Entry++ )
                    if ( !Scm_ManAffineModelArc(p, pSclCell, Entry,
                            Scm_ManLinearArc(p, pMioCell, Entry)) )
                        p->nLinearSkipped++;
            }
            if ( p->nLinearSkipped == 0 )
                Scm_ManAffineUnitBlend(p);
            if ( p->nLinearSkipped == 0 )
                for ( i = 0; i < p->nCells; i++ )
                    if ( !Scm_ManLinearSlewPwlFit(p, p->pCells + i,
                            p->pLinearSlewPwls + i) )
                        p->nLinearSkipped++;
            if ( p->nLinearSkipped )
            {
                Abc_Print( -1, "&scmap -X could not fit %d Liberty timing arcs.\n",
                    p->nLinearSkipped );
                Scm_StoDelete( p );
                return NULL;
            }
            if ( (12 == 12) &&
                 !Scm_ManAffBufferPwlsStart(p) )
            {
                Abc_Print(-1, "&scmap: could not construct buffered library PWLs.\n");
                Scm_StoDelete(p);
                return NULL;
            }
            p->pAffDirect = ABC_CALLOC( Scm_AffSet_t, nLits );
            p->pAffFull = ABC_CALLOC( Scm_AffSet_t, nLits );

            p->pAffFanouts = ABC_CALLOC( Scm_AffFanSet_t, nLits );
            p->pAffTails = ABC_ALLOC( float, nLits );
            p->pAffSlews = ABC_ALLOC( float, nLits );
            if ( 1 || pPars->fUseRiseFallAll )
            {
                p->pAffLoadProbes = ABC_ALLOC( float, 4 * nLits );
                p->pAffCoeffProbes = ABC_ALLOC( float, 4 * nLits );
                p->pAffExactArrs = ABC_CALLOC( float, nLits );
                p->pAffExactSlews = ABC_CALLOC( float, nLits );
                if ( pPars->fUseRiseFallAll )
                {
                    p->pAffExactRfArrs = ABC_CALLOC( Scm_RfPair_t, nLits );
                    p->pAffExactRfSlews = ABC_CALLOC( Scm_RfPair_t, nLits );
                    if ( pPars->fUseRiseFallAll )
                        p->pAllRfLoads = ABC_CALLOC( Scm_RfPair_t, nLits );
                }
                p->pAffResiduals = ABC_CALLOC( float, nLits );
                p->pAffPrev = ABC_ALLOC( Scm_Obj_t, Gia_ManObjNum(pGia) );
                p->pAffPrevRefs = ABC_ALLOC( int, nLits );
                p->pAffPrevLoads = ABC_ALLOC( float, nLits );

                {
                    Vec_IntFill( &p->vBackRootResolved, nLits, 0 );
                    Vec_FltFill( &p->vAffCalLoads, nLits, 0.0f );
                    p->vPaperRootRefs = Vec_WecStart( nLits );
                }

            }
        }
    }
    p->InvDelayI = p->pCells[3].iDelays[0];
    p->InvAreaW  = p->pCells[3].AreaW;
    p->InvAreaF  = p->pCells[3].AreaF;
    Scm_ObjMatchD(p, 0, 0)->Gate = 0;
    Scm_ObjMatchD(p, 0, 1)->Gate = 1;
    return p;
}
static void Scm_StoDelete( Scm_Man_t * p )
{
    int i;
    ABC_FREE( p->pFitCache );
    ABC_FREE( p->pFitState );
    ABC_FREE( p->pEnvState );
    ABC_FREE( p->pEnvBufs );
    Vec_PtrFreeData( &p->vPages );
    ABC_FREE( p->vPages.pArray );
    ABC_FREE( p->vMapRefs.pArray );
    ABC_FREE( p->vFlowRefs.pArray );
    ABC_FREE( p->vRequired.pArray );
    ABC_FREE( p->vCutSets.pArray );
    ABC_FREE( p->vCutFlows.pArray );
    ABC_FREE( p->vCutDelays.pArray );
    ABC_FREE( p->vBackup.pArray );
    ABC_FREE( p->pSclCells );
    ABC_FREE( p->pAffineCaps );
    ABC_FREE( p->pFamilyCapsRf );
    ABC_FREE( p->pLinearArcs );
    ABC_FREE( p->pLinearSlewPwls );
    if ( p->pBufferDelays )
        for ( i = 0; i < p->nCells * NF_LEAF_MAX; i++ )
            ABC_FREE(p->pBufferDelays[i].pSegs);
    if ( p->pBufferSlews )
        for ( i = 0; i < p->nCells; i++ )
        {
            ABC_FREE(p->pBufferSlews[i].pSegs);
            ABC_FREE(p->pBufferCosts[i].pSegs);
        }
    ABC_FREE(p->pBufferDelays);
    ABC_FREE(p->pBufferSlews);
    ABC_FREE(p->pBufferCosts);
    if(p->pBufferRfDelays) for(i=0;i<2*p->nCells*NF_LEAF_MAX;i++) ABC_FREE(p->pBufferRfDelays[i].pSegs);
    if(p->pBufferRfSlews) for(i=0;i<2*p->nCells;i++) ABC_FREE(p->pBufferRfSlews[i].pSegs);
    ABC_FREE(p->pBufferRfDelays); ABC_FREE(p->pBufferRfSlews);
    if ( p->pPaperDirectPwls )
        for ( i = 0; i < 2*Gia_ManObjNum(p->pGia); i++ )
            ABC_FREE( p->pPaperDirectPwls[i].pSegs );
    if ( p->pPaperPwls )
        for ( i = 0; i < 2*Gia_ManObjNum(p->pGia); i++ )
            ABC_FREE( p->pPaperPwls[i].pSegs );
    if ( p->pAffDirect )
        for ( i = 0; i < 2*Gia_ManObjNum(p->pGia); i++ )
        {
            int k;
            for ( k = 0; k < p->pAffDirect[i].nMatches; k++ )
            {
                ABC_FREE(p->pAffDirect[i].pMatches[k].Arrival.pSegs);
                ABC_FREE(p->pAffDirect[i].pMatches[k].Arrival.pShared);
            }
            for ( k = 0; k < p->pAffFull[i].nMatches; k++ )
            {
                ABC_FREE(p->pAffFull[i].pMatches[k].Arrival.pSegs);
                ABC_FREE(p->pAffFull[i].pMatches[k].Arrival.pShared);
            }
            ABC_FREE( p->pAffDirect[i].pMatches );
            ABC_FREE( p->pAffFull[i].pMatches );
            ABC_FREE( p->pAffFanouts[i].pFans );
        }
    ABC_FREE( p->pPaperArcs );
    ABC_FREE( p->pPaperDirectPwls );
    ABC_FREE( p->pPaperPwls );
    ABC_FREE( p->pAffDirect );
    ABC_FREE( p->pAffFull );
    ABC_FREE( p->pAffFanouts );
    ABC_FREE( p->pAffTails );
    ABC_FREE( p->pAffSlews );
    ABC_FREE( p->pAffLoadProbes );
    ABC_FREE( p->pAffCoeffProbes );
    ABC_FREE( p->pAffExactArrs );
    ABC_FREE( p->pAffExactSlews );
    ABC_FREE( p->pAffExactRfArrs );
    ABC_FREE( p->pAffExactRfSlews );
    ABC_FREE( p->pAllRfLoads );
    ABC_FREE( p->pAffResiduals );
    ABC_FREE( p->pAffPrev );
    ABC_FREE( p->pAffPrevRefs );
    ABC_FREE( p->pAffPrevLoads );
    ABC_FREE( p->pAffEverLoads );
    ABC_FREE( p->pAffEverSeen );
    if ( p->pAffHistCurrent || p->pAffHistSaved )
    {
        int nLits = 2 * Gia_ManObjNum(p->pGia);
        for ( i = 0; i < nLits; i++ )
        {
            if ( p->pAffHistCurrent ) ABC_FREE( p->pAffHistCurrent[i].pEdges );
            if ( p->pAffHistSaved ) ABC_FREE( p->pAffHistSaved[i].pEdges );
        }
    }
    ABC_FREE( p->pAffHistCurrent );
    ABC_FREE( p->pAffHistSaved );
    ABC_FREE( p->vAffCalLoads.pArray );
    ABC_FREE( p->vPaperLiveLoads.pArray );
    ABC_FREE( p->vPaperExpectedLoads.pArray );
    ABC_FREE( p->vPaperMatchCounts.pArray );
    Vec_WecFreeP( &p->vPaperPotRefs );
    Vec_WecFreeP( &p->vPaperRootRefs );
    ABC_FREE( p->vBackRootResolved.pArray );
    ABC_FREE( p->pPaperPotLoads );
    ABC_FREE( p->pNfObjs );
    ABC_FREE( p );
}

static inline int Scm_CutComputeTruth6( Scm_Man_t * p, Scm_Cut_t * pCut0, Scm_Cut_t * pCut1, int fCompl0, int fCompl1, Scm_Cut_t * pCutR, int fIsXor )
{
//    extern int Scm_ManTruthCanonicize( word * t, int nVars );
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

static inline int Scm_CutCountBits( word i )
{
    i = i - ((i >> 1) & 0x5555555555555555);
    i = (i & 0x3333333333333333) + ((i >> 2) & 0x3333333333333333);
    i = ((i + (i >> 4)) & 0x0F0F0F0F0F0F0F0F);
    return (i*(0x0101010101010101))>>56;
}
static inline word Scm_CutGetSign( int * pLeaves, int nLeaves )
{
    word Sign = 0; int i;
    for ( i = 0; i < nLeaves; i++ )
        Sign |= ((word)1) << (pLeaves[i] & 0x3F);
    return Sign;
}
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
static inline int Scm_ManSaveCuts( Scm_Man_t * p, Scm_Cut_t ** pCuts, int nCuts, int fUseful )
{
    int i, * pPlace, iCur, nInts = 1, nCutsNew = 0;
    for ( i = 0; i < nCuts; i++ )
        if ( !fUseful || !pCuts[i]->Useless )
            nInts += pCuts[i]->nLeaves + 1, nCutsNew++;
    if ( (p->iCur & 0xFFFF) + nInts > 0xFFFF )
        p->iCur = ((p->iCur >> 16) + 1) << 16;
    if ( Vec_PtrSize(&p->vPages) == (p->iCur >> 16) )
        Vec_PtrPush( &p->vPages, ABC_ALLOC(int, (1<<16)) );
    iCur = p->iCur; p->iCur += nInts;
    pPlace = Scm_ManCutSet( p, iCur );
    *pPlace++ = nCutsNew;
    for ( i = 0; i < nCuts; i++ )
        if ( !fUseful || !pCuts[i]->Useless )
        {
            *pPlace++ = Scm_CutSetBoth( pCuts[i]->nLeaves, pCuts[i]->iFunc );
            memcpy( pPlace, pCuts[i]->pLeaves, sizeof(int) * pCuts[i]->nLeaves );
            pPlace += pCuts[i]->nLeaves;
        }
    return iCur;
}
static inline int Scm_ManCountUseful( Scm_Cut_t ** pCuts, int nCuts )
{
    int i, Count = 0;
    for ( i = 0; i < nCuts; i++ )
        Count += !pCuts[i]->Useless;
    return Count;
}
static inline int Scm_ManCountMatches( Scm_Man_t * p, Scm_Cut_t ** pCuts, int nCuts )
{
    int i, Count = 0;
    for ( i = 0; i < nCuts; i++ )
        if ( !pCuts[i]->Useless )
            Count += Vec_IntSize(Vec_WecEntry(p->vTt2Match, Abc_Lit2Var(pCuts[i]->iFunc))) / 2;
    return Count;
}

/**Function*************************************************************

  Synopsis    [Check correctness of cuts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

static inline int Scm_CutMergeOrder( Scm_Cut_t * pCut0, Scm_Cut_t * pCut1, Scm_Cut_t * pCut, int nLutSize )
{
    int nSize0   = pCut0->nLeaves;
    int nSize1   = pCut1->nLeaves;
    int i, * pC0 = pCut0->pLeaves;
    int k, * pC1 = pCut1->pLeaves;
    int c, * pC  = pCut->pLeaves;
    // the case of the largest cut sizes
    if ( nSize0 == nLutSize && nSize1 == nLutSize )
    {
        for ( i = 0; i < nSize0; i++ )
        {
            if ( pC0[i] != pC1[i] )  return 0;
            pC[i] = pC0[i];
        }
        pCut->nLeaves = nLutSize;
        pCut->iFunc = NF_NO_FUNC;
        pCut->Sign = pCut0->Sign | pCut1->Sign;
        return 1;
    }
    // compare two cuts with different numbers
    i = k = c = 0;
    if ( nSize0 == 0 ) goto FlushCut1;
    if ( nSize1 == 0 ) goto FlushCut0;
    while ( 1 )
    {
        if ( c == nLutSize ) return 0;
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
    if ( c + nSize0 > nLutSize + i ) return 0;
    while ( i < nSize0 )
        pC[c++] = pC0[i++];
    pCut->nLeaves = c;
    pCut->iFunc = NF_NO_FUNC;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;

FlushCut1:
    if ( c + nSize1 > nLutSize + k ) return 0;
    while ( k < nSize1 )
        pC[c++] = pC1[k++];
    pCut->nLeaves = c;
    pCut->iFunc = NF_NO_FUNC;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;
}
static inline int Scm_CutMergeOrderMux( Scm_Cut_t * pCut0, Scm_Cut_t * pCut1, Scm_Cut_t * pCut2, Scm_Cut_t * pCut, int nLutSize )
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
        if ( c == nLutSize ) return 0;
        pC[c++] = xMin;
        if (x0 == xMin) i0++;
        if (x1 == xMin) i1++;
        if (x2 == xMin) i2++;
    }
    pCut->nLeaves = c;
    pCut->iFunc = NF_NO_FUNC;
    pCut->Sign = pCut0->Sign | pCut1->Sign | pCut2->Sign;
    return 1;
}
static inline int Scm_SetCutIsContainedOrder( Scm_Cut_t * pBase, Scm_Cut_t * pCut ) // check if pCut is contained in pBase
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
static inline int Scm_SetLastCutIsContained( Scm_Cut_t ** pCuts, int nCuts )
{
    int i;
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[i]->nLeaves <= pCuts[nCuts]->nLeaves && (pCuts[i]->Sign & pCuts[nCuts]->Sign) == pCuts[i]->Sign && Scm_SetCutIsContainedOrder(pCuts[nCuts], pCuts[i]) )
            return 1;
    return 0;
}
static inline int Scm_SetLastCutContainsArea( Scm_Cut_t ** pCuts, int nCuts )
{
    int i, k, fChanges = 0;
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[nCuts]->nLeaves < pCuts[i]->nLeaves && (pCuts[nCuts]->Sign & pCuts[i]->Sign) == pCuts[nCuts]->Sign && Scm_SetCutIsContainedOrder(pCuts[i], pCuts[nCuts]) )
            pCuts[i]->nLeaves = NF_NO_LEAF, fChanges = 1;
    if ( !fChanges )
        return nCuts;
    for ( i = k = 0; i <= nCuts; i++ )
    {
        if ( pCuts[i]->nLeaves == NF_NO_LEAF )
            continue;
        if ( k < i )
            ABC_SWAP( Scm_Cut_t *, pCuts[k], pCuts[i] )
        k++;
    }
    return k - 1;
}
static inline int Scm_CutCompareArea( Scm_Cut_t * pCut0, Scm_Cut_t * pCut1 )
{
    if ( pCut0->Useless < pCut1->Useless )  return -1;
    if ( pCut0->Useless > pCut1->Useless )  return  1;
    if ( pCut0->Flow    < pCut1->Flow - NF_EPSILON )  return -1;
    if ( pCut0->Flow    > pCut1->Flow + NF_EPSILON )  return  1;
    if ( pCut0->Delay   < pCut1->Delay   )  return -1;
    if ( pCut0->Delay   > pCut1->Delay   )  return  1;
    if ( pCut0->nLeaves < pCut1->nLeaves )  return -1;
    if ( pCut0->nLeaves > pCut1->nLeaves )  return  1;
    return 0;
}
static inline void Scm_SetSortByArea( Scm_Cut_t ** pCuts, int nCuts )
{
    int i;
    for ( i = nCuts; i > 0; i-- )
    {
        if ( Scm_CutCompareArea(pCuts[i - 1], pCuts[i]) < 0 )//!= 1 )
            return;
        ABC_SWAP( Scm_Cut_t *, pCuts[i - 1], pCuts[i] )
    }
}

/* SCMap reserves three of fifteen nontrivial cut slots for shallow cuts.
   The other slots retain area-priority cuts. */
static int Scm_CutDepthBetter( Scm_Cut_t * a, Scm_Cut_t * b )
{
    if ( a->Useless != b->Useless ) return a->Useless < b->Useless;
    if ( a->Delay != b->Delay ) return a->Delay < b->Delay;
    return Scm_CutCompareArea(a, b) < 0;
}

static int Scm_SetAddCutStructure( Scm_Man_t * p, Scm_Cut_t ** Cuts, int n, int Limit )
{
    Scm_Cut_t * pWorst;
    int j, Count, Best, AreaSlots;

    if ( !n ) return 1;
    Count = Scm_SetLastCutContainsArea(Cuts, n) + 1;
    /* Retained cuts are in area order, so insert the new cut once. */
    Scm_SetSortByArea(Cuts, Count - 1);
    if ( Count < Limit ) return Count;
    AreaSlots = (Limit - 1) - Abc_MaxInt(1, (Limit - 1) / 4);
    /* Exactly one cut is dropped (Count == Limit). Selecting the remaining
       depth slots one by one (earliest index wins ties) leaves the cut with
       the worst depth rank and, among equals, the largest index. Find it in
       one scan and move it to the end; the retained order is unchanged. */
    assert( Count == Limit );
    Best = AreaSlots;
    for ( j = AreaSlots + 1; j < Count; j++ )
        if ( !Scm_CutDepthBetter(Cuts[j], Cuts[Best]) ) Best = j;
    pWorst = Cuts[Best];
    for ( j = Best; j + 1 < Count; j++ ) Cuts[j] = Cuts[j+1];
    Cuts[Count-1] = pWorst;
    return Limit - 1;
}

static inline int Scm_CutArea( Scm_Man_t * p, int nLeaves )
{
    if ( nLeaves < 2 )
        return 0;
    return nLeaves;
}
static inline void Scm_CutParams( Scm_Man_t * p, Scm_Cut_t * pCut, float FlowRefs )
{
    int i, nLeaves = pCut->nLeaves;
    assert( nLeaves <= p->pPars->nLutSize );
    pCut->Delay = 0;
    pCut->Flow  = 0;
    for ( i = 0; i < nLeaves; i++ )
    {
        pCut->Delay = Abc_MaxInt( pCut->Delay, Scm_ObjCutDelay(p, pCut->pLeaves[i]) );
        pCut->Flow += Scm_ObjCutFlow(p, pCut->pLeaves[i]);
    }
    pCut->Delay += (int)(nLeaves > 1);
    pCut->Flow = (pCut->Flow + Scm_CutArea(p, nLeaves)) / FlowRefs;
}
static void Scm_ObjMergeOrder( Scm_Man_t * p, int iObj )
{
    Scm_Cut_t pCuts0[NF_CUT_MAX], pCuts1[NF_CUT_MAX], pCuts[NF_CUT_MAX], * pCutsR[NF_CUT_MAX];
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    float dFlowRefs  = Scm_ObjFlowRefs(p, iObj, 0) + Scm_ObjFlowRefs(p, iObj, 1);
    int nLutSize = p->pPars->nLutSize;
    int nCutNum  = p->pPars->nCutNum;
    int nCuts0   = Scm_ManPrepareCuts(pCuts0, p, Gia_ObjFaninId0(pObj, iObj), 1);
    int nCuts1   = Scm_ManPrepareCuts(pCuts1, p, Gia_ObjFaninId1(pObj, iObj), 1);
    int fComp0   = Gia_ObjFaninC0(pObj);
    int fComp1   = Gia_ObjFaninC1(pObj);
    int iSibl    = Gia_ObjSibl(p->pGia, iObj);
    Scm_Cut_t * pCut0, * pCut1, * pCut0Lim = pCuts0 + nCuts0, * pCut1Lim = pCuts1 + nCuts1;
    int i, nCutsUse, nCutsR = 0;
    assert( !Gia_ObjIsBuf(pObj) );
    for ( i = 0; i < nCutNum; i++ )
        pCutsR[i] = pCuts + i;
    if ( iSibl )
    {
        Scm_Cut_t pCuts2[NF_CUT_MAX];
        Gia_Obj_t * pObjE = Gia_ObjSiblObj(p->pGia, iObj);
        int fCompE = Gia_ObjPhase(pObj) ^ Gia_ObjPhase(pObjE);
        int nCuts2 = Scm_ManPrepareCuts(pCuts2, p, iSibl, 0);
        Scm_Cut_t * pCut2, * pCut2Lim = pCuts2 + nCuts2;
        for ( pCut2 = pCuts2; pCut2 < pCut2Lim; pCut2++ )
        {
            *pCutsR[nCutsR] = *pCut2;
            pCutsR[nCutsR]->iFunc = Abc_LitNotCond( pCutsR[nCutsR]->iFunc, fCompE );
            Scm_CutParams( p, pCutsR[nCutsR], dFlowRefs );
            nCutsR = Scm_SetAddCutStructure( p, pCutsR, nCutsR, nCutNum );
        }
    }
    if ( Gia_ObjIsMuxId(p->pGia, iObj) )
    {
        Scm_Cut_t pCuts2[NF_CUT_MAX];
        int nCuts2  = Scm_ManPrepareCuts(pCuts2, p, Gia_ObjFaninId2(p->pGia, iObj), 1);
        int fComp2  = Gia_ObjFaninC2(p->pGia, pObj);
        Scm_Cut_t * pCut2, * pCut2Lim = pCuts2 + nCuts2;
        p->CutCount[0] += nCuts0 * nCuts1 * nCuts2;
        for ( pCut0 = pCuts0; pCut0 < pCut0Lim; pCut0++ )
        for ( pCut1 = pCuts1; pCut1 < pCut1Lim; pCut1++ )
        for ( pCut2 = pCuts2; pCut2 < pCut2Lim; pCut2++ )
        {
            if ( Scm_CutCountBits(pCut0->Sign | pCut1->Sign | pCut2->Sign) > nLutSize )
                continue;
            p->CutCount[1]++;
            if ( !Scm_CutMergeOrderMux(pCut0, pCut1, pCut2, pCutsR[nCutsR], nLutSize) )
                continue;
            if ( Scm_SetLastCutIsContained(pCutsR, nCutsR) )
                continue;
            p->CutCount[2]++;
            if ( Scm_CutComputeTruthMux6(p, pCut0, pCut1, pCut2, fComp0, fComp1, fComp2, pCutsR[nCutsR]) )
                pCutsR[nCutsR]->Sign = Scm_CutGetSign(pCutsR[nCutsR]->pLeaves, pCutsR[nCutsR]->nLeaves);
            Scm_CutParams( p, pCutsR[nCutsR], dFlowRefs );
            nCutsR = Scm_SetAddCutStructure( p, pCutsR, nCutsR, nCutNum );
        }
    }
    else
    {
        int fIsXor = Gia_ObjIsXor(pObj);
        p->CutCount[0] += nCuts0 * nCuts1;
        for ( pCut0 = pCuts0; pCut0 < pCut0Lim; pCut0++ )
        for ( pCut1 = pCuts1; pCut1 < pCut1Lim; pCut1++ )
        {
            if ( (int)(pCut0->nLeaves + pCut1->nLeaves) > nLutSize && Scm_CutCountBits(pCut0->Sign | pCut1->Sign) > nLutSize )
                continue;
            p->CutCount[1]++;
            if ( !Scm_CutMergeOrder(pCut0, pCut1, pCutsR[nCutsR], nLutSize) )
                continue;
            if ( Scm_SetLastCutIsContained(pCutsR, nCutsR) )
                continue;
            p->CutCount[2]++;
            if ( Scm_CutComputeTruth6(p, pCut0, pCut1, fComp0, fComp1, pCutsR[nCutsR], fIsXor) )
                pCutsR[nCutsR]->Sign = Scm_CutGetSign(pCutsR[nCutsR]->pLeaves, pCutsR[nCutsR]->nLeaves);
            Scm_CutParams( p, pCutsR[nCutsR], dFlowRefs );
            nCutsR = Scm_SetAddCutStructure( p, pCutsR, nCutsR, nCutNum );
        }
    }
    // debug printout

    // verify
    assert( nCutsR > 0 && nCutsR < nCutNum );
    // store the cutset
    Scm_ObjSetCutFlow( p, iObj, pCutsR[0]->Flow );
    Scm_ObjSetCutDelay( p, iObj, pCutsR[0]->Delay );

        for ( i = 1; i < nCutsR; i++ )
            if ( pCutsR[i]->Useless == pCutsR[0]->Useless )
                Scm_ObjSetCutDelay(p, iObj, Abc_MinInt(Scm_ObjCutDelay(p, iObj), pCutsR[i]->Delay));
    *Vec_IntEntryP(&p->vCutSets, iObj) = Scm_ManSaveCuts(p, pCutsR, nCutsR, 0);
    p->CutCount[3] += nCutsR;
    nCutsUse = Scm_ManCountUseful(pCutsR, nCutsR);
    p->CutCount[4] += nCutsUse;
    p->nCutUseAll  += nCutsUse == nCutsR;
    p->CutCount[5] += Scm_ManCountMatches(p, pCutsR, nCutsR);
}
static void Scm_ManComputeCuts( Scm_Man_t * p )
{
    Gia_Obj_t * pObj; int i, iFanin, arrTime;
    float CutFlow = 0, CutFlowAve = 0; int fFirstCi = 0, nCutFlow = 0;
    if ( p->pManTim )
        Tim_ManIncrementTravId( p->pManTim );
    Gia_ManForEachObjWithBoxes( p->pGia, pObj, i )
        if ( Gia_ObjIsBuf(pObj) )
        {
            iFanin = Gia_ObjFaninId0(pObj, i);
            Scm_ObjSetCutFlow( p, i,  Scm_ObjCutFlow(p, iFanin) );
            Scm_ObjSetCutDelay( p, i, Scm_ObjCutDelay(p, iFanin) );
        }
        else if ( Gia_ObjIsAnd(pObj) )
            Scm_ObjMergeOrder( p, i );
        else if ( Gia_ObjIsCi(pObj) )
        {
            if ( fFirstCi ) {
                CutFlowAve = CutFlow / nCutFlow;
                CutFlow  = 0;
                nCutFlow = 0;
                fFirstCi = 0;
            }
            arrTime = Tim_ManGetCiArrival( p->pManTim, Gia_ObjCioId(pObj) );
            Scm_ObjSetCutFlow( p, i,  CutFlowAve ); // approximation!
            Scm_ObjSetCutDelay( p, i, arrTime );
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            iFanin   = Gia_ObjFaninId0(pObj, i);
            CutFlow += Scm_ObjCutFlow(p, iFanin);
            arrTime  = Scm_ObjCutDelay(p, iFanin);
            Tim_ManSetCoArrival( p->pManTim, Gia_ObjCioId(pObj), arrTime );
            nCutFlow++;
            fFirstCi = 1;
        }
}

static void Scm_ManPrintInit( Scm_Man_t * p )
{
    int nChoices;
    if ( !p->pPars->fVerbose )
        return;
    printf( "LutSize = %d  ", p->pPars->nLutSize );
    printf( "CutNum = %d  ",  p->pPars->nCutNum );
    printf( "Seeds = 2  Seed rounds = 4  " );
    printf( "Coarse = %d   ", 0 );
    printf( "Cells = %d  ",   p->nCells );
    printf( "Funcs = %d  ",   Vec_MemEntryNum(p->vTtMem) );
    printf( "Matches = %d  ", Vec_WecSizeSize(p->vTt2Match)/2 );
    printf( "And = %d  ",     Gia_ManAndNum(p->pGia) );
    nChoices = Gia_ManChoiceNum( p->pGia );
    if ( nChoices )
    printf( "Choices = %d  ", nChoices );
    printf( "\n" );
    printf( "Computing cuts...\r" );
    fflush( stdout );
}
static void Scm_ManPrintQuit( Scm_Man_t * p )
{
    float MemGia   = Gia_ManMemory(p->pGia) / (1<<20);
    float MemMan   =(1.0 * sizeof(Scm_Obj_t) + 8.0 * sizeof(int)) * Gia_ManObjNum(p->pGia) / (1<<20);
    float MemCuts  = 1.0 * sizeof(int) * (1 << 16) * Vec_PtrSize(&p->vPages) / (1<<20);
    float MemTt    = p->vTtMem ? Vec_MemMemory(p->vTtMem) / (1<<20) : 0;
    if ( p->CutCount[0] == 0 )
        p->CutCount[0] = 1;
    if ( !p->pPars->fVerbose )
        return;
    printf( "CutPair = %.0f  ",         p->CutCount[0] );
    printf( "Merge = %.0f (%.1f)  ",    p->CutCount[1], 1.0*p->CutCount[1]/Gia_ManAndNum(p->pGia) );
    printf( "Eval = %.0f (%.1f)  ",     p->CutCount[2], 1.0*p->CutCount[2]/Gia_ManAndNum(p->pGia) );
    printf( "Cut = %.0f (%.1f)  ",      p->CutCount[3], 1.0*p->CutCount[3]/Gia_ManAndNum(p->pGia) );
    printf( "Use = %.0f (%.1f)  ",      p->CutCount[4], 1.0*p->CutCount[4]/Gia_ManAndNum(p->pGia) );
    printf( "Mat = %.0f (%.1f)  ",      p->CutCount[5], 1.0*p->CutCount[5]/Gia_ManAndNum(p->pGia) );
//    printf( "Equ = %d (%.2f %%)  ",     p->nCutUseAll,  100.0*p->nCutUseAll /p->CutCount[0] );
    printf( "\n" );
    printf( "Gia = %.2f MB  ",          MemGia );
    printf( "Man = %.2f MB  ",          MemMan );
    printf( "Cut = %.2f MB   ",         MemCuts );
    printf( "TT = %.2f MB  ",           MemTt );
    printf( "Total = %.2f MB   ",       MemGia + MemMan + MemCuts + MemTt );
//    printf( "\n" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
    fflush( stdout );
}

static inline Scm_Mat_t * Scm_ObjMatchBest( Scm_Man_t * p, int i, int c )
{
    Scm_Mat_t * pD = Scm_ObjMatchD(p, i, c);
    Scm_Mat_t * pA = Scm_ObjMatchA(p, i, c);
    assert( pD->fBest != pA->fBest );
    if ( pA->fBest )
        return pA;
    if ( pD->fBest )
        return pD;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Area recovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Scm_MatchDeref_rec( Scm_Man_t * p, int i, int c, Scm_Mat_t * pM )
{
    word Area = 0;
    int k, iVar, fCompl, * pCut;
    assert( pM->fBest );
    if ( pM->fCompl )
    {
        assert( Scm_ObjMapRefNum(p, i, !c) > 0 );
        if ( !Scm_ObjMapRefDec(p, i, !c) )
            Area += Scm_MatchDeref_rec( p, i, !c, Scm_ObjMatchD(p, i, !c) );
        return Area + p->InvAreaW;
    }
    if ( Scm_ObjCutSetId(p, i) == 0 )
        return 0;
    pCut = Scm_CutFromHandle( Scm_ObjCutSet(p, i), pM->CutH );
    Scm_CutForEachVarCompl( pCut, pM->Cfg, iVar, fCompl, k )
    {
        assert( Scm_ObjMapRefNum(p, iVar, fCompl) > 0 );
        if ( !Scm_ObjMapRefDec(p, iVar, fCompl) )
            Area += Scm_MatchDeref_rec( p, iVar, fCompl, Scm_ObjMatchD(p, iVar, fCompl) );
    }
    return Area + Scm_ManCell(p, pM->Gate)->AreaW;
}
static word Scm_MatchRef_rec( Scm_Man_t * p, int i, int c, Scm_Mat_t * pM, int Required, Vec_Int_t * vBackup )
{
    word Area = 0;
    int ReqFanin;
    int k, iVar, fCompl, * pCut;
    assert( pM->fBest );
    /* SCL_INFINITY denotes an unbounded reference-only transaction.
       Paired/affine callers check their own floating-point timing bounds. */
    assert( Required == SCL_INFINITY || pM->D <= Required );
    if ( pM->fCompl )
    {
        ReqFanin = Required == SCL_INFINITY ? SCL_INFINITY : Required - p->InvDelayI;
        if ( vBackup )
            Vec_IntPush( vBackup, Abc_Var2Lit(i, !c) );
        assert( Scm_ObjMapRefNum(p, i, !c) >= 0 );
        if ( !Scm_ObjMapRefInc(p, i, !c) )
            Area += Scm_MatchRef_rec( p, i, !c, Scm_ObjMatchD(p, i, !c), ReqFanin, vBackup );
        return Area + p->InvAreaW;
    }
    if ( Scm_ObjCutSetId(p, i) == 0 )
        return 0;
    pCut = Scm_CutFromHandle( Scm_ObjCutSet(p, i), pM->CutH );
    Scm_CutForEachVarCompl( pCut, pM->Cfg, iVar, fCompl, k )
    {
        ReqFanin = Required == SCL_INFINITY ? SCL_INFINITY : Required - Scm_ManCell(p, pM->Gate)->iDelays[k];
        if ( vBackup )
            Vec_IntPush( vBackup, Abc_Var2Lit(iVar, fCompl) );
        assert( Scm_ObjMapRefNum(p, iVar, fCompl) >= 0 );
        if ( !Scm_ObjMapRefInc(p, iVar, fCompl) )
            Area += Scm_MatchRef_rec( p, iVar, fCompl, Scm_ObjMatchD(p, iVar, fCompl), ReqFanin, vBackup );
    }
    return Area + Scm_ManCell(p, pM->Gate)->AreaW;
}

/**Function*************************************************************

  Synopsis    [Dump matches.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/




/**Function*************************************************************

  Synopsis    [Deriving mapping.]

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
    vMapping = Vec_IntAlloc( 2*Gia_ManObjNum(p->pGia) + (int)p->pPars->Edge + (int)p->pPars->Area * 2 );
    Vec_IntFill( vMapping, 2*Gia_ManObjNum(p->pGia), 0 );
    // create CI inverters
    Gia_ManForEachCiId( p->pGia, Id, i )
    if ( Scm_ObjMapRefNum(p, Id, 1) )
        Vec_IntWriteEntry( vMapping, Abc_Var2Lit(Id, 1), -1 );
    // create internal nodes
    Gia_ManForEachAndId( p->pGia, i )
    {
        Gia_Obj_t * pObj = Gia_ManObj(p->pGia, i);
        if ( Gia_ObjIsBuf(pObj) )
        {
            if ( Scm_ObjMapRefNum(p, i, 1) )
                Vec_IntWriteEntry( vMapping, Abc_Var2Lit(i, 1), -1 );
            Vec_IntWriteEntry( vMapping, Abc_Var2Lit(i, 0), -2 );
            continue;
        }
        for ( c = 0; c < 2; c++ )
        if ( Scm_ObjMapRefNum(p, i, c) )
        {
            pM = Scm_ObjMatchBest( p, i, c );
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
static void Scm_ManUpdateStats( Scm_Man_t * p )
{
    Scm_Mat_t * pM;
    Gia_Obj_t * pObj;
    Mio_Cell2_t * pCell;
    int i, c, Id, * pCut;
    p->pPars->MapAreaF = 0; p->nInvs = 0;
    p->pPars->Area = p->pPars->Edge = 0;
    Gia_ManForEachAndReverse( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            if ( Scm_ObjMapRefNum(p, i, 1) )
            {
                p->pPars->MapAreaF += p->InvAreaF;
                p->pPars->Edge++;
                p->pPars->Area++;
                p->nInvs++;
            }
            continue;
        }
        for ( c = 0; c < 2; c++ )
        if ( Scm_ObjMapRefNum(p, i, c) )
        {
            pM = Scm_ObjMatchBest( p, i, c );
            if ( pM->fCompl )
            {
                p->pPars->MapAreaF += p->InvAreaF;
                p->pPars->Edge++;
                p->pPars->Area++;
                p->nInvs++;
                continue;
            }
            pCut = Scm_CutFromHandle( Scm_ObjCutSet(p, i), pM->CutH );
            pCell = Scm_ManCell( p, pM->Gate );
            assert( Scm_CutSize(pCut) == (int)pCell->nFanins );
            p->pPars->MapAreaF += pCell->AreaF;
            p->pPars->Edge += Scm_CutSize(pCut);
            p->pPars->Area++;
        }
    }
    Gia_ManForEachCiId( p->pGia, Id, i )
        if ( Scm_ObjMapRefNum(p, Id, 1) )
        {
            p->pPars->MapAreaF += p->InvAreaF;
            p->pPars->Edge++;
            p->pPars->Area++;
            p->nInvs++;
        }
}

/**Function*************************************************************

  Synopsis    [Extract window.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

/*
    int              nInputs;   // the number of inputs
    int              nObjs;     // number of all objects
    Vec_Int_t *      vRoots;    // output drivers to be mapped (root -> obj lit)
    Vec_Wec_t *      vCuts;     // cuts (cut -> obj lit + fanin lits)
    Vec_Wec_t *      vObjCuts;  // cuts (obj lit -> obj lit + cut lits)
    Vec_Int_t *      vSolCuts;  // current solution (index -> cut)
    Vec_Int_t *      vCutGates; // gates (cut -> gate)
*/

/**Function*************************************************************

  Synopsis    [Technology mappping.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
#define NF_PAPER_LOAD_INF  1.0e20f
#define NF_PAPER_EPS       1.0e-6f

typedef struct Scm_AffElaCtx_t_ Scm_AffElaCtx_t;
static float Scm_ManAffTail( Scm_Man_t * p, int iLit, float Slew,
    Scm_AffFan_t * pExtra );
static int Scm_ManAffElaEvalLit( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iObj, int c );

typedef struct Scm_AffChoice_t_ Scm_AffChoice_t;
struct Scm_AffChoice_t_
{
    Scm_AffMatch_t * pMatch;
    float           Arrival;
    float           Slew;
    float           Tail;
    float           Score;
    float           Flow;
};

typedef struct Scm_AffConfig_t_ Scm_AffConfig_t;
struct Scm_AffConfig_t_
{
    int             fValid;
    int             iInvOut;       // -1: requested rails direct; 0/1: this rail is inverted
    Scm_AffChoice_t  Direct[2];
    float           InvArrival;
    float           InvSlew;
    float           InvTail;
    float           Score;
    float           Area;
};

typedef struct Scm_AffElaCand_t_ Scm_AffElaCand_t;
struct Scm_AffElaCand_t_
{
    Scm_Mat_t M;
    word Area;
};

typedef struct Scm_AffElaFanSet_t_ Scm_AffElaFanSet_t;
struct Scm_AffElaFanSet_t_
{
    int * pRoots;
    unsigned char * pPins;
    int nRoots;
    int nAlloc;
};

typedef struct Cf_Node_ Cf_Node;
typedef struct Scm_AffElaCtx_t_ Scm_AffElaCtx_t;
struct Scm_AffElaCtx_t_
{
    Scm_AffElaFanSet_t * pFans;
    Scm_AffFanSet_t * pTailLines;
    Scm_RfFanSet_t * pTailLinesRf;
    double * pLiveLoads;
    double * pLiveLoadsRf;
    float * pBufferAreas; // SCMap virtual-tree area in AreaW units
    word BufferFreed;
    float * pTrialArr;
    float * pTrialSlew;
    float * pTailAtBaseSlew;
    Scm_RfPair_t * pTrialArrRf;
    Scm_RfPair_t * pTrialSlewRf;
    Scm_RfPair_t * pTailAtBaseSlewRf;
    unsigned * pTouched;
    unsigned * pComputed;
    unsigned * pConeSeen;
    unsigned * pTailSeen;
    unsigned char * pTailValid;
    unsigned char * pIsPo;
    unsigned Epoch;
    unsigned ConeEpoch;
    unsigned TailEpoch;
    unsigned SeedEpoch;      // stamps for linear-time seed deduplication
    int * pEdgePos;          // position of edge (root literal, pin) in its child's fanout list
    unsigned * pSeedStamp;
    Vec_Int_t * vSeedSort;
    Vec_Int_t * vOldSeeds;
    Vec_Int_t * vTrialSeeds;
    Vec_Int_t * vAffected;
    word * pQueueBits[6];
    int nQueueLevels;
    Vec_Int_t * vConeStack;
    Vec_Int_t * vBoundary;
    Vec_Flt_t * vBoundaryPriorities;
    Vec_Int_t * vTailStack;
    Vec_Int_t * vTailWork;
    Vec_Int_t * vTailSort;
    Vec_Int_t * pCollectSeeds;
    int nLits;
    int fRiseFall;
    Cf_Node **pArcCache; // private keyed cell/load cache
    int fLiveTail; // live boundary feasibility state
    void *pScorePrune; // private, separately owned backward score bound
    int fScorePrune, ScorePruneCutoff, nScorePruned, fScoreRejected;
    int fFullPropagation; // propagate changed timing to affected outputs
    Vec_Int_t *vScoreOutputs; // optional changed-PO list for incremental objective
    int fError;
};

/* Choice cuts have already been copied to their representative.  A sibling
   with no retained-cut or output users cannot be a physical mapping root.
   Exclude its candidate population, not its cuts or internal nodes.  Keep
   siblings that are independently used, including through a buffer alias.
   The same conversion is used for all internal arrival metadata. */

static inline int Scm_PaperMatSame( Scm_Mat_t * pA, Scm_Mat_t * pB )
{
    return pA->Gate == pB->Gate && pA->CutH == pB->CutH &&
        pA->fCompl == pB->fCompl && Scm_Cfg2Int(pA->Cfg) == Scm_Cfg2Int(pB->Cfg);
}

static void Scm_AffPwlPush( Scm_AffPwl_t * pPwl,
    float Lo, float Hi, float Offset, float Slope )
{
    Scm_AffSeg_t * pLast, * pSeg;
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
        pPwl->pSegs = ABC_REALLOC( Scm_AffSeg_t, pPwl->pSegs, pPwl->nAlloc );
    }
    pSeg = pPwl->pSegs + pPwl->nSegs++;
    pSeg->Lo = Lo;
    pSeg->Hi = Hi;
    pSeg->Offset = Offset;
    pSeg->Slope = Slope;
}

static float Scm_AffPwlEval( Scm_AffPwl_t * pPwl, float Load )
{
    int Lo = 0, Hi = pPwl->nSegs, Mid;
    Scm_AffSeg_t * pSeg;
    if ( pPwl->pShared )
    {
        Scm_AffShared_t * q = pPwl->pShared;
        float Best = -FLT_MAX;
        int k;
        Load = Abc_MaxFloat(0.0f, Load);
        for ( k = 0; k < q->nPins; k++ )
        {
            Scm_AffPwl_t * pin = q->pPins + k;
            int lo = 0, hi = pin->nSegs;
            Scm_AffSeg_t * seg;
            while ( lo + 1 < hi )
            {
                int mid = (lo + hi) >> 1;
                if ( Load >= pin->pSegs[mid].Lo ) lo = mid;
                else hi = mid;
            }
            seg = pin->pSegs + lo;
            /* Preserve the materialized envelope's arithmetic order. */
            Best = Abc_MaxFloat(Best,
                (q->Offsets[k] + seg->Offset) + seg->Slope * Load);
        }
        return Best;
    }
    assert( pPwl->nSegs > 0 );
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

static int Scm_AffPwlCheck( Scm_AffPwl_t * pPwl )
{
    float Previous = 0.0f;
    int i;
    if ( pPwl->pShared )
    {
        Scm_AffShared_t * q = pPwl->pShared;
        if ( q->nPins < 1 || q->nPins > NF_LEAF_MAX || !q->pPins ) return 0;
        for ( i = 0; i < q->nPins; i++ )
            if ( !isfinite(q->Offsets[i]) ) return 0;
        return 1;
    }
    for ( i = 0; i < pPwl->nSegs; i++ )
    {
        Scm_AffSeg_t * pSeg = pPwl->pSegs + i;
        float Tol = 1.0e-4f * Abc_MaxFloat(1.0f, fabsf(Previous));
        if ( !isfinite(pSeg->Lo) || !isfinite(pSeg->Hi) ||
             !isfinite(pSeg->Offset) || !isfinite(pSeg->Slope) ||
             pSeg->Hi <= pSeg->Lo || fabsf(pSeg->Lo - Previous) > Tol )
            return 0;
        Previous = pSeg->Hi;
    }
    return pPwl->nSegs > 0 && Previous >= 0.5f * NF_PAPER_LOAD_INF;
}

static float Scm_ManAffRawCellSlew( Scm_Man_t * p, Mio_Cell2_t * pCell, float Load )
{
    Scm_LinSlewPwl_t * pPwl;
    int Lo = 0, Hi, Mid;
    pPwl = p->pLinearSlewPwls + pCell->Id;
    assert( pPwl->nSegs > 0 );
    Load = Abc_MaxFloat(0.0f, Load);
    Hi = pPwl->nSegs;
    while ( Lo + 1 < Hi )
    {
        Mid = (Lo + Hi) >> 1;
        if ( Load >= pPwl->Start[Mid] ) Lo = Mid;
        else Hi = Mid;
    }
    return Abc_MaxFloat(0.0f, pPwl->Offset[Lo] + pPwl->Slope[Lo] * Load);
}

static void Scm_ManEnsureEnvBuild( Scm_Man_t * p, Mio_Cell2_t * pCell );
static inline void Scm_ManEnsureEnv( Scm_Man_t * p, Mio_Cell2_t * pCell )
{
    if ( p->pEnvState && !p->pEnvState[pCell->Id] ) Scm_ManEnsureEnvBuild( p, pCell );
}

/* With the output load fixed, the composed tree remains affine in input
   slew.  Forward arrivals and reverse constraints use this same helper. */
static Scm_LinArc_t * Scm_ManAffArcAtLoad( Scm_Man_t * p,
    Mio_Cell2_t * pCell, int iPin, float Load, Scm_LinArc_t * pTemp )
{
    Scm_LinArc_t * pArc = Scm_ManLinearArc(p, pCell, iPin);
    if ( !p->pBufferDelays || !pArc || !pArc->fValid ) return pArc;
    Scm_ManEnsureEnv(p, pCell);
    *pTemp = *pArc;
    pTemp->Delay0 = Scm_AffPwlEval(p->pBufferDelays +
        pCell->Id * NF_LEAF_MAX + iPin, Load);
    pTemp->DelayLoad = 0.0f;
    return pTemp;
}

/* Both output transitions use the same virtual size/tree selected at the
   library knot. Its load-only output slew is shared across all input pins;
   evaluate it at the same load as the delay response. */
static Scm_LinArc_t * Scm_ManAffArcAtLoadRf(Scm_Man_t *p,Mio_Cell2_t *c,int pin,Scm_RfPair_t load,Scm_LinArc_t *a)
{
    Scm_LinArc_t *base=Scm_ManLinearArc(p,c,pin);
    if(!p->pBufferRfDelays) return base;
    Scm_ManEnsureEnv(p,c);
    *a=*base;

    for(int t=0;t<2;t++) {
        a->RfDelay0[t]=Scm_AffPwlEval(p->pBufferRfDelays+2*(c->Id*NF_LEAF_MAX+pin)+t,load.Value[t]);
        a->RfDelayLoad[t]=0;
        a->RfSlew0[t]=Scm_AffPwlEval(p->pBufferRfSlews+2*c->Id+t,load.Value[t]);
        a->RfSlewLoad[t]=0;
    }
    return a;
}

static float Scm_ManAffCellSlew( Scm_Man_t * p, Scm_AffMatch_t * pM, float Load )
{
    Mio_Cell2_t * pCell;
    if ( pM->fSource ) return 0.0f;
    pCell = Scm_ManCell(p, pM->M.Gate);
    if ( p->pBufferSlews )
    {
        Scm_ManEnsureEnv(p, pCell);
        return Abc_MaxFloat(0.0f, Scm_AffPwlEval(p->pBufferSlews + pCell->Id, Load));
    }
    return Scm_ManAffRawCellSlew(p, pCell, Load);
}

typedef struct Scm_BufferType_t_ {
    Scm_LinArc_t Arc;
    float Cap, Area;
} Scm_BufferType_t;

/* SCMap library preprocessing. Fit each physical logic-cell size on
   its own NLDM grid, then choose a shared size/tree for all arcs at each
   load sample. Preserve separate fall/rise responses of that same choice;
   do not independently select a size/tree for each transition. This models
   downstream sizing opportunity, not circuit STA.
   Family-average input caps remain an approximation: a chosen size is
   not fed back into sink caps. Sparse geometric knots define continuous
   monotone PWLs; the last secant is extrapolated. Virtual buffer trees
   charge delay and area but do not model ABC's sink grouping. Gain 9 is
   ABC buffer's default gain 3 squared for noninverting buffers. */
typedef struct Scm_SizedType_t_ {
    Scm_LinArc_t Arcs[NF_LEAF_MAX];
    float ExtraArea;
} Scm_SizedType_t;

static float Scm_SizedSlew( Scm_SizedType_t * t, int nPins, float Load )
{
    float Slew = 0.0f;
    int k;
    for ( k = 0; k < nPins; k++ )
        Slew = Abc_MaxFloat(Slew, t->Arcs[k].Slew0 + t->Arcs[k].SlewLoad * Load);
    return Slew;
}

static void Scm_SizedConsider( Scm_Man_t * p, Mio_Cell2_t * c, Scm_SizedType_t * t,
    float Root, float Extra, float Slew, float Area,
    float * Best, float * Delays, float * BestSlew, float * BestArea,
    Scm_BufferType_t *buf,int depth,float RfDelays[2][NF_LEAF_MAX],float RfSlew[2] )
{
    float Score = -FLT_MAX;
    int k;
    /* Retain the family input-slew coefficient consistently in both
       selection and evaluation. Only the load/intrinsic part and output
       slew use the selected physical size; no hidden slew state is added. */
    for ( k = 0; k < (int)c->nFanins; k++ )
        Score = Abc_MaxFloat(Score, t->Arcs[k].Delay0 + t->Arcs[k].DelayLoad * Root +
            Extra + Scm_ManLinearArc(p, c, k)->DelaySlew * p->BufferRefSlew);

    Area += t->ExtraArea;
    if ( Score > *Best || (Score == *Best && Area >= *BestArea) ) return;
    *Best = Score;
    *BestSlew = Slew;
    *BestArea = Area;
    for ( k = 0; k < (int)c->nFanins; k++ )
        Delays[k] = t->Arcs[k].Delay0 + t->Arcs[k].DelayLoad * Root + Extra;
    for(int u=0;u<2;u++) {
        float sr=0, extra=0;
        for(k=0;k<(int)c->nFanins;k++)
            sr=Abc_MaxFloat(sr,t->Arcs[k].RfSlew0[u]+t->Arcs[k].RfSlewLoad[u]*Root);
        RfSlew[u]=sr;
        if(buf) {
            float sb=Abc_MaxFloat(0,buf->Arc.RfSlew0[u]+buf->Arc.RfSlewLoad[u]*9*buf->Cap);
            float db=buf->Arc.RfDelay0[u]+buf->Arc.RfDelayLoad[u]*9*buf->Cap;
            extra=db+buf->Arc.RfDelaySlew[u]*sr+(depth-1)*(db+buf->Arc.RfDelaySlew[u]*sb);
            RfSlew[u]=sb;
        }
        for(k=0;k<(int)c->nFanins;k++)
            RfDelays[u][k]=t->Arcs[k].RfDelay0[u]+t->Arcs[k].RfDelayLoad[u]*Root+extra;
    }
}

static int Scm_ManSizedCellPwls( Scm_Man_t * p, Mio_Cell2_t * c,
    Scm_BufferType_t * Buffers, int nBuffers, float Cap )
{
    SC_Cell * rep = Scm_ManSclCell(p, c), * cell;
    Scm_SizedType_t * Types;
    float PrevLoad = 0, PrevDelay[NF_LEAF_MAX] = {0}, PrevSlew = 0, PrevArea = 0;
    float PrevRfD[2][NF_LEAF_MAX]={{0}},PrevRfS[2]={0};
    int nTypes = 0, i, j, k, t, b;
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
            Scm_LinArc_t * a = type->Arcs + k;
            if ( !Scm_ManFitOwnGridCached(p, cell, k, a) ) { ABC_FREE(Types); return 0; }
            {
                a->Delay0 = 0.75f * a->Delay0 + 0.25f * p->BufferUnitDelay;
                a->DelayLoad *= 0.75f;
                a->DelaySlew *= 0.75f;
                for(int u=0;u<2;u++) {
                    a->RfDelay0[u]=.75f*a->RfDelay0[u]+.25f*p->BufferUnitDelay;
                    a->RfDelayLoad[u]*=.75f; a->RfDelaySlew[u]*=.75f;
                }
            }
        }
        type->ExtraArea = c->AreaW * Abc_MaxFloat(0, cell->area / rep->area - 1.0f);
        nTypes++;
    }
    if ( !nTypes ) { ABC_FREE(Types); return 0; }
    for ( j = 0; j < 15; j++ )
    {
        float Load = j ? Cap * powf(4.0f, (float)j - 2.0f) : 0.0f;
        float Best = FLT_MAX, Delays[NF_LEAF_MAX] = {0}, Slew = 0, Area = FLT_MAX;
        float RfD[2][NF_LEAF_MAX]={{0}},RfS[2]={0};
        float Hi = j == 14 ? NF_PAPER_LOAD_INF : Load;
        for ( t = 0; t < nTypes; t++ )
        {
            Scm_SizedType_t * type = Types + t;
            Scm_SizedConsider(p, c, type, Load, 0, Scm_SizedSlew(type, c->nFanins, Load),
                0, &Best, Delays, &Slew, &Area, NULL,0,RfD,RfS);
            for ( b = 0; b < nBuffers; b++ )
            {
                Scm_BufferType_t * buf = Buffers + b;
                float Scale = 1.0f, Count = 0, Root = Load;
                float BufSlew = Abc_MaxFloat(0, buf->Arc.Slew0 + buf->Arc.SlewLoad * 9 * buf->Cap);
                float BufDelay = buf->Arc.Delay0 + buf->Arc.DelayLoad * 9 * buf->Cap;
                int Depth;
                for ( Depth = 1; Depth <= 16 && Root > buf->Cap; Depth++ )
                {
                    float Extra;
                    Scale *= 9;
                    Root = Abc_MaxFloat(buf->Cap, Load / Scale);
                    Count += ceilf(Load / (Scale * buf->Cap));
                    Extra = BufDelay + buf->Arc.DelaySlew * Scm_SizedSlew(type, c->nFanins, Root) +
                        (Depth - 1) * (BufDelay + buf->Arc.DelaySlew * BufSlew);
                    Scm_SizedConsider(p, c, type, Root, Extra, BufSlew, Count * buf->Area,
                        &Best, Delays, &Slew, &Area,buf,Depth,RfD,RfS);
                }
            }
        }
        for ( k = 0; k < (int)c->nFanins; k++ )
        {
            Delays[k] = Abc_MaxFloat(Delays[k], PrevDelay[k]);
            if ( j )
            {
                float Slope = (Delays[k] - PrevDelay[k]) / (Load - PrevLoad);
                Scm_AffPwlPush(p->pBufferDelays + c->Id * NF_LEAF_MAX + k,
                    PrevLoad, Hi, PrevDelay[k] - Slope * PrevLoad, Slope);
            }
            PrevDelay[k] = Delays[k];
        }
        Slew = Abc_MaxFloat(Slew, PrevSlew);
        Area = Abc_MaxFloat(Area, PrevArea);
        if ( j )
        {
            float Slope = (Slew - PrevSlew) / (Load - PrevLoad);
            Scm_AffPwlPush(p->pBufferSlews + c->Id, PrevLoad, Hi,
                PrevSlew - Slope * PrevLoad, Slope);
            Slope = (Area - PrevArea) / (Load - PrevLoad);
            Scm_AffPwlPush(p->pBufferCosts + c->Id, PrevLoad, Hi,
                PrevArea - Slope * PrevLoad, Slope);
        }
        if(p->pBufferRfDelays) for(int u=0;u<2;u++) {
            for(k=0;k<(int)c->nFanins;k++) {
                RfD[u][k]=Abc_MaxFloat(RfD[u][k],PrevRfD[u][k]);
                if(j) {
                    float slope=(RfD[u][k]-PrevRfD[u][k])/(Load-PrevLoad);
                    Scm_AffPwlPush(p->pBufferRfDelays+2*(c->Id*NF_LEAF_MAX+k)+u,PrevLoad,Hi,PrevRfD[u][k]-slope*PrevLoad,slope);
                }
                PrevRfD[u][k]=RfD[u][k];
            }
            RfS[u]=Abc_MaxFloat(RfS[u],PrevRfS[u]);
            if(j) {
                float slope=(RfS[u]-PrevRfS[u])/(Load-PrevLoad);
                Scm_AffPwlPush(p->pBufferRfSlews+2*c->Id+u,PrevLoad,Hi,PrevRfS[u]-slope*PrevLoad,slope);
            }
            PrevRfS[u]=RfS[u];
        }
        PrevLoad = Load; PrevSlew = Slew; PrevArea = Area;
    }
    ABC_FREE(Types);
    return 1;
}

static int Scm_ManAffBufferPwlsStart( Scm_Man_t * p )
{
    SC_Cell * pBuf = Scm_ManSclCell(p, p->pCells + 2);
    Scm_BufferType_t * Types;
    SC_Cell * pMember;
    float Cap;
    int i, k, nTypes = 0;
    if ( !pBuf ) return 0;
    Cap = Scm_ManCellPinCap(p, pBuf, 0);
    if ( Cap <= 0 ) return 0;
    Types = ABC_ALLOC(Scm_BufferType_t, SC_LibCellNum(p->pScl));
    SC_RingForEachCell(pBuf, pMember, i)
    {
        Scm_BufferType_t * b = Types + nTypes;
        if ( pMember->fSkip ) continue;
        memset(b, 0, sizeof(*b));
        if ( !Scm_ManFitOwnGridCached(p, pMember, 0, &b->Arc) ) continue;
        b->Cap = SC_CellPinCap(pMember, 0);
        b->Area = p->pCells[2].AreaW * (pMember->area / pBuf->area);
        if ( b->Cap <= 0 || b->Area <= 0 ) continue;
        b->Arc.Delay0 = .75f * b->Arc.Delay0 + .25f * p->BufferUnitDelay;
        b->Arc.DelayLoad *= .75f;
        b->Arc.DelaySlew *= .75f;
        for(int u=0;u<2;u++) {
            b->Arc.RfDelay0[u]=.75f*b->Arc.RfDelay0[u]+.25f*p->BufferUnitDelay;
            b->Arc.RfDelayLoad[u]*=.75f; b->Arc.RfDelaySlew[u]*=.75f;
        }
        nTypes++;
    }
    if ( !nTypes ) { ABC_FREE(Types); return 0; }
    {
        p->pBufferRfDelays=ABC_CALLOC(Scm_AffPwl_t,2*p->nCells*NF_LEAF_MAX);
        p->pBufferRfSlews=ABC_CALLOC(Scm_AffPwl_t,2*p->nCells);
    }
    p->pBufferDelays = ABC_CALLOC(Scm_AffPwl_t, p->nCells * NF_LEAF_MAX);
    p->pBufferSlews = ABC_CALLOC(Scm_AffPwl_t, p->nCells);
    p->pBufferCosts = ABC_CALLOC(Scm_AffPwl_t, p->nCells);
    /* Each cell's envelope depends only on library data and these buffer
       types; build it on first use (identical values, any order). */
    p->pEnvBufs = Types; p->nEnvBufs = nTypes; p->EnvCap = Cap;
    p->pEnvState = ABC_CALLOC(unsigned char, p->nCells);
    (void)k;
    return 1;
}

static void Scm_ManEnsureEnvBuild( Scm_Man_t * p, Mio_Cell2_t * pCell )
{
    int i = pCell->Id, k, fOk;
    if ( !pCell->nFanins ) { p->pEnvState[i] = 1; return; }
    fOk = Scm_ManSizedCellPwls(p, pCell, (Scm_BufferType_t *)p->pEnvBufs, p->nEnvBufs, p->EnvCap);
    for ( k = 0; fOk && k < (int)pCell->nFanins; k++ )
        fOk = Scm_AffPwlCheck(p->pBufferDelays + i * NF_LEAF_MAX + k);
    fOk = fOk && Scm_AffPwlCheck(p->pBufferSlews + i) && Scm_AffPwlCheck(p->pBufferCosts + i);
    p->pEnvState[i] = fOk ? 1 : 2;
    if ( !fOk ) p->fEnvError = 1;
}

/* A candidate is max_k(child_offset[k] + library_pin_curve[k](load)).
   Keep that exact expression instead of repeatedly materializing its PWL
   envelope.  The borrowed library curves outlive every candidate; copies
   own only their small offset block.  Old modes retain their original hull. */

static void Scm_ManAffHistAdd( Scm_Man_t * p, int iSrcLit, int iRootLit, float Cap )
{
    Scm_AffHistSet_t * pSet;
    if ( p->pAffHistCurrent == NULL || Cap == 0.0f )
        return;
    assert( iSrcLit >= 0 && iSrcLit < 2 * Gia_ManObjNum(p->pGia) );
    assert( iRootLit >= 0 && iRootLit < 2 * Gia_ManObjNum(p->pGia) );
    pSet = p->pAffHistCurrent + iSrcLit;
    if ( pSet->nEdges == pSet->nAlloc )
    {
        pSet->nAlloc = pSet->nAlloc ? 2 * pSet->nAlloc : 4;
        pSet->pEdges = ABC_REALLOC( Scm_AffHistEdge_t, pSet->pEdges,
            pSet->nAlloc );
    }
    pSet->pEdges[pSet->nEdges].RootLit = iRootLit;
    pSet->pEdges[pSet->nEdges++].Cap = Cap;
}

static void Scm_ManAffHistCopyAlias( Scm_Man_t * p, int iAliasLit, int iSrcLit )
{
    Scm_AffHistSet_t * pSet;
    int i;
    if ( p->pAffHistCurrent == NULL )
        return;
    assert( iAliasLit != iSrcLit );
    pSet = p->pAffHistCurrent + iAliasLit;
    for ( i = 0; i < pSet->nEdges; i++ )
        Scm_ManAffHistAdd(p, iSrcLit, pSet->pEdges[i].RootLit,
            pSet->pEdges[i].Cap);
}

/* Timing and area witnesses use identical child arrival/slew evaluations
   at the same conditioned load.  Share this work, keeping their selection
   rules and correlated child witnesses separate. */

static void Scm_AffFanPush( Scm_AffFanSet_t * pSet, Scm_AffFan_t Fan )
{
    if ( pSet->nFans == pSet->nAlloc )
    {
        pSet->nAlloc = pSet->nAlloc ? 2 * pSet->nAlloc : 4;
        pSet->pFans = ABC_REALLOC(Scm_AffFan_t, pSet->pFans, pSet->nAlloc);
    }
    pSet->pFans[pSet->nFans++] = Fan;
}

static void Scm_RfFanPush( Scm_RfFanSet_t * pSet, Scm_RfFan_t Fan )
{
    if ( pSet->nFans == pSet->nAlloc )
    {
        pSet->nAlloc = pSet->nAlloc ? 2 * pSet->nAlloc : 4;
        pSet->pFans = ABC_REALLOC(Scm_RfFan_t, pSet->pFans, pSet->nAlloc);
    }
    pSet->pFans[pSet->nFans++] = Fan;
}

static Scm_RfPair_t Scm_ManRfTailLinesEval( Scm_RfFanSet_t * pSet,
    Scm_RfPair_t Slew )
{
    Scm_RfPair_t Tail = {{-FLT_MAX, -FLT_MAX}};
    int i, iPol;
    for ( i = 0; i < pSet->nFans; i++ )
        for ( iPol = NF_RF_FALL; iPol <= NF_RF_RISE; iPol++ )
            if ( pSet->pFans[i].Valid[iPol] )
            {
                /* Preserve the separate product rounding of the original
                   affine branch; contracting this into an FMA can change
                   near-tied reverse choices on very deep networks. */
                float SlewDelay = pSet->pFans[i].SlewCoeff[iPol] * Slew.Value[iPol];
                Tail.Value[iPol] = Abc_MaxFloat(Tail.Value[iPol],
                    pSet->pFans[i].Constant[iPol] + SlewDelay);
            }
    return Tail;
}

static float Scm_ManAffTail( Scm_Man_t * p, int iLit, float Slew,
    Scm_AffFan_t * pExtra )
{
    Scm_AffFanSet_t * pSet = p->pAffFanouts + iLit;
    float Tail = -FLT_MAX;
    int i;
    for ( i = 0; i < pSet->nFans; i++ )
        Tail = Abc_MaxFloat(Tail,
            pSet->pFans[i].Constant + pSet->pFans[i].SlewCoeff * Slew);
    if ( pExtra )
        Tail = Abc_MaxFloat(Tail,
            pExtra->Constant + pExtra->SlewCoeff * Slew);
    return Tail;
}

static inline float Scm_ManRfPairMax( Scm_RfPair_t Pair )
{
    return Abc_MaxFloat(Pair.Value[NF_RF_FALL], Pair.Value[NF_RF_RISE]);
}

static Scm_RfPair_t Scm_ManRfLoad( Scm_Man_t * p, int iLit )
{
    Scm_RfPair_t Load;
    if ( p->pAllRfLoads ) return p->pAllRfLoads[iLit];
    Load.Value[0] = Load.Value[1] = Vec_FltEntry(&p->vPaperLiveLoads, iLit);
    return Load;
}

static Scm_RfPair_t Scm_ManRfPinCap( Scm_Man_t * p, Mio_Cell2_t * pCell, int k )
{
    SC_Cell * pSclCell = Scm_ManSclCell(p, pCell);
    SC_Pin * pPin = SC_CellPin(pSclCell, k);
    if ( p->pFamilyCapsRf ) return p->pFamilyCapsRf[pSclCell->Id * NF_LEAF_MAX + k];
    Scm_RfPair_t Cap = {{pPin->fall_cap, pPin->rise_cap}};
    return Cap;
}

static int Scm_ManCollectLoadsRf( Scm_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, c, k, t, iVar, fCompl;
    memset(p->pAllRfLoads, 0, sizeof(Scm_RfPair_t) * 2 * Gia_ManObjNum(p->pGia));
    Gia_ManForEachObjWithBoxes(p->pGia, pObj, i)
    {
        if ( !Gia_ObjIsAnd(pObj) && !Gia_ObjIsCi(pObj) ) continue;
        for ( c = 0; c < 2; c++ )
        if ( Scm_ObjMapRefNum(p, i, c) )
        {
            Scm_Mat_t * pM = Scm_ObjMatchBest(p, i, c);
            if ( ((Gia_ObjIsCi(pObj) || Gia_ObjIsBuf(pObj)) && c) ||
                 (Gia_ObjIsAndNotBuf(pObj) && pM->fCompl) )
            {
                Scm_RfPair_t Cap = Scm_ManRfPinCap(p, p->pCells + 3, 0);
                for ( t = 0; t < 2; t++ )
                    p->pAllRfLoads[Abc_Var2Lit(i, !c)].Value[t] += Cap.Value[t];
            }
            else if ( Gia_ObjIsAndNotBuf(pObj) && pM->CutH )
            {
                Mio_Cell2_t * pCell = Scm_ManCell(p, pM->Gate);
                int * pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, i), pM->CutH);
                Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
                {
                    Scm_RfPair_t Cap = Scm_ManRfPinCap(p, pCell, k);
                    for ( t = 0; t < 2; t++ )
                        p->pAllRfLoads[Abc_Var2Lit(iVar, fCompl)].Value[t] += Cap.Value[t];
                }
            }
        }
    }
    /* The with-boxes object iterator starts after CIs. */
    Gia_ManForEachCiIdWithBoxes(p->pGia, i, c)
        if ( Scm_ObjMapRefNum(p, i, 1) )
        {
            Scm_RfPair_t Cap = Scm_ManRfPinCap(p, p->pCells + 3, 0);
            for ( t = 0; t < 2; t++ )
                p->pAllRfLoads[Abc_Var2Lit(i, 0)].Value[t] += Cap.Value[t];
        }
    Gia_ManForEachObjReverseWithBoxes(p->pGia, pObj, i)
        if ( Gia_ObjIsBuf(pObj) && Scm_ObjMapRefNum(p, i, 0) )
            for ( t = 0; t < 2; t++ )
                p->pAllRfLoads[Gia_ObjFaninLit0p(p->pGia, pObj)].Value[t] +=
                    p->pAllRfLoads[Abc_Var2Lit(i, 0)].Value[t];
    return 1;
}

static inline float Scm_ManRfDelay( Scm_LinArc_t * pArc, int iOut,
    float Load, float InSlew )
{
    return pArc->RfDelay0[iOut] + pArc->RfDelayLoad[iOut] * Load +
        pArc->RfDelaySlew[iOut] * InSlew;
}

static inline float Scm_ManRfSlew( Scm_LinArc_t * pArc, int iOut,
    float Load )
{
    return Abc_MaxFloat(0.0f,
        pArc->RfSlew0[iOut] + pArc->RfSlewLoad[iOut] * Load);
}

static void Scm_ManRfArcAccumulate( Scm_LinArc_t * pArc, Scm_RfPair_t Load,
    Scm_RfPair_t ChildArrival, Scm_RfPair_t ChildSlew,
    Scm_RfPair_t * pArrival, Scm_RfPair_t * pSlew )
{
    int iOut;
    for ( iOut = NF_RF_FALL; iOut <= NF_RF_RISE; iOut++ )
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

static Scm_RfPair_t Scm_ManRfCellSlew( Scm_Man_t * p, Mio_Cell2_t * pCell,
    Scm_RfPair_t Load )
{
    Scm_RfPair_t Result = {{0.0f, 0.0f}};
    int i, iOut;
    if(p->pBufferRfSlews) {
        Scm_ManEnsureEnv(p,pCell);
        for(int t=0;t<2;t++) Result.Value[t]=Abc_MaxFloat(0,Scm_AffPwlEval(p->pBufferRfSlews+2*pCell->Id+t,Load.Value[t]));
        return Result;
    }
    for ( i = 0; i < (int)pCell->nFanins; i++ )
    {
        Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, pCell, i, Load, &Temp);
        if ( pArc == NULL || !pArc->fValid ) continue;
        for ( iOut = NF_RF_FALL; iOut <= NF_RF_RISE; iOut++ )
            Result.Value[iOut] = Abc_MaxFloat(Result.Value[iOut],
                Scm_ManRfSlew(pArc, iOut, Load.Value[iOut]));
    }
    return Result;
}

static int Scm_ManAffAuditTimingRf( Scm_Man_t * p )
{
    Gia_Obj_t * pObj;
    int nLits = 2 * Gia_ManObjNum(p->pGia), i, c, k, nBad = 0;
    Scm_RfPair_t * pArr = ABC_CALLOC(Scm_RfPair_t, nLits);
    Scm_RfPair_t * pSlew = ABC_CALLOC(Scm_RfPair_t, nLits);
    float ExactPo = 0.0f;
    assert(p->pAffExactRfArrs != NULL && p->pAffExactRfSlews != NULL);
    Gia_ManForEachCiIdWithBoxes(p->pGia, i, c)
        if ( Scm_ObjMapRefNum(p, i, 1) )
        {
            int iLit = Abc_Var2Lit(i, 1);
            Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, p->pCells + 3, 0, Scm_ManRfLoad(p, iLit), &Temp);
            Scm_RfPair_t Zero = {{0.0f, 0.0f}};
            pArr[iLit].Value[0] = pArr[iLit].Value[1] = -FLT_MAX;
            Scm_ManRfArcAccumulate(pArc,
                Scm_ManRfLoad(p, iLit), Zero, Zero,
                pArr + iLit, pSlew + iLit);
        }
    Gia_ManForEachObjWithBoxes(p->pGia, pObj, i)
    {
        if ( Gia_ObjIsCi(pObj) || Gia_ObjIsCo(pObj) ) continue;
        if ( Gia_ObjIsBuf(pObj) )
        {
            int iSrcLit = Gia_ObjFaninLit0p(p->pGia, pObj);
            int iPosLit = Abc_Var2Lit(i, 0);
            pArr[iPosLit] = pArr[iSrcLit];
            pSlew[iPosLit] = pSlew[iSrcLit];
            if ( Scm_ObjMapRefNum(p, i, 1) )
            {
                int iNegLit = Abc_Var2Lit(i, 1);
                Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, p->pCells + 3, 0, Scm_ManRfLoad(p, iNegLit), &Temp);
                pArr[iNegLit].Value[0] = pArr[iNegLit].Value[1] = -FLT_MAX;
                Scm_ManRfArcAccumulate(pArc,
                    Scm_ManRfLoad(p, iNegLit),
                    pArr[iPosLit], pSlew[iPosLit], pArr + iNegLit,
                    pSlew + iNegLit);
            }
            continue;
        }
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) )
            {
                int iLit = Abc_Var2Lit(i, c);
                Scm_Mat_t * pM = Scm_ObjMatchBest(p, i, c);
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
                    Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, pCell, k, Scm_ManRfLoad(p, iLit), &Temp);
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
                 Scm_ObjMatchBest(p, i, c)->fCompl )
            {
                int iLit = Abc_Var2Lit(i, c);
                int iSrcLit = Abc_Var2Lit(i, !c);
                Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, p->pCells + 3, 0, Scm_ManRfLoad(p, iLit), &Temp);
                pArr[iLit].Value[0] = pArr[iLit].Value[1] = -FLT_MAX;
                Scm_ManRfArcAccumulate(pArc,
                    Scm_ManRfLoad(p, iLit), pArr[iSrcLit],
                    pSlew[iSrcLit], pArr + iLit, pSlew + iLit);
            }
    }
    Gia_ManForEachCoWithBoxes(p->pGia, pObj, i)
        ExactPo = Abc_MaxFloat(ExactPo,
            Scm_ManRfPairMax(pArr[Gia_ObjFaninLit0p(p->pGia, pObj)]));
    for ( i = 0; i < nLits; i++ )
    {
        if ( !isfinite(pArr[i].Value[0]) || !isfinite(pArr[i].Value[1]) ||
             !isfinite(pSlew[i].Value[0]) || !isfinite(pSlew[i].Value[1]) )
            nBad++;
        p->pAffExactArrs[i] = Scm_ManRfPairMax(pArr[i]);
        p->pAffExactSlews[i] = Scm_ManRfPairMax(pSlew[i]);
    }
    memcpy(p->pAffExactRfArrs, pArr, sizeof(Scm_RfPair_t) * nLits);
    memcpy(p->pAffExactRfSlews, pSlew, sizeof(Scm_RfPair_t) * nLits);
    p->AffExactDelay = ExactPo;
    ABC_FREE(pArr);
    ABC_FREE(pSlew);
    return nBad == 0;
}

static int Scm_ManAffAuditTiming( Scm_Man_t * p )
{
    Gia_Obj_t * pObj;
    int nLits = 2 * Gia_ManObjNum(p->pGia), i, c, k, nBad = 0;
    float * pArr = ABC_CALLOC(float, nLits);
    float * pSlew = ABC_CALLOC(float, nLits);
    float ExactPo = 0.0f;
    Gia_ManForEachCiIdWithBoxes( p->pGia, i, c )
        if ( Scm_ObjMapRefNum(p, i, 1) )
        {
            Scm_AffMatch_t Inv;
            Scm_LinArc_t Temp, * pArc;
            float Load = Vec_FltEntry(&p->vPaperLiveLoads, Abc_Var2Lit(i, 1));
            pArc = Scm_ManAffArcAtLoad(p, p->pCells + 3, 0, Load, &Temp);
            memset(&Inv, 0, sizeof(Inv));
            Inv.M.Gate = p->pCells[3].Id;
            pArr[Abc_Var2Lit(i, 1)] = pArc->Delay0 + pArc->DelayLoad * Load;
            pSlew[Abc_Var2Lit(i, 1)] = Scm_ManAffCellSlew(p, &Inv, Load);
        }
    Gia_ManForEachObjWithBoxes( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) || Gia_ObjIsCo(pObj) )
            continue;
        if ( Gia_ObjIsBuf(pObj) )
        {
            int iSrcLit = Gia_ObjFaninLit0p(p->pGia, pObj);
            int iPosLit = Abc_Var2Lit(i, 0);
            pArr[iPosLit] = pArr[iSrcLit];
            pSlew[iPosLit] = pSlew[iSrcLit];
            if ( Scm_ObjMapRefNum(p, i, 1) )
            {
                Scm_AffMatch_t Inv;
                Scm_LinArc_t Temp, * pArc;
                float Load = Vec_FltEntry(&p->vPaperLiveLoads, Abc_Var2Lit(i, 1));
                pArc = Scm_ManAffArcAtLoad(p, p->pCells + 3, 0, Load, &Temp);
                memset(&Inv, 0, sizeof(Inv));
                Inv.M.Gate = p->pCells[3].Id;
                pArr[Abc_Var2Lit(i, 1)] = pArr[iPosLit] + pArc->Delay0 +
                    pArc->DelayLoad * Load + pArc->DelaySlew * pSlew[iPosLit];
                pSlew[Abc_Var2Lit(i, 1)] = Scm_ManAffCellSlew(p, &Inv, Load);
            }
            continue;
        }
        if ( !Gia_ObjIsAnd(pObj) )
            continue;
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) )
            {
                Scm_Mat_t * pM = Scm_ObjMatchBest(p, i, c);
                Mio_Cell2_t * pCell;
                int * pCut, iVar, fCompl;
                float Load, Arrival = -FLT_MAX;
                Scm_AffMatch_t Match;
                if ( pM->fCompl )
                    continue;
                pCell = Scm_ManCell(p, pM->Gate);
                Load = Vec_FltEntry(&p->vPaperLiveLoads, Abc_Var2Lit(i, c));
                memset(&Match, 0, sizeof(Match));
                Match.M = *pM;
                if ( pM->CutH == 0 || pCell->nFanins == 0 )
                {
                    pArr[Abc_Var2Lit(i, c)] = 0.0f;
                    pSlew[Abc_Var2Lit(i, c)] = 0.0f;
                    continue;
                }
                pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, i), pM->CutH);
                if ( Scm_CutSize(pCut) != (int)pCell->nFanins ||
                     !Scm_CfgIsCutPermutation(pM->Cfg, Scm_CutSize(pCut)) )
                {
                    nBad++;
                    continue;
                }
                Scm_CutForEachVarCompl( pCut, pM->Cfg, iVar, fCompl, k )
                {
                    Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoad(p, pCell, k, Load, &Temp);
                    int iChildLit = Abc_Var2Lit(iVar, fCompl);
                    float This;
                    if ( pArc == NULL || !pArc->fValid )
                    {
                        nBad++;
                        continue;
                    }
                    This = pArr[iChildLit] + pArc->Delay0 +
                        pArc->DelayLoad * Load + pArc->DelaySlew * pSlew[iChildLit];
                    Arrival = Abc_MaxFloat(Arrival, This);
                }
                pArr[Abc_Var2Lit(i, c)] = Arrival;
                pSlew[Abc_Var2Lit(i, c)] = Scm_ManAffCellSlew(p, &Match, Load);
            }
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) && Scm_ObjMatchBest(p, i, c)->fCompl )
            {
                Scm_AffMatch_t Inv;
                Scm_LinArc_t Temp, * pArc;
                float Load = Vec_FltEntry(&p->vPaperLiveLoads, Abc_Var2Lit(i, c));
                int iSrcLit = Abc_Var2Lit(i, !c);
                pArc = Scm_ManAffArcAtLoad(p, p->pCells + 3, 0, Load, &Temp);
                memset(&Inv, 0, sizeof(Inv));
                Inv.M.Gate = p->pCells[3].Id;
                pArr[Abc_Var2Lit(i, c)] = pArr[iSrcLit] + pArc->Delay0 +
                    pArc->DelayLoad * Load + pArc->DelaySlew * pSlew[iSrcLit];
                pSlew[Abc_Var2Lit(i, c)] = Scm_ManAffCellSlew(p, &Inv, Load);
            }
    }
    Gia_ManForEachCoWithBoxes( p->pGia, pObj, i )
        ExactPo = Abc_MaxFloat(ExactPo,
            pArr[Gia_ObjFaninLit0p(p->pGia, pObj)]);
    for ( i = 0; i < nLits; i++ )
        if ( !isfinite(pArr[i]) || !isfinite(pSlew[i]) )
            nBad++;

    {
        memcpy(p->pAffExactArrs, pArr, sizeof(float) * nLits);
        memcpy(p->pAffExactSlews, pSlew, sizeof(float) * nLits);
        p->AffExactDelay = ExactPo;
    }
    ABC_FREE(pArr);
    ABC_FREE(pSlew);
    return nBad == 0;
}

static int Scm_ManAffElaCollectLoads( Scm_Man_t * p, int fBuildHistory )
{
    Gia_Obj_t * pObj;
    int nLits = 2 * Gia_ManObjNum(p->pGia), i, c, iVar, fCompl, k;
    Vec_FltFill(&p->vPaperLiveLoads, nLits, 0.0f);
    if ( fBuildHistory && p->pAffHistCurrent )
        for ( i = 0; i < nLits; i++ )
            p->pAffHistCurrent[i].nEdges = 0;
    Gia_ManForEachAnd(p->pGia, pObj, i)
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            if ( Scm_ObjMapRefNum(p, i, 1) )
            {
                Vec_FltAddToEntry(&p->vPaperLiveLoads,
                    Abc_Var2Lit(i, 0), Scm_ManInvInputCap(p));
                if ( fBuildHistory )
                    Scm_ManAffHistAdd(p, Abc_Var2Lit(i, 0),
                        Abc_Var2Lit(i, 1), Scm_ManInvInputCap(p));
            }
            continue;
        }
        for ( c = 0; c < 2; c++ )
        if ( Scm_ObjMapRefNum(p, i, c) )
        {
            Scm_Mat_t * pM = Scm_ObjMatchBest(p, i, c);
            Mio_Cell2_t * pCell;
            SC_Cell * pSclCell;
            int * pCut;
            if ( pM->fCompl )
            {
                if ( !Scm_ObjMapRefNum(p, i, !c) ) return 0;
                Vec_FltAddToEntry(&p->vPaperLiveLoads,
                    Abc_Var2Lit(i, !c), Scm_ManInvInputCap(p));
                if ( fBuildHistory )
                    Scm_ManAffHistAdd(p, Abc_Var2Lit(i, !c),
                        Abc_Var2Lit(i, c), Scm_ManInvInputCap(p));
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
                Vec_FltAddToEntry(&p->vPaperLiveLoads,
                    Abc_Var2Lit(iVar, fCompl),
                    Scm_ManCellPinCap(p, pSclCell, k));
                if ( fBuildHistory )
                    Scm_ManAffHistAdd(p, Abc_Var2Lit(iVar, fCompl),
                        Abc_Var2Lit(i, c),
                        Scm_ManCellPinCap(p, pSclCell, k));
            }
        }
    }
    Gia_ManForEachCiIdWithBoxes(p->pGia, i, c)
        if ( Scm_ObjMapRefNum(p, i, 1) )
        {
            Vec_FltAddToEntry(&p->vPaperLiveLoads,
                Abc_Var2Lit(i, 0), Scm_ManInvInputCap(p));
            if ( fBuildHistory )
                Scm_ManAffHistAdd(p, Abc_Var2Lit(i, 0),
                    Abc_Var2Lit(i, 1), Scm_ManInvInputCap(p));
        }
    Gia_ManForEachObjReverseWithBoxes(p->pGia, pObj, i)
        if ( Gia_ObjIsBuf(pObj) && Scm_ObjMapRefNum(p, i, 0) )
        {
            if ( !Scm_ObjMapRefNum(p, Gia_ObjFaninId0(pObj, i),
                    Gia_ObjFaninC0(pObj)) ) return 0;
            Vec_FltAddToEntry(&p->vPaperLiveLoads,
                Gia_ObjFaninLit0p(p->pGia, pObj),
                Vec_FltEntry(&p->vPaperLiveLoads, Abc_Var2Lit(i, 0)));
            if ( fBuildHistory )
                Scm_ManAffHistCopyAlias(p, Abc_Var2Lit(i, 0),
                    Gia_ObjFaninLit0p(p->pGia, pObj));
        }
    return 1;
}

static int Scm_ManAffElaTimeCover( Scm_Man_t * p )
{
    if ( !Scm_ManAffElaCollectLoads(p, 0) ) return 0;
    if ( p->pAllRfLoads && !Scm_ManCollectLoadsRf(p) ) return 0;
    return (p->pPars->fUseRiseFallAll) ?
        Scm_ManAffAuditTimingRf(p) : Scm_ManAffAuditTiming(p);
}

static int Scm_ManAffElaRebuildTails( Scm_Man_t * p )
{
    Gia_Obj_t * pObj;
    Scm_AffFan_t PoFan = {0.0f, 0.0f};
    int nLits = 2 * Gia_ManObjNum(p->pGia), i, c, iVar, fCompl, k;
    for ( i = 0; i < nLits; i++ )
        p->pAffFanouts[i].nFans = 0, p->pAffTails[i] = 0.0f;
    Gia_ManForEachCoWithBoxes(p->pGia, pObj, i)
        Scm_AffFanPush(p->pAffFanouts + Gia_ObjFaninLit0p(p->pGia, pObj), PoFan);
    Gia_ManForEachObjReverseWithBoxes(p->pGia, pObj, i)
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            int iPos = Abc_Var2Lit(i, 0);
            if ( Scm_ObjMapRefNum(p, i, 1) )
            {
                Scm_LinArc_t Temp, * pArc;
                int iNeg = Abc_Var2Lit(i, 1);
                Scm_AffFan_t Fan;
                pArc = Scm_ManAffArcAtLoad(p, p->pCells + 3, 0, Vec_FltEntry(&p->vPaperLiveLoads, iNeg), &Temp);
                if ( pArc == NULL || !pArc->fValid ) return 0;
                Fan.Constant = pArc->Delay0 + pArc->DelayLoad *
                    Vec_FltEntry(&p->vPaperLiveLoads, iNeg) +
                    Scm_ManAffTail(p, iNeg, p->pAffExactSlews[iNeg], NULL);
                Fan.SlewCoeff = pArc->DelaySlew;
                Scm_AffFanPush(p->pAffFanouts + iPos, Fan);
            }
            if ( Scm_ObjMapRefNum(p, i, 0) )
            {
                int iSrc = Gia_ObjFaninLit0p(p->pGia, pObj);
                Scm_AffFanSet_t * pSet = p->pAffFanouts + iPos;
                for ( k = 0; k < pSet->nFans; k++ )
                    Scm_AffFanPush(p->pAffFanouts + iSrc, pSet->pFans[k]);
            }
            continue;
        }
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        for ( c = 0; c < 2; c++ )
        if ( Scm_ObjMapRefNum(p, i, c) && Scm_ObjMatchBest(p, i, c)->fCompl )
        {
            Scm_LinArc_t Temp, * pArc;
            int iLit = Abc_Var2Lit(i, c);
            Scm_AffFan_t Fan;
            pArc = Scm_ManAffArcAtLoad(p, p->pCells + 3, 0, Vec_FltEntry(&p->vPaperLiveLoads, iLit), &Temp);
            if ( pArc == NULL || !pArc->fValid ) return 0;
            Fan.Constant = pArc->Delay0 + pArc->DelayLoad *
                Vec_FltEntry(&p->vPaperLiveLoads, iLit) +
                Scm_ManAffTail(p, iLit, p->pAffExactSlews[iLit], NULL);
            Fan.SlewCoeff = pArc->DelaySlew;
            Scm_AffFanPush(p->pAffFanouts + Abc_Var2Lit(i, !c), Fan);
        }
        for ( c = 0; c < 2; c++ )
        if ( Scm_ObjMapRefNum(p, i, c) && !Scm_ObjMatchBest(p, i, c)->fCompl )
        {
            Scm_Mat_t * pM = Scm_ObjMatchBest(p, i, c);
            Mio_Cell2_t * pCell = Scm_ManCell(p, pM->Gate);
            SC_Cell * pSclCell = Scm_ManSclCell(p, pCell);
            int iLit = Abc_Var2Lit(i, c);
            int * pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, i), pM->CutH);
            float Tail = Scm_ManAffTail(p, iLit, p->pAffExactSlews[iLit], NULL);
            if ( (pCell->nFanins && pSclCell == NULL) || Tail == -FLT_MAX )
                return 0;
            p->pAffTails[iLit] = Tail;
            Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
            {
                Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoad(p, pCell, k, Vec_FltEntry(&p->vPaperLiveLoads, iLit), &Temp);
                Scm_AffFan_t Fan;
                if ( pArc == NULL || !pArc->fValid ) return 0;
                Fan.Constant = pArc->Delay0 + pArc->DelayLoad *
                    Vec_FltEntry(&p->vPaperLiveLoads, iLit) + Tail;
                Fan.SlewCoeff = pArc->DelaySlew;
                Scm_AffFanPush(p->pAffFanouts + Abc_Var2Lit(iVar, fCompl), Fan);
            }
        }
    }
    Gia_ManForEachCiIdWithBoxes(p->pGia, i, c)
        if ( Scm_ObjMapRefNum(p, i, 1) )
        {
            Scm_LinArc_t Temp, * pArc;
            int iNeg = Abc_Var2Lit(i, 1);
            Scm_AffFan_t Fan;
            pArc = Scm_ManAffArcAtLoad(p, p->pCells + 3, 0, Vec_FltEntry(&p->vPaperLiveLoads, iNeg), &Temp);
            if ( pArc == NULL || !pArc->fValid ) return 0;
            Fan.Constant = pArc->Delay0 + pArc->DelayLoad *
                Vec_FltEntry(&p->vPaperLiveLoads, iNeg) +
                Scm_ManAffTail(p, iNeg, p->pAffExactSlews[iNeg], NULL);
            Fan.SlewCoeff = pArc->DelaySlew;
            Scm_AffFanPush(p->pAffFanouts + Abc_Var2Lit(i, 0), Fan);
        }
    return 1;
}

static void Scm_ManAffElaCandPush( Scm_AffElaCand_t ** ppList,
    int * pnList, int * pnAlloc, Scm_Mat_t * pM, word Area )
{
    if ( *pnList == *pnAlloc )
    {
        *pnAlloc = *pnAlloc ? 2 * *pnAlloc : 16;
        *ppList = ABC_REALLOC(Scm_AffElaCand_t, *ppList, *pnAlloc);
    }
    (*ppList)[*pnList].M = *pM;
    (*ppList)[*pnList].Area = Area;
    (*pnList)++;
}

static int Scm_ManAffElaAreaUseful( word Freed, word Added )
{
    return Added < Freed;
}

static word Scm_ManAffElaAreaLimit_rec( Scm_Man_t * p, int i, int c,
    Scm_Mat_t * pM, word Limit )
{
    int k, v, phase, * pCut;
    word Area = pM->fCompl ? p->InvAreaW :
        (Scm_ObjCutSetId(p, i) ? Scm_ManCell(p, pM->Gate)->AreaW : 0);
    if ( Area >= Limit ) return Area;
    if ( pM->fCompl )
    {
        Vec_IntPush(&p->vBackup, Abc_Var2Lit(i, !c));
        if ( !Scm_ObjMapRefInc(p, i, !c) )
            Area += Scm_ManAffElaAreaLimit_rec(p, i, !c,
                Scm_ObjMatchD(p, i, !c), Limit - Area);
        return Area;
    }
    if ( !Scm_ObjCutSetId(p, i) ) return Area;
    pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, i), pM->CutH);
    Scm_CutForEachVarCompl(pCut, pM->Cfg, v, phase, k)
    {
        Vec_IntPush(&p->vBackup, Abc_Var2Lit(v, phase));
        if ( !Scm_ObjMapRefInc(p, v, phase) )
            Area += Scm_ManAffElaAreaLimit_rec(p, v, phase,
                Scm_ObjMatchD(p, v, phase), Limit - Area);
        if ( Area >= Limit ) break;
    }
    return Area;
}

static word Scm_ManAffElaRefArea( Scm_Man_t * p, int i, int c,
    Scm_Mat_t * pM, word Limit )
{
    word Area;
    int Lit, k;

    /* Exact pruning: once positive cell costs exhaust the removable
       cone's area, this candidate cannot save area.  Roll back every
       reference touched by the partial traversal before returning. */
    Vec_IntClear(&p->vBackup);
    Area = Scm_ManAffElaAreaLimit_rec(p, i, c, pM, Limit);
    Vec_IntForEachEntry(&p->vBackup, Lit, k)
        Scm_ObjMapRefDec(p, Abc_Lit2Var(Lit), Abc_LitIsCompl(Lit));
#ifdef SCM_AFF_ELA_AREA_VERIFY
    SCM_AFF_ELA_AREA_VERIFY(p, i, c, pM, Limit, Area);
#endif
    return Area;
}

static void Scm_ManAffElaCandidatesInt( Scm_Man_t * p, int iObj, int c,
    Scm_Mat_t * pOld, word Freed, Scm_AffElaCand_t ** ppList,
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
            M.fBest = 1;
            if ( !Scm_PaperMatSame(pOld, &M) )
            {
                word Area = fMeasureArea ? Scm_ManAffElaRefArea(p, iObj, c, &M, Freed) : 0;
                if ( Scm_ManAffElaAreaUseful(Freed, Area) )
                    Scm_ManAffElaCandPush(ppList, pnList, pnAlloc, &M, Area);
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
                Scm_LinArc_t * pArc = Scm_ManLinearArc(p, pCell, k);
                fValid = pArc != NULL && pArc->fValid;
            }
            if ( !fValid ) continue;
            Cfg.fCompl = 0;
            M.Gate = Info;
            M.CutH = Scm_CutHandle(pCutSet, pCut);
            M.Cfg = Cfg;
            M.fBest = 1;
            if ( Scm_PaperMatSame(pOld, &M) ) continue;

            Area = fMeasureArea ? Scm_ManAffElaRefArea(p, iObj, c, &M, Freed) : 0;
            if ( Scm_ManAffElaAreaUseful(Freed, Area) )
                Scm_ManAffElaCandPush(ppList, pnList, pnAlloc, &M, Area);
        }
    }
}

/* Existing cheap repair and area-recovery callers retain exact area
   enumeration. Only delay-first screening can omit this unused cost. */
static void Scm_ManAffElaCandidates( Scm_Man_t *p,int iObj,int c,
    Scm_Mat_t *old,word freed,Scm_AffElaCand_t **list,int *n,int *alloc )
{
    Scm_ManAffElaCandidatesInt(p,iObj,c,old,freed,list,n,alloc,1);
}

static void Scm_ManAffElaCtxFree( Scm_AffElaCtx_t * pCtx )
{
    int i;
    if ( pCtx == NULL ) return;
    if ( pCtx->pFans )
        for ( i = 0; i < pCtx->nLits; i++ )
        {
            ABC_FREE(pCtx->pFans[i].pRoots);
            ABC_FREE(pCtx->pFans[i].pPins);
        }
    if ( pCtx->pTailLines )
        for ( i = 0; i < pCtx->nLits; i++ )
            ABC_FREE(pCtx->pTailLines[i].pFans);
    if ( pCtx->pTailLinesRf )
        for ( i = 0; i < pCtx->nLits; i++ )
            ABC_FREE(pCtx->pTailLinesRf[i].pFans);
    if (pCtx->pArcCache) {
        for (i=0;i<pCtx->nLits;i++) ABC_FREE(pCtx->pArcCache[i]);
        ABC_FREE(pCtx->pArcCache);
    }
    ABC_FREE(pCtx->pFans);
    ABC_FREE(pCtx->pTailLines);
    ABC_FREE(pCtx->pTailLinesRf);
    ABC_FREE(pCtx->pLiveLoads);
    ABC_FREE(pCtx->pLiveLoadsRf);
    ABC_FREE(pCtx->pBufferAreas);
    ABC_FREE(pCtx->pTrialArr);
    ABC_FREE(pCtx->pTrialSlew);
    ABC_FREE(pCtx->pTailAtBaseSlew);
    ABC_FREE(pCtx->pTrialArrRf);
    ABC_FREE(pCtx->pTrialSlewRf);
    ABC_FREE(pCtx->pTailAtBaseSlewRf);
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

static void Scm_ManAffElaFanEdit( Scm_AffElaCtx_t * pCtx, int iChildLit,
    int iRootLit, int iPin, int Sign )
{
    Scm_AffElaFanSet_t * pSet = pCtx->pFans + iChildLit;
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
        if ( pCtx->pEdgePos ) pCtx->pEdgePos[iRootLit * NF_LEAF_MAX + iPin] = pSet->nRoots;
        pSet->nRoots++;
        return;
    }
    /* An edge (root, pin) occurs once in its child's list, so the indexed
       removal reproduces the scan below (same slot, same swap with the last). */
    if ( pCtx->pEdgePos )
    {
        k = pCtx->pEdgePos[iRootLit * NF_LEAF_MAX + iPin];
        if ( k >= 0 && k < pSet->nRoots && pSet->pRoots[k] == iRootLit && pSet->pPins[k] == iPin )
        {
            pSet->pRoots[k] = pSet->pRoots[--pSet->nRoots];
            pSet->pPins[k] = pSet->pPins[pSet->nRoots];
            if ( k < pSet->nRoots )
                pCtx->pEdgePos[pSet->pRoots[k] * NF_LEAF_MAX + pSet->pPins[k]] = k;
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
                pCtx->pEdgePos[pSet->pRoots[k] * NF_LEAF_MAX + pSet->pPins[k]] = k;
            return;
        }
    pCtx->fError = 1;
}

static void Scm_ManAffElaEdgeEdit( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iChildLit, int iRootLit, int iPin, float Cap, int Sign, int fInitial )
{
    Scm_ManAffElaFanEdit(pCtx, iChildLit, iRootLit, iPin, Sign);
    if ( fInitial ) return;
    /* Area trials repeatedly remove and restore the same pin loads.  Float
       add/subtract does not cancel and can drift noticeably on long sweeps.
       Keep the live sum in double, rounding only for the affine evaluator. */
    pCtx->pLiveLoads[iChildLit] += (double)Sign * (double)Cap;
    Vec_FltWriteEntry(&p->vPaperLiveLoads, iChildLit,
        (float)pCtx->pLiveLoads[iChildLit]);
    if ( pCtx->pCollectSeeds )
        Vec_IntPush(pCtx->pCollectSeeds, iChildLit),
        Vec_IntPush(pCtx->pCollectSeeds, iRootLit);
}

static void Scm_ManAffElaMatchEdit( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iObj, int c, Scm_Mat_t * pM, int Sign, int fInitial )
{
    int iRootLit = Abc_Var2Lit(iObj, c), iVar, fCompl, k, * pCut;
    Mio_Cell2_t * pCell;
    SC_Cell * pSclCell;
    if ( !fInitial && pCtx->pCollectSeeds )
        Vec_IntPush(pCtx->pCollectSeeds, iRootLit);
    if ( pM->fCompl )
    {
        if ( pCtx->pLiveLoadsRf && !fInitial )
        {
            Scm_RfPair_t Cap = Scm_ManRfPinCap(p, p->pCells + 3, 0);
            int t, iLit = Abc_Var2Lit(iObj, !c);
            for ( t = 0; t < 2; t++ )
            {
                pCtx->pLiveLoadsRf[2*iLit+t] += (double)Sign * Cap.Value[t];
                p->pAllRfLoads[iLit].Value[t] = (float)pCtx->pLiveLoadsRf[2*iLit+t];
            }
        }
        Scm_ManAffElaEdgeEdit(p, pCtx, Abc_Var2Lit(iObj, !c),
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
        if ( pCtx->pLiveLoadsRf && !fInitial )
        {
            Scm_RfPair_t Cap = Scm_ManRfPinCap(p, pCell, k);
            int t, iLit = Abc_Var2Lit(iVar, fCompl);
            for ( t = 0; t < 2; t++ )
            {
                pCtx->pLiveLoadsRf[2*iLit+t] += (double)Sign * Cap.Value[t];
                p->pAllRfLoads[iLit].Value[t] = (float)pCtx->pLiveLoadsRf[2*iLit+t];
            }
        }
        Scm_ManAffElaEdgeEdit(p, pCtx, Abc_Var2Lit(iVar, fCompl),
            iRootLit, k, Scm_ManCellPinCap(p, pSclCell, k), Sign, fInitial);
    }
}

/* A hierarchy of nonempty 64-bit words is a bounded integer priority
   queue.  AIG IDs already give the topological order, so comparisons and
   repeated match lookups are unnecessary during propagation. */
static void Scm_ManAffElaQueueStart( Scm_AffElaCtx_t * pCtx, unsigned nKeys )
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

static int Scm_ManAffElaQueueHas( Scm_AffElaCtx_t * pCtx )
{
    return pCtx->pQueueBits[pCtx->nQueueLevels - 1][0] != 0;
}

static void Scm_ManAffElaQueuePush( Scm_AffElaCtx_t * pCtx, unsigned Key )
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

static unsigned Scm_ManAffElaQueuePop( Scm_AffElaCtx_t * pCtx )
{
    unsigned Key = 0, Result;
    int Level;
    assert(Scm_ManAffElaQueueHas(pCtx));
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

static float Scm_ManAffBufferArea( Scm_Man_t * p, int Lit )
{
    int Obj = Abc_Lit2Var(Lit), c = Abc_LitIsCompl(Lit);
    Scm_Mat_t * pM;
    Mio_Cell2_t * pCell;
    if ( !Scm_ObjMapRefNum(p, Obj, c) || !Obj ||
         (Gia_ObjIsCi(Gia_ManObj(p->pGia, Obj)) && !c) ) return 0.0f;
    pM = Scm_ObjMatchBest(p, Obj, c);
    pCell = pM->fCompl ? p->pCells + 3 : Scm_ManCell(p, pM->Gate);
    if ( !pCell->nFanins ) return 0.0f;
    if ( p->pBufferCosts )
    {
        Scm_ManEnsureEnv(p, pCell);
        return Scm_AffPwlEval(p->pBufferCosts + pCell->Id,
            Vec_FltEntry(&p->vPaperLiveLoads, Lit));
    }
    return 0.0f;
}

/* Only changed implementations and loads can change virtual buffer area.
   Count shared boundary nets once, including nets that disappear entirely. */
/* Same result as Vec_IntUniqify() (ascending, unique) for literal vectors:
   stamp-based deduplication, then an LSD radix sort of the unique entries.
   Called for every repair candidate; qsort dominated runtime on wide nets. */
static void Scm_ManAffElaSeedsUniqify( Scm_AffElaCtx_t * pCtx, Vec_Int_t * vSeeds )
{
    int nSize = Vec_IntSize(vSeeds), i, k, Pass, Lit, * pSrc, * pDst;
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
    for ( Pass = 0; Pass < 3; Pass++ )
    {
        int Shift = 11 * Pass, nBins = Pass == 2 ? 1024 : 2048, Sum = 0, c;
        memset(Counts, 0, sizeof(int) * nBins);
        for ( i = 0; i < k; i++ ) Counts[((unsigned)pSrc[i] >> Shift) & (nBins - 1)]++;
        for ( i = 0; i < nBins; i++ ) c = Counts[i], Counts[i] = Sum, Sum += c;
        for ( i = 0; i < k; i++ ) pDst[Counts[((unsigned)pSrc[i] >> Shift) & (nBins - 1)]++] = pSrc[i];
        { int * t = pSrc; pSrc = pDst; pDst = t; }
    }
    if ( pSrc != Vec_IntArray(vSeeds) )
        memcpy(Vec_IntArray(vSeeds), pSrc, sizeof(int) * k);
}

static double Scm_ManAffBufferAreaDelta( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int fCommit )
{
    double Delta = 0.0;
    int i, Lit;
    Scm_ManAffElaSeedsUniqify(pCtx, pCtx->vTrialSeeds);
    Vec_IntForEachEntry(pCtx->vTrialSeeds, Lit, i)
    {
        float Area = Scm_ManAffBufferArea(p, Lit);
        Delta += (double)Area - pCtx->pBufferAreas[Lit];
        if ( fCommit ) pCtx->pBufferAreas[Lit] = Area;
    }
#ifdef SCM_BUFFER_AREA_VERIFY
    SCM_BUFFER_AREA_VERIFY(p, pCtx, Delta, fCommit);
#endif
    return Delta;
}

static Scm_AffElaCtx_t * Scm_ManAffElaCtxStart( Scm_Man_t * p )
{
    Gia_Obj_t * pObj;
    Scm_AffElaCtx_t * pCtx;
    int i, c;
    /* Buffer aliases need a separate dynamic load-transfer edge.  Retain
       the proven full-cover guard for those uncommon GIA networks. */
    Gia_ManForEachAnd(p->pGia, pObj, i)
        if ( Gia_ObjIsBuf(pObj) ) return NULL;
    pCtx = ABC_CALLOC(Scm_AffElaCtx_t, 1);
    /* The retained -W 3 algorithm uses lazy residual-tail construction,
       exact commit propagation, and incremental tail maintenance. */
    pCtx->nLits = 2 * Gia_ManObjNum(p->pGia);
    pCtx->fRiseFall = p->pPars->fUseRiseFallAll;
    if (pCtx->fRiseFall && 12 == 12)
        pCtx->pArcCache=ABC_CALLOC(Cf_Node *,pCtx->nLits);
    pCtx->pFans = ABC_CALLOC(Scm_AffElaFanSet_t, pCtx->nLits);
    pCtx->pLiveLoads = ABC_ALLOC(double, pCtx->nLits);
    if ( p->pAllRfLoads )
    {
        int t;
        pCtx->pLiveLoadsRf = ABC_ALLOC(double, 2*pCtx->nLits);
        for ( i = 0; i < pCtx->nLits; i++ )
            for ( t = 0; t < 2; t++ )
                pCtx->pLiveLoadsRf[2*i+t] = p->pAllRfLoads[i].Value[t];
    }

    {
        pCtx->pBufferAreas = ABC_ALLOC(float, pCtx->nLits);
        for ( i = 0; i < pCtx->nLits; i++ )
            pCtx->pBufferAreas[i] = Scm_ManAffBufferArea(p, i);
    }
    pCtx->pTrialArr = ABC_ALLOC(float, pCtx->nLits);
    pCtx->pTrialSlew = ABC_ALLOC(float, pCtx->nLits);
    pCtx->pTouched = ABC_CALLOC(unsigned, pCtx->nLits);
    pCtx->pComputed = ABC_CALLOC(unsigned, pCtx->nLits);
    pCtx->vOldSeeds = Vec_IntAlloc(128);
    pCtx->vTrialSeeds = Vec_IntAlloc(128);
    pCtx->vAffected = Vec_IntAlloc(128);
    pCtx->pSeedStamp = ABC_CALLOC(unsigned, pCtx->nLits);
    pCtx->pEdgePos = ABC_FALLOC(int, pCtx->nLits * NF_LEAF_MAX);
    pCtx->vSeedSort = Vec_IntAlloc(128);
    Scm_ManAffElaQueueStart(pCtx, 2u * (unsigned)pCtx->nLits);
    pCtx->pTailLines = ABC_CALLOC(Scm_AffFanSet_t, pCtx->nLits);
    pCtx->pTailAtBaseSlew = ABC_ALLOC(float, pCtx->nLits);
    if ( pCtx->fRiseFall )
    {
        pCtx->pTailLinesRf = ABC_CALLOC(Scm_RfFanSet_t, pCtx->nLits);
        pCtx->pTrialArrRf = ABC_ALLOC(Scm_RfPair_t, pCtx->nLits);
        pCtx->pTrialSlewRf = ABC_ALLOC(Scm_RfPair_t, pCtx->nLits);
        pCtx->pTailAtBaseSlewRf = ABC_ALLOC(Scm_RfPair_t, pCtx->nLits);
    }
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
    Gia_ManForEachCoWithBoxes(p->pGia, pObj, i)
        pCtx->pIsPo[Gia_ObjFaninLit0p(p->pGia, pObj)] = 1;
    for ( i = 0; i < pCtx->nLits; i++ )
        pCtx->pLiveLoads[i] = Vec_FltEntry(&p->vPaperLiveLoads, i);
    if ( 12 && !pCtx->fRiseFall )
        for ( i = 0; i < pCtx->nLits; i++ )
        {
            Scm_AffFanSet_t * pSource = p->pAffFanouts + i;
            Scm_AffFanSet_t * pTarget = pCtx->pTailLines + i;
            int k;
            if ( !pSource->nFans ) continue;
            for ( k = 0; k < pSource->nFans; k++ )
                Scm_AffFanPush(pTarget, pSource->pFans[k]);
            pCtx->pTailAtBaseSlew[i] = Scm_ManAffTail(p, i,
                p->pAffExactSlews[i], NULL);
            pCtx->pTailValid[i] = 1;
        }
    Gia_ManForEachCiIdWithBoxes(p->pGia, i, c)
        if ( Scm_ObjMapRefNum(p, i, 1) )
            Scm_ManAffElaMatchEdit(p, pCtx, i, 1,
                Scm_ObjMatchBest(p, i, 1), 1, 1);
    Gia_ManForEachAnd(p->pGia, pObj, i)
        for ( c = 0; c < 2; c++ )
            if ( Scm_ObjMapRefNum(p, i, c) )
                Scm_ManAffElaMatchEdit(p, pCtx, i, c,
                    Scm_ObjMatchBest(p, i, c), 1, 1);
    if ( pCtx->fError )
    {
        Scm_ManAffElaCtxFree(pCtx);
        return NULL;
    }
    return pCtx;
}

static word Scm_ManAffElaDerefRec( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iObj, int c, Scm_Mat_t * pM )
{
    word Area = 0;
    int iVar, fCompl, k, * pCut;
    assert(pM->fBest);
    Scm_ManAffElaMatchEdit(p, pCtx, iObj, c, pM, -1, 0);
    if ( pM->fCompl )
    {
        assert(Scm_ObjMapRefNum(p, iObj, !c) > 0);
        if ( !Scm_ObjMapRefDec(p, iObj, !c) )
            Area += Scm_ManAffElaDerefRec(p, pCtx, iObj, !c,
                Scm_ObjMatchD(p, iObj, !c));
        return Area + p->InvAreaW;
    }
    if ( Scm_ObjCutSetId(p, iObj) == 0 ) return 0;
    pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
    Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
    {
        assert(Scm_ObjMapRefNum(p, iVar, fCompl) > 0);
        if ( !Scm_ObjMapRefDec(p, iVar, fCompl) )
            Area += Scm_ManAffElaDerefRec(p, pCtx, iVar, fCompl,
                Scm_ObjMatchD(p, iVar, fCompl));
    }
    return Area + Scm_ManCell(p, pM->Gate)->AreaW;
}

static word Scm_ManAffElaRefRec( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iObj, int c, Scm_Mat_t * pM )
{
    word Area = 0;
    int iVar, fCompl, k, * pCut;
    assert(pM->fBest);
    Scm_ManAffElaMatchEdit(p, pCtx, iObj, c, pM, 1, 0);
    if ( pM->fCompl )
    {
        if ( !Scm_ObjMapRefInc(p, iObj, !c) )
            Area += Scm_ManAffElaRefRec(p, pCtx, iObj, !c,
                Scm_ObjMatchD(p, iObj, !c));
        return Area + p->InvAreaW;
    }
    if ( Scm_ObjCutSetId(p, iObj) == 0 ) return 0;
    pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
    Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
        if ( !Scm_ObjMapRefInc(p, iVar, fCompl) )
            Area += Scm_ManAffElaRefRec(p, pCtx, iVar, fCompl,
                Scm_ObjMatchD(p, iVar, fCompl));
    return Area + Scm_ManCell(p, pM->Gate)->AreaW;
}

static int Scm_ManAffElaReadState( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iLit, float * pArrival, float * pSlew )
{
    if ( pCtx->pTouched[iLit] == pCtx->Epoch )
    {
        if ( pCtx->pComputed[iLit] != pCtx->Epoch ) return 0;
        *pArrival = pCtx->pTrialArr[iLit];
        *pSlew = pCtx->pTrialSlew[iLit];
    }
    else
    {
        *pArrival = p->pAffExactArrs[iLit];
        *pSlew = p->pAffExactSlews[iLit];
    }
    return 1;
}

static int Scm_ManAffElaReadStateRf( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iLit, Scm_RfPair_t * pArrival, Scm_RfPair_t * pSlew )
{
    if ( pCtx->pTouched[iLit] == pCtx->Epoch )
    {
        if ( pCtx->pComputed[iLit] != pCtx->Epoch ) return 0;
        *pArrival = pCtx->pTrialArrRf[iLit];
        *pSlew = pCtx->pTrialSlewRf[iLit];
    }
    else
    {
        *pArrival = p->pAffExactRfArrs[iLit];
        *pSlew = p->pAffExactRfSlews[iLit];
    }
    return 1;
}

static int Scm_ManAffElaEvalLit( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iObj, int c )
{
    int iLit = Abc_Var2Lit(iObj, c), iVar, fCompl, k, * pCut;
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    Scm_Mat_t * pM = Scm_ObjMatchBest(p, iObj, c);
    Mio_Cell2_t * pCell;
    Scm_AffMatch_t Match;
    float Load = Vec_FltEntry(&p->vPaperLiveLoads, iLit);
    float Arrival = 0.0f, Slew = 0.0f;
    if ( iObj == 0 || (Gia_ObjIsCi(pObj) && !c) )
        goto done;
    if ( pM->fCompl )
    {
        Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoad(p, p->pCells + 3, 0, Load, &Temp);
        float SourceArrival, SourceSlew;
        if ( pArc == NULL || !pArc->fValid ||
             !Scm_ManAffElaReadState(p, pCtx, Abc_Var2Lit(iObj, !c),
                 &SourceArrival, &SourceSlew) ) return 0;
        memset(&Match, 0, sizeof(Match));
        Match.M.Gate = p->pCells[3].Id;
        Arrival = SourceArrival + pArc->Delay0 +
            pArc->DelayLoad * Load + pArc->DelaySlew * SourceSlew;
        Slew = Scm_ManAffCellSlew(p, &Match, Load);
        goto done;
    }
    if ( Gia_ObjIsCi(pObj) ) goto done;
    if ( !Gia_ObjIsAnd(pObj) ) return 0;
    pCell = Scm_ManCell(p, pM->Gate);
    if ( pM->CutH == 0 || pCell->nFanins == 0 ) goto done;
    pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
    if ( Scm_CutSize(pCut) != (int)pCell->nFanins ||
         !Scm_CfgIsCutPermutation(pM->Cfg, Scm_CutSize(pCut)) ) return 0;
    Arrival = -FLT_MAX;
    Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
    {
        Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoad(p, pCell, k, Load, &Temp);
        float ChildArrival, ChildSlew;
        if ( pArc == NULL || !pArc->fValid ||
             !Scm_ManAffElaReadState(p, pCtx, Abc_Var2Lit(iVar, fCompl),
                 &ChildArrival, &ChildSlew) ) return 0;
        Arrival = Abc_MaxFloat(Arrival, ChildArrival + pArc->Delay0 +
            pArc->DelayLoad * Load + pArc->DelaySlew * ChildSlew);
    }
    memset(&Match, 0, sizeof(Match));
    Match.M = *pM;
    Slew = Scm_ManAffCellSlew(p, &Match, Load);
done:
    if ( !isfinite(Arrival) || !isfinite(Slew) ) return 0;
    pCtx->pTrialArr[iLit] = Arrival;
    pCtx->pTrialSlew[iLit] = Slew;
    pCtx->pComputed[iLit] = pCtx->Epoch;
    return 1;
}

/* Private exact timing acceleration. Cache the selected cell's input
   literals and fixed-load arc coefficients, not its arrivals. The key
   includes both transition loads and every structural match field, so a
   trial, restore, or phase change cannot reuse incompatible coefficients.
   Keep the original floating-point operation grouping and pin order. */
typedef struct {
    int child, sense;
    float delay[2], slope[2];
} Cf_Edge;
struct Cf_Node_ {
    int gate, cut, cfg, inv, valid, n;
    Scm_RfPair_t load, slew;
    Cf_Edge edges[NF_LEAF_MAX];
};

static int Cf_Build(Scm_Man_t *p,Cf_Node *node,int lit,Scm_Mat_t *m,Scm_RfPair_t load)
{
    int obj=lit>>1;
    int *cut;
    Mio_Cell2_t *cell;
    Gia_Obj_t *o=Gia_ManObj(p->pGia,obj);
    node->valid=0;node->n=0;
    node->slew.Value[0]=node->slew.Value[1]=0;
    if(!obj || (Gia_ObjIsCi(o) && !(lit&1))) goto done;
    cell=m->fCompl?p->pCells+3:Scm_ManCell(p,m->Gate);
    if(!m->fCompl && (!m->CutH || !cell->nFanins)) goto done;
    cut=m->fCompl?NULL:Scm_CutFromHandle(Scm_ObjCutSet(p,obj),m->CutH);
    if(cell->nFanins>NF_LEAF_MAX || (!m->fCompl &&
       (Scm_CutSize(cut)!=(int)cell->nFanins || !Scm_CfgIsCutPermutation(m->Cfg,Scm_CutSize(cut))))) return 0;
    node->n=cell->nFanins;
    for(int k=0;k<node->n;k++) {
        Cf_Edge *e=node->edges+k;
        Scm_LinArc_t tmp,*arc=Scm_ManAffArcAtLoadRf(p,cell,k,load,&tmp);
        if(!arc || !arc->fValid) return 0;
        e->child=m->fCompl?(lit^1):Abc_Var2Lit(Scm_CutLeaves(cut)[Scm_CfgVar(m->Cfg,k)],Scm_CfgCompl(m->Cfg,k));
        e->sense=arc->TimingSense;
        for(int t=0;t<2;t++) {
            e->delay[t]=arc->RfDelay0[t]+arc->RfDelayLoad[t]*load.Value[t];
            e->slope[t]=arc->RfDelaySlew[t];
            node->slew.Value[t]=Abc_MaxFloat(node->slew.Value[t],Scm_ManRfSlew(arc,t,load.Value[t]));
        }
    }
done:
    node->gate=m->Gate;node->cut=m->CutH;node->cfg=Scm_Cfg2Int(m->Cfg);node->inv=m->fCompl;
    node->load=load;node->valid=1;
    return 1;
}

static Cf_Node *Cf_Get(Scm_Man_t *p,Scm_AffElaCtx_t *ctx,int obj,int phase)
{
    int lit=2*obj+phase;
    Scm_Mat_t *m=Scm_ObjMatchBest(p,obj,phase);
    Scm_RfPair_t load=Scm_ManRfLoad(p,lit);
    Cf_Node *node=ctx->pArcCache[lit];
    if(!node) node=ctx->pArcCache[lit]=ABC_CALLOC(Cf_Node,1);
    if(!node->valid || node->gate!=(int)m->Gate || node->cut!=m->CutH ||
       node->cfg!=Scm_Cfg2Int(m->Cfg) || node->inv!=(int)m->fCompl ||
       node->load.Value[0]!=load.Value[0] || node->load.Value[1]!=load.Value[1])
        if(!Cf_Build(p,node,lit,m,load)) return NULL;
    return node;
}

static int Cf_Eval(Scm_Man_t *p,Scm_AffElaCtx_t *ctx,int obj,int phase)
{
    int lit=2*obj+phase;
    Scm_RfPair_t arr={{0,0}};
    Cf_Node *node=Cf_Get(p,ctx,obj,phase);
    if(!node) return 0;
    if(node->n) arr.Value[0]=arr.Value[1]=-FLT_MAX;
    for(int k=0;k<node->n;k++) {
        Cf_Edge *e=node->edges+k;Scm_RfPair_t a,s;
        if(!Scm_ManAffElaReadStateRf(p,ctx,e->child,&a,&s)) return 0;
        for(int t=0;t<2;t++) {
            if(e->sense==sc_ts_Pos || e->sense==sc_ts_Non)
                arr.Value[t]=Abc_MaxFloat(arr.Value[t],a.Value[t]+(e->delay[t]+e->slope[t]*s.Value[t]));
            if(e->sense==sc_ts_Neg || e->sense==sc_ts_Non)
                arr.Value[t]=Abc_MaxFloat(arr.Value[t],a.Value[!t]+(e->delay[t]+e->slope[t]*s.Value[!t]));
        }
    }
    if(!isfinite(arr.Value[0]) || !isfinite(arr.Value[1]) ||
       !isfinite(node->slew.Value[0]) || !isfinite(node->slew.Value[1])) return 0;
    ctx->pTrialArrRf[lit]=arr;ctx->pTrialSlewRf[lit]=node->slew;
    ctx->pTrialArr[lit]=Scm_ManRfPairMax(arr);ctx->pTrialSlew[lit]=Scm_ManRfPairMax(node->slew);
    ctx->pComputed[lit]=ctx->Epoch;
    return 1;
}

static int Scm_ManAffElaEvalLitRf( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iObj, int c )
{
    int iLit = Abc_Var2Lit(iObj, c), iVar, fCompl, k, * pCut;
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    Scm_Mat_t * pM = Scm_ObjMatchBest(p, iObj, c);
    Mio_Cell2_t * pCell;
    if (pCtx->pArcCache) return Cf_Eval(p,pCtx,iObj,c);
    Scm_RfPair_t Load = Scm_ManRfLoad(p, iLit);
    Scm_RfPair_t Arrival = {{0.0f, 0.0f}};
    Scm_RfPair_t Slew = {{0.0f, 0.0f}};
    if ( iObj == 0 || (Gia_ObjIsCi(pObj) && !c) )
        goto done;
    if ( pM->fCompl )
    {
        Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, p->pCells + 3, 0, Load, &Temp);
        Scm_RfPair_t SourceArrival, SourceSlew;
        if ( pArc == NULL || !pArc->fValid ||
             !Scm_ManAffElaReadStateRf(p, pCtx, Abc_Var2Lit(iObj, !c),
                 &SourceArrival, &SourceSlew) ) return 0;
        Arrival.Value[0] = Arrival.Value[1] = -FLT_MAX;
        Scm_ManRfArcAccumulate(pArc, Load, SourceArrival, SourceSlew,
            &Arrival, &Slew);
        goto done;
    }
    if ( Gia_ObjIsCi(pObj) ) goto done;
    if ( !Gia_ObjIsAnd(pObj) ) return 0;
    pCell = Scm_ManCell(p, pM->Gate);
    if ( pM->CutH == 0 || pCell->nFanins == 0 ) goto done;
    pCut = Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
    if ( Scm_CutSize(pCut) != (int)pCell->nFanins ||
         !Scm_CfgIsCutPermutation(pM->Cfg, Scm_CutSize(pCut)) ) return 0;
    Arrival.Value[0] = Arrival.Value[1] = -FLT_MAX;
    Scm_CutForEachVarCompl(pCut, pM->Cfg, iVar, fCompl, k)
    {
        Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, pCell, k, Load, &Temp);
        Scm_RfPair_t ChildArrival, ChildSlew;
        if ( pArc == NULL || !pArc->fValid ||
             !Scm_ManAffElaReadStateRf(p, pCtx, Abc_Var2Lit(iVar, fCompl),
                 &ChildArrival, &ChildSlew) ) return 0;
        Scm_ManRfArcAccumulate(pArc, Load, ChildArrival, ChildSlew,
            &Arrival, &Slew);
    }
done:
    if ( !isfinite(Arrival.Value[0]) || !isfinite(Arrival.Value[1]) ||
         !isfinite(Slew.Value[0]) || !isfinite(Slew.Value[1]) ) return 0;
    pCtx->pTrialArrRf[iLit] = Arrival;
    pCtx->pTrialSlewRf[iLit] = Slew;
    pCtx->pTrialArr[iLit] = Scm_ManRfPairMax(Arrival);
    pCtx->pTrialSlew[iLit] = Scm_ManRfPairMax(Slew);
    pCtx->pComputed[iLit] = pCtx->Epoch;
    return 1;
}

static int Scm_ManAffElaOrderKey( Scm_Man_t * p, int iLit )
{
    int iObj = Abc_Lit2Var(iLit), c = Abc_LitIsCompl(iLit);
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    int fInv = (iObj == 0 || Gia_ObjIsCi(pObj)) ? c :
        !!Scm_ObjMatchBest(p, iObj, c)->fCompl;
    return 2 * iObj + fInv;
}

static void Scm_ManAffElaQueueLit( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iLit )
{
    if ( pCtx->pTouched[iLit] == pCtx->Epoch ||
         !Scm_ObjMapRefNum(p, Abc_Lit2Var(iLit), Abc_LitIsCompl(iLit)) )
        return;
    pCtx->pTouched[iLit] = pCtx->Epoch;
    /* Bit 0 preserves the literal phase; bit 1 places an inverter after
       its direct phase even when the direct phase is complemented. */
    Scm_ManAffElaQueuePush(pCtx,
        2u * (unsigned)Scm_ManAffElaOrderKey(p, iLit) + Abc_LitIsCompl(iLit));
}

/* Exact-score pruning for the load-only slew model. Outside ALL changed
   match/load seeds, arc delay increments are fixed floats. A backward cache
   gives the greatest input arrival whose paths cannot exceed the objective's
   pressure threshold. Prune only if BOTH incumbent and trial meet it.
   This leaves fast22's global max/pressure unchanged (with an exact fallback
   if the entire trial drops below the threshold). Commits always retime fully.
   This cache is separate from fast22's frozen screening tails. */
typedef struct {
    Scm_AffElaCtx_t shadow;
    Scm_RfPair_t *required;
    Vec_Int_t *dfs;
    float threshold; int reject;
    unsigned long queries, builds, skips;
} Rq_Man;

/* Largest float x such that float(x + cost) <= required. Form the upper
   rounding-bin boundary in double, then check the actual float operation.
   This avoids accumulating approximate subtracted required times on deep
   paths. Do not start from required-cost: cancellation at zero can require
   millions of nextafter steps. */
static float Rq_Back(float required,float cost)
{
    if(required==FLT_MAX) return FLT_MAX;
    double edge=((double)required+(double)nextafterf(required,INFINITY))*0.5;
    float x=(float)(edge-(double)cost);
    int steps=0;
    (void)steps;
    while((float)(x+cost)>required) {x=nextafterf(x,-INFINITY);assert(++steps<8);}
    while(isfinite(nextafterf(x,INFINITY)) && (float)(nextafterf(x,INFINITY)+cost)<=required) {
        x=nextafterf(x,INFINITY);assert(++steps<8);
    }
    return x;
}

static Rq_Man *Rq_Start(Scm_AffElaCtx_t *ctx,double threshold)
{
    Rq_Man *r=ABC_CALLOC(Rq_Man,1);r->shadow=*ctx;
    r->shadow.fLiveTail=1;r->shadow.pTailValid=ABC_CALLOC(unsigned char,ctx->nLits);
    r->shadow.vTailStack=Vec_IntAlloc(128);r->dfs=Vec_IntAlloc(128);
    r->required=ABC_ALLOC(Scm_RfPair_t,ctx->nLits);
    r->threshold=(float)threshold;
    if((double)r->threshold>threshold) r->threshold=nextafterf(r->threshold,-INFINITY);
    return r;
}
static void Rq_Stop(Rq_Man *r)
{
    if(!r) return;
    ABC_FREE(r->shadow.pTailValid);Vec_IntFree(r->shadow.vTailStack);
    Vec_IntFree(r->dfs);ABC_FREE(r->required);ABC_FREE(r);
}
static int Rq_Build(Scm_Man_t *p,Rq_Man *r,int lit)
{
    Scm_AffElaCtx_t *c=&r->shadow;
    if(c->pTailValid[lit]) return 1;
    Vec_IntClear(r->dfs);Vec_IntPush(r->dfs,lit);Vec_IntPush(r->dfs,0);
    while(Vec_IntSize(r->dfs)) {
        int n=Vec_IntSize(r->dfs),x=Vec_IntEntry(r->dfs,n-2),j=Vec_IntEntry(r->dfs,n-1);
        Scm_AffElaFanSet_t *fans=c->pFans+x;
        if(j<fans->nRoots) {
            int y=fans->pRoots[j];Vec_IntWriteEntry(r->dfs,n-1,j+1);
            if(!c->pTailValid[y]) {Vec_IntPush(r->dfs,y);Vec_IntPush(r->dfs,0);}
            continue;
        }
        Scm_RfPair_t req={{FLT_MAX,FLT_MAX}},slew=p->pAffExactRfSlews[x];
        if(c->pIsPo[x]) req.Value[0]=req.Value[1]=r->threshold;
        for(j=0;j<fans->nRoots;j++) {
            int y=fans->pRoots[j],pin=fans->pPins[j],sense;
            float fixed[2],slope[2];
            /* Forward timing already caches these exact fixed-load arc
               coefficients. Share that cache with the backward requirement
               walk; validate the full match/load key before every reuse. */
            if(c->pArcCache) {
                Cf_Node *node=Cf_Get(p,c,y>>1,y&1);
                if(!node || pin<0 || pin>=node->n || node->edges[pin].child!=x) return 0;
                Cf_Edge *edge=node->edges+pin;sense=edge->sense;
                for(int t=0;t<2;t++) {fixed[t]=edge->delay[t];slope[t]=edge->slope[t];}
            } else {
                Scm_Mat_t *m=Scm_ObjMatchBest(p,y>>1,y&1);
                Mio_Cell2_t *cell=m->fCompl?p->pCells+3:Scm_ManCell(p,m->Gate);
                Scm_RfPair_t load=Scm_ManRfLoad(p,y);
                Scm_LinArc_t temp,*arc=Scm_ManAffArcAtLoadRf(p,cell,pin,load,&temp);
                if(!arc || !arc->fValid) return 0;
                sense=arc->TimingSense;
                for(int t=0;t<2;t++) {fixed[t]=arc->RfDelay0[t]+arc->RfDelayLoad[t]*load.Value[t];slope[t]=arc->RfDelaySlew[t];}
            }
            for(int out=0;out<2;out++) {
                for(int in=0;in<2;in++) {
                    if(sense!=sc_ts_Non &&
                       !(sense==sc_ts_Pos && in==out) &&
                       !(sense==sc_ts_Neg && in!=out)) continue;
                    float cost=fixed[out]+slope[out]*slew.Value[in];
                    if(!isfinite(cost)) return 0;
                    /* If the current bound already satisfies this edge,
                       its exact inverse cannot tighten the minimum. */
                    if((float)(req.Value[in]+cost)>r->required[y].Value[out])
                        req.Value[in]=fminf(req.Value[in],Rq_Back(r->required[y].Value[out],cost));
                }
            }
        }
        r->required[x]=req;c->pTailValid[x]=1;r->builds++;
        Vec_IntPop(r->dfs);Vec_IntPop(r->dfs);
    }
    return 1;
}
static int Rq_CanSkip(Scm_Man_t *p,Scm_AffElaCtx_t *ctx,int lit)
{
    Rq_Man *r=(Rq_Man *)ctx->pScorePrune;
    if(!ctx->fScorePrune || !r || (lit>>1)<=ctx->ScorePruneCutoff) return 0;
    /* Changed slew would change the suffix increments; never prune it. */
    for(int t=0;t<2;t++) if(p->pAffExactRfSlews[lit].Value[t]!=ctx->pTrialSlewRf[lit].Value[t]) return 0;
    r->queries++;
    if(!Rq_Build(p,r,lit)) {ctx->fError=1;return 0;}
    if(r->reject) {
        for(int t=0;t<2;t++) if(ctx->pTrialArrRf[lit].Value[t]>r->required[lit].Value[t]) {
            ctx->fScoreRejected=1;r->skips++;return 1;
        }
        return 0;
    }
    for(int t=0;t<2;t++) if(p->pAffExactRfArrs[lit].Value[t]>r->required[lit].Value[t] ||
        ctx->pTrialArrRf[lit].Value[t]>r->required[lit].Value[t]) return 0;
    r->skips++;ctx->nScorePruned++;return 1;
}

static int Scm_ManAffElaTimeLocal( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iMaxObj )
{
    int i, iLit, j;
    if ( pCtx->fError ) return 0;
    ++pCtx->Epoch;
    assert(pCtx->Epoch != 0);
    Vec_IntClear(pCtx->vAffected);
    if(pCtx->vScoreOutputs) Vec_IntClear(pCtx->vScoreOutputs);
    /* Normally empty; discard unfinished work after an invalid trial. */
    while ( Scm_ManAffElaQueueHas(pCtx) ) Scm_ManAffElaQueuePop(pCtx);
    Vec_IntForEachEntry(pCtx->vTrialSeeds, iLit, i)
        if ( Abc_Lit2Var(iLit) <= iMaxObj )
            Scm_ManAffElaQueueLit(p, pCtx, iLit);
    /* AIG IDs are topological.  The queue orders a direct phase before
       an inverter on the same object.  Only a changed arrival or slew can
       affect selected fanouts, so reconvergent noncritical changes stop. */
    while ( Scm_ManAffElaQueueHas(pCtx) )
    {
        Scm_AffElaFanSet_t * pFans;
        unsigned Key = Scm_ManAffElaQueuePop(pCtx);
        iLit = Abc_Var2Lit(Key >> 2, Key & 1);
        if ( pCtx->fRiseFall ?
             !Scm_ManAffElaEvalLitRf(p, pCtx, Abc_Lit2Var(iLit),
                Abc_LitIsCompl(iLit)) :
             !Scm_ManAffElaEvalLit(p, pCtx, Abc_Lit2Var(iLit),
                Abc_LitIsCompl(iLit)) ) return 0;
        Vec_IntPush(pCtx->vAffected, iLit);
        if(pCtx->vScoreOutputs && pCtx->pIsPo[iLit]) Vec_IntPush(pCtx->vScoreOutputs,iLit);
        /* Timing approximation: every changed match and pin-load
           driver is already a transaction seed.  Retiming only those seeds
           bounds work by the edited cone, but retains cached arrivals along
           unchanged reconvergent paths.  The round-end fitted-model refresh
           restores full timing; it does not choose between coverings. */
        if ( 12 && !pCtx->fFullPropagation ) continue;
        if ( pCtx->fRiseFall )
        {
            if ( pCtx->pTrialArrRf[iLit].Value[0] ==
                     p->pAffExactRfArrs[iLit].Value[0] &&
                 pCtx->pTrialArrRf[iLit].Value[1] ==
                     p->pAffExactRfArrs[iLit].Value[1] &&
                 pCtx->pTrialSlewRf[iLit].Value[0] ==
                     p->pAffExactRfSlews[iLit].Value[0] &&
                 pCtx->pTrialSlewRf[iLit].Value[1] ==
                     p->pAffExactRfSlews[iLit].Value[1] ) continue;
        }
        else if ( pCtx->pTrialArr[iLit] == p->pAffExactArrs[iLit] &&
                  pCtx->pTrialSlew[iLit] == p->pAffExactSlews[iLit] ) continue;
        if (Rq_CanSkip(p,pCtx,iLit)) {
            if(pCtx->fScoreRejected) {
                while(Scm_ManAffElaQueueHas(pCtx)) Scm_ManAffElaQueuePop(pCtx);
                return 1;
            }
            continue;
        }
        if(pCtx->fError) return 0;
        pFans = pCtx->pFans + iLit;
        for ( j = 0; j < pFans->nRoots; j++ )
        {
            int iRootLit = pFans->pRoots[j];
            if ( !Scm_ObjMapRefNum(p, Abc_Lit2Var(iRootLit),
                    Abc_LitIsCompl(iRootLit)) ) return 0;
            /* The ELA sweep visits AIG objects in reverse ID order.
               Later trials can only use this root or a lower-ID object
               as a leaf.  The tail cache needs downstream loads/slews,
               not downstream arrivals; final full STA restores them. */
            if ( Abc_Lit2Var(iRootLit) > iMaxObj )
                continue;
            Scm_ManAffElaQueueLit(p, pCtx, iRootLit);
        }
    }
    /* The original scalar interface refreshes arrivals needed by
       later reverse-topological trials, including retained reconvergent
       paths. Global timing waits for the round-end refresh. */
    return 1;
}

static float Scm_ManAffElaTailLinesEval( Scm_AffFanSet_t * pSet, float Slew )
{
    float Tail = -FLT_MAX;
    int k;
    for ( k = 0; k < pSet->nFans; k++ )
        Tail = Abc_MaxFloat(Tail,
            pSet->pFans[k].Constant + pSet->pFans[k].SlewCoeff * Slew);
    return Tail;
}

static float Scm_ManAffElaBaseSlew( Scm_Man_t * p, int iLit )
{
    int iObj = Abc_Lit2Var(iLit), c = Abc_LitIsCompl(iLit);
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    Scm_Mat_t * pM;
    Scm_AffMatch_t Match;
    if ( iObj == 0 || (Gia_ObjIsCi(pObj) && !c) ) return 0.0f;
    pM = Scm_ObjMatchBest(p, iObj, c);
    if ( !pM->fCompl && Scm_ObjCutSetId(p, iObj) == 0 ) return 0.0f;
    if ( !pM->fCompl && Scm_ManCell(p, pM->Gate)->nFanins == 0 )
        return 0.0f;
    memset(&Match, 0, sizeof(Match));
    Match.M.Gate = pM->fCompl ? p->pCells[3].Id : pM->Gate;
    return Scm_ManAffCellSlew(p, &Match,
        Vec_FltEntry(&p->vPaperLiveLoads, iLit));
}

static Scm_RfPair_t Scm_ManAffElaBaseSlewRf( Scm_Man_t * p, int iLit )
{
    int iObj = Abc_Lit2Var(iLit), c = Abc_LitIsCompl(iLit);
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    Scm_Mat_t * pM;
    Scm_RfPair_t Zero = {{0.0f, 0.0f}};
    if ( iObj == 0 || (Gia_ObjIsCi(pObj) && !c) ) return Zero;
    pM = Scm_ObjMatchBest(p, iObj, c);
    if ( !pM->fCompl && Scm_ObjCutSetId(p, iObj) == 0 ) return Zero;
    if ( !pM->fCompl && Scm_ManCell(p, pM->Gate)->nFanins == 0 ) return Zero;
    return Scm_ManRfCellSlew(p,
        pM->fCompl ? p->pCells + 3 : Scm_ManCell(p, pM->Gate),
        Scm_ManRfLoad(p, iLit));
}

static void Scm_ManAffElaTailSortFast( Scm_AffElaCtx_t * pCtx )
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

static void Scm_ManAffElaRfTailAddArc( Scm_RfFanSet_t * pSet,
    Scm_LinArc_t * pArc, Scm_RfPair_t Load, Scm_RfPair_t ParentTail )
{
    Scm_RfFan_t Fan;
    int iOut;
    if ( pArc->TimingSense == sc_ts_Pos || pArc->TimingSense == sc_ts_Non )
    {
        memset(&Fan, 0, sizeof(Fan));
        for ( iOut = NF_RF_FALL; iOut <= NF_RF_RISE; iOut++ )
        {
            Fan.Valid[iOut] = 1;
            Fan.Constant[iOut] = pArc->RfDelay0[iOut] +
                pArc->RfDelayLoad[iOut] * Load.Value[iOut] + ParentTail.Value[iOut];
            Fan.SlewCoeff[iOut] = pArc->RfDelaySlew[iOut];
        }
        Scm_RfFanPush(pSet, Fan);
    }
    if ( pArc->TimingSense == sc_ts_Neg || pArc->TimingSense == sc_ts_Non )
    {
        memset(&Fan, 0, sizeof(Fan));
        for ( iOut = NF_RF_FALL; iOut <= NF_RF_RISE; iOut++ )
        {
            int iIn = !iOut;
            Fan.Valid[iIn] = 1;
            Fan.Constant[iIn] = pArc->RfDelay0[iOut] +
                pArc->RfDelayLoad[iOut] * Load.Value[iOut] + ParentTail.Value[iOut];
            Fan.SlewCoeff[iIn] = pArc->RfDelaySlew[iOut];
        }
        Scm_RfFanPush(pSet, Fan);
    }
}

static int Scm_ManAffElaTailBuildObjRf( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iObj )
{
    int Pass, c, j;
    for ( Pass = 1; Pass >= 0; Pass-- )
        for ( c = 0; c < 2; c++ )
        {
            Scm_RfFanSet_t * pLines;
            Scm_AffElaFanSet_t * pFans;
            int iLit = Abc_Var2Lit(iObj, c);
            if ( pCtx->pTailSeen[iLit] != pCtx->TailEpoch ||
                 pCtx->pTailValid[iLit] ||
                 (Scm_ManAffElaOrderKey(p, iLit) & 1) != Pass ) continue;
            pLines = pCtx->pTailLinesRf + iLit;
            pLines->nFans = 0;
            if ( pCtx->pIsPo[iLit] )
            {
                Scm_RfFan_t Fan;
                memset(&Fan, 0, sizeof(Fan));
                Fan.Valid[0] = Fan.Valid[1] = 1;
                Scm_RfFanPush(pLines, Fan);
            }
            pFans = pCtx->pFans + iLit;
            for ( j = 0; j < pFans->nRoots; j++ )
            {
                int iFanLit = pFans->pRoots[j];
                Scm_Mat_t * pM = Scm_ObjMatchBest(p,
                    Abc_Lit2Var(iFanLit), Abc_LitIsCompl(iFanLit));
                Mio_Cell2_t * pCell = pM->fCompl ? p->pCells + 3 :
                    Scm_ManCell(p, pM->Gate);
                Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoadRf(p, pCell, pFans->pPins[j], Scm_ManRfLoad(p, iFanLit), &Temp);
                if ( !pCtx->pTailValid[iFanLit] || pArc == NULL ||
                     !pArc->fValid ) return 0;
                if ( pCtx->pTailAtBaseSlewRf[iFanLit].Value[0] == -FLT_MAX &&
                     pCtx->pTailAtBaseSlewRf[iFanLit].Value[1] == -FLT_MAX )
                    continue;
                Scm_ManAffElaRfTailAddArc(pLines, pArc,
                    Scm_ManRfLoad(p, iFanLit),
                    pCtx->pTailAtBaseSlewRf[iFanLit]);
            }
            pCtx->pTailAtBaseSlewRf[iLit] = Scm_ManRfTailLinesEval(pLines,
                Scm_ManAffElaBaseSlewRf(p, iLit));
            pCtx->pTailValid[iLit] = 1;
        }
    return 1;
}

static int Scm_ManAffElaTailBuildObj( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iObj )
{
    int Pass, c, j;
    if ( pCtx->fRiseFall )
        return Scm_ManAffElaTailBuildObjRf(p, pCtx, iObj);
    /* At one object an inverter tail depends on its direct source phase,
       so reverse timing order is inverter first and direct phase second. */
    for ( Pass = 1; Pass >= 0; Pass-- )
        for ( c = 0; c < 2; c++ )
        {
            Scm_AffFanSet_t * pLines;
            Scm_AffElaFanSet_t * pFans;
            Scm_AffFan_t Fan;
            int iLit = Abc_Var2Lit(iObj, c);
            if ( pCtx->pTailSeen[iLit] != pCtx->TailEpoch ||
                 pCtx->pTailValid[iLit] ||
                 (Scm_ManAffElaOrderKey(p, iLit) & 1) != Pass ) continue;
            pLines = pCtx->pTailLines + iLit;
            pLines->nFans = 0;
            if ( pCtx->pIsPo[iLit] )
            {
                Fan.Constant = Fan.SlewCoeff = 0.0f;
                Scm_AffFanPush(pLines, Fan);
            }
            pFans = pCtx->pFans + iLit;
            for ( j = 0; j < pFans->nRoots; j++ )
            {
                int iFanLit = pFans->pRoots[j];
                Scm_Mat_t * pM = Scm_ObjMatchBest(p,
                    Abc_Lit2Var(iFanLit), Abc_LitIsCompl(iFanLit));
                Mio_Cell2_t * pCell = pM->fCompl ? p->pCells + 3 :
                    Scm_ManCell(p, pM->Gate);
                Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoad(p, pCell,
                    pFans->pPins[j], Vec_FltEntry(&p->vPaperLiveLoads, iFanLit), &Temp);
                if ( !pCtx->pTailValid[iFanLit] || pArc == NULL ||
                     !pArc->fValid ) return 0;
                if ( pCtx->pTailAtBaseSlew[iFanLit] == -FLT_MAX )
                    continue;
                Fan.Constant = pArc->Delay0 + pArc->DelayLoad *
                    Vec_FltEntry(&p->vPaperLiveLoads, iFanLit) +
                    pCtx->pTailAtBaseSlew[iFanLit];
                Fan.SlewCoeff = pArc->DelaySlew;
                Scm_AffFanPush(pLines, Fan);
            }
            pCtx->pTailAtBaseSlew[iLit] =
                Scm_ManAffElaTailLinesEval(pLines,
                    Scm_ManAffElaBaseSlew(p, iLit));
            pCtx->pTailValid[iLit] = 1;
        }
    return 1;
}

static int Scm_ManAffElaTailBuild( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iStartLit )
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
        Scm_AffElaFanSet_t * pFans;
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
    Scm_ManAffElaTailSortFast(pCtx);
    /* Fanout edges increase AIG IDs.  At one ID an inverter's tail must
       precede the direct phase's tail, the reverse of forward STA order. */
    for ( i = 0; i < Vec_IntSize(pCtx->vTailWork); )
    {
        iObj = Abc_Lit2Var(Vec_IntEntry(pCtx->vTailWork, i));
        if ( !Scm_ManAffElaTailBuildObj(p, pCtx, iObj) ) return 0;
        while ( i < Vec_IntSize(pCtx->vTailWork) &&
                Abc_Lit2Var(Vec_IntEntry(pCtx->vTailWork, i)) == iObj )
            i++;
    }
    return pCtx->pTailValid[iStartLit];
}

static int Scm_ManAffElaTailRefreshBase( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iRootLit )
{
    Scm_AffFanSet_t * pLines = pCtx->pTailLines + iRootLit;
    float Tail;
    if ( !pCtx->pTailValid[iRootLit] || pLines->nFans == 0 )
    {
        if ( !pCtx->fRiseFall ) return 0;
    }
    if ( pCtx->fRiseFall )
    {
        Scm_RfFanSet_t * pLinesRf = pCtx->pTailLinesRf + iRootLit;
        Scm_RfPair_t TailRf;
        if ( !pCtx->pTailValid[iRootLit] || pLinesRf->nFans == 0 ) return 0;
        TailRf = Scm_ManRfTailLinesEval(pLinesRf,
            Scm_ManAffElaBaseSlewRf(p, iRootLit));
        if ( (TailRf.Value[0] == -FLT_MAX && TailRf.Value[1] == -FLT_MAX) ||
             !isfinite(TailRf.Value[0]) || !isfinite(TailRf.Value[1]) )
            return 0;
        pCtx->pTailAtBaseSlewRf[iRootLit] = TailRf;
        return 1;
    }
    Tail = Scm_ManAffElaTailLinesEval(pLines,
        Scm_ManAffElaBaseSlew(p, iRootLit));
    if ( Tail == -FLT_MAX || !isfinite(Tail) )
        return 0;
    pCtx->pTailAtBaseSlew[iRootLit] = Tail;
    return 1;
}

static void Scm_ManAffElaTailInvalidate( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, Vec_Int_t * vSeeds, int iSkipLit )
{
    int i, iLit, iVar, fCompl, k, * pCut;
    /* The mapper retains accumulated required-time bounds.
       The reverse sweep tightens each selected gate's cut inputs once,
       instead of invalidating its entire transitive fanin cone per trial.
       Side-load/slew effects remain approximate, not an exact bound. */
    if ( 12 && !pCtx->fLiveTail ) return;
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
        pM = Scm_ObjMatchBest(p, iObj, c);
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

static int Scm_ManAffElaConeCollect( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iRootLit, Scm_Mat_t * pCandidate )
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
        pM = iLit == iRootLit ? pCandidate : Scm_ObjMatchD(p, iObj, c);
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
    /* An old shared leaf may lose its old root fanout even when the trial
       candidate does not reuse it.  Its external paths still need a check. */
    Vec_IntForEachEntry(pCtx->vOldSeeds, iLit, i)
        if ( iLit != iRootLit &&
             pCtx->pConeSeen[iLit] != pCtx->ConeEpoch &&
             Scm_ObjMapRefNum(p, Abc_Lit2Var(iLit),
                 Abc_LitIsCompl(iLit)) )
        {
            pCtx->pConeSeen[iLit] = pCtx->ConeEpoch;
            Vec_IntPush(pCtx->vBoundary, iLit);
        }
    /* Build the root residual tail now.  Boundary tails are constructed
       lazily during timing, after a root rejection has been ruled out. */
    if ( !Scm_ManAffElaTailBuild(p, pCtx, iRootLit) ||
         (pCtx->fRiseFall ? pCtx->pTailLinesRf[iRootLit].nFans == 0 :
                            pCtx->pTailLines[iRootLit].nFans == 0) ) return 0;
    return 1;
}

static float Scm_ManAffElaBoundaryPriority( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iLit )
{
    float Arrival, Slew, Tail = -FLT_MAX;
    if ( pCtx->fRiseFall )
    {
        Scm_RfPair_t ArrivalRf, SlewRf, TailRf;
        if ( !Scm_ManAffElaReadStateRf(p, pCtx, iLit,
                &ArrivalRf, &SlewRf) ) return -FLT_MAX;
        if ( pCtx->pTailLinesRf[iLit].nFans )
            TailRf = Scm_ManRfTailLinesEval(pCtx->pTailLinesRf + iLit,
                SlewRf);
        else
        {
            float ScalarTail = Scm_ManAffTail(p, iLit,
                Scm_ManRfPairMax(SlewRf), NULL);
            /* Boundary order affects work only; feasibility below builds
               and checks the exact paired residual tail.  Until that lazy
               tail exists, use the deterministic scalar tail solely as a
               priority estimate rather than reading an uninitialized pair. */
            return Scm_ManRfPairMax(ArrivalRf) +
                (ScalarTail == -FLT_MAX ? 0.0f : ScalarTail);
        }
        return Abc_MaxFloat(ArrivalRf.Value[0] + TailRf.Value[0],
            ArrivalRf.Value[1] + TailRf.Value[1]);
    }
    if ( !Scm_ManAffElaReadState(p, pCtx, iLit, &Arrival, &Slew) )
        return -FLT_MAX;
    if ( pCtx->pTailLines[iLit].nFans )
        Tail = Scm_ManAffElaTailLinesEval(pCtx->pTailLines + iLit, Slew);
    if ( Tail == -FLT_MAX )
        Tail = Scm_ManAffTail(p, iLit, Slew, NULL);
    return Arrival + (Tail == -FLT_MAX ? 0.0f : Tail);
}

static void Scm_ManAffElaBoundaryOrder( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx )
{
    int i, j, k, Temp, nSize = Vec_IntSize(pCtx->vBoundary);
    int * pArray = Vec_IntArray(pCtx->vBoundary);
    float * pPriorities;
    /* Timing state is immutable during ordering. Evaluate each priority
       once, retaining the original comparison and tie order exactly. */
    Vec_FltGrow(pCtx->vBoundaryPriorities, nSize);
    pPriorities = Vec_FltArray(pCtx->vBoundaryPriorities);
    for ( i = 0; i < nSize; i++ )
        pPriorities[i] = Scm_ManAffElaBoundaryPriority(p, pCtx, pArray[i]);
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

static int Scm_ManAffElaTimeTailRf( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iRootLit, float Target, float * pDelay )
{
    int i, iLit;
    int fOkay = 1, fResidualRemoved = 0;
    word Removed = 0;
    float Delay = 0.0f;
    Scm_RfPair_t Arrival, Slew, Tail;
    /* Load changes can reach another boundary through retained nodes.
       Re-time their selected fanout closure, not only the explicit cone.
       The reverse sweep needs arrivals only up to this root; residual
       tails represent the remaining paths to outputs. */
    if ( !Scm_ManAffElaTimeLocal(p, pCtx, Abc_Lit2Var(iRootLit)) )
        return 0;
    if ( !Scm_ManAffElaReadStateRf(p, pCtx, iRootLit,
            &Arrival, &Slew) ) return 0;
    Tail = Scm_ManRfTailLinesEval(pCtx->pTailLinesRf + iRootLit, Slew);
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
        Scm_ManAffElaBoundaryOrder(p, pCtx);
    if ( Vec_IntSize(pCtx->vBoundary) && 12 != 12 )
    {
        Scm_Mat_t * pCandidate = Scm_ObjMatchD(p,
            Abc_Lit2Var(iRootLit), Abc_LitIsCompl(iRootLit));
        Removed = Scm_ManAffElaDerefRec(p, pCtx, Abc_Lit2Var(iRootLit),
            Abc_LitIsCompl(iRootLit), pCandidate);
        fResidualRemoved = 1;
    }
    Vec_IntForEachEntry(pCtx->vBoundary, iLit, i)
    {
        if ( !Scm_ManAffElaTailBuild(p, pCtx, iLit) ||
             pCtx->pTailLinesRf[iLit].nFans == 0 )
        {
            fOkay = 0;
            break;
        }
        if ( !Scm_ManAffElaReadStateRf(p, pCtx, iLit,
                &Arrival, &Slew) )
        {
            fOkay = 0;
            break;
        }
        Tail = Scm_ManRfTailLinesEval(pCtx->pTailLinesRf + iLit, Slew);
        if ( Tail.Value[0] != -FLT_MAX )
            Delay = Abc_MaxFloat(Delay, Arrival.Value[0] + Tail.Value[0]);
        if ( Tail.Value[1] != -FLT_MAX )
            Delay = Abc_MaxFloat(Delay, Arrival.Value[1] + Tail.Value[1]);
        if ( Delay > Target + 1.0e-3f ) break;
    }
    if ( fResidualRemoved )
    {
        Scm_Mat_t * pCandidate = Scm_ObjMatchD(p,
            Abc_Lit2Var(iRootLit), Abc_LitIsCompl(iRootLit));
        word Restored = Scm_ManAffElaRefRec(p, pCtx,
            Abc_Lit2Var(iRootLit), Abc_LitIsCompl(iRootLit), pCandidate);
        (void)Restored;
        assert(Restored == Removed);
        if ( pCtx->fError ) fOkay = 0;
    }
    *pDelay = Delay;
    return fOkay && isfinite(Delay);
}

static int Scm_ManAffElaTimeTail( Scm_Man_t * p, Scm_AffElaCtx_t * pCtx,
    int iRootLit, float Target, float * pDelay )
{
    int i, iLit;
    int fOkay = 1, fResidualRemoved = 0;
    word Removed = 0;
    float Arrival, Slew, Tail, Delay = 0.0f;
    if ( pCtx->fRiseFall )
        return Scm_ManAffElaTimeTailRf(p, pCtx, iRootLit, Target, pDelay);
    /* Load changes can reach another boundary through retained nodes.
       Re-time their selected fanout closure, not only the explicit cone.
       The reverse sweep needs arrivals only up to this root; residual
       tails represent the remaining paths to outputs. */
    if ( !Scm_ManAffElaTimeLocal(p, pCtx, Abc_Lit2Var(iRootLit)) )
        return 0;
    if ( !Scm_ManAffElaReadState(p, pCtx, iRootLit,
            &Arrival, &Slew) ) return 0;
    Tail = Scm_ManAffElaTailLinesEval(pCtx->pTailLines + iRootLit, Slew);
    if ( Tail != -FLT_MAX ) Delay = Arrival + Tail;
    if ( Delay > Target + 1.0e-3f )
    {
        *pDelay = Delay;
        return isfinite(Delay);
    }
    if ( Vec_IntSize(pCtx->vBoundary) > 1 )
        Scm_ManAffElaBoundaryOrder(p, pCtx);
    /* Lazy boundary tails must describe the residual cover, before this
       trial adds its pin loads.  Temporarily remove the already-timed
       candidate, construct only the tails actually queried below, and
       restore the identical transaction before returning to the caller. */
    if ( Vec_IntSize(pCtx->vBoundary) && !12 )
    {
        Scm_Mat_t * pCandidate = Scm_ObjMatchD(p,
            Abc_Lit2Var(iRootLit), Abc_LitIsCompl(iRootLit));
        Removed = Scm_ManAffElaDerefRec(p, pCtx, Abc_Lit2Var(iRootLit),
            Abc_LitIsCompl(iRootLit), pCandidate);
        fResidualRemoved = 1;
    }
    Vec_IntForEachEntry(pCtx->vBoundary, iLit, i)
    {
        if ( !Scm_ManAffElaTailBuild(p, pCtx, iLit) ||
             pCtx->pTailLines[iLit].nFans == 0 )
        {
            fOkay = 0;
            break;
        }
        if ( !Scm_ManAffElaReadState(p, pCtx, iLit,
                &Arrival, &Slew) )
        {
            fOkay = 0;
            break;
        }
        Tail = Scm_ManAffElaTailLinesEval(pCtx->pTailLines + iLit, Slew);
        if ( Tail != -FLT_MAX )
            Delay = Abc_MaxFloat(Delay, Arrival + Tail);
        if ( Delay > Target + 1.0e-3f )
            break;
    }
    if ( fResidualRemoved )
    {
        Scm_Mat_t * pCandidate = Scm_ObjMatchD(p,
            Abc_Lit2Var(iRootLit), Abc_LitIsCompl(iRootLit));
        word Restored = Scm_ManAffElaRefRec(p, pCtx,
            Abc_Lit2Var(iRootLit), Abc_LitIsCompl(iRootLit), pCandidate);
        (void)Restored;
        assert(Restored == Removed);
        if ( pCtx->fError ) fOkay = 0;
    }
    *pDelay = Delay;
    return fOkay && isfinite(Delay);
}

static void Scm_ManAffElaCommitTail( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx )
{
    int i, iLit;
    /* Commit only evaluated literals. Reverse ELA visits fanouts before
       fanins; SCMap's forward repair refreshes each root before proposing
       edits. Retained reconvergent paths may still use cached arrivals.
       The final fitted-model timing walk materializes the complete state. */
    Vec_IntForEachEntry(pCtx->vAffected, iLit, i)
        if ( pCtx->pComputed[iLit] == pCtx->Epoch )
        {
            p->pAffExactArrs[iLit] = pCtx->pTrialArr[iLit];
            p->pAffExactSlews[iLit] = pCtx->pTrialSlew[iLit];
            if ( pCtx->fRiseFall )
            {
                p->pAffExactRfArrs[iLit] = pCtx->pTrialArrRf[iLit];
                p->pAffExactRfSlews[iLit] = pCtx->pTrialSlewRf[iLit];
            }
        }
}

static int Scm_ManAffElaFinishCandidate( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iObj, int c, int fTimed )
{
    if ( !fTimed && !Scm_ManAffElaTimeLocal(p, pCtx, iObj) )
        pCtx->fError = 1;
    else
        Scm_ManAffElaCommitTail(p, pCtx);
    if ( pCtx->fError || !Scm_ManAffElaTailRefreshBase(p, pCtx,
            Abc_Var2Lit(iObj, c)) )
    {
        pCtx->fError = 1;
        return -1;
    }
    if ( pCtx->pBufferAreas ) Scm_ManAffBufferAreaDelta(p, pCtx, 1);
    return 2;
}

static int Scm_ManAffElaApplyCandidate( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iObj, int c, Scm_AffElaCand_t * pCand )
{
    word Added;
    Vec_IntClear(pCtx->vTrialSeeds);
    Vec_IntAppend(pCtx->vTrialSeeds, pCtx->vOldSeeds);
    pCtx->pCollectSeeds = pCtx->vTrialSeeds;
    Added = Scm_ManAffElaRefRec(p, pCtx, iObj, c, &pCand->M);
    pCtx->pCollectSeeds = NULL;
    assert(Added == pCand->Area);
    *Scm_ObjMatchD(p, iObj, c) = pCand->M;
    if ( pCtx->fError ) return -1;
    return Scm_ManAffElaFinishCandidate(p, pCtx, iObj, c, 0);
}

static int Scm_ManAffElaTryCandidate( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iObj, int c, Scm_Mat_t * pOld,
    Scm_AffElaCand_t * pCand, float Target, int fCommit, float * pDelay )
{
    Scm_Mat_t * pSelected = Scm_ObjMatchD(p, iObj, c);
    Scm_Mat_t Candidate = pCand->M;
    word Added, Removed;
    int fTimingOkay;
    *pDelay = FLT_MAX;
    if ( pCtx && !Scm_ManAffElaConeCollect(p, pCtx,
            Abc_Var2Lit(iObj, c), &Candidate) )
        return -1;
    if ( pCtx )
    {
        Vec_IntClear(pCtx->vTrialSeeds);
        Vec_IntAppend(pCtx->vTrialSeeds, pCtx->vOldSeeds);
        pCtx->pCollectSeeds = pCtx->vTrialSeeds;
        Added = Scm_ManAffElaRefRec(p, pCtx, iObj, c, &Candidate);
        pCtx->pCollectSeeds = NULL;
    }
    else
        Added = Scm_MatchRef_rec(p, iObj, c, &Candidate,
            SCL_INFINITY, NULL);
    assert(Added == pCand->Area);
    *pSelected = Candidate;
#ifdef SCM_RF_ELA_LOAD_VERIFY
    SCM_RF_ELA_LOAD_VERIFY(p);
#endif
    fTimingOkay = (pCtx && pCtx->pBufferAreas &&
        (double)Added + Scm_ManAffBufferAreaDelta(p, pCtx, 0) >
            (double)pCtx->BufferFreed + 1.0e-3) ? 0 : pCtx ?
        Scm_ManAffElaTimeTail(p, pCtx, Abc_Var2Lit(iObj, c),
            Target, pDelay) : Scm_ManAffElaTimeCover(p);
#ifdef SCM_RF_ELA_LOAD_VERIFY
    SCM_RF_ELA_LOAD_VERIFY(p);
#endif
    if ( !pCtx )
        *pDelay = p->AffExactDelay;
#ifdef SCM_AFF_ELA_VERIFY
    SCM_AFF_ELA_VERIFY(p, pCtx, fTimingOkay, Target, *pDelay);
#endif
    if ( fTimingOkay && *pDelay <= Target + 1.0e-3f && fCommit )
    {
        if ( !pCtx )
            return 2;
        return Scm_ManAffElaFinishCandidate(p, pCtx, iObj, c, 1);
    }
    *pSelected = *pOld;
    Removed = pCtx ? Scm_ManAffElaDerefRec(p, pCtx,
        iObj, c, &Candidate) : Scm_MatchDeref_rec(p, iObj, c, &Candidate);
    assert(Removed == Added);
    if ( pCtx && pCtx->fError )
        return -1;
    return fTimingOkay && *pDelay <= Target + 1.0e-3f;
}

static void Scm_ManAffElaTightenInputs( Scm_Man_t * p,
    Scm_AffElaCtx_t * pCtx, int iObj )
{
    int Pass, c, k, v, phase;
    /* Each fanout has settled before its cut leaves are visited.  Retain
       the round-start constraints and add the chosen gate's current one.
       Stale old edges can overconstrain recovery, but deleting an edge
       must not silently relax a still-shared input's required time. */
    for ( Pass = 1; Pass >= 0; Pass-- )
        for ( c = 0; c < 2; c++ )
        {
            int Lit = Abc_Var2Lit(iObj, c), * pCut;
            Scm_Mat_t * pM;
            Mio_Cell2_t * pCell;
            float Tail, Load;
            if ( !Scm_ObjMapRefNum(p, iObj, c) ) continue;
            pM = Scm_ObjMatchD(p, iObj, c);
            if ( (int)pM->fCompl != Pass ) continue;
            Tail = Scm_ManAffElaTailLinesEval(pCtx->pTailLines + Lit,
                p->pAffExactSlews[Lit]);
            if ( Tail == -FLT_MAX ) continue;
            Load = Vec_FltEntry(&p->vPaperLiveLoads, Lit);
            pCell = pM->fCompl ? p->pCells + 3 : Scm_ManCell(p, pM->Gate);
            pCut = pM->fCompl ? NULL :
                Scm_CutFromHandle(Scm_ObjCutSet(p, iObj), pM->CutH);
            for ( k = 0; k < (int)pCell->nFanins; k++ )
            {
                Scm_LinArc_t Temp, * pArc = Scm_ManAffArcAtLoad(p, pCell, k, Load, &Temp);
                Scm_AffFan_t Fan;
                int Child;
                if ( pM->fCompl ) Child = Lit ^ 1;
                else
                {
                    v = Scm_CutLeaves(pCut)[Scm_CfgVar(pM->Cfg, k)];
                    phase = Scm_CfgCompl(pM->Cfg, k);
                    Child = Abc_Var2Lit(v, phase);
                }
                Fan.Constant = Tail + pArc->Delay0 + pArc->DelayLoad * Load;
                Fan.SlewCoeff = pArc->DelaySlew;
                Scm_AffFanPush(pCtx->pTailLines + Child, Fan);
                pCtx->pTailValid[Child] = 1;
                pCtx->pTailAtBaseSlew[Child] = Scm_ManAffElaTailLinesEval(
                    pCtx->pTailLines + Child, p->pAffExactSlews[Child]);
            }
        }
}

#include "giaScmapSeed.h"
#include "giaScmapRefine.h"

static void Scm_ManSetDefaultPars(Scm_Par_t *pPars) { memset(pPars, 0, sizeof(*pPars));
 pPars->nLutSize=6;
 pPars->nCutNum=16;

 pPars->nPaperAffineElaCritical=80;

}

#include "giaScmapQuality.h"

static Gia_Man_t * Scm_ManPerformMappingInt( Gia_Man_t * pGia, Scm_Par_t * pPars )
{
    Gia_Man_t *pNew = NULL;
    Scm_Man_t *p;
    if (pGia->pManTime || pGia->vInArrs || Scl_ConIsRunning()) {
        Abc_Print(-1, "&scmap requires an unboxed AIG without explicit input timing.\n");
        return NULL;
    }
    p = Scm_StoCreate(pGia, pPars);
    if (!p) return NULL;
    pGia->iFirstNonPiId = Gia_ManCiNum(pGia);
    pGia->iFirstPoId = 0;
    pGia->iFirstAndObj = 1 + pGia->iFirstNonPiId;
    pGia->iFirstPoObj = Gia_ManObjNum(pGia) - Gia_ManCoNum(pGia);
    Scm_ManPrintInit(p);
    Scm_ManComputeCuts(p);
    Scm_ManPrintQuit(p);
    p->Iter = 0;
    int nLits = 2 * Gia_ManObjNum(p->pGia), nObjs = Gia_ManObjNum(p->pGia);
    int m, Best = -1, fOk = 1;
    Scm_Obj_t * pSaveObjs[2] = {0};
    int * pSaveRefs[2] = {0};
    float * pSaveFlow[2] = {0};
    float Delay[2] = {0};
    long long Area[2] = {0};
    float * pFlow0 = ABC_ALLOC(float, nLits);
    memcpy(pFlow0, Vec_FltArray(&p->vFlowRefs), sizeof(float) * nLits);
    p->pAffExactRfArrs = ABC_CALLOC(Scm_RfPair_t, nLits);
    p->pAffExactRfSlews = ABC_CALLOC(Scm_RfPair_t, nLits);
    if ( pPars->fQuality )
    {
        assert(p->pAllRfLoads == NULL);
        p->pAllRfLoads = ABC_CALLOC(Scm_RfPair_t, nLits);
    }
    for ( m = 0; fOk && m < 2; m++ )
    {
        if ( m > 0 )
        {
            Vec_IntFill(&p->vMapRefs, nLits, 0);
            memcpy(Vec_FltArray(&p->vFlowRefs), pFlow0, sizeof(float) * nLits);
            memset(p->pNfObjs, 0, sizeof(Scm_Obj_t) * nObjs);
            Scm_ObjMatchD(p, 0, 0)->Gate = 0;
            Scm_ObjMatchD(p, 0, 1)->Gate = 1;
        }
        pPars->nSeedMode = m;
        pPars->fUseRiseFallAll = 0;
        if ( !Scm_ManAffPairedSeed(p) ) { fOk = 0; break; }
        pPars->fUseRiseFallAll = 1;
        if ( !Scm_ManAffElaTimeCover(p) ) { fOk = 0; break; }
        Delay[m] = p->AffExactDelay;
        Area[m] = Df_Area(p);
        if ( pPars->fVerbose )
            printf("SCMAP_SEED mode=%d delay=%.6f area=%lld\n", m, Delay[m], Area[m]);
        pSaveObjs[m] = ABC_ALLOC(Scm_Obj_t, nObjs);
        memcpy(pSaveObjs[m], p->pNfObjs, sizeof(Scm_Obj_t) * nObjs);
        pSaveRefs[m] = ABC_ALLOC(int, nLits);
        memcpy(pSaveRefs[m], Vec_IntArray(&p->vMapRefs), sizeof(int) * nLits);
        pSaveFlow[m] = ABC_ALLOC(float, nLits);
        memcpy(pSaveFlow[m], Vec_FltArray(&p->vFlowRefs), sizeof(float) * nLits);
    }
    if ( fOk )
    {
        for ( m = 0; m < 2; m++ )
            if ( Area[m] <= Area[0] && (Best < 0 || Delay[m] < Delay[Best] ||
                 (Delay[m] == Delay[Best] && Area[m] < Area[Best])) ) Best = m;
        if ( Best != 1 )
        {
            memcpy(p->pNfObjs, pSaveObjs[Best], sizeof(Scm_Obj_t) * nObjs);
            memcpy(Vec_IntArray(&p->vMapRefs), pSaveRefs[Best], sizeof(int) * nLits);
            memcpy(Vec_FltArray(&p->vFlowRefs), pSaveFlow[Best], sizeof(float) * nLits);
        }
        pPars->nSeedMode = Best;
        /* Reconstruct the winner's loads/timing before refining its cover. */
        if ( !Scm_ManAffElaTimeCover(p) || !Scm_ManRefineCover(p) ) fOk = 0;
        if ( fOk && pPars->fQuality )
            fOk = Scm_ManSelectSeed(p, pSaveObjs[1-Best], pSaveRefs[1-Best], pSaveFlow[1-Best], 1-Best);
        if ( fOk && pPars->fVerbose )
            printf("SCMAP_SELECTED seed=%d delay=%.3f area=%lld\n", pPars->nSeedMode, p->AffExactDelay, Df_Area(p));
    }
    for ( m = 0; m < 2; m++ )
    {
        ABC_FREE(pSaveObjs[m]); ABC_FREE(pSaveRefs[m]); ABC_FREE(pSaveFlow[m]);
    }
    ABC_FREE(pFlow0);
    pPars->nSeedMode = 0;
    if ( p->fEnvError ) fOk = 0;
    if ( fOk ) pNew = Scm_ManDeriveMapping(p);
    else Abc_Print(-1, "&scmap: seed or cover repair failed.\n");
    pPars->fUseRiseFallAll = 0;
    Scm_StoDelete(p);
    return pNew;
}

static Gia_Man_t * Scm_ManPerformMapping(Gia_Man_t *p, Scm_Par_t *pPars)
{
    Gia_Man_t *pNew = Scm_ManPerformMappingInt(p, pPars);
    if (!pNew) return NULL;
    Gia_ManTransferTiming(pNew, p);
    /* The emitted mapped graph no longer needs choice alternatives. */
    ABC_FREE(pNew->pReprs);
    ABC_FREE(pNew->pNexts);
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

Gia_Man_t * Gia_ManScmap(Gia_Man_t *pGia, int fVerbose, int fVeryVerbose)
{
    Scm_Par_t Pars;
    Scm_ManSetDefaultPars(&Pars);
    Pars.fVerbose = fVerbose;
    Pars.fVeryVerbose = fVeryVerbose;
    return Scm_ManPerformMapping(pGia, &Pars);
}

/**Function*************************************************************

  Synopsis    [Maps with refined seeds and electrically scored windows.]

  Description [The input is retained when a distinct manager is returned.
  Seed selection sizes private networks; the returned cover is unsized.]

  SideEffects [Uses the input scratch values and mapping fields.]

  SeeAlso     [Gia_ManScmap]

***********************************************************************/
Gia_Man_t * Gia_ManScmapQuality( Gia_Man_t * pGia, int fVerbose, int fVeryVerbose )
{
    Scm_Par_t Pars;
    Gia_Man_t * pMapped, * pNew;
    if ( pGia == NULL || !Gia_ManCoNum(pGia) || Gia_ManRegNum(pGia) || pGia->pManTime || Gia_ManBufNum(pGia) ||
         pGia->vInArrs || pGia->vOutReqs || pGia->vCiArrs || pGia->vCoReqs || Scl_ConIsRunning() )
    {
        Abc_Print(-1, "&scmap -q requires outputs and an unboxed combinational AIG without explicit timing.\n");
        return NULL;
    }
    if ( !Abc_FrameReadLibGen() || !Abc_FrameReadLibScl() )
    {
        Abc_Print(-1, "&scmap -q requires a Liberty library loaded with read_lib.\n");
        return NULL;
    }
    Scm_ManSetDefaultPars(&Pars);
    Pars.fQuality = 1;
    Pars.fVerbose = fVerbose;
    Pars.fVeryVerbose = fVeryVerbose;
    pMapped = Scm_ManPerformMapping(pGia, &Pars);
    if ( pMapped == NULL ) return NULL;
    pNew = Scm_ManWindowImprove(pMapped, fVerbose, fVeryVerbose);
    if ( pMapped != pGia && pMapped != pNew ) Gia_ManStop(pMapped);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Adds bounded full-flow lookahead to quality mapping.]

  Description [The returned cover is unsized. Trials are measured after a
  fixed MFS/buffering/sizing flow on private networks. The 1% area allowance
  and nonincreasing delay apply to that flow, not arbitrary postprocessing.
  Zero trials is identical to Gia_ManScmapQuality. The input is not freed.]

  SideEffects [Uses the input scratch values and mapping fields.]

  SeeAlso     [Gia_ManScmapQuality]

***********************************************************************/
Gia_Man_t * Gia_ManScmapLookahead( Gia_Man_t * pGia, int nTrials, int fVerbose, int fVeryVerbose )
{
    Gia_Man_t * pMapped, * pNew;
    if ( nTrials < 0 ) return NULL;
    pMapped = Gia_ManScmapQuality(pGia, fVerbose, fVeryVerbose);
    if ( pMapped == NULL || nTrials == 0 ) return pMapped;
    // Trivial covers have no window replacements; MFS requires primary inputs.
    if ( !Gia_ManCiNum(pMapped) || !Gia_ManAndNum(pMapped) ) return pMapped;
    pNew = Scm_ManWindowLookahead(pMapped, nTrials, fVerbose, fVeryVerbose);
    if ( pMapped != pGia && pMapped != pNew ) Gia_ManStop(pMapped);
    return pNew;
}

ABC_NAMESPACE_IMPL_END
