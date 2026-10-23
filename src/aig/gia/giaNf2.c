/**CFile****************************************************************

  FileName    [giaNf2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Compact standard-cell mapping.]

  Synopsis    [Library-guided standard-cell mapping on the GIA.]

  Description [Library patterns generate shared cut templates and predecoded
  cell matches.  Physical nodes retain only their template and leaf bindings.
  Exact cost-context reuse accelerates repeated cones; bounded reference
  trials recover area without rebuilding or mutating each trial cover.

  The two cached configurations contain library and structural data only.  Arrivals,
  reference counts, and cached mapping decisions belong to one invocation.
  Proved choices carry library patterns through compact child bindings.
  Oversized libraries use the reference mapper.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaNf2.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <float.h>
#include <limits.h>
#include "gia.h"
#include "map/amap/amap.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"
#include "misc/util/utilTruth.h"
#include "misc/extra/extra.h"
#include "base/main/main.h"
#include "misc/vec/vecMem.h"
#include "misc/vec/vecWec.h"
#include "opt/dau/dau.h"
#include "misc/util/utilNam.h"
#include "map/scl/sclCon.h"
#include "misc/tim/tim.h"


ABC_NAMESPACE_IMPL_START

extern void Gia_ManTransferCellMapping( Gia_Man_t * p, Gia_Man_t * pGia );

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define NF2_LEAF_MAX  6
#define NF2_CUT_MAX  128
#define NF2_NO_LEAF  31
#define NF2_EPSILON  0.001
#define NF2_DIRECT_PROGRAM_MAX 16
#define NF2_CONTEXT_MAX 8192
#define NF2_BANK_HASH_SIZE (1 << 16)
#define NF2_CHOICE_BITS 12
#define NF2_CHOICE_MASK ((1 << NF2_CHOICE_BITS) - 1)

typedef struct Nf2_Cut_t_ Nf2_Cut_t;
struct Nf2_Cut_t_
{
    word            Sign;           // signature
    unsigned        iFunc   : 26;   // function
    unsigned        Useless :  1;   // function
    unsigned        nLeaves :  5;   // leaf number (NF2_NO_LEAF)
    int             pLeaves[NF2_LEAF_MAX+1]; // leaves
};
typedef struct Nf2_Cfg_t_ Nf2_Cfg_t;
struct Nf2_Cfg_t_
{
    unsigned        fCompl  :  1;   // complemented
    unsigned        Phase   :  7;   // match phase
    unsigned        Perm    : 24;   // match permutation
};
typedef struct Nf2_Mat_t_ Nf2_Mat_t;
struct Nf2_Mat_t_
{
    unsigned        Gate    : 20;   // gate
    unsigned        CutH    : 10;   // cut handle
    unsigned        fCompl  :  1;   // complemented
    unsigned        fBest   :  1;   // best cut
    Nf2_Cfg_t        Cfg;            // input literals
    int             D;              // delay
    float           F;              // area
};
typedef struct Nf2_Obj_t_ Nf2_Obj_t;
struct Nf2_Obj_t_
{
    Nf2_Mat_t        M[2][2];         // del/area (2x)
};
typedef struct Nf2_Ptc_t_ Nf2_Ptc_t;
struct Nf2_Ptc_t_ { word Code; unsigned Rule, Result; };
typedef struct Nf2_Bank_t_ Nf2_Bank_t;
typedef struct Nf2_Template_t_ Nf2_Template_t;
typedef struct Nf2_Prog_t_ { int Gate,Config; unsigned short CutH,Pins[6]; unsigned char Pol,nFans,Phase,NeedArea,NeedDelay; } Nf2_Prog_t;
typedef struct Nf2_Value_t_ { int D,A; float F,G; } Nf2_Value_t;
typedef struct Nf2_Last_t_ { int Root,Round,Req[2],Template; unsigned Hash; float RawF[4]; } Nf2_Last_t;
// Ownership of compiled library data moves as one unit between invocations.
typedef struct Nf2_Bin_t_ { int Key0,Key1,Kind,Bank; } Nf2_Bin_t;
typedef struct Nf2_Data_t_
{
    Vec_Mem_t * vTtMem;
    Vec_Wec_t * vTt2Match, * vMatchFlags;
    unsigned short * pPatternAnd, * pPatternXor;
    Nf2_Ptc_t * pPatternTruth;
    int nPatternLits;
    Nf2_Bank_t ** pBanks;
    Nf2_Bin_t * pBankBins;
    int * pChoiceBins;
    int * pBankContent, nBankBins, nBankHashSize, nBanks, nBankCap;
    Nf2_Template_t ** pTemplates;
    int * pTemplateBins, nTemplates, nTemplateCap;
    Vec_Ptr_t vPages;
    int iCur;
} Nf2_Data_t;
typedef struct Nf2_Ref_t_ { int Count; unsigned Stamp; } Nf2_Ref_t;
typedef struct Nf2_Man_t_ Nf2_Man_t;
struct Nf2_Man_t_
{
    // user data
    Gia_Man_t *     pGia;           // derived manager
    Tim_Man_t *     pManTim;        // timing manager
    Jf_Par_t *      pPars;          // parameters
    // matching
    Nf2_Data_t      Data;           // reusable library compilation
    Mio_Cell2_t *   pCells;         // library gates
    Amap_PatView_t Patterns;
    unsigned TrialStamp;
    int * pNodeBanks, * pBankValues, nBankValues;
    int * pBindOffsets, * pNodeTemplates;
    Vec_Int_t vBindings, vChoiceValues;
    int * pChoiceOffsets;
    Nf2_Mat_t AreaOriginal; word AreaInitial;
    unsigned * pBindSeen;       // root ID marks unique bindings during import
    word nBindHits,nBindQueries;
    word nSmallEla,nTotalEla;
    Nf2_Last_t * pLast; int nLastCap,nMinPinDelay; word nLastQueries[2],nLastHits[2];
    int             nCells;         // library gate count
    // cut data
    Nf2_Obj_t *      pNfObjs;        // best cuts
    Vec_Int_t       vCutSets;       // cut offsets
    Nf2_Ref_t *     pRefs;          // reference and trial state per literal
    Vec_Flt_t       vFlowRefs;      // flow refs      (2x)
    Vec_Int_t       vRequired;      // required times (2x)
    int             Iter;           // mapping iterations
    int             fUseEla;        // use exact area
    int             nInvs;          // the inverter count
    int             InvDelayI;      // inverter delay
    word            InvAreaW;       // inverter area
    float           InvAreaF;       // inverter area
    // statistics
    abctime         clkStart;       // starting time
    word            nCutsTotal;     // cuts retained over all mapped nodes
};

// Node arrays have fixed sizes for the GIA lifetime; cut handles and binding
// indices are generated by this manager before mapping traversals use them.

static inline Nf2_Cfg_t     Nf2_Int2Cfg( int Int )                                     { union { int x; Nf2_Cfg_t y; } v; v.x = Int; return v.y;           }

static inline Nf2_Obj_t *   Nf2_ManObj( Nf2_Man_t * p, int i )                          { return p->pNfObjs + i;                                           }
static inline Mio_Cell2_t* Nf2_ManCell( Nf2_Man_t * p, int i )                         { return p->pCells + i;                                            }
static inline int *        Nf2_ManCutSet( Nf2_Man_t * p, int i )                       { return (int *)p->Data.vPages.pArray[i >> 16] + (i & 0xFFFF);  }
static inline int          Nf2_ObjCutSetId( Nf2_Man_t * p, int i )                     { return p->vCutSets.pArray[i];                          }
static inline int *        Nf2_ObjCutSet( Nf2_Man_t * p, int i )                       { return Nf2_ManCutSet(p, Nf2_ObjCutSetId(p, i));                    }
static inline int          Nf2_ObjHasCuts( Nf2_Man_t * p, int i )                      { return (int)(p->vCutSets.pArray[i] > 0);                 }

static inline int          Nf2_ObjCutUseless( Nf2_Man_t * p, int TruthId )             { return (int)(TruthId >= Vec_WecSize(p->Data.vTt2Match));              }


static inline int          Nf2_ObjMapRefNum( Nf2_Man_t * p, int i, int c )             { return p->pRefs[Abc_Var2Lit(i,c)].Count;             }
static inline int          Nf2_ObjMapRefInc( Nf2_Man_t * p, int i, int c )             { return p->pRefs[Abc_Var2Lit(i,c)].Count++;       }
static inline int          Nf2_ObjMapRefDec( Nf2_Man_t * p, int i, int c )             { return --p->pRefs[Abc_Var2Lit(i,c)].Count;       }
static inline float        Nf2_ObjFlowRefs( Nf2_Man_t * p, int i, int c )              { return p->vFlowRefs.pArray[Abc_Var2Lit(i,c)];            }
static inline int          Nf2_ObjRequired( Nf2_Man_t * p, int i, int c )              { return p->vRequired.pArray[Abc_Var2Lit(i,c)];            }
static inline void         Nf2_ObjSetRequired( Nf2_Man_t * p,int i, int c, int f )     { p->vRequired.pArray[Abc_Var2Lit(i,c)] = f;           }
static inline void         Nf2_ObjUpdateRequired( Nf2_Man_t * p,int i, int c, int f )  { if (Nf2_ObjRequired(p, i, c) > f) Nf2_ObjSetRequired(p, i, c, f);  }

static inline Nf2_Mat_t *   Nf2_ObjMatchD( Nf2_Man_t * p, int i, int c )                { return &Nf2_ManObj(p, i)->M[c][0];                                }
static inline Nf2_Mat_t *   Nf2_ObjMatchA( Nf2_Man_t * p, int i, int c )                { return &Nf2_ManObj(p, i)->M[c][1];                                }

static inline int          Nf2_CutSize( int * pCut )                                  { return pCut[0] & NF2_NO_LEAF;                                     }
static inline int          Nf2_CutFunc( int * pCut )                                  { return ((unsigned)pCut[0] >> 5);                                 }
static inline int *        Nf2_CutLeaves( int * pCut )                                { return pCut + 1;                                                 }
static inline int          Nf2_CutSetBoth( int n, int f )                             { return n | (f << 5);                                             }

static inline int          Nf2_CutHandle( int * pCutSet, int * pCut )                 { assert( pCut > pCutSet ); return pCut - pCutSet;                 }
static inline int *        Nf2_CutFromHandle( int * pCutSet, int h )                  { assert( h > 0 ); return pCutSet + h;                             }

static inline int          Nf2_CfgVar( Nf2_Cfg_t Cfg, int i )                          { return (Cfg.Perm >> (i<<2)) & 15;                                }
static inline int          Nf2_CfgCompl( Nf2_Cfg_t Cfg, int i )                        { return (Cfg.Phase >> i) & 1;                                     }

#define Nf2_SetForEachCut( pList, pCut, i )                   for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += Nf2_CutSize(pCut) + 1 )
#define Nf2_CutForEachVarCompl( p, Id, pCut, Cfg, iVar, fCompl, i ) \
    for ( i=0, Nf2_PinPerm=(Cfg).Perm, Nf2_PinPhase=(Cfg).Phase, Nf2_PinDirect=Nf2_PinPhase>>6, \
          Nf2_PinCount=Nf2_CutSize(pCut), Nf2_PinFans=Nf2_CutLeaves(pCut), \
          Nf2_PinBinds=(p)->vBindings.pArray+(p)->pBindOffsets[Id]; \
          i<Nf2_PinCount && ((Nf2_PinLit=Nf2_PinDirect?2*(Nf2_PinPerm&15):Nf2_PinFans[Nf2_PinPerm&15]), \
          (iVar=Nf2_PinBinds[Nf2_PinLit>>1]),1) && \
          ((fCompl=(Nf2_PinPhase^Nf2_PinLit)&1),1); \
          i++, Nf2_PinPerm>>=4, Nf2_PinPhase>>=1 )
#define Nf2_CfgForEachVarCompl( Cfg, Size, iVar, fCompl, i )  for ( i = 0; i < Size && ((iVar = Nf2_CfgVar(Cfg, i)), 1) && ((fCompl = Nf2_CfgCompl(Cfg, i)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static void Nf2_PatternStart( Nf2_Man_t * p );
static void Nf2_TemplateStart( Nf2_Man_t * p );
static void Nf2_TemplateStop( Nf2_Man_t * p );
static void Nf2_BankStart( Nf2_Man_t * p );
static void Nf2_BankStop( Nf2_Man_t * p );
static int Nf2_SharedAttach( Nf2_Man_t * p );
static void Nf2_SharedDetach( Nf2_Man_t * p );
static void Nf2_StoDelete( Nf2_Man_t * p );
/**Function*************************************************************

  Synopsis    [Creates mapping state and attaches the compiled library cache.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Nf2_Man_t * Nf2_StoCreate( Gia_Man_t * pGia, Jf_Par_t * pPars, Mio_Library_t * pMio, Amap_Lib_t * pAmap )
{
    extern void Mf_ManSetFlowRefs( Gia_Man_t * p, Vec_Int_t * vRefs );
    Vec_Int_t * vFlowRefs;
    Vec_Mem_t * vTtMem;
    Vec_Wec_t * vTt2Match;
    Mio_Cell2_t * pCells;
    int nCells;
    Nf2_Man_t * p;
    int i, Entry;
    assert( pPars->nCutNum > 1  && pPars->nCutNum <= NF2_CUT_MAX );
    assert( pPars->nLutSize > 1 && pPars->nLutSize <= NF2_LEAF_MAX );
    Mio_LibraryMatchesFetch( pMio, &vTtMem, &vTt2Match, &pCells, &nCells, pPars->fPinFilter, pPars->fPinPerm, pPars->fPinQuick );
    if ( pCells == NULL || nCells < 4 )
        return NULL;
    // create
    p = ABC_CALLOC( Nf2_Man_t, 1 );
    p->clkStart = Abc_Clock();
    p->pGia     = pGia;
    p->pManTim  = (Tim_Man_t *)pGia->pManTime;
    p->pPars    = pPars;
    p->Data.vTtMem = vTtMem; p->Data.vTt2Match = vTt2Match;
    p->pCells = pCells; p->nCells = nCells;
    p->pNfObjs  = ABC_CALLOC( Nf2_Obj_t, Gia_ManObjNum(pGia) );
    p->Data.iCur     = 2;
    // other
    Vec_PtrGrow( &p->Data.vPages, 256 );                                    // cut memory
    p->pRefs=ABC_CALLOC(Nf2_Ref_t,2*(size_t)Gia_ManObjNum(pGia));
    Vec_FltGrow(&p->vFlowRefs,2*Gia_ManObjNum(pGia)); p->vFlowRefs.nSize=2*Gia_ManObjNum(pGia);            // flow refs      (2x)
    Vec_IntGrow(&p->vRequired,2*Gia_ManObjNum(pGia)); p->vRequired.nSize=2*Gia_ManObjNum(pGia); // required times (2x)
    Vec_IntFill( &p->vCutSets,  Gia_ManObjNum(pGia), 0 );              // cut offsets
    // references
    vFlowRefs = Vec_IntAlloc(0);
    Mf_ManSetFlowRefs( pGia, vFlowRefs );
    Vec_IntForEachEntry( vFlowRefs, Entry, i )
    {
        Vec_FltWriteEntry( &p->vFlowRefs, 2*i,   Entry );
        Vec_FltWriteEntry( &p->vFlowRefs, 2*i+1, Entry );
    }
    Vec_IntFree(vFlowRefs);
    if ( Gia_ManHasChoices(pGia) )
    {
        float * Refs=Gia_ManChoiceRefs(pGia);
        for ( i=0; i<Gia_ManObjNum(pGia); i++ )
            p->vFlowRefs.pArray[2*i]=p->vFlowRefs.pArray[2*i+1]=Abc_MaxFloat(1.0f,Refs[i]);
        ABC_FREE(Refs);
    }
    {
        int j;
        p->nMinPinDelay = SCL_INFINITY;
        for ( i=0; i<p->nCells; i++ ) for ( j=0; j<(int)p->pCells[i].nFanins; j++ )
            p->nMinPinDelay=Abc_MinInt(p->nMinPinDelay,p->pCells[i].iDelays[j]);
    }
    p->InvDelayI = p->pCells[3].iDelays[0];
    p->InvAreaW  = p->pCells[3].AreaW;
    p->InvAreaF  = p->pCells[3].AreaF;
    Nf2_ObjMatchD(p, 0, 0)->Gate = 0;
    Nf2_ObjMatchD(p, 0, 1)->Gate = 1;
    Amap_LibReadPatterns( pAmap, &p->Patterns );
    if ( !Nf2_SharedAttach(p) ) { Nf2_PatternStart(p); Nf2_BankStart(p); Nf2_TemplateStart(p); }
    if ( Gia_ManXorNum(pGia) && !p->Data.pPatternXor[0] )
    {
        Abc_Print( -1, "&nf2: this library has no two-input XOR pattern for explicit XOR objects.\n" );
        Nf2_StoDelete(p);
        return NULL;
    }
    ABC_FREE( pGia->pRefs );
    Vec_IntFreeP( &pGia->vCellMapping );
    p->nLastCap=64;
    while ( p->nLastCap<NF2_CONTEXT_MAX && Gia_ManAndNum(pGia)>p->nLastCap/2 ) p->nLastCap*=2;
    p->pLast=ABC_CALLOC(Nf2_Last_t,p->nLastCap);
    p->pBindSeen=ABC_CALLOC(unsigned,Gia_ManObjNum(pGia));
    // prepare cuts
    return p;
}
/**Function*************************************************************

  Synopsis    [Releases per-network state and retains reusable compiled templates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_StoDelete( Nf2_Man_t * p )
{
    Nf2_SharedDetach(p);
    ABC_FREE(p->pRefs);
    ABC_FREE( p->vFlowRefs.pArray );
    ABC_FREE( p->vRequired.pArray );
    ABC_FREE( p->vCutSets.pArray );
    Nf2_TemplateStop(p);
    Nf2_BankStop(p);
    if ( p->pPars->fVerbose ) printf("Binding reuse %lld/%lld\n",(long long)p->nBindHits,(long long)p->nBindQueries);
    if ( p->pPars->fVerbose ) printf("Minimum-size ELA %lld/%lld\n",(long long)p->nSmallEla,(long long)p->nTotalEla);
    if ( p->pPars->fVerbose ) printf("Last context %lld/%lld initial; %lld/%lld later\n",(long long)p->nLastHits[0],(long long)p->nLastQueries[0],(long long)p->nLastHits[1],(long long)p->nLastQueries[1]);
    ABC_FREE(p->pBindSeen);
    ABC_FREE(p->pChoiceOffsets); ABC_FREE(p->vChoiceValues.pArray);
    ABC_FREE(p->pLast);
    ABC_FREE( p->pNfObjs );
    ABC_FREE( p );
}


static inline word Nf2_CutGetSign( int * pLeaves, int nLeaves )
{
    word Sign = 0; int i;
    for ( i = 0; i < nLeaves; i++ )
        Sign |= ((word)1) << (pLeaves[i] & 0x3F);
    return Sign;
}


static inline int Nf2_ManSaveCuts( Nf2_Man_t * p, Nf2_Cut_t ** pCuts, int nCuts )
{
    int i, j, * pPlace, iCur, nInts = 1;
    for ( i = 0; i < nCuts; i++ )
        nInts += pCuts[i]->nLeaves + 1;
    if ( (p->Data.iCur & 0xFFFF) + nInts > 0xFFFF )
        p->Data.iCur = ((p->Data.iCur >> 16) + 1) << 16;
    if ( Vec_PtrSize(&p->Data.vPages) == (p->Data.iCur >> 16) )
        Vec_PtrPush( &p->Data.vPages, ABC_ALLOC(int, (1<<16)) );
    iCur = p->Data.iCur; p->Data.iCur += nInts;
    pPlace = Nf2_ManCutSet( p, iCur );
    *pPlace++ = nCuts;
    for ( i = 0; i < nCuts; i++ )
    {
        *pPlace++ = Nf2_CutSetBoth( pCuts[i]->nLeaves, pCuts[i]->iFunc );
        for ( j = 0; j < (int)pCuts[i]->nLeaves; j++ )
            pPlace[j] = Abc_Var2Lit(pCuts[i]->pLeaves[j], 0);
        pPlace += pCuts[i]->nLeaves;
    }
    return iCur;
}


static inline int Nf2_SetCutIsContainedOrder( Nf2_Cut_t * pBase, Nf2_Cut_t * pCut ) // check if pCut is contained in pBase
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
static inline int Nf2_SetLastCutIsContained( Nf2_Cut_t ** pCuts, int nCuts )
{
    int i;
    // Pattern leaves can contain both a node and its fanins. Equal leaf sets
    // can therefore represent different functions; subset dominance is unsafe.
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[i]->nLeaves == 0 || (pCuts[i]->nLeaves == pCuts[nCuts]->nLeaves && pCuts[i]->iFunc == pCuts[nCuts]->iFunc && pCuts[i]->Sign == pCuts[nCuts]->Sign && Nf2_SetCutIsContainedOrder(pCuts[nCuts], pCuts[i])) )
            return 1;
    return 0;
}
static inline int Nf2_SetLastCutContainsArea( Nf2_Cut_t ** pCuts, int nCuts )
{
    int i, k, fChanges = 0;
    if ( pCuts[nCuts]->nLeaves ) return nCuts;
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[nCuts]->nLeaves < pCuts[i]->nLeaves && (pCuts[nCuts]->Sign & pCuts[i]->Sign) == pCuts[nCuts]->Sign && Nf2_SetCutIsContainedOrder(pCuts[i], pCuts[nCuts]) )
            pCuts[i]->nLeaves = NF2_NO_LEAF, fChanges = 1;
    if ( !fChanges )
        return nCuts;
    for ( i = k = 0; i <= nCuts; i++ )
    {
        if ( pCuts[i]->nLeaves == NF2_NO_LEAF )
            continue;
        if ( k < i )
            ABC_SWAP( Nf2_Cut_t *, pCuts[k], pCuts[i] );
        k++;
    }
    return k - 1;
}


static void Nf2_ManCutMatch( Nf2_Man_t * p, int iObj );
static inline void Nf2_ObjPrepareCi( Nf2_Man_t * p, int iObj, int Time );
static inline void Nf2_ObjPrepareBuf( Nf2_Man_t * p, Gia_Obj_t * pObj );

// Library-guided patterns over the original GIA.
#define NF2_PATTERN_MAX 128
#define NF2_PATTERN_FANS 16

typedef struct Nf2_Pat_t_ Nf2_Pat_t;
struct Nf2_Pat_t_ { int Rule, nFans, Fans[NF2_PATTERN_FANS]; };

static word Nf2_PatternEval_rec( Nf2_Man_t *, int, word *, int * );
/**Function*************************************************************

  Synopsis    [Builds AND and XOR transitions from the Amap library.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_PatternStart( Nf2_Man_t * p )
{
    int i, j, Entry, nRules;
    assert(p->Patterns.pNodes != NULL);
    nRules = p->Patterns.nNodes;
    p->Data.nPatternLits = 2*nRules;
    assert(nRules < 2048);
    p->Data.pPatternAnd = ABC_CALLOC(unsigned short, 4*nRules*nRules);
    p->Data.pPatternXor = ABC_CALLOC(unsigned short, 4*nRules*nRules);
    for ( i = 0; i < 2*nRules; i++ )
    {
        for ( j = 0; (Entry = p->Patterns.pRules[i][j]); j++ ) p->Data.pPatternAnd[i*2*nRules+(Entry&65535)] = (unsigned)Entry >> 16;
        for ( j = 0; (Entry = p->Patterns.pRulesX[i][j]); j++ ) p->Data.pPatternXor[i*2*nRules+(Entry&65535)] = (unsigned)Entry >> 16;
    }
    if ( p->pPars->fVerbose ) printf("Structural patterns = %d\n", nRules);
}


/**Function*************************************************************

  Synopsis    [Adds a distinct partial pattern within the bounded bank.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_PatternAdd( Nf2_Pat_t * pPats, int * pnPats, Nf2_Pat_t * pNew )
{
    int i;
    for ( i = 0; i < *pnPats; i++ )
        if ( pPats[i].Rule == pNew->Rule && !memcmp(pPats[i].Fans, pNew->Fans, sizeof(int)*pNew->nFans) ) return;
    if ( *pnPats < NF2_PATTERN_MAX-1 ) pPats[(*pnPats)++] = *pNew;
}


/**Function*************************************************************

  Synopsis    [Evaluates a library pattern with the supplied leaf truths.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf2_PatternEval_rec( Nf2_Man_t * p, int Rule, word * pValues, int * pPos )
{
    const Amap_Nod_t * pNode = p->Patterns.pNodes+Rule;
    word t0, t1, t2;
    if ( !Rule ) return pValues[(*pPos)++];
    t0 = Nf2_PatternEval_rec(p, Abc_Lit2Var(pNode->iFan0), pValues, pPos);
    t1 = Nf2_PatternEval_rec(p, Abc_Lit2Var(pNode->iFan1), pValues, pPos);
    if ( Abc_LitIsCompl(pNode->iFan0) ) t0 = ~t0;
    if ( Abc_LitIsCompl(pNode->iFan1) ) t1 = ~t1;
    if ( pNode->Type == AMAP_OBJ_AND ) return t0&t1;
    if ( pNode->Type == AMAP_OBJ_XOR ) return t0^t1;
    assert(pNode->Type == AMAP_OBJ_MUX);
    t2 = Nf2_PatternEval_rec(p, Abc_Lit2Var(pNode->iFan2), pValues, pPos);
    if ( Abc_LitIsCompl(pNode->iFan2) ) t2 = ~t2;
    return (~t2&t0)|(t2&t1);
}
/**Function*************************************************************

  Synopsis    [Resolves repeated leaves and minimizes a matching cut truth.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_PatternCut( Nf2_Man_t * p, Nf2_Pat_t * pPat, Nf2_Cut_t * pCut )
{
    word Values[NF2_PATTERN_FANS], Code = 0, Hash, Truth;
    Nf2_Ptc_t * pCache;
    int i, j, k, Id, Pos = 0, Phase, nOld, Old[6]; unsigned Supp = 0;
    pCut->nLeaves = 0;
    for ( i = 0; i < pPat->nFans; i++ )
    {
        Id = Abc_Lit2Var(pPat->Fans[i]);
        if ( !Id ) continue;
        for ( j = 0; j < (int)pCut->nLeaves && pCut->pLeaves[j] < Id; j++ ) {}
        if ( j < (int)pCut->nLeaves && pCut->pLeaves[j] == Id ) continue;
        if ( pCut->nLeaves == (unsigned)p->pPars->nLutSize ) return 0;
        for ( k = pCut->nLeaves; k > j; k-- ) pCut->pLeaves[k] = pCut->pLeaves[k-1];
        pCut->pLeaves[j] = Id; pCut->nLeaves++;
    }
    for ( i = 0; i < pPat->nFans; i++ )
    {
        Id = Abc_Lit2Var(pPat->Fans[i]);
        for ( j = 0; j < (int)pCut->nLeaves; j++ ) if ( pCut->pLeaves[j] == Id ) break;
        Values[i] = !Id ? 0 : s_Truths6[j];
        if ( Abc_LitIsCompl(pPat->Fans[i]) ) Values[i] = ~Values[i];
        Code |= (word)Abc_Var2Lit(!Id ? 6 : j, Abc_LitIsCompl(pPat->Fans[i])) << (4*i);
    }
    Hash = (Code ^ ((word)pPat->Rule * 12582917u)) * ABC_CONST(0x9e3779b97f4a7c15);
    if ( !p->Data.pPatternTruth ) p->Data.pPatternTruth=ABC_CALLOC(Nf2_Ptc_t,65536);
    pCache = p->Data.pPatternTruth + (unsigned)(Hash >> 48);
    nOld = pCut->nLeaves;
    if ( pCache->Rule == (unsigned)pPat->Rule+1 && pCache->Code == Code )
    {
        pCut->iFunc = pCache->Result >> 6; Supp = pCache->Result & 63;
        for ( i = k = 0; i < nOld; i++ ) if ( Supp & (1u << i) ) pCut->pLeaves[k++] = pCut->pLeaves[i];
        pCut->nLeaves = k;
    }
    else
    {
        Truth = Nf2_PatternEval_rec(p, Abc_Lit2Var(pPat->Rule), Values, &Pos);
        assert(Pos == pPat->nFans);
        if ( Abc_LitIsCompl(pPat->Rule) ) Truth = ~Truth;
        Phase = (int)(Truth & 1); if ( Phase ) Truth = ~Truth;
        memcpy(Old,pCut->pLeaves,sizeof(int)*nOld);
        pCut->nLeaves = Abc_Tt6MinBase(&Truth,pCut->pLeaves,pCut->nLeaves);
        Id = Vec_MemHashInsert(p->Data.vTtMem,&Truth);
        pCut->iFunc = Abc_Var2Lit(Id,Phase);
        for ( i = k = 0; i < nOld && k < (int)pCut->nLeaves; i++ ) if ( Old[i] == pCut->pLeaves[k] ) Supp |= 1u << i, k++;
        pCache->Rule = pPat->Rule+1; pCache->Code = Code; pCache->Result = (pCut->iFunc<<6)|Supp;
    }
    pCut->Sign = Nf2_CutGetSign(pCut->pLeaves,pCut->nLeaves);
    pCut->Useless = Nf2_ObjCutUseless(p, Abc_Lit2Var(pCut->iFunc));
    return 1;
}
struct Nf2_Bank_t_
{
    int Key[12],Next,ContentNext,Result,nPats,nPaths,MaxPath,nLeaves,LastTemplate;
    int * Leaves;
    Nf2_Pat_t * Pats;
    int * Paths;
};
/**Function*************************************************************

  Synopsis    [Composes two binary fanin paths.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_BankPrefix( int Prefix, int Path )
{
    int Top=1;
    // Choice banks address a child's compact bindings, including its root.
    if ( Prefix < 0 ) return ((-Prefix-1) << NF2_CHOICE_BITS) + Path;
    while ( Top<=Path/2 ) Top*=2;
    return Prefix*Top+(Path-Top);
}
/**Function*************************************************************

  Synopsis    [Combines compatible child patterns for an AND or XOR.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_BankPair( Nf2_Man_t * p, Nf2_Pat_t * Pats, int * nPats,
    int Bank0,int Bank1,int Pol0,int Pol1,int Prefix0,int Prefix1,int Xor )
{
    Nf2_Bank_t * B0=p->Data.pBanks[Bank0],* B1=p->Data.pBanks[Bank1];
    Nf2_Pat_t Unit,New,*P0,*P1; unsigned short * Rules=Xor?p->Data.pPatternXor:p->Data.pPatternAnd;
    int i,j,k,R0,R1,Rule,Off0,Off1;
    Unit.Rule=0; Unit.nFans=1; Unit.Fans[0]=2;
    for ( i=-1; i<B0->nPats; i++ )
    {
        P0=i<0?&Unit:B0->Pats+i; R0=P0->Rule?P0->Rule^Pol0:0;
        for ( j=-1; j<B1->nPats; j++ )
        {
            P1=j<0?&Unit:B1->Pats+j; R1=P1->Rule?P1->Rule^Pol1:0;
            Rule=Rules[R0*p->Data.nPatternLits+R1];
            if ( !Rule || P0->nFans+P1->nFans>NF2_PATTERN_FANS ) continue;
            New.Rule=2*Rule; New.nFans=P0->nFans+P1->nFans;
            Off0=R0>=R1?0:P1->nFans; Off1=R0>=R1?P0->nFans:0;
            for ( k=0; k<P0->nFans; k++ ) New.Fans[Off0+k]=2*Nf2_BankPrefix(Prefix0,P0->Fans[k]>>1)+((P0->Fans[k]&1)^(P0->Rule?0:Pol0));
            for ( k=0; k<P1->nFans; k++ ) New.Fans[Off1+k]=2*Nf2_BankPrefix(Prefix1,P1->Fans[k]>>1)+((P1->Fans[k]&1)^(P1->Rule?0:Pol1));
            Nf2_PatternAdd(Pats,nPats,&New);
        }
    }
}
/**Function*************************************************************

  Synopsis    [Combines compatible child patterns for a multiplexer.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_BankMux( Nf2_Man_t * p,Nf2_Pat_t * Pats,int * nPats,int * Banks,int * Pols,int * Prefixes )
{
    Nf2_Bank_t * Bs[3]={p->Data.pBanks[Banks[0]],p->Data.pBanks[Banks[1]],p->Data.pBanks[Banks[2]]};
    Nf2_Pat_t Unit,New,*Ins[3]; Vec_Int_t * Rules=p->Patterns.vRules3;
    int i,j,k,r,c,f,n,Target[3],Rule;
    Unit.Rule=0; Unit.nFans=1; Unit.Fans[0]=2;
    for ( r=0; r<Vec_IntSize(Rules); r+=4 )
    {
        for ( c=0; c<3; c++ ) Target[c]=Vec_IntEntry(Rules,r+c);
        Rule=Vec_IntEntry(Rules,r+3);
        if ( p->Patterns.pNodes[Rule].nSuppSize>NF2_PATTERN_FANS ) continue;
        for ( i=-1; i<Bs[0]->nPats; i++ )
        {
            Ins[0]=i<0?&Unit:Bs[0]->Pats+i;
            if ( (Ins[0]->Rule?Ins[0]->Rule^Pols[0]:0)!=Target[0] ) continue;
            for ( j=-1; j<Bs[1]->nPats; j++ )
            {
                Ins[1]=j<0?&Unit:Bs[1]->Pats+j;
                if ( (Ins[1]->Rule?Ins[1]->Rule^Pols[1]:0)!=Target[1] ) continue;
                for ( k=-1; k<Bs[2]->nPats; k++ )
                {
                    Ins[2]=k<0?&Unit:Bs[2]->Pats+k;
                    if ( (Ins[2]->Rule?Ins[2]->Rule^Pols[2]:0)!=Target[2] ) continue;
                    New.Rule=2*Rule; n=0;
                    for ( c=0; c<3; c++ ) for ( f=0; f<Ins[c]->nFans; f++ )
                        New.Fans[n++]=2*Nf2_BankPrefix(Prefixes[c],Ins[c]->Fans[f]>>1)+((Ins[c]->Fans[f]&1)^(Ins[c]->Rule?0:Pols[c]));
                    New.nFans=n; Nf2_PatternAdd(Pats,nPats,&New);
                }
            }
        }
    }
}
/**Function*************************************************************

  Synopsis    [Allocates the structural-bank interning tables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_BankStart( Nf2_Man_t * p )
{
    int Size=NF2_BANK_HASH_SIZE;
    p->Data.nBankBins=Size; p->Data.nBankHashSize=Size; p->Data.pBankBins=ABC_CALLOC(Nf2_Bin_t,Size);
    p->Data.pBankContent=ABC_CALLOC(int,Size);
    p->pNodeBanks=ABC_CALLOC(int,Gia_ManObjNum(p->pGia));
    p->Data.nBanks=1; p->Data.nBankCap=1024; p->Data.pBanks=ABC_ALLOC(Nf2_Bank_t *,p->Data.nBankCap);
    p->Data.pBanks[0]=ABC_CALLOC(Nf2_Bank_t,1);
}
/**Function*************************************************************

  Synopsis    [Orders relative fanin paths for topological evaluation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_BankPathCompare( const void * a,const void * b )
{ int x=*(const int *)a,y=*(const int *)b; return (x>y)-(x<y); }
/**Function*************************************************************

  Synopsis    [Compiles pattern leaves and traversal paths for a structural bank.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Nf2_Bank_t * Nf2_BankCompile( Nf2_Man_t * p,int * Key )
{
    Nf2_Bank_t * B=ABC_CALLOC(Nf2_Bank_t,1); Nf2_Pat_t Pats[NF2_PATTERN_MAX];
    Vec_Int_t Paths; int i,k,Path,Max=1,n=0,Ids[3],Pols[3],Prefixes[3];
    memset(&Paths,0,sizeof(Paths)); memcpy(B->Key,Key,10*sizeof(int));
    Nf2_BankPair(p,Pats,&n,Key[0]>>1,Key[1]>>1,Key[0]&1,Key[1]&1,2,3,Key[2]);
    if ( Key[3] )
    {
        for ( i=0; i<3; i++ ) { Ids[i]=Key[4+2*i]>>1; Pols[i]=Key[4+2*i]&1; Prefixes[i]=Key[5+2*i]; }
        if ( Key[3]==1 ) Nf2_BankPair(p,Pats,&n,Ids[0],Ids[1],Pols[0],Pols[1],Prefixes[0],Prefixes[1],1);
        else Nf2_BankMux(p,Pats,&n,Ids,Pols,Prefixes);
    }
    {
        Vec_Int_t Leaves; memset(&Leaves,0,sizeof(Leaves));
        for ( i=0; i<n; i++ ) for ( k=0; k<Pats[i].nFans; k++ ) Vec_IntPushUnique(&Leaves,Pats[i].Fans[k]>>1);
        B->Leaves=Leaves.pArray; B->nLeaves=Leaves.nSize;
    }
    B->nPats=n; B->Pats=ABC_ALLOC(Nf2_Pat_t,n); memcpy(B->Pats,Pats,n*sizeof(Nf2_Pat_t));
    for ( i=0; i<n; i++ ) for ( k=0; k<Pats[i].nFans; k++ )
    {
        Path=Pats[i].Fans[k]>>1; Max=Abc_MaxInt(Max,Path);
        for ( ; Path>1; Path>>=1 ) Vec_IntPushUnique(&Paths,Path);
    }
    qsort(Vec_IntArray(&Paths),Vec_IntSize(&Paths),sizeof(int),Nf2_BankPathCompare);
    B->Paths=Paths.pArray; B->nPaths=Paths.nSize; B->MaxPath=Max;
    return B;
}
/**Function*************************************************************

  Synopsis    [Hashes the ordered contents of a structural bank.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Nf2_BankContentHash( Nf2_Bank_t * B )
{
    unsigned Hash=B->nPats; int i,k;
    for ( i=0; i<B->nPats; i++ )
    {
        Hash=(Hash^(unsigned)B->Pats[i].Rule)*12582917u;
        for ( k=0; k<B->Pats[i].nFans; k++ ) Hash=(Hash^(unsigned)B->Pats[i].Fans[k])*4256249u;
    }
    return Hash^(Hash>>16);
}
/**Function*************************************************************

  Synopsis    [Compares structural-bank contents independent of their keys.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_BankEqual( Nf2_Bank_t * A,Nf2_Bank_t * B )
{
    int i;
    if ( A->Key[11]!=B->Key[11] || A->nPats!=B->nPats ) return 0;
    for ( i=0; i<A->nPats; i++ )
        if ( A->Pats[i].Rule!=B->Pats[i].Rule || A->Pats[i].nFans!=B->Pats[i].nFans || memcmp(A->Pats[i].Fans,B->Pats[i].Fans,A->Pats[i].nFans*sizeof(int)) ) return 0;
    return 1;
}
/**Function*************************************************************

  Synopsis    [Hashes the nonzero part of a structural-bank key.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Nf2_BankKeyHash( int * Key )
{
    unsigned Hash=(unsigned)Key[0]*12582917u; int i;
    Hash=(Hash^(unsigned)Key[1])*12582917u;
    Hash=(Hash^(unsigned)Key[2])*12582917u;
    if ( Key[3] )
        for ( i=3; i<10; i++ ) Hash=(Hash^(unsigned)Key[i])*12582917u;
    return Hash^(Hash>>16);
}
/**Function*************************************************************

  Synopsis    [Registers a bank and shares identical pattern contents.]

  Description [Choice banks retain their own compact binding programs even when
  their patterns are shared. Structural banks can also share the paths.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_BankRegister( Nf2_Man_t * p, Nf2_Bank_t * B )
{
    int Bank = p->Data.nBanks++, Other;
    unsigned Content = Nf2_BankContentHash( B ) & (p->Data.nBankBins - 1);
    if ( p->Data.nBanks > p->Data.nBankCap )
    {
        p->Data.nBankCap *= 2;
        p->Data.pBanks = ABC_REALLOC( Nf2_Bank_t *, p->Data.pBanks, p->Data.nBankCap );
    }
    p->Data.pBanks[Bank] = B;
    for ( Other = p->Data.pBankContent[Content]; Other; Other = p->Data.pBanks[Other]->ContentNext )
        if ( Nf2_BankEqual(B, p->Data.pBanks[Other]) ) break;
    if ( Other )
    {
        B->Result = Other;
        ABC_FREE( B->Pats );
        if ( !B->Key[11] )
        {
            ABC_FREE( B->Paths );
            ABC_FREE( B->Leaves );
            B->nPats = B->nPaths = 0;
        }
    }
    else
    {
        B->Result = Bank;
        B->ContentNext = p->Data.pBankContent[Content];
        p->Data.pBankContent[Content] = Bank;
    }
    return Bank;
}
/**Function*************************************************************

  Synopsis    [Grows the exact structural-bank hash table at half occupancy.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_BankHashGrow( Nf2_Man_t * p )
{
    Nf2_Bin_t * Old=p->Data.pBankBins, * Bin;
    int OldSize=p->Data.nBankHashSize, i, Slot, Key[4];
    p->Data.nBankHashSize*=2;
    p->Data.pBankBins=ABC_CALLOC(Nf2_Bin_t,p->Data.nBankHashSize);
    for ( i=0; i<OldSize; i++ )
    {
        Bin=Old+i;
        if ( !Bin->Bank ) continue;
        Key[0]=Bin->Key0; Key[1]=Bin->Key1; Key[2]=Bin->Kind&1; Key[3]=Bin->Kind>>1;
        Slot=Nf2_BankKeyHash(Key[3]?p->Data.pBanks[Bin->Bank]->Key:Key)&(p->Data.nBankHashSize-1);
        while ( p->Data.pBankBins[Slot].Bank ) Slot=(Slot+1)&(p->Data.nBankHashSize-1);
        p->Data.pBankBins[Slot]=*Bin;
    }
    ABC_FREE(Old);
}
/**Function*************************************************************

  Synopsis    [Builds the common AND/XOR/MUX recognition key for both banks.]

  Description [The structural recognizers require AND semantics in the root
  and both children. An explicit XOR in any of these positions must instead
  be composed through its own bank. Extra returns recognized input literals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_BankRootKey( Nf2_Man_t * p, int Id, int * Key, int * Extra )
{
    Gia_Obj_t * Obj = Gia_ManObj(p->pGia,Id), * F0, * F1, * FC;
    int Id0 = Gia_ObjFaninId0(Obj,Id), Id1 = Gia_ObjFaninId1(Obj,Id), k, n;
    Key[0] = 2*p->pNodeBanks[Id0] + Gia_ObjFaninC0(Obj);
    Key[1] = 2*p->pNodeBanks[Id1] + Gia_ObjFaninC1(Obj);
    Key[2] = Gia_ObjIsXor(Obj);
    if ( Key[2] || Gia_ObjIsXor(Gia_ManObj(p->pGia,Id0)) ||
         Gia_ObjIsXor(Gia_ManObj(p->pGia,Id1)) || !Gia_ObjIsMuxType(Obj) )
        return 0;
    if ( Gia_ObjRecognizeExor(Obj,&F0,&F1) )
    {
        Key[3] = 1;
        Extra[0] = Gia_ObjToLit(p->pGia,F0);
        Extra[1] = Gia_ObjToLit(p->pGia,F1);
        n = 2;
    }
    else
    {
        Key[3] = 2;
        FC = Gia_ObjRecognizeMux(Obj,&F1,&F0);
        Extra[0] = Gia_ObjToLit(p->pGia,F0);
        Extra[1] = Gia_ObjToLit(p->pGia,F1);
        Extra[2] = Gia_ObjToLit(p->pGia,FC);
        n = 3;
    }
    for ( k = 0; k < n; k++ )
        Key[4+2*k] = 2*p->pNodeBanks[Extra[k]>>1] + (Extra[k]&1);
    return n;
}
/**Function*************************************************************

  Synopsis    [Finds a node bank and resolves its relative paths to GIA objects.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_BankRead( Nf2_Man_t * p,int Id )
{
    Gia_Obj_t * Obj=Gia_ManObj(p->pGia,Id),*O;
    int Key[10]={0},Extra[3],Values[8],i,k,n,Path,Bank,Slot,Kind; unsigned Hash;
    Nf2_Bin_t * Bin;
    Nf2_Bank_t * B;
    Values[1]=Id; Values[2]=Gia_ObjFaninId0p(p->pGia,Obj); Values[3]=Gia_ObjFaninId1p(p->pGia,Obj);
    n=Nf2_BankRootKey(p,Id,Key,Extra);
    if ( n )
    {
        for ( i=4; i<8; i++ ) { O=Gia_ManObj(p->pGia,Values[i>>1]); Values[i]=(i&1)?Gia_ObjFaninId1p(p->pGia,O):Gia_ObjFaninId0p(p->pGia,O); }
        for ( k=0; k<n; k++ )
        {
            for ( i=4; i<8; i++ ) if ( Values[i]==(Extra[k]>>1) ) break;
            assert(i<8); Key[5+2*k]=i;
        }
    }
    Kind=Key[2]+2*Key[3]; Hash=Nf2_BankKeyHash(Key);
    Slot=Hash&(p->Data.nBankHashSize-1);
    for ( ; ; Slot=(Slot+1)&(p->Data.nBankHashSize-1) )
    {
        Bin=p->Data.pBankBins+Slot; Bank=Bin->Bank;
        if ( !Bank || (Bin->Key0==Key[0] && Bin->Key1==Key[1] && Bin->Kind==Kind &&
             (!Key[3] || !memcmp(Key+4,p->Data.pBanks[Bank]->Key+4,6*sizeof(int)))) ) break;
    }
    if ( !Bank )
    {
        if ( p->Data.nBanks*2>=p->Data.nBankHashSize )
        {
            Nf2_BankHashGrow(p); Slot=Hash&(p->Data.nBankHashSize-1);
            while ( p->Data.pBankBins[Slot].Bank ) Slot=(Slot+1)&(p->Data.nBankHashSize-1);
            Bin=p->Data.pBankBins+Slot;
        }
        B=Nf2_BankCompile(p,Key); Bank=Nf2_BankRegister(p,B);
        Bin->Key0=Key[0]; Bin->Key1=Key[1]; Bin->Kind=Kind; Bin->Bank=Key[3]?Bank:B->Result;
    }
    else B=p->Data.pBanks[Bank];
    Bank=B->Result; B=p->Data.pBanks[Bank];
    p->pNodeBanks[Id]=Bank;
    if ( p->nBankValues<=B->MaxPath )
    { p->nBankValues=2*(B->MaxPath+1); p->pBankValues=ABC_REALLOC(int,p->pBankValues,p->nBankValues); }
    p->pBankValues[1]=Id;
    for ( i=0; i<B->nPaths; i++ )
    {
        Path=B->Paths[i]; O=Gia_ManObj(p->pGia,p->pBankValues[Path>>1]);
        assert(Gia_ObjIsAnd(O));
        p->pBankValues[Path]=(Path&1)?Gia_ObjFaninId1p(p->pGia,O):Gia_ObjFaninId0p(p->pGia,O);
    }
    return B->nPats;
}
/**Function*************************************************************

  Synopsis    [Releases structural banks and per-network path storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_BankStop( Nf2_Man_t * p )
{
    int i;
    for ( i=0; i<p->Data.nBanks; i++ ) { ABC_FREE(p->Data.pBanks[i]->Pats); ABC_FREE(p->Data.pBanks[i]->Paths); ABC_FREE(p->Data.pBanks[i]->Leaves); ABC_FREE(p->Data.pBanks[i]); }
    ABC_FREE(p->Data.pChoiceBins);
    ABC_FREE(p->Data.pBanks); ABC_FREE(p->Data.pBankBins); ABC_FREE(p->Data.pBankContent); ABC_FREE(p->pNodeBanks); ABC_FREE(p->pBankValues);
}
/**Function*************************************************************

  Synopsis    [Resolves shared library patterns through fanins and proved choices.]

  Description [A bank records which child binding supplies each leaf. This permits
  patterns to cross any number of choice links without encoding long paths.
  A sibling precedes its representative, so every binding is topological.
  Structural keys retain their binding programs while identical pattern sets
  share one canonical bank and its compiled match templates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_ChoiceRead( Nf2_Man_t * p, int Id )
{
    Gia_Obj_t *Obj = Gia_ManObj( p->pGia, Id );
    int Key[12] = { 0 }, Objs[6] = { 0 }, Extra[3], i, k, n = 0, Sib = Gia_ObjSibl( p->pGia, Id ), Bank, Slot;
    unsigned Hash = 0;
    Nf2_Bank_t * B;
    if ( !p->Data.pChoiceBins )
        p->Data.pChoiceBins = ABC_CALLOC( int, NF2_BANK_HASH_SIZE );
    if ( !p->pChoiceOffsets )
        p->pChoiceOffsets = ABC_CALLOC( int, Gia_ManObjNum( p->pGia ) );
    Objs[0] = Gia_ObjFaninId0( Obj, Id );
    Objs[1] = Gia_ObjFaninId1( Obj, Id );
    Objs[5] = Sib;
    n = Nf2_BankRootKey( p, Id, Key, Extra );
    for ( k = 0; k < n; k++ ) Objs[2+k] = Extra[k] >> 1;
    if ( Sib )
    {
        assert( Sib < Id );
        Key[10] = 2 * p->pNodeBanks[Sib] + ( Gia_ObjPhase( Obj ) ^ Gia_ObjPhase( Gia_ManObj( p->pGia, Sib ) ) );
    }
    Key[11] = 1;
    for ( i = 0; i < 12; i++ )
        Hash = ( Hash ^ (unsigned)Key[i] ) * 12582917u;
    Slot = ( Hash ^ ( Hash >> 16 ) ) & ( NF2_BANK_HASH_SIZE - 1 );
    for ( Bank = p->Data.pChoiceBins[Slot]; Bank; Bank = p->Data.pBanks[Bank]->Next )
        if ( !memcmp( Key, p->Data.pBanks[Bank]->Key, sizeof( Key ) ) )
            break;
    if ( !Bank )
    {
        Nf2_Pat_t Pats[NF2_PATTERN_MAX], Pat;
        Vec_Int_t * vSources = Vec_IntAlloc( 16 );
        int nPats = 0, Ids[3], Pols[3], Prefixes[3] = { -3, -4, -5 }, Source, Index;
        Nf2_BankPair( p, Pats, &nPats, Key[0] >> 1, Key[1] >> 1, Key[0] & 1, Key[1] & 1, -1, -2, Key[2] );
        if ( Key[3] )
        {
            for ( i = 0; i < 3; i++ )
            {
                Ids[i] = Key[4 + 2 * i] >> 1;
                Pols[i] = Key[4 + 2 * i] & 1;
            }
            if ( Key[3] == 1 )
                Nf2_BankPair( p, Pats, &nPats, Ids[0], Ids[1], Pols[0], Pols[1], -3, -4, 1 );
            else
                Nf2_BankMux( p, Pats, &nPats, Ids, Pols, Prefixes );
        }
        if ( Sib )
        {
            Nf2_Bank_t * S = p->Data.pBanks[Key[10] >> 1];
            for ( i = 0; i < S->nPats; i++ )
            {
                Pat = S->Pats[i];
                Pat.Rule ^= Key[10] & 1;
                for ( k = 0; k < Pat.nFans; k++ )
                    Pat.Fans[k] += 2 * ( 5 << NF2_CHOICE_BITS );
                Nf2_PatternAdd( Pats, &nPats, &Pat );
            }
        }
        for ( i = 0; i < nPats; i++ )
            for ( k = 0; k < Pats[i].nFans; k++ )
            {
                Source = Pats[i].Fans[k] >> 1;
                for ( Index = 0; Index < Vec_IntSize(vSources); Index++ )
                    if ( Vec_IntEntry(vSources, Index) == Source )
                        break;
                if ( Index == Vec_IntSize(vSources) )
                    Vec_IntPush( vSources, Source );
                Pats[i].Fans[k] = 2 * ( Index + 2 ) + ( Pats[i].Fans[k] & 1 );
            }
        B = ABC_CALLOC( Nf2_Bank_t, 1 );
        memcpy( B->Key, Key, sizeof( Key ) );
        B->nPats = nPats;
        B->Pats = ABC_ALLOC( Nf2_Pat_t, nPats );
        memcpy( B->Pats, Pats, nPats * sizeof( Nf2_Pat_t ) );
        B->nLeaves = B->nPaths = Vec_IntSize( vSources );
        B->MaxPath = B->nLeaves + 1;
        assert( B->MaxPath <= NF2_CHOICE_MASK );
        B->Paths = Vec_IntReleaseArray( vSources );
        Vec_IntFree( vSources );
        B->Leaves = ABC_ALLOC( int, B->nLeaves );
        for ( i = 0; i < B->nLeaves; i++ )
            B->Leaves[i] = i + 2;
        Bank = Nf2_BankRegister( p, B );
        B->Next = p->Data.pChoiceBins[Slot];
        p->Data.pChoiceBins[Slot] = Bank;
    }
    B = p->Data.pBanks[Bank];
    p->pNodeBanks[Id] = B->Result;
    if ( p->nBankValues <= B->MaxPath )
    {
        p->nBankValues = 2 * ( B->MaxPath + 1 );
        p->pBankValues = ABC_REALLOC( int, p->pBankValues, p->nBankValues );
    }
    p->pBankValues[1] = Id;
    for ( i = 0; i < B->nLeaves; i++ )
    {
        int Owner = B->Paths[i] >> NF2_CHOICE_BITS, Path = B->Paths[i] & NF2_CHOICE_MASK, Child = Objs[Owner];
        assert( Owner < 6 && Child < Id && Path > 0 );
        p->pBankValues[i + 2] =
            Path == 1 ? Child : Vec_IntEntry( &p->vChoiceValues, p->pChoiceOffsets[Child] + Path - 1 );
    }
    p->pChoiceOffsets[Id] = Vec_IntSize( &p->vChoiceValues );
    Vec_IntPushArray( &p->vChoiceValues, p->pBankValues + 1, B->nLeaves + 1 );
    return B->nPats;
}
struct Nf2_Template_t_
{
    int Bank,Next,Handle,nMap,nBindings,nPrograms,fConstant;
    int * BindPaths;
    int PolStarts[3]; int * MinIds[2],nMin[2]; word NextArea[2];
    Nf2_Prog_t * Programs, * Initial; int InitStarts[3];
    int * Used,nUsed;
    int Map[1];
};
/**Function*************************************************************

  Synopsis    [Allocates cut-template lookup and physical binding storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_TemplateStart( Nf2_Man_t * p )
{
    p->Data.pTemplateBins=ABC_CALLOC(int,p->Data.nBankBins);
    p->Data.nTemplates=1; p->Data.nTemplateCap=1024; p->Data.pTemplates=ABC_CALLOC(Nf2_Template_t *,p->Data.nTemplateCap);
    p->pBindOffsets=ABC_CALLOC(int,Gia_ManObjNum(p->pGia));
    p->pNodeTemplates=ABC_CALLOC(int,Gia_ManObjNum(p->pGia));
    Vec_IntPush(&p->vBindings,0);
}
/**Function*************************************************************

  Synopsis    [Compiles distinct cell matches with predecoded leaf polarities.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ProgramBuild( Nf2_Man_t * p,Nf2_Template_t * T )
{
    Vec_Int_t * Matches, * Flags; Nf2_Prog_t R,*Programs; int n=0,i,j,k,Gate,Config,Var,Pol,Raw=0;
    int * Set=Nf2_ManCutSet(p,T->Handle),*Cut,*Fans;
    Nf2_SetForEachCut(Set,Cut,i)
        Raw+=Vec_IntSize(Vec_WecEntry(p->Data.vTt2Match,Nf2_CutFunc(Cut)>>1))/2;
    Programs=ABC_ALLOC(Nf2_Prog_t,Raw);
    Nf2_SetForEachCut(Set,Cut,i)
    {
        Fans=Nf2_CutLeaves(Cut); Matches=Vec_WecEntry(p->Data.vTt2Match,Nf2_CutFunc(Cut)>>1);
        Flags=Vec_WecEntry(p->Data.vMatchFlags,Nf2_CutFunc(Cut)>>1);
        if ( !Nf2_CutSize(Cut) )
        {
            assert(Set[0]==1); T->fConstant=1; continue;
        }
        Vec_IntForEachEntryDouble(Matches,Gate,Config,j)
        {
            Nf2_Cfg_t Cfg=Nf2_Int2Cfg(Config);
            memset(&R,0,sizeof(R)); R.Gate=Gate; R.CutH=Nf2_CutHandle(Set,Cut); R.Config=Config; R.NeedArea=Vec_IntEntry(Flags,j/2)&1; R.NeedDelay=(Vec_IntEntry(Flags,j/2)>>1)&1;
            R.Pol=Cfg.fCompl^(Nf2_CutFunc(Cut)&1); R.nFans=Nf2_CutSize(Cut);
            Nf2_CfgForEachVarCompl(Cfg,R.nFans,Var,Pol,k)
            { R.Pins[k]=Fans[Var]^Pol; R.Phase|=(unsigned)(R.Pins[k]&1)<<Var; }
            Programs[n++]=R;
        }
    }
    {
        Nf2_Prog_t * Order=ABC_ALLOC(Nf2_Prog_t,n); int c,Pos=0;
        for ( c=0; c<2; c++ )
        {
            T->PolStarts[c]=Pos;
            for ( i=0; i<n; i++ ) if ( Programs[i].Pol==c )
            {
                Nf2_Prog_t * P=Programs+i;
                Order[Pos++]=*P;
            }
        }
        T->PolStarts[2]=Pos; assert(Pos==n); ABC_FREE(Programs); Programs=Order;
    }
    T->Programs=Programs; T->nPrograms=n;
    {
        unsigned char Seen[NF2_PATTERN_MAX*NF2_PATTERN_FANS+1];
        Vec_Int_t Used; memset(&Used,0,sizeof(Used));
        memset(Seen,0,T->nBindings+1);
        for ( i=0; i<n; i++ ) for ( j=0; j<Programs[i].nFans; j++ )
        {
            Var=Programs[i].Pins[j]>>1;
            if ( !Seen[Var] ) { Seen[Var]=1; Vec_IntPush(&Used,Var); }
        }
        T->Used=Used.pArray; T->nUsed=Used.nSize;
    }
    {
        int c; word Min,Area; Vec_Int_t Ids;
        for ( c=0; c<2; c++ )
        {
            Min=T->NextArea[c]=~(word)0;
            for ( i=T->PolStarts[c]; i<T->PolStarts[c+1]; i++ )
            {
                Area=p->pCells[Programs[i].Gate].AreaW;
                if ( Area<Min ) { T->NextArea[c]=Min; Min=Area; }
                else if ( Area>Min && Area<T->NextArea[c] ) T->NextArea[c]=Area;
            }
            memset(&Ids,0,sizeof(Ids));
            for ( i=T->PolStarts[c]; i<T->PolStarts[c+1]; i++ )
                if ( p->pCells[Programs[i].Gate].AreaW==Min ) Vec_IntPush(&Ids,i);
            T->MinIds[c]=Ids.pArray; T->nMin[c]=Ids.nSize;
        }
    }
    // For small binding sets, use the existing permutation nibbles directly.
    // The unused seventh phase bit selects this representation.
    for ( i=0; i<n; i++ )
    {
        Nf2_Prog_t * P=Programs+i;
        union { int x; Nf2_Cfg_t y; } Direct;
        for ( j=0; j<P->nFans && P->Pins[j]<32; j++ ) {}
        if ( j<P->nFans ) continue;
        Direct.x=0; Direct.y.Phase=64;
        for ( j=0; j<P->nFans; j++ )
        {
            Direct.y.Phase|=(unsigned)(P->Pins[j]&1)<<j;
            Direct.y.Perm|=(unsigned)(P->Pins[j]>>1)<<(4*j);
        }
        P->Config=Direct.x;
    }

    {
        int c, Count=0;
        for ( i=0; i<n; i++ ) Count+=Programs[i].NeedDelay || Programs[i].NeedArea;
        T->Initial=ABC_ALLOC(Nf2_Prog_t,Count);
        Count=0;
        for ( c=0; c<2; c++ )
        {
            T->InitStarts[c]=Count;
            for ( i=T->PolStarts[c]; i<T->PolStarts[c+1]; i++ )
                if ( Programs[i].NeedDelay || Programs[i].NeedArea ) T->Initial[Count++]=Programs[i];
        }
        T->InitStarts[2]=Count;
    }

}
/**Function*************************************************************

  Synopsis    [Appends physical leaf bindings with geometric capacity growth.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_BindAppend( Nf2_Man_t * p,int * Binds,int Count )
{
    Vec_Int_t * V=&p->vBindings;
    assert(Count>=0 && V->nSize<=INT_MAX-Count);
    if ( V->nCap-V->nSize<Count )
        Vec_IntGrow(V,Abc_MaxInt(V->nSize+Count,V->nCap<=INT_MAX/2?2*V->nCap:INT_MAX));
    memcpy(V->pArray+V->nSize,Binds,Count*sizeof(int)); V->nSize+=Count;
}
/**Function*************************************************************

  Synopsis    [Interns path-ordered leaf bindings, minimized cuts, and cell matches.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_TemplateFind( Nf2_Man_t * p,int Id )
{
    int Bank=p->pNodeBanks[Id],i,k,j,nUnique=0,nCuts=0,Entry,Handle,Map[NF2_PATTERN_MAX*NF2_PATTERN_FANS],Unique[NF2_PATTERN_MAX*NF2_PATTERN_FANS+1];
    Nf2_Bank_t * B=p->Data.pBanks[Bank]; Nf2_Template_t * T; unsigned Hash=(unsigned)Bank*12582917u;
    Nf2_Pat_t Pat; Nf2_Cut_t Cuts[NF2_CUT_MAX],*Ptrs[NF2_CUT_MAX];
    p->nBindQueries++;
    // Preserve first path occurrence; reject aliases before reusing a template.
    if ( B->LastTemplate )
    {
        int Valid=1;
        int * Stored;
        T=p->Data.pTemplates[B->LastTemplate];
        assert(p->vBindings.nSize<=INT_MAX-T->nBindings-1);
        if ( p->vBindings.nCap-p->vBindings.nSize<T->nBindings+1 )
            Vec_IntGrow(&p->vBindings,Abc_MaxInt(p->vBindings.nSize+T->nBindings+1,p->vBindings.nCap<=INT_MAX/2?2*p->vBindings.nCap:INT_MAX));
        // Fill reserved storage directly; a failed match leaves its size unchanged.
        Stored=p->vBindings.pArray+p->vBindings.nSize; Stored[0]=0;
        for ( i=1; i<=T->nBindings; i++ )
        {
            Stored[i]=p->pBankValues[T->BindPaths[i]];
            if ( !Stored[i] ) { Valid=0; break; }
            if ( p->pBindSeen[Stored[i]]==(unsigned)Id ) { Valid=0; break; }
            p->pBindSeen[Stored[i]]=(unsigned)Id;
        }
        if ( Valid && T->nBindings!=T->nMap )
            for ( i=0; i<B->nLeaves; i++ )
                if ( p->pBankValues[B->Leaves[i]]!=Stored[T->Map[i]] ) { Valid=0; break; }
        if ( Valid )
        {
            p->pBindOffsets[Id]=Vec_IntSize(&p->vBindings);
            p->vBindings.nSize+=T->nBindings+1;
            p->pNodeTemplates[Id]=B->LastTemplate; p->nBindHits++; return T->Handle;
        }
    }
    for ( i=0; i<B->nLeaves; i++ )
    {
        int Obj=p->pBankValues[B->Leaves[i]];
        if ( !Obj ) { Map[i]=0; continue; }
        for ( k=0; k<nUnique; k++ ) if ( Unique[k]==Obj ) break;
        if ( k==nUnique ) Unique[nUnique++]=Obj;
        Map[i]=k+1;
    }
    p->pBindOffsets[Id]=Vec_IntSize(&p->vBindings);
    Vec_IntPush(&p->vBindings,0);
    Nf2_BindAppend(p,Unique,nUnique);
    for ( i=0; i<B->nLeaves; i++ ) Hash=(Hash^(unsigned)Map[i])*4256249u;
    Hash=(Hash^(Hash>>16))&(p->Data.nBankBins-1);
    for ( Entry=p->Data.pTemplateBins[Hash]; Entry; Entry=p->Data.pTemplates[Entry]->Next )
    {
        T=p->Data.pTemplates[Entry];
        if ( T->Bank==Bank && T->nMap==B->nLeaves && !memcmp(T->Map,Map,B->nLeaves*sizeof(int)) )
        { B->LastTemplate=Entry; p->pNodeTemplates[Id]=Entry; return T->Handle; }
    }
    for ( i=0; i<NF2_CUT_MAX; i++ ) Ptrs[i]=Cuts+i;
    for ( i=0; i<B->nPats; i++ )
    {
        Pat=B->Pats[i];
        for ( k=0; k<Pat.nFans; k++ )
        {
            for ( j=0; j<B->nLeaves; j++ ) if ( B->Leaves[j]==(Pat.Fans[k]>>1) ) break;
            assert(j<B->nLeaves); Pat.Fans[k]=2*Map[j]+(Pat.Fans[k]&1);
        }
        if ( !Nf2_PatternCut(p,&Pat,Ptrs[nCuts]) || Ptrs[nCuts]->Useless ) continue;
        if ( Nf2_SetLastCutIsContained(Ptrs,nCuts) ) continue;
        nCuts=Nf2_SetLastCutContainsArea(Ptrs,nCuts)+1;
        if ( nCuts==p->pPars->nCutNum ) break;
    }
    assert(nCuts); Handle=Nf2_ManSaveCuts(p,Ptrs,nCuts);
    T=(Nf2_Template_t *)ABC_ALLOC(char,sizeof(Nf2_Template_t)+sizeof(int)*B->nLeaves);
    memset(T,0,sizeof(*T)); T->nBindings=nUnique;
    T->Bank=Bank; T->nMap=B->nLeaves; T->Handle=Handle; memcpy(T->Map,Map,B->nLeaves*sizeof(int));
    T->BindPaths=ABC_CALLOC(int,nUnique+1);
    for ( i=0; i<B->nLeaves; i++ ) if ( Map[i] ) T->BindPaths[Map[i]]=B->Leaves[i];
    Nf2_ProgramBuild(p,T);
    Entry=p->Data.nTemplates++; B->LastTemplate=Entry; p->pNodeTemplates[Id]=Entry;
    if ( p->Data.nTemplates>p->Data.nTemplateCap ) { p->Data.nTemplateCap*=2; p->Data.pTemplates=ABC_REALLOC(Nf2_Template_t *,p->Data.pTemplates,p->Data.nTemplateCap); }
    p->Data.pTemplates[Entry]=T; T->Next=p->Data.pTemplateBins[Hash]; p->Data.pTemplateBins[Hash]=Entry;
    return Handle;
}
/**Function*************************************************************

  Synopsis    [Releases cut templates and per-network bindings.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_TemplateStop( Nf2_Man_t * p )
{
    int i;
    for ( i=1; i<p->Data.nTemplates; i++ ) { ABC_FREE(p->Data.pTemplates[i]->Programs); ABC_FREE(p->Data.pTemplates[i]->Initial); ABC_FREE(p->Data.pTemplates[i]->Used); ABC_FREE(p->Data.pTemplates[i]->MinIds[0]); ABC_FREE(p->Data.pTemplates[i]->MinIds[1]); ABC_FREE(p->Data.pTemplates[i]->BindPaths); ABC_FREE(p->Data.pTemplates[i]); }
    ABC_FREE(p->pNodeTemplates);
    ABC_FREE(p->Data.pTemplates); ABC_FREE(p->Data.pTemplateBins); ABC_FREE(p->pBindOffsets); ABC_FREE(p->vBindings.pArray);
}
typedef struct Nf2_Shared_t_
{
    Nf2_Man_t Man;
    Mio_Cell2_t * Cells;
    Amap_Nod_t * Nodes;
    int nCells,nNodes,K,Cuts,Flags;
} Nf2_Shared_t;
// A worker that maps must call Abc_Stop or Nf2_ManClearCache before exiting;
// portable thread-local storage does not supply an automatic destructor.
static ABC_THREAD_LOCAL Nf2_Shared_t * s_pNf2Shared;
// Retain one previous library/configuration for ordinary/tied-mode alternation.
static ABC_THREAD_LOCAL Nf2_Shared_t * s_pNf2Previous;
/**Function*************************************************************

  Synopsis    [Releases one compiled library cache.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_SharedFree( Nf2_Shared_t * S )
{
    if ( !S ) return;
    if ( S->Man.Data.vTtMem ) { Vec_MemHashFree(S->Man.Data.vTtMem); Vec_MemFree(S->Man.Data.vTtMem); }
    Vec_WecFree(S->Man.Data.vTt2Match); Vec_WecFree(S->Man.Data.vMatchFlags);
    Nf2_TemplateStop(&S->Man); Nf2_BankStop(&S->Man);
    ABC_FREE(S->Man.Data.pPatternAnd); ABC_FREE(S->Man.Data.pPatternXor); ABC_FREE(S->Man.Data.pPatternTruth);
    Vec_PtrFreeData(&S->Man.Data.vPages); ABC_FREE(S->Man.Data.vPages.pArray);
    ABC_FREE(S->Cells); ABC_FREE(S->Nodes); ABC_FREE(S);
}
/**Function*************************************************************

  Synopsis    [Releases both compiled library caches owned by this thread.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nf2_ManClearCache( void )
{
    Nf2_SharedFree( s_pNf2Shared );
    Nf2_SharedFree( s_pNf2Previous );
    s_pNf2Shared = s_pNf2Previous = NULL;
}
/**Function*************************************************************

  Synopsis    [Transfers ownership of compiled data between cache and manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_SharedMove( Nf2_Man_t * To, Nf2_Man_t * From )
{
    To->Data = From->Data;
    memset( &From->Data, 0, sizeof(From->Data) );
}

/**Function*************************************************************

  Synopsis    [Checks library contents and parameters before cache reuse.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_SharedValid( Nf2_Man_t * p, Nf2_Shared_t * S )
{
    if ( !S || !S->Man.Data.nBanks || S->nCells!=p->nCells || S->nNodes!=p->Patterns.nNodes || S->K!=p->pPars->nLutSize || S->Cuts!=p->pPars->nCutNum ) return 0;
    if ( S->Flags!=(p->pPars->fPinFilter+2*p->pPars->fPinPerm+4*p->pPars->fPinQuick) ) return 0;
    if ( memcmp(S->Cells,p->pCells,S->nCells*sizeof(Mio_Cell2_t)) || memcmp(S->Nodes,p->Patterns.pNodes,S->nNodes*sizeof(Amap_Nod_t)) ) return 0;
    return 1;
}
// The library match rows use the immutable initial truth-table prefix.
// Keep a private copy of that prefix and its matches with the compiled banks;
// subsequent NF truth-table insertions cannot affect this cache's identifiers.
/**Function*************************************************************

  Synopsis    [Marks dominated initial delay profiles in the library.]

  Description [The initial delay pass considers an inverter in both
  directions, so each leaf obeys D[c] <= D[!c] + InvDelay.  This bounds
  comparisons between different input phases.  Equal delay profiles retain
  their first occurrence.  Other dominated profiles can change which equal-
  delay cell wins, while their area alternatives remain available.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_LibraryDelayFlags( Nf2_Man_t * p )
{
    Vec_Int_t * Matches, * Flags;
    int * Delays, * Phases, * Memory;
    int t, i, j, k, n, N, Max = 0, Gate, Strict;
    unsigned Mask;
    Nf2_Cfg_t Cfg;
    if ( p->InvDelayI <= 0 ) return;
    Vec_WecForEachLevel(p->Data.vTt2Match, Matches, t)
        Max = Abc_MaxInt(Max, Vec_IntSize(Matches) / 2);
    if ( Max == 0 || Max > INT_MAX / 7 ) return;
    Memory = ABC_ALLOC(int, 7 * Max);
    Delays = Memory; Phases = Memory + 6 * Max;
    Vec_WecForEachLevel(p->Data.vTt2Match, Matches, t)
    {
        N = Vec_IntSize(Matches) / 2;
        Flags = Vec_WecEntry(p->Data.vMatchFlags, t);
        for ( i = 0; i < N; i++ )
        {
            Gate = Vec_IntEntry(Matches, 2*i);
            Cfg = Nf2_Int2Cfg(Vec_IntEntry(Matches, 2*i+1));
            Phases[i] = Cfg.fCompl << 6;
            Mask = 0;
            for ( k = 0; k < (int)p->pCells[Gate].nFanins; k++ )
            {
                int Var = Nf2_CfgVar(Cfg, k);
                assert(Var < (int)p->pCells[Gate].nFanins && !(Mask & (1u << Var)));
                Mask |= 1u << Var;
                Delays[6*i+Var] = p->pCells[Gate].iDelays[k];
                Phases[i] |= Nf2_CfgCompl(Cfg, k) << Var;
            }
        }
        for ( i = 0; i < N; i++ )
        {
            Gate = Vec_IntEntry(Matches, 2*i);
            n = p->pCells[Gate].nFanins;
            for ( j = 0; j < N; j++ )
            {
                if ( i == j || ((Phases[i] ^ Phases[j]) & 64) ||
                     p->pCells[Vec_IntEntry(Matches, 2*j)].nFanins != (unsigned)n ) continue;
                Strict = 0;
                for ( k = 0; k < n; k++ )
                {
                    long long Bound = (long long)Delays[6*j+k] +
                        ((((Phases[j] ^ Phases[i]) >> k) & 1) ? p->InvDelayI : 0);
                    if ( Bound > Delays[6*i+k] ) break;
                    Strict |= Bound < Delays[6*i+k];
                }
                if ( k < n || (j > i && !Strict) ) continue;
                Vec_IntWriteEntry(Flags, i, Vec_IntEntry(Flags, i) & 1);
                break;
            }
        }
    }
    ABC_FREE(Memory);
}
/**Function*************************************************************

  Synopsis    [Marks initial area sums dominated by an earlier library match.]

  Description [Input phases are expressed in canonical variable order, so
  pin permutations share a sum.  Floating-point addition order can differ
  between permutations; pruning changes the area heuristic by roundoff.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_LibraryFlags( Nf2_Man_t * p )
{
    int t,i,Size,Slot,Config,Old,Gate,*Bins,*Keys,k,Key; unsigned Hash;
    Vec_Int_t * Matches, * Flags;
    p->Data.vMatchFlags=Vec_WecStart(Vec_WecSize(p->Data.vTt2Match));
    Vec_WecForEachLevel(p->Data.vTt2Match,Matches,t)
    {
        Flags=Vec_WecEntry(p->Data.vMatchFlags,t);
        Vec_IntFill(Flags,Vec_IntSize(Matches)/2,3);
        if ( !Vec_IntSize(Matches) ) continue;
        Size=16; while ( Size<Vec_IntSize(Matches) ) Size*=2;
        Bins=ABC_CALLOC(int,Size);
        Keys=ABC_ALLOC(int,Vec_IntSize(Matches)/2);
        for ( i=0; i<Vec_IntSize(Matches)/2; i++ )
        {
            Nf2_Cfg_t Cfg=Nf2_Int2Cfg(Vec_IntEntry(Matches,2*i+1));
            Gate=Vec_IntEntry(Matches,2*i); Key=Cfg.fCompl;
            for ( k=0; k<(int)p->pCells[Gate].nFanins; k++ )
                Key|=Nf2_CfgCompl(Cfg,k)<<(1+Nf2_CfgVar(Cfg,k));
            Keys[i]=Key;
        }
        for ( i=0; i<Vec_IntSize(Matches)/2; i++ )
        {
            Gate=Vec_IntEntry(Matches,2*i); Config=Keys[i];
            Hash=(unsigned)Config*12582917u; Slot=(Hash^(Hash>>16))&(Size-1);
            while ( Bins[Slot] && Keys[Bins[Slot]-1]!=Config ) Slot=(Slot+1)&(Size-1);
            if ( Bins[Slot] )
            {
                Old=Vec_IntEntry(Matches,2*(Bins[Slot]-1));
                if ( p->pCells[Old].AreaF<=p->pCells[Gate].AreaF ) { Vec_IntWriteEntry(Flags,i,2); continue; }
            }
            Bins[Slot]=i+1;
        }
        ABC_FREE(Bins); ABC_FREE(Keys);
    }
}
/**Function*************************************************************

  Synopsis    [Copies immutable library truths and matches into private storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_PrivateMatches( Nf2_Man_t * p )
{
    Vec_Mem_t * Source=p->Data.vTtMem;
    int i,Count=Vec_WecSize(p->Data.vTt2Match),Entry;
    assert(Count<=Vec_MemEntryNum(Source));
    p->Data.vTtMem=Vec_MemAlloc(1,12);
    Vec_MemHashAlloc(p->Data.vTtMem,Abc_MaxInt(10000,Count));
    for ( i=0; i<Count; i++ )
    {
        Entry=Vec_MemHashInsert(p->Data.vTtMem,Vec_MemReadEntry(Source,i));
        assert(Entry==i);
    }
    p->Data.vTt2Match=Vec_WecDup(p->Data.vTt2Match);
    Nf2_LibraryFlags(p);
    Nf2_LibraryDelayFlags(p);
}
/**Function*************************************************************

  Synopsis    [Reuses compiled data only for the same library and parameters.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_SharedAttach( Nf2_Man_t * p )
{
    if ( !Nf2_SharedValid(p, s_pNf2Shared) )
    {
        if ( Nf2_SharedValid(p, s_pNf2Previous) )
        {
            ABC_SWAP( Nf2_Shared_t *, s_pNf2Shared, s_pNf2Previous );
        }
        else
        {
            Nf2_SharedFree( s_pNf2Previous );
            s_pNf2Previous = s_pNf2Shared;
            s_pNf2Shared = NULL;
            Nf2_PrivateMatches(p);
            return 0;
        }
    }
    ABC_FREE(p->Data.vPages.pArray);
    Nf2_SharedMove(p,&s_pNf2Shared->Man);
    p->pNodeBanks=ABC_CALLOC(int,Gia_ManObjNum(p->pGia));
    p->pBindOffsets=ABC_CALLOC(int,Gia_ManObjNum(p->pGia));
    p->pNodeTemplates=ABC_CALLOC(int,Gia_ManObjNum(p->pGia));
    Vec_IntPush(&p->vBindings,0);
    return 1;
}
/**Function*************************************************************

  Synopsis    [Preserves compiled structural data after one mapping invocation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_SharedDetach( Nf2_Man_t * p )
{
    Nf2_Shared_t * S;
    if ( !s_pNf2Shared ) s_pNf2Shared=ABC_CALLOC(Nf2_Shared_t,1);
    S=s_pNf2Shared;
    if ( !S->Cells )
    {
        S->nCells=p->nCells; S->nNodes=p->Patterns.nNodes; S->K=p->pPars->nLutSize; S->Cuts=p->pPars->nCutNum;
        S->Flags=p->pPars->fPinFilter+2*p->pPars->fPinPerm+4*p->pPars->fPinQuick;
        S->Cells=ABC_ALLOC(Mio_Cell2_t,S->nCells); memcpy(S->Cells,p->pCells,S->nCells*sizeof(Mio_Cell2_t));
        S->Nodes=ABC_ALLOC(Amap_Nod_t,S->nNodes); memcpy(S->Nodes,p->Patterns.pNodes,S->nNodes*sizeof(Amap_Nod_t));
    }
    if ( p->pPars->fVerbose ) printf("Cached %d pattern banks and %d cut templates\n",p->Data.nBanks,p->Data.nTemplates);
    Nf2_SharedMove(&S->Man,p);
}
/**Function*************************************************************

  Synopsis    [Builds a node cut template and computes its initial matches.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ObjMergeOrder( Nf2_Man_t * p, int iObj )
{
    int nCuts;
    if ( Gia_ManHasChoices(p->pGia) ) Nf2_ChoiceRead(p,iObj);
    else Nf2_BankRead(p,iObj);
    *Vec_IntEntryP(&p->vCutSets,iObj)=Nf2_TemplateFind(p,iObj);
    nCuts=*Nf2_ObjCutSet(p,iObj);
    Nf2_ManCutMatch(p,iObj);
    p->nCutsTotal+=nCuts;
}
/**Function*************************************************************

  Synopsis    [Traverses the GIA with box-aware timing and library patterns.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManComputeCuts( Nf2_Man_t * p )
{
    Gia_Obj_t * pObj; int i,Arrival;
    if ( p->pManTim ) Tim_ManIncrementTravId(p->pManTim);
    Gia_ManForEachObjWithBoxes(p->pGia,pObj,i)
        if ( Gia_ObjIsBuf(pObj) ) Nf2_ObjPrepareBuf(p,pObj);
        else if ( Gia_ObjIsAnd(pObj) ) Nf2_ObjMergeOrder(p,i);
        else if ( Gia_ObjIsCi(pObj) )
        {
            Arrival=Tim_ManGetCiArrival(p->pManTim,Gia_ObjCioId(pObj));
            Nf2_ObjPrepareCi(p,i,Arrival);
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            Arrival=Nf2_ObjMatchD(p,Gia_ObjFaninId0(pObj,i),Gia_ObjFaninC0(pObj))->D;
            Tim_ManSetCoArrival(p->pManTim,Gia_ObjCioId(pObj),Arrival);
        }
}

/**Function*************************************************************

  Synopsis    [Prints mapped delay, area, and elapsed mapping time.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManPrintStats( Nf2_Man_t * p, const char * pTitle )
{
    if ( !p->pPars->fVerbose )
        return;
    printf( "%s :  ", pTitle );
    printf( "Delay =%8.2f  ",  Scl_Int2Flt(p->pPars->MapDelay) );
    printf( "Area =%12.2f  ",  p->pPars->MapAreaF );
    printf( "Gate =%6d  ",    (int)p->pPars->Area );
    printf( "Inv =%6d  ",     (int)p->nInvs );
    printf( "Edge =%7d  ",    (int)p->pPars->Edge );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
    fflush( stdout );
}
/**Function*************************************************************

  Synopsis    [Prints mapping parameters and library statistics.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManPrintInit( Nf2_Man_t * p )
{
    int nChoices;
    if ( !p->pPars->fVerbose )
        return;
    printf( "LutSize = %d  ", p->pPars->nLutSize );
    printf( "CutNum = %d  ",  p->pPars->nCutNum );
    printf( "Iter = %d  ",    p->pPars->nRounds );//+ p->pPars->nRoundsEla );
    printf( "Cells = %d  ",   p->nCells );
    printf( "Funcs = %d  ",   Vec_MemEntryNum(p->Data.vTtMem) );
    printf( "Matches = %d  ", Vec_WecSizeSize(p->Data.vTt2Match)/2 );
    printf( "And = %d  ",     Gia_ManAndNum(p->pGia) );
    nChoices = Gia_ManChoiceNum( p->pGia );
    if ( nChoices )
    printf( "Choices = %d  ", nChoices );
    printf( "\n" );
    printf( "Computing cuts...\r" );
    fflush( stdout );
}
/**Function*************************************************************

  Synopsis    [Prints cut and memory statistics after initial mapping.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManPrintQuit( Nf2_Man_t * p )
{
    if ( !p->pPars->fVerbose )
        return;
    printf( "Cuts = %lld (%.1f/node)  ", (long long)p->nCutsTotal,
        (double)p->nCutsTotal / Abc_MaxInt(1, Gia_ManAndNum(p->pGia)) );
    printf( "Banks = %d  Templates = %d\n", p->Data.nBanks, p->Data.nTemplates );
    // These are individual storage categories, not a total-memory estimate.
    printf( "Gia = %.2f MB  ", Gia_ManMemory(p->pGia) / (1<<20) );
    printf( "Cut pages = %.2f MB  ", (double)sizeof(int) * (1<<16) * Vec_PtrSize(&p->Data.vPages) / (1<<20) );
    printf( "Truth tables = %.2f MB  ", p->Data.vTtMem ? Vec_MemMemory(p->Data.vTtMem) / (1<<20) : 0.0 );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
    fflush( stdout );
}


/**Function*************************************************************

  Synopsis    [Assigns both output polarities of a zero-leaf cut.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManMatchConstant( Nf2_Man_t * p, int Id, int * pCutSet )
{
    int c, * pCut = pCutSet + 1;
    int Const = Nf2_CutFunc( pCut );
    assert( pCutSet[0] == 1 && Nf2_CutSize(pCut) == 0 && Const < 2 );
    for ( c = 0; c < 2; c++ )
    {
        Nf2_Mat_t * pD = Nf2_ObjMatchD( p, Id, c );
        Nf2_Mat_t * pA = Nf2_ObjMatchA( p, Id, c );
        pD->D = pA->D = 0;
        pD->F = pA->F = p->pCells[c ^ Const].AreaF;
        pD->CutH = pA->CutH = 1;
        pD->Gate = pA->Gate = c ^ Const;
        pD->Cfg = pA->Cfg = Nf2_Int2Cfg( 0 );
    }
}
static inline void Nf2_ObjPrepareCi( Nf2_Man_t * p, int iObj, int Time )
{
    Nf2_Mat_t * pD0 = Nf2_ObjMatchD( p, iObj, 0 );
    Nf2_Mat_t * pA0 = Nf2_ObjMatchA( p, iObj, 0 );
    Nf2_Mat_t * pD = Nf2_ObjMatchD( p, iObj, 1 );
    Nf2_Mat_t * pA = Nf2_ObjMatchA( p, iObj, 1 );
    memset(Nf2_ManObj(p,iObj),0,sizeof(Nf2_Obj_t));
    pD0->D = pA0->D = pD->D = pA->D = Time;
    pD->fCompl = 1;
    pD->D += p->InvDelayI;
    pD->F = p->InvAreaF;
    pA->fCompl = 1;
    pA->D += p->InvDelayI;
    pA->F = p->InvAreaF;
    Nf2_ObjMatchD( p, iObj, 0 )->fBest = 1;
    Nf2_ObjMatchD( p, iObj, 1 )->fBest = 1;
}
static inline void Nf2_ObjPrepareBuf( Nf2_Man_t * p, Gia_Obj_t * pObj )
{
    // get fanin info
    int iObj = Gia_ObjId( p->pGia, pObj );
    int iFanin = Gia_ObjFaninId0( pObj, iObj );
    Nf2_Mat_t * pDf = Nf2_ObjMatchD( p, iFanin, Gia_ObjFaninC0(pObj) );
    // set the direct phase
    Nf2_Mat_t * pDp = Nf2_ObjMatchD( p, iObj, 0 );
    Nf2_Mat_t * pAp = Nf2_ObjMatchA( p, iObj, 0 );
    Nf2_Mat_t * pDn = Nf2_ObjMatchD( p, iObj, 1 );
    Nf2_Mat_t * pAn = Nf2_ObjMatchA( p, iObj, 1 );
    assert( Gia_ObjIsBuf(pObj) );
    memset( Nf2_ManObj(p, iObj), 0, sizeof(Nf2_Obj_t) );
    // set the direct phase
    pDp->D = pAp->D = pDf->D;
    pDp->F = pAp->F = pDf->F; // do not pass flow???
    pDp->fBest = 1;
    // set the inverted phase
    pDn->D = pAn->D = pDf->D + p->InvDelayI;
    pDn->F = pAn->F = pDf->F + p->InvAreaF;
    pDn->fCompl = pAn->fCompl = 1;
    pDn->fBest = 1;
}
static inline int Nf2_CutRequired( Nf2_Man_t * p, int iObj, Nf2_Mat_t * pM, int * pCutSet )
{
    unsigned Nf2_PinPerm, Nf2_PinPhase, Nf2_PinDirect;
    int Nf2_PinCount, Nf2_PinLit, * Nf2_PinFans, * Nf2_PinBinds;
    Mio_Cell2_t * pCell = Nf2_ManCell( p, pM->Gate );
    int * pCut = Nf2_CutFromHandle( pCutSet, pM->CutH );
    int i, iVar, fCompl;
    int Arr, Req, Arrival = 0, Required = 0;
    Nf2_CutForEachVarCompl(p,iObj, pCut, pM->Cfg, iVar, fCompl, i )
    {
        Arr     = Nf2_ManObj(p, iVar)->M[fCompl][0].D + pCell->iDelays[i];
        Req     = Nf2_ObjRequired(p, iVar, fCompl);
        Arrival = Abc_MaxInt( Arrival, Arr );
        if ( Req < SCL_INFINITY )
            Required = Abc_MaxInt( Required, Req + pCell->iDelays[i] );
    }
    // API callers may request flexibility; the command leaves this at zero.
    return Abc_MaxInt( Required + p->pPars->nReqTimeFlex*p->InvDelayI, Arrival );
}
static inline void Nf2_ObjComputeRequired( Nf2_Man_t * p, int iObj )
{
    Nf2_Obj_t * pBest = Nf2_ManObj(p, iObj);
    int c, * pCutSet = Nf2_ObjCutSet( p, iObj );
    // Unreferenced nodes must not acquire a timing budget in area-only rounds.
    if ( p->pPars->fAreaOnly )
    {
        Nf2_ObjSetRequired( p, iObj, 0, SCL_INFINITY - 1 );
        Nf2_ObjSetRequired( p, iObj, 1, SCL_INFINITY - 1 );
        return;
    }
    for ( c = 0; c < 2; c++ )
        if ( Nf2_ObjRequired(p, iObj, c) == SCL_INFINITY )
            Nf2_ObjSetRequired( p, iObj, c, Nf2_CutRequired(p, iObj, &pBest->M[c][0], pCutSet) );
}
/**Function*************************************************************

  Synopsis    [Checks exact cost-context equality under an arrival-time shift.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_LastEqual( Nf2_Man_t * p,Nf2_Template_t * T,int * Binds,Nf2_Last_t * Last,int * Req,int * pDiff )
{
    int * OldBinds=(p->vBindings.pArray+p->pBindOffsets[Last->Root]);
    int i,c,k,Diff,Min=SCL_INFINITY,Count=p->Iter?2:1;
    Nf2_Obj_t * A,*B;
    if ( !T->nUsed ) return 0;
    A=Nf2_ManObj(p,Binds[T->Used[0]]); B=Nf2_ManObj(p,OldBinds[T->Used[0]]);
    {
        long long Delta=(long long)A->M[0][0].D-B->M[0][0].D;
        if ( Delta<-SCL_INFINITY || Delta>SCL_INFINITY ) return 0;
        Diff=(int)Delta;
    }
    for ( c=0; c<2; c++ )
    {
        if ( (Req[c]==SCL_INFINITY)!=(Last->Req[c]==SCL_INFINITY) ) return 0;
        if ( Req[c]!=SCL_INFINITY && (long long)Req[c]!=(long long)Last->Req[c]+Diff ) return 0;
    }
    for ( i=0; i<T->nUsed; i++ )
    {
        A=Nf2_ManObj(p,Binds[T->Used[i]]); B=Nf2_ManObj(p,OldBinds[T->Used[i]]);
        for ( c=0; c<2; c++ ) for ( k=0; k<Count; k++ )
        {
            if ( (long long)A->M[c][k].D!=(long long)B->M[c][k].D+Diff || A->M[c][k].F!=B->M[c][k].F ) return 0;
            Min=Abc_MinInt(Min,B->M[c][k].D);
        }
    }
    // Translation is valid only when the max-with-zero arrival computation does not clip.
    if ( Diff && ((long long)Min+p->nMinPinDelay<0 || (long long)Min+Diff+p->nMinPinDelay<0) ) return 0;
    *pDiff=Diff; return 1;
}
/**Function*************************************************************

  Synopsis    [Initializes all four physical match alternatives.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Nf2_MatchesInit( Nf2_Obj_t * Best )
{
    static const Nf2_Obj_t Empty = { {
        { {0,0,0,0,{0,0,0},SCL_INFINITY,FLT_MAX}, {0,0,0,0,{0,0,0},SCL_INFINITY,FLT_MAX} },
        { {0,0,0,0,{0,0,0},SCL_INFINITY,FLT_MAX}, {0,0,0,0,{0,0,0},SCL_INFINITY,FLT_MAX} }
    } };
    *Best=Empty;
}
/**Function*************************************************************

  Synopsis    [Stores a physical program's implementation and costs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Nf2_MatchStore( Nf2_Mat_t * M, Nf2_Prog_t * P, int Delay, float Area )
{
    M->D=Delay; M->F=Area; M->Gate=P->Gate; M->CutH=P->CutH;
    M->Cfg=Nf2_Int2Cfg(P->Config); M->Cfg.fCompl=0;
}
/**Function*************************************************************

  Synopsis    [Evaluates small initial match sets directly from the leaf records.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ProgramShort( Nf2_Man_t * p, int Id, Nf2_Template_t * T )
{
    int * Binds=p->vBindings.pArray+p->pBindOffsets[Id];
    int c,i,k,Delay; float Area;
    Nf2_Prog_t * P; Nf2_Mat_t * D, * A, * L, * L0, * L1; Mio_Cell2_t * Cell;
    for ( c=0; c<2; c++ )
    {
        D=Nf2_ObjMatchD(p,Id,c); A=Nf2_ObjMatchA(p,Id,c);
        for ( i=T->InitStarts[c]; i<T->InitStarts[c+1]; i++ )
        {
            P=T->Initial+i; Cell=p->pCells+P->Gate; Delay=0; Area=Cell->AreaF;
            // A dominated delay profile can still supply the best area match.
            if ( !P->NeedDelay )
            {
                if ( !P->NeedArea ) continue;
                for ( k=0; k<P->nFans; k++ )
                    Area+=Abc_MinFloat(1e32f,Nf2_ObjMatchD(p,Binds[P->Pins[k]>>1],P->Pins[k]&1)->F);
                Area=Abc_MinFloat(Area,1e32f);
                if ( !(A->F>Area+NF2_EPSILON) ) continue;
                for ( k=0; k<P->nFans; k++ )
                    Delay=Abc_MaxInt(Delay,Nf2_ObjMatchD(p,Binds[P->Pins[k]>>1],P->Pins[k]&1)->D+Cell->iDelays[k]);
                Nf2_MatchStore(A,P,Delay,Area);
                continue;
            }
            if ( !P->NeedArea )
            {
                for ( k=0; k<P->nFans; k++ )
                    Delay=Abc_MaxInt(Delay,Nf2_ObjMatchD(p,Binds[P->Pins[k]>>1],P->Pins[k]&1)->D+Cell->iDelays[k]);
                if ( D->D<=Delay ) continue;
                for ( k=0; k<P->nFans; k++ )
                    Area+=Abc_MinFloat(1e32f,Nf2_ObjMatchD(p,Binds[P->Pins[k]>>1],P->Pins[k]&1)->F);
                Nf2_MatchStore(D,P,Delay,Abc_MinFloat(Area,1e32f));
                continue;
            }
            if ( P->nFans==2 )
            {
                L0=Nf2_ObjMatchD(p,Binds[P->Pins[0]>>1],P->Pins[0]&1);
                L1=Nf2_ObjMatchD(p,Binds[P->Pins[1]>>1],P->Pins[1]&1);
                Delay=Abc_MaxInt(0,Abc_MaxInt(L0->D+Cell->iDelays[0],L1->D+Cell->iDelays[1]));
                Area+=Abc_MinFloat(1e32f,L0->F); Area+=Abc_MinFloat(1e32f,L1->F);
            }
            else for ( k=0; k<P->nFans; k++ )
            {
                L=Nf2_ObjMatchD(p,Binds[P->Pins[k]>>1],P->Pins[k]&1);
                Delay=Abc_MaxInt(Delay,L->D+Cell->iDelays[k]); Area+=Abc_MinFloat(1e32f,L->F);
            }
            Area=Abc_MinFloat(Area,1e32f);
            if ( D->D>Delay )
            { Nf2_MatchStore(D,P,Delay,Area); }
            if ( A->F>Area+NF2_EPSILON )
            { Nf2_MatchStore(A,P,Delay,Area); }
        }
    }
}
/**Function*************************************************************

  Synopsis    [Finds an exactly matching cost context for a completed node result.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Nf2_Last_t * Nf2_CompleteQuery( Nf2_Man_t * p,int Id,int * Required,int * pHit,int * pDiff )
{
    int Template=p->pNodeTemplates[Id],Mode=p->Iter>0,Diff=0;
    int Req[2]={p->Iter?Required[0]:SCL_INFINITY,p->Iter?Required[1]:SCL_INFINITY};
    Nf2_Template_t * T=p->Data.pTemplates[Template];
    int * Binds=p->vBindings.pArray+p->pBindOffsets[Id];
    Nf2_Last_t * Last; unsigned Hash; int First,Sample,Index,c,k; Nf2_Obj_t * O;
    if ( !Mode )
    {
        Hash=(unsigned)Template*12582917u;
        if ( T->nUsed )
        {
            Nf2_Obj_t * Q=Nf2_ManObj(p,Binds[T->Used[T->nUsed-1]]);
            O=Nf2_ManObj(p,Binds[T->Used[0]]); First=O->M[0][0].D;
            Hash^=(unsigned)Abc_Float2Int(O->M[0][0].F)*4256249u;
            Hash^=(unsigned)Abc_Float2Int(O->M[1][0].F)*741457u;
            Hash^=(unsigned)Abc_Float2Int(Q->M[0][0].F)*1610612741u;
            Hash^=(unsigned)Abc_Float2Int(Q->M[1][0].F)*805306457u;
            Hash^=((unsigned)O->M[1][0].D-(unsigned)First)*100663319u;
            Hash^=((unsigned)Q->M[0][0].D-(unsigned)First)*196613u;
            Hash^=((unsigned)Q->M[1][0].D-(unsigned)First)*24593u;
        }
    }
    else
    {
    First=T->nUsed?Nf2_ObjMatchD(p,Binds[T->Used[0]],0)->D:0;
    Hash=(unsigned)Template*12582917u;
    for ( c=0; c<2; c++ ) Hash=(Hash^(Req[c]==SCL_INFINITY?(unsigned)SCL_INFINITY:(unsigned)Req[c]-(unsigned)First))*4256249u;
    for ( Sample=0; Sample<2 && Sample<T->nUsed; Sample++ )
    {
        Index=Sample?T->nUsed-1:0; O=Nf2_ManObj(p,Binds[T->Used[Index]]);
        for ( c=0; c<2; c++ ) for ( k=0; k<=Mode; k++ )
        {
            Hash=(Hash^((unsigned)O->M[c][k].D-(unsigned)First))*12582917u;
            Hash=(Hash^(unsigned)Abc_Float2Int(O->M[c][k].F))*4256249u;
        }
    }
    }
    if ( p->Iter || p->pPars->fAreaOnly )
    {
        Hash^=(unsigned)Abc_Float2Int(Nf2_ObjFlowRefs(p,Id,0))*16777619u;
        Hash^=(unsigned)Abc_Float2Int(Nf2_ObjFlowRefs(p,Id,1))*4256249u;
    }
    Hash^=Hash>>16; Last=p->pLast+(Hash&(p->nLastCap-1)); p->nLastQueries[Mode]++;
    if ( Last->Root && Last->Round==p->Iter+1 && Last->Template==Template && Last->Hash==Hash &&
         ((!p->Iter && !p->pPars->fAreaOnly) ||
          (Nf2_ObjFlowRefs(p,Id,0)==Nf2_ObjFlowRefs(p,Last->Root,0) &&
           Nf2_ObjFlowRefs(p,Id,1)==Nf2_ObjFlowRefs(p,Last->Root,1))) && Nf2_LastEqual(p,T,Binds,Last,Req,&Diff) )
    {
        *pHit=1; *pDiff=Diff;
        p->nLastHits[Mode]++; return Last;
    }
    Last->Template=Template; Last->Hash=Hash; Last->Root=0;
    Last->Round=p->Iter+1; Last->Req[0]=Req[0]; Last->Req[1]=Req[1];
    *pHit=0; return Last;
}
/**Function*************************************************************

  Synopsis    [Evaluates compiled physical matches for delay and area flow.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ProgramMatch( Nf2_Man_t * p,int Id )
{
    Nf2_Template_t * T=p->Data.pTemplates[p->pNodeTemplates[Id]];
    Nf2_Value_t Values[2*NF2_PATTERN_MAX*NF2_PATTERN_FANS];
    int * Binds=(p->vBindings.pArray+p->pBindOffsets[Id]);
    int i,k,c,Delay,Required;
    int * Starts=p->pPars->fAreaOnly?T->PolStarts:T->InitStarts;
    Nf2_Prog_t * Initial=p->pPars->fAreaOnly?T->Programs:T->Initial;
    Nf2_Obj_t * Best=Nf2_ManObj(p,Id),* Leaf;
    float Area; Nf2_Prog_t * P; Nf2_Mat_t * D,*A; Nf2_Value_t * V; Mio_Cell2_t * Cell;
    if ( !p->Iter && !p->pPars->fAreaOnly && T->nPrograms<=NF2_DIRECT_PROGRAM_MAX )
    { Nf2_MatchesInit(Best); Nf2_ProgramShort(p,Id,T); return; }
    Nf2_MatchesInit(Best);
    if ( !p->Iter )
        for ( i=0; i<=T->nBindings; i++ )
        {
            Leaf=Nf2_ManObj(p,Binds[i]);
            for ( c=0; c<2; c++ )
            {
                V=Values+2*i+c; V->D=Leaf->M[c][0].D;
                V->F=Abc_MinFloat(1e32f,Leaf->M[c][0].F);
            }
        }
    else
    for ( i=0; i<=T->nBindings; i++ )
    {
        Leaf=Nf2_ManObj(p,Binds[i]);
        for ( c=0; c<2; c++ )
        {
            V=Values+2*i+c; V->D=Leaf->M[c][0].D; V->A=Leaf->M[c][1].D;
            V->F=Abc_MinFloat(1e32f,Leaf->M[c][0].F); V->G=Abc_MinFloat(1e32f,Leaf->M[c][1].F);
        }
    }
    for ( c=0; c<2; c++ )
    {
        D=&Best->M[c][0]; A=&Best->M[c][1]; Required=p->Iter?Nf2_ObjRequired(p,Id,c):SCL_INFINITY;
        if ( !p->Iter )
        {
            for ( i=Starts[c]; i<Starts[c+1]; i++ )
            {
                P=Initial+i; Cell=p->pCells+P->Gate; Delay=0; Area=Cell->AreaF;
                // Compute this delay only if its independent area choice improves.
                if ( !P->NeedDelay && !p->pPars->fAreaOnly )
                {
                    if ( !P->NeedArea ) continue;
                    for ( k=0; k<P->nFans; k++ ) Area+=Values[P->Pins[k]].F;
                    Area=Abc_MinFloat(Area,1e32f);
                    if ( !(A->F>Area+NF2_EPSILON) ) continue;
                    for ( k=0; k<P->nFans; k++ )
                        Delay=Abc_MaxInt(Delay,Values[P->Pins[k]].D+Cell->iDelays[k]);
                    Nf2_MatchStore(A,P,Delay,Area);
                    continue;
                }
                if ( !P->NeedArea && !p->pPars->fAreaOnly )
                {
                    for ( k=0; k<P->nFans; k++ )
                        Delay=Abc_MaxInt(Delay,Values[P->Pins[k]].D+Cell->iDelays[k]);
                    if ( D->D<=Delay ) continue;
                    for ( k=0; k<P->nFans; k++ ) Area+=Values[P->Pins[k]].F;
                    Nf2_MatchStore(D,P,Delay,Abc_MinFloat(Area,1e32f));
                    continue;
                }
                for ( k=0; k<P->nFans; k++ )
                { V=Values+P->Pins[k]; Delay=Abc_MaxInt(Delay,V->D+Cell->iDelays[k]); Area+=V->F; }
                Area=Abc_MinFloat(Area,1e32f);
                if ( D->D>Delay )
                { Nf2_MatchStore(D,P,Delay,Area); }
                if ( p->pPars->fAreaOnly ? (A->F>Area || (A->F==Area && A->D>Delay)) : A->F>Area+NF2_EPSILON )
                { Nf2_MatchStore(A,P,Delay,Area); }
            }
        }
        else
        {
            for ( i=T->PolStarts[c]; i<T->PolStarts[c+1]; i++ )
            {
                P=T->Programs+i; Cell=p->pCells+P->Gate; Delay=0; Area=Cell->AreaF;
                for ( k=0; k<P->nFans; k++ )
                {
                    V=Values+P->Pins[k];
                    if ( Required!=SCL_INFINITY && V->A+Cell->iDelays[k]<=Required )
                    { Delay=Abc_MaxInt(Delay,V->A+Cell->iDelays[k]); Area+=V->G; }
                    else
                    {
                        if ( D->D<SCL_INFINITY && A->D<SCL_INFINITY && V->D+Cell->iDelays[k]>Required ) break;
                        Delay=Abc_MaxInt(Delay,V->D+Cell->iDelays[k]); Area+=V->F;
                    }
                }
                if ( k<P->nFans ) continue;
                Area=Abc_MinFloat(Area,1e32f);
                if ( D->D>Delay )
                { Nf2_MatchStore(D,P,Delay,Area); }
                if ( p->pPars->fAreaOnly ? (A->F>Area || (A->F==Area && A->D>Delay)) : A->F>Area+NF2_EPSILON )
                { Nf2_MatchStore(A,P,Delay,Area); }
            }
        }
    }

}
/**Function*************************************************************

  Synopsis    [Selects physical matches and inverter implementations for a node.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManCutMatch( Nf2_Man_t * p, int iObj )
{
    Nf2_Obj_t * pBest = Nf2_ManObj(p, iObj);
    Nf2_Mat_t * pDp = &pBest->M[0][0];
    Nf2_Mat_t * pDn = &pBest->M[1][0];
    Nf2_Mat_t * pAp = &pBest->M[0][1];
    Nf2_Mat_t * pAn = &pBest->M[1][1];
    float FlowRefPf  = Nf2_ObjFlowRefs(p, iObj, 0);
    float FlowRefNf  = Nf2_ObjFlowRefs(p, iObj, 1);
    int * pCutSet = Nf2_ObjCutSet( p, iObj );
    int Required[2] = {0};
    int c,k,Hit,Diff=0;
    Nf2_Last_t * Last=NULL;
    if ( p->pPars->fAreaOnly ) Required[0] = Required[1] = SCL_INFINITY - 1;
    if ( p->Iter )
    {
        Nf2_ObjComputeRequired( p, iObj );
        Required[0] = Nf2_ObjRequired( p, iObj, 0 );
        Required[1] = Nf2_ObjRequired( p, iObj, 1 );
    }
    if ( !p->Data.pTemplates[p->pNodeTemplates[iObj]]->fConstant &&
         !(!p->Iter && !p->pPars->fAreaOnly &&
           (p->InvDelayI<=0 || p->Data.pTemplates[p->pNodeTemplates[iObj]]->nPrograms<=NF2_DIRECT_PROGRAM_MAX)) )
    {
        Last=Nf2_CompleteQuery(p,iObj,Required,&Hit,&Diff);
        if ( Hit )
        {
            // Initial delay selection is independent of the root flow divisor.
            // With positive inverter delay and zero required times, only the
            // delay alternatives can introduce an opposite-polarity inverter.
            // This also assumes nonnegative input arrivals: negative arrivals
            // can enable an area-slot inverter in round zero, as in &nf.
            *pBest=*Nf2_ManObj(p,Last->Root);
            if ( !p->Iter && !p->pPars->fAreaOnly &&
                 (FlowRefPf!=Nf2_ObjFlowRefs(p,Last->Root,0) || FlowRefNf!=Nf2_ObjFlowRefs(p,Last->Root,1)) )
                for ( c=0; c<2; c++ ) for ( k=0; k<2; k++ )
                    pBest->M[c][k].F=pBest->M[c][k].fCompl ?
                        Last->RawF[2*(!c)]/Nf2_ObjFlowRefs(p,iObj,!c)+p->InvAreaF :
                        Last->RawF[2*c+k]/Nf2_ObjFlowRefs(p,iObj,c);
            for ( c=0; c<2; c++ ) for ( k=0; k<2; k++ )
                if ( pBest->M[c][k].D<SCL_INFINITY ) pBest->M[c][k].D+=Diff;
            return;
        }
    }
    // Later flow rounds can change both delay and area implementations;
    // retaining only the first round's delay choice blocks area recovery.
    if ( p->Data.pTemplates[p->pNodeTemplates[iObj]]->fConstant )
    {
        Nf2_MatchesInit(pBest);
        Nf2_ManMatchConstant(p,iObj,pCutSet);
    }
    else
        Nf2_ProgramMatch(p,iObj);

    if ( Last ) for ( c=0; c<2; c++ ) for ( k=0; k<2; k++ )
        Last->RawF[2*c+k]=pBest->M[c][k].F;
    // divide by ref count
    pDp->F/=FlowRefPf; pDn->F/=FlowRefNf;
    pAp->F/=FlowRefPf; pAn->F/=FlowRefNf;

    // add the inverters
    assert( pDp->D < SCL_INFINITY || pDn->D < SCL_INFINITY );
    if ( pDp->D > pDn->D + p->InvDelayI )
    {
        *pDp = *pDn;
        pDp->D += p->InvDelayI;
        pDp->F += p->InvAreaF;
        pDp->fCompl = 1;
        if ( pAp->D == SCL_INFINITY )
            *pAp = *pDp;
    }
    else if ( pDn->D > pDp->D + p->InvDelayI )
    {
        *pDn = *pDp;
        pDn->D += p->InvDelayI;
        pDn->F += p->InvAreaF;
        pDn->fCompl = 1;
        if ( pAn->D == SCL_INFINITY )
            *pAn = *pDn;
    }
    // try replacing pos with neg
    if ( pAp->D == SCL_INFINITY || (pAp->F > pAn->F + p->InvAreaF + NF2_EPSILON && pAn->D + p->InvDelayI <= Required[0]) )
    {
        assert( p->Iter > 0 || p->pPars->fAreaOnly );
        *pAp = *pAn;
        pAp->D += p->InvDelayI;
        pAp->F += p->InvAreaF;
        pAp->fCompl = 1;
        if ( pDp->D == SCL_INFINITY )
            *pDp = *pAp;
    }
    // try replacing neg with pos
    else if ( pAn->D == SCL_INFINITY || (pAn->F > pAp->F + p->InvAreaF + NF2_EPSILON && pAp->D + p->InvDelayI <= Required[1]) )
    {
        assert( p->Iter > 0 || p->pPars->fAreaOnly );
        *pAn = *pAp;
        pAn->D += p->InvDelayI;
        pAn->F += p->InvAreaF;
        pAn->fCompl = 1;
        if ( pDn->D == SCL_INFINITY )
            *pDn = *pAn;
    }


    assert( pDp->D < SCL_INFINITY );
    assert( pDn->D < SCL_INFINITY );
    assert( pAp->D < SCL_INFINITY );
    assert( pAn->D < SCL_INFINITY );

    assert( pDp->F < FLT_MAX );
    assert( pDn->F < FLT_MAX );
    assert( pAp->F < FLT_MAX );
    assert( pAn->F < FLT_MAX );
    // Area-only mapping propagates the area choices in the forward pass too.
    // Subsequent exact-area trials use delay only to break equal-area ties.
    if ( p->pPars->fAreaOnly )
    {
        *pDp = *pAp;
        *pDn = *pAn;
    }
    if ( Last ) Last->Root=iObj;
}

/**Function*************************************************************

  Synopsis    [Performs a forward area-flow recovery round.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManComputeMapping( Nf2_Man_t * p )
{
    Gia_Obj_t * pObj; int i, arrTime;
    if ( p->pManTim )
        Tim_ManIncrementTravId( p->pManTim );
    Gia_ManForEachObjWithBoxes( p->pGia, pObj, i )
        if ( Gia_ObjIsBuf(pObj) )
            Nf2_ObjPrepareBuf( p, pObj );
        else if ( Gia_ObjIsAnd(pObj) )
            Nf2_ManCutMatch( p, i );
        else if ( Gia_ObjIsCi(pObj) ) {
            arrTime = Tim_ManGetCiArrival( p->pManTim, Gia_ObjCioId(pObj) );
            Nf2_ObjPrepareCi( p, i, arrTime );
        }
        else if ( Gia_ObjIsCo(pObj) ) {
            arrTime = Nf2_ObjMatchD( p, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninC0(pObj) )->D;
            Tim_ManSetCoArrival( p->pManTim, Gia_ObjCioId(pObj), arrTime );
        }
}


/**Function*************************************************************

  Synopsis    [Assigns required times to primary and box outputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManSetOutputRequireds( Nf2_Man_t * p, int fPropCompl )
{
    Gia_Obj_t * pObj;
    int Required = 0, MapDelayOld = p->pPars->MapDelay;
    int fUseConMan = Scl_ConIsRunning() && Scl_ConHasOutReqs();
    int i, iObj, fCompl, nLits = 2*Gia_ManObjNum(p->pGia);
    Vec_IntFill( &p->vRequired, nLits, SCL_INFINITY );
    // compute delay
    p->pPars->MapDelay = 0;
    Gia_ManForEachCoWithBoxes( p->pGia, pObj, i )
    {
        Required = Nf2_ObjMatchD( p, Gia_ObjFaninId0p(p->pGia, pObj), Gia_ObjFaninC0(pObj) )->D;
        p->pPars->MapDelay = Abc_MaxInt( p->pPars->MapDelay, Required );
    }
    if ( !p->pPars->fAreaOnly && p->Iter && MapDelayOld < p->pPars->MapDelay && p->pGia->vOutReqs == NULL )
        printf( "******** Critical delay violation %.2f -> %.2f ********\n", Scl_Int2Flt(MapDelayOld), Scl_Int2Flt(p->pPars->MapDelay) );
    if ( !p->pPars->fAreaOnly )
        p->pPars->MapDelay = Abc_MaxInt( p->pPars->MapDelay, MapDelayOld );
    // check delay target
    if ( !p->pPars->fAreaOnly && p->pPars->MapDelayTarget == 0 && p->pPars->nRelaxRatio )
        p->pPars->MapDelayTarget = p->pPars->MapDelay * (100 + p->pPars->nRelaxRatio) / 100;
    if ( !p->pPars->fAreaOnly && p->pPars->MapDelayTarget > 0 )
    {
        if ( p->pPars->MapDelay < p->pPars->MapDelayTarget )
            p->pPars->MapDelay = p->pPars->MapDelayTarget;
        else if ( p->pPars->MapDelay > p->pPars->MapDelayTarget && p->pPars->nRelaxRatio == 0 && !p->Iter )
            Abc_Print( 0, "Relaxing user-specified delay target from %.2f to %.2f.\n", Scl_Int2Flt(p->pPars->MapDelayTarget), Scl_Int2Flt(p->pPars->MapDelay) );
    }
    // set required times
    if ( p->pManTim )
        Tim_ManIncrementTravId( p->pManTim );
    Gia_ManForEachCoWithBoxes( p->pGia, pObj, i )
    {
        iObj     = Gia_ObjFaninId0p(p->pGia, pObj);
        fCompl   = Gia_ObjFaninC0(pObj);
        Required = Nf2_ObjMatchD(p, iObj, fCompl)->D;
        // The command uses the global target; per-output relaxation is API-only.
        Required = p->pPars->fDoAverage ? Required * (100 + p->pPars->nRelaxRatio) / 100 : p->pPars->MapDelay;
        // if external required time can be achieved, use it
        if ( p->pPars->fAreaOnly )
            // Reserve SCL_INFINITY for an unassigned match or required time.
            Required = SCL_INFINITY - 1;
        else if ( fUseConMan )
        {
            if ( Scl_ConGetOutReq(i) > 0 && Required <= Scl_ConGetOutReq(i) )
                Required = Scl_ConGetOutReq(i);
        }
        else if ( p->pGia->vOutReqs )
        {
            int NewRequired = Scl_Flt2Int(Vec_FltEntry(p->pGia->vOutReqs, i));
            if ( NewRequired > 0 && Required <= NewRequired )
                Required = Abc_MinInt( 2*Required, NewRequired );
        }
        // if external required cannot be achieved, set the earliest possible arrival time
//        else if ( p->pGia->vOutReqs && Vec_FltEntry(p->pGia->vOutReqs, i) > 0 && Required > Vec_FltEntry(p->pGia->vOutReqs, i) )
//            ptTime->Rise = ptTime->Fall = ptTime->Worst = Required;
        // otherwise, set the global required time
        Nf2_ObjUpdateRequired( p, iObj, fCompl, Required );
        if ( fPropCompl && iObj > 0 && Nf2_ObjMatchD(p, iObj, fCompl)->fCompl )
            Nf2_ObjUpdateRequired( p, iObj, !fCompl, Required - p->InvDelayI );

        if ( p->pManTim == NULL )
            continue;
        if ( fPropCompl && iObj > 0 && Nf2_ObjMatchD(p, iObj, fCompl)->fCompl )
            Tim_ManSetCoRequired( p->pManTim, Gia_ObjCioId(pObj), Required - p->InvDelayI );
        else
            Tim_ManSetCoRequired( p->pManTim, Gia_ObjCioId(pObj), Required );
    }
}
/**Function*************************************************************

  Synopsis    [Selects a feasible implementation and propagates its references.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManSetMapRefsGate( Nf2_Man_t * p, int iObj, int Required, Nf2_Mat_t * pM )
{
    unsigned Nf2_PinPerm, Nf2_PinPhase, Nf2_PinDirect;
    int Nf2_PinCount, Nf2_PinLit, * Nf2_PinFans, * Nf2_PinBinds;
    int k, iVar, fCompl;
    Mio_Cell2_t * pCell = Nf2_ManCell( p, pM->Gate );
    int * pCut = Nf2_CutFromHandle( Nf2_ObjCutSet(p, iObj), pM->CutH );
    Nf2_CutForEachVarCompl(p,iObj, pCut, pM->Cfg, iVar, fCompl, k )
    {
        Nf2_ObjMapRefInc( p, iVar, fCompl );
        Nf2_ObjUpdateRequired( p, iVar, fCompl, Required - pCell->iDelays[k] );
    }
    assert( Nf2_CutSize(pCut) == (int)pCell->nFanins );
    // update global stats
    p->pPars->MapAreaF += pCell->AreaF;
    p->pPars->Edge += Nf2_CutSize(pCut);
    p->pPars->Area++;
    // update status of the gate
    assert( pM->fBest == 0 );
    pM->fBest = 1;
}

/**Function*************************************************************

  Synopsis    [Builds the mapped cover and propagates required times.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_ManSetMapRefs( Nf2_Man_t * p )
{
    float Coef = 1.0 / (1.0 + (p->Iter + 1) * (p->Iter + 1));
    float * pFlowRefs = Vec_FltArray( &p->vFlowRefs );
    Nf2_Ref_t * pMapRefs=p->pRefs;
    int nLits = 2*Gia_ManObjNum(p->pGia);
    int i, c, Id, nRefs[2], reqTime;
    Gia_Obj_t * pObj;
    Nf2_Mat_t * pD, * pA, * pM;
    Nf2_Mat_t * pDs[2], * pAs[2], * pMs[2];
    int Required = 0, Requireds[2];
    assert( !p->fUseEla );
    Nf2_ManSetOutputRequireds( p, 0 );
    // set output references
    memset( pMapRefs, 0, sizeof(Nf2_Ref_t) * nLits );
    Gia_ManForEachCo( p->pGia, pObj, i )
        Nf2_ObjMapRefInc( p, Gia_ObjFaninId0p(p->pGia, pObj), Gia_ObjFaninC0(pObj));

    // compute area and edges
    p->nInvs = 0;
    p->pPars->MapAreaF = 0;
    p->pPars->Area = p->pPars->Edge = 0;
    Gia_ManForEachObjReverseWithBoxes( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            if ( Nf2_ObjMapRefNum(p, i, 1) )
            {
                Nf2_ObjMapRefInc( p, i, 0 );
                Nf2_ObjUpdateRequired( p, i, 0, Nf2_ObjRequired(p, i, 1) - p->InvDelayI );
                p->pPars->MapAreaF += p->InvAreaF;
                p->pPars->Edge++;
                p->pPars->Area++;
                p->nInvs++;
            }
            Nf2_ObjUpdateRequired( p, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninC0(pObj), Nf2_ObjRequired(p, i, 0) );
            Nf2_ObjMapRefInc( p, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninC0(pObj));
            continue;
        }
        if ( Gia_ObjIsCi(pObj) )
        {
            if ( Nf2_ObjMapRefNum(p, i, 1) )
            {
                Nf2_ObjMapRefInc( p, i, 0 );
                Nf2_ObjUpdateRequired( p, i, 0, Nf2_ObjRequired(p, i, 1) - p->InvDelayI );
                p->pPars->MapAreaF += p->InvAreaF;
                p->pPars->Edge++;
                p->pPars->Area++;
                p->nInvs++;
            }
            Tim_ManSetCiRequired( p->pManTim, Gia_ObjCioId(pObj), Nf2_ObjRequired(p, i, 0) );
            continue;
        }
        if ( Gia_ObjIsCo(pObj) )
        {
            reqTime = Tim_ManGetCoRequired( p->pManTim, Gia_ObjCioId(pObj) );
            Nf2_ObjUpdateRequired( p, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninC0(pObj), reqTime );
            Nf2_ObjMapRefInc( p, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninC0(pObj));
            continue;
        }
        // skip if this node is not used
        for ( c = 0; c < 2; c++ )
            nRefs[c] = Nf2_ObjMapRefNum(p, i, c);
        if ( !nRefs[0] && !nRefs[1] )
            continue;

        // consider two cases
        if ( nRefs[0] && nRefs[1] )
        {
            // find best matches for both phases
            for ( c = 0; c < 2; c++ )
            {
                Requireds[c] = Nf2_ObjRequired( p, i, c );
                pDs[c] = Nf2_ObjMatchD( p, i, c );
                pAs[c] = Nf2_ObjMatchA( p, i, c );
                pMs[c] = (pAs[c]->D <= Requireds[c]) ? pAs[c] : pDs[c];
            }
            // swap complemented matches
            if ( pMs[0]->fCompl && pMs[1]->fCompl )
            {
//                pMs[0]->fCompl = pMs[1]->fCompl = 0;
                // find best matches for both phases
                pMs[0] = Nf2_ObjMatchD( p, i, 0 );
                pMs[1] = Nf2_ObjMatchD( p, i, 1 );
                assert( !pMs[0]->fCompl || !pMs[1]->fCompl );
            }
            // check if intervers are involved
            if ( !pMs[0]->fCompl && !pMs[1]->fCompl ) // no inverters
            {
                for ( c = 0; c < 2; c++ )
                    Nf2_ManSetMapRefsGate( p, i, Requireds[c], pMs[c] );
            }
            else
            {
                // one interver
                assert( !pMs[0]->fCompl || !pMs[1]->fCompl );
                c = pMs[1]->fCompl;
                assert( pMs[c]->fCompl && !pMs[!c]->fCompl );
                // update this phase
                pM = pMs[c];
                pM->fBest = 1;
                Required = Requireds[c];
                // update opposite phase
                Nf2_ObjMapRefInc( p, i, !c );
                Nf2_ObjUpdateRequired( p, i, !c, Required - p->InvDelayI );
                // select opposite phase
                Required = Nf2_ObjRequired( p, i, !c );
                pD = Nf2_ObjMatchD( p, i, !c );
                pA = Nf2_ObjMatchA( p, i, !c );
                pM = (pA->D <= Required) ? pA : pD;
                assert( !pM->fCompl );
                // create gate
                Nf2_ManSetMapRefsGate( p, i, Required, pM );
                // account for the inverter
                p->pPars->MapAreaF += p->InvAreaF;
                p->pPars->Edge++;
                p->pPars->Area++;
                p->nInvs++;
            }
        }
        else
        {
            c = (int)(nRefs[1] > 0);
            assert( nRefs[c] && !nRefs[!c] );
            // consider this phase
            Required = Nf2_ObjRequired( p, i, c );
            pD = Nf2_ObjMatchD( p, i, c );
            pA = Nf2_ObjMatchA( p, i, c );
            pM = (pA->D <= Required) ? pA : pD;
            if ( pM->fCompl ) // use inverter
            {
                p->nInvs++;
                pM->fBest = 1;
                // update opposite phase
                Nf2_ObjMapRefInc( p, i, !c );
                Nf2_ObjUpdateRequired( p, i, !c, Required - p->InvDelayI );
                // select opposite phase
                Required = Nf2_ObjRequired( p, i, !c );
                pD = Nf2_ObjMatchD( p, i, !c );
                pA = Nf2_ObjMatchA( p, i, !c );
                pM = (pA->D <= Required) ? pA : pD;
                assert( !pM->fCompl );
                // account for the inverter
                p->pPars->MapAreaF += p->InvAreaF;
                p->pPars->Edge++;
                p->pPars->Area++;
            }
            // create gate
            Nf2_ManSetMapRefsGate( p, i, Required, pM );
        }
        // the result of this:
        // - only one phase can be implemented as inverter of the other phase
        // - required times are propagated correctly
        // - references are set correctly
    }
    Gia_ManForEachCiIdWithBoxes( p->pGia, Id, i )
        if ( Nf2_ObjMapRefNum(p, Id, 1) )
        {
            Nf2_ObjMapRefInc( p, Id, 0 );
            Nf2_ObjUpdateRequired( p, Id, 0, Nf2_ObjRequired(p, Id, 1) - p->InvDelayI );
            p->pPars->MapAreaF += p->InvAreaF;
            p->pPars->Edge++;
            p->pPars->Area++;
            p->nInvs++;
        }
    // Exact-area recovery does not consume area-flow reference estimates.
    if ( p->Iter + 1 < p->pPars->nRounds )
    for ( i = 0; i < nLits; i++ )
        pFlowRefs[i] = Abc_MaxFloat(1.0, Coef * pFlowRefs[i] + (1.0 - Coef) * Abc_MaxFloat(1, pMapRefs[i].Count));
//        pFlowRefs[i] = 0.2 * pFlowRefs[i] + 0.8 * Abc_MaxFloat(1, pMapRefs[i].Count);
    return p->pPars->Area;
}


/**Function*************************************************************

  Synopsis    [Dereferences the old cover and counts cells that become unused.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf2_MatchDeref_rec( Nf2_Man_t * p, int i, int c, Nf2_Mat_t * pM )
{
    unsigned Nf2_PinPerm, Nf2_PinPhase, Nf2_PinDirect;
    int Nf2_PinCount, Nf2_PinLit, * Nf2_PinFans, * Nf2_PinBinds;
    word Area = 0;
    int k, iVar, fCompl, * pCut;
    assert( pM->fBest );
    if ( pM->fCompl )
    {
        assert( Nf2_ObjMapRefNum(p, i, !c) > 0 );
        if ( !Nf2_ObjMapRefDec(p, i, !c) )
            Area += Nf2_MatchDeref_rec( p, i, !c, Nf2_ObjMatchD(p, i, !c) );
        return Area + p->InvAreaW;
    }
    if ( Nf2_ObjCutSetId(p, i) == 0 )
        return 0;
    pCut = Nf2_CutFromHandle( Nf2_ObjCutSet(p, i), pM->CutH );
    Nf2_CutForEachVarCompl(p,i, pCut, pM->Cfg, iVar, fCompl, k )
    {
        assert( Nf2_ObjMapRefNum(p, iVar, fCompl) > 0 );
        if ( !Nf2_ObjMapRefDec(p, iVar, fCompl) )
            Area += Nf2_MatchDeref_rec( p, iVar, fCompl, Nf2_ObjMatchD(p, iVar, fCompl) );
    }
    return Area + Nf2_ManCell(p, pM->Gate)->AreaW;
}
/**Function*************************************************************

  Synopsis    [References a selected cover and propagates required times.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_MatchRef_rec( Nf2_Man_t * p, int i, int c, Nf2_Mat_t * pM, int Required )
{
    unsigned Nf2_PinPerm, Nf2_PinPhase, Nf2_PinDirect;
    int Nf2_PinCount, Nf2_PinLit, * Nf2_PinFans, * Nf2_PinBinds;
    int ReqFanin;
    int k, iVar, fCompl, * pCut;
    assert( pM->fBest );
    assert( pM->D <= Required );
    if ( pM->fCompl )
    {
        ReqFanin = Required - p->InvDelayI;
        assert( Nf2_ObjMapRefNum(p, i, !c) >= 0 );
        if ( !Nf2_ObjMapRefInc(p, i, !c) )
            Nf2_MatchRef_rec( p, i, !c, Nf2_ObjMatchD(p, i, !c), ReqFanin );
        return;
    }
    if ( Nf2_ObjCutSetId(p, i) == 0 )
        return;
    pCut = Nf2_CutFromHandle( Nf2_ObjCutSet(p, i), pM->CutH );
    Nf2_CutForEachVarCompl(p,i, pCut, pM->Cfg, iVar, fCompl, k )
    {
        ReqFanin = Required - Nf2_ManCell(p, pM->Gate)->iDelays[k];
        assert( Nf2_ObjMapRefNum(p, iVar, fCompl) >= 0 );
        if ( !Nf2_ObjMapRefInc(p, iVar, fCompl) )
            Nf2_MatchRef_rec( p, iVar, fCompl, Nf2_ObjMatchD(p, iVar, fCompl), ReqFanin );
    }
}
/**Function*************************************************************

  Synopsis    [Considers the constant cell during exact-area recovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManElaConstant( Nf2_Man_t * p, int c, int * pCutSet, Nf2_Mat_t * pRes, word * pAreaBest )
{
    Nf2_Mat_t Match;
    int * pCut = pCutSet + 1;
    int Const = Nf2_CutFunc( pCut );
    assert( pCutSet[0] == 1 && Nf2_CutSize(pCut) == 0 && Const < 2 );
    memset( &Match, 0, sizeof(Match) );
    Match.F = p->pCells[c ^ Const].AreaF;
    Match.CutH = 1;
    Match.Gate = c ^ Const;
    Match.fBest = 1;
    if ( p->pCells[c ^ Const].AreaW < *pAreaBest ||
         (p->pCells[c ^ Const].AreaW == *pAreaBest && pRes->D > 0) )
    {
        *pRes = Match;
        *pAreaBest = p->pCells[c ^ Const].AreaW;
    }
}
static void Nf2_TrialClear( Nf2_Man_t * p )
{
    int i;
    for ( i=0; i<2*Gia_ManObjNum(p->pGia); i++ ) p->pRefs[i].Stamp=0;
}
static word Nf2_TrialCost_rec( Nf2_Man_t * p,int Lit,word Limit );
static inline word Nf2_TrialCost( Nf2_Man_t * p,int Lit,word Limit )
{
    if ( p->pRefs[Lit].Count || p->pRefs[Lit].Stamp==p->TrialStamp ) return 0;
    return Nf2_TrialCost_rec(p,Lit,Limit);
}
/**Function*************************************************************

  Synopsis    [Counts newly referenced cells until the candidate exceeds its bound.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf2_TrialCost_rec( Nf2_Man_t * p,int Lit,word Limit )
{
    unsigned Nf2_PinPerm, Nf2_PinPhase, Nf2_PinDirect;
    int Nf2_PinCount, Nf2_PinLit, * Nf2_PinFans, * Nf2_PinBinds;
    Nf2_Mat_t * M; int Id=Lit>>1,*Cut,k,Leaf,Pol;
    word Cost;
    p->pRefs[Lit].Stamp=p->TrialStamp; M=Nf2_ObjMatchD(p,Id,Lit&1);
    if ( M->fCompl )
    {
        Cost=p->InvAreaW;
        if ( Cost<=Limit ) Cost+=Nf2_TrialCost(p,Lit^1,Limit-Cost);
        return Cost;
    }
    if ( !Nf2_ObjHasCuts(p,Id) ) return 0;
    Cost=p->pCells[M->Gate].AreaW;
    if ( Cost>Limit ) return Cost;
    Cut=Nf2_CutFromHandle(Nf2_ObjCutSet(p,Id),M->CutH);
    Nf2_CutForEachVarCompl(p,Id,Cut,M->Cfg,Leaf,Pol,k)
    {
        Cost+=Nf2_TrialCost(p,2*Leaf+Pol,Limit-Cost);
        if ( Cost>Limit ) break;
    }
    return Cost;
}
static inline void Nf2_TrialAdd( Nf2_Man_t * p,int Lit,word * Cost,word Limit )
{
    if ( *Cost<=Limit ) *Cost+=Nf2_TrialCost(p,Lit,Limit-*Cost);
}
/**Function*************************************************************

  Synopsis    [Computes bounded fanin area with sharing counted once per trial.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf2_TrialBound( Nf2_Man_t * p,int * Binds,Nf2_Prog_t * P,word Limit )
{
    word Cost=0; int k;
    if ( ++p->TrialStamp==0 ) { Nf2_TrialClear(p); p->TrialStamp=1; }
    for ( k=0; k<P->nFans; k++ )
    {
        Nf2_TrialAdd(p,2*Binds[P->Pins[k]>>1]+(P->Pins[k]&1),&Cost,Limit);
        if ( Cost>Limit ) break;
    }
    return Cost;
}
/**Function*************************************************************

  Synopsis    [Searches feasible cell matches using bounded exact-area trials.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ProgramEla( Nf2_Man_t * p,int Id,int c,Nf2_Mat_t * Res,int Required,word * pAreaBest )
{
    Nf2_Template_t * T=p->Data.pTemplates[p->pNodeTemplates[Id]]; Nf2_Prog_t * P;
    int * Binds=(p->vBindings.pArray+p->pBindOffsets[Id]);
    int Arrivals[2*NF2_PATTERN_MAX*NF2_PATTERN_FANS],i,k,Delay,LastCut=-1;
    word TotalLimit=*pAreaBest,Total;
    int Small=TotalLimit<T->NextArea[c],nProgs=Small?T->nMin[c]:T->PolStarts[c+1]-T->PolStarts[c];
    int Direct=nProgs*3<T->nBindings+1,Arrival;
    word AreaCache[64],AreaValid=0,AreaExact=0,Limit; Nf2_Mat_t R; Mio_Cell2_t * Cell;
    // No physical implementation can fit the incumbent's exact area budget.
    if ( !nProgs || (T->nMin[c] && p->pCells[T->Programs[T->MinIds[c][0]].Gate].AreaW>TotalLimit) ) return;
    if ( !Direct )
        for ( i=0; i<=T->nBindings; i++ ) for ( k=0; k<2; k++ ) Arrivals[2*i+k]=Nf2_ObjMatchD(p,Binds[i],k)->D;
    p->nSmallEla+=Small; p->nTotalEla++;
    for ( i=0; i<nProgs; i++ )
    {
        P=T->Programs+(Small?T->MinIds[c][i]:T->PolStarts[c]+i);
        if ( P->CutH!=LastCut ) { AreaValid=AreaExact=0; LastCut=P->CutH; }
        Cell=p->pCells+P->Gate; if ( Cell->AreaW>TotalLimit ) continue; Delay=0;
        for ( k=0; k<P->nFans; k++ )
        {
            Arrival=Direct?Nf2_ObjMatchD(p,Binds[P->Pins[k]>>1],P->Pins[k]&1)->D:Arrivals[P->Pins[k]];
            Delay=Abc_MaxInt(Delay,Arrival+Cell->iDelays[k]);
            if ( Delay>Required ) break;
        }
        if ( k<P->nFans ) continue;
        memset(&R,0,sizeof(R)); R.fBest=1; Nf2_MatchStore(&R,P,Delay,0);
        Limit=TotalLimit;
        if ( Cell->AreaW>Limit ) continue;
        Limit-=Cell->AreaW;
        if ( (AreaValid&(((word)1)<<P->Phase)) && AreaCache[P->Phase]>Limit ) continue;
        if ( !(AreaExact&(((word)1)<<P->Phase)) )
        {
            AreaCache[P->Phase]=Nf2_TrialBound(p,Binds,P,Limit); AreaValid|=((word)1)<<P->Phase;
            if ( AreaCache[P->Phase]>Limit ) continue;
            AreaExact|=((word)1)<<P->Phase;
        }
        Total=AreaCache[P->Phase]+Cell->AreaW;
        R.F=(float)((double)Total/SCL_NUM);
        // Cone areas can exceed INT_MAX; compare the exact 64-bit costs.
        // Timing breaks ties only after the fixed-point areas are equal.
        if ( Total<*pAreaBest || (Total==*pAreaBest && Res->D>R.D) )
        {
            *Res=R; *pAreaBest=Total;
            TotalLimit=Total;
        }
    }
}
/**Function*************************************************************

  Synopsis    [Compares physical cells with a shared opposite-polarity driver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManElaBestMatch( Nf2_Man_t * p, int iObj, int c, Nf2_Mat_t * pRes, int Required )
{
    int * pCutSet = Nf2_ObjCutSet( p, iObj );
    word AreaBest = p->AreaInitial;
    *pRes=p->AreaOriginal; pRes->F=(float)((double)p->AreaInitial/SCL_NUM);
    {
        Nf2_Mat_t * Other=Nf2_ObjMatchD(p,iObj,!c);
        if ( !Other->fCompl && Other->D+p->InvDelayI<=Required )
        {
            word Cost=p->InvAreaW, Limit=AreaBest;
            if ( ++p->TrialStamp==0 )
            { Nf2_TrialClear(p); p->TrialStamp=1; }
            Nf2_TrialAdd(p,2*iObj+!c,&Cost,Limit);
            if ( Cost<AreaBest || (Cost==AreaBest && pRes->D>Other->D+p->InvDelayI) )
            {
                *pRes=*Other; pRes->D+=p->InvDelayI;
                pRes->F=(float)((double)Cost/SCL_NUM); pRes->fBest=1; pRes->fCompl=1;
                AreaBest=Cost;
            }
        }
    }
    if ( !p->Data.pTemplates[p->pNodeTemplates[iObj]]->fConstant ) { Nf2_ProgramEla(p,iObj,c,pRes,Required,&AreaBest); return; }
    Nf2_ManElaConstant( p, c, pCutSet, pRes, &AreaBest );
}
/**Function*************************************************************

  Synopsis    [Recomputes a selected physical cell arrival from its pins.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_ManComputeArrival( Nf2_Man_t * p, int iObj, Nf2_Mat_t * pM, int * pCutSet )
{
    unsigned Nf2_PinPerm, Nf2_PinPhase, Nf2_PinDirect;
    int Nf2_PinCount, Nf2_PinLit, * Nf2_PinFans, * Nf2_PinBinds;
    int Delay = 0;
    Nf2_Mat_t * pMfan;
    int iVar, fCompl, k;
    Mio_Cell2_t * pCell = Nf2_ManCell( p, pM->Gate );
    int * pCut = Nf2_CutFromHandle( pCutSet, pM->CutH );
    assert( !pM->fCompl );
    Nf2_CutForEachVarCompl(p,iObj, pCut, pM->Cfg, iVar, fCompl, k )
    {
        pMfan = Nf2_ObjMatchD( p, iVar, fCompl );
        Delay = Abc_MaxInt( Delay, pMfan->D + pCell->iDelays[k] );
    }
    return Delay;
}
/**Function*************************************************************

  Synopsis    [Prepares selected implementations for reverse area recovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManResetMatches( Nf2_Man_t * p, int Round )
{
    Gia_Obj_t * pObj;
    Nf2_Mat_t * pDc, * pAc, * pMfan, * pM[2];
    int i, c, Arrival, Required, fUseArea;
    // go through matches in the topo order
    if ( p->pManTim )
        Tim_ManIncrementTravId( p->pManTim );
    Gia_ManForEachObjWithBoxes( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            pMfan = Nf2_ObjMatchD( p, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninC0(pObj) );
            for ( c = 0; c < 2; c++ )
            {
                pDc = Nf2_ObjMatchD( p, i, c );
                pAc = Nf2_ObjMatchA( p, i, c );
                pDc->F = pAc->F = 0;
                pDc->D = pMfan->D + (c ? p->InvDelayI : 0);
                assert( pDc->fBest );
                assert( !pAc->fBest );
                assert( c==0 || pDc->fCompl );
            }
            continue;
        }
        if ( Gia_ObjIsCi(pObj) )
        {
            Arrival = Tim_ManGetCiArrival( p->pManTim, Gia_ObjCioId(pObj) );
            Nf2_ObjPrepareCi( p, i, Arrival );
            continue;
        }
        if ( Gia_ObjIsCo(pObj) )
        {
            Arrival = Nf2_ObjMatchD( p, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninC0(pObj) )->D;
            Tim_ManSetCoArrival( p->pManTim, Gia_ObjCioId(pObj), Arrival );
            continue;
        }
        // select the best match for each phase
        for ( c = 0; c < 2; c++ )
        {
            pDc = Nf2_ObjMatchD( p, i, c );
            pAc = Nf2_ObjMatchA( p, i, c );
            pDc->F = pAc->F = 0;
            if ( Nf2_ObjMapRefNum(p, i, c) )
            {
                assert( pDc->fBest != pAc->fBest );
                if ( pAc->fBest )
                    ABC_SWAP( Nf2_Mat_t, *pDc, *pAc );
                assert( pDc->fBest );
                assert( !pAc->fBest );
            }
            else
            {
                assert( Round > 0 || (!pDc->fBest && !pAc->fBest) );
                fUseArea = Round & 1;
                // Seed unused nodes with area choices when their current
                // fanin arrivals fit the estimated budget for the first pass.
                if ( Round == 0 && !pAc->fCompl )
                {
                    Required = Nf2_CutRequired( p, i, pDc, Nf2_ObjCutSet(p, i) );
                    fUseArea = Nf2_ManComputeArrival(p, i, pAc, Nf2_ObjCutSet(p, i)) <= Required;
                }
                if ( fUseArea && !pAc->fCompl )
                    ABC_SWAP( Nf2_Mat_t, *pDc, *pAc );
                pDc->fBest = 1;
                pAc->fBest = 0;
            }
        }
        // consider best matches of both phases
        pM[0] = Nf2_ObjMatchD( p, i, 0 );
        pM[1] = Nf2_ObjMatchD( p, i, 1 );
        assert( pM[0]->fBest && pM[1]->fBest );
        // swap complemented matches
        if ( pM[0]->fCompl && pM[1]->fCompl )
        {
            assert( 0 );
        }
        if ( !pM[0]->fCompl && !pM[1]->fCompl )
        {
            for ( c = 0; c < 2; c++ )
            {
                Arrival = Nf2_ManComputeArrival( p, i, pM[c], Nf2_ObjCutSet(p, i) );
                pM[c]->D = Arrival;
            }
        }
        else
        {
            // consider non-complemented match
            c = !pM[1]->fCompl;
            assert( !pM[c]->fCompl );
            assert( pM[!c]->fCompl );
            Arrival = Nf2_ManComputeArrival( p, i, pM[c], Nf2_ObjCutSet(p, i) );
            pM[c]->D = Arrival;
            // consider complemented match
            *pM[!c] = *pM[c];
            pM[!c]->D += p->InvDelayI;
            pM[!c]->fCompl = 1;
        }
    }
}
/**Function*************************************************************

  Synopsis    [Performs one reverse exact-area recovery pass.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManComputeMappingEla( Nf2_Man_t * p )
{
    unsigned Nf2_PinPerm, Nf2_PinPhase, Nf2_PinDirect;
    int Nf2_PinCount, Nf2_PinLit, * Nf2_PinFans, * Nf2_PinBinds;
    Gia_Obj_t * pObj;
    Mio_Cell2_t * pCell;
    Nf2_Mat_t Mb, * pMb = &Mb, * pM, * pTiming;
    word AreaBef;
    int i, c, iVar, Id, fCompl, k, * pCut, Required;
    Nf2_ManResetMatches( p, p->Iter - p->pPars->nRounds );
    Nf2_ManSetOutputRequireds( p, 1 );
    Gia_ManForEachObjReverseWithBoxes( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            int reqTime, iObj;
            if ( Nf2_ObjMapRefNum(p, i, 1) )
                Nf2_ObjUpdateRequired( p, i, 0, Nf2_ObjRequired(p, i, 1) - p->InvDelayI );
            reqTime = Nf2_ObjRequired(p, i, 0);
            iObj    = Gia_ObjFaninId0p(p->pGia, pObj);
            fCompl      = Gia_ObjFaninC0(pObj);
            Nf2_ObjUpdateRequired( p, iObj, fCompl, reqTime );
            if ( iObj > 0 && Nf2_ObjMatchD(p, iObj, fCompl)->fCompl )
                Nf2_ObjUpdateRequired( p, iObj, !fCompl, reqTime - p->InvDelayI );
            continue;
        }
        if ( Gia_ObjIsCi(pObj) )
        {
            if ( Nf2_ObjMapRefNum(p, i, 1) )
                Nf2_ObjUpdateRequired( p, i, 0, Nf2_ObjRequired(p, i, 1) - p->InvDelayI );
            Tim_ManSetCiRequired( p->pManTim, Gia_ObjCioId(pObj), Nf2_ObjRequired(p, i, 0) );
            continue;
        }
        if ( Gia_ObjIsCo(pObj) )
        {
            int reqTime = Tim_ManGetCoRequired( p->pManTim, Gia_ObjCioId(pObj) );
            int iObj    = Gia_ObjFaninId0p(p->pGia, pObj);
            fCompl      = Gia_ObjFaninC0(pObj);
            Nf2_ObjUpdateRequired( p, iObj, fCompl, reqTime );
            if ( iObj > 0 && Nf2_ObjMatchD(p, iObj, fCompl)->fCompl )
                Nf2_ObjUpdateRequired( p, iObj, !fCompl, reqTime - p->InvDelayI );
            continue;
        }
        for ( c = 0; c < 2; c++ )
        if ( Nf2_ObjMapRefNum(p, i, c) )
        {
            pM = Nf2_ObjMatchD( p, i, c );
            Required = Nf2_ObjRequired( p, i, c );
            assert( pM->D <= Required );
            if ( pM->fCompl && Nf2_ObjMapRefNum(p,i,!c)>1 )
            {
                Nf2_Template_t * T=p->Data.pTemplates[p->pNodeTemplates[i]];
                if ( !T->fConstant && (!T->nMin[c] ||
                    p->pCells[T->Programs[T->MinIds[c][0]].Gate].AreaW>p->InvAreaW) ) continue;
            }
            // The trial dereferences an exclusive opposite-phase driver too.
            AreaBef = Nf2_MatchDeref_rec( p, i, c, pM );
            assert( pM->fBest );
            p->AreaOriginal=*pM; p->AreaInitial=AreaBef;
            Nf2_ManElaBestMatch( p, i, c, pMb, Required );
            Nf2_MatchRef_rec( p, i, c, pMb, Required );
            // set best match
            assert( pMb->fBest );
            assert( pMb->D <= Required );
            *pM = *pMb;
            pTiming=pM;
            if ( pM->fCompl )
            {
                Required-=p->InvDelayI;
                Nf2_ObjUpdateRequired(p,i,!c,Required);
                pTiming=Nf2_ObjMatchD(p,i,!c);
                assert(!pTiming->fCompl);
            }
            // Propagate through the physical opposite phase even if it was
            // processed earlier in this round.
            pCell = Nf2_ManCell( p, pTiming->Gate );
            pCut = Nf2_CutFromHandle( Nf2_ObjCutSet(p, i), pTiming->CutH );
            Nf2_CutForEachVarCompl(p,i, pCut, pTiming->Cfg, iVar, fCompl, k )
            {
                pM = Nf2_ObjMatchD( p, iVar, fCompl );
                assert( pM->D <= Required - pCell->iDelays[k] );
                Nf2_ObjUpdateRequired( p, iVar, fCompl, Required - pCell->iDelays[k] );
                if ( pM->fCompl )
                {
                    pM = Nf2_ObjMatchD( p, iVar, !fCompl );
                    assert( pM->D <= Required - pCell->iDelays[k] - p->InvDelayI );
                    Nf2_ObjUpdateRequired( p, iVar, !fCompl, Required - pCell->iDelays[k] - p->InvDelayI );
                }
            }
        }
    }
    Gia_ManForEachCiIdWithBoxes( p->pGia, Id, i )
        if ( Nf2_ObjMapRefNum(p, Id, 1) )
        {
            Required = Nf2_ObjRequired( p, Id, 1 );
            Nf2_ObjUpdateRequired( p, Id, 0, Required - p->InvDelayI );
        }
}
/**Function*************************************************************

  Synopsis    [Refreshes arrivals of the final referenced implementations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManFinalTiming( Nf2_Man_t * p )
{
    Gia_Obj_t * Obj; Nf2_Mat_t * M; int Id,c,Delay;
    if ( p->pManTim ) { Nf2_ManResetMatches(p,2); return; }
    // Exact-area recovery has already selected the D slot for every phase.
    // Reference counts close over fanins, so unused phases need no timing.
    Gia_ManForEachAnd(p->pGia,Obj,Id)
    {
        if ( !Nf2_ObjMapRefNum(p,Id,0) && !Nf2_ObjMapRefNum(p,Id,1) ) continue;
        if ( Gia_ObjIsBuf(Obj) )
        {
            Delay=Nf2_ObjMatchD(p,Gia_ObjFaninId0(Obj,Id),Gia_ObjFaninC0(Obj))->D;
            Nf2_ObjMatchD(p,Id,0)->D=Delay;
            Nf2_ObjMatchD(p,Id,1)->D=Delay+p->InvDelayI;
            continue;
        }
        for ( c=0; c<2; c++ )
        {
            M=Nf2_ObjMatchD(p,Id,c);
            if ( Nf2_ObjMapRefNum(p,Id,c) && !M->fCompl )
                M->D=Nf2_ManComputeArrival(p,Id,M,Nf2_ObjCutSet(p,Id));
        }
        for ( c=0; c<2; c++ )
        {
            M=Nf2_ObjMatchD(p,Id,c);
            if ( Nf2_ObjMapRefNum(p,Id,c) && M->fCompl )
                M->D=Nf2_ObjMatchD(p,Id,!c)->D+p->InvDelayI;
        }
    }
}
/**Function*************************************************************

  Synopsis    [Removes redundant inverters at primary outputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Nf2_ManFixPoDrivers( Nf2_Man_t * p )
{
    Gia_Obj_t * pObj;
    Nf2_Mat_t * pM, * pMc;
    int i, iDriver, Count = 0;
    word Area;
    Gia_ManForEachCo( p->pGia, pObj, i )
    {
        iDriver = Gia_ObjFaninId0p(p->pGia, pObj);
        if ( !Gia_ObjIsAnd(Gia_ManObj(p->pGia, iDriver)) )
            continue;
        // skip unless both are used
        if ( !Nf2_ObjMapRefNum(p, iDriver, 0) || !Nf2_ObjMapRefNum(p, iDriver, 1) )
            continue;
        pM  = Nf2_ObjMatchD( p, iDriver,  Gia_ObjFaninC0(pObj) );
        pMc = Nf2_ObjMatchD( p, iDriver, !Gia_ObjFaninC0(pObj) );
        // skip unless both are non-complemented
        if ( pM->fCompl || pMc->fCompl )
            continue;
        // skip if arrival time exceeds the required time
        if ( !p->pPars->fAreaOnly && pMc->D + p->InvDelayI > pM->D )
            continue;
        // update references
        Area = Nf2_MatchDeref_rec( p, iDriver, Gia_ObjFaninC0(pObj), pM );
        if ( Area < p->InvAreaW || (p->pPars->fAreaOnly &&
             Area == p->InvAreaW && pMc->D + p->InvDelayI >= pM->D) )
        {
            Nf2_MatchRef_rec( p, iDriver, Gia_ObjFaninC0(pObj), pM, SCL_INFINITY - 1 );
            continue;
        }
        Nf2_ObjMapRefInc( p, iDriver, !Gia_ObjFaninC0(pObj) );
        // add inverter
        *pM = *pMc;
        pM->D += p->InvDelayI;
        pM->fCompl = 1;
        pM->fBest = 1;
        pMc->fBest = 1;
        Count++;
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Exports the selected cells and pin literals into the GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Nf2_ManDeriveMapping( Nf2_Man_t * p )
{
    unsigned Nf2_PinPerm, Nf2_PinPhase, Nf2_PinDirect;
    int Nf2_PinCount, Nf2_PinLit, * Nf2_PinFans, * Nf2_PinBinds;
    Vec_Int_t * vMapping;
    Nf2_Mat_t * pM;
    int i, k, c, Id, iVar, fCompl, * pCut;
    assert( p->pGia->vCellMapping == NULL );
    vMapping = Vec_IntAlloc( 2*Gia_ManObjNum(p->pGia) + (int)p->pPars->Edge + (int)p->pPars->Area * 2 );
    Vec_IntFill( vMapping, 2*Gia_ManObjNum(p->pGia), 0 );
    // create CI inverters
    Gia_ManForEachCiId( p->pGia, Id, i )
    if ( Nf2_ObjMapRefNum(p, Id, 1) )
        Vec_IntWriteEntry( vMapping, Abc_Var2Lit(Id, 1), -1 );
    // create internal nodes
    Gia_ManForEachAndId( p->pGia, i )
    {
        Gia_Obj_t * pObj = Gia_ManObj(p->pGia, i);
        if ( Gia_ObjIsBuf(pObj) )
        {
            if ( Nf2_ObjMapRefNum(p, i, 1) )
                Vec_IntWriteEntry( vMapping, Abc_Var2Lit(i, 1), -1 );
            Vec_IntWriteEntry( vMapping, Abc_Var2Lit(i, 0), -2 );
            continue;
        }
        for ( c = 0; c < 2; c++ )
        if ( Nf2_ObjMapRefNum(p, i, c) )
        {
            pM = Nf2_ObjMatchD( p, i, c );
            // remember inverter
            if ( pM->fCompl )
            {
                Vec_IntWriteEntry( vMapping, Abc_Var2Lit(i, c), -1 );
                continue;
            }
            pCut = Nf2_CutFromHandle( Nf2_ObjCutSet(p, i), pM->CutH );
            Vec_IntWriteEntry( vMapping, Abc_Var2Lit(i, c), Vec_IntSize(vMapping) );
            Vec_IntPush( vMapping, Nf2_CutSize(pCut) );
            Nf2_CutForEachVarCompl(p,i, pCut, pM->Cfg, iVar, fCompl, k )
                Vec_IntPush( vMapping, Abc_Var2Lit(iVar, fCompl) );
            Vec_IntPush( vMapping, pM->Gate );
        }
    }
    p->pGia->vCellMapping = vMapping;
    return p->pGia;
}
/**Function*************************************************************

  Synopsis    [Counts cells, edges, and area in the selected cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_ManUpdateStats( Nf2_Man_t * p )
{
    Nf2_Mat_t * pM;
    Gia_Obj_t * pObj;
    Mio_Cell2_t * pCell;
    int i, c, Id, * pCut;
    p->pPars->MapAreaF = 0; p->nInvs = 0;
    p->pPars->Area = p->pPars->Edge = 0;
    Gia_ManForEachAndReverse( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) )
        {
            if ( Nf2_ObjMapRefNum(p, i, 1) )
            {
                p->pPars->MapAreaF += p->InvAreaF;
                p->pPars->Edge++;
                p->pPars->Area++;
                p->nInvs++;
            }
            continue;
        }
        for ( c = 0; c < 2; c++ )
        if ( Nf2_ObjMapRefNum(p, i, c) )
        {
            pM = Nf2_ObjMatchD( p, i, c );
            if ( pM->fCompl )
            {
                p->pPars->MapAreaF += p->InvAreaF;
                p->pPars->Edge++;
                p->pPars->Area++;
                p->nInvs++;
                continue;
            }
            pCut = Nf2_CutFromHandle( Nf2_ObjCutSet(p, i), pM->CutH );
            pCell = Nf2_ManCell( p, pM->Gate );
            assert( Nf2_CutSize(pCut) == (int)pCell->nFanins );
            p->pPars->MapAreaF += pCell->AreaF;
            p->pPars->Edge += Nf2_CutSize(pCut);
            p->pPars->Area++;
        }
    }
    Gia_ManForEachCiId( p->pGia, Id, i )
        if ( Nf2_ObjMapRefNum(p, Id, 1) )
        {
            p->pPars->MapAreaF += p->InvAreaF;
            p->pPars->Edge++;
            p->pPars->Area++;
            p->nInvs++;
        }
}

/**Function*************************************************************

  Synopsis    [Initializes mapping parameters with automatic round counts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nf2_ManSetDefaultPars( Jf_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Jf_Par_t) );
    pPars->nLutSize     =  6;
    pPars->nCutNum      = NF2_CUT_MAX - 1;
    pPars->nProcNum     =  0;
    // Automatic counts select 1/1 for native mapping, or the reference
    // defaults for unsupported libraries. Choices use two exact-area rounds.
    pPars->nRounds      = -1;
    pPars->nRoundsEla   = -1;
    pPars->nRelaxRatio  =  0;
    pPars->nCoarseLimit =  3;
    pPars->nAreaTuner   =  0;
    pPars->nReqTimeFlex =  0;
    pPars->nVerbLimit   =  5;
    pPars->DelayTarget  = -1;
    pPars->fAreaOnly    =  0;
    pPars->fPinPerm     =  0;
    pPars->fPinQuick    =  0;
    pPars->fPinFilter   =  0;
    pPars->fOptEdge     =  1;
    pPars->fCoarsen     =  0;
    pPars->fCutMin      =  1;
    pPars->fGenCnf      =  0;
    pPars->fPureAig     =  0;
    pPars->fVerbose     =  0;
    pPars->fVeryVerbose =  0;
    pPars->nLutSizeMax  =  NF2_LEAF_MAX;
    pPars->nCutNumMax   =  NF2_CUT_MAX - 1;
    pPars->MapDelayTarget = 0;
}
/**Function*************************************************************

  Synopsis    [Runs cut construction, mapping rounds, and cover export.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Nf2_ManPerformMappingInt( Gia_Man_t * pGia, Jf_Par_t * pPars, Mio_Library_t * pMio, Amap_Lib_t * pAmap, int fAdaptive )
{
    Gia_Man_t * pNew = NULL;
    Nf2_Man_t * p; int i, Id, Stable = 0;
    float OldArea = 0;
    p = Nf2_StoCreate( pGia, pPars, pMio, pAmap );
    if ( p == NULL )
        return NULL;
    p->pGia->iFirstNonPiId = p->pManTim ? Tim_ManPiNum(p->pManTim) : Gia_ManCiNum(p->pGia);
    p->pGia->iFirstPoId    = p->pManTim ? Gia_ManCoNum(p->pGia) - Tim_ManPoNum(p->pManTim) : 0;
    p->pGia->iFirstAndObj  = 1 + p->pGia->iFirstNonPiId;
    p->pGia->iFirstPoObj   = Gia_ManObjNum(p->pGia) - Gia_ManCoNum(p->pGia) + p->pGia->iFirstPoId;
    Nf2_ManPrintInit( p );
    if ( Scl_ConIsRunning() )
    {
        Gia_ManForEachCiIdWithBoxes( p->pGia, Id, i )
            Nf2_ObjPrepareCi( p, Id, Scl_ConGetInArr(i) );
    }
    else
    {
        Gia_ManForEachCiIdWithBoxes( p->pGia, Id, i )
            Nf2_ObjPrepareCi( p, Id, Scl_Flt2Int(p->pGia->vInArrs ? Vec_FltEntry(p->pGia->vInArrs, i) : 0.0) );
    }
    if ( Gia_ManHasChoices(pGia) ) Gia_ManSetPhase(pGia);
    Nf2_ManComputeCuts( p );
    // Child binding programs are needed only while importing the choices.
    ABC_FREE( p->pChoiceOffsets );
    ABC_FREE( p->vChoiceValues.pArray );
    Nf2_ManPrintQuit( p );
    for ( p->Iter = 0; p->Iter < p->pPars->nRounds; p->Iter++ )
    {
        if ( p->Iter ) Nf2_ManComputeMapping( p );
        Nf2_ManSetMapRefs( p );
        Nf2_ManPrintStats( p, p->Iter || pPars->fAreaOnly ? "Area " : "Delay" );
        // The area-oriented caller permits early termination after two weak
        // rounds. Ordinary NF2 retains its requested iteration schedule.
        if ( fAdaptive )
        {
            Stable = p->Iter && pPars->MapAreaF > 0.998f * OldArea ? Stable+1 : 0;
            OldArea = pPars->MapAreaF;
            if ( p->Iter >= 3 && Stable >= 2 ) { pPars->nRounds = ++p->Iter; break; }
        }
    }

    p->fUseEla = 1; Stable = 0;
    for ( ; p->Iter < p->pPars->nRounds + pPars->nRoundsEla; p->Iter++ )
    {
        Nf2_ManComputeMappingEla( p );
        Nf2_ManUpdateStats( p );
        Nf2_ManPrintStats( p, "Ela  " );
        if ( fAdaptive )
        {
            Stable = pPars->MapAreaF > 0.9995f * OldArea ? Stable+1 : 0;
            OldArea = pPars->MapAreaF;
            if ( p->Iter >= pPars->nRounds+2 && Stable >= 2 ) break;
        }
    }
    if ( pPars->nRoundsEla == 0 ) Nf2_ManResetMatches(p,0);
    // Refresh selected arrivals after reverse exact-area changes.
    if ( pPars->nRoundsEla ) Nf2_ManFinalTiming(p);
    if ( Nf2_ManFixPoDrivers(p) )
    {
        Nf2_ManFinalTiming(p);
        Nf2_ManUpdateStats(p);
    }
    if ( pPars->fAreaOnly )
        Nf2_ManSetOutputRequireds(p,0);
    pNew = Nf2_ManDeriveMapping( p );

    Nf2_StoDelete( p );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Maps a GIA while preserving timing boxes and cell metadata.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Nf2_ManPerformMappingWithLibInt( Gia_Man_t * p, Jf_Par_t * pPars, Mio_Library_t * pMio, Amap_Lib_t * pAmap, int fAdaptive )
{
    extern Gia_Man_t * Nf_ManPerformMappingWithLib( Gia_Man_t *, Jf_Par_t *, Mio_Library_t * );
    extern void Nf_ManSetDefaultPars( Jf_Par_t * );
    Gia_Man_t * pNew, * pOrig = p;
    Jf_Par_t Params, Defaults, * pUserPars = pPars;
    int fFallback;
    Amap_PatView_t Patterns;
    if ( p == NULL || pPars == NULL || pMio == NULL )
        return NULL;
    Params = *pPars;
    // MapDelay is an output from the previous call, not a new constraint.
    Params.MapDelay = 0;
    pPars = &Params;
    Amap_LibReadPatterns( pAmap, &Patterns );
    fFallback = pAmap == NULL || Patterns.nNodes >= 2048;
    if ( fFallback ) Nf_ManSetDefaultPars( &Defaults );
    if ( pPars->nRounds == -1 ) pPars->nRounds = fFallback ? Defaults.nRounds : 1;
    if ( pPars->nRoundsEla == -1 ) pPars->nRoundsEla = fFallback ? Defaults.nRoundsEla : (Gia_ManHasChoices(p) ? 2 : 1);
    if ( pPars->fCoarsen || Gia_ManMuxNum(p) )
    {
        Abc_Print( -1, "&nf2: XOR/MUX coarsening and explicit MUX objects are not supported.\n" );
        return NULL;
    }
    // Preserve integer targets supplied by API callers; the command writes the
    // fixed-point field directly so fractional targets are not truncated.
    if ( pPars->DelayTarget > 0 && pPars->MapDelayTarget == 0 )
    {
        if ( pPars->DelayTarget >= SCL_INFINITY / SCL_NUM )
        {
            Abc_Print( -1, "&nf2: delay target exceeds fixed-point capacity.\n" );
            return NULL;
        }
        pPars->MapDelayTarget = pPars->DelayTarget * SCL_NUM;
    }
    if ( pPars->nLutSize < 2 || pPars->nLutSize > NF2_LEAF_MAX ||
         pPars->nCutNum < 2 || pPars->nCutNum >= NF2_CUT_MAX ||
         pPars->nRounds < 1 || pPars->nRoundsEla < 0 ||
         pPars->nRounds > INT_MAX - pPars->nRoundsEla ||
         !(pPars->MapDelayTarget >= 0 && (double)pPars->MapDelayTarget < SCL_INFINITY) ||
         Gia_ManObjNum(p) > INT_MAX / 20 )
    {
        Abc_Print( -1, "&nf2: mapping parameters or network size exceed capacity.\n" );
        return NULL;
    }
    if ( pPars->fPinFilter )
    {
        Abc_Print( -1, "&nf2: filtered pin matching is not supported.\n" );
        return NULL;
    }
    if ( fFallback )
    {
        Jf_Par_t Fallback = *pPars;
        Fallback.DelayTarget = -1;
        if ( Fallback.fAreaOnly ) Fallback.MapDelayTarget = (float)(SCL_INFINITY - 1);
        if ( Fallback.nRoundsEla == 0 )
        {
            Abc_Print( -1, "&nf2: the reference fallback requires at least one exact area round.\n" );
            return NULL;
        }
        // Keep the reference mapper's cut capacity for unsupported pattern inputs.
        Fallback.nCutNum = Abc_MinInt( Fallback.nCutNum, 32 );
        if ( pPars->fVerbose )
            Abc_Print( 1, "&nf2: using reference mapping for this library.\n" );
        pNew = Nf_ManPerformMappingWithLib( p, &Fallback, pMio );
        pPars->MapAreaF = Fallback.MapAreaF;
        // The area-only fallback reports its artificial target, not an arrival.
        pPars->MapDelay = pPars->fAreaOnly ? 0 : Fallback.MapDelay;
        pPars->Area = Fallback.Area;
        pPars->Edge = Fallback.Edge;
        goto finish;
    }
    if ( p->pManTime && Tim_ManBoxNum((Tim_Man_t*)p->pManTime) && Gia_ManIsNormalized(p) )
    {
        pNew = Gia_ManDupUnnormalize( p );
        if ( pNew == NULL )
            return NULL;
        Gia_ManTransferTiming( pNew, p );
        p = pNew;
        // mapping
        pNew = Nf2_ManPerformMappingInt( p, pPars, pMio, pAmap, fAdaptive );
        if ( pNew == NULL )
        {
            Gia_ManTransferTiming( pOrig, p );
            Gia_ManStop( p );
            return NULL;
        }
        if ( pNew != p )
        {
            Gia_ManTransferTiming( pNew, p );
            Gia_ManStop( p );
        }
        // normalize
        pNew = Gia_ManDupNormalize( p = pNew, 0 );
        Gia_ManTransferCellMapping( pNew, p );
        Gia_ManTransferTiming( pNew, p );
        Gia_ManStop( p );
        assert( Gia_ManIsNormalized(pNew) );
    }
    else
    {
        pNew = Nf2_ManPerformMappingInt( p, pPars, pMio, pAmap, fAdaptive );
        if ( pNew == NULL ) return NULL;
        Gia_ManTransferTiming( pNew, p );
    }
finish:
    // Preserve input settings when callers reuse the parameter object.
    pPars->nRounds = pUserPars->nRounds;
    pPars->nRoundsEla = pUserPars->nRoundsEla;
    pPars->MapDelayTarget = pUserPars->MapDelayTarget;
    *pUserPars = *pPars;
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Maps with supplied libraries and the ordinary NF2 schedule.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Nf2_ManPerformMappingWithLib( Gia_Man_t * p, Jf_Par_t * pPars, Mio_Library_t * pMio, Amap_Lib_t * pAmap )
{
    return Nf2_ManPerformMappingWithLibInt( p, pPars, pMio, pAmap, 0 );
}

/**Function*************************************************************

  Synopsis    [Maps for NF3, stopping additional recovery rounds at diminishing gains.]

  Description [Rounds are upper bounds. This entry point shares the matcher
  and compiled library with NF2 without changing the NF2 command's schedule.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Nf2_ManPerformMappingArea( Gia_Man_t * pGia, Jf_Par_t * pPars )
{
    return Nf2_ManPerformMappingWithLibInt( pGia, pPars,
        (Mio_Library_t *)Abc_FrameReadLibGen(), (Amap_Lib_t *)Abc_FrameReadLibGen2(), 1 );
}

/**Function*************************************************************

  Synopsis    [Maps using the frame's standard-cell and pattern libraries.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Nf2_ManPerformMapping( Gia_Man_t * pGia, Jf_Par_t * pPars )
{
    return Nf2_ManPerformMappingWithLib( pGia, pPars,
        (Mio_Library_t *)Abc_FrameReadLibGen(), (Amap_Lib_t *)Abc_FrameReadLibGen2() );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
