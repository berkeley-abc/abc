/**CFile****************************************************************

  FileName    [acbTest.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    []

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 21, 2015.]

  Revision    [$Id: acbTest.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acb.h"
#include "acbXec.h"
#include "aig/saig/saig.h"
#include "aig/gia/giaAig.h"
#include "base/abc/abc.h"
#include "proof/fraig/fraig.h"
#include "proof/cec/cec.h"
#include "proof/dch/dch.h"
#include "proof/acec/acec.h"
#include "opt/dar/dar.h"
#include "sat/cadical/cadicalSolver.h"
#include "sat/cnf/cnf.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ACB_FORCE_ZERO 0
#define ACB_XEC_RECURSION_LIMIT 8192

typedef enum Acb_CexCheckStatus_t_
{
    ACB_CEX_UNSUPPORTED = -1,
    ACB_CEX_INVALID     =  0,
    ACB_CEX_VALID       =  1
} Acb_CexCheckStatus_t;

typedef struct Acb_XecCtx_t_
{
    struct Acb_XecParams_t_
    {
        int nScratchVecInit;          /* Initial capacity for per-run hard-output vectors. */
        int nOverlapMinPermille;      /* Minimum cone overlap for grouping outputs in one SAT cluster. */
        int nOverlapSizePermille;     /* Minimum smaller/larger cone-size ratio for output clustering. */
        int nBranchMinOutputSec;      /* Keep this much branch budget before starting another PO solve. */
        int nBranchLocalOptAndMin;    /* Try local optimization/abstraction only for large branch cones. */
        int nBranchLocalOptSec;       /* Time cap for local optimized branch-cone SAT. */
        int nBranchFrontierAbsSec;    /* Time cap for frontier abstraction probe. */
        int nBranchHardConflictMin;   /* Report/isolate branch outputs above this conflict delta. */
        int nBranchHardTimeMin;       /* Report/isolate branch outputs above this runtime delta. */
        int nBranchSchedulePrintMax;  /* Max branch output ids printed in the clustered schedule. */
        int nLocalManyPoThreshold;    /* Above this PO count, local sweep uses quick SAT-hunting probes. */
        int nLocalMediumPoMin;        /* Lower PO count for medium sweep behavior. */
        int nLocalMediumPoMax;        /* Upper PO count for medium sweep behavior. */
        int nLocalQuickMaxUndec;      /* Quick many-output sweep stops after this many undecided probes. */
        int nLocalQuickPoSec;         /* Per-output limit for quick many-output probes. */
        int nLocalMediumPoSec;        /* Per-output limit for medium local sweep. */
        int nLocalMediumHardPoSec;    /* Per-output limit after first hard output in medium sweep. */
        int nLocalConeCompressAndMin; /* Compress local cone only when it has at least this many ANDs. */
        int nSimLargeAndMin;          /* Use larger random simulation only above this miter size. */
        int nSimSmallWords;           /* Random-simulation words for small miters. */
        int nSimLargeWords;           /* Random-simulation words for large miters. */
        int nMainLargeAndMin;         /* Enter heavy xec proof orchestration above this AND count. */
        int nMainLargePiMin;          /* Enter heavy xec proof orchestration above this PI count. */
        int nMainLargePoMin;          /* Enter heavy xec proof orchestration above this PO count. */
        int nSharedDcPiMin;           /* Prefer shared whole-miter SAT for few-control DC above this PI count. */
        int nSharedDcPoMin;           /* Prefer shared whole-miter SAT for few-control DC above this PO count. */
        int nSharedDcPoMax;           /* Upper PO bound for the few-control high-PI DC shape. */
        int nSharedDcAndMin;          /* Lower AND bound for the few-control high-PI DC shape. */
        int nSharedDcAndMax;          /* Upper AND bound for the few-control high-PI DC shape. */
        int nSharedDcObjMin;          /* Lower DC-object count for the few-control high-PI DC shape. */
        int nSharedDcObjMax;          /* Upper DC-object count for the few-control high-PI DC shape. */
        int nSharedDcWholeSec;        /* Whole-miter SAT time cap for the few-control high-PI DC shape. */
    } Pars;
    int LastHardPo;
    Vec_Int_t * vLastHardPos;
    Vec_Int_t * vLastProvenPos;
    Vec_Int_t * vLastBranchHardPos;
    int LastHardDirectTried;
} Acb_XecCtx_t;

static inline void Acb_XecParamsSetDefault( Acb_XecCtx_t * p )
{
    p->Pars.nScratchVecInit          = 8;
    p->Pars.nOverlapMinPermille      = 700;
    p->Pars.nOverlapSizePermille     = 450;
    p->Pars.nBranchMinOutputSec      = 60;
    p->Pars.nBranchLocalOptAndMin    = 10000;
    p->Pars.nBranchLocalOptSec       = 300;
    p->Pars.nBranchFrontierAbsSec    = 60;
    p->Pars.nBranchHardConflictMin   = 1000000;
    p->Pars.nBranchHardTimeMin       = 60;
    p->Pars.nBranchSchedulePrintMax  = 12;
    p->Pars.nLocalManyPoThreshold    = 64;
    p->Pars.nLocalMediumPoMin        = 8;
    p->Pars.nLocalMediumPoMax        = 64;
    p->Pars.nLocalQuickMaxUndec      = 12;
    p->Pars.nLocalQuickPoSec         = 5;
    p->Pars.nLocalMediumPoSec        = 60;
    p->Pars.nLocalMediumHardPoSec    = 15;
    p->Pars.nLocalConeCompressAndMin = 1000;
    p->Pars.nSimLargeAndMin          = 5000;
    p->Pars.nSimSmallWords           = 1;
    p->Pars.nSimLargeWords           = 256;
    p->Pars.nMainLargeAndMin         = 30000;
    p->Pars.nMainLargePiMin          = 256;
    p->Pars.nMainLargePoMin          = 64;
    p->Pars.nSharedDcPiMin           = 4096;
    p->Pars.nSharedDcPoMin           = 80;
    p->Pars.nSharedDcPoMax           = 128;
    p->Pars.nSharedDcAndMin          = 100000;
    p->Pars.nSharedDcAndMax          = 200000;
    p->Pars.nSharedDcObjMin          = 160;
    p->Pars.nSharedDcObjMax          = 256;
    p->Pars.nSharedDcWholeSec        = 1800;
}

static inline int Acb_XecIsSharedDcWholeMiterShape( Gia_Man_t * pGia, Vec_Int_t * vMuxSelectorsG, Vec_Int_t * vIntDcObjsG, Vec_Int_t * vIntDcCtrlsG, Acb_XecCtx_t * pCtx )
{
    if ( pGia == NULL || pCtx == NULL )
        return 0;
    if ( vMuxSelectorsG && Vec_IntSize(vMuxSelectorsG) > 0 )
        return 0;
    if ( vIntDcObjsG == NULL || vIntDcCtrlsG == NULL )
        return 0;
    if ( Vec_IntSize(vIntDcCtrlsG) != 2 )
        return 0;
    if ( Vec_IntSize(vIntDcObjsG) < pCtx->Pars.nSharedDcObjMin || Vec_IntSize(vIntDcObjsG) > pCtx->Pars.nSharedDcObjMax )
        return 0;
    if ( Gia_ManCiNum(pGia) < pCtx->Pars.nSharedDcPiMin )
        return 0;
    if ( Gia_ManCoNum(pGia) < pCtx->Pars.nSharedDcPoMin || Gia_ManCoNum(pGia) > pCtx->Pars.nSharedDcPoMax )
        return 0;
    if ( Gia_ManAndNum(pGia) < pCtx->Pars.nSharedDcAndMin || Gia_ManAndNum(pGia) > pCtx->Pars.nSharedDcAndMax )
        return 0;
    return 1;
}

static inline void Acb_XecCtxInit( Acb_XecCtx_t * p )
{
    memset( p, 0, sizeof(*p) );
    Acb_XecParamsSetDefault( p );
    p->LastHardPo = -1;
}

static inline void Acb_XecCtxFree( Acb_XecCtx_t * p )
{
    Vec_IntFreeP( &p->vLastHardPos );
    Vec_IntFreeP( &p->vLastProvenPos );
    Vec_IntFreeP( &p->vLastBranchHardPos );
    p->LastHardPo = -1;
    p->LastHardDirectTried = 0;
}

static inline void Acb_XecCtxResetLocalSweep( Acb_XecCtx_t * p )
{
    p->LastHardPo = -1;
    p->LastHardDirectTried = 0;
    Vec_IntFreeP( &p->vLastHardPos );
    p->vLastHardPos = Vec_IntAlloc( p->Pars.nScratchVecInit );
    Vec_IntFreeP( &p->vLastProvenPos );
    p->vLastProvenPos = Vec_IntAlloc( p->Pars.nScratchVecInit );
}

static inline void Acb_XecCtxResetBranchSweep( Acb_XecCtx_t * p, int nOuts )
{
    Vec_IntFreeP( &p->vLastBranchHardPos );
    p->vLastBranchHardPos = Vec_IntAlloc( nOuts );
}

Gia_Man_t * Acb_GiaDupOnePoTrimmed( Gia_Man_t * p, int iPo, Vec_Int_t * vSuppMap )
{
    Gia_Obj_t * pPo;
    Gia_Man_t * pNew;
    int iLit, iPoObj;
    if ( vSuppMap )
        Vec_IntClear( vSuppMap );
    if ( p == NULL || iPo < 0 || iPo >= Gia_ManCoNum(p) )
        return NULL;
    pPo = Gia_ManCo( p, iPo );
    iLit = Gia_ObjFaninLit0p( p, pPo );
    if ( Gia_ManIsConst0Lit(iLit) || Gia_ManIsConst1Lit(iLit) )
    {
        Gia_Man_t * pNew = Gia_ManStart( 1 );
        pNew->pName = Abc_UtilStrsav( p->pName );
        Gia_ManAppendCo( pNew, Gia_ManIsConst1Lit(iLit) );
        return pNew;
    }
    iPoObj = Gia_ObjFaninId0p( p, pPo );
    if ( vSuppMap )
    {
        Gia_ManCollectCis( p, &iPoObj, 1, vSuppMap );
        Vec_IntSort( vSuppMap, 0 );
    }
    pNew = Gia_ManDupCones( p, &iPo, 1, 1 );
    if ( pNew == NULL && vSuppMap )
        Vec_IntClear( vSuppMap );
    return pNew;
}

int * Acb_NtkSolveCadicalLocalConeSweepSkipCtx( Gia_Man_t * p, int fVerbose, int * pStatus, int nSatTimeLimit, int nPoTimeLimit, Vec_Int_t * vSkipUnsat, Acb_XecCtx_t * pCtx );
int Acb_GiaRequiredLiteralUnitProof( Gia_Man_t * p, int iPo, int fVerbose, int nSatTimeLimit );
int * Acb_NtkSolveMuxDcControlTargetList( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, Vec_Int_t * vHardPos, Vec_Int_t * vCutObjsG, Vec_Int_t * vMuxSelectorsG, Vec_Int_t * vMuxPoSelIdsG, int fSelBranch, Vec_Int_t * vDcObjsG, Vec_Int_t * vDcCtrlsG, Vec_Int_t * vDcCtrlIdsG, int fVerbose, int * pStatus, int nBranchLimit );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Acb_NtkFindSimCex( Gia_Man_t * pF, Gia_Man_t * pG, int nWords, int fVerbose )
{
    Vec_Wrd_t * vSimsF, * vSimsG;
    Gia_Obj_t * pObjFb, * pObjFx, * pObjGb, * pObjGx;
    word * pSimFb, * pSimFx, * pSimGb, * pSimGx, * pSimPi;
    int i, k, b, nBits = 64 * nWords;
    int * pModel = NULL;
    assert( Gia_ManCiNum(pF) == Gia_ManCiNum(pG) );
    assert( Gia_ManCoNum(pF) == Gia_ManCoNum(pG) );
    Abc_Random(1);
    Vec_WrdFreeP( &pF->vSimsPi );
    Vec_WrdFreeP( &pG->vSimsPi );
    pF->vSimsPi = Vec_WrdStartRandom( Gia_ManCiNum(pF) * nWords );
    pG->vSimsPi = Vec_WrdDup( pF->vSimsPi );
    vSimsF = Gia_ManSimPatSim( pF );
    vSimsG = Gia_ManSimPatSim( pG );
    for ( i = 0; i < Gia_ManCoNum(pF)/2 && pModel == NULL; i++ )
    {
        pObjFb = Gia_ManCo( pF, 2*i+0 );
        pObjFx = Gia_ManCo( pF, 2*i+1 );
        pObjGb = Gia_ManCo( pG, 2*i+0 );
        pObjGx = Gia_ManCo( pG, 2*i+1 );
        pSimFb = Vec_WrdEntryP(vSimsF, Gia_ObjId(pF, pObjFb)*nWords);
        pSimFx = Vec_WrdEntryP(vSimsF, Gia_ObjId(pF, pObjFx)*nWords);
        pSimGb = Vec_WrdEntryP(vSimsG, Gia_ObjId(pG, pObjGb)*nWords);
        pSimGx = Vec_WrdEntryP(vSimsG, Gia_ObjId(pG, pObjGx)*nWords);
        for ( b = 0; b < nBits; b++ )
            if ( !Abc_TtGetBit(pSimGx, b) && (Abc_TtGetBit(pSimFx, b) || (Abc_TtGetBit(pSimFb, b) ^ Abc_TtGetBit(pSimGb, b))) )
            {
                pModel = ABC_ALLOC( int, Gia_ManCiNum(pF) );
                for ( k = 0; k < Gia_ManCiNum(pF); k++ )
                {
                    pSimPi = Vec_WrdEntryP( pF->vSimsPi, k*nWords );
                    pModel[k] = Abc_TtGetBit( pSimPi, b );
                }
                if ( fVerbose )
                    printf( "Random simulation found mismatch at output %d, pattern %d.\n", i, b );
                break;
            }
    }
    if ( fVerbose && pModel == NULL )
        printf( "Random simulation tried %d patterns and found no mismatch.\n", nBits );
    Vec_WrdFree( vSimsF );
    Vec_WrdFree( vSimsG );
    Vec_WrdFreeP( &pF->vSimsPi );
    Vec_WrdFreeP( &pG->vSimsPi );
    return pModel;
}
int * Acb_GiaFindOnePoSimCex( Gia_Man_t * p, int nWords, int fVerbose, char * pLabel )
{
    Vec_Wrd_t * vSims = NULL;
    Gia_Obj_t * pObjPo;
    word * pSimPo, * pSimPi;
    int k, b, nBits = 64 * nWords;
    int * pModel = NULL;
    if ( p == NULL || Gia_ManCoNum(p) != 1 || Gia_ManCiNum(p) <= 0 || nWords <= 0 )
        return NULL;
    Abc_Random( 1 );
    Vec_WrdFreeP( &p->vSimsPi );
    p->vSimsPi = Vec_WrdStartRandom( Gia_ManCiNum(p) * nWords );
    vSims = Gia_ManSimPatSim( p );
    pObjPo = Gia_ManCo( p, 0 );
    pSimPo = Vec_WrdEntryP( vSims, Gia_ObjId(p, pObjPo) * nWords );
    for ( b = 0; b < nBits; b++ )
    {
        if ( !Abc_TtGetBit(pSimPo, b) )
            continue;
        pModel = ABC_ALLOC( int, Gia_ManCiNum(p) );
        for ( k = 0; k < Gia_ManCiNum(p); k++ )
        {
            pSimPi = Vec_WrdEntryP( p->vSimsPi, k * nWords );
            pModel[k] = Abc_TtGetBit( pSimPi, b );
        }
        if ( fVerbose )
            printf( "%s simulation found bad pattern at pattern %d/%d.\n",
                pLabel ? pLabel : "Hard-output", b, nBits );
        break;
    }
    if ( fVerbose && pModel == NULL )
        printf( "%s simulation tried %d patterns and found no bad pattern.\n",
            pLabel ? pLabel : "Hard-output", nBits );
    Vec_WrdFreeP( &vSims );
    Vec_WrdFreeP( &p->vSimsPi );
    return pModel;
}

int Acb_NtkCheckModelCex( Gia_Man_t * pF, Gia_Man_t * pG, int * pModel, int fVerbose )
{
    Gia_Obj_t * pObj;
    int i, Fb, Fx, Gb, Gx;
    if ( pModel == NULL )
        return 0;
    Gia_ManConst0(pF)->Value = 0;
    Gia_ManConst0(pG)->Value = 0;
    Gia_ManForEachCi( pF, pObj, i )
        pObj->Value = pModel[i] ? 1 : 0;
    Gia_ManForEachCi( pG, pObj, i )
        pObj->Value = pModel[i] ? 1 : 0;
    Gia_ManForEachAnd( pF, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj) & Gia_ObjFanin1Copy(pObj);
    Gia_ManForEachAnd( pG, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj) & Gia_ObjFanin1Copy(pObj);
    for ( i = 0; i < Gia_ManCoNum(pF)/2; i++ )
    {
        Fb = Gia_ObjFanin0Copy( Gia_ManCo(pF, 2*i+0) );
        Fx = Gia_ObjFanin0Copy( Gia_ManCo(pF, 2*i+1) );
        Gb = Gia_ObjFanin0Copy( Gia_ManCo(pG, 2*i+0) );
        Gx = Gia_ObjFanin0Copy( Gia_ManCo(pG, 2*i+1) );
        if ( !Gx && (Fx || (Fb ^ Gb)) )
        {
            if ( fVerbose )
                printf( "Validated SAT counterexample at output %d.\n", i );
            return 1;
        }
    }
    if ( fVerbose )
        printf( "SAT model validation failed: no compatible mismatch is observed.\n" );
    return 0;
}
int Acb_NtkEvalModelBool( Acb_Ntk_t * p, int * pModel, Vec_Int_t * vVals )
{
    int i, k, iObj, Type, * pFans;
    Vec_IntFill( vVals, Acb_NtkObjNumMax(p), 0 );
    Acb_NtkForEachCi( p, iObj, i )
        Vec_IntWriteEntry( vVals, iObj, pModel[i] ? 1 : 0 );
    Acb_NtkForEachObj( p, iObj )
    {
        int z = 0;
        if ( Acb_ObjIsCio(p, iObj) )
            continue;
        Type = Acb_ObjType( p, iObj );
        pFans = Acb_ObjFanins( p, iObj );
        if ( Type == ABC_OPER_CONST_F )
            z = 0;
        else if ( Type == ABC_OPER_CONST_T )
            z = 1;
        else if ( Type == ABC_OPER_BIT_BUF )
            z = Vec_IntEntry(vVals, pFans[1]);
        else if ( Type == ABC_OPER_BIT_INV )
            z = !Vec_IntEntry(vVals, pFans[1]);
        else if ( Type == ABC_OPER_BIT_AND || Type == ABC_OPER_BIT_NAND )
        {
            z = 1;
            for ( k = 0; k < pFans[0]; k++ )
                z &= Vec_IntEntry(vVals, pFans[k+1]);
            if ( Type == ABC_OPER_BIT_NAND )
                z = !z;
        }
        else if ( Type == ABC_OPER_BIT_OR || Type == ABC_OPER_BIT_NOR )
        {
            z = 0;
            for ( k = 0; k < pFans[0]; k++ )
                z |= Vec_IntEntry(vVals, pFans[k+1]);
            if ( Type == ABC_OPER_BIT_NOR )
                z = !z;
        }
        else if ( Type == ABC_OPER_BIT_XOR || Type == ABC_OPER_BIT_NXOR )
        {
            z = 0;
            for ( k = 0; k < pFans[0]; k++ )
                z ^= Vec_IntEntry(vVals, pFans[k+1]);
            if ( Type == ABC_OPER_BIT_NXOR )
                z = !z;
        }
        else
            return 0;
        Vec_IntWriteEntry( vVals, iObj, z );
    }
    return 1;
}
int Acb_NtkCheckModelCexAcbBool( Acb_Ntk_t * pF, Acb_Ntk_t * pG, int * pModel, int fVerbose )
{
    Vec_Int_t * vF = Vec_IntAlloc( Acb_NtkObjNumMax(pF) );
    Vec_Int_t * vG = Vec_IntAlloc( Acb_NtkObjNumMax(pG) );
    int i, iCoF, iCoG, Ret = ACB_CEX_INVALID;
    if ( pModel && Acb_NtkEvalModelBool(pF, pModel, vF) && Acb_NtkEvalModelBool(pG, pModel, vG) )
    {
        Acb_NtkForEachCo( pF, iCoF, i )
        {
            iCoG = Acb_NtkCo( pG, i );
            if ( Vec_IntEntry(vF, Acb_ObjFanin(pF, iCoF, 0)) != Vec_IntEntry(vG, Acb_ObjFanin(pG, iCoG, 0)) )
            {
                if ( fVerbose )
                    printf( "Original ACB Boolean validation found SAT counterexample at output %d.\n", i );
                Ret = ACB_CEX_VALID;
                break;
            }
        }
    }
    Vec_IntFree( vF );
    Vec_IntFree( vG );
    return Ret;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDualNot( Gia_Man_t * p, int LitA[2], int LitZ[2] )
{
    LitZ[0]   = Abc_LitNot(LitA[0]);
    LitZ[1]   = LitA[1];

    if ( ACB_FORCE_ZERO ) LitZ[0]   = Gia_ManHashAnd( p, LitZ[0], Abc_LitNot(LitZ[1]) );
}
// computes Z = XOR(A, B) where A, B, Z belong to {0,1,x} encoded as 0=00, 1=01, x=1-
void Gia_ManDualXor2( Gia_Man_t * p, int LitA[2], int LitB[2], int LitZ[2] )
{
    LitZ[0]   = Gia_ManHashXor( p, LitA[0], LitB[0] );
    LitZ[1]   = Gia_ManHashOr( p, LitA[1], LitB[1] );

    if ( ACB_FORCE_ZERO ) LitZ[0]   = Gia_ManHashAnd( p, LitZ[0], Abc_LitNot(LitZ[1]) );
}
// computes Z = AND(A, B) where A, B, Z belong to {0,1,x} encoded as 0=00, 1=01, z=1-
void Gia_ManDualAndN( Gia_Man_t * p, int * pLits, int n, int LitZ[2] )
{
    int i, LitZero = 0, LitOne = 0;
    LitZ[0] = 1;
    for ( i = 0; i < n; i++ )
    {
        int Lit = Gia_ManHashAnd( p, Abc_LitNot(pLits[2*i]), Abc_LitNot(pLits[2*i+1]) );
        LitZero = Gia_ManHashOr( p, LitZero, Lit );
        LitOne  = Gia_ManHashOr( p, LitOne,  pLits[2*i+1] );
        LitZ[0] = Gia_ManHashAnd( p, LitZ[0], pLits[2*i] );
    }
    LitZ[1] = Gia_ManHashAnd( p, LitOne, Abc_LitNot(LitZero) );

    if ( ACB_FORCE_ZERO ) LitZ[0]   = Gia_ManHashAnd( p, LitZ[0], Abc_LitNot(LitZ[1]) );
}
/*
module _DC(O, C, D);
 output O;
 input C, D;
 assign O = D ? 1'bx : C;
endmodule
*/
void Gia_ManDualDc( Gia_Man_t * p, int LitC[2], int LitD[2], int LitZ[2] )
{
    LitZ[0]   = LitC[0];
//    LitZ[0]   = Gia_ManHashMux( p, LitD[0], 0, LitC[0] );
    LitZ[1]   = Gia_ManHashOr(p, Gia_ManHashOr(p,LitD[0],LitD[1]), LitC[1] );

    if ( ACB_FORCE_ZERO ) LitZ[0]   = Gia_ManHashAnd( p, LitZ[0], Abc_LitNot(LitZ[1]) );
}
void Gia_ManDualMux( Gia_Man_t * p, int LitC[2], int LitT[2], int LitE[2], int LitZ[2] )
{
/*
    // total logic size: 18 nodes
    int Xnor = Gia_ManHashXor( p, Abc_LitNot(LitT[0]), LitE[0] );
    int Cond = Gia_ManHashAnd( p, Abc_LitNot(LitT[1]), Abc_LitNot(LitE[1]) );
    int pTempE[2], pTempT[2];
    pTempE[0] = Gia_ManHashMux( p, LitC[0], LitT[0], LitE[0] );
    pTempE[1] = Gia_ManHashMux( p, LitC[0], LitT[1], LitE[1] );
    //pTempT[0] = LitT[0];
    pTempT[0] = Gia_ManHashAnd( p, LitT[0], LitE[0] );
    pTempT[1] = Gia_ManHashAnd( p, Cond, Xnor );
    LitZ[0] = Gia_ManHashMux( p, LitC[1], pTempT[0], pTempE[0] );
    LitZ[1] = Gia_ManHashMux( p, LitC[1], pTempT[1], pTempE[1] );
*/
    // total logic size: 14 nodes
    int Xnor = Gia_ManHashXor( p, Abc_LitNot(LitT[0]), LitE[0] );
    int Cond = Gia_ManHashAnd( p, Abc_LitNot(LitT[1]), Abc_LitNot(LitE[1]) );
    int XVal1 = Abc_LitNot( Gia_ManHashAnd( p, Cond, Xnor ) );
    int XVal0 = Gia_ManHashMux( p, LitC[0], LitT[1], LitE[1] );
    LitZ[0] = Gia_ManHashMux( p, LitC[0], LitT[0], LitE[0] );
    LitZ[1] = Gia_ManHashMux( p, LitC[1], XVal1, XVal0 );

    if ( ACB_FORCE_ZERO ) LitZ[0]   = Gia_ManHashAnd( p, LitZ[0], Abc_LitNot(LitZ[1]) );
}
int Gia_ManDualCompare( Gia_Man_t * p, int LitF[2], int LitS[2] )
{
    int iMiter = Gia_ManHashXor( p, LitF[0], LitS[0] );
    iMiter = Gia_ManHashOr( p, LitF[1], iMiter );
    iMiter = Gia_ManHashAnd( p, Abc_LitNot(LitS[1]), iMiter );
    return iMiter;
}
static inline void Gia_ManDualForceZero( Gia_Man_t * p, int LitZ[2], int fForceZero )
{
    if ( fForceZero )
        LitZ[0] = Gia_ManHashAnd( p, LitZ[0], Abc_LitNot(LitZ[1]) );
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_ObjToGiaDual( Gia_Man_t * pNew, Acb_Ntk_t * p, int iObj, Vec_Int_t * vTemp, Vec_Int_t * vCopies, int pRes[2], Vec_Int_t * vDcBranchObjs, Vec_Int_t * vDcBranchVals, int fDcBranchOne, int fForceZero )
{
    //char * pName = Abc_NamStr( p->pDesign->pStrs, Acb_ObjName(p, iObj) );
    int * pFanin, iFanin, k, Type;
    if ( Acb_ObjIsCio(p, iObj) )
    {
        Acb_NtkPrintUnsupportedObj( p, iObj, "ACB dual translation", -1, 0 );
        return 0;
    }
    Vec_IntClear( vTemp );
    Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, k )
    {
        int * pLits = Vec_IntEntryP( vCopies, 2*iFanin );
        if ( pLits[0] < 0 || pLits[1] < 0 )
        {
            Acb_NtkPrintUnsupportedObj( p, iObj, "ACB dual translation has unmapped fanin", -1, k );
            return 0;
        }
        Vec_IntPushTwo( vTemp, pLits[0], pLits[1] );
    }
    Type = Acb_ObjType( p, iObj );
    if ( Type == ABC_OPER_CONST_F )
    {
        pRes[0] = 0;
        pRes[1] = 0;
        return 1;
    }
    if ( Type == ABC_OPER_CONST_T )
    {
        pRes[0] = 1;
        pRes[1] = 0;
        return 1;
    }
    if ( Type == ABC_OPER_CONST_X )
    {
        pRes[0] = 0;
        pRes[1] = 1;
        return 1;
    }
    if ( Type == ABC_OPER_BIT_BUF )
    {
        pRes[0] = Vec_IntEntry(vTemp, 0);
        pRes[1] = Vec_IntEntry(vTemp, 1);
        Gia_ManDualForceZero( pNew, pRes, fForceZero );
        return 1;
    }
    if ( Type == ABC_OPER_BIT_INV )
    {
        Gia_ManDualNot( pNew, Vec_IntArray(vTemp), pRes );
        Gia_ManDualForceZero( pNew, pRes, fForceZero );
        return 1;
    }
    if ( Type == ABC_OPER_TRI )
    {
        // in the file inputs are ordered as follows:  _DC \n6_5[9] ( .O(\108 ), .C(\96 ), .D(\107 ));
        // in this code, we expect them as follows: void Gia_ManDualDc( Gia_Man_t * p, int LitC[2], int LitD[2], int LitZ[2] )
        if ( Vec_IntSize(vTemp) != 4 )
        {
            Acb_NtkPrintUnsupportedObj( p, iObj, "ACB dual TRI translation", 2, Vec_IntSize(vTemp)/2 );
            return 0;
        }
        if ( vDcBranchObjs && Vec_IntFind(vDcBranchObjs, iObj) >= 0 )
        {
            int iPos = Vec_IntFind(vDcBranchObjs, iObj);
            int fOne = vDcBranchVals ? Vec_IntEntry(vDcBranchVals, iPos) : fDcBranchOne;
            if ( fOne )
            {
                pRes[0] = 0;
                pRes[1] = 1;
            }
            else
            {
                pRes[0] = Vec_IntEntry(vTemp, 0);
                pRes[1] = Vec_IntEntry(vTemp, 1);
            }
            Gia_ManDualForceZero( pNew, pRes, fForceZero );
            return 1;
        }
        Gia_ManDualDc( pNew, Vec_IntArray(vTemp), Vec_IntArray(vTemp) + 2, pRes );
        Gia_ManDualForceZero( pNew, pRes, fForceZero );
        return 1;
    }
    if ( Type == ABC_OPER_BIT_MUX )
    {
        // in the file inputs are ordered as follows:  _HMUX \U$1 ( .O(\282 ), .I0(1'b1), .I1(\277 ), .S(\281 ));
        // in this code, we expect them as follows: void Gia_ManDualMux( Gia_Man_t * p, int LitC[2], int LitT[2], int LitE[2], int LitZ[2] )
        if ( Vec_IntSize(vTemp) != 6 )
        {
            Acb_NtkPrintUnsupportedObj( p, iObj, "ACB dual MUX translation", 3, Vec_IntSize(vTemp)/2 );
            return 0;
        }
        ABC_SWAP( int, Vec_IntArray(vTemp)[0], Vec_IntArray(vTemp)[4] );
        ABC_SWAP( int, Vec_IntArray(vTemp)[1], Vec_IntArray(vTemp)[5] );
        Gia_ManDualMux( pNew, Vec_IntArray(vTemp), Vec_IntArray(vTemp) + 2, Vec_IntArray(vTemp) + 4, pRes );
        Gia_ManDualForceZero( pNew, pRes, fForceZero );
        return 1;
    }
    if ( Type == ABC_OPER_BIT_AND || Type == ABC_OPER_BIT_NAND )
    {
        Gia_ManDualAndN( pNew, Vec_IntArray(vTemp), Vec_IntSize(vTemp)/2, pRes );
        if ( Type == ABC_OPER_BIT_NAND )
            pRes[0] = Abc_LitNot( pRes[0] );
        Gia_ManDualForceZero( pNew, pRes, fForceZero );
        return 1;
    }
    if ( Type == ABC_OPER_BIT_OR || Type == ABC_OPER_BIT_NOR )
    {
        int * pArray = Vec_IntArray( vTemp );
        for ( k = 0; k < Vec_IntSize(vTemp)/2; k++ )
            pArray[2*k] = Abc_LitNot( pArray[2*k] );
        Gia_ManDualAndN( pNew, pArray, Vec_IntSize(vTemp)/2, pRes );
        if ( Type == ABC_OPER_BIT_OR )
            pRes[0] = Abc_LitNot( pRes[0] );
        Gia_ManDualForceZero( pNew, pRes, fForceZero );
        return 1;
    }
    if ( Type == ABC_OPER_BIT_XOR || Type == ABC_OPER_BIT_NXOR )
    {
        if ( Vec_IntSize(vTemp) != 4 )
        {
            Acb_NtkPrintUnsupportedObj( p, iObj, "ACB dual XOR translation", 2, Vec_IntSize(vTemp)/2 );
            return 0;
        }
        Gia_ManDualXor2( pNew, Vec_IntArray(vTemp), Vec_IntArray(vTemp) + 2, pRes );
        if ( Type == ABC_OPER_BIT_NXOR )
            pRes[0] = Abc_LitNot( pRes[0] );
        Gia_ManDualForceZero( pNew, pRes, fForceZero );
        return 1;
    }
    Acb_NtkPrintUnsupportedObj( p, iObj, "ACB dual translation", -1, Vec_IntSize(vTemp)/2 );
    return 0;
}
Gia_Man_t * Acb_NtkGiaDeriveDualTargetsBranchValuesForceZero( Acb_Ntk_t * p, Vec_Int_t * vTargets, Vec_Int_t * vDcBranchObjs, Vec_Int_t * vDcBranchVals, int fDcBranchOne, int fForceZero )
{
    extern Vec_Int_t * Acb_NtkFindNodes2( Acb_Ntk_t * p );
    Gia_Man_t * pNew, * pOne;
    Vec_Int_t * vFanins, * vNodes;
    Vec_Int_t * vCopies = Vec_IntStartFull( 2*Acb_NtkObjNum(p) );
    int i, iObj, * pLits;
    pNew = Gia_ManStart( 5 * Acb_NtkObjNum(p) );
    pNew->pName = Abc_UtilStrsav(Acb_NtkName(p));
    Gia_ManHashAlloc( pNew );
    pLits = Vec_IntEntryP( vCopies, 0 );
    pLits[0] = 0;
    pLits[1] = 0;
    Acb_NtkForEachCi( p, iObj, i )
    {
        pLits = Vec_IntEntryP( vCopies, 2*iObj );
        pLits[0] = Gia_ManAppendCi(pNew);
        pLits[1] = 0;
    }
    vFanins = Vec_IntAlloc( 4 );
    vNodes  = Acb_NtkFindNodes2( p );
    Vec_IntForEachEntry( vNodes, iObj, i )
    {
        pLits = Vec_IntEntryP( vCopies, 2*iObj );
        if ( !Acb_ObjToGiaDual( pNew, p, iObj, vFanins, vCopies, pLits, vDcBranchObjs, vDcBranchVals, fDcBranchOne, fForceZero ) )
        {
            Vec_IntFree( vNodes );
            Vec_IntFree( vFanins );
            Vec_IntFree( vCopies );
            Gia_ManStop( pNew );
            return NULL;
        }
    }
    Vec_IntFree( vNodes );
    Vec_IntFree( vFanins );
    if ( vTargets )
    {
        Vec_IntForEachEntry( vTargets, iObj, i )
        {
            pLits = Vec_IntEntryP( vCopies, 2*iObj );
            Gia_ManAppendCo( pNew, pLits[0] );
            Gia_ManAppendCo( pNew, pLits[1] );
        }
    }
    else Acb_NtkForEachCo( p, iObj, i )
    {
        pLits = Vec_IntEntryP( vCopies, 2*Acb_ObjFanin(p, iObj, 0) );
        Gia_ManAppendCo( pNew, pLits[0] );
        Gia_ManAppendCo( pNew, pLits[1] );
    }
    Vec_IntFree( vCopies );
    pNew = Gia_ManCleanup( pOne = pNew );
    Gia_ManStop( pOne );
    return pNew;
}
Gia_Man_t * Acb_NtkGiaDeriveDualTargetsBranchValues( Acb_Ntk_t * p, Vec_Int_t * vTargets, Vec_Int_t * vDcBranchObjs, Vec_Int_t * vDcBranchVals, int fDcBranchOne )
{
    return Acb_NtkGiaDeriveDualTargetsBranchValuesForceZero( p, vTargets, vDcBranchObjs, vDcBranchVals, fDcBranchOne, 0 );
}
Gia_Man_t * Acb_NtkGiaDeriveDualTargetsBranch( Acb_Ntk_t * p, Vec_Int_t * vTargets, Vec_Int_t * vDcBranchObjs, int fDcBranchOne )
{
    return Acb_NtkGiaDeriveDualTargetsBranchValues( p, vTargets, vDcBranchObjs, NULL, fDcBranchOne );
}
Gia_Man_t * Acb_NtkGiaDeriveDualTargets( Acb_Ntk_t * p, Vec_Int_t * vTargets )
{
    return Acb_NtkGiaDeriveDualTargetsBranch( p, vTargets, NULL, 0 );
}
Gia_Man_t * Acb_NtkGiaDeriveDualTargetsForceZero( Acb_Ntk_t * p, Vec_Int_t * vTargets )
{
    return Acb_NtkGiaDeriveDualTargetsBranchValuesForceZero( p, vTargets, NULL, NULL, 0, 1 );
}

Gia_Man_t * Acb_NtkGiaDeriveDualTargetsCutLeaves( Acb_Ntk_t * p, Vec_Int_t * vTargets, Vec_Int_t * vCutObjs )
{
    extern Vec_Int_t * Acb_NtkFindNodes2( Acb_Ntk_t * p );
    Gia_Man_t * pNew, * pOne;
    Vec_Int_t * vFanins, * vNodes;
    Vec_Int_t * vCopies = Vec_IntStartFull( 2*Acb_NtkObjNum(p) );
    Vec_Int_t * vCutMap = Vec_IntStart( Acb_NtkObjNumMax(p) );
    int i, iObj, * pLits;
    pNew = Gia_ManStart( 5 * Acb_NtkObjNum(p) );
    pNew->pName = Abc_UtilStrsav(Acb_NtkName(p));
    Gia_ManHashAlloc( pNew );
    pLits = Vec_IntEntryP( vCopies, 0 );
    pLits[0] = 0;
    pLits[1] = 0;
    Acb_NtkForEachCi( p, iObj, i )
    {
        pLits = Vec_IntEntryP( vCopies, 2*iObj );
        pLits[0] = Gia_ManAppendCi(pNew);
        pLits[1] = 0;
    }
    if ( vCutObjs )
        Vec_IntForEachEntry( vCutObjs, iObj, i )
        {
            pLits = Vec_IntEntryP( vCopies, 2*iObj );
            pLits[0] = Gia_ManAppendCi(pNew);
            pLits[1] = Gia_ManAppendCi(pNew);
            Vec_IntWriteEntry( vCutMap, iObj, 1 );
        }
    vFanins = Vec_IntAlloc( 4 );
    vNodes  = Acb_NtkFindNodes2( p );
    Vec_IntForEachEntry( vNodes, iObj, i )
    {
        if ( Vec_IntEntry(vCutMap, iObj) )
            continue;
        pLits = Vec_IntEntryP( vCopies, 2*iObj );
        if ( !Acb_ObjToGiaDual( pNew, p, iObj, vFanins, vCopies, pLits, NULL, NULL, 0, 0 ) )
        {
            Vec_IntFree( vNodes );
            Vec_IntFree( vFanins );
            Vec_IntFree( vCutMap );
            Vec_IntFree( vCopies );
            Gia_ManStop( pNew );
            return NULL;
        }
    }
    Vec_IntFree( vNodes );
    Vec_IntFree( vFanins );
    if ( vTargets )
    {
        Vec_IntForEachEntry( vTargets, iObj, i )
        {
            pLits = Vec_IntEntryP( vCopies, 2*iObj );
            Gia_ManAppendCo( pNew, pLits[0] );
            Gia_ManAppendCo( pNew, pLits[1] );
        }
    }
    else Acb_NtkForEachCo( p, iObj, i )
    {
        pLits = Vec_IntEntryP( vCopies, 2*Acb_ObjFanin(p, iObj, 0) );
        Gia_ManAppendCo( pNew, pLits[0] );
        Gia_ManAppendCo( pNew, pLits[1] );
    }
    Vec_IntFree( vCutMap );
    Vec_IntFree( vCopies );
    pNew = Gia_ManCleanup( pOne = pNew );
    Gia_ManStop( pOne );
    return pNew;
}
Gia_Man_t * Acb_NtkGiaDeriveDual( Acb_Ntk_t * p )
{
    return Acb_NtkGiaDeriveDualTargets( p, NULL );
}

Vec_Int_t * Acb_NtkCollectPoMuxCutpoints( Acb_Ntk_t * p )
{
    Vec_Int_t * vCutObjs = Vec_IntAlloc( Acb_NtkCoNum(p) );
    int i, iObj, iFanin;
    Acb_NtkForEachCo( p, iObj, i )
    {
        iFanin = Acb_ObjFanin( p, iObj, 0 );
        while ( !Acb_ObjIsCio(p, iFanin) && Acb_ObjType(p, iFanin) == ABC_OPER_BIT_BUF )
            iFanin = Acb_ObjFanin( p, iFanin, 0 );
        if ( !Acb_ObjIsCio(p, iFanin) && Acb_ObjType(p, iFanin) == ABC_OPER_BIT_MUX )
            Vec_IntPush( vCutObjs, iFanin );
    }
    if ( Vec_IntSize(vCutObjs) != Acb_NtkCoNum(p) )
        Vec_IntClear( vCutObjs );
    return vCutObjs;
}

Vec_Int_t * Acb_NtkCollectPoMuxSelectors( Acb_Ntk_t * p, Vec_Int_t * vCutObjs )
{
    Vec_Int_t * vSelectors = Vec_IntAlloc( 4 );
    int i, iObj, iSel;
    if ( vCutObjs == NULL )
        return vSelectors;
    Vec_IntForEachEntry( vCutObjs, iObj, i )
    {
        assert( !Acb_ObjIsCio(p, iObj) && Acb_ObjType(p, iObj) == ABC_OPER_BIT_MUX );
        iSel = Acb_ObjFanin( p, iObj, 2 );
        if ( Vec_IntFind(vSelectors, iSel) == -1 )
            Vec_IntPush( vSelectors, iSel );
    }
    return vSelectors;
}

Vec_Int_t * Acb_NtkCollectPoMuxSelectorIds( Acb_Ntk_t * p, Vec_Int_t * vCutObjs, Vec_Int_t * vSelectors )
{
    Vec_Int_t * vIds = Vec_IntAlloc( Acb_NtkCoNum(p) );
    int i, iObj, iSel, iSelId;
    if ( vCutObjs == NULL || vSelectors == NULL )
        return vIds;
    Vec_IntForEachEntry( vCutObjs, iObj, i )
    {
        assert( !Acb_ObjIsCio(p, iObj) && Acb_ObjType(p, iObj) == ABC_OPER_BIT_MUX );
        iSel = Acb_ObjFanin( p, iObj, 2 );
        iSelId = Vec_IntFind( vSelectors, iSel );
        assert( iSelId >= 0 );
        Vec_IntPush( vIds, iSelId );
    }
    return vIds;
}

Vec_Int_t * Acb_NtkCollectCoDriversForSelector( Acb_Ntk_t * p, Vec_Int_t * vPoSelIds, int iSelId )
{
    Vec_Int_t * vDrivers = Vec_IntAlloc( Acb_NtkCoNum(p) );
    int i, iObj;
    Acb_NtkForEachCo( p, iObj, i )
        if ( Vec_IntEntry(vPoSelIds, i) == iSelId )
            Vec_IntPush( vDrivers, Acb_ObjFanin(p, iObj, 0) );
    return vDrivers;
}

Vec_Int_t * Acb_NtkCollectPoIdsForSelector( Acb_Ntk_t * p, Vec_Int_t * vPoSelIds, int iSelId )
{
    Vec_Int_t * vPos = Vec_IntAlloc( Acb_NtkCoNum(p) );
    int i, iObj;
    Acb_NtkForEachCo( p, iObj, i )
    {
        (void)iObj;
        if ( Vec_IntEntry(vPoSelIds, i) == iSelId )
            Vec_IntPush( vPos, i );
    }
    return vPos;
}

Vec_Int_t * Acb_NtkCollectPoMuxBranchTargets( Acb_Ntk_t * p, Vec_Int_t * vCutObjs, Vec_Int_t * vPoSelIds, int iSelId, int fUseOneBranch )
{
    Vec_Int_t * vTargets = Vec_IntAlloc( Acb_NtkCoNum(p) );
    int i, iObj;
    Vec_IntForEachEntry( vCutObjs, iObj, i )
    {
        if ( Vec_IntEntry(vPoSelIds, i) != iSelId )
            continue;
        assert( !Acb_ObjIsCio(p, iObj) && Acb_ObjType(p, iObj) == ABC_OPER_BIT_MUX );
        Vec_IntPush( vTargets, Acb_ObjFanin(p, iObj, fUseOneBranch ? 1 : 0) );
    }
    return vTargets;
}
Vec_Int_t * Acb_NtkCollectPoMuxCubeTargets( Acb_Ntk_t * p, Vec_Int_t * vCutObjs, Vec_Int_t * vPoSelIds, Vec_Int_t * vCubeVals )
{
    Vec_Int_t * vTargets = Vec_IntAlloc( Acb_NtkCoNum(p) + 2 * Vec_IntSize(vCubeVals) );
    int i, iObj, iSelId, fUseOneBranch;
    Vec_IntForEachEntry( vCutObjs, iObj, i )
    {
        assert( !Acb_ObjIsCio(p, iObj) && Acb_ObjType(p, iObj) == ABC_OPER_BIT_MUX );
        iSelId = Vec_IntEntry( vPoSelIds, i );
        assert( iSelId >= 0 && iSelId < Vec_IntSize(vCubeVals) );
        fUseOneBranch = Vec_IntEntry( vCubeVals, iSelId );
        Vec_IntPush( vTargets, Acb_ObjFanin(p, iObj, fUseOneBranch ? 1 : 0) );
    }
    return vTargets;
}

int Acb_NtkCollectInternalDcControls( Acb_Ntk_t * p, Vec_Int_t ** pvDcObjs, Vec_Int_t ** pvDcCtrls, Vec_Int_t ** pvDcCtrlIds )
{
    extern Vec_Int_t * Acb_NtkFindNodes2( Acb_Ntk_t * p );
    Vec_Int_t * vNodes = Acb_NtkFindNodes2( p );
    Vec_Int_t * vDcObjs = Vec_IntAlloc( 16 );
    Vec_Int_t * vDcCtrls = Vec_IntAlloc( 4 );
    Vec_Int_t * vDcCtrlIds = Vec_IntAlloc( 16 );
    int i, iObj, iCtrl, iCtrlId;
    Vec_IntForEachEntry( vNodes, iObj, i )
    {
        if ( Acb_ObjIsCio(p, iObj) || Acb_ObjType(p, iObj) != ABC_OPER_TRI )
            continue;
        iCtrl = Acb_ObjFanin( p, iObj, 1 );
        iCtrlId = Vec_IntFind( vDcCtrls, iCtrl );
        if ( iCtrlId == -1 )
        {
            iCtrlId = Vec_IntSize( vDcCtrls );
            Vec_IntPush( vDcCtrls, iCtrl );
        }
        Vec_IntPush( vDcObjs, iObj );
        Vec_IntPush( vDcCtrlIds, iCtrlId );
    }
    Vec_IntFree( vNodes );
    *pvDcObjs = vDcObjs;
    *pvDcCtrls = vDcCtrls;
    *pvDcCtrlIds = vDcCtrlIds;
    return Vec_IntSize( vDcObjs );
}

Vec_Int_t * Acb_NtkCollectDcObjsForControl( Vec_Int_t * vDcObjs, Vec_Int_t * vDcCtrlIds, int iCtrlId )
{
    Vec_Int_t * vRes = Vec_IntAlloc( Vec_IntSize(vDcObjs) );
    int i, iObj;
    Vec_IntForEachEntry( vDcObjs, iObj, i )
        if ( Vec_IntEntry(vDcCtrlIds, i) == iCtrlId )
            Vec_IntPush( vRes, iObj );
    return vRes;
}

int Acb_NtkCollectPoDcCutpoints( Acb_Ntk_t * p, Vec_Int_t ** pvDataObjs, Vec_Int_t ** pvCtrlObjs )
{
    Vec_Int_t * vDataObjs = Vec_IntAlloc( Acb_NtkCoNum(p) );
    Vec_Int_t * vCtrlObjs = Vec_IntAlloc( Acb_NtkCoNum(p) );
    int i, iObj, iFanin;
    Acb_NtkForEachCo( p, iObj, i )
    {
        iFanin = Acb_ObjFanin( p, iObj, 0 );
        while ( !Acb_ObjIsCio(p, iFanin) && Acb_ObjType(p, iFanin) == ABC_OPER_BIT_BUF )
            iFanin = Acb_ObjFanin( p, iFanin, 0 );
        if ( Acb_ObjIsCio(p, iFanin) || Acb_ObjType(p, iFanin) != ABC_OPER_TRI )
            break;
        Vec_IntPush( vDataObjs, Acb_ObjFanin(p, iFanin, 0) );
        Vec_IntPush( vCtrlObjs, Acb_ObjFanin(p, iFanin, 1) );
    }
    if ( i != Acb_NtkCoNum(p) )
    {
        Vec_IntFree( vDataObjs );
        Vec_IntFree( vCtrlObjs );
        *pvDataObjs = NULL;
        *pvCtrlObjs = NULL;
        return 0;
    }
    *pvDataObjs = vDataObjs;
    *pvCtrlObjs = vCtrlObjs;
    return 1;
}

Vec_Int_t * Acb_NtkCollectCoDrivers( Acb_Ntk_t * p )
{
    Vec_Int_t * vDrivers = Vec_IntAlloc( Acb_NtkCoNum(p) );
    int i, iObj;
    Acb_NtkForEachCo( p, iObj, i )
        Vec_IntPush( vDrivers, Acb_ObjFanin(p, iObj, 0) );
    return vDrivers;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Acb_NtkGiaDeriveMiter( Gia_Man_t * pOne, Gia_Man_t * pTwo, int Type )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    assert( Gia_ManCiNum(pOne) == Gia_ManCiNum(pTwo) );
    assert( Gia_ManCoNum(pOne) == Gia_ManCoNum(pTwo) );
    pNew = Gia_ManStart( Gia_ManObjNum(pOne) + Gia_ManObjNum(pTwo) + 5*Gia_ManCoNum(pOne)/2 );
    pNew->pName = Abc_UtilStrsav( "miter" );
    pNew->pSpec = NULL;
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(pOne)->Value = 0;
    Gia_ManConst0(pTwo)->Value = 0;
    Gia_ManForEachCi( pOne, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachCi( pTwo, pObj, i )
        pObj->Value = Gia_ManCi(pOne, i)->Value;
    Gia_ManForEachAnd( pOne, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachAnd( pTwo, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( pOne, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    Gia_ManForEachCo( pTwo, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    if ( Type == 0 ) // only main circuit
    {
        for ( i = 0; i < Gia_ManCoNum(pOne); i += 2 )
        {
            unsigned pLitsF[2] = { Gia_ManCo(pOne, i)->Value, Gia_ManCo(pOne, i+1)->Value };
            unsigned pLitsS[2] = { Gia_ManCo(pTwo, i)->Value, Gia_ManCo(pTwo, i+1)->Value };
            Gia_ManAppendCo( pNew, pLitsF[0] );
            Gia_ManAppendCo( pNew, pLitsS[0] );
        }
    }
    else if ( Type == 1 ) // only shadow circuit
    {
        for ( i = 0; i < Gia_ManCoNum(pOne); i += 2 )
        {
            unsigned pLitsF[2] = { Gia_ManCo(pOne, i)->Value, Gia_ManCo(pOne, i+1)->Value };
            unsigned pLitsS[2] = { Gia_ManCo(pTwo, i)->Value, Gia_ManCo(pTwo, i+1)->Value };
            Gia_ManAppendCo( pNew, pLitsF[1] );
            Gia_ManAppendCo( pNew, pLitsS[1] );
        }
    }
    else if ( Type == 3 ) // raw dual-rail outputs of the two designs
    {
        for ( i = 0; i < Gia_ManCoNum(pOne); i += 2 )
        {
            Gia_ManAppendCo( pNew, Gia_ManCo(pOne, i)->Value );
            Gia_ManAppendCo( pNew, Gia_ManCo(pOne, i+1)->Value );
            Gia_ManAppendCo( pNew, Gia_ManCo(pTwo, i)->Value );
            Gia_ManAppendCo( pNew, Gia_ManCo(pTwo, i+1)->Value );
        }
    }
    else // comparator of the two
    {
        for ( i = 0; i < Gia_ManCoNum(pOne); i += 2 )
        {
            int pLitsF[2] = { (int)Gia_ManCo(pOne, i)->Value, (int)Gia_ManCo(pOne, i+1)->Value };
            int pLitsS[2] = { (int)Gia_ManCo(pTwo, i)->Value, (int)Gia_ManCo(pTwo, i+1)->Value };
            Gia_ManAppendCo( pNew, Gia_ManDualCompare( pNew, pLitsF, pLitsS ) );
        }
    }
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

Gia_Man_t * Acb_NtkGiaDeriveMiterWithSecondExtras( Gia_Man_t * pOne, Gia_Man_t * pTwo, int nExtraPairs )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, nCompareCos = Gia_ManCoNum(pOne);
    assert( Gia_ManCiNum(pOne) == Gia_ManCiNum(pTwo) );
    assert( Gia_ManCoNum(pTwo) == Gia_ManCoNum(pOne) + 2*nExtraPairs );
    pNew = Gia_ManStart( Gia_ManObjNum(pOne) + Gia_ManObjNum(pTwo) + 5*nCompareCos/2 + 2*nExtraPairs );
    pNew->pName = Abc_UtilStrsav( "miter_with_selectors" );
    pNew->pSpec = NULL;
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(pOne)->Value = 0;
    Gia_ManConst0(pTwo)->Value = 0;
    Gia_ManForEachCi( pOne, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachCi( pTwo, pObj, i )
        pObj->Value = Gia_ManCi(pOne, i)->Value;
    Gia_ManForEachAnd( pOne, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachAnd( pTwo, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( pOne, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    Gia_ManForEachCo( pTwo, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    for ( i = 0; i < nCompareCos; i += 2 )
    {
        int pLitsF[2] = { (int)Gia_ManCo(pOne, i)->Value, (int)Gia_ManCo(pOne, i+1)->Value };
        int pLitsS[2] = { (int)Gia_ManCo(pTwo, i)->Value, (int)Gia_ManCo(pTwo, i+1)->Value };
        Gia_ManAppendCo( pNew, Gia_ManDualCompare( pNew, pLitsF, pLitsS ) );
    }
    for ( i = nCompareCos; i < Gia_ManCoNum(pTwo); i++ )
        Gia_ManAppendCo( pNew, (int)Gia_ManCo(pTwo, i)->Value );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

Gia_Man_t * Acb_GiaDeriveBranchConditionMiter( Gia_Man_t * p, int nMiterOuts, int fUseOneBranch )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, LitSel, LitSelX, LitCond;
    assert( nMiterOuts > 0 );
    assert( Gia_ManCoNum(p) == nMiterOuts + 2 );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + nMiterOuts + 4 );
    pNew->pName = Abc_UtilStrsav( "branch_condition_miter" );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    LitSel  = (int)Gia_ManCo(p, nMiterOuts)->Value;
    LitSelX = (int)Gia_ManCo(p, nMiterOuts + 1)->Value;
    LitCond = Gia_ManHashAnd( pNew, Abc_LitNot(LitSelX), fUseOneBranch ? LitSel : Abc_LitNot(LitSel) );
    for ( i = 0; i < nMiterOuts; i++ )
        Gia_ManAppendCo( pNew, Gia_ManHashAnd( pNew, (int)Gia_ManCo(p, i)->Value, LitCond ) );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}
Gia_Man_t * Acb_GiaDeriveCubeConditionMiter( Gia_Man_t * p, int nMiterOuts, Vec_Int_t * vCubeVals )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, k, LitSel, LitSelX, LitCond = 1;
    int nCubes = Vec_IntSize(vCubeVals);
    assert( nMiterOuts > 0 );
    assert( Gia_ManCoNum(p) == nMiterOuts + 2*nCubes );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + nMiterOuts + 4*nCubes + 4 );
    pNew->pName = Abc_UtilStrsav( "cube_condition_miter" );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    for ( k = 0; k < nCubes; k++ )
    {
        LitSel  = (int)Gia_ManCo(p, nMiterOuts + 2*k)->Value;
        LitSelX = (int)Gia_ManCo(p, nMiterOuts + 2*k + 1)->Value;
        LitSel  = Vec_IntEntry(vCubeVals, k) ? LitSel : Abc_LitNot(LitSel);
        LitCond = Gia_ManHashAnd( pNew, LitCond, Gia_ManHashAnd( pNew, Abc_LitNot(LitSelX), LitSel ) );
    }
    for ( i = 0; i < nMiterOuts; i++ )
        Gia_ManAppendCo( pNew, Gia_ManHashAnd( pNew, (int)Gia_ManCo(p, i)->Value, LitCond ) );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

Gia_Man_t * Acb_NtkGiaDeriveMiterDcGuard( Gia_Man_t * pOne, Gia_Man_t * pData, Gia_Man_t * pCtrl )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    assert( Gia_ManCiNum(pOne) == Gia_ManCiNum(pData) );
    assert( Gia_ManCiNum(pOne) == Gia_ManCiNum(pCtrl) );
    assert( Gia_ManCoNum(pOne) == Gia_ManCoNum(pData) );
    assert( Gia_ManCoNum(pOne) == Gia_ManCoNum(pCtrl) );
    pNew = Gia_ManStart( Gia_ManObjNum(pOne) + Gia_ManObjNum(pData) + Gia_ManObjNum(pCtrl) + 6*Gia_ManCoNum(pOne)/2 );
    pNew->pName = Abc_UtilStrsav( "dc_guard_miter" );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(pOne)->Value = 0;
    Gia_ManConst0(pData)->Value = 0;
    Gia_ManConst0(pCtrl)->Value = 0;
    Gia_ManForEachCi( pOne, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachCi( pData, pObj, i )
        pObj->Value = Gia_ManCi(pOne, i)->Value;
    Gia_ManForEachCi( pCtrl, pObj, i )
        pObj->Value = Gia_ManCi(pOne, i)->Value;
    Gia_ManForEachAnd( pOne, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachAnd( pData, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachAnd( pCtrl, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( pOne, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    Gia_ManForEachCo( pData, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    Gia_ManForEachCo( pCtrl, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    for ( i = 0; i < Gia_ManCoNum(pOne); i += 2 )
    {
        int pLitsF[2] = { (int)Gia_ManCo(pOne, i)->Value,  (int)Gia_ManCo(pOne, i+1)->Value };
        int pLitsS[2] = { (int)Gia_ManCo(pData, i)->Value, (int)Gia_ManCo(pData, i+1)->Value };
        int Ctrl0     = (int)Gia_ManCo(pCtrl, i)->Value;
        int Ctrl1     = (int)Gia_ManCo(pCtrl, i+1)->Value;
        pLitsS[1] = Gia_ManHashOr( pNew, pLitsS[1], Gia_ManHashOr( pNew, Ctrl0, Ctrl1 ) );
        Gia_ManAppendCo( pNew, Gia_ManDualCompare( pNew, pLitsF, pLitsS ) );
    }
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}


/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_OutputFile( char * pFileName, Acb_Ntk_t * pNtkF, int * pModel, int Status )
{
    const char * pFileName0 = pFileName? pFileName : "output";
    FILE * pFile = fopen( pFileName0, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open results file \"%s\".\n", pFileName0 );
        return;
    }
    if ( Status == ACB_XEC_UNDEC )
        fprintf( pFile, "UNDECIDED\n" );
    else if ( pModel == NULL )
        fprintf( pFile, "EQ\n" );
    else
    {
        /*
        NEQ
        in 1
        a 1
        b 0
        */
        int i, iObj;
        fprintf( pFile, "NEQ\n" );
        Acb_NtkForEachPi( pNtkF, iObj, i )
            fprintf( pFile, "%s %d\n", Acb_ObjNameStr(pNtkF, iObj), pModel[i] );
    }
    fclose( pFile );
    printf( "Produced output file \"%s\".\n\n", pFileName0 );
}
int * Acb_NtkSolve( Gia_Man_t * p, int fVerbose, int * pStatus )
{
    extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
    Aig_Man_t * pMan = Gia_ManToAig( p, 0 );
    Abc_Ntk_t * pNtkTemp = Abc_NtkFromAigPhase( pMan );
    Prove_Params_t Params, * pParams = &Params;
    Prove_ParamsSetDefault( pParams );
    pParams->fUseRewriting = 1;
    pParams->fVerbose      = fVerbose;
    Aig_ManStop( pMan );
    if ( pNtkTemp )
    {
        abctime clk = Abc_Clock();
        int RetValue = Abc_NtkIvyProve( &pNtkTemp, pParams );
        int * pModel = pNtkTemp->pModel;
        pNtkTemp->pModel = NULL;
        Abc_NtkDelete( pNtkTemp );
        *pStatus = RetValue;
        printf( "The networks are %s.  ", RetValue == 1 ? "equivalent" : (RetValue == 0 ? "NOT equivalent" : "UNDECIDED") );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        if ( RetValue == 0 )
            return pModel;
    }
    *pStatus = ACB_XEC_UNDEC;
    return NULL;
}
int * Acb_NtkSolveIvyPrecheck( Gia_Man_t * p, int fVerbose, int * pStatus )
{
    extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
    Aig_Man_t * pMan = Gia_ManToAig( p, 0 );
    Abc_Ntk_t * pNtkTemp = Abc_NtkFromAigPhase( pMan );
    Prove_Params_t Params, * pParams = &Params;
    Prove_ParamsSetDefault( pParams );
    pParams->fUseFraiging         = 1;
    pParams->fUseRewriting        = 1;
    pParams->fUseBdds             = 0;
    pParams->nItersMax            = 6;
    pParams->nMiteringLimitStart  = 5000;
    pParams->nMiteringLimitMulti  = 2.0;
    pParams->nFraigingLimitStart  = 2;
    pParams->nFraigingLimitMulti  = 8.0;
    pParams->nMiteringLimitLast   = 0;
    pParams->nTotalBacktrackLimit = 750000;
    pParams->fVerbose             = fVerbose;
    Aig_ManStop( pMan );
    if ( pNtkTemp )
    {
        abctime clk = Abc_Clock();
        int RetValue;
        int * pModel;
        if ( fVerbose )
            printf( "Trying bounded Ivy/FRAIG precheck before CaDiCaL: And = %d. PO = %d. total conflict limit = %d.\n",
                Gia_ManAndNum(p), Gia_ManCoNum(p), (int)pParams->nTotalBacktrackLimit );
        RetValue = Abc_NtkIvyProve( &pNtkTemp, pParams );
        pModel = pNtkTemp->pModel;
        pNtkTemp->pModel = NULL;
        Abc_NtkDelete( pNtkTemp );
        *pStatus = RetValue;
        printf( "The networks are %s by bounded Ivy/FRAIG precheck.  ",
            RetValue == 1 ? "equivalent" : (RetValue == 0 ? "NOT equivalent" : "UNDECIDED") );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        if ( RetValue == 0 )
            return pModel;
        ABC_FREE( pModel );
        return NULL;
    }
    *pStatus = ACB_XEC_UNDEC;
    return NULL;
}
int * Acb_NtkSolveNormalPrecheck( Gia_Man_t * p, int fVerbose, int * pStatus, int nBacktrackLimit )
{
    extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
    Aig_Man_t * pMan = Gia_ManToAig( p, 0 );
    Abc_Ntk_t * pNtkTemp = Abc_NtkFromAigPhase( pMan );
    Prove_Params_t Params, * pParams = &Params;
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    Prove_ParamsSetDefault( pParams );
    pParams->fUseRewriting        = 1;
    pParams->nTotalBacktrackLimit = nBacktrackLimit;
    pParams->fVerbose             = fVerbose;
    Aig_ManStop( pMan );
    if ( pNtkTemp )
    {
        abctime clk = Abc_Clock();
        int RetValue;
        int * pModel;
        if ( fVerbose )
            printf( "Trying normal XEC precheck before CaDiCaL-specific UNSAT passes: And = %d. PO = %d. backtrack limit = %d.\n",
                Gia_ManAndNum(p), Gia_ManCoNum(p), nBacktrackLimit );
        RetValue = Abc_NtkIvyProve( &pNtkTemp, pParams );
        pModel = pNtkTemp->pModel;
        pNtkTemp->pModel = NULL;
        Abc_NtkDelete( pNtkTemp );
        if ( pStatus )
            *pStatus = RetValue;
        printf( "The networks are %s by normal XEC precheck.  ",
            RetValue == 1 ? "equivalent" : (RetValue == 0 ? "NOT equivalent" : "UNDECIDED") );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        if ( RetValue == 0 )
            return pModel;
        ABC_FREE( pModel );
        return NULL;
    }
    return NULL;
}
Gia_Man_t * Acb_NtkFraigEquivReduce( Gia_Man_t * p, int fVerbose, char * pLabel, char * pPhase, int nWords, int nConfLimit, int nSatVarMax, int nMinGain )
{
    Dch_Pars_t Pars, * pPars = &Pars;
    Gia_Man_t * pWork = NULL, * pNew = NULL, * pTemp = NULL;
    int nAndStart = Gia_ManAndNum( p );
    abctime clk = Abc_Clock();
    if ( Gia_ManCoNum(p) == 0 || nAndStart < 1000 )
        return NULL;
    Dch_ManSetDefaultParams( pPars );
    pPars->nWords      = nWords;
    pPars->nBTLimit    = nConfLimit;
    pPars->nSatVarMax  = nSatVarMax;
    pPars->fSynthesis  = 0;
    pPars->fPolarFlip  = 1;
    pPars->fSimulateTfo= 1;
    pPars->fVerbose    = 0;
    pWork = Gia_ManDup( p );
    if ( pWork == NULL )
        return NULL;
    if ( fVerbose )
        printf( "%s %s FRAIG equivalence reduction: And = %d. PO = %d. words = %d. node-conf = %d. sat-var-max = %d.\n",
            pLabel ? pLabel : "XEC", pPhase ? pPhase : "structural", nAndStart, Gia_ManCoNum(p), nWords, nConfLimit, nSatVarMax );
    pNew = Gia_ManFraigSweepSimple( pWork, pPars );
    Gia_ManStop( pWork );
    if ( pNew == NULL )
        return NULL;
    pTemp = Gia_ManCompress2( pNew, 1, 0 );
    if ( pTemp )
    {
        Gia_ManStop( pNew );
        pNew = pTemp;
    }
    if ( fVerbose )
    {
        printf( "%s %s FRAIG equivalence reduction: And = %d -> %d. Lev = %d -> %d. ",
            pLabel ? pLabel : "XEC", pPhase ? pPhase : "structural",
            nAndStart, Gia_ManAndNum(pNew), Gia_ManLevelNum(p), Gia_ManLevelNum(pNew) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    if ( Gia_ManCoNum(pNew) != Gia_ManCoNum(p) || Gia_ManAndNum(pNew) >= nAndStart - nMinGain )
    {
        if ( fVerbose && Gia_ManCoNum(pNew) == Gia_ManCoNum(p) )
            printf( "%s %s FRAIG equivalence reduction skipped because the proven merge gain is too small.\n",
                pLabel ? pLabel : "XEC", pPhase ? pPhase : "structural" );
        Gia_ManStop( pNew );
        return NULL;
    }
    return pNew;
}
int Acb_NtkObjIsConstTypeThroughBuf( Acb_Ntk_t * p, int iObj, Acb_ObjType_t Type )
{
    while ( !Acb_ObjIsCio(p, iObj) && Acb_ObjType(p, iObj) == ABC_OPER_BIT_BUF )
        iObj = Acb_ObjFanin(p, iObj, 0);
    return !Acb_ObjIsCio(p, iObj) && Acb_ObjType(p, iObj) == Type;
}
int Acb_NtkDcObjIsConstXSeed( Acb_Ntk_t * p, int iObj )
{
    if ( iObj <= 0 || Acb_ObjIsCio(p, iObj) || Acb_ObjType(p, iObj) != ABC_OPER_TRI )
        return 0;
    if ( Acb_ObjFaninNum(p, iObj) != 2 )
        return 0;
    return Acb_NtkObjIsConstTypeThroughBuf( p, Acb_ObjFanin(p, iObj, 0), ABC_OPER_CONST_F ) &&
           Acb_NtkObjIsConstTypeThroughBuf( p, Acb_ObjFanin(p, iObj, 1), ABC_OPER_CONST_T );
}
int Acb_NtkAllDcObjsAreConstXSeeds( Acb_Ntk_t * p, Vec_Int_t * vDcObjs )
{
    int i, iObj;
    if ( vDcObjs == NULL || Vec_IntSize(vDcObjs) == 0 )
        return 0;
    Vec_IntForEachEntry( vDcObjs, iObj, i )
        if ( !Acb_NtkDcObjIsConstXSeed(p, iObj) )
            return 0;
    return 1;
}
int * Acb_NtkSolveConstXSeedCanonical( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, Vec_Int_t * vDcObjsG, int fVerbose, int * pStatus, int nSatTimeLimit )
{
    Vec_Int_t * vTargetsF = NULL, * vTargetsG = NULL;
    Gia_Man_t * pGiaF = NULL, * pGiaG = NULL, * pGia = NULL, * pTemp = NULL;
    int Status = ACB_XEC_UNDEC, * pModel = NULL;
    abctime clk = Abc_Clock();
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    if ( !Acb_NtkAllDcObjsAreConstXSeeds(pNtkG, vDcObjsG) )
        return NULL;
    vTargetsF = Acb_NtkCollectCoDrivers( pNtkF );
    vTargetsG = Acb_NtkCollectCoDrivers( pNtkG );
    pGiaF = Acb_NtkGiaDeriveDualTargets( pNtkF, vTargetsF );
    pGiaG = Acb_NtkGiaDeriveDualTargetsForceZero( pNtkG, vTargetsG );
    pGia  = Acb_NtkGiaDeriveMiter( pGiaF, pGiaG, 2 );
    if ( fVerbose )
        printf( "Trying constant-X seed canonical proof: DC seeds = %d. And = %d. PO = %d. limit = %d sec.\n",
            Vec_IntSize(vDcObjsG), Gia_ManAndNum(pGia), Gia_ManCoNum(pGia), nSatTimeLimit );
    if ( Gia_ManAndNum(pGia) > 5000 )
    {
        pTemp = Gia_ManCompress2( pGia, 1, 0 );
        if ( pTemp )
        {
            if ( fVerbose )
                printf( "Constant-X seed canonical compression: And = %d -> %d. PO = %d.\n",
                    Gia_ManAndNum(pGia), Gia_ManAndNum(pTemp), Gia_ManCoNum(pTemp) );
            Gia_ManStop( pGia );
            pGia = pTemp;
            pTemp = NULL;
        }
    }
    if ( Gia_ManAndNum(pGia) > 8000 )
    {
        pTemp = Acb_NtkFraigEquivReduce( pGia, fVerbose,
            "Constant-X seed canonical proof", "canonical dual", 32, 300, 12000,
            Abc_MaxInt( 50, Gia_ManAndNum(pGia) / 200 ) );
        if ( pTemp )
        {
            Gia_ManStop( pGia );
            pGia = pTemp;
            pTemp = NULL;
        }
    }
    if ( Gia_ManCoNum(pGia) == 0 || Acb_GiaAllPosConst0(pGia) )
    {
        Status = ACB_XEC_EQ;
        if ( fVerbose )
            printf( "Constant-X seed canonical proof: all miter outputs are constant-0 after canonicalization.\n" );
    }
    else
        pModel = Acb_NtkSolveCadicalLimit( pGia, 0, fVerbose, &Status, nSatTimeLimit,
            "constant-X seed canonical CaDiCaL", 0 );
    if ( pStatus )
        *pStatus = Status;
    if ( Status == ACB_XEC_EQ )
    {
        printf( "The networks are equivalent by constant-X seed canonical proof.  " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    else if ( fVerbose )
    {
        printf( "The networks are %s by constant-X seed canonical proof.  ",
            Status == ACB_XEC_NEQ ? "NOT equivalent" : "UNDECIDED" );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    Gia_ManStop( pGia );
    Gia_ManStop( pGiaG );
    Gia_ManStop( pGiaF );
    Vec_IntFree( vTargetsG );
    Vec_IntFree( vTargetsF );
    return pModel;
}
Gia_Man_t * Acb_NtkBranchSweepReduce( Gia_Man_t * p, int fVerbose, char * pLabel )
{
    Cec_ParFra_t Pars, * pPars = &Pars;
    Gia_Man_t * pNew = NULL, * pBest = NULL, * pFraig = NULL;
    abctime clk = Abc_Clock();
    int nAndStart = Gia_ManAndNum( p );
    if ( Gia_ManCoNum(p) < 8 || nAndStart < 8000 || nAndStart > 60000 )
        return NULL;
    Cec_ManFraSetDefaultParams( pPars );
    pPars->nWords       = 64;
    pPars->nRounds      = 8;
    pPars->nItersMax    = 6;
    pPars->nBTLimit     = 800;
    pPars->nBTLimitPo   = 0;
    pPars->TimeLimit    = 90;
    pPars->fCheckMiter  = 0;
    pPars->fSatSweeping = 1;
    pPars->fUseCones    = 1;
    pPars->fRewriting   = 1;
    pPars->fVerbose     = 0;
    if ( fVerbose )
        printf( "%s branch SAT-sweeping reduction: And = %d. PO = %d. limit = %d sec. node-conf = %d.\n",
            pLabel ? pLabel : "XEC", nAndStart, Gia_ManCoNum(p), pPars->TimeLimit, pPars->nBTLimit );
    pNew = Cec_ManSatSweeping( p, pPars, 1 );
    if ( pNew == NULL )
    {
        if ( fVerbose )
            printf( "%s branch SAT-sweeping reduction produced no network.\n", pLabel ? pLabel : "XEC" );
    }
    else if ( fVerbose )
    {
        printf( "%s branch SAT-sweeping reduction: And = %d -> %d. Lev = %d -> %d. ",
            pLabel ? pLabel : "XEC", nAndStart, Gia_ManAndNum(pNew), Gia_ManLevelNum(p), Gia_ManLevelNum(pNew) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    if ( pNew && Gia_ManCoNum(pNew) == Gia_ManCoNum(p) && Gia_ManAndNum(pNew) < nAndStart )
        pBest = pNew, pNew = NULL;
    if ( pNew )
        Gia_ManStop( pNew );
    if ( nAndStart >= 15000 )
        pFraig = Acb_NtkFraigEquivReduce( pBest ? pBest : p, fVerbose, pLabel, "branch", 32, 300, 12000, Abc_MaxInt( 50, nAndStart / 200 ) );
    if ( pFraig )
    {
        if ( pBest )
            Gia_ManStop( pBest );
        pBest = pFraig;
    }
    if ( pBest == NULL || Gia_ManAndNum(pBest) >= nAndStart - Abc_MaxInt( 50, nAndStart / 100 ) )
    {
        if ( fVerbose )
            printf( "%s branch structural reduction skipped because reduction is too small.\n", pLabel ? pLabel : "XEC" );
        if ( pBest )
            Gia_ManStop( pBest );
        return NULL;
    }
    return pBest;
}
int Acb_GiaAndObligationsUniq( Gia_Man_t * p, Vec_Int_t * vReq )
{
    Vec_Int_t * vSeen = Vec_IntStart( Gia_ManObjNum(p) );
    int i, Lit, Var, Sign, Prev, nOut = 0;
    Vec_IntForEachEntry( vReq, Lit, i )
    {
        if ( Lit < 2 )
            continue;
        Var = Abc_Lit2Var( Lit );
        Sign = Abc_LitIsCompl( Lit ) ? 2 : 1;
        Prev = Vec_IntEntry( vSeen, Var );
        if ( Prev && Prev != Sign )
        {
            Vec_IntFree( vSeen );
            return 1;
        }
        if ( Prev == Sign )
            continue;
        Vec_IntWriteEntry( vSeen, Var, Sign );
        Vec_IntWriteEntry( vReq, nOut++, Lit );
    }
    Vec_IntShrink( vReq, nOut );
    Vec_IntFree( vSeen );
    return 0;
}
int Acb_GiaCollectLinearLit_rec( Gia_Man_t * p, int Lit, word * pRow, int nWords, int * pConst, int Depth )
{
    Gia_Obj_t * pObj, * pFan0 = NULL, * pFan1 = NULL;
    int iVar, Lit0, Lit1;
    if ( Depth > ACB_XEC_RECURSION_LIMIT )
        return 0;
    if ( Lit < 2 )
    {
        if ( Lit == 1 )
            *pConst ^= 1;
        return 1;
    }
    pObj = Gia_ManObj( p, Abc_Lit2Var(Lit) );
    if ( Abc_LitIsCompl(Lit) )
        *pConst ^= 1;
    if ( Gia_ObjIsCi(pObj) )
    {
        iVar = Gia_ObjCioId(pObj);
        pRow[iVar >> 6] ^= ((word)1) << (iVar & 63);
        return 1;
    }
    if ( Gia_ObjIsXor(pObj) )
    {
        if ( !Acb_GiaCollectLinearLit_rec( p, Gia_ObjFaninLit0p(p, pObj), pRow, nWords, pConst, Depth + 1 ) )
            return 0;
        if ( !Acb_GiaCollectLinearLit_rec( p, Gia_ObjFaninLit1p(p, pObj), pRow, nWords, pConst, Depth + 1 ) )
            return 0;
        return 1;
    }
    if ( Gia_ObjRecognizeExor( pObj, &pFan0, &pFan1 ) )
    {
        Lit0 = Abc_Var2Lit( Gia_ObjId(p, Gia_Regular(pFan0)), Gia_IsComplement(pFan0) );
        Lit1 = Abc_Var2Lit( Gia_ObjId(p, Gia_Regular(pFan1)), Gia_IsComplement(pFan1) );
        if ( !Acb_GiaCollectLinearLit_rec( p, Lit0, pRow, nWords, pConst, Depth + 1 ) )
            return 0;
        if ( !Acb_GiaCollectLinearLit_rec( p, Lit1, pRow, nWords, pConst, Depth + 1 ) )
            return 0;
        return 1;
    }
    return 0;
}
int Acb_GiaSolveLinearObligations( Gia_Man_t * p, Vec_Int_t * vReq, int fVerbose )
{
    int nVars, nWords, nRows, i, k, Lit, Const, Pivot, PivotRow, nRank = 0, fLinear = 1;
    word * pRows = NULL;
    unsigned char * pRhs = NULL;
    if ( p == NULL || vReq == NULL || Vec_IntSize(vReq) == 0 || Gia_ManCiNum(p) > 4096 )
        return ACB_XEC_UNDEC;
    nVars = Gia_ManCiNum(p);
    nWords = Abc_BitWordNum(nVars);
    nRows = Vec_IntSize(vReq);
    pRows = ABC_CALLOC( word, nRows * nWords );
    pRhs  = ABC_CALLOC( unsigned char, nRows );
    Vec_IntForEachEntry( vReq, Lit, i )
    {
        Const = 0;
        if ( !Acb_GiaCollectLinearLit_rec( p, Lit, pRows + i * nWords, nWords, &Const, 0 ) )
        {
            if ( fVerbose )
                printf( "Required-literal XOR-linear proof: obligation %d is non-linear; skipping.\n", i );
            fLinear = 0;
            break;
        }
        pRhs[i] = Const ^ 1;
    }
    for ( Pivot = 0; fLinear && Pivot < nVars && nRank < nRows; Pivot++ )
    {
        word Mask = ((word)1) << (Pivot & 63);
        int WordId = Pivot >> 6;
        PivotRow = -1;
        for ( i = nRank; i < nRows; i++ )
            if ( pRows[i*nWords + WordId] & Mask )
            {
                PivotRow = i;
                break;
            }
        if ( PivotRow < 0 )
            continue;
        if ( PivotRow != nRank )
        {
            for ( k = 0; k < nWords; k++ )
            {
                word Temp = pRows[nRank*nWords + k];
                pRows[nRank*nWords + k] = pRows[PivotRow*nWords + k];
                pRows[PivotRow*nWords + k] = Temp;
            }
            ABC_SWAP( unsigned char, pRhs[nRank], pRhs[PivotRow] );
        }
        for ( i = 0; i < nRows; i++ )
        {
            if ( i == nRank || !(pRows[i*nWords + WordId] & Mask) )
                continue;
            for ( k = WordId; k < nWords; k++ )
                pRows[i*nWords + k] ^= pRows[nRank*nWords + k];
            pRhs[i] ^= pRhs[nRank];
        }
        nRank++;
    }
    for ( i = 0; fLinear && i < nRows; i++ )
    {
        int fZero = 1;
        for ( k = 0; k < nWords; k++ )
            if ( pRows[i*nWords + k] )
            {
                fZero = 0;
                break;
            }
        if ( fZero && pRhs[i] )
        {
            if ( fVerbose )
                printf( "Required-literal XOR-linear proof: UNSAT. equations = %d. rank = %d.\n", nRows, nRank );
            ABC_FREE( pRows );
            ABC_FREE( pRhs );
            return ACB_XEC_EQ;
        }
    }
    if ( fLinear && fVerbose )
        printf( "Required-literal XOR-linear proof: consistent. equations = %d. rank = %d.\n", nRows, nRank );
    ABC_FREE( pRows );
    ABC_FREE( pRhs );
    return ACB_XEC_UNDEC;
}
Gia_Man_t * Acb_GiaDupWithObligationOutputs( Gia_Man_t * p, Vec_Int_t * vReq )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, Lit;
    pNew = Gia_ManStart( Gia_ManObjNum(p) + Vec_IntSize(vReq) + 100 );
    pNew->pName = Abc_UtilStrsav( "and_obligations" );
    Gia_ManHashAlloc( pNew );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Vec_IntForEachEntry( vReq, Lit, i )
        Gia_ManAppendCo( pNew, Gia_ObjLitCopy(p, Lit) );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}
int Acb_CnfWriteIntoCadical( cadical_solver * pSat, Cnf_Dat_t * pCnf )
{
    int i, * pBeg, * pEnd;
    if ( pSat == NULL || pCnf == NULL )
        return 0;
    cadical_solver_setnvars( pSat, pCnf->nVars );
    Cnf_CnfForClause( pCnf, pBeg, pEnd, i )
        if ( !cadical_solver_addclause( pSat, pBeg, pEnd ) )
            return 0;
    return 1;
}
int Acb_GiaSolveObligationListUnit( Gia_Man_t * p, Vec_Int_t * vReq, int fVerbose, int nSatTimeLimit, char * pLabel )
{
    Gia_Man_t * pObl = NULL;
    Aig_Man_t * pMan = NULL;
    Cnf_Dat_t * pCnf = NULL;
    cadical_solver * pSat = NULL;
    int i, Lit, Ret, Status = ACB_XEC_UNDEC;
    abctime clk = Abc_Clock();
    (void)nSatTimeLimit;
    if ( p == NULL || vReq == NULL || Vec_IntSize(vReq) == 0 )
        return ACB_XEC_UNDEC;
    if ( Acb_GiaAndObligationsUniq( p, vReq ) )
        return ACB_XEC_EQ;
    Status = Acb_GiaSolveLinearObligations( p, vReq, 0 );
    if ( Status == ACB_XEC_EQ )
        return Status;
    pObl = Acb_GiaDupWithObligationOutputs( p, vReq );
    pMan = pObl ? Gia_ManToAig( pObl, 0 ) : NULL;
    pCnf = pMan ? Cnf_Derive( pMan, Aig_ManCoNum(pMan) ) : NULL;
    pSat = pCnf ? cadical_solver_new() : NULL;
    if ( pCnf == NULL || pSat == NULL || !Acb_CnfWriteIntoCadical(pSat, pCnf) )
        goto cleanup;
    for ( i = 0; i < Gia_ManCoNum(pObl); i++ )
    {
        Ret = Acb_CnfCoDriverLit( pCnf, i, &Lit );
        if ( Ret < 0 )
        {
            Status = Ret == -1 ? ACB_XEC_EQ : ACB_XEC_UNDEC;
            goto cleanup;
        }
        if ( Ret > 0 && !cadical_solver_addclause( pSat, &Lit, &Lit + 1 ) )
        {
            Status = ACB_XEC_EQ;
            goto cleanup;
        }
    }
    Ret = cadical_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
    Status = Ret == -1 ? ACB_XEC_EQ : ACB_XEC_UNDEC;
cleanup:
    if ( fVerbose )
    {
        printf( "%s: %s. obligations = %d. ",
            pLabel ? pLabel : "Exact obligation unit branch",
            Status == ACB_XEC_EQ ? "UNSAT" : "UNDECIDED", Vec_IntSize(vReq) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    if ( pSat )
        cadical_solver_delete( pSat );
    if ( pCnf )
        Cnf_DataFree( pCnf );
    if ( pMan )
        Aig_ManStop( pMan );
    if ( pObl )
        Gia_ManStop( pObl );
    return Status;
}
typedef struct Acb_SplitPoOrder_t_ Acb_SplitPoOrder_t;
struct Acb_SplitPoOrder_t_
{
    int iPo;
    int nAnds;
};
void Acb_NtkSortSplitOutputsLimit( Gia_Man_t * p, Acb_SplitPoOrder_t * pOrder, int nPos );
void Acb_NtkSortSplitOutputs( Gia_Man_t * p, Acb_SplitPoOrder_t * pOrder );
int * Acb_NtkSolveCadicalPoSweepLabel( Gia_Man_t * p, int fVerbose, int * pStatus, int nSatTimeLimit, int nPoConfLimit, char * pLabel, int fStopOnUndec );
int Acb_GiaMarkCone_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vMarks, int Mark )
{
    int Id;
    if ( Gia_ObjIsConst0(pObj) || Gia_ObjIsCi(pObj) )
        return 0;
    assert( Gia_ObjIsAnd(pObj) );
    Id = Gia_ObjId( p, pObj );
    if ( Vec_IntEntry(vMarks, Id) == Mark )
        return 0;
    Vec_IntWriteEntry( vMarks, Id, Mark );
    return 1 + Acb_GiaMarkCone_rec( p, Gia_ObjFanin0(pObj), vMarks, Mark ) +
        Acb_GiaMarkCone_rec( p, Gia_ObjFanin1(pObj), vMarks, Mark );
}
int Acb_GiaCountConeOverlap_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vMarks, int Mark )
{
    int Id;
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 0;
    Gia_ObjSetTravIdCurrent( p, pObj );
    if ( Gia_ObjIsConst0(pObj) || Gia_ObjIsCi(pObj) )
        return 0;
    assert( Gia_ObjIsAnd(pObj) );
    Id = Gia_ObjId( p, pObj );
    return (int)(Vec_IntEntry(vMarks, Id) == Mark) +
        Acb_GiaCountConeOverlap_rec( p, Gia_ObjFanin0(pObj), vMarks, Mark ) +
        Acb_GiaCountConeOverlap_rec( p, Gia_ObjFanin1(pObj), vMarks, Mark );
}
void Acb_GiaCollectFrontier_rec( Gia_Man_t * p, Gia_Obj_t * pObj, int LevelCut, Vec_Int_t * vFrontier )
{
    if ( Gia_ObjIsConst0(pObj) || Gia_ObjIsCi(pObj) )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent( p, pObj );
    if ( Gia_ObjLevel(p, pObj) <= LevelCut )
    {
        Vec_IntPush( vFrontier, Gia_ObjId(p, pObj) );
        return;
    }
    Acb_GiaCollectFrontier_rec( p, Gia_ObjFanin0(pObj), LevelCut, vFrontier );
    Acb_GiaCollectFrontier_rec( p, Gia_ObjFanin1(pObj), LevelCut, vFrontier );
}
Vec_Int_t * Acb_GiaCollectPoFrontier( Gia_Man_t * p, int iPo, int * pLevelRoot, int * pLevelCut )
{
    Gia_Obj_t * pRoot = Gia_ObjFanin0( Gia_ManCo(p, iPo) );
    Vec_Int_t * vFrontier = Vec_IntAlloc( 64 );
    int LevelRoot = 0, LevelCut = 0;
    Gia_ManLevelNum( p );
    if ( !Gia_ObjIsConst0(pRoot) && !Gia_ObjIsCi(pRoot) )
    {
        LevelRoot = Gia_ObjLevel( p, pRoot );
        LevelCut  = Abc_MaxInt( 1, LevelRoot / 2 );
        Gia_ManIncrementTravId( p );
        Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
        Acb_GiaCollectFrontier_rec( p, pRoot, LevelCut, vFrontier );
    }
    if ( pLevelRoot )
        *pLevelRoot = LevelRoot;
    if ( pLevelCut )
        *pLevelCut = LevelCut;
    return vFrontier;
}
void Acb_GiaPrintHardPoFrontier( Gia_Man_t * p, int iPo, int fVerbose )
{
    Vec_Int_t * vFrontier;
    int i, iObj, LevelRoot, LevelCut, nFront, nPrint;
    if ( !fVerbose )
        return;
    vFrontier = Acb_GiaCollectPoFrontier( p, iPo, &LevelRoot, &LevelCut );
    nFront = Vec_IntSize( vFrontier );
    printf( "    frontier: root level = %d, cut level = %d, candidates = %d",
        LevelRoot, LevelCut, nFront );
    nPrint = Abc_MinInt( nFront, 8 );
    if ( nPrint )
    {
        printf( ", sample obj/level/cone =" );
        for ( i = 0; i < nPrint; i++ )
        {
            iObj = Vec_IntEntry( vFrontier, i );
            printf( " %d/%d/%d", iObj, Gia_ObjLevelId(p, iObj), Gia_ManConeSize(p, &iObj, 1) );
        }
    }
    printf( ".\n" );
    Vec_IntFree( vFrontier );
}
int Acb_GiaDupPoFrontier_rec( Gia_Man_t * p, Gia_Man_t * pNew, Gia_Obj_t * pObj, Vec_Int_t * vFrontMarks, int * pNFrontPis )
{
    int Id, Lit0, Lit1;
    if ( Gia_ObjIsConst0(pObj) )
        return 0;
    if ( ~pObj->Value )
        return pObj->Value;
    Id = Gia_ObjId( p, pObj );
    if ( Gia_ObjIsCi(pObj) || Vec_IntEntry(vFrontMarks, Id) )
    {
        (*pNFrontPis)++;
        return pObj->Value = Gia_ManAppendCi( pNew );
    }
    assert( Gia_ObjIsAnd(pObj) );
    Lit0 = Acb_GiaDupPoFrontier_rec( p, pNew, Gia_ObjFanin0(pObj), vFrontMarks, pNFrontPis );
    Lit1 = Acb_GiaDupPoFrontier_rec( p, pNew, Gia_ObjFanin1(pObj), vFrontMarks, pNFrontPis );
    return pObj->Value = Gia_ManHashAnd( pNew, Abc_LitNotCond(Lit0, Gia_ObjFaninC0(pObj)), Abc_LitNotCond(Lit1, Gia_ObjFaninC1(pObj)) );
}
Gia_Man_t * Acb_GiaDerivePoFrontierAbstract( Gia_Man_t * p, int iPo, int LevelCut, int * pNFrontier, int * pNFrontPis )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pRoot = Gia_ObjFanin0( Gia_ManCo(p, iPo) );
    Vec_Int_t * vFrontier, * vMarks;
    int i, iObj, Lit, LevelRoot = 0, nFrontPis = 0;
    assert( iPo >= 0 && iPo < Gia_ManCoNum(p) );
    Gia_ManLevelNum( p );
    if ( !Gia_ObjIsConst0(pRoot) && !Gia_ObjIsCi(pRoot) )
        LevelRoot = Gia_ObjLevel( p, pRoot );
    if ( LevelCut <= 0 || LevelCut >= LevelRoot )
        LevelCut = Abc_MaxInt( 1, LevelRoot / 2 );
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    vFrontier = Vec_IntAlloc( 64 );
    Acb_GiaCollectFrontier_rec( p, pRoot, LevelCut, vFrontier );
    vMarks = Vec_IntStart( Gia_ManObjNum(p) );
    Vec_IntForEachEntry( vFrontier, iObj, i )
        Vec_IntWriteEntry( vMarks, iObj, 1 );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    pNew = Gia_ManStart( Abc_MaxInt( 1000, 2 * Vec_IntSize(vFrontier) + 100 ) );
    pNew->pName = Abc_UtilStrsav( "frontier_abs" );
    Gia_ManHashStart( pNew );
    Lit = Acb_GiaDupPoFrontier_rec( p, pNew, pRoot, vMarks, &nFrontPis );
    Lit = Abc_LitNotCond( Lit, Gia_ObjFaninC0(Gia_ManCo(p, iPo)) );
    Gia_ManAppendCo( pNew, Lit );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    if ( pNFrontier )
        *pNFrontier = Vec_IntSize( vFrontier );
    if ( pNFrontPis )
        *pNFrontPis = nFrontPis;
    Vec_IntFree( vMarks );
    Vec_IntFree( vFrontier );
    return pNew;
}
int Acb_NtkTryFrontierAbstractPo( Gia_Man_t * p, int iPo, int fVerbose, int nSatTimeLimit, int iSelId, int fUseOneBranch, char * pLabel )
{
    Gia_Obj_t * pRoot = Gia_ObjFanin0( Gia_ManCo(p, iPo) );
    int Cuts[3], c, Status = -1, nFrontier = 0, nFrontPis = 0;
    int LevelRoot = 0, nAndBest = -1;
    abctime clk = Abc_Clock();
    if ( nSatTimeLimit <= 0 )
        return -1;
    Gia_ManLevelNum( p );
    if ( Gia_ObjIsConst0(pRoot) )
        return Gia_ObjFaninC0(Gia_ManCo(p, iPo)) ? -1 : 1;
    if ( Gia_ObjIsCi(pRoot) )
        return -1;
    LevelRoot = Gia_ObjLevel( p, pRoot );
    Cuts[0] = Abc_MaxInt( 1, LevelRoot / 2 );
    Cuts[1] = Abc_MaxInt( 1, (2 * LevelRoot) / 3 );
    Cuts[2] = Abc_MaxInt( 1, LevelRoot / 3 );
    for ( c = 0; c < 3; c++ )
    {
        Gia_Man_t * pAbs, * pOpt = NULL, * pSolve;
        int nLimit = Abc_MinInt( nSatTimeLimit, c == 0 ? 30 : 15 );
        if ( c && Cuts[c] == Cuts[c-1] )
            continue;
        pAbs = Acb_GiaDerivePoFrontierAbstract( p, iPo, Cuts[c], &nFrontier, &nFrontPis );
        nAndBest = Gia_ManAndNum( pAbs );
        pOpt = nAndBest > 100 ? Gia_ManCompress2( pAbs, 1, 0 ) : NULL;
        pSolve = pOpt ? pOpt : pAbs;
        if ( fVerbose )
            printf( "%s frontier abstraction: selector %d branch %d output %d. level %d/%d, frontier = %d, abs PIs = %d, And = %d -> %d, limit = %d sec.\n",
                pLabel, iSelId, fUseOneBranch, iPo, Cuts[c], LevelRoot, nFrontier, nFrontPis, nAndBest, Gia_ManAndNum(pSolve), nLimit );
        if ( Gia_ManAndNum(pSolve) == 0 )
        {
            Gia_Obj_t * pCo = Gia_ManCo( pSolve, 0 );
            if ( Gia_ObjIsConst0(Gia_ObjFanin0(pCo)) && !Gia_ObjFaninC0(pCo) )
                Status = 1;
        }
        if ( Status != 1 )
        {
            int StatusSat = -1;
            int * pModel = Acb_NtkSolveCadicalLimit( pSolve, 0, 0, &StatusSat, nLimit, NULL, 0 );
            if ( pModel )
                ABC_FREE( pModel );
            Status = StatusSat == 1 ? 1 : -1;
        }
        if ( fVerbose )
        {
            printf( "%s frontier abstraction: output %d %s.  ",
                pLabel, iPo, Status == 1 ? "UNSAT" : "inconclusive" );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        }
        if ( pOpt )
            Gia_ManStop( pOpt );
        Gia_ManStop( pAbs );
        if ( Status == 1 )
            return 1;
    }
    return -1;
}
int Acb_GiaSolveSmallConeInternalFrontier( Gia_Man_t * p, int fVerbose, int nSatTimeLimit )
{
    Gia_Obj_t * pRoot;
    int Cuts[8], nCuts = 0, c, LevelRoot, Status = ACB_XEC_UNDEC;
    abctime clk = Abc_Clock();
    abctime clkLimit = nSatTimeLimit > 0 ? clk + nSatTimeLimit * CLOCKS_PER_SEC : 0;
    if ( p == NULL || Gia_ManCoNum(p) != 1 || Gia_ManAndNum(p) <= 0 || Gia_ManAndNum(p) > 5000 || nSatTimeLimit < 10 )
        return ACB_XEC_UNDEC;
    pRoot = Gia_ObjFanin0( Gia_ManCo(p, 0) );
    if ( Gia_ObjIsConst0(pRoot) || Gia_ObjIsCi(pRoot) )
        return ACB_XEC_UNDEC;
    Gia_ManLevelNum( p );
    LevelRoot = Gia_ObjLevel( p, pRoot );
    if ( LevelRoot < 8 )
        return ACB_XEC_UNDEC;
#define ACB_ADD_FRONTIER_CUT(cut_) do {                                            \
        int Cut_ = (cut_);                                                         \
        int t_;                                                                    \
        if ( Cut_ > 0 && Cut_ < LevelRoot )                                        \
        {                                                                          \
            for ( t_ = 0; t_ < nCuts; t_++ )                                       \
                if ( Cuts[t_] == Cut_ )                                            \
                    break;                                                         \
            if ( t_ == nCuts && nCuts < (int)(sizeof(Cuts)/sizeof(Cuts[0])) )      \
                Cuts[nCuts++] = Cut_;                                              \
        }                                                                          \
    } while (0)
    ACB_ADD_FRONTIER_CUT( LevelRoot / 4 );
    ACB_ADD_FRONTIER_CUT( LevelRoot / 3 );
    ACB_ADD_FRONTIER_CUT( LevelRoot / 2 );
    ACB_ADD_FRONTIER_CUT( (2 * LevelRoot) / 3 );
    ACB_ADD_FRONTIER_CUT( (3 * LevelRoot) / 4 );
    ACB_ADD_FRONTIER_CUT( Abc_MaxInt(1, LevelRoot - 32) );
    ACB_ADD_FRONTIER_CUT( Abc_MaxInt(1, LevelRoot - 16) );
#undef ACB_ADD_FRONTIER_CUT
    if ( fVerbose )
        printf( "Trying small-cone internal frontier proof: CI = %d. AND = %d. levels = %d. cuts = %d. limit = %d sec.\n",
            Gia_ManCiNum(p), Gia_ManAndNum(p), LevelRoot, nCuts, nSatTimeLimit );
    for ( c = 0; c < nCuts; c++ )
    {
        Gia_Man_t * pAbs = NULL, * pTemp = NULL, * pSolve = NULL;
        int nFront = 0, nFrontPis = 0, nRemain, nThisLimit, StatusOne = ACB_XEC_UNDEC;
        int * pModel = NULL;
        if ( clkLimit )
        {
            nRemain = (int)((clkLimit - Abc_Clock()) / CLOCKS_PER_SEC);
            if ( nRemain < 5 )
                break;
        }
        else
            nRemain = nSatTimeLimit;
        nThisLimit = Abc_MinInt( nRemain, c < 3 ? 45 : 30 );
        pAbs = Acb_GiaDerivePoFrontierAbstract( p, 0, Cuts[c], &nFront, &nFrontPis );
        if ( pAbs == NULL )
            continue;
        if ( Gia_ManPoIsConst0(pAbs, 0) )
        {
            Status = ACB_XEC_EQ;
            Gia_ManStop( pAbs );
            break;
        }
        if ( Gia_ManAndNum(pAbs) > 200 )
        {
            pTemp = Gia_ManCompress2( pAbs, 1, 0 );
            if ( pTemp )
            {
                Gia_ManStop( pAbs );
                pAbs = pTemp;
                pTemp = NULL;
            }
        }
        if ( Gia_ManAndNum(pAbs) > 1000 && nThisLimit >= 20 )
        {
            pTemp = Acb_NtkFraigEquivReduce( pAbs, 0, "Small-cone internal frontier", "abstraction", 32, 300, 20000, 1 );
            if ( pTemp )
            {
                Gia_ManStop( pAbs );
                pAbs = pTemp;
                pTemp = NULL;
            }
        }
        pSolve = pAbs;
        if ( fVerbose )
            printf( "Small-cone internal frontier proof: cut = %d/%d. frontier = %d. abs PIs = %d. And = %d. limit = %d sec.\n",
                Cuts[c], LevelRoot, nFront, nFrontPis, Gia_ManAndNum(pSolve), nThisLimit );
        pModel = Acb_NtkSolveCadicalLimit( pSolve, 0, 0, &StatusOne, nThisLimit, NULL, 0 );
        ABC_FREE( pModel );
        if ( StatusOne == ACB_XEC_EQ )
        {
            Status = ACB_XEC_EQ;
            Gia_ManStop( pAbs );
            break;
        }
        Gia_ManStop( pAbs );
    }
    if ( fVerbose )
    {
        printf( "Small-cone internal frontier proof: %s.  ", Status == ACB_XEC_EQ ? "UNSAT" : "UNDECIDED" );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    return Status;
}
int * Acb_NtkSolveCadicalLocalOptPo( Gia_Man_t * p, int iPo, int fVerbose, int * pStatus, int nSatTimeLimit, int iSelId, int fUseOneBranch, char * pLabel )
{
    Gia_Man_t * pOne, * pOpt = NULL, * pSyn = NULL, * pTemp, * pBase, * pSolve;
    int Status = -1;
    int fSkipped = 0;
    int * pModel;
    int nAndBefore, nAndAfter;
    abctime clk = Abc_Clock();
    assert( iPo >= 0 && iPo < Gia_ManCoNum(p) );
    if ( nSatTimeLimit <= 0 )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_UNDEC;
        return NULL;
    }
    pOne = Gia_ManDupCones( p, &iPo, 1, 0 );
    nAndBefore = Gia_ManAndNum( pOne );
    if ( fVerbose )
        printf( "%s local optimized cone: selector %d branch %d output %d. And = %d. limit = %d sec.\n",
            pLabel, iSelId, fUseOneBranch, iPo, nAndBefore, nSatTimeLimit );
    pOpt = Gia_ManCompress2( pOne, 1, fVerbose );
    pBase = pOpt ? pOpt : pOne;
    pSyn = Gia_ManAigSyn2( pBase, 0, 1, 0, 100, 0, 0, 0 );
    if ( pSyn )
    {
        pTemp = Gia_ManCompress2( pSyn, 1, 0 );
        if ( pTemp )
        {
            Gia_ManStop( pSyn );
            pSyn = pTemp;
        }
    }
    pSolve = pSyn ? pSyn : pBase;
    nAndAfter = Gia_ManAndNum( pSolve );
    if ( fVerbose )
        printf( "%s local optimized cone: optimized And = %d -> %d.\n", pLabel, nAndBefore, nAndAfter );
    if ( 10 * nAndAfter > 9 * nAndBefore )
    {
        if ( fVerbose )
            printf( "%s local optimized cone: output %d skipped because reduction is below 10%%.  ", pLabel, iPo );
        if ( pStatus )
            *pStatus = ACB_XEC_UNDEC;
        fSkipped = 1;
        pModel = NULL;
        goto cleanup;
    }
    pModel = Acb_NtkSolveCadicalLimit( pSolve, 0, fVerbose, &Status, nSatTimeLimit, NULL, 0 );
cleanup:
    if ( pSyn )
        Gia_ManStop( pSyn );
    if ( pOpt )
        Gia_ManStop( pOpt );
    Gia_ManStop( pOne );
    if ( pStatus )
        *pStatus = Status;
    if ( fVerbose )
    {
        printf( "%s local optimized cone: output %d %s.  ",
            pLabel, iPo, fSkipped ? "SKIPPED" : (Status == 0 ? "SAT" : (Status == 1 ? "UNSAT" : "UNDECIDED")) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    return pModel;
}
Vec_Int_t * Acb_GiaCollectPoConeAnds( Gia_Man_t * p, int iPo )
{
    Vec_Int_t * vCone = Vec_IntAlloc( 1000 );
    int iObj = Gia_ObjId( p, Gia_ManCo(p, iPo) );
    Gia_ManIncrementTravId( p );
    Gia_ManCollectAnds( p, &iObj, 1, vCone, NULL );
    return vCone;
}
int Acb_GiaConeOverlapPermille( Vec_Int_t * vCone0, Vec_Int_t * vCone1, Vec_Int_t * vMarks )
{
    Vec_Int_t * vSmall = Vec_IntSize(vCone0) <= Vec_IntSize(vCone1) ? vCone0 : vCone1;
    Vec_Int_t * vLarge = Vec_IntSize(vCone0) <= Vec_IntSize(vCone1) ? vCone1 : vCone0;
    int i, iObj, nInter = 0;
    if ( Vec_IntSize(vSmall) == 0 )
        return Vec_IntSize(vLarge) == 0 ? 1000 : 0;
    Vec_IntForEachEntry( vSmall, iObj, i )
        Vec_IntWriteEntry( vMarks, iObj, 1 );
    Vec_IntForEachEntry( vLarge, iObj, i )
        nInter += Vec_IntEntry( vMarks, iObj );
    Vec_IntForEachEntry( vSmall, iObj, i )
        Vec_IntWriteEntry( vMarks, iObj, 0 );
    return 1000 * nInter / Vec_IntSize(vSmall);
}
int Acb_GiaBuildOverlapSchedule( Gia_Man_t * p, Acb_SplitPoOrder_t * pOrder, int nMiterOuts, int * pSched, int * pGroupStart, int fVerbose, char * pLabel, Acb_XecCtx_t * pCtx )
{
    Vec_Int_t ** ppCones = ABC_CALLOC( Vec_Int_t *, nMiterOuts );
    Vec_Int_t * vMarks = Vec_IntStart( Gia_ManObjNum(p) );
    Vec_Int_t * vCluster = Vec_IntAlloc( nMiterOuts );
    unsigned char * pUsed = ABC_CALLOC( unsigned char, nMiterOuts );
    int i, k, s, l, r, iPo, iSeedPo, nSched = 0, nGroups = 0;
    for ( i = 0; i < nMiterOuts; i++ )
    {
        ppCones[i] = Acb_GiaCollectPoConeAnds( p, i );
        pGroupStart[i] = 0;
    }
    for ( s = 0; s < nMiterOuts; s++ )
    {
        int nSeedSize, nAdded = 0;
        if ( pUsed[s] )
            continue;
        Vec_IntClear( vCluster );
        pGroupStart[nSched] = 1;
        Vec_IntPush( vCluster, s );
        pUsed[s] = 1;
        nGroups++;
        iSeedPo = pOrder[s].iPo;
        nSeedSize = Vec_IntSize( ppCones[iSeedPo] );
        for ( k = s + 1; k < nMiterOuts; k++ )
        {
            int nSize, nMin, nMax, nOverlap;
            if ( pUsed[k] )
                continue;
            iPo = pOrder[k].iPo;
            nSize = Vec_IntSize( ppCones[iPo] );
            nMin = Abc_MinInt( nSeedSize, nSize );
            nMax = Abc_MaxInt( nSeedSize, nSize );
            if ( nMax == 0 || 1000 * nMin < pCtx->Pars.nOverlapSizePermille * nMax )
                continue;
            nOverlap = Acb_GiaConeOverlapPermille( ppCones[iSeedPo], ppCones[iPo], vMarks );
            if ( nOverlap < pCtx->Pars.nOverlapMinPermille )
                continue;
            Vec_IntPush( vCluster, k );
            pUsed[k] = 1;
            nAdded++;
        }
        for ( l = 0, r = Vec_IntSize(vCluster) - 1; l <= r; l++, r-- )
        {
            if ( nGroups == 1 )
            {
                pSched[nSched++] = Vec_IntEntry( vCluster, l );
                if ( l < r )
                    pSched[nSched++] = Vec_IntEntry( vCluster, r );
            }
            else
            {
                pSched[nSched++] = Vec_IntEntry( vCluster, r );
                if ( l < r )
                    pSched[nSched++] = Vec_IntEntry( vCluster, l );
            }
        }
        if ( fVerbose && nAdded )
            printf( "%s support-overlap cluster %d: seed output %d, members = %d.\n",
                pLabel, nGroups - 1, iSeedPo, nAdded + 1 );
    }
    if ( fVerbose )
        printf( "%s support-overlap clustering: outputs = %d. clusters = %d. overlap >= %d.%d%%, size ratio >= %d.%d%%.\n",
            pLabel, nMiterOuts, nGroups,
            pCtx->Pars.nOverlapMinPermille / 10, pCtx->Pars.nOverlapMinPermille % 10,
            pCtx->Pars.nOverlapSizePermille / 10, pCtx->Pars.nOverlapSizePermille % 10 );
    for ( i = 0; i < nMiterOuts; i++ )
        Vec_IntFree( ppCones[i] );
    ABC_FREE( ppCones );
    ABC_FREE( pUsed );
    Vec_IntFree( vCluster );
    Vec_IntFree( vMarks );
    return nGroups;
}
int * Acb_NtkSolveCadicalSelectorBranch( Gia_Man_t * p, int nMiterOuts, int fUseOneBranch, int fVerbose, int * pStatus, int nSatTimeLimit, int iSelId, int fStopOnUndec, char * pLabel, Acb_XecCtx_t * pCtx )
{
    int * pModel = NULL;
    int * pPoStatus = NULL, * pPoCone = NULL, * pPoConf = NULL, * pPoLearn = NULL, * pPoTime = NULL, * pPoSlot = NULL;
    int * pPoConfTotal = NULL, * pPoLearnTotal = NULL;
    Acb_SplitPoOrder_t * pOrder = NULL;
    Gia_Man_t * pCond = NULL, * pOpt = NULL, * pSweep = NULL, * pCnfGia = NULL;
    Aig_Man_t * pMan = NULL;
    Cnf_Dat_t * pCnf = NULL;
    cadical_solver * pSat = NULL;
    int Lit, Status = 0, i, nUnsat = 0, nUndec = 0;
    int nGroups = 0, nIsolations = 0;
    int * pSched = NULL, * pGroupStart = NULL, nSched = 0;
    int nConflicts = 0, nLearned = 0;
    int nMinOutTime = nSatTimeLimit > 0 ? Abc_MinInt( pCtx->Pars.nBranchMinOutputSec, Abc_MaxInt( 1, nSatTimeLimit / 10 ) ) : pCtx->Pars.nBranchMinOutputSec;
    int nAndCond;
    abctime clk = Abc_Clock();
    abctime clkLimit = nSatTimeLimit > 0 ? clk + nSatTimeLimit * CLOCKS_PER_SEC : 0;
    assert( nMiterOuts > 0 );
    assert( pCtx != NULL );
    Acb_XecCtxResetBranchSweep( pCtx, nMiterOuts );
    assert( Gia_ManCoNum(p) == nMiterOuts + 2 );
    pCond = Acb_GiaDeriveBranchConditionMiter( p, nMiterOuts, fUseOneBranch );
    nAndCond = Gia_ManAndNum( pCond );
    pOpt = nAndCond > 1000 ? Gia_ManCompress2( pCond, 1, 0 ) : NULL;
    pCnfGia = pOpt ? pOpt : pCond;
    pSweep = Acb_NtkBranchSweepReduce( pCnfGia, fVerbose, pLabel );
    if ( pSweep )
        pCnfGia = pSweep;
    pMan = Gia_ManToAig( pCnfGia, 0 );
    pCnf = pMan ? Cnf_Derive( pMan, Aig_ManCoNum(pMan) ) : NULL;
    if ( pCnf == NULL )
    {
        Status = 0;
        nUndec++;
        goto cleanup;
    }
    if ( fVerbose )
        printf( "%s conditioned grouped CaDiCaL sweep: selector %d branch %d. outputs = %d. And = %d -> %d. CNF var = %d. cla = %d.\n",
            pLabel, iSelId, fUseOneBranch, nMiterOuts, nAndCond, Gia_ManAndNum(pCnfGia), pCnf->nVars, pCnf->nClauses );
    pOrder = ABC_ALLOC( Acb_SplitPoOrder_t, nMiterOuts );
    Acb_NtkSortSplitOutputsLimit( pCnfGia, pOrder, nMiterOuts );
    pPoStatus = ABC_ALLOC( int, nMiterOuts );
    pPoCone   = ABC_ALLOC( int, nMiterOuts );
    pPoConf   = ABC_ALLOC( int, nMiterOuts );
    pPoLearn  = ABC_ALLOC( int, nMiterOuts );
    pPoTime   = ABC_ALLOC( int, nMiterOuts );
    pPoSlot   = ABC_ALLOC( int, nMiterOuts );
    pPoConfTotal  = ABC_ALLOC( int, nMiterOuts );
    pPoLearnTotal = ABC_ALLOC( int, nMiterOuts );
    for ( i = 0; i < nMiterOuts; i++ )
    {
        pPoStatus[i] = 2;
        pPoCone[i]   = 0;
        pPoConf[i]   = 0;
        pPoLearn[i]  = 0;
        pPoTime[i]   = 0;
        pPoSlot[i]   = 0;
        pPoConfTotal[i]  = 0;
        pPoLearnTotal[i] = 0;
    }
    for ( i = 0; i < nMiterOuts; i++ )
    {
        pPoCone[pOrder[i].iPo] = pOrder[i].nAnds;
        pPoSlot[pOrder[i].iPo] = i + 1;
    }
    if ( fVerbose )
        printf( "%s output order: smallest cone %d ANDs, largest cone %d ANDs.\n",
            pLabel, pOrder[0].nAnds, pOrder[nMiterOuts-1].nAnds );
    pSched = ABC_ALLOC( int, nMiterOuts );
    pGroupStart = ABC_ALLOC( int, nMiterOuts );
    nGroups = Acb_GiaBuildOverlapSchedule( pCnfGia, pOrder, nMiterOuts, pSched, pGroupStart, fVerbose, pLabel, pCtx );
    nSched = nMiterOuts;
    if ( fVerbose )
    {
        int nPrint = Abc_MinInt( nSched, pCtx->Pars.nBranchSchedulePrintMax );
        printf( "%s support-overlap schedule: selector %d branch %d outputs = %d. order =", pLabel, iSelId, fUseOneBranch, nSched );
        for ( i = 0; i < nPrint; i++ )
        {
            if ( pGroupStart[i] )
                printf( " |" );
            printf( " %d", pOrder[pSched[i]].iPo );
        }
        if ( nPrint < nSched )
            printf( " ..." );
        printf( ".\n" );
    }
    for ( i = 0; i < nSched; i++ )
    {
        abctime clkOut = Abc_Clock();
        int iPos = pSched[i];
        int iPo = pOrder[iPos].iPo;
        int nConflictsBeg, nLearnedBeg;
        int fTryLocalOpt = iPos >= nMiterOuts/2 && iPos <= nMiterOuts - 4 && pOrder[iPos].nAnds >= pCtx->Pars.nBranchLocalOptAndMin;
        if ( pGroupStart[i] || pSat == NULL )
        {
            if ( pSat )
                cadical_solver_delete( pSat );
            pSat = cadical_solver_new();
            if ( pSat == NULL || !Acb_CnfWriteIntoCadical( pSat, pCnf ) )
            {
                Status = 0;
                nUndec++;
                break;
            }
            if ( fVerbose )
                printf( "%s grouped CaDiCaL: starting overlap cluster at output %d.\n",
                    pLabel, iPo );
        }
        nConflictsBeg = cadical_solver_nconflicts(pSat);
        nLearnedBeg   = cadical_solver_nlearned(pSat);
        if ( clkLimit && Abc_Clock() >= clkLimit )
        {
            Status = 0;
            nUndec++;
            break;
        }
        if ( clkLimit && clkLimit - Abc_Clock() < nMinOutTime * CLOCKS_PER_SEC )
        {
            Status = 0;
            nUndec++;
            if ( fVerbose )
                printf( "%s grouped CaDiCaL: skipping output %d because remaining branch budget is below %d sec.\n",
                    pLabel, iPo, nMinOutTime );
            break;
        }
        if ( fTryLocalOpt && clkLimit )
        {
            int StatusLocal = -1;
            int nRemain = (int)((clkLimit - Abc_Clock()) / CLOCKS_PER_SEC);
            int nLocalLimit = Abc_MinInt( pCtx->Pars.nBranchLocalOptSec, nRemain - nMinOutTime );
            int nAbsLimit = Abc_MinInt( pCtx->Pars.nBranchFrontierAbsSec, nRemain - nMinOutTime );
            if ( nAbsLimit >= 15 && Acb_NtkTryFrontierAbstractPo( pCnfGia, iPo, fVerbose, nAbsLimit, iSelId, fUseOneBranch, pLabel ) == 1 )
            {
                pPoStatus[iPo] = -1;
                pPoConf[iPo]   = 0;
                pPoLearn[iPo]  = 0;
                pPoConfTotal[iPo]  = nConflictsBeg;
                pPoLearnTotal[iPo] = nLearnedBeg;
                pPoTime[iPo]   = (int)((Abc_Clock() - clkOut + CLOCKS_PER_SEC/2) / CLOCKS_PER_SEC);
                Status = -1;
                nUnsat++;
                if ( fVerbose )
                    printf( "%s grouped CaDiCaL: output %d UNSAT by frontier abstraction; skipping grouped assumption.\n", pLabel, iPo );
                continue;
            }
            if ( nLocalLimit >= nMinOutTime )
            {
                int * pLocalModel = Acb_NtkSolveCadicalLocalOptPo( pCnfGia, iPo, fVerbose, &StatusLocal, nLocalLimit, iSelId, fUseOneBranch, pLabel );
                pPoStatus[iPo] = StatusLocal == 0 ? 1 : (StatusLocal == 1 ? -1 : 0);
                pPoConf[iPo]   = 0;
                pPoLearn[iPo]  = 0;
                pPoConfTotal[iPo]  = nConflictsBeg;
                pPoLearnTotal[iPo] = nLearnedBeg;
                pPoTime[iPo]   = (int)((Abc_Clock() - clkOut + CLOCKS_PER_SEC/2) / CLOCKS_PER_SEC);
                if ( StatusLocal == 0 )
                {
                    pModel = pLocalModel;
                    Status = 1;
                    break;
                }
                if ( pLocalModel )
                    ABC_FREE( pLocalModel );
                if ( StatusLocal == 1 )
                {
                    Status = -1;
                    nUnsat++;
                    if ( fVerbose )
                        printf( "%s grouped CaDiCaL: output %d UNSAT by local optimized cone; skipping grouped assumption.\n", pLabel, iPo );
                    continue;
                }
            }
        }
        {
            int RetLit = Acb_CnfCoDriverLit( pCnf, iPo, &Lit );
            if ( RetLit == -2 )
            {
                Status = 0;
                nUndec++;
                pPoStatus[iPo] = Status;
                pPoConf[iPo]   = 0;
                pPoLearn[iPo]  = 0;
                pPoConfTotal[iPo]  = cadical_solver_nconflicts(pSat);
                pPoLearnTotal[iPo] = cadical_solver_nlearned(pSat);
                pPoTime[iPo]   = (int)((Abc_Clock() - clkOut + CLOCKS_PER_SEC/2) / CLOCKS_PER_SEC);
                if ( fVerbose )
                    printf( "%s grouped CaDiCaL: output %d UNDECIDED because its CNF driver is unmapped.\n", pLabel, iPo );
                break;
            }
            if ( RetLit == -1 )
            {
                Status = -1;
                nUnsat++;
                pPoStatus[iPo] = Status;
                pPoConf[iPo]   = 0;
                pPoLearn[iPo]  = 0;
                pPoConfTotal[iPo]  = cadical_solver_nconflicts(pSat);
                pPoLearnTotal[iPo] = cadical_solver_nlearned(pSat);
                pPoTime[iPo]   = (int)((Abc_Clock() - clkOut + CLOCKS_PER_SEC/2) / CLOCKS_PER_SEC);
                if ( fVerbose )
                    printf( "%s grouped CaDiCaL: output %d UNSAT because it is constant 0.\n", pLabel, iPo );
                continue;
            }
            if ( RetLit == 0 )
            {
                Status = 1;
                Lit = -1;
            }
        }
        if ( fVerbose )
            printf( "%s grouped CaDiCaL: selector %d branch %d output %d (%d/%d), cone = %d ANDs.\n",
                pLabel, iSelId, fUseOneBranch, iPo, iPos + 1, nMiterOuts, pOrder[iPos].nAnds );
        if ( Status != 1 )
            Status = cadical_solver_solve( pSat, &Lit, &Lit + 1, 0, 0, 0, 0 );
        nConflicts = cadical_solver_nconflicts(pSat);
        nLearned   = cadical_solver_nlearned(pSat);
        pPoStatus[iPo] = Status;
        pPoConf[iPo]   = nConflicts - nConflictsBeg;
        pPoLearn[iPo]  = nLearned - nLearnedBeg;
        pPoConfTotal[iPo]  = nConflicts;
        pPoLearnTotal[iPo] = nLearned;
        pPoTime[iPo]   = (int)((Abc_Clock() - clkOut + CLOCKS_PER_SEC/2) / CLOCKS_PER_SEC);
        if ( Status == 1 )
        {
            Aig_Obj_t * pObj;
            pModel = ABC_ALLOC( int, Aig_ManCiNum(pMan) );
            Aig_ManForEachCi( pMan, pObj, iPo )
                pModel[iPo] = cadical_solver_get_var_value( pSat, pCnf->pVarNums[pObj->Id] );
            break;
        }
        if ( Status == -1 )
        {
            nUnsat++;
            if ( fVerbose )
            {
                printf( "%s grouped CaDiCaL: output %d UNSAT. delta conflicts = %d. delta learned = %d. total conflicts = %d. total learned = %d.  ",
                    pLabel, iPo, pPoConf[iPo], pPoLearn[iPo], nConflicts, nLearned );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clkOut );
            }
        }
        else
        {
            nUndec++;
            if ( fVerbose )
            {
                printf( "%s grouped CaDiCaL: output %d UNDECIDED. delta conflicts = %d. delta learned = %d. total conflicts = %d. total learned = %d.  ",
                    pLabel, iPo, pPoConf[iPo], pPoLearn[iPo], nConflicts, nLearned );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clkOut );
            }
            if ( fStopOnUndec )
                break;
        }
        if ( Status != -1 || pPoConf[iPo] >= pCtx->Pars.nBranchHardConflictMin || pPoTime[iPo] >= pCtx->Pars.nBranchHardTimeMin )
        {
            if ( Status == -1 )
                nIsolations++;
            if ( fVerbose && Status == -1 )
                printf( "%s hard-output isolation: resetting solver after output %d. delta conflicts = %d, time = %d sec.\n",
                    pLabel, iPo, pPoConf[iPo], pPoTime[iPo] );
            cadical_solver_delete( pSat );
            pSat = NULL;
        }
    }
    if ( pStatus )
        *pStatus = Status == 1 ? 0 : (nUndec ? -1 : 1);
    printf( "The selector %d branch %d is %s by %s CaDiCaL.  ",
        iSelId, fUseOneBranch, Status == 1 ? "SAT" : (nUndec ? "UNDECIDED" : "UNSAT"), pLabel );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    for ( i = 0; i < nMiterOuts; i++ )
        if ( pPoStatus && (pPoStatus[i] == 2 || pPoStatus[i] != -1 || pPoConf[i] >= pCtx->Pars.nBranchHardConflictMin || pPoTime[i] >= pCtx->Pars.nBranchHardTimeMin) )
            Vec_IntPushUnique( pCtx->vLastBranchHardPos, i );
    if ( fVerbose )
    {
        int nHard = 0;
        printf( "%s grouped CaDiCaL stats: overlap clusters = %d. hard isolations = %d. SAT = %d. UNSAT = %d. UNDEC = %d. last-group conflicts = %d. last-group learned = %d.\n",
            pLabel, nGroups, nIsolations, Status == 1, nUnsat, nUndec, nConflicts, nLearned );
        for ( i = 0; i < nMiterOuts; i++ )
            if ( pPoStatus[i] != 2 && (pPoStatus[i] != -1 || pPoConf[i] >= pCtx->Pars.nBranchHardConflictMin || pPoTime[i] >= pCtx->Pars.nBranchHardTimeMin) )
                nHard++;
        if ( nHard )
        {
            printf( "%s hard-output summary: selector %d branch %d. thresholds: delta conflicts >= %d OR time >= %d sec OR non-UNSAT.\n",
                pLabel, iSelId, fUseOneBranch, pCtx->Pars.nBranchHardConflictMin, pCtx->Pars.nBranchHardTimeMin );
            for ( i = 0; i < nMiterOuts; i++ )
                if ( pPoStatus[i] != 2 && (pPoStatus[i] != -1 || pPoConf[i] >= pCtx->Pars.nBranchHardConflictMin || pPoTime[i] >= pCtx->Pars.nBranchHardTimeMin) )
                {
                    printf( "  output %d: status = %s, sorted slot = %d/%d, cone = %d ANDs, delta conflicts = %d, delta learned = %d, total conflicts = %d, total learned = %d, time = %d sec.\n",
                        i, pPoStatus[i] == 1 ? "SAT" : (pPoStatus[i] == -1 ? "UNSAT" : "UNDECIDED"),
                        pPoSlot[i], nMiterOuts, pPoCone[i], pPoConf[i], pPoLearn[i], pPoConfTotal[i], pPoLearnTotal[i], pPoTime[i] );
                    Acb_GiaPrintHardPoFrontier( pCnfGia, i, fVerbose );
                }
        }
    }
cleanup:
    if ( pPoStatus )
        ABC_FREE( pPoStatus );
    if ( pPoCone )
        ABC_FREE( pPoCone );
    if ( pPoConf )
        ABC_FREE( pPoConf );
    if ( pPoLearn )
        ABC_FREE( pPoLearn );
    if ( pPoTime )
        ABC_FREE( pPoTime );
    if ( pPoSlot )
        ABC_FREE( pPoSlot );
    if ( pPoConfTotal )
        ABC_FREE( pPoConfTotal );
    if ( pPoLearnTotal )
        ABC_FREE( pPoLearnTotal );
    if ( pSched )
        ABC_FREE( pSched );
    if ( pGroupStart )
        ABC_FREE( pGroupStart );
    if ( pOrder )
        ABC_FREE( pOrder );
    if ( pSat )
        cadical_solver_delete( pSat );
    if ( pCnf )
        Cnf_DataFree( pCnf );
    if ( pMan )
        Aig_ManStop( pMan );
    if ( pOpt )
        Gia_ManStop( pOpt );
    if ( pSweep )
        Gia_ManStop( pSweep );
    if ( pCond )
        Gia_ManStop( pCond );
    return pModel;
}
int * Acb_NtkSolveHmuxBranches( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, Vec_Int_t * vCutObjsG, Vec_Int_t * vMuxSelectorsG, Vec_Int_t * vMuxPoSelIdsG, Vec_Int_t * vIntDcObjsG, Vec_Int_t * vIntDcCtrlsG, Vec_Int_t * vIntDcCtrlIdsG, int fVerbose, int * pStatus, Acb_XecCtx_t * pCtx )
{
    int iSel, fOne, Status, fUndec = 0;
    int * pModel = NULL;
    abctime clk = Abc_Clock();
    if ( fVerbose )
        printf( "Trying HMUX branch-level proving: selectors = %d.\n", Vec_IntSize(vMuxSelectorsG) );
    for ( iSel = 0; iSel < Vec_IntSize(vMuxSelectorsG); iSel++ )
    {
        for ( fOne = 0; fOne <= 1; fOne++ )
        {
            Vec_Int_t * vFTargets = Acb_NtkCollectCoDriversForSelector( pNtkF, vMuxPoSelIdsG, iSel );
            Vec_Int_t * vGTargets = Acb_NtkCollectPoMuxBranchTargets( pNtkG, vCutObjsG, vMuxPoSelIdsG, iSel, fOne );
            Gia_Man_t * pGiaFBranch = NULL, * pGiaGBranch = NULL, * pGiaBranch = NULL, * pGiaCond = NULL;
            int fTriedBranchWhole = 0;
            assert( Vec_IntSize(vFTargets) == Vec_IntSize(vGTargets) );
            Vec_IntPush( vGTargets, Vec_IntEntry(vMuxSelectorsG, iSel) );
            pGiaFBranch = Acb_NtkGiaDeriveDualTargets( pNtkF, vFTargets );
            pGiaGBranch = Acb_NtkGiaDeriveDualTargets( pNtkG, vGTargets );
            pGiaBranch  = Acb_NtkGiaDeriveMiterWithSecondExtras( pGiaFBranch, pGiaGBranch, 1 );
            if ( fVerbose )
                printf( "HMUX branch miter: selector %d branch %d. And = %d. PO = %d.\n",
                    iSel, fOne, Gia_ManAndNum(pGiaBranch), Gia_ManPoNum(pGiaBranch) );
            Status = -1;
            if ( Vec_IntSize(vFTargets) >= 16 && Gia_ManAndNum(pGiaBranch) <= 30000 )
            {
                int nWholeLimit = Vec_IntSize(vFTargets) >= 24 ? 60 : 450;
                pGiaCond = Acb_GiaDeriveBranchConditionMiter( pGiaBranch, Vec_IntSize(vFTargets), fOne );
                if ( fVerbose )
                    printf( "HMUX branch whole-miter try: selector %d branch %d. And = %d. PO = %d. limit = %d sec.\n",
                        iSel, fOne, Gia_ManAndNum(pGiaCond), Gia_ManPoNum(pGiaCond), nWholeLimit );
                fTriedBranchWhole = 1;
                pModel = Acb_NtkSolveCadicalLimit( pGiaCond, 0, fVerbose, &Status, nWholeLimit, "HMUX branch whole-miter CaDiCaL", 0 );
                Gia_ManStop( pGiaCond );
                pGiaCond = NULL;
                if ( Status == -1 && fVerbose )
                    printf( "HMUX branch whole-miter CaDiCaL was UNDECIDED; skipping duplicate grouped branch sweep.\n" );
            }
            if ( Status == -1 && !fTriedBranchWhole )
                pModel = Acb_NtkSolveCadicalSelectorBranch( pGiaBranch, Vec_IntSize(vFTargets), fOne, fVerbose, &Status, 1200, iSel, 0, "HMUX branch", pCtx );
            Gia_ManStop( pGiaBranch );
            Gia_ManStop( pGiaGBranch );
            Gia_ManStop( pGiaFBranch );
            Vec_IntFree( vGTargets );
            Vec_IntFree( vFTargets );
            if ( Status == 0 )
            {
                if ( pStatus )
                    *pStatus = ACB_XEC_NEQ;
                return pModel;
            }
            if ( Status == -1 )
            {
                int StatusDc = -1;
                if ( vIntDcObjsG && vIntDcCtrlsG && vIntDcCtrlIdsG &&
                     Vec_IntSize(vIntDcObjsG) > 0 && Vec_IntSize(vIntDcCtrlsG) > 4 &&
                     pCtx->vLastBranchHardPos && Vec_IntSize(pCtx->vLastBranchHardPos) > 0 )
                {
                    Vec_Int_t * vPoIds = Acb_NtkCollectPoIdsForSelector( pNtkF, vMuxPoSelIdsG, iSel );
                    Vec_Int_t * vHardOrig = Vec_IntAlloc( Vec_IntSize(pCtx->vLastBranchHardPos) );
                    int iHardLocal, k;
                    Vec_IntForEachEntry( pCtx->vLastBranchHardPos, iHardLocal, k )
                        if ( iHardLocal >= 0 && iHardLocal < Vec_IntSize(vPoIds) )
                            Vec_IntPushUnique( vHardOrig, Vec_IntEntry(vPoIds, iHardLocal) );
                    if ( fVerbose )
                        printf( "HMUX branch selector %d branch %d collected %d hard/unvisited local outputs -> %d original outputs for targeted DC-control proof.\n",
                            iSel, fOne, Vec_IntSize(pCtx->vLastBranchHardPos), Vec_IntSize(vHardOrig) );
                    if ( Vec_IntSize(vHardOrig) <= 4 && Vec_IntSize(vIntDcCtrlsG) <= 8 )
                        pModel = Acb_NtkSolveMuxDcControlTargetList( pNtkF, pNtkG, vHardOrig,
                            vCutObjsG, vMuxSelectorsG, vMuxPoSelIdsG, fOne,
                            vIntDcObjsG, vIntDcCtrlsG, vIntDcCtrlIdsG, fVerbose, &StatusDc, 90 );
                    else if ( fVerbose )
                        printf( "Skipping HMUX+DC targeted recursive proof: hard outputs = %d, DC controls = %d; recursion is too broad for this branch.\n",
                            Vec_IntSize(vHardOrig), Vec_IntSize(vIntDcCtrlsG) );
                    Vec_IntFree( vHardOrig );
                    Vec_IntFree( vPoIds );
                    if ( StatusDc == 0 )
                    {
                        if ( pStatus )
                            *pStatus = ACB_XEC_NEQ;
                        return pModel;
                    }
                    if ( StatusDc == 1 )
                        Status = 1;
                }
                if ( Status == -1 )
                    fUndec = 1;
            }
        }
    }
    if ( pStatus )
        *pStatus = fUndec ? -1 : 1;
    printf( "The networks are %s by HMUX branch-level proving.  ", fUndec ? "UNDECIDED" : "equivalent" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return NULL;
}
int * Acb_NtkSolveHmuxCompleteCubes( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, Vec_Int_t * vCutObjsG, Vec_Int_t * vMuxSelectorsG, Vec_Int_t * vMuxPoSelIdsG, int fVerbose, int * pStatus, int nTotalLimit, int nCubeLimit )
{
    Vec_Int_t * vFTargets = NULL, * vGTargets = NULL, * vCubeVals = NULL;
    Gia_Man_t * pGiaF = NULL, * pGiaG = NULL, * pGiaMiter = NULL, * pGiaCond = NULL, * pTemp = NULL;
    int nSels, nCubes, iCube, iSel, Status = ACB_XEC_UNDEC, StatusAll = ACB_XEC_EQ, * pModel = NULL;
    abctime clk = Abc_Clock();
    abctime clkLimit = nTotalLimit > 0 ? clk + nTotalLimit * CLOCKS_PER_SEC : 0;
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    if ( vCutObjsG == NULL || vMuxSelectorsG == NULL || vMuxPoSelIdsG == NULL )
        return NULL;
    nSels = Vec_IntSize( vMuxSelectorsG );
    if ( nSels <= 0 || nSels > 4 || Vec_IntSize(vCutObjsG) != Acb_NtkCoNum(pNtkG) )
        return NULL;
    nCubes = 1 << nSels;
    vFTargets = Acb_NtkCollectCoDrivers( pNtkF );
    pGiaF = Acb_NtkGiaDeriveDualTargets( pNtkF, vFTargets );
    vCubeVals = Vec_IntAlloc( nSels );
    if ( fVerbose )
        printf( "Trying complete HMUX selector-cube proof: selectors = %d. cubes = %d. outputs = %d. total limit = %d sec.\n",
            nSels, nCubes, Acb_NtkCoNum(pNtkF), nTotalLimit );
    for ( iCube = 0; iCube < nCubes; iCube++ )
    {
        int nThisLimit = nCubeLimit;
        if ( clkLimit )
        {
            int nRemain = (int)((clkLimit - Abc_Clock()) / CLOCKS_PER_SEC);
            if ( nRemain <= 0 )
            {
                StatusAll = ACB_XEC_UNDEC;
                break;
            }
            nThisLimit = nCubeLimit > 0 ? Abc_MinInt( nCubeLimit, nRemain ) : nRemain;
        }
        Vec_IntClear( vCubeVals );
        for ( iSel = 0; iSel < nSels; iSel++ )
            Vec_IntPush( vCubeVals, (iCube >> iSel) & 1 );
        vGTargets = Acb_NtkCollectPoMuxCubeTargets( pNtkG, vCutObjsG, vMuxPoSelIdsG, vCubeVals );
        Vec_IntAppend( vGTargets, vMuxSelectorsG );
        pGiaG = Acb_NtkGiaDeriveDualTargets( pNtkG, vGTargets );
        pGiaMiter = Acb_NtkGiaDeriveMiterWithSecondExtras( pGiaF, pGiaG, nSels );
        pGiaCond = Acb_GiaDeriveCubeConditionMiter( pGiaMiter, Acb_NtkCoNum(pNtkF), vCubeVals );
        if ( Gia_ManAndNum(pGiaCond) > 5000 )
        {
            pTemp = Gia_ManCompress2( pGiaCond, 1, 0 );
            if ( pTemp )
            {
                Gia_ManStop( pGiaCond );
                pGiaCond = pTemp;
                pTemp = NULL;
            }
        }
        if ( Gia_ManAndNum(pGiaCond) > 8000 && Gia_ManAndNum(pGiaCond) < 70000 )
        {
            pTemp = Acb_NtkFraigEquivReduce( pGiaCond, fVerbose, "Complete HMUX selector cube", "conditioned cube", 32, 300, 12000, Abc_MaxInt( 50, Gia_ManAndNum(pGiaCond) / 200 ) );
            if ( pTemp )
            {
                Gia_ManStop( pGiaCond );
                pGiaCond = pTemp;
                pTemp = NULL;
            }
        }
        if ( fVerbose )
        {
            printf( "Complete HMUX selector cube %d/%d: values =", iCube + 1, nCubes );
            for ( iSel = 0; iSel < nSels; iSel++ )
                printf( " s%d=%d", iSel, Vec_IntEntry(vCubeVals, iSel) );
            printf( ". And = %d. PO = %d. limit = %d sec.\n", Gia_ManAndNum(pGiaCond), Gia_ManCoNum(pGiaCond), nThisLimit );
        }
        pModel = Acb_NtkSolveCadicalPoSweepLabel( pGiaCond, fVerbose, &Status, nThisLimit, 500000, "complete HMUX selector-cube PO sweep", 0 );
        if ( Status == ACB_XEC_UNDEC )
        {
            if ( fVerbose )
                printf( "Complete HMUX selector cube %d/%d PO sweep was inconclusive; skipping duplicate whole-cube CaDiCaL.\n",
                    iCube + 1, nCubes );
        }
        Gia_ManStop( pGiaCond );  pGiaCond = NULL;
        Gia_ManStop( pGiaMiter ); pGiaMiter = NULL;
        Gia_ManStop( pGiaG );     pGiaG = NULL;
        Vec_IntFreeP( &vGTargets );
        if ( Status == ACB_XEC_NEQ )
        {
            StatusAll = ACB_XEC_NEQ;
            break;
        }
        if ( Status != ACB_XEC_EQ )
        {
            StatusAll = ACB_XEC_UNDEC;
            break;
        }
    }
    if ( pStatus )
        *pStatus = StatusAll;
    if ( StatusAll == ACB_XEC_EQ )
    {
        printf( "The networks are equivalent by complete HMUX selector-cube proof.  " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    else if ( fVerbose )
    {
        printf( "The networks are %s by complete HMUX selector-cube proof.  ",
            StatusAll == ACB_XEC_NEQ ? "NOT equivalent" : "UNDECIDED" );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    Vec_IntFreeP( &vFTargets );
    Vec_IntFreeP( &vGTargets );
    Vec_IntFreeP( &vCubeVals );
    if ( pGiaF ) Gia_ManStop( pGiaF );
    if ( pGiaG ) Gia_ManStop( pGiaG );
    if ( pGiaMiter ) Gia_ManStop( pGiaMiter );
    if ( pGiaCond ) Gia_ManStop( pGiaCond );
    if ( pTemp ) Gia_ManStop( pTemp );
    return pModel;
}
int * Acb_NtkSolveMuxTargetBranches( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, int iPo, Vec_Int_t * vCutObjsG, Vec_Int_t * vMuxSelectorsG, Vec_Int_t * vMuxPoSelIdsG, int fVerbose, int * pStatus, int nBranchLimit, int nMaxBranchAnd )
{
    Vec_Int_t * vFTargets = Vec_IntAlloc( 1 );
    Acb_XecCtx_t BranchCtx;
    int iSel, fOne, Status, fUndec = 0;
    int * pModel = NULL;
    abctime clk = Abc_Clock();
    Acb_XecCtxInit( &BranchCtx );
    assert( iPo >= 0 && iPo < Acb_NtkCoNum(pNtkF) && iPo < Acb_NtkCoNum(pNtkG) );
    assert( vCutObjsG && vMuxSelectorsG && vMuxPoSelIdsG );
    assert( Vec_IntSize(vCutObjsG) == Acb_NtkCoNum(pNtkG) );
    assert( Vec_IntSize(vMuxPoSelIdsG) == Acb_NtkCoNum(pNtkG) );
    iSel = Vec_IntEntry( vMuxPoSelIdsG, iPo );
    if ( iSel < 0 || iSel >= Vec_IntSize(vMuxSelectorsG) )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_UNDEC;
        Vec_IntFree( vFTargets );
        Acb_XecCtxFree( &BranchCtx );
        return NULL;
    }
    Vec_IntPush( vFTargets, Acb_ObjFanin(pNtkF, Acb_NtkCo(pNtkF, iPo), 0) );
    if ( fVerbose )
        printf( "Trying MUX target branch proving: output = %d. selector = %d/%d.\n",
            iPo, iSel, Vec_IntSize(vMuxSelectorsG) );
    for ( fOne = 0; fOne <= 1; fOne++ )
    {
        Vec_Int_t * vGTargets = Vec_IntAlloc( 2 );
        Gia_Man_t * pGiaFBranch = NULL, * pGiaGBranch = NULL, * pGiaBranch = NULL;
        int iMux = Vec_IntEntry( vCutObjsG, iPo );
        assert( !Acb_ObjIsCio(pNtkG, iMux) && Acb_ObjType(pNtkG, iMux) == ABC_OPER_BIT_MUX );
        Vec_IntPush( vGTargets, Acb_ObjFanin(pNtkG, iMux, fOne ? 1 : 0) );
        Vec_IntPush( vGTargets, Vec_IntEntry(vMuxSelectorsG, iSel) );
        pGiaFBranch = Acb_NtkGiaDeriveDualTargets( pNtkF, vFTargets );
        pGiaGBranch = Acb_NtkGiaDeriveDualTargets( pNtkG, vGTargets );
        pGiaBranch  = Acb_NtkGiaDeriveMiterWithSecondExtras( pGiaFBranch, pGiaGBranch, 1 );
        if ( fVerbose )
            printf( "MUX target branch miter: output %d selector %d branch %d. And = %d. PO = %d.\n",
                iPo, iSel, fOne, Gia_ManAndNum(pGiaBranch), Gia_ManPoNum(pGiaBranch) );
        if ( nMaxBranchAnd > 0 && Gia_ManAndNum(pGiaBranch) >= nMaxBranchAnd )
        {
            if ( fVerbose )
                printf( "Skipping MUX target branch output %d selector %d/%d because branch miter is not smaller than current hard cone: branch And = %d, current And = %d.\n",
                    iPo, iSel, fOne, Gia_ManAndNum(pGiaBranch), nMaxBranchAnd );
            Status = -1;
            fUndec = 1;
        }
        else
            pModel = Acb_NtkSolveCadicalSelectorBranch( pGiaBranch, 1, fOne, fVerbose, &Status, nBranchLimit, iSel, 0, "MUX target branch", &BranchCtx );
        Gia_ManStop( pGiaBranch );
        Gia_ManStop( pGiaGBranch );
        Gia_ManStop( pGiaFBranch );
        Vec_IntFree( vGTargets );
        if ( Status == 0 )
        {
            Vec_IntFree( vFTargets );
            Acb_XecCtxFree( &BranchCtx );
            if ( pStatus )
                *pStatus = ACB_XEC_NEQ;
            return pModel;
        }
        if ( Status == -1 )
            fUndec = 1;
    }
    Vec_IntFree( vFTargets );
    if ( pStatus )
        *pStatus = fUndec ? ACB_XEC_UNDEC : ACB_XEC_EQ;
    printf( "The hard output %d is %s by MUX target branch proving.  ",
        iPo, fUndec ? "UNDECIDED" : "UNSAT" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Acb_XecCtxFree( &BranchCtx );
    return NULL;
}
int * Acb_NtkSolveDcControlBranchesLimit( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, Vec_Int_t * vDcObjsG, Vec_Int_t * vDcCtrlsG, Vec_Int_t * vDcCtrlIdsG, int fVerbose, int * pStatus, int nBranchLimit, int fStopOnUndec, int nMaxBranchAnd )
{
    Vec_Int_t * vFTargets = Acb_NtkCollectCoDrivers( pNtkF );
    Acb_XecCtx_t BranchCtx;
    int iCtrl, fOne, Status, fUndec = 0;
    int * pModel = NULL;
    abctime clk = Abc_Clock();
    Acb_XecCtxInit( &BranchCtx );
    if ( fVerbose )
        printf( "Trying DC-control branch proving: DC nodes = %d. controls = %d.\n",
            Vec_IntSize(vDcObjsG), Vec_IntSize(vDcCtrlsG) );
    for ( iCtrl = 0; iCtrl < Vec_IntSize(vDcCtrlsG); iCtrl++ )
    {
        Vec_Int_t * vDcObjsOne = Acb_NtkCollectDcObjsForControl( vDcObjsG, vDcCtrlIdsG, iCtrl );
        int fCtrlUndec = 0;
        for ( fOne = 0; fOne <= 1; fOne++ )
        {
            Vec_Int_t * vGTargets = Vec_IntAlloc( Acb_NtkCoNum(pNtkG) + 1 );
            Gia_Man_t * pGiaFBranch = NULL, * pGiaGBranch = NULL, * pGiaBranch = NULL;
            int i, iObj;
            Acb_NtkForEachCo( pNtkG, iObj, i )
                Vec_IntPush( vGTargets, Acb_ObjFanin(pNtkG, iObj, 0) );
            Vec_IntPush( vGTargets, Vec_IntEntry(vDcCtrlsG, iCtrl) );
            pGiaFBranch = Acb_NtkGiaDeriveDualTargets( pNtkF, vFTargets );
            pGiaGBranch = Acb_NtkGiaDeriveDualTargetsBranch( pNtkG, vGTargets, vDcObjsOne, fOne );
            pGiaBranch  = Acb_NtkGiaDeriveMiterWithSecondExtras( pGiaFBranch, pGiaGBranch, 1 );
            if ( fVerbose )
                printf( "DC-control branch miter: control %d branch %d. DC nodes = %d. And = %d. PO = %d.\n",
                    iCtrl, fOne, Vec_IntSize(vDcObjsOne), Gia_ManAndNum(pGiaBranch), Gia_ManPoNum(pGiaBranch) );
            if ( nMaxBranchAnd > 0 && Gia_ManAndNum(pGiaBranch) >= nMaxBranchAnd )
            {
                if ( fVerbose )
                    printf( "Skipping DC-control branch %d/%d because branch miter is not smaller than current miter: branch And = %d, current And = %d.\n",
                        iCtrl, fOne, Gia_ManAndNum(pGiaBranch), nMaxBranchAnd );
                Status = -1;
                fUndec = 1;
            }
            else
            {
            pModel = Acb_NtkSolveCadicalSelectorBranch( pGiaBranch, Vec_IntSize(vFTargets), fOne, fVerbose, &Status, nBranchLimit, iCtrl, fStopOnUndec, "DC-control branch", &BranchCtx );
            }
            Gia_ManStop( pGiaBranch );
            Gia_ManStop( pGiaGBranch );
            Gia_ManStop( pGiaFBranch );
            Vec_IntFree( vGTargets );
            if ( Status == 0 )
            {
                Vec_IntFree( vDcObjsOne );
                Vec_IntFree( vFTargets );
                Acb_XecCtxFree( &BranchCtx );
                if ( pStatus )
                    *pStatus = ACB_XEC_NEQ;
                return pModel;
            }
            if ( Status == -1 )
            {
                fUndec = 1;
                fCtrlUndec = 1;
            }
        }
        Vec_IntFree( vDcObjsOne );
        if ( !fCtrlUndec )
        {
            Vec_IntFree( vFTargets );
            Acb_XecCtxFree( &BranchCtx );
            if ( pStatus )
                *pStatus = ACB_XEC_EQ;
            printf( "The networks are equivalent by DC-control branch proving on control %d.  ", iCtrl );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            return NULL;
        }
    }
    Vec_IntFree( vFTargets );
    if ( pStatus )
        *pStatus = fUndec ? -1 : 1;
    printf( "The networks are %s by DC-control branch proving.  ", fUndec ? "UNDECIDED" : "equivalent" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Acb_XecCtxFree( &BranchCtx );
    return NULL;
}
int * Acb_NtkSolveDcControlTargetBranches( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, int iPo, Vec_Int_t * vDcObjsG, Vec_Int_t * vDcCtrlsG, Vec_Int_t * vDcCtrlIdsG, int fVerbose, int * pStatus, int nBranchLimit, int nMaxBranchAnd )
{
    Vec_Int_t * vFTargets = Vec_IntAlloc( 1 );
    Acb_XecCtx_t BranchCtx;
    int iCtrl, fOne, Status, fUndec = 0;
    int * pModel = NULL;
    abctime clk = Abc_Clock();
    Acb_XecCtxInit( &BranchCtx );
    assert( iPo >= 0 && iPo < Acb_NtkCoNum(pNtkF) && iPo < Acb_NtkCoNum(pNtkG) );
    Vec_IntPush( vFTargets, Acb_ObjFanin(pNtkF, Acb_NtkCo(pNtkF, iPo), 0) );
    if ( fVerbose )
        printf( "Trying DC-control target branch proving: output = %d. DC nodes = %d. controls = %d.\n",
            iPo, Vec_IntSize(vDcObjsG), Vec_IntSize(vDcCtrlsG) );
    for ( iCtrl = 0; iCtrl < Vec_IntSize(vDcCtrlsG); iCtrl++ )
    {
        Vec_Int_t * vDcObjsOne = Acb_NtkCollectDcObjsForControl( vDcObjsG, vDcCtrlIdsG, iCtrl );
        int fCtrlUndec = 0;
        for ( fOne = 0; fOne <= 1; fOne++ )
        {
            Vec_Int_t * vGTargets = Vec_IntAlloc( 2 );
            Gia_Man_t * pGiaFBranch = NULL, * pGiaGBranch = NULL, * pGiaBranch = NULL;
            Vec_IntPush( vGTargets, Acb_ObjFanin(pNtkG, Acb_NtkCo(pNtkG, iPo), 0) );
            Vec_IntPush( vGTargets, Vec_IntEntry(vDcCtrlsG, iCtrl) );
            pGiaFBranch = Acb_NtkGiaDeriveDualTargets( pNtkF, vFTargets );
            pGiaGBranch = Acb_NtkGiaDeriveDualTargetsBranch( pNtkG, vGTargets, vDcObjsOne, fOne );
            pGiaBranch  = Acb_NtkGiaDeriveMiterWithSecondExtras( pGiaFBranch, pGiaGBranch, 1 );
            if ( fVerbose )
                printf( "DC-control target branch miter: output %d control %d branch %d. DC nodes = %d. And = %d. PO = %d.\n",
                    iPo, iCtrl, fOne, Vec_IntSize(vDcObjsOne), Gia_ManAndNum(pGiaBranch), Gia_ManPoNum(pGiaBranch) );
            if ( nMaxBranchAnd > 0 && Gia_ManAndNum(pGiaBranch) >= nMaxBranchAnd )
            {
                if ( fVerbose )
                    printf( "Skipping DC-control target branch output %d control %d/%d because branch miter is not smaller than current hard cone: branch And = %d, current And = %d.\n",
                        iPo, iCtrl, fOne, Gia_ManAndNum(pGiaBranch), nMaxBranchAnd );
                Status = -1;
                fUndec = 1;
            }
            else
                pModel = Acb_NtkSolveCadicalSelectorBranch( pGiaBranch, 1, fOne, fVerbose, &Status, nBranchLimit, iCtrl, 0, "DC-control target branch", &BranchCtx );
            Gia_ManStop( pGiaBranch );
            Gia_ManStop( pGiaGBranch );
            Gia_ManStop( pGiaFBranch );
            Vec_IntFree( vGTargets );
            if ( Status == 0 )
            {
                Vec_IntFree( vDcObjsOne );
                Vec_IntFree( vFTargets );
                Acb_XecCtxFree( &BranchCtx );
                if ( pStatus )
                    *pStatus = ACB_XEC_NEQ;
                return pModel;
            }
            if ( Status == -1 )
            {
                fUndec = 1;
                fCtrlUndec = 1;
            }
        }
        Vec_IntFree( vDcObjsOne );
        if ( !fCtrlUndec )
        {
            Vec_IntFree( vFTargets );
            Acb_XecCtxFree( &BranchCtx );
            if ( pStatus )
                *pStatus = ACB_XEC_EQ;
            printf( "The hard output %d is UNSAT by DC-control target branch proving on control %d.  ", iPo, iCtrl );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            return NULL;
        }
    }
    Vec_IntFree( vFTargets );
    if ( pStatus )
        *pStatus = fUndec ? ACB_XEC_UNDEC : ACB_XEC_EQ;
    printf( "The hard output %d is %s by DC-control target branch proving.  ",
        iPo, fUndec ? "UNDECIDED" : "UNSAT" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Acb_XecCtxFree( &BranchCtx );
    return NULL;
}
void Acb_NtkCollectDcObjsForCube( Vec_Int_t * vDcObjs, Vec_Int_t * vDcCtrlIds, Vec_Int_t * vCubeCtrls, Vec_Int_t * vCubeVals, Vec_Int_t ** pvObjs, Vec_Int_t ** pvVals )
{
    Vec_Int_t * vObjs = Vec_IntAlloc( Vec_IntSize(vDcObjs) );
    Vec_Int_t * vVals = Vec_IntAlloc( Vec_IntSize(vDcObjs) );
    int i, k, iObj, iCtrlId, iCubeCtrl;
    Vec_IntForEachEntry( vDcObjs, iObj, i )
    {
        iCtrlId = Vec_IntEntry( vDcCtrlIds, i );
        Vec_IntForEachEntry( vCubeCtrls, iCubeCtrl, k )
            if ( iCubeCtrl == iCtrlId )
            {
                Vec_IntPush( vObjs, iObj );
                Vec_IntPush( vVals, Vec_IntEntry(vCubeVals, k) );
                break;
            }
    }
    *pvObjs = vObjs;
    *pvVals = vVals;
}
int * Acb_NtkSolveDcControlTargetCube( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, int iPo, Vec_Int_t * vDcObjsG, Vec_Int_t * vDcCtrlsG, Vec_Int_t * vDcCtrlIdsG, Vec_Int_t * vCubeCtrls, Vec_Int_t * vCubeVals, int fVerbose, int * pStatus, int nBranchLimit, int nDepthLeft )
{
    Vec_Int_t * vFTargets = Vec_IntAlloc( 1 );
    Vec_Int_t * vGTargets = Vec_IntAlloc( 1 + Vec_IntSize(vCubeCtrls) );
    Vec_Int_t * vDcObjsCube = NULL, * vDcValsCube = NULL;
    Gia_Man_t * pGiaFBranch = NULL, * pGiaGBranch = NULL, * pGiaBranch = NULL, * pGiaCond = NULL, * pTemp = NULL;
    int i, k, iCtrl, Status = -1, * pModel = NULL;
    int nProbeLimit = nDepthLeft > 0 ? Abc_MinInt( nBranchLimit, 30 ) : nBranchLimit;
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    Vec_IntPush( vFTargets, Acb_ObjFanin(pNtkF, Acb_NtkCo(pNtkF, iPo), 0) );
    Vec_IntPush( vGTargets, Acb_ObjFanin(pNtkG, Acb_NtkCo(pNtkG, iPo), 0) );
    Vec_IntForEachEntry( vCubeCtrls, iCtrl, i )
        Vec_IntPush( vGTargets, Vec_IntEntry(vDcCtrlsG, iCtrl) );
    Acb_NtkCollectDcObjsForCube( vDcObjsG, vDcCtrlIdsG, vCubeCtrls, vCubeVals, &vDcObjsCube, &vDcValsCube );
    pGiaFBranch = Acb_NtkGiaDeriveDualTargets( pNtkF, vFTargets );
    pGiaGBranch = Acb_NtkGiaDeriveDualTargetsBranchValues( pNtkG, vGTargets, vDcObjsCube, vDcValsCube, 0 );
    pGiaBranch  = Acb_NtkGiaDeriveMiterWithSecondExtras( pGiaFBranch, pGiaGBranch, Vec_IntSize(vCubeCtrls) );
    pGiaCond    = Acb_GiaDeriveCubeConditionMiter( pGiaBranch, 1, vCubeVals );
    if ( Gia_ManAndNum(pGiaCond) > 5000 )
    {
        pTemp = Gia_ManCompress2( pGiaCond, 1, 0 );
        if ( pTemp )
        {
            Gia_ManStop( pGiaCond );
            pGiaCond = pTemp;
            pTemp = NULL;
        }
    }
    if ( fVerbose )
    {
        printf( "DC-control recursive target: output %d cube =", iPo );
        Vec_IntForEachEntry( vCubeCtrls, iCtrl, i )
            printf( " c%d=%d", iCtrl, Vec_IntEntry(vCubeVals, i) );
        printf( ". And = %d. limit = %d sec%s.\n", Gia_ManAndNum(pGiaCond), nProbeLimit,
            nDepthLeft > 0 ? " before split" : "" );
    }
    pModel = Acb_NtkSolveCadicalLimit( pGiaCond, 0, 0, &Status, nProbeLimit, NULL, 0 );
    Gia_ManStop( pGiaCond );
    Gia_ManStop( pGiaBranch );
    Gia_ManStop( pGiaGBranch );
    Gia_ManStop( pGiaFBranch );
    Vec_IntFree( vDcObjsCube );
    Vec_IntFree( vDcValsCube );
    Vec_IntFree( vGTargets );
    Vec_IntFree( vFTargets );
    if ( Status == 1 )
    {
        if ( fVerbose )
            printf( "DC-control recursive target: output %d cube UNSAT.\n", iPo );
        if ( pStatus )
            *pStatus = ACB_XEC_EQ;
        return NULL;
    }
    if ( Status == 0 )
    {
        if ( fVerbose )
            printf( "DC-control recursive target: output %d cube SAT.\n", iPo );
        if ( pStatus )
            *pStatus = ACB_XEC_NEQ;
        return pModel;
    }
    ABC_FREE( pModel );
    if ( nDepthLeft <= 0 )
    {
        if ( fVerbose )
            printf( "DC-control recursive target: output %d cube UNDECIDED at depth limit.\n", iPo );
        return NULL;
    }
    {
    Vec_Int_t * vTriedCtrls = Vec_IntAlloc( Vec_IntSize(vDcCtrlsG) );
    for ( k = 0; k < Vec_IntSize(vDcCtrlsG); k++ )
    {
        int fOne, fCtrlUndec = 0, nBestCount = -1;
        iCtrl = -1;
        for ( i = 0; i < Vec_IntSize(vDcCtrlsG); i++ )
        {
            int j, iCtrlId, nCount = 0;
            if ( Vec_IntFind(vCubeCtrls, i) >= 0 || Vec_IntFind(vTriedCtrls, i) >= 0 )
                continue;
            Vec_IntForEachEntry( vDcCtrlIdsG, iCtrlId, j )
                nCount += (iCtrlId == i);
            if ( nCount > nBestCount )
            {
                nBestCount = nCount;
                iCtrl = i;
            }
        }
        if ( iCtrl < 0 )
            break;
        Vec_IntPush( vTriedCtrls, iCtrl );
        for ( fOne = 1; fOne >= 0; fOne-- )
        {
            int StatusSub = -1;
            Vec_IntPush( vCubeCtrls, iCtrl );
            Vec_IntPush( vCubeVals, fOne );
            pModel = Acb_NtkSolveDcControlTargetCube( pNtkF, pNtkG, iPo, vDcObjsG, vDcCtrlsG, vDcCtrlIdsG,
                vCubeCtrls, vCubeVals, fVerbose, &StatusSub, nBranchLimit, nDepthLeft - 1 );
            Vec_IntPop( vCubeCtrls );
            Vec_IntPop( vCubeVals );
            if ( StatusSub == 0 )
            {
                Vec_IntFree( vTriedCtrls );
                if ( pStatus )
                    *pStatus = ACB_XEC_NEQ;
                return pModel;
            }
            if ( StatusSub != 1 )
                fCtrlUndec = 1;
        }
        if ( !fCtrlUndec )
        {
            if ( fVerbose )
                printf( "DC-control recursive target: output %d proven by splitting control %d.\n", iPo, iCtrl );
            Vec_IntFree( vTriedCtrls );
            if ( pStatus )
                *pStatus = ACB_XEC_EQ;
            return NULL;
        }
    }
    Vec_IntFree( vTriedCtrls );
    }
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    return NULL;
}
int * Acb_NtkSolveDcControlTargetList( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, Vec_Int_t * vHardPos, Vec_Int_t * vDcObjsG, Vec_Int_t * vDcCtrlsG, Vec_Int_t * vDcCtrlIdsG, int fVerbose, int * pStatus, int nBranchLimit )
{
    int i, iPo, StatusOne = -1, fUndec = 0;
    int * pModel = NULL;
    abctime clk = Abc_Clock();
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    if ( vHardPos == NULL || Vec_IntSize(vHardPos) == 0 )
        return NULL;
    if ( fVerbose )
        printf( "Trying DC-control target proving for %d hard outputs.\n", Vec_IntSize(vHardPos) );
    Vec_IntForEachEntry( vHardPos, iPo, i )
    {
        Vec_Int_t * vCubeCtrls = Vec_IntAlloc( Vec_IntSize(vDcCtrlsG) );
        Vec_Int_t * vCubeVals = Vec_IntAlloc( Vec_IntSize(vDcCtrlsG) );
        int nDepth = Vec_IntSize(vDcCtrlsG) <= 3 ? Vec_IntSize(vDcCtrlsG) : Abc_MinInt( 2, Vec_IntSize(vDcCtrlsG) );
        pModel = Acb_NtkSolveDcControlTargetCube( pNtkF, pNtkG, iPo, vDcObjsG, vDcCtrlsG, vDcCtrlIdsG,
            vCubeCtrls, vCubeVals, fVerbose, &StatusOne, nBranchLimit, nDepth );
        Vec_IntFree( vCubeCtrls );
        Vec_IntFree( vCubeVals );
        if ( StatusOne == 0 )
        {
            if ( pStatus )
                *pStatus = ACB_XEC_NEQ;
            return pModel;
        }
        if ( StatusOne != 1 )
        {
            fUndec = 1;
            if ( fVerbose )
                printf( "DC-control target list: output %d remains UNDECIDED; stopping target-list proof.\n", iPo );
            break;
        }
    }
    if ( pStatus )
        *pStatus = fUndec ? -1 : 1;
    printf( "The hard outputs are %s by DC-control target-list proving.  ", fUndec ? "UNDECIDED" : "UNSAT" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return NULL;
}
int * Acb_NtkSolveMuxDcControlTargetCube( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, int iPo, Vec_Int_t * vCutObjsG, Vec_Int_t * vMuxSelectorsG, Vec_Int_t * vMuxPoSelIdsG, int fSelBranch, Vec_Int_t * vDcObjsG, Vec_Int_t * vDcCtrlsG, Vec_Int_t * vDcCtrlIdsG, Vec_Int_t * vCubeCtrls, Vec_Int_t * vCubeVals, int fVerbose, int * pStatus, int nBranchLimit, int nDepthLeft )
{
    Vec_Int_t * vFTargets = Vec_IntAlloc( 1 );
    Vec_Int_t * vGTargets = Vec_IntAlloc( 2 + Vec_IntSize(vCubeCtrls) );
    Vec_Int_t * vDcObjsCube = NULL, * vDcValsCube = NULL, * vCondVals = Vec_IntAlloc( 1 + Vec_IntSize(vCubeCtrls) );
    Gia_Man_t * pGiaFBranch = NULL, * pGiaGBranch = NULL, * pGiaBranch = NULL, * pGiaCond = NULL, * pTemp = NULL;
    int i, k, iCtrl, iMux, Status = -1, * pModel = NULL;
    int nProbeLimit = nDepthLeft > 0 ? Abc_MinInt( nBranchLimit, 30 ) : nBranchLimit;
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    assert( iPo >= 0 && iPo < Acb_NtkCoNum(pNtkF) && iPo < Acb_NtkCoNum(pNtkG) );
    assert( vCutObjsG && vMuxSelectorsG && vMuxPoSelIdsG );
    iMux = Vec_IntEntry( vCutObjsG, iPo );
    assert( !Acb_ObjIsCio(pNtkG, iMux) && Acb_ObjType(pNtkG, iMux) == ABC_OPER_BIT_MUX );
    Vec_IntPush( vFTargets, Acb_ObjFanin(pNtkF, Acb_NtkCo(pNtkF, iPo), 0) );
    Vec_IntPush( vGTargets, Acb_ObjFanin(pNtkG, iMux, fSelBranch ? 1 : 0) );
    Vec_IntPush( vGTargets, Vec_IntEntry(vMuxSelectorsG, Vec_IntEntry(vMuxPoSelIdsG, iPo)) );
    Vec_IntForEachEntry( vCubeCtrls, iCtrl, i )
        Vec_IntPush( vGTargets, Vec_IntEntry(vDcCtrlsG, iCtrl) );
    Acb_NtkCollectDcObjsForCube( vDcObjsG, vDcCtrlIdsG, vCubeCtrls, vCubeVals, &vDcObjsCube, &vDcValsCube );
    pGiaFBranch = Acb_NtkGiaDeriveDualTargets( pNtkF, vFTargets );
    pGiaGBranch = Acb_NtkGiaDeriveDualTargetsBranchValues( pNtkG, vGTargets, vDcObjsCube, vDcValsCube, 0 );
    pGiaBranch  = Acb_NtkGiaDeriveMiterWithSecondExtras( pGiaFBranch, pGiaGBranch, 1 + Vec_IntSize(vCubeCtrls) );
    Vec_IntPush( vCondVals, fSelBranch );
    Vec_IntForEachEntry( vCubeVals, iCtrl, i )
        Vec_IntPush( vCondVals, iCtrl );
    pGiaCond = Acb_GiaDeriveCubeConditionMiter( pGiaBranch, 1, vCondVals );
    if ( Gia_ManAndNum(pGiaCond) > 5000 )
    {
        pTemp = Gia_ManCompress2( pGiaCond, 1, 0 );
        if ( pTemp )
        {
            Gia_ManStop( pGiaCond );
            pGiaCond = pTemp;
            pTemp = NULL;
        }
    }
    if ( fVerbose )
    {
        printf( "HMUX+DC recursive target: output %d selector %d branch %d cube =",
            iPo, Vec_IntEntry(vMuxPoSelIdsG, iPo), fSelBranch );
        Vec_IntForEachEntry( vCubeCtrls, iCtrl, i )
            printf( " c%d=%d", iCtrl, Vec_IntEntry(vCubeVals, i) );
        printf( ". And = %d. limit = %d sec%s.\n", Gia_ManAndNum(pGiaCond), nProbeLimit,
            nDepthLeft > 0 ? " before split" : "" );
    }
    pModel = Acb_NtkSolveCadicalLimit( pGiaCond, 0, 0, &Status, nProbeLimit, NULL, 0 );
    Gia_ManStop( pGiaCond );
    Gia_ManStop( pGiaBranch );
    Gia_ManStop( pGiaGBranch );
    Gia_ManStop( pGiaFBranch );
    Vec_IntFree( vDcObjsCube );
    Vec_IntFree( vDcValsCube );
    Vec_IntFree( vCondVals );
    Vec_IntFree( vGTargets );
    Vec_IntFree( vFTargets );
    if ( Status == 1 )
    {
        if ( fVerbose )
            printf( "HMUX+DC recursive target: output %d cube UNSAT.\n", iPo );
        if ( pStatus )
            *pStatus = ACB_XEC_EQ;
        return NULL;
    }
    if ( Status == 0 )
    {
        if ( fVerbose )
            printf( "HMUX+DC recursive target: output %d cube SAT.\n", iPo );
        if ( pStatus )
            *pStatus = ACB_XEC_NEQ;
        return pModel;
    }
    ABC_FREE( pModel );
    if ( nDepthLeft <= 0 )
    {
        if ( fVerbose )
            printf( "HMUX+DC recursive target: output %d cube UNDECIDED at depth limit.\n", iPo );
        return NULL;
    }
    {
    Vec_Int_t * vTriedCtrls = Vec_IntAlloc( Vec_IntSize(vDcCtrlsG) );
    for ( k = 0; k < Vec_IntSize(vDcCtrlsG); k++ )
    {
        int fOne, fCtrlUndec = 0, nBestCount = -1;
        iCtrl = -1;
        for ( i = 0; i < Vec_IntSize(vDcCtrlsG); i++ )
        {
            int j, iCtrlId, nCount = 0;
            if ( Vec_IntFind(vCubeCtrls, i) >= 0 || Vec_IntFind(vTriedCtrls, i) >= 0 )
                continue;
            Vec_IntForEachEntry( vDcCtrlIdsG, iCtrlId, j )
                nCount += (iCtrlId == i);
            if ( nCount > nBestCount )
            {
                nBestCount = nCount;
                iCtrl = i;
            }
        }
        if ( iCtrl < 0 )
            break;
        Vec_IntPush( vTriedCtrls, iCtrl );
        for ( fOne = 1; fOne >= 0; fOne-- )
        {
            int StatusSub = -1;
            Vec_IntPush( vCubeCtrls, iCtrl );
            Vec_IntPush( vCubeVals, fOne );
            pModel = Acb_NtkSolveMuxDcControlTargetCube( pNtkF, pNtkG, iPo, vCutObjsG, vMuxSelectorsG, vMuxPoSelIdsG, fSelBranch,
                vDcObjsG, vDcCtrlsG, vDcCtrlIdsG, vCubeCtrls, vCubeVals, fVerbose, &StatusSub, nBranchLimit, nDepthLeft - 1 );
            Vec_IntPop( vCubeCtrls );
            Vec_IntPop( vCubeVals );
            if ( StatusSub == 0 )
            {
                Vec_IntFree( vTriedCtrls );
                if ( pStatus )
                    *pStatus = ACB_XEC_NEQ;
                return pModel;
            }
            if ( StatusSub != 1 )
                fCtrlUndec = 1;
        }
        if ( !fCtrlUndec )
        {
            if ( fVerbose )
                printf( "HMUX+DC recursive target: output %d proven by splitting control %d.\n", iPo, iCtrl );
            Vec_IntFree( vTriedCtrls );
            if ( pStatus )
                *pStatus = ACB_XEC_EQ;
            return NULL;
        }
    }
    Vec_IntFree( vTriedCtrls );
    }
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    return NULL;
}

int * Acb_NtkSolveMuxDcControlTargetList( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, Vec_Int_t * vHardPos, Vec_Int_t * vCutObjsG, Vec_Int_t * vMuxSelectorsG, Vec_Int_t * vMuxPoSelIdsG, int fSelBranch, Vec_Int_t * vDcObjsG, Vec_Int_t * vDcCtrlsG, Vec_Int_t * vDcCtrlIdsG, int fVerbose, int * pStatus, int nBranchLimit )
{
    int i, iPo, StatusOne = -1, fUndec = 0;
    int * pModel = NULL;
    Vec_Int_t * vCubeCtrls = NULL, * vCubeVals = NULL;
    abctime clk = Abc_Clock();
    int nCtrls = vDcCtrlsG ? Vec_IntSize(vDcCtrlsG) : 0;
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    if ( vHardPos == NULL || Vec_IntSize(vHardPos) == 0 )
        return NULL;
    if ( Vec_IntSize(vHardPos) > 4 || nCtrls > 8 )
    {
        if ( fVerbose )
            printf( "Skipping HMUX+DC target proving because recursive search is too broad: hard outputs = %d, controls = %d.\n",
                Vec_IntSize(vHardPos), nCtrls );
        return NULL;
    }
    if ( fVerbose )
        printf( "Trying HMUX+DC target proving for %d hard outputs. selector branch = %d. controls = %d.\n",
            Vec_IntSize(vHardPos), fSelBranch, nCtrls );
    vCubeCtrls = Vec_IntAlloc( nCtrls );
    vCubeVals = Vec_IntAlloc( nCtrls );
    Vec_IntForEachEntry( vHardPos, iPo, i )
    {
        int nDepth = nCtrls <= 3 ? nCtrls : 2;
        Vec_IntClear( vCubeCtrls );
        Vec_IntClear( vCubeVals );
        pModel = Acb_NtkSolveMuxDcControlTargetCube( pNtkF, pNtkG, iPo, vCutObjsG, vMuxSelectorsG, vMuxPoSelIdsG, fSelBranch,
            vDcObjsG, vDcCtrlsG, vDcCtrlIdsG, vCubeCtrls, vCubeVals, fVerbose, &StatusOne, nBranchLimit, nDepth );
        if ( StatusOne == 0 )
        {
            if ( pStatus )
                *pStatus = ACB_XEC_NEQ;
            Vec_IntFree( vCubeCtrls );
            Vec_IntFree( vCubeVals );
            return pModel;
        }
        if ( StatusOne != 1 )
        {
            fUndec = 1;
            if ( fVerbose )
                printf( "HMUX+DC target list: output %d remains UNDECIDED; stopping target-list proof.\n", iPo );
            break;
        }
    }
    if ( pStatus )
        *pStatus = fUndec ? -1 : 1;
    printf( "The HMUX hard outputs are %s by targeted DC-control proving.  ", fUndec ? "UNDECIDED" : "UNSAT" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Vec_IntFree( vCubeCtrls );
    Vec_IntFree( vCubeVals );
    return NULL;
}
int * Acb_NtkSolveDcControlWholeCubes( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, Vec_Int_t * vDcObjsG, Vec_Int_t * vDcCtrlsG, Vec_Int_t * vDcCtrlIdsG, int fVerbose, int * pStatus, int nTotalLimit, int nCubeLimit )
{
    Vec_Int_t * vFTargets = NULL, * vGTargets = NULL, * vCubeCtrls = NULL, * vCubeVals = NULL;
    Vec_Int_t * vDcObjsCube = NULL, * vDcValsCube = NULL;
    Gia_Man_t * pGiaF = NULL, * pGiaG = NULL, * pGiaMiter = NULL, * pGiaCond = NULL, * pTemp = NULL;
    int nCtrls = vDcCtrlsG ? Vec_IntSize(vDcCtrlsG) : 0;
    int nCubes, i, iObj, iCube, StatusCube = -1, StatusAll = 1, * pModel = NULL;
    abctime clk = Abc_Clock();
    abctime clkLimit = nTotalLimit > 0 ? clk + nTotalLimit * CLOCKS_PER_SEC : 0;
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    if ( nCtrls <= 0 || nCtrls > 4 || vDcObjsG == NULL || Vec_IntSize(vDcObjsG) == 0 )
        return NULL;
    nCubes = 1 << nCtrls;
    if ( fVerbose )
        printf( "Trying few-control DC whole-cube proof: outputs = %d. DC nodes = %d. controls = %d. cubes = %d. total limit = %d sec.\n",
            Acb_NtkCoNum(pNtkF), Vec_IntSize(vDcObjsG), nCtrls, nCubes, nTotalLimit );
    vFTargets = Vec_IntAlloc( Acb_NtkCoNum(pNtkF) );
    vGTargets = Vec_IntAlloc( Acb_NtkCoNum(pNtkG) + nCtrls );
    vCubeCtrls = Vec_IntAlloc( nCtrls );
    vCubeVals  = Vec_IntAlloc( nCtrls );
    Acb_NtkForEachCo( pNtkF, iObj, i )
        Vec_IntPush( vFTargets, Acb_ObjFanin(pNtkF, iObj, 0) );
    Acb_NtkForEachCo( pNtkG, iObj, i )
        Vec_IntPush( vGTargets, Acb_ObjFanin(pNtkG, iObj, 0) );
    for ( i = 0; i < nCtrls; i++ )
    {
        Vec_IntPush( vCubeCtrls, i );
        Vec_IntPush( vGTargets, Vec_IntEntry(vDcCtrlsG, i) );
    }
    pGiaF = Acb_NtkGiaDeriveDualTargets( pNtkF, vFTargets );
    for ( iCube = 0; iCube < nCubes; iCube++ )
    {
        int nThisLimit, nRemain;
        Vec_IntClear( vCubeVals );
        for ( i = 0; i < nCtrls; i++ )
            Vec_IntPush( vCubeVals, (iCube >> i) & 1 );
        if ( clkLimit )
        {
            nRemain = (int)((clkLimit - Abc_Clock()) / CLOCKS_PER_SEC);
            if ( nRemain <= 0 )
            {
                StatusAll = -1;
                break;
            }
            nThisLimit = nCubeLimit > 0 ? Abc_MinInt( nCubeLimit, nRemain ) : nRemain;
        }
        else
            nThisLimit = nCubeLimit;
        Acb_NtkCollectDcObjsForCube( vDcObjsG, vDcCtrlIdsG, vCubeCtrls, vCubeVals, &vDcObjsCube, &vDcValsCube );
        pGiaG     = Acb_NtkGiaDeriveDualTargetsBranchValues( pNtkG, vGTargets, vDcObjsCube, vDcValsCube, 0 );
        pGiaMiter = Acb_NtkGiaDeriveMiterWithSecondExtras( pGiaF, pGiaG, nCtrls );
        pGiaCond  = Acb_GiaDeriveCubeConditionMiter( pGiaMiter, Acb_NtkCoNum(pNtkF), vCubeVals );
        if ( Gia_ManAndNum(pGiaCond) > 5000 )
        {
            pTemp = Gia_ManCompress2( pGiaCond, 1, 0 );
            if ( pTemp )
            {
                Gia_ManStop( pGiaCond );
                pGiaCond = pTemp;
                pTemp = NULL;
            }
        }
        if ( fVerbose )
        {
            printf( "Few-control DC whole cube %d/%d:", iCube + 1, nCubes );
            for ( i = 0; i < nCtrls; i++ )
                printf( " c%d=%d", i, Vec_IntEntry(vCubeVals, i) );
            printf( ". And = %d. PO = %d. limit = %d sec.\n", Gia_ManAndNum(pGiaCond), Gia_ManCoNum(pGiaCond), nThisLimit );
        }
        pModel = Acb_NtkSolveCadicalLimit( pGiaCond, 0, fVerbose, &StatusCube, nThisLimit, "few-control DC whole-cube CaDiCaL", 0 );
        Gia_ManStop( pGiaCond );  pGiaCond = NULL;
        Gia_ManStop( pGiaMiter ); pGiaMiter = NULL;
        Gia_ManStop( pGiaG );     pGiaG = NULL;
        Vec_IntFreeP( &vDcObjsCube );
        Vec_IntFreeP( &vDcValsCube );
        if ( StatusCube == 0 )
        {
            StatusAll = 0;
            break;
        }
        if ( StatusCube != 1 )
        {
            StatusAll = -1;
            break;
        }
    }
    if ( pStatus )
        *pStatus = StatusAll;
    if ( StatusAll == 1 )
    {
        printf( "The networks are equivalent by few-control DC whole-cube proof.  " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    else if ( fVerbose )
    {
        printf( "The networks are %s by few-control DC whole-cube proof.  ",
            StatusAll == 0 ? "NOT equivalent" : "UNDECIDED" );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    Vec_IntFreeP( &vFTargets );
    Vec_IntFreeP( &vGTargets );
    Vec_IntFreeP( &vCubeCtrls );
    Vec_IntFreeP( &vCubeVals );
    Vec_IntFreeP( &vDcObjsCube );
    Vec_IntFreeP( &vDcValsCube );
    if ( pGiaF )
        Gia_ManStop( pGiaF );
    if ( pGiaG )
        Gia_ManStop( pGiaG );
    if ( pGiaMiter )
        Gia_ManStop( pGiaMiter );
    if ( pGiaCond )
        Gia_ManStop( pGiaCond );
    if ( pTemp )
        Gia_ManStop( pTemp );
    return pModel;
}
int Acb_NtkObjIsCutCandBasic( Acb_Ntk_t * p, int iObj );
int Acb_NtkObjIsCutCand( Acb_Ntk_t * p, int iObj )
{
    if ( !Acb_NtkObjIsCutCandBasic(p, iObj) )
        return 0;
    if ( Acb_ObjName(p, iObj) <= 0 )
        return 0;
    return 1;
}
int Acb_NtkObjIsCutCandBasic( Acb_Ntk_t * p, int iObj )
{
    Acb_ObjType_t Type;
    if ( iObj <= 0 || Acb_ObjIsCio(p, iObj) )
        return 0;
    Type = Acb_ObjType( p, iObj );
    if ( Type == ABC_OPER_NONE || Type == ABC_OPER_CONST_F || Type == ABC_OPER_CONST_T || Type == ABC_OPER_CONST_X )
        return 0;
    if ( Type == ABC_OPER_TRI || Type == ABC_OPER_BIT_MUX )
        return 0;
    return 1;
}
void Acb_NtkMarkCone_rec( Acb_Ntk_t * p, int iObj, Vec_Int_t * vMarks )
{
    int iFanin, k;
    if ( iObj <= 0 || Vec_IntEntry(vMarks, iObj) )
        return;
    Vec_IntWriteEntry( vMarks, iObj, 1 );
    if ( Acb_ObjIsCio(p, iObj) )
        return;
    Acb_ObjForEachFanin( p, iObj, iFanin, k )
        Acb_NtkMarkCone_rec( p, iFanin, vMarks );
}
int Acb_NtkConeLevel_rec( Acb_Ntk_t * p, int iObj, Vec_Int_t * vMarks, Vec_Int_t * vLevels )
{
    int iFanin, k, Level, LevelMax = 0;
    if ( iObj <= 0 || !Vec_IntEntry(vMarks, iObj) || Acb_ObjIsCio(p, iObj) )
        return 0;
    Level = Vec_IntEntry(vLevels, iObj);
    if ( Level >= 0 )
        return Level;
    Acb_ObjForEachFanin( p, iObj, iFanin, k )
        LevelMax = Abc_MaxInt( LevelMax, Acb_NtkConeLevel_rec(p, iFanin, vMarks, vLevels) );
    Vec_IntWriteEntry( vLevels, iObj, LevelMax + 1 );
    return LevelMax + 1;
}
void Acb_NtkCollectTargetCutCandidates( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, int iPo, Vec_Int_t ** pvCutsF, Vec_Int_t ** pvCutsG, int nLimit )
{
    Vec_Int_t * vNamesInvF = Vec_IntInvert( &pNtkF->vObjName, 0 );
    Vec_Int_t * vMarksF = Vec_IntStart( Acb_NtkObjNumMax(pNtkF) );
    Vec_Int_t * vMarksG = Vec_IntStart( Acb_NtkObjNumMax(pNtkG) );
    Vec_Int_t * vLevelsG = Vec_IntStartFull( Acb_NtkObjNumMax(pNtkG) );
    Vec_Int_t * vCutsF = Vec_IntAlloc( nLimit );
    Vec_Int_t * vCutsG = Vec_IntAlloc( nLimit );
    int iRootF, iRootG, iObjG, iObjF, NameIdF, Level, LevelMax;
    assert( iPo >= 0 && iPo < Acb_NtkCoNum(pNtkF) && iPo < Acb_NtkCoNum(pNtkG) );
    iRootF = Acb_ObjFanin( pNtkF, Acb_NtkCo(pNtkF, iPo), 0 );
    iRootG = Acb_ObjFanin( pNtkG, Acb_NtkCo(pNtkG, iPo), 0 );
    Acb_NtkMarkCone_rec( pNtkF, iRootF, vMarksF );
    Acb_NtkMarkCone_rec( pNtkG, iRootG, vMarksG );
    LevelMax = Acb_NtkConeLevel_rec( pNtkG, iRootG, vMarksG, vLevelsG );
    Acb_NtkForEachNodeReverse( pNtkG, iObjG )
    {
        if ( Vec_IntSize(vCutsG) >= nLimit )
            break;
        if ( !Vec_IntEntry(vMarksG, iObjG) || !Acb_NtkObjIsCutCand(pNtkG, iObjG) )
            continue;
        Level = Vec_IntEntry(vLevelsG, iObjG);
        if ( Level < Abc_MaxInt(2, LevelMax/4) || Level > Abc_MaxInt(3, 3*LevelMax/4) )
            continue;
        NameIdF = Acb_NtkStrId( pNtkF, Acb_ObjNameStr(pNtkG, iObjG) );
        if ( NameIdF <= 0 || NameIdF >= Vec_IntSize(vNamesInvF) )
            continue;
        iObjF = Vec_IntEntry( vNamesInvF, NameIdF );
        if ( iObjF <= 0 || iObjF >= Vec_IntSize(vMarksF) || !Vec_IntEntry(vMarksF, iObjF) )
            continue;
        if ( !Acb_NtkObjIsCutCand(pNtkF, iObjF) )
            continue;
        if ( Acb_ObjType(pNtkF, iObjF) != Acb_ObjType(pNtkG, iObjG) )
            continue;
        if ( Acb_ObjFaninNum(pNtkF, iObjF) != Acb_ObjFaninNum(pNtkG, iObjG) )
            continue;
        Vec_IntPush( vCutsF, iObjF );
        Vec_IntPush( vCutsG, iObjG );
    }
    Vec_IntFree( vNamesInvF );
    Vec_IntFree( vMarksF );
    Vec_IntFree( vMarksG );
    Vec_IntFree( vLevelsG );
    *pvCutsF = vCutsF;
    *pvCutsG = vCutsG;
}
Vec_Int_t * Acb_NtkCollectTargetCutPool( Acb_Ntk_t * p, int iPo, int nLimit )
{
    Vec_Int_t * vMarks = Vec_IntStart( Acb_NtkObjNumMax(p) );
    Vec_Int_t * vLevels = Vec_IntStartFull( Acb_NtkObjNumMax(p) );
    Vec_Int_t * vPool = Vec_IntAlloc( nLimit );
    int iRoot, iObj, Level, LevelMax;
    assert( iPo >= 0 && iPo < Acb_NtkCoNum(p) );
    iRoot = Acb_ObjFanin( p, Acb_NtkCo(p, iPo), 0 );
    Acb_NtkMarkCone_rec( p, iRoot, vMarks );
    LevelMax = Acb_NtkConeLevel_rec( p, iRoot, vMarks, vLevels );
    Acb_NtkForEachNodeReverse( p, iObj )
    {
        if ( Vec_IntSize(vPool) >= nLimit )
            break;
        if ( !Vec_IntEntry(vMarks, iObj) || !Acb_NtkObjIsCutCandBasic(p, iObj) )
            continue;
        Level = Vec_IntEntry(vLevels, iObj);
        if ( Level < Abc_MaxInt(2, LevelMax/5) || Level > Abc_MaxInt(3, 4*LevelMax/5) )
            continue;
        Vec_IntPush( vPool, iObj );
    }
    Vec_IntFree( vMarks );
    Vec_IntFree( vLevels );
    return vPool;
}
int Acb_NtkSimSignaturesEqual( Vec_Wrd_t * vSimsF, Vec_Wrd_t * vSimsG, int nWords, int iCandF, int iCandG )
{
    word * pF0 = Vec_WrdEntryP( vSimsF, (2*iCandF + 0) * nWords );
    word * pF1 = Vec_WrdEntryP( vSimsF, (2*iCandF + 1) * nWords );
    word * pG0 = Vec_WrdEntryP( vSimsG, (2*iCandG + 0) * nWords );
    word * pG1 = Vec_WrdEntryP( vSimsG, (2*iCandG + 1) * nWords );
    int w;
    for ( w = 0; w < nWords; w++ )
        if ( pF0[w] != pG0[w] || pF1[w] != pG1[w] )
            return 0;
    return 1;
}
void Acb_NtkCollectTargetCutCandidatesSim( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, int iPo, Vec_Int_t ** pvCutsF, Vec_Int_t ** pvCutsG, int nLimit, int fVerbose )
{
    Vec_Int_t * vPoolF = Acb_NtkCollectTargetCutPool( pNtkF, iPo, 192 );
    Vec_Int_t * vPoolG = Acb_NtkCollectTargetCutPool( pNtkG, iPo, 384 );
    Vec_Int_t * vCutsF = Vec_IntAlloc( nLimit );
    Vec_Int_t * vCutsG = Vec_IntAlloc( nLimit );
    Vec_Int_t * vUsedF = Vec_IntStart( Vec_IntSize(vPoolF) );
    Gia_Man_t * pGiaF = NULL, * pGiaG = NULL;
    Vec_Wrd_t * vSimsF = NULL, * vSimsG = NULL;
    int i, k, iObjF, iObjG, nWords = 16;
    if ( Vec_IntSize(vPoolF) == 0 || Vec_IntSize(vPoolG) == 0 )
        goto finish;
    pGiaF = Acb_NtkGiaDeriveDualTargets( pNtkF, vPoolF );
    pGiaG = Acb_NtkGiaDeriveDualTargets( pNtkG, vPoolG );
    if ( Gia_ManCiNum(pGiaF) != Gia_ManCiNum(pGiaG) )
        goto finish;
    Abc_Random(1);
    Vec_WrdFreeP( &pGiaF->vSimsPi );
    Vec_WrdFreeP( &pGiaG->vSimsPi );
    pGiaF->vSimsPi = Vec_WrdStartRandom( Gia_ManCiNum(pGiaF) * nWords );
    pGiaG->vSimsPi = Vec_WrdDup( pGiaF->vSimsPi );
    vSimsF = Gia_ManSimPatSim( pGiaF );
    vSimsG = Gia_ManSimPatSim( pGiaG );
    Vec_IntForEachEntry( vPoolG, iObjG, i )
    {
        if ( Vec_IntSize(vCutsG) >= nLimit )
            break;
        Vec_IntForEachEntry( vPoolF, iObjF, k )
        {
            if ( Vec_IntEntry(vUsedF, k) )
                continue;
            if ( Acb_ObjType(pNtkF, iObjF) != Acb_ObjType(pNtkG, iObjG) )
                continue;
            if ( Acb_ObjFaninNum(pNtkF, iObjF) != Acb_ObjFaninNum(pNtkG, iObjG) )
                continue;
            if ( !Acb_NtkSimSignaturesEqual(vSimsF, vSimsG, nWords, k, i) )
                continue;
            Vec_IntPush( vCutsF, iObjF );
            Vec_IntPush( vCutsG, iObjG );
            Vec_IntWriteEntry( vUsedF, k, 1 );
            break;
        }
    }
finish:
    if ( fVerbose )
        printf( "Hard-output simulation cutpoint candidates: F pool = %d. G pool = %d. matched = %d.\n",
            Vec_IntSize(vPoolF), Vec_IntSize(vPoolG), Vec_IntSize(vCutsF) );
    Vec_IntFree( vPoolF );
    Vec_IntFree( vPoolG );
    Vec_IntFree( vUsedF );
    Vec_WrdFreeP( &vSimsF );
    Vec_WrdFreeP( &vSimsG );
    if ( pGiaF )
    {
        Vec_WrdFreeP( &pGiaF->vSimsPi );
        Gia_ManStop( pGiaF );
    }
    if ( pGiaG )
    {
        Vec_WrdFreeP( &pGiaG->vSimsPi );
        Gia_ManStop( pGiaG );
    }
    *pvCutsF = vCutsF;
    *pvCutsG = vCutsG;
}
int * Acb_NtkSolveTargetCutpoints( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, int iPo, int fVerbose, int * pStatus, int nSatTimeLimit )
{
    Vec_Int_t * vCandF = NULL, * vCandG = NULL, * vProofF = Vec_IntAlloc( 64 ), * vProofG = Vec_IntAlloc( 64 );
    Vec_Int_t * vOneF = Vec_IntAlloc( 1 ), * vOneG = Vec_IntAlloc( 1 ), * vTargetF = Vec_IntAlloc( 1 ), * vTargetG = Vec_IntAlloc( 1 );
    Gia_Man_t * pGiaF = NULL, * pGiaG = NULL, * pGiaMiter = NULL, * pTemp = NULL;
    int i, iObjF, iObjG, StatusOne = -1, StatusTop = -1, nTried = 0, nSat = 0, nUndec = 0;
    int * pModel = NULL;
    abctime clk = Abc_Clock(), clkLimit = nSatTimeLimit > 0 ? Abc_Clock() + nSatTimeLimit * CLOCKS_PER_SEC : 0;
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    if ( iPo < 0 || iPo >= Acb_NtkCoNum(pNtkF) || iPo >= Acb_NtkCoNum(pNtkG) )
        goto cleanup;
    Acb_NtkCollectTargetCutCandidates( pNtkF, pNtkG, iPo, &vCandF, &vCandG, 96 );
    if ( Vec_IntSize(vCandF) == 0 )
    {
        Vec_IntFreeP( &vCandF );
        Vec_IntFreeP( &vCandG );
        Acb_NtkCollectTargetCutCandidatesSim( pNtkF, pNtkG, iPo, &vCandF, &vCandG, 96, fVerbose );
    }
    if ( fVerbose )
        printf( "Trying hard-output internal cutpoints: output = %d. candidates = %d.\n", iPo, Vec_IntSize(vCandF) );
    Vec_IntForEachEntryTwo( vCandF, vCandG, iObjF, iObjG, i )
    {
        if ( clkLimit && Abc_Clock() > clkLimit )
            break;
        Vec_IntClear( vOneF );
        Vec_IntClear( vOneG );
        Vec_IntPush( vOneF, iObjF );
        Vec_IntPush( vOneG, iObjG );
        pGiaF = Acb_NtkGiaDeriveDualTargets( pNtkF, vOneF );
        pGiaG = Acb_NtkGiaDeriveDualTargets( pNtkG, vOneG );
        pGiaMiter = Acb_NtkGiaDeriveMiter( pGiaF, pGiaG, 2 );
        if ( Gia_ManAndNum(pGiaMiter) > 5000 )
        {
            pTemp = Gia_ManCompress2( pGiaMiter, 0, 0 );
            if ( pTemp )
            {
                Gia_ManStop( pGiaMiter );
                pGiaMiter = pTemp;
                pTemp = NULL;
            }
        }
        nTried++;
        StatusOne = -1;
        pModel = Acb_NtkSolveCadicalPoSweepLabel( pGiaMiter, fVerbose && nTried <= 8, &StatusOne, 8, 100000, "Hard-output cutpoint proof", 0 );
        if ( pModel )
        {
            ABC_FREE( pModel );
            pModel = NULL;
        }
        if ( StatusOne == 1 )
        {
            Vec_IntPush( vProofF, iObjF );
            Vec_IntPush( vProofG, iObjG );
        }
        else if ( StatusOne == 0 )
            nSat++;
        else
            nUndec++;
        Gia_ManStop( pGiaF );
        Gia_ManStop( pGiaG );
        Gia_ManStop( pGiaMiter );
        pGiaF = pGiaG = pGiaMiter = NULL;
        if ( Vec_IntSize(vProofF) >= 48 )
            break;
    }
    if ( fVerbose )
        printf( "Hard-output cutpoints: tried = %d. proven = %d. bad = %d. undecided = %d.\n",
            nTried, Vec_IntSize(vProofF), nSat, nUndec );
    if ( Vec_IntSize(vProofF) == 0 )
        goto cleanup;
    Vec_IntPush( vTargetF, Acb_ObjFanin(pNtkF, Acb_NtkCo(pNtkF, iPo), 0) );
    Vec_IntPush( vTargetG, Acb_ObjFanin(pNtkG, Acb_NtkCo(pNtkG, iPo), 0) );
    pGiaF = Acb_NtkGiaDeriveDualTargetsCutLeaves( pNtkF, vTargetF, vProofF );
    pGiaG = Acb_NtkGiaDeriveDualTargetsCutLeaves( pNtkG, vTargetG, vProofG );
    pGiaMiter = Acb_NtkGiaDeriveMiter( pGiaF, pGiaG, 2 );
    if ( Gia_ManAndNum(pGiaMiter) > 5000 )
    {
        pTemp = Gia_ManCompress2( pGiaMiter, 1, 0 );
        if ( pTemp )
        {
            Gia_ManStop( pGiaMiter );
            pGiaMiter = pTemp;
            pTemp = NULL;
        }
    }
    if ( fVerbose )
        printf( "Hard-output top cutpoint miter: output = %d. cutpoints = %d. And = %d. PO = %d.\n",
            iPo, Vec_IntSize(vProofF), Gia_ManAndNum(pGiaMiter), Gia_ManCoNum(pGiaMiter) );
    pModel = Acb_NtkSolveCadicalPoSweepLabel( pGiaMiter, fVerbose, &StatusTop, nSatTimeLimit, 250000, "Hard-output top cutpoint miter", 0 );
    if ( StatusTop == 1 )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_EQ;
        printf( "The hard output %d is UNSAT by internal cutpoint abstraction.  ", iPo );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    else
    {
        if ( pModel )
        {
            ABC_FREE( pModel );
            pModel = NULL;
        }
        if ( fVerbose )
            printf( "Hard-output cutpoint abstraction did not prove output %d; SAT on abstraction may be spurious.\n", iPo );
    }
cleanup:
    Vec_IntFreeP( &vCandF );
    Vec_IntFreeP( &vCandG );
    Vec_IntFree( vProofF );
    Vec_IntFree( vProofG );
    Vec_IntFree( vOneF );
    Vec_IntFree( vOneG );
    Vec_IntFree( vTargetF );
    Vec_IntFree( vTargetG );
    if ( pGiaF )
        Gia_ManStop( pGiaF );
    if ( pGiaG )
        Gia_ManStop( pGiaG );
    if ( pGiaMiter )
        Gia_ManStop( pGiaMiter );
    if ( pTemp )
        Gia_ManStop( pTemp );
    return pModel;
}
int * Acb_NtkSolveTargetCutpointList( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, Vec_Int_t * vHardPos, int fVerbose, int * pStatus, int nTotalLimit, int nPoLimit )
{
    int i, iPo, StatusOne = -1, fUndec = 0;
    int * pModel = NULL;
    abctime clk = Abc_Clock();
    abctime clkLimit = nTotalLimit > 0 ? clk + nTotalLimit * CLOCKS_PER_SEC : 0;
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    if ( vHardPos == NULL || Vec_IntSize(vHardPos) == 0 )
        return NULL;
    if ( fVerbose )
        printf( "Trying hard-output cutpoint abstraction for %d collected outputs.\n", Vec_IntSize(vHardPos) );
    Vec_IntForEachEntry( vHardPos, iPo, i )
    {
        int nLimit = nPoLimit;
        if ( clkLimit )
        {
            int nRemain = (int)((clkLimit - Abc_Clock()) / CLOCKS_PER_SEC);
            if ( nRemain <= 0 )
            {
                fUndec = 1;
                break;
            }
            nLimit = nPoLimit > 0 ? Abc_MinInt( nPoLimit, nRemain ) : nRemain;
        }
        StatusOne = -1;
        pModel = Acb_NtkSolveTargetCutpoints( pNtkF, pNtkG, iPo, fVerbose, &StatusOne, nLimit );
        if ( StatusOne == 0 )
        {
            if ( pStatus )
                *pStatus = ACB_XEC_NEQ;
            return pModel;
        }
        if ( pModel )
        {
            ABC_FREE( pModel );
            pModel = NULL;
        }
        if ( StatusOne != 1 )
        {
            fUndec = 1;
            if ( fVerbose )
                printf( "Hard-output cutpoint abstraction: output %d remains UNDECIDED; stopping list proof.\n", iPo );
            break;
        }
    }
    if ( pStatus )
        *pStatus = fUndec ? -1 : 1;
    printf( "The collected hard outputs are %s by cutpoint abstraction.  ", fUndec ? "UNDECIDED" : "UNSAT" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return NULL;
}
int * Acb_NtkSolveCadicalPoSweepLabel( Gia_Man_t * p, int fVerbose, int * pStatus, int nSatTimeLimit, int nPoConfLimit, char * pLabel, int fStopOnUndec )
{
    Gia_Man_t * pGiaCnf = p;
    Aig_Man_t * pMan = NULL;
    Cnf_Dat_t * pCnf = NULL;
    cadical_solver * pSat = NULL;
    Acb_SplitPoOrder_t * pOrder = NULL;
    int i, k, Lit, Ret, Status, * pModel = NULL;
    int nSat = 0, nUnsat = 0, nUndec = 0;
    int fManyOutputs = Gia_ManCoNum(p) > 64;
    int nMaxManyUndec = fManyOutputs ? 12 : Gia_ManCoNum(p);
    abctime clk = Abc_Clock();
    (void)nSatTimeLimit;
    if ( Gia_ManCoNum(p) == 0 )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_EQ;
        return NULL;
    }
    pMan = Gia_ManToAig( pGiaCnf, 0 );
    pCnf = pMan ? Cnf_Derive( pMan, Aig_ManCoNum(pMan) ) : NULL;
    pSat = pCnf ? cadical_solver_new() : NULL;
    if ( pCnf == NULL || pSat == NULL )
        goto cleanup;
    if ( !Acb_CnfWriteIntoCadical( pSat, pCnf ) )
        goto cleanup;
    pOrder = ABC_ALLOC( Acb_SplitPoOrder_t, Gia_ManCoNum(p) );
    Acb_NtkSortSplitOutputs( p, pOrder );
    if ( fVerbose )
        printf( "%s: smallest cone %d ANDs, largest cone %d ANDs.\n",
            pLabel, pOrder[0].nAnds, pOrder[Gia_ManCoNum(p)-1].nAnds );
    for ( k = 0; k < Gia_ManCoNum(p); k++ )
    {
        i = pOrder[k].iPo;
        Ret = Acb_CnfCoDriverLit( pCnf, i, &Lit );
        if ( fVerbose )
            printf( "%s: trying output %d (%d/%d), cone = %d ANDs.\n",
                pLabel, i, k + 1, Gia_ManCoNum(p), pOrder[k].nAnds );
        if ( Ret == -2 )
        {
            nUndec++;
            if ( fVerbose )
                printf( "%s: output %d UNDECIDED because its CNF driver is unmapped.\n", pLabel, i );
            if ( fStopOnUndec )
                break;
            continue;
        }
        if ( Ret == -1 )
        {
            nUnsat++;
            if ( fVerbose )
                printf( "%s: output %d UNSAT because it is constant 0.\n", pLabel, i );
            continue;
        }
        if ( Ret == 0 )
        {
            nSat++;
            pModel = ABC_CALLOC( int, Aig_ManCiNum(pMan) );
            if ( pStatus )
                *pStatus = ACB_XEC_NEQ;
            printf( "%s found SAT on output %d.  ", pLabel, pOrder[k].iPo );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            goto cleanup;
        }
        Status = cadical_solver_solve( pSat, &Lit, &Lit + 1, (ABC_INT64_T)nPoConfLimit, 0, 0, 0 );
        if ( Status == 1 )
        {
            Aig_Obj_t * pObjCi;
            nSat++;
            pModel = ABC_ALLOC( int, Aig_ManCiNum(pMan) );
            Aig_ManForEachCi( pMan, pObjCi, i )
                pModel[i] = cadical_solver_get_var_value( pSat, pCnf->pVarNums[pObjCi->Id] );
            if ( pStatus )
                *pStatus = ACB_XEC_NEQ;
            printf( "%s found SAT on output %d.  ", pLabel, pOrder[k].iPo );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            goto cleanup;
        }
        if ( Status == -1 )
        {
            nUnsat++;
            if ( fVerbose )
                printf( "%s: output %d UNSAT. conflicts = %d. learned = %d.\n",
                    pLabel, i, cadical_solver_nconflicts(pSat), cadical_solver_nlearned(pSat) );
        }
        else
        {
            nUndec++;
            if ( fVerbose )
                printf( "%s: output %d UNDECIDED. conflicts = %d. learned = %d.\n",
                    pLabel, i, cadical_solver_nconflicts(pSat), cadical_solver_nlearned(pSat) );
            if ( fStopOnUndec )
            {
                if ( fVerbose )
                    printf( "%s: stopping after first UNDECIDED output because this proof needs every output UNSAT.\n", pLabel );
                break;
            }
            if ( (fManyOutputs || Gia_ManCoNum(p) > 16) && k + 1 < Gia_ManCoNum(p) )
            {
                cadical_solver_delete( pSat );
                pSat = cadical_solver_new();
                if ( pSat == NULL || !Acb_CnfWriteIntoCadical( pSat, pCnf ) )
                    goto cleanup;
                if ( fVerbose )
                    printf( "%s: reset solver after undecided output %d to avoid carrying unrelated learned clauses.\n",
                        pLabel, i );
            }
            if ( fManyOutputs && nUndec >= nMaxManyUndec && nUnsat == 0 )
            {
                if ( fVerbose )
                    printf( "%s: stopping early after %d many-output UNDECIDED probes; moving to next XEC method.\n",
                        pLabel, nUndec );
                break;
            }
        }
    }
    if ( pStatus )
        *pStatus = nUndec ? -1 : 1;
    printf( "%s is %s.  ", pLabel, nUndec ? "UNDECIDED" : "UNSAT" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
cleanup:
    if ( fVerbose && pSat )
        printf( "%s stats: SAT = %d. UNSAT = %d. UNDEC = %d. conflicts = %d. learned = %d.\n",
            pLabel, nSat, nUnsat, nUndec, cadical_solver_nconflicts(pSat), cadical_solver_nlearned(pSat) );
    if ( pOrder )
        ABC_FREE( pOrder );
    if ( pSat )
        cadical_solver_delete( pSat );
    if ( pCnf )
        Cnf_DataFree( pCnf );
    if ( pMan )
        Aig_ManStop( pMan );
    return pModel;
}
void Acb_NtkSortSplitOutputsLimit( Gia_Man_t * p, Acb_SplitPoOrder_t * pOrder, int nPos )
{
    Gia_Obj_t * pObj;
    Acb_SplitPoOrder_t Temp;
    int i, k, iObj;
    assert( nPos > 0 && nPos <= Gia_ManCoNum(p) );
    for ( i = 0; i < nPos; i++ )
    {
        pObj = Gia_ManCo( p, i );
        iObj = Gia_ObjId( p, pObj );
        pOrder[i].iPo = i;
        pOrder[i].nAnds = Gia_ManConeSize( p, &iObj, 1 );
    }
    for ( i = 1; i < nPos; i++ )
    {
        Temp = pOrder[i];
        for ( k = i; k > 0 && pOrder[k-1].nAnds > Temp.nAnds; k-- )
            pOrder[k] = pOrder[k-1];
        pOrder[k] = Temp;
    }
}
void Acb_NtkSortSplitOutputs( Gia_Man_t * p, Acb_SplitPoOrder_t * pOrder )
{
    Acb_NtkSortSplitOutputsLimit( p, pOrder, Gia_ManCoNum(p) );
}
int Acb_GiaRequiredLiteralContradiction( Gia_Man_t * p, int iPo, int fVerbose )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 1024 );
    Vec_Int_t * vAssign = Vec_IntStartFull( Gia_ManObjNum(p) );
    Gia_Obj_t * pObj;
    int Lit, Var, Sign, Val, nSeen = 0, Ret = ACB_XEC_UNDEC;
    if ( iPo < 0 || iPo >= Gia_ManCoNum(p) )
    {
        Vec_IntFree( vStack );
        Vec_IntFree( vAssign );
        return Ret;
    }
    Vec_IntPush( vStack, Gia_ObjFaninLit0p(p, Gia_ManCo(p, iPo)) );
    while ( Vec_IntSize(vStack) > 0 )
    {
        Lit = Vec_IntPop( vStack );
        Var = Abc_Lit2Var(Lit);
        Sign = Abc_LitIsCompl(Lit);
        if ( Var == 0 )
        {
            if ( Sign == 0 )
            {
                Ret = ACB_XEC_EQ;
                break;
            }
            continue;
        }
        Val = Vec_IntEntry( vAssign, Var );
        if ( Val >= 0 )
        {
            if ( Val != (Sign ? 0 : 1) )
            {
                Ret = ACB_XEC_EQ;
                break;
            }
            continue;
        }
        Vec_IntWriteEntry( vAssign, Var, Sign ? 0 : 1 );
        nSeen++;
        pObj = Gia_ManObj( p, Var );
        if ( !Sign && Gia_ObjIsAnd(pObj) )
        {
            Vec_IntPush( vStack, Gia_ObjFaninLit0(pObj, Var) );
            Vec_IntPush( vStack, Gia_ObjFaninLit1(pObj, Var) );
        }
        if ( nSeen > 200000 )
            break;
    }
    if ( fVerbose )
        printf( "Required-literal structural proof: output %d %s. required literals = %d.\n",
            iPo, Ret == ACB_XEC_EQ ? "UNSAT" : "inconclusive", nSeen );
    Vec_IntFree( vStack );
    Vec_IntFree( vAssign );
    return Ret;
}
Vec_Int_t * Acb_GiaCollectRequiredLiteralAssigns( Gia_Man_t * p, int iPo, int fVerbose, int * pStatus );
int Acb_GiaRequiredLiteralUnitProof( Gia_Man_t * p, int iPo, int fVerbose, int nSatTimeLimit )
{
    Vec_Int_t * vAssign = NULL, * vReq = NULL;
    Gia_Obj_t * pObj;
    int i, Val, Status = ACB_XEC_UNDEC, nReq = 0;
    if ( p == NULL || iPo < 0 || iPo >= Gia_ManCoNum(p) || Gia_ManAndNum(p) > 30000 )
        return ACB_XEC_UNDEC;
    vAssign = Acb_GiaCollectRequiredLiteralAssigns( p, iPo, 0, &Status );
    if ( Status == ACB_XEC_EQ )
    {
        Vec_IntFreeP( &vAssign );
        return Status;
    }
    if ( vAssign == NULL )
        return ACB_XEC_UNDEC;
    vReq = Vec_IntAlloc( 100 );
    Gia_ManForEachObj1( p, pObj, i )
    {
        Val = Vec_IntEntry( vAssign, i );
        if ( Val < 0 )
            continue;
        Vec_IntPush( vReq, Abc_Var2Lit(i, Val ? 0 : 1) );
        nReq++;
    }
    if ( nReq < 2 || nReq > 512 )
        Status = ACB_XEC_UNDEC;
    else
    {
        Status = Acb_GiaSolveObligationListUnit( p, vReq, 0, nSatTimeLimit, NULL );
        if ( fVerbose )
            printf( "Required-literal unit proof: output %d %s. required literals = %d.\n",
                iPo, Status == ACB_XEC_EQ ? "UNSAT" : "inconclusive", nReq );
    }
    Vec_IntFreeP( &vAssign );
    Vec_IntFreeP( &vReq );
    return Status;
}
Vec_Int_t * Acb_GiaCollectRequiredLiteralAssigns( Gia_Man_t * p, int iPo, int fVerbose, int * pStatus )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 1024 );
    Vec_Int_t * vAssign = Vec_IntStartFull( Gia_ManObjNum(p) );
    Gia_Obj_t * pObj;
    int Lit, Var, Sign, Val, nSeen = 0;
    *pStatus = ACB_XEC_UNDEC;
    if ( iPo < 0 || iPo >= Gia_ManCoNum(p) )
    {
        Vec_IntFree( vStack );
        return vAssign;
    }
    Vec_IntPush( vStack, Gia_ObjFaninLit0p(p, Gia_ManCo(p, iPo)) );
    while ( Vec_IntSize(vStack) > 0 )
    {
        Lit = Vec_IntPop( vStack );
        Var = Abc_Lit2Var(Lit);
        Sign = Abc_LitIsCompl(Lit);
        if ( Var == 0 )
        {
            if ( Sign == 0 )
            {
                *pStatus = ACB_XEC_EQ;
                break;
            }
            continue;
        }
        Val = Vec_IntEntry( vAssign, Var );
        if ( Val >= 0 )
        {
            if ( Val != (Sign ? 0 : 1) )
            {
                *pStatus = ACB_XEC_EQ;
                break;
            }
            continue;
        }
        Vec_IntWriteEntry( vAssign, Var, Sign ? 0 : 1 );
        nSeen++;
        pObj = Gia_ManObj( p, Var );
        if ( !Sign && Gia_ObjIsAnd(pObj) )
        {
            Vec_IntPush( vStack, Gia_ObjFaninLit0(pObj, Var) );
            Vec_IntPush( vStack, Gia_ObjFaninLit1(pObj, Var) );
        }
        if ( nSeen > 200000 )
            break;
    }
    if ( fVerbose && *pStatus == ACB_XEC_EQ )
        printf( "Required-literal cofactor: output %d is UNSAT before cofactoring. required literals = %d.\n", iPo, nSeen );
    Vec_IntFree( vStack );
    return vAssign;
}
static int Acb_XecRemainingTimeLimit( abctime clkLimit, int nCap )
{
    if ( clkLimit == 0 )
        return nCap;
    if ( Abc_Clock() >= clkLimit )
        return 0;
    return Abc_MinInt( nCap, (int)((clkLimit - Abc_Clock()) / CLOCKS_PER_SEC) );
}
static int Acb_XecLocalConeStatus( int nSat, int nUnsat, int nSkipUnsat, int nUndec, int nOuts )
{
    if ( nSat )
        return ACB_XEC_NEQ;
    if ( nUndec == 0 )
        return nUnsat + nSkipUnsat == nOuts ? ACB_XEC_EQ : ACB_XEC_UNDEC;
    if ( nUndec == 1 && nUnsat + nSkipUnsat == nOuts - 1 )
        return ACB_XEC_ONE_HARD;
    if ( nUnsat + nSkipUnsat + nUndec == nOuts && nUndec > 1 )
        return ACB_XEC_MANY_HARD;
    return ACB_XEC_UNDEC;
}
static int Acb_XecLocalConeKeepSweeping( int fQuickMany, int fMediumSweep, int fResumeSweep, int nUndec, int nMaxUndec )
{
    if ( nUndec >= nMaxUndec )
        return 0;
    return fQuickMany || fMediumSweep || fResumeSweep;
}
static Gia_Man_t * Acb_XecLocalConePrepare( Gia_Man_t * p, int iPo, Vec_Int_t ** pvSuppMap, Acb_XecCtx_t * pCtx, int fVerbose )
{
    Gia_Man_t * pOne, * pTemp;
    Vec_Int_t * vSuppMap = Vec_IntAlloc( 1000 );
    pOne = Acb_GiaDupOnePoTrimmed( p, iPo, vSuppMap );
    if ( pOne == NULL )
    {
        Vec_IntFree( vSuppMap );
        *pvSuppMap = NULL;
        return NULL;
    }
    if ( Gia_ManAndNum(pOne) > pCtx->Pars.nLocalConeCompressAndMin )
    {
        pTemp = Gia_ManCompress2( pOne, 1, 0 );
        if ( pTemp )
        {
            Gia_ManStop( pOne );
            pOne = pTemp;
        }
    }
    if ( Vec_IntSize(vSuppMap) <= 64 && Gia_ManAndNum(pOne) <= 8000 )
    {
        pTemp = Acb_XecGiaSmallConeXorRewrite( pOne, fVerbose );
        if ( pTemp )
        {
            Gia_ManStop( pOne );
            pOne = pTemp;
        }
    }
    *pvSuppMap = vSuppMap;
    return pOne;
}
static int * Acb_XecLocalConeExpandModel( Gia_Man_t * p, Gia_Man_t * pOne, Vec_Int_t * vSuppMap, int * pModel )
{
    int * pModelFull = NULL;
    int i, iObj;
    if ( pModel == NULL )
        return NULL;
    if ( Vec_IntSize(vSuppMap) != Gia_ManCiNum(pOne) )
    {
        ABC_FREE( pModel );
        return NULL;
    }
    pModelFull = ABC_CALLOC( int, Gia_ManCiNum(p) );
    Vec_IntForEachEntry( vSuppMap, iObj, i )
        if ( Gia_ObjIsCi(Gia_ManObj(p, iObj)) )
            pModelFull[Gia_ObjCioId(Gia_ManObj(p, iObj))] = pModel[i];
    ABC_FREE( pModel );
    return pModelFull;
}
static int Acb_XecLocalConeProof( Gia_Man_t * pOne, int nSuppSize, int nLimit, abctime clkLimit, int fVerbose, int ** ppModel )
{
    int Status = ACB_XEC_UNDEC;
    int nExhLimit, nFrontLimit;
    *ppModel = NULL;
    if ( Gia_ManCoNum(pOne) == 1 && Gia_ManAndNum(pOne) > 0 &&
         (Gia_ManAndNum(pOne) >= 1000 || nSuppSize >= 32) )
    {
        int nSimWords = Gia_ManAndNum(pOne) <= 5000 ? 256 : 64;
        *ppModel = Acb_GiaFindOnePoSimCex( pOne, nSimWords, fVerbose, "Local-cone hard-output" );
        if ( *ppModel )
            return ACB_XEC_NEQ;
    }
    if ( Gia_ManAndNum(pOne) <= 8000 )
        Status = Acb_GiaRequiredLiteralContradiction( pOne, 0, fVerbose );
    if ( Status == ACB_XEC_UNDEC && Gia_ManAndNum(pOne) <= 8000 && nSuppSize >= 40 && nSuppSize <= 64 )
        Status = Acb_GiaRequiredLiteralUnitProof( pOne, 0, fVerbose, Abc_MinInt(nLimit, 120) );
    if ( Status == ACB_XEC_UNDEC && Gia_ManAndNum(pOne) < 5000 && nSuppSize >= 32 && nSuppSize <= 64 )
    {
        nFrontLimit = Acb_XecRemainingTimeLimit( clkLimit, nLimit > 120 ? 180 : 90 );
        if ( nFrontLimit >= 20 )
            Status = Acb_GiaSolveSmallConeInternalFrontier( pOne, fVerbose, nFrontLimit );
    }
    if ( Status == ACB_XEC_UNDEC && Gia_ManAndNum(pOne) <= 5000 )
    {
        nExhLimit = Acb_XecRemainingTimeLimit( clkLimit, 600 );
        if ( nExhLimit >= 30 )
            Status = Acb_XecGiaSolveSmallConeExhaustive( pOne, fVerbose, nExhLimit );
    }
    if ( Status == ACB_XEC_UNDEC )
        *ppModel = Acb_NtkSolveCadicalLimit( pOne, 0, 0, &Status, nLimit, NULL, 0 );
    return Status;
}
int * Acb_NtkSolveCadicalLocalConeSweepSkipCtx( Gia_Man_t * p, int fVerbose, int * pStatus, int nSatTimeLimit, int nPoTimeLimit, Vec_Int_t * vSkipUnsat, Acb_XecCtx_t * pCtx )
{
    Acb_SplitPoOrder_t * pOrder;
    int i, k, StatusOne, StatusFinal, nSat = 0, nUnsat = 0, nUndec = 0, iLastUndec = -1;
    int nSkipUnsat = vSkipUnsat ? Vec_IntSize(vSkipUnsat) : 0;
    int fDisableQuickMany = nPoTimeLimit < 0;
    int fResumeSweep = vSkipUnsat != NULL;
    int fStopAfterFirstHard, fMediumSweep, fQuickMany, nProbeLimit, nHardProbeLimit, nMaxUndec;
    int * pModel = NULL;
    abctime clk = Abc_Clock();
    abctime clkLimit = nSatTimeLimit > 0 ? clk + nSatTimeLimit * CLOCKS_PER_SEC : 0;
    assert( pCtx != NULL );
    Acb_XecCtxResetLocalSweep( pCtx );
    if ( pStatus )
        *pStatus = ACB_XEC_UNDEC;
    if ( Gia_ManCoNum(p) == 0 )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_EQ;
        return NULL;
    }
    if ( fDisableQuickMany )
        nPoTimeLimit = -nPoTimeLimit;
    fStopAfterFirstHard = pCtx->Pars.nLocalMediumPoMin == ABC_INFINITY;
    fMediumSweep = !fStopAfterFirstHard && Gia_ManCoNum(p) > pCtx->Pars.nLocalMediumPoMin && Gia_ManCoNum(p) <= pCtx->Pars.nLocalMediumPoMax;
    fQuickMany = !fStopAfterFirstHard && !fDisableQuickMany && Gia_ManCoNum(p) > pCtx->Pars.nLocalManyPoThreshold;
    nMaxUndec = fStopAfterFirstHard ? 1 : (fResumeSweep ? Gia_ManCoNum(p) : (fQuickMany ? pCtx->Pars.nLocalQuickMaxUndec : (fMediumSweep ? Gia_ManCoNum(p) : 1)));
    nProbeLimit = nPoTimeLimit;
    if ( fQuickMany )
        nProbeLimit = nPoTimeLimit > 0 ? Abc_MinInt( nPoTimeLimit, pCtx->Pars.nLocalQuickPoSec ) : pCtx->Pars.nLocalQuickPoSec;
    else if ( fMediumSweep )
        nProbeLimit = nPoTimeLimit > 0 ? Abc_MinInt( nPoTimeLimit, pCtx->Pars.nLocalMediumPoSec ) : pCtx->Pars.nLocalMediumPoSec;
    nHardProbeLimit = fResumeSweep ? nPoTimeLimit : (fQuickMany ? pCtx->Pars.nLocalQuickPoSec : (fMediumSweep ? pCtx->Pars.nLocalMediumHardPoSec : nPoTimeLimit));
    pOrder = ABC_ALLOC( Acb_SplitPoOrder_t, Gia_ManCoNum(p) );
    Acb_NtkSortSplitOutputs( p, pOrder );
    if ( fVerbose )
        printf( "Local-cone CaDiCaL sweep: outputs = %d. skip = %d. smallest cone %d ANDs, largest cone %d ANDs. total limit = %d sec, per-output limit = %d sec%s.\n",
            Gia_ManCoNum(p), nSkipUnsat, pOrder[0].nAnds, pOrder[Gia_ManCoNum(p)-1].nAnds, nSatTimeLimit, nProbeLimit,
            fQuickMany ? " (SAT-hunting quick probe for many-output miter)" : "" );
    for ( k = 0; k < Gia_ManCoNum(p); k++ )
    {
        Gia_Man_t * pOne;
        Vec_Int_t * vSuppMap = NULL;
        abctime clkOut = Abc_Clock();
        int nBaseLimit = nUndec > 0 ? nHardProbeLimit : nProbeLimit;
        int nLimit = Acb_XecRemainingTimeLimit( clkLimit, nBaseLimit );
        int nSuppSize;
        i = pOrder[k].iPo;
        if ( vSkipUnsat && Vec_IntFind(vSkipUnsat, i) >= 0 )
        {
            if ( fVerbose )
                printf( "Local-cone CaDiCaL: skipping output %d because it is already proven UNSAT.\n", i );
            continue;
        }
        if ( clkLimit && nLimit <= 0 )
        {
            nUndec++;
            iLastUndec = i;
            Vec_IntPushUnique( pCtx->vLastHardPos, i );
            break;
        }
        pOne = Acb_XecLocalConePrepare( p, i, &vSuppMap, pCtx, fVerbose );
        if ( pOne == NULL )
        {
            nUndec++;
            iLastUndec = i;
            Vec_IntPushUnique( pCtx->vLastHardPos, i );
            break;
        }
        nSuppSize = Vec_IntSize( vSuppMap );
        if ( Gia_ManCiNum(p) <= 64 && Gia_ManCoNum(p) >= 16 && Gia_ManCoNum(p) <= 64 &&
             nUnsat >= 3 && nSuppSize >= 40 && nSuppSize <= 56 &&
             Gia_ManAndNum(pOne) <= 5000 && nLimit <= 120 )
            nLimit = Abc_MaxInt( nLimit, Acb_XecRemainingTimeLimit( clkLimit, nUnsat >= 4 ? 420 : 180 ) );
        if ( fVerbose )
            printf( "Local-cone CaDiCaL: output %d (%d/%d), cone = %d ANDs, support = %d/%d PIs, limit = %d sec.\n",
                i, k + 1, Gia_ManCoNum(p), Gia_ManAndNum(pOne), nSuppSize, Gia_ManCiNum(p), nLimit );
        StatusOne = Acb_XecLocalConeProof( pOne, nSuppSize, nLimit, clkLimit, fVerbose && (nUndec > 0 || nSuppSize >= 40), &pModel );
        if ( StatusOne == ACB_XEC_NEQ )
        {
            nSat++;
            pModel = Acb_XecLocalConeExpandModel( p, pOne, vSuppMap, pModel );
            if ( fVerbose )
            {
                printf( "Local-cone CaDiCaL: output %d SAT.  ", i );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clkOut );
            }
            Gia_ManStop( pOne );
            Vec_IntFree( vSuppMap );
            break;
        }
        if ( pModel )
        {
            ABC_FREE( pModel );
            pModel = NULL;
        }
        if ( StatusOne == ACB_XEC_EQ )
        {
            nUnsat++;
            Vec_IntPushUnique( pCtx->vLastProvenPos, i );
            if ( fVerbose )
            {
                printf( "Local-cone CaDiCaL: output %d UNSAT.  ", i );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clkOut );
            }
            Gia_ManStop( pOne );
            Vec_IntFree( vSuppMap );
            continue;
        }
        nUndec++;
        iLastUndec = i;
        Vec_IntPushUnique( pCtx->vLastHardPos, i );
        if ( fVerbose )
        {
            printf( "Local-cone CaDiCaL: output %d UNDECIDED.  ", i );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clkOut );
        }
        Gia_ManStop( pOne );
        Vec_IntFree( vSuppMap );
        if ( Acb_XecLocalConeKeepSweeping( fQuickMany, fMediumSweep, fResumeSweep, nUndec, nMaxUndec ) )
        {
            if ( fVerbose )
                printf( "Local-cone CaDiCaL: continuing after hard output %d; undecided probes = %d/%d.\n",
                    i, nUndec, nMaxUndec );
            continue;
        }
        break;
    }
    StatusFinal = Acb_XecLocalConeStatus( nSat, nUnsat, nSkipUnsat, nUndec, Gia_ManCoNum(p) );
    if ( StatusFinal == ACB_XEC_ONE_HARD || StatusFinal == ACB_XEC_MANY_HARD )
        pCtx->LastHardPo = iLastUndec;
    if ( pStatus )
        *pStatus = StatusFinal;
    printf( "The networks are %s by local-cone CaDiCaL sweep.  ",
        nSat ? "NOT equivalent" : (nUndec ? "UNDECIDED" : "equivalent") );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    if ( fVerbose )
    {
        printf( "Local-cone CaDiCaL stats: SAT = %d. UNSAT = %d. SKIP = %d. UNDEC = %d.\n", nSat, nUnsat, nSkipUnsat, nUndec );
        if ( StatusFinal == ACB_XEC_ONE_HARD )
            printf( "Local-cone CaDiCaL: only output %d remains hard; whole-miter CaDiCaL would duplicate this cone.\n", iLastUndec );
        else if ( StatusFinal == ACB_XEC_MANY_HARD )
            printf( "Local-cone CaDiCaL: %d outputs remain hard after complete short-probe sweep.\n", nUndec );
    }
    ABC_FREE( pOrder );
    return pModel;
}
int * Acb_NtkSolveCadicalOdc( Gia_Man_t * p, int fVerbose, int * pStatus )
{
    Gia_Man_t * pOne;
    Acb_SplitPoOrder_t * pOrder;
    int i, k, Status = -1, fOneUndef = 0, * pModel = NULL;
    int nConeTimeLimit = 5;
    int nTotalTimeLimit = 60;
    abctime clk = Abc_Clock();
    if ( Gia_ManCoNum(p) == 0 )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_EQ;
        printf( "The networks are equivalent by ODC CaDiCaL.  " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        return NULL;
    }
    pOrder = ABC_ALLOC( Acb_SplitPoOrder_t, Gia_ManCoNum(p) );
    Acb_NtkSortSplitOutputs( p, pOrder );
    if ( fVerbose )
        printf( "ODC CaDiCaL: solving one observable output cone at a time; cone limit = %d sec, total limit = %d sec.\n",
            nConeTimeLimit, nTotalTimeLimit );
    for ( k = 0; k < Gia_ManCoNum(p); k++ )
    {
        if ( (Abc_Clock() - clk) / CLOCKS_PER_SEC >= nTotalTimeLimit )
        {
            fOneUndef = 1;
            break;
        }
        i = pOrder[k].iPo;
        if ( fVerbose )
            printf( "ODC CaDiCaL output %d: cone ANDs = %d.\n", i, pOrder[k].nAnds );
        pOne = Gia_ManDupCones( p, &i, 1, 0 );
        pModel = Acb_NtkSolveCadicalLimit( pOne, 0, fVerbose, &Status, nConeTimeLimit, NULL, 0 );
        Gia_ManStop( pOne );
        if ( Status == 0 )
        {
            ABC_FREE( pOrder );
            if ( pStatus )
                *pStatus = ACB_XEC_NEQ;
            printf( "The networks are NOT equivalent by ODC CaDiCaL on output %d.  ", i );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            return pModel;
        }
        if ( Status == -1 )
            fOneUndef = 1;
    }
    ABC_FREE( pOrder );
    if ( pStatus )
        *pStatus = fOneUndef ? -1 : 1;
    printf( "The networks are %s by ODC CaDiCaL.  ", fOneUndef ? "UNDECIDED" : "equivalent" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return NULL;
}

int * Acb_NtkSolveSplit( Gia_Man_t * p, int fVerbose, int * pStatus )
{
    Gia_Man_t * pOne;
    Acb_SplitPoOrder_t * pOrder;
    int i, k, Status, fOneUndef = 0, * pModel = NULL;
    abctime clk = Abc_Clock();
    Abc_CexFreeP( &p->pCexComb );
    if ( Gia_ManCoNum(p) == 0 )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_EQ;
        printf( "The networks are equivalent by split SAT.  " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        return NULL;
    }
    pOrder = ABC_ALLOC( Acb_SplitPoOrder_t, Gia_ManCoNum(p) );
    Acb_NtkSortSplitOutputs( p, pOrder );
    if ( fVerbose && Gia_ManCoNum(p) > 1 )
        printf( "Split SAT output order: smallest cone %d ANDs, largest cone %d ANDs.\n",
            pOrder[0].nAnds, pOrder[Gia_ManCoNum(p)-1].nAnds );
    for ( k = 0; k < Gia_ManCoNum(p); k++ )
    {
        i = pOrder[k].iPo;
        pOne = Gia_ManDupCones( p, &i, 1, 0 );
        pModel = Acb_NtkSolveCadicalLimit( pOne, 0, fVerbose, &Status, 0, NULL, 0 );
        if ( Status == 0 )
        {
            Gia_ManStop( pOne );
            ABC_FREE( pOrder );
            if ( pStatus )
                *pStatus = ACB_XEC_NEQ;
            printf( "The networks are NOT equivalent by split SAT on output %d.  ", i );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            return pModel;
        }
        ABC_FREE( pModel );
        pModel = NULL;
        if ( Status == ACB_XEC_UNDEC )
            fOneUndef = 1;
        Gia_ManStop( pOne );
    }
    ABC_FREE( pOrder );
    if ( pStatus )
        *pStatus = fOneUndef ? -1 : 1;
    printf( "The networks are %s by split SAT.  ", fOneUndef ? "UNDECIDED" : "equivalent" );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Various statistics.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkPrintCecStats( Acb_Ntk_t * pNtk )
{
    int iObj, nDcs = 0, nMuxes = 0;
    Acb_NtkForEachNode( pNtk, iObj )
        if ( Acb_ObjType( pNtk, iObj ) == ABC_OPER_TRI )
            nDcs++;
        else if ( Acb_ObjType( pNtk, iObj ) == ABC_OPER_BIT_MUX )
            nMuxes++;

    printf( "PI = %6d  ",  Acb_NtkCiNum(pNtk) );
    printf( "PO = %6d  ",  Acb_NtkCoNum(pNtk) );
    printf( "Obj = %6d  ", Acb_NtkObjNum(pNtk) );
    printf( "DC = %4d  ",  nDcs );
    printf( "Mux = %4d  ", nMuxes );
    printf( "\n" );
}

void Acb_NtkCountXConstructs( Acb_Ntk_t * pNtk, int * pnDcs, int * pnMuxes, int * pnConstXs )
{
    int iObj;
    *pnDcs = *pnMuxes = *pnConstXs = 0;
    Acb_NtkForEachNode( pNtk, iObj )
        if ( Acb_ObjType( pNtk, iObj ) == ABC_OPER_TRI )
            (*pnDcs)++;
        else if ( Acb_ObjType( pNtk, iObj ) == ABC_OPER_BIT_MUX )
            (*pnMuxes)++;
        else if ( Acb_ObjType( pNtk, iObj ) == ABC_OPER_CONST_X )
            (*pnConstXs)++;
}

int * Acb_NtkSolveBinaryCec( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, int fVerbose, int * pStatus, int nTimeLimit )
{
    extern Vec_Int_t * Acb_NtkFindNodes( Acb_Ntk_t * p, Vec_Int_t * vRoots, Vec_Int_t * vDivs );
    extern Gia_Man_t * Acb_NtkToGia( Acb_Ntk_t * p, Vec_Int_t * vSupp, Vec_Int_t * vNodes, Vec_Int_t * vRoots, Vec_Int_t * vDivs, Vec_Int_t * vTargets );
    Vec_Int_t * vRoots = Vec_IntAlloc( Acb_NtkCoNum(pNtkF) );
    Vec_Int_t * vSupp  = Vec_IntAlloc( Acb_NtkCiNum(pNtkF) );
    Vec_Int_t * vNodesF = NULL, * vNodesG = NULL;
    Gia_Man_t * pGiaF = NULL, * pGiaG = NULL, * pMiter = NULL;
    int i, RetValue = ACB_XEC_UNDEC, * pModel = NULL;
    abctime clk = Abc_Clock();
    for ( i = 0; i < Acb_NtkCoNum(pNtkF); i++ )
        Vec_IntPush( vRoots, i );
    for ( i = 0; i < Acb_NtkCiNum(pNtkF); i++ )
        Vec_IntPush( vSupp, i );
    vNodesF = Acb_NtkFindNodes( pNtkF, vRoots, NULL );
    vNodesG = Acb_NtkFindNodes( pNtkG, vRoots, NULL );
    pGiaF  = Acb_NtkToGia( pNtkF, vSupp, vNodesF, vRoots, NULL, NULL );
    pGiaG  = Acb_NtkToGia( pNtkG, vSupp, vNodesG, vRoots, NULL, NULL );
    pMiter = Gia_ManMiter( pGiaF, pGiaG, 0, 0, 0, 0, fVerbose );
    if ( pMiter == NULL )
    {
        if ( pStatus )
            *pStatus = ACB_XEC_UNDEC;
        Gia_ManStop( pGiaF );
        Gia_ManStop( pGiaG );
        Vec_IntFree( vNodesF );
        Vec_IntFree( vNodesG );
        Vec_IntFree( vRoots );
        Vec_IntFree( vSupp );
        return NULL;
    }
    if ( Gia_ManAndNum(pMiter) > 5000 )
    {
        Gia_Man_t * pTemp;
        int nAndBefore = Gia_ManAndNum(pMiter);
        int nLevBefore = Gia_ManLevelNum(pMiter);
        pTemp = Gia_ManCompress2( pMiter, 1, 0 );
        if ( pTemp )
        {
            Gia_ManStop( pMiter );
            pMiter = pTemp;
            if ( fVerbose )
                printf( "Conventional binary XOR-miter compression: And = %d -> %d. Lev = %d -> %d. PO = %d.\n",
                    nAndBefore, Gia_ManAndNum(pMiter), nLevBefore, Gia_ManLevelNum(pMiter), Gia_ManCoNum(pMiter) );
        }
    }
    if ( fVerbose )
    {
        printf( "Trying conventional binary XOR-miter CaDiCaL for no-X design: PI = %d. PO = %d. And = %d. limit = %d sec.\n",
            Gia_ManCiNum(pMiter), Gia_ManCoNum(pMiter), Gia_ManAndNum(pMiter), nTimeLimit );
        Gia_ManPrintStats( pMiter, NULL );
    }
    pModel = Acb_NtkSolveCadicalLimit( pMiter, 0, fVerbose, &RetValue, nTimeLimit, NULL, 0 );
    if ( pStatus )
        *pStatus = RetValue;
    if ( RetValue == 0 && pModel )
    {
        if ( !Acb_NtkCheckModelCexAcbBool( pNtkF, pNtkG, pModel, fVerbose ) )
        {
            ABC_FREE( pModel );
            pModel = NULL;
            if ( pStatus )
                *pStatus = ACB_XEC_UNDEC;
            RetValue = ACB_XEC_UNDEC;
            printf( "The binary XOR-miter CaDiCaL SAT model is not a valid original Boolean counterexample; treating it as UNDECIDED.\n" );
        }
    }
    printf( "The networks are %s by conventional binary XOR-miter CaDiCaL.  ",
        RetValue == 1 ? "equivalent" : (RetValue == 0 ? "NOT equivalent" : "UNDECIDED") );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Gia_ManStop( pMiter );
    Gia_ManStop( pGiaF );
    Gia_ManStop( pGiaG );
    Vec_IntFree( vNodesF );
    Vec_IntFree( vNodesG );
    Vec_IntFree( vRoots );
    Vec_IntFree( vSupp );
    return pModel;
}

/**Function*************************************************************

  Synopsis    [Changing the PI order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkUpdateCiOrder( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG )
{
    int i, iObj;
    Vec_Int_t * vMap = Vec_IntStartFull( Acb_ManNameIdMax(pNtkG->pDesign) );
    Vec_Int_t * vOrder = Vec_IntStartFull( Acb_NtkCiNum(pNtkG) );
    Acb_NtkForEachCi( pNtkG, iObj, i )
        Vec_IntWriteEntry( vMap, Acb_ObjName(pNtkG, iObj), i );
    Acb_NtkForEachCi( pNtkF, iObj, i )
    {
        int NameIdG = Acb_ManStrId( pNtkG->pDesign, Acb_ObjNameStr(pNtkF, iObj) );
        int iPerm = NameIdG < Vec_IntSize(vMap) ? Vec_IntEntry( vMap, NameIdG ) : -1;
        if ( iPerm == -1 )
            printf( "Cannot find name \"%s\" of PI %d of F among PIs of G.\n", Acb_ObjNameStr(pNtkF, iObj), i );
        else
            Vec_IntWriteEntry( vOrder, iPerm, iObj );
    }
    Vec_IntClear( &pNtkF->vCis );
    Vec_IntAppend( &pNtkF->vCis, vOrder );
    Vec_IntFree( vOrder );
    Vec_IntFree( vMap );
}
int Acb_NtkCheckPiOrder( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG )
{
    int i, nPis = Acb_NtkCiNum(pNtkF);
    for ( i = 0; i < nPis; i++ )
    {
        char * pNameF = Acb_ObjNameStr( pNtkF, Acb_NtkCi(pNtkF, i) );
        char * pNameG = Acb_ObjNameStr( pNtkG, Acb_NtkCi(pNtkG, i) );
        if ( strcmp(pNameF, pNameG) )
        {
//            printf( "PI %d has different names (%s and %s) in these networks.\n", i, pNameF, pNameG );
            printf( "Networks have different PI names. Reordering PIs of the implementation network.\n" );
            Acb_NtkUpdateCiOrder( pNtkF, pNtkG );
            break;
        }
    }
    if ( i == nPis )
        printf( "Networks have the same PI names.\n" );
    return i == nPis;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkRunTest( char * pFileNames[4], int fFancy, int fVerbose, int fUseCadical )
{
    int Status = -1;
    int * pModel = NULL;
    Gia_Man_t * pGiaF = NULL;
    Gia_Man_t * pGiaG = NULL;
    Gia_Man_t * pGia  = NULL;
    Gia_Man_t * pGiaFCut = NULL;
    Gia_Man_t * pGiaGCut = NULL;
    Gia_Man_t * pGiaGCtrl = NULL;
    Gia_Man_t * pGiaCut = NULL;
    Gia_Man_t * pGiaX = NULL;
    Gia_Man_t * pTemp = NULL;
    Vec_Int_t * vCutObjsF = NULL;
    Vec_Int_t * vCutObjsG = NULL;
    Vec_Int_t * vMuxSelectorsG = NULL;
    Vec_Int_t * vMuxPoSelIdsG = NULL;
    Vec_Int_t * vSymCutObjsF = NULL;
    Vec_Int_t * vSymMuxSelectorsF = NULL;
    Vec_Int_t * vSymIntDcObjsF = NULL;
    Vec_Int_t * vSymIntDcCtrlsF = NULL;
    Vec_Int_t * vSymIntDcCtrlIdsF = NULL;
    Vec_Int_t * vIntDcObjsG = NULL;
    Vec_Int_t * vIntDcCtrlsG = NULL;
    Vec_Int_t * vIntDcCtrlIdsG = NULL;
    Vec_Int_t * vDcDataObjsG = NULL;
    Vec_Int_t * vDcCtrlObjsG = NULL;
    Acb_XecCtx_t XecCtx;
    int fSymmetricMuxDc = 0;
    int nDcsF = 0, nMuxesF = 0, nConstXsF = 0, nDcsG = 0, nMuxesG = 0, nConstXsG = 0;
    Acb_Ntk_t * pNtkF = Acb_VerilogSimpleRead( pFileNames[0], NULL );
    Acb_Ntk_t * pNtkG = Acb_VerilogSimpleRead( pFileNames[1], NULL );
    if ( !pNtkF || !pNtkG )
    {
        if ( pNtkF )
            Acb_ManFree( pNtkF->pDesign );
        if ( pNtkG )
            Acb_ManFree( pNtkG->pDesign );
        return;
    }
    Acb_XecCtxInit( &XecCtx );

    assert( Acb_NtkCiNum(pNtkF) == Acb_NtkCiNum(pNtkG) );
    assert( Acb_NtkCoNum(pNtkF) == Acb_NtkCoNum(pNtkG) );

    Acb_NtkCheckPiOrder( pNtkF, pNtkG );
    //Acb_NtkCheckPiOrder( pNtkG, pNtkF );
    Acb_NtkPrintCecStats( pNtkF );
    Acb_NtkPrintCecStats( pNtkG );
    Acb_NtkCountXConstructs( pNtkF, &nDcsF, &nMuxesF, &nConstXsF );
    Acb_NtkCountXConstructs( pNtkG, &nDcsG, &nMuxesG, &nConstXsG );

    if ( fUseCadical && nDcsF == 0 && nMuxesF == 0 && nConstXsF == 0 && nDcsG == 0 && nMuxesG == 0 && nConstXsG == 0 )
    {
        if ( fVerbose )
            printf( "No X/DC/MUX constructs found; using conventional binary CaDiCaL instead of X-aware dual-rail proving.\n" );
        pModel = Acb_NtkSolveBinaryCec( pNtkF, pNtkG, fVerbose, &Status, 1200 );
        Acb_OutputFile( pFileNames[2], pNtkF, pModel, Status );
        ABC_FREE( pModel );
        Acb_XecCtxFree( &XecCtx );
        Acb_ManFree( pNtkF->pDesign );
        Acb_ManFree( pNtkG->pDesign );
        return;
    }

    pGiaF = Acb_NtkGiaDeriveDual( pNtkF );
    pGiaG = Acb_NtkGiaDeriveDual( pNtkG );
    if ( pGiaF == NULL || pGiaG == NULL )
    {
        printf( "XEC dual-rail translation failed; see unsupported ACB object diagnostic above.\n" );
        Status = ACB_XEC_UNDEC;
        Acb_OutputFile( pFileNames[2], pNtkF, NULL, Status );
        Gia_ManStopP( &pGiaF );
        Gia_ManStopP( &pGiaG );
        Acb_XecCtxFree( &XecCtx );
        Acb_ManFree( pNtkF->pDesign );
        Acb_ManFree( pNtkG->pDesign );
        return;
    }
    pGia  = Acb_NtkGiaDeriveMiter( pGiaF, pGiaG, 2 );
    if ( fUseCadical )
    {
        if ( Acb_NtkCollectPoDcCutpoints( pNtkG, &vDcDataObjsG, &vDcCtrlObjsG ) )
        {
            vCutObjsF = Acb_NtkCollectCoDrivers( pNtkF );
            if ( fVerbose )
                printf( "Found %d output DC cutpoints in implementation network.\n", Vec_IntSize(vDcDataObjsG) );
        }
        vCutObjsG = Acb_NtkCollectPoMuxCutpoints( pNtkG );
        if ( vCutObjsF == NULL && Vec_IntSize(vCutObjsG) == Acb_NtkCoNum(pNtkG) )
        {
            vCutObjsF = Acb_NtkCollectCoDrivers( pNtkF );
            vMuxSelectorsG = Acb_NtkCollectPoMuxSelectors( pNtkG, vCutObjsG );
            vMuxPoSelIdsG = Acb_NtkCollectPoMuxSelectorIds( pNtkG, vCutObjsG, vMuxSelectorsG );
            if ( fVerbose )
                printf( "Found %d output partition-candidate cutpoints using %d unique selectors in implementation network.\n",
                    Vec_IntSize(vCutObjsG), Vec_IntSize(vMuxSelectorsG) );
        }
        else if ( fVerbose && vCutObjsF == NULL && Vec_IntSize(vCutObjsG) > 0 )
            printf( "No complete output partition-candidate cutpoint set found.\n" );
        if ( Acb_NtkCollectInternalDcControls( pNtkG, &vIntDcObjsG, &vIntDcCtrlsG, &vIntDcCtrlIdsG ) && fVerbose )
            printf( "Found %d internal DC nodes using %d unique controls in implementation network.\n",
                Vec_IntSize(vIntDcObjsG), Vec_IntSize(vIntDcCtrlsG) );
        if ( vIntDcObjsG && Vec_IntSize(vIntDcObjsG) > 0 && Acb_NtkCoNum(pNtkG) > 512 )
            Acb_NtkCollectInternalDcControls( pNtkF, &vSymIntDcObjsF, &vSymIntDcCtrlsF, &vSymIntDcCtrlIdsF );
        if ( vCutObjsG && vMuxSelectorsG && Vec_IntSize(vCutObjsG) == Acb_NtkCoNum(pNtkG) &&
             vIntDcObjsG && vIntDcCtrlsG && Vec_IntSize(vIntDcObjsG) > 0 && Vec_IntSize(vIntDcCtrlsG) > 0 )
        {
            vSymCutObjsF = Acb_NtkCollectPoMuxCutpoints( pNtkF );
            if ( vSymCutObjsF && Vec_IntSize(vSymCutObjsF) == Acb_NtkCoNum(pNtkF) )
                vSymMuxSelectorsF = Acb_NtkCollectPoMuxSelectors( pNtkF, vSymCutObjsF );
            if ( vSymIntDcObjsF == NULL )
                Acb_NtkCollectInternalDcControls( pNtkF, &vSymIntDcObjsF, &vSymIntDcCtrlsF, &vSymIntDcCtrlIdsF );
            fSymmetricMuxDc =
                vSymMuxSelectorsF && vSymIntDcObjsF && vSymIntDcCtrlsF &&
                Vec_IntSize(vSymMuxSelectorsF) == Vec_IntSize(vMuxSelectorsG) &&
                Vec_IntSize(vSymIntDcObjsF) == Vec_IntSize(vIntDcObjsG) &&
                Vec_IntSize(vSymIntDcCtrlsF) == Vec_IntSize(vIntDcCtrlsG);
            if ( fVerbose && fSymmetricMuxDc )
                printf( "Detected symmetric output-MUX/internal-DC structure in both networks.\n" );
        }
    }
    if ( Gia_ManAndNum(pGia) > 5000 )
    {
        int nAndBefore = Gia_ManAndNum(pGia);
        pTemp = Gia_ManCompress2( pGia, 1, fVerbose );
        if ( pTemp )
        {
            if ( fVerbose )
                printf( "XEC miter compression: And = %d -> %d. PO = %d.\n", nAndBefore, Gia_ManAndNum(pTemp), Gia_ManPoNum(pTemp) );
            Gia_ManStop( pGia );
            pGia = pTemp;
        }
    }
    {
        int nSimWords = Gia_ManAndNum(pGia) > XecCtx.Pars.nSimLargeAndMin ? XecCtx.Pars.nSimLargeWords : XecCtx.Pars.nSimSmallWords;
        int fCheckModel = 0;
        int fSkipWholeMiter = 0;
        int fTriedWholeMiterEarly = 0;
        int fSkipAsymHmuxBranch = 0;
        int fSkipHighPiDcFallbacks = 0;
        int fHighPiTwoCtrlDc = !fFancy &&
            Acb_XecIsSharedDcWholeMiterShape( pGia, vMuxSelectorsG, vIntDcObjsG, vIntDcCtrlsG, &XecCtx );
        int fConstXSeedDc = !fFancy &&
            nDcsF == 0 && nMuxesF == 0 && nConstXsF == 0 &&
            (vMuxSelectorsG == NULL || Vec_IntSize(vMuxSelectorsG) == 0) &&
            vIntDcObjsG && Vec_IntSize(vIntDcObjsG) > 0 && Vec_IntSize(vIntDcObjsG) <= 8 &&
            Acb_NtkAllDcObjsAreConstXSeeds( pNtkG, vIntDcObjsG ) &&
            Gia_ManCiNum(pGia) <= 512 && Gia_ManCoNum(pGia) >= 64;
        pModel = Acb_NtkFindSimCex( pGiaF, pGiaG, nSimWords, fVerbose );
        if ( pModel )
        {
            Status = 0;
            printf( "The networks are NOT equivalent by random simulation.\n" );
        }
        else
        {
            if ( fUseCadical )
            {
                if ( Gia_ManAndNum(pGia) > XecCtx.Pars.nMainLargeAndMin || Gia_ManCiNum(pGia) > XecCtx.Pars.nMainLargePiMin || Gia_ManCoNum(pGia) > XecCtx.Pars.nMainLargePoMin )
                {
                    if ( Status == -1 && !fFancy && vDcDataObjsG && vDcCtrlObjsG &&
                         vIntDcObjsG && Vec_IntSize(vIntDcObjsG) > 0 &&
                         vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) == 1 &&
                         (vMuxSelectorsG == NULL || Vec_IntSize(vMuxSelectorsG) == 0) &&
                         Vec_IntSize(vDcDataObjsG) == Acb_NtkCoNum(pNtkG) &&
                         Gia_ManCiNum(pGia) <= 512 && Gia_ManCoNum(pGia) > 32 )
                    {
                        int StatusPre = -1;
                        pModel = Acb_NtkSolveNormalPrecheck( pGia, fVerbose, &StatusPre, 750000 );
                        Acb_XecMergeTargetStatus( StatusPre, pModel != NULL, &Status, &fCheckModel );
                    }
                    if ( !fFancy && !fSkipHighPiDcFallbacks && Status == -1 && vCutObjsF && vDcDataObjsG && vDcCtrlObjsG )
                    {
                        pGiaFCut  = Acb_NtkGiaDeriveDualTargets( pNtkF, vCutObjsF );
                        pGiaGCut  = Acb_NtkGiaDeriveDualTargets( pNtkG, vDcDataObjsG );
                        pGiaGCtrl = Acb_NtkGiaDeriveDualTargets( pNtkG, vDcCtrlObjsG );
                        pGiaCut   = Acb_NtkGiaDeriveMiterDcGuard( pGiaFCut, pGiaGCut, pGiaGCtrl );
                        if ( Gia_ManAndNum(pGiaCut) >= Gia_ManAndNum(pGia) )
                        {
                            if ( fVerbose )
                                printf( "Skipping output-DC guarded cutpoint miter because it is not smaller: And = %d, current = %d.\n",
                                    Gia_ManAndNum(pGiaCut), Gia_ManAndNum(pGia) );
                        }
                        else
                        {
                            if ( fVerbose )
                                printf( "Trying output-DC guarded cutpoint CaDiCaL sweep before whole-miter CaDiCaL: And = %d. PO = %d.\n",
                                    Gia_ManAndNum(pGiaCut), Gia_ManPoNum(pGiaCut) );
                            pModel = Acb_NtkSolveCadicalLimit( pGiaCut, 0, fVerbose, &Status, 900, "output-DC guarded cutpoint CaDiCaL", 0 );
                            Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                        }
                    }
                    if ( Status == -1 && !fFancy &&
                         (vMuxSelectorsG == NULL || Vec_IntSize(vMuxSelectorsG) == 0) &&
                         vIntDcObjsG && Vec_IntSize(vIntDcObjsG) > 0 && Vec_IntSize(vIntDcObjsG) <= 8 &&
                         vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) > 1 && Vec_IntSize(vIntDcCtrlsG) <= 2 &&
                         Gia_ManCiNum(pGia) <= 512 && Gia_ManCoNum(pGia) > 64 )
                    {
                        int StatusTarget = -1;
                        pModel = Acb_NtkSolveDcControlWholeCubes( pNtkF, pNtkG,
                            vIntDcObjsG, vIntDcCtrlsG, vIntDcCtrlIdsG, fVerbose, &StatusTarget, 900, 300 );
                        Acb_XecMergeTargetStatus( StatusTarget, pModel != NULL, &Status, &fCheckModel );
                    }
                    if ( Status == -1 && fConstXSeedDc )
                    {
                        int StatusConstX = -1;
                        pModel = Acb_NtkSolveConstXSeedCanonical( pNtkF, pNtkG, vIntDcObjsG,
                            fVerbose, &StatusConstX, 1200 );
                        Acb_XecMergeTargetStatus( StatusConstX, pModel != NULL, &Status, &fCheckModel );
                    }
                    if ( Status == -1 && !fFancy &&
                         (vMuxSelectorsG == NULL || Vec_IntSize(vMuxSelectorsG) == 0) &&
                         vIntDcObjsG && Vec_IntSize(vIntDcObjsG) > 0 &&
                         vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) > 0 && Vec_IntSize(vIntDcCtrlsG) <= 2 &&
                         (fHighPiTwoCtrlDc || (Gia_ManCiNum(pGia) >= XecCtx.Pars.nSharedDcPiMin &&
                          Gia_ManCoNum(pGia) > 64 && Gia_ManAndNum(pGia) > XecCtx.Pars.nSharedDcAndMin)) )
                    {
                        int nWholeDcLimit = fHighPiTwoCtrlDc ? XecCtx.Pars.nSharedDcWholeSec : 1200;
                        if ( fVerbose )
                            printf( "Trying whole-miter CaDiCaL before local sweep for %slarge high-PI DC design: And = %d. PO = %d. DC controls = %d.\n",
                            fHighPiTwoCtrlDc ? "case8-style " : "", Gia_ManAndNum(pGia), Gia_ManCoNum(pGia), Vec_IntSize(vIntDcCtrlsG) );
                        fTriedWholeMiterEarly = 1;
                        pModel = Acb_NtkSolveCadicalLimit( pGia, 0, fVerbose, &Status, nWholeDcLimit, "large high-PI DC whole-miter CaDiCaL", 0 );
                        Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                        if ( Status == -1 && fVerbose )
                            printf( "Large high-PI DC whole-miter CaDiCaL was UNDECIDED%s.\n",
                                fHighPiTwoCtrlDc ? "; skipping local/cube detours for this case8-style shape" : "; continuing with local structural attempts" );
                        if ( Status == -1 && fHighPiTwoCtrlDc )
                        {
                            fSkipHighPiDcFallbacks = 1;
                            fSkipWholeMiter = 1;
                        }
                    }
                    if ( Status == -1 && !fFancy && fSymmetricMuxDc &&
                         vMuxSelectorsG && Vec_IntSize(vMuxSelectorsG) > 0 && Vec_IntSize(vMuxSelectorsG) <= 4 &&
                         vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) > 4 &&
                         Gia_ManCoNum(pGia) >= 32 && Gia_ManCoNum(pGia) <= 128 &&
                         Gia_ManCiNum(pGia) <= 1024 &&
                         Gia_ManAndNum(pGia) >= 30000 && Gia_ManAndNum(pGia) <= 70000 )
                    {
                        if ( fVerbose )
                            printf( "Trying whole-miter CaDiCaL before local sweep for symmetric MUX/DC design: And = %d. PO = %d. selectors = %d. DC controls = %d.\n",
                            Gia_ManAndNum(pGia), Gia_ManCoNum(pGia), Vec_IntSize(vMuxSelectorsG), Vec_IntSize(vIntDcCtrlsG) );
                        fTriedWholeMiterEarly = 1;
                        pModel = Acb_NtkSolveCadicalLimit( pGia, 0, fVerbose, &Status, 1200, "symmetric MUX/DC whole-miter CaDiCaL", 0 );
                        Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                        if ( Status == -1 && fVerbose )
                            printf( "Symmetric MUX/DC whole-miter CaDiCaL was UNDECIDED; continuing with local structural attempts.\n" );
                    }
                    if ( Status == -1 && !fFancy && !fSymmetricMuxDc && !fSkipAsymHmuxBranch &&
                         vCutObjsG && vMuxSelectorsG && vMuxPoSelIdsG &&
                         Vec_IntSize(vCutObjsG) == Acb_NtkCoNum(pNtkG) &&
                         Vec_IntSize(vMuxSelectorsG) > 0 && Vec_IntSize(vMuxSelectorsG) <= 4 &&
                         vIntDcObjsG && vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) > 4 &&
                         Gia_ManCiNum(pGia) <= 1024 && Gia_ManCoNum(pGia) >= 32 && Gia_ManCoNum(pGia) <= 96 )
                    {
                        int StatusCube = -1;
                        pModel = Acb_NtkSolveHmuxCompleteCubes( pNtkF, pNtkG,
                            vCutObjsG, vMuxSelectorsG, vMuxPoSelIdsG,
                            fVerbose, &StatusCube, 1200, 300 );
                        Acb_XecMergeTargetStatus( StatusCube, pModel != NULL, &Status, &fCheckModel );
                        if ( StatusCube == ACB_XEC_UNDEC )
                        {
                            fSkipAsymHmuxBranch = 1;
                            if ( fVerbose )
                                printf( "Complete HMUX selector-cube proof was inconclusive; skipping CEPR and partial-selector HMUX detours for this broad asymmetric shape.\n" );
                        }
                    }
                    if ( Status == -1 && !fFancy && !fSymmetricMuxDc && !fSkipAsymHmuxBranch &&
                         vCutObjsG && vMuxSelectorsG && vMuxPoSelIdsG &&
                         Vec_IntSize(vCutObjsG) == Acb_NtkCoNum(pNtkG) &&
                         Vec_IntSize(vMuxSelectorsG) > 0 && Vec_IntSize(vMuxSelectorsG) <= 4 &&
                         vIntDcObjsG && Vec_IntSize(vIntDcObjsG) >= 128 &&
                         vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) >= 8 &&
                         Gia_ManCiNum(pGia) <= 1024 && Gia_ManCoNum(pGia) >= 32 && Gia_ManCoNum(pGia) <= 64 &&
                         Gia_ManAndNum(pGia) <= 35000 )
                    {
                        if ( fVerbose )
                            printf( "Trying compact HMUX/DC whole-miter CaDiCaL before asymmetric branch proof: And = %d. PO = %d. selectors = %d. DC controls = %d.\n",
                                Gia_ManAndNum(pGia), Gia_ManCoNum(pGia), Vec_IntSize(vMuxSelectorsG), Vec_IntSize(vIntDcCtrlsG) );
                        fTriedWholeMiterEarly = 1;
                        fSkipAsymHmuxBranch = 1;
                        pModel = Acb_NtkSolveCadicalLimit( pGia, 0, fVerbose, &Status, 1200, "compact HMUX/DC whole-miter CaDiCaL", 0 );
                        Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                        if ( Status == -1 && fVerbose )
                            printf( "Compact HMUX/DC whole-miter CaDiCaL was UNDECIDED; skipping the expensive asymmetric HMUX branch detour.\n" );
                    }

                    if ( Status == -1 && !fFancy && !fSymmetricMuxDc && !fSkipAsymHmuxBranch &&
                         vCutObjsG && vMuxSelectorsG && vMuxPoSelIdsG &&
                         Vec_IntSize(vCutObjsG) == Acb_NtkCoNum(pNtkG) &&
                         Vec_IntSize(vMuxSelectorsG) > 0 && Vec_IntSize(vMuxSelectorsG) <= 4 &&
                         vIntDcObjsG && vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) > 4 &&
                         Gia_ManCoNum(pGia) >= 16 && Gia_ManCoNum(pGia) <= 128 )
                    {
                        int StatusHmux = -1;
                        if ( fVerbose )
                            printf( "Trying asymmetric HMUX branch proof with targeted DC fallback before local sweep.\n" );
                        pModel = Acb_NtkSolveHmuxBranches( pNtkF, pNtkG,
                            vCutObjsG, vMuxSelectorsG, vMuxPoSelIdsG,
                            vIntDcObjsG, vIntDcCtrlsG, vIntDcCtrlIdsG,
                            fVerbose, &StatusHmux, &XecCtx );
                        Acb_XecMergeTargetStatus( StatusHmux, pModel != NULL, &Status, &fCheckModel );
                    }
                    if ( Status == -1 && !fFancy && !fSkipHighPiDcFallbacks )
                    {
                        pModel = Acb_NtkSolveCadicalLocalConeSweepSkipCtx( pGia, fVerbose, &Status, 900, 120, NULL, &XecCtx );
                        Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                    }
                    if ( Status == -1 && !fSkipHighPiDcFallbacks )
                    {
                        int StatusTarget = -1;
                        if ( !fFancy && vIntDcObjsG && Vec_IntSize(vIntDcObjsG) > 0 &&
                             vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) > 0 && Vec_IntSize(vIntDcCtrlsG) <= 4 &&
                             (vMuxSelectorsG == NULL || Vec_IntSize(vMuxSelectorsG) == 0) &&
                             XecCtx.vLastHardPos && Vec_IntSize(XecCtx.vLastHardPos) > 0 )
                        {
                            int fTriedSmallDcCutpoints = 0;
                            if ( Vec_IntSize(vIntDcCtrlsG) == 1 && Vec_IntSize(vIntDcObjsG) <= 2 &&
                                 Gia_ManCiNum(pGia) <= 256 && Gia_ManCoNum(pGia) > 64 &&
                                 Vec_IntSize(XecCtx.vLastHardPos) <= 16 )
                            {
                                fTriedSmallDcCutpoints = 1;
                                if ( fVerbose )
                                    printf( "Trying collected hard-output cutpoint abstraction for small single-control DC design: hard outputs = %d. DC nodes = %d.\n",
                                        Vec_IntSize(XecCtx.vLastHardPos), Vec_IntSize(vIntDcObjsG) );
                                pModel = Acb_NtkSolveTargetCutpointList( pNtkF, pNtkG, XecCtx.vLastHardPos,
                                    fVerbose, &StatusTarget, 900, 120 );
                            }
                            if ( StatusTarget == -1 && !fTriedSmallDcCutpoints && !fHighPiTwoCtrlDc )
                            {
                                if ( fVerbose )
                                    printf( "Trying DC-control target recursion after local-cone sweep: hard outputs = %d. controls = %d.\n",
                                        Vec_IntSize(XecCtx.vLastHardPos), Vec_IntSize(vIntDcCtrlsG) );
                                pModel = Acb_NtkSolveDcControlTargetList( pNtkF, pNtkG, XecCtx.vLastHardPos,
                                    vIntDcObjsG, vIntDcCtrlsG, vIntDcCtrlIdsG, fVerbose, &StatusTarget, 180 );
                            }
                            Acb_XecMergeTargetStatus( StatusTarget, pModel != NULL, &Status, &fCheckModel );
                            if ( StatusTarget == 1 )
                            {
                                if ( Vec_IntSize(XecCtx.vLastHardPos) == Gia_ManCoNum(pGia) )
                                    Status = 1;
                                else
                                {
                                    Vec_Int_t * vSkipUnsat = Vec_IntDup( XecCtx.vLastHardPos );
                                    int iPoSkip, iSkip, StatusResume = -1;
                                    if ( XecCtx.vLastProvenPos )
                                        Vec_IntForEachEntry( XecCtx.vLastProvenPos, iPoSkip, iSkip )
                                            Vec_IntPushUnique( vSkipUnsat, iPoSkip );
                                    if ( fVerbose )
                                        printf( "DC-control target recursion proved %d collected hard outputs; resuming local-cone sweep for %d remaining outputs.\n",
                                            Vec_IntSize(XecCtx.vLastHardPos), Gia_ManCoNum(pGia) - Vec_IntSize(vSkipUnsat) );
                                    pModel = Acb_NtkSolveCadicalLocalConeSweepSkipCtx( pGia, fVerbose, &StatusResume, 900, -120, vSkipUnsat, &XecCtx );
                                    Vec_IntFree( vSkipUnsat );
                                    Acb_XecMergeTargetStatus( StatusResume, pModel != NULL, &Status, &fCheckModel );
                                    if ( StatusResume != ACB_XEC_EQ && StatusResume != ACB_XEC_NEQ )
                                        Status = StatusResume;
                                }
                            }
                            else if ( fHighPiTwoCtrlDc )
                            {
                                fSkipWholeMiter = 1;
                                if ( fVerbose )
                                    printf( "Skipping expensive high-PI two-control DC fallbacks after quick local sweep; remaining outputs need a specialized proof.\n" );
                            }
                        }
                    }
                    if ( Status == ACB_XEC_ONE_HARD )
                    {
                        int StatusTarget = -1;
                        if ( !fFancy && vCutObjsG && vMuxSelectorsG && vMuxPoSelIdsG &&
                             Vec_IntSize(vCutObjsG) == Acb_NtkCoNum(pNtkG) &&
                             Vec_IntSize(vMuxSelectorsG) > 0 && Vec_IntSize(vMuxSelectorsG) <= 16 )
                        {
                            pModel = Acb_NtkSolveMuxTargetBranches( pNtkF, pNtkG, XecCtx.LastHardPo,
                                vCutObjsG, vMuxSelectorsG, vMuxPoSelIdsG, fVerbose, &StatusTarget, 450, 0 );
                            Acb_XecMergeTargetStatus( StatusTarget, pModel != NULL, &Status, &fCheckModel );
                        }
                    }
                    if ( Status == ACB_XEC_MANY_HARD )
                    {
                        int StatusTarget = -1;
                        if ( !fFancy && vIntDcObjsG && Vec_IntSize(vIntDcObjsG) > 0 &&
                             vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) > 0 && Vec_IntSize(vIntDcCtrlsG) <= 4 &&
                             (vMuxSelectorsG == NULL || Vec_IntSize(vMuxSelectorsG) == 0) &&
                             XecCtx.vLastHardPos && Vec_IntSize(XecCtx.vLastHardPos) > 0 )
                        {
                            pModel = Acb_NtkSolveDcControlTargetList( pNtkF, pNtkG, XecCtx.vLastHardPos,
                                vIntDcObjsG, vIntDcCtrlsG, vIntDcCtrlIdsG, fVerbose, &StatusTarget, 180 );
                            Acb_XecMergeTargetStatus( StatusTarget, pModel != NULL, &Status, &fCheckModel );
                        }
                    }
                    if ( Status == ACB_XEC_ONE_HARD )
                    {
                        int StatusTarget = -1;
                        if ( !fFancy && vIntDcObjsG && Vec_IntSize(vIntDcObjsG) > 0 &&
                             vIntDcCtrlsG && Vec_IntSize(vIntDcCtrlsG) > 0 && Vec_IntSize(vIntDcCtrlsG) <= 4 &&
                             (vMuxSelectorsG == NULL || Vec_IntSize(vMuxSelectorsG) == 0) )
                        {
                            pModel = Acb_NtkSolveDcControlTargetBranches( pNtkF, pNtkG, XecCtx.LastHardPo,
                                vIntDcObjsG, vIntDcCtrlsG, vIntDcCtrlIdsG, fVerbose, &StatusTarget, 450, 0 );
                            Acb_XecMergeTargetStatus( StatusTarget, pModel != NULL, &Status, &fCheckModel );
                        }
                    }
                    if ( Status == ACB_XEC_ONE_HARD )
                    {
                        int StatusTarget = -1;
                        pModel = Acb_NtkSolveTargetCutpoints( pNtkF, pNtkG, XecCtx.LastHardPo, fVerbose, &StatusTarget, 900 );
                        Acb_XecMergeTargetStatus( StatusTarget, pModel != NULL, &Status, &fCheckModel );
                    }
                    if ( Status == ACB_XEC_ONE_HARD )
                    {
                        if ( XecCtx.LastHardDirectTried )
                        {
                            if ( fVerbose )
                                printf( "Skipping whole-miter CaDiCaL because the isolated hard output already had a rejected direct-clause SAT model.\n" );
                            Status = -1;
                            fSkipWholeMiter = 1;
                        }
                        else
                        {
                            if ( fVerbose )
                                printf( "Skipping whole-miter CaDiCaL because it duplicates the isolated hard-output cone.\n" );
                            Status = -1;
                            fSkipWholeMiter = 1;
                        }
                    }
                    if ( Status == ACB_XEC_MANY_HARD )
                    {
                        if ( fVerbose )
                            printf( "Skipping whole-miter CaDiCaL because the remaining hard-output proof already isolated the unresolved outputs.\n" );
                        Status = -1;
                        fSkipWholeMiter = 1;
                    }
                    if ( Status == -1 && !fFancy && !fSkipWholeMiter && !fTriedWholeMiterEarly )
                        pModel = Acb_NtkSolveCadicalLimit( pGia, 0, fVerbose, &Status, 1200, "CaDiCaL SAT-only", 0 );
                    else if ( Status == -1 && !fSkipWholeMiter )
                        pModel = Acb_NtkSolveCadicalLimit( pGia, fFancy, fVerbose, &Status, 1200, fFancy ? "X-aware CaDiCaL SAT-only" : "CaDiCaL SAT-only", fFancy );
                    if ( Status == -1 && fFancy && vCutObjsF && vDcDataObjsG && vDcCtrlObjsG )
                    {
                        pGiaFCut  = Acb_NtkGiaDeriveDualTargets( pNtkF, vCutObjsF );
                        pGiaGCut  = Acb_NtkGiaDeriveDualTargets( pNtkG, vDcDataObjsG );
                        pGiaGCtrl = Acb_NtkGiaDeriveDualTargets( pNtkG, vDcCtrlObjsG );
                        pGiaCut   = Acb_NtkGiaDeriveMiterDcGuard( pGiaFCut, pGiaGCut, pGiaGCtrl );
                        if ( fVerbose )
                            printf( "Trying exact split SAT on output-DC cutpoint miter: And = %d. PO = %d.\n", Gia_ManAndNum(pGiaCut), Gia_ManPoNum(pGiaCut) );
                        pModel = Acb_NtkSolveSplit( pGiaCut, fVerbose, &Status );
                        Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                    }
                    if ( Status == -1 && fFancy && vCutObjsF && vCutObjsG && Vec_IntSize(vCutObjsG) == Acb_NtkCoNum(pNtkG) )
                    {
                        if ( pGiaCut )
                        {
                            Gia_ManStop( pGiaCut );
                            pGiaCut = NULL;
                        }
                        if ( pGiaFCut )
                        {
                            Gia_ManStop( pGiaFCut );
                            pGiaFCut = NULL;
                        }
                        if ( pGiaGCut )
                        {
                            Gia_ManStop( pGiaGCut );
                            pGiaGCut = NULL;
                        }
                        pGiaFCut = Acb_NtkGiaDeriveDualTargets( pNtkF, vCutObjsF );
                        pGiaGCut = Acb_NtkGiaDeriveDualTargets( pNtkG, vCutObjsG );
                        pGiaCut  = Acb_NtkGiaDeriveMiter( pGiaFCut, pGiaGCut, 2 );
                        if ( Gia_ManAndNum(pGiaCut) >= Gia_ManAndNum(pGia) )
                        {
                            if ( fVerbose )
                                printf( "Skipping partition-candidate cutpoint miter because it is not smaller: And = %d, current = %d.\n",
                                    Gia_ManAndNum(pGiaCut), Gia_ManAndNum(pGia) );
                        }
                        else
                        {
                            if ( fVerbose )
                                printf( "Trying exact split SAT on partition-candidate cutpoint miter: And = %d. PO = %d.\n", Gia_ManAndNum(pGiaCut), Gia_ManPoNum(pGiaCut) );
                            pModel = Acb_NtkSolveSplit( pGiaCut, fVerbose, &Status );
                            Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                        }
                    }
                    if ( Status == -1 && fFancy )
                        pModel = Acb_NtkSolveCadicalOdc( pGia, fVerbose, &Status );
                    if ( Status == -1 && fFancy )
                    {
                        pModel = Acb_NtkSolveSplit( pGia, fVerbose, &Status );
                        Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                    }
                    if ( Status == -1 && fFancy )
                    {
                        printf( "Trying X-aware whole-miter CaDiCaL after ODC/split SAT was undecided.\n" );
                        if ( pGiaX == NULL )
                            pGiaX = Acb_NtkGiaDeriveMiter( pGiaF, pGiaG, 3 );
                        pModel = Acb_NtkSolveCadicalLimit( pGiaX, fFancy, fVerbose, &Status, 1200, "X-aware CaDiCaL SAT-only", 1 );
                        fCheckModel = 1;
                    }
                }
                else
                {
                    if ( !fFancy && Status == -1 && Gia_ManCoNum(pGia) == 1 && Gia_ManAndNum(pGia) <= 30000 &&
                         (vMuxSelectorsG == NULL || Vec_IntSize(vMuxSelectorsG) == 0) )
                    {
                        pModel = Acb_NtkSolveIvyPrecheck( pGia, fVerbose, &Status );
                        Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                    }
                    if ( !fFancy && Status == -1 && vIntDcObjsG && Vec_IntSize(vIntDcObjsG) > 0 && Vec_IntSize(vIntDcCtrlsG) > 0 && Vec_IntSize(vIntDcCtrlsG) <= 4 )
                    {
                        int fSmallMultiOutput = Gia_ManAndNum(pGia) <= 5000 && Gia_ManCoNum(pGia) > 1;
                        if ( fSmallMultiOutput && Vec_IntSize(vIntDcCtrlsG) == 1 && Vec_IntSize(vIntDcObjsG) <= 16 &&
                             Gia_ManCoNum(pGia) >= 8 && Gia_ManCoNum(pGia) <= 32 )
                        {
                            pModel = Acb_NtkSolveCadicalLimit( pGia, fFancy, fVerbose, &Status, 1700,
                                "small single-control DC whole-miter CaDiCaL", 0 );
                            Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                        }
                        else
                        {
                            pModel = Acb_NtkSolveDcControlBranchesLimit( pNtkF, pNtkG, vIntDcObjsG, vIntDcCtrlsG, vIntDcCtrlIdsG,
                                fVerbose, &Status, fSmallMultiOutput ? 60 : 5, !fSmallMultiOutput, 0 );
                            Acb_XecMergeTargetStatus( Status, pModel != NULL, &Status, &fCheckModel );
                        }
                    }

                    if ( Status == -1 )
                        pModel = Acb_NtkSolveCadicalLimit( pGia, fFancy, fVerbose, &Status, 1200, fFancy ? "X-aware CaDiCaL SAT-only" : "CaDiCaL SAT-only", fFancy );
                }
            }
            else
            {
                pModel = Acb_NtkSolve( pGia, fVerbose, &Status );
            }
            if ( fCheckModel && pModel && !Acb_NtkCheckModelCex( pGiaF, pGiaG, pModel, fVerbose ) )
            {
                ABC_FREE( pModel );
                pModel = NULL;
                Status = -1;
                printf( "The SAT model is not a valid XEC counterexample; treating the result as UNDECIDED.\n" );
            }
        }
        Acb_OutputFile( pFileNames[2], pNtkF, pModel, Status );
        ABC_FREE( pModel );
    }

    Gia_ManStopP( &pGiaX );
    Gia_ManStopP( &pGiaCut );
    Gia_ManStopP( &pGiaFCut );
    Gia_ManStopP( &pGiaGCut );
    Gia_ManStopP( &pGiaGCtrl );
    Gia_ManStopP( &pGia );
    Gia_ManStopP( &pGiaF );
    Gia_ManStopP( &pGiaG );
    Vec_IntFreeP( &vCutObjsF );
    Vec_IntFreeP( &vCutObjsG );
    Vec_IntFreeP( &vMuxSelectorsG );
    Vec_IntFreeP( &vMuxPoSelIdsG );
    Vec_IntFreeP( &vSymCutObjsF );
    Vec_IntFreeP( &vSymMuxSelectorsF );
    Vec_IntFreeP( &vSymIntDcObjsF );
    Vec_IntFreeP( &vSymIntDcCtrlsF );
    Vec_IntFreeP( &vSymIntDcCtrlIdsF );
    Vec_IntFreeP( &vIntDcObjsG );
    Vec_IntFreeP( &vIntDcCtrlsG );
    Vec_IntFreeP( &vIntDcCtrlIdsG );
    Vec_IntFreeP( &vDcDataObjsG );
    Vec_IntFreeP( &vDcCtrlObjsG );
    Acb_XecCtxFree( &XecCtx );

    Acb_ManFree( pNtkF->pDesign );
    Acb_ManFree( pNtkG->pDesign );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
