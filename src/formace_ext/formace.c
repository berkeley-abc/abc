/**CFile****************************************************************

  FileName    [formace.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ForMACE extension commands.]

  Synopsis    [Experimental extension commands for ForMACE work.]

***********************************************************************/

#include "base/main/mainInt.h"
#include "base/abc/abc.h"
#include "base/cmd/cmd.h"
#include "misc/extra/extra.h"
#include "aig/aig/aig.h"
#include "proof/int/int.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "sat/cadical/cadicalSolver.h"
#include "formace_ext/fm_camus.h"
#include "formace_ext/fm_minunsat.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void ForMace_Init( Abc_Frame_t * pAbc );
static void ForMace_End( Abc_Frame_t * pAbc );
static int  ForMace_CommandSummary( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  ForMace_CommandInter( Abc_Frame_t * pAbc, int argc, char ** argv );
static int  ForMace_CommandBmcInter( Abc_Frame_t * pAbc, int argc, char ** argv );

static int          ForMace_AigIsUnsat( Aig_Man_t * pMan );
static int          ForMace_IsUnsat( Aig_Man_t * pManOn, Aig_Man_t * pManOff, Vec_Int_t * vShared );
static Aig_Man_t *  ForMace_AigInter( Aig_Man_t * pManOn, Aig_Man_t * pManOff, Vec_Int_t * vShared, int fVerbose );
static Vec_Int_t *  ForMace_FindCamusShared( Aig_Man_t * pManOn, Aig_Man_t * pManOff, Vec_Int_t * vCandidates, int fMinimum );
static void         ForMace_CollectSupport_rec( Aig_Man_t * pMan, Aig_Obj_t * pObj, Vec_Int_t * vSupport );
static Vec_Int_t *  ForMace_CollectAigSupport( Aig_Man_t * pMan );
static Vec_Int_t *  ForMace_TrimAigInputs( Aig_Man_t * pMan, Vec_Int_t * vSelected );
static Abc_Ntk_t *  ForMace_NtkFromAig( Aig_Man_t * pMan, Abc_Ntk_t * pNtkNames, Vec_Int_t * vPiMap );
static Abc_Ntk_t *  ForMace_NtkConst( Abc_Ntk_t * pNtkNames, int fValue );
static Abc_Ntk_t *  ForMace_NtkInterOne( Abc_Frame_t * pAbc, Abc_Ntk_t * pNtkOn, Abc_Ntk_t * pNtkOff, int fHybrid, int fCamus, int nLimit, int fVerbose );
static void         ForMace_PrintSelected( FILE * pOut, const char * pLabel, Abc_Ntk_t * pNtk, Vec_Int_t * vSelected );

extern Aig_Man_t *  Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern int          Abc_NtkDarBmcInter( Abc_Ntk_t * pNtk, Inter_ManParams_t * pPars, Abc_Ntk_t ** ppNtkRes );

static Abc_FrameInitializer_t ForMace_FrameInitializer = { ForMace_Init, ForMace_End, NULL, NULL };

#if defined(__GNUC__)
static void ForMace_Register( void ) __attribute__((constructor));
static void ForMace_Register( void )
{
    Abc_FrameAddInitializer( &ForMace_FrameInitializer );
}
#else
#error "ForMACE extension registration currently requires a compiler with constructor attributes."
#endif

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static void ForMace_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "ForMACE", "fm_summary", ForMace_CommandSummary, 0 );
    Cmd_CommandAdd( pAbc, "ForMACE", "fm_minunsat", Fm_CommandMinUnsat, 0 );
    Cmd_CommandAdd( pAbc, "ForMACE", "fm_inter", ForMace_CommandInter, 1 );
    Cmd_CommandAdd( pAbc, "ForMACE", "fm_int", ForMace_CommandBmcInter, 0 );
}

static void ForMace_End( Abc_Frame_t * pAbc )
{
}

static int ForMace_CommandSummary( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    int c;
    int fVerbose = 0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( argc != globalUtilOptind )
        goto usage;

    pNtk = Abc_FrameReadNtk( pAbc );
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "There is no current network.\n" );
        return 1;
    }

    fprintf( pAbc->Out, "ForMACE summary for \"%s\":\n", Abc_NtkName(pNtk) );
    fprintf( pAbc->Out, "  pi      = %d\n", Abc_NtkPiNum(pNtk) );
    fprintf( pAbc->Out, "  po      = %d\n", Abc_NtkPoNum(pNtk) );
    fprintf( pAbc->Out, "  latches = %d\n", Abc_NtkLatchNum(pNtk) );
    fprintf( pAbc->Out, "  nodes   = %d\n", Abc_NtkNodeNum(pNtk) );
    fprintf( pAbc->Out, "  levels  = %d\n", Abc_NtkLevel(pNtk) );

    if ( fVerbose )
    {
        fprintf( pAbc->Out, "  objects = %d\n", Abc_NtkObjNum(pNtk) );
        fprintf( pAbc->Out, "  type    = %s\n", Abc_NtkIsStrash(pNtk) ? "strashed AIG" : "logic network" );
        fprintf( pAbc->Out, "  seq     = %s\n", Abc_NtkIsComb(pNtk) ? "combinational" : "sequential" );
    }

    return 0;

usage:
    fprintf( pAbc->Err, "usage: fm_summary [-vh]\n" );
    fprintf( pAbc->Err, "\t-v    : toggle verbose network details [default = %s]\n", fVerbose ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-h    : print the command usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [ForMACE interpolation-based model checking command.]

***********************************************************************/
static int ForMace_CommandBmcInter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Inter_ManParams_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk( pAbc );
    int c, fOriginal = 0, fMinvar = 0, fHybrid = 0, nLimit = 16;

    Inter_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "C:F:S:T:K:I:L:omyairtcgvh")) != EOF )
    {
        switch ( c )
        {
        case 'C': pPars->nBTLimit = atoi(globalUtilOptarg); break;
        case 'F': pPars->nFramesMax = atoi(globalUtilOptarg); break;
        case 'S': pPars->nFramesStart = atoi(globalUtilOptarg); break;
        case 'T': pPars->nSecLimit = atoi(globalUtilOptarg); break;
        case 'K': pPars->nFramesK = atoi(globalUtilOptarg); break;
        case 'I': pPars->pFileName = (char *)globalUtilOptarg; break;
        case 'L': nLimit = atoi(globalUtilOptarg); break;
        case 'o': fOriginal = 1; break;
        case 'm': fMinvar = 1; break;
        case 'y': fHybrid = 1; break;
        case 'a': pPars->fUseAllFrames = 1; break;
        case 'i': pPars->fDropInvar = 1; break;
        case 'r': pPars->fRewrite = 1; break;
        case 't': pPars->fTransLoop = 1; break;
        case 'c': pPars->fCheckKstep ^= 1; break;
        case 'g': pPars->fUseBias = 1; break;
        case 'v': pPars->fVerbose = 1; break;
        case 'h': goto usage;
        default: goto usage;
        }
    }
    if ( argc != globalUtilOptind || fOriginal + fMinvar + fHybrid != 1 || pPars->nBTLimit < 0 || pPars->nFramesMax < 0 || pPars->nFramesStart <= 0 || pPars->nSecLimit < 0 || pPars->nFramesK < 0 || nLimit < 0 )
        goto usage;
    if ( pNtk == NULL )
    {
        fprintf( pAbc->Err, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        fprintf( pAbc->Err, "ForMACE fm_int requires a structurally hashed circuit; run strash first.\n" );
        return 1;
    }
    if ( pAbc->fBatchMode && (pAbc->Status == 0 || pAbc->Status == 1) )
    {
        fprintf( pAbc->Out, "The miter is already solved; skipping the command.\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 || Abc_NtkPiNum(pNtk) == 0 )
    {
        fprintf( pAbc->Err, "ForMACE fm_int requires a sequential circuit with at least one primary input.\n" );
        return 1;
    }
    if ( Abc_NtkConstrNum(pNtk) != 0 )
    {
        fprintf( pAbc->Err, "ForMACE fm_int does not support constraints; use fold before running it.\n" );
        return 1;
    }
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        fprintf( pAbc->Err, "ForMACE fm_int currently requires exactly one property output.\n" );
        return 1;
    }

    pPars->fForMaceMinvar = fMinvar;
    pPars->fForMaceHybrid = fHybrid;
    pPars->nForMaceVarLimit = nLimit;
    if ( pPars->fVerbose )
        fprintf( pAbc->Out, "ForMACE fm_int partition: suffix k = %d, bad states = %s.\n", pPars->nFramesStart, pPars->fUseAllFrames ? "1..k" : "k only" );
    pAbc->Status = Abc_NtkDarBmcInter( pNtk, pPars, NULL );
    pAbc->nFrames = pPars->iFrameMax;
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    return 0;

usage:
    fprintf( pAbc->Err, "usage: fm_int (-o | -m | -y) [-CFSTK num] [-I file] [-L num] [-airtcgvh]\n" );
    fprintf( pAbc->Err, "\t-o       : original ABC interpolation without boundary minimization\n" );
    fprintf( pAbc->Err, "\t-m       : exact minvar search over latch-boundary equality groups\n" );
    fprintf( pAbc->Err, "\t-y       : hybrid search from baseline interpolant latch support\n" );
    fprintf( pAbc->Err, "\t-L num   : maximum candidates for exact search [default = %d]\n", nLimit );
    fprintf( pAbc->Err, "\t-C num   : conflict limit per SAT call [default = %d]\n", pPars->nBTLimit );
    fprintf( pAbc->Err, "\t-F num   : maximum interpolation frames [default = %d]\n", pPars->nFramesMax );
    fprintf( pAbc->Err, "\t-S num   : initial suffix length k [default = %d]\n", pPars->nFramesStart );
    fprintf( pAbc->Err, "\t-T num   : runtime limit in seconds [default = %d]\n", pPars->nSecLimit );
    fprintf( pAbc->Err, "\t-K num   : induction-check depth [default = %d]\n", pPars->nFramesK );
    fprintf( pAbc->Err, "\t-I file  : invariant/interpolant output file\n" );
    fprintf( pAbc->Err, "\t-i       : dump invariant/interpolants\n" );
    fprintf( pAbc->Err, "\t-a       : OR Bad over all suffix states 1..k [default = final state k only]\n" );
    fprintf( pAbc->Err, "\t-r       : rewrite unrolled timeframes\n" );
    fprintf( pAbc->Err, "\t-t       : add transition into the initial state\n" );
    fprintf( pAbc->Err, "\t-c       : toggle inductive containment checking [default = %s]\n", pPars->fCheckKstep ? "yes" : "no" );
    fprintf( pAbc->Err, "\t-g       : bias SAT decisions toward global variables\n" );
    fprintf( pAbc->Err, "\t-v       : print verbose statistics\n" );
    fprintf( pAbc->Err, "\t-h       : print this usage\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Tests whether an asserted AIG output is UNSAT.]

***********************************************************************/
static int ForMace_AigIsUnsat( Aig_Man_t * pMan )
{
    Cnf_Dat_t * pCnf;
    cadical_solver * pSat;
    int i, fUnsat = 0;

    pCnf = Cnf_DeriveSimple( pMan, 0 );
    pSat = cadical_solver_new();
    cadical_solver_setnvars( pSat, pCnf->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !cadical_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
        {
            fUnsat = 1;
            break;
        }
    if ( !fUnsat )
        fUnsat = cadical_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 ) == l_False;
    Cnf_DataFree( pCnf );
    cadical_solver_delete( pSat );
    return fUnsat;
}

/**Function*************************************************************

  Synopsis    [Tests the selected shared-PI equality partition.]

***********************************************************************/
static int ForMace_IsUnsat( Aig_Man_t * pManOn, Aig_Man_t * pManOff, Vec_Int_t * vShared )
{
    Cnf_Dat_t * pCnfOn, * pCnfOff;
    cadical_solver * pSat;
    Aig_Obj_t * pObjOn, * pObjOff;
    int Lits[2], i, iPi, fUnsat = 0;

    pCnfOn  = Cnf_DeriveSimple( pManOn, 0 );
    pCnfOff = Cnf_DeriveSimple( pManOff, 0 );
    Cnf_DataLift( pCnfOff, pCnfOn->nVars );
    pSat = cadical_solver_new();
    cadical_solver_setnvars( pSat, pCnfOn->nVars + pCnfOff->nVars );

    for ( i = 0; i < pCnfOn->nClauses; i++ )
        if ( !cadical_solver_addclause( pSat, pCnfOn->pClauses[i], pCnfOn->pClauses[i+1] ) )
        {
            fUnsat = 1;
            goto finish;
        }
    for ( i = 0; i < pCnfOff->nClauses; i++ )
        if ( !cadical_solver_addclause( pSat, pCnfOff->pClauses[i], pCnfOff->pClauses[i+1] ) )
        {
            fUnsat = 1;
            goto finish;
        }

    Vec_IntForEachEntry( vShared, iPi, i )
    {
        pObjOn  = Aig_ManCi( pManOn, iPi );
        pObjOff = Aig_ManCi( pManOff, iPi );
        Lits[0] = toLitCond( pCnfOn->pVarNums[pObjOn->Id], 0 );
        Lits[1] = toLitCond( pCnfOff->pVarNums[pObjOff->Id], 1 );
        if ( !cadical_solver_addclause( pSat, Lits, Lits + 2 ) )
        {
            fUnsat = 1;
            goto finish;
        }
        Lits[0] = toLitCond( pCnfOn->pVarNums[pObjOn->Id], 1 );
        Lits[1] = toLitCond( pCnfOff->pVarNums[pObjOff->Id], 0 );
        if ( !cadical_solver_addclause( pSat, Lits, Lits + 2 ) )
        {
            fUnsat = 1;
            goto finish;
        }
    }
    fUnsat = cadical_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 ) == l_False;

finish:
    Cnf_DataFree( pCnfOn );
    Cnf_DataFree( pCnfOff );
    cadical_solver_delete( pSat );
    return fUnsat;
}

/**Function*************************************************************

  Synopsis    [Derives an interpolant using only the selected shared PIs.]

***********************************************************************/
static Aig_Man_t * ForMace_AigInter( Aig_Man_t * pManOn, Aig_Man_t * pManOff, Vec_Int_t * vShared, int fVerbose )
{
    void * pSatCnf = NULL;
    Inta_Man_t * pManInter;
    Aig_Man_t * pRes;
    Cnf_Dat_t * pCnfOn, * pCnfOff;
    sat_solver * pSat;
    Vec_Int_t * vVarsAB;
    Aig_Obj_t * pObjOn, * pObjOff;
    int Lits[2], i, iPi, fUnsatAtAdd = 0;

    pCnfOn  = Cnf_DeriveSimple( pManOn, 0 );
    pCnfOff = Cnf_DeriveSimple( pManOff, 0 );
    Cnf_DataLift( pCnfOff, pCnfOn->nVars );
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat );
    sat_solver_setnvars( pSat, pCnfOn->nVars + pCnfOff->nVars );

    for ( i = 0; i < pCnfOn->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnfOn->pClauses[i], pCnfOn->pClauses[i+1] ) )
        {
            fUnsatAtAdd = 1;
            break;
        }
    sat_solver_store_mark_clauses_a( pSat );

    if ( !fUnsatAtAdd )
        for ( i = 0; i < pCnfOff->nClauses; i++ )
            if ( !sat_solver_addclause( pSat, pCnfOff->pClauses[i], pCnfOff->pClauses[i+1] ) )
            {
                fUnsatAtAdd = 1;
                break;
            }

    vVarsAB = Vec_IntAlloc( Vec_IntSize(vShared) );
    if ( !fUnsatAtAdd )
        Vec_IntForEachEntry( vShared, iPi, i )
        {
            pObjOn  = Aig_ManCi( pManOn, iPi );
            pObjOff = Aig_ManCi( pManOff, iPi );
            Vec_IntPush( vVarsAB, pCnfOn->pVarNums[pObjOn->Id] );
            Lits[0] = toLitCond( pCnfOn->pVarNums[pObjOn->Id], 0 );
            Lits[1] = toLitCond( pCnfOff->pVarNums[pObjOff->Id], 1 );
            if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
            {
                fUnsatAtAdd = 1;
                break;
            }
            Lits[0] = toLitCond( pCnfOn->pVarNums[pObjOn->Id], 1 );
            Lits[1] = toLitCond( pCnfOff->pVarNums[pObjOff->Id], 0 );
            if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
            {
                fUnsatAtAdd = 1;
                break;
            }
        }

    Cnf_DataFree( pCnfOn );
    Cnf_DataFree( pCnfOff );
    sat_solver_store_mark_roots( pSat );
    if ( sat_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 ) == l_False )
        pSatCnf = sat_solver_store_release( pSat );
    sat_solver_delete( pSat );
    if ( pSatCnf == NULL )
    {
        Vec_IntFree( vVarsAB );
        return NULL;
    }

    pManInter = Inta_ManAlloc();
    pRes = (Aig_Man_t *)Inta_ManInterpolate( pManInter, (Sto_Man_t *)pSatCnf, 0, vVarsAB, fVerbose );
    Inta_ManFree( pManInter );
    Vec_IntFree( vVarsAB );
    Sto_ManFree( (Sto_Man_t *)pSatCnf );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Finds a CAMUS-selected shared PI set using the in-memory API.]

***********************************************************************/
static Vec_Int_t * ForMace_FindCamusShared( Aig_Man_t * pManOn, Aig_Man_t * pManOff, Vec_Int_t * vCandidates, int fMinimum )
{
    Cnf_Dat_t * pCnfOn = NULL, * pCnfOff = NULL;
    Fm_CamusMan_t * pCamus = NULL;
    Vec_Int_t * vResult = NULL;
    Aig_Obj_t * pObjOn, * pObjOff;
    int Lits[2], i;

    pCnfOn  = Cnf_DeriveSimple( pManOn, 0 );
    pCnfOff = Cnf_DeriveSimple( pManOff, 0 );
    Cnf_DataLift( pCnfOff, pCnfOn->nVars );
    pCamus = Fm_CamusStart( pCnfOn->nVars + pCnfOff->nVars, Aig_ManCiNum(pManOn) );
    if ( pCamus == NULL )
        goto finish;
    for ( i = 0; i < pCnfOn->nClauses; i++ )
        if ( !Fm_CamusAddBackground(pCamus, pCnfOn->pClauses[i], pCnfOn->pClauses[i+1] - pCnfOn->pClauses[i]) )
            goto finish;
    for ( i = 0; i < pCnfOff->nClauses; i++ )
        if ( !Fm_CamusAddBackground(pCamus, pCnfOff->pClauses[i], pCnfOff->pClauses[i+1] - pCnfOff->pClauses[i]) )
            goto finish;
    for ( i = 0; i < Aig_ManCiNum(pManOn); i++ )
    {
        pObjOn  = Aig_ManCi( pManOn, i );
        pObjOff = Aig_ManCi( pManOff, i );
        Lits[0] = toLitCond( pCnfOn->pVarNums[pObjOn->Id], 0 );
        Lits[1] = toLitCond( pCnfOff->pVarNums[pObjOff->Id], 1 );
        if ( !Fm_CamusAddGroup(pCamus, i, Lits, 2) )
            goto finish;
        Lits[0] = toLitCond( pCnfOn->pVarNums[pObjOn->Id], 1 );
        Lits[1] = toLitCond( pCnfOff->pVarNums[pObjOff->Id], 0 );
        if ( !Fm_CamusAddGroup(pCamus, i, Lits, 2) )
            goto finish;
    }
    vResult = fMinimum ? Fm_CamusFindMinimumMus(pCamus, vCandidates) : Fm_CamusFindMus(pCamus, vCandidates);

finish:
    Cnf_DataFree( pCnfOn );
    Cnf_DataFree( pCnfOff );
    Fm_CamusStop( pCamus );
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Collects CI positions in an AIG output support.]

***********************************************************************/
static void ForMace_CollectSupport_rec( Aig_Man_t * pMan, Aig_Obj_t * pObj, Vec_Int_t * vSupport )
{
    pObj = Aig_Regular( pObj );
    if ( Aig_ObjIsTravIdCurrent(pMan, pObj) )
        return;
    Aig_ObjSetTravIdCurrent( pMan, pObj );
    if ( Aig_ObjIsCi(pObj) )
    {
        Vec_IntPush( vSupport, Aig_ObjCioId(pObj) );
        return;
    }
    if ( Aig_ObjIsConst1(pObj) )
        return;
    ForMace_CollectSupport_rec( pMan, Aig_ObjFanin0(pObj), vSupport );
    if ( Aig_ObjFanin1(pObj) )
        ForMace_CollectSupport_rec( pMan, Aig_ObjFanin1(pObj), vSupport );
}

/**Function*************************************************************

  Synopsis    [Returns sorted CI positions used by the first AIG output.]

***********************************************************************/
static Vec_Int_t * ForMace_CollectAigSupport( Aig_Man_t * pMan )
{
    Vec_Int_t * vSupport;
    vSupport = Vec_IntAlloc( Aig_ManCiNum(pMan) );
    Aig_ManSetCioIds( pMan );
    Aig_ManIncrementTravId( pMan );
    Aig_ObjSetTravIdCurrent( pMan, Aig_ManConst1(pMan) );
    ForMace_CollectSupport_rec( pMan, Aig_ObjFanin0(Aig_ManCo(pMan, 0)), vSupport );
    Vec_IntSort( vSupport, 0 );
    Aig_ManCleanCioIds( pMan );
    return vSupport;
}

/**Function*************************************************************

  Synopsis    [Prunes unused AIG CIs and returns their original PI positions.]

***********************************************************************/
static Vec_Int_t * ForMace_TrimAigInputs( Aig_Man_t * pMan, Vec_Int_t * vSelected )
{
    Vec_Int_t * vSupport, * vPiMap;
    int i, iCi;

    vSupport = ForMace_CollectAigSupport( pMan );
    vPiMap = Vec_IntAlloc( Vec_IntSize(vSupport) );
    Vec_IntForEachEntry( vSupport, iCi, i )
        Vec_IntPush( vPiMap, Vec_IntEntry(vSelected, iCi) );
    Vec_IntFree( vSupport );
    Aig_ManCiCleanup( pMan );
    return vPiMap;
}

/**Function*************************************************************

  Synopsis    [Converts an interpolant AIG while preserving selected PI names.]

***********************************************************************/
static Abc_Ntk_t * ForMace_NtkFromAig( Aig_Man_t * pMan, Abc_Ntk_t * pNtkNames, Vec_Int_t * vPiMap )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pPi, * pPo;
    Aig_Obj_t * pObj;
    int i, iPi;

    if ( Aig_ManCiNum(pMan) != Vec_IntSize(vPiMap) )
        return NULL;
    pNtkNew = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1 );
    pNtkNew->pName = Extra_UtilStrsav( pNtkNames->pName ? pNtkNames->pName : "fm_inter" );
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    for ( i = 0; i < Abc_NtkPiNum(pNtkNames); i++ )
    {
        pPi = Abc_NtkCreatePi( pNtkNew );
        Abc_ObjAssignName( pPi, Abc_ObjName(Abc_NtkPi(pNtkNames, i)), NULL );
    }
    Aig_ManForEachCi( pMan, pObj, i )
    {
        iPi = Vec_IntEntry( vPiMap, i );
        pObj->pData = Abc_NtkPi( pNtkNew, iPi );
    }
    vNodes = Aig_ManDfs( pMan, 1 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = Aig_ObjChild0Copy( pObj );
        else
            pObj->pData = Abc_AigAnd( (Abc_Aig_t *)pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    pPo = Abc_NtkCreatePo( pNtkNew );
    Abc_ObjAssignName( pPo, Abc_ObjName(Abc_NtkPo(pNtkNames, 0)), NULL );
    Abc_ObjAddFanin( pPo, (Abc_Obj_t *)Aig_ObjChild0Copy(Aig_ManCo(pMan, 0)) );
    if ( !Abc_NtkCheck(pNtkNew) )
    {
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Creates a constant interpolant network.]

***********************************************************************/
static Abc_Ntk_t * ForMace_NtkConst( Abc_Ntk_t * pNtkNames, int fValue )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pPo, * pConst;

    pNtkNew = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1 );
    pNtkNew->pName = Extra_UtilStrsav( pNtkNames->pName ? pNtkNames->pName : "fm_inter" );
    pPo = Abc_NtkCreatePo( pNtkNew );
    Abc_ObjAssignName( pPo, Abc_ObjName(Abc_NtkPo(pNtkNames, 0)), NULL );
    pConst = Abc_AigConst1( pNtkNew );
    Abc_ObjAddFanin( pPo, fValue ? pConst : Abc_ObjNot(pConst) );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Prints selected original PI names.]

***********************************************************************/
static void ForMace_PrintSelected( FILE * pOut, const char * pLabel, Abc_Ntk_t * pNtk, Vec_Int_t * vSelected )
{
    int i, iPi;
    fprintf( pOut, "ForMACE %s (%d):", pLabel, Vec_IntSize(vSelected) );
    Vec_IntForEachEntry( vSelected, iPi, i )
        fprintf( pOut, " %s", Abc_ObjName(Abc_NtkPi(pNtk, iPi)) );
    if ( Vec_IntSize(vSelected) == 0 )
        fprintf( pOut, " (none)" );
    fprintf( pOut, "\n" );
}

/**Function*************************************************************

  Synopsis    [Runs the minvar or hybrid interpolation flow.]

***********************************************************************/
static Abc_Ntk_t * ForMace_NtkInterOne( Abc_Frame_t * pAbc, Abc_Ntk_t * pNtkOn, Abc_Ntk_t * pNtkOff, int fHybrid, int fCamus, int nLimit, int fVerbose )
{
    Aig_Man_t * pManOn = NULL, * pManOff = NULL, * pManAig = NULL, * pManBase = NULL;
    Abc_Ntk_t * pNtkRes = NULL;
    Vec_Int_t * vAll = NULL, * vCandidates = NULL, * vSelected = NULL, * vPiMap = NULL, * vEmpty = NULL;
    int i, fFallback = 0;

    pManOn = Abc_NtkToDar( pNtkOn, 0, 0 );
    pManOff = Abc_NtkToDar( pNtkOff, 0, 0 );
    if ( pManOn == NULL || pManOff == NULL )
        goto finish;
    vAll = Vec_IntAlloc( Aig_ManCiNum(pManOn) );
    for ( i = 0; i < Aig_ManCiNum(pManOn); i++ )
        Vec_IntPush( vAll, i );

    if ( !ForMace_IsUnsat(pManOn, pManOff, vAll) )
    {
        fprintf( pAbc->Err, "ForMACE interpolation requires the onset and offset to be disjoint under all paired PIs.\n" );
        goto finish;
    }
    vEmpty = Vec_IntAlloc( 0 );
    if ( ForMace_IsUnsat(pManOn, pManOff, vEmpty) )
    {
        int fOnUnsat = ForMace_AigIsUnsat( pManOn );
        pNtkRes = ForMace_NtkConst( pNtkOn, !fOnUnsat );
        ForMace_PrintSelected( pAbc->Out, "selected shared PIs", pNtkOn, vEmpty );
        goto finish;
    }

    if ( fHybrid )
    {
        pManBase = ForMace_AigInter( pManOn, pManOff, vAll, fVerbose );
        if ( pManBase == NULL )
        {
            fprintf( pAbc->Err, "ForMACE hybrid could not derive its baseline interpolant; using all PIs as candidates.\n" );
            vCandidates = Vec_IntDup( vAll );
        }
        else
        {
            vCandidates = ForMace_CollectAigSupport( pManBase );
            Aig_ManStop( pManBase );
            pManBase = NULL;
            if ( !ForMace_IsUnsat(pManOn, pManOff, vCandidates) )
            {
                fprintf( pAbc->Out, "ForMACE hybrid baseline support is insufficient after PI privatization; using all PIs as candidates.\n" );
                Vec_IntFree( vCandidates );
                vCandidates = Vec_IntDup( vAll );
                fFallback = 1;
            }
        }
    }
    else
        vCandidates = Vec_IntDup( vAll );

    if ( !fCamus && Vec_IntSize(vCandidates) > nLimit )
    {
        fprintf( pAbc->Err, "ForMACE exact search has %d candidate PIs, exceeding -L %d.\n", Vec_IntSize(vCandidates), nLimit );
        goto finish;
    }
    ForMace_PrintSelected( pAbc->Out, fCamus ? "CAMUS candidates" : (fHybrid ? "hybrid candidates" : "minvar candidates"), pNtkOn, vCandidates );
    vSelected = ForMace_FindCamusShared( pManOn, pManOff, vCandidates, !fCamus );
    if ( vSelected == NULL )
    {
        fprintf( pAbc->Err, "ForMACE CAMUS could not find the requested shared-PI set.\n" );
        goto finish;
    }
    ForMace_PrintSelected( pAbc->Out, fCamus ? "CAMUS MUS shared PIs" : (fHybrid ? "CAMUS hybrid minimum shared PIs" : "CAMUS minimum shared PIs"), pNtkOn, vSelected );
    pManAig = ForMace_AigInter( pManOn, pManOff, vSelected, fVerbose );
    if ( pManAig == NULL )
    {
        int fOnsetContained = 1, k;
        vPiMap = ForMace_CollectAigSupport( pManOn );
        Vec_IntForEachEntry( vPiMap, i, k )
            if ( Vec_IntFind(vSelected, i) == -1 )
            {
                fOnsetContained = 0;
                break;
            }
        if ( !fOnsetContained )
        {
            fprintf( pAbc->Err, "ForMACE proof interpolation failed for the selected PI set.\n" );
            goto finish;
        }
        pNtkRes = Abc_NtkDup( pNtkOn );
        fprintf( pAbc->Out, "ForMACE used the onset as a valid interpolant after a root-clause conflict.\n" );
    }
    else
    {
        vPiMap = ForMace_TrimAigInputs( pManAig, vSelected );
        pNtkRes = ForMace_NtkFromAig( pManAig, pNtkOn, vPiMap );
    }
    if ( pNtkRes == NULL )
        fprintf( pAbc->Err, "ForMACE could not convert the interpolant back into an ABC network.\n" );
    else
    {
        ForMace_PrintSelected( pAbc->Out, "selected shared PIs", pNtkOn, vSelected );
        ForMace_PrintSelected( pAbc->Out, "interpolant support", pNtkOn, vPiMap );
        if ( fFallback )
            fprintf( pAbc->Out, "ForMACE hybrid completed after its full-candidate fallback.\n" );
    }

finish:
    if ( pManOn ) Aig_ManStop( pManOn );
    if ( pManOff ) Aig_ManStop( pManOff );
    if ( pManAig ) Aig_ManStop( pManAig );
    if ( pManBase ) Aig_ManStop( pManBase );
    Vec_IntFreeP( &vAll );
    Vec_IntFreeP( &vCandidates );
    Vec_IntFreeP( &vSelected );
    Vec_IntFreeP( &vPiMap );
    Vec_IntFreeP( &vEmpty );
    return pNtkRes;
}

/**Function*************************************************************

  Synopsis    [ForMACE minimum-variable interpolation command.]

***********************************************************************/
static int ForMace_CommandInter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkOn, * pNtkOff, * pNtkRes;
    Abc_Obj_t * pObj;
    char ** pArgvNew;
    int nArgcNew, c, fDeleteOn, fDeleteOff, fMinvar = 0, fHybrid = 0, fCamus = 0, fVerbose = 0, nLimit = 16, i;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "mcyL:vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'm': fMinvar = 1; break;
        case 'c': fCamus = 1; break;
        case 'y': fHybrid = 1; break;
        case 'L':
            nLimit = atoi( globalUtilOptarg );
            if ( nLimit < 0 )
                goto usage;
            break;
        case 'v': fVerbose = 1; break;
        case 'h': goto usage;
        default: goto usage;
        }
    }
    if ( fMinvar + fHybrid + fCamus != 1 )
        goto usage;
    pNtk = Abc_FrameReadNtk( pAbc );
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( pAbc->Err, pNtk, pArgvNew, nArgcNew, &pNtkOn, &pNtkOff, &fDeleteOn, &fDeleteOff, 1 ) )
        return 1;
    if ( nArgcNew == 0 )
        Abc_NtkForEachPo( pNtkOff, pObj, i )
            Abc_ObjXorFaninC( pObj, 0 );
    if ( !Abc_NtkIsComb(pNtkOn) || !Abc_NtkIsComb(pNtkOff) || Abc_NtkCoNum(pNtkOn) != 1 || Abc_NtkCoNum(pNtkOff) != 1 )
    {
        fprintf( pAbc->Err, "ForMACE fm_inter currently requires two combinational, single-output networks.\n" );
        goto fail;
    }
    if ( Abc_NtkPiNum(pNtkOn) != Abc_NtkPiNum(pNtkOff) )
    {
        fprintf( pAbc->Err, "ForMACE fm_inter requires the same number of PIs.\n" );
        goto fail;
    }
    for ( i = 0; i < Abc_NtkPiNum(pNtkOn); i++ )
        if ( strcmp(Abc_ObjName(Abc_NtkPi(pNtkOn, i)), Abc_ObjName(Abc_NtkPi(pNtkOff, i))) )
        {
            fprintf( pAbc->Err, "ForMACE fm_inter PI %d differs: onset=%s offset=%s.\n", i, Abc_ObjName(Abc_NtkPi(pNtkOn, i)), Abc_ObjName(Abc_NtkPi(pNtkOff, i)) );
            goto fail;
        }

    pNtkRes = ForMace_NtkInterOne( pAbc, pNtkOn, pNtkOff, fHybrid, fCamus, nLimit, fVerbose );
    if ( fDeleteOn ) Abc_NtkDelete( pNtkOn );
    if ( fDeleteOff ) Abc_NtkDelete( pNtkOff );
    if ( pNtkRes == NULL )
        return 1;
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

fail:
    if ( fDeleteOn ) Abc_NtkDelete( pNtkOn );
    if ( fDeleteOff ) Abc_NtkDelete( pNtkOff );
    return 1;

usage:
    fprintf( pAbc->Err, "usage: fm_inter (-m | -c | -y) [-L num] [-vh] <onset.blif> <offset.blif>\n" );
    fprintf( pAbc->Err, "\t-m       : exact minvar search over all paired PIs\n" );
    fprintf( pAbc->Err, "\t-c       : CAMUS-style subset-minimal shared-PI selection\n" );
    fprintf( pAbc->Err, "\t-y       : hybrid search restricted to baseline interpolant support\n" );
    fprintf( pAbc->Err, "\t-L num   : maximum candidate PIs for exact search [default = %d]\n", nLimit );
    fprintf( pAbc->Err, "\t-v       : print proof interpolation statistics\n" );
    fprintf( pAbc->Err, "\t-h       : print this usage\n" );
    fprintf( pAbc->Err, "\t         One file uses the current network as onset; no files complements its spec as offset.\n" );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
