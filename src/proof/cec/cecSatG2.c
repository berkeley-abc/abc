/**CFile****************************************************************

  FileName    [cecSatG2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Detection of structural isomorphism.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSatG2.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig/gia/gia.h"
#include "misc/util/utilTruth.h"
#include "sat/glucose/AbcGlucose.h"
#include "cec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// SAT solving manager
typedef struct Cec4_Man_t_ Cec4_Man_t;
struct Cec4_Man_t_
{
    Cec_ParFra_t *   pPars;          // parameters
    Gia_Man_t *      pAig;           // user's AIG
    Gia_Man_t *      pNew;           // internal AIG
    // SAT solving
    bmcg_sat_solver* pSat;           // SAT solver
    Vec_Ptr_t *      vFrontier;      // CNF construction
    Vec_Ptr_t *      vFanins;        // CNF construction
    Vec_Wrd_t *      vSims;          // CI simulation info
    Vec_Int_t *      vCexMin;        // minimized CEX
    Vec_Int_t *      vClassUpdates;  // updated equiv classes
    Vec_Int_t *      vCexStamps;     // time stamps
    Vec_Int_t *      vCands;
    Vec_Int_t *      vVisit;
    Vec_Int_t *      vPat;
    int              iLastConst;     // last const node proved
    // statistics
    int              nPatterns;
    int              nSatSat;
    int              nSatUnsat;
    int              nSatUndec;
    int              nCallsSince;
    int              nSimulates;
    int              nRecycles;
    int              nConflicts[2][3];
    abctime          timeCnf;
    abctime          timeGenPats;
    abctime          timeSatSat0;
    abctime          timeSatUnsat0;
    abctime          timeSatSat;
    abctime          timeSatUnsat;
    abctime          timeSatUndec;
    abctime          timeSim;
    abctime          timeRefine;
    abctime          timeResimGlo;
    abctime          timeResimLoc;
    abctime          timeStart;
};

static inline int    Cec4_ObjSatId( Gia_Man_t * p, Gia_Obj_t * pObj )             { return Gia_ObjCopy2Array(p, Gia_ObjId(p, pObj));                                                     }
static inline int    Cec4_ObjSetSatId( Gia_Man_t * p, Gia_Obj_t * pObj, int Num ) { assert(Cec4_ObjSatId(p, pObj) == -1); Gia_ObjSetCopy2Array(p, Gia_ObjId(p, pObj), Num); Vec_IntPush(&p->vSuppVars, Gia_ObjId(p, pObj)); if ( Gia_ObjIsCi(pObj) ) Vec_IntPushTwo(&p->vCopiesTwo, Gia_ObjId(p, pObj), Num); return Num;  }
static inline void   Cec4_ObjCleanSatId( Gia_Man_t * p, Gia_Obj_t * pObj )        { assert(Cec4_ObjSatId(p, pObj) != -1); Gia_ObjSetCopy2Array(p, Gia_ObjId(p, pObj), -1);               }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cec4_Man_t * Cec4_ManCreate( Gia_Man_t * pAig, Cec_ParFra_t * pPars )
{
    Cec4_Man_t * p = ABC_CALLOC( Cec4_Man_t, 1 );
    memset( p, 0, sizeof(Cec4_Man_t) );
    p->timeStart     = Abc_Clock();
    p->pPars         = pPars;
    p->pAig          = pAig;
    p->pSat          = bmcg_sat_solver_start();
    p->vFrontier     = Vec_PtrAlloc( 1000 );
    p->vFanins       = Vec_PtrAlloc( 100 );
    p->vCexMin       = Vec_IntAlloc( 100 );
    p->vClassUpdates = Vec_IntAlloc( 100 );
    p->vCexStamps    = Vec_IntStart( Gia_ManObjNum(pAig) );
    p->vCands        = Vec_IntAlloc( 100 );
    p->vVisit        = Vec_IntAlloc( 100 );
    p->vPat          = Vec_IntAlloc( 100 );
    //pAig->pData     = p->pSat; // point AIG manager to the solver
    return p;
}
void Cec4_ManDestroy( Cec4_Man_t * p )
{
    if ( p->pPars->fVerbose ) 
    {
        abctime timeTotal = Abc_Clock() - p->timeStart;
        abctime timeSat   = p->timeSatSat0 + p->timeSatSat + p->timeSatUnsat0 + p->timeSatUnsat + p->timeSatUndec;
        abctime timeOther = timeTotal - timeSat - p->timeSim - p->timeRefine - p->timeResimLoc - p->timeGenPats;// - p->timeResimGlo;
        ABC_PRTP( "SAT solving  ", timeSat,          timeTotal );
        ABC_PRTP( "  sat(easy)  ", p->timeSatSat0,   timeTotal );
        ABC_PRTP( "  sat        ", p->timeSatSat,    timeTotal );
        ABC_PRTP( "  unsat(easy)", p->timeSatUnsat0, timeTotal );
        ABC_PRTP( "  unsat      ", p->timeSatUnsat,  timeTotal );
        ABC_PRTP( "  fail       ", p->timeSatUndec,  timeTotal );
        ABC_PRTP( "Generate CNF ", p->timeCnf,       timeTotal );
        ABC_PRTP( "Generate pats", p->timeGenPats,   timeTotal );
        ABC_PRTP( "Simulation   ", p->timeSim,       timeTotal );
        ABC_PRTP( "Refinement   ", p->timeRefine,    timeTotal );
        ABC_PRTP( "Resim global ", p->timeResimGlo,  timeTotal );
        ABC_PRTP( "Resim local  ", p->timeResimLoc,  timeTotal );
        ABC_PRTP( "Other        ", timeOther,        timeTotal );
        ABC_PRTP( "TOTAL        ", timeTotal,        timeTotal );
        fflush( stdout );
    }
    Vec_WrdFreeP( &p->pAig->vSims );
    Gia_ManCleanMark01( p->pAig );
    bmcg_sat_solver_stop( p->pSat );
    Gia_ManStopP( &p->pNew );
    Vec_PtrFreeP( &p->vFrontier );
    Vec_PtrFreeP( &p->vFanins );
    Vec_IntFreeP( &p->vCexMin );
    Vec_IntFreeP( &p->vClassUpdates );
    Vec_IntFreeP( &p->vCexStamps );
    Vec_IntFreeP( &p->vCands );
    Vec_IntFreeP( &p->vVisit );
    Vec_IntFreeP( &p->vPat );
    ABC_FREE( p );
}
Gia_Man_t * Cec4_ManStartNew( Gia_Man_t * pAig )
{
    Gia_Obj_t * pObj; int i;
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(pAig) );
    pNew->pName = Abc_UtilStrsav( pAig->pName );
    pNew->pSpec = Abc_UtilStrsav( pAig->pSpec );
    Gia_ManFillValue( pAig );
    Gia_ManConst0(pAig)->Value = 0;
    Gia_ManForEachCi( pAig, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManHashAlloc( pNew );
    Vec_IntFill( &pNew->vCopies2, Gia_ManObjNum(pAig), -1 );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(pAig) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Adds clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec4_AddClausesMux( Gia_Man_t * p, Gia_Obj_t * pNode, bmcg_sat_solver * pSat )
{
    int fPolarFlip = 0;
    Gia_Obj_t * pNodeI, * pNodeT, * pNodeE;
    int pLits[4], RetValue, VarF, VarI, VarT, VarE, fCompT, fCompE;

    assert( !Gia_IsComplement( pNode ) );
    assert( pNode->fMark0 );
    // get nodes (I = if, T = then, E = else)
    pNodeI = Gia_ObjRecognizeMux( pNode, &pNodeT, &pNodeE );
    // get the variable numbers
    VarF = Cec4_ObjSatId(p, pNode);
    VarI = Cec4_ObjSatId(p, pNodeI);
    VarT = Cec4_ObjSatId(p, Gia_Regular(pNodeT));
    VarE = Cec4_ObjSatId(p, Gia_Regular(pNodeE));
    // get the complementation flags
    fCompT = Gia_IsComplement(pNodeT);
    fCompE = Gia_IsComplement(pNodeE);

    // f = ITE(i, t, e)

    // i' + t' + f
    // i' + t  + f'
    // i  + e' + f
    // i  + e  + f'

    // create four clauses
    pLits[0] = Abc_Var2Lit(VarI, 1);
    pLits[1] = Abc_Var2Lit(VarT, 1^fCompT);
    pLits[2] = Abc_Var2Lit(VarF, 0);
    if ( fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = Abc_LitNot( pLits[0] );
        if ( Gia_Regular(pNodeT)->fPhase )  pLits[1] = Abc_LitNot( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = Abc_LitNot( pLits[2] );
    }
    RetValue = bmcg_sat_solver_addclause( pSat, pLits, 3 );
    assert( RetValue );
    pLits[0] = Abc_Var2Lit(VarI, 1);
    pLits[1] = Abc_Var2Lit(VarT, 0^fCompT);
    pLits[2] = Abc_Var2Lit(VarF, 1);
    if ( fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = Abc_LitNot( pLits[0] );
        if ( Gia_Regular(pNodeT)->fPhase )  pLits[1] = Abc_LitNot( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = Abc_LitNot( pLits[2] );
    }
    RetValue = bmcg_sat_solver_addclause( pSat, pLits, 3 );
    assert( RetValue );
    pLits[0] = Abc_Var2Lit(VarI, 0);
    pLits[1] = Abc_Var2Lit(VarE, 1^fCompE);
    pLits[2] = Abc_Var2Lit(VarF, 0);
    if ( fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = Abc_LitNot( pLits[0] );
        if ( Gia_Regular(pNodeE)->fPhase )  pLits[1] = Abc_LitNot( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = Abc_LitNot( pLits[2] );
    }
    RetValue = bmcg_sat_solver_addclause( pSat, pLits, 3 );
    assert( RetValue );
    pLits[0] = Abc_Var2Lit(VarI, 0);
    pLits[1] = Abc_Var2Lit(VarE, 0^fCompE);
    pLits[2] = Abc_Var2Lit(VarF, 1);
    if ( fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = Abc_LitNot( pLits[0] );
        if ( Gia_Regular(pNodeE)->fPhase )  pLits[1] = Abc_LitNot( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = Abc_LitNot( pLits[2] );
    }
    RetValue = bmcg_sat_solver_addclause( pSat, pLits, 3 );
    assert( RetValue );

    // two additional clauses
    // t' & e' -> f'
    // t  & e  -> f 

    // t  + e   + f'
    // t' + e'  + f 

    if ( VarT == VarE )
    {
//        assert( fCompT == !fCompE );
        return;
    }

    pLits[0] = Abc_Var2Lit(VarT, 0^fCompT);
    pLits[1] = Abc_Var2Lit(VarE, 0^fCompE);
    pLits[2] = Abc_Var2Lit(VarF, 1);
    if ( fPolarFlip )
    {
        if ( Gia_Regular(pNodeT)->fPhase )  pLits[0] = Abc_LitNot( pLits[0] );
        if ( Gia_Regular(pNodeE)->fPhase )  pLits[1] = Abc_LitNot( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = Abc_LitNot( pLits[2] );
    }
    RetValue = bmcg_sat_solver_addclause( pSat, pLits, 3 );
    assert( RetValue );
    pLits[0] = Abc_Var2Lit(VarT, 1^fCompT);
    pLits[1] = Abc_Var2Lit(VarE, 1^fCompE);
    pLits[2] = Abc_Var2Lit(VarF, 0);
    if ( fPolarFlip )
    {
        if ( Gia_Regular(pNodeT)->fPhase )  pLits[0] = Abc_LitNot( pLits[0] );
        if ( Gia_Regular(pNodeE)->fPhase )  pLits[1] = Abc_LitNot( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = Abc_LitNot( pLits[2] );
    }
    RetValue = bmcg_sat_solver_addclause( pSat, pLits, 3 );
    assert( RetValue );
}
void Cec4_AddClausesSuper( Gia_Man_t * p, Gia_Obj_t * pNode, Vec_Ptr_t * vSuper, bmcg_sat_solver * pSat )
{
    int fPolarFlip = 0;
    Gia_Obj_t * pFanin;
    int * pLits, nLits, RetValue, i;
    assert( !Gia_IsComplement(pNode) );
    assert( Gia_ObjIsAnd( pNode ) );
    // create storage for literals
    nLits = Vec_PtrSize(vSuper) + 1;
    pLits = ABC_ALLOC( int, nLits );
    // suppose AND-gate is A & B = C
    // add !A => !C   or   A + !C
    Vec_PtrForEachEntry( Gia_Obj_t *, vSuper, pFanin, i )
    {
        pLits[0] = Abc_Var2Lit(Cec4_ObjSatId(p, Gia_Regular(pFanin)), Gia_IsComplement(pFanin));
        pLits[1] = Abc_Var2Lit(Cec4_ObjSatId(p, pNode), 1);
        if ( fPolarFlip )
        {
            if ( Gia_Regular(pFanin)->fPhase )  pLits[0] = Abc_LitNot( pLits[0] );
            if ( pNode->fPhase )                pLits[1] = Abc_LitNot( pLits[1] );
        }
        RetValue = bmcg_sat_solver_addclause( pSat, pLits, 2 );
        assert( RetValue );
    }
    // add A & B => C   or   !A + !B + C
    Vec_PtrForEachEntry( Gia_Obj_t *, vSuper, pFanin, i )
    {
        pLits[i] = Abc_Var2Lit(Cec4_ObjSatId(p, Gia_Regular(pFanin)), !Gia_IsComplement(pFanin));
        if ( fPolarFlip )
        {
            if ( Gia_Regular(pFanin)->fPhase )  pLits[i] = Abc_LitNot( pLits[i] );
        }
    }
    pLits[nLits-1] = Abc_Var2Lit(Cec4_ObjSatId(p, pNode), 0);
    if ( fPolarFlip )
    {
        if ( pNode->fPhase )  pLits[nLits-1] = Abc_LitNot( pLits[nLits-1] );
    }
    RetValue = bmcg_sat_solver_addclause( pSat, pLits, nLits );
    assert( RetValue );
    ABC_FREE( pLits );
}

/**Function*************************************************************

  Synopsis    [Adds clauses and returns CNF variable of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec4_CollectSuper_rec( Gia_Obj_t * pObj, Vec_Ptr_t * vSuper, int fFirst, int fUseMuxes )
{
    // if the new node is complemented or a PI, another gate begins
    if ( Gia_IsComplement(pObj) || Gia_ObjIsCi(pObj) || 
         (!fFirst && Gia_ObjValue(pObj) > 1) || 
         (fUseMuxes && pObj->fMark0) )
    {
        Vec_PtrPushUnique( vSuper, pObj );
        return;
    }
    // go through the branches
    Cec4_CollectSuper_rec( Gia_ObjChild0(pObj), vSuper, 0, fUseMuxes );
    Cec4_CollectSuper_rec( Gia_ObjChild1(pObj), vSuper, 0, fUseMuxes );
}
void Cec4_CollectSuper( Gia_Obj_t * pObj, int fUseMuxes, Vec_Ptr_t * vSuper )
{
    assert( !Gia_IsComplement(pObj) );
    assert( !Gia_ObjIsCi(pObj) );
    Vec_PtrClear( vSuper );
    Cec4_CollectSuper_rec( pObj, vSuper, 1, fUseMuxes );
}
void Cec4_ObjAddToFrontier( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Ptr_t * vFrontier, bmcg_sat_solver * pSat )
{
    assert( !Gia_IsComplement(pObj) );
    assert( !Gia_ObjIsConst0(pObj) );
    if ( Cec4_ObjSatId(p, pObj) >= 0 )
        return;
    assert( Cec4_ObjSatId(p, pObj) == -1 );
    Cec4_ObjSetSatId( p, pObj, bmcg_sat_solver_addvar(pSat) );
    if ( Gia_ObjIsAnd(pObj) )
        Vec_PtrPush( vFrontier, pObj );
}
int Cec4_ObjGetCnfVar( Cec4_Man_t * p, int iObj )
{ 
    int fUseAnd2  = 1; // enable simple CNF
    int fUseMuxes = 1; // enable MUXes when using complex CNF
    Gia_Obj_t * pNode, * pFanin;
    Gia_Obj_t * pObj = Gia_ManObj(p->pNew, iObj);
    int i, k;
    // quit if CNF is ready
    if ( Cec4_ObjSatId(p->pNew,pObj) >= 0 )
        return Cec4_ObjSatId(p->pNew,pObj);
    assert( iObj > 0 );
    if ( Gia_ObjIsCi(pObj) )
        return Cec4_ObjSetSatId( p->pNew, pObj, bmcg_sat_solver_addvar(p->pSat) );
    assert( Gia_ObjIsAnd(pObj) );
    if ( fUseAnd2 )
    {
        Cec4_ObjGetCnfVar( p, Gia_ObjFaninId0(pObj, iObj) );
        Cec4_ObjGetCnfVar( p, Gia_ObjFaninId1(pObj, iObj) );
        Vec_PtrClear( p->vFanins );
        Vec_PtrPush( p->vFanins, Gia_ObjChild0(pObj) );
        Vec_PtrPush( p->vFanins, Gia_ObjChild1(pObj) );
        Cec4_ObjSetSatId( p->pNew, pObj, bmcg_sat_solver_addvar(p->pSat) );
        Cec4_AddClausesSuper( p->pNew, pObj, p->vFanins, p->pSat );
        return Cec4_ObjSatId( p->pNew, pObj );
    }
    // start the frontier
    Vec_PtrClear( p->vFrontier );
    Cec4_ObjAddToFrontier( p->pNew, pObj, p->vFrontier, p->pSat );
    // explore nodes in the frontier
    Vec_PtrForEachEntry( Gia_Obj_t *, p->vFrontier, pNode, i )
    {
        // create the supergate
        assert( Cec4_ObjSatId(p->pNew,pNode) >= 0 );
        if ( fUseMuxes && pNode->fMark0 )
        {
            Vec_PtrClear( p->vFanins );
            Vec_PtrPushUnique( p->vFanins, Gia_ObjFanin0( Gia_ObjFanin0(pNode) ) );
            Vec_PtrPushUnique( p->vFanins, Gia_ObjFanin0( Gia_ObjFanin1(pNode) ) );
            Vec_PtrPushUnique( p->vFanins, Gia_ObjFanin1( Gia_ObjFanin0(pNode) ) );
            Vec_PtrPushUnique( p->vFanins, Gia_ObjFanin1( Gia_ObjFanin1(pNode) ) );
            Vec_PtrForEachEntry( Gia_Obj_t *, p->vFanins, pFanin, k )
                Cec4_ObjAddToFrontier( p->pNew, Gia_Regular(pFanin), p->vFrontier, p->pSat );
            Cec4_AddClausesMux( p->pNew, pNode, p->pSat );
        }
        else
        {
            Cec4_CollectSuper( pNode, fUseMuxes, p->vFanins );
            Vec_PtrForEachEntry( Gia_Obj_t *, p->vFanins, pFanin, k )
                Cec4_ObjAddToFrontier( p->pNew, Gia_Regular(pFanin), p->vFrontier, p->pSat );
            Cec4_AddClausesSuper( p->pNew, pNode, p->vFanins, p->pSat );
        }
        assert( Vec_PtrSize(p->vFanins) > 1 );
    }
    return Cec4_ObjSatId(p->pNew,pObj);
}


/**Function*************************************************************

  Synopsis    [Internal simulation APIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word * Cec4_ObjSim( Gia_Man_t * p, int iObj )
{
    return Vec_WrdEntryP( p->vSims, p->nSimWords * iObj );
}
static inline void Cec4_ObjSimSetInputBit( Gia_Man_t * p, int iObj, int Bit )
{
    word * pSim = Cec4_ObjSim( p, iObj );
    if ( Abc_InfoHasBit( (unsigned*)pSim, p->iPatsPi ) != Bit )
        Abc_InfoXorBit( (unsigned*)pSim, p->iPatsPi );
}
static inline int Cec4_ObjSimGetInputBit( Gia_Man_t * p, int iObj )
{
    word * pSim = Cec4_ObjSim( p, iObj );
    return Abc_InfoHasBit( (unsigned*)pSim, p->iPatsPi );
}
static inline void Cec4_ObjSimRo( Gia_Man_t * p, int iObj )
{
    int w;
    word * pSimRo = Cec4_ObjSim( p, iObj );
    word * pSimRi = Cec4_ObjSim( p, Gia_ObjRoToRiId(p, iObj) );
    for ( w = 0; w < p->nSimWords; w++ )
        pSimRo[w] = pSimRi[w];
}
static inline void Cec4_ObjSimCo( Gia_Man_t * p, int iObj )
{
    int w;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    word * pSimCo  = Cec4_ObjSim( p, iObj );
    word * pSimDri = Cec4_ObjSim( p, Gia_ObjFaninId0(pObj, iObj) );
    if ( Gia_ObjFaninC0(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSimCo[w] = ~pSimDri[w];
    else
        for ( w = 0; w < p->nSimWords; w++ )
            pSimCo[w] =  pSimDri[w];
}
static inline void Cec4_ObjSimAnd( Gia_Man_t * p, int iObj )
{
    int w;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    word * pSim  = Cec4_ObjSim( p, iObj );
    word * pSim0 = Cec4_ObjSim( p, Gia_ObjFaninId0(pObj, iObj) );
    word * pSim1 = Cec4_ObjSim( p, Gia_ObjFaninId1(pObj, iObj) );
    if ( Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = ~pSim0[w] & ~pSim1[w];
    else if ( Gia_ObjFaninC0(pObj) && !Gia_ObjFaninC1(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = ~pSim0[w] & pSim1[w];
    else if ( !Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = pSim0[w] & ~pSim1[w];
    else
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = pSim0[w] & pSim1[w];
}
static inline int Cec4_ObjSimEqual( Gia_Man_t * p, int iObj0, int iObj1 )
{
    int w;
    word * pSim0 = Cec4_ObjSim( p, iObj0 );
    word * pSim1 = Cec4_ObjSim( p, iObj1 );
    if ( (pSim0[0] & 1) == (pSim1[0] & 1) )
    {
        for ( w = 0; w < p->nSimWords; w++ )
            if ( pSim0[w] != pSim1[w] )
                return 0;
        return 1;
    }
    else
    {
        for ( w = 0; w < p->nSimWords; w++ )
            if ( pSim0[w] != ~pSim1[w] )
                return 0;
        return 1;
    }
}
static inline void Cec4_ObjSimCi( Gia_Man_t * p, int iObj )
{
    int w;
    word * pSim = Cec4_ObjSim( p, iObj );
    for ( w = 0; w < p->nSimWords; w++ )
        pSim[w] = Gia_ManRandomW( 0 );
    pSim[0] <<= 1;
}
static inline void Cec4_ObjClearSimCi( Gia_Man_t * p, int iObj )
{
    int w;
    word * pSim = Cec4_ObjSim( p, iObj );
    for ( w = 0; w < p->nSimWords; w++ )
        pSim[w] = 0;
}
void Cec4_ManSimulateCis( Gia_Man_t * p )
{
    int i, Id;
    Gia_ManForEachCiId( p, Id, i )
        Cec4_ObjSimCi( p, Id );
    p->iPatsPi = 0;
}
void Cec4_ManClearCis( Gia_Man_t * p )
{
    int i, Id;
    Gia_ManForEachCiId( p, Id, i )
        Cec4_ObjClearSimCi( p, Id );
    p->iPatsPi = 0;
}
Abc_Cex_t * Cec4_ManDeriveCex( Gia_Man_t * p, int iOut, int iPat )
{
    Abc_Cex_t * pCex;
    int i, Id;
    pCex = Abc_CexAlloc( 0, Gia_ManCiNum(p), 1 );
    pCex->iPo = iOut;
    if ( iPat == -1 )
        return pCex;
    Gia_ManForEachCiId( p, Id, i )
        if ( Abc_InfoHasBit((unsigned *)Cec4_ObjSim(p, Id), iPat) )
            Abc_InfoSetBit( pCex->pData, i );
    return pCex;
}
int Cec4_ManSimulateCos( Gia_Man_t * p )
{
    int i, Id;
    // check outputs and generate CEX if they fail
    Gia_ManForEachCoId( p, Id, i )
    {
        Cec4_ObjSimCo( p, Id );
        if ( Cec4_ObjSimEqual(p, Id, 0) )
            continue;
        p->pCexSeq = Cec4_ManDeriveCex( p, i, Abc_TtFindFirstBit2(Cec4_ObjSim(p, Id), p->nSimWords) );
        return 0;
    }
    return 1;
}
void Cec4_ManSimulate( Gia_Man_t * p, Cec4_Man_t * pMan, int fRefine )
{
    extern void Cec4_ManSimClassRefineOne( Gia_Man_t * p, int iRepr );
    abctime clk = Abc_Clock();
    Gia_Obj_t * pObj; int i;
    pMan->nSimulates++;
    Gia_ManForEachAnd( p, pObj, i )
        Cec4_ObjSimAnd( p, i );
    pMan->timeSim += Abc_Clock() - clk;
    if ( !fRefine )
        return;
    clk = Abc_Clock();
    Gia_ManForEachClass0( p, i )
        Cec4_ManSimClassRefineOne( p, i );
    pMan->timeRefine += Abc_Clock() - clk;
}
void Cec4_ManSimulate_rec( Gia_Man_t * p, Cec4_Man_t * pMan, int iObj )
{
    Gia_Obj_t * pObj; 
    if ( !iObj || Vec_IntEntry(pMan->vCexStamps, iObj) == p->iPatsPi )
        return;
    Vec_IntWriteEntry( pMan->vCexStamps, iObj, p->iPatsPi );
    pObj = Gia_ManObj(p, iObj);
    if ( Gia_ObjIsCi(pObj) )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Cec4_ManSimulate_rec( p, pMan, Gia_ObjFaninId0(pObj, iObj) );
    Cec4_ManSimulate_rec( p, pMan, Gia_ObjFaninId1(pObj, iObj) );
    Cec4_ObjSimAnd( p, iObj );
}
void Cec4_ManSimAlloc( Gia_Man_t * p, int nWords )
{
    Vec_WrdFreeP( &p->vSims );
    p->vSims   = Vec_WrdStart( Gia_ManObjNum(p) * nWords );
    p->nSimWords = nWords;
}


/**Function*************************************************************

  Synopsis    [Creating initial equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec4_ManPrintTfiConeStats( Gia_Man_t * p )
{
    Vec_Int_t * vRoots  = Vec_IntAlloc( 100 );
    Vec_Int_t * vNodes  = Vec_IntAlloc( 100 );
    Vec_Int_t * vLeaves = Vec_IntAlloc( 100 );
    int i, k;
    Gia_ManForEachClass0( p, i )
    {
        Vec_IntClear( vRoots );
        if ( i % 100 != 0 )
            continue;
        Vec_IntPush( vRoots, i );
        Gia_ClassForEachObj1( p, i, k )
            Vec_IntPush( vRoots, k );
        Gia_ManCollectTfi( p, vRoots, vNodes );
        printf( "Class %6d : ", i );
        printf( "Roots = %6d  ", Vec_IntSize(vRoots) );
        printf( "Nodes = %6d  ", Vec_IntSize(vNodes) );
        printf( "\n" );
    }
    Vec_IntFree( vRoots );
    Vec_IntFree( vNodes );
    Vec_IntFree( vLeaves );
}
void Cec4_ManPrintStats( Gia_Man_t * p, Cec_ParFra_t * pPars, Cec4_Man_t * pMan )
{
    if ( !pPars->fVerbose )
        return;
    printf( "P =%6d  ", pMan ? pMan->nSatUnsat : 0 );
    printf( "D =%6d  ", pMan ? pMan->nSatSat   : 0 );
    printf( "F =%6d  ", pMan ? pMan->nSatUndec : 0 );
    //printf( "Last =%6d  ", pMan ? pMan->iLastConst : 0 );
    Gia_ManEquivPrintClasses( p, pPars->fVeryVerbose, 0 );
}
void Cec4_ManSimClassRefineOne( Gia_Man_t * p, int iRepr )
{
    int iObj, iPrev = iRepr, iPrev2, iRepr2;
    Gia_ClassForEachObj1( p, iRepr, iRepr2 )
        if ( Cec4_ObjSimEqual(p, iRepr, iRepr2) )
            iPrev = iRepr2;
        else
            break;
    if ( iRepr2 <= 0 ) // no refinement
        return;
    // relink remaining nodes of the class
    // nodes that are equal to iRepr, remain in the class of iRepr
    // nodes that are not equal to iRepr, move to the class of iRepr2
    Gia_ObjSetRepr( p, iRepr2, GIA_VOID );
    iPrev2 = iRepr2;
    for ( iObj = Gia_ObjNext(p, iRepr2); iObj > 0; iObj = Gia_ObjNext(p, iObj) )
    {
        if ( Cec4_ObjSimEqual(p, iRepr, iObj) ) // remains with iRepr
        {
            Gia_ObjSetNext( p, iPrev, iObj );
            iPrev = iObj;
        }
        else // moves to iRepr2
        {
            Gia_ObjSetRepr( p, iObj, iRepr2 );
            Gia_ObjSetNext( p, iPrev2, iObj );
            iPrev2 = iObj;
        }
    }
    Gia_ObjSetNext( p, iPrev, -1 );
    Gia_ObjSetNext( p, iPrev2, -1 );
}

void Cec4_ManPrintClasses2( Gia_Man_t * p )
{
    int i, k;
    Gia_ManForEachClass0( p, i )
    {
        printf( "Class %d : ", i );
        Gia_ClassForEachObj1( p, i, k )
            printf( "%d ", k );
        printf( "\n" );
    }
}
void Cec4_ManPrintClasses( Gia_Man_t * p )
{
    int k, Count = 0;
    Gia_ClassForEachObj1( p, 0, k )
        Count++;
    printf( "Const0 class has %d entries.\n", Count );
}
int Cec4_ManSimHashKey( word * pSim, int nSims, int nTableSize )
{
    static int s_Primes[16] = { 
        1291, 1699, 1999, 2357, 2953, 3313, 3907, 4177, 
        4831, 5147, 5647, 6343, 6899, 7103, 7873, 8147 };
    unsigned uHash = 0, * pSimU = (unsigned *)pSim;
    int i, nSimsU = 2 * nSims;
    if ( pSimU[0] & 1 )
        for ( i = 0; i < nSimsU; i++ )
            uHash ^= ~pSimU[i] * s_Primes[i & 0xf];
    else
        for ( i = 0; i < nSimsU; i++ )
            uHash ^= pSimU[i] * s_Primes[i & 0xf];
    return (int)(uHash % nTableSize);

}
void Cec4_ManCreateClasses( Gia_Man_t * p, Cec4_Man_t * pMan )
{
    abctime clk;
    Gia_Obj_t * pObj;
    int nWords = p->nSimWords;
    int * pTable, nTableSize, i, Key;
    // allocate representation
    ABC_FREE( p->pReprs );
    ABC_FREE( p->pNexts );
    p->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(p) );
    p->pNexts = ABC_FALLOC( int, Gia_ManObjNum(p) );
    p->pReprs[0].iRepr = GIA_VOID;
    Gia_ManForEachCoId( p, Key, i )
        p->pReprs[Key].iRepr = GIA_VOID;
    Cec4_ManPrintStats( p, pMan->pPars, pMan );
    // hash each node by its simulation info
    nTableSize = Abc_PrimeCudd( Gia_ManObjNum(p) );
    pTable = ABC_FALLOC( int, nTableSize );
    Gia_ManForEachObj( p, pObj, i )
    {
        p->pReprs[i].iRepr = GIA_VOID;
        if ( Gia_ObjIsCo(pObj) )
            continue;
        Key = Cec4_ManSimHashKey( Cec4_ObjSim(p, i), nWords, nTableSize );
        assert( Key >= 0 && Key < nTableSize );
        if ( pTable[Key] == -1 )
            pTable[Key] = i;
        else
            Gia_ObjSetRepr( p, i, pTable[Key] );
    }
    // create classes
    for ( i = Gia_ManObjNum(p) - 1; i >= 0; i-- )
    {
        int iRepr = Gia_ObjRepr(p, i);
        if ( iRepr == GIA_VOID )
            continue;
        Gia_ObjSetNext( p, i, Gia_ObjNext(p, iRepr) );
        Gia_ObjSetNext( p, iRepr, i );
    }
    ABC_FREE( pTable );
    clk = Abc_Clock();
    Gia_ManForEachClass0( p, i )
        Cec4_ManSimClassRefineOne( p, i );
    pMan->timeRefine += Abc_Clock() - clk;
}



/**Function*************************************************************

  Synopsis    [Verify counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec4_ManVerify_rec( Gia_Man_t * p, int iObj, bmcg_sat_solver * pSat )
{
    int Value0, Value1;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    if ( iObj == 0 ) return 0;
    if ( Gia_ObjIsTravIdCurrentId(p, iObj) )
        return pObj->fMark1;
    Gia_ObjSetTravIdCurrentId(p, iObj);
    if ( Gia_ObjIsCi(pObj) )
        return pObj->fMark1 = bmcg_sat_solver_read_cex_varvalue(pSat, Cec4_ObjSatId(p, pObj));
    assert( Gia_ObjIsAnd(pObj) );
    Value0 = Cec4_ManVerify_rec( p, Gia_ObjFaninId0(pObj, iObj), pSat ) ^ Gia_ObjFaninC0(pObj);
    Value1 = Cec4_ManVerify_rec( p, Gia_ObjFaninId1(pObj, iObj), pSat ) ^ Gia_ObjFaninC1(pObj);
    return pObj->fMark1 = Value0 & Value1;
}
void Cec4_ManVerify( Gia_Man_t * p, int iObj0, int iObj1, int fPhase, bmcg_sat_solver * pSat )
{
    int Value0, Value1;
    Gia_ManIncrementTravId( p );
    Value0 = Cec4_ManVerify_rec( p, iObj0, pSat );
    Value1 = Cec4_ManVerify_rec( p, iObj1, pSat );
    if ( (Value0 ^ Value1) == fPhase )
        printf( "CEX verification FAILED for obj %d and obj %d.\n", iObj0, iObj1 );
//    else
//        printf( "CEX verification succeeded for obj %d and obj %d.\n", iObj0, iObj1 );;
}


/**Function*************************************************************

  Synopsis    [Verify counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec4_ManCexVerify_rec( Gia_Man_t * p, int iObj )
{
    int Value0, Value1;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    if ( iObj == 0 ) return 0;
    if ( Gia_ObjIsTravIdCurrentId(p, iObj) )
        return pObj->fMark1;
    Gia_ObjSetTravIdCurrentId(p, iObj);
    if ( Gia_ObjIsCi(pObj) )
        return pObj->fMark1 = Cec4_ObjSimGetInputBit(p, iObj);
    assert( Gia_ObjIsAnd(pObj) );
    Value0 = Cec4_ManCexVerify_rec( p, Gia_ObjFaninId0(pObj, iObj) ) ^ Gia_ObjFaninC0(pObj);
    Value1 = Cec4_ManCexVerify_rec( p, Gia_ObjFaninId1(pObj, iObj) ) ^ Gia_ObjFaninC1(pObj);
    return pObj->fMark1 = Value0 & Value1;
}
void Cec4_ManCexVerify( Gia_Man_t * p, int iObj0, int iObj1, int fPhase )
{
    int Value0, Value1;
    Gia_ManIncrementTravId( p );
    Value0 = Cec4_ManCexVerify_rec( p, iObj0 );
    Value1 = Cec4_ManCexVerify_rec( p, iObj1 );
    if ( (Value0 ^ Value1) == fPhase )
        printf( "CEX verification FAILED for obj %d and obj %d.\n", iObj0, iObj1 );
//    else
//        printf( "CEX verification succeeded for obj %d and obj %d.\n", iObj0, iObj1 );;
}

/**Function*************************************************************

  Synopsis    [Generates counter-examples to refine the candidate equivalences.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cec4_ObjFan0HasValue( Gia_Obj_t * pObj, int v )
{
    return (v ^ Gia_ObjFaninC0(pObj)) ? Gia_ObjFanin0(pObj)->fMark1 : Gia_ObjFanin0(pObj)->fMark0;
}
static inline int Cec4_ObjFan1HasValue( Gia_Obj_t * pObj, int v )
{
    return (v ^ Gia_ObjFaninC1(pObj)) ? Gia_ObjFanin1(pObj)->fMark1 : Gia_ObjFanin1(pObj)->fMark0;
}
int Cec4_ManGeneratePatterns_rec( Gia_Man_t * p, Gia_Obj_t * pObj, int Value, Vec_Int_t * vPat, Vec_Int_t * vVisit )
{
    Gia_Obj_t * pFan0, * pFan1;
    assert( !pObj->fMark0 && !pObj->fMark1 ); // not visited
    if ( Value ) pObj->fMark1 = 1; else pObj->fMark0 = 1;
    Vec_IntPush( vVisit, Gia_ObjId(p, pObj) );
    if ( Gia_ObjIsCi(pObj) )
    {
        Vec_IntPush( vPat, Abc_Var2Lit(Gia_ObjId(p, pObj), Value) );
        return 1;
    }
    assert( Gia_ObjIsAnd(pObj) );
    pFan0 = Gia_ObjFanin0(pObj);
    pFan1 = Gia_ObjFanin1(pObj);
    if ( Value )
    {
        if ( Cec4_ObjFan0HasValue(pObj, 0) || Cec4_ObjFan1HasValue(pObj, 0) )
            return 0;
        if ( !Cec4_ObjFan0HasValue(pObj, 1) && !Cec4_ManGeneratePatterns_rec(p, pFan0, !Gia_ObjFaninC0(pObj), vPat, vVisit) )
            return 0;
        if ( !Cec4_ObjFan1HasValue(pObj, 1) && !Cec4_ManGeneratePatterns_rec(p, pFan1, !Gia_ObjFaninC1(pObj), vPat, vVisit) )
            return 0;
        assert( Cec4_ObjFan0HasValue(pObj, 1) && Cec4_ObjFan1HasValue(pObj, 1) );
        return 1;
    }
    else
    {
        if ( Cec4_ObjFan0HasValue(pObj, 1) && Cec4_ObjFan1HasValue(pObj, 1) )
            return 0;
        if ( Cec4_ObjFan0HasValue(pObj, 0) || Cec4_ObjFan1HasValue(pObj, 0) )
            return 1;
        if ( Cec4_ObjFan0HasValue(pObj, 1) )
        {
            if ( !Cec4_ManGeneratePatterns_rec(p, pFan1, Gia_ObjFaninC1(pObj), vPat, vVisit) )
                return 0;
        }
        else if ( Cec4_ObjFan1HasValue(pObj, 1) )
        {
            if ( !Cec4_ManGeneratePatterns_rec(p, pFan0, Gia_ObjFaninC0(pObj), vPat, vVisit) )
                return 0;
        }
        else if ( Abc_Random(0) & 1 )
        {
            if ( !Cec4_ManGeneratePatterns_rec(p, pFan1, Gia_ObjFaninC1(pObj), vPat, vVisit) )
                return 0;
        }
        else
        {
            if ( !Cec4_ManGeneratePatterns_rec(p, pFan0, Gia_ObjFaninC0(pObj), vPat, vVisit) )
                return 0;
        }
        assert( Cec4_ObjFan0HasValue(pObj, 0) || Cec4_ObjFan1HasValue(pObj, 0) );
        return 1;
    }
}
int Cec4_ManGeneratePatternOne( Gia_Man_t * p, int iRepr, int iReprVal, int iCand, int iCandVal, Vec_Int_t * vPat, Vec_Int_t * vVisit )
{
    int Res, k;
    Gia_Obj_t * pObj;
    assert( iCand > 0 );
    if ( !iRepr && iReprVal )
        return 0;
    Vec_IntClear( vPat );
    Vec_IntClear( vVisit );
    //Gia_ManForEachObj( p, pObj, k )
    //    assert( !pObj->fMark0 && !pObj->fMark1 );
    Res = (!iRepr || Cec4_ManGeneratePatterns_rec(p, Gia_ManObj(p, iRepr), iReprVal, vPat, vVisit)) && Cec4_ManGeneratePatterns_rec(p, Gia_ManObj(p, iCand), iCandVal, vPat, vVisit);
    Gia_ManForEachObjVec( vVisit, p, pObj, k )
        pObj->fMark0 = pObj->fMark1 = 0;
    return Res;
}
void Cec4_ManGeneratePatterns( Cec4_Man_t * p )
{
    abctime clk = Abc_Clock();
    int i, k, iLit, nPats = 64 * p->pAig->nSimWords;
    // collect candidate nodes
    if ( p->pPars->nGenIters )
    {
        if ( Vec_IntSize(p->vCands) == 0 )
        {
            for ( i = 1; i < Gia_ManObjNum(p->pAig); i++ )
                if ( Gia_ObjRepr(p->pAig, i) != GIA_VOID )
                    Vec_IntPush( p->vCands, i );
        }
        else
        {
            int iObj, k = 0;
            Vec_IntForEachEntry( p->vCands, iObj, i )
                if ( Gia_ObjRepr(p->pAig, iObj) != GIA_VOID )
                    Vec_IntWriteEntry( p->vCands, k++, iObj );
            Vec_IntShrink( p->vCands, k );
            assert( Vec_IntSize(p->vCands) > 0 );
        }
    }
    // generate the given number of patterns
    for ( i = 0, p->pAig->iPatsPi = 1; i < p->pPars->nGenIters * nPats && p->pAig->iPatsPi < nPats; p->pAig->iPatsPi++, i++ )
    {
        int iCand    = Vec_IntEntry( p->vCands, Abc_Random(0) % Vec_IntSize(p->vCands) );
        int iRepr    = Gia_ObjRepr( p->pAig, iCand );
        int iCandVal = Gia_ManObj(p->pAig, iCand)->fPhase;
        int iReprVal = Gia_ManObj(p->pAig, iRepr)->fPhase;
        int Res = Cec4_ManGeneratePatternOne( p->pAig, iRepr,  iReprVal, iCand, !iCandVal, p->vPat, p->vVisit );
        if ( !Res )
            Res = Cec4_ManGeneratePatternOne( p->pAig, iRepr, !iReprVal, iCand,  iCandVal, p->vPat, p->vVisit );
        if ( !Res )
            p->pAig->iPatsPi--;
        else
        {
            // record this pattern
            Vec_IntForEachEntry( p->vPat, iLit, k )
                Cec4_ObjSimSetInputBit( p->pAig, Abc_Lit2Var(iLit), Abc_LitIsCompl(iLit) );
            //Cec4_ManCexVerify( p->pAig, iRepr, iCand, iReprVal ^ iCandVal );
            //Gia_ManCleanMark01( p->pAig );
        }
    }
    //printf( "Generated %d CEXs after trying %d candidate equivalence pairs.\n", p->pAig->iPatsPi-1, i );
    p->timeGenPats += Abc_Clock() - clk;
}


/**Function*************************************************************

  Synopsis    [Internal simulation APIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec4_ManSatSolverRecycle( Cec4_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    //printf( "Solver size = %d.\n", bmcg_sat_solver_varnum(p->pSat) );
    p->nRecycles++;
    p->nCallsSince = 0;
    bmcg_sat_solver_reset( p->pSat );
    // clean mapping of AigIds into SatIds
    Gia_ManForEachObjVec( &p->pNew->vSuppVars, p->pNew, pObj, i )
        Cec4_ObjCleanSatId( p->pNew, pObj );
    Vec_IntClear( &p->pNew->vSuppVars );  // AigIds for which SatId is defined
    Vec_IntClear( &p->pNew->vCopiesTwo ); // pairs (CiAigId, SatId)
}
int Cec4_ManSolveTwo( Cec4_Man_t * p, int iObj0, int iObj1, int fPhase, int * pfEasy, int fVerbose )
{
    abctime clk;
    int nConfEnd, nConfBeg;
    int status, iVar0, iVar1, Lits[2];
    int UnsatConflicts[3] = {0};
    if ( iObj1 <  iObj0 ) 
         iObj1 ^= iObj0, iObj0 ^= iObj1, iObj1 ^= iObj0;
    assert( iObj0 < iObj1 );    
    *pfEasy = 0;
    // check if SAT solver needs recycling
    p->nCallsSince++; 
    if ( p->nCallsSince > p->pPars->nCallsRecycle && 
         Vec_IntSize(&p->pNew->vSuppVars) > p->pPars->nSatVarMax && p->pPars->nSatVarMax )
        Cec4_ManSatSolverRecycle( p );
    // add more logic to the solver
    if ( !iObj0 && Cec4_ObjSatId(p->pNew, Gia_ManConst0(p->pNew)) == -1 )
        Cec4_ObjSetSatId( p->pNew, Gia_ManConst0(p->pNew), bmcg_sat_solver_addvar(p->pSat) );
    clk = Abc_Clock();
    iVar0 = Cec4_ObjGetCnfVar( p, iObj0 );
    iVar1 = Cec4_ObjGetCnfVar( p, iObj1 );
    p->timeCnf += Abc_Clock() - clk;
    // perform solving
    Lits[0] = Abc_Var2Lit(iVar0, 1);
    Lits[1] = Abc_Var2Lit(iVar1, fPhase);
    bmcg_sat_solver_set_conflict_budget( p->pSat, p->pPars->nBTLimit );
    nConfBeg = bmcg_sat_solver_conflictnum( p->pSat );
    status = bmcg_sat_solver_solve( p->pSat, Lits, 2 );
    nConfEnd = bmcg_sat_solver_conflictnum( p->pSat );
    assert( nConfEnd >= nConfBeg );
    if ( fVerbose )
    {
        if ( status == GLUCOSE_SAT ) 
        {
            p->nConflicts[0][0] += nConfEnd == nConfBeg;
            p->nConflicts[0][1] += nConfEnd -  nConfBeg;
            p->nConflicts[0][2]  = Abc_MaxInt(p->nConflicts[0][2], nConfEnd - nConfBeg);
            *pfEasy = nConfEnd == nConfBeg;
        }
        else if ( status == GLUCOSE_UNSAT ) 
        {
            if ( iObj0 > 0 )
            {
                UnsatConflicts[0] = nConfEnd == nConfBeg;
                UnsatConflicts[1] = nConfEnd -  nConfBeg;
                UnsatConflicts[2] = Abc_MaxInt(p->nConflicts[1][2], nConfEnd - nConfBeg);
            }
            else
            {
                p->nConflicts[1][0] += nConfEnd == nConfBeg;
                p->nConflicts[1][1] += nConfEnd -  nConfBeg;
                p->nConflicts[1][2]  = Abc_MaxInt(p->nConflicts[1][2], nConfEnd - nConfBeg);
                *pfEasy = nConfEnd == nConfBeg;
            }
        }
    }
    if ( status == GLUCOSE_UNSAT && iObj0 > 0 )
    {
        Lits[0] = Abc_Var2Lit(iVar0, 0);
        Lits[1] = Abc_Var2Lit(iVar1, !fPhase);
        bmcg_sat_solver_set_conflict_budget( p->pSat, p->pPars->nBTLimit );
        nConfBeg = bmcg_sat_solver_conflictnum( p->pSat );
        status = bmcg_sat_solver_solve( p->pSat, Lits, 2 );
        nConfEnd = bmcg_sat_solver_conflictnum( p->pSat );
        assert( nConfEnd >= nConfBeg );
        if ( fVerbose )
        {
            if ( status == GLUCOSE_SAT ) 
            {
                p->nConflicts[0][0] += nConfEnd == nConfBeg;
                p->nConflicts[0][1] += nConfEnd -  nConfBeg;
                p->nConflicts[0][2]  = Abc_MaxInt(p->nConflicts[0][2], nConfEnd - nConfBeg);
                *pfEasy = nConfEnd == nConfBeg;
            }
            else if ( status == GLUCOSE_UNSAT ) 
            {
                UnsatConflicts[0]  &= nConfEnd == nConfBeg;
                UnsatConflicts[1]  += nConfEnd -  nConfBeg;
                UnsatConflicts[2]   = Abc_MaxInt(p->nConflicts[1][2], nConfEnd - nConfBeg);

                p->nConflicts[1][0] += UnsatConflicts[0];
                p->nConflicts[1][1] += UnsatConflicts[1];
                p->nConflicts[1][2]  = Abc_MaxInt(p->nConflicts[1][2], UnsatConflicts[2]);
                *pfEasy = UnsatConflicts[0];
            }
        }
    }
    return status;
}
int Cec4_ManSweepNode( Cec4_Man_t * p, int iObj, int iRepr )
{
    abctime clk = Abc_Clock();
    int i, IdAig, IdSat, status, fEasy, RetValue = 1;
    Gia_Obj_t * pObj = Gia_ManObj( p->pAig, iObj );
    Gia_Obj_t * pRepr = Gia_ManObj( p->pAig, iRepr );
    int fCompl = Abc_LitIsCompl(pObj->Value) ^ Abc_LitIsCompl(pRepr->Value) ^ pObj->fPhase ^ pRepr->fPhase;
    status = Cec4_ManSolveTwo( p, Abc_Lit2Var(pRepr->Value), Abc_Lit2Var(pObj->Value), fCompl, &fEasy, p->pPars->fVerbose );
    if ( status == GLUCOSE_SAT )
    {
        //printf( "Disproved: %d == %d.\n", Abc_Lit2Var(pRepr->Value), Abc_Lit2Var(pObj->Value) );
        p->nSatSat++;
        p->nPatterns++;
        p->pAig->iPatsPi++;
        assert( p->pAig->iPatsPi > 0 && p->pAig->iPatsPi < 64 * p->pAig->nSimWords );
        Vec_IntForEachEntryDouble( &p->pNew->vCopiesTwo, IdAig, IdSat, i )
            Cec4_ObjSimSetInputBit( p->pAig, IdAig, bmcg_sat_solver_read_cex_varvalue(p->pSat, IdSat) );
        if ( fEasy )
            p->timeSatSat0 += Abc_Clock() - clk;
        else
            p->timeSatSat += Abc_Clock() - clk;
        RetValue = 0;
        // this is not needed, but we keep it here anyway, because it takes very little time
        //Cec4_ManVerify( p->pNew, Abc_Lit2Var(pRepr->Value), Abc_Lit2Var(pObj->Value), fCompl, p->pSat );
        // resimulated once in a while
        if ( p->pAig->iPatsPi == 64 * p->pAig->nSimWords - 1 )
        {
            abctime clk2 = Abc_Clock();
            Cec4_ManSimulate( p->pAig, p, 1 );
            //if ( p->nSatSat && p->nSatSat % 100 == 0 )
                Cec4_ManPrintStats( p->pAig, p->pPars, p );
            Vec_IntFill( p->vCexStamps, Gia_ManObjNum(p->pAig), 0 );
            p->pAig->iPatsPi = 0;
            p->timeResimGlo += Abc_Clock() - clk2;
        }
    }
    else if ( status == GLUCOSE_UNSAT )
    {
        //printf( "Proved: %d == %d.\n", Abc_Lit2Var(pRepr->Value), Abc_Lit2Var(pObj->Value) );
        p->nSatUnsat++;
        pObj->Value = Abc_LitNotCond( pRepr->Value, fCompl );
        Gia_ObjSetProved( p->pAig, iObj );
        if ( iRepr == 0 )
            p->iLastConst = iObj;
        if ( fEasy )
            p->timeSatUnsat0 += Abc_Clock() - clk;
        else
            p->timeSatUnsat += Abc_Clock() - clk;
        RetValue = 1;
    }
    else 
    {
        p->nSatUndec++;
        assert( status == GLUCOSE_UNDEC );
        Gia_ObjSetFailed( p->pAig, iObj );
        p->timeSatUndec += Abc_Clock() - clk;
        RetValue = 2;
    }
    return RetValue;
}
Gia_Obj_t * Cec4_ManFindRepr( Gia_Man_t * p, Cec4_Man_t * pMan, int iObj )
{
    abctime clk = Abc_Clock();
    int iMem, iRepr;
    assert( Gia_ObjHasRepr(p, iObj) );
    assert( !Gia_ObjProved(p, iObj) );
    iRepr = Gia_ObjRepr(p, iObj);
    assert( iRepr != iObj );
    assert( !Gia_ObjProved(p, iRepr) );
    Cec4_ManSimulate_rec( p, pMan, iObj );
    Cec4_ManSimulate_rec( p, pMan, iRepr );
    if ( Cec4_ObjSimEqual(p, iObj, iRepr) )
    {
        pMan->timeResimLoc += Abc_Clock() - clk;
        return Gia_ManObj(p, iRepr);
    }
    Gia_ClassForEachObj1( p, iRepr, iMem )
    {
        if ( iObj == iMem )
            break;
        if ( Gia_ObjProved(p, iMem) )
            continue;
        Cec4_ManSimulate_rec( p, pMan, iMem );
        if ( Cec4_ObjSimEqual(p, iObj, iMem) )
        {
            pMan->timeResimLoc += Abc_Clock() - clk;
            return Gia_ManObj(p, iMem);
        }
    }
    pMan->timeResimLoc += Abc_Clock() - clk;
    return NULL;
}
int Cec4_ManPerformSweeping( Gia_Man_t * p, Cec_ParFra_t * pPars, Gia_Man_t ** ppNew )
{
    Cec4_Man_t * pMan = Cec4_ManCreate( p, pPars ); 
    Gia_Obj_t * pObj, * pRepr; int i;
    if ( pPars->fVerbose )
        printf( "Simulate %d words in %d rounds. Easy SAT with %d tries. SAT with %d confs. Recycle after %d SAT calls.\n", 
            pPars->nWords, pPars->nRounds, pPars->nGenIters, pPars->nBTLimit, pPars->nCallsRecycle );

    // check if any output trivially fails under all-0 pattern
    Gia_ManRandomW( 1 );
    Gia_ManSetPhase( p );
    //Gia_ManStaticFanoutStart( p );
    if ( pPars->fCheckMiter ) 
    {
        Gia_ManForEachCo( p, pObj, i )
            if ( pObj->fPhase )
            {
                p->pCexSeq = Cec4_ManDeriveCex( p, i, -1 );
                goto finalize;
            }
    }

    // simulate one round and create classes
    Cec4_ManSimAlloc( p, pPars->nWords );
    Cec4_ManSimulateCis( p );
    Cec4_ManSimulate( p, pMan, 0 );
    if ( pPars->fCheckMiter && !Cec4_ManSimulateCos(p) ) // cex detected
        goto finalize;
    Cec4_ManCreateClasses( p, pMan );
    if ( pPars->fVerbose )
        Cec4_ManPrintStats( p, pPars, pMan );

    // perform additional simulation
    for ( i = 0; i < pPars->nRounds; i++ )
    {
        Cec4_ManSimulateCis( p );
        if ( i >= pPars->nRounds/3 )
            Cec4_ManGeneratePatterns( pMan );
        Cec4_ManSimulate( p, pMan, 1 );
        if ( pPars->fCheckMiter && !Cec4_ManSimulateCos(p) ) // cex detected
            goto finalize;
        if ( i % (pPars->nRounds / 5) == 0 && pPars->fVerbose )
            Cec4_ManPrintStats( p, pPars, pMan );
    }

    p->iPatsPi = 0;
    pMan->pNew = Cec4_ManStartNew( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        //Gia_Obj_t * pObjNew; 
        pObj->Value = Gia_ManHashAnd( pMan->pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        //pObjNew = Gia_ManObj( pMan->pNew, Abc_Lit2Var(pObj->Value) );
        //if ( Gia_ObjIsAnd(pObjNew) )
        //    Gia_ObjSetAndLevel( pMan->pNew, pObjNew );
        // select representative based on candidate equivalence classes
        pRepr = Gia_ObjReprObj( p, i );
        if ( pRepr == NULL )
            continue;
        if ( 1 ) // select representative based on recent counter-examples
        {
            pRepr = Cec4_ManFindRepr( p, pMan, i );
            if ( pRepr == NULL )
                continue;
        }
        if ( Abc_Lit2Var(pObj->Value) == Abc_Lit2Var(pRepr->Value) )
        {
            assert( (pObj->Value ^ pRepr->Value) == (pObj->fPhase ^ pRepr->fPhase) );
            Gia_ObjSetProved( p, i );
            if ( Gia_ObjId(p, pRepr) == 0 )
                pMan->iLastConst = i;
            continue;
        }
        if ( Cec4_ManSweepNode(pMan, i, Gia_ObjId(p, pRepr)) && Gia_ObjProved(p, i) )
            pObj->Value = Abc_LitNotCond( pRepr->Value, pObj->fPhase ^ pRepr->fPhase );
    }
    if ( p->iPatsPi > 0 )
    {
        abctime clk2 = Abc_Clock();
        Cec4_ManSimulate( p, pMan, 1 );
        Vec_IntFill( pMan->vCexStamps, Gia_ManObjNum(p), 0 );
        p->iPatsPi = 0;
        pMan->timeResimGlo += Abc_Clock() - clk2;
    }
    if ( pPars->fVerbose )
        Cec4_ManPrintStats( p, pPars, pMan );
    if ( ppNew )
    {
        Gia_ManForEachCo( p, pObj, i )
            pObj->Value = Gia_ManAppendCo( pMan->pNew, Gia_ObjFanin0Copy(pObj) );
        *ppNew = Gia_ManCleanup( pMan->pNew );
    }
finalize:
    if ( pPars->fVerbose )
        printf( "Performed %d SAT calls:  P = %d (0=%d a=%.2f m=%d)  D = %d (0=%d a=%.2f m=%d)  F = %d   Sim = %d  Recyc = %d\n", 
            pMan->nSatUnsat + pMan->nSatSat + pMan->nSatUndec, 
            pMan->nSatUnsat, pMan->nConflicts[1][0], (float)pMan->nConflicts[1][1]/Abc_MaxInt(1, pMan->nSatUnsat-pMan->nConflicts[1][0]), pMan->nConflicts[1][2],
            pMan->nSatSat,   pMan->nConflicts[0][0], (float)pMan->nConflicts[0][1]/Abc_MaxInt(1, pMan->nSatSat  -pMan->nConflicts[0][0]), pMan->nConflicts[0][2],  
            pMan->nSatUndec,  
            pMan->nSimulates, pMan->nRecycles );
    Cec4_ManDestroy( pMan );
    //Gia_ManStaticFanoutStop( p );
    //Gia_ManEquivPrintClasses( p, 1, 0 );
    return p->pCexSeq ? 0 : 1;
}
Gia_Man_t * Cec4_ManSimulateTest( Gia_Man_t * p, Cec_ParFra_t * pPars )
{
    Gia_Man_t * pNew = NULL;
    Cec4_ManPerformSweeping( p, pPars, &pNew );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

