/**CFile****************************************************************

  FileName    [saigInter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Interplation for unbounded model checking.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigInter.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "fra.h"
#include "cnf.h"
#include "satStore.h"

/* 
    The interpolation algorithm implemented here was introduced in the paper:
    K. L. McMillan. Interpolation and SAT-based model checking. CAV’03, pp. 1-13.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// simulation manager
typedef struct Saig_IntMan_t_ Saig_IntMan_t;
struct Saig_IntMan_t_
{
    // AIG manager
    Aig_Man_t *      pAig;         // the original AIG manager
    Aig_Man_t *      pAigTrans;    // the transformed original AIG manager
    Cnf_Dat_t *      pCnfAig;      // CNF for the original manager
    // interpolant
    Aig_Man_t *      pInter;       // the current interpolant
    Cnf_Dat_t *      pCnfInter;    // CNF for the current interplant
    // timeframes
    Aig_Man_t *      pFrames;      // the timeframes      
    Cnf_Dat_t *      pCnfFrames;   // CNF for the timeframes 
    // other data
    Vec_Int_t *      vVarsAB;      // the variables participating in 
    // temporary place for the new interpolant
    Aig_Man_t *      pInterNew;
    // parameters
    int              nFrames;      // the number of timeframes
    int              nConfCur;     // the current number of conflicts
    int              nConfLimit;   // the limit on the number of conflicts
    int              fVerbose;     // the verbosiness flag
    // runtime
    int              timeRwr;
    int              timeCnf;
    int              timeSat;
    int              timeInt;
    int              timeEqu;
    int              timeOther;
    int              timeTotal;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Create trivial AIG manager for the init state.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManInit( int nRegs )
{
    Aig_Man_t * p;
    Aig_Obj_t * pRes;
    Aig_Obj_t ** ppInputs;
    int i;
    assert( nRegs > 0 );
    ppInputs = ALLOC( Aig_Obj_t *, nRegs );
    p = Aig_ManStart( nRegs );
    for ( i = 0; i < nRegs; i++ )
        ppInputs[i] = Aig_Not( Aig_ObjCreatePi(p) );
    pRes = Aig_Multi( p, ppInputs, nRegs, AIG_OBJ_AND );
    Aig_ObjCreatePo( p, pRes );
    free( ppInputs );
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicate the AIG w/o POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManDuplicated( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManRegNum(p) > 0 );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // set registers
    pNew->nRegs    = p->nRegs;
    pNew->nTruePis = p->nTruePis;
    pNew->nTruePos = 0;
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create register inputs with MUXes
    Saig_ManForEachLi( p, pObj, i )
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicate the AIG w/o POs and transforms to transit into init state.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManTransformed( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    Aig_Obj_t * pCtrl = NULL; // Suppress "might be used uninitialized"
    int i;
    assert( Aig_ManRegNum(p) > 0 );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
    {
        if ( i == Saig_ManPiNum(p) )
            pCtrl = Aig_ObjCreatePi( pNew );
        pObj->pData = Aig_ObjCreatePi( pNew );
    }
    // set registers
    pNew->nRegs    = p->nRegs;
    pNew->nTruePis = p->nTruePis + 1;
    pNew->nTruePos = 0;
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create register inputs with MUXes
    Saig_ManForEachLiLo( p, pObjLi, pObjLo, i )
    {
        pObj = Aig_Mux( pNew, pCtrl, pObjLo->pData, Aig_ObjChild0Copy(pObjLi) );
//        pObj = Aig_Mux( pNew, pCtrl, Aig_ManConst0(pNew), Aig_ObjChild0Copy(pObjLi) );
        Aig_ObjCreatePo( pNew, pObj );
    }
    Aig_ManCleanup( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Create timeframes of the manager for interpolation.]

  Description [The resulting manager is combinational. The primary inputs
  corresponding to register outputs are ordered first. The only POs of the 
  manager is the property output of the last timeframe.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManFramesInter( Aig_Man_t * pAig, int nFrames )
{
    Aig_Man_t * pFrames;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, f;
    assert( Saig_ManRegNum(pAig) > 0 );
    assert( Saig_ManPoNum(pAig) == 1 );
    pFrames = Aig_ManStart( Aig_ManNodeNum(pAig) * nFrames );
    // map the constant node
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pFrames );
    // create variables for register outputs
    Saig_ManForEachLo( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pFrames );
    // add timeframes
    for ( f = 0; f < nFrames; f++ )
    {
        // create PI nodes for this frame
        Saig_ManForEachPi( pAig, pObj, i )
            pObj->pData = Aig_ObjCreatePi( pFrames );
        // add internal nodes of this frame
        Aig_ManForEachNode( pAig, pObj, i )
            pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        if ( f == nFrames - 1 )
            break;
        // save register inputs
        Saig_ManForEachLi( pAig, pObj, i )
            pObj->pData = Aig_ObjChild0Copy(pObj);
        // transfer to register outputs
        Saig_ManForEachLiLo(  pAig, pObjLi, pObjLo, i )
            pObjLo->pData = pObjLi->pData;
    }
    // create the only PO of the manager
    pObj = Aig_ManPo( pAig, 0 );
    Aig_ObjCreatePo( pFrames, Aig_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pFrames );
    return pFrames;
}

/**Function*************************************************************

  Synopsis    [Returns the SAT solver for one interpolation run.]

  Description [pInter is the previous interpolant. pAig is one time frame.
  pFrames is the unrolled time frames.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * Saig_DeriveSatSolver( 
    Aig_Man_t * pInter, Cnf_Dat_t * pCnfInter, 
    Aig_Man_t * pAig, Cnf_Dat_t * pCnfAig, 
    Aig_Man_t * pFrames, Cnf_Dat_t * pCnfFrames, 
    Vec_Int_t * vVarsAB )
{
    sat_solver * pSat;
    Aig_Obj_t * pObj, * pObj2;
    int i, Lits[2];

    // sanity checks
    assert( Aig_ManRegNum(pInter) == 0 );
    assert( Aig_ManRegNum(pAig) > 0 );
    assert( Aig_ManRegNum(pFrames) == 0 );
    assert( Aig_ManPoNum(pInter) == 1 );
    assert( Aig_ManPoNum(pFrames) == 1 );
    assert( Aig_ManPiNum(pInter) == Aig_ManRegNum(pAig) );
//    assert( (Aig_ManPiNum(pFrames) - Aig_ManRegNum(pAig)) % Saig_ManPiNum(pAig) == 0 );

    // prepare CNFs
    Cnf_DataLift( pCnfAig,   pCnfFrames->nVars );
    Cnf_DataLift( pCnfInter, pCnfFrames->nVars + pCnfAig->nVars );

    // start the solver
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat );
    sat_solver_setnvars( pSat, pCnfInter->nVars + pCnfAig->nVars + pCnfFrames->nVars );

    // add clauses of A
    // interpolant
    for ( i = 0; i < pCnfInter->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfInter->pClauses[i], pCnfInter->pClauses[i+1] ) )
            assert( 0 );
    }
    // connector clauses
    Aig_ManForEachPi( pInter, pObj, i )
    {
        pObj2 = Saig_ManLo( pAig, i );
        Lits[0] = toLitCond( pCnfInter->pVarNums[pObj->Id], 0 );
        Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 1 );
        if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            assert( 0 );
        Lits[0] = toLitCond( pCnfInter->pVarNums[pObj->Id], 1 );
        Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 0 );
        if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            assert( 0 );
    }
    // one timeframe
    for ( i = 0; i < pCnfAig->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfAig->pClauses[i], pCnfAig->pClauses[i+1] ) )
            assert( 0 );
    }
    // connector clauses
    Vec_IntClear( vVarsAB );
    Aig_ManForEachPi( pFrames, pObj, i )
    {
        if ( i == Aig_ManRegNum(pAig) )
            break;
        Vec_IntPush( vVarsAB, pCnfFrames->pVarNums[pObj->Id] );

        pObj2 = Saig_ManLi( pAig, i );
        Lits[0] = toLitCond( pCnfFrames->pVarNums[pObj->Id], 0 );
        Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 1 );
        if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            assert( 0 );
        Lits[0] = toLitCond( pCnfFrames->pVarNums[pObj->Id], 1 );
        Lits[1] = toLitCond( pCnfAig->pVarNums[pObj2->Id], 0 );
        if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            assert( 0 );
    }
    // add clauses of B
    sat_solver_store_mark_clauses_a( pSat );
    for ( i = 0; i < pCnfFrames->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfFrames->pClauses[i], pCnfFrames->pClauses[i+1] ) )
            assert( 0 );
    }
    sat_solver_store_mark_roots( pSat );
    // return clauses to the original state
    Cnf_DataLift( pCnfAig, -pCnfFrames->nVars );
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Checks constainment of two interpolants.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManCheckContainment( Aig_Man_t * pNew, Aig_Man_t * pOld )
{
    Aig_Man_t * pMiter, * pAigTemp;
    int RetValue;
    pMiter = Aig_ManCreateMiter( pNew, pOld, 1 );
//    pMiter = Dar_ManRwsat( pAigTemp = pMiter, 1, 0 );
//    Aig_ManStop( pAigTemp );
    RetValue = Fra_FraigMiterStatus( pMiter );
    if ( RetValue == -1 )
    {
        pAigTemp = Fra_FraigEquivence( pMiter, 1000000, 1 );
        RetValue = Fra_FraigMiterStatus( pAigTemp );
        Aig_ManStop( pAigTemp );
//        RetValue = Fra_FraigSat( pMiter, 1000000, 0, 0, 0 );
    }
    assert( RetValue != -1 );
    Aig_ManStop( pMiter );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Checks constainment of two interpolants.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManCheckEquivalence( Aig_Man_t * pNew, Aig_Man_t * pOld )
{
    Aig_Man_t * pMiter, * pAigTemp;
    int RetValue;
    pMiter = Aig_ManCreateMiter( pNew, pOld, 0 );
//    pMiter = Dar_ManRwsat( pAigTemp = pMiter, 1, 0 );
//    Aig_ManStop( pAigTemp );
    RetValue = Fra_FraigMiterStatus( pMiter );
    if ( RetValue == -1 )
    {
        pAigTemp = Fra_FraigEquivence( pMiter, 1000000, 1 );
        RetValue = Fra_FraigMiterStatus( pAigTemp );
        Aig_ManStop( pAigTemp );
//        RetValue = Fra_FraigSat( pMiter, 1000000, 0, 0, 0 );
    }
    assert( RetValue != -1 );
    Aig_ManStop( pMiter );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Performs one SAT run with interpolation.]

  Description [Returns 1 if proven. 0 if failed. -1 if undecided.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_PerformOneStep_old( Saig_IntMan_t * p, int fUseIp )
{
    sat_solver * pSat;
    void * pSatCnf = NULL;
    Inta_Man_t * pManInterA; 
    Intb_Man_t * pManInterB; 
    int clk, status, RetValue;
    assert( p->pInterNew == NULL );

    // derive the SAT solver
    pSat = Saig_DeriveSatSolver( p->pInter, p->pCnfInter, p->pAigTrans, p->pCnfAig, p->pFrames, p->pCnfFrames, p->vVarsAB );
//Sat_SolverWriteDimacs( pSat, "test.cnf", NULL, NULL, 1 );
    // solve the problem
clk = clock();
    status = sat_solver_solve( pSat, NULL, NULL, (sint64)p->nConfLimit, (sint64)0, (sint64)0, (sint64)0 );
    p->nConfCur = pSat->stats.conflicts;
p->timeSat += clock() - clk;
    if ( status == l_False )
    {
        pSatCnf = sat_solver_store_release( pSat );
        RetValue = 1;
    }
    else if ( status == l_True )
    {
        RetValue = 0;
    }
    else
    {
        RetValue = -1;
    }
    sat_solver_delete( pSat );
    if ( pSatCnf == NULL )
        return RetValue;

    // create the resulting manager
clk = clock();
    if ( !fUseIp )
    {
        pManInterA = Inta_ManAlloc();
        p->pInterNew = Inta_ManInterpolate( pManInterA, pSatCnf, p->vVarsAB, 0 );
        Inta_ManFree( pManInterA );
    }
    else
    {
        pManInterB = Intb_ManAlloc();
        p->pInterNew = Intb_ManInterpolate( pManInterB, pSatCnf, p->vVarsAB, 0 );
        Intb_ManFree( pManInterB );
    }
p->timeInt += clock() - clk;
    Sto_ManFree( pSatCnf );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupExpand( Aig_Man_t * pInter, Aig_Man_t * pOther )
{
    Aig_Man_t * pInterC;
    assert( Aig_ManPiNum(pInter) <= Aig_ManPiNum(pOther) );
    pInterC = Aig_ManDupSimple( pInter );
    Aig_IthVar( pInterC, Aig_ManPiNum(pOther)-1 );
    assert( Aig_ManPiNum(pInterC) == Aig_ManPiNum(pOther) );
    return pInterC;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_VerifyInterpolant1( Inta_Man_t * pMan, Sto_Man_t * pCnf, Aig_Man_t * pInter )
{
    extern Aig_Man_t * Inta_ManDeriveClauses( Inta_Man_t * pMan, Sto_Man_t * pCnf, int fClausesA );
    Aig_Man_t * pLower, * pUpper, * pInterC;
    int RetValue1, RetValue2;

    pLower = Inta_ManDeriveClauses( pMan, pCnf, 1 );
    pUpper = Inta_ManDeriveClauses( pMan, pCnf, 0 );
    Aig_ManFlipFirstPo( pUpper );

    pInterC = Aig_ManDupExpand( pInter, pLower );
    RetValue1 = Saig_ManCheckContainment( pLower, pInterC );
    Aig_ManStop( pInterC );

    pInterC = Aig_ManDupExpand( pInter, pUpper );
    RetValue2 = Saig_ManCheckContainment( pInterC, pUpper );
    Aig_ManStop( pInterC );
    
    if ( RetValue1 && RetValue2 )
        printf( "Im is correct.\n" );
    if ( !RetValue1 )
        printf( "Property A => Im fails.\n" );
    if ( !RetValue2 )
        printf( "Property Im => !B fails.\n" );

    Aig_ManStop( pLower );
    Aig_ManStop( pUpper );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_VerifyInterpolant2( Intb_Man_t * pMan, Sto_Man_t * pCnf, Aig_Man_t * pInter )
{
    extern Aig_Man_t * Intb_ManDeriveClauses( Intb_Man_t * pMan, Sto_Man_t * pCnf, int fClausesA );
    Aig_Man_t * pLower, * pUpper, * pInterC;
    int RetValue1, RetValue2;

    pLower = Intb_ManDeriveClauses( pMan, pCnf, 1 );
    pUpper = Intb_ManDeriveClauses( pMan, pCnf, 0 );
    Aig_ManFlipFirstPo( pUpper );

    pInterC = Aig_ManDupExpand( pInter, pLower );
//Aig_ManPrintStats( pLower );
//Aig_ManPrintStats( pUpper );
//Aig_ManPrintStats( pInterC );
//Aig_ManDumpBlif( pInterC, "inter_c.blif", NULL, NULL );
    RetValue1 = Saig_ManCheckContainment( pLower, pInterC );
    Aig_ManStop( pInterC );

    pInterC = Aig_ManDupExpand( pInter, pUpper );
    RetValue2 = Saig_ManCheckContainment( pInterC, pUpper );
    Aig_ManStop( pInterC );
    
    if ( RetValue1 && RetValue2 )
        printf( "Ip is correct.\n" );
    if ( !RetValue1 )
        printf( "Property A => Ip fails.\n" );
    if ( !RetValue2 )
        printf( "Property Ip => !B fails.\n" );

    Aig_ManStop( pLower );
    Aig_ManStop( pUpper );
}

/**Function*************************************************************

  Synopsis    [Performs one SAT run with interpolation.]

  Description [Returns 1 if proven. 0 if failed. -1 if undecided.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_PerformOneStep( Saig_IntMan_t * p, int fUseIp )
{
    sat_solver * pSat;
    void * pSatCnf = NULL;
    Inta_Man_t * pManInterA; 
    Intb_Man_t * pManInterB; 
    int clk, status, RetValue;
    assert( p->pInterNew == NULL );

    // derive the SAT solver
    pSat = Saig_DeriveSatSolver( p->pInter, p->pCnfInter, p->pAigTrans, p->pCnfAig, p->pFrames, p->pCnfFrames, p->vVarsAB );
//Sat_SolverWriteDimacs( pSat, "test.cnf", NULL, NULL, 1 );
    // solve the problem
clk = clock();
    status = sat_solver_solve( pSat, NULL, NULL, (sint64)p->nConfLimit, (sint64)0, (sint64)0, (sint64)0 );
    p->nConfCur = pSat->stats.conflicts;
p->timeSat += clock() - clk;
    if ( status == l_False )
    {
        pSatCnf = sat_solver_store_release( pSat );
        RetValue = 1;
    }
    else if ( status == l_True )
    {
        RetValue = 0;
    }
    else
    {
        RetValue = -1;
    }
    sat_solver_delete( pSat );
    if ( pSatCnf == NULL )
        return RetValue;

    // create the resulting manager
clk = clock();
    if ( !fUseIp )
    {
        pManInterA = Inta_ManAlloc();
        p->pInterNew = Inta_ManInterpolate( pManInterA, pSatCnf, p->vVarsAB, 0 );
        Inta_ManFree( pManInterA );
    }
    else
    {
        Aig_Man_t * pInterNew2;
        int RetValue;

        pManInterA = Inta_ManAlloc();
        p->pInterNew = Inta_ManInterpolate( pManInterA, pSatCnf, p->vVarsAB, 0 );
//        Saig_VerifyInterpolant1( pManInterA, pSatCnf, p->pInterNew );
        Inta_ManFree( pManInterA );

        pManInterB = Intb_ManAlloc();
        pInterNew2 = Intb_ManInterpolate( pManInterB, pSatCnf, p->vVarsAB, 0 );
        Saig_VerifyInterpolant2( pManInterB, pSatCnf, pInterNew2 );
        Intb_ManFree( pManInterB );

        // check relationship
        RetValue = Saig_ManCheckEquivalence( pInterNew2, p->pInterNew );
        if ( RetValue )
            printf( "Equivalence \"Ip == Im\" holds\n" );
        else
        {
//            printf( "Equivalence \"Ip == Im\" does not hold\n" );
            RetValue = Saig_ManCheckContainment( pInterNew2, p->pInterNew );
            if ( RetValue )
                printf( "Containment \"Ip -> Im\" holds\n" );
            else
                printf( "Containment \"Ip -> Im\" does not hold\n" );

            RetValue = Saig_ManCheckContainment( p->pInterNew, pInterNew2 );
            if ( RetValue )
                printf( "Containment \"Im -> Ip\" holds\n" );
            else
                printf( "Containment \"Im -> Ip\" does not hold\n" );
        }

        Aig_ManStop( pInterNew2 );
    }
p->timeInt += clock() - clk;
    Sto_ManFree( pSatCnf );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Frees the interpolation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManagerClean( Saig_IntMan_t * p )
{
    if ( p->pCnfInter )
        Cnf_DataFree( p->pCnfInter );
    if ( p->pCnfFrames )
        Cnf_DataFree( p->pCnfFrames );
    if ( p->pInter )
        Aig_ManStop( p->pInter );
    if ( p->pFrames )
        Aig_ManStop( p->pFrames );
}

/**Function*************************************************************

  Synopsis    [Frees the interpolation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManagerFree( Saig_IntMan_t * p )
{
    if ( p->fVerbose )
    {
        p->timeOther = p->timeTotal-p->timeRwr-p->timeCnf-p->timeSat-p->timeInt-p->timeEqu;
        printf( "Runtime statistics:\n" );
        PRTP( "Rewriting  ", p->timeRwr,   p->timeTotal );
        PRTP( "CNF mapping", p->timeCnf,   p->timeTotal );
        PRTP( "SAT solving", p->timeSat,   p->timeTotal );
        PRTP( "Interpol   ", p->timeInt,   p->timeTotal );
        PRTP( "Containment", p->timeEqu,   p->timeTotal );
        PRTP( "Other      ", p->timeOther, p->timeTotal );
        PRTP( "TOTAL      ", p->timeTotal, p->timeTotal );
    }

    if ( p->pCnfAig )
        Cnf_DataFree( p->pCnfAig );
    if ( p->pCnfFrames )
        Cnf_DataFree( p->pCnfFrames );
    if ( p->pCnfInter )
        Cnf_DataFree( p->pCnfInter );
    Vec_IntFree( p->vVarsAB );
    if ( p->pAigTrans )
        Aig_ManStop( p->pAigTrans );
    if ( p->pFrames )
        Aig_ManStop( p->pFrames );
    if ( p->pInter )
        Aig_ManStop( p->pInter );
    if ( p->pInterNew )
        Aig_ManStop( p->pInterNew );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Interplates while the number of conflicts is not exceeded.]

  Description [Returns 1 if proven. 0 if failed. -1 if undecided.]
               
  SideEffects [Does not check the property in 0-th frame.]

  SeeAlso     []

***********************************************************************/
int Saig_Interpolate( Aig_Man_t * pAig, int nConfLimit, int fRewrite, int fTransLoop, int fUseIp, int fVerbose, int * pDepth )
{
    Saig_IntMan_t * p;
    Aig_Man_t * pAigTemp;
    int s, i, RetValue, Status, clk, clk2, clkTotal = clock();

    // sanity checks
    assert( Saig_ManRegNum(pAig) > 0 );
    assert( Saig_ManPiNum(pAig) > 0 );
    assert( Saig_ManPoNum(pAig) == 1 );

    // create interpolation manager
    p = ALLOC( Saig_IntMan_t, 1 );
    memset( p, 0, sizeof(Saig_IntMan_t) );
    p->vVarsAB = Vec_IntAlloc( Aig_ManRegNum(pAig) );
    p->nFrames = 1;
    p->nConfLimit = nConfLimit;
    p->fVerbose = fVerbose;
    // can perform SAT sweeping and/or rewriting of this AIG...
    p->pAig = pAig;      
    if ( fTransLoop )
        p->pAigTrans = Saig_ManTransformed( pAig );
    else
        p->pAigTrans = Saig_ManDuplicated( pAig );
    // derive CNF for the transformed AIG
clk = clock();
    p->pCnfAig = Cnf_Derive( p->pAigTrans, Aig_ManRegNum(p->pAigTrans) ); 
p->timeCnf += clock() - clk;    
    if ( fVerbose )
    { 
        printf( "AIG: PI/PO/Reg = %d/%d/%d. And = %d. Lev = %d.  CNF: Var/Cla = %d/%d.\n",
            Saig_ManPiNum(pAig), Saig_ManPoNum(pAig), Saig_ManRegNum(pAig), 
            Aig_ManAndNum(pAig), Aig_ManLevelNum(pAig),
            p->pCnfAig->nVars, p->pCnfAig->nClauses );
    }

    // derive interpolant
    *pDepth = -1;
    for ( s = 0; ; s++ )
    {
clk2 = clock();
        // initial state
        p->pInter = Saig_ManInit( Aig_ManRegNum(pAig) );
clk = clock();
        p->pCnfInter = Cnf_Derive( p->pInter, 0 );  
p->timeCnf += clock() - clk;    
        // timeframes
        p->pFrames = Saig_ManFramesInter( pAig, p->nFrames );
clk = clock();
        if ( fRewrite )
        {
            p->pFrames = Dar_ManRwsat( pAigTemp = p->pFrames, 1, 0 );
            Aig_ManStop( pAigTemp );
//        p->pFrames = Fra_FraigEquivence( pAigTemp = p->pFrames, 100, 0 );
//        Aig_ManStop( pAigTemp );
        }
p->timeRwr += clock() - clk;
        // can also do SAT sweeping on the timeframes...
clk = clock();
        p->pCnfFrames = Cnf_Derive( p->pFrames, 0 );  
p->timeCnf += clock() - clk;    
        // report statistics
        if ( fVerbose )
        {
            printf( "Step = %2d. Frames = 1 + %d. And = %5d. Lev = %5d.  ", 
                s+1, p->nFrames, Aig_ManNodeNum(p->pFrames), Aig_ManLevelNum(p->pFrames) );
            PRT( "Time", clock() - clk2 );
        }
        // iterate the interpolation procedure
        for ( i = 0; ; i++ )
        {
            if ( p->nFrames + i >= 75 )
            {
                if ( fVerbose )
                    printf( "Reached limit (%d) on the number of timeframes.\n", 75 );
                p->timeTotal = clock() - clkTotal;
                Saig_ManagerFree( p );
                return -1;
            }
            // perform interplation
            clk = clock();
            RetValue = Saig_PerformOneStep( p, fUseIp );
            if ( fVerbose )
            {
                printf( "   I = %2d. Bmc =%3d. IntAnd =%6d. IntLev =%5d. Conf =%6d.  ", 
                    i+1, i + 1 + p->nFrames, Aig_ManNodeNum(p->pInter), Aig_ManLevelNum(p->pInter), p->nConfCur );
                PRT( "Time", clock() - clk );
            }
            if ( RetValue == 0 ) // found a (spurious?) counter-example
            {
                if ( i == 0 ) // real counterexample
                {
                    if ( fVerbose )
                        printf( "Found a real counterexample in the first frame.\n" );
                    p->timeTotal = clock() - clkTotal;
                    *pDepth = p->nFrames + 1;
                    Saig_ManagerFree( p );
                    return 0;
                }
                // likely spurious counter-example
                p->nFrames += i;
                Saig_ManagerClean( p );
                break;
            }
            else if ( RetValue == -1 ) // timed out
            {
                if ( fVerbose )
                    printf( "Reached limit (%d) on the number of conflicts.\n", p->nConfLimit );
                assert( p->nConfCur >= p->nConfLimit );
                p->timeTotal = clock() - clkTotal;
                Saig_ManagerFree( p );
                return -1;
            }
            assert( RetValue == 1 ); // found new interpolant
            // compress the interpolant
clk = clock();
            p->pInterNew = Dar_ManRwsat( pAigTemp = p->pInterNew, 1, 0 );
            Aig_ManStop( pAigTemp );
p->timeRwr += clock() - clk;
            // check containment of interpolants
clk = clock();
            Status = Saig_ManCheckContainment( p->pInterNew, p->pInter );
p->timeEqu += clock() - clk;
            if ( Status ) // contained
            {
                if ( fVerbose )
                    printf( "Proved containment of interpolants.\n" );
                p->timeTotal = clock() - clkTotal;
                Saig_ManagerFree( p );
                return 1;
            }
            // save interpolant and convert it into CNF
            if ( fTransLoop )
            {
                Aig_ManStop( p->pInter );
                p->pInter = p->pInterNew; 
            }
            else
            {
                p->pInter = Aig_ManCreateMiter( pAigTemp = p->pInter, p->pInterNew, 2 );
                Aig_ManStop( pAigTemp );
                Aig_ManStop( p->pInterNew );
                // compress the interpolant
clk = clock();
                p->pInter = Dar_ManRwsat( pAigTemp = p->pInter, 1, 0 );
                Aig_ManStop( pAigTemp );
p->timeRwr += clock() - clk;
            }
            p->pInterNew = NULL;
            Cnf_DataFree( p->pCnfInter );
clk = clock();
            p->pCnfInter = Cnf_Derive( p->pInter, 0 );  
p->timeCnf += clock() - clk;
        }
    }
    assert( 0 );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


