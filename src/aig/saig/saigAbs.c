/**CFile****************************************************************

  FileName    [saigAbs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Proof-based abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigAbs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

#include "cnf.h"
#include "satSolver.h"
#include "satStore.h"
#include "ssw.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline char Saig_AbsVisited( Vec_Str_t * p, int nObjs, Aig_Obj_t * pObj, int i )    { return Vec_StrGetEntry( p, nObjs*i+pObj->Id );    }
static inline void Saig_AbsSetVisited( Vec_Str_t * p, int nObjs, Aig_Obj_t * pObj, int i ) { Vec_StrSetEntry( p, nObjs*i+pObj->Id, (char)1 );  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Finds the set of clauses involved in the UNSAT core.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_AbsSolverUnsatCore( sat_solver * pSat, int nConfMax, int fVerbose )
{
    Vec_Int_t * vCore;
    void * pSatCnf; 
    Intp_Man_t * pManProof;
    int RetValue, clk = clock();
    // solve the problem
    RetValue = sat_solver_solve( pSat, NULL, NULL, (sint64)nConfMax, (sint64)0, (sint64)0, (sint64)0 );
    if ( RetValue == l_Undef )
    {
        printf( "Conflict limit is reached.\n" );
        return NULL;
    }
    if ( RetValue == l_True )
    {
        printf( "The BMC problem is SAT.\n" );
        return NULL;
    }
    if ( fVerbose )
    {
        printf( "SAT solver returned UNSAT after %d conflicts.  ", pSat->stats.conflicts );
        PRT( "Time", clock() - clk );
    }
    assert( RetValue == l_False );
    pSatCnf = sat_solver_store_release( pSat ); 
    // derive the UNSAT core
    clk = clock();
    pManProof = Intp_ManAlloc();
    vCore = Intp_ManUnsatCore( pManProof, pSatCnf, 0 );
    Intp_ManFree( pManProof );
    Sto_ManFree( pSatCnf );
    if ( fVerbose )
    {
        printf( "SAT core contains %d clauses (out of %d).  ", Vec_IntSize(vCore), pSat->stats.clauses );
        PRT( "Time", clock() - clk );
    }
    return vCore;
}


/**Function*************************************************************

  Synopsis    [Mark visited nodes recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_AbsMarkVisited_rec( Aig_Man_t * p, Vec_Str_t * vObj2Visit, Aig_Obj_t * pObj, int i )
{
    if ( Saig_AbsVisited( vObj2Visit, Aig_ManObjNumMax(p), pObj, i ) )
        return 1;
    Saig_AbsSetVisited( vObj2Visit, Aig_ManObjNumMax(p), pObj, i );
    if ( Saig_ObjIsPi( p, pObj ) )
        return 1;
    if ( Saig_ObjIsLo( p, pObj ) )
    {
        if ( i == 0 )
            return 1;
        return Saig_AbsMarkVisited_rec( p, vObj2Visit, Saig_ObjLoToLi(p, pObj), i-1 );
    }
    if ( Aig_ObjIsPo( pObj ) )
        return Saig_AbsMarkVisited_rec( p, vObj2Visit, Aig_ObjFanin0(pObj), i );
    Saig_AbsMarkVisited_rec( p, vObj2Visit, Aig_ObjFanin0(pObj), i );
    Saig_AbsMarkVisited_rec( p, vObj2Visit, Aig_ObjFanin1(pObj), i );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Mark visited nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Saig_AbsMarkVisited( Aig_Man_t * p, int nFramesMax )
{
    Vec_Str_t * vObj2Visit;
    Aig_Obj_t * pObj;
    int i, f;
    vObj2Visit = Vec_StrStart( Aig_ManObjNumMax(p) * nFramesMax );
//    Saig_ManForEachLo( p, pObj, i )
//        Saig_AbsSetVisited( vObj2Visit, Aig_ManObjNumMax(p), pObj, 0 ); 
    for ( f = 0; f < nFramesMax; f++ )
    {
        Saig_AbsSetVisited( vObj2Visit, Aig_ManObjNumMax(p), Aig_ManConst1(p), f );
        Saig_ManForEachPo( p, pObj, i )
            Saig_AbsMarkVisited_rec( p, vObj2Visit, pObj, f );
    }
    return vObj2Visit;
}

/**Function*************************************************************

  Synopsis    [Performs the actual construction of the output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Saig_AbsCreateFrames_rec( Aig_Man_t * pFrame, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return pObj->pData;
    assert( Aig_ObjIsNode(pObj) );
    Saig_AbsCreateFrames_rec( pFrame, Aig_ObjFanin0(pObj) );
    Saig_AbsCreateFrames_rec( pFrame, Aig_ObjFanin1(pObj) );
    return pObj->pData = Aig_And( pFrame, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Derives a vector of AIG managers, one for each frame.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Saig_AbsCreateFrames( Aig_Man_t * p, int nFramesMax, int fVerbose )
{
    Vec_Ptr_t * vFrames, * vLoObjs, * vLiObjs;
    Vec_Str_t * vObj2Visit;
    Aig_Man_t * pFrame;
    Aig_Obj_t * pObj;
    int f, i;
    vObj2Visit = Saig_AbsMarkVisited( p, nFramesMax );
    vFrames = Vec_PtrAlloc( nFramesMax );
    vLoObjs = Vec_PtrAlloc( 100 );
    vLiObjs = Vec_PtrAlloc( 100 );
    for ( f = 0; f < nFramesMax; f++ )
    {
        Aig_ManCleanData( p );
        pFrame = Aig_ManStart( 1000 );
        Aig_ManConst1(p)->pData = Aig_ManConst1(pFrame);
        // create PIs
        Vec_PtrClear( vLoObjs );
        Vec_PtrClear( vLiObjs );
        Aig_ManForEachPi( p, pObj, i )
        { 
            if ( Saig_AbsVisited( vObj2Visit, Aig_ManObjNumMax(p), pObj, f ) )
            {
                pObj->pData = Aig_ObjCreatePi(pFrame);
                if ( i >= Saig_ManPiNum(p) )
                    Vec_PtrPush( vLoObjs, pObj );
            } 
        }
        // remember the number of (implicit) registers in this frame
        pFrame->nAsserts = Vec_PtrSize(vLoObjs);
        // create POs
        Aig_ManForEachPo( p, pObj, i )
        {
            if ( Saig_AbsVisited( vObj2Visit, Aig_ManObjNumMax(p), pObj, f ) )
            {
                Saig_AbsCreateFrames_rec( pFrame, Aig_ObjFanin0(pObj) );
                pObj->pData = Aig_ObjCreatePo( pFrame, Aig_ObjChild0Copy(pObj) );
                if ( i >= Saig_ManPoNum(p) )
                    Vec_PtrPush( vLiObjs, pObj );
            }
        }
//        Vec_PtrPush( vFrames, Cnf_Derive(pFrame, Aig_ManPoNum(pFrame)) );
        Vec_PtrPush( vFrames, Cnf_DeriveSimple(pFrame, Aig_ManPoNum(pFrame)) );
        // set the new PIs to point to the corresponding registers
        Aig_ManCleanData( pFrame );
        Vec_PtrForEachEntry( vLoObjs, pObj, i )
            ((Aig_Obj_t *)pObj->pData)->pData = pObj;
        Vec_PtrForEachEntry( vLiObjs, pObj, i )
            ((Aig_Obj_t *)pObj->pData)->pData = pObj;
        if ( fVerbose )
            printf( "%3d : PI =%8d. PO =%8d. Flop =%8d. Node =%8d.\n", 
                f, Aig_ManPiNum(pFrame), Aig_ManPoNum(pFrame), pFrame->nAsserts, Aig_ManNodeNum(pFrame) );
    }
    Vec_PtrFree( vLoObjs );
    Vec_PtrFree( vLiObjs );
    Vec_StrFree( vObj2Visit );
    return vFrames;
}

/**Function*************************************************************

  Synopsis    [Derives a vector of AIG managers, one for each frame.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * Saig_AbsCreateSolverDyn( Aig_Man_t * p, Vec_Ptr_t * vFrames )
{
    sat_solver * pSat;
    Cnf_Dat_t * pCnf, * pCnfPrev;
    Vec_Int_t * vPoLits;
    Aig_Obj_t * pObjPo, * pObjLi, * pObjLo;
    int f, i, Lit, Lits[2], iVarOld, iVarNew, nSatVars, nRegisters;
    // start array of output literals
    vPoLits = Vec_IntAlloc( 100 );
    // count the number of CNF variables
    nSatVars = 0;
    Vec_PtrForEachEntry( vFrames, pCnf, f )
        nSatVars += pCnf->nVars;

    // create the SAT solver
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat ); 
    sat_solver_setnvars( pSat, nSatVars );

    // add clauses for the timeframes
    nSatVars = 0;
//    Vec_PtrForEachEntryReverse( vFrames, pCnf, f )
    Vec_PtrForEachEntry( vFrames, pCnf, f )
    {
        // lift clauses of this CNF
        Cnf_DataLift( pCnf, nSatVars );
        nSatVars += pCnf->nVars;
        // copy clauses into the manager
        for ( i = 0; i < pCnf->nClauses; i++ )
        {
            if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            {
                printf( "The BMC problem is trivially UNSAT.\n" );
                sat_solver_delete( pSat );
                Vec_IntFree( vPoLits );
                return NULL;
            }
        }
        // remember output literal
        Aig_ManForEachPo( pCnf->pMan, pObjPo, i )
        {
            if ( i == Saig_ManPoNum(p) )
                break;
            Vec_IntPush( vPoLits, toLit(pCnf->pVarNums[pObjPo->Id]) );
        }
    }

    // add auxiliary clauses (output, connectors, initial)
    // add output clause
    if ( !sat_solver_addclause( pSat, Vec_IntArray(vPoLits), Vec_IntArray(vPoLits) + Vec_IntSize(vPoLits) ) )
    {
        printf( "SAT solver is not created correctly.\n" );
        assert( 0 );
    }
    Vec_IntFree( vPoLits );

    // add connecting clauses
    pCnfPrev = Vec_PtrEntry( vFrames, 0 );
    Vec_PtrForEachEntryStart( vFrames, pCnf, f, 1 )
    {
        nRegisters = pCnf->pMan->nAsserts;
        assert( nRegisters <= Aig_ManPoNum(pCnfPrev->pMan) );
        assert( nRegisters <= Aig_ManPiNum(pCnf->pMan) );
        for ( i = 0; i < nRegisters; i++ )
        {
            pObjLi = Aig_ManPo( pCnfPrev->pMan, Aig_ManPoNum(pCnfPrev->pMan) - nRegisters + i );
            pObjLo = Aig_ManPi( pCnf->pMan,     Aig_ManPiNum(pCnf->pMan) -     nRegisters + i );
            // get variable numbers
            iVarOld = pCnfPrev->pVarNums[pObjLi->Id];
            iVarNew = pCnf->pVarNums[pObjLo->Id];
            // add clauses connecting existing variables
            Lits[0] = toLitCond( iVarOld, 0 );
            Lits[1] = toLitCond( iVarNew, 1 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
            Lits[0] = toLitCond( iVarOld, 1 );
            Lits[1] = toLitCond( iVarNew, 0 );
            if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                assert( 0 );
        }
        pCnfPrev = pCnf;
    }
    // add unit clauses
    pCnf = Vec_PtrEntry( vFrames, 0 );
    nRegisters = pCnf->pMan->nAsserts;
    for ( i = 0; i < nRegisters; i++ )
    {
        pObjLo = Aig_ManPi( pCnf->pMan, Aig_ManPiNum(pCnf->pMan) - nRegisters + i );
        assert( pCnf->pVarNums[pObjLo->Id] >= 0 );
        Lit = toLitCond( pCnf->pVarNums[pObjLo->Id], 1 );
        if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
            assert( 0 );
    }
    sat_solver_store_mark_roots( pSat ); 
    return pSat;
}


/**Function*************************************************************

  Synopsis    [Creates SAT solver for BMC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * Saig_AbsCreateSolver( Cnf_Dat_t * pCnf, int nFrames )
{
    sat_solver * pSat;
    Vec_Int_t * vPoLits;
    Aig_Obj_t * pObjPo, * pObjLi, * pObjLo;
    int f, i, Lit, Lits[2], iVarOld, iVarNew;
    // start array of output literals
    vPoLits = Vec_IntAlloc( nFrames * Saig_ManPoNum(pCnf->pMan) );
    // create the SAT solver
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat ); 
    sat_solver_setnvars( pSat, pCnf->nVars * nFrames );

    // add clauses for the timeframes
    for ( f = 0; f < nFrames; f++ )
    {
        for ( i = 0; i < pCnf->nClauses; i++ )
        {
            if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            {
                printf( "The BMC problem is trivially UNSAT.\n" );
                sat_solver_delete( pSat );
                Vec_IntFree( vPoLits );
                return NULL;
            }
        }
        // remember output literal
        Saig_ManForEachPo( pCnf->pMan, pObjPo, i )
            Vec_IntPush( vPoLits, toLit(pCnf->pVarNums[pObjPo->Id]) );
        // lift CNF to the next frame
        Cnf_DataLift( pCnf, pCnf->nVars );
    }
    // put CNF back to the original level
    Cnf_DataLift( pCnf, - pCnf->nVars * nFrames );

    // add auxiliary clauses (output, connectors, initial)
    // add output clause
    if ( !sat_solver_addclause( pSat, Vec_IntArray(vPoLits), Vec_IntArray(vPoLits) + Vec_IntSize(vPoLits) ) )
        assert( 0 );
    Vec_IntFree( vPoLits );
    // add connecting clauses
    for ( f = 0; f < nFrames; f++ )
    {
        // connect to the previous timeframe
        if ( f > 0 )
        {
            Saig_ManForEachLiLo( pCnf->pMan, pObjLi, pObjLo, i )
            {
                iVarOld = pCnf->pVarNums[pObjLi->Id] - pCnf->nVars;
                iVarNew = pCnf->pVarNums[pObjLo->Id];
                // add clauses connecting existing variables
                Lits[0] = toLitCond( iVarOld, 0 );
                Lits[1] = toLitCond( iVarNew, 1 );
                if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                    assert( 0 );
                Lits[0] = toLitCond( iVarOld, 1 );
                Lits[1] = toLitCond( iVarNew, 0 );
                if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
                    assert( 0 );
            }
        }
        // lift CNF to the next frame
        Cnf_DataLift( pCnf, pCnf->nVars );
    }
    // put CNF back to the original level
    Cnf_DataLift( pCnf, - pCnf->nVars * nFrames );
    // add unit clauses
    Saig_ManForEachLo( pCnf->pMan, pObjLo, i )
    {
        assert( pCnf->pVarNums[pObjLo->Id] >= 0 );
        Lit = toLitCond( pCnf->pVarNums[pObjLo->Id], 1 );
        if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
            assert( 0 );
    }
    sat_solver_store_mark_roots( pSat ); 
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Performs proof-based abstraction using BMC of the given depth.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_AbsCollectRegistersDyn( Aig_Man_t * p, Vec_Ptr_t * vFrames, Vec_Int_t * vCore )
{
    Aig_Obj_t * pObj;
    Cnf_Dat_t * pCnf;
    Vec_Int_t * vFlops;
    int * pVars, * pFlops;
    int i, f, iClause, iReg, * piLit, nSatVars, nSatClauses;
    // count the number of CNF variables
    nSatVars = 0;
    Vec_PtrForEachEntry( vFrames, pCnf, f )
        nSatVars += pCnf->nVars;
    // mark register variables
    pVars = ALLOC( int, nSatVars );
    for ( i = 0; i < nSatVars; i++ )
        pVars[i] = -1;
    Vec_PtrForEachEntry( vFrames, pCnf, f )
    {
        Aig_ManForEachPi( pCnf->pMan, pObj, i )
        {
            assert( pCnf->pVarNums[pObj->Id] >= 0 );
            assert( pCnf->pVarNums[pObj->Id] < nSatVars );
            if ( pObj->pData == NULL )
                continue;
            iReg = Aig_ObjPioNum(pObj->pData) - Saig_ManPiNum(p);
            assert( iReg >= 0 && iReg < Aig_ManRegNum(p) );
            pVars[ pCnf->pVarNums[pObj->Id] ] = iReg;
        }
        Aig_ManForEachPo( pCnf->pMan, pObj, i )
        {
            assert( pCnf->pVarNums[pObj->Id] >= 0 );
            assert( pCnf->pVarNums[pObj->Id] < nSatVars );
            if ( pObj->pData == NULL )
                continue;
            iReg = Aig_ObjPioNum(pObj->pData) - Saig_ManPoNum(p);
            assert( iReg >= 0 && iReg < Aig_ManRegNum(p) );
            pVars[ pCnf->pVarNums[pObj->Id] ] = iReg;
        }
    }
    // mark used registers
    pFlops = CALLOC( int, Aig_ManRegNum(p) );
    Vec_IntForEachEntry( vCore, iClause, i )
    {
        nSatClauses = 0;
        Vec_PtrForEachEntry( vFrames, pCnf, f )
        {
            if ( iClause < nSatClauses + pCnf->nClauses )
                break;
            nSatClauses += pCnf->nClauses;
        }
        if ( f == Vec_PtrSize(vFrames) )
            continue;
        iClause = iClause - nSatClauses;
        assert( iClause >= 0 );
        assert( iClause < pCnf->nClauses );
        // consider the clause
        for ( piLit = pCnf->pClauses[iClause]; piLit < pCnf->pClauses[iClause+1]; piLit++ )
        {
            iReg = pVars[ lit_var(*piLit) ];
            if ( iReg >= 0 )
                pFlops[iReg] = 1;
        }
    }
    // collect registers
    vFlops = Vec_IntAlloc( Aig_ManRegNum(p) );
    for ( i = 0; i < Aig_ManRegNum(p); i++ )
        if ( pFlops[i] )
            Vec_IntPush( vFlops, i );
    free( pFlops );
    free( pVars );
    return vFlops;
}

/**Function*************************************************************

  Synopsis    [Performs proof-based abstraction using BMC of the given depth.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_AbsCollectRegisters( Cnf_Dat_t * pCnf, int nFrames, Vec_Int_t * vCore )
{
    Aig_Obj_t * pObj;
    Vec_Int_t * vFlops;
    int * pVars, * pFlops;
    int i, iClause, iReg, * piLit;
    // mark register variables
    pVars = ALLOC( int, pCnf->nVars );
    for ( i = 0; i < pCnf->nVars; i++ )
        pVars[i] = -1;
    Saig_ManForEachLi( pCnf->pMan, pObj, i )
        pVars[ pCnf->pVarNums[pObj->Id] ] = i;
    Saig_ManForEachLo( pCnf->pMan, pObj, i )
        pVars[ pCnf->pVarNums[pObj->Id] ] = i;
    // mark used registers
    pFlops = CALLOC( int, Aig_ManRegNum(pCnf->pMan) );
    Vec_IntForEachEntry( vCore, iClause, i )
    {
        // skip auxiliary clauses
        if ( iClause >= pCnf->nClauses * nFrames )
            continue;
        // consider the clause
        iClause = iClause % pCnf->nClauses;
        for ( piLit = pCnf->pClauses[iClause]; piLit < pCnf->pClauses[iClause+1]; piLit++ )
        {
            iReg = pVars[ lit_var(*piLit) ];
            if ( iReg >= 0 )
                pFlops[iReg] = 1;
        }
    }
    // collect registers
    vFlops = Vec_IntAlloc( Aig_ManRegNum(pCnf->pMan) );
    for ( i = 0; i < Aig_ManRegNum(pCnf->pMan); i++ )
        if ( pFlops[i] )
            Vec_IntPush( vFlops, i );
    free( pFlops );
    free( pVars );
    return vFlops;
}

/**Function*************************************************************

  Synopsis    [Performs proof-based abstraction using BMC of the given depth.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_AbsFreeCnfs( Vec_Ptr_t * vFrames )
{
    Cnf_Dat_t * pCnf;
    int i;
    Vec_PtrForEachEntry( vFrames, pCnf, i )
    {
        Aig_ManStop( pCnf->pMan );
        Cnf_DataFree( pCnf );
    }
    Vec_PtrFree( vFrames );
}

/**Function*************************************************************

  Synopsis    [Performs proof-based abstraction using BMC of the given depth.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_AbsExtendOneStep( Aig_Man_t * p, Vec_Int_t * vFlops )
{
    Vec_Ptr_t * vFlopPtrs, * vSupp;
    Aig_Obj_t * pObj;
    int i, Entry;
    // collect latch inputs
    vFlopPtrs = Vec_PtrAlloc( 1000 );
    Vec_IntForEachEntry( vFlops, Entry, i )
    {
        Vec_PtrPush( vFlopPtrs, Saig_ManLi(p, Entry) );
        pObj = Saig_ManLo(p, Entry);
        pObj->fMarkA = 1;
    }
    // collect latch outputs
    vSupp = Vec_PtrAlloc( 1000 );
    Aig_SupportNodes( p, (Aig_Obj_t **)Vec_PtrArray(vFlopPtrs), Vec_PtrSize(vFlopPtrs), vSupp );
    Vec_PtrFree( vFlopPtrs );
    // mark influencing flops
    Vec_PtrForEachEntry( vSupp, pObj, i )
        pObj->fMarkA = 1;
    Vec_PtrFree( vSupp );
    // reload flops
    Vec_IntClear( vFlops );
    Aig_ManForEachPi( p, pObj, i )
    {
        if ( pObj->fMarkA == 0 )
            continue;
        pObj->fMarkA = 0;
        if ( Aig_ObjPioNum(pObj)-Saig_ManPiNum(p) >= 0 )
            Vec_IntPush( vFlops, Aig_ObjPioNum(pObj)-Saig_ManPiNum(p) );
    }
}

/**Function*************************************************************

  Synopsis    [Derive a new counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ssw_Cex_t * Saig_ManCexShrink( Aig_Man_t * p, Aig_Man_t * pAbs, Ssw_Cex_t * pCexAbs )
{
    Ssw_Cex_t * pCex;
    Aig_Obj_t * pObj;
    int i, f;
    // start the counter-example
    pCex = Ssw_SmlAllocCounterExample( Aig_ManRegNum(p), Saig_ManPiNum(p), pCexAbs->iFrame+1 );
    pCex->iFrame = pCexAbs->iFrame;
    pCex->iPo    = pCexAbs->iPo;
    // copy the bit data
    for ( f = 0; f <= pCexAbs->iFrame; f++ )
    {
        Saig_ManForEachPi( pAbs, pObj, i )
        {
            if ( i == Saig_ManPiNum(p) )
                break;
            if ( Aig_InfoHasBit( pCexAbs->pData, pCexAbs->nRegs + pCexAbs->nPis * f + i ) )
                Aig_InfoSetBit( pCex->pData, pCex->nRegs + pCex->nPis * f + i );
        }
    }
    // verify the counter example
    if ( !Ssw_SmlRunCounterExample( p, pCex ) )
    {
        printf( "Saig_ManCexShrink(): Counter-example is invalid.\n" );
        Ssw_SmlFreeCounterExample( pCex );
        pCex = NULL;
    }
    else
    {
        printf( "Counter-example verification is successful.\n" );
        printf( "Output %d was asserted in frame %d (use \"write_counter\" to dump a witness). \n", pCex->iPo, pCex->iFrame );
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Performs proof-based abstraction using BMC of the given depth.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManProofRefine( Aig_Man_t * p, Aig_Man_t * pAbs, Vec_Int_t * vFlops, int fVerbose )
{
    extern void Saig_BmcPerform( Aig_Man_t * pAig, int nFramesMax, int nNodesMax, int nConfMaxOne, int nConfMaxAll, int fVerbose );
    extern Vec_Int_t * Saig_ManExtendCounterExampleTest( Aig_Man_t * p, int iFirstPi, void * pCex, int fVerbose );

    Vec_Int_t * vFlopsNew, * vPiToReg;
    Aig_Obj_t * pObj;
    int i, Entry, iFlop;
    Saig_BmcPerform( pAbs, 2000, 2000, 5000, 1000000, fVerbose );
    if ( pAbs->pSeqModel == NULL )
        return NULL;
//    Saig_ManExtendCounterExampleTest( p->pAig, 0, p->pAig->pSeqModel );
    vFlopsNew = Saig_ManExtendCounterExampleTest( pAbs, Saig_ManPiNum(p), pAbs->pSeqModel, fVerbose );
    if ( Vec_IntSize(vFlopsNew) == 0 )
    {
        printf( "Discovered a true counter-example!\n" );
        p->pSeqModel = Saig_ManCexShrink( p, pAbs, pAbs->pSeqModel );
        Vec_IntFree( vFlopsNew );
        return NULL;
    }
    if ( fVerbose )
        printf( "Adding %d registers to the abstraction.\n", Vec_IntSize(vFlopsNew) );
    // vFlopsNew contains PI number that should be kept in pAbs

    // for each additional PI, collect the number of a register it stands for
    Vec_IntForEachEntry( vFlops, Entry, i )
    {
        pObj = Saig_ManLo( p, Entry );
        pObj->fMarkA = 1;
    }
    vPiToReg = Vec_IntAlloc( 1000 );
    Aig_ManForEachPi( p, pObj, i )
    {
        if ( pObj->fMarkA )
        {
            pObj->fMarkA = 0;
            continue;
        }
        if ( i < Saig_ManPiNum(p) )
            Vec_IntPush( vPiToReg, -1 );
        else
            Vec_IntPush( vPiToReg, Aig_ObjPioNum(pObj)-Saig_ManPiNum(p) );
    }
    // collect registers
    Vec_IntForEachEntry( vFlopsNew, Entry, i )
    {
        iFlop = Vec_IntEntry( vPiToReg, Entry );
        assert( iFlop >= 0 );
        assert( iFlop < Aig_ManRegNum(p) );
        Vec_IntPush( vFlops, iFlop );
    }
    Vec_IntFree( vPiToReg );
    Vec_IntFree( vFlopsNew );

    Vec_IntSort( vFlops, 0 );
    Vec_IntForEachEntryStart( vFlops, Entry, i, 1 )
        assert( Vec_IntEntry(vFlops, i-1) != Entry );

    return Saig_ManAbstraction( p, vFlops );
}

/**Function*************************************************************

  Synopsis    [Performs proof-based abstraction using BMC of the given depth.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Aig_Man_t * Saig_ManProofAbstraction( Aig_Man_t * p, int nFrames, int nConfMax, int fDynamic, int fExtend, int fSkipProof, int fVerbose )
{
    Aig_Man_t * pResult, * pTemp;
    Cnf_Dat_t * pCnf;
    Vec_Ptr_t * vFrames;
    sat_solver * pSat;
    Vec_Int_t * vCore;
    Vec_Int_t * vFlops;
    int Iter, clk = clock(), clk2 = clock();
    assert( Aig_ManRegNum(p) > 0 );
    Aig_ManSetPioNumbers( p );

    if ( fSkipProof )
    {
        assert( 0 );
        if ( fVerbose )
            printf( "Performing counter-example-based refinement.\n" );
//        vFlops = Vec_IntStartNatural( 100 );
//        Vec_IntPush( vFlops, 0 );
    }
    else
    {
        if ( fVerbose )
            printf( "Performing proof-based abstraction with %d frames and %d max conflicts.\n", nFrames, nConfMax );
        if ( fDynamic )
        {
            // create CNF for the frames
            vFrames = Saig_AbsCreateFrames( p, nFrames, fVerbose );
            // create dynamic solver
            pSat = Saig_AbsCreateSolverDyn( p, vFrames );
        }
        else
        {
            // create CNF for the AIG
            pCnf = Cnf_DeriveSimple( p, Aig_ManPoNum(p) );
            // create SAT solver for the unrolled AIG
            pSat = Saig_AbsCreateSolver( pCnf, nFrames );
        }
        if ( fVerbose )
        {
            printf( "SAT solver: Vars = %7d. Clauses = %7d.  ", pSat->size, pSat->stats.clauses );
            PRT( "Time", clock() - clk2 );
        }
        // compute UNSAT core
        vCore = Saig_AbsSolverUnsatCore( pSat, nConfMax, fVerbose );
        sat_solver_delete( pSat );
        if ( vCore == NULL )
        {
            Saig_AbsFreeCnfs( vFrames );
            return NULL;
        }
        // collect registers
        if ( fDynamic )
        {
            vFlops = Saig_AbsCollectRegistersDyn( p, vFrames, vCore );
            Saig_AbsFreeCnfs( vFrames );
        }
        else
        {
            vFlops = Saig_AbsCollectRegisters( pCnf, nFrames, vCore );
            Cnf_DataFree( pCnf );
        }
        Vec_IntFree( vCore );
        if ( fVerbose )
        {
            printf( "The number of relevant registers is %d (out of %d).  ", Vec_IntSize(vFlops), Aig_ManRegNum(p) );
            PRT( "Time", clock() - clk );
        }
    }
/*
    // extend the abstraction
    if ( fExtend )
    {
        if ( fVerbose )
            printf( "Support extended from %d flops to", Vec_IntSize(vFlops) );
        Saig_AbsExtendOneStep( p, vFlops );
        if ( fVerbose )
            printf( " %d flops.\n", Vec_IntSize(vFlops) );
    }
*/
    // create the resulting AIG
    pResult = Saig_ManAbstraction( p, vFlops );

    if ( fExtend )
    {
        if ( !fVerbose )
        {
            printf( "Init : " );
            Aig_ManPrintStats( pResult );
        }
        printf( "Refining abstraction...\n" );
        for ( Iter = 0; ; Iter++ )
        {
            pTemp = Saig_ManProofRefine( p, pResult, vFlops, fVerbose );
            if ( pTemp == NULL )
                break;
            Aig_ManStop( pResult );
            pResult = pTemp;
            printf( "%4d : ", Iter );
            if ( !fVerbose )
                Aig_ManPrintStats( pResult );
            else
                printf( " -----------------------------------------------------\n" );
        }
    }

    Vec_IntFree( vFlops );
    return pResult;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


