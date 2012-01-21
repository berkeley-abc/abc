/**CFile****************************************************************

  FileName    [pdrCnf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [CNF computation on demand.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdrCnf.c,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdrInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/*
    The CNF (p->pCnf2) is expressed in terms of object IDs.
    Each node in the CNF is marked if it has clauses (p->pCnf2->pObj2Count[Id] > 0).
    Each node in the CNF has the first clause (p->pCnf2->pObj2Clause) 
    and the number of clauses (p->pCnf2->pObj2Count).
    Each node used in a CNF of any timeframe has its SAT var recorded.
    Each frame has a reserve mapping of SAT variables into ObjIds.
*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns SAT variable of the given object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr_ObjSatVar1( Pdr_Man_t * p, int k, Aig_Obj_t * pObj )
{
    return p->pCnf1->pVarNums[ Aig_ObjId(pObj) ];
}

/**Function*************************************************************

  Synopsis    [Returns SAT variable of the given object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr_ObjSatVar2FindOrAdd( Pdr_Man_t * p, int k, Aig_Obj_t * pObj )
{ 
    assert( p->pCnf2->pObj2Count[Aig_ObjId(pObj)] >= 0 );
    if ( p->pvId2Vars[Aig_ObjId(pObj)] == NULL )
        p->pvId2Vars[Aig_ObjId(pObj)] = Vec_IntStart( 16 );
    if ( Vec_IntGetEntry( p->pvId2Vars[Aig_ObjId(pObj)], k ) == 0 )
    {
        sat_solver * pSat = Pdr_ManSolver(p, k);
        Vec_Int_t * vVar2Ids = (Vec_Int_t *)Vec_PtrEntry(p->vVar2Ids, k);
        int iVarNew = Vec_IntSize( vVar2Ids );
        assert( iVarNew > 0 );
        Vec_IntPush( vVar2Ids, Aig_ObjId(pObj) );
        Vec_IntWriteEntry( p->pvId2Vars[Aig_ObjId(pObj)], k, iVarNew );
        sat_solver_setnvars( pSat, iVarNew + 1 );
        if ( k == 0 && Saig_ObjIsLo(p->pAig, pObj) ) // initialize the register output
        {
            int Lit = toLitCond( iVarNew, 1 );
            int RetValue = sat_solver_addclause( pSat, &Lit, &Lit + 1 );
            assert( RetValue == 1 );
            sat_solver_compress( pSat );
        }
    }
    return Vec_IntEntry( p->pvId2Vars[Aig_ObjId(pObj)], k );
}

/**Function*************************************************************

  Synopsis    [Recursively adds CNF for the given object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ObjSatVar2( Pdr_Man_t * p, int k, Aig_Obj_t * pObj )
{
    sat_solver * pSat;
    Vec_Int_t * vLits;
    Vec_Int_t * vVar2Ids = (Vec_Int_t *)Vec_PtrEntry(p->vVar2Ids, k);
    int nVarCount = Vec_IntSize(vVar2Ids);
    int iVarThis  = Pdr_ObjSatVar2FindOrAdd( p, k, pObj );
    int * pLit, i, iVar, nClauses, iFirstClause, RetValue;
    if ( nVarCount == Vec_IntSize(vVar2Ids) )
        return iVarThis;
    assert( nVarCount + 1 == Vec_IntSize(vVar2Ids) );
    if ( Aig_ObjIsPi(pObj) )
        return iVarThis;
    nClauses = p->pCnf2->pObj2Count[Aig_ObjId(pObj)];
    iFirstClause = p->pCnf2->pObj2Clause[Aig_ObjId(pObj)];
    assert( nClauses > 0 );
    pSat = Pdr_ManSolver(p, k);
    vLits = Vec_IntAlloc( 16 );
    for ( i = iFirstClause; i < iFirstClause + nClauses; i++ )
    {
        Vec_IntClear( vLits );
        for ( pLit = p->pCnf2->pClauses[i]; pLit < p->pCnf2->pClauses[i+1]; pLit++ )
        {
            iVar = Pdr_ObjSatVar2( p, k, Aig_ManObj(p->pAig, lit_var(*pLit)) );
            Vec_IntPush( vLits, toLitCond( iVar, lit_sign(*pLit) ) );
        }
        RetValue = sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits)+Vec_IntSize(vLits) );
        assert( RetValue );
    }
    Vec_IntFree( vLits );
    return iVarThis;
}

/**Function*************************************************************

  Synopsis    [Returns SAT variable of the given object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ObjSatVar( Pdr_Man_t * p, int k, Aig_Obj_t * pObj )
{
    if ( p->pPars->fMonoCnf )
        return Pdr_ObjSatVar1( p, k, pObj );
    else
        return Pdr_ObjSatVar2( p, k, pObj );
}


/**Function*************************************************************

  Synopsis    [Returns register number for the given SAT variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr_ObjRegNum1( Pdr_Man_t * p, int k, int iSatVar )
{
    int RegId;
    assert( iSatVar >= 0 );
    // consider the case of auxiliary variable
    if ( iSatVar >= p->pCnf1->nVars )
        return -1;
    // consider the case of register output
    RegId = Vec_IntEntry( p->vVar2Reg, iSatVar );
    assert( RegId >= 0 && RegId < Aig_ManRegNum(p->pAig) );
    return RegId;
}

/**Function*************************************************************

  Synopsis    [Returns register number for the given SAT variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr_ObjRegNum2( Pdr_Man_t * p, int k, int iSatVar )
{
    Aig_Obj_t * pObj;
    int ObjId;
    Vec_Int_t * vVar2Ids = (Vec_Int_t *)Vec_PtrEntry(p->vVar2Ids, k);
    assert( iSatVar > 0 && iSatVar < Vec_IntSize(vVar2Ids) );
    ObjId = Vec_IntEntry( vVar2Ids, iSatVar );
    if ( ObjId == -1 ) // activation variable
        return -1;
    pObj = Aig_ManObj( p->pAig, ObjId );
    if ( Saig_ObjIsLi( p->pAig, pObj ) )
        return Aig_ObjPioNum(pObj)-Saig_ManPoNum(p->pAig);
    assert( 0 ); // should be called for register inputs only
    return -1;
}

/**Function*************************************************************

  Synopsis    [Returns register number for the given SAT variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ObjRegNum( Pdr_Man_t * p, int k, int iSatVar )
{
    if ( p->pPars->fMonoCnf )
        return Pdr_ObjRegNum1( p, k, iSatVar );
    else
        return Pdr_ObjRegNum2( p, k, iSatVar );
}


/**Function*************************************************************

  Synopsis    [Returns the index of unused SAT variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManFreeVar( Pdr_Man_t * p, int k )
{
    if ( p->pPars->fMonoCnf )
        return sat_solver_nvars( Pdr_ManSolver(p, k) );
    else
    {
        Vec_Int_t * vVar2Ids = (Vec_Int_t *)Vec_PtrEntry( p->vVar2Ids, k );
        Vec_IntPush( vVar2Ids, -1 );
        return Vec_IntSize( vVar2Ids ) - 1;
    }
}

/**Function*************************************************************

  Synopsis    [Creates SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sat_solver * Pdr_ManNewSolver1( sat_solver * pSat, Pdr_Man_t * p, int k, int fInit )
{
    Aig_Obj_t * pObj;
    int i;
    assert( pSat );
    if ( p->pCnf1 == NULL )
    {
        int nRegs = p->pAig->nRegs;
        p->pAig->nRegs = Aig_ManPoNum(p->pAig);
        p->pCnf1 = Cnf_Derive( p->pAig, Aig_ManPoNum(p->pAig) );
        p->pAig->nRegs = nRegs;
        assert( p->vVar2Reg == NULL );
        p->vVar2Reg = Vec_IntStartFull( p->pCnf1->nVars );
        Saig_ManForEachLi( p->pAig, pObj, i )
            Vec_IntWriteEntry( p->vVar2Reg, Pdr_ObjSatVar(p, k, pObj), i );
    }
    pSat = (sat_solver *)Cnf_DataWriteIntoSolverInt( pSat, p->pCnf1, 1, fInit );
    sat_solver_set_runtime_limit( pSat, p->timeToStop );
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Creates SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sat_solver * Pdr_ManNewSolver2( sat_solver * pSat, Pdr_Man_t * p, int k, int fInit )
{
    Vec_Int_t * vVar2Ids;
    int i, Entry;
    assert( pSat );
    if ( p->pCnf2 == NULL )
    {
        p->pCnf2     = Cnf_DeriveOther( p->pAig );
        p->pvId2Vars = ABC_CALLOC( Vec_Int_t *, Aig_ManObjNumMax(p->pAig) );
        p->vVar2Ids  = Vec_PtrAlloc( 256 );
    }
    // update the variable mapping
    vVar2Ids = (Vec_Int_t *)Vec_PtrGetEntry( p->vVar2Ids, k );
    if ( vVar2Ids == NULL )
    {
        vVar2Ids = Vec_IntAlloc( 500 );
        Vec_PtrWriteEntry( p->vVar2Ids, k, vVar2Ids );
    }
    Vec_IntForEachEntry( vVar2Ids, Entry, i )
    {
        if ( Entry == -1 )
            continue;
        assert( Vec_IntEntry( p->pvId2Vars[Entry], k ) > 0 );
        Vec_IntWriteEntry( p->pvId2Vars[Entry], k, 0 );
    }
    Vec_IntClear( vVar2Ids );
    Vec_IntPush( vVar2Ids, -1 );
    // start the SAT solver
//    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, 500 );
    sat_solver_set_runtime_limit( pSat, p->timeToStop );
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Creates SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * Pdr_ManNewSolver( sat_solver * pSat, Pdr_Man_t * p, int k, int fInit )
{
    assert( pSat != NULL );
    if ( p->pPars->fMonoCnf )
        return Pdr_ManNewSolver1( pSat, p, k, fInit );
    else
        return Pdr_ManNewSolver2( pSat, p, k, fInit );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

