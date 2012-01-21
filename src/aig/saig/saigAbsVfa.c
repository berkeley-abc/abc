/**CFile****************************************************************

  FileName    [saigAbsVfa.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Intergrated abstraction procedure.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigAbsVfa.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "src/sat/cnf/cnf.h"
#include "src/sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abs_VfaMan_t_ Abs_VfaMan_t;
struct Abs_VfaMan_t_
{
    Aig_Man_t *    pAig;
    int            nConfLimit;
    int            fVerbose;
    // unrolling info
    int            iFrame;
    int            nFrames;
    Vec_Int_t *    vObj2Vec;  // maps obj ID into its vec ID
    Vec_Int_t *    vVec2Var;  // maps vec ID into its sat Var (nFrames per vec ID)
    Vec_Int_t *    vVar2Inf;  // maps sat Var into its frame and obj ID
    Vec_Int_t *    vFra2Var;  // maps frame number into the first variable
    // SAT solver
    sat_solver *   pSat;
    Cnf_Dat_t *    pCnf;
    Vec_Int_t *    vAssumps;
    Vec_Int_t *    vCore;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Adds CNF clauses for the MUX.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs_VfaManSatMux( sat_solver * pSat, int VarF, int VarI, int VarT, int VarE )
{
    int RetValue, pLits[3];

    // f = ITE(i, t, e)

    // i' + t' + f
    // i' + t  + f'
    // i  + e' + f
    // i  + e  + f'

    // create four clauses
    pLits[0] = toLitCond(VarI, 1);
    pLits[1] = toLitCond(VarT, 1);
    pLits[2] = toLitCond(VarF, 0);
    RetValue = sat_solver_addclause( pSat, pLits, pLits + 3 );
    assert( RetValue );

    pLits[0] = toLitCond(VarI, 1);
    pLits[1] = toLitCond(VarT, 0);
    pLits[2] = toLitCond(VarF, 1);
    RetValue = sat_solver_addclause( pSat, pLits, pLits + 3 );
    assert( RetValue );

    pLits[0] = toLitCond(VarI, 0);
    pLits[1] = toLitCond(VarE, 1);
    pLits[2] = toLitCond(VarF, 0);
    RetValue = sat_solver_addclause( pSat, pLits, pLits + 3 );
    assert( RetValue );

    pLits[0] = toLitCond(VarI, 0);
    pLits[1] = toLitCond(VarE, 0);
    pLits[2] = toLitCond(VarF, 1);
    RetValue = sat_solver_addclause( pSat, pLits, pLits + 3 );
    assert( RetValue );

    // two additional clauses
    // t' & e' -> f'
    // t  & e  -> f 

    // t  + e   + f'
    // t' + e'  + f 
    assert( VarT != VarE );

    pLits[0] = toLitCond(VarT, 0);
    pLits[1] = toLitCond(VarE, 0);
    pLits[2] = toLitCond(VarF, 1);
    RetValue = sat_solver_addclause( pSat, pLits, pLits + 3 );
    assert( RetValue );

    pLits[0] = toLitCond(VarT, 1);
    pLits[1] = toLitCond(VarE, 1);
    pLits[2] = toLitCond(VarF, 0);
    RetValue = sat_solver_addclause( pSat, pLits, pLits + 3 );
    assert( RetValue );
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs_VfaManAddVar( Abs_VfaMan_t * p, Aig_Obj_t * pObj, int f, int * pfNew )
{
    int i, SatId, VecId = Vec_IntEntry( p->vObj2Vec, Aig_ObjId(pObj) );
    *pfNew = 0;
    if ( VecId == -1 )
        return -1;
    if ( VecId == 0 )
    {
        VecId = Vec_IntSize( p->vVec2Var ) / p->nFrames;
        for ( i = 0; i < p->nFrames; i++ )
            Vec_IntPush( p->vVec2Var, 0 );
        Vec_IntWriteEntry( p->vObj2Vec, Aig_ObjId(pObj), VecId );
    }
    SatId = Vec_IntEntry( p->vVec2Var, p->nFrames * VecId + f );
    if ( SatId )
        return SatId;
    SatId = Vec_IntSize( p->vVar2Inf ) / 2;
    // save SatId
    Vec_IntWriteEntry( p->vVec2Var, p->nFrames * VecId + f, SatId );
    Vec_IntPush( p->vVar2Inf, Aig_ObjId(pObj) );
    Vec_IntPush( p->vVar2Inf, f );
    if ( Saig_ObjIsLo( p->pAig, pObj ) ) // reserve IDs for aux vars
    {
        Vec_IntPush( p->vVar2Inf, -1 );
        Vec_IntPush( p->vVar2Inf, f );
        Vec_IntPush( p->vVar2Inf, -2 );
        Vec_IntPush( p->vVar2Inf, f );
    }
    *pfNew = 1;
    return SatId;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs_VfaManCreateFrame_rec( Abs_VfaMan_t * p, Aig_Obj_t * pObj, int f )
{
    int SatVar, fNew;
    if ( Aig_ObjIsConst1(pObj) )
        return -1;
    SatVar = Abs_VfaManAddVar( p, pObj, f, &fNew );
    if ( (SatVar > 0 && !fNew) || Saig_ObjIsPi(p->pAig, pObj) || (Aig_ObjIsPi(pObj) && f==0) )
        return SatVar;
    if ( Aig_ObjIsPo(pObj) )
        return Abs_VfaManCreateFrame_rec( p, Aig_ObjFanin0(pObj), f );
    if ( Aig_ObjIsPi(pObj) )
        return Abs_VfaManCreateFrame_rec( p, Saig_ObjLoToLi(p->pAig, pObj), f-1 );
    assert( Aig_ObjIsAnd(pObj) );
    Abs_VfaManCreateFrame_rec( p, Aig_ObjFanin0(pObj), f );
    Abs_VfaManCreateFrame_rec( p, Aig_ObjFanin1(pObj), f );
    return SatVar;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs_VfaManCreateFrame( Abs_VfaMan_t * p, int f )
{
    Aig_Obj_t * pObj;
    int i, clk = clock();

    Saig_ManForEachPo( p->pAig, pObj, i )
        Abs_VfaManCreateFrame_rec( p, pObj, f );
    
    Vec_IntPush( p->vFra2Var, Vec_IntSize( p->vVar2Inf ) / 2 );

    printf( "Frame = %3d : ", f );
    printf( "Vecs = %8d  ", Vec_IntSize( p->vVec2Var ) / p->nFrames );
    printf( "Vars = %8d  ", Vec_IntSize( p->vVar2Inf ) / 2 );
    Abc_PrintTime( 1, "Time", clock() - clk );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abs_VfaMan_t * Abs_VfaManStart( Aig_Man_t * pAig )
{
    Abs_VfaMan_t * p;
    int i;

    p = ABC_CALLOC( Abs_VfaMan_t, 1 );
    p->pAig = pAig;
    p->vObj2Vec = Vec_IntStart( Aig_ManObjNumMax(pAig) );
    p->vVec2Var = Vec_IntAlloc( 1 << 20 );
    p->vVar2Inf = Vec_IntAlloc( 1 << 20 );
    p->vFra2Var = Vec_IntStart( 1 );

    // skip the first variable
    Vec_IntPush( p->vVar2Inf, -3 );
    Vec_IntPush( p->vVar2Inf, -3 );
    for ( i = 0; i < p->nFrames; i++ )
        Vec_IntPush( p->vVec2Var, -1 );

    // transfer values from CNF
    p->pCnf = Cnf_DeriveOther( pAig );
    for ( i = 0; i < Aig_ManObjNumMax(pAig); i++ )
        if ( p->pCnf->pObj2Clause[i] == -1 )
            Vec_IntWriteEntry( p->vObj2Vec, i, -1 );

    p->vAssumps = Vec_IntAlloc( 100 );
    p->vCore    = Vec_IntAlloc( 100 );
    return p;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs_VfaManStop( Abs_VfaMan_t * p )
{
    Vec_IntFreeP( &p->vObj2Vec );
    Vec_IntFreeP( &p->vVec2Var );
    Vec_IntFreeP( &p->vVar2Inf );
    Vec_IntFreeP( &p->vFra2Var );
    Vec_IntFreeP( &p->vAssumps );
    Vec_IntFreeP( &p->vCore );
    if ( p->pCnf )
        Cnf_DataFree( p->pCnf );
    if ( p->pSat )
        sat_solver_delete( p->pSat );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Perform variable frame abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs_VfaManTest( Aig_Man_t * pAig, int nFrames, int nConfLimit, int fVerbose )
{
    Abs_VfaMan_t * p;
    int i;

    p = Abs_VfaManStart( pAig );
    p->nFrames    = nFrames;
    p->nConfLimit = nConfLimit;
    p->fVerbose   = fVerbose;


    // create unrolling for the given number of frames
    for ( i = 0; i < p->nFrames; i++ )
        Abs_VfaManCreateFrame( p, i );    


    Abs_VfaManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

