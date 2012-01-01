/**CFile****************************************************************

  FileName    [giaCCof.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Backward reachability using circuit cofactoring.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCCof.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "satSolver.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ccf_Man_t_ Ccf_Man_t; // manager
struct Ccf_Man_t_
{
    // user data
    Gia_Man_t *   pGia;         // single output AIG manager
    int           nFrameMax;    // maximum number of frames
    int           nConfMax;     // maximum number of conflicts
    int           nTimeMax;     // maximum runtime in seconds
    int           fVerbose;     // verbose flag
    // internal data
    sat_solver *  pSat;         // SAT solver
    Gia_Man_t *   pFrames;      // unrolled timeframes
    Vec_Int_t *   vIdToFra;     // maps GIA obj IDs into frame obj IDs
    Vec_Int_t *   vOrder;       // map Num to Id
    Vec_Int_t *   vFraLims;     // frame limits
};

extern Vec_Int_t * Gia_VtaCollect( Gia_Man_t * p, Vec_Int_t ** pvFraLims, Vec_Int_t ** pvRoots );

static inline int  Gia_ObjFrames( Ccf_Man_t * p, int f, Gia_Obj_t * pObj )             { assert( Vec_IntEntry(p->vIdToFra, f*Gia_ManObjNum(p->pGia)+Gia_ObjId(p->pGia,pObj)) >= 0 ); return Vec_IntEntry(p->vIdToFra, f*Gia_ManObjNum(p->pGia)+Gia_ObjId(p->pGia,pObj));     }
static inline void Gia_ObjSetFrames( Ccf_Man_t * p, int f, Gia_Obj_t * pObj, int Lit ) { Vec_IntWriteEntry(p->vIdToFra, f*Gia_ManObjNum(p->pGia)+Gia_ObjId(p->pGia,pObj), Lit);  }

static inline int  Gia_ObjChild0Frames( Ccf_Man_t * p, int f, Gia_Obj_t * pObj )       { return Gia_LitNotCond(Gia_ObjFrames(p, f, Gia_ObjFanin0(pObj)), Gia_ObjFaninC0(pObj));  }
static inline int  Gia_ObjChild1Frames( Ccf_Man_t * p, int f, Gia_Obj_t * pObj )       { return Gia_LitNotCond(Gia_ObjFrames(p, f, Gia_ObjFanin1(pObj)), Gia_ObjFaninC1(pObj));  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline int sat_solver_add_const( sat_solver * pSat, int iVar, int fCompl )
{
    lit Lits[1];
    int Cid;
    assert( iVar >= 0 );

    Lits[0] = toLitCond( iVar, fCompl );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 1 );
    assert( Cid );
    return 1;
}
static inline int sat_solver_add_buffer( sat_solver * pSat, int iVarA, int iVarB, int fCompl )
{
    lit Lits[2];
    int Cid;
    assert( iVarA >= 0 && iVarB >= 0 );

    Lits[0] = toLitCond( iVarA, 0 );
    Lits[1] = toLitCond( iVarB, !fCompl );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );

    Lits[0] = toLitCond( iVarA, 1 );
    Lits[1] = toLitCond( iVarB, fCompl );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );
    return 2;
}
static inline int sat_solver_add_and( sat_solver * pSat, int iVar, int iVar0, int iVar1, int fCompl0, int fCompl1 )
{
    lit Lits[3];
    int Cid;

    Lits[0] = toLitCond( iVar, 1 );
    Lits[1] = toLitCond( iVar0, fCompl0 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );

    Lits[0] = toLitCond( iVar, 1 );
    Lits[1] = toLitCond( iVar1, fCompl1 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );

    Lits[0] = toLitCond( iVar, 0 );
    Lits[1] = toLitCond( iVar0, !fCompl0 );
    Lits[2] = toLitCond( iVar1, !fCompl1 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 3 );
    assert( Cid );
    return 3;
}
static inline int sat_solver_add_xor( sat_solver * pSat, int iVarA, int iVarB, int iVarC, int fCompl )
{
    lit Lits[3];
    int Cid;
    assert( iVarA >= 0 && iVarB >= 0 && iVarC >= 0 );

    Lits[0] = toLitCond( iVarA, !fCompl );
    Lits[1] = toLitCond( iVarB, 1 );
    Lits[2] = toLitCond( iVarC, 1 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 3 );
    assert( Cid );

    Lits[0] = toLitCond( iVarA, !fCompl );
    Lits[1] = toLitCond( iVarB, 0 );
    Lits[2] = toLitCond( iVarC, 0 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 3 );
    assert( Cid );

    Lits[0] = toLitCond( iVarA, fCompl );
    Lits[1] = toLitCond( iVarB, 1 );
    Lits[2] = toLitCond( iVarC, 0 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 3 );
    assert( Cid );

    Lits[0] = toLitCond( iVarA, fCompl );
    Lits[1] = toLitCond( iVarB, 0 );
    Lits[2] = toLitCond( iVarC, 1 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 3 );
    assert( Cid );
    return 4;
}
static inline int sat_solver_add_constraint( sat_solver * pSat, int iVar, int fCompl )
{
    lit Lits[2];
    int Cid;
    assert( iVar >= 0 );

    Lits[0] = toLitCond( iVar, fCompl );
    Lits[1] = toLitCond( iVar+1, 0 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );

    Lits[0] = toLitCond( iVar, fCompl );
    Lits[1] = toLitCond( iVar+1, 1 );
    Cid = sat_solver_addclause( pSat, Lits, Lits + 2 );
    assert( Cid );
    return 2;
}


/**Function*************************************************************

  Synopsis    [Create manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ccf_Man_t * Ccf_ManStart( Gia_Man_t * pGia, int nFrameMax, int nConfMax, int nTimeMax, int fVerbose )
{
    Ccf_Man_t * p;
    assert( nFrameMax > 0 );
    p = ABC_CALLOC( Ccf_Man_t, 1 );
    p->pGia       = pGia;
    p->nFrameMax  = nFrameMax;    
    p->nConfMax   = nConfMax;
    p->nTimeMax   = nTimeMax;
    p->fVerbose   = fVerbose;
    // internal data
    p->pFrames    = Gia_ManStart( 10000 );
    Gia_ManHashAlloc( p->pFrames );
    p->vOrder     = Gia_VtaCollect( pGia, &p->vFraLims, NULL );
    p->vIdToFra   = Vec_IntAlloc( 0 );
    p->pSat       = sat_solver_new();
    sat_solver_setnvars( p->pSat, 10000 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Delete manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ccf_ManStop( Ccf_Man_t * p )
{
    Vec_IntFreeP( &p->vIdToFra );
    Vec_IntFreeP( &p->vOrder );
    Vec_IntFreeP( &p->vFraLims );
    sat_solver_delete( p->pSat );
    Gia_ManStopP( &p->pFrames );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Extends the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCofExtendSolver( Ccf_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    // add SAT clauses
    for ( i = sat_solver_nvars(p->pSat); i < Gia_ManObjNum(p->pFrames); i++ )
    {
        pObj = Gia_ManObj( p->pGia, i );
        if ( Gia_ObjIsAnd(pObj) )
            sat_solver_add_and( p->pSat, i, 
                Gia_ObjFaninId0(pObj, i), 
                Gia_ObjFaninId1(pObj, i), 
                Gia_ObjFaninC0(pObj), 
                Gia_ObjFaninC1(pObj) ); 
    }
}

/**Function*************************************************************

  Synopsis    [Adds logic of one timeframe to the manager.]

  Description [Returns literal of the property output.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCofAddTimeFrame( Ccf_Man_t * p, int fMax )
{
    Gia_Obj_t * pObj;
    int i, f, Beg, End, Lit;
    assert( fMax > 0 && fMax <= p->nFrameMax );
    assert( Vec_IntSize(p->vIdToFra) == (fMax - 1) * Gia_ManObjNum(p->pGia) );
    // add to the mapping of nodes
    Vec_IntFillExtra( p->vIdToFra, fMax * Gia_ManObjNum(p->pGia), -1 );
    // add nodes to each time-frame
    for ( f = 0; f < fMax; f++ )
    {
        if ( Vec_IntSize(p->vFraLims) >= fMax-f )
            continue;
        Beg = Vec_IntEntry( p->vFraLims, fMax-f-1 );
        End = Vec_IntEntry( p->vFraLims, fMax-f );
        for ( i = Beg; i < End; i++ )
        {
            pObj = Gia_ManObj( p->pGia, Vec_IntEntry(p->vOrder, i) );
            if ( Gia_ObjIsAnd(pObj) )
                Lit = Gia_ManHashAnd( p->pFrames, Gia_ObjChild0Frames(p, f, pObj), Gia_ObjChild1Frames(p, f, pObj) );
            else if ( Gia_ObjIsRo(p->pGia, pObj) && f > 0 )
                Lit = Gia_ObjChild0Frames(p, f-1, Gia_ObjRoToRi(p->pGia, pObj));
            else if ( Gia_ObjIsCi(pObj) )
            {
                Lit = Gia_ManAppendCi(p->pFrames);
                // mark primary input
                Gia_ManObj(p->pFrames, Gia_Lit2Var(Lit))->fMark0 = Gia_ObjIsPi(p->pGia, pObj);
            }
            else assert( 0 );
            Gia_ObjSetFrames( p, f, pObj, Lit );
        }
    }
    // add SAT clauses
    Gia_ManCofExtendSolver( p );
    // return output literal
    return Gia_ObjChild0Frames( p, fMax-1, Gia_ManPo(p->pGia, 0) );
}

/**Function*************************************************************

  Synopsis    [Cofactor the circuit w.r.t. the given assignment.]

  Description [Assumes that the solver has just returned SAT.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCofOneDerive_rec( Ccf_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return pObj->Value;
    assert( Gia_ObjIsCi(pObj) || Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjIsAnd(pObj) )
    {
        Gia_ManCofOneDerive_rec( p, Gia_ObjFanin0(pObj) );
        Gia_ManCofOneDerive_rec( p, Gia_ObjFanin1(pObj) );
        pObj->Value = Gia_ManHashAnd( p->pFrames, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    else if ( pObj->fMark0 ) // PI
        pObj->Value = sat_solver_var_value( p->pSat, Gia_ObjId(p->pGia, pObj) );
    else
        pObj->Value = Gia_Var2Lit( Gia_ObjId(p->pGia, pObj), 0 );
    return pObj->Value;
}

/**Function*************************************************************

  Synopsis    [Cofactor the circuit w.r.t. the given assignment.]

  Description [Assumes that the solver has just returned SAT.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCofOneDerive( Ccf_Man_t * p, int LitProp )
{
    Gia_Obj_t * pObj;
    int LitOut;
    // get the property node
    pObj = Gia_ManObj( p->pFrames, Gia_Lit2Var(LitProp) );
    // derive the cofactor
    Gia_ManFillValue( p->pFrames );
    LitOut = Gia_ManCofOneDerive_rec( p, pObj );
    LitOut = Gia_LitNotCond(LitOut, Gia_LitIsCompl(LitProp));
    // add new PO for the cofactor
    Gia_ManAppendCo( p->pFrames, LitOut );
    // add SAT clauses
    Gia_ManCofExtendSolver( p );
    // return negative literal of the cofactor
    return Gia_LitNot(LitOut);
}

/**Function*************************************************************

  Synopsis    [Enumerates backward reachable states.]

  Description [Return -1 if resource limit is reached. Returns 1 
  if computation converged (there is no more reachable states).
  Returns 0 if no more states to enumerate.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCofGetReachable( Ccf_Man_t * p, int Lit )
{
    int RetValue;
    // try solving for the first time and quit if converged
    RetValue = sat_solver_solve( p->pSat, &Lit, &Lit + 1, p->nConfMax, 0, 0, 0 );
    if ( RetValue == l_False )
        return 1;
    // iterate circuit cofactoring
    while ( RetValue == 0 )
    {
        // derive cofactor
        int LitOut = Gia_ManCofOneDerive( p, Lit );
        // add the blocking clause
        RetValue = sat_solver_addclause( p->pSat, &LitOut, &LitOut + 1 );
        assert( RetValue );
        // try solving again
        RetValue = sat_solver_solve( p->pSat, &Lit, &Lit + 1, p->nConfMax, 0, 0, 0 );
    }
    if ( RetValue == l_Undef )
        return -1;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCofTest( Gia_Man_t * pGia, int nFrameMax, int nConfMax, int nTimeMax, int fVerbose )
{
    Gia_Man_t * pNew;
    Ccf_Man_t * p;
    int f, Lit, RetValue;
    assert( Gia_ManPoNum(pGia) == 1 );
    // create reachability manager
    p = Ccf_ManStart( pGia, nFrameMax, nConfMax, nTimeMax, fVerbose );
    // perform backward image computation
    for ( f = 0; f < nFrameMax; f++ )
    {
        if ( fVerbose )
            printf( "ITER %3d :\n", f );
        // derives new timeframe and returns the property literal
        Lit = Gia_ManCofAddTimeFrame( p, f+1 );
        // derives cofactors of the property literal till all states are blocked
        RetValue = Gia_ManCofGetReachable( p, Lit );
        if ( RetValue )
            break;
    }
    // report the result
    if ( f == nFrameMax )
        printf( "Completed %d frames without converging.\n", f );
    else if ( RetValue == 1 )
        printf( "Backward reachability converged after %d iterations.\n", f );
    else if ( RetValue == -1 )
        printf( "Conflict limit or timeout is reached after %d frames.\n", f );

    // get the resulting AIG manager
    Gia_ManHashStop( p->pFrames );
    Gia_ManCleanMark0( p->pFrames );
    pNew = p->pFrames;  p->pFrames = NULL;
    Ccf_ManStop( p );
    pNew = Gia_ManCleanup( pGia = pNew );
    Gia_ManStop( pGia );

//    if ( fVerbose )
        Gia_ManPrintStats( pNew, 0 );
    return pNew;   
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

