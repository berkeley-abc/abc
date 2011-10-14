/**CFile****************************************************************

  FileName    [saigAbsGla.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Gate level abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigAbsGla.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "satSolver.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Aig_GlaMan_t_ Aig_GlaMan_t;
struct Aig_GlaMan_t_
{
    // user data
    Aig_Man_t *    pAig;
    int            nConfLimit;
    int            nFramesMax;
    int            fVerbose;
    // abstraction
    Vec_Int_t *    vAbstr;     // collects objects used in the abstraction
    Vec_Int_t *    vUsed;      // maps object ID into its status (0=unused; 1=used)
    Vec_Int_t *    vPis;       // primary inputs
    Vec_Int_t *    vPPis;      // pseudo primary inputs
    Vec_Int_t *    vFlops;     // flops
    Vec_Int_t *    vNodes;     // nodes
    // unrolling
    int            iFrame;
    int            nFrames;
    Vec_Int_t *    vObj2Vec;   // maps obj ID into its vec ID
    Vec_Int_t *    vVec2Var;   // maps vec ID into its sat Var (nFrames per vec ID)
    Vec_Int_t *    vVar2Inf;   // maps sat Var into its frame and obj ID
    // SAT solver
    sat_solver *   pSat;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs abstraction of the AIG to preserve the included gates.]

  Description [The array contains 1 if the obj is included; 0 otherwise.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_GlaDupAbsGates( Aig_Man_t * p, Vec_Int_t * vUsed, int * pnRealPis )
{ 
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, nFlops = 0, RetValue;
    assert( Aig_ManPoNum(p) == 1 );
    // start the new manager
    pNew = Aig_ManStart( 5000 );
    pNew->pName = Aig_UtilStrsav( p->pName );
    // create constant
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    // create PIs
    Saig_ManForEachPi( p, pObj, i )
        if ( Vec_IntEntry(vUsed, Aig_ObjId(pObj)) )
            pObj->pData = Aig_ObjCreatePi(pNew);
    if ( pnRealPis )
        *pnRealPis = Aig_ManPiNum(pNew);
    // create additional PIs
    Saig_ManForEachLiLo( p, pObjLi, pObjLo, i )
        if ( Vec_IntEntry(vUsed, Aig_ObjId(pObjLo)) && !Vec_IntEntry(vUsed, Aig_ObjId(pObjLi)) )
            pObjLo->pData = Aig_ObjCreatePi(pNew);
    Aig_ManForEachNode( p, pObj, i )
    {
        if ( Vec_IntEntry(vUsed, Aig_ObjId(pObj)) && 
             (!Vec_IntEntry(vUsed, Aig_ObjFaninId0(pObj)) ||
              !Vec_IntEntry(vUsed, Aig_ObjFaninId1(pObj))) )
            pObj->pData = Aig_ObjCreatePi(pNew);
    }
    // create ROs
    Saig_ManForEachLiLo( p, pObjLi, pObjLo, i )
        if ( Vec_IntEntry(vUsed, Aig_ObjId(pObjLo)) && Vec_IntEntry(vUsed, Aig_ObjId(pObjLi)) )
            pObjLo->pData = Aig_ObjCreatePi(pNew), nFlops++;
    // create internal nodes
    Aig_ManForEachNode( p, pObj, i )
    {
        if ( Vec_IntEntry(vUsed, Aig_ObjId(pObj)) && 
             Vec_IntEntry(vUsed, Aig_ObjFaninId0(pObj)) && 
             Vec_IntEntry(vUsed, Aig_ObjFaninId1(pObj)) )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    }
    // create PO
    Saig_ManForEachPo( p, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    // create RIs
    Saig_ManForEachLiLo( p, pObjLi, pObjLo, i )
        if ( Vec_IntEntry(vUsed, Aig_ObjId(pObjLo)) && Vec_IntEntry(vUsed, Aig_ObjId(pObjLi)) )
            pObjLi->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObjLi) );
    Aig_ManSetRegNum( pNew, nFlops );
    // clean up
    RetValue = Aig_ManCleanup( pNew );
    assert( RetValue == 0 );
    return pNew;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_GlaDeriveAbs( Aig_GlaMan_t * p )
{ 
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i, nFlops = 0, RetValue;
    assert( Aig_ManPoNum(p) == 1 );
    // start the new manager
    pNew = Aig_ManStart( 5000 );
    pNew->pName = Aig_UtilStrsav( p->pAig->pName );
    // create constant
    Aig_ManCleanData( p->pAig );
    Aig_ManConst1(p->pAig)->pData = Aig_ManConst1(pNew);
    // create PIs
    Aig_ManForEachObjVec( p->vPis, p->pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi(pNew);
    // create additional PIs
    Aig_ManForEachObjVec( p->vPPis, p->pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi(pNew);
    // create ROs
    Aig_ManForEachObjVec( p->vFlops, p->pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi(pNew);
    // create internal nodes
    Aig_ManForEachObjVec( p->vNodes, p->pAig, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create PO
    Saig_ManForEachPo( p->pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    // create RIs
    Aig_ManForEachObjVec( p->vFlops, p->pAig, pObj, i )
        Saig_ObjLoToLi(p->pAig, pObj)->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(Saig_ObjLoToLi(p->pAig, pObj)) );
    Aig_ManSetRegNum( pNew, Vec_IntSize(p->vFlops) );
    // clean up
    RetValue = Aig_ManCleanup( pNew );
    assert( RetValue == 0 );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Adds constant to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_GlaAddConst( sat_solver * pSat, int iVar, int fCompl )
{
    lit Lit = toLitCond( iVar, fCompl );
    if ( !sat_solver_addclause( pSat, &Lit, &Lit + 1 ) )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds buffer to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_GlaAddBuffer( sat_solver * pSat, int iVar0, int iVar1, int fCompl )
{
    lit Lits[2];

    Lits[0] = toLitCond( iVar0, 0 );
    Lits[1] = toLitCond( iVar1, !fCompl );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
        return 0;

    Lits[0] = toLitCond( iVar0, 1 );
    Lits[1] = toLitCond( iVar1, fCompl );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
        return 0;

    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds buffer to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_GlaAddNode( sat_solver * pSat, int iVar, int iVar0, int iVar1, int fCompl0, int fCompl1 )
{
    lit Lits[3];

    Lits[0] = toLitCond( iVar, 1 );
    Lits[1] = toLitCond( iVar0, fCompl0 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
        return 0;

    Lits[0] = toLitCond( iVar, 1 );
    Lits[1] = toLitCond( iVar1, fCompl1 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
        return 0;

    Lits[0] = toLitCond( iVar, 0 );
    Lits[1] = toLitCond( iVar0, !fCompl0 );
    Lits[2] = toLitCond( iVar1, !fCompl1 );
    if ( !sat_solver_addclause( pSat, Lits, Lits + 3 ) )
        return 0;

    return 1;
}


/**Function*************************************************************

  Synopsis    [Finds existing SAT variable or creates a new one.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_GlaFetchVar( Aig_GlaMan_t * p, Aig_Obj_t * pObj, int k )
{
    int i, iVecId, iSatVar;
    if ( !Vec_IntEntry(p->vUsed, Aig_ObjId(pObj)) )
    {
        Vec_IntWriteEntry( p->vUsed, Aig_ObjId(pObj), 1 );
        Vec_IntPush( p->vAbstr, Aig_ObjId(pObj) );
    }
    iVecId = Vec_IntEntry( p->vObj2Vec, Aig_ObjId(pObj) );
    if ( iVecId == 0 )
    {
        iVecId = Vec_IntSize( p->vVec2Var ) / p->nFrames;
        for ( i = 0; i < p->nFrames; i++ )
            Vec_IntPush( p->vVec2Var, 0 );
    }
    iSatVar = Vec_IntEntry( p->vVec2Var, iVecId * p->nFrames + k );
    if ( iSatVar == 0 )
    {
        iSatVar = Vec_IntSize( p->vVar2Inf ) / 2;
        Vec_IntPush( p->vVar2Inf, Aig_ObjId(pObj) );
        Vec_IntPush( p->vVar2Inf, k );
        Vec_IntWriteEntry( p->vVec2Var, iVecId * p->nFrames + k, iSatVar );
    }
    return iSatVar;
}

/**Function*************************************************************

  Synopsis    [Adds CNF for the given object in the given frame.]

  Description [Returns 0, if the solver becames UNSAT.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_GlaObjAddToSolver( Aig_GlaMan_t * p, Aig_Obj_t * pObj, int k )
{
    assert( Vec_IntEntry(vUsed, Aig_ObjId(pObj)) );
    if ( Aig_ObjIsConst1(pObj) )
        return Aig_GlaAddConst( p->pSat, Aig_GlaFetchVar(p, pObj, k), 0 );
    if ( Saig_ObjIsPi(p->pAig, pObj) )
        return 1;
    if ( Saig_ObjIsLo(p->pAig, pObj) )
    {
        Aig_Obj_t * pObjLi = Saig_ObjLoToLi(p->pAig, pObj);
        if ( k == 0 )
            return Aig_GlaAddConst( p->pSat, Aig_GlaFetchVar(p, pObj, k), 1 );
        if ( Vec_IntEntry(p->vUsed, Aig_ObjId(pObjLi)) )
            return 1;
        return Aig_GlaAddBuffer( p->pSat, Aig_GlaFetchVar(p, pObj, k), Aig_GlaFetchVar(p, Aig_ObjFanin0(pObjLi), k-1), Aig_ObjFaninC0(pObjLi) );
    }
    assert( Aig_ObjIsNode(pObj) );
    if ( Vec_IntEntry(p->vUsed, Aig_ObjFaninId0(pObj)) && Vec_IntEntry(p->vUsed, Aig_ObjFaninId1(pObj)) )
        return 0;
    return Aig_GlaAddNode( p->pSat, Aig_GlaFetchVar(p, pObj, k), 
        Aig_GlaFetchVar(p, Aig_ObjFanin0(pObj), k), 
        Aig_GlaFetchVar(p, Aig_ObjFanin1(pObj), k), 
        Aig_ObjFaninC0(pObj), Aig_ObjFaninC1(pObj) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_GlaMan_t * Aig_GlaManStart( Aig_Man_t * pAig )
{
    Aig_GlaMan_t * p;
    int i;

    p = ABC_CALLOC( Aig_GlaMan_t, 1 );
    p->pAig     = pAig;
    p->vAbstr   = Vec_IntAlloc( 1000 );
    p->vUsed    = Vec_IntStart( Aig_ManObjNumMax(pAig) );
    p->nFrames  = 16;

    p->vPis     = Vec_IntAlloc( 1000 );
    p->vPPis    = Vec_IntAlloc( 1000 );
    p->vFlops   = Vec_IntAlloc( 1000 );
    p->vNodes   = Vec_IntAlloc( 1000 );

    p->vObj2Vec = Vec_IntStart( Aig_ManObjNumMax(pAig) );
    p->vVec2Var = Vec_IntAlloc( 1 << 20 );
    p->vVar2Inf = Vec_IntAlloc( 1 << 20 );

    // skip first vector ID
    for ( i = 0; i < p->nFrames; i++ )
        Vec_IntPush( p->vVec2Var, -1 );
    // skip  first SAT variable
    Vec_IntPush( p->vVar2Inf, -1 );
    Vec_IntPush( p->vVar2Inf, -1 );

    // start the SAT solver
    p->pSat = sat_solver_new();
    sat_solver_setnvars( p->pSat, 1000 );
    return p;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_GlaManStop( Aig_GlaMan_t * p )
{
    Vec_IntFreeP( &p->vAbstr );
    Vec_IntFreeP( &p->vUsed );

    Vec_IntFreeP( &p->vPis );
    Vec_IntFreeP( &p->vPPis );
    Vec_IntFreeP( &p->vFlops );
    Vec_IntFreeP( &p->vNodes );

    Vec_IntFreeP( &p->vObj2Vec );
    Vec_IntFreeP( &p->vVec2Var );
    Vec_IntFreeP( &p->vVar2Inf );

    if ( p->pSat )
        sat_solver_delete( p->pSat );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_GlaCollectAbstr( Aig_GlaMan_t * p )
{
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i;
    Vec_IntClear( p->vPis );
    Vec_IntClear( p->vPPis );
    Vec_IntClear( p->vFlops );
    Vec_IntClear( p->vNodes );

    Saig_ManForEachPi( p->pAig, pObj, i )
        if ( Vec_IntEntry(p->vUsed, Aig_ObjId(pObj)) )
            Vec_IntPush( p->vPis, Aig_ObjId(pObj) );

    Saig_ManForEachLiLo( p->pAig, pObjLi, pObjLo, i )
        if ( Vec_IntEntry(p->vUsed, Aig_ObjId(pObjLo)) )
        {
            if ( Vec_IntEntry(p->vUsed, Aig_ObjFaninId0(pObjLi)) )
                Vec_IntPush( p->vFlops, Aig_ObjId(pObjLo) );
            else
                Vec_IntPush( p->vPPis, Aig_ObjId(pObjLo) );
        }

    Aig_ManForEachNode( p->pAig, pObj, i )
        if ( Vec_IntEntry(p->vUsed, Aig_ObjId(pObj)) )
        {
            if ( Vec_IntEntry(p->vUsed, Aig_ObjFaninId0(pObj)) && Vec_IntEntry(p->vUsed, Aig_ObjFaninId1(pObj)) )
                Vec_IntPush( p->vNodes, Aig_ObjId(pObjLo) );
            else
                Vec_IntPush( p->vPPis, Aig_ObjId(pObjLo) );
        }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Aig_GlaDeriveCex( Aig_GlaMan_t * p )
{
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_GlaPrintAbstr( Aig_GlaMan_t * p, int f, int r )
{
    printf( "Fra %3d : Ref %3d : PI =%6d  PPI =%6d  Flop =%6d  Node =%6d\n", 
        f, r, Vec_IntSize(p->vPis), Vec_IntSize(p->vPPis), Vec_IntSize(p->vFlops), Vec_IntSize(p->vNodes) );
}

/**Function*************************************************************

  Synopsis    [Perform variable frame abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_GlaManTest( Aig_Man_t * pAig, int nFramesMax, int nConfLimit, int fVerbose )
{
    Aig_GlaMan_t * p;
    Aig_Man_t * pAbs;
    Aig_Obj_t * pObj;
    Abc_Cex_t * pCex;
    Vec_Int_t * vPPisToRefine;
    int f, g, r, i, iSatVar, Lit, Entry, RetValue;
    assert( Saig_ManPoNum(pAig) == 1 );

    // start the solver
    p = Aig_GlaManStart( pAig );
    p->nFramesMax = nFramesMax;
    p->nConfLimit = nConfLimit;
    p->fVerbose   = fVerbose;

    // iterate over the timeframes
    for ( f = 0; f < nFramesMax; f++ )
    {
        // initialize abstraction in this timeframe
        Aig_ManForEachObjVec( p->vAbstr, pAig, pObj, i )
            Aig_GlaObjAddToSolver( p, pObj, f );

        // create output literal to represent property failure
        pObj    = Aig_ManPo( pAig, 0 );
        iSatVar = Aig_GlaFetchVar( p, Aig_ObjFanin0(pObj), f );
        Lit     = toLitCond( iSatVar, Aig_ObjFaninC0(pObj) );

        // try solving the abstraction
        Aig_GlaPrintAbstr( p, f, -1 );
        for ( r = 0; r < 1000000; r++ )
        {
            RetValue = sat_solver_solve( p->pSat, &Lit, &Lit + 1, 
                (ABC_INT64_T)nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
            if ( RetValue != l_True )
                break;
            // derive abstraction
            Aig_GlaCollectAbstr( p );
            // derive counter-example
            pCex = Aig_GlaDeriveCex( p );
            // derive abstraction
            pAbs = Aig_GlaDeriveAbs( p );
            // perform refinement
            vPPisToRefine = Saig_ManCbaFilterInputs( pAig, Vec_IntSize(p->vPis), pCex, 0 );
            // update
            Vec_IntForEachEntry( vPPisToRefine, Entry, i )
            {
                for ( g = 0; g <= f; g++ )
                    Aig_GlaObjAddToSolver( p, Aig_ManObj(pAig, Vec_IntEntry(p->vPPis, Entry)), g );
            }
            Vec_IntFree( vPPisToRefine );
            // print abstraction
            Aig_GlaPrintAbstr( p, f, r );
        }
        if ( RetValue != l_False )
            break;
    }
    Aig_GlaPrintAbstr( p, f, -1 );
    if ( f == nFramesMax )
        printf( "Finished %d frames without exceeding conflict limit (%d).\n", f, nConfLimit );
    else
        printf( "Ran out of conflict limit (%d) at frame %d.\n", nConfLimit, f );

    Aig_GlaManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

