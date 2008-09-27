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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Aig_Obj_t * Saig_ObjFrame( Aig_Obj_t ** ppMap, int nFrames, Aig_Obj_t * pObj, int i )                       { return ppMap[nFrames*pObj->Id + i];  }
static inline void        Saig_ObjSetFrame( Aig_Obj_t ** ppMap, int nFrames, Aig_Obj_t * pObj, int i, Aig_Obj_t * pNode ) { ppMap[nFrames*pObj->Id + i] = pNode; }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Create timeframes of the manager for BMC.]

  Description [The resulting manager is combinational. The only PO is
  the output of the last frame.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManFramesBmcLast( Aig_Man_t * pAig, int nFrames, Aig_Obj_t *** pppMap )
{
    Aig_Man_t * pFrames;
    Aig_Obj_t ** ppMap;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, f;
    assert( Saig_ManRegNum(pAig) > 0 );
    // start the mapping
    ppMap = *pppMap = CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAig) * nFrames );
    // start the manager
    pFrames = Aig_ManStart( Aig_ManNodeNum(pAig) * nFrames );
    // create variables for register outputs
    Saig_ManForEachLo( pAig, pObj, i )
    {
        pObj->pData = Aig_ManConst0( pFrames );
        Saig_ObjSetFrame( ppMap, nFrames, pObj, 0, pObj->pData );
    }
    // add timeframes
    for ( f = 0; f < nFrames; f++ )
    {
        // map the constant node
        Aig_ManConst1(pAig)->pData = Aig_ManConst1( pFrames );
        Saig_ObjSetFrame( ppMap, nFrames, Aig_ManConst1(pAig), f, Aig_ManConst1(pAig)->pData );
        // create PI nodes for this frame
        Saig_ManForEachPi( pAig, pObj, i )
        {
            pObj->pData = Aig_ObjCreatePi( pFrames );
            Saig_ObjSetFrame( ppMap, nFrames, pObj, f, pObj->pData );
        }
        // add internal nodes of this frame
        Aig_ManForEachNode( pAig, pObj, i )
        {
            pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
            Saig_ObjSetFrame( ppMap, nFrames, pObj, f, pObj->pData );
        }
        // create POs for this frame
        if ( f == nFrames - 1 )
        {
            Saig_ManForEachPo( pAig, pObj, i )
            {
                pObj->pData = Aig_ObjCreatePo( pFrames, Aig_ObjChild0Copy(pObj) );
                Saig_ObjSetFrame( ppMap, nFrames, pObj, f, pObj->pData );
            }
            break;
        }
        // save register inputs
        Saig_ManForEachLi( pAig, pObj, i )
        {
            pObj->pData = Aig_ObjChild0Copy(pObj);
            Saig_ObjSetFrame( ppMap, nFrames, pObj, f, pObj->pData );
        }
        // transfer to register outputs
        Saig_ManForEachLiLo(  pAig, pObjLi, pObjLo, i )
        {
            pObjLo->pData = pObjLi->pData;
            Saig_ObjSetFrame( ppMap, nFrames, pObjLo, f, pObjLo->pData );
        }
    }
    Aig_ManCleanup( pFrames );
    // remove mapping for the nodes that are no longer there
    for ( i = 0; i < Aig_ManObjNumMax(pAig) * nFrames; i++ )
        if ( ppMap[i] && Aig_ObjIsNone( Aig_Regular(ppMap[i]) ) )
            ppMap[i] = NULL;
    return pFrames;
}

/**Function*************************************************************

  Synopsis    [Finds the set of variables involved in the UNSAT core.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Saig_ManFindUnsatVariables( Cnf_Dat_t * pCnf, int nConfMax, int fVerbose )
{
    void * pSatCnf; 
    Intp_Man_t * pManProof;
    sat_solver * pSat;
    Vec_Int_t * vCore;
    int * pClause1, * pClause2, * pLit, * pVars, iClause, nVars;
    int i, RetValue;
    // create the SAT solver
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat ); 
    sat_solver_setnvars( pSat, pCnf->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
        {
            printf( "The BMC problem is trivially UNSAT.\n" );
            sat_solver_delete( pSat );
            return NULL;
        }
    }
    sat_solver_store_mark_roots( pSat ); 
    // solve the problem
    RetValue = sat_solver_solve( pSat, NULL, NULL, (sint64)nConfMax, (sint64)0, (sint64)0, (sint64)0 );
    if ( RetValue == l_Undef )
    {
        printf( "Conflict limit is reached.\n" );
        sat_solver_delete( pSat );
        return NULL;
    }
    if ( RetValue == l_True )
    {
        printf( "The BMC problem is SAT.\n" );
        sat_solver_delete( pSat );
        return NULL;
    }
    printf( "SAT solver returned UNSAT after %d conflicts.\n", pSat->stats.conflicts );
    assert( RetValue == l_False );
    pSatCnf = sat_solver_store_release( pSat ); 
    sat_solver_delete( pSat );
    // derive the UNSAT core
    pManProof = Intp_ManAlloc();
    vCore = Intp_ManUnsatCore( pManProof, pSatCnf, fVerbose );
    Intp_ManFree( pManProof );
    Sto_ManFree( pSatCnf );
    // derive the set of variables on which the core depends
    // collect the variable numbers
    nVars = 0;
    pVars = ALLOC( int, pCnf->nVars );
    memset( pVars, 0, sizeof(int) * pCnf->nVars );
    Vec_IntForEachEntry( vCore, iClause, i )
    {
        pClause1 = pCnf->pClauses[iClause];
        pClause2 = pCnf->pClauses[iClause+1];
        for ( pLit = pClause1; pLit < pClause2; pLit++ )
        {
            if ( pVars[ (*pLit) >> 1 ] == 0 )
                nVars++;
            pVars[ (*pLit) >> 1 ] = 1;
            if ( fVerbose )
            printf( "%s%d ", ((*pLit) & 1)? "-" : "+", (*pLit) >> 1 );
        }
        if ( fVerbose )
        printf( "\n" );
    }
    Vec_IntFree( vCore );
    return pVars;
}

/**Function*************************************************************

  Synopsis    [Labels nodes with the given CNF variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManMarkIntoPresentVars_rec( Aig_Obj_t * pObj, Cnf_Dat_t * pCnf, int iVar )
{
    int iVarThis = pCnf->pVarNums[pObj->Id];
    if ( iVarThis >= 0 && iVarThis != iVar )
        return;
    assert( Aig_ObjIsNode(pObj) );
    Saig_ManMarkIntoPresentVars_rec( Aig_ObjFanin0(pObj), pCnf, iVar );
    Saig_ManMarkIntoPresentVars_rec( Aig_ObjFanin1(pObj), pCnf, iVar );
    pCnf->pVarNums[pObj->Id] = iVar;
}

/**Function*************************************************************

  Synopsis    [Performs proof-based abstraction using BMC of the given depth.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManProofAbstraction( Aig_Man_t * p, int nFrames, int nConfMax, int fVerbose )
{
    Cnf_Dat_t * pCnf;
    Vec_Int_t * vFlops;
    Aig_Man_t * pFrames, * pResult;
    Aig_Obj_t ** ppAigToFrames;
    Aig_Obj_t * pObj, * pObjFrame;
    int f, i, * pUnsatCoreVars, clk = clock();
    assert( Saig_ManPoNum(p) == 1 );
    Aig_ManSetPioNumbers( p );
    if ( fVerbose )
        printf( "Performing proof-based abstraction with %d frames and %d max conflicts.\n", nFrames, nConfMax );
    // create the timeframes
    pFrames = Saig_ManFramesBmcLast( p, nFrames, &ppAigToFrames );
    // convert them into CNF
//    pCnf = Cnf_Derive( pFrames, 0 );
    pCnf = Cnf_DeriveSimple( pFrames, 0 );
    // collect CNF variables involved in UNSAT core
    pUnsatCoreVars = Saig_ManFindUnsatVariables( pCnf, nConfMax, 0 );
    if ( pUnsatCoreVars == NULL )
    {
        Aig_ManStop( pFrames );
        Cnf_DataFree( pCnf );
        return NULL;
    }
    if ( fVerbose )
    {
        int Counter = 0;
        for ( i = 0; i < pCnf->nVars; i++ )
            Counter += pUnsatCoreVars[i];
        printf( "The number of variables in the UNSAT core is %d (out of %d).\n", Counter, pCnf->nVars );
    }
    // map other nodes into existing CNF variables
    Aig_ManForEachNode( pFrames, pObj, i )
        if ( pCnf->pVarNums[pObj->Id] >= 0 )
            Saig_ManMarkIntoPresentVars_rec( pObj, pCnf, pCnf->pVarNums[pObj->Id] );
    // collect relevant registers
    for ( f = 0; f < nFrames; f++ )
    {
        Saig_ManForEachLo( p, pObj, i )
        {
            pObjFrame = Saig_ObjFrame( ppAigToFrames, nFrames, pObj, f );
            if ( pObjFrame == NULL )
                continue;
            pObjFrame = Aig_Regular(pObjFrame);
            if ( Aig_ObjIsConst1( pObjFrame ) )
                continue;
            assert( pCnf->pVarNums[pObjFrame->Id] >= 0 );
            if ( pUnsatCoreVars[ pCnf->pVarNums[pObjFrame->Id] ] )
                pObj->fMarkA = 1;
        }
    }
    // collect the flops
    vFlops = Vec_IntAlloc( 1000 );
    Saig_ManForEachLo( p, pObj, i )
        if ( pObj->fMarkA )
        {
            pObj->fMarkA = 0;
            Vec_IntPush( vFlops, i );
        }
    if ( fVerbose )
    {
        printf( "The number of relevant registers is %d (out of %d).\n", Vec_IntSize(vFlops), Aig_ManRegNum(p) );
        PRT( "Time", clock() - clk );
    }
    // create the resulting AIG
    pResult = Saig_ManAbstraction( p, vFlops );
    // cleanup
    Aig_ManStop( pFrames );
    Cnf_DataFree( pCnf );
    free( ppAigToFrames );
    free( pUnsatCoreVars );
    Vec_IntFree( vFlops );
    return pResult;

}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


