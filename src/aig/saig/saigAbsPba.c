/**CFile****************************************************************

  FileName    [saigAbsPba.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Proof-based abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigAbsPba.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "cnf.h"
#include "satSolver.h"
#include "giaAig.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect nodes in the unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManUnrollForPba_rec( Aig_Man_t * pAig, Aig_Obj_t * pObj, Vec_Int_t * vObjs, Vec_Int_t * vRoots )
{
    if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(pAig, pObj);
    if ( Aig_ObjIsPo(pObj) )
        Saig_ManUnrollForPba_rec( pAig, Aig_ObjFanin0(pObj), vObjs, vRoots );
    else if ( Aig_ObjIsNode(pObj) )
    {
        Saig_ManUnrollForPba_rec( pAig, Aig_ObjFanin0(pObj), vObjs, vRoots );
        Saig_ManUnrollForPba_rec( pAig, Aig_ObjFanin1(pObj), vObjs, vRoots );
    }
    if ( vRoots && Saig_ObjIsLo( pAig, pObj ) )
        Vec_IntPush( vRoots, Aig_ObjId( Saig_ObjLoToLi(pAig, pObj) ) );
    Vec_IntPush( vObjs, Aig_ObjId(pObj) );
}

/**Function*************************************************************

  Synopsis    [Derives unrolled timeframes for PBA.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Aig_Man_t * Saig_ManUnrollForPba( Aig_Man_t * pAig, int nFrames, Vec_Int_t ** pvPiVarMap )
{
    Aig_Man_t * pFrames;     // unrolled timeframes
    Vec_Vec_t * vFrameCos;   // the list of COs per frame
    Vec_Vec_t * vFrameObjs;  // the list of objects per frame
    Vec_Int_t * vRoots, * vObjs;
    Aig_Obj_t * pObj, * pObjNew;
    int i, f;
    // collect COs and Objs visited in each frame
    vFrameCos  = Vec_VecStart( nFrames );
    vFrameObjs = Vec_VecStart( nFrames );
    for ( f = nFrames-1; f >= 0; f-- )
    {
        // add POs of this frame
        vRoots = Vec_VecEntryInt( vFrameCos, f );
        Saig_ManForEachPo( pAig, pObj, i )
            Vec_IntPush( vRoots, Aig_ObjId(pObj) );
        // collect nodes starting from the roots
        Aig_ManIncrementTravId( pAig );
        Aig_ManForEachObjVec( vRoots, pAig, pObj, i )
            Saig_ManUnrollForPba_rec( pAig, pObj, 
                Vec_VecEntryInt( vFrameObjs, f ),
                (Vec_Int_t *)(f ? Vec_VecEntry(vFrameCos, f-1) : NULL) );
    }
    // derive unrolled timeframes
    pFrames = Aig_ManStart( 10000 );
    pFrames->pName = Aig_UtilStrsav( pAig->pName );
    pFrames->pSpec = Aig_UtilStrsav( pAig->pSpec );
    // create activation variables
    Saig_ManForEachLo( pAig, pObj, i )
        Aig_ObjCreatePi( pFrames );
    // initialize the flops 
    Saig_ManForEachLo( pAig, pObj, i )
        pObj->pData = Aig_Mux( pFrames, Aig_ManPi(pFrames,i), Aig_ObjCreatePi(pFrames), Aig_ManConst0(pFrames) );
    // iterate through the frames
    *pvPiVarMap = Vec_IntStartFull( nFrames * Saig_ManPiNum(pAig) );
    pObjNew = Aig_ManConst0(pFrames);
    for ( f = 0; f < nFrames; f++ )
    {
        // construct
        vObjs = Vec_VecEntryInt( vFrameObjs, f );
        Aig_ManForEachObjVec( vObjs, pAig, pObj, i )
        {
            if ( Aig_ObjIsNode(pObj) )
                pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
            else if ( Aig_ObjIsPo(pObj) )
                pObj->pData = Aig_ObjChild0Copy(pObj);
            else if ( Saig_ObjIsPi(pAig, pObj) )
            {
                Vec_IntWriteEntry( *pvPiVarMap, f * Saig_ManPiNum(pAig) + Aig_ObjPioNum(pObj), Aig_ManPiNum(pFrames) );
                pObj->pData = Aig_ObjCreatePi( pFrames );
            }
            else if ( Aig_ObjIsConst1(pObj) )
                pObj->pData = Aig_ManConst1(pFrames);
            else if ( !Saig_ObjIsLo(pAig, pObj) )
                assert( 0 );
        }
        // create output
        Saig_ManForEachPo( pAig, pObj, i )
            pObjNew = Aig_Or( pFrames, pObjNew, pObj->pData );
        // transfer
        if ( f == nFrames - 1 )
            break;
        vRoots = Vec_VecEntryInt( vFrameCos, f );
        Aig_ManForEachObjVec( vRoots, pAig, pObj, i )
        {
            if ( Saig_ObjIsLi(pAig, pObj) )
            {
                int iFlopNum = Aig_ObjPioNum(pObj) - Saig_ManPoNum(pAig);
                assert( iFlopNum >= 0 && iFlopNum < Aig_ManRegNum(pAig) );
                Saig_ObjLiToLo(pAig, pObj)->pData = Aig_Mux( pFrames, Aig_ManPi(pFrames,iFlopNum), Aig_ObjCreatePi(pFrames), pObj->pData );
            }
        }
    }
    // cleanup
    Vec_VecFree( vFrameCos );
    Vec_VecFree( vFrameObjs );
    // create output
    Aig_ObjCreatePo( pFrames, pObjNew );
    Aig_ManSetRegNum( pFrames, 0 );
    // finallize
    Aig_ManCleanup( pFrames );
    return pFrames;
}

/**Function*************************************************************

  Synopsis    [Derives the counter-example from the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Saig_ManPbaDeriveCex( Aig_Man_t * pAig, sat_solver * pSat, Cnf_Dat_t * pCnf, int nFrames, Vec_Int_t * vPiVarMap )
{
    Abc_Cex_t * pCex;
    int i, f, Entry;
    pCex = Abc_CexAlloc( Aig_ManRegNum(pAig), Saig_ManPiNum(pAig), nFrames );   
    Vec_IntForEachEntry( vPiVarMap, Entry, i )
        if ( Entry >= 0 )
        {
            int iSatVar = pCnf->pVarNums[ Aig_ObjId(Aig_ManPi(pCnf->pMan, Entry)) ];
            if ( sat_solver_var_value( pSat, iSatVar ) )
                Aig_InfoSetBit( pCex->pData, Aig_ManRegNum(pAig) + i );
        }
    // check what frame has failed
    for ( f = 0; f < nFrames; f++ )
    {
//        Aig_ManForEach
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Derive unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManPbaDerive( Aig_Man_t * pAig, int nInputs, int nFrames, int nConfLimit, int fVerbose )
{
    Vec_Int_t * vFlops, * vMapVar2FF, * vAssumps, * vPiVarMap;
    Aig_Man_t * pFrames;
    sat_solver * pSat;
    Cnf_Dat_t * pCnf;
    Aig_Obj_t * pObj;
    int nCoreLits, * pCoreLits;
    int i, iVar, RetValue, clk;

    // create SAT solver
clk = clock();
    pFrames = Saig_ManUnrollForPba( pAig, nFrames, &vPiVarMap );
if ( fVerbose )
Aig_ManPrintStats( pFrames );
//    pCnf = Cnf_DeriveSimple( pFrames, 0 );
    pCnf = Cnf_Derive( pFrames, 0 );
    pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
    if ( pSat == NULL )
    {
        Aig_ManStop( pFrames );
        Cnf_DataFree( pCnf );
        return NULL;
    }
if ( fVerbose )
Abc_PrintTime( 1, "Preparing", clock() - clk );

    // map activation variables into flop numbers
    vAssumps = Vec_IntAlloc( Aig_ManRegNum(pAig) );
    vMapVar2FF = Vec_IntStartFull( pCnf->nVars );
    Aig_ManForEachPi( pFrames, pObj, i )
    {
        if ( i >= Aig_ManRegNum(pAig) )
            break;
        iVar = pCnf->pVarNums[Aig_ObjId(pObj)];
        Vec_IntPush( vAssumps, toLitCond(iVar, 1) );
        Vec_IntWriteEntry( vMapVar2FF, iVar, i );
    }

    // run SAT solver
clk = clock();
    RetValue = sat_solver_solve( pSat, Vec_IntArray(vAssumps), Vec_IntArray(vAssumps) + Vec_IntSize(vAssumps), 
        (ABC_INT64_T)nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
if ( fVerbose )
Abc_PrintTime( 1, "Solving", clock() - clk );
    if ( RetValue != l_False )
    {
        if ( RetValue == l_True )
        {
            Vec_Int_t * vAbsFfsToAdd;
            ABC_FREE( pAig->pSeqModel );
            pAig->pSeqModel = Saig_ManPbaDeriveCex( pAig, pSat, pCnf, nFrames, vPiVarMap );
            // CEX is detected - refine the flops
            vAbsFfsToAdd = Saig_ManCbaFilterInputs( pAig, nInputs, pAig->pSeqModel, fVerbose );
            if ( Vec_IntSize(vAbsFfsToAdd) == 0 )
            {
                Vec_IntFree( vAbsFfsToAdd );
                return NULL;
            }
            if ( fVerbose )
            {
                printf( "Adding %d registers to the abstraction.  ", Vec_IntSize(vAbsFfsToAdd) );
                Abc_PrintTime( 0, "Time", clock() - clk );
            }
            return vAbsFfsToAdd;
        }
        else
        {
            printf( "Saig_ManPerformPba(): SAT solver timed out. Abstraction is not changed.\n" );
        }
        Vec_IntFree( vPiVarMap );
        Vec_IntFree( vAssumps );
        Vec_IntFree( vMapVar2FF );
        sat_solver_delete( pSat );
        Aig_ManStop( pFrames );
        Cnf_DataFree( pCnf );
        return NULL;
    }
    assert( RetValue == l_False ); // UNSAT

    // get relevant SAT literals
    nCoreLits = sat_solver_final( pSat, &pCoreLits );
    assert( nCoreLits > 0 );
    if ( fVerbose )
        printf( "AnalizeFinal selected %d assumptions (out of %d). Conflicts = %d.\n", 
            nCoreLits, Vec_IntSize(vAssumps), (int)pSat->stats.conflicts );

    // collect flops
    vFlops = Vec_IntAlloc( nCoreLits );
    for ( i = 0; i < nCoreLits; i++ )
    {
        iVar = Vec_IntEntry( vMapVar2FF, lit_var(pCoreLits[i]) );
        assert( iVar >= 0 && iVar < Aig_ManRegNum(pAig) );
        Vec_IntPush( vFlops, iVar );
    }
    Vec_IntSort( vFlops, 0 );

    // cleanup
    Vec_IntFree( vPiVarMap );
    Vec_IntFree( vAssumps );
    Vec_IntFree( vMapVar2FF );
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnf );
    Aig_ManStop( pFrames );
    return vFlops;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

