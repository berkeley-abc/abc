/**CFile****************************************************************

  FileName    [saigRefSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [SAT based refinement of a counter-example.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigRefSat.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "cnf.h"
#include "satSolver.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// local manager
typedef struct Saig_RefMan_t_ Saig_RefMan_t;
struct Saig_RefMan_t_
{
    // user data
    Aig_Man_t * pAig;       // user's AIG
    Abc_Cex_t * pCex;       // user's CEX
    int         nInputs;    // the number of first inputs to skip
    int         fVerbose;   // verbose flag
    // unrolling
    Aig_Man_t * pFrames;    // unrolled timeframes
    Vec_Int_t * vMapPiA3F;  // mapping of frame PIs into real PIs
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect nodes in the unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManUnrollCollect_rec( Aig_Man_t * pAig, Aig_Obj_t * pObj, Vec_Int_t * vObjs, Vec_Int_t * vRoots )
{
    if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(pAig, pObj);
    if ( Aig_ObjIsPo(pObj) )
        Saig_ManUnrollCollect_rec( pAig, Aig_ObjFanin0(pObj), vObjs, vRoots );
    else if ( Aig_ObjIsNode(pObj) )
    {
        Saig_ManUnrollCollect_rec( pAig, Aig_ObjFanin0(pObj), vObjs, vRoots );
        Saig_ManUnrollCollect_rec( pAig, Aig_ObjFanin1(pObj), vObjs, vRoots );
    }
    if ( vRoots && Saig_ObjIsLo( pAig, pObj ) )
        Vec_IntPush( vRoots, Aig_ObjId( Saig_ObjLoToLi(pAig, pObj) ) );
    Vec_IntPush( vObjs, Aig_ObjId(pObj) );
}

/**Function*************************************************************

  Synopsis    [Derive unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManUnrollWithCex( Aig_Man_t * pAig, Abc_Cex_t * pCex, int nInputs, Vec_Int_t ** pvMapPiA3F )
{
    Aig_Man_t * pFrames;     // unrolled timeframes
    Vec_Vec_t * vFrameCos;   // the list of COs per frame
    Vec_Vec_t * vFrameObjs;  // the list of objects per frame
    Vec_Int_t * vRoots, * vObjs;
    Aig_Obj_t * pObj;
    int i, f;
    // sanity checks
    assert( Saig_ManPiNum(pAig) == pCex->nPis );
    assert( Saig_ManRegNum(pAig) == pCex->nRegs );
    assert( pCex->iPo >= 0 && pCex->iPo < Saig_ManPoNum(pAig) );

    // map PIs of the unrolled frames into PIs of the original design
    *pvMapPiA3F = Vec_IntAlloc( 1000 );

    // collect COs and Objs visited in each frame
    vFrameCos  = Vec_VecStart( pCex->iFrame+1 );
    vFrameObjs = Vec_VecStart( pCex->iFrame+1 );
    // initialized the topmost frame
    pObj = Aig_ManPo( pAig, pCex->iPo );
    Vec_VecPushInt( vFrameCos, pCex->iFrame, Aig_ObjId(pObj) );
    for ( f = pCex->iFrame; f >= 0; f-- )
    {
        // collect nodes starting from the roots
        Aig_ManIncrementTravId( pAig );
        vRoots = (Vec_Int_t *)Vec_VecEntry( vFrameCos, f );
        Aig_ManForEachNodeVec( pAig, vRoots, pObj, i )
            Saig_ManUnrollCollect_rec( pAig, pObj, 
                (Vec_Int_t *)Vec_VecEntry(vFrameObjs, f),
                (Vec_Int_t *)(f ? Vec_VecEntry(vFrameCos, f-1) : NULL) );
    }

    // derive unrolled timeframes
    pFrames = Aig_ManStart( Aig_ManObjNumMax(pAig) * (pCex->iFrame+1) );
    pFrames->pName = Aig_UtilStrsav( pAig->pName );
    pFrames->pSpec = Aig_UtilStrsav( pAig->pSpec );
    // initialize the flops of
    Saig_ManForEachLo( pAig, pObj, i )
        pObj->pData = Aig_NotCond( Aig_ManConst1(pFrames), !Aig_InfoHasBit(pCex->pData, i) );
    // iterate through the frames
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        // construct
        vObjs = (Vec_Int_t *)Vec_VecEntry( vFrameObjs, f );
        Aig_ManForEachNodeVec( pAig, vObjs, pObj, i )
        {
            if ( Aig_ObjIsNode(pObj) )
                pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
            else if ( Aig_ObjIsPo(pObj) )
                pObj->pData = Aig_ObjChild0Copy(pObj);
            else if ( Aig_ObjIsConst1(pObj) )
                pObj->pData = Aig_ManConst1(pFrames);
            else if ( Saig_ObjIsPi(pAig, pObj) )
            {
                if ( Aig_ObjPioNum(pObj) < nInputs )
                {
                    int iBit = pCex->nRegs + f * pCex->nPis + Aig_ObjPioNum(pObj);
                    pObj->pData = Aig_NotCond( Aig_ManConst1(pFrames), !Aig_InfoHasBit(pCex->pData, iBit) );
                }
                else
                {
                    pObj->pData = Aig_ObjCreatePi( pFrames );
                    Vec_IntPush( *pvMapPiA3F, Aig_ObjPioNum(pObj) );
                    Vec_IntPush( *pvMapPiA3F, f );
                }
            }
        }
        if ( f == pCex->iFrame )
            break;
        // transfer
        vRoots = (Vec_Int_t *)Vec_VecEntry( vFrameCos, f );
        Aig_ManForEachNodeVec( pAig, vRoots, pObj, i )
            Saig_ObjLiToLo( pAig, pObj )->pData = pObj->pData;
    }
    // create output
    pObj = Aig_ManPo( pAig, pCex->iPo );
    Aig_ObjCreatePo( pFrames, Aig_Not((Aig_Obj_t *)pObj->pData) );
    // cleanup
    Vec_VecFree( vFrameCos );
    Vec_VecFree( vFrameObjs );
    // finallize
    Aig_ManCleanup( pFrames );
    // return
    return pFrames;
}

/**Function*************************************************************

  Synopsis    [Creates refinement manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Saig_RefMan_t * Saig_RefManStart( Aig_Man_t * pAig, Abc_Cex_t * pCex, int nInputs, int fVerbose )
{
    Saig_RefMan_t * p;
    p = ABC_CALLOC( Saig_RefMan_t, 1 );
    p->pAig = pAig;
    p->pCex = pCex;
    p->nInputs = nInputs;
    p->fVerbose = fVerbose;
    return p;
}

/**Function*************************************************************

  Synopsis    [Destroys refinement manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_RefManStop( Saig_RefMan_t * p )
{
    Aig_ManStopP( &p->pFrames );
    Vec_IntFreeP( &p->vMapPiA3F );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Sets phase bits in the timeframe AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_RefManSetPhases( Saig_RefMan_t * p, Abc_Cex_t * pCare, int fValue1 )
{
    Aig_Obj_t * pObj;
    int i, iFrame, iInput;
    Aig_ManConst1( p->pFrames )->fPhase = 1;
    Aig_ManForEachPi( p->pFrames, pObj, i )
    {
        iInput = Vec_IntEntry( p->vMapPiA3F, 2*i );
        iFrame = Vec_IntEntry( p->vMapPiA3F, 2*i+1 );
        pObj->fPhase = Aig_InfoHasBit( p->pCex->pData, p->pCex->nRegs + p->pCex->nPis * iFrame + iInput );
        // update value if it is a don't-care
        if ( pCare && !Aig_InfoHasBit( pCare->pData, p->pCex->nRegs + p->pCex->nPis * iFrame + iInput ) )
            pObj->fPhase = fValue1;
    }
    Aig_ManForEachNode( p->pFrames, pObj, i )
        pObj->fPhase = ( Aig_ObjFanin0(pObj)->fPhase ^ Aig_ObjFaninC0(pObj) )
                     & ( Aig_ObjFanin1(pObj)->fPhase ^ Aig_ObjFaninC1(pObj) );
    Aig_ManForEachPo( p->pFrames, pObj, i )
        pObj->fPhase = ( Aig_ObjFanin0(pObj)->fPhase ^ Aig_ObjFaninC0(pObj) );
    pObj = Aig_ManPo( p->pFrames, 0 );
    return pObj->fPhase;
}

/**Function*************************************************************

  Synopsis    [Generate the care set using SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Saig_RefManRunSat( Saig_RefMan_t * p )
{
    int nConfLimit = 1000000;
    Abc_Cex_t * pCare;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Aig_Obj_t * pObj;
    Vec_Int_t * vAssumps, * vVar2PiId;
    int i, f, iInput, iFrame, RetValue, Counter;
    int nCoreLits, * pCoreLits;
    // create CNF
    assert( Aig_ManRegNum(p->pFrames) == 0 );
    pCnf = Cnf_Derive( p->pFrames, 0 );
    RetValue = Saig_RefManSetPhases( p, NULL, 0 );
    if ( RetValue )
    {
        printf( "Constructed frames are incorrect.\n" );
        Cnf_DataFree( pCnf );
        return NULL;
    }
    Cnf_DataTranformPolarity( pCnf, 0 );
    // create SAT solver
    pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
    if ( pSat == NULL )
    {
        Cnf_DataFree( pCnf );
        return NULL;
    }
    // look for a true counter-example
    if ( p->nInputs > 0 )
    {
        RetValue = sat_solver_solve( pSat, NULL, NULL, 
            (ABC_INT64_T)nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if ( RetValue == l_False )
        {
            printf( "The problem is trivially UNSAT. The CEX is real.\n" );
            // create counter-example
            pCare = Abc_CexDup( p->pCex, p->pCex->nRegs );
            memset( pCare->pData, 0, sizeof(unsigned) * Aig_BitWordNum(pCare->nBits) );
            return pCare;
        }
        // the problem is SAT - it is expected
    }
    // create assumptions
    vVar2PiId = Vec_IntStartFull( pCnf->nVars );
    vAssumps = Vec_IntAlloc( Aig_ManPiNum(p->pFrames) );
    Aig_ManForEachPi( p->pFrames, pObj, i )
    {
        iInput = Vec_IntEntry( p->vMapPiA3F, 2*i );
        iFrame = Vec_IntEntry( p->vMapPiA3F, 2*i+1 );
//        RetValue = Aig_InfoHasBit( p->pCex->pData, p->pCex->nRegs + p->pCex->nPis * iFrame + iInput );
//        Vec_IntPush( vAssumps, toLitCond( pCnf->pVarNums[Aig_ObjId(pObj)], !RetValue ) );
        Vec_IntPush( vAssumps, toLitCond( pCnf->pVarNums[Aig_ObjId(pObj)], 1 ) );
        Vec_IntWriteEntry( vVar2PiId, pCnf->pVarNums[Aig_ObjId(pObj)], i );
    }
    // solve
    RetValue = sat_solver_solve( pSat, Vec_IntArray(vAssumps), Vec_IntArray(vAssumps) + Vec_IntSize(vAssumps), 
        (ABC_INT64_T)nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( RetValue != l_False )
    {
        if ( RetValue == l_True )
            printf( "Internal Error!!! The resulting problem is SAT.\n" );
        else
            printf( "Internal Error!!! SAT solver timed out.\n" );
        Cnf_DataFree( pCnf );
        sat_solver_delete( pSat );
        Vec_IntFree( vAssumps );
        Vec_IntFree( vVar2PiId );
        return NULL;
    }
    // get relevant SAT literals
    nCoreLits = sat_solver_final( pSat, &pCoreLits );
    assert( nCoreLits > 0 );
    if ( p->fVerbose )
    printf( "Analize final selected %d assumptions out of %d.\n", nCoreLits, Vec_IntSize(vAssumps) );
    // create counter-example
    pCare = Abc_CexDup( p->pCex, p->pCex->nRegs );
    memset( pCare->pData, 0, sizeof(unsigned) * Aig_BitWordNum(pCare->nBits) );
    // set new values
    for ( i = 0; i < nCoreLits; i++ )
    {
        int iPiNum = Vec_IntEntry( vVar2PiId, lit_var(pCoreLits[i]) );
        assert( iPiNum >= 0 && iPiNum < Aig_ManPiNum(p->pFrames) );
        iInput = Vec_IntEntry( p->vMapPiA3F, 2*iPiNum );
        iFrame = Vec_IntEntry( p->vMapPiA3F, 2*iPiNum+1 );
        Aig_InfoSetBit( pCare->pData, pCare->nRegs + pCare->nPis * iFrame + iInput );
    }

    // further reduce the CEX
    Counter = 0;
    for ( i = p->nInputs; i < Saig_ManPiNum(p->pAig); i++ )
    {
        for ( f = 0; f <= pCare->iFrame; f++ )
            if ( Aig_InfoHasBit( pCare->pData, pCare->nRegs + pCare->nPis * f + i ) )
                break;
        if ( f == pCare->iFrame + 1 )
            continue;
        Counter++;

        // try removing this input
    }
    if ( p->fVerbose )
    printf( "Essential primary inputs %d out of %d.\n", Counter, Saig_ManPiNum(p->pAig) - p->nInputs );


    // cleanup
    Cnf_DataFree( pCnf );
    sat_solver_delete( pSat );
    Vec_IntFree( vAssumps );
    Vec_IntFree( vVar2PiId );
    // verify counter-example
    RetValue = Saig_RefManSetPhases( p, pCare, 0 );
    if ( RetValue )
        printf( "Reduced CEX verification has failed.\n" );
    RetValue = Saig_RefManSetPhases( p, pCare, 1 );
    if ( RetValue )
        printf( "Reduced CEX verification has failed.\n" );

    return pCare;
} 


/**Function*************************************************************

  Synopsis    [SAT-based refinement of the counter-example.]

  Description [The first parameter (nInputs) indicates how many first 
  primary inputs to skip without considering as care candidates.]
               

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Saig_ManFindCexCareBits( Aig_Man_t * pAig, Abc_Cex_t * pCex, int nInputs, int fVerbose )
{
    Abc_Cex_t * pCare = NULL;
    int clk = clock();
    Saig_RefMan_t * p = Saig_RefManStart( pAig, pCex, nInputs, fVerbose );
    p->pFrames = Saig_ManUnrollWithCex( pAig, pCex, nInputs, &p->vMapPiA3F );
if ( p->fVerbose )
Aig_ManPrintStats( p->pFrames );

if ( p->fVerbose )
Abc_PrintTime( 1, "Frames", clock() - clk );

    clk = clock();
    pCare = Saig_RefManRunSat( p );
    Saig_RefManStop( p );

if ( p->fVerbose )
Abc_PrintTime( 1, "Filter", clock() - clk );

if ( p->fVerbose )
Abc_CexPrintStats( pCex );
if ( p->fVerbose )
Abc_CexPrintStats( pCare );
    return pCare;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

