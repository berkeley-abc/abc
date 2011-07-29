/**CFile****************************************************************

  FileName    [saigAbsCba.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [CEX-based abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigAbsCba.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "giaAig.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// local manager
typedef struct Saig_ManCba_t_ Saig_ManCba_t;
struct Saig_ManCba_t_
{
    // user data
    Aig_Man_t * pAig;       // user's AIG
    Abc_Cex_t * pCex;       // user's CEX
    int         nInputs;    // the number of first inputs to skip
    int         fVerbose;   // verbose flag
    // unrolling
    Aig_Man_t * pFrames;    // unrolled timeframes
    Vec_Int_t * vMapPiF2A;  // mapping of frame PIs into real PIs
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Maps array of frame PI IDs into array of additional PI IDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManCbaReason2Inputs( Saig_ManCba_t * p, Vec_Int_t * vReasons )
{
    Vec_Int_t * vOriginal, * vVisited;
    int i, Entry;
    vOriginal = Vec_IntAlloc( Saig_ManPiNum(p->pAig) ); 
    vVisited = Vec_IntStart( Saig_ManPiNum(p->pAig) );
    Vec_IntForEachEntry( vReasons, Entry, i )
    {
        int iInput = Vec_IntEntry( p->vMapPiF2A, 2*Entry );
        assert( iInput >= p->nInputs && iInput < Aig_ManPiNum(p->pAig) );
        if ( Vec_IntEntry(vVisited, iInput) == 0 )
            Vec_IntPush( vOriginal, iInput - p->nInputs );
        Vec_IntAddToEntry( vVisited, iInput, 1 );
    }
    Vec_IntFree( vVisited );
    return vOriginal;
}

/**Function*************************************************************

  Synopsis    [Creates the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Saig_ManCbaReason2Cex( Saig_ManCba_t * p, Vec_Int_t * vReasons )
{
    Abc_Cex_t * pCare;
    int i, Entry, iInput, iFrame;
    pCare = Abc_CexDup( p->pCex, p->pCex->nRegs );
    memset( pCare->pData, 0, sizeof(unsigned) * Aig_BitWordNum(pCare->nBits) );
    Vec_IntForEachEntry( vReasons, Entry, i )
    {
        assert( Entry >= 0 && Entry < Aig_ManPiNum(p->pFrames) );
        iInput = Vec_IntEntry( p->vMapPiF2A, 2*Entry );
        iFrame = Vec_IntEntry( p->vMapPiF2A, 2*Entry+1 );
        Aig_InfoSetBit( pCare->pData, pCare->nRegs + pCare->nPis * iFrame + iInput );
    }
    return pCare;
}

/**Function*************************************************************

  Synopsis    [Returns reasons for the property to fail.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManCbaFindReason_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Int_t * vPrios, Vec_Int_t * vReasons )
{
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    if ( Aig_ObjIsPi(pObj) )
    {
        Vec_IntPush( vReasons, Aig_ObjPioNum(pObj) );
        return;
    }
    assert( Aig_ObjIsNode(pObj) );
    if ( pObj->fPhase )
    {
        Saig_ManCbaFindReason_rec( p, Aig_ObjFanin0(pObj), vPrios, vReasons );
        Saig_ManCbaFindReason_rec( p, Aig_ObjFanin1(pObj), vPrios, vReasons );
    }
    else
    {
        int fPhase0 = Aig_ObjFaninC0(pObj) ^ Aig_ObjFanin0(pObj)->fPhase;
        int fPhase1 = Aig_ObjFaninC1(pObj) ^ Aig_ObjFanin1(pObj)->fPhase;
        assert( !fPhase0 || !fPhase1 );
        if ( !fPhase0 && fPhase1 )
            Saig_ManCbaFindReason_rec( p, Aig_ObjFanin0(pObj), vPrios, vReasons );
        else if ( fPhase0 && !fPhase1 )
            Saig_ManCbaFindReason_rec( p, Aig_ObjFanin1(pObj), vPrios, vReasons );
        else 
        {
            int iPrio0 = Vec_IntEntry( vPrios, Aig_ObjFaninId0(pObj) );
            int iPrio1 = Vec_IntEntry( vPrios, Aig_ObjFaninId1(pObj) );
            if ( iPrio0 <= iPrio1 )
                Saig_ManCbaFindReason_rec( p, Aig_ObjFanin0(pObj), vPrios, vReasons );
            else
                Saig_ManCbaFindReason_rec( p, Aig_ObjFanin1(pObj), vPrios, vReasons );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Returns reasons for the property to fail.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManCbaFindReason( Saig_ManCba_t * p )
{
    Aig_Obj_t * pObj;
    Vec_Int_t * vPrios, * vPi2Prio, * vReasons;
    int i, CountPrios;

    vPi2Prio = Vec_IntStartFull( Saig_ManPiNum(p->pAig) );
    vPrios   = Vec_IntStartFull( Aig_ManObjNumMax(p->pFrames) );

    // set PI values according to CEX
    CountPrios = 0;
    Aig_ManConst1(p->pFrames)->fPhase = 1;
    Aig_ManForEachPi( p->pFrames, pObj, i )
    {
        int iInput = Vec_IntEntry( p->vMapPiF2A, 2*i );
        int iFrame = Vec_IntEntry( p->vMapPiF2A, 2*i+1 );
        pObj->fPhase = Aig_InfoHasBit( p->pCex->pData, p->pCex->nRegs + p->pCex->nPis * iFrame + iInput );
        // assign priority
        if ( Vec_IntEntry(vPi2Prio, iInput) == ~0 )
            Vec_IntWriteEntry( vPi2Prio, iInput, CountPrios++ );
//        Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), Vec_IntEntry(vPi2Prio, iInput) );
        Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), i );
    }
//    printf( "Priority numbers = %d.\n", CountPrios );
    Vec_IntFree( vPi2Prio );

    // traverse and set the priority
    Aig_ManForEachNode( p->pFrames, pObj, i )
    {
        int fPhase0 = Aig_ObjFaninC0(pObj) ^ Aig_ObjFanin0(pObj)->fPhase;
        int fPhase1 = Aig_ObjFaninC1(pObj) ^ Aig_ObjFanin1(pObj)->fPhase;
        int iPrio0  = Vec_IntEntry( vPrios, Aig_ObjFaninId0(pObj) );
        int iPrio1  = Vec_IntEntry( vPrios, Aig_ObjFaninId1(pObj) );
        pObj->fPhase = fPhase0 && fPhase1;
        if ( fPhase0 && fPhase1 ) // both are one
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), Abc_MaxInt(iPrio0, iPrio1) );
        else if ( !fPhase0 && fPhase1 ) 
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), iPrio0 );
        else if ( fPhase0 && !fPhase1 )
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), iPrio1 );
        else // both are zero
            Vec_IntWriteEntry( vPrios, Aig_ObjId(pObj), Abc_MinInt(iPrio0, iPrio1) );
    }
    // check the property output
    pObj = Aig_ManPo( p->pFrames, 0 );
    assert( (int)Aig_ObjFanin0(pObj)->fPhase == Aig_ObjFaninC0(pObj) );

    // select the reason
    vReasons = Vec_IntAlloc( 100 );
    Aig_ManIncrementTravId( p->pFrames );
    Saig_ManCbaFindReason_rec( p->pFrames, Aig_ObjFanin0(pObj), vPrios, vReasons );
    Vec_IntFree( vPrios );
    return vReasons;
}


/**Function*************************************************************

  Synopsis    [Collect nodes in the unrolled timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManCbaUnrollCollect_rec( Aig_Man_t * pAig, Aig_Obj_t * pObj, Vec_Int_t * vObjs, Vec_Int_t * vRoots )
{
    if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(pAig, pObj);
    if ( Aig_ObjIsPo(pObj) )
        Saig_ManCbaUnrollCollect_rec( pAig, Aig_ObjFanin0(pObj), vObjs, vRoots );
    else if ( Aig_ObjIsNode(pObj) )
    {
        Saig_ManCbaUnrollCollect_rec( pAig, Aig_ObjFanin0(pObj), vObjs, vRoots );
        Saig_ManCbaUnrollCollect_rec( pAig, Aig_ObjFanin1(pObj), vObjs, vRoots );
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
Aig_Man_t * Saig_ManCbaUnrollWithCex( Aig_Man_t * pAig, Abc_Cex_t * pCex, int nInputs, Vec_Int_t ** pvMapPiF2A )
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
    *pvMapPiF2A = Vec_IntAlloc( 1000 );

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
            Saig_ManCbaUnrollCollect_rec( pAig, pObj, 
                (Vec_Int_t *)Vec_VecEntry(vFrameObjs, f),
                (Vec_Int_t *)(f ? Vec_VecEntry(vFrameCos, f-1) : NULL) );
    }

    // derive unrolled timeframes
    pFrames = Aig_ManStart( 10000 );
    pFrames->pName = Aig_UtilStrsav( pAig->pName );
    pFrames->pSpec = Aig_UtilStrsav( pAig->pSpec );
    // initialize the flops 
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
                    Vec_IntPush( *pvMapPiF2A, Aig_ObjPioNum(pObj) );
                    Vec_IntPush( *pvMapPiF2A, f );
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
    Aig_ManSetRegNum( pFrames, 0 );
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
Saig_ManCba_t * Saig_ManCbaStart( Aig_Man_t * pAig, Abc_Cex_t * pCex, int nInputs, int fVerbose )
{
    Saig_ManCba_t * p;
    p = ABC_CALLOC( Saig_ManCba_t, 1 );
    p->pAig = pAig;
    p->pCex = pCex;
    p->nInputs = nInputs;
    p->fVerbose = fVerbose;
    p->pFrames = Saig_ManCbaUnrollWithCex( pAig, pCex, nInputs, &p->vMapPiF2A );
    return p;
}

/**Function*************************************************************

  Synopsis    [Destroys refinement manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManCbaStop( Saig_ManCba_t * p )
{
    Aig_ManStopP( &p->pFrames );
    Vec_IntFreeP( &p->vMapPiF2A );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [SAT-based refinement of the counter-example.]

  Description [The first parameter (nInputs) indicates how many first 
  primary inputs to skip without considering as care candidates.]
               

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Saig_ManCbaFindCexCareBits( Aig_Man_t * pAig, Abc_Cex_t * pCex, int nInputs, int fNewOrder, int fVerbose )
{
    Saig_ManCba_t * p;
    Vec_Int_t * vReasons;
    Abc_Cex_t * pCare;
    int clk = clock();

    clk = clock();
    p = Saig_ManCbaStart( pAig, pCex, nInputs, fVerbose );
    vReasons = Saig_ManCbaFindReason( p );

if ( fVerbose )
Aig_ManPrintStats( p->pFrames );

    if ( fVerbose )
    {
        Vec_Int_t * vRes = Saig_ManCbaReason2Inputs( p, vReasons );
        printf( "Frame PIs = %4d (essential = %4d)   AIG PIs = %4d (essential = %4d)   ",
            Aig_ManPiNum(p->pFrames), Vec_IntSize(vReasons), 
            Saig_ManPiNum(p->pAig) - p->nInputs, Vec_IntSize(vRes) );
        Vec_IntFree( vRes );
ABC_PRT( "Time", clock() - clk );
    }

    pCare = Saig_ManCbaReason2Cex( p, vReasons );
    Vec_IntFree( vReasons );
    Saig_ManCbaStop( p );

if ( fVerbose )
Abc_CexPrintStats( pCex );
if ( fVerbose )
Abc_CexPrintStats( pCare );

    return pCare;
}

/**Function*************************************************************

  Synopsis    [Returns the array of PIs for flops that should not be absracted.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManCbaFilterInputs( Aig_Man_t * pAig, int iFirstFlopPi, Abc_Cex_t * pCex, int fVerbose )
{
    Saig_ManCba_t * p;
    Vec_Int_t * vRes, * vReasons;
    int clk;
    if ( Saig_ManPiNum(pAig) != pCex->nPis )
    {
        printf( "Saig_ManCbaFilterInputs(): The PI count of AIG (%d) does not match that of cex (%d).\n", 
            Aig_ManPiNum(pAig), pCex->nPis );
        return NULL;
    }

clk = clock();
    p = Saig_ManCbaStart( pAig, pCex, iFirstFlopPi, fVerbose );
    vReasons = Saig_ManCbaFindReason( p );
    vRes = Saig_ManCbaReason2Inputs( p, vReasons );
    if ( fVerbose )
    {
        printf( "Frame PIs = %4d (essential = %4d)   AIG PIs = %4d (essential = %4d)   ",
            Aig_ManPiNum(p->pFrames), Vec_IntSize(vReasons), 
            Saig_ManPiNum(p->pAig) - p->nInputs, Vec_IntSize(vRes) );
ABC_PRT( "Time", clock() - clk );
    }

    Vec_IntFree( vReasons );
    Saig_ManCbaStop( p );
    return vRes;
}




/**Function*************************************************************

  Synopsis    [Checks the abstracted model for a counter-example.]

  Description [Returns the array of abstracted flops that should be added
  to the abstraction.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManCbaPerform( Aig_Man_t * pAbs, int nInputs, Saig_ParBmc_t * pPars )
{    
    Vec_Int_t * vAbsFfsToAdd;
    int RetValue, clk = clock();
    assert( pAbs->nRegs > 0 );
    // perform BMC
    RetValue = Saig_ManBmcScalable( pAbs, pPars );
    if ( RetValue == -1 ) // time out - nothing to add
    {
        assert( pAbs->pSeqModel == NULL );
        return Vec_IntAlloc( 0 );
    }
    // CEX is detected - refine the flops
    vAbsFfsToAdd = Saig_ManCbaFilterInputs( pAbs, nInputs, pAbs->pSeqModel, pPars->fVerbose );
    if ( Vec_IntSize(vAbsFfsToAdd) == 0 )
    {
        Vec_IntFree( vAbsFfsToAdd );
        return NULL;
    }
    if ( pPars->fVerbose )
    {
        printf( "Adding %d registers to the abstraction.  ", Vec_IntSize(vAbsFfsToAdd) );
        Abc_PrintTime( 0, "Time", clock() - clk );
    }
    return vAbsFfsToAdd;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

