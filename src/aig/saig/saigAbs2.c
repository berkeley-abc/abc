/**CFile****************************************************************

  FileName    [saigAbs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Counter-example-based abstraction with constraints.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigAbs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "ssw.h"
#include "fra.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Saig_ManFindFirstFlop( Aig_Man_t * p );
extern Aig_Man_t * Saig_ManCexRefine( Aig_Man_t * p, Aig_Man_t * pAbs, Vec_Int_t * vFlops, 
    int nFrames, int nConfMaxOne, int fUseBdds, int fUseDprove, int fVerbose, int * pnUseStart, 
    int * piRetValue, int * pnFrames );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the array of constraint numbers that are violated.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManFindViolatedConstrs( Aig_Man_t * p, Abc_Cex_t * pCexAbs )
{
    Vec_Int_t * vFailed;
    Aig_Obj_t * pObj, * pObjRi, * pObjRo;
    int * pPoMap, i, k, iBit;
    pPoMap = ABC_CALLOC( int, Saig_ManPoNum(p) );
    Aig_ManCleanMarkA(p);
    Saig_ManForEachLo( p, pObj, i )
        pObj->fMarkA = 0;
    assert( pCexAbs->nBits == pCexAbs->nRegs + (pCexAbs->iFrame + 1) * pCexAbs->nPis );
    for ( i = 0; i <= pCexAbs->iFrame; i++ )
    {
        iBit = pCexAbs->nRegs + i * pCexAbs->nPis;
        Saig_ManForEachPi( p, pObj, k )
            pObj->fMarkA = Aig_InfoHasBit(pCexAbs->pData, iBit++);
        Aig_ManForEachNode( p, pObj, k )
            pObj->fMarkA = (Aig_ObjFanin0(pObj)->fMarkA ^ Aig_ObjFaninC0(pObj)) & 
                           (Aig_ObjFanin1(pObj)->fMarkA ^ Aig_ObjFaninC1(pObj));
        Aig_ManForEachPo( p, pObj, k )
            pObj->fMarkA = Aig_ObjFanin0(pObj)->fMarkA ^ Aig_ObjFaninC0(pObj);
        Saig_ManForEachPo( p, pObj, k )
            pPoMap[k] |= pObj->fMarkA;
        Saig_ManForEachLiLo( p, pObjRi, pObjRo, k )
            pObjRo->fMarkA = pObjRi->fMarkA;
    }
    Aig_ManCleanMarkA(p);
    // collect numbers of failed constraints
    vFailed = Vec_IntAlloc( Saig_ManPoNum(p) );
    Saig_ManForEachPo( p, pObj, k )
        if ( pPoMap[k] )
            Vec_IntPush( vFailed, k );
    ABC_FREE( pPoMap );
    return vFailed;
}

/**Function*************************************************************

  Synopsis    [Computes the flops to remain after abstraction.]

  Description [Updates the set of included constraints.]
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Vec_Int_t * Saig_ManConCexAbstractionFlops( Aig_Man_t * pInit, Gia_ParAbs_t * pPars, Vec_Int_t * vConstrs )
{
    int nUseStart = 0;
    Aig_Man_t * pCur, * pAbs, * pTemp;
    Vec_Int_t * vFlops, * vFlopsCopy, * vConstrsToAdd;
    int i, Entry, iFlop, Iter, clk = clock(), clk2 = clock();
    assert( Aig_ManRegNum(pInit) > 0 );
    if ( pPars->fVerbose )
        printf( "Performing counter-example-based refinement with constraints.\n" );
//    Aig_ManSetPioNumbers( p );
    // create constrained AIG
    pCur = Saig_ManDupFoldConstrs( pInit, vConstrs );
    assert( Saig_ManPoNum(pCur) == 1 );
    printf( "cur>>> " ); Aig_ManPrintStats( pCur );
    // start the flop map
    iFlop = Saig_ManFindFirstFlop( pCur );
    assert( iFlop >= 0 );
//    vFlops = Vec_IntStartNatural( 1 );
    vFlops = Vec_IntAlloc( 1 );
    Vec_IntPush( vFlops, iFlop );
    // create the abstraction
    pAbs = Saig_ManDeriveAbstraction( pCur, vFlops );
    printf( "abs>>> " ); Aig_ManPrintStats( pAbs );
    if ( !pPars->fVerbose )
    {
        printf( "Init : " );
        Aig_ManPrintStats( pAbs );
    }
    printf( "Refining abstraction...\n" );
    for ( Iter = 0; ; Iter++ )
    {
        while ( 1 )
        {
            vFlopsCopy = Vec_IntDup( vFlops );
            pTemp = Saig_ManCexRefine( pCur, pAbs, vFlops, pPars->nFramesBmc, pPars->nConfMaxBmc, pPars->fUseBdds, pPars->fUseDprove, pPars->fVerbose, pPars->fUseStart?&nUseStart:NULL, &pPars->Status, &pPars->nFramesDone );
            if ( pTemp == NULL )
            {
                Vec_IntFree( vFlopsCopy );
                break;
            }
            vConstrsToAdd = Saig_ManFindViolatedConstrs( pInit, pAbs->pSeqModel );
            if ( Vec_IntSize(vConstrsToAdd) == 0 )
            {
                Vec_IntFree( vConstrsToAdd );
                Vec_IntFree( vFlopsCopy );
                break;
            }
            // add the constraints to the base set
            Vec_IntForEachEntry( vConstrsToAdd, Entry, i )
            {
//                assert( Vec_IntFind(vConstrs, Entry) == -1 );
                Vec_IntPushUnique( vConstrs, Entry );
            }
            printf( "Adding %3d constraints.  The total is %3d (out of %3d).\n", 
                Vec_IntSize(vConstrsToAdd), Vec_IntSize(vConstrs), Saig_ManPoNum(pInit)-1 );
            Vec_IntFree( vConstrsToAdd );
            // update the current one
            Aig_ManStop( pCur );
            pCur = Saig_ManDupFoldConstrs( pInit, vConstrs );
            printf( "cur>>> " ); Aig_ManPrintStats( pCur );
            // update the flop map
            Vec_IntFree( vFlops );
            vFlops = vFlopsCopy;
//            Vec_IntFree( vFlopsCopy );
//            vFlops = vFlops;
            // update abstraction
            Aig_ManStop( pAbs );
            pAbs = Saig_ManDeriveAbstraction( pCur, vFlops );
            printf( "abs>>> " ); Aig_ManPrintStats( pAbs );
        }
        Aig_ManStop( pAbs );
        if ( pTemp == NULL )
            break;
        pAbs = pTemp;
        printf( "ITER %4d : ", Iter );
        if ( !pPars->fVerbose )
            Aig_ManPrintStats( pAbs );
        // output the intermediate result of abstraction
        Ioa_WriteAiger( pAbs, "gabs.aig", 0, 0 );
//            printf( "Intermediate abstracted model was written into file \"%s\".\n", "gabs.aig" );
        // check if the ratio is reached
        if ( 100.0*(Aig_ManRegNum(pCur)-Aig_ManRegNum(pAbs))/Aig_ManRegNum(pCur) < 1.0*pPars->nRatio )
        {
            printf( "Refinements is stopped because flop reduction is less than %d%%\n", pPars->nRatio );
            Aig_ManStop( pAbs );
            pAbs = NULL;
            Vec_IntFree( vFlops );
            vFlops = NULL;
            break;
        }
    }
    ABC_FREE( pInit->pSeqModel );
    pInit->pSeqModel = pCur->pSeqModel;
    pCur->pSeqModel = NULL;
    Aig_ManStop( pCur );
    return vFlops;
}

/**Function*************************************************************

  Synopsis    [Performs counter-example-based abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Aig_Man_t * Saig_ManConCexAbstraction( Aig_Man_t * p, Gia_ParAbs_t * pPars )
{
    Vec_Int_t * vFlops, * vConstrs;
    Aig_Man_t * pCur, * pAbs = NULL;
    assert( Saig_ManPoNum(p) > 1 ); // should contain constraint outputs
    // start included constraints
    vConstrs = Vec_IntAlloc( 100 );
    // perform refinement
    vFlops = Saig_ManConCexAbstractionFlops( p, pPars, vConstrs );
    // write the final result
    if ( vFlops )
    {
        pCur = Saig_ManDupFoldConstrs( p, vConstrs );
        pAbs = Saig_ManDeriveAbstraction( pCur, vFlops );
        Aig_ManStop( pCur );

        Ioa_WriteAiger( pAbs, "gabs.aig", 0, 0 );
        printf( "Final abstracted model was written into file \"%s\".\n", "gabs.aig" );
        Vec_IntFree( vFlops );
    }
    Vec_IntFree( vConstrs );
    return pAbs;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

