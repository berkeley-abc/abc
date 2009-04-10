/**CFile****************************************************************

  FileName    [cecChoice.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Computation of structural choices.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecChoice.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"
#include "giaAig.h"
#include "dch.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Cec_ManCombSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj );

extern int Cec_ManResimulateCounterExamplesComb( Cec_ManSim_t * pSim, Vec_Int_t * vCexStore );
extern int Gia_ManCheckRefinements( Gia_Man_t * p, Vec_Str_t * vStatus, Vec_Int_t * vOutputs, Cec_ManSim_t * pSim, int fRings );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the real value of the literal w/o spec reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cec_ManCombSpecReal( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    assert( Gia_ObjIsAnd(pObj) );
    Cec_ManCombSpecReduce_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Cec_ManCombSpecReduce_rec( pNew, p, Gia_ObjFanin1(pObj) );
    return Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Recursively performs speculative reduction for the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCombSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Gia_Obj_t * pRepr;
    if ( ~pObj->Value )
        return;
    if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
    {
        Cec_ManCombSpecReduce_rec( pNew, p, pRepr );
        pObj->Value = Gia_LitNotCond( pRepr->Value, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
        return;
    }
    pObj->Value = Cec_ManCombSpecReal( pNew, p, pObj );
}

/**Function*************************************************************

  Synopsis    [Derives SRM for signal correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManCombSpecReduce( Gia_Man_t * p, Vec_Int_t ** pvOutputs, int fRings )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits;
    int i, iPrev, iObj, iPrevNew, iObjNew;
    assert( p->pReprs != NULL );
    Gia_ManSetPhase( p );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Gia_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    *pvOutputs = Vec_IntAlloc( 1000 );
    vXorLits = Vec_IntAlloc( 1000 );
    if ( fRings )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsConst( p, i ) )
            {
                iObjNew = Cec_ManCombSpecReal( pNew, p, pObj );
                iObjNew = Gia_LitNotCond( iObjNew, Gia_ObjPhase(pObj) );
                if ( iObjNew != 0 )
                {
                    Vec_IntPush( *pvOutputs, 0 );
                    Vec_IntPush( *pvOutputs, i );
                    Vec_IntPush( vXorLits, iObjNew );
                }
            }
            else if ( Gia_ObjIsHead( p, i ) )
            {
                iPrev = i;
                Gia_ClassForEachObj1( p, i, iObj )
                {
                    iPrevNew = Cec_ManCombSpecReal( pNew, p, Gia_ManObj(p, iPrev) );
                    iObjNew  = Cec_ManCombSpecReal( pNew, p, Gia_ManObj(p, iObj) );
                    iPrevNew = Gia_LitNotCond( iPrevNew, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                    iObjNew  = Gia_LitNotCond( iObjNew,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
                    if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                    {
                        Vec_IntPush( *pvOutputs, iPrev );
                        Vec_IntPush( *pvOutputs, iObj );
                        Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Gia_LitNot(iObjNew)) );
                    }
                    iPrev = iObj;
                }
                iObj = i;
                iPrevNew = Cec_ManCombSpecReal( pNew, p, Gia_ManObj(p, iPrev) );
                iObjNew  = Cec_ManCombSpecReal( pNew, p, Gia_ManObj(p, iObj) );
                iPrevNew = Gia_LitNotCond( iPrevNew, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                iObjNew  = Gia_LitNotCond( iObjNew,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
                if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                {
                    Vec_IntPush( *pvOutputs, iPrev );
                    Vec_IntPush( *pvOutputs, iObj );
                    Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Gia_LitNot(iObjNew)) );
                }
            }
        }
    }
    else
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
            if ( pRepr == NULL )
                continue;
            iPrevNew = Gia_ObjIsConst(p, i)? 0 : Cec_ManCombSpecReal( pNew, p, pRepr );
            iObjNew  = Cec_ManCombSpecReal( pNew, p, pObj );
            iObjNew  = Gia_LitNotCond( iObjNew, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pObj) );
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
            }
        }
    }
    Vec_IntForEachEntry( vXorLits, iObjNew, i )
        Gia_ManAppendCo( pNew, iObjNew );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
//printf( "Before sweeping = %d\n", Gia_ManAndNum(pNew) );
    pNew = Gia_ManCleanup( pTemp = pNew );
//printf( "After sweeping = %d\n", Gia_ManAndNum(pNew) );
    Gia_ManStop( pTemp );
    return pNew;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManChoiceComputation_int( Gia_Man_t * pAig, Cec_ParChc_t * pPars )
{
    int nItersMax = 1000;
    Vec_Str_t * vStatus;
    Vec_Int_t * vOutputs;
    Vec_Int_t * vCexStore;
    Cec_ParSim_t ParsSim, * pParsSim = &ParsSim;
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Cec_ManSim_t * pSim;
    Gia_Man_t * pSrm;
    int r, RetValue;
    int clkSat = 0, clkSim = 0, clkSrm = 0, clkTotal = clock();
    int clk2, clk = clock();
    ABC_FREE( pAig->pReprs );
    ABC_FREE( pAig->pNexts );
    Gia_ManRandom( 1 );
    // prepare simulation manager
    Cec_ManSimSetDefaultParams( pParsSim );
    pParsSim->nWords     = pPars->nWords;
    pParsSim->nRounds    = pPars->nRounds;
    pParsSim->fVerbose   = pPars->fVerbose;
    pParsSim->fLatchCorr   = 0;
    pParsSim->fSeqSimulate = 0;
    // create equivalence classes of registers
    pSim = Cec_ManSimStart( pAig, pParsSim );
    Cec_ManSimClassesPrepare( pSim );
    Cec_ManSimClassesRefine( pSim );
    // prepare SAT solving
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->nBTLimit = pPars->nBTLimit;
    pParsSat->fVerbose = pPars->fVerbose;
    if ( pPars->fVerbose )
    {
        printf( "Obj = %7d. And = %7d. Conf = %5d. Ring = %d. CSat = %d.\n",
            Gia_ManObjNum(pAig), Gia_ManAndNum(pAig), pPars->nBTLimit, pPars->fUseRings, pPars->fUseCSat );
        Cec_ManRefinedClassPrintStats( pAig, NULL, 0, clock() - clk );
    }
    // perform refinement of equivalence classes
    for ( r = 0; r < nItersMax; r++ )
    { 
        clk = clock();
        // perform speculative reduction
        clk2 = clock();
        pSrm = Cec_ManCombSpecReduce( pAig, &vOutputs, pPars->fUseRings );
        assert( Gia_ManRegNum(pSrm) == 0 && Gia_ManCiNum(pSrm) == Gia_ManCiNum(pAig) );
        clkSrm += clock() - clk2;
        if ( Gia_ManCoNum(pSrm) == 0 )
        {
            if ( pPars->fVerbose )
                Cec_ManRefinedClassPrintStats( pAig, NULL, r+1, clock() - clk );
            Vec_IntFree( vOutputs );
            Gia_ManStop( pSrm );            
            break;
        }
//Gia_DumpAiger( pSrm, "choicesrm", r, 2 );
        // found counter-examples to speculation
        clk2 = clock();
        if ( pPars->fUseCSat )
            vCexStore = Cbs_ManSolveMiterNc( pSrm, pPars->nBTLimit, &vStatus, 0 );
        else
            vCexStore = Cec_ManSatSolveMiter( pSrm, pParsSat, &vStatus );
        Gia_ManStop( pSrm );
        clkSat += clock() - clk2;
        if ( Vec_IntSize(vCexStore) == 0 )
        {
            if ( pPars->fVerbose )
                Cec_ManRefinedClassPrintStats( pAig, vStatus, r+1, clock() - clk );
            Vec_IntFree( vCexStore );
            Vec_StrFree( vStatus );
            Vec_IntFree( vOutputs );
            break;
        }
        // refine classes with these counter-examples
        clk2 = clock();
        RetValue = Cec_ManResimulateCounterExamplesComb( pSim, vCexStore );
        Vec_IntFree( vCexStore );
        clkSim += clock() - clk2;
        Gia_ManCheckRefinements( pAig, vStatus, vOutputs, pSim, pPars->fUseRings );
        if ( pPars->fVerbose )
            Cec_ManRefinedClassPrintStats( pAig, vStatus, r+1, clock() - clk );
        Vec_StrFree( vStatus );
        Vec_IntFree( vOutputs );
//Gia_ManEquivPrintClasses( pAig, 1, 0 );
    }
    // check the overflow
    if ( r == nItersMax )
        printf( "The refinement was not finished. The result may be incorrect.\n" );
    Cec_ManSimStop( pSim );
    clkTotal = clock() - clkTotal;
    // report the results
    if ( pPars->fVerbose )
    {
        ABC_PRTP( "Srm  ", clkSrm,                        clkTotal );
        ABC_PRTP( "Sat  ", clkSat,                        clkTotal );
        ABC_PRTP( "Sim  ", clkSim,                        clkTotal );
        ABC_PRTP( "Other", clkTotal-clkSat-clkSrm-clkSim, clkTotal );
        ABC_PRT( "TOTAL",  clkTotal );
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManChoiceMiter_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return pObj->Value;
    Gia_ManChoiceMiter_rec( pNew, p, Gia_ObjFanin0(pObj) );
    if ( Gia_ObjIsCo(pObj) )
        return pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManChoiceMiter_rec( pNew, p, Gia_ObjFanin1(pObj) );
    return pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
} 

/**Function*************************************************************

  Synopsis    [Derives the miter of several AIGs for choice computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManChoiceMiter( Vec_Ptr_t * vGias )
{
    Gia_Man_t * pNew, * pGia, * pGia0;
    int i, k, iNode, nNodes;
    // make sure they have equal parameters
    assert( Vec_PtrSize(vGias) > 0 );
    pGia0 = Vec_PtrEntry( vGias, 0 );
    Vec_PtrForEachEntry( vGias, pGia, i )
    {
        assert( Gia_ManCiNum(pGia)  == Gia_ManCiNum(pGia0) );
        assert( Gia_ManCoNum(pGia)  == Gia_ManCoNum(pGia0) );
        assert( Gia_ManRegNum(pGia) == Gia_ManRegNum(pGia0) );
        Gia_ManFillValue( pGia );
        Gia_ManConst0(pGia)->Value = 0;
    }
    // start the new manager
    pNew = Gia_ManStart( Vec_PtrSize(vGias) * Gia_ManObjNum(pGia0) );
    pNew->pName = Gia_UtilStrsav( pGia0->pName );
    // create new CIs and assign them to the old manager CIs
    for ( k = 0; k < Gia_ManCiNum(pGia0); k++ )
    {
        iNode = Gia_ManAppendCi(pNew);
        Vec_PtrForEachEntry( vGias, pGia, i )
            Gia_ManCi( pGia, k )->Value = iNode; 
    }
    // create internal nodes
    Gia_ManHashAlloc( pNew );
    for ( k = 0; k < Gia_ManCoNum(pGia0); k++ )
    {
        Vec_PtrForEachEntry( vGias, pGia, i )
            Gia_ManChoiceMiter_rec( pNew, pGia, Gia_ManCo( pGia, k ) );
    }
    Gia_ManHashStop( pNew );
    // check the presence of dangling nodes
    nNodes = Gia_ManHasDandling( pNew );
    assert( nNodes == 0 );
    // finalize
//    Gia_ManSetRegNum( pNew, Gia_ManRegNum(pGia0) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Computes choices for the vector of AIGs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManChoiceComputationVec( Vec_Ptr_t * vGias, Cec_ParChc_t * pPars )
{
    Gia_Man_t * pMiter, * pNew;
    int RetValue;
    // compute equivalences of the miter
    pMiter = Gia_ManChoiceMiter( vGias );
    RetValue = Cec_ManChoiceComputation_int( pMiter, pPars );
    // derive AIG with choices
    pNew = Gia_ManEquivToChoices( pMiter, Vec_PtrSize(vGias) );
    Gia_ManHasChoices( pNew );
    Gia_ManStop( pMiter );
    // report the results
    if ( pPars->fVerbose )
    {
//        printf( "NBeg = %d. NEnd = %d. (Gain = %6.2f %%).  RBeg = %d. REnd = %d. (Gain = %6.2f %%).\n", 
//            Gia_ManAndNum(pAig), Gia_ManAndNum(pNew), 
//            100.0*(Gia_ManAndNum(pAig)-Gia_ManAndNum(pNew))/(Gia_ManAndNum(pAig)?Gia_ManAndNum(pAig):1), 
//            Gia_ManRegNum(pAig), Gia_ManRegNum(pNew), 
//            100.0*(Gia_ManRegNum(pAig)-Gia_ManRegNum(pNew))/(Gia_ManRegNum(pAig)?Gia_ManRegNum(pAig):1) );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Computes choices for one AIGs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManChoiceComputation( Gia_Man_t * pAig, Cec_ParChc_t * pParsChc )
{
    extern Aig_Man_t * Dar_ManChoiceNew( Aig_Man_t * pAig, Dch_Pars_t * pPars );
    Dch_Pars_t Pars, * pPars = &Pars;
    Aig_Man_t * pMan, * pManNew;
    Gia_Man_t * pGia;
    if ( 0 ) 
    {
        Vec_Ptr_t * vGias;
        vGias = Vec_PtrAlloc( 1 );
        Vec_PtrPush( vGias, pAig );
        pGia = Cec_ManChoiceComputationVec( vGias, pParsChc );
        Vec_PtrFree( vGias );
    }
    else
    {
        pMan = Gia_ManToAig( pAig, 0 );
        Dch_ManSetDefaultParams( pPars );
        pPars->fUseGia  = 1;
        pPars->nBTLimit = pParsChc->nBTLimit;
        pPars->fUseCSat = pParsChc->fUseCSat;
        pPars->fVerbose = pParsChc->fVerbose;
        pManNew = Dar_ManChoiceNew( pMan, pPars );
        pGia = Gia_ManFromAig( pManNew );
        Aig_ManStop( pManNew );
        Aig_ManStop( pMan );
    }
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Performs computation of AIGs with choices.]

  Description [Takes several AIGs and performs choicing.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cec_ComputeChoices( Vec_Ptr_t * vAigs, Dch_Pars_t * pPars )
{
    Cec_ParChc_t ParsChc, * pParsChc = &ParsChc;
    Vec_Ptr_t * vGias;
    Gia_Man_t * pGia;
    Aig_Man_t * pAig;
    int i;
    if ( pPars->fVerbose )
        ABC_PRT( "Synthesis time", pPars->timeSynth );
    Cec_ManChcSetDefaultParams( pParsChc );
    pParsChc->nBTLimit = pPars->nBTLimit;
    pParsChc->fUseCSat = pPars->fUseCSat;
    if ( pParsChc->fUseCSat && pParsChc->nBTLimit > 100 )
        pParsChc->nBTLimit = 100;
    pParsChc->fVerbose = pPars->fVerbose;
    vGias = Vec_PtrAlloc( 10 );
    Vec_PtrForEachEntry( vAigs, pAig, i )
        Vec_PtrPush( vGias, Gia_ManFromAig(pAig) );
    pGia = Cec_ManChoiceComputationVec( vGias, pParsChc );
    Gia_ManSetRegNum( pGia, Gia_ManRegNum(Vec_PtrEntry(vGias, 0)) );
    Vec_PtrForEachEntry( vGias, pAig, i )
        Gia_ManStop( (Gia_Man_t *)pAig );
    Vec_PtrFree( vGias );
    pAig = Gia_ManToAig( pGia, 1 );
    Gia_ManStop( pGia );
    return pAig;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


