/**CFile****************************************************************

  FileName    [bmcCexCare.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Computing care set of the counter-example.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmcCexCare.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "aig/gia/giaAig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Takes CEX and its care-set. Returns care-set of all objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Bmc_CexCareExtendToObjects( Gia_Man_t * p, Abc_Cex_t * pCex, Abc_Cex_t * pCexCare )
{
    Abc_Cex_t * pNew;
    Gia_Obj_t * pObj;
    int i, k;
    assert( pCex->nPis == pCexCare->nPis );
    assert( pCex->nRegs == pCexCare->nRegs );
    assert( pCex->nBits == pCexCare->nBits );
    // start the counter-example
    pNew = Abc_CexAlloc( pCex->nRegs, Gia_ManObjNum(p), pCex->iFrame + 1 );
    pNew->iFrame = pCex->iFrame;
    pNew->iPo    = pCex->iPo;
    // initialize terminary simulation
    Gia_ObjTerSimSet0( Gia_ManConst0(p) );
    Gia_ManForEachRi( p, pObj, k )
        Gia_ObjTerSimSet0( pObj );
    for ( i = 0; i <= pCex->iFrame; i++ )
    {
        Gia_ManForEachPi( p, pObj, k )
        {
            if ( !Abc_InfoHasBit( pCexCare->pData, pCexCare->nRegs + i * pCexCare->nPis + k ) )
                Gia_ObjTerSimSetX( pObj );
            else if ( Abc_InfoHasBit( pCex->pData, pCex->nRegs + i * pCex->nPis + k ) )
                Gia_ObjTerSimSet1( pObj );
            else
                Gia_ObjTerSimSet0( pObj );
        }
        Gia_ManForEachRo( p, pObj, k )
            Gia_ObjTerSimRo( p, pObj );
        Gia_ManForEachAnd( p, pObj, k )
            Gia_ObjTerSimAnd( pObj );
        Gia_ManForEachCo( p, pObj, k )
            Gia_ObjTerSimCo( pObj );
        // add cares to the exdended counter-example
        Gia_ManForEachObj( p, pObj, k )
            if ( !Gia_ObjTerSimGetX(pObj) )
                Abc_InfoSetBit( pNew->pData, pNew->nRegs + pNew->nPis * i + k );
    }
    pObj = Gia_ManPo( p, pCex->iPo );
    assert( Gia_ObjTerSimGet1(pObj) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Backward propagation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_CexCarePropagateFwdOne( Gia_Man_t * p, Abc_Cex_t * pCex, int f, int fGrow )
{
    Gia_Obj_t * pObj;
    int Prio, Prio0, Prio1;
    int i, Phase0, Phase1;
    if ( (fGrow & 2) )
    {
        Gia_ManForEachPi( p, pObj, i )
            pObj->Value = Abc_Var2Lit( f * pCex->nPis + (pCex->nPis-1-i) + 1, Abc_InfoHasBit(pCex->pData, pCex->nRegs + pCex->nPis * f + i) );
    }
    else
    {
        Gia_ManForEachPi( p, pObj, i )
            pObj->Value = Abc_Var2Lit( f * pCex->nPis + i + 1, Abc_InfoHasBit(pCex->pData, pCex->nRegs + pCex->nPis * f + i) );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        Prio0  = Abc_Lit2Var(Gia_ObjFanin0(pObj)->Value);
        Prio1  = Abc_Lit2Var(Gia_ObjFanin1(pObj)->Value);
        Phase0 = Abc_LitIsCompl(Gia_ObjFanin0(pObj)->Value) ^ Gia_ObjFaninC0(pObj);
        Phase1 = Abc_LitIsCompl(Gia_ObjFanin1(pObj)->Value) ^ Gia_ObjFaninC1(pObj);
        if ( Phase0 && Phase1 )
            Prio = (fGrow & 1) ? Abc_MinInt(Prio0, Prio1) : Abc_MaxInt(Prio0, Prio1);
        else if ( Phase0 && !Phase1 )
            Prio = Prio1;
        else if ( !Phase0 && Phase1 )
            Prio = Prio0;
        else // if ( !Phase0 && !Phase1 )
            Prio = (fGrow & 1) ? Abc_MaxInt(Prio0, Prio1) : Abc_MinInt(Prio0, Prio1);
        pObj->Value = Abc_Var2Lit( Prio, Phase0 & Phase1 );
    }
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Abc_LitNotCond( Gia_ObjFanin0(pObj)->Value, Gia_ObjFaninC0(pObj) );
}
void Bmc_CexCarePropagateFwd( Gia_Man_t * p, Abc_Cex_t * pCex, int fGrow, Vec_Int_t * vPrios )
{
    Gia_Obj_t * pObj, * pObjRo, * pObjRi;
    int f, i;
    Gia_ManConst0( p )->Value = 0;
    Gia_ManForEachRi( p, pObj, i )
        pObj->Value = 0;
    Vec_IntClear( vPrios );
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        Gia_ManForEachRiRo( p, pObjRi, pObjRo, i )
            Vec_IntPush( vPrios, (pObjRo->Value = pObjRi->Value) );
        Bmc_CexCarePropagateFwdOne( p, pCex, f, fGrow );
    }
}

/**Function*************************************************************

  Synopsis    [Forward propagation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_CexCarePropagateBwdOne( Gia_Man_t * p, Abc_Cex_t * pCex, int f, Abc_Cex_t * pCexMin )
{
    Gia_Obj_t * pObj;
    int i, Phase0, Phase1;
    Gia_ManForEachCand( p, pObj, i )
        pObj->fPhase = 0;
    Gia_ManForEachCo( p, pObj, i )
        if ( pObj->fPhase )
            Gia_ObjFanin0(pObj)->fPhase = 1;
    Gia_ManForEachAndReverse( p, pObj, i )
    {
        if ( !pObj->fPhase )
            continue;
        Phase0 = Abc_LitIsCompl(Gia_ObjFanin0(pObj)->Value) ^ Gia_ObjFaninC0(pObj);
        Phase1 = Abc_LitIsCompl(Gia_ObjFanin1(pObj)->Value) ^ Gia_ObjFaninC1(pObj);
        if ( Phase0 && Phase1 )
        {
            Gia_ObjFanin0(pObj)->fPhase = 1;
            Gia_ObjFanin1(pObj)->fPhase = 1;
        }
        else if ( Phase0 && !Phase1 )
            Gia_ObjFanin1(pObj)->fPhase = 1;
        else if ( !Phase0 && Phase1 )
            Gia_ObjFanin0(pObj)->fPhase = 1;
        else // if ( !Phase0 && !Phase1 )
        {
            if ( Abc_Lit2Var(Gia_ObjFanin0(pObj)->Value) <= Abc_Lit2Var(Gia_ObjFanin1(pObj)->Value) )
                Gia_ObjFanin0(pObj)->fPhase = 1;
            else
                Gia_ObjFanin1(pObj)->fPhase = 1;
        }
    }
    Gia_ManForEachPi( p, pObj, i )
        if ( pObj->fPhase )
            Abc_InfoSetBit( pCexMin->pData, pCexMin->nRegs + pCexMin->nPis * f + i );
}
Abc_Cex_t * Bmc_CexCarePropagateBwd( Gia_Man_t * p, Abc_Cex_t * pCex, Vec_Int_t * vPrios, int fGrow )
{
    Abc_Cex_t * pCexMin;
    Gia_Obj_t * pObj, * pObjRo, * pObjRi;
    int f, i;
    pCexMin = Abc_CexAlloc( pCex->nRegs, pCex->nPis, pCex->iFrame + 1 );
    pCexMin->iPo    = pCex->iPo;
    pCexMin->iFrame = pCex->iFrame;
    Gia_ManForEachCo( p, pObj, i )
        pObj->fPhase = 0;
    for ( f = pCex->iFrame; f >= 0; f-- )
    {
        Gia_ManPo(p, pCex->iPo)->fPhase = (int)(f == pCex->iFrame);
        Gia_ManForEachRo( p, pObj, i )
            pObj->Value = Vec_IntEntry( vPrios, f * pCex->nRegs + i );
        Bmc_CexCarePropagateFwdOne( p, pCex, f, fGrow );
        Bmc_CexCarePropagateBwdOne( p, pCex, f, pCexMin );
        Gia_ManForEachRiRo( p, pObjRi, pObjRo, i )
            pObjRi->fPhase = pObjRo->fPhase;
    }
    return pCexMin;
}

/**Function*************************************************************

  Synopsis    [Computes the care set of the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Bmc_CexCareMinimizeAig( Gia_Man_t * p, Abc_Cex_t * pCex, int fCheck, int fVerbose )
{
    int nTryCexes = 4; // belongs to range [1;4]
    Abc_Cex_t * pCexBest, * pCexMin[4] = {NULL};
    int k, nOnesBest, nOnesCur;
    Vec_Int_t * vPrios;
    if ( pCex->nPis != Gia_ManPiNum(p) )
    {
        printf( "Given CEX does to have same number of inputs as the AIG.\n" );
        return NULL;
    }
    if ( pCex->nRegs != Gia_ManRegNum(p) )
    {
        printf( "Given CEX does to have same number of flops as the AIG.\n" );
        return NULL;
    }
    if ( !(pCex->iPo >= 0 && pCex->iPo < Gia_ManPoNum(p)) )
    {
        printf( "Given CEX has PO whose index is out of range for the AIG.\n" );
        return NULL;
    }
    assert( pCex->nPis == Gia_ManPiNum(p) );
    assert( pCex->nRegs == Gia_ManRegNum(p) );
    assert( pCex->iPo >= 0 && pCex->iPo < Gia_ManPoNum(p) );
    if ( fVerbose )
    {
        printf( "Original :    " );
        Bmc_CexPrint( pCex, Gia_ManPiNum(p), 0 );
    }
    vPrios = Vec_IntAlloc( pCex->nRegs * (pCex->iFrame + 1) );
    for ( k = 0; k < nTryCexes; k++ )
    {
        Bmc_CexCarePropagateFwd(p, pCex, k, vPrios );
        assert( Vec_IntSize(vPrios) == pCex->nRegs * (pCex->iFrame + 1) );
        if ( !Abc_LitIsCompl(Gia_ManPo(p, pCex->iPo)->Value) )
        {
            printf( "Counter-example is invalid.\n" );
            Vec_IntFree( vPrios );
            return NULL;
        }
        pCexMin[k] = Bmc_CexCarePropagateBwd( p, pCex, vPrios, k );
        if ( fVerbose )
        {
            if ( (k & 1) )
                printf( "Decrease :    " );
            else
                printf( "Increase :    " );
            Bmc_CexPrint( pCexMin[k], Gia_ManPiNum(p), 0 );
        }
    }
    Vec_IntFree( vPrios );
    // select the best one
    pCexBest  = pCexMin[0];
    nOnesBest = Abc_CexCountOnes(pCexMin[0]);
    for ( k = 1; k < nTryCexes; k++ )
    {
        nOnesCur = Abc_CexCountOnes(pCexMin[k]);
        if ( nOnesBest > nOnesCur )
        {
            nOnesBest = nOnesCur;
            pCexBest  = pCexMin[k];
        }
    }
    for ( k = 0; k < nTryCexes; k++ )
        if ( pCexBest != pCexMin[k] )
            Abc_CexFreeP( &pCexMin[k] );
    // verify and return
    if ( fVerbose )
    {
        printf( "Final    :    " );
        Bmc_CexPrint( pCexBest, Gia_ManPiNum(p), 0 );
    }
    if ( !Bmc_CexVerify( p, pCex, pCexBest ) )
        printf( "Counter-example verification has failed.\n" );
    else if ( fCheck ) 
        printf( "Counter-example verification succeeded.\n" );
    return pCexBest;
}
Abc_Cex_t * Bmc_CexCareMinimize( Aig_Man_t * p, Abc_Cex_t * pCex, int fCheck, int fVerbose )
{
    Gia_Man_t * pGia = Gia_ManFromAigSimple( p );
    Abc_Cex_t * pCexMin = Bmc_CexCareMinimizeAig( pGia, pCex, fCheck, fVerbose );
    Gia_ManStop( pGia );
    return pCexMin;
}

/**Function*************************************************************

  Synopsis    [Verifies the care set of the counter-example.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_CexCareVerify( Aig_Man_t * p, Abc_Cex_t * pCex, Abc_Cex_t * pCexMin, int fVerbose )
{
    Gia_Man_t * pGia = Gia_ManFromAigSimple( p );
    if ( fVerbose )
    {
        printf( "Original :    " );
        Bmc_CexPrint( pCex, Gia_ManPiNum(pGia), 0 );
        printf( "Minimized:    " );
        Bmc_CexPrint( pCexMin, Gia_ManPiNum(pGia), 0 );
    }
    if ( !Bmc_CexVerify( pGia, pCex, pCexMin ) )
        printf( "Counter-example verification has failed.\n" );
    else 
        printf( "Counter-example verification succeeded.\n" );
    Gia_ManStop( pGia );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

