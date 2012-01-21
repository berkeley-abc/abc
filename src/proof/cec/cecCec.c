/**CFile****************************************************************

  FileName    [cecCec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Integrated combinatinal equivalence checker.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecCec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"
#include "src/proof/fra/fra.h"
#include "src/aig/gia/giaAig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Saves the input pattern with the given number.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManTransformPattern( Gia_Man_t * p, int iOut, int * pValues )
{
    int i;
    assert( p->pCexComb == NULL );
    p->pCexComb = (Abc_Cex_t *)ABC_CALLOC( char, 
        sizeof(Abc_Cex_t) + sizeof(unsigned) * Abc_BitWordNum(Gia_ManCiNum(p)) );
    p->pCexComb->iPo = iOut;
    p->pCexComb->nPis = Gia_ManCiNum(p);
    p->pCexComb->nBits = Gia_ManCiNum(p);
    for ( i = 0; i < Gia_ManCiNum(p); i++ )
        if ( pValues[i] )
            Abc_InfoSetBit( p->pCexComb->pData, i );
}

/**Function*************************************************************

  Synopsis    [Interface to the old CEC engine]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManVerifyOld( Gia_Man_t * pMiter, int fVerbose, int * piOutFail )
{
//    extern int Fra_FraigCec( Aig_Man_t ** ppAig, int nConfLimit, int fVerbose );
    extern int Ssw_SecCexResimulate( Aig_Man_t * p, int * pModel, int * pnOutputs );
    Gia_Man_t * pTemp = Gia_ManTransformMiter( pMiter );
    Aig_Man_t * pMiterCec = Gia_ManToAig( pTemp, 0 );
    int RetValue, iOut, nOuts, clkTotal = clock();
    if ( piOutFail )
        *piOutFail = -1;
    Gia_ManStop( pTemp );
    // run CEC on this miter
    RetValue = Fra_FraigCec( &pMiterCec, 10000000, fVerbose );
    // report the miter
    if ( RetValue == 1 )
    {
        Abc_Print( 1, "Networks are equivalent.   " );
Abc_PrintTime( 1, "Time", clock() - clkTotal );
    }
    else if ( RetValue == 0 )
    {
        Abc_Print( 1, "Networks are NOT EQUIVALENT.   " );
Abc_PrintTime( 1, "Time", clock() - clkTotal );
        if ( pMiterCec->pData == NULL )
            Abc_Print( 1, "Counter-example is not available.\n" );
        else
        {
            iOut = Ssw_SecCexResimulate( pMiterCec, (int *)pMiterCec->pData, &nOuts );
            if ( iOut == -1 )
                Abc_Print( 1, "Counter-example verification has failed.\n" );
            else 
            {
//                Aig_Obj_t * pObj = Aig_ManPo(pMiterCec, iOut);
//                Aig_Obj_t * pFan = Aig_ObjFanin0(pObj);
                Abc_Print( 1, "Primary output %d has failed", iOut );
                if ( nOuts-1 >= 0 )
                    Abc_Print( 1, ", along with other %d incorrect outputs", nOuts-1 );
                Abc_Print( 1, ".\n" );
                if ( piOutFail )
                    *piOutFail = iOut;
            }
            Cec_ManTransformPattern( pMiter, iOut, (int *)pMiterCec->pData );
        }
    }
    else
    {
        Abc_Print( 1, "Networks are UNDECIDED.   " );
Abc_PrintTime( 1, "Time", clock() - clkTotal );
    }
    fflush( stdout );
    Aig_ManStop( pMiterCec );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [New CEC engine.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManVerify( Gia_Man_t * pInit, Cec_ParCec_t * pPars )
{
    int fDumpUndecided = 0;
    Cec_ParFra_t ParsFra, * pParsFra = &ParsFra;
    Gia_Man_t * p, * pNew;
    int RetValue, clk = clock();
    double clkTotal = clock();
    // preprocess 
    p = Gia_ManDup( pInit );
    Gia_ManEquivFixOutputPairs( p );
    p = Gia_ManCleanup( pNew = p );
    Gia_ManStop( pNew );
    // sweep for equivalences
    Cec_ManFraSetDefaultParams( pParsFra );
    pParsFra->nItersMax    = 1000;
    pParsFra->nBTLimit     = pPars->nBTLimit;
    pParsFra->TimeLimit    = pPars->TimeLimit;
    pParsFra->fVerbose     = pPars->fVerbose;
    pParsFra->fCheckMiter  = 1;
    pParsFra->fDualOut     = 1;
    pNew = Cec_ManSatSweeping( p, pParsFra );
    pPars->iOutFail = pParsFra->iOutFail;
    // update
    pInit->pCexComb = p->pCexComb; p->pCexComb = NULL;
    Gia_ManStop( p );
    p = pInit;
    // continue
    if ( pNew == NULL )
    {
        if ( p->pCexComb != NULL )
        {
            if ( p->pCexComb && !Gia_ManVerifyCex( p, p->pCexComb, 1 ) )
                Abc_Print( 1, "Counter-example simulation has failed.\n" );
            Abc_Print( 1, "Networks are NOT EQUIVALENT.  " );
            Abc_PrintTime( 1, "Time", clock() - clk );
            return 0;
        }
        p = Gia_ManDup( pInit );
        Gia_ManEquivFixOutputPairs( p );
        p = Gia_ManCleanup( pNew = p );
        Gia_ManStop( pNew );
        pNew = p;
    }
    if ( Gia_ManAndNum(pNew) == 0 )
    {
        Gia_Obj_t * pObj1, * pObj2;
        int i;
        Gia_ManForEachPo( pNew, pObj1, i )
        {
            pObj2 = Gia_ManPo( pNew, ++i );
            if ( Gia_ObjChild0(pObj1) != Gia_ObjChild0(pObj2) )
            {
                Abc_Print( 1, "Networks are NOT EQUIVALENT. Outputs %d trivially differ.  ", i/2 );
                Abc_PrintTime( 1, "Time", clock() - clk );
                Gia_ManStop( pNew );
                pPars->iOutFail = i/2;
                return 0;
            }
        }
        Abc_Print( 1, "Networks are equivalent.  " );
        Abc_PrintTime( 1, "Time", clock() - clk );
        Gia_ManStop( pNew );
        return 1;
    }
    if ( pPars->fVerbose )
    {
    Abc_Print( 1, "Networks are UNDECIDED after the new CEC engine.  " );
    Abc_PrintTime( 1, "Time", clock() - clk );
    }
    if ( fDumpUndecided )
    {
        ABC_FREE( pNew->pReprs );
        ABC_FREE( pNew->pNexts );
        Gia_WriteAiger( pNew, "gia_cec_undecided.aig", 0, 0 );
        Abc_Print( 1, "The result is written into file \"%s\".\n", "gia_cec_undecided.aig" );
    }
    if ( pPars->TimeLimit && ((double)clock() - clkTotal)/CLOCKS_PER_SEC >= pPars->TimeLimit )
    {
        Gia_ManStop( pNew );
        return -1;
    }
    // call other solver
    if ( pPars->fVerbose )
    Abc_Print( 1, "Calling the old CEC engine.\n" );
    fflush( stdout );
    RetValue = Cec_ManVerifyOld( pNew, pPars->fVerbose, &pPars->iOutFail );
    p->pCexComb = pNew->pCexComb; pNew->pCexComb = NULL;
    if ( p->pCexComb && !Gia_ManVerifyCex( p, p->pCexComb, 1 ) )
        Abc_Print( 1, "Counter-example simulation has failed.\n" );
    Gia_ManStop( pNew );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [New CEC engine applied to two circuits.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManVerifyTwo( Gia_Man_t * p0, Gia_Man_t * p1, int fVerbose )
{
    Cec_ParCec_t ParsCec, * pPars = &ParsCec;
    Gia_Man_t * pMiter;
    int RetValue;
    Cec_ManCecSetDefaultParams( pPars );
    pPars->fVerbose = fVerbose;
    pMiter = Gia_ManMiter( p0, p1, 1, 0, pPars->fVerbose );
    if ( pMiter == NULL )
        return -1;
    RetValue = Cec_ManVerify( pMiter, pPars );
    p0->pCexComb = pMiter->pCexComb; pMiter->pCexComb = NULL;
    Gia_ManStop( pMiter );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [New CEC engine applied to two circuits.]

  Description [Returns 1 if equivalent, 0 if counter-example, -1 if undecided.
  Counter-example is returned in the first manager as pAig0->pSeqModel.
  The format is given in Abc_Cex_t (file "abc\src\aig\gia\gia.h").]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManVerifyTwoAigs( Aig_Man_t * pAig0, Aig_Man_t * pAig1, int fVerbose )
{
    Gia_Man_t * p0, * p1, * pTemp;
    int RetValue;

    p0 = Gia_ManFromAig( pAig0 );
    p0 = Gia_ManCleanup( pTemp = p0 );
    Gia_ManStop( pTemp );

    p1 = Gia_ManFromAig( pAig1 );
    p1 = Gia_ManCleanup( pTemp = p1 );
    Gia_ManStop( pTemp );

    RetValue = Cec_ManVerifyTwo( p0, p1, fVerbose );
    pAig0->pSeqModel = p0->pCexComb; p0->pCexComb = NULL;
    Gia_ManStop( p0 );
    Gia_ManStop( p1 );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Implementation of new signal correspodence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cec_LatchCorrespondence( Aig_Man_t * pAig, int nConfs, int fUseCSat )
{
    Gia_Man_t * pGia;
    Cec_ParCor_t CorPars, * pCorPars = &CorPars;
    Cec_ManCorSetDefaultParams( pCorPars );
    pCorPars->fLatchCorr = 1;
    pCorPars->fUseCSat   = fUseCSat;
    pCorPars->nBTLimit   = nConfs;
    pGia = Gia_ManFromAigSimple( pAig );
    Cec_ManLSCorrespondenceClasses( pGia, pCorPars );
    Gia_ManReprToAigRepr( pAig, pGia );
    Gia_ManStop( pGia );
    return Aig_ManDupSimple( pAig );
}

/**Function*************************************************************

  Synopsis    [Implementation of new signal correspodence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cec_SignalCorrespondence( Aig_Man_t * pAig, int nConfs, int fUseCSat )
{
    Gia_Man_t * pGia;
    Cec_ParCor_t CorPars, * pCorPars = &CorPars;
    Cec_ManCorSetDefaultParams( pCorPars );
    pCorPars->fUseCSat  = fUseCSat;
    pCorPars->nBTLimit  = nConfs;
    pGia = Gia_ManFromAigSimple( pAig );
    Cec_ManLSCorrespondenceClasses( pGia, pCorPars );
    Gia_ManReprToAigRepr( pAig, pGia );
    Gia_ManStop( pGia );
    return Aig_ManDupSimple( pAig );
}

/**Function*************************************************************

  Synopsis    [Implementation of fraiging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cec_FraigCombinational( Aig_Man_t * pAig, int nConfs, int fVerbose )
{
    Gia_Man_t * pGia;
    Cec_ParFra_t FraPars, * pFraPars = &FraPars;
    Cec_ManFraSetDefaultParams( pFraPars );
    pFraPars->fSatSweeping = 1;
    pFraPars->nBTLimit  = nConfs;
    pFraPars->nItersMax = 20;
    pFraPars->fVerbose  = fVerbose;
    pGia = Gia_ManFromAigSimple( pAig );
    Cec_ManSatSweeping( pGia, pFraPars );
    Gia_ManReprToAigRepr( pAig, pGia );
    Gia_ManStop( pGia );
    return Aig_ManDupSimple( pAig );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

