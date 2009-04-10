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
#include "giaAig.h"

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
    p->pCexComb = (Gia_Cex_t *)ABC_CALLOC( char, 
        sizeof(Gia_Cex_t) + sizeof(unsigned) * Gia_BitWordNum(Gia_ManCiNum(p)) );
    p->pCexComb->iPo = iOut;
    p->pCexComb->nPis = Gia_ManCiNum(p);
    p->pCexComb->nBits = Gia_ManCiNum(p);
    for ( i = 0; i < Gia_ManCiNum(p); i++ )
        if ( pValues[i] )
            Aig_InfoSetBit( p->pCexComb->pData, i );
}

/**Function*************************************************************

  Synopsis    [Interface to the old CEC engine]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManVerifyOld( Gia_Man_t * pMiter, int fVerbose )
{
    extern int Fra_FraigCec( Aig_Man_t ** ppAig, int nConfLimit, int fVerbose );
    extern int Ssw_SecCexResimulate( Aig_Man_t * p, int * pModel, int * pnOutputs );
    Gia_Man_t * pTemp = Gia_ManTransformMiter( pMiter );
    Aig_Man_t * pMiterCec = Gia_ManToAig( pTemp, 0 );
    int RetValue, iOut, nOuts, clkTotal = clock();
    Gia_ManStop( pTemp );
    // run CEC on this miter
    RetValue = Fra_FraigCec( &pMiterCec, 100000, fVerbose );
    // report the miter
    if ( RetValue == 1 )
    {
        printf( "Networks are equivalent.   " );
ABC_PRT( "Time", clock() - clkTotal );
    }
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT.   " );
ABC_PRT( "Time", clock() - clkTotal );
        if ( pMiterCec->pData == NULL )
            printf( "Counter-example is not available.\n" );
        else
        {
            iOut = Ssw_SecCexResimulate( pMiterCec, pMiterCec->pData, &nOuts );
            if ( iOut == -1 )
                printf( "Counter-example verification has failed.\n" );
            else 
            {
                printf( "Primary output %d has failed in frame %d.\n", iOut );
                printf( "The counter-example detected %d incorrect outputs.\n", nOuts );
            }
            Cec_ManTransformPattern( pMiter, iOut, pMiterCec->pData );
        }
    }
    else
    {
        printf( "Networks are UNDECIDED.   " );
ABC_PRT( "Time", clock() - clkTotal );
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
int Cec_ManVerify( Gia_Man_t * p, Cec_ParCec_t * pPars )
{
    int fDumpUndecided = 1;
    Cec_ParFra_t ParsFra, * pParsFra = &ParsFra;
    Gia_Man_t * pNew;
    int RetValue, clk = clock();
    double clkTotal = clock();
    // sweep for equivalences
    Cec_ManFraSetDefaultParams( pParsFra );
    pParsFra->nItersMax    = 1000;
    pParsFra->nBTLimit     = pPars->nBTLimit;
    pParsFra->TimeLimit    = pPars->TimeLimit;
    pParsFra->fVerbose     = pPars->fVerbose;
    pParsFra->fCheckMiter  = 1;
    pParsFra->fFirstStop   = 1;
    pParsFra->fDualOut     = 1;
    pNew = Cec_ManSatSweeping( p, pParsFra );
    if ( pNew == NULL )
    {
        if ( !Gia_ManVerifyCounterExample( p, p->pCexComb, 1 ) )
            printf( "Counter-example simulation has failed.\n" );
        printf( "Networks are NOT EQUIVALENT.  " );
        ABC_PRT( "Time", clock() - clk );
        return 0;
    }
    if ( Gia_ManAndNum(pNew) == 0 )
    {
        printf( "Networks are equivalent.  " );
        ABC_PRT( "Time", clock() - clk );
        Gia_ManStop( pNew );
        return 1;
    }
    printf( "Networks are UNDECIDED after the new CEC engine.  " );
    ABC_PRT( "Time", clock() - clk );
    if ( fDumpUndecided )
    {
        Gia_WriteAiger( pNew, "gia_cec_undecided.aig", 0, 0 );
        printf( "The result is written into file \"%s\".\n", "gia_cec_undecided.aig" );
    }
    if ( pPars->TimeLimit && ((double)clock() - clkTotal)/CLOCKS_PER_SEC >= pPars->TimeLimit )
    {
        Gia_ManStop( pNew );
        return -1;
    }
    // call other solver
    printf( "Calling the old CEC engine.\n" );
    fflush( stdout );
    RetValue = Cec_ManVerifyOld( pNew, pPars->fVerbose );
    p->pCexComb = pNew->pCexComb; pNew->pCexComb = NULL;
    if ( p->pCexComb && !Gia_ManVerifyCounterExample( p, p->pCexComb, 1 ) )
        printf( "Counter-example simulation has failed.\n" );
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
  The format is given in Gia_Cex_t (file "abc\src\aig\gia\gia.h").]
               
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


