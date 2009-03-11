/**CFile****************************************************************

  FileName    [cecSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [Refinement of sequential equivalence classes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSeq.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets register values from the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSeqDeriveInfoFromCex( Vec_Ptr_t * vInfo, Gia_Man_t * pAig, Gia_Cex_t * pCex )
{
    unsigned * pInfo;
    int k, w, nWords;
    assert( pCex->nBits == pCex->nRegs + pCex->nPis * (pCex->iFrame + 1) );
    assert( pCex->nBits <= Vec_PtrSize(vInfo) );
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    for ( k = 0; k < pCex->nRegs; k++ )
    {
        pInfo = Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = Aig_InfoHasBit( pCex->pData, k )? ~0 : 0;
    }
    for ( ; k < pCex->nBits; k++ )
    {
        pInfo = Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = Aig_ManRandom(0);
        // set simulation pattern and make sure it is second (first will be erased during simulation)
        pInfo[0] = (pInfo[0] << 1) | Aig_InfoHasBit( pCex->pData, k ); 
        pInfo[0] <<= 1;
    }
    for ( ; k < Vec_PtrSize(vInfo); k++ )
    {
        pInfo = Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = Aig_ManRandom(0);
    }
}

/**Function*************************************************************

  Synopsis    [Sets register values from the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSeqDeriveInfoInitRandom( Vec_Ptr_t * vInfo, Gia_Man_t * pAig, Gia_Cex_t * pCex )
{
    unsigned * pInfo;
    int k, w, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    assert( Gia_ManRegNum(pAig) == pCex->nRegs );
    assert( Gia_ManRegNum(pAig) <= Vec_PtrSize(vInfo) );
    for ( k = 0; k < Gia_ManRegNum(pAig); k++ )
    {
        pInfo = Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = Aig_InfoHasBit( pCex->pData, k )? ~0 : 0;
    }

    for ( ; k < Vec_PtrSize(vInfo); k++ )
    {
        pInfo = Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = Aig_ManRandom( 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Resimulates the classes using sequential simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSeqResimulate( Cec_ManSim_t * p, Vec_Ptr_t * vInfo )
{
    unsigned * pInfo0, * pInfo1;
    int f, i, k, w, RetValue = 0;
    assert( Gia_ManRegNum(p->pAig) > 0 );
    assert( Vec_PtrSize(vInfo) == Gia_ManRegNum(p->pAig) + Gia_ManPiNum(p->pAig) * p->pPars->nRounds );
    for ( k = 0; k < Gia_ManRegNum(p->pAig); k++ )
    {
        pInfo0 = Vec_PtrEntry( vInfo, k );
        pInfo1 = Vec_PtrEntry( p->vCoSimInfo, Gia_ManPoNum(p->pAig) + k );
        for ( w = 0; w < p->nWords; w++ )
            pInfo1[w] = pInfo0[w];
    }
    for ( f = 0; f < p->pPars->nRounds; f++ )
    {
        for ( i = 0; i < Gia_ManPiNum(p->pAig); i++ )
        {
            pInfo0 = Vec_PtrEntry( vInfo, k++ );
            pInfo1 = Vec_PtrEntry( p->vCiSimInfo, i );
            for ( w = 0; w < p->nWords; w++ )
                pInfo1[w] = pInfo0[w];
        }
        for ( i = 0; i < Gia_ManRegNum(p->pAig); i++ )
        {
            pInfo0 = Vec_PtrEntry( p->vCoSimInfo, Gia_ManPoNum(p->pAig) + i );
            pInfo1 = Vec_PtrEntry( p->vCiSimInfo, Gia_ManPiNum(p->pAig) + i );
            for ( w = 0; w < p->nWords; w++ )
                pInfo1[w] = pInfo0[w];
        }
        if ( Cec_ManSimSimulateRound( p, p->vCiSimInfo, p->vCoSimInfo ) )
        {
            printf( "One of the outputs of the miter is asserted.\n" );
            RetValue = 1;
        }
    }
    assert( k == Vec_PtrSize(vInfo) );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Resimulates information to refine equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSeqResimulateInfo( Gia_Man_t * pAig, Vec_Ptr_t * vSimInfo, Gia_Cex_t * pBestState )
{
    Cec_ParSim_t ParsSim, * pParsSim = &ParsSim;
    Cec_ManSim_t * pSim;
    int RetValue, clkTotal = clock();
    assert( (Vec_PtrSize(vSimInfo) - Gia_ManRegNum(pAig)) % Gia_ManPiNum(pAig) == 0 );
    Cec_ManSimSetDefaultParams( pParsSim );
    pParsSim->nRounds = (Vec_PtrSize(vSimInfo) - Gia_ManRegNum(pAig)) / Gia_ManPiNum(pAig);
    pParsSim->nWords  = Vec_PtrReadWordsSimInfo( vSimInfo );
    Gia_ManSetRefs( pAig );
    pSim = Cec_ManSimStart( pAig, pParsSim );
    if ( pBestState )
        pSim->pBestState = pBestState;
    RetValue = Cec_ManSeqResimulate( pSim, vSimInfo );
    pSim->pBestState = NULL;
    Cec_ManSimStop( pSim );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Resimuates one counter-example to refine equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSeqResimulateCounter( Gia_Man_t * pAig, Cec_ParSim_t * pPars, Gia_Cex_t * pCex )
{
    Vec_Ptr_t * vSimInfo;
    int RetValue, clkTotal = clock();
    if ( pCex == NULL )
    {
        printf( "Cec_ManSeqResimulateCounter(): Counter-example is not available.\n" );
        return -1;
    }
    if ( pAig->pReprs == NULL )
    {
        printf( "Cec_ManSeqResimulateCounter(): Equivalence classes are not available.\n" );
        return -1;
    }
    if ( Gia_ManRegNum(pAig) == 0 )
    {
        printf( "Cec_ManSeqResimulateCounter(): Not a sequential AIG.\n" );
        return -1;
    }
    if ( Gia_ManRegNum(pAig) != pCex->nRegs || Gia_ManPiNum(pAig) != pCex->nPis )
    {
        printf( "Cec_ManSeqResimulateCounter(): Parameters of the ccounter-example differ.\n" );
        return -1;
    }
    if ( pPars->fVerbose )
        printf( "Resimulating %d timeframes.\n", pPars->nRounds + pCex->iFrame + 1 );
    Aig_ManRandom( 1 );
    vSimInfo = Vec_PtrAllocSimInfo( Gia_ManRegNum(pAig) + 
        Gia_ManPiNum(pAig) * (pPars->nRounds + pCex->iFrame + 1), 1 );
    Cec_ManSeqDeriveInfoFromCex( vSimInfo, pAig, pCex );
    if ( pPars->fVerbose )
        Gia_ManEquivPrintClasses( pAig, 0, 0 );
    RetValue = Cec_ManSeqResimulateInfo( pAig, vSimInfo, NULL );
    if ( pPars->fVerbose )
        Gia_ManEquivPrintClasses( pAig, 0, 0 );
    Vec_PtrFree( vSimInfo );
    if ( pPars->fVerbose )
        ABC_PRT( "Time", clock() - clkTotal );
    return RetValue;
}


/**Function*************************************************************

  Synopsis    [Performs semiformal refinement of equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSeqSemiformal( Gia_Man_t * pAig, Cec_ParSmf_t * pPars )
{ 
    int nAddFrames = 10; // additional timeframes to simulate
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Vec_Ptr_t * vSimInfo; 
    Gia_Cex_t * pState;
    Gia_Man_t * pSrm;
    int r, nPats, RetValue = -1;
    if ( pAig->pReprs == NULL )
    {
        printf( "Cec_ManSeqSemiformal(): Equivalence classes are not available.\n" );
        return -1;
    }
    if ( Gia_ManRegNum(pAig) == 0 )
    {
        printf( "Cec_ManSeqSemiformal(): Not a sequential AIG.\n" );
        return -1;
    }
    Aig_ManRandom( 1 );
    // prepare starting pattern
    pState = Gia_ManAllocCounterExample( Gia_ManRegNum(pAig), 0, 0 );
    pState->iFrame = -1;
    pState->iPo = -1;
    // prepare SAT solving
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->nBTLimit = pPars->nBTLimit;
    pParsSat->fVerbose = pPars->fVerbose;
    if ( pParsSat->fVerbose )
    {
        printf( "Starting: " );
        Gia_ManEquivPrintClasses( pAig, 0, 0 );
    }
    // perform the given number of BMC rounds
    for ( r = 0; r < pPars->nRounds; r++ )
    {
//        Gia_ManPrintCounterExample( pState );
        // derive speculatively reduced model
        pSrm = Gia_ManSpecReduceInit( pAig, pState, pPars->nFrames, pPars->fDualOut );
        assert( Gia_ManRegNum(pSrm) == 0 && Gia_ManPiNum(pSrm) == Gia_ManPiNum(pAig) * pPars->nFrames );
        // allocate room for simulation info
        vSimInfo = Vec_PtrAllocSimInfo( Gia_ManRegNum(pAig) + 
            Gia_ManPiNum(pAig) * (pPars->nFrames + nAddFrames), pPars->nWords );
        Cec_ManSeqDeriveInfoInitRandom( vSimInfo, pAig, pState );
        // fill in simulation info with counter-examples
        Cec_ManSatSolveSeq( vSimInfo, pSrm, pParsSat, Gia_ManRegNum(pAig), &nPats );
        Gia_ManStop( pSrm );
        // resimulate and refine the classes
        RetValue = Cec_ManSeqResimulateInfo( pAig, vSimInfo, pState );
        Vec_PtrFree( vSimInfo );
        assert( pState->iPo >= 0 ); // hit counter
        pState->iPo = -1;
        if ( pPars->fVerbose )
        {
            printf( "BMC = %3d ", nPats );
            Gia_ManEquivPrintClasses( pAig, 0, 0 );
        }
    }
    ABC_FREE( pState );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


