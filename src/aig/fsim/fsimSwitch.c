/**CFile****************************************************************

  FileName    [fsimSwitch.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Fast sequential AIG simulator.]

  Synopsis    [Computing switching activity.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: fsimSwitch.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fsimInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimInfoRandom( Fsim_Man_t * p, unsigned * pInfo, int nProbNum )
{
    unsigned Mask;
    int w, i;
    if ( nProbNum )
    {
        Mask = Aig_ManRandom( 0 );
        for ( i = 0; i < nProbNum; i++ )
            Mask &= Aig_ManRandom( 0 );
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] ^= Mask;
    }
    else
    {
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] = Aig_ManRandom( 0 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimInfoRandomShift( Fsim_Man_t * p, unsigned * pInfo, int nProbNum )
{
    unsigned Mask;
    int w, i;
    Mask = Aig_ManRandom( 0 );
    for ( i = 0; i < nProbNum; i++ )
        Mask &= Aig_ManRandom( 0 );
    if ( p->nWords == 1 )
        pInfo[0] = (pInfo[0] << 16) | ((pInfo[0] ^ Mask) & 0xffff);
    else
    {
        assert( (p->nWords & 1) == 0 );   // should be even number
        for ( w = p->nWords-1; w >= 0; w-- )
            if ( w >= p->nWords/2 )
                pInfo[w] = pInfo[w - p->nWords/2]; 
            else
                pInfo[w] ^= Mask;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimInfoZero( Fsim_Man_t * p, unsigned * pInfo )
{
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimInfoOne( Fsim_Man_t * p, unsigned * pInfo )
{
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = ~0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimInfoCopy( Fsim_Man_t * p, unsigned * pInfo, unsigned * pInfo0 )
{
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = pInfo0[w];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimInfoCopyShift( Fsim_Man_t * p, unsigned * pInfo, unsigned * pInfo0 )
{
    int w;
    if ( p->nWords == 1 )
        pInfo[0] = (pInfo[0] << 16) | (pInfo0[0] & 0xffff);
    else
    {
        assert( (p->nWords & 1) == 0 );   // should be even number
        for ( w = p->nWords-1; w >= 0; w-- )
        {
            if ( w >= p->nWords/2 )
                pInfo[w] = pInfo[w - p->nWords/2]; 
            else
                pInfo[w] = pInfo0[w]; 
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimulateCi( Fsim_Man_t * p, int iNode, int iCi )
{
    unsigned * pInfo  = Fsim_SimData( p, iNode % p->nFront );
    unsigned * pInfo0 = Fsim_SimDataCi( p, iCi );
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = pInfo0[w];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimulateCo( Fsim_Man_t * p, int iCo, int iFan0 )
{
    unsigned * pInfo  = Fsim_SimDataCo( p, iCo );
    unsigned * pInfo0 = Fsim_SimData( p, Fsim_Lit2Var(iFan0) % p->nFront );
    int w;
    if ( Fsim_LitIsCompl(iFan0) )
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] = ~pInfo0[w];
    else //if ( !Fsim_LitIsCompl(iFan0) )
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] = pInfo0[w];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimulateNode( Fsim_Man_t * p, int iNode, int iFan0, int iFan1 )
{
    unsigned * pInfo  = Fsim_SimData( p, iNode % p->nFront );
    unsigned * pInfo0 = Fsim_SimData( p, Fsim_Lit2Var(iFan0) % p->nFront );
    unsigned * pInfo1 = Fsim_SimData( p, Fsim_Lit2Var(iFan1) % p->nFront );
    int w;
    if ( Fsim_LitIsCompl(iFan0) && Fsim_LitIsCompl(iFan1) )
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] = ~(pInfo0[w] | pInfo1[w]);
    else if ( Fsim_LitIsCompl(iFan0) && !Fsim_LitIsCompl(iFan1) )
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] = ~pInfo0[w] & pInfo1[w];
    else if ( !Fsim_LitIsCompl(iFan0) && Fsim_LitIsCompl(iFan1) )
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] = pInfo0[w] & ~pInfo1[w];
    else //if ( !Fsim_LitIsCompl(iFan0) && !Fsim_LitIsCompl(iFan1) )
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] = pInfo0[w] & pInfo1[w];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimInfoInit( Fsim_Man_t * p )
{
    int iPioNum, i;
    Vec_IntForEachEntry( p->vCis2Ids, iPioNum, i )
    {
        if ( iPioNum < p->nPis )
            Fsim_ManSwitchSimInfoRandom( p, Fsim_SimDataCi(p, i), 0 );
        else
            Fsim_ManSwitchSimInfoZero( p, Fsim_SimDataCi(p, i) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimInfoTransfer( Fsim_Man_t * p, int nProbNum )
{
    int iPioNum, i;
    Vec_IntForEachEntry( p->vCis2Ids, iPioNum, i )
    {
        if ( iPioNum < p->nPis )
            Fsim_ManSwitchSimInfoRandom( p, Fsim_SimDataCi(p, i), nProbNum );
        else
            Fsim_ManSwitchSimInfoCopy( p, Fsim_SimDataCi(p, i), Fsim_SimDataCo(p, p->nPos+iPioNum-p->nPis) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimInfoTransferShift( Fsim_Man_t * p, int nProbNum )
{
    int iPioNum, i;
    Vec_IntForEachEntry( p->vCis2Ids, iPioNum, i )
    {
        if ( iPioNum < p->nPis )
            Fsim_ManSwitchSimInfoRandomShift( p, Fsim_SimDataCi(p, i), nProbNum );
        else
            Fsim_ManSwitchSimInfoCopyShift( p, Fsim_SimDataCi(p, i), Fsim_SimDataCo(p, p->nPos+iPioNum-p->nPis) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Fsim_ManSwitchSimInfoCountOnes( Fsim_Man_t * p, int iNode )
{
    unsigned * pInfo;
    int w, Counter = 0;
    pInfo = Fsim_SimData( p, iNode % p->nFront );
    for ( w = p->nWords-1; w >= 0; w-- )
        Counter += Aig_WordCountOnes( pInfo[w] );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Fsim_ManSwitchSimInfoCountTrans( Fsim_Man_t * p, int iNode )
{
    unsigned * pInfo;
    int w, Counter = 0;
    assert( iNode % p->nFront );
    pInfo = Fsim_SimData( p, iNode % p->nFront );
    if ( p->nWords == 1 )
        return Aig_WordCountOnes( (pInfo[0] ^ (pInfo[0] >> 16)) & 0xffff );
    for ( w = p->nWords/2-1; w >= 0; w-- )
        Counter += Aig_WordCountOnes( pInfo[w] ^ pInfo[w + p->nWords/2] );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fsim_ManSwitchSimulateRound( Fsim_Man_t * p, int fCount )
{
    int * pCur, * pEnd;
    int i, iCis = 0, iCos = 0;
    if ( Aig_ObjRefs(Aig_ManConst1(p->pAig)) )
        Fsim_ManSwitchSimInfoOne( p, Fsim_SimData(p, 1) );
    pCur = p->pDataAig2 + 6;
    pEnd = p->pDataAig2 + 3 * p->nObjs;
    for ( i = 2; pCur < pEnd; i++ )
    {
        if ( pCur[1] == 0 )
            Fsim_ManSwitchSimulateCi( p, pCur[0], iCis++ );
        else if ( pCur[2] == 0 )
            Fsim_ManSwitchSimulateCo( p, iCos++, pCur[1] );
        else
            Fsim_ManSwitchSimulateNode( p, pCur[0], pCur[1], pCur[2] );
        if ( fCount && pCur[0] )
        {
            if ( p->pData1 )
                p->pData1[i] += Fsim_ManSwitchSimInfoCountOnes( p, pCur[0] );
            if ( p->pData2 )
                p->pData2[i] += Fsim_ManSwitchSimInfoCountTrans( p, pCur[0] );
        }
        pCur += 3;
    }
    assert( iCis == p->nCis );
    assert( iCos == p->nCos );
}

/**Function*************************************************************

  Synopsis    [Computes switching activity of one node.]

  Description [Uses the formula: Switching = 2 * nOnes * nZeros / (nTotal ^ 2) ]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Fsim_ManSwitchComputeSwitching( int nOnes, int nSimWords )
{
    int nTotal = 32 * nSimWords;
    return (float)2.0 * nOnes / nTotal * (nTotal - nOnes) / nTotal;
}

/**Function*************************************************************

  Synopsis    [Computes switching activity of one node.]

  Description [Uses the formula: Switching = 2 * nOnes * nZeros / (nTotal ^ 2) ]
               
  SideEffects []

  SeeAlso     [] 

***********************************************************************/
float Fsim_ManSwitchComputeProbOne( int nOnes, int nSimWords )
{
    int nTotal = 32 * nSimWords;
    return (float)nOnes / nTotal;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Fsim_ManSwitchSimulate( Aig_Man_t * pAig, Fsim_ParSwitch_t * pPars )
{
    Vec_Int_t * vSwitching;
    float * pSwitching;
    Aig_Obj_t * pObj;
    Fsim_Man_t * p;
    int i, clk, clkTotal = clock();
    // create manager
    clk = clock();
    p = Fsim_ManCreate( pAig );
    p->nWords = pPars->nWords;
    // if the number of words is larger then 1, it should be even
    if ( p->nWords > 1 && (p->nWords & 1) )
        p->nWords++;
    // print stats
    if ( pPars->fVerbose )
    {
        printf( "Obj = %8d (%8d). Cut = %6d. Front = %6d.  FrtMem = %7.2f Mb. ", 
            p->nObjs, p->nCis + p->nNodes, p->nCrossCutMax, p->nFront, 
            4.0*pPars->nWords*(p->nFront)/(1<<20) );
        PRT( "Time", clock() - clk );
    }
    // create simulation frontier
    clk = clock();
    Fsim_ManFront( p, 0 );
    if ( pPars->fVerbose )
    {
        printf( "Max ID = %8d. Log max ID = %2d.  AigMem = %7.2f Mb (%5.2f byte/obj).  ", 
            p->iNumber, Aig_Base2Log(p->iNumber), 
            1.0*(p->pDataCur-p->pDataAig)/(1<<20), 
            1.0*(p->pDataCur-p->pDataAig)/p->nObjs ); 
        PRT( "Time", clock() - clk );
    }
    // perform simulation
    Aig_ManRandom( 1 );
    assert( p->pDataSim == NULL );
    p->pDataSim = ALLOC( unsigned, pPars->nWords * p->nFront * sizeof(unsigned) );
    p->pDataSimCis = ALLOC( unsigned, pPars->nWords * p->nCis * sizeof(unsigned) );
    p->pDataSimCos = ALLOC( unsigned, pPars->nWords * p->nCos * sizeof(unsigned) );
    if ( pPars->fProbOne )
        p->pData1 = CALLOC( int, p->nObjs * sizeof(int) );
    if ( pPars->fProbTrans )
        p->pData2 = CALLOC( int, p->nObjs * sizeof(int) );
    Fsim_ManSwitchSimInfoInit( p );
    for ( i = 0; i < pPars->nIters; i++ )
    {
        Fsim_ManSwitchSimulateRound( p, i >= pPars->nPref );
        if ( i < pPars->nIters - 1 )
        {
//            if ( pPars->fProbTrans )
                Fsim_ManSwitchSimInfoTransferShift( p, pPars->nRandPiNum );
//            else
//                Fsim_ManSwitchSimInfoTransfer( p, pPars->nRandPiNum );
        }
    }
    if ( pPars->fVerbose )
    {
        printf( "Maxcut = %8d.  AigMem = %7.2f Mb.  SimMem = %7.2f Mb.  ", 
            p->nCrossCutMax, 
            p->pDataAig2? 12.0*p->nObjs/(1<<20) : 1.0*(p->pDataCur-p->pDataAig)/(1<<20), 
            4.0*pPars->nWords*(p->nFront+p->nCis+p->nCos)/(1<<20) );
        PRT( "Sim time", clock() - clkTotal );
    }
    // derive the result
    vSwitching = Vec_IntStart( Aig_ManObjNumMax(pAig) );
    pSwitching = (float *)vSwitching->pArray;
/*
    if ( pPars->fProbOne && pPars->fProbTrans )
    {
        Aig_ManForEachObj( pAig, pObj, i )
//            pSwitching[pObj->Id] = Fsim_ManSwitchComputeSwitching( p->pData1[pObj->iData], pPars->nWords*(pPars->nIters-pPars->nPref) );
            pSwitching[pObj->Id] = Fsim_ManSwitchComputeProbOne( p->pData2[pObj->iData], pPars->nWords*(pPars->nIters-pPars->nPref)/2 );
    }
    else if ( !pPars->fProbOne && pPars->fProbTrans )
    {
        Aig_ManForEachObj( pAig, pObj, i )
            pSwitching[pObj->Id] = Fsim_ManSwitchComputeProbOne( p->pData2[pObj->iData], pPars->nWords*(pPars->nIters-pPars->nPref)/2 );
    }
    else if ( pPars->fProbOne && !pPars->fProbTrans )
    {
        Aig_ManForEachObj( pAig, pObj, i )
            pSwitching[pObj->Id] = Fsim_ManSwitchComputeProbOne( p->pData1[pObj->iData], pPars->nWords*(pPars->nIters-pPars->nPref) );
    }
    else
        assert( 0 );
*/
    if ( pPars->fProbOne && !pPars->fProbTrans )
    {
        Aig_ManForEachObj( pAig, pObj, i )
            pSwitching[pObj->Id] = Fsim_ManSwitchComputeProbOne( p->pData1[pObj->iData], pPars->nWords*(pPars->nIters-pPars->nPref) );
    }
    else if ( !pPars->fProbOne && pPars->fProbTrans )
    {
        Aig_ManForEachObj( pAig, pObj, i )
            pSwitching[pObj->Id] = Fsim_ManSwitchComputeProbOne( p->pData2[pObj->iData], pPars->nWords*(pPars->nIters-pPars->nPref)/2 );
    }
    else
        assert( 0 );
    Fsim_ManDelete( p );
    return vSwitching;

}

/**Function*************************************************************

  Synopsis    [Computes probability of switching (or of being 1).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManComputeSwitchProbs4( Aig_Man_t * p, int nFrames, int nPref, int fProbOne )
{
    Fsim_ParSwitch_t Pars, * pPars = &Pars;
    Fsim_ManSetDefaultParamsSwitch( pPars );
    pPars->nWords = 1;
    pPars->nIters = nFrames;
    pPars->nPref  = nPref;
    if ( fProbOne )
    {
        pPars->fProbOne = 1;
        pPars->fProbTrans = 0;
    }
    else
    {
        pPars->fProbOne = 0;
        pPars->fProbTrans = 1;
    }
    pPars->fVerbose = 0;
    return Fsim_ManSwitchSimulate( p, pPars );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


