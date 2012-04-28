/**CFile****************************************************************

  FileName    [ifTruth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Computation of truth tables of the cuts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifTruth.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Several simple procedures working with truth tables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int  If_TruthWordNum( int nVars )  { return nVars <= 5 ? 1 : (1 << (nVars - 5)); }
static inline void If_TruthNot( unsigned * pOut, unsigned * pIn, int nVars )
{
    int w;
    for ( w = If_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = ~pIn[w];
}
static inline void If_TruthCopy( unsigned * pOut, unsigned * pIn, int nVars )
{
    int w;
    for ( w = If_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn[w];
}
static inline void If_TruthNand( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = If_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = ~(pIn0[w] & pIn1[w]);
}
static inline void If_TruthAnd( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = If_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn0[w] & pIn1[w];
}

/**Function*************************************************************

  Synopsis    [Swaps two adjacent variables in the truth table.]

  Description [Swaps var number Start and var number Start+1 (0-based numbers).
  The input truth table is pIn. The output truth table is pOut.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_TruthSwapAdjacentVars( unsigned * pOut, unsigned * pIn, int nVars, int iVar )
{
    static unsigned PMasks[4][3] = {
        { 0x99999999, 0x22222222, 0x44444444 },
        { 0xC3C3C3C3, 0x0C0C0C0C, 0x30303030 },
        { 0xF00FF00F, 0x00F000F0, 0x0F000F00 },
        { 0xFF0000FF, 0x0000FF00, 0x00FF0000 }
    };
    int nWords = If_TruthWordNum( nVars );
    int i, k, Step, Shift;

    assert( iVar < nVars - 1 );
    if ( iVar < 4 )
    {
        Shift = (1 << iVar);
        for ( i = 0; i < nWords; i++ )
            pOut[i] = (pIn[i] & PMasks[iVar][0]) | ((pIn[i] & PMasks[iVar][1]) << Shift) | ((pIn[i] & PMasks[iVar][2]) >> Shift);
    }
    else if ( iVar > 4 )
    {
        Step = (1 << (iVar - 5));
        for ( k = 0; k < nWords; k += 4*Step )
        {
            for ( i = 0; i < Step; i++ )
                pOut[i] = pIn[i];
            for ( i = 0; i < Step; i++ )
                pOut[Step+i] = pIn[2*Step+i];
            for ( i = 0; i < Step; i++ )
                pOut[2*Step+i] = pIn[Step+i];
            for ( i = 0; i < Step; i++ )
                pOut[3*Step+i] = pIn[3*Step+i];
            pIn  += 4*Step;
            pOut += 4*Step;
        }
    }
    else // if ( iVar == 4 )
    {
        for ( i = 0; i < nWords; i += 2 )
        {
            pOut[i]   = (pIn[i]   & 0x0000FFFF) | ((pIn[i+1] & 0x0000FFFF) << 16);
            pOut[i+1] = (pIn[i+1] & 0xFFFF0000) | ((pIn[i]   & 0xFFFF0000) >> 16);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Implements given permutation of variables.]

  Description [Permutes truth table in-place (returns it in pIn).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutTruthPermute( unsigned * pOut, unsigned * pIn, int nVars, float * pDelays, int * pVars )
{
    unsigned * pTemp;
    float tTemp;
    int i, Temp, Counter = 0, fChange = 1;
    while ( fChange )
    {
        fChange = 0;
        for ( i = 0; i < nVars - 1; i++ )
        {
            if ( pDelays[i] >= pDelays[i+1] )
//            if ( pDelays[i] <= pDelays[i+1] )
                continue;
            tTemp = pDelays[i]; pDelays[i] = pDelays[i+1]; pDelays[i+1] = tTemp;
            Temp = pVars[i]; pVars[i] = pVars[i+1]; pVars[i+1] = Temp;
            if ( pOut && pIn )
            If_TruthSwapAdjacentVars( pOut, pIn, nVars, i );
            pTemp = pOut; pOut = pIn; pIn = pTemp;
            fChange = 1;
            Counter++;
        }
    }
    if ( pOut && pIn && (Counter & 1) )
        If_TruthCopy( pOut, pIn, nVars );
}


/**Function*************************************************************

  Synopsis    [Expands the truth table according to the phase.]

  Description [The input and output truth tables are in pIn/pOut. The current number
  of variables is nVars. The total number of variables in nVarsAll. The last argument
  (Phase) contains shows where the variables should go.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_TruthStretch( unsigned * pOut, unsigned * pIn, int nVars, int nVarsAll, unsigned Phase )
{
    unsigned * pTemp;
    int i, k, Var = nVars - 1, Counter = 0;
    for ( i = nVarsAll - 1; i >= 0; i-- )
        if ( Phase & (1 << i) )
        {
            for ( k = Var; k < i; k++ )
            {
                If_TruthSwapAdjacentVars( pOut, pIn, nVarsAll, k );
                pTemp = pIn; pIn = pOut; pOut = pTemp;
                Counter++;
            }
            Var--;
        }
    assert( Var == -1 );
    // swap if it was moved an even number of times
    if ( !(Counter & 1) )
        If_TruthCopy( pOut, pIn, nVarsAll );
}

/**Function*************************************************************

  Synopsis    [Shrinks the truth table according to the phase.]

  Description [The input and output truth tables are in pIn/pOut. The current number
  of variables is nVars. The total number of variables in nVarsAll. The last argument
  (Phase) contains shows what variables should remain.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_TruthShrink( unsigned * pOut, unsigned * pIn, int nVars, int nVarsAll, unsigned Phase, int fReturnIn )
{
    unsigned * pTemp;
    int i, k, Var = 0, Counter = 0;
    for ( i = 0; i < nVarsAll; i++ )
        if ( Phase & (1 << i) )
        {
            for ( k = i-1; k >= Var; k-- )
            {
                If_TruthSwapAdjacentVars( pOut, pIn, nVarsAll, k );
                pTemp = pIn; pIn = pOut; pOut = pTemp;
                Counter++;
            }
            Var++;
        }
    assert( Var == nVars );
    // swap if it was moved an even number of times
    if ( fReturnIn ^ !(Counter & 1) )
        If_TruthCopy( pOut, pIn, nVarsAll );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if TT depends on the given variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutTruthVarInSupport( unsigned * pTruth, int nVars, int iVar )
{
    int nWords = If_TruthWordNum( nVars );
    int i, k, Step;

    assert( iVar < nVars );
    switch ( iVar )
    {
    case 0:
        for ( i = 0; i < nWords; i++ )
            if ( (pTruth[i] & 0x55555555) != ((pTruth[i] & 0xAAAAAAAA) >> 1) )
                return 1;
        return 0;
    case 1:
        for ( i = 0; i < nWords; i++ )
            if ( (pTruth[i] & 0x33333333) != ((pTruth[i] & 0xCCCCCCCC) >> 2) )
                return 1;
        return 0;
    case 2:
        for ( i = 0; i < nWords; i++ )
            if ( (pTruth[i] & 0x0F0F0F0F) != ((pTruth[i] & 0xF0F0F0F0) >> 4) )
                return 1;
        return 0;
    case 3:
        for ( i = 0; i < nWords; i++ )
            if ( (pTruth[i] & 0x00FF00FF) != ((pTruth[i] & 0xFF00FF00) >> 8) )
                return 1;
        return 0;
    case 4:
        for ( i = 0; i < nWords; i++ )
            if ( (pTruth[i] & 0x0000FFFF) != ((pTruth[i] & 0xFFFF0000) >> 16) )
                return 1;
        return 0;
    default:
        Step = (1 << (iVar - 5));
        for ( k = 0; k < nWords; k += 2*Step )
        {
            for ( i = 0; i < Step; i++ )
                if ( pTruth[i] != pTruth[Step+i] )
                    return 1;
            pTruth += 2*Step;
        }
        return 0;
    }
}

/**Function*************************************************************

  Synopsis    [Returns support of the function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned If_CutTruthSupport( unsigned * pTruth, int nVars, int * pnSuppSize )
{
    int i, Support = 0;
    int nSuppSize = 0;
    for ( i = 0; i < nVars; i++ )
        if ( If_CutTruthVarInSupport( pTruth, nVars, i ) )
        {
            Support |= (1 << i);
            nSuppSize++;
        }
    *pnSuppSize = nSuppSize;
    return Support;
}


/**Function*************************************************************

  Synopsis    [Computes the stretching phase of the cut w.r.t. the merged cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned If_CutTruthPhase( If_Cut_t * pCut, If_Cut_t * pCut1 )
{
    unsigned uPhase = 0;
    int i, k;
    for ( i = k = 0; i < (int)pCut->nLeaves; i++ )
    {
        if ( k == (int)pCut1->nLeaves )
            break;
        if ( pCut->pLeaves[i] < pCut1->pLeaves[k] )
            continue;
        assert( pCut->pLeaves[i] == pCut1->pLeaves[k] );
        uPhase |= (1 << i);
        k++;
    }
    return uPhase;
}

//static FILE * pTruths;

/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutComputeTruth( If_Man_t * p, If_Cut_t * pCut, If_Cut_t * pCut0, If_Cut_t * pCut1, int fCompl0, int fCompl1 )
{
    extern void If_CutFactorTest( unsigned * pTruth, int nVars );

    // permute the first table
    if ( fCompl0 ^ pCut0->fCompl ) 
        If_TruthNot( p->puTemp[0], If_CutTruth(pCut0), pCut->nLimit );
    else
        If_TruthCopy( p->puTemp[0], If_CutTruth(pCut0), pCut->nLimit );
    If_TruthStretch( p->puTemp[2], p->puTemp[0], pCut0->nLeaves, pCut->nLimit, If_CutTruthPhase(pCut, pCut0) );
    // permute the second table
    if ( fCompl1 ^ pCut1->fCompl ) 
        If_TruthNot( p->puTemp[1], If_CutTruth(pCut1), pCut->nLimit );
    else
        If_TruthCopy( p->puTemp[1], If_CutTruth(pCut1), pCut->nLimit );
    If_TruthStretch( p->puTemp[3], p->puTemp[1], pCut1->nLeaves, pCut->nLimit, If_CutTruthPhase(pCut, pCut1) );
    // produce the resulting table
    assert( pCut->fCompl == 0 );
    if ( pCut->fCompl )
        If_TruthNand( If_CutTruth(pCut), p->puTemp[2], p->puTemp[3], pCut->nLimit );
    else
        If_TruthAnd( If_CutTruth(pCut), p->puTemp[2], p->puTemp[3], pCut->nLimit );
/*
    if ( pCut->nLeaves == 5 )
    {
        if ( pTruths == NULL )
            pTruths = fopen( "fun5var.txt", "w" );
        Extra_PrintHex( pTruths, If_CutTruth(pCut), pCut->nLeaves );
        fprintf( pTruths, "\n" );
    }
*/
    // minimize the support of the cut
    if ( p->pPars->fCutMin )
        return If_CutTruthMinimize( p, pCut );

    // perform 
//    If_CutFactorTest( If_CutTruth(pCut), pCut->nLimit );
//    printf( "%d ", If_CutLeaveNum(pCut) - If_CutTruthSupportSize(If_CutTruth(pCut), If_CutLeaveNum(pCut)) );
    return 0;
}


/**Function*************************************************************

  Synopsis    [Minimize support of the cut.]

  Description [Returns 1 if the node's support has changed]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutTruthMinimize( If_Man_t * p, If_Cut_t * pCut )
{
    unsigned uSupport;
    int nSuppSize, i, k;
    // compute the support of the cut's function
    uSupport = If_CutTruthSupport( If_CutTruth(pCut), If_CutLeaveNum(pCut), &nSuppSize );
    if ( nSuppSize == If_CutLeaveNum(pCut) )
        return 0;

// TEMPORARY
    if ( nSuppSize < 2 )
    {
        p->nSmallSupp++;
        return 2;
    }
//    if ( If_CutLeaveNum(pCut) - nSuppSize > 1 )
//        return 0;
//printf( "%d %d  ", If_CutLeaveNum(pCut), nSuppSize );
//    pCut->fUseless = 1;

    // shrink the truth table
    If_TruthShrink( p->puTemp[0], If_CutTruth(pCut), nSuppSize, pCut->nLimit, uSupport, 1 );
    // update leaves and signature
    pCut->uSign = 0;
    for ( i = k = 0; i < If_CutLeaveNum(pCut); i++ )
    {
        if ( !(uSupport & (1 << i)) )
            continue;    
        pCut->pLeaves[k++] = pCut->pLeaves[i];
        pCut->uSign |= If_ObjCutSign( pCut->pLeaves[i] );
    }
    assert( k == nSuppSize );
    pCut->nLeaves = nSuppSize;
    // verify the result
//    uSupport = If_CutTruthSupport( If_CutTruth(pCut), If_CutLeaveNum(pCut), &nSuppSize );
//    assert( nSuppSize == If_CutLeaveNum(pCut) );
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

