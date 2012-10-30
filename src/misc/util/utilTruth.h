/**CFile****************************************************************

  FileName    [utilTruth.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Truth table manipulation.]

  Synopsis    [Truth table manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 28, 2012.]

  Revision    [$Id: utilTruth.h,v 1.00 2012/10/28 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__misc__util__utilTruth_h
#define ABC__misc__util__utilTruth_h

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

static word s_Truths6[6] = {
    0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int  Abc_TtWordNum( int nVars ) { return nVars <= 6 ? 1 : 1 << (nVars-6); }

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_TtCopy( word * pOut, word * pIn, int nWords, int fCompl )
{
    int w;
    if ( fCompl )
        for ( w = 0; w < nWords; w++ )
            pOut[w] = ~pIn[w];
    else
        for ( w = 0; w < nWords; w++ )
            pOut[w] = pIn[w];
}
static inline void Abc_TtAnd( word * pOut, word * pIn1, word * pIn2, int nWords, int fCompl )
{
    int w;
    if ( fCompl )
        for ( w = 0; w < nWords; w++ )
            pOut[w] = ~(pIn1[w] & pIn2[w]);
    else
        for ( w = 0; w < nWords; w++ )
            pOut[w] = pIn1[w] & pIn2[w];
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_TtSuppIsMinBase( int Supp )
{
    return (Supp & (Supp+1)) == 0;
}
static inline int Abc_Tt6HasVar( word t, int iVar )
{
    return ((t << (1<<iVar)) & s_Truths6[iVar]) != (t & s_Truths6[iVar]);
}
static inline int Abc_TtHasVar( word * t, int nVars, int iVar )
{
    int nWords = Abc_TtWordNum( nVars );
    assert( iVar < nVars );
    if ( iVar < 6 )
    {
        int i, Shift = (1 << iVar);
        for ( i = 0; i < nWords; i++ )
            if ( ((t[i] << Shift) & s_Truths6[iVar]) != (t[i] & s_Truths6[iVar]) )
                return 1;
        return 0;
    }
    else
    {
        int i, Step = (1 << (iVar - 6));
        word * tLimit = t + nWords;
        for ( ; t < tLimit; t += 2*Step )
            for ( i = 0; i < Step; i++ )
                if ( t[i] != t[Step+i] )
                    return 1;
        return 0;
    }
}
static inline int Abc_TtSupport( word * t, int nVars )
{
    int v, Supp = 0;
    for ( v = 0; v < nVars; v++ )
        if ( Abc_TtHasVar( t, nVars, v ) )
            Supp |= (1 << v);
    return Supp;
}
static inline int Abc_TtSupportSize( word * t, int nVars )
{
    int v, SuppSize = 0;
    for ( v = 0; v < nVars; v++ )
        if ( Abc_TtHasVar( t, nVars, v ) )
            SuppSize++;
    return SuppSize;
}
static inline int Abc_TtSupportAndSize( word * t, int nVars, int * pSuppSize )
{
    int v, Supp = 0;
    *pSuppSize = 0;
    for ( v = 0; v < nVars; v++ )
        if ( Abc_TtHasVar( t, nVars, v ) )
            Supp |= (1 << v), (*pSuppSize)++;
    return Supp;
}
static inline int Abc_Tt6SupportAndSize( word t, int nVars, int * pSuppSize )
{
    int v, Supp = 0;
    *pSuppSize = 0;
    assert( nVars <= 6 );
    for ( v = 0; v < nVars; v++ )
        if ( Abc_Tt6HasVar( t, v ) )
            Supp |= (1 << v), (*pSuppSize)++;
    return Supp;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_TtSwapVars( word * pTruth, int nVars, int iVar, int jVar )
{
    static word PPMasks[5][6][3] = {
        { 
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 0 0  
            { 0x9999999999999999, 0x2222222222222222, 0x4444444444444444 }, // 0 1  
            { 0xA5A5A5A5A5A5A5A5, 0x0A0A0A0A0A0A0A0A, 0x5050505050505050 }, // 0 2 
            { 0xAA55AA55AA55AA55, 0x00AA00AA00AA00AA, 0x5500550055005500 }, // 0 3 
            { 0xAAAA5555AAAA5555, 0x0000AAAA0000AAAA, 0x5555000055550000 }, // 0 4 
            { 0xAAAAAAAA55555555, 0x00000000AAAAAAAA, 0x5555555500000000 }  // 0 5 
        },
        { 
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 1 0  
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 1 1  
            { 0xC3C3C3C3C3C3C3C3, 0x0C0C0C0C0C0C0C0C, 0x3030303030303030 }, // 1 2 
            { 0xCC33CC33CC33CC33, 0x00CC00CC00CC00CC, 0x3300330033003300 }, // 1 3 
            { 0xCCCC3333CCCC3333, 0x0000CCCC0000CCCC, 0x3333000033330000 }, // 1 4 
            { 0xCCCCCCCC33333333, 0x00000000CCCCCCCC, 0x3333333300000000 }  // 1 5 
        },
        { 
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 2 0  
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 2 1  
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 2 2 
            { 0xF00FF00FF00FF00F, 0x00F000F000F000F0, 0x0F000F000F000F00 }, // 2 3 
            { 0xF0F00F0FF0F00F0F, 0x0000F0F00000F0F0, 0x0F0F00000F0F0000 }, // 2 4 
            { 0xF0F0F0F00F0F0F0F, 0x00000000F0F0F0F0, 0x0F0F0F0F00000000 }  // 2 5 
        },
        { 
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 3 0  
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 3 1  
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 3 2 
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 3 3 
            { 0xFF0000FFFF0000FF, 0x0000FF000000FF00, 0x00FF000000FF0000 }, // 3 4 
            { 0xFF00FF0000FF00FF, 0x00000000FF00FF00, 0x00FF00FF00000000 }  // 3 5 
        },
        { 
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 4 0  
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 4 1  
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 4 2 
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 4 3 
            { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000 }, // 4 4 
            { 0xFFFF00000000FFFF, 0x00000000FFFF0000, 0x0000FFFF00000000 }  // 4 5 
        }
    };
    if ( iVar == jVar )
        return;
    if ( jVar < iVar )
        ABC_SWAP( int, iVar, jVar );
    assert( iVar < jVar && jVar < nVars );
    if ( nVars <= 6 )
    {
        word * pMasks = PPMasks[iVar][jVar];
        int shift = (1 << jVar) - (1 << iVar);
        pTruth[0] = (pTruth[0] & pMasks[0]) | ((pTruth[0] & pMasks[1]) << shift) | ((pTruth[0] & pMasks[2]) >> shift);
    }
    else
    {
        if ( jVar <= 5 )
        {
            word * pMasks = PPMasks[iVar][jVar];
            int nWords = Abc_TtWordNum(nVars);
            int w, shift = (1 << jVar) - (1 << iVar);
            for ( w = 0; w < nWords; w++ )
                pTruth[w] = (pTruth[w] & pMasks[0]) | ((pTruth[w] & pMasks[1]) << shift) | ((pTruth[w] & pMasks[2]) >> shift);
        }
        else if ( iVar <= 5 && jVar > 5 )
        {
            word low2High, high2Low;
            word * pLimit = pTruth + Abc_TtWordNum(nVars);
            int j, jStep = Abc_TtWordNum(jVar);
            int shift = 1 << iVar;
            for ( ; pTruth < pLimit; pTruth += 2*jStep )
                for ( j = 0; j < jStep; j++ )
                {
                    low2High = (pTruth[j] & s_Truths6[iVar]) >> shift;
                    high2Low = (pTruth[j+jStep] << shift) & s_Truths6[iVar];
                    pTruth[j] = (pTruth[j] & ~s_Truths6[iVar]) | high2Low;
                    pTruth[j+jStep] = (pTruth[j+jStep] & s_Truths6[iVar]) | low2High;
                }
        }
        else
        {
            word temp, * pLimit = pTruth + Abc_TtWordNum(nVars);
            int i, iStep = Abc_TtWordNum(iVar);
            int j, jStep = Abc_TtWordNum(jVar);
            for ( ; pTruth < pLimit; pTruth += 2*jStep )
                for ( i = 0; i < jStep; i += 2*iStep )
                    for ( j = 0; j < iStep; j++ )
                    {
                        temp = pTruth[iStep + i + j];
                        pTruth[iStep + i + j] = pTruth[jStep + i + j];
                        pTruth[jStep + i + j] = temp;
                    }
        }    
    }
}

static inline void Abc_TtSwapVars_( word * pTruth, int nVars, int iVar, int jVar )
{
    static word PPMasks[6][6] = {
        { 0x2222222222222222, 0x0A0A0A0A0A0A0A0A, 0x00AA00AA00AA00AA, 0x0000AAAA0000AAAA, 0x00000000AAAAAAAA, 0xAAAAAAAAAAAAAAAA },
        { 0x0000000000000000, 0x0C0C0C0C0C0C0C0C, 0x00CC00CC00CC00CC, 0x0000CCCC0000CCCC, 0x00000000CCCCCCCC, 0xCCCCCCCCCCCCCCCC },
        { 0x0000000000000000, 0x0000000000000000, 0x00F000F000F000F0, 0x0000F0F00000F0F0, 0x00000000F0F0F0F0, 0xF0F0F0F0F0F0F0F0 },
        { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000FF000000FF00, 0x00000000FF00FF00, 0xFF00FF00FF00FF00 },
        { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x00000000FFFF0000, 0xFFFF0000FFFF0000 },
        { 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xFFFFFFFF00000000 }
    };
    if ( nVars <= 6 )
    {
        int shift;
        word low2High, high2Low; 
        assert( iVar <= 5 && jVar <= 5 && iVar < jVar );
        shift = (1 << jVar) - (1 << iVar);
        low2High = (pTruth[0] & PPMasks[iVar][jVar - 1] ) << shift;
        pTruth[0] &= ~PPMasks[iVar][jVar - 1];
        high2Low = (pTruth[0] & (PPMasks[iVar][jVar - 1] << shift )) >> shift;
        pTruth[0] &= ~(PPMasks[iVar][jVar - 1] << shift);
        pTruth[0] |= low2High | high2Low;
    }
    else
    {
        word low2High, high2Low, temp;
        int nWords = Abc_TtWordNum(nVars);
        int shift, step, iStep, jStep;
        int w = 0, i = 0, j = 0;
        if ( iVar == jVar )
            return;
        if ( jVar < iVar )
            ABC_SWAP( int, iVar, jVar );
        if ( iVar <= 5 && jVar <= 5 )
        {
            shift = (1 << jVar) - (1 << iVar);
            for ( w = 0; w < nWords; w++ )
            {
                low2High = (pTruth[w] & PPMasks[iVar][jVar - 1] ) << shift;
                pTruth[w] &= ~PPMasks[iVar][jVar - 1];
                high2Low = (pTruth[w] & (PPMasks[iVar][jVar - 1] << shift )) >> shift;
                pTruth[w] &= ~(PPMasks[iVar][jVar - 1] << shift);
                pTruth[w] |= low2High | high2Low;
            }
        }
        else if ( iVar <= 5 && jVar > 5 )
        {
            step = Abc_TtWordNum(jVar + 1)/2;
            shift = 1 << iVar;
            for ( w = 0; w < nWords; w += 2*step )
            {
                for (j = 0; j < step; j++)
                {
                    low2High = (pTruth[w + j] & PPMasks[iVar][5]) >> shift;
                    pTruth[w + j] &= ~PPMasks[iVar][5];
                    high2Low = (pTruth[w + step + j] & (PPMasks[iVar][5] >> shift)) << shift;
                    pTruth[w + step + j] &= ~(PPMasks[iVar][5] >> shift);
                    pTruth[w + j] |= high2Low;
                    pTruth[w + step + j] |= low2High;            
                }
            }
        }
        else
        {
            iStep = Abc_TtWordNum(iVar + 1)/2;
            jStep = Abc_TtWordNum(jVar + 1)/2;
            for (w = 0; w < nWords; w += 2*jStep)
            {
                for (i = 0; i < jStep; i += 2*iStep)
                {
                    for (j = 0; j < iStep; j++)
                    {
                        temp = pTruth[w + iStep + i + j];
                        pTruth[w + iStep + i + j] = pTruth[w + jStep + i + j];
                        pTruth[w + jStep + i + j] = temp;
                    }
                }
            }
        }    
    }
}



/**Function*************************************************************

  Synopsis    [Stretch truthtable to have more input variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_TtStretch5( unsigned * pInOut, int nVarS, int nVarB )
{
    int w, i, step, nWords;
    if ( nVarS == nVarB )
        return;
    assert( nVarS < nVarB );
    step = Abc_TruthWordNum(nVarS);
    nWords = Abc_TruthWordNum(nVarB);
    if ( step == nWords )
        return;
    assert( step < nWords );
    for ( w = 0; w < nWords; w += step )
        for ( i = 0; i < step; i++ )
            pInOut[w + i] = pInOut[i];              
}
static void Abc_TtStretch6( word * pInOut, int nVarS, int nVarB )
{
    int w, i, step, nWords;
    if ( nVarS == nVarB )
        return;
    assert( nVarS < nVarB );
    step = Abc_Truth6WordNum(nVarS);
    nWords = Abc_Truth6WordNum(nVarB);
    if ( step == nWords )
        return;
    assert( step < nWords );
    for ( w = 0; w < nWords; w += step )
        for ( i = 0; i < step; i++ )
            pInOut[w + i] = pInOut[i];              
}

/*=== utilTruth.c ===========================================================*/


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
