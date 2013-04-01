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
    ABC_CONST(0xAAAAAAAAAAAAAAAA),
    ABC_CONST(0xCCCCCCCCCCCCCCCC),
    ABC_CONST(0xF0F0F0F0F0F0F0F0),
    ABC_CONST(0xFF00FF00FF00FF00),
    ABC_CONST(0xFFFF0000FFFF0000),
    ABC_CONST(0xFFFFFFFF00000000)
};

static word s_Truths6Neg[6] = {
    ABC_CONST(0x5555555555555555),
    ABC_CONST(0x3333333333333333),
    ABC_CONST(0x0F0F0F0F0F0F0F0F),
    ABC_CONST(0x00FF00FF00FF00FF),
    ABC_CONST(0x0000FFFF0000FFFF),
    ABC_CONST(0x00000000FFFFFFFF)
};

static word s_PMasks[5][3] = {
    { ABC_CONST(0x9999999999999999), ABC_CONST(0x2222222222222222), ABC_CONST(0x4444444444444444) },
    { ABC_CONST(0xC3C3C3C3C3C3C3C3), ABC_CONST(0x0C0C0C0C0C0C0C0C), ABC_CONST(0x3030303030303030) },
    { ABC_CONST(0xF00FF00FF00FF00F), ABC_CONST(0x00F000F000F000F0), ABC_CONST(0x0F000F000F000F00) },
    { ABC_CONST(0xFF0000FFFF0000FF), ABC_CONST(0x0000FF000000FF00), ABC_CONST(0x00FF000000FF0000) },
    { ABC_CONST(0xFFFF00000000FFFF), ABC_CONST(0x00000000FFFF0000), ABC_CONST(0x0000FFFF00000000) }
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
// read/write/flip i-th bit of a bit string table:
static inline int     Abc_TtGetBit( word * p, int i )         { return (int)(p[i>>6] >> (i & 63)) & 1;        }
static inline void    Abc_TtSetBit( word * p, int i )         { p[i>>6] |= (((word)1)<<(i & 63));             }
static inline void    Abc_TtXorBit( word * p, int i )         { p[i>>6] ^= (((word)1)<<(i & 63));             }

// read/write k-th digit d of a hexadecimal number:
static inline int     Abc_TtGetHex( word * p, int k )         { return (int)(p[k>>4] >> ((k<<2) & 63)) & 15;  }
static inline void    Abc_TtSetHex( word * p, int k, int d )  { p[k>>4] |= (((word)d)<<((k<<2) & 63));        }
static inline void    Abc_TtXorHex( word * p, int k, int d )  { p[k>>4] ^= (((word)d)<<((k<<2) & 63));        }

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int  Abc_TtWordNum( int nVars )     { return nVars <= 6 ? 1 : 1 << (nVars-6); }
static inline int  Abc_TtByteNum( int nVars )     { return nVars <= 3 ? 1 : 1 << (nVars-3); }
static inline int  Abc_TtHexDigitNum( int nVars ) { return nVars <= 2 ? 1 : 1 << (nVars-2); }

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_TtClear( word * pOut, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pOut[w] = 0;
}
static inline void Abc_TtFill( word * pOut, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pOut[w] = ~(word)0;
}
static inline void Abc_TtNot( word * pOut, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pOut[w] = ~pOut[w];
}
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
static inline void Abc_TtSharp( word * pOut, word * pIn1, word * pIn2, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pOut[w] = pIn1[w] & ~pIn2[w];
}
static inline void Abc_TtOr( word * pOut, word * pIn1, word * pIn2, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pOut[w] = pIn1[w] | pIn2[w];
}
static inline void Abc_TtXor( word * pOut, word * pIn1, word * pIn2, int nWords, int fCompl )
{
    int w;
    if ( fCompl )
        for ( w = 0; w < nWords; w++ )
            pOut[w] = pIn1[w] ^ ~pIn2[w];
    else
        for ( w = 0; w < nWords; w++ )
            pOut[w] = pIn1[w] ^ pIn2[w];
}
static inline void Abc_TtMux( word * pOut, word * pCtrl, word * pIn1, word * pIn0, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pOut[w] = (pCtrl[w] & pIn1[w]) | (~pCtrl[w] & pIn0[w]);
}
static inline int Abc_TtEqual( word * pIn1, word * pIn2, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        if ( pIn1[w] != pIn2[w] )
            return 0;
    return 1;
}
static inline int Abc_TtCompare( word * pIn1, word * pIn2, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        if ( pIn1[w] != pIn2[w] )
            return (pIn1[w] < pIn2[w]) ? -1 : 1;
    return 0;
}
static inline int Abc_TtCompareRev( word * pIn1, word * pIn2, int nWords )
{
    int w;
    for ( w = nWords - 1; w >= 0; w-- )
        if ( pIn1[w] != pIn2[w] )
            return (pIn1[w] < pIn2[w]) ? -1 : 1;
    return 0;
}
static inline int Abc_TtIsConst0( word * pIn1, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        if ( pIn1[w] )
            return 0;
    return 1;
}
static inline int Abc_TtIsConst1( word * pIn1, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        if ( ~pIn1[w] )
            return 0;
    return 1;
}
static inline void Abc_TtConst0( word * pIn1, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pIn1[w] = 0;
}
static inline void Abc_TtConst1( word * pIn1, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pIn1[w] = ~(word)0;
}

/**Function*************************************************************

  Synopsis    [Compute elementary truth tables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_TtElemInit( word ** pTtElems, int nVars )
{
    int i, k, nWords = Abc_TtWordNum( nVars );
    for ( i = 0; i < nVars; i++ )
        if ( i < 6 )
            for ( k = 0; k < nWords; k++ )
                pTtElems[i][k] = s_Truths6[i];
        else
            for ( k = 0; k < nWords; k++ )
                pTtElems[i][k] = (k & (1 << (i-6))) ? ~(word)0 : 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Abc_Tt6Cofactor0( word t, int iVar )
{
    assert( iVar >= 0 && iVar < 6 );
    return (t &s_Truths6Neg[iVar]) | ((t &s_Truths6Neg[iVar]) << (1<<iVar));
}
static inline word Abc_Tt6Cofactor1( word t, int iVar )
{
    assert( iVar >= 0 && iVar < 6 );
    return (t & s_Truths6[iVar]) | ((t & s_Truths6[iVar]) >> (1<<iVar));
}

static inline void Abc_TtCofactor0p( word * pOut, word * pIn, int nWords, int iVar )
{
    if ( nWords == 1 )
        pOut[0] = ((pIn[0] & s_Truths6Neg[iVar]) << (1 << iVar)) | (pIn[0] & s_Truths6Neg[iVar]);
    else if ( iVar <= 5 )
    {
        int w, shift = (1 << iVar);
        for ( w = 0; w < nWords; w++ )
            pOut[w] = ((pIn[w] & s_Truths6Neg[iVar]) << shift) | (pIn[w] & s_Truths6Neg[iVar]);
    }
    else // if ( iVar > 5 )
    {
        word * pLimit = pIn + nWords;
        int i, iStep = Abc_TtWordNum(iVar);
        for ( ; pIn < pLimit; pIn += 2*iStep, pOut += 2*iStep )
            for ( i = 0; i < iStep; i++ )
            {
                pOut[i]         = pIn[i];
                pOut[i + iStep] = pIn[i];
            }
    }    
}
static inline void Abc_TtCofactor1p( word * pOut, word * pIn, int nWords, int iVar )
{
    if ( nWords == 1 )
        pOut[0] = (pIn[0] & s_Truths6[iVar]) | ((pIn[0] & s_Truths6[iVar]) >> (1 << iVar));
    else if ( iVar <= 5 )
    {
        int w, shift = (1 << iVar);
        for ( w = 0; w < nWords; w++ )
            pOut[w] = (pIn[w] & s_Truths6[iVar]) | ((pIn[w] & s_Truths6[iVar]) >> shift);
    }
    else // if ( iVar > 5 )
    {
        word * pLimit = pIn + nWords;
        int i, iStep = Abc_TtWordNum(iVar);
        for ( ; pIn < pLimit; pIn += 2*iStep, pOut += 2*iStep )
            for ( i = 0; i < iStep; i++ )
            {
                pOut[i]         = pIn[i + iStep];
                pOut[i + iStep] = pIn[i + iStep];
            }
    }    
}
static inline void Abc_TtCofactor0( word * pTruth, int nWords, int iVar )
{
    if ( nWords == 1 )
        pTruth[0] = ((pTruth[0] & s_Truths6Neg[iVar]) << (1 << iVar)) | (pTruth[0] & s_Truths6Neg[iVar]);
    else if ( iVar <= 5 )
    {
        int w, shift = (1 << iVar);
        for ( w = 0; w < nWords; w++ )
            pTruth[w] = ((pTruth[w] & s_Truths6Neg[iVar]) << shift) | (pTruth[w] & s_Truths6Neg[iVar]);
    }
    else // if ( iVar > 5 )
    {
        word * pLimit = pTruth + nWords;
        int i, iStep = Abc_TtWordNum(iVar);
        for ( ; pTruth < pLimit; pTruth += 2*iStep )
            for ( i = 0; i < iStep; i++ )
                pTruth[i + iStep] = pTruth[i];
    }
}
static inline void Abc_TtCofactor1( word * pTruth, int nWords, int iVar )
{
    if ( nWords == 1 )
        pTruth[0] = (pTruth[0] & s_Truths6[iVar]) | ((pTruth[0] & s_Truths6[iVar]) >> (1 << iVar));
    else if ( iVar <= 5 )
    {
        int w, shift = (1 << iVar);
        for ( w = 0; w < nWords; w++ )
            pTruth[w] = (pTruth[w] & s_Truths6[iVar]) | ((pTruth[w] & s_Truths6[iVar]) >> shift);
    }
    else // if ( iVar > 5 )
    {
        word * pLimit = pTruth + nWords;
        int i, iStep = Abc_TtWordNum(iVar);
        for ( ; pTruth < pLimit; pTruth += 2*iStep )
            for ( i = 0; i < iStep; i++ )
                pTruth[i] = pTruth[i + iStep];
    }
}

/**Function*************************************************************

  Synopsis    [Checks pairs of cofactors w.r.t. two variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_TtCheckEqualCofs( word * pTruth, int nWords, int iVar, int jVar, int Num1, int Num2 )
{
    assert( Num1 < Num2 && Num2 < 4 );
    assert( iVar < jVar );
    if ( nWords == 1 )
    {
        word Mask = s_Truths6Neg[jVar] & s_Truths6Neg[iVar];
        int shift1 = (Num1 >> 1) * (1 << jVar) + (Num1 & 1) * (1 << iVar);
        int shift2 = (Num2 >> 1) * (1 << jVar) + (Num2 & 1) * (1 << iVar);
        return ((pTruth[0] >> shift1) & Mask) == ((pTruth[0] >> shift2) & Mask);
    }
    if ( jVar <= 5 )
    {
        word Mask = s_Truths6Neg[jVar] & s_Truths6Neg[iVar];
        int shift1 = (Num1 >> 1) * (1 << jVar) + (Num1 & 1) * (1 << iVar);
        int shift2 = (Num2 >> 1) * (1 << jVar) + (Num2 & 1) * (1 << iVar);
        int w;
        for ( w = 0; w < nWords; w++ )
            if ( ((pTruth[w] >> shift1) & Mask) != ((pTruth[w] >> shift2) & Mask) )
                return 0;
        return 1;
    }
    if ( iVar <= 5 && jVar > 5 )
    {
        word * pLimit = pTruth + nWords;
        int j, jStep = Abc_TtWordNum(jVar);
        int shift1 = (Num1 & 1) * (1 << iVar);
        int shift2 = (Num2 & 1) * (1 << iVar);
        int Offset1 = (Num1 >> 1) * jStep;
        int Offset2 = (Num2 >> 1) * jStep;
        for ( ; pTruth < pLimit; pTruth += 2*jStep )
            for ( j = 0; j < jStep; j++ )
                if ( ((pTruth[j + Offset1] >> shift1) & s_Truths6Neg[iVar]) != ((pTruth[j + Offset2] >> shift2) & s_Truths6Neg[iVar]) )
                    return 0;
        return 1;
    }
    {
        word * pLimit = pTruth + nWords;
        int j, jStep = Abc_TtWordNum(jVar);
        int i, iStep = Abc_TtWordNum(iVar);
        int Offset1 = (Num1 >> 1) * jStep + (Num1 & 1) * iStep;
        int Offset2 = (Num2 >> 1) * jStep + (Num2 & 1) * iStep;
        for ( ; pTruth < pLimit; pTruth += 2*jStep )
            for ( i = 0; i < jStep; i += 2*iStep )
                for ( j = 0; j < iStep; j++ )
                    if ( pTruth[Offset1 + i + j] != pTruth[Offset2 + i + j] )
                        return 0;
        return 1;
    }    
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_Tt6Cof0IsConst0( word t, int iVar ) { return (t & s_Truths6Neg[iVar]) == 0;                                          }
static inline int Abc_Tt6Cof0IsConst1( word t, int iVar ) { return (t & s_Truths6Neg[iVar]) == s_Truths6Neg[iVar];                         }
static inline int Abc_Tt6Cof1IsConst0( word t, int iVar ) { return (t & s_Truths6[iVar]) == 0;                                             }
static inline int Abc_Tt6Cof1IsConst1( word t, int iVar ) { return (t & s_Truths6[iVar]) == s_Truths6[iVar];                               }
static inline int Abc_Tt6CofsOpposite( word t, int iVar ) { return (~t & s_Truths6Neg[iVar]) == ((t >> (1 << iVar)) & s_Truths6Neg[iVar]); } 
static inline int Abc_Tt6Cof0EqualCof1( word t1, word t2, int iVar ) { return (t1 & s_Truths6Neg[iVar]) == ((t2 >> (1 << iVar)) & s_Truths6Neg[iVar]); } 
static inline int Abc_Tt6Cof0EqualCof0( word t1, word t2, int iVar ) { return (t1 & s_Truths6Neg[iVar]) == (t2 & s_Truths6Neg[iVar]); } 
static inline int Abc_Tt6Cof1EqualCof1( word t1, word t2, int iVar ) { return (t1 & s_Truths6[iVar])    == (t2 & s_Truths6[iVar]); } 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_TtTruthIsConst0( word * p, int nWords ) { int w; for ( w = 0; w < nWords; w++ ) if ( p[w] != 0        ) return 0; return 1; }
static inline int Abc_TtTruthIsConst1( word * p, int nWords ) { int w; for ( w = 0; w < nWords; w++ ) if ( p[w] != ~(word)0 ) return 0; return 1; }

static inline int Abc_TtCof0IsConst0( word * t, int nWords, int iVar ) 
{ 
    if ( iVar < 6 )
    {
        int i;
        for ( i = 0; i < nWords; i++ )
            if ( t[i] & s_Truths6Neg[iVar] )
                return 0;
        return 1;
    }
    else
    {
        int i, Step = (1 << (iVar - 6));
        word * tLimit = t + nWords;
        for ( ; t < tLimit; t += 2*Step )
            for ( i = 0; i < Step; i++ )
                if ( t[i] )
                    return 0;
        return 1;
    }
}
static inline int Abc_TtCof0IsConst1( word * t, int nWords, int iVar ) 
{ 
    if ( iVar < 6 )
    {
        int i;
        for ( i = 0; i < nWords; i++ )
            if ( (t[i] & s_Truths6Neg[iVar]) != s_Truths6Neg[iVar] )
                return 0;
        return 1;
    }
    else
    {
        int i, Step = (1 << (iVar - 6));
        word * tLimit = t + nWords;
        for ( ; t < tLimit; t += 2*Step )
            for ( i = 0; i < Step; i++ )
                if ( ~t[i] )
                    return 0;
        return 1;
    }
}
static inline int Abc_TtCof1IsConst0( word * t, int nWords, int iVar ) 
{ 
    if ( iVar < 6 )
    {
        int i;
        for ( i = 0; i < nWords; i++ )
            if ( t[i] & s_Truths6[iVar] )
                return 0;
        return 1;
    }
    else
    {
        int i, Step = (1 << (iVar - 6));
        word * tLimit = t + nWords;
        for ( ; t < tLimit; t += 2*Step )
            for ( i = 0; i < Step; i++ )
                if ( t[i+Step] )
                    return 0;
        return 1;
    }
}
static inline int Abc_TtCof1IsConst1( word * t, int nWords, int iVar ) 
{ 
    if ( iVar < 6 )
    {
        int i;
        for ( i = 0; i < nWords; i++ )
            if ( (t[i] & s_Truths6[iVar]) != s_Truths6[iVar] )
                return 0;
        return 1;
    }
    else
    {
        int i, Step = (1 << (iVar - 6));
        word * tLimit = t + nWords;
        for ( ; t < tLimit; t += 2*Step )
            for ( i = 0; i < Step; i++ )
                if ( ~t[i+Step] )
                    return 0;
        return 1;
    }
}
static inline int Abc_TtCofsOpposite( word * t, int nWords, int iVar ) 
{ 
    if ( iVar < 6 )
    {
        int i, Shift = (1 << iVar);
        for ( i = 0; i < nWords; i++ )
            if ( ((t[i] << Shift) & s_Truths6[iVar]) != (~t[i] & s_Truths6[iVar]) )
                return 0;
        return 1;
    }
    else
    {
        int i, Step = (1 << (iVar - 6));
        word * tLimit = t + nWords;
        for ( ; t < tLimit; t += 2*Step )
            for ( i = 0; i < Step; i++ )
                if ( t[i] != ~t[i+Step] )
                    return 0;
        return 1;
    }
}

/**Function*************************************************************

  Synopsis    [Stretch truthtable to have more input variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_TtStretch5( unsigned * pInOut, int nVarS, int nVarB )
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
static inline void Abc_TtStretch6( word * pInOut, int nVarS, int nVarB )
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
static inline word Abc_Tt6Stretch( word t, int nVars )
{
    assert( nVars >= 0 );
    if ( nVars == 0 )
        nVars++, t = (t & 0x1) | ((t & 0x1) << 1);
    if ( nVars == 1 )
        nVars++, t = (t & 0x3) | ((t & 0x3) << 2);
    if ( nVars == 2 )
        nVars++, t = (t & 0xF) | ((t & 0xF) << 4);
    if ( nVars == 3 )
        nVars++, t = (t & 0xFF) | ((t & 0xFF) << 8);
    if ( nVars == 4 )
        nVars++, t = (t & 0xFFFF) | ((t & 0xFFFF) << 16);
    if ( nVars == 5 )
        nVars++, t = (t & 0xFFFFFFFF) | ((t & 0xFFFFFFFF) << 32);
    assert( nVars == 6 );
    return t;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_TtIsHexDigit( char HexChar )
{
    return (HexChar >= '0' && HexChar <= '9') || (HexChar >= 'A' && HexChar <= 'F') || (HexChar >= 'a' && HexChar <= 'f');
}
static inline char Abc_TtPrintDigit( int Digit )
{
    assert( Digit >= 0 && Digit < 16 );
    if ( Digit < 10 )
        return '0' + Digit;
    return 'A' + Digit-10;
}
static inline int Abc_TtReadHexDigit( char HexChar )
{
    if ( HexChar >= '0' && HexChar <= '9' )
        return HexChar - '0';
    if ( HexChar >= 'A' && HexChar <= 'F' )
        return HexChar - 'A' + 10;
    if ( HexChar >= 'a' && HexChar <= 'f' )
        return HexChar - 'a' + 10;
    assert( 0 ); // not a hexadecimal symbol
    return -1; // return value which makes no sense
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_TtPrintHex( word * pTruth, int nVars )
{
    word * pThis, * pLimit = pTruth + Abc_TtWordNum(nVars);
    int k;
    assert( nVars >= 2 );
    for ( pThis = pTruth; pThis < pLimit; pThis++ )
        for ( k = 0; k < 16; k++ )
            printf( "%c", Abc_TtPrintDigit((int)(pThis[0] >> (k << 2)) & 15) );
    printf( "\n" );
}
static inline void Abc_TtPrintHexRev( FILE * pFile, word * pTruth, int nVars )
{
    word * pThis;
    int k, StartK = nVars >= 6 ? 16 : (1 << (nVars - 2));
    assert( nVars >= 2 );
    for ( pThis = pTruth + Abc_TtWordNum(nVars) - 1; pThis >= pTruth; pThis-- )
        for ( k = StartK - 1; k >= 0; k-- )
            fprintf( pFile, "%c", Abc_TtPrintDigit((int)(pThis[0] >> (k << 2)) & 15) );
//    printf( "\n" );
}
static inline void Abc_TtPrintHexSpecial( word * pTruth, int nVars )
{
    word * pThis;
    int k;
    assert( nVars >= 2 );
    for ( pThis = pTruth + Abc_TtWordNum(nVars) - 1; pThis >= pTruth; pThis-- )
        for ( k = 0; k < 16; k++ )
            printf( "%c", Abc_TtPrintDigit((int)(pThis[0] >> (k << 2)) & 15) );
    printf( "\n" );
}
static inline int Abc_TtWriteHexRev( char * pStr, word * pTruth, int nVars )
{
    word * pThis;
    char * pStrInit = pStr;
    int k, StartK = nVars >= 6 ? 16 : (1 << (nVars - 2));
    assert( nVars >= 2 );
    for ( pThis = pTruth + Abc_TtWordNum(nVars) - 1; pThis >= pTruth; pThis-- )
        for ( k = StartK - 1; k >= 0; k-- )
            *pStr++ = Abc_TtPrintDigit( (int)(pThis[0] >> (k << 2)) & 15 );
    return pStr - pStrInit;
}

/**Function*************************************************************

  Synopsis    [Reads hex truth table from a string.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_TtReadHex( word * pTruth, char * pString )
{
    int k, nVars, Digit, nDigits;
    // skip the first 2 symbols if they are "0x"
    if ( pString[0] == '0' && pString[1] == 'x' )
        pString += 2;
    // count the number of hex digits
    nDigits = 0;
    for ( k = 0; Abc_TtIsHexDigit(pString[k]); k++ )
        nDigits++;
    if ( nDigits == 1 )
    {
        if ( pString[0] == '0' || pString[0] == 'F' )
        {
            pTruth[0] = (pString[0] == '0') ? 0 : ~(word)0;
            return 0;
        }
        if ( pString[0] == '5' || pString[0] == 'A' )
        {
            pTruth[0] = (pString[0] == '5') ? s_Truths6Neg[0] : s_Truths6[0];
            return 1;
        }
    }
    // determine the number of variables
    nVars = 2 + Abc_Base2Log( nDigits );
    // clean storage
    for ( k = Abc_TtWordNum(nVars) - 1; k >= 0; k-- )
        pTruth[k] = 0;
    // read hexadecimal digits in the reverse order
    // (the last symbol in the string is the least significant digit)
    for ( k = 0; k < nDigits; k++ )
    {
        Digit = Abc_TtReadHexDigit( pString[nDigits - 1 - k] );
        assert( Digit >= 0 && Digit < 16 );
        Abc_TtSetHex( pTruth, k, Digit );
    }
    if ( nVars < 6 )
        pTruth[0] = Abc_Tt6Stretch( pTruth[0], nVars );
    return nVars;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_TtPrintBinary( word * pTruth, int nVars )
{
    word * pThis, * pLimit = pTruth + Abc_TtWordNum(nVars);
    int k, Limit = Abc_MinInt( 64, (1 << nVars) );
    assert( nVars >= 2 );
    for ( pThis = pTruth; pThis < pLimit; pThis++ )
        for ( k = 0; k < Limit; k++ )
            printf( "%d", Abc_InfoHasBit( (unsigned *)pThis, k ) );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_TtSuppFindFirst( int Supp )
{
    int i;
    assert( Supp > 0 );
    for ( i = 0; i < 32; i++ )
        if ( Supp & (1 << i) )
            return i;
    return -1;
}
static inline int Abc_TtSuppOnlyOne( int Supp )
{
    if ( Supp == 0 )
        return 0;
    return (Supp & (Supp-1)) == 0;
}
static inline int Abc_TtSuppIsMinBase( int Supp )
{
    assert( Supp > 0 );
    return (Supp & (Supp+1)) == 0;
}
static inline int Abc_Tt6HasVar( word t, int iVar )
{
    return ((t >> (1<<iVar)) & s_Truths6Neg[iVar]) != (t & s_Truths6Neg[iVar]);
}
static inline int Abc_TtHasVar( word * t, int nVars, int iVar )
{
    assert( iVar < nVars );
    if ( nVars <= 6 )
        return Abc_Tt6HasVar( t[0], iVar );
    if ( iVar < 6 )
    {
        int i, Shift = (1 << iVar);
        int nWords = Abc_TtWordNum( nVars );
        for ( i = 0; i < nWords; i++ )
            if ( ((t[i] >> Shift) & s_Truths6Neg[iVar]) != (t[i] & s_Truths6Neg[iVar]) )
                return 1;
        return 0;
    }
    else
    {
        int i, Step = (1 << (iVar - 6));
        word * tLimit = t + Abc_TtWordNum( nVars );
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
static inline word Abc_Tt6Flip( word Truth, int iVar )
{
    return Truth = ((Truth << (1 << iVar)) & s_Truths6[iVar]) | ((Truth & s_Truths6[iVar]) >> (1 << iVar));
}
static inline void Abc_TtFlip( word * pTruth, int nWords, int iVar )
{
    if ( nWords == 1 )
        pTruth[0] = ((pTruth[0] << (1 << iVar)) & s_Truths6[iVar]) | ((pTruth[0] & s_Truths6[iVar]) >> (1 << iVar));
    else if ( iVar <= 5 )
    {
        int w, shift = (1 << iVar);
        for ( w = 0; w < nWords; w++ )
            pTruth[w] = ((pTruth[w] << shift) & s_Truths6[iVar]) | ((pTruth[w] & s_Truths6[iVar]) >> shift);
    }
    else // if ( iVar > 5 )
    {
        word * pLimit = pTruth + nWords;
        int i, iStep = Abc_TtWordNum(iVar);
        for ( ; pTruth < pLimit; pTruth += 2*iStep )
            for ( i = 0; i < iStep; i++ )
                ABC_SWAP( word, pTruth[i], pTruth[i + iStep] );
    }    
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Abc_Tt6SwapAdjacent( word Truth, int iVar )
{
    return (Truth & s_PMasks[iVar][0]) | ((Truth & s_PMasks[iVar][1]) << (1 << iVar)) | ((Truth & s_PMasks[iVar][2]) >> (1 << iVar));
}
static inline void Abc_TtSwapAdjacent( word * pTruth, int nWords, int iVar )
{
    static word s_PMasks[5][3] = {
        { ABC_CONST(0x9999999999999999), ABC_CONST(0x2222222222222222), ABC_CONST(0x4444444444444444) },
        { ABC_CONST(0xC3C3C3C3C3C3C3C3), ABC_CONST(0x0C0C0C0C0C0C0C0C), ABC_CONST(0x3030303030303030) },
        { ABC_CONST(0xF00FF00FF00FF00F), ABC_CONST(0x00F000F000F000F0), ABC_CONST(0x0F000F000F000F00) },
        { ABC_CONST(0xFF0000FFFF0000FF), ABC_CONST(0x0000FF000000FF00), ABC_CONST(0x00FF000000FF0000) },
        { ABC_CONST(0xFFFF00000000FFFF), ABC_CONST(0x00000000FFFF0000), ABC_CONST(0x0000FFFF00000000) }
    };
    if ( iVar < 5 )
    {
        int i, Shift = (1 << iVar);
        for ( i = 0; i < nWords; i++ )
            pTruth[i] = (pTruth[i] & s_PMasks[iVar][0]) | ((pTruth[i] & s_PMasks[iVar][1]) << Shift) | ((pTruth[i] & s_PMasks[iVar][2]) >> Shift);
    }
    else if ( iVar == 5 )
    {
        unsigned * pTruthU = (unsigned *)pTruth;
        unsigned * pLimitU = (unsigned *)(pTruth + nWords);
        for ( ; pTruthU < pLimitU; pTruthU += 4 )
            ABC_SWAP( unsigned, pTruthU[1], pTruthU[2] );
    }
    else // if ( iVar > 5 )
    {
        word * pLimit = pTruth + nWords;
        int i, iStep = Abc_TtWordNum(iVar);
        for ( ; pTruth < pLimit; pTruth += 4*iStep )
            for ( i = 0; i < iStep; i++ )
                ABC_SWAP( word, pTruth[i + iStep], pTruth[i + 2*iStep] );
    }
}
static inline void Abc_TtSwapVars( word * pTruth, int nVars, int iVar, int jVar )
{
    static word Ps_PMasks[5][6][3] = {
        { 
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 0 0  
            { ABC_CONST(0x9999999999999999), ABC_CONST(0x2222222222222222), ABC_CONST(0x4444444444444444) }, // 0 1  
            { ABC_CONST(0xA5A5A5A5A5A5A5A5), ABC_CONST(0x0A0A0A0A0A0A0A0A), ABC_CONST(0x5050505050505050) }, // 0 2 
            { ABC_CONST(0xAA55AA55AA55AA55), ABC_CONST(0x00AA00AA00AA00AA), ABC_CONST(0x5500550055005500) }, // 0 3 
            { ABC_CONST(0xAAAA5555AAAA5555), ABC_CONST(0x0000AAAA0000AAAA), ABC_CONST(0x5555000055550000) }, // 0 4 
            { ABC_CONST(0xAAAAAAAA55555555), ABC_CONST(0x00000000AAAAAAAA), ABC_CONST(0x5555555500000000) }  // 0 5 
        },
        { 
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 1 0  
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 1 1  
            { ABC_CONST(0xC3C3C3C3C3C3C3C3), ABC_CONST(0x0C0C0C0C0C0C0C0C), ABC_CONST(0x3030303030303030) }, // 1 2 
            { ABC_CONST(0xCC33CC33CC33CC33), ABC_CONST(0x00CC00CC00CC00CC), ABC_CONST(0x3300330033003300) }, // 1 3 
            { ABC_CONST(0xCCCC3333CCCC3333), ABC_CONST(0x0000CCCC0000CCCC), ABC_CONST(0x3333000033330000) }, // 1 4 
            { ABC_CONST(0xCCCCCCCC33333333), ABC_CONST(0x00000000CCCCCCCC), ABC_CONST(0x3333333300000000) }  // 1 5 
        },
        { 
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 2 0  
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 2 1  
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 2 2 
            { ABC_CONST(0xF00FF00FF00FF00F), ABC_CONST(0x00F000F000F000F0), ABC_CONST(0x0F000F000F000F00) }, // 2 3 
            { ABC_CONST(0xF0F00F0FF0F00F0F), ABC_CONST(0x0000F0F00000F0F0), ABC_CONST(0x0F0F00000F0F0000) }, // 2 4 
            { ABC_CONST(0xF0F0F0F00F0F0F0F), ABC_CONST(0x00000000F0F0F0F0), ABC_CONST(0x0F0F0F0F00000000) }  // 2 5 
        },
        { 
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 3 0  
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 3 1  
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 3 2 
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 3 3 
            { ABC_CONST(0xFF0000FFFF0000FF), ABC_CONST(0x0000FF000000FF00), ABC_CONST(0x00FF000000FF0000) }, // 3 4 
            { ABC_CONST(0xFF00FF0000FF00FF), ABC_CONST(0x00000000FF00FF00), ABC_CONST(0x00FF00FF00000000) }  // 3 5 
        },
        { 
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 4 0  
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 4 1  
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 4 2 
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 4 3 
            { ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000), ABC_CONST(0x0000000000000000) }, // 4 4 
            { ABC_CONST(0xFFFF00000000FFFF), ABC_CONST(0x00000000FFFF0000), ABC_CONST(0x0000FFFF00000000) }  // 4 5 
        }
    };
    if ( iVar == jVar )
        return;
    if ( jVar < iVar )
        ABC_SWAP( int, iVar, jVar );
    assert( iVar < jVar && jVar < nVars );
    if ( nVars <= 6 )
    {
        word * s_PMasks = Ps_PMasks[iVar][jVar];
        int shift = (1 << jVar) - (1 << iVar);
        pTruth[0] = (pTruth[0] & s_PMasks[0]) | ((pTruth[0] & s_PMasks[1]) << shift) | ((pTruth[0] & s_PMasks[2]) >> shift);
        return;
    }
    if ( jVar <= 5 )
    {
        word * s_PMasks = Ps_PMasks[iVar][jVar];
        int nWords = Abc_TtWordNum(nVars);
        int w, shift = (1 << jVar) - (1 << iVar);
        for ( w = 0; w < nWords; w++ )
            pTruth[w] = (pTruth[w] & s_PMasks[0]) | ((pTruth[w] & s_PMasks[1]) << shift) | ((pTruth[w] & s_PMasks[2]) >> shift);
        return;
    }
    if ( iVar <= 5 && jVar > 5 )
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
        return;
    }
    {
        word * pLimit = pTruth + Abc_TtWordNum(nVars);
        int i, iStep = Abc_TtWordNum(iVar);
        int j, jStep = Abc_TtWordNum(jVar);
        for ( ; pTruth < pLimit; pTruth += 2*jStep )
            for ( i = 0; i < jStep; i += 2*iStep )
                for ( j = 0; j < iStep; j++ )
                    ABC_SWAP( word, pTruth[iStep + i + j], pTruth[jStep + i + j] );
        return;
    }    
}

/**Function*************************************************************

  Synopsis    [Implemeting given NPN config.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_TtImplementNpnConfig( word * pTruth, int nVars, char * pCanonPerm, unsigned uCanonPhase )
{
    int i, k, nWords = Abc_TtWordNum( nVars );
    if ( (uCanonPhase >> nVars) & 1 )
        Abc_TtNot( pTruth, nWords );
    for ( i = 0; i < nVars; i++ )
        if ( (uCanonPhase >> i) & 1 )
            Abc_TtFlip( pTruth, nWords, i );
    for ( i = 0; i < nVars; i++ )
    {
        for ( k = i; k < nVars; k++ )
            if ( pCanonPerm[k] == i )
                break;
        assert( k < nVars );
        if ( i == k )
            continue;
        Abc_TtSwapVars( pTruth, nVars, i, k );
        ABC_SWAP( int, pCanonPerm[i], pCanonPerm[k] );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_TtCountOnesSlow( word t )
{
    t =    (t & ABC_CONST(0x5555555555555555)) + ((t>> 1) & ABC_CONST(0x5555555555555555));
    t =    (t & ABC_CONST(0x3333333333333333)) + ((t>> 2) & ABC_CONST(0x3333333333333333));
    t =    (t & ABC_CONST(0x0F0F0F0F0F0F0F0F)) + ((t>> 4) & ABC_CONST(0x0F0F0F0F0F0F0F0F));
    t =    (t & ABC_CONST(0x00FF00FF00FF00FF)) + ((t>> 8) & ABC_CONST(0x00FF00FF00FF00FF));
    t =    (t & ABC_CONST(0x0000FFFF0000FFFF)) + ((t>>16) & ABC_CONST(0x0000FFFF0000FFFF));
    return (t & ABC_CONST(0x00000000FFFFFFFF)) +  (t>>32);
}
static inline int Abc_TtCountOnes( word x )
{
    x = x - ((x >> 1) & ABC_CONST(0x5555555555555555));   
    x = (x & ABC_CONST(0x3333333333333333)) + ((x >> 2) & ABC_CONST(0x3333333333333333));    
    x = (x + (x >> 4)) & ABC_CONST(0x0F0F0F0F0F0F0F0F);    
    x = x + (x >> 8);
    x = x + (x >> 16);
    x = x + (x >> 32); 
    return (int)(x & 0xFF);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_Tt6FirstBit( word t )
{
    int n = 0;
    if ( t == 0 ) return -1;
    if ( (t & 0x00000000FFFFFFFF) == 0 ) { n += 32; t >>= 32; }
    if ( (t & 0x000000000000FFFF) == 0 ) { n += 16; t >>= 16; }
    if ( (t & 0x00000000000000FF) == 0 ) { n +=  8; t >>=  8; }
    if ( (t & 0x000000000000000F) == 0 ) { n +=  4; t >>=  4; }
    if ( (t & 0x0000000000000003) == 0 ) { n +=  2; t >>=  2; }
    if ( (t & 0x0000000000000001) == 0 ) { n++; }
    return n;
}
static inline int Abc_Tt6LastBit( word t )
{
    int n = 0;
    if ( t == 0 ) return -1;
    if ( (t & 0xFFFFFFFF00000000) == 0 ) { n += 32; t <<= 32; }
    if ( (t & 0xFFFF000000000000) == 0 ) { n += 16; t <<= 16; }
    if ( (t & 0xFF00000000000000) == 0 ) { n +=  8; t <<=  8; }
    if ( (t & 0xF000000000000000) == 0 ) { n +=  4; t <<=  4; }
    if ( (t & 0xC000000000000000) == 0 ) { n +=  2; t <<=  2; }
    if ( (t & 0x8000000000000000) == 0 ) { n++; }
    return 63-n;
}
static inline int Abc_TtFindFirstBit( word * pIn, int nVars )
{
    int w, nWords = Abc_TtWordNum(nVars);
    for ( w = 0; w < nWords; w++ )
        if ( pIn[w] )
            return 64*w + Abc_Tt6FirstBit(pIn[w]);
    return -1;
}
static inline int Abc_TtFindFirstZero( word * pIn, int nVars )
{
    int w, nWords = Abc_TtWordNum(nVars);
    for ( w = 0; w < nWords; w++ )
        if ( ~pIn[w] )
            return 64*w + Abc_Tt6FirstBit(~pIn[w]);
    return -1;
}
static inline int Abc_TtFindLastBit( word * pIn, int nVars )
{
    int w, nWords = Abc_TtWordNum(nVars);
    for ( w = nWords - 1; w >= 0; w-- )
        if ( pIn[w] )
            return 64*w + Abc_Tt6LastBit(pIn[w]);
    return -1;
}
static inline int Abc_TtFindLastZero( word * pIn, int nVars )
{
    int w, nWords = Abc_TtWordNum(nVars);
    for ( w = nWords - 1; w >= 0; w-- )
        if ( ~pIn[w] )
            return 64*w + Abc_Tt6LastBit(~pIn[w]);
    return -1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_TtReverseVars( word * pTruth, int nVars )
{
    int k;
    for ( k = 0; k < nVars/2 ; k++ )
        Abc_TtSwapVars( pTruth, nVars, k, nVars - 1 - k );
}
static inline void Abc_TtReverseBits( word * pTruth, int nVars )
{
    static unsigned char pMirror[256] = {
          0, 128,  64, 192,  32, 160,  96, 224,  16, 144,  80, 208,  48, 176, 112, 240,
          8, 136,  72, 200,  40, 168, 104, 232,  24, 152,  88, 216,  56, 184, 120, 248,
          4, 132,  68, 196,  36, 164, 100, 228,  20, 148,  84, 212,  52, 180, 116, 244,
         12, 140,  76, 204,  44, 172, 108, 236,  28, 156,  92, 220,  60, 188, 124, 252,
          2, 130,  66, 194,  34, 162,  98, 226,  18, 146,  82, 210,  50, 178, 114, 242,
         10, 138,  74, 202,  42, 170, 106, 234,  26, 154,  90, 218,  58, 186, 122, 250,
          6, 134,  70, 198,  38, 166, 102, 230,  22, 150,  86, 214,  54, 182, 118, 246,
         14, 142,  78, 206,  46, 174, 110, 238,  30, 158,  94, 222,  62, 190, 126, 254,
          1, 129,  65, 193,  33, 161,  97, 225,  17, 145,  81, 209,  49, 177, 113, 241,
          9, 137,  73, 201,  41, 169, 105, 233,  25, 153,  89, 217,  57, 185, 121, 249,
          5, 133,  69, 197,  37, 165, 101, 229,  21, 149,  85, 213,  53, 181, 117, 245,
         13, 141,  77, 205,  45, 173, 109, 237,  29, 157,  93, 221,  61, 189, 125, 253,
          3, 131,  67, 195,  35, 163,  99, 227,  19, 147,  83, 211,  51, 179, 115, 243,
         11, 139,  75, 203,  43, 171, 107, 235,  27, 155,  91, 219,  59, 187, 123, 251,
          7, 135,  71, 199,  39, 167, 103, 231,  23, 151,  87, 215,  55, 183, 119, 247,
         15, 143,  79, 207,  47, 175, 111, 239,  31, 159,  95, 223,  63, 191, 127, 255
    };
    unsigned char Temp, * pTruthC = (unsigned char *)pTruth;
    int i, nBytes = (nVars > 6) ? (1 << (nVars - 3)) : 8;
    for ( i = 0; i < nBytes/2; i++ )
    {
        Temp = pMirror[pTruthC[i]];
        pTruthC[i] = pMirror[pTruthC[nBytes-1-i]];
        pTruthC[nBytes-1-i] = Temp;
    }
}


/**Function*************************************************************

  Synopsis    [Computes ISOP for 6 variables or less.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Abc_Tt6Isop( word uOn, word uOnDc, int nVars )
{
    word uOn0, uOn1, uOnDc0, uOnDc1, uRes0, uRes1, uRes2;
    int Var;
    assert( nVars <= 5 );
    assert( (uOn & ~uOnDc) == 0 );
    if ( uOn == 0 )
        return 0;
    if ( uOnDc == ~(word)0 )
        return ~(word)0;
    assert( nVars > 0 );
    // find the topmost var
    for ( Var = nVars-1; Var >= 0; Var-- )
        if ( Abc_Tt6HasVar( uOn, Var ) || Abc_Tt6HasVar( uOnDc, Var ) )
             break;
    assert( Var >= 0 );
    // cofactor
    uOn0   = Abc_Tt6Cofactor0( uOn,   Var );
    uOn1   = Abc_Tt6Cofactor1( uOn  , Var );
    uOnDc0 = Abc_Tt6Cofactor0( uOnDc, Var );
    uOnDc1 = Abc_Tt6Cofactor1( uOnDc, Var );
    // solve for cofactors
    uRes0 = Abc_Tt6Isop( uOn0 & ~uOnDc1, uOnDc0, Var );
    uRes1 = Abc_Tt6Isop( uOn1 & ~uOnDc0, uOnDc1, Var );
    uRes2 = Abc_Tt6Isop( (uOn0 & ~uRes0) | (uOn1 & ~uRes1), uOnDc0 & uOnDc1, Var );
    // derive the final truth table
    uRes2 |= (uRes0 & s_Truths6Neg[Var]) | (uRes1 & s_Truths6[Var]);
    assert( (uOn & ~uRes2) == 0 );
    assert( (uRes2 & ~uOnDc) == 0 );
    return uRes2;
}

/*=== utilTruth.c ===========================================================*/


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
