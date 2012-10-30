/**CFile****************************************************************

  FileName    [dauDsd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware unmapping.]

  Synopsis    [Disjoint-support decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: dauDsd.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dauInt.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define DAU_MAX_STR 300

static word s_Truth6[6] = 
{
    0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000
};

/* 
    This code performs truth-table-based decomposition for 6-variable functions.
    Representation of operations:
    ! = not; 
    (ab) = a and b;  
    [ab] = a xor b;  
    <abc> = ITE( a, b, c )
*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes truth table for the DSD formula.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Dau_DsdFindMatch( char * p )
{
    int Counter = 0;
    assert( *p == '(' || *p == '[' || *p == '<' );
    while ( *p )
    {
        if ( *p == '(' || *p == '[' || *p == '<' )
            Counter++;
        else if ( *p == ')' || *p == ']' || *p == '>' )
            Counter--;
        if ( Counter == 0 )
            return p;
        p++;
    }
    return NULL;
}
word Dau_DsdToTruth_rec( char ** p )
{
    int fCompl = 0;
    if ( **p == '!' )
        (*p)++, fCompl = 1;
    if ( **p >= 'a' && **p <= 'f' )
        return fCompl ? ~s_Truth6[**p - 'a'] : s_Truth6[**p - 'a'];
    if ( **p == '(' || **p == '[' || **p == '<' )
    {
        word Res = 0;
        char * q = Dau_DsdFindMatch( *p );
        assert( q != NULL );
        assert( (**p == '(') == (*q == ')') );
        assert( (**p == '[') == (*q == ']') );
        assert( (**p == '<') == (*q == '>') );
        if ( **p == '(' ) // and/or
        {
            Res = ~(word)0;
            for ( (*p)++; *p < q; (*p)++ )
                Res &= Dau_DsdToTruth_rec( p );
        }
        else if ( **p == '[' ) // xor
        {
            Res = 0;
            for ( (*p)++; *p < q; (*p)++ )
                Res ^= Dau_DsdToTruth_rec( p );
        }
        else if ( **p == '<' ) // mux
        {
            word Temp[3], * pTemp = Temp;
            for ( (*p)++; *p < q; (*p)++ )
                *pTemp++ = Dau_DsdToTruth_rec( p );
            assert( pTemp == Temp + 3 );
            Res = (Temp[0] & Temp[1]) | (~Temp[0] & Temp[2]);
        }
        else assert( 0 );
        assert( *p == q );
        return fCompl ? ~Res : Res;
    }
    assert( 0 );
    return 0;
}
word Dau_DsdToTruth( char * p )
{
    word Res;
    if ( *p == '0' )
        Res = 0;
    else if ( *p == '1' )
        Res = ~(word)0;
    else
        Res = Dau_DsdToTruth_rec( &p );
    assert( *++p == 0 );
    return Res;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dau_DsdTest2()
{
//    char * p = Abc_UtilStrsav( "!(ab!(de[cf]))" );
//    char * p = Abc_UtilStrsav( "!(a![d<ecf>]b)" );
//    word t = Dau_DsdToTruth( p );
}



/**Function*************************************************************

  Synopsis    [Performs DSD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Dau_DsdCof0( word t, int iVar )
{
    assert( iVar >= 0 && iVar < 6 );
    return (t &~s_Truth6[iVar]) | ((t &~s_Truth6[iVar]) << (1<<iVar));
}
static inline word Dau_DsdCof1( word t, int iVar )
{
    assert( iVar >= 0 && iVar < 6 );
    return (t & s_Truth6[iVar]) | ((t & s_Truth6[iVar]) >> (1<<iVar));
}
static inline word Dau_DsdVarPres( word t, int iVar )
{
    assert( iVar >= 0 && iVar < 6 );
    return (t & s_Truth6[iVar]) != ((t << (1<<iVar)) & s_Truth6[iVar]);
}
static inline int Dau_DsdPerformReplace( char * pBuffer, int PosStart, int Pos, int Symb, char * pNext )
{
    static char pTemp[DAU_MAX_STR+20];
    char * pCur = pTemp;
    int i, k, RetValue;
    for ( i = PosStart; i < Pos; i++ )
        if ( pBuffer[i] != Symb )
            *pCur++ = pBuffer[i];
        else
            for ( k = 0; pNext[k]; k++ )
                *pCur++ = pNext[k];
    RetValue = PosStart + (pCur - pTemp);
    for ( i = PosStart; i < RetValue; i++ )
        pBuffer[i] = pTemp[i-PosStart];
    return RetValue;
}
int Dau_DsdPerform_rec( word t, char * pBuffer, int Pos, int * pVars, int nVars )
{
    char pNest[10];
    word Cof0[6], Cof1[6], Cof[4];
    int pVarsNew[6], nVarsNew, PosStart;
    int v, u, vBest, CountBest;
    assert( Pos < DAU_MAX_STR );
    // perform support minimization
    nVarsNew = 0;
    for ( v = 0; v < nVars; v++ )
        if ( Dau_DsdVarPres( t, pVars[v] ) )
            pVarsNew[ nVarsNew++ ] = pVars[v];
    assert( nVarsNew > 0 );
    // special case when function is a var
    if ( nVarsNew == 1 )
    {
        if ( t == s_Truth6[ pVarsNew[0] ] )
        {
            pBuffer[Pos++] = 'a' +  pVarsNew[0];
            return Pos;
        }
        if ( t == ~s_Truth6[ pVarsNew[0] ] )
        {
            pBuffer[Pos++] = '!';
            pBuffer[Pos++] = 'a' +  pVarsNew[0];
            return Pos;
        }
        assert( 0 );
        return Pos;
    }
    // decompose on the output side
    for ( v = 0; v < nVarsNew; v++ )
    {
        Cof0[v] = Dau_DsdCof0( t, pVarsNew[v] );
        Cof1[v] = Dau_DsdCof1( t, pVarsNew[v] );
        assert( Cof0[v] != Cof1[v] );
        if ( Cof0[v] == 0 ) // ax
        {
            pBuffer[Pos++] = '(';
            pBuffer[Pos++] = 'a' + pVarsNew[v];
            Pos = Dau_DsdPerform_rec( Cof1[v], pBuffer, Pos, pVarsNew, nVarsNew );
            pBuffer[Pos++] = ')';
            return Pos;
        }
        if ( Cof0[v] == ~(word)0 ) // !(ax)
        {
            pBuffer[Pos++] = '!';
            pBuffer[Pos++] = '(';
            pBuffer[Pos++] = 'a' + pVarsNew[v];
            Pos = Dau_DsdPerform_rec( ~Cof1[v], pBuffer, Pos, pVarsNew, nVarsNew );
            pBuffer[Pos++] = ')';
            return Pos;
        }
        if ( Cof1[v] == 0 ) // !ax
        {
            pBuffer[Pos++] = '(';
            pBuffer[Pos++] = '!';
            pBuffer[Pos++] = 'a' + pVarsNew[v];
            Pos = Dau_DsdPerform_rec( Cof0[v], pBuffer, Pos, pVarsNew, nVarsNew );
            pBuffer[Pos++] = ')';
            return Pos;
        }
        if ( Cof1[v] == ~(word)0 ) // !(!ax)
        {
            pBuffer[Pos++] = '!';
            pBuffer[Pos++] = '(';
            pBuffer[Pos++] = '!';
            pBuffer[Pos++] = 'a' + pVarsNew[v];
            Pos = Dau_DsdPerform_rec( ~Cof0[v], pBuffer, Pos, pVarsNew, nVarsNew );
            pBuffer[Pos++] = ')';
            return Pos;
        }
        if ( Cof0[v] == ~Cof1[v] ) // a^x
        {
            pBuffer[Pos++] = '[';
            pBuffer[Pos++] = 'a' + pVarsNew[v];
            Pos = Dau_DsdPerform_rec( Cof0[v], pBuffer, Pos, pVarsNew, nVarsNew );
            pBuffer[Pos++] = ']';
            return Pos;
        }
    }
    // decompose on the input side
    for ( v = 0; v < nVarsNew; v++ )
    for ( u = v+1; u < nVarsNew; u++ )
    {
        Cof[0] = Dau_DsdCof0( Cof0[v], pVarsNew[u] );
        Cof[1] = Dau_DsdCof1( Cof0[v], pVarsNew[u] );
        Cof[2] = Dau_DsdCof0( Cof1[v], pVarsNew[u] );
        Cof[3] = Dau_DsdCof1( Cof1[v], pVarsNew[u] );
        if ( Cof[0] == Cof[1] && Cof[0] == Cof[2] ) // vu
        {
            PosStart = Pos;
            sprintf( pNest, "(%c%c)", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truth6[pVarsNew[u]] & Cof[3]) | (~s_Truth6[pVarsNew[u]] & Cof[0]), pBuffer, Pos, pVarsNew, nVarsNew );
            Pos = Dau_DsdPerformReplace( pBuffer, PosStart, Pos, 'a' + pVarsNew[u], pNest );
            return Pos;
        }
        if ( Cof[0] == Cof[1] && Cof[0] == Cof[3] ) // v!u
        {
            PosStart = Pos;
            sprintf( pNest, "(%c!%c)", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truth6[pVarsNew[u]] & Cof[2]) | (~s_Truth6[pVarsNew[u]] & Cof[0]), pBuffer, Pos, pVarsNew, nVarsNew );
            Pos = Dau_DsdPerformReplace( pBuffer, PosStart, Pos, 'a' + pVarsNew[u], pNest );
            return Pos;
        }
        if ( Cof[0] == Cof[2] && Cof[0] == Cof[3] ) // !vu
        {
            PosStart = Pos;
            sprintf( pNest, "(!%c%c)", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truth6[pVarsNew[u]] & Cof[1]) | (~s_Truth6[pVarsNew[u]] & Cof[0]), pBuffer, Pos, pVarsNew, nVarsNew );
            Pos = Dau_DsdPerformReplace( pBuffer, PosStart, Pos, 'a' + pVarsNew[u], pNest );
            return Pos;
        }
        if ( Cof[1] == Cof[2] && Cof[1] == Cof[3] ) // !v!u
        {
            PosStart = Pos;
            sprintf( pNest, "(!%c!%c)", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truth6[pVarsNew[u]] & Cof[0]) | (~s_Truth6[pVarsNew[u]] & Cof[1]), pBuffer, Pos, pVarsNew, nVarsNew );
            Pos = Dau_DsdPerformReplace( pBuffer, PosStart, Pos, 'a' + pVarsNew[u], pNest );
            return Pos;
        }
        if ( Cof[0] == Cof[3] && Cof[1] == Cof[2] ) // v+u
        {
            PosStart = Pos;
            sprintf( pNest, "[%c%c]", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truth6[pVarsNew[u]] & Cof[1]) | (~s_Truth6[pVarsNew[u]] & Cof[0]), pBuffer, Pos, pVarsNew, nVarsNew );
            Pos = Dau_DsdPerformReplace( pBuffer, PosStart, Pos, 'a' + pVarsNew[u], pNest );
            return Pos;
        }
    }
    // find best variable for MUX decomposition
    vBest = -1;
    CountBest = 10;
    for ( v = 0; v < nVarsNew; v++ )
    {
        int CountCur = 0;
        for ( u = 0; u < nVarsNew; u++ )
            if ( u != v && Dau_DsdVarPres(Cof0[v], pVarsNew[u]) && Dau_DsdVarPres(Cof1[v], pVarsNew[u]) )
                CountCur++;
        if ( CountBest > CountCur )
        {
            CountBest = CountCur;
            vBest = v;
        }
        if ( CountCur == 0 )
            break;
    }
    // perform MUX decomposition
    pBuffer[Pos++] = '<';
    pBuffer[Pos++] = 'a' + pVarsNew[vBest];
    Pos = Dau_DsdPerform_rec( Cof1[vBest], pBuffer, Pos, pVarsNew, nVarsNew );
    Pos = Dau_DsdPerform_rec( Cof0[vBest], pBuffer, Pos, pVarsNew, nVarsNew );
    pBuffer[Pos++] = '>';
    return Pos;
}

static inline void Dau_DsdCleanBraces( char * p )
{
    char * q, Last = -1;
    int i;
    for ( i = 0; p[i]; i++ )
    {
        if ( p[i] == '(' || p[i] == '[' || p[i] == '<' )
        {
            if ( p[i] != '<' && p[i] == Last && i > 0 && p[i-1] != '!' )
            {
                q = Dau_DsdFindMatch( p + i );
                assert( (p[i] == '(') == (*q == ')') );
                assert( (p[i] == '[') == (*q == ']') );
                p[i] = *q = 'x';
            }
            else
                Last = p[i];
        }
        else if ( p[i] == ')' || p[i] == ']' || p[i] == '>' )
            Last = -1;
    }
/*
    if ( p[0] == '(' )
    {
        assert( p[i-1] == ')' );
        p[0] = p[i-1] = 'x';
    }
    else if ( p[0] == '[' )
    {
        assert( p[i-1] == ']' );
        p[0] = p[i-1] = 'x';
    }
*/
    for ( q = p; *p; p++ )
        if ( *p != 'x' )
            *q++ = *p;
    *q = 0;
}

char * Dau_DsdPerform( word t )
{
    static char pBuffer[DAU_MAX_STR+20];
    int pVarsNew[6] = {0, 1, 2, 3, 4, 5};
    int Pos = 0;
    if ( t == 0 )
        pBuffer[Pos++] = '0';
    else if ( t == ~(word)0 )
        pBuffer[Pos++] = '1';
    else
        Pos = Dau_DsdPerform_rec( t, pBuffer, Pos, pVarsNew, 6 );
    pBuffer[Pos++] = 0;
//    printf( "%d ", strlen(pBuffer) );
//    printf( "%s ->", pBuffer );
    Dau_DsdCleanBraces( pBuffer );
//    printf( " %s\n", pBuffer );
    return pBuffer;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dau_DsdTest()
{
//    word t = s_Truth6[0] & s_Truth6[1] & s_Truth6[2];
//    word t = ~s_Truth6[0] | (s_Truth6[1] ^ ~s_Truth6[2]);
//    word t = (s_Truth6[1] & s_Truth6[2]) | (s_Truth6[0] & s_Truth6[3]);
//    word t = (~s_Truth6[1] & ~s_Truth6[2]) | (s_Truth6[0] ^ s_Truth6[3]);
//    word t = ((~s_Truth6[1] & ~s_Truth6[2]) | (s_Truth6[0] ^ s_Truth6[3])) ^ s_Truth6[5];
//    word t = ((s_Truth6[1] & ~s_Truth6[2]) ^ (s_Truth6[0] & s_Truth6[3])) & s_Truth6[5];
//    word t = (~(~s_Truth6[0] & ~s_Truth6[4]) & s_Truth6[2]) | (~s_Truth6[1] & ~s_Truth6[0] & ~s_Truth6[4]);
//    word t = 0x0000000000005F3F;
//    word t = 0xF3F5030503050305;
//    word t = (s_Truth6[0] & s_Truth6[1] & (s_Truth6[2] ^ s_Truth6[4])) | (~s_Truth6[0] & ~s_Truth6[1] & ~(s_Truth6[2] ^ s_Truth6[4]));
//    word t = 0x05050500f5f5f5f3;
    word t = 0x9ef7a8d9c7193a0f;
    char * p = Dau_DsdPerform( t );
    word t2 = Dau_DsdToTruth( p );
    if ( t != t2 )
        printf( "Verification failed.\n" );
}
void Dau_DsdTestOne( word t, int i )
{
    word t2;
    char * p = Dau_DsdPerform( t );
    return;
    t2 = Dau_DsdToTruth( p ); 
    if ( t != t2 )
    {
        printf( "Verification failed.  " );
        printf( "%8d : ", i );
        printf( "%30s  ", p );
//        Kit_DsdPrintFromTruth( (unsigned *)&t, 6 );
//        printf( "  " );
//        Kit_DsdPrintFromTruth( (unsigned *)&t2, 6 );
        printf( "\n" );
    }
}

/*
    extern void Dau_DsdTestOne( word t, int i );
    assert( p->nVars == 6 );
    Dau_DsdTestOne( *p->pFuncs[i], i );
*/




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
            if ( t[i] & ~s_Truths6[iVar] )
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
            if ( (t[i] & ~s_Truths6[iVar]) != ~s_Truths6[iVar] )
                return 0;
        return 1;
    }
    else
    {
        int i, Step = (1 << (iVar - 6));
        word * tLimit = t + nWords;
        for ( ; t < tLimit; t += 2*Step )
            for ( i = 0; i < Step; i++ )
                if ( t[i] != ~(word)0 )
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
                if ( t[i+Step] != ~(word)0 )
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

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_TtCof0HasVar( word * t, int nWords, int iVarI, int iVarJ ) 
{
    assert( iVarI > iVarJ );
    if ( iVarI < 6 )
    {
        int i, Shift = (1 << iVarJ);
        for ( i = 0; i < nWords; i++ )
            if ( (((t[i] & ~s_Truths6[iVarI]) << Shift) & s_Truths6[iVarJ]) != ((t[i] & ~s_Truths6[iVarI]) & s_Truths6[iVarJ]) )
                return 0;
        return 1;
    }
    else if ( iVarI == 6 )
    {
    }
    else
    {
        int i, Step = (1 << (iVarJ - 6));
        word * tLimit = t + nWords;
        for ( ; t < tLimit; t += 2*Step )
            for ( i = 0; i < Step; i++ )
                if ( t[i] != t[i+Step] )
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
int Dau_DsdMinimize( word * p, int * pVars, int nVars )
{
    int i, k;
    assert( nVars > 6 );
    for ( i = k = nVars - 1; i >= 0; i-- )
    {
        if ( Abc_TtHasVar( p, nVars, i ) )
            continue;
        if ( i < k )
        {
            pVars[i] = pVars[k];
            Abc_TtSwapVars( p, nVars, i, k );
        }
        k--;
        nVars--;
    }
    return nVars;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dau_DsdRun6_rec( word * p, int * pVars, int nVars, char * pBuffer, int Pos, char pStore[16][16], int Func )
{
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dau_DsdRun_rec( word * p, int * pVars, int nVars, char * pBuffer, int Pos, char pStore[16][16], int Func )
{
    int v, nWords = Abc_TtWordNum( nVars );
    nVars = Dau_DsdMinimize( p, pVars, nVars );
    if ( nVars <= 6 )
        return Dau_DsdRun6_rec( p, pVars, nVars, pBuffer, Pos, pStore, Func );
    if ( p[0] & 1 )
    {
        // check for !(ax)
        for ( v = 0; v < nVars; v++ )
        if ( Abc_TtCof0IsConst0( p, nWords, v ) )
        {
            pBuffer[Pos++] = '(';
            pBuffer[Pos++] = 'a' + pVars[v];
            Abc_TtSwapVars( p, nVars, v, nVars - 1 );
            pVars[v] = pVars[nVars-1];
            Pos = Dau_DsdRun_rec( p + nWords/2, pVars, nVars-1, pBuffer, Pos, pStore, Func );
            pBuffer[Pos++] = ')';
            return Pos;
        }
    }
    else
    {
        // check for ax
        for ( v = 0; v < nVars; v++ )
        if ( Abc_TtCof0IsConst1( p, nWords, v ) )
        {
            pBuffer[Pos++] = '!';
            pBuffer[Pos++] = '(';
            pBuffer[Pos++] = 'a' + pVars[v];
            Abc_TtSwapVars( p, nVars, v, nVars - 1 );
            pVars[v] = pVars[nVars-1];
            Pos = Dau_DsdRun_rec( p + nWords/2, pVars, nVars-1, pBuffer, Pos, pStore, Func );
            pBuffer[Pos++] = ')';
            return Pos;
        }
    }
    if ( (p[nWords-1] >> 63) & 1 )
    {
        // check for !(!ax)
        for ( v = 0; v < nVars; v++ )
        if ( Abc_TtCof0IsConst1( p, nWords, v ) )
        {
            pBuffer[Pos++] = '!';
            pBuffer[Pos++] = '(';
            pBuffer[Pos++] = '!';
            pBuffer[Pos++] = 'a' + pVars[v];
            Abc_TtSwapVars( p, nVars, v, nVars - 1 );
            pVars[v] = pVars[nVars-1];
            Pos = Dau_DsdRun_rec( p, pVars, nVars-1, pBuffer, Pos, pStore, Func );
            pBuffer[Pos++] = ')';
            return Pos;
        }
    }
    else
    {
        // check for !ax
        for ( v = 0; v < nVars; v++ )
        if ( Abc_TtCof1IsConst0( p, nWords, v ) )
        {
            pBuffer[Pos++] = '(';
            pBuffer[Pos++] = '!';
            pBuffer[Pos++] = 'a' + pVars[v];
            Abc_TtSwapVars( p, nVars, v, nVars - 1 );
            pVars[v] = pVars[nVars-1];
            Pos = Dau_DsdRun_rec( p, pVars, nVars-1, pBuffer, Pos, pStore, Func );
            pBuffer[Pos++] = ')';
            return Pos;
        }
    }
    // check for a^x
    for ( v = 0; v < nVars; v++ )
    if ( Abc_TtCofsOpposite( p, nWords, v ) )
    {
        pBuffer[Pos++] = '[';
        pBuffer[Pos++] = 'a' + pVars[v];
        Abc_TtSwapVars( p, nVars, v, nVars - 1 );
        pVars[v] = pVars[nVars-1];
        Pos = Dau_DsdRun_rec( p, pVars, nVars-1, pBuffer, Pos, pStore, Func );
        pBuffer[Pos++] = ']';
        return Pos;
    }

    return 0;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Dau_DsdRun( word * p, int nVars )
{
    static char pBuffer[DAU_MAX_STR+20];
    static char pStore[16][16];
    int nWords = Abc_TtWordNum( nVars );
    int i, Pos = 0, Func = 0, pVars[16];
    assert( nVars <= 16 );
    for ( i = 0; i < nVars; i++ )
        pVars[i] = i;
    if ( Abc_TtTruthIsConst0( p, nWords ) )
        pBuffer[Pos++] = '0';
    else if ( Abc_TtTruthIsConst1( p, nWords ) )
        pBuffer[Pos++] = '1';
    else if ( nVars <= 6 )
        Pos = Dau_DsdRun6_rec( p, pVars, nVars, pBuffer, Pos, pStore, Func );
    else
        Pos = Dau_DsdRun_rec( p, pVars, nVars, pBuffer, Pos, pStore, Func );
    pBuffer[Pos++] = 0;
    Dau_DsdCleanBraces( pBuffer );
    return pBuffer;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END


