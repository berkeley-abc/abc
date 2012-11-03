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

#define DAU_MAX_STR 256

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
    {
        assert( **p - 'a' >= 0 && **p - 'a' < 6 );
        return fCompl ? ~s_Truths6[**p - 'a'] : s_Truths6[**p - 'a'];
    }
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
        if ( Abc_Tt6HasVar( t, pVars[v] ) )
            pVarsNew[ nVarsNew++ ] = pVars[v];
    assert( nVarsNew > 0 );
    // special case when function is a var
    if ( nVarsNew == 1 )
    {
        if ( t == s_Truths6[ pVarsNew[0] ] )
        {
            pBuffer[Pos++] = 'a' +  pVarsNew[0];
            return Pos;
        }
        if ( t == ~s_Truths6[ pVarsNew[0] ] )
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
        Cof0[v] = Abc_Tt6Cofactor0( t, pVarsNew[v] );
        Cof1[v] = Abc_Tt6Cofactor1( t, pVarsNew[v] );
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
        Cof[0] = Abc_Tt6Cofactor0( Cof0[v], pVarsNew[u] );
        Cof[1] = Abc_Tt6Cofactor1( Cof0[v], pVarsNew[u] );
        Cof[2] = Abc_Tt6Cofactor0( Cof1[v], pVarsNew[u] );
        Cof[3] = Abc_Tt6Cofactor1( Cof1[v], pVarsNew[u] );
        if ( Cof[0] == Cof[1] && Cof[0] == Cof[2] ) // vu
        {
            PosStart = Pos;
            sprintf( pNest, "(%c%c)", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truths6[pVarsNew[u]] & Cof[3]) | (~s_Truths6[pVarsNew[u]] & Cof[0]), pBuffer, Pos, pVarsNew, nVarsNew );
            Pos = Dau_DsdPerformReplace( pBuffer, PosStart, Pos, 'a' + pVarsNew[u], pNest );
            return Pos;
        }
        if ( Cof[0] == Cof[1] && Cof[0] == Cof[3] ) // v!u
        {
            PosStart = Pos;
            sprintf( pNest, "(%c!%c)", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truths6[pVarsNew[u]] & Cof[2]) | (~s_Truths6[pVarsNew[u]] & Cof[0]), pBuffer, Pos, pVarsNew, nVarsNew );
            Pos = Dau_DsdPerformReplace( pBuffer, PosStart, Pos, 'a' + pVarsNew[u], pNest );
            return Pos;
        }
        if ( Cof[0] == Cof[2] && Cof[0] == Cof[3] ) // !vu
        {
            PosStart = Pos;
            sprintf( pNest, "(!%c%c)", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truths6[pVarsNew[u]] & Cof[1]) | (~s_Truths6[pVarsNew[u]] & Cof[0]), pBuffer, Pos, pVarsNew, nVarsNew );
            Pos = Dau_DsdPerformReplace( pBuffer, PosStart, Pos, 'a' + pVarsNew[u], pNest );
            return Pos;
        }
        if ( Cof[1] == Cof[2] && Cof[1] == Cof[3] ) // !v!u
        {
            PosStart = Pos;
            sprintf( pNest, "(!%c!%c)", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truths6[pVarsNew[u]] & Cof[0]) | (~s_Truths6[pVarsNew[u]] & Cof[1]), pBuffer, Pos, pVarsNew, nVarsNew );
            Pos = Dau_DsdPerformReplace( pBuffer, PosStart, Pos, 'a' + pVarsNew[u], pNest );
            return Pos;
        }
        if ( Cof[0] == Cof[3] && Cof[1] == Cof[2] ) // v+u
        {
            PosStart = Pos;
            sprintf( pNest, "[%c%c]", 'a' + pVarsNew[v], 'a' + pVarsNew[u] );
            Pos = Dau_DsdPerform_rec( (s_Truths6[pVarsNew[u]] & Cof[1]) | (~s_Truths6[pVarsNew[u]] & Cof[0]), pBuffer, Pos, pVarsNew, nVarsNew );
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
            if ( u != v && Abc_Tt6HasVar(Cof0[v], pVarsNew[u]) && Abc_Tt6HasVar(Cof1[v], pVarsNew[u]) )
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
void Dau_DsdTest3()
{
//    word t = s_Truths6[0] & s_Truths6[1] & s_Truths6[2];
//    word t = ~s_Truths6[0] | (s_Truths6[1] ^ ~s_Truths6[2]);
//    word t = (s_Truths6[1] & s_Truths6[2]) | (s_Truths6[0] & s_Truths6[3]);
//    word t = (~s_Truths6[1] & ~s_Truths6[2]) | (s_Truths6[0] ^ s_Truths6[3]);
//    word t = ((~s_Truths6[1] & ~s_Truths6[2]) | (s_Truths6[0] ^ s_Truths6[3])) ^ s_Truths6[5];
//    word t = ((s_Truths6[1] & ~s_Truths6[2]) ^ (s_Truths6[0] & s_Truths6[3])) & s_Truths6[5];
//    word t = (~(~s_Truths6[0] & ~s_Truths6[4]) & s_Truths6[2]) | (~s_Truths6[1] & ~s_Truths6[0] & ~s_Truths6[4]);
//    word t = 0x0000000000005F3F;
//    word t = 0xF3F5030503050305;
//    word t = (s_Truths6[0] & s_Truths6[1] & (s_Truths6[2] ^ s_Truths6[4])) | (~s_Truths6[0] & ~s_Truths6[1] & ~(s_Truths6[2] ^ s_Truths6[4]));
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
    int v, u, nWords = Abc_TtWordNum( nVars );
    nVars = Dau_DsdMinimize( p, pVars, nVars );
    if ( nVars <= 6 )
        return Dau_DsdRun6_rec( p, pVars, nVars, pBuffer, Pos, pStore, Func );
    // consider negative cofactors
    if ( p[0] & 1 )
    {
        // check for !(ax)
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
    else
    {
        // check for ax
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
    // consider positive cofactors
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

    // consider two-variable cofactors
    for ( v = nVars - 1; v > 0; v-- )
    {
        unsigned uSupp0 = 0, uSupp1 = 0;
        for ( u = v - 1; u >= 0; u-- )
        {
            if ( Abc_TtCheckEqualCofs( p, nWords, u, v, 0, 1 ) )
            {
                uSupp0 |= (1 << u);
                if ( Abc_TtCheckEqualCofs( p, nWords, u, v, 2, 3 ) )
                {
                    uSupp1 |= (1 << u);
                    // check XOR decomposition
                    if ( Abc_TtCheckEqualCofs( p, nWords, u, v, 0, 3 ) && Abc_TtCheckEqualCofs( p, nWords, u, v, 1, 2 ) )
                    {
                        // perform XOR (u, v)
                        return Pos;
                    }
                }
                else
                {
                    // F(v=0) does not depend on u; F(v=1) depends on u
                    if ( Abc_TtCheckEqualCofs( p, nWords, u, v, 0, 2 ) )
                    {
                        // perform AND (u, v)
                        return Pos;
                    }
                    if ( Abc_TtCheckEqualCofs( p, nWords, u, v, 0, 3 ) )
                    {
                        // perform AND (u, v)
                        return Pos;
                    }
                }
            }
            else if ( Abc_TtCheckEqualCofs( p, nWords, u, v, 2, 3 ) )
            {
                uSupp1 |= (1 << u);
                // F(v=0) depends on u; F(v=1) does not depend on u
                if ( Abc_TtCheckEqualCofs( p, nWords, u, v, 0, 2 ) )
                {
                    // perform AND (u, v)
                    return Pos;
                }
                if ( Abc_TtCheckEqualCofs( p, nWords, u, v, 1, 2 ) )
                {
                    // perform AND (u, v)
                    return Pos;
                }
            }
            else assert( 0 );
        }
        // check MUX decomposition w.r.t. u
        if ( (uSupp0 & uSupp1) == 0 )
        {
            // perform MUX( v, F(v=1), F(v=0) )
        }
        // check MUX decomposition w.r.t. u
        if ( Abc_TtSuppOnlyOne( uSupp0 & ~uSupp1 ) && Abc_TtSuppOnlyOne( ~uSupp0 & uSupp1 ) )
        {
            // check MUX 
            int iVar0 = Abc_TtSuppFindFirst( uSupp0 );
            int iVar1 = Abc_TtSuppFindFirst( uSupp1 );
            int fEqual0, fEqual1;

            if ( iVar0 > iVar1 )
                ABC_SWAP( int, iVar0, iVar1 );

            // check existence conditions
            assert( iVar0 < iVar1 );
            fEqual0 = Abc_TtCheckEqualCofs( p, nWords, iVar0, iVar1, 0, 2 ) && Abc_TtCheckEqualCofs( p, nWords, iVar0, iVar1, 1, 3 );
            fEqual1 = Abc_TtCheckEqualCofs( p, nWords, iVar0, iVar1, 0, 3 ) && Abc_TtCheckEqualCofs( p, nWords, iVar0, iVar1, 1, 2 );
            if ( fEqual0 || fEqual1 )
            {
                // perform MUX( v, F(v=1), F(v=0) )
                return Pos;
            }
        }
    }
    return Pos;
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




typedef struct Dau_Dsd_t_ Dau_Dsd_t;
struct Dau_Dsd_t_
{
    int      nVarsInit;            // the initial number of variables
    int      nVarsUsed;            // the current number of variables
    char     pVarDefs[32][8];      // variable definitions
    char     pOutput[DAU_MAX_STR]; // output stream
    int      nPos;                 // writing position
    int      nConsts;              // the number of constant decompositions
    int      uConstMask;           // constant decomposition mask
};

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dua_DsdInit( Dau_Dsd_t * p, int nVarsInit )
{
    int i;
    memset( p, 0, sizeof(Dau_Dsd_t) );
    p->nVarsInit = p->nVarsUsed = nVarsInit;
    for ( i = 0; i < nVarsInit; i++ )
        p->pVarDefs[i][0] = 'a' + i;
}
void Dua_DsdWrite( Dau_Dsd_t * p, char * pStr )
{
    while ( *pStr )
        p->pOutput[ p->nPos++ ] = *pStr++;
}
void Dua_DsdWriteInv( Dau_Dsd_t * p, int Cond )
{
    if ( Cond )
        p->pOutput[ p->nPos++ ] = '!';
}
void Dua_DsdWriteVar( Dau_Dsd_t * p, int iVar, int fInv )
{
    char * pStr;
    if ( fInv )
        p->pOutput[ p->nPos++ ] = '!';
    for ( pStr = p->pVarDefs[iVar]; *pStr; pStr++ )
        if ( *pStr >= 'a' + p->nVarsInit && *pStr < 'a' + p->nVarsUsed )
            Dua_DsdWriteVar( p, *pStr - 'a', 0 );
        else
            p->pOutput[ p->nPos++ ] = *pStr;
}
void Dua_DsdWriteStop( Dau_Dsd_t * p )
{
    int i;
    for ( i = 0; i < p->nConsts; i++ )
        p->pOutput[ p->nPos++ ] = ((p->uConstMask >> i) & 1) ? ']' : ')';
    p->pOutput[ p->nPos++ ] = 0;
}
int Dua_DsdAddVarDef( Dau_Dsd_t * p, char * pStr )
{
    assert( strlen(pStr) < 8 );
    assert( p->nVarsUsed < 32 );
    sprintf( p->pVarDefs[p->nVarsUsed++], "%s", pStr );
    return p->nVarsUsed - 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dua_DsdMinBase( word * pTruth, int nVars, int * pVarsNew )
{
    int v;
    for ( v = 0; v < nVars; v++ )
        pVarsNew[v] = v;
    for ( v = nVars - 1; v >= 0; v-- )
    {
        if ( Abc_TtHasVar( pTruth, nVars, v ) )
            continue;
        Abc_TtSwapVars( pTruth, nVars, v, nVars-1 );
        pVarsNew[v] = pVarsNew[--nVars];
    }
    return nVars;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if constant cofactor is found.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dau_Dsd6DecomposeConstCofOne( Dau_Dsd_t * p, word * pTruth, int * pVars, int nVars, int v )
{
    // consider negative cofactors
    if ( pTruth[0] & 1 )
    {        
        if ( Abc_Tt6Cof0IsConst1( pTruth[0], v ) ) // !(ax)
        {
            Dua_DsdWrite( p, "!(" );
            pTruth[0] = ~Abc_Tt6Cofactor1( pTruth[0], v );
            goto finish;            
        }
    }
    else
    {
        if ( Abc_Tt6Cof0IsConst0( pTruth[0], v ) ) // ax
        {
            Dua_DsdWrite( p, "(" );
            pTruth[0] = Abc_Tt6Cofactor1( pTruth[0], v );
            goto finish;            
        }
    }
    // consider positive cofactors
    if ( pTruth[0] >> 63 )
    {        
        if ( Abc_Tt6Cof1IsConst1( pTruth[0], v ) ) // !(!ax)
        {
            Dua_DsdWrite( p, "!(!" );
            pTruth[0] = ~Abc_Tt6Cofactor0( pTruth[0], v );
            goto finish;            
        }
    }
    else
    {
        if ( Abc_Tt6Cof1IsConst0( pTruth[0], v ) ) // !ax
        {
            Dua_DsdWrite( p, "(!" );
            pTruth[0] = Abc_Tt6Cofactor0( pTruth[0], v );
            goto finish;            
        }
    }
    // consider equal cofactors
    if ( Abc_Tt6CofsOpposite( pTruth[0], v ) ) // [ax]
    {
        Dua_DsdWrite( p, "[" );
        pTruth[0] = Abc_Tt6Cofactor0( pTruth[0], v );
        p->uConstMask |= (1 << p->nConsts);
        goto finish;            
    }
    return 0;

finish:
    p->nConsts++;
    Dua_DsdWriteVar( p, pVars[v], 0 );
    pVars[v] = pVars[nVars-1];
    Abc_TtSwapVars( pTruth, 6, v, nVars-1 );
    return 1;
}
int Dau_Dsd6DecomposeConstCof( Dau_Dsd_t * p, word * pTruth, int * pVars, int nVars )
{
    int v, nVarsOld;
    assert( nVars > 1 );
    while ( 1 )
    {
        nVarsOld = nVars;
        for ( v = nVars - 1; v >= 0 && nVars > 1; v-- )
            if ( Dau_Dsd6DecomposeConstCofOne( p, pTruth, pVars, nVars, v ) )
                nVars--;
        if ( nVarsOld == nVars || nVars == 1 )
            break;
    }
    if ( nVars == 1 )
        Dua_DsdWriteVar( p, pVars[--nVars], (int)(pTruth[0] & 1) );
    return nVars;
}
void Dau_Dsd6DecomposeInternal( Dau_Dsd_t * p, word t, int * pVars, int nVars )
{
    char pBuffer[10]; 
    int v, u;
    nVars = Dau_Dsd6DecomposeConstCof( p, &t, pVars, nVars );
    if ( nVars == 0 )
        return;
    // consider two-variable cofactors
    for ( v = nVars - 1; v > 0; v-- )
    {
        word tCof0 = Abc_Tt6Cofactor0( t, v );
        word tCof1 = Abc_Tt6Cofactor1( t, v );
        unsigned uSupp0 = 0, uSupp1 = 0;
        Kit_DsdPrintFromTruth( &t, 6 );printf( "\n" );
        pBuffer[0] = 0;
        for ( u = v - 1; u >= 0; u-- )
        {
            if ( !Abc_Tt6HasVar(tCof0, u) )
            {
                if ( Abc_Tt6HasVar(tCof1, u) )
                {
                    uSupp1 |= (1 << u);
                    // F(v=0) does not depend on u; F(v=1) depends on u
                    if ( Abc_Tt6Cof0EqualCof0(tCof0, tCof1, u) ) // vu
                    {
                        sprintf( pBuffer, "(%c%c)", 'a' + pVars[v], 'a' + pVars[u] );
                        t = (s_Truths6[u] & Abc_Tt6Cofactor1(tCof1, u)) | (~s_Truths6[u] & Abc_Tt6Cofactor0(tCof0, u));
                        break;
                    }
                    if ( Abc_Tt6Cof0EqualCof1(tCof0, tCof1, u) ) // v!u
                    {
                        sprintf( pBuffer, "(%c!%c)", 'a' + pVars[v], 'a' + pVars[u] );
                        t = (s_Truths6[u] & Abc_Tt6Cofactor0(tCof1, u)) | (~s_Truths6[u] & Abc_Tt6Cofactor0(tCof0, u));
                        break;
                    }
                }
                else assert( 0 ); // should depend on u
            }
            else
            {
                uSupp0 |= (1 << u);
                if ( !Abc_Tt6HasVar(tCof1, u) )
                {
                    // F(v=0) depends on u; F(v=1) does not depend on u
                    if ( Abc_Tt6Cof0EqualCof1(tCof0, tCof1, u) ) // !vu
                    {
                        sprintf( pBuffer, "(!%c%c)", 'a' + pVars[v], 'a' + pVars[u] );
                        t = (s_Truths6[u] & Abc_Tt6Cofactor1(tCof0, u)) | (~s_Truths6[u] & Abc_Tt6Cofactor0(tCof0, u));
                        break;
                    }
                    if ( Abc_Tt6Cof1EqualCof1(tCof0, tCof1, u) ) // !v!u
                    {
                        sprintf( pBuffer, "(!%c!%c)", 'a' + pVars[v], 'a' + pVars[u] );
                        t = (s_Truths6[u] & Abc_Tt6Cofactor0(tCof0, u)) | (~s_Truths6[u] & Abc_Tt6Cofactor1(tCof1, u));
                        break;
                    }
                }
                else
                {
                    uSupp1 |= (1 << u);
                    // both F(v=0) and F(v=1) depend on u
                    if ( Abc_Tt6Cof0EqualCof1(tCof0, tCof1, u) && Abc_Tt6Cof0EqualCof1(tCof1, tCof0, u) ) // v+u
                    {
                        t = (s_Truths6[u] & Abc_Tt6Cofactor1(tCof0, u)) | (~s_Truths6[u] & Abc_Tt6Cofactor0(tCof0, u));
                        sprintf( pBuffer, "[%c%c]", 'a' + pVars[v], 'a' + pVars[u] );
                        break;
                    }
                }
            }
        }
        // check if decomposition happened
        if ( u >= 0 )
        {
            // finalize decomposition
            assert( pBuffer[0] != 0 );
            pVars[u] = Dua_DsdAddVarDef( p, pBuffer );
            pVars[v] = pVars[nVars-1];
            Abc_TtSwapVars( &t, 6, v, nVars-1 );
            nVars = Dau_Dsd6DecomposeConstCof( p, &t, pVars, --nVars );
            v = Abc_MinInt( v, nVars - 1 ) + 1;
            if ( nVars == 0 )
                return;
            continue;
        }
        // check MUX decomposition w.r.t. u
        if ( Abc_TtSuppOnlyOne( uSupp0 & ~uSupp1 ) && Abc_TtSuppOnlyOne( ~uSupp0 & uSupp1 ) )
        {
            // check MUX 
            int iVar0 = Abc_TtSuppFindFirst(  uSupp0 & ~uSupp1 );
            int iVar1 = Abc_TtSuppFindFirst( ~uSupp0 &  uSupp1 );
            int iVarMin = Abc_MinInt( v, Abc_MinInt( iVar0, iVar1 ) );
            int fEqual0, fEqual1;
            word C00, C01, C10, C11;
            // check existence conditions
            if ( iVar0 > iVar1 )
                ABC_SWAP( int, iVar0, iVar1 );
            assert( iVar0 < iVar1 );
//            fEqual0 = Abc_TtCheckEqualCofs( &t, 1, iVar0, iVar1, 0, 2 ) && Abc_TtCheckEqualCofs( &t, 1, iVar0, iVar1, 1, 3 );
//            fEqual1 = Abc_TtCheckEqualCofs( &t, 1, iVar0, iVar1, 0, 3 ) && Abc_TtCheckEqualCofs( &t, 1, iVar0, iVar1, 1, 2 );
            C00 = Abc_Tt6Cofactor0(tCof0, iVar0);
            C01 = Abc_Tt6Cofactor1(tCof0, iVar0);
            C10 = Abc_Tt6Cofactor0(tCof1, iVar1);
            C11 = Abc_Tt6Cofactor1(tCof1, iVar1);
            fEqual0 = (C00 == C10) && (C01 == C11);
            fEqual1 = (C00 == C11) && (C01 == C10);
            if ( fEqual0 || fEqual1 )
            {
                assert( iVarMin < iVar0 && iVar0 < iVar1 );
                t = (s_Truths6[iVarMin] & Abc_Tt6Cofactor0(tCof1, iVar1)) | (~s_Truths6[iVarMin] & Abc_Tt6Cofactor1(tCof1, iVar1));
                if ( fEqual1 )
                    t = ~t;
                sprintf( pBuffer, "<%c%c%c>", 'a' + pVars[v], 'a' + pVars[iVar1], 'a' + pVars[iVar0] );
                pVars[iVarMin] = Dua_DsdAddVarDef( p, pBuffer );
                pVars[iVar1] = pVars[nVars-1];
                Abc_TtSwapVars( &t, 6, iVar1, nVars-1 );
                pVars[iVar0] = pVars[nVars-2];
                Abc_TtSwapVars( &t, 6, iVar0, nVars-2 );
                nVars -= 2;
                nVars = Dau_Dsd6DecomposeConstCof( p, &t, pVars, nVars );
                v = Abc_MinInt( v, nVars - 1 ) + 1;
                if ( nVars == 0 )
                    return;
                break;
            }
        }


/*
            // get the single variale cofactors
            Kit_TruthCofactor0New( pCofs2[0], pTruth, pObj->nFans, i );  // tCof0
            Kit_TruthCofactor1New( pCofs2[1], pTruth, pObj->nFans, i );  // tCof1
            // get four cofactors                                        
            Kit_TruthCofactor0New( pCofs4[0][0], pCofs2[0], pObj->nFans, iLit0 ); // Abc_Tt6Cofactor0(tCof0, iLit0)
            Kit_TruthCofactor1New( pCofs4[0][1], pCofs2[0], pObj->nFans, iLit0 ); // Abc_Tt6Cofactor1(tCof0, iLit0)
            Kit_TruthCofactor0New( pCofs4[1][0], pCofs2[1], pObj->nFans, iLit1 ); // Abc_Tt6Cofactor0(tCof1, iLit1)
            Kit_TruthCofactor1New( pCofs4[1][1], pCofs2[1], pObj->nFans, iLit1 ); // Abc_Tt6Cofactor1(tCof1, iLit1)
            // check existence conditions
            fEquals[0][0] = Kit_TruthIsEqual( pCofs4[0][0], pCofs4[1][0], pObj->nFans );
            fEquals[0][1] = Kit_TruthIsEqual( pCofs4[0][1], pCofs4[1][1], pObj->nFans );
            fEquals[1][0] = Kit_TruthIsEqual( pCofs4[0][0], pCofs4[1][1], pObj->nFans );
            fEquals[1][1] = Kit_TruthIsEqual( pCofs4[0][1], pCofs4[1][0], pObj->nFans );
            if ( (fEquals[0][0] && fEquals[0][1]) || (fEquals[1][0] && fEquals[1][1]) )
            {
                // construct the MUX
                pRes = Kit_DsdObjAlloc( pNtk, KIT_DSD_PRIME, 3 );
                Kit_DsdObjTruth(pRes)[0] = 0xCACACACA;
                pRes->nRefs++;
                pRes->nFans = 3;
                pRes->pFans[0] = pObj->pFans[iLit0]; pObj->pFans[iLit0] = 127;  uSupp &= ~(1 << iLit0);
                pRes->pFans[1] = pObj->pFans[iLit1]; pObj->pFans[iLit1] = 127;  uSupp &= ~(1 << iLit1);
                pRes->pFans[2] = pObj->pFans[i];     pObj->pFans[i] = 2 * pRes->Id; // remains in support
                // update the node
//                if ( fEquals[0][0] && fEquals[0][1] )
//                    Kit_TruthMuxVar( pTruth, pCofs4[0][0], pCofs4[0][1], pObj->nFans, i );
//                else
//                    Kit_TruthMuxVar( pTruth, pCofs4[0][1], pCofs4[0][0], pObj->nFans, i );
                Kit_TruthMuxVar( pTruth, pCofs4[1][0], pCofs4[1][1], pObj->nFans, i );
                if ( fEquals[1][0] && fEquals[1][1] )
                    pRes->pFans[0] = Abc_LitNot(pRes->pFans[0]);
                // decompose the remainder
                Kit_DsdDecompose_rec( pNtk, pObj, uSupp, pPar, nDecMux );
                return;
            }
*/



/*
        // check MUX decomposition w.r.t. u
        if ( (uSupp0 & uSupp1) == 0 )
        {
            // perform MUX( v, F(v=1), F(v=0) )
        }
*/
    }
    // this non-DSD-decomposable function
    assert( nVars > 2 );
    // write truth table
    p->nPos += Abc_TtWriteHexRev( p->pOutput + p->nPos, &t, nVars );
    Dua_DsdWrite( p, "{" );
    for ( v = 0; v < nVars; v++ )
        Dua_DsdWriteVar( p, pVars[v], 0 );
    Dua_DsdWrite( p, "}" );
}
void Dau_DsdDecomposeInternal( Dau_Dsd_t * p, word  * pTruth, int * pVars, int nVars )
{
}
char * Dau_DsdDecompose( word * pTruth, int nVarsInit )
{
    Dau_Dsd_t P, * p = &P;
    int nVars, pVars[16];
    Dua_DsdInit( p, nVarsInit );
    if ( (pTruth[0] & 1) == 0 && Abc_TtIsConst0(pTruth, Abc_TtWordNum(nVarsInit)) )
        Dua_DsdWrite( p, "0" );
    else if ( (pTruth[0] & 1) && Abc_TtIsConst1(pTruth, Abc_TtWordNum(nVarsInit)) )
        Dua_DsdWrite( p, "1" );
    else 
    {
        nVars = Dua_DsdMinBase( pTruth, nVarsInit, pVars );
        assert( nVars > 0 && nVars <= 6 );
        if ( nVars == 1 )
            Dua_DsdWriteVar( p, pVars[0], (int)(pTruth[0] & 1) );
        else if ( nVars <= 6 )
            Dau_Dsd6DecomposeInternal( p, pTruth[0], pVars, nVars );
        else
            Dau_DsdDecomposeInternal( p, pTruth, pVars, nVars );
    }
    Dua_DsdWriteStop( p );
    Dau_DsdCleanBraces( p->pOutput );
    return p->pOutput;
}
void Dau_DsdTest()
{
//    char * pStr = "(!(!a<bcd>)!(!fe))";
    char * pStr = "<cba>";
    char * pStr2;
    word t = Dau_DsdToTruth( pStr );
    return;
    pStr2 = Dau_DsdDecompose( &t, 6 );
    t = 0;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END


