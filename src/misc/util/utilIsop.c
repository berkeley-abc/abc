/**CFile****************************************************************

  FileName    [utilIsop.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ISOP computation.]

  Synopsis    [ISOP computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 4, 2014.]

  Revision    [$Id: utilIsop.c,v 1.00 2014/10/04 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "misc/vec/vec.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef int FUNC_ISOP( word *, word *, word *, int *, int );

static FUNC_ISOP Abc_Isop7Cover; 
static FUNC_ISOP Abc_Isop8Cover;
static FUNC_ISOP Abc_Isop9Cover; 
static FUNC_ISOP Abc_Isop10Cover;
static FUNC_ISOP Abc_Isop11Cover;
static FUNC_ISOP Abc_Isop12Cover;
static FUNC_ISOP Abc_Isop13Cover;
static FUNC_ISOP Abc_Isop14Cover;
static FUNC_ISOP Abc_Isop15Cover;
static FUNC_ISOP Abc_Isop16Cover;

static FUNC_ISOP * s_pFuncIsopCover[17] =
{
    NULL, // 0
    NULL, // 1
    NULL, // 2
    NULL, // 3
    NULL, // 4
    NULL, // 5
    NULL, // 6
    Abc_Isop7Cover,  // 7
    Abc_Isop8Cover,  // 8
    Abc_Isop9Cover,  // 9
    Abc_Isop10Cover, // 10
    Abc_Isop11Cover, // 11
    Abc_Isop12Cover, // 12
    Abc_Isop13Cover, // 13
    Abc_Isop14Cover, // 14
    Abc_Isop15Cover, // 15
    Abc_Isop16Cover  // 16
};

extern int Abc_IsopCheck( word * pOn, word * pOnDc, word * pRes, int nVars, int nCostLim, int * pCover );
extern int Abc_EsopCheck( word * pOn, int nVars, int nCostLim, int * pCover );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [These procedures assume that function has exact support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_IsopAddLits( int * pCover, int nCost0, int nCost1, int Var )
{
    int c;
    if ( pCover == NULL ) return;
    nCost0 >>= 16;
    nCost1 >>= 16;
    for ( c = 0; c < nCost0; c++ )
        pCover[c] |= (1 << Abc_Var2Lit(Var,0));
    for ( c = 0; c < nCost1; c++ )
        pCover[nCost0+c] |= (1 << Abc_Var2Lit(Var,1));
}
int Abc_Isop6Cover( word uOn, word uOnDc, word * pRes, int nVars, int nCostLim, int * pCover )
{
    word uOn0, uOn1, uOnDc0, uOnDc1, uRes0, uRes1, uRes2;
    int Var, nCost0, nCost1, nCost2;
    assert( nVars <= 6 );
    assert( (uOn & ~uOnDc) == 0 );
    if ( uOn == 0 )
    {
        pRes[0] = 0;
        return 0;
    }
    if ( uOnDc == ~(word)0 )
    {
        pRes[0] = ~(word)0;
        if ( pCover ) pCover[0] = 0;
        return (1 << 16);
    }
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
    nCost0 = Abc_Isop6Cover( uOn0 & ~uOnDc1, uOnDc0, &uRes0, Var, nCostLim, pCover );
    if ( nCost0 >= nCostLim ) return nCostLim;
    nCost1 = Abc_Isop6Cover( uOn1 & ~uOnDc0, uOnDc1, &uRes1, Var, nCostLim, pCover ? pCover + (nCost0 >> 16) : NULL );
    if ( nCost0 + nCost1 >= nCostLim ) return nCostLim;
    nCost2 = Abc_Isop6Cover( (uOn0 & ~uRes0) | (uOn1 & ~uRes1), uOnDc0 & uOnDc1, &uRes2, Var, nCostLim, pCover ? pCover + (nCost0 >> 16) + (nCost1 >> 16) : NULL );
    if ( nCost0 + nCost1 + nCost2 >= nCostLim ) return nCostLim;
    // derive the final truth table
    *pRes = uRes2 | (uRes0 & s_Truths6Neg[Var]) | (uRes1 & s_Truths6[Var]);
    assert( (uOn & ~*pRes) == 0 && (*pRes & ~uOnDc) == 0 );
    Abc_IsopAddLits( pCover, nCost0, nCost1, Var );
    return nCost0 + nCost1 + nCost2 + (nCost0 >> 16) + (nCost1 >> 16);
}
int Abc_Isop7Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    word uOn0, uOn1, uOn2, uOnDc2, uRes0, uRes1, uRes2;
    int nCost0, nCost1, nCost2, nVars = 6;
    assert( (pOn[0] & ~pOnDc[0]) == 0 );
    assert( (pOn[1] & ~pOnDc[1]) == 0 );
    // cofactor
    uOn0 = pOn[0] & ~pOnDc[1];
    uOn1 = pOn[1] & ~pOnDc[0];
    // solve for cofactors
    nCost0 = Abc_IsopCheck( &uOn0, pOnDc,   &uRes0, nVars, nCostLim, pCover );
    if ( nCost0 >= nCostLim ) return nCostLim;
    nCost1 = Abc_IsopCheck( &uOn1, pOnDc+1, &uRes1, nVars, nCostLim, pCover ? pCover + (nCost0 >> 16) : NULL );
    if ( nCost0 + nCost1 >= nCostLim ) return nCostLim;
    uOn2 = (pOn[0] & ~uRes0) | (pOn[1] & ~uRes1);
    uOnDc2 = pOnDc[0] & pOnDc[1];
    nCost2 = Abc_IsopCheck( &uOn2, &uOnDc2,  &uRes2, nVars, nCostLim, pCover ? pCover + (nCost0 >> 16) + (nCost1 >> 16) : NULL );
    if ( nCost0 + nCost1 + nCost2 >= nCostLim ) return nCostLim;
    // derive the final truth table
    pRes[0] = uRes2 | uRes0;
    pRes[1] = uRes2 | uRes1;
    assert( (pOn[0] & ~pRes[0]) == 0 && (pRes[0] & ~pOnDc[0]) == 0 );
    assert( (pOn[1] & ~pRes[1]) == 0 && (pRes[1] & ~pOnDc[1]) == 0 );
    Abc_IsopAddLits( pCover, nCost0, nCost1, nVars );
    return nCost0 + nCost1 + nCost2 + (nCost0 >> 16) + (nCost1 >> 16);
}
int Abc_Isop8Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    word uOn0[2], uOn1[2], uOn2[2], uOnDc2[2], uRes0[2], uRes1[2], uRes2[2];
    int nCost0, nCost1, nCost2, nVars = 7;
    // cofactor
    uOn0[0] = pOn[0] & ~pOnDc[2];
    uOn0[1] = pOn[1] & ~pOnDc[3];
    uOn1[0] = pOn[2] & ~pOnDc[0];
    uOn1[1] = pOn[3] & ~pOnDc[1];
    // solve for cofactors
    nCost0 = Abc_IsopCheck( uOn0, pOnDc,   uRes0, nVars, nCostLim, pCover );
    if ( nCost0 >= nCostLim ) return nCostLim;
    nCost1 = Abc_IsopCheck( uOn1, pOnDc+2, uRes1, nVars, nCostLim, pCover ? pCover + (nCost0 >> 16) : NULL );
    if ( nCost0 + nCost1 >= nCostLim ) return nCostLim;
    uOn2[0] = (pOn[0] & ~uRes0[0]) | (pOn[2] & ~uRes1[0]);
    uOn2[1] = (pOn[1] & ~uRes0[1]) | (pOn[3] & ~uRes1[1]);
    uOnDc2[0] = pOnDc[0] & pOnDc[2];
    uOnDc2[1] = pOnDc[1] & pOnDc[3];
    nCost2 = Abc_IsopCheck( uOn2, uOnDc2,  uRes2, nVars, nCostLim, pCover ? pCover + (nCost0 >> 16) + (nCost1 >> 16) : NULL );
    if ( nCost0 + nCost1 + nCost2 >= nCostLim ) return nCostLim;
    // derive the final truth table
    pRes[0] = uRes2[0] | uRes0[0];
    pRes[1] = uRes2[1] | uRes0[1];
    pRes[2] = uRes2[0] | uRes1[0];
    pRes[3] = uRes2[1] | uRes1[1];
    assert( (pOn[0] & ~pRes[0]) == 0 && (pOn[1] & ~pRes[1]) == 0 && (pOn[2] & ~pRes[2]) == 0 && (pOn[3] & ~pRes[3]) == 0 );
    assert( (pRes[0] & ~pOnDc[0])==0 && (pRes[1] & ~pOnDc[1])==0 && (pRes[2] & ~pOnDc[2])==0 && (pRes[3] & ~pOnDc[3])==0 );
    Abc_IsopAddLits( pCover, nCost0, nCost1, nVars );
    return nCost0 + nCost1 + nCost2 + (nCost0 >> 16) + (nCost1 >> 16);
}
int Abc_Isop9Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    word uOn0[4], uOn1[4], uOn2[4], uOnDc2[4], uRes0[4], uRes1[4], uRes2[4];
    int c, nCost0, nCost1, nCost2, nVars = 8, nWords = 4;
    // cofactor
    for ( c = 0; c < nWords; c++ )
        uOn0[c] = pOn[c] & ~pOnDc[c+nWords], uOn1[c] = pOn[c+nWords] & ~pOnDc[c];
    // solve for cofactors
    nCost0 = Abc_IsopCheck( uOn0, pOnDc,        uRes0, nVars, nCostLim, pCover );
    if ( nCost0 >= nCostLim ) return nCostLim;
    nCost1 = Abc_IsopCheck( uOn1, pOnDc+nWords, uRes1, nVars, nCostLim, pCover ? pCover + (nCost0 >> 16) : NULL );
    if ( nCost0 + nCost1 >= nCostLim ) return nCostLim;
    for ( c = 0; c < nWords; c++ )
        uOn2[c] = (pOn[c] & ~uRes0[c]) | (pOn[c+nWords] & ~uRes1[c]), uOnDc2[c] = pOnDc[c] & pOnDc[c+nWords];
    nCost2 = Abc_IsopCheck( uOn2, uOnDc2,       uRes2, nVars, nCostLim, pCover ? pCover + (nCost0 >> 16) + (nCost1 >> 16) : NULL );
    if ( nCost0 + nCost1 + nCost2 >= nCostLim ) return nCostLim;
    // derive the final truth table
    for ( c = 0; c < nWords; c++ )
        pRes[c] = uRes2[c] | uRes0[c], pRes[c+nWords] = uRes2[c] | uRes1[c];
    // verify
    for ( c = 0; c < (nWords<<1); c++ )
        assert( (pOn[c]  & ~pRes[c] ) == 0 && (pRes[c] & ~pOnDc[c]) == 0 );
    Abc_IsopAddLits( pCover, nCost0, nCost1, nVars );
    return nCost0 + nCost1 + nCost2 + (nCost0 >> 16) + (nCost1 >> 16);
}
int Abc_Isop10Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    word uOn0[8], uOn1[8], uOn2[8], uOnDc2[8], uRes0[8], uRes1[8], uRes2[8];
    int c, nCost0, nCost1, nCost2, nVars = 9, nWords = 8;
    // cofactor
    for ( c = 0; c < nWords; c++ )
        uOn0[c] = pOn[c] & ~pOnDc[c+nWords], uOn1[c] = pOn[c+nWords] & ~pOnDc[c];
    // solve for cofactors
    nCost0 = Abc_IsopCheck( uOn0, pOnDc,        uRes0, nVars, nCostLim, pCover );
    if ( nCost0 >= nCostLim ) return nCostLim;
    nCost1 = Abc_IsopCheck( uOn1, pOnDc+nWords, uRes1, nVars, nCostLim, pCover ? pCover + (nCost0 >> 16) : NULL );
    if ( nCost0 + nCost1 >= nCostLim ) return nCostLim;
    for ( c = 0; c < nWords; c++ )
        uOn2[c] = (pOn[c] & ~uRes0[c]) | (pOn[c+nWords] & ~uRes1[c]), uOnDc2[c] = pOnDc[c] & pOnDc[c+nWords];
    nCost2 = Abc_IsopCheck( uOn2, uOnDc2,       uRes2, nVars, nCostLim, pCover ? pCover + (nCost0 >> 16) + (nCost1 >> 16) : NULL );
    if ( nCost0 + nCost1 + nCost2 >= nCostLim ) return nCostLim;
    // derive the final truth table
    for ( c = 0; c < nWords; c++ )
        pRes[c] = uRes2[c] | uRes0[c], pRes[c+nWords] = uRes2[c] | uRes1[c];
    // verify
    for ( c = 0; c < (nWords<<1); c++ )
        assert( (pOn[c]  & ~pRes[c] ) == 0 && (pRes[c] & ~pOnDc[c]) == 0 );
    Abc_IsopAddLits( pCover, nCost0, nCost1, nVars );
    return nCost0 + nCost1 + nCost2 + (nCost0 >> 16) + (nCost1 >> 16);
}
int Abc_Isop11Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    return 0;
}
int Abc_Isop12Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    return 0;
}
int Abc_Isop13Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    return 0;
}
int Abc_Isop14Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    return 0;
}
int Abc_Isop15Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    return 0;
}
int Abc_Isop16Cover( word * pOn, word * pOnDc, word * pRes, int * pCover, int nCostLim )
{
    return 0;
}
int Abc_IsopCheck( word * pOn, word * pOnDc, word * pRes, int nVars, int nCostLim, int * pCover )
{
    int nVarsNew, Cost;
    if ( nVars <= 6 )
        return Abc_Isop6Cover( *pOn, *pOnDc, pRes, nVars, nCostLim, pCover );
    for ( nVarsNew = nVars; nVarsNew > 6; nVarsNew-- )
        if ( Abc_TtHasVar( pOn, nVars, nVarsNew-1 ) || Abc_TtHasVar( pOnDc, nVars, nVarsNew-1 ) )
            break;
    if ( nVarsNew == 6 )
        Cost = Abc_Isop6Cover( *pOn, *pOnDc, pRes, nVarsNew, nCostLim, pCover );
    else
        Cost = s_pFuncIsopCover[nVarsNew]( pOn, pOnDc, pRes, pCover, nCostLim );
    Abc_TtStretch6( pRes, nVarsNew, nVars );
    return Cost;
}

/**Function*************************************************************

  Synopsis    [Compute CNF assuming it does not exceed the limit.]

  Description [Please note that pCover should have at least 32 extra entries!]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_IsopCnf( word * pFunc, int nVars, int nCubeLim, int * pCover )
{
    word pRes[1024];
    int c, Cost0, Cost1, CostLim = nCubeLim << 16;
    assert( Abc_TtHasVar( pFunc, nVars, nVars - 1 ) );
    if ( nVars > 6 )
        Cost0 = s_pFuncIsopCover[nVars]( pFunc, pFunc, pRes, pCover, CostLim );
    else
        Cost0 = Abc_Isop6Cover( *pFunc, *pFunc, pRes, nVars, CostLim, pCover );
    if ( Cost0 >= CostLim )
        return CostLim;
    Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
    if ( nVars > 6 )
        Cost1 = s_pFuncIsopCover[nVars]( pFunc, pFunc, pRes, pCover ? pCover + (Cost0 >> 16) : NULL, CostLim );
    else
        Cost1 = Abc_Isop6Cover( *pFunc, *pFunc, pRes, nVars, CostLim, pCover ? pCover + (Cost0 >> 16) : NULL );
    Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
    if ( Cost0 + Cost1 >= CostLim )
        return CostLim;
    if ( pCover == NULL )
        return Cost0 + Cost1;
    for ( c = 0; c < (Cost0 >> 16); c++ )
        pCover[c] |= (1 << Abc_Var2Lit(nVars, 0));
    for ( c = 0; c < (Cost1 >> 16); c++ )
        pCover[c+(Cost0 >> 16)] |= (1 << Abc_Var2Lit(nVars, 1));
    return Cost0 + Cost1;
}


/**Function*************************************************************

  Synopsis    [These procedures assume that function has exact support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_EsopAddLits( int * pCover, int r0, int r1, int r2, int Max, int Var )
{
    int i;
    if ( Max == r0 )
    {
        r2 >>= 16;
        if ( pCover )
        {
            r0 >>= 16;
            r1 >>= 16;
            for ( i = 0; i < r1; i++ )
                pCover[i] = pCover[r0+i];
            for ( i = 0; i < r2; i++ )
                pCover[r1+i] = pCover[r0+r1+i] | (1 << Abc_Var2Lit(Var,0));
        }
        return r2;
    }
    else if ( Max == r1 )
    {
        r2 >>= 16;
        if ( pCover )
        {
            r0 >>= 16;
            r1 >>= 16;
            for ( i = 0; i < r2; i++ )
                pCover[r0+i] = pCover[r0+r1+i] | (1 << Abc_Var2Lit(Var,1));
        }
        return r2;
    }
    else
    {
        r0 >>= 16;
        r1 >>= 16;
        if ( pCover )
        {
            r2 >>= 16;
            for ( i = 0; i < r0; i++ )
                pCover[i] |= (1 << Abc_Var2Lit(Var,0));
            for ( i = 0; i < r1; i++ )
                pCover[r0+i] |= (1 << Abc_Var2Lit(Var,1));
        }
        return r0 + r1;
    }
}
int Abc_Esop6Cover( word t, int nVars, int nCostLim, int * pCover )
{
    word c0, c1;
    int Var, r0, r1, r2, Max;
    assert( nVars <= 6 );
    if ( t == 0 )
        return 0;
    if ( t == ~(word)0 )
    {
        if ( pCover ) *pCover = 0;
        return 1 << 16;
    }
    assert( nVars > 0 );
    // find the topmost var
    for ( Var = nVars-1; Var >= 0; Var-- )
        if ( Abc_Tt6HasVar( t, Var ) )
             break;
    assert( Var >= 0 );
    // cofactor
    c0 = Abc_Tt6Cofactor0( t, Var );
    c1 = Abc_Tt6Cofactor1( t, Var );
    // call recursively
    r0 = Abc_Esop6Cover( c0,      Var, nCostLim, pCover ? pCover : NULL );
    if ( r0 >= nCostLim ) return nCostLim;
    r1 = Abc_Esop6Cover( c1,      Var, nCostLim, pCover ? pCover + (r0 >> 16) : NULL );
    if ( r1 >= nCostLim ) return nCostLim;
    r2 = Abc_Esop6Cover( c0 ^ c1, Var, nCostLim, pCover ? pCover + (r0 >> 16) + (r1 >> 16) : NULL );
    if ( r2 >= nCostLim ) return nCostLim;
    Max = Abc_MaxInt( r0, Abc_MaxInt(r1, r2) );
    if ( r0 + r1 + r2 - Max >= nCostLim ) return nCostLim;
    return r0 + r1 + r2 - Max + Abc_EsopAddLits( pCover, r0, r1, r2, Max, Var );
}
int Abc_EsopCover( word * pOn, int nVars, int nCostLim, int * pCover )
{
    int c, r0, r1, r2, Max, nWords = (1 << (nVars - 7));
    assert( nVars > 6 );
    assert( Abc_TtHasVar( pOn, nVars, nVars - 1 ) );
    r0 = Abc_EsopCheck( pOn,        nVars-1, nCostLim, pCover );
    if ( r0 >= nCostLim ) return nCostLim;
    r1 = Abc_EsopCheck( pOn+nWords, nVars-1, nCostLim, pCover ? pCover + (r0 >> 16) : NULL );
    if ( r1 >= nCostLim ) return nCostLim;
    for ( c = 0; c < nWords; c++ )
        pOn[c] ^= pOn[nWords+c];
    r2 = Abc_EsopCheck( pOn, nVars-1, nCostLim, pCover ? pCover + (r0 >> 16) + (r1 >> 16) : NULL );
    for ( c = 0; c < nWords; c++ )
        pOn[c] ^= pOn[nWords+c];
    if ( r2 >= nCostLim ) return nCostLim;
    Max = Abc_MaxInt( r0, Abc_MaxInt(r1, r2) );
    if ( r0 + r1 + r2 - Max >= nCostLim ) return nCostLim;
    return r0 + r1 + r2 - Max + Abc_EsopAddLits( pCover, r0, r1, r2, Max, nVars-1 );
}
int Abc_EsopCheck( word * pOn, int nVars, int nCostLim, int * pCover )
{
    int nVarsNew, Cost;
    if ( nVars <= 6 )
        return Abc_Esop6Cover( *pOn, nVars, nCostLim, pCover );
    for ( nVarsNew = nVars; nVarsNew > 6; nVarsNew-- )
        if ( Abc_TtHasVar( pOn, nVars, nVarsNew-1 ) )
            break;
    if ( nVarsNew == 6 )
        Cost = Abc_Esop6Cover( *pOn, nVarsNew, nCostLim, pCover );
    else
        Cost = Abc_EsopCover( pOn, nVarsNew, nCostLim, pCover );
    return Cost;
}

/**Function*************************************************************

  Synopsis    [This procedure assumes that function has exact support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#define ABC_ISOP_MAX_VAR 12
static inline word ** Abc_IsopTtElems()
{
    static word TtElems[ABC_ISOP_MAX_VAR+1][ABC_ISOP_MAX_VAR > 6 ? (1 << (ABC_ISOP_MAX_VAR-6)) : 1], * pTtElems[ABC_ISOP_MAX_VAR+1] = {NULL};
    if ( pTtElems[0] == NULL )
    {
        int v;
        for ( v = 0; v <= ABC_ISOP_MAX_VAR; v++ )
            pTtElems[v] = TtElems[v];
        Abc_TtElemInit( pTtElems, ABC_ISOP_MAX_VAR );
    }
    return pTtElems;
}

/**Function*************************************************************

  Synopsis    [Create truth table for the given cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_IsopBuildTruth( Vec_Int_t * vCover, int nVars, word * pRes, int fXor, int fCompl )
{
    word ** pTtElems = Abc_IsopTtElems();
    word pCube[1024];
    int nWords = Abc_TtWordNum( nVars );
    int c, v, Cube;
    Abc_TtClear( pRes, nWords );
    Vec_IntForEachEntry( vCover, Cube, c )
    {
        Abc_TtFill( pCube, nWords );
        for ( v = 0; v < nVars; v++ )
            if ( ((Cube >> (v << 1)) & 3) == 1 )
                Abc_TtSharp( pCube, pCube, pTtElems[v], nWords );
            else if ( ((Cube >> (v << 1)) & 3) == 2 )
                Abc_TtAnd( pCube, pCube, pTtElems[v], nWords, 0 );
        if ( fXor )
            Abc_TtXor( pRes, pRes, pCube, nWords, 0 );
        else
            Abc_TtOr( pRes, pRes, pCube, nWords );
    }
    if ( fCompl )
        Abc_TtNot( pRes, nWords );
}
static inline void Abc_IsopVerify( word * pFunc, int nVars, word * pRes, Vec_Int_t * vCover, int fXor, int fCompl )
{
    Abc_IsopBuildTruth( vCover, nVars, pRes, fXor, fCompl );
    if ( !Abc_TtEqual( pFunc, pRes, Abc_TtWordNum(nVars) ) )
        printf( "Verification failed.\n" );
}

/**Function*************************************************************

  Synopsis    [This procedure assumes that function has exact support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_Isop( word * pFunc, int nVars, int Type, int nCubeLim, Vec_Int_t * vCover )
{
    word pRes[1024];
    int Limit = nCubeLim ? nCubeLim : 0xFFFF; 
    int LimitXor = nCubeLim ? 3 * Limit : 3 * (nVars + 1); 
    int nCost0 = -1, nCost1 = -1, nCost2 = -1;
    assert( nVars <= 16 );
    assert( Abc_TtHasVar( pFunc, nVars, nVars - 1 ) );
    assert( !(Type & 4) );
    // xor polarity
    if ( Type & 4 )
        nCost2 = Abc_EsopCheck( pFunc, nVars, LimitXor << 16, NULL );
    // direct polarity
    if ( Type & 1 )
        nCost0 = Abc_IsopCheck( pFunc, pFunc, pRes, nVars, Abc_MinInt(Limit, 3*nCost2) << 16, NULL );
    // opposite polarity
    if ( Type & 2 )
    {
        Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
        nCost1 = Abc_IsopCheck( pFunc, pFunc, pRes, nVars, Abc_MinInt(nCost0, Abc_MinInt(Limit, 3*nCost2)) << 16, NULL );
        Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
    }
    assert( nCost0 >= 0 || nCost1 >= 0 );
    // find minimum cover
    if ( nCost0 <= nCost1 || nCost0 != -1 )
    {
        Vec_IntFill( vCover, -1, nCost0 >> 16 );
        Abc_IsopCheck( pFunc, pFunc, pRes, nVars, ABC_INFINITY, Vec_IntArray(vCover) );
        Abc_IsopVerify( pFunc, nVars, pRes, vCover, 0, 0 );
        return 0;
    }
    if ( nCost1 < nCost0 || nCost1 != -1 )
    {
        Vec_IntFill( vCover, -1, nCost1 >> 16 );
        Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
        Abc_IsopCheck( pFunc, pFunc, pRes, nVars, ABC_INFINITY, Vec_IntArray(vCover) );
        Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
        Abc_IsopVerify( pFunc, nVars, pRes, vCover, 0, 1 );
        return 1;
    }
    assert( 0 );
    return -1;
}

/**Function*************************************************************

  Synopsis    [Compute CNF assuming it does not exceed the limit.]

  Description [Please note that pCover should have at least 32 extra entries!]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_IsopTest( word * pFunc, int nVars, Vec_Int_t * vCover )
{
    int Cost, fVerbose = 0;
    word pRes[1024];
//    if ( fVerbose )
//    Dau_DsdPrintFromTruth( pFunc, nVars ), printf( "         " );

    Cost = Abc_IsopCheck( pFunc, pFunc, pRes, nVars, ABC_INFINITY, Vec_IntArray(vCover) );
    vCover->nSize = Cost >> 16;
    assert( vCover->nSize <= vCover->nCap );
    if ( fVerbose )
    printf( "%5d(%5d) ", Cost >> 16, Cost & 0xFFFF );
    Abc_IsopVerify( pFunc, nVars, pRes, vCover, 0, 0 );


    Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
    Cost = Abc_IsopCheck( pFunc, pFunc, pRes, nVars, ABC_INFINITY, Vec_IntArray(vCover) );
    Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
    vCover->nSize = Cost >> 16;
    assert( vCover->nSize <= vCover->nCap );
    if ( fVerbose )
    printf( "%5d(%5d) ", Cost >> 16, Cost & 0xFFFF );
    Abc_IsopVerify( pFunc, nVars, pRes, vCover, 0, 1 );


    Cost = Abc_EsopCheck( pFunc, nVars, ABC_INFINITY, Vec_IntArray(vCover) );
    vCover->nSize = Cost >> 16;
    assert( vCover->nSize <= vCover->nCap );
    if ( fVerbose )
    printf( "%5d(%5d)  ", Cost >> 16, Cost & 0xFFFF );
    Abc_IsopVerify( pFunc, nVars, pRes, vCover, 1, 0 );


    Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
    Cost = Abc_EsopCheck( pFunc, nVars, ABC_INFINITY, Vec_IntArray(vCover) );
    Abc_TtNot( pFunc, Abc_TtWordNum(nVars) );
    vCover->nSize = Cost >> 16;
    assert( vCover->nSize <= vCover->nCap );
    if ( fVerbose )
    printf( "%5d(%5d)  ", Cost >> 16, Cost & 0xFFFF );
    Abc_IsopVerify( pFunc, nVars, pRes, vCover, 1, 1 );


    if ( fVerbose )
    printf( "\n" );
//Kit_TruthIsopPrintCover( vCover, nVars, 0 );
    return 1; 
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

