/**CFile****************************************************************

  FileName    [bmcMaj9.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Exact synthesis with majority gates.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 1, 2017.]

  Revision    [$Id: bmcMaj9.c,v 1.00 2017/10/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/kissat/kissat.h"
#include "aig/miniaig/miniaig.h"
#include "base/io/ioResub.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"

#include <unistd.h>
#include <limits.h>

#define KISSAT_UNSAT 20
#define KISSAT_SAT   10
#define KISSAT_UNDEC  0

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MAJ_NOBJS  64 // Const0 + Const1 + nVars + nNodes

typedef struct Exa9_Man_t_ Exa9_Man_t;
struct Exa9_Man_t_ 
{
    Bmc_EsPar_t *     pPars;     // parameters
    int               nVars;     // inputs
    int               nNodes;    // internal nodes
    int               nObjs;     // total objects (nVars inputs + nNodes internal nodes)
    int               nWords;    // the truth table size in 64-bit words
    int               nMints;    // number of input minterms
    int               nSelVars;  // number of selection variables (fanin + output)
    int               nValVars;  // number of value variables
    int               nVarAlloc; // total vars reserved in the solver
    int               nClausesStart; // clauses added in the structural part (excluding 1-hot)
    int               nClausesHot;   // clauses added for 1-hot constraints
    int               nClausesMints; // clauses added per-minterm
    int               fCountStruct;  // flag: counting structural clauses
    int               fCountHot;     // flag: counting 1-hot clauses
    word *            pTruth;    // truth table
    Vec_Wrd_t *       vTruths;   // computed truth tables
    kissat *          pSat;      // SAT solver
    abctime           timeStop;  // runtime limit (0 = unlimited)
};

static inline int Exa9_LitToKissat( int Lit )
{
    int v = Abc_Lit2Var( Lit );
    assert( v > 0 );
    return Abc_LitIsCompl( Lit ) ? -v : v;
}
static inline int Exa9_KissatAddClause( Exa9_Man_t * p, int * pLits, int nLits )
{
    int i;
    for ( i = 0; i < nLits; i++ )
        kissat_add( p->pSat, Exa9_LitToKissat( pLits[i] ) );
    kissat_add( p->pSat, 0 );
    if ( p->fCountStruct )
    {
        if ( p->fCountHot )
            p->nClausesHot++;
        else
            p->nClausesStart++;
    }
    else
        p->nClausesMints++;
    return !kissat_is_inconsistent( p->pSat );
}
static inline int Exa9_KissatVarValue( Exa9_Man_t * p, int v )
{
    assert( v > 0 );
    return kissat_value( p->pSat, v ) > 0;
}
static int Exa9_KissatTerminate( void * pData )
{
    Exa9_Man_t * p = (Exa9_Man_t *)pData;
    return p && p->timeStop && Abc_Clock() > p->timeStop;
}

static inline word *  Exa9_ManTruth( Exa9_Man_t * p, int v ) { return Vec_WrdEntryP( p->vTruths, p->nWords * v ); }

static inline int     Exa9_ManSelVar( Exa9_Man_t * p, int iNode, int iFanin, int fCompl, int iObj )
{
    return 1 + (((iNode * 2 + iFanin) * 2 + fCompl) * p->nObjs + (iObj - 1));
}
static inline int     Exa9_ManSelVarAux( Exa9_Man_t * p, int iNode, int iFanin, int fCompl, int iObj )
{
    return 1 + p->nSelVars + (((iNode * 2 + iFanin) * 2 + fCompl) * p->nObjs + (iObj - 1));
}
static inline int     Exa9_ManSelVarOut( Exa9_Man_t * p, int fCompl, int iObj )
{
    return 1 + 4 * p->nNodes * p->nObjs + fCompl * p->nObjs + (iObj - 1);
}
static inline int     Exa9_ManSelVarOutAux( Exa9_Man_t * p, int fCompl, int iObj )
{
    return 1 + p->nSelVars + 4 * p->nNodes * p->nObjs + fCompl * p->nObjs + (iObj - 1);
}
static inline int     Exa9_ManValueVar( Exa9_Man_t * p, int iObj, int Place, int iMint )
{
    int Base = 1 + 2 * p->nSelVars;
    return Base + ((iObj - 1) * 3 + Place) * p->nMints + iMint;
}

// return auxiliary vars actually used by a 1-hot of size nLits under the chosen encoding
static inline int Exa9_ManCountAuxOneHot( int nLits, int Algo )
{
    if ( nLits <= 1 )
        return 0;
    if ( Algo == 0 ) // naive pairwise
        return 0;
    if ( Algo == 1 ) // sequential
        return nLits - 1;
    if ( Algo == 2 ) // bimander
    {
        const int GroupSize = 6;
        if ( nLits <= GroupSize )
            return 0;
        {
            int nGroups = (nLits + GroupSize - 1) / GroupSize;
            int nBits   = Abc_Base2Log( nGroups );
            return nBits;
        }
    }
    if ( Algo == 3 ) // commander
    {
        const int GroupSize = 5;
        if ( nLits <= GroupSize )
            return 0;
        {
            int nGroups = (nLits + GroupSize - 1) / GroupSize;
            return nGroups;
        }
    }
    return 0;
}

static int Exa9_ManCountAuxTotal( Exa9_Man_t * p )
{
    int Algo = p->pPars->n1HotAlgo;
    int Total = 0;
    int n;
    // fanin selectors (two fanins * two polarities per node)
    for ( n = 0; n < p->nNodes; n++ )
    {
        int Obj = p->nVars + n + 1;
        int nLits = Obj - 1; // choices for each polarity
        int AuxPerGroup = Exa9_ManCountAuxOneHot( nLits, Algo );
        Total += 4 * AuxPerGroup;
    }
    // output selector (two polarities over all objects)
    Total += Exa9_ManCountAuxOneHot( 2 * p->nObjs, Algo );
    return Total;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Exa9_ManVarReserve( Exa9_Man_t * p )
{
    int64_t Count = 2 * (int64_t)p->nSelVars + (int64_t)p->nValVars;
    if ( Count > INT_MAX )
        Count = INT_MAX;
    return (int)Count;
}
static Exa9_Man_t * Exa9_ManAlloc( Bmc_EsPar_t * pPars, word * pTruth )
{
    Exa9_Man_t * p = ABC_CALLOC( Exa9_Man_t, 1 );
    p->pPars      = pPars;
    p->nVars      = pPars->nVars;
    p->nNodes     = pPars->nNodes;
    p->nObjs      = pPars->nVars + pPars->nNodes;
    p->nWords     = Abc_TtWordNum(pPars->nVars);
    p->nMints     = 1 << pPars->nVars;
    p->nSelVars   = p->nNodes * 4 * p->nObjs + 2 * p->nObjs;
    p->nValVars   = 3 * p->nObjs * p->nMints;
    p->nVarAlloc  = Exa9_ManVarReserve( p );
    p->nClausesStart = p->nClausesHot = p->nClausesMints = 0;
    p->fCountStruct  = 0;
    p->fCountHot     = 0;
    p->pTruth     = pTruth;
    p->vTruths    = Vec_WrdStart( p->nWords * (p->nObjs + 1) );
    p->pSat       = kissat_init();
    {
        int nBias = 0; // 0=neutral, 1=SAT bias, -1=UNSAT bias
        if ( nBias > 0 )
        {
            kissat_set_option( p->pSat, "target", 2 );
            kissat_set_option( p->pSat, "restartint", 50 );
        }
        else if ( nBias < 0 )
            kissat_set_option( p->pSat, "stable", 0 );
    }
    assert( Exa9_ManValueVar( p, p->nObjs, 2, p->nMints - 1 ) <= p->nVarAlloc );
    kissat_reserve( p->pSat, p->nVarAlloc );
    if ( pPars->Seed > 0 )
        kissat_set_option( p->pSat, "seed", pPars->Seed );
    p->timeStop   = 0;
    return p;
}
static void Exa9_ManFree( Exa9_Man_t * p )
{
    kissat_release( p->pSat );
    Vec_WrdFree( p->vTruths );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Exa9_ManAddUnit( Exa9_Man_t * p, int Var, int fCompl )
{
    int Lit = Abc_Var2Lit( Var, fCompl );
    return Exa9_KissatAddClause( p, &Lit, 1 );
}
static inline int Exa9_ManAddEquality( Exa9_Man_t * p, int iSel, int iFan, int iOut, int fCompl )
{
    int pLits[3];
    pLits[0] = Abc_Var2Lit( iSel, 1 );
    pLits[1] = Abc_Var2Lit( iFan, 1 );
    pLits[2] = Abc_Var2Lit( iOut, fCompl );
    if ( !Exa9_KissatAddClause( p, pLits, 3 ) )
        return 0;
    pLits[1] = Abc_Var2Lit( iFan, 0 );
    pLits[2] = Abc_Var2Lit( iOut, !fCompl );
    return Exa9_KissatAddClause( p, pLits, 3 );
}
static int Exa9_ManAddOneHotQuad( Exa9_Man_t * p, Vec_Int_t * vLits )
{
    int * pArray = Vec_IntArray( vLits );
    int nLits = Vec_IntSize( vLits );
    int i, k;
    assert( nLits > 0 );
    if ( !Exa9_KissatAddClause( p, pArray, nLits ) )
        return 0;
    for ( i = 0; i < nLits; i++ )
    for ( k = i + 1; k < nLits; k++ )
    {
        int pLits[2] = { Abc_LitNot(pArray[i]), Abc_LitNot(pArray[k]) };
        if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
            return 0;
    }
    return 1;
}
static int Exa9_ManAddOneHotSeq( Exa9_Man_t * p, Vec_Int_t * vLits, Vec_Int_t * vAux )
{
    int nLits = Vec_IntSize( vLits );
    int * x = Vec_IntArray( vLits );
    int * y = Vec_IntArray( vAux );
    int pLits[2], i;
    assert( nLits > 0 );
    if ( !Exa9_KissatAddClause( p, x, nLits ) )
        return 0;
    if ( nLits == 1 )
        return 1;
    assert( Vec_IntSize(vAux) >= nLits - 1 );
    // (¬x1 ∨ y1)
    pLits[0] = Abc_LitNot( x[0] );
    pLits[1] = Abc_Var2Lit( y[0], 0 );
    if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
        return 0;
    // middle constraints
    for ( i = 1; i < nLits - 1; i++ )
    {
        // (¬xi ∨ yi)
        pLits[0] = Abc_LitNot( x[i] );
        pLits[1] = Abc_Var2Lit( y[i], 0 );
        if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
            return 0;
        // (¬yi-1 ∨ yi)
        pLits[0] = Abc_LitNot( Abc_Var2Lit( y[i-1], 0 ) );
        pLits[1] = Abc_Var2Lit( y[i], 0 );
        if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
            return 0;
        // (¬xi ∨ ¬yi-1)
        pLits[0] = Abc_LitNot( x[i] );
        pLits[1] = Abc_LitNot( Abc_Var2Lit( y[i-1], 0 ) );
        if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
            return 0;
    }
    // (¬xn ∨ ¬y_{n-1})
    pLits[0] = Abc_LitNot( x[nLits-1] );
    pLits[1] = Abc_LitNot( Abc_Var2Lit( y[nLits-2], 0 ) );
    return Exa9_KissatAddClause( p, pLits, 2 );
}
static inline int Exa9_ManAddAtMostOnePair( Exa9_Man_t * p, Vec_Int_t * vLits )
{
    int nLits = Vec_IntSize( vLits );
    int * x = Vec_IntArray( vLits );
    int pLits[2], i, j;
    for ( i = 0; i < nLits; i++ )
    for ( j = i + 1; j < nLits; j++ )
    {
        pLits[0] = Abc_LitNot( x[i] );
        pLits[1] = Abc_LitNot( x[j] );
        if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
            return 0;
    }
    return 1;
}
static int Exa9_ManAddOneHotBim( Exa9_Man_t * p, Vec_Int_t * vLits, Vec_Int_t * vAux )
{
    int nLits = Vec_IntSize( vLits );
    int * x = Vec_IntArray( vLits );
    int * y = Vec_IntArray( vAux );
    int pLits[2], i, j, g;
    int GroupSize = 6;
    if ( nLits == 0 )
        return 0;
    if ( !Exa9_KissatAddClause( p, x, nLits ) )
        return 0;
    if ( nLits == 1 )
        return 1;
    if ( nLits <= GroupSize )
        return Exa9_ManAddOneHotQuad( p, vLits );
    {
        int nGroups = (nLits + GroupSize - 1) / GroupSize;
        int nBits   = Abc_Base2Log( nGroups );
        if ( nBits == 0 )
            return Exa9_ManAddOneHotQuad( p, vLits );
        assert( Vec_IntSize(vAux) >= nBits );
        // pairwise inside each group
        for ( g = 0; g < nGroups; g++ )
        {
            int iStart = g * GroupSize;
            int iStop  = Abc_MinInt( iStart + GroupSize, nLits );
            for ( i = iStart; i < iStop; i++ )
            for ( j = i + 1; j < iStop; j++ )
            {
                pLits[0] = Abc_LitNot( x[i] );
                pLits[1] = Abc_LitNot( x[j] );
                if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
                    return 0;
            }
            // connect literals in the group to shared binary variables
            for ( i = iStart; i < iStop; i++ )
            {
                int Code = g;
                int b;
                for ( b = 0; b < nBits; b++, Code >>= 1 )
                {
                    pLits[0] = Abc_LitNot( x[i] );
                    pLits[1] = (Code & 1) ? Abc_Var2Lit( y[b], 0 ) : Abc_LitNot( Abc_Var2Lit( y[b], 0 ) );
                    if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
                        return 0;
                }
            }
        }
    }
    return 1;
}
static int Exa9_ManAddOneHotCom( Exa9_Man_t * p, Vec_Int_t * vLits, Vec_Int_t * vAux )
{
    int nLits = Vec_IntSize( vLits );
    int * x = Vec_IntArray( vLits );
    int * y = Vec_IntArray( vAux );
    int GroupSize = 4;
    int i, j, g;
    Vec_Int_t * vCmd;
    if ( nLits == 0 )
        return 0;
    if ( !Exa9_KissatAddClause( p, x, nLits ) )
        return 0;
    if ( nLits == 1 )
        return 1;
    if ( nLits <= GroupSize )
        return Exa9_ManAddOneHotQuad( p, vLits );
    vCmd = Vec_IntAlloc(16);
    {
        int nGroups = (nLits + GroupSize - 1) / GroupSize;
        if ( nGroups > Vec_IntSize(vAux) )
        {
            Vec_IntFree( vCmd );
            return Exa9_ManAddOneHotQuad( p, vLits );
        }
        for ( g = 0; g < nGroups; g++ )
        {
            int CmdVar = y[g];
            Vec_IntPush( vCmd, Abc_Var2Lit( CmdVar, 0 ) );
            int iStart = g * GroupSize;
            int iStop  = Abc_MinInt( iStart + GroupSize, nLits );
            // CmdVar => at least one literal in the group
            {
                int pLits[6]; // GroupSize <= 5
                int nCls = 0;
                pLits[nCls++] = Abc_LitNot( Abc_Var2Lit( CmdVar, 0 ) );
                for ( i = iStart; i < iStop; i++ )
                    pLits[nCls++] = x[i];
                assert( nCls <= 6 );
                if ( !Exa9_KissatAddClause( p, pLits, nCls ) )
                {
                    Vec_IntFree( vCmd );
                    return 0;
                }
            }
            for ( i = iStart; i < iStop; i++ )
            {
                int pLits[2] = { Abc_LitNot( x[i] ), Abc_Var2Lit( CmdVar, 0 ) };
                if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
                {
                    Vec_IntFree( vCmd );
                    return 0;
                }
            }
            for ( i = iStart; i < iStop; i++ )
            for ( j = i + 1; j < iStop; j++ )
            {
                int pLits[2] = { Abc_LitNot( x[i] ), Abc_LitNot( x[j] ) };
                if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
                {
                    Vec_IntFree( vCmd );
                    return 0;
                }
            }
        }
    }
    if ( !Exa9_ManAddAtMostOnePair( p, vCmd ) )
    {
        Vec_IntFree( vCmd );
        return 0;
    }
    Vec_IntFree( vCmd );
    return 1;
}
static int Exa9_ManAddOneHot( Exa9_Man_t * p, Vec_Int_t * vLits, Vec_Int_t * vAux )
{
    int Res = 0;
    int fOldHot = p->fCountHot;
    p->fCountHot = 1;
    if ( Vec_IntSize(vLits) < 7 )
        Res = Exa9_ManAddOneHotQuad( p, vLits );
    else if ( p->pPars->n1HotAlgo == 1 )
        Res = Exa9_ManAddOneHotSeq( p, vLits, vAux );
    else if ( p->pPars->n1HotAlgo == 2 )
        Res = Exa9_ManAddOneHotBim( p, vLits, vAux );
    else if ( p->pPars->n1HotAlgo == 3 )
        Res = Exa9_ManAddOneHotCom( p, vLits, vAux );
    else
        Res = Exa9_ManAddOneHotQuad( p, vLits );
    p->fCountHot = fOldHot;
    return Res;
}
static int Exa9_ManAddCnfStart( Exa9_Man_t * p )
{
    p->fCountStruct = 1;
    Vec_Int_t * vLits = Vec_IntAlloc( 100 );
    Vec_Int_t * vAux  = Vec_IntAlloc( 100 );
    Vec_Int_t * vUse  = Vec_IntAlloc( 100 );
    int n, j, k, c, Var;
    for ( n = 0; n < p->nNodes; n++ )
    {
        int Obj = p->nVars + n + 1;
        for ( k = 0; k < 2; k++ )
        {
            Vec_IntClear( vLits );
            Vec_IntClear( vAux );
            for ( j = 1; j <= p->nObjs; j++ )
            for ( c = 0; c < 2; c++ )
            {
                Var = Exa9_ManSelVar( p, n, k, c, j );
                if ( j >= Obj )
                {
                    if ( !Exa9_ManAddUnit( p, Var, 1 ) )
                    {
                        Vec_IntFree( vLits );
                        Vec_IntFree( vAux );
                        return 0;
                    }
                    continue;
                }
                Vec_IntPush( vLits, Abc_Var2Lit( Var, 0 ) );
                Vec_IntPush( vAux, Exa9_ManSelVarAux( p, n, k, c, j ) );
            }
            if ( Vec_IntSize(vLits) == 0 || !Exa9_ManAddOneHot( p, vLits, vAux ) )
            {
                Vec_IntFree( vLits );
                Vec_IntFree( vAux );
                return 0;
            }
        }
        // enforce first fanin index < second fanin index
        for ( j = 1; j < Obj; j++ )
        for ( c = 0; c < 2; c++ )
        {
            int Var0 = Exa9_ManSelVar( p, n, 0, c, j );
            int j2, c2;
            for ( j2 = 1; j2 <= j; j2++ )
            for ( c2 = 0; c2 < 2; c2++ )
            {
                int Var1 = Exa9_ManSelVar( p, n, 1, c2, j2 );
                int pLits[2] = { Abc_Var2Lit( Var0, 1 ), Abc_Var2Lit( Var1, 1 ) };
                if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
                {
                    Vec_IntFree( vLits );
                    Vec_IntFree( vAux );
                    return 0;
                }
            }
        }
        /*
        // order nodes by larger (second) fanin index
        for ( j = 1; j < Obj; j++ )
        for ( c = 0; c < 2; c++ )
        {
            int VarLargeThis = Exa9_ManSelVar( p, n, 1, c, j );
            int m, k, c3;
            for ( m = 0; m < n; m++ )
            {
                int ObjM = p->nVars + m + 1;
                if ( j + 1 >= ObjM )
                    continue;
                for ( k = j + 1; k < ObjM; k++ )
                for ( c3 = 0; c3 < 2; c3++ )
                {
                    int VarLargePrev = Exa9_ManSelVar( p, m, 1, c3, k );
                    int pLits[2] = { Abc_Var2Lit( VarLargeThis, 1 ), Abc_Var2Lit( VarLargePrev, 1 ) };
                    if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
                    {
                        Vec_IntFree( vLits );
                        Vec_IntFree( vAux );
                        Vec_IntFree( vUse );
                        return 0;
                    }
                }
            }
        }
        // forbid duplicate fanin pairs across nodes (respecting polarity)
        for ( int m = 0; m < n; m++ )
        {
            int j2, c2, ObjM = p->nVars + m + 1;
            for ( j = 1; j + 1 < ObjM; j++ )
            for ( j2 = j + 1; j2 < ObjM; j2++ )
            for ( c = 0; c < 2; c++ )
            for ( c2 = 0; c2 < 2; c2++ )
            {
                int VarN0 = Exa9_ManSelVar( p, n, 0, c,  j );
                int VarN1 = Exa9_ManSelVar( p, n, 1, c2, j2 );
                int VarM0 = Exa9_ManSelVar( p, m, 0, c,  j );
                int VarM1 = Exa9_ManSelVar( p, m, 1, c2, j2 );
                int pLits4[4] = { Abc_Var2Lit( VarN0, 1 ), Abc_Var2Lit( VarN1, 1 ),
                                  Abc_Var2Lit( VarM0, 1 ), Abc_Var2Lit( VarM1, 1 ) };
                if ( !Exa9_KissatAddClause( p, pLits4, 4 ) )
                {
                    Vec_IntFree( vLits );
                    Vec_IntFree( vAux );
                    Vec_IntFree( vUse );
                    return 0;
                }
            }
        }
        */
    }
    // output connectivity (one-hot over all objects and two polarities)
    Vec_IntClear( vLits );
    Vec_IntClear( vAux );
    for ( j = 1; j <= p->nObjs; j++ )
    for ( c = 0; c < 2; c++ )
    {
        Vec_IntPush( vLits, Abc_Var2Lit( Exa9_ManSelVarOut(p, c, j), 0 ) );
        Vec_IntPush( vAux, Exa9_ManSelVarOutAux( p, c, j ) );
    }
    if ( Vec_IntSize(vLits) == 0 || !Exa9_ManAddOneHot( p, vLits, vAux ) )
    {
        Vec_IntFree( vLits );
        Vec_IntFree( vAux );
        Vec_IntFree( vUse );
        return 0;
    }
    // ensure each object (PI or internal) is used at least once as a fanin of some node/output
    for ( j = 1; j <= p->nObjs; j++ )
    {
        Vec_IntClear( vUse );
        for ( n = 0; n < p->nNodes; n++ )
        {
            int Obj = p->nVars + n + 1;
            if ( Obj <= j )
                continue;
            for ( k = 0; k < 2; k++ )
            for ( c = 0; c < 2; c++ )
                Vec_IntPush( vUse, Abc_Var2Lit( Exa9_ManSelVar(p, n, k, c, j), 0 ) );
        }
        for ( c = 0; c < 2; c++ )
            Vec_IntPush( vUse, Abc_Var2Lit( Exa9_ManSelVarOut(p, c, j), 0 ) );
        if ( Vec_IntSize(vUse) == 0 )
            continue;
        if ( !Exa9_KissatAddClause( p, Vec_IntArray(vUse), Vec_IntSize(vUse) ) )
        {
            Vec_IntFree( vLits );
            Vec_IntFree( vAux );
            Vec_IntFree( vUse );
            return 0;
        }
    }
    Vec_IntFree( vLits );
    Vec_IntFree( vAux );
    Vec_IntFree( vUse );
    return 1;
}
static int Exa9_ManAddCnf( Exa9_Man_t * p, int iMint )
{
    p->fCountStruct = 0;
    int i, j, k, c;
    // assign primary input values for this minterm
    for ( i = 1; i <= p->nVars; i++ )
    {
        int Value = (iMint >> (i-1)) & 1;
        int VarOut = Exa9_ManValueVar( p, i, 2, iMint );
        if ( !Exa9_ManAddUnit( p, VarOut, !Value ) )
            return 0;
    }
    // internal nodes
    for ( i = 0; i < p->nNodes; i++ )
    {
        int Obj = p->nVars + i + 1;
        int VarFan[2] = { Exa9_ManValueVar( p, Obj, 0, iMint ), Exa9_ManValueVar( p, Obj, 1, iMint ) };
        int VarOut    = Exa9_ManValueVar( p, Obj, 2, iMint );
        for ( k = 0; k < 2; k++ )
        {
            for ( j = 1; j < Obj; j++ )
            for ( c = 0; c < 2; c++ )
            {
                int SelVar = Exa9_ManSelVar( p, i, k, c, j );
                int SrcVal = Exa9_ManValueVar( p, j, 2, iMint );
                if ( !Exa9_ManAddEquality( p, SelVar, VarFan[k], SrcVal, c ) )
                    return 0;
            }
        }
        // functionality clauses for a*b = out
        {
            int pLits1[2] = { Abc_Var2Lit( VarFan[0], 0 ), Abc_Var2Lit( VarOut, 1 ) };
            int pLits2[2] = { Abc_Var2Lit( VarFan[1], 0 ), Abc_Var2Lit( VarOut, 1 ) };
            int pLits3[3] = { Abc_Var2Lit( VarFan[0], 1 ), Abc_Var2Lit( VarFan[1], 1 ), Abc_Var2Lit( VarOut, 0 ) };
            if ( !Exa9_KissatAddClause( p, pLits1, 2 ) ) return 0;
            if ( !Exa9_KissatAddClause( p, pLits2, 2 ) ) return 0;
            if ( !Exa9_KissatAddClause( p, pLits3, 3 ) ) return 0;
        }
    }
    // constrain the output to match the target function via selected source
    {
        int Value  = Abc_TtGetBit( p->pTruth, iMint );
        for ( j = 1; j <= p->nObjs; j++ )
        for ( c = 0; c < 2; c++ )
        {
            int SelVar = Exa9_ManSelVarOut( p, c, j );
            int SrcVal = Exa9_ManValueVar( p, j, 2, iMint );
            int pLits[2] = { Abc_Var2Lit( SelVar, 1 ), Abc_Var2Lit( SrcVal, (Value ^ c) ? 0 : 1 ) };
            if ( !Exa9_KissatAddClause( p, pLits, 2 ) )
                return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Exa9_ManFindFanin( Exa9_Man_t * p, int Obj, int k, int * pCompl )
{
    int n = Obj - p->nVars - 1;
    int j, c;
    assert( Obj > p->nVars && n >= 0 && n < p->nNodes );
    for ( j = 1; j < Obj; j++ )
    for ( c = 0; c < 2; c++ )
    {
        int Var = Exa9_ManSelVar( p, n, k, c, j );
        if ( Exa9_KissatVarValue(p, Var) )
        {
            if ( pCompl )
                *pCompl = c;
            return j;
        }
    }
    assert( 0 );
    return -1;
}
static inline int Exa9_ManFindOutput( Exa9_Man_t * p, int * pCompl )
{
    int j, c;
    for ( j = 1; j <= p->nObjs; j++ )
    for ( c = 0; c < 2; c++ )
        if ( Exa9_KissatVarValue(p, Exa9_ManSelVarOut(p, c, j)) )
        {
            if ( pCompl )
                *pCompl = c;
            return j;
        }
    assert( 0 );
    return -1;
}
static int Exa9_ManEval( Exa9_Man_t * p )
{
    int i, c0, c1, i0, i1;
    int cOut, iOutObj;
    for ( i = 1; i <= p->nVars; i++ )
        Abc_TtIthVar( Exa9_ManTruth(p, i), i-1, p->nVars );
    for ( i = p->nVars + 1; i <= p->nObjs; i++ )
    {
        i0 = Exa9_ManFindFanin( p, i, 0, &c0 );
        i1 = Exa9_ManFindFanin( p, i, 1, &c1 );
        Abc_TtAndCompl( Exa9_ManTruth(p, i), Exa9_ManTruth(p, i0), c0, Exa9_ManTruth(p, i1), c1, p->nWords );
    }
    iOutObj = Exa9_ManFindOutput( p, &cOut );
    if ( cOut )
    {
        Abc_TtNot( Exa9_ManTruth(p, iOutObj), p->nWords );
        i0 = Abc_TtFindFirstDiffBit( Exa9_ManTruth(p, iOutObj), p->pTruth, p->nVars );
        Abc_TtNot( Exa9_ManTruth(p, iOutObj), p->nWords );
        return i0;
    }
    return Abc_TtFindFirstDiffBit( Exa9_ManTruth(p, iOutObj), p->pTruth, p->nVars );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Exa9_ManName( Exa9_Man_t * p, int Obj, char * pBuf, int fFinal )
{
    if ( Obj <= p->nVars )
        sprintf( pBuf, "%c", 'a'+Obj-1 );
    else if ( fFinal )
        sprintf( pBuf, "F" );
    else
        sprintf( pBuf, "%02d", Obj );
}
static void Exa9_ManPrintSolution( Exa9_Man_t * p )
{
    int i, c0, c1, i0, i1, cOut, iOutObj;
    int nInv = 0;
    char Buf0[16], Buf1[16];
    iOutObj = Exa9_ManFindOutput( p, &cOut );
    nInv += cOut;
    for ( i = p->nVars + 1; i <= p->nObjs; i++ )
    {
        Exa9_ManFindFanin( p, i, 0, &c0 );
        Exa9_ManFindFanin( p, i, 1, &c1 );
        nInv += c0 + c1;
    }
    printf( "Realization of given %d-input function using %d two-input and-nodes and %d inverters:\n", p->nVars, p->nNodes, nInv );
    if ( iOutObj <= p->nVars ) sprintf( Buf0, "%c", 'a'+iOutObj-1 );
    else sprintf( Buf0, "%c", 'A'+iOutObj-p->nVars-1 );
    printf( "F =%s%s\n", cOut ? " !" : "  ", Buf0 );
    for ( i = p->nObjs; i > p->nVars; i-- )
    {
        i0 = Exa9_ManFindFanin( p, i, 0, &c0 );
        i1 = Exa9_ManFindFanin( p, i, 1, &c1 );
        if ( i0 <= p->nVars ) sprintf( Buf0, "%c", 'a'+i0-1 );
        else sprintf( Buf0, "%c", 'A'+i0-p->nVars-1 );
        if ( i1 <= p->nVars ) sprintf( Buf1, "%c", 'a'+i1-1 );
        else sprintf( Buf1, "%c", 'A'+i1-p->nVars-1 );
        printf( "%c =%s%s  & %s%s\n", 'A'+i-p->nVars-1, c0 ? " !" : "  ", Buf0, c1 ? " !" : "  ", Buf1 );
    }
}
static void Exa9_ManDumpBlif( Exa9_Man_t * p )
{
    int i, c0, c1, i0, i1, cOut, iOutObj;
    char pFileName[1000];
    char Buf0[16], Buf1[16], BufOut[16];
    char * pStr = Abc_UtilStrsav(p->pPars->pSymStr ? p->pPars->pSymStr : p->pPars->pTtStr);
    if ( strlen(pStr) > 16 ) {
        pStr[16] = '_';
        pStr[17] = '\0';
    }    
    sprintf( pFileName, "%s.blif", pStr );
    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL ) return;
    fprintf( pFile, "# Realization of given %d-input function using %d two-input and-nodes synthesized by ABC on %s\n", p->nVars, p->nNodes, Extra_TimeStamp() );
    fprintf( pFile, ".model %s\n", pStr );
    fprintf( pFile, ".inputs" );
    for ( i = 0; i < p->nVars; i++ )
        fprintf( pFile, " %c", 'a'+i );
    fprintf( pFile, "\n.outputs F\n" );
    for ( i = p->nVars + 1; i <= p->nObjs; i++ )
    {
        i0 = Exa9_ManFindFanin( p, i, 0, &c0 );
        i1 = Exa9_ManFindFanin( p, i, 1, &c1 );
        Exa9_ManName( p, i0, Buf0, 0 );
        Exa9_ManName( p, i1, Buf1, 0 );
        Exa9_ManName( p, i,  BufOut, 0 );
        fprintf( pFile, ".names %s %s %s\n", Buf0, Buf1, BufOut );
        fprintf( pFile, "%d%d 1\n", !c0, !c1 );
    }
    iOutObj = Exa9_ManFindOutput( p, &cOut );
    Exa9_ManName( p, iOutObj, Buf0, iOutObj == p->nObjs );
    fprintf( pFile, ".names %s F\n", Buf0 );
    fprintf( pFile, "%d 1\n", cOut ? 0 : 1 );
    fprintf( pFile, ".end\n\n" );
    fclose( pFile );
    if ( !p->pPars->fSilent ) printf( "Finished dumping the resulting network into file \"%s\".\n", pFileName );
    ABC_FREE( pStr );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Exa9_ManExactSynthesis( Bmc_EsPar_t * pPars )
{
    extern int Exa9_ManExactSynthesisIter( Bmc_EsPar_t * pPars );
    if ( pPars->fMinNodes ) 
        return Exa9_ManExactSynthesisIter( pPars );
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "Params:    I = %d  M = %d  H = %d  S = %d  T = %d   i = %d  a = %d  m = %d  d = %d  v = %d  s = %d\n", 
            pPars->nVars, pPars->nNodes, pPars->n1HotAlgo, pPars->Seed, pPars->RuntimeLim, pPars->fUseIncr, pPars->fOnlyAnd, pPars->fMinNodes, pPars->fDumpBlif, pPars->fVerbose, pPars->fSilent );
    int status = KISSAT_UNDEC;
    int Res = 0;
    abctime clkTotal = Abc_Clock();
    Exa9_Man_t * p; 
    assert( pPars->nVars <= 14 );
    int nTruthWords = Abc_TtWordNum( pPars->nVars );
    word * pTruth = ABC_CALLOC( word, nTruthWords );
    assert( pTruth );
    if ( pPars->pSymStr ) {
        word * pFun = Abc_TtSymFunGenerate( pPars->pSymStr, pPars->nVars );
        pPars->pTtStr = ABC_CALLOC( char, pPars->nVars > 2 ? (1 << (pPars->nVars-2)) + 1 : 2 );
        Extra_PrintHexadecimalString( pPars->pTtStr, (unsigned *)pFun, pPars->nVars );
        if ( !pPars->fSilent ) printf( "Generated symmetric function: %s\n", pPars->pTtStr );
        ABC_FREE( pFun );
    }
    if ( pPars->pTtStr )
        Abc_TtReadHex( pTruth, pPars->pTtStr );
    else assert( 0 );
    if ( pPars->fUseIncr && !pPars->fSilent )
        printf( "Warning: Ignoring incremental option when using Kissat.\n" );
    pPars->fUseIncr = 0;
    p = Exa9_ManAlloc( pPars, pTruth );
    if ( pPars->fVerbose && !pPars->fSilent ) {
        int nStruct = p->nNodes * 4 * p->nObjs + 2 * p->nObjs;
        int nAux    = Exa9_ManCountAuxTotal( p );
        int nTotal  = nStruct + nAux + p->nValVars;
        const char * pAlgo = p->pPars->n1HotAlgo == 1 ? "seq" : (p->pPars->n1HotAlgo == 2 ? "bim" : (p->pPars->n1HotAlgo == 3 ? "cmd" : "naive"));
        printf( "Variables: Structure = %6d.  Uniqueness (%s) = %6d.  Internal = %6d.  Total = %6d.\n", 
            nStruct, pAlgo, nAux, p->nValVars, nTotal );
        //if ( pPars->Seed > 0 )
        //    printf( "Kissat seed set to %d.\n", pPars->Seed );
    }
    if ( Exa9_ManAddCnfStart( p ) )
    {
        if ( pPars->fVerbose && !pPars->fSilent )
        {
            int clausesPerMint = 0;
            clausesPerMint += p->nVars; // PI assignments
            for ( int i = 0; i < p->nNodes; i++ )
            {
                int Obj = p->nVars + i + 1;
                int choices = Obj - 1;
                clausesPerMint += 2 /*fanins*/ * 2 /*polarity*/ * choices * 2; // two clauses per equality
                clausesPerMint += 3; // functionality
            }
            clausesPerMint += 2 * p->nObjs; // output selector
            const char * pAlgo = p->pPars->n1HotAlgo == 1 ? "seq" : (p->pPars->n1HotAlgo == 2 ? "bim" : (p->pPars->n1HotAlgo == 3 ? "cmd" : "naive"));
            int internalTotal = clausesPerMint * p->nMints;
            printf( "Clauses:   Structure = %6d.  Uniqueness (%s) = %6d.  Internal = %6d.  Total = %6d.\n",
                p->nClausesStart, pAlgo, p->nClausesHot, internalTotal, p->nClausesStart + p->nClausesHot + internalTotal );
        }
        if ( !pPars->fSilent ) 
            printf( "Running exact synthesis for %d-input function with %d two-input and-nodes...\n", p->nVars, p->nNodes );
        int iMint;
        Vec_Int_t * vMints = Vec_IntAlloc( p->nMints );
        for ( iMint = 0; iMint < p->nMints; iMint++ )
            Vec_IntPush( vMints, iMint );
        if ( pPars->Seed > 0 )
        {
            Abc_Random( pPars->Seed );
            for ( iMint = 1; iMint < p->nMints; iMint++ )
            {
                int jMint = Abc_Random(0) % (iMint + 1);
                int Temp = Vec_IntEntry( vMints, iMint );
                Vec_IntWriteEntry( vMints, iMint, Vec_IntEntry(vMints, jMint) );
                Vec_IntWriteEntry( vMints, jMint, Temp );
            }
        }
        status = KISSAT_UNSAT;
        for ( iMint = 0; iMint < p->nMints; iMint++ )
        {
            int Mint = Vec_IntEntry( vMints, iMint );
            if ( !Exa9_ManAddCnf( p, Mint ) )
                break;
        }
        Vec_IntFree( vMints );
        if ( iMint == p->nMints )
        {
            if ( pPars->RuntimeLim )
            {
                p->timeStop = Abc_Clock() + pPars->RuntimeLim * CLOCKS_PER_SEC;
                kissat_set_terminate( p->pSat, p, Exa9_KissatTerminate );
            }
            else
            {
                p->timeStop = 0;
                kissat_set_terminate( p->pSat, NULL, NULL );
            }
            status = kissat_solve( p->pSat );
        }
    }
    else
        status = KISSAT_UNSAT;

    if ( status == KISSAT_SAT )
    {
        int DiffMint = Exa9_ManEval( p );
        if ( DiffMint != -1 )
            printf( "******** Warning: Verification detected a mismatch at minterm %d.\n", DiffMint );
        Exa9_ManPrintSolution( p );
        if ( pPars->fDumpBlif )
            Exa9_ManDumpBlif( p );
        Res = 1;
    }
    else if ( status == KISSAT_UNSAT )
    {
        if ( !p->pPars->fSilent )
            printf( "The problem has no solution.\n" );
        Res = 2;
    }
    else
    {
        Res = 0;
        if ( pPars->RuntimeLim )
            printf( "The solver timed out after %d sec.\n", pPars->RuntimeLim );
    }
    if ( !pPars->fSilent )
        Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
    if ( pPars->pSymStr ) 
        ABC_FREE( pPars->pTtStr );
    Exa9_ManFree( p );
    ABC_FREE( pTruth );
    return Res;
}

int Exa9_ManExactSynthesisIter( Bmc_EsPar_t * pPars )
{
    pPars->fMinNodes = 0;
    int nNodeMin = pPars->nVars - 1;
    int nNodeMax = pPars->nNodes, Result = 0;
    for ( int n = nNodeMin; n <= nNodeMax; n++ ) {
        //printf( "\nTrying M = %d:\n", n );
        printf( "\n" );
        pPars->nNodes = n;
        Result = Exa9_ManExactSynthesis(pPars);
        fflush( stdout );
        if ( Result == 1 )
            break;
    }
    return Result;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
