/**CFile****************************************************************

  FileName    [bmcMaj.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Exact synthesis with majority gates.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 1, 2017.]

  Revision    [$Id: bmcMaj.c,v 1.00 2017/10/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/cadical/cadicalSolver.h"
#include "sat/cadical/ccadical.h"
#include "aig/miniaig/miniaig.h"
#include "base/io/ioResub.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"

#define CADICAL_UNSAT -1
#define CADICAL_SAT    1
#define CADICAL_UNDEC  0

ABC_NAMESPACE_IMPL_START

static inline void Exa7_CadicalSetRuntimeLimit( cadical_solver * pSat, int nSeconds )
{
    if ( pSat == NULL || nSeconds <= 0 )
        return;
    ccadical_limit( (CCaDiCaL *)pSat->p, "seconds", nSeconds );
}


#ifdef WIN32
#include <process.h> 
#define unlink _unlink
#else
#include <unistd.h>
#endif
#include <limits.h>

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MAJ_NOBJS  64 // Const0 + Const1 + nVars + nNodes

typedef struct Exa7_Man_t_ Exa7_Man_t;
struct Exa7_Man_t_ 
{
    Bmc_EsPar_t *     pPars;     // parameters
    int               nVars;     // inputs
    int               nNodes;    // internal nodes
    int               nLutSize;  // lut size
    int               LutMask;   // lut mask
    int               nObjs;     // total objects (nVars inputs + nNodes internal nodes)
    int               nWords;    // the truth table size in 64-bit words
    int               iVar;      // the next available SAT variable
    word *            pTruth;    // truth table
    Vec_Wrd_t *       vInfo;     // nVars + nNodes + 1
    Vec_Bit_t *       vUsed2;    // bit masks
    Vec_Bit_t *       vUsed3;    // bit masks
    int               VarMarks[MAJ_NOBJS][6][MAJ_NOBJS]; // variable marks
    int               VarVals[MAJ_NOBJS]; // values of the first nVars variables
    Vec_Wec_t *       vOutLits;  // output vars
    Vec_Wec_t *       vInVars;   // input vars
    cadical_solver *  pSat;      // SAT solver
    int               nVarAlloc; // total vars reserved in the solver
    int               nUsed[2];
};

static inline word *  Exa7_ManTruth( Exa7_Man_t * p, int v ) { return Vec_WrdEntryP( p->vInfo, p->nWords * v ); }

static inline int     Exa7_ManIsUsed2( Exa7_Man_t * p, int m, int n, int i, int j )
{
    int Pos = ((m * p->pPars->nNodes + n - p->pPars->nVars) * p->nObjs + i) * p->nObjs + j;
    p->nUsed[0]++;
    assert( i < n && j < n && i < j );
    if ( Vec_BitEntry(p->vUsed2, Pos) )
        return 1;
    p->nUsed[1]++;
    Vec_BitWriteEntry( p->vUsed2, Pos, 1 );
    return 0;
}

static inline int     Exa7_ManIsUsed3( Exa7_Man_t * p, int m, int n, int i, int j, int k )
{
    int Pos = (((m * p->pPars->nNodes + n - p->pPars->nVars) * p->nObjs + i) * p->nObjs + j) * p->nObjs + k;
    p->nUsed[0]++;
    assert( i < n && j < n && k < n && i < j && j < k );
    if ( Vec_BitEntry(p->vUsed3, Pos) )
        return 1;
    p->nUsed[1]++;
    Vec_BitWriteEntry( p->vUsed3, Pos, 1 );
    return 0;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Exa7_ChooseInputVars_int( int nVars, int nLuts, int nLutSize )
{
    Vec_Wec_t * p = Vec_WecStart( nLuts ); 
    Vec_Int_t * vLevel; int i;
    Vec_WecForEachLevel( p, vLevel, i ) {
        do { 
            int iVar = (Abc_Random(0) ^ Abc_Random(0) ^ Abc_Random(0)) % nVars;
            Vec_IntPushUniqueOrder( vLevel, iVar );
        }
        while ( Vec_IntSize(vLevel) < nLutSize-(int)(i>0) );
    }
    return p;
}
Vec_Int_t * Exa7_CountInputVars( int nVars, Vec_Wec_t * p )
{
    Vec_Int_t * vLevel; int i, k, Obj;
    Vec_Int_t * vCounts = Vec_IntStart( nVars );
    Vec_WecForEachLevel( p, vLevel, i )
        Vec_IntForEachEntry( vLevel, Obj, k )
            Vec_IntAddToEntry( vCounts, Obj, 1 );
    return vCounts;
}
Vec_Wec_t * Exa7_ChooseInputVars( int nVars, int nLuts, int nLutSize )
{
    for ( int i = 0; i < 1000; i++ ) {
        Vec_Wec_t * p = Exa7_ChooseInputVars_int( nVars, nLuts, nLutSize );
        Vec_Int_t * q = Exa7_CountInputVars( nVars, p );
        int RetValue  = Vec_IntFind( q, 0 );
        Vec_IntFree( q );
        if ( RetValue == -1 )
            return p;
        Vec_WecFree( p );
    }
    assert( 0 );
    return NULL;
}
Vec_Wec_t * Exa7_ChooseInputVars2( int nVars, int nLuts, int nLutSize, char * pPermStr )
{
    Vec_Wec_t * p = Vec_WecStart( nLuts );
    Vec_Int_t * vLevel; int i, Pos = 0;
    assert( nLuts * nLutSize == (int)strlen(pPermStr) );
    Vec_WecForEachLevel( p, vLevel, i ) {
        for ( int k = 0; k < nLutSize; k++, Pos++ )
            if ( pPermStr[Pos] != '_' )
                Vec_IntPush( vLevel, pPermStr[Pos] == '*' ? -1 : (int)(pPermStr[Pos]-'a') );
    }
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wrd_t * Exa7_ManTruthTables( Exa7_Man_t * p )
{
    Vec_Wrd_t * vInfo = p->vInfo = Vec_WrdStart( p->nWords * (p->nObjs+1) ); int i;
    for ( i = 0; i < p->nVars; i++ )
        Abc_TtIthVar( Exa7_ManTruth(p, i), i, p->nVars );
    //Dau_DsdPrintFromTruth( Exa7_ManTruth(p, p->nObjs), p->nVars );
    return vInfo;
}
static int Exa7_ManVarReserve( Exa7_Man_t * p )
{
    int nMintMax = 1 << p->nVars;
    int nVarsPerMint = p->pPars->fUseIncr ? p->nNodes : (p->nLutSize + 1) * p->nNodes;
    int64_t nTotal = (int64_t)p->iVar + (int64_t)nVarsPerMint * nMintMax;
    if ( nTotal > INT_MAX )
        nTotal = INT_MAX;
    return (int)nTotal;
}
static int Exa7_ManMarkup( Exa7_Man_t * p )
{
    int i, k, j;
    assert( p->nObjs <= MAJ_NOBJS );
    // assign functionality variables
    p->iVar = 1 + p->LutMask * p->nNodes;
    // assign connectivity variables
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        if ( p->pPars->fLutCascade )
        {
            if ( i > p->nVars ) 
            {
                Vec_WecPush( p->vOutLits, i-1, Abc_Var2Lit(p->iVar, 0) );
                p->VarMarks[i][0][i-1] = p->iVar++;
            }
            for ( k = (int)(i > p->nVars); k < p->nLutSize; k++ )
            {
                for ( j = 0; j < p->nVars - k + (int)(i > p->nVars); j++ )
                {
                    Vec_WecPush( p->vOutLits, j, Abc_Var2Lit(p->iVar, 0) );
                    p->VarMarks[i][k][j] = p->iVar++;
                }
            }
            continue;
        }        
        for ( k = 0; k < p->nLutSize; k++ )
        {
            if ( p->pPars->fFewerVars && i == p->nObjs - 1 && k == 0 )
            {
                j = p->nObjs - 2;
                Vec_WecPush( p->vOutLits, j, Abc_Var2Lit(p->iVar, 0) );
                p->VarMarks[i][k][j] = p->iVar++;
                continue;
            }
            for ( j = p->pPars->fFewerVars ? p->nLutSize - 1 - k : 0; j < i - k; j++ )
            {
                Vec_WecPush( p->vOutLits, j, Abc_Var2Lit(p->iVar, 0) );
                p->VarMarks[i][k][j] = p->iVar++;
            }
        }
    }
    if ( !p->pPars->fSilent ) printf( "The number of parameter variables = %d.\n", p->iVar );
    if ( p->pPars->fLutCascade && (p->pPars->fLutInFixed || p->pPars->pPermStr) ) {
        if ( p->pPars->pPermStr )
            p->vInVars = Exa7_ChooseInputVars2( p->nVars, p->nNodes, p->nLutSize, p->pPars->pPermStr );
        else
            p->vInVars = Exa7_ChooseInputVars( p->nVars, p->nNodes, p->nLutSize );
        if ( !p->pPars->fSilent ) {
            Vec_Int_t * vLevel; int i, Var;
            printf( "Using fixed input assignment %s%s:\n", 
                p->pPars->pPermStr ? "provided by the user " : "generated randomly", p->pPars->pPermStr ? p->pPars->pPermStr : "" );
            Vec_WecForEachLevelReverse( p->vInVars, vLevel, i ) {
                printf( "%c : ", 'A'+p->nVars+i-p->nVars );
                Vec_IntForEachEntry( vLevel, Var, k )
                    printf( "%c ", Var < 0 ? '*' : 'a'+Var );
                printf( "\n" );
            }
        }
    }
    return p->iVar;
    // printout
    for ( i = p->nObjs - 1; i >= p->nVars; i-- )
    {
        printf( "       Node %2d\n", i );
        for ( j = 0; j < p->nObjs; j++ )
        {
            printf( "Fanin %2d : ", j );
            for ( k = 0; k < p->nLutSize; k++ )
                printf( "%3d ", p->VarMarks[i][k][j] );
            printf( "\n" );
        }
    }
    return p->iVar;
}
static Exa7_Man_t * Exa7_ManAlloc( Bmc_EsPar_t * pPars, word * pTruth )
{
    Exa7_Man_t * p = ABC_CALLOC( Exa7_Man_t, 1 );
    p->pPars      = pPars;
    p->nVars      = pPars->nVars;
    p->nNodes     = pPars->nNodes;
    p->nLutSize   = pPars->nLutSize;
    p->LutMask    = (1 << pPars->nLutSize) - 1;
    p->nObjs      = pPars->nVars + pPars->nNodes;
    p->nWords     = Abc_TtWordNum(pPars->nVars);
    p->pTruth     = pTruth;
    p->vOutLits   = Vec_WecStart( p->nObjs );
    p->iVar       = Exa7_ManMarkup( p );
    p->vInfo      = Exa7_ManTruthTables( p );
    if ( p->pPars->nLutSize == 2 )
    p->vUsed2     = Vec_BitStart( (1 << p->pPars->nVars) * p->pPars->nNodes * p->nObjs * p->nObjs );
    else if ( p->pPars->nLutSize == 3 )
    p->vUsed3     = Vec_BitStart( (1 << p->pPars->nVars) * p->pPars->nNodes * p->nObjs * p->nObjs * p->nObjs );
    p->pSat       = cadical_solver_new();
    p->nVarAlloc  = Exa7_ManVarReserve( p );
    assert( p->nVarAlloc >= p->iVar );
    //cadical_solver_setnvars( p->pSat, p->nVarAlloc );
    cadical_solver_setnvars( p->pSat, p->nVarAlloc+(p->nLutSize+1)*p->nNodes*(1 << p->nVars) );
    if ( pPars->RuntimeLim )
        Exa7_CadicalSetRuntimeLimit( p->pSat, pPars->RuntimeLim );
    return p;
}
static void Exa7_ManFree( Exa7_Man_t * p )
{
    cadical_solver_delete( p->pSat );
    Vec_WrdFree( p->vInfo );
    Vec_BitFreeP( &p->vUsed2 );
    Vec_BitFreeP( &p->vUsed3 );
    Vec_WecFree( p->vOutLits );
    Vec_WecFreeP( &p->vInVars );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Exa7_ManFindFanin( Exa7_Man_t * p, int i, int k )
{
    int j, Count = 0, iVar = -1;
    for ( j = 0; j < p->nObjs; j++ )
        if ( p->VarMarks[i][k][j] && cadical_solver_get_var_value(p->pSat, p->VarMarks[i][k][j]) )
        {
            iVar = j;
            Count++;
        }
    assert( Count == 1 );
    return iVar;
}
static inline int Exa7_ManEval( Exa7_Man_t * p )
{
    static int Flag = 0;
    int i, k, j, iMint; word * pFanins[6];
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        int iVarStart = 1 + p->LutMask*(i - p->nVars);
        for ( k = 0; k < p->nLutSize; k++ )
            pFanins[k] = Exa7_ManTruth( p, Exa7_ManFindFanin(p, i, k) );
        Abc_TtConst0( Exa7_ManTruth(p, i),        p->nWords );
        for ( k = 1; k <= p->LutMask; k++ )
        {
            if ( !cadical_solver_get_var_value(p->pSat, iVarStart+k-1) )
                continue;
//            Abc_TtAndCompl( Exa7_ManTruth(p, p->nObjs), pFanins[0], !(k&1), pFanins[1], !(k>>1), p->nWords );
            Abc_TtConst1( Exa7_ManTruth(p, p->nObjs), p->nWords );
            for ( j = 0; j < p->nLutSize; j++ )
                Abc_TtAndCompl( Exa7_ManTruth(p, p->nObjs), Exa7_ManTruth(p, p->nObjs), 0, pFanins[j], !((k >> j) & 1), p->nWords );
            Abc_TtOr( Exa7_ManTruth(p, i), Exa7_ManTruth(p, i), Exa7_ManTruth(p, p->nObjs), p->nWords );
        }
    }
    if ( Flag && p->nVars >= 6 )
        iMint = Abc_TtFindLastDiffBit( Exa7_ManTruth(p, p->nObjs-1), p->pTruth, p->nVars );
    else
        iMint = Abc_TtFindFirstDiffBit( Exa7_ManTruth(p, p->nObjs-1), p->pTruth, p->nVars );
    //Flag ^= 1;
    assert( iMint < (1 << p->nVars) );
    return iMint;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Exa7_ManPrintSolution( Exa7_Man_t * p, int fCompl )
{
    int i, k, iVar;
    printf( "Realization of given %d-input function using %d %d-input LUTs:\n", p->nVars, p->nNodes, p->nLutSize );
    for ( i = p->nObjs - 1; i >= p->nVars; i-- )
    {
        int Val, iVarStart = 1 + p->LutMask*(i - p->nVars);
        printf( "%c = %d\'b", 'A'+i-p->nVars, 1 << p->nLutSize );
        for ( k = p->LutMask - 1; k >= 0; k-- )
        {
            Val = cadical_solver_get_var_value(p->pSat, iVarStart+k); 
            if ( i == p->nObjs - 1 && fCompl )
                printf( "%d", !Val );
            else
                printf( "%d", Val );
        }
        if ( i == p->nObjs - 1 && fCompl )
            printf( "1(" );
        else
            printf( "0(" );

        for ( k = p->nLutSize - 1; k >= 0; k-- )
        {
            iVar = Exa7_ManFindFanin( p, i, k );
            if ( iVar >= 0 && iVar < p->nVars )
                printf( " %c", 'a'+iVar );
            else
                printf( " %c", 'A'+iVar-p->nVars );
        }
        printf( " )\n" );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wrd_t * Exa7_ManSaveTruthTables( Exa7_Man_t * p, int fCompl )
{
    int i, k, nWordsNode, nMintsNode;
    assert( p->nLutSize <= 8 );
    nMintsNode = 1 << p->nLutSize;
    nWordsNode = (p->nLutSize <= 6) ? 1 : (p->nLutSize == 7 ? 2 : 4);
    Vec_Wrd_t * vTruths = Vec_WrdStart( p->nObjs * nWordsNode );
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        word Truth[4] = {0, 0, 0, 0};
        int iVarStart = 1 + p->LutMask*(i - p->nVars);
        for ( k = 0; k < p->LutMask; k++ )
        {
            if ( cadical_solver_get_var_value(p->pSat, iVarStart + k) )
            {
                int bit = k + 1; // minterm index (minterm 0 is fixed to 0)
                int w = bit >> 6;
                int b = bit & 63;
                Truth[w] |= ((word)1 << b);
            }
        }
        // complement the output fully if needed (including minterm 0)
        if ( i == p->nObjs - 1 && fCompl )
        {
            for ( int w = 0; w < nWordsNode; w++ )
            {
                word Mask;
                int rem = nMintsNode - w * 64;
                if ( rem <= 0 )
                    Mask = 0;
                else if ( rem >= 64 )
                    Mask = ~(word)0;
                else
                    Mask = (((word)1) << rem) - 1;
                Truth[w] = (~Truth[w]) & Mask;
            }
        }
        if ( p->nLutSize < 6 )
            Truth[0] = Abc_Tt6Stretch( Truth[0], p->nLutSize );
        for ( int w = 0; w < nWordsNode; w++ )
            Vec_WrdWriteEntry( vTruths, i * nWordsNode + w, Truth[w] );
    }
    return vTruths;
}
static void Exa7_ManPrintPerm( Exa7_Man_t * p )
{
    int i, k, iVar;
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        if ( i > p->nVars )
            printf( "_" );
        for ( k = p->nLutSize - 1; k >= 0; k-- )
        {
            iVar = Exa7_ManFindFanin( p, i, k );
            if ( iVar >= 0 && iVar < p->nVars )
                printf( "%c", 'a'+iVar );
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Exa7_ManDumpBlif( Exa7_Man_t * p, int fCompl )
{
    int i, k, b, iVar;
    char pFileName[1000];
    char * pStr = Abc_UtilStrsav(p->pPars->pSymStr ? p->pPars->pSymStr : p->pPars->pTtStr);
    if ( strlen(pStr) > 16 ) {
        pStr[16] = '_';
        pStr[17] = '\0';
    }    
    sprintf( pFileName, "%s.blif", pStr );
    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL ) return;
    fprintf( pFile, "# Realization of given %d-input function using %d %d-input LUTs synthesized by ABC on %s\n", p->nVars, p->nNodes, p->nLutSize, Extra_TimeStamp() );
    fprintf( pFile, ".model %s\n", pStr );
    fprintf( pFile, ".inputs" );
    for ( k = 0; k < p->nVars; k++ )
        fprintf( pFile, " %c", 'a'+k );
    fprintf( pFile, "\n.outputs F\n" );    
    for ( i = p->nObjs - 1; i >= p->nVars; i-- )
    {
        fprintf( pFile, ".names" );
        for ( k = 0; k < p->nLutSize; k++ )
        {
            iVar = Exa7_ManFindFanin( p, i, k );
            if ( iVar >= 0 && iVar < p->nVars )
                fprintf( pFile, " %c", 'a'+iVar );
            else
                fprintf( pFile, " %02d", iVar );
        }
        if ( i == p->nObjs - 1 )
            fprintf( pFile, " F\n" );
        else 
            fprintf( pFile, " %02d\n", i );
        int iVarStart = 1 + p->LutMask*(i - p->nVars);
        for ( k = 0; k < p->LutMask; k++ )
        {
            int Val = cadical_solver_get_var_value(p->pSat, iVarStart+k); 
            if ( Val == 0 )
                continue;
            for ( b = 0; b < p->nLutSize; b++ )
                fprintf( pFile, "%d", ((k+1) >> b) & 1 );
            fprintf( pFile, " %d\n", i != p->nObjs - 1 || !fCompl );
        }
    }
    fprintf( pFile, ".end\n\n" );
    fclose( pFile );
    if ( !p->pPars->fSilent ) printf( "Finished dumping the resulting LUT network into file \"%s\".\n", pFileName );
    ABC_FREE( pStr );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Exa7_ManAddCnfStart( Exa7_Man_t * p, int fOnlyAnd )
{
    int pLits[MAJ_NOBJS], pLits2[2], i, j, k, n, m;
    // input constraints
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        int iVarStart = 1 + p->LutMask*(i - p->nVars);
        for ( k = 0; k < p->nLutSize; k++ )
        {
            int nLits = 0;
            for ( j = 0; j < p->nObjs; j++ )
                if ( p->VarMarks[i][k][j] )
                    pLits[nLits++] = Abc_Var2Lit( p->VarMarks[i][k][j], 0 );
            assert( nLits > 0 );
            // input uniqueness
            if ( !cadical_solver_addclause( p->pSat, pLits, pLits + nLits ) )
                return 0;
            for ( n = 0;   n < nLits; n++ )
            for ( m = n+1; m < nLits; m++ )
            {
                pLits2[0] = Abc_LitNot(pLits[n]);
                pLits2[1] = Abc_LitNot(pLits[m]);
                if ( !cadical_solver_addclause( p->pSat, pLits2, pLits2 + 2 ) )
                    return 0;
            }
            if ( k == p->nLutSize - 1 )
                break;
            // symmetry breaking
            for ( j = 0; j < p->nObjs; j++ ) if ( p->VarMarks[i][k][j] )
            for ( n = j; n < p->nObjs; n++ ) if ( p->VarMarks[i][k+1][n] )
            {
                pLits2[0] = Abc_Var2Lit( p->VarMarks[i][k][j], 1 );
                pLits2[1] = Abc_Var2Lit( p->VarMarks[i][k+1][n], 1 );
                if ( !cadical_solver_addclause( p->pSat, pLits2, pLits2 + 2 ) )
                    return 0;
            }
        }
//#ifdef USE_NODE_ORDER
        // node ordering
        if ( p->pPars->fOrderNodes )
        {
            for ( j = p->nVars; j < i; j++ )
            for ( n = 0;   n < p->nObjs; n++ ) if ( p->VarMarks[i][0][n] )
            for ( m = n+1; m < p->nObjs; m++ ) if ( p->VarMarks[j][0][m] )
            {
                pLits2[0] = Abc_Var2Lit( p->VarMarks[i][0][n], 1 );
                pLits2[1] = Abc_Var2Lit( p->VarMarks[j][0][m], 1 );
                if ( !cadical_solver_addclause( p->pSat, pLits2, pLits2 + 2 ) )
                    return 0;
            }
        }
//#endif
        if ( p->nLutSize != 2 )
            continue;
        // two-input functions
        for ( k = 0; k < 3; k++ )
        {
            pLits[0] = Abc_Var2Lit( iVarStart,   k==1 );
            pLits[1] = Abc_Var2Lit( iVarStart+1, k==2 );
            pLits[2] = Abc_Var2Lit( iVarStart+2, k!=0 );
            if ( !cadical_solver_addclause( p->pSat, pLits, pLits + 3 ) )
                return 0;
        }
        if ( fOnlyAnd )
        {
            pLits[0] = Abc_Var2Lit( iVarStart,   1 );
            pLits[1] = Abc_Var2Lit( iVarStart+1, 1 );
            pLits[2] = Abc_Var2Lit( iVarStart+2, 0 );
            if ( !cadical_solver_addclause( p->pSat, pLits, pLits + 3 ) )
                return 0;
        }
    }
    // outputs should be used
    for ( i = 0; i < p->nObjs - 1; i++ )
    {
        Vec_Int_t * vArray = Vec_WecEntry(p->vOutLits, i);
        int * pArray = Vec_IntArray( vArray );
        int nArrayLits = Vec_IntSize( vArray );
        assert( nArrayLits > 0 );
        if ( !cadical_solver_addclause( p->pSat, pArray, pArray + nArrayLits ) )
            return 0;
    }
    if ( p->vInVars ) {
        Vec_Int_t * vLevel; int Var;
        //Vec_WecPrint( p->vInVars, 0 );
        Vec_WecForEachLevel( p->vInVars, vLevel, i )
        {
            assert( Vec_IntSize(vLevel) > 0 );
            Vec_IntForEachEntry( vLevel, Var, k ) {
                if ( Var < 0 ) continue;
                if ( p->VarMarks[p->nVars+i][p->nLutSize-1-k][Var] == 0 ) {
                    printf( "Skipping variable %d in place %d because it cannot be constrained.\n", Var, k );
                    continue;
                }
                pLits[0] = Abc_Var2Lit( p->VarMarks[p->nVars+i][p->nLutSize-1-k][Var], 0 ); assert(pLits[0]);
                if ( !cadical_solver_addclause( p->pSat, pLits, pLits + 1 ) )
                    return 0;
            }
        }
    }
    return 1;
}
static int Exa7_ManAddCnf( Exa7_Man_t * p, int iMint )
{
    // save minterm values
    int i, k, n, j, Value = Abc_TtGetBit(p->pTruth, iMint);
    for ( i = 0; i < p->nVars; i++ )
        p->VarVals[i] = (iMint >> i) & 1;
//    sat_solver_setnvars( p->pSat, p->iVar + (p->nLutSize+1)*p->nNodes );
    //cadical_solver_setnvars( p->pSat, p->iVar + (p->nLutSize+1)*p->nNodes );
    //printf( "Adding clauses for minterm %d with value %d.\n", iMint, Value );
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        // fanin connectivity
        int iVarStart = 1 + p->LutMask*(i - p->nVars);
        int iBaseSatVarI = p->iVar + (p->nLutSize+1)*(i - p->nVars);
        for ( k = 0; k < p->nLutSize; k++ )
        {
            for ( j = 0; j < p->nObjs; j++ ) if ( p->VarMarks[i][k][j] )
            {
                int iBaseSatVarJ = p->iVar + (p->nLutSize+1)*(j - p->nVars);
                for ( n = 0; n < 2; n++ )
                {
                    int pLits[3], nLits = 0;
                    pLits[nLits++] = Abc_Var2Lit( p->VarMarks[i][k][j], 1 );
                    pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + k, n );
                    if ( j >= p->nVars )
                        pLits[nLits++] = Abc_Var2Lit( iBaseSatVarJ + p->nLutSize, !n );
                    else if ( p->VarVals[j] == n )
                        continue;
                    if ( !cadical_solver_addclause( p->pSat, pLits, pLits + nLits ) )
                        return 0;
                }
            }
        }
        // node functionality
        for ( n = 0; n < 2; n++ )
        {
            if ( i == p->nObjs - 1 && n == Value )
                continue;
            for ( k = 0; k <= p->LutMask; k++ )
            {
                int pLits[16], nLits = 0;
                if ( k == 0 && n == 1 )
                    continue;
                //pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + 0, (k&1)  );
                //pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + 1, (k>>1) );
                //if ( i != p->nObjs - 1 ) pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + 2, !n );
                for ( j = 0; j < p->nLutSize; j++ )
                    pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + j, (k >> j) & 1 );
                if ( i != p->nObjs - 1 ) pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + j, !n );
                if ( k > 0 )             pLits[nLits++] = Abc_Var2Lit( iVarStart +  k-1,  n );
                assert( nLits <= p->nLutSize+2 );
                if ( !cadical_solver_addclause( p->pSat, pLits, pLits + nLits ) )
                    return 0;
            }
        }
    }
    p->iVar += (p->nLutSize+1)*p->nNodes;
    assert( p->iVar <= p->nVarAlloc );
    return 1;
}

static int Exa7_ManAddCnf2( Exa7_Man_t * p, int iMint )
{
    int iBaseSatVar = p->iVar + p->nNodes*iMint;
    assert( iBaseSatVar + p->nNodes <= p->nVarAlloc );
    // save minterm values
    int i, k, n, j, Value = Abc_TtGetBit(p->pTruth, iMint);
    for ( i = 0; i < p->nVars; i++ )
        p->VarVals[i] = (iMint >> i) & 1;
    //printf( "Adding clauses for minterm %d with value %d.\n", iMint, Value );
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
//        int iBaseSatVarI = p->iVar + (p->nLutSize+1)*(i - p->nVars);
        int iVarStart = 1 + p->LutMask*(i - p->nVars);
        // collect fanin variables
        int pFanins[16];
        for ( j = 0; j < p->nLutSize; j++ )
            pFanins[j] = Exa7_ManFindFanin(p, i, j);
        // check cache
        if ( p->pPars->nLutSize == 2 && Exa7_ManIsUsed2(p, iMint, i, pFanins[1], pFanins[0]) )
            continue;
        if ( p->pPars->nLutSize == 3 && Exa7_ManIsUsed3(p, iMint, i, pFanins[2], pFanins[1], pFanins[0]) )
            continue;
        // node functionality
        for ( n = 0; n < 2; n++ )
        {
            if ( i == p->nObjs - 1 && n == Value )
                continue;
            for ( k = 0; k <= p->LutMask; k++ )
            {
                int pLits[16], nLits = 0;
                if ( k == 0 && n == 1 )
                    continue;
                for ( j = 0; j < p->nLutSize; j++ )
                {
//                    pLits[nLits++] = Abc_Var2Lit( iBaseSatVar + j, (k >> j) & 1 );
                    pLits[nLits++] = Abc_Var2Lit( p->VarMarks[i][j][pFanins[j]], 1 );
                    if ( pFanins[j] >= p->nVars )
                        pLits[nLits++] = Abc_Var2Lit( iBaseSatVar + pFanins[j] - p->nVars, (k >> j) & 1 );
                    else if ( p->VarVals[pFanins[j]] != ((k >> j) & 1) )
                        break;
                }
                if ( j < p->nLutSize )
                    continue;
//                if ( i != p->nObjs - 1 ) pLits[nLits++] = Abc_Var2Lit( iBaseSatVar + j, !n );
                if ( i != p->nObjs - 1 ) pLits[nLits++] = Abc_Var2Lit( iBaseSatVar + i - p->nVars, !n );
                if ( k > 0 )             pLits[nLits++] = Abc_Var2Lit( iVarStart + k-1,             n );
                assert( nLits <= 2*p->nLutSize+2 );
                if ( !cadical_solver_addclause( p->pSat, pLits, pLits + nLits ) )
                    return 0;
            }
        }
    }
    return 1;
}
void Exa7_ManPrint( Exa7_Man_t * p, int i, int iMint, abctime clk )
{
    printf( "Iter%6d : ", i );
    Extra_PrintBinary( stdout, (unsigned *)&iMint, p->nVars );
    printf( "  Var =%5d  ", cadical_solver_nvars(p->pSat) );
    printf( "Cla =%6d  ", cadical_solver_nclauses(p->pSat) );
    printf( "Conf =%9d  ", cadical_solver_nconflicts(p->pSat) );
    Abc_PrintTime( 1, "Time", clk );
}
int Exa7_ManExactSynthesis( Bmc_EsPar_t * pPars )
{
    extern int Exa7_ManExactSynthesisIter( Bmc_EsPar_t * pPars );
    if ( pPars->fMinNodes )
        return Exa7_ManExactSynthesisIter( pPars );
    int i, status, Res = 0, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa7_Man_t * p; int fCompl = 0;
    word pTruth[64]; 
    if ( pPars->pSymStr ) {
        word * pFun = Abc_TtSymFunGenerate( pPars->pSymStr, pPars->nVars );
        pPars->pTtStr = ABC_CALLOC( char, pPars->nVars > 2 ? (1 << (pPars->nVars-2)) + 1 : 2 );
        Extra_PrintHexadecimalString( pPars->pTtStr, (unsigned *)pFun, pPars->nVars );
        if ( !pPars->fSilent && pPars->nVars <= 7 ) printf( "Generated symmetric function: %s\n", pPars->pTtStr );
        ABC_FREE( pFun );
    }
    if ( pPars->pTtStr )
        Abc_TtReadHex( pTruth, pPars->pTtStr );
    else assert( 0 );
    assert( pPars->nVars <= 12 );
    assert( pPars->nLutSize <= 6 );
    p = Exa7_ManAlloc( pPars, pTruth );
    if ( pTruth[0] & 1 ) { fCompl = 1; Abc_TtNot( pTruth, p->nWords ); }
    status = Exa7_ManAddCnfStart( p, pPars->fOnlyAnd );
    assert( status );
    if ( !pPars->fSilent ) printf( "Running exact synthesis for %d-input function with %d %d-input LUTs...\n", p->nVars, p->nNodes, p->nLutSize );
    if ( pPars->fUseIncr ) 
    {
        status = cadical_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
        assert( status == CADICAL_SAT );
    }
    for ( i = 0; iMint != -1; i++ )
    {
        if ( pPars->fUseIncr ? !Exa7_ManAddCnf2( p, iMint ) : !Exa7_ManAddCnf( p, iMint ) )
            break;
        status = cadical_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
        if ( pPars->fVerbose && (!pPars->fUseIncr || i % 100 == 0) )
            Exa7_ManPrint( p, i, iMint, Abc_Clock() - clkTotal );
        if ( status == CADICAL_UNSAT || status == CADICAL_UNDEC )
            break;
        iMint = Exa7_ManEval( p );
    }
    if ( pPars->fVerbose && status != CADICAL_UNDEC )
        Exa7_ManPrint( p, i, iMint, Abc_Clock() - clkTotal );
    if ( iMint == -1 )
    {
        Exa7_ManPrintSolution( p, fCompl );
        printf( "The variable permutation is \"" );
        Exa7_ManPrintPerm( p );
        printf( "\".\n" );
        if ( pPars->fDumpBlif )
            Exa7_ManDumpBlif( p, fCompl );
        if ( p->pPars->fGenTruths ) {
            if ( p->pPars->vTruths )
                Vec_WrdFreeP( &p->pPars->vTruths );
            p->pPars->vTruths = Exa7_ManSaveTruthTables( p, fCompl );
        }
        Res = 1;
    }
    else if ( status == CADICAL_UNDEC )
        printf( "The solver timed out after %d sec.\n", pPars->RuntimeLim );
    else if ( !p->pPars->fSilent ) 
        printf( "The problem has no solution.\n" ), Res = 2;
    if ( !pPars->fSilent && (p->nUsed[0] || p->nUsed[1])  ) printf( "Added = %d.  Tried = %d.  ", p->nUsed[1], p->nUsed[0] );
    if ( !pPars->fSilent ) Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
    if ( pPars->pSymStr ) 
        ABC_FREE( pPars->pTtStr );
    Exa7_ManFree( p );
    return Res;
}

int Exa7_ManExactSynthesisIter( Bmc_EsPar_t * pPars )
{
    pPars->fMinNodes = 0;
    int nNodeMin = (pPars->nVars-2)/(pPars->nLutSize-1) + 1;
    int nNodeMax = pPars->nNodes, Result = 0;
    int fGenPerm = pPars->pPermStr == NULL;
    for ( int n = nNodeMin; n <= nNodeMax; n++ ) {
        if ( !pPars->fSilent ) printf( "\nTrying M = %d:\n", n );
        pPars->nNodes = n;
        if ( !pPars->fUsePerm && fGenPerm ) {
            Vec_Str_t * vStr = Vec_StrAlloc( 100 );
            for ( int v = 0; v < pPars->nLutSize; v++ )
                Vec_StrPush( vStr, 'a'+v );
            int nDupVars = Abc_MaxInt(0, (pPars->nLutSize-1) - (pPars->nVars-pPars->nLutSize));
            Vec_StrPush( vStr, '_' );
            for ( int v = 0; v < nDupVars; v++ )
                Vec_StrPush( vStr, 'a'+v );
            for ( int v = 0; v < pPars->nLutSize-1-nDupVars; v++ )
                Vec_StrPush( vStr, '*' );
            for ( int m = 2; m < pPars->nNodes; m++ ) {
                Vec_StrPush( vStr, '_' );
                for ( int v = 0; v < pPars->nLutSize-1; v++ )
                    Vec_StrPush( vStr, '*' );
            }
            Vec_StrPush( vStr, '\0' );
            ABC_FREE( pPars->pPermStr );
            pPars->pPermStr = Vec_StrReleaseArray(vStr);
            Vec_StrFree( vStr );
        }
        else if ( pPars->fUsePerm && fGenPerm ) {
            Vec_Str_t * vStr = Vec_StrAlloc( 100 );
            for ( int v = 0; v < pPars->nLutSize; v++ )
                Vec_StrPush( vStr, 'a'+v );
            for ( int m = 1; m < pPars->nNodes; m++ ) {
                Vec_StrPush( vStr, '_' );
                if ( m & 1 ) 
                    for ( int v = 0; v < pPars->nLutSize-1; v++ )
                        Vec_StrPush( vStr, 'a'+(pPars->nVars-(pPars->nLutSize-1-v)) );
                else
                    for ( int v = 0; v < pPars->nLutSize-1; v++ )
                        Vec_StrPush( vStr, 'a'+v );
            }
            Vec_StrPush( vStr, '\0' );
            ABC_FREE( pPars->pPermStr );
            pPars->pPermStr = Vec_StrReleaseArray(vStr);
            Vec_StrFree( vStr );
        }
        Result = Exa7_ManExactSynthesis(pPars);
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
