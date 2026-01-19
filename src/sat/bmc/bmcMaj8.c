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
#include "sat/kissat/kissat.h"
#include "aig/miniaig/miniaig.h"
#include "base/io/ioResub.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"

#ifdef _WIN32
#include <windows.h>
typedef __int64 int64_t;
#endif

#define KISSAT_UNSAT 20
#define KISSAT_SAT   10
#define KISSAT_UNDEC  0

ABC_NAMESPACE_IMPL_START


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
#define MAJ_MAX_LUT 8

typedef struct Exa8_Man_t_ Exa8_Man_t;
struct Exa8_Man_t_ 
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
    int               VarMarks[MAJ_NOBJS][MAJ_MAX_LUT][MAJ_NOBJS]; // variable marks
    int               VarVals[MAJ_NOBJS]; // values of the first nVars variables
    Vec_Wec_t *       vOutLits;  // output vars
    Vec_Wec_t *       vInVars;   // input vars
    kissat *          pSat;      // SAT solver
    int               nVarAlloc; // total vars reserved in the solver
    abctime           timeStop;  // runtime limit (0 = unlimited)
    int               nUsed[2];
};

static inline int Exa8_LitToKissat( int Lit )
{
    return Abc_LitIsCompl( Lit ) ? -(Abc_Lit2Var( Lit ) + 1) : (Abc_Lit2Var( Lit ) + 1);
}
static inline int Exa8_KissatAddClause( Exa8_Man_t * p, int * pLits, int nLits )
{
    int i;
    for ( i = 0; i < nLits; i++ )
        kissat_add( p->pSat, Exa8_LitToKissat( pLits[i] ) );
    kissat_add( p->pSat, 0 );
    return !kissat_is_inconsistent( p->pSat );
}
static inline int Exa8_KissatVarValue( Exa8_Man_t * p, int v )
{
    return kissat_value( p->pSat, v + 1 ) > 0;
}
static int Exa8_KissatTerminate( void * pData )
{
    Exa8_Man_t * p = (Exa8_Man_t *)pData;
    return p && p->timeStop && Abc_Clock() > p->timeStop;
}

static inline word *  Exa8_ManTruth( Exa8_Man_t * p, int v ) { return Vec_WrdEntryP( p->vInfo, p->nWords * v ); }

static inline int     Exa8_ManIsUsed2( Exa8_Man_t * p, int m, int n, int i, int j )
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

static inline int     Exa8_ManIsUsed3( Exa8_Man_t * p, int m, int n, int i, int j, int k )
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
Vec_Wec_t * Exa8_ChooseInputVars_int( int nVars, int nLuts, int nLutSize )
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
Vec_Int_t * Exa8_CountInputVars( int nVars, Vec_Wec_t * p )
{
    Vec_Int_t * vLevel; int i, k, Obj;
    Vec_Int_t * vCounts = Vec_IntStart( nVars );
    Vec_WecForEachLevel( p, vLevel, i )
        Vec_IntForEachEntry( vLevel, Obj, k )
            Vec_IntAddToEntry( vCounts, Obj, 1 );
    return vCounts;
}
Vec_Wec_t * Exa8_ChooseInputVars( int nVars, int nLuts, int nLutSize )
{
    for ( int i = 0; i < 1000; i++ ) {
        Vec_Wec_t * p = Exa8_ChooseInputVars_int( nVars, nLuts, nLutSize );
        Vec_Int_t * q = Exa8_CountInputVars( nVars, p );
        int RetValue  = Vec_IntFind( q, 0 );
        Vec_IntFree( q );
        if ( RetValue == -1 )
            return p;
        Vec_WecFree( p );
    }
    assert( 0 );
    return NULL;
}
Vec_Wec_t * Exa8_ChooseInputVars2( int nVars, int nLuts, int nLutSize, char * pPermStr )
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
static Vec_Wrd_t * Exa8_ManTruthTables( Exa8_Man_t * p )
{
    Vec_Wrd_t * vInfo = p->vInfo = Vec_WrdStart( p->nWords * (p->nObjs+1) ); int i;
    for ( i = 0; i < p->nVars; i++ )
        Abc_TtIthVar( Exa8_ManTruth(p, i), i, p->nVars );
    //Dau_DsdPrintFromTruth( Exa8_ManTruth(p, p->nObjs), p->nVars );
    return vInfo;
}
static int Exa8_ManVarReserve( Exa8_Man_t * p )
{
    int nMintMax = 1 << p->nVars;
    int nVarsPerMint = p->pPars->fUseIncr ? p->nNodes : (p->nLutSize + 1) * p->nNodes;
    int64_t nTotal = (int64_t)p->iVar + (int64_t)nVarsPerMint * nMintMax;
    if ( nTotal > INT_MAX )
        nTotal = INT_MAX;
    return (int)nTotal;
}
static int Exa8_ManMarkup( Exa8_Man_t * p )
{
    int i, k, j;
    assert( p->nObjs <= MAJ_NOBJS );
    assert( p->nLutSize <= MAJ_MAX_LUT );
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
            p->vInVars = Exa8_ChooseInputVars2( p->nVars, p->nNodes, p->nLutSize, p->pPars->pPermStr );
        else
            p->vInVars = Exa8_ChooseInputVars( p->nVars, p->nNodes, p->nLutSize );
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
static Exa8_Man_t * Exa8_ManAlloc( Bmc_EsPar_t * pPars, word * pTruth )
{
    Exa8_Man_t * p = ABC_CALLOC( Exa8_Man_t, 1 );
    p->pPars      = pPars;
    p->nVars      = pPars->nVars;
    p->nNodes     = pPars->nNodes;
    p->nLutSize   = pPars->nLutSize;
    p->LutMask    = (1 << pPars->nLutSize) - 1;
    p->nObjs      = pPars->nVars + pPars->nNodes;
    p->nWords     = Abc_TtWordNum(pPars->nVars);
    p->pTruth     = pTruth;
    p->vOutLits   = Vec_WecStart( p->nObjs );
    p->iVar       = Exa8_ManMarkup( p );
    p->vInfo      = Exa8_ManTruthTables( p );
    if ( p->pPars->nLutSize == 2 )
    p->vUsed2     = Vec_BitStart( (1 << p->pPars->nVars) * p->pPars->nNodes * p->nObjs * p->nObjs );
    else if ( p->pPars->nLutSize == 3 )
    p->vUsed3     = Vec_BitStart( (1 << p->pPars->nVars) * p->pPars->nNodes * p->nObjs * p->nObjs * p->nObjs );
    p->pSat       = kissat_init();
    p->nVarAlloc  = Exa8_ManVarReserve( p );
    assert( p->nVarAlloc >= p->iVar );
    kissat_reserve( p->pSat, p->nVarAlloc );
    p->timeStop   = 0;
    return p;
}
static void Exa8_ManFree( Exa8_Man_t * p )
{
    kissat_release( p->pSat );
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
static inline int Exa8_ManFindFanin( Exa8_Man_t * p, int i, int k )
{
    int j, Count = 0, iVar = -1;
    for ( j = 0; j < p->nObjs; j++ )
        if ( p->VarMarks[i][k][j] && Exa8_KissatVarValue(p, p->VarMarks[i][k][j]) )
        {
            iVar = j;
            Count++;
        }
    assert( Count == 1 );
    return iVar;
}
static inline int Exa8_ManEval( Exa8_Man_t * p )
{
    static int Flag = 0;
    int i, k, j, iMint; word * pFanins[MAJ_MAX_LUT];
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        int iVarStart = 1 + p->LutMask*(i - p->nVars);
        for ( k = 0; k < p->nLutSize; k++ )
            pFanins[k] = Exa8_ManTruth( p, Exa8_ManFindFanin(p, i, k) );
        Abc_TtConst0( Exa8_ManTruth(p, i),        p->nWords );
        for ( k = 1; k <= p->LutMask; k++ )
        {
            if ( !Exa8_KissatVarValue(p, iVarStart+k-1) )
                continue;
//            Abc_TtAndCompl( Exa8_ManTruth(p, p->nObjs), pFanins[0], !(k&1), pFanins[1], !(k>>1), p->nWords );
            Abc_TtConst1( Exa8_ManTruth(p, p->nObjs), p->nWords );
            for ( j = 0; j < p->nLutSize; j++ )
                Abc_TtAndCompl( Exa8_ManTruth(p, p->nObjs), Exa8_ManTruth(p, p->nObjs), 0, pFanins[j], !((k >> j) & 1), p->nWords );
            Abc_TtOr( Exa8_ManTruth(p, i), Exa8_ManTruth(p, i), Exa8_ManTruth(p, p->nObjs), p->nWords );
        }
    }
    if ( Flag && p->nVars >= 6 )
        iMint = Abc_TtFindLastDiffBit( Exa8_ManTruth(p, p->nObjs-1), p->pTruth, p->nVars );
    else
        iMint = Abc_TtFindFirstDiffBit( Exa8_ManTruth(p, p->nObjs-1), p->pTruth, p->nVars );
    if ( iMint == -1 )
        return -1;
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
static Vec_Wrd_t * Exa8_ManSaveTruthTables( Exa8_Man_t * p, int fCompl )
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
            if ( Exa8_KissatVarValue( p, iVarStart + k ) )
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
static void Exa8_ManPrintSolution( Exa8_Man_t * p, int fCompl )
{
    int i, k, iVar;
    printf( "Realization of given %d-input function using %d %d-input LUTs:\n", p->nVars, p->nNodes, p->nLutSize );
    for ( i = p->nObjs - 1; i >= p->nVars; i-- )
    {
        int Val, iVarStart = 1 + p->LutMask*(i - p->nVars);
        printf( "%c = %d\'b", 'A'+i-p->nVars, 1 << p->nLutSize );
        for ( k = p->LutMask - 1; k >= 0; k-- )
        {
            Val = Exa8_KissatVarValue(p, iVarStart+k); 
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
            iVar = Exa8_ManFindFanin( p, i, k );
            if ( iVar >= 0 && iVar < p->nVars )
                printf( " %c", 'a'+iVar );
            else
                printf( " %c", 'A'+iVar-p->nVars );
        }
        printf( " )\n" );
    }
}
static void Exa8_ManPrintPerm( Exa8_Man_t * p )
{
    int i, k, iVar;
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        if ( i > p->nVars )
            printf( "_" );
        for ( k = p->nLutSize - 1; k >= 0; k-- )
        {
            iVar = Exa8_ManFindFanin( p, i, k );
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
static void Exa8_ManDumpBlif( Exa8_Man_t * p, int fCompl )
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
            iVar = Exa8_ManFindFanin( p, i, k );
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
            int Val = Exa8_KissatVarValue(p, iVarStart+k); 
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
static int Exa8_ManAddCnfStart( Exa8_Man_t * p, int fOnlyAnd )
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
            if ( !Exa8_KissatAddClause( p, pLits, nLits ) )
                return 0;
            for ( n = 0;   n < nLits; n++ )
            for ( m = n+1; m < nLits; m++ )
            {
                pLits2[0] = Abc_LitNot(pLits[n]);
                pLits2[1] = Abc_LitNot(pLits[m]);
                if ( !Exa8_KissatAddClause( p, pLits2, 2 ) )
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
                if ( !Exa8_KissatAddClause( p, pLits2, 2 ) )
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
                if ( !Exa8_KissatAddClause( p, pLits2, 2 ) )
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
            if ( !Exa8_KissatAddClause( p, pLits, 3 ) )
                return 0;
        }
        if ( fOnlyAnd )
        {
            pLits[0] = Abc_Var2Lit( iVarStart,   1 );
            pLits[1] = Abc_Var2Lit( iVarStart+1, 1 );
            pLits[2] = Abc_Var2Lit( iVarStart+2, 0 );
            if ( !Exa8_KissatAddClause( p, pLits, 3 ) )
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
        if ( !Exa8_KissatAddClause( p, pArray, nArrayLits ) )
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
                if ( !Exa8_KissatAddClause( p, pLits, 1 ) )
                    return 0;
            }
        }
    }
    return 1;
}
static int Exa8_ManAddCnf( Exa8_Man_t * p, int iMint )
{
    // save minterm values
    int i, k, n, j, Value = Abc_TtGetBit(p->pTruth, iMint);
    for ( i = 0; i < p->nVars; i++ )
        p->VarVals[i] = (iMint >> i) & 1;
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
                    if ( !Exa8_KissatAddClause( p, pLits, nLits ) )
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
                if ( !Exa8_KissatAddClause( p, pLits, nLits ) )
                    return 0;
            }
        }
    }
    p->iVar += (p->nLutSize+1)*p->nNodes;
    assert( p->iVar <= p->nVarAlloc );
    return 1;
}

int Exa8_ManExactSynthesis( Bmc_EsPar_t * pPars )
{
    extern int Exa8_ManExactSynthesisIter( Bmc_EsPar_t * pPars );
    if ( pPars->fMinNodes )
        return Exa8_ManExactSynthesisIter( pPars );
    int status = KISSAT_UNDEC;
    int Res = 0;
    abctime clkTotal = Abc_Clock();
    Exa8_Man_t * p; 
    int fCompl = 0;
    assert( pPars->nVars <= 14 );
    assert( pPars->nLutSize <= 8 );
    int nTruthWords = Abc_TtWordNum( pPars->nVars );
    word * pTruth = ABC_CALLOC( word, nTruthWords );
    assert( pTruth );
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
    if ( pPars->fUseIncr && !pPars->fSilent )
        printf( "Warning: Ignoring incremental option when using Kissat.\n" );
    pPars->fUseIncr = 0;
    p = Exa8_ManAlloc( pPars, pTruth );
    if ( pTruth[0] & 1 ) { fCompl = 1; Abc_TtNot( pTruth, p->nWords ); }
    if ( !pPars->fSilent ) 
        printf( "Running exact synthesis for %d-input function with %d %d-input LUTs...\n", p->nVars, p->nNodes, p->nLutSize );
    if ( Exa8_ManAddCnfStart( p, pPars->fOnlyAnd ) )
    {
        int nMints = 1 << p->nVars;
        int iMint;
        status = KISSAT_UNSAT;
        for ( iMint = 0; iMint < nMints; iMint++ )
        {
            if ( !Exa8_ManAddCnf( p, iMint ) )
                break;
        }
        if ( iMint == nMints )
        {
            if ( pPars->RuntimeLim )
            {
                p->timeStop = Abc_Clock() + pPars->RuntimeLim * CLOCKS_PER_SEC;
                kissat_set_terminate( p->pSat, p, Exa8_KissatTerminate );
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
        int DiffMint = Exa8_ManEval( p );
        if ( DiffMint != -1 )
            printf( "Warning: Verification detected a mismatch at minterm %d.\n", DiffMint );
        Exa8_ManPrintSolution( p, fCompl );
        printf( "The variable permutation is \"" );
        Exa8_ManPrintPerm(p);
        printf( "\".\n" );
        if ( pPars->fDumpBlif )
            Exa8_ManDumpBlif( p, fCompl );
        if ( p->pPars->fGenTruths ) {
            if ( p->pPars->vTruths )
                Vec_WrdFreeP( &p->pPars->vTruths );
            p->pPars->vTruths = Exa8_ManSaveTruthTables( p, fCompl );
        }
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
    if ( !pPars->fSilent && (p->nUsed[0] || p->nUsed[1]) )
        printf( "Added = %d.  Tried = %d.  ", p->nUsed[1], p->nUsed[0] );
    if ( !pPars->fSilent )
        Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
    if ( pPars->pSymStr ) 
        ABC_FREE( pPars->pTtStr );
    Exa8_ManFree( p );
    ABC_FREE( pTruth );
    return Res;
}

int Exa8_ManExactSynthesisIter( Bmc_EsPar_t * pPars )
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
        if ( 0 && fGenPerm ) {
            Vec_Str_t * vStr = Vec_StrAlloc( 100 );
            for ( int v = 0; v < pPars->nLutSize; v++ )
                Vec_StrPush( vStr, 'a'+v );
            for ( int m = 1; m < pPars->nNodes; m++ ) {
                Vec_StrPush( vStr, '_' );
                if ( m & 1 ) {
                    Vec_StrPush( vStr, '*' );
                    Vec_StrPush( vStr, '*' );
                    for ( int v = 2; v < pPars->nLutSize-1; v++ )
                        Vec_StrPush( vStr, 'a'+(pPars->nVars-(pPars->nLutSize-1-v)) );
                }
                else {
                    for ( int v = 0; v < pPars->nLutSize-3; v++ )
                        Vec_StrPush( vStr, 'a'+v );
                    Vec_StrPush( vStr, '*' );
                    Vec_StrPush( vStr, '*' );
                }
            }
            Vec_StrPush( vStr, '\0' );
            ABC_FREE( pPars->pPermStr );
            pPars->pPermStr = Vec_StrReleaseArray(vStr);
            Vec_StrFree( vStr );
        }
        Result = Exa8_ManExactSynthesis(pPars);
        fflush( stdout );
        if ( Result == 1 )
            break;
    }
    return Result;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Exa8_ManExactSynthesisPopcount( int nVars, int nLutSize, int fVerbose )
{
    assert( nVars > nLutSize );
    Bmc_EsPar_t Pars, * pPars = &Pars;
    Bmc_EsParSetDefault( pPars );
    pPars->nVars       = nVars;
    pPars->nLutSize    = nLutSize;
    pPars->fKissat     = 1;
    pPars->fLutCascade = 1;
    pPars->fUsePerm    = 1;
    pPars->fGenTruths  = 1;
    pPars->fSilent     = !fVerbose;
    int v, o, nOuts = Abc_Base2Log(nVars+1);
    Vec_Ptr_t * vRes = Vec_PtrAlloc( nOuts );
    for ( o = 0; o < nOuts; o++ ) {
        pPars->nNodes  = 10;
        ABC_FREE( pPars->pPermStr );
        pPars->pPermStr = NULL;
        char pBuffer[100];
        for ( v = 0; v <= nVars; v++ )
            pBuffer[v] = '0' + ((v >> o) & 1);
        pBuffer[nVars+1] = '\0';
        pPars->pSymStr = pBuffer;
        int status = Exa8_ManExactSynthesisIter( pPars );
        if ( status != 1 ) {
            printf( "Synthesis failed for output %d.\n", o );
            break;
        }
        Vec_PtrPush( vRes, pPars->vTruths );
        pPars->vTruths = NULL;
    }
    ABC_FREE( pPars->pPermStr );
    return vRes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
