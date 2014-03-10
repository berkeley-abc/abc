/**CFile****************************************************************

  FileName    [ifTune.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Library tuning.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifTune.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "aig/gia/giaAig.h"
#include "sat/bsat/satStore.h"
#include "sat/cnf/cnf.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// network types
typedef enum { 
    IF_DSD_NONE = 0,               // 0:  unknown
    IF_DSD_CONST0,                 // 1:  constant
    IF_DSD_VAR,                    // 2:  variable
    IF_DSD_AND,                    // 3:  AND
    IF_DSD_XOR,                    // 4:  XOR
    IF_DSD_MUX,                    // 5:  MUX
    IF_DSD_PRIME                   // 6:  PRIME
} If_DsdType_t;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManStrCheck( char * pStr, int * pnVars, int * pnObjs )
{
    int i, Marks[32] = {0}, MaxVar = 0, MaxDef = 0, RetValue = 1;
    for ( i = 0; pStr[i]; i++ )
    {
        if ( pStr[i] == '=' || pStr[i] == ';' || 
             pStr[i] == '(' || pStr[i] == ')' || 
             pStr[i] == '[' || pStr[i] == ']' || 
             pStr[i] == '<' || pStr[i] == '>' || 
             pStr[i] == '{' || pStr[i] == '}' )
            continue;
        if ( pStr[i] >= 'a' && pStr[i] <= 'z' )
        {
            if ( pStr[i+1] == '=' )
                Marks[pStr[i] - 'a'] = 2, MaxDef = Abc_MaxInt(MaxDef, pStr[i] - 'a');
            continue;
        }
        printf( "String \"%s\" contains unrecognized symbol (%c).\n", pStr, pStr[i] );
        RetValue = 0;
    }
    if ( !RetValue )
        return 0;
    for ( i = 0; pStr[i]; i++ )
    {
        if ( pStr[i] == '=' || pStr[i] == ';' || 
             pStr[i] == '(' || pStr[i] == ')' || 
             pStr[i] == '[' || pStr[i] == ']' || 
             pStr[i] == '<' || pStr[i] == '>' || 
             pStr[i] == '{' || pStr[i] == '}' )
            continue;
        if ( pStr[i] >= 'a' && pStr[i] <= 'z' )
        {
            if ( pStr[i+1] != '=' && Marks[pStr[i] - 'a'] != 2 )
                Marks[pStr[i] - 'a'] = 1, MaxVar = Abc_MaxInt(MaxVar, pStr[i] - 'a');
            continue;
        }
        printf( "String \"%s\" contains unrecognized symbol (%c).\n", pStr, pStr[i] );
        RetValue = 0;
    }
    if ( !RetValue )
        return 0;
    MaxVar++;
    MaxDef++;
    for ( i = 0; i < MaxDef; i++ )
        if ( Marks[i] == 0 )
            printf( "String \"%s\" has no symbol (%c).\n", pStr, 'a' + i ), RetValue = 0;
    for ( i = 0; i < MaxVar; i++ )
        if ( Marks[i] == 2 )
            printf( "String \"%s\" has definition of input variable (%c).\n", pStr, 'a' + i ), RetValue = 0;
    for ( i = MaxVar; i < MaxDef; i++ )
        if ( Marks[i] == 1 )
            printf( "String \"%s\" has no definition for internal variable (%c).\n", pStr, 'a' + i ), RetValue = 0;
    if ( !RetValue )
        return 0;
    *pnVars = MaxVar;
    *pnObjs = MaxDef;
    return 1;
}
int If_ManStrParse( char * pStr, int nVars, int nObjs, int * pTypes, int * pnFans, int ppFans[][6], int * pFirsts, int * pnSatVars )
{
    int i, k, n, f, nPars = nVars;
    char Next = 0;
    assert( nVars < nObjs );
    for ( i = nVars; i < nObjs; i++ )
    {
        for ( k = 0; pStr[k]; k++ )
            if ( pStr[k] == 'a' + i && pStr[k+1] == '=' )
                break;
        assert( pStr[k] );
        if ( pStr[k+2] == '(' )
            pTypes[i] = IF_DSD_AND, Next = ')';
        else if ( pStr[k+2] == '[' )
            pTypes[i] = IF_DSD_XOR, Next = ']';
        else if ( pStr[k+2] == '<' )
            pTypes[i] = IF_DSD_MUX, Next = '>';
        else if ( pStr[k+2] == '{' )
            pTypes[i] = IF_DSD_PRIME, Next = '}';
        else assert( 0 );
        for ( n = k + 3; pStr[n]; n++ )
            if ( pStr[n] == Next )
                break;
        assert( pStr[k] );
        pnFans[i] = n - k - 3;
        assert( pnFans[i] > 0 && pnFans[i] <= 6 );
        for ( f = 0; f < pnFans[i]; f++ )
        {
            ppFans[i][f] = pStr[k + 3 + f] - 'a';
            assert( ppFans[i][k] < i );
            if ( ppFans[i][f] < 0 || ppFans[i][f] >= nObjs )
                printf( "Error!\n" );
        }
        if ( pTypes[i] != IF_DSD_PRIME )
            continue;
        pFirsts[i] = nPars;
        nPars += (1 << pnFans[i]);
    }
    *pnSatVars = nPars;
    return 1;
}
Gia_Man_t * If_ManStrFindModel( int nVars, int nObjs, int nSatVars, int * pTypes, int * pnFans, int ppFans[][6], int * pFirsts )
{
    Gia_Man_t * pNew, * pTemp;
    int * pVarsPar, * pVarsObj;
    int i, k, n, Step, iLit, nMints, nPars = 0;
    pNew = Gia_ManStart( 1000 );
    pNew->pName = Abc_UtilStrsav( "model" );
    Gia_ManHashStart( pNew );
    pVarsPar = ABC_ALLOC( int, nSatVars );
    pVarsObj = ABC_ALLOC( int, nObjs );
    for ( i = 0; i < nSatVars; i++ )
        pVarsPar[i] = Gia_ManAppendCi(pNew);
    for ( i = 0; i < nVars; i++ )
        pVarsObj[i] = pVarsPar[nSatVars - nVars + i];
    for ( i = nVars; i < nObjs; i++ )
    {
        if ( pTypes[i] == IF_DSD_AND )
        {
            iLit = 1;
            for ( k = 0; k < pnFans[i]; k++ )
                iLit = Gia_ManHashAnd( pNew, iLit, pVarsObj[ppFans[i][k]] );
            pVarsObj[i] = iLit;
        }
        else if ( pTypes[i] == IF_DSD_XOR )
        {
            iLit = 0;
            for ( k = 0; k < pnFans[i]; k++ )
                iLit = Gia_ManHashXor( pNew, iLit, pVarsObj[ppFans[i][k]] );
            pVarsObj[i] = iLit;
        }
        else if ( pTypes[i] == IF_DSD_MUX )
        {
            assert( pnFans[i] == 3 );
            pVarsObj[i] = Gia_ManHashMux( pNew, pVarsObj[ppFans[i][0]], pVarsObj[ppFans[i][1]], pVarsObj[ppFans[i][2]] );
        }
        else if ( pTypes[i] == IF_DSD_PRIME )
        {
            int pVarsData[64];
            assert( pnFans[i] >= 1 && pnFans[i] <= 6 );
            nMints = (1 << pnFans[i]);
            for ( k = 0; k < nMints; k++ )
                pVarsData[k] = pVarsPar[nPars++];
            for ( Step = 1, k = 0; k < pnFans[i]; k++, Step <<= 1 )
                for ( n = 0; n < nMints; n += Step << 1 )
                    pVarsData[n] = Gia_ManHashMux( pNew, pVarsObj[ppFans[i][k]], pVarsData[n+Step], pVarsData[n] );
            assert( Step == nMints );
            pVarsObj[i] = pVarsData[0];
        }
        else assert( 0 );
    }
    assert( nPars + nVars == nSatVars );
    Gia_ManAppendCo( pNew, pVarsObj[nObjs-1] );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    ABC_FREE( pVarsPar );
    ABC_FREE( pVarsObj );
    assert( Gia_ManPiNum(pNew) == nSatVars );
    assert( Gia_ManPoNum(pNew) == 1 );
    return pNew;
}
Gia_Man_t * If_ManStrFindCofactors( int nPars, Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pTemp; 
    Gia_Obj_t * pObj;
    int i, m, nMints = 1 << (Gia_ManCiNum(p) - nPars);
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        if ( i < nPars )
            pObj->Value = Gia_ManAppendCi( pNew );
    for ( m = 0; m < nMints; m++ )
    {
        Gia_ManForEachCi( p, pObj, i )
            if ( i >= nPars )
                pObj->Value = ((m >> (i - nPars)) & 1);
        Gia_ManForEachAnd( p, pObj, i )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Gia_ManForEachPo( p, pObj, i )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Cnf_Dat_t * Cnf_DeriveGiaRemapped( Gia_Man_t * p )
{
    Cnf_Dat_t * pCnf;
    Aig_Man_t * pAig = Gia_ManToAigSimple( p );
    pAig->nRegs = 0;
    pCnf = Cnf_Derive( pAig, Aig_ManCoNum(pAig) );
    Aig_ManStop( pAig );
    return pCnf;
}
sat_solver * If_ManStrFindSolver( Gia_Man_t * p, Vec_Int_t ** pvPiVars, Vec_Int_t ** pvPoVars )
{
    sat_solver * pSat;
    Gia_Obj_t * pObj;
    Cnf_Dat_t * pCnf;
    int i;    
    pCnf = Cnf_DeriveGiaRemapped( p );
    // start the SAT solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnf->nVars );
    // add timeframe clauses
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            assert( 0 );
    // inputs/outputs
    *pvPiVars = Vec_IntAlloc( Gia_ManPiNum(p) );
    Gia_ManForEachCi( p, pObj, i )
        Vec_IntPush( *pvPiVars, pCnf->pVarNums[Gia_ObjId(p, pObj)] );
    *pvPoVars = Vec_IntAlloc( Gia_ManPoNum(p) );
    Gia_ManForEachCo( p, pObj, i )
        Vec_IntPush( *pvPoVars, pCnf->pVarNums[Gia_ObjId(p, pObj)] );
    Cnf_DataFree( pCnf );
    return pSat;
}

sat_solver * If_ManSatBuild( char * pStr, Vec_Int_t ** pvPiVars, Vec_Int_t ** pvPoVars )
{
    int nVars, nObjs, nSatVars;
    int pTypes[32] = {0};
    int pnFans[32] = {0};
    int ppFans[32][6] = {{0}};
    int pFirsts[32] = {0};
    Gia_Man_t * p1, * p2;
    sat_solver * pSat = NULL;
    *pvPiVars = *pvPoVars = NULL;
    if ( !If_ManStrCheck(pStr, &nVars, &nObjs) )
        return NULL;
    if ( !If_ManStrParse(pStr, nVars, nObjs, pTypes, pnFans, ppFans, pFirsts, &nSatVars) )
        return NULL;
    p1 = If_ManStrFindModel(nVars, nObjs, nSatVars, pTypes, pnFans, ppFans, pFirsts);
    if ( p1 == NULL )
        return NULL;
//    Gia_AigerWrite( p1, "satbuild.aig", 0, 0 );
    p2 = If_ManStrFindCofactors( nSatVars - nVars, p1 );
    Gia_ManStop( p1 );
    if ( p2 == NULL )
        return NULL;
//    Gia_AigerWrite( p2, "satbuild2.aig", 0, 0 );
    pSat = If_ManStrFindSolver( p2, pvPiVars, pvPoVars );
    Gia_ManStop( p2 );
    return pSat;
}
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManSatPrintPerm( char * pPerms, int nVars )
{
    int i;
    for ( i = 0; i < nVars; i++ )
        printf( "%c", 'a' + pPerms[i] );
    printf( "\n" );
}
int If_ManSatCheckOne( sat_solver * pSat, Vec_Int_t * vPoVars, word * pTruth, int nVars, int * pPerm, int nVarsAll, Vec_Int_t * vLits )
{
    int v, Value, m, mNew, nMints = (1 << nVars);
    assert( (1 << nVarsAll) == Vec_IntSize(vPoVars) );
    assert( nMints <= Vec_IntSize(vPoVars) );
    // remap minterms
    Vec_IntFill( vLits, Vec_IntSize(vPoVars), -1 );
    for ( m = 0; m < nMints; m++ )
    {
        mNew = 0;
        for ( v = 0; v < nVarsAll; v++ )
        {
            assert( pPerm[v] < nVars );
            if ( ((m >> pPerm[v]) & 1) )
                mNew |= (1 << v);
        }
        assert( Vec_IntEntry(vLits, mNew) == -1 );
        Vec_IntWriteEntry( vLits, mNew, Abc_TtGetBit(pTruth, m) );
    }
    // find assumptions
    v = 0;
    Vec_IntForEachEntry( vLits, Value, m )
        if ( Value >= 0 )
            Vec_IntWriteEntry( vLits, v++, Abc_Var2Lit(Vec_IntEntry(vPoVars, m), !Value) );
    Vec_IntShrink( vLits, v );
    // run SAT solver
    Value = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), 0, 0, 0, 0 );
    return (int)(Value == l_True);
}
void If_ManSatDeriveOne( sat_solver * pSat, Vec_Int_t * vPiVars, Vec_Int_t * vValues )
{
    int i, iVar;
    Vec_IntClear( vValues );
    Vec_IntForEachEntry( vPiVars, iVar, i )
        Vec_IntPush( vValues, sat_solver_var_value(pSat, iVar) );
}
int If_ManSatCheckAll_int( sat_solver * pSat, Vec_Int_t * vPoVars, word * pTruth, int nVars, Vec_Int_t * vLits, char ** pPerms, int nPerms )
{
    int pPerm[IF_MAX_FUNC_LUTSIZE];
    int p, i;
    for ( p = 0; p < nPerms; p++ )
    {
        for ( i = 0; i < nVars; i++ )
            pPerm[i] = (int)pPerms[p][i];
        if ( If_ManSatCheckOne(pSat, vPoVars, pTruth, nVars, pPerm, nVars, vLits) )
            return p;
    }
    return -1;
}
int If_ManSatCheckAll( sat_solver * pSat, Vec_Int_t * vPoVars, word * pTruth, int nVars, Vec_Int_t * vLits, char ** pPerms, int nPerms )
{
    abctime clk = Abc_Clock();
    int RetValue = If_ManSatCheckAll_int( pSat, vPoVars, pTruth, nVars, vLits, pPerms, nPerms );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

