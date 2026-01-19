/**CFile****************************************************************

  FileName    [giaLutCas.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [LUT cascade generator.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaLutCas.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

#ifdef _WIN32
#include <windows.h>
#endif
#include "sat/cnf/cnf.h"
#include "misc/util/utilTruth.h"
#include "sat/cadical/cadicalSolver.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManGenSymFun_rec( Gia_Man_t * p, word Str, int nChars, Vec_Ptr_t * vStrs,  Vec_Wec_t * vLits,  Vec_Int_t * vIns )
{
    if ( Str == 0 ) return 0;
    if ( Str == Abc_Tt6Mask(nChars) ) return 1;
    assert( nChars > 1 );
    Vec_Wrd_t * vStore = (Vec_Wrd_t *)Vec_PtrEntry(vStrs, nChars-1);
    Vec_Int_t * vValue = Vec_WecEntry(vLits, nChars-1);
    int Index;
    if ( (Index = Vec_WrdFind(vStore, Str)) >= 0 )
        return Vec_IntEntry(vValue, Index);
    word Str0 = Str & ~Abc_Tt6MaskI(nChars-1);
    word Str1 = Str >> 1;
    int Lit0 = Gia_ManGenSymFun_rec( p, Str0, nChars-1, vStrs, vLits, vIns );
    int Lit1 = Gia_ManGenSymFun_rec( p, Str1, nChars-1, vStrs, vLits, vIns );
    int Lit  = Gia_ManAppendMux2( p, Vec_IntEntry(vIns, nChars-2), Lit1, Lit0 );
    Vec_WrdPush( vStore, Str );
    Vec_WrdPush( vStore, ~Str & Abc_Tt6Mask(nChars) );
    Vec_IntPush( vValue, Lit );
    Vec_IntPush( vValue, Abc_LitNot(Lit) );
    return Lit;
}
Gia_Man_t * Gia_ManGenSymFun( Vec_Wrd_t * vFuns, int nChars, int fVerbose )
{
    assert( nChars <= 64 );
    word Str; int i;
    Vec_Ptr_t * vStrs = Vec_PtrAlloc(nChars);
    for ( i = 0; i < nChars; i++ )
        Vec_PtrPush( vStrs, Vec_WrdAlloc(0) );    
    Vec_Wec_t * vLits = Vec_WecStart(nChars);
    Vec_Int_t * vOuts = Vec_IntAlloc(Vec_WrdSize(vFuns));
    Gia_Man_t * pNew  = Gia_ManStart( 10000 );
    pNew->pName = Abc_UtilStrsav( "sym" );
    Vec_Int_t * vIns  = Vec_IntAlloc(nChars-1);
    for ( i = 0; i < nChars-1; i++ )
        Vec_IntPush(vIns, Gia_ManAppendCi(pNew));
    Vec_WrdForEachEntry( vFuns, Str, i )
        Vec_IntPush( vOuts, Gia_ManGenSymFun_rec(pNew, Str, nChars, vStrs, vLits, vIns ) );
    Vec_WrdForEachEntry( vFuns, Str, i )
        Gia_ManAppendCo(pNew, Vec_IntEntry(vOuts,i) );
    for ( i = 0; i < nChars; i++ )
        Vec_WrdFree( (Vec_Wrd_t *)Vec_PtrEntry(vStrs, i) );
    Vec_PtrFree(vStrs);
    Vec_WecFree(vLits);
    Vec_IntFree(vOuts);    
    Vec_IntFree(vIns);
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_LutCasSort( char * pStr, int iStart, int nChars )
{
    int i, j;
    for ( i = iStart; i < iStart + nChars - 1; i++ )
        for ( j = i + 1; j < iStart + nChars; j++ )
            if ( pStr[i] > pStr[j] )
                ABC_SWAP( char, pStr[i], pStr[j] );
}
char * Gia_LutCasPerm( int nVars, int nLuts, int LutSize )
{
    assert( nVars <= 26 && nLuts <= 100 );
    int nStrLen = nLuts * LutSize;
    char * pRes = ABC_CALLOC( char, nStrLen+1 );
    int i, j, iVar, pPerm[26], nVarCount[100] = {0};
    // create a random permutation
    for ( i = 0; i < nVars; i++ )
        pPerm[i] = i;
    for ( i = nVars - 1; i > 0; i-- ) {
        j = rand() % (i + 1);
        ABC_SWAP( int, pPerm[i], pPerm[j] );
    }
    // assign the first variable
    for ( i = 0; i < nLuts; i++ ) {
        pRes[i * LutSize] = i ? '_' : 'a' + pPerm[0];
        nVarCount[i] = 1;
    }
    // First pass: distribute each variable (starting from the second in permutation) to at least one LUT
    for ( i = 1; i < nVars; i++ ) {
        // Find a LUT with space that doesn't have this variable
        int Tries = 0, iLut = rand() % nLuts;
        while ( nVarCount[iLut] >= LutSize && Tries++ < nLuts )
            iLut = (iLut + 1) % nLuts;
        // the variables are unique - no need to check this
        pRes[iLut * LutSize + nVarCount[iLut]] = 'a' + pPerm[i];
        nVarCount[iLut]++;        
    }
    // Second pass: fill remaining slots with random variables (cycling through permutation)
    for ( i = 0; i < nLuts; i++ ) {
        while ( nVarCount[i] < LutSize ) {
            iVar = pPerm[rand() % nVars];
            // Check this LUT already has this variable
            for ( j = 0; j < nVarCount[i]; j++ )
                if ( pRes[i * LutSize + j] == 'a' + iVar )
                    break;
            if ( j == nVarCount[i] ) { // does not have
                pRes[i * LutSize + nVarCount[i]] = 'a' + iVar;
                nVarCount[i]++;
            }
        }
    }
    // Sort inputs within each LUT (skip '_' for non-first LUTs)
    Gia_LutCasSort( pRes, 0, LutSize );
    for ( i = 1; i < nLuts; i++ )
        Gia_LutCasSort( pRes + i * LutSize, 1, LutSize-1 );
    return pRes;
}
int Gia_ManGenLutCas_rec( Gia_Man_t * pNew, Vec_Int_t * vCtrls, int iCtrl, Vec_Int_t * vDatas, int Shift, int Offset )
{
    if ( iCtrl-- == 0 )
        return Vec_IntEntry( vDatas, Shift );
    int iLit0 = Gia_ManGenLutCas_rec( pNew, vCtrls, iCtrl, vDatas, Shift, Offset );
    int iLit1 = Gia_ManGenLutCas_rec( pNew, vCtrls, iCtrl, vDatas, Shift + (1<<iCtrl), Offset );
    return Gia_ManAppendMux( pNew, Vec_IntEntry(vCtrls, iCtrl+Offset), iLit1, iLit0 );
}
int Gia_ManGenWire( Gia_Man_t * pNew, Vec_Int_t * vCtrls, Vec_Int_t * vParams2, int iParam2 )
{
    int nVars = Vec_IntSize(vCtrls);
    int nBits = Abc_Base2Log(nVars);
    while ( Vec_IntSize(vCtrls) < (1 << nBits) )
        Vec_IntPush( vCtrls, 0 );
    int iRes = Gia_ManGenLutCas_rec( pNew, vParams2, nBits, vCtrls, 0, iParam2 );
    Vec_IntShrink( vCtrls, nVars );
    return iRes;
}
Gia_Man_t * Gia_ManGenLutCas( Gia_Man_t * p, char * pPermStr, int nVars, int nLuts, int LutSize, int Seed, int fVerbose )
{
    if ( Seed ) 
        srand(Seed); 
    else {
#ifdef _WIN32
        unsigned int seed = (unsigned int)GetTickCount();
#else
        struct timespec ts;
        clock_gettime(CLOCK_REALTIME, &ts);
        unsigned int seed = (unsigned int)(ts.tv_sec ^ ts.tv_nsec);
#endif
        srand(seed);
    }
    int fOwnPerm = (pPermStr == NULL);
    char * pPerm = fOwnPerm ? Gia_LutCasPerm( nVars, nLuts, LutSize ) : pPermStr;
    int nParams = nLuts * (1 << LutSize);
    // count how many variables are unassigned in the permutation
    int nParams2 = 0;
    for ( int v = 0; v < strlen(pPerm); v++ )
        if ( pPerm[v] == '*' )
            nParams2 += Abc_Base2Log(nVars);
    if ( fVerbose ) 
        printf( "Generating AIG with %d parameters (%d functional + %d structural) and %d inputs using fanin assignment \"%s\".\n", 
            nParams+nParams2, nParams, nParams2, nVars, pPerm );
    Gia_Man_t * pNew = Gia_ManStart( nParams + nVars );
    pNew->pName = Abc_UtilStrsav( pPerm );
    Vec_Int_t * vDatas = Vec_IntAlloc( nParams );
    Vec_Int_t * vWires = Vec_IntAlloc( nParams2 );
    Vec_Int_t * vCtrls = Vec_IntAlloc( nVars );
    for ( int i = 0; i < nParams; i++ )
        Vec_IntPush( vDatas, Gia_ManAppendCi(pNew) );
    for ( int i = 0; i < nParams2; i++ )
        Vec_IntPush( vWires, Gia_ManAppendCi(pNew) );
    for ( int i = 0; i < nVars; i++ )
        Vec_IntPush( vCtrls, Gia_ManAppendCi(pNew) );
    Vec_Int_t * vLits = Vec_IntStart( LutSize );
    Vec_IntWriteEntry( vLits, 0, pPerm[0] == '*' ? Gia_ManGenWire(pNew, vCtrls, vWires, 0) : Vec_IntEntry(vCtrls, (int)(pPerm[0]-'a')) );
    int iWireVars = pPerm[0] == '*' ? Abc_Base2Log(nVars) : 0;
    char * pCur = pPerm;
    for ( int i = 0; i < nLuts; i++ ) {
        assert( i == 0 || *pCur == '_' );
        pCur++;
        for ( int k = 1; k < LutSize; k++ ) {
            Vec_IntWriteEntry( vLits, k, *pCur == '*' ? Gia_ManGenWire(pNew, vCtrls, vWires, iWireVars) : Vec_IntEntry(vCtrls, (int)(*pCur - 'a')) );
            iWireVars += *pCur++ == '*' ? Abc_Base2Log(nVars) : 0;
        }
        Vec_IntWriteEntry( vLits, 0, Gia_ManGenLutCas_rec(pNew, vLits, LutSize, vDatas, i * (1 << LutSize), 0) );        
    }
    assert( iWireVars == nParams2 );
    // if the AIG is given, create a miter
    int iLit = Vec_IntEntry(vLits, 0);
    if ( p ) {
        assert( Gia_ManCiNum(p) == nVars );
        assert( Gia_ManCoNum(p) == 1 );
        Gia_ManFillValue( p );
        Gia_ManConst0(p)->Value = 0;
        Gia_Obj_t * pObj; int i;
        Gia_ManForEachCi( p, pObj, i )
            pObj->Value = Vec_IntEntry(vCtrls, i);
        Gia_ManForEachAnd( p, pObj, i )
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        iLit = Gia_ManAppendXor( pNew, iLit, Gia_ObjFanin0Copy(Gia_ManCo(p, 0)) );
        iLit = Abc_LitNot(iLit);
    }
    Gia_ManAppendCo( pNew, iLit );
    Vec_IntFree( vDatas );
    Vec_IntFree( vCtrls );
    Vec_IntFree( vWires );
    Vec_IntFree( vLits );
    if ( fOwnPerm )
        ABC_FREE( pPerm );
    return pNew;
}

/*
int Gia_ManGenLutCasSolve( int nVars, int nLuts, int LutSize, char * pTtStr, int fVerbose )
{
    extern Gia_Man_t * Gia_QbfQuantifyAll( Gia_Man_t * p, int nPars, int fAndAll, int fOrAll );
    assert( strlen(pTtStr) <= 1024 );
    word pTruth[64] = {0};
    int i, Id, nVars = Abc_TtReadHex( pTruth, pTtStr );
    assert( nVars <= 12 );
    int nParams = nLuts * (1 << LutSize);
    Gia_Man_t * pCas = Gia_ManGenLutCas( NULL, NULL, nVars, nLuts, LutSize, 0, fVerbose );
    Gia_Man_t * pCofs = Gia_QbfQuantifyAll( pCas, nParams, 0, 0 );
    Gia_ManFree( pCas );
    Cnf_Dat_t * pCnf = (Cnf_Dat_t *)Mf_ManGenerateCnf( pCofs, 8, 0, 0, 0, 0 );
    cadical_solver*  pSat = cadical_solver_new(void);
    cadical_solver_setnvars( pSat, pCnf->nVars );
    // add output literals
    assert( Gia_ManCoNum(pCofs) == (1 << nVars) );
    Gia_ManForEachCoId( pCofs, Id, i ) {
        int Lit = Abc_Var2Lit(pCnf->pVarNums[Id], Abc_TtGetBit(pTruth, i));
        int status = cadical_solver_addclause( pSat, &Lit, &Lit+1 ); 
    }
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !cadical_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) ) {
            Cnf_DataFree( pCnf );
            return 0;
        }
    Cnf_DataFree( pCnf );
    Gia_ManFree( pCofs );
    int status = cadical_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
    for ( i = 0; i < nLuts; i++, printf(" ") )
        for ( k = 0; k < (1 << LutSize); k++ ) {
            int Value = cadical_solver_get_var_value(pSat, i*(1 << LutSize) + k);
            printf( "%d", Value );
        }
    cadical_solver_delete( pSat );
    return 1;
}
*/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
