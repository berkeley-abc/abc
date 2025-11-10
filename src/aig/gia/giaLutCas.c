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
int Gia_ManLutCasGen_rec( Gia_Man_t * pNew, Vec_Int_t * vCtrls, int iCtrl, Vec_Int_t * vDatas, int Shift )
{
    if ( iCtrl-- == 0 )
        return Vec_IntEntry( vDatas, Shift );
    int iLit0 = Gia_ManLutCasGen_rec( pNew, vCtrls, iCtrl, vDatas, Shift );
    int iLit1 = Gia_ManLutCasGen_rec( pNew, vCtrls, iCtrl, vDatas, Shift + (1<<iCtrl));
    return Gia_ManAppendMux( pNew, Vec_IntEntry(vCtrls, iCtrl), iLit1, iLit0 );
}
Gia_Man_t * Gia_ManLutCasGen( int nVars, int nLuts, int LutSize, int Seed, int fVerbose )
{
    srand(Seed);
    char * pPerm = Gia_LutCasPerm( nVars, nLuts, LutSize );
    int nParams = nLuts * (1 << LutSize);
    printf( "Generating AIG with %d parameters and %d inputs using fanin assignment %s.\n", nParams, nVars, pPerm );
    Gia_Man_t * pNew = Gia_ManStart( nParams + nVars );
    pNew->pName = Abc_UtilStrsav( pPerm );
    Vec_Int_t * vDatas = Vec_IntAlloc( nParams );
    Vec_Int_t * vCtrls = Vec_IntAlloc( nVars );
    for ( int i = 0; i < nParams; i++ )
        Vec_IntPush( vDatas, Gia_ManAppendCi(pNew) );
    for ( int i = 0; i < nVars; i++ )
        Vec_IntPush( vCtrls, Gia_ManAppendCi(pNew) );
    Vec_Int_t * vLits = Vec_IntStart( LutSize );
    Vec_IntWriteEntry( vLits, 0, Vec_IntEntry(vCtrls, (int)(pPerm[0]-'a')) );
    char * pCur = pPerm;
    for ( int i = 0; i < nLuts; i++ ) {
        pCur++;
        for ( int k = 1; k < LutSize; k++ )
            Vec_IntWriteEntry( vLits, k, Vec_IntEntry(vCtrls, (int)(*pCur++ - 'a')) );
        Vec_IntWriteEntry( vLits, 0, Gia_ManLutCasGen_rec(pNew, vLits, LutSize, vDatas, i * (1 << LutSize)) );        
    }
    Gia_ManAppendCo( pNew, Vec_IntEntry(vLits, 0) );
    Vec_IntFree( vDatas );
    Vec_IntFree( vCtrls );
    Vec_IntFree( vLits );
    ABC_FREE( pPerm );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

