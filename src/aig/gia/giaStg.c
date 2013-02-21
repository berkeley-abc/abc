/**CFile****************************************************************

  FileName    [gia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: gia.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/extra/extra.h"

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
int Gia_ManCreateOrGate( Gia_Man_t * p, Vec_Int_t * vLits )
{
    if ( Vec_IntSize(vLits) == 0 )
        return 0;
    while ( Vec_IntSize(vLits) > 1 )
    {
        int i, k = 0, Lit1, Lit2, LitRes;
        Vec_IntForEachEntryDouble( vLits, Lit1, Lit2, i )
        {
            LitRes = Gia_ManHashOr( p, Lit1, Lit2 );
            Vec_IntWriteEntry( vLits, k++, LitRes );
        }
        if ( Vec_IntSize(vLits) & 1 )
            Vec_IntWriteEntry( vLits, k++, Vec_IntEntryLast(vLits) );
        Vec_IntShrink( vLits, k );
    }
    assert( Vec_IntSize(vLits) == 1 );
    return Vec_IntEntry(vLits, 0);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManStgOneHot( Vec_Int_t * vLines, int nIns, int nOuts, int nStates )
{
    Gia_Man_t * p;
    Vec_Int_t * vInMints, * vCurs, * vVec;
    Vec_Vec_t * vLitsNext, * vLitsOuts;
    int i, b, LitC, Lit;
    assert( Vec_IntSize(vLines) % 4 == 0 );

    // start manager
    p = Gia_ManStart( 10000 );
    p->pName = Abc_UtilStrsav( "stg" );
    for ( i = 0; i < nIns + nStates; i++ )
        Gia_ManAppendCi(p);

    // create input minterms
    Gia_ManHashAlloc( p );
    vInMints = Vec_IntAlloc( 1 << nIns );
    for ( i = 0; i < (1 << nIns); i++ )
    {
        for ( Lit = 1, b = 0; b < nIns; b++ )
            Lit = Gia_ManHashAnd( p, Lit, Abc_Var2Lit( b+1, !((i >> b) & 1) ) );
        Vec_IntPush( vInMints, Lit );
    } 

    // create current states
    vCurs  = Vec_IntAlloc( nStates );
    for ( i = 0; i < nStates; i++ )
        Vec_IntPush( vCurs, Abc_Var2Lit( 1+nIns+i, !i ) );

    // go through the lines
    vLitsNext = Vec_VecStart( nStates );
    vLitsOuts = Vec_VecStart( nOuts );
    for ( i = 0; i < Vec_IntSize(vLines); )
    {
        int iMint = Vec_IntEntry(vLines, i++);
        int iCur  = Vec_IntEntry(vLines, i++) - 1;
        int iNext = Vec_IntEntry(vLines, i++) - 1;
        int iOut  = Vec_IntEntry(vLines, i++);
        assert( iMint >= 0 && iMint < (1<<nIns)  );
        assert( iCur  >= 0 && iCur  < nStates    );
        assert( iNext >= 0 && iNext < nStates    );
        assert( iOut  >= 0 && iOut  < (1<<nOuts) );
        // create condition
        LitC = Gia_ManHashAnd( p, Vec_IntEntry(vInMints, iMint), Vec_IntEntry(vCurs, iCur) );
        // update next state
//        Lit = Gia_ManHashOr( p, LitC, Vec_IntEntry(vNexts, iNext) );
//        Vec_IntWriteEntry( vNexts, iNext, Lit );
        Vec_VecPushInt( vLitsNext, iNext, LitC );
        // update outputs
        for ( b = 0; b < nOuts; b++ )
            if ( (iOut >> b) & 1 ) 
            {
//                Lit = Gia_ManHashOr( p, LitC, Vec_IntEntry(vOuts, b) );
//                Vec_IntWriteEntry( vOuts, b, Lit );
                Vec_VecPushInt( vLitsOuts, b, LitC );
            }
    }
    Vec_IntFree( vInMints );
    Vec_IntFree( vCurs );

    // create POs
    Vec_VecForEachLevelInt( vLitsOuts, vVec, i )
        Gia_ManAppendCo( p, Gia_ManCreateOrGate(p, vVec) );
    Vec_VecFree( vLitsOuts );

    // create next states
    Vec_VecForEachLevelInt( vLitsNext, vVec, i )
        Gia_ManAppendCo( p, Abc_LitNotCond( Gia_ManCreateOrGate(p, vVec), !i ) );
    Vec_VecFree( vLitsNext );

    Gia_ManSetRegNum( p, nStates );
    Gia_ManHashStop( p );

    assert( !Gia_ManHasDangling(p) );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManStgPrint( FILE * pFile, Vec_Int_t * vLines, int nIns, int nOuts, int nStates )
{
    int i, nDigits = Abc_Base10Log( nStates );
    assert( Vec_IntSize(vLines) % 4 == 0 );
    for ( i = 0; i < Vec_IntSize(vLines); i += 4 )
    {
        int iMint = Vec_IntEntry(vLines, i  );
        int iCur  = Vec_IntEntry(vLines, i+1) - 1;
        int iNext = Vec_IntEntry(vLines, i+2) - 1;
        int iOut  = Vec_IntEntry(vLines, i+3);
        assert( iMint >= 0 && iMint < (1<<nIns)  );
        assert( iCur  >= 0 && iCur  < nStates    );
        assert( iNext >= 0 && iNext < nStates    );
        assert( iOut  >= 0 && iOut  < (1<<nOuts) );
        Extra_PrintBinary( pFile, (unsigned *)Vec_IntEntryP(vLines, i),  nIns );
        fprintf( pFile, " %*d",  nDigits,     Vec_IntEntry(vLines,  i+1) );
        fprintf( pFile, " %*d ", nDigits,     Vec_IntEntry(vLines,  i+2) );
        Extra_PrintBinary( pFile, (unsigned *)Vec_IntEntryP(vLines, i+3), nOuts );
        fprintf( pFile, "\n" );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManStgReadLines( char * pFileName, int * pnIns, int * pnOuts, int * pnStates )
{
    Vec_Int_t * vLines;
    char pBuffer[1000];
    char * pToken;
    int Number, nInputs = -1, nOutputs = -1, nStates = 1;
    FILE * pFile;
    if ( !strcmp(pFileName + strlen(pFileName) - 3, "aig") )
    {
        printf( "Input file \"%s\" has extension \"%s\".\n", pFileName, "aig" );
        return NULL;
    }
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\".\n", pFileName );
        return NULL;
    }
    vLines = Vec_IntAlloc( 1000 );
    while ( fgets( pBuffer, 1000, pFile ) != NULL )
    {
        // read condition
        pToken = strtok( pBuffer, " \n" );
        if ( nInputs == -1 )
            nInputs = strlen(pToken);
        else
            assert( nInputs == (int)strlen(pToken) );
        Number = Extra_ReadBinary( pToken );
        Vec_IntPush( vLines, Number );
        // read current state
        pToken = strtok( NULL, " \n" );
        Vec_IntPush( vLines, atoi(pToken) );
        nStates = Abc_MaxInt( nStates, Vec_IntEntryLast(vLines) );
        // read next state
        pToken = strtok( NULL, " \n" );
        Vec_IntPush( vLines, atoi(pToken) );
        // read output
        pToken = strtok( NULL, " \n" );
        if ( nOutputs == -1 )
            nOutputs = strlen(pToken);
        else
            assert( nOutputs == (int)strlen(pToken) );
        Number = Extra_ReadBinary( pToken );
        Vec_IntPush( vLines, Number );
    }
    fclose( pFile );
    if ( pnIns )
        *pnIns = nInputs;
    if ( pnOuts )
        *pnOuts = nOutputs;
    if ( pnStates )
        *pnStates = nStates;
    return vLines;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManStgRead( char * pFileName, int fOneHot, int fLogar )
{
    Gia_Man_t * p;
    Vec_Int_t * vLines;
    int nIns, nOuts, nStates;
    vLines = Gia_ManStgReadLines( pFileName, &nIns, &nOuts, &nStates );
    if ( vLines == NULL )
        return NULL;
    p = Gia_ManStgOneHot( vLines, nIns, nOuts, nStates );
    Vec_IntFree( vLines );
    return p;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

