/**CFile****************************************************************

  FileName    [giaGen.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaGen.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Populate internal simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word * Gia_ManObjSim( Gia_Man_t * p, int iObj )
{
    return Vec_WrdEntryP( p->vSims, p->nSimWords * iObj );
}
static inline void Gia_ManObjSimPi( Gia_Man_t * p, int iObj )
{
    int w;
    word * pSim = Gia_ManObjSim( p, iObj );
    for ( w = 0; w < p->nSimWords; w++ )
        pSim[w] = Gia_ManRandomW( 0 );
//    pSim[0] <<= 1;
}
static inline void Gia_ManObjSimPo( Gia_Man_t * p, int iObj )
{
    int w;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    word * pSimCo  = Gia_ManObjSim( p, iObj );
    word * pSimDri = Gia_ManObjSim( p, Gia_ObjFaninId0(pObj, iObj) );
    if ( Gia_ObjFaninC0(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSimCo[w] = ~pSimDri[w];
    else
        for ( w = 0; w < p->nSimWords; w++ )
            pSimCo[w] =  pSimDri[w];
}
static inline void Gia_ManObjSimAnd( Gia_Man_t * p, int iObj )
{
    int w;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    word * pSim  = Gia_ManObjSim( p, iObj );
    word * pSim0 = Gia_ManObjSim( p, Gia_ObjFaninId0(pObj, iObj) );
    word * pSim1 = Gia_ManObjSim( p, Gia_ObjFaninId1(pObj, iObj) );
    if ( Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = ~pSim0[w] & ~pSim1[w];
    else if ( Gia_ObjFaninC0(pObj) && !Gia_ObjFaninC1(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = ~pSim0[w] & pSim1[w];
    else if ( !Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = pSim0[w] & ~pSim1[w];
    else
        for ( w = 0; w < p->nSimWords; w++ )
            pSim[w] = pSim0[w] & pSim1[w];
}
int Gia_ManSimulateWords( Gia_Man_t * p, int nWords )
{
    Gia_Obj_t * pObj; int i;
    // allocate simulation info for one timeframe
    Vec_WrdFreeP( &p->vSims );
    p->vSims = Vec_WrdStart( Gia_ManObjNum(p) * nWords );
    p->nSimWords = nWords;
    // perform simulation
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            Gia_ManObjSimAnd( p, i );
        else if ( Gia_ObjIsCi(pObj) )
            Gia_ManObjSimPi( p, i );
        else if ( Gia_ObjIsCo(pObj) )
            Gia_ManObjSimPo( p, i );
        else assert( 0 );
    }
    return 1;
}

int Gia_ManSimulateWordsInit( Gia_Man_t * p, Vec_Wrd_t * vSimsIn )
{
    Gia_Obj_t * pObj; int i, Id;
    int nWords = Vec_WrdSize(vSimsIn) / Gia_ManCiNum(p);
    assert( Vec_WrdSize(vSimsIn) == nWords * Gia_ManCiNum(p) );
    // allocate simulation info for one timeframe
    Vec_WrdFreeP( &p->vSims );
    p->vSims = Vec_WrdStart( Gia_ManObjNum(p) * nWords );
    p->nSimWords = nWords;
    // set input sim info
    Gia_ManForEachCiId( p, Id, i )
        memcpy( Vec_WrdEntryP(p->vSims, Id*nWords), Vec_WrdEntryP(vSimsIn, i*nWords), sizeof(word)*nWords );
    // perform simulation
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            Gia_ManObjSimAnd( p, i );
        else if ( Gia_ObjIsCi(pObj) )
            continue;
        else if ( Gia_ObjIsCo(pObj) )
            Gia_ManObjSimPo( p, i );
        else assert( 0 );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Dump data files.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDumpFiles( Gia_Man_t * p, int nCexesT, int nCexesV, int Seed, char * pFileName )
{
    int n, nSize[2] = {nCexesT*64, nCexesV*64};

    char pFileNameOutTX[100];
    char pFileNameOutTY[100];
    char pFileNameOutVX[100];
    char pFileNameOutVY[100];
    char pFileNameOut[100];
    
    //sprintf( pFileNameOutTX, "train_%s_%d_%d.data", pFileName ? pFileName : Gia_ManName(p), nSize[0], Gia_ManCiNum(p) );
    //sprintf( pFileNameOutTY, "train_%s_%d_%d.data", pFileName ? pFileName : Gia_ManName(p), nSize[0], Gia_ManCoNum(p) );
    //sprintf( pFileNameOutVX, "test_%s_%d_%d.data",  pFileName ? pFileName : Gia_ManName(p), nSize[1], Gia_ManCiNum(p) );
    //sprintf( pFileNameOutVY, "test_%s_%d_%d.data",  pFileName ? pFileName : Gia_ManName(p), nSize[1], Gia_ManCoNum(p) );
    
    sprintf( pFileNameOutTX, "%s_x.train.data", pFileName ? pFileName : Gia_ManName(p) );
    sprintf( pFileNameOutTY, "%s_y.train.data", pFileName ? pFileName : Gia_ManName(p) );
    sprintf( pFileNameOutVX, "%s_x.test.data",  pFileName ? pFileName : Gia_ManName(p) );
    sprintf( pFileNameOutVY, "%s_y.test.data",  pFileName ? pFileName : Gia_ManName(p) );

    Gia_ManRandomW( 1 );
    for ( n = 0; n < Seed; n++ )
        Gia_ManRandomW( 0 );
    for ( n = 0; n < 2; n++ )
    {
        int Res = Gia_ManSimulateWords( p, nSize[n] );

        Vec_Bit_t * vBitX = Vec_BitAlloc( nSize[n] * Gia_ManCiNum(p) );
        Vec_Bit_t * vBitY = Vec_BitAlloc( nSize[n] * Gia_ManCoNum(p) );

        FILE * pFileOutX  = fopen( n ? pFileNameOutVX : pFileNameOutTX, "wb" );
        FILE * pFileOutY  = fopen( n ? pFileNameOutVY : pFileNameOutTY, "wb" );

        int i, k, Id, Num, Value, nBytes;
        for ( k = 0; k < nSize[n]; k++ )
        {
            Gia_ManForEachCiId( p, Id, i )
            {
                Vec_BitPush( vBitX, Abc_TtGetBit(Gia_ManObjSim(p, Id), k) );
                //printf( "%d", Abc_TtGetBit(Gia_ManObjSim(p, Id), k) );
            }
            //printf( " " );
            Gia_ManForEachCoId( p, Id, i )
            {
                Vec_BitPush( vBitY, Abc_TtGetBit(Gia_ManObjSim(p, Id), k) );
                //printf( "%d", Abc_TtGetBit(Gia_ManObjSim(p, Id), k) );
            }
            //printf( "\n" );
        }
        assert( Vec_BitSize(vBitX) <= Vec_BitCap(vBitX) );
        assert( Vec_BitSize(vBitY) <= Vec_BitCap(vBitY) );

        Num = 2;               Value = fwrite( &Num, 1, 4, pFileOutX ); assert( Value == 4 );
        Num = nSize[n];        Value = fwrite( &Num, 1, 4, pFileOutX ); assert( Value == 4 );
        Num = Gia_ManCiNum(p); Value = fwrite( &Num, 1, 4, pFileOutX ); assert( Value == 4 );

        nBytes = nSize[n] * Gia_ManCiNum(p) / 8;
        assert( nSize[n] * Gia_ManCiNum(p) % 8 == 0 );
        Value = fwrite( Vec_BitArray(vBitX), 1, nBytes, pFileOutX );
        assert( Value == nBytes );

        Num = 2;               Value = fwrite( &Num, 1, 4, pFileOutY ); assert( Value == 4 );
        Num = nSize[n];        Value = fwrite( &Num, 1, 4, pFileOutY ); assert( Value == 4 );
        Num = Gia_ManCoNum(p); Value = fwrite( &Num, 1, 4, pFileOutY ); assert( Value == 4 );

        nBytes = nSize[n] * Gia_ManCoNum(p) / 8;
        assert( nSize[n] * Gia_ManCoNum(p) % 8 == 0 );
        Value = fwrite( Vec_BitArray(vBitY), 1, nBytes, pFileOutY );
        assert( Value == nBytes );

        fclose( pFileOutX );
        fclose( pFileOutY );

        Vec_BitFree( vBitX );
        Vec_BitFree( vBitY );

        Res = 0;
    }
    printf( "Finished dumping files \"%s\" and \"%s\".\n", pFileNameOutTX, pFileNameOutTY );
    printf( "Finished dumping files \"%s\" and \"%s\".\n", pFileNameOutVX, pFileNameOutVY );

    sprintf( pFileNameOut, "%s.flist", pFileName ? pFileName : Gia_ManName(p) );
    {
        FILE * pFile = fopen( pFileNameOut, "wb" );
        fprintf( pFile, "%s\n", pFileNameOutTX );
        fprintf( pFile, "%s\n", pFileNameOutTY );
        fprintf( pFile, "%s\n", pFileNameOutVX );
        fprintf( pFile, "%s\n", pFileNameOutVY );
        fclose( pFile );
        printf( "Finished dumping file list \"%s\".\n", pFileNameOut );
    }
}

/**Function*************************************************************

  Synopsis    [Dump data files.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDumpPlaFiles( Gia_Man_t * p, int nCexesT, int nCexesV, int Seed, char * pFileName )
{
    int n, nSize[3] = {nCexesT, nCexesV, nCexesV};

    char pFileNameOut[3][100];
    
    sprintf( pFileNameOut[0], "%s.train.pla", pFileName ? pFileName : Gia_ManName(p) );
    sprintf( pFileNameOut[1], "%s.valid.pla", pFileName ? pFileName : Gia_ManName(p) );
    sprintf( pFileNameOut[2], "%s.test.pla",  pFileName ? pFileName : Gia_ManName(p) );

    Gia_ManRandomW( 1 );
    for ( n = 0; n < Seed; n++ )
        Gia_ManRandomW( 0 );
    for ( n = 0; n < 3; n++ )
    {
        int Res = Gia_ManSimulateWords( p, nSize[n] );
        int i, k, Id;

        FILE * pFileOut  = fopen( pFileNameOut[n], "wb" );

        fprintf( pFileOut, ".i %d\n", Gia_ManCiNum(p) );
        fprintf( pFileOut, ".o %d\n", Gia_ManCoNum(p) );
        fprintf( pFileOut, ".p %d\n", nSize[n]*64 );
        fprintf( pFileOut, ".type fr\n" );
        for ( k = 0; k < nSize[n]*64; k++ )
        {
            Gia_ManForEachCiId( p, Id, i )
            {
                //Vec_BitPush( vBitX, Abc_TtGetBit(Gia_ManObjSim(p, Id), k) );
                fprintf( pFileOut, "%d", Abc_TtGetBit(Gia_ManObjSim(p, Id), k) );
            }
            fprintf( pFileOut, " " );
            Gia_ManForEachCoId( p, Id, i )
            {
                //Vec_BitPush( vBitY, Abc_TtGetBit(Gia_ManObjSim(p, Id), k) );
                fprintf( pFileOut, "%d", Abc_TtGetBit(Gia_ManObjSim(p, Id), k) );
            }
            fprintf( pFileOut, "\n" );
        }
        fprintf( pFileOut, ".e\n" );

        fclose( pFileOut );

        Res = 0;
    }
    printf( "Finished dumping files: \"%s.{train, valid, test}.pla\".\n", pFileName ? pFileName : Gia_ManName(p) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSimLogStats( Gia_Man_t * p, char * pDumpFile, int Total, int Correct, int Guess )
{
    FILE * pTable = fopen( pDumpFile, "wb" );
    fprintf( pTable, "{\n" );
    fprintf( pTable, "    \"name\" : \"%s\",\n", p->pName );
    fprintf( pTable, "    \"input\" : %d,\n",    Gia_ManCiNum(p) );
    fprintf( pTable, "    \"output\" : %d,\n",   Gia_ManCoNum(p) );
    fprintf( pTable, "    \"and\" : %d,\n",      Gia_ManAndNum(p) );
    fprintf( pTable, "    \"level\" : %d,\n",    Gia_ManLevelNum(p) );
    fprintf( pTable, "    \"total\" : %d,\n",    Total );
    fprintf( pTable, "    \"correct\" : %d,\n",  Correct );
    fprintf( pTable, "    \"guess\" : %d\n",     Guess );
    fprintf( pTable, "}\n" );
    fclose( pTable );
}
int Gia_ManSimParamRead( char * pFileName, int * pnIns, int * pnWords )
{
    int c, nIns = -1, nLines = 0, Count = 0, fReadDot = 0;
    FILE * pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return 0;
    }
    while ( (c = fgetc(pFile)) != EOF )
    {
        if ( c == '.' )
            fReadDot = 1;
        if ( c == '\n' )
        {
            if ( !fReadDot )
            {
                if ( nIns == -1 )
                    nIns = Count;
                else if ( nIns != Count )
                {
                    printf( "The number of symbols (%d) does not match other lines (%d).\n", Count, nIns );
                    fclose( pFile );
                    return 0;
                }
                Count = 0;
                nLines++;
            }
            fReadDot = 0;
        }
        if ( fReadDot )
            continue;
        if ( c != '0' && c != '1' )
            continue;
        Count++;
    }
    if ( nLines % 64 > 0 )
    {
        printf( "The number of lines (%d) is not divisible by 64.\n", nLines );
        fclose( pFile );
        return 0;
    }
    *pnIns = nIns - 1;
    *pnWords = nLines / 64;
    //printf( "Expecting %d inputs and %d words of simulation data.\n", *pnIns, *pnWords );
    fclose( pFile );
    return 1;
}
void Gia_ManSimFileRead( char * pFileName, int nIns, int nWords, Vec_Wrd_t * vSimsIn, Vec_Int_t * vValues )
{
    int c, nPats = 0, Count = 0, fReadDot = 0;
    FILE * pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return;
    }
    assert( Vec_WrdSize(vSimsIn) % nWords == 0 );
    while ( (c = fgetc(pFile)) != EOF )
    {
        if ( c == '.' )
            fReadDot = 1;
        if ( c == '\n' )
            fReadDot = 0;
        if ( fReadDot )
            continue;
        if ( c != '0' && c != '1' )
            continue;
        if ( Count == nIns )
        {
            Vec_IntPush( vValues, c - '0' );
            Count = 0;
            nPats++;
        }
        else
        {
            if ( c == '1' )
                Abc_TtSetBit( Vec_WrdEntryP(vSimsIn, Count * nWords), nPats );
            Count++;
        }
    }
    assert( nPats == 64*nWords );
    fclose( pFile );
    printf( "Finished reading %d simulation patterns for %d inputs. Probability of 1 at the output is %6.2f %%.\n", 64*nWords, nIns, 100.0*Vec_IntSum(vValues)/nPats );
}
void Gia_ManCompareValues( Gia_Man_t * p, Vec_Wrd_t * vSimsIn, Vec_Int_t * vValues, char * pDumpFile )
{
    int i, Value, Guess, Count = 0, nWords = Vec_WrdSize(vSimsIn) / Gia_ManCiNum(p);
    word * pSims;
    assert( Vec_IntSize(vValues) == nWords * 64 );
    Gia_ManSimulateWordsInit( p, vSimsIn );
    assert( p->nSimWords == nWords );
    pSims = Gia_ManObjSim( p, Gia_ObjId(p, Gia_ManCo(p, 0)) );
    Vec_IntForEachEntry( vValues, Value, i )
        if ( Abc_TtGetBit(pSims, i) == Value )
            Count++;
    Guess = (Vec_IntSum(vValues) > nWords * 32) ? Vec_IntSum(vValues) : nWords * 64 - Vec_IntSum(vValues);
    printf( "Total = %6d.  Errors = %6d.  Correct = %6d.  (%6.2f %%)   Naive guess = %6d.  (%6.2f %%)\n", 
        Vec_IntSize(vValues), Vec_IntSize(vValues) - Count, 
        Count, 100.0*Count/Vec_IntSize(vValues),
        Guess, 100.0*Guess/Vec_IntSize(vValues));
    if ( pDumpFile == NULL )
        return;
    Gia_ManSimLogStats( p, pDumpFile, Vec_IntSize(vValues), Count, Guess );
    printf( "Finished dumping statistics into file \"%s\".\n", pDumpFile );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManTestOneFile( Gia_Man_t * p, char * pFileName, char * pDumpFile )
{
    Vec_Wrd_t * vSimsIn;
    Vec_Int_t * vValues;
    int nIns, nWords;
    if ( !Gia_ManSimParamRead( pFileName, &nIns, &nWords ) )
        return;
    if ( nIns != Gia_ManCiNum(p) )
    {
        printf( "The number of inputs in the file \"%s\" (%d) does not match the AIG (%d).\n", pFileName, nIns, Gia_ManCiNum(p) );
        return;
    }
    vSimsIn = Vec_WrdStart( nIns * nWords );
    vValues = Vec_IntAlloc( nWords * 64 );
    Gia_ManSimFileRead( pFileName, nIns, nWords, vSimsIn, vValues );
    Gia_ManCompareValues( p, vSimsIn, vValues, pDumpFile );
    Vec_WrdFree( vSimsIn );
    Vec_IntFree( vValues );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

