/**CFile****************************************************************

  FileName    [giaAiger.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Procedures to read/write binary AIGER format developed by
  Armin Biere, Johannes Kepler University (http://fmv.jku.at/)]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAiger.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Extracts one unsigned AIG edge from the input buffer.]

  Description [This procedure is a slightly modified version of Armin Biere's
  procedure "unsigned decode (FILE * file)". ]
  
  SideEffects [Updates the current reading position.]

  SeeAlso     []

***********************************************************************/
unsigned Gia_ReadAigerDecode( char ** ppPos )
{
    unsigned x = 0, i = 0;
    unsigned char ch;
    while ((ch = *(*ppPos)++) & 0x80)
        x |= (ch & 0x7f) << (7 * i++);
    return x | (ch << (7 * i));
}

/**Function*************************************************************

  Synopsis    [Decodes the encoded array of literals.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_WriteDecodeLiterals( char ** ppPos, int nEntries )
{
    Vec_Int_t * vLits;
    int Lit, LitPrev, Diff, i;
    vLits = Vec_IntAlloc( nEntries );
    LitPrev = Gia_ReadAigerDecode( ppPos );
    Vec_IntPush( vLits, LitPrev );
    for ( i = 1; i < nEntries; i++ )
    {
//        Diff = Lit - LitPrev;
//        Diff = (Lit < LitPrev)? -Diff : Diff;
//        Diff = ((2 * Diff) << 1) | (int)(Lit < LitPrev);
        Diff = Gia_ReadAigerDecode( ppPos );
        Diff = (Diff & 1)? -(Diff >> 1) : Diff >> 1;
        Lit  = Diff + LitPrev;
        Vec_IntPush( vLits, Lit );
        LitPrev = Lit;
    }
    return vLits;
}


/**Function*************************************************************

  Synopsis    [Returns the file size.]

  Description [The file should be closed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_FixFileName( char * pFileName )
{
    char * pName;
    for ( pName = pFileName; *pName; pName++ )
        if ( *pName == '>' )
            *pName = '\\';
}

/**Function*************************************************************

  Synopsis    [Returns the file size.]

  Description [The file should be closed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_FileSize( char * pFileName )
{
    FILE * pFile;
    int nFileSize;
    pFile = fopen( pFileName, "r" );
    if ( pFile == NULL )
    {
        printf( "Gia_FileSize(): The file is unavailable (absent or open).\n" );
        return 0;
    }
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile ); 
    fclose( pFile );
    return nFileSize;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Gia_FileNameGeneric( char * FileName )
{
    char * pDot, * pRes;
    pRes = Aig_UtilStrsav( FileName );
    if ( (pDot = strrchr( pRes, '.' )) )
        *pDot = 0;
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Returns the time stamp.]

  Description [The file should be closed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Gia_TimeStamp()
{
    static char Buffer[100];
    char * TimeStamp;
    time_t ltime;
    // get the current time
    time( &ltime );
    TimeStamp = asctime( localtime( &ltime ) );
    TimeStamp[ strlen(TimeStamp) - 1 ] = 0;
    strcpy( Buffer, TimeStamp );
    return Buffer;
}

/**Function*************************************************************

  Synopsis    [Reads the AIG in the binary AIGER format.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ReadAiger( char * pFileName, int fCheck )
{
    FILE * pFile;
    Gia_Man_t * pNew;
    Vec_Int_t * vLits = NULL;
    Vec_Int_t * vNodes, * vDrivers;//, * vTerms;
    int iObj, iNode0, iNode1;
    int nTotal, nInputs, nOutputs, nLatches, nAnds, nFileSize, i;//, iTerm, nDigits;
    char * pContents, * pDrivers, * pSymbols, * pCur, * pName;//, * pType;
    unsigned uLit0, uLit1, uLit;

    // read the file into the buffer
    Gia_FixFileName( pFileName );
    nFileSize = Gia_FileSize( pFileName );
    pFile = fopen( pFileName, "rb" );
    pContents = ABC_ALLOC( char, nFileSize );
    fread( pContents, nFileSize, 1, pFile );
    fclose( pFile );

    // check if the input file format is correct
    if ( strncmp(pContents, "aig", 3) != 0 || (pContents[3] != ' ' && pContents[3] != '2') )
    {
        fprintf( stdout, "Wrong input file format.\n" );
        free( pContents );
        return NULL;
    }

    // read the file type
    pCur = pContents;         while ( *pCur++ != ' ' );
    // read the number of objects
    nTotal = atoi( pCur );    while ( *pCur++ != ' ' );
    // read the number of inputs
    nInputs = atoi( pCur );   while ( *pCur++ != ' ' );
    // read the number of latches
    nLatches = atoi( pCur );  while ( *pCur++ != ' ' );
    // read the number of outputs
    nOutputs = atoi( pCur );  while ( *pCur++ != ' ' );
    // read the number of nodes
    nAnds = atoi( pCur );     while ( *pCur++ != '\n' );  
    // check the parameters
    if ( nTotal != nInputs + nLatches + nAnds )
    {
        fprintf( stdout, "The paramters are wrong.\n" );
        return NULL;
    }

    // allocate the empty AIG
    pNew = Gia_ManStart( nTotal + nLatches + nOutputs + 1 );
    pName = Gia_FileNameGeneric( pFileName );
    pNew->pName = Aig_UtilStrsav( pName );
//    pNew->pSpec = Aig_UtilStrsav( pFileName );
    ABC_FREE( pName );

    // prepare the array of nodes
    vNodes = Vec_IntAlloc( 1 + nTotal );
    Vec_IntPush( vNodes, 0 );

    // create the PIs
    for ( i = 0; i < nInputs + nLatches; i++ )
    {
        iObj = Gia_ManAppendCi(pNew);    
        Vec_IntPush( vNodes, iObj );
    }

    // remember the beginning of latch/PO literals
    pDrivers = pCur;
    if ( pContents[3] == ' ' ) // standard AIGER
    {
        // scroll to the beginning of the binary data
        for ( i = 0; i < nLatches + nOutputs; )
            if ( *pCur++ == '\n' )
                i++;
    }
    else // modified AIGER
    {
        vLits = Gia_WriteDecodeLiterals( &pCur, nLatches + nOutputs );
    }

    // create the AND gates
    for ( i = 0; i < nAnds; i++ )
    {
        uLit = ((i + 1 + nInputs + nLatches) << 1);
        uLit1 = uLit  - Gia_ReadAigerDecode( &pCur );
        uLit0 = uLit1 - Gia_ReadAigerDecode( &pCur );
//        assert( uLit1 > uLit0 );
        iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), uLit0 & 1 );
        iNode1 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit1 >> 1), uLit1 & 1 );
        assert( Vec_IntSize(vNodes) == i + 1 + nInputs + nLatches );
//        Vec_IntPush( vNodes, Gia_And(pNew, iNode0, iNode1) );
        Vec_IntPush( vNodes, Gia_ManAppendAnd(pNew, iNode0, iNode1) );
    }

    // remember the place where symbols begin
    pSymbols = pCur;

    // read the latch driver literals
    vDrivers = Vec_IntAlloc( nLatches + nOutputs );
    if ( pContents[3] == ' ' ) // standard AIGER
    {
        pCur = pDrivers;
        for ( i = 0; i < nLatches; i++ )
        {
            uLit0 = atoi( pCur );  while ( *pCur++ != '\n' );
            iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );
            Vec_IntPush( vDrivers, iNode0 );
        }
        // read the PO driver literals
        for ( i = 0; i < nOutputs; i++ )
        {
            uLit0 = atoi( pCur );  while ( *pCur++ != '\n' );
            iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );
            Vec_IntPush( vDrivers, iNode0 );
        }

    }
    else
    {
        // read the latch driver literals
        for ( i = 0; i < nLatches; i++ )
        {
            uLit0 = Vec_IntEntry( vLits, i );
            iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );
            Vec_IntPush( vDrivers, iNode0 );
        }
        // read the PO driver literals
        for ( i = 0; i < nOutputs; i++ )
        {
            uLit0 = Vec_IntEntry( vLits, i+nLatches );
            iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );
            Vec_IntPush( vDrivers, iNode0 );
        }
        Vec_IntFree( vLits );
    }

    // create the POs
    for ( i = 0; i < nOutputs; i++ )
        Gia_ManAppendCo( pNew, Vec_IntEntry(vDrivers, nLatches + i) );
    for ( i = 0; i < nLatches; i++ )
        Gia_ManAppendCo( pNew, Vec_IntEntry(vDrivers, i) );
    Vec_IntFree( vDrivers );

    // create the latches
    Gia_ManSetRegNum( pNew, nLatches );

    // skipping the comments
    ABC_FREE( pContents );
    Vec_IntFree( vNodes );
/*
    // check the result
    if ( fCheck && !Gia_ManCheck( pNew ) )
    {
        printf( "Gia_ReadAiger: The network check has failed.\n" );
        Gia_ManStop( pNew );
        return NULL;
    }
*/
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Adds one unsigned AIG edge to the output buffer.]

  Description [This procedure is a slightly modified version of Armin Biere's
  procedure "void encode (FILE * file, unsigned x)" ]
  
  SideEffects [Returns the current writing position.]

  SeeAlso     []

***********************************************************************/
int Gia_WriteAigerEncode( unsigned char * pBuffer, int Pos, unsigned x )
{
    unsigned char ch;
    while (x & ~0x7f)
    {
        ch = (x & 0x7f) | 0x80;
        pBuffer[Pos++] = ch;
        x >>= 7;
    }
    ch = x;
    pBuffer[Pos++] = ch;
    return Pos;
}

/**Function*************************************************************

  Synopsis    [Create the array of literals to be written.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_WriteAigerLiterals( Gia_Man_t * p )
{
    Vec_Int_t * vLits;
    Gia_Obj_t * pObj;
    int i;
    vLits = Vec_IntAlloc( Gia_ManPoNum(p) );
    Gia_ManForEachRi( p, pObj, i )
        Vec_IntPush( vLits, Gia_ObjFaninLit0p(p, pObj) );
    Gia_ManForEachPo( p, pObj, i )
        Vec_IntPush( vLits, Gia_ObjFaninLit0p(p, pObj) );
    return vLits;
}

/**Function*************************************************************

  Synopsis    [Creates the binary encoded array of literals.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Gia_WriteEncodeLiterals( Vec_Int_t * vLits )
{
    Vec_Str_t * vBinary;
    int Pos = 0, Lit, LitPrev, Diff, i;
    vBinary = Vec_StrAlloc( 2 * Vec_IntSize(vLits) );
    LitPrev = Vec_IntEntry( vLits, 0 );
    Pos = Gia_WriteAigerEncode( (unsigned char *)Vec_StrArray(vBinary), Pos, LitPrev ); 
    Vec_IntForEachEntryStart( vLits, Lit, i, 1 )
    {
        Diff = Lit - LitPrev;
        Diff = (Lit < LitPrev)? -Diff : Diff;
        Diff = (Diff << 1) | (int)(Lit < LitPrev);
        Pos = Gia_WriteAigerEncode( (unsigned char *)Vec_StrArray(vBinary), Pos, Diff );
        LitPrev = Lit;
        if ( Pos + 10 > vBinary->nCap )
            Vec_StrGrow( vBinary, vBinary->nCap+1 );
    }
    vBinary->nSize = Pos;
/*
    // verify
    {
        extern Vec_Int_t * Gia_WriteDecodeLiterals( char ** ppPos, int nEntries );
        char * pPos = Vec_StrArray( vBinary );
        Vec_Int_t * vTemp = Gia_WriteDecodeLiterals( &pPos, Vec_IntSize(vLits) );
        for ( i = 0; i < Vec_IntSize(vLits); i++ )
        {
            int Entry1 = Vec_IntEntry(vLits,i);
            int Entry2 = Vec_IntEntry(vTemp,i);
            assert( Entry1 == Entry2 );
        }
        Vec_IntFree( vTemp );
    }
*/
    return vBinary;
}

/**Function*************************************************************

  Synopsis    [Writes the AIG in the binary AIGER format.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_WriteAiger( Gia_Man_t * pInit, char * pFileName, int fWriteSymbols, int fCompact )
{
    FILE * pFile;
    Gia_Man_t * p;
    Gia_Obj_t * pObj;
    int i, nBufferSize, Pos;
    unsigned char * pBuffer;
    unsigned uLit0, uLit1, uLit;

    if ( Gia_ManCoNum(pInit) == 0 )
    {
        printf( "AIG cannot be written because it has no POs.\n" );
        return;
    }

    // start the output stream
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Gia_WriteAiger(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }

    // create normalized AIG
    if ( !Gia_ManIsNormalized(pInit) )
        p = Gia_ManDupNormalized( pInit );
    else
        p = pInit;

    // write the header "M I L O A" where M = I + L + A
    fprintf( pFile, "aig%s %u %u %u %u %u\n", 
        fCompact? "2" : "",
        Gia_ManCiNum(p) + Gia_ManAndNum(p), 
        Gia_ManPiNum(p),
        Gia_ManRegNum(p),
        Gia_ManPoNum(p),
        Gia_ManAndNum(p) );

    if ( !fCompact ) 
    {
        // write latch drivers
        Gia_ManForEachRi( p, pObj, i )
            fprintf( pFile, "%u\n", Gia_ObjFaninLit0p(p, pObj) );
        // write PO drivers
        Gia_ManForEachPo( p, pObj, i )
            fprintf( pFile, "%u\n", Gia_ObjFaninLit0p(p, pObj) );
    }
    else
    {
        Vec_Int_t * vLits = Gia_WriteAigerLiterals( p );
        Vec_Str_t * vBinary = Gia_WriteEncodeLiterals( vLits );
        fwrite( Vec_StrArray(vBinary), 1, Vec_StrSize(vBinary), pFile );
        Vec_StrFree( vBinary );
        Vec_IntFree( vLits );
    }

    // write the nodes into the buffer
    Pos = 0;
    nBufferSize = 6 * Gia_ManAndNum(p) + 100; // skeptically assuming 3 chars per one AIG edge
    pBuffer = ABC_ALLOC( unsigned char, nBufferSize );
    Gia_ManForEachAnd( p, pObj, i )
    {
        uLit  = Gia_Var2Lit( i, 0 );
        uLit0 = Gia_ObjFaninLit0( pObj, i );
        uLit1 = Gia_ObjFaninLit1( pObj, i );
        assert( uLit0 < uLit1 );
        Pos = Gia_WriteAigerEncode( pBuffer, Pos, uLit  - uLit1 );
        Pos = Gia_WriteAigerEncode( pBuffer, Pos, uLit1 - uLit0 );
        if ( Pos > nBufferSize - 10 )
        {
            printf( "Gia_WriteAiger(): AIGER generation has failed because the allocated buffer is too small.\n" );
            fclose( pFile );
            if ( p != pInit )
                Gia_ManStop( p );
            return;
        }
    }
    assert( Pos < nBufferSize );

    // write the buffer
    fwrite( pBuffer, 1, Pos, pFile );
    ABC_FREE( pBuffer );

    // write the comment
    fprintf( pFile, "c\n" );
    if ( p->pName )
        fprintf( pFile, ".model %s\n", p->pName );
    fprintf( pFile, "This file was produced by the AIG package on %s\n", Gia_TimeStamp() );
    fprintf( pFile, "For information about AIGER format, refer to %s\n", "http://fmv.jku.at/aiger" );
    fclose( pFile );
    if ( p != pInit )
        Gia_ManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


