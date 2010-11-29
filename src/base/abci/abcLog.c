/**CFile****************************************************************

  FileName    [abcLog.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Log file printing.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcLog.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "gia.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/*
    Log file format (Jiang, Mon, 28 Sep 2009)

    <result> <cyc> <engine_name>
    <TRACE> : default is "NULL"
    <INIT_STATE> : default is "NULL"
   
    <retult> is the following:
    snl_SAT
    snl_UNSAT
    snl_UNK
    snl_ABORT
   
    <cyc> : # of cycles
   
    <INIT_STATE>  : initial state
    <TRACE> : input vector
   
    <INIT_STATE>and <TRACE> are strings of 0/1/- ( - means don't care). The length is equivalent to #input*#<cyc>.
*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkWriteLogFile( char * pFileName, Abc_Cex_t * pCex, int Status, char * pCommand )
{
    FILE * pFile;
    int i;
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        printf( "Cannot open log file for writing \"%s\".\n" , pFileName );
        return;
    }
    // write <result>
    if ( Status == 1 )
        fprintf( pFile, "snl_UNSAT" );
    else if ( Status == 0 )
        fprintf( pFile, "snl_SAT" );
    else if ( Status == -1 )
        fprintf( pFile, "snl_UNK" );
    else 
        printf( "Abc_NtkWriteLogFile(): Cannot recognize solving status.\n" );
    fprintf( pFile, " " );
    // write <cyc>
    fprintf( pFile, "%d", pCex ? pCex->iFrame + 1 : -1 );
    fprintf( pFile, " " );
    // write <engine_name>
    fprintf( pFile, "%s", pCommand ? pCommand : "unknown" );
    if ( Status == 0 )
        fprintf( pFile, " %d", pCex->iPo );
    fprintf( pFile, "\n" );
    // write <INIT_STATE>
    if ( pCex == NULL )
        fprintf( pFile, "NULL" );
    else
    {
        for ( i = 0; i < pCex->nRegs; i++ )
            fprintf( pFile, "%d", Gia_InfoHasBit(pCex->pData,i) );
    }
    fprintf( pFile, "\n" );
    // write <TRACE>
    if ( pCex == NULL )
        fprintf( pFile, "NULL" );
    else
    {
        assert( pCex->nBits - pCex->nRegs == pCex->nPis * (pCex->iFrame + 1) );
        for ( i = pCex->nRegs; i < pCex->nBits; i++ )
            fprintf( pFile, "%d", Gia_InfoHasBit(pCex->pData,i) );
    }
    fprintf( pFile, "\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkReadLogFile( char * pFileName, Abc_Cex_t ** ppCex )
{
    Abc_Cex_t * pCex;
    Vec_Int_t * vNums;
    char Buffer[1000], * pToken;
    FILE * pFile;
    int c, nRegs = -1, nFrames = -1, iPo = -1, Status = -1;
    pFile = fopen( pFileName, "r" );
    if ( pFile == NULL )
    {
        printf( "Cannot open log file for reading \"%s\".\n" , pFileName );
        return -1;
    }
    fgets( Buffer, 1000, pFile );
    if ( !strncmp( Buffer, "snl_UNSAT", strlen("snl_UNSAT") ) )
    {
        Status = 1;
        nFrames = atoi( Buffer + strlen("snl_UNSAT") ); 
    }
    else if ( !strncmp( Buffer, "snl_SAT", strlen("snl_SAT") ) )
    {
        Status = 0;
//        nFrames = atoi( Buffer + strlen("snl_SAT") ); 
        pToken  = strtok( Buffer + strlen("snl_SAT"), " \t\n" );
        nFrames = atoi( pToken ); 
        pToken  = strtok( NULL, " \t\n" );
        pToken  = strtok( NULL, " \t\n" );
        iPo     = atoi( pToken ); 
    }
    else if ( !strncmp( Buffer, "snl_UNK", strlen("snl_UNK") ) )
    {
        Status = -1;
        nFrames = atoi( Buffer + strlen("snl_UNK") ); 
    }
    else
    {
        printf( "Unrecognized status.\n" );
    }
    // found regs till the new line
    vNums = Vec_IntAlloc( 100 );
    while ( (c = fgetc(pFile)) != EOF )
    {
        if ( c == '\n' )
            break;
        if ( c == '0' || c == '1' )
            Vec_IntPush( vNums, c - '0' );
    }
    nRegs = Vec_IntSize(vNums);
    // skip till the new line
    while ( (c = fgetc(pFile)) != EOF )
    {
        if ( c == '0' || c == '1' )
            Vec_IntPush( vNums, c - '0' );
    }
    fclose( pFile );
    if ( Vec_IntSize(vNums) )
    {
        if ( nRegs == 0 )
        {
            printf( "Cannot read register number.\n" );
            return -1;
        }
        if ( Vec_IntSize(vNums)-nRegs == 0 )
        {
            printf( "Cannot read counter example.\n" );
            return -1;
        }
        if ( (Vec_IntSize(vNums)-nRegs) % nFrames != 0 )
        {
            printf( "Incorrect number of bits.\n" );
            return -1;
        }
        pCex = Gia_ManAllocCounterExample( nRegs, (Vec_IntSize(vNums)-nRegs)/nFrames, nFrames );
        pCex->iPo    = iPo;
        pCex->iFrame = nFrames - 1;
        assert( Vec_IntSize(vNums) == pCex->nBits );
        for ( c = 0; c < pCex->nBits; c++ )
            if ( Vec_IntEntry(vNums, c) )
                Gia_InfoSetBit( pCex->pData, c );
        Vec_IntFree( vNums );
        if ( ppCex )
            *ppCex = pCex;
        else
            ABC_FREE( pCex );
    }
    return Status;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

