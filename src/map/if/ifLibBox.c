/**CFile****************************************************************

  FileName    [ifLibBox.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Box library.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifLibBox.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define If_LibBoxForEachBox( p, pBox, i )     \
    Vec_PtrForEachEntry( If_Box_t *, p->vBoxes, pBox, i ) if ( pBox == NULL ) {} else

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Box_t * If_BoxStart( char * pName, int Id, int fBlack, int nPis, int nPos )
{
    If_Box_t * p;
    p = ABC_CALLOC( If_Box_t, 1 );
    p->pName   = pName; // consumes memory
    p->Id      = Id;
    p->fBlack  = fBlack;
    p->nPis    = nPis;
    p->nPos    = nPos;
    p->pDelays = ABC_CALLOC( int, nPis * nPos );
    return p;
}
If_Box_t * If_BoxDup( If_Box_t * p )
{
    If_Box_t * pNew = NULL;
    return pNew;
}
void If_BoxFree( If_Box_t * p )
{
    ABC_FREE( p->pDelays );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_LibBox_t * If_LibBoxStart()
{
    If_LibBox_t * p;
    p = ABC_CALLOC( If_LibBox_t, 1 );
    p->vBoxes = Vec_PtrAlloc( 100 );
    return p;
}
If_LibBox_t * If_LibBoxDup( If_Box_t * p )
{
    If_LibBox_t * pNew = NULL;
    return pNew;
}
void If_LibBoxFree( If_LibBox_t * p )
{
    If_Box_t * pBox;
    int i;
    if ( p == NULL )
        return;
    If_LibBoxForEachBox( p, pBox, i )
        If_BoxFree( pBox );
    Vec_PtrFree( p->vBoxes );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Box_t * If_LibBoxReadBox( If_LibBox_t * p, int Id )
{
    return (If_Box_t *)Vec_PtrEntry( p->vBoxes, Id );
}
void If_LibBoxAdd( If_LibBox_t * p, If_Box_t * pBox )
{
    if ( pBox->Id >= Vec_PtrSize(p->vBoxes) )
        Vec_PtrFillExtra( p->vBoxes, 2 * pBox->Id + 10, NULL );
    assert( Vec_PtrEntry( p->vBoxes, pBox->Id ) == NULL );
    Vec_PtrWriteEntry( p->vBoxes, pBox->Id, pBox );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * If_LibBoxGetToken( FILE * pFile )
{
    static char pBuffer[1000];
    char c, * pTemp = pBuffer;
    while ( (c = fgetc(pFile)) != EOF )
    {
        if ( c == '#' )
        {
            while ( (c = fgetc(pFile)) != EOF )
                if ( c == '\n' )
                    break;
        }
        if ( c == ' ' || c == '\t' || c == '\n' || c == '\r' )
        {
            if ( pTemp > pBuffer )
                break;
            continue;
        }
        *pTemp++ = c;
    }
    *pTemp = 0;
    return pTemp > pBuffer ? pBuffer : NULL;
}
If_LibBox_t * If_LibBoxRead( char * pFileName )
{
    FILE * pFile;
    If_LibBox_t * p;
    If_Box_t * pBox;
    char * pToken;
    char * pName;
    int i, Id, fWhite, nPis, nPos;
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\".\n", pFileName );
        return NULL;
    }
    // get the library name
    pToken = If_LibBoxGetToken( pFile );
    if ( pToken == NULL )
    {
        printf( "Cannot read library name from file \"%s\".\n", pFileName );
        return NULL;
    }
    // create library
    p = If_LibBoxStart();
    while ( pToken )
    {
        // save name
        pName  = Abc_UtilStrsav(pToken);
        // save ID
        pToken = If_LibBoxGetToken( pFile );
        Id     = atoi( pToken );
        // save white/black
        pToken = If_LibBoxGetToken( pFile );
        fWhite = atoi( pToken );
        // save PIs
        pToken = If_LibBoxGetToken( pFile );
        nPis   = atoi( pToken );
        // save POs
        pToken = If_LibBoxGetToken( pFile );
        nPos   = atoi( pToken );
        // create box
        pBox   = If_BoxStart( pName, Id, !fWhite, nPis, nPos );
        If_LibBoxAdd( p, pBox );
        // read the table
        for ( i = 0; i < nPis * nPos; i++ )
        {
            pToken = If_LibBoxGetToken( pFile );
            pBox->pDelays[i] = (pToken[0] == '-') ? -1 : atoi(pToken);
        }
        // extract next name
        pToken = If_LibBoxGetToken( pFile );
    }
    fclose( pFile );
    return p;
}
void If_LibBoxPrint( FILE * pFile, If_LibBox_t * p )
{
    If_Box_t * pBox;
    int i, j, k;
    fprintf( pFile, "# Box library written by ABC on %s.\n", Extra_TimeStamp() );
    fprintf( pFile, "# <Name> <ID> <Type> <I> <O>\n" );
    If_LibBoxForEachBox( p, pBox, i )
    {
        fprintf( pFile, "%s %d %d %d %d\n", pBox->pName, pBox->Id, !pBox->fBlack, pBox->nPis, pBox->nPos );
        for ( j = 0; j < pBox->nPos; j++, printf("\n") )
            for ( k = 0; k < pBox->nPis; k++ )
                if ( pBox->pDelays[j * pBox->nPis + k] == -1 )
                    fprintf( pFile, "    - " );
                else
                    fprintf( pFile, "%5d ", pBox->pDelays[j * pBox->nPis + k] );
    }
}
void If_LibBoxWrite( char * pFileName, If_LibBox_t * p )
{
    FILE * pFile;
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\".\n", pFileName );
        return;
    }
    If_LibBoxPrint( pFile, p );
    fclose( pFile );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

