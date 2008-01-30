/**CFile****************************************************************

  FileName    [ioReadEqn.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to read equation format files.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioReadEqn.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t * Io_ReadEqnNetwork( Extra_FileReader_t * p );
static void        Io_ReadEqnStrCompact( char * pStr );
static int         Io_ReadEqnStrFind( Vec_Ptr_t * vTokens, char * pName );
static void        Io_ReadEqnStrCutAt( char * pStr, char * pStop, int fUniqueOnly, Vec_Ptr_t * vTokens );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads the network from a BENCH file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadEqn( char * pFileName, int fCheck )
{
    Extra_FileReader_t * p;
    Abc_Ntk_t * pNtk;

    // start the file
    p = Extra_FileReaderAlloc( pFileName, "#", ";", "=" );
    if ( p == NULL )
        return NULL;

    // read the network
    pNtk = Io_ReadEqnNetwork( p );
    Extra_FileReaderFree( p );
    if ( pNtk == NULL )
        return NULL;

    // make sure that everything is okay with the network structure
    if ( fCheck && !Abc_NtkCheckRead( pNtk ) )
    {
        printf( "Io_ReadEqn: The network check has failed.\n" );
        Abc_NtkDelete( pNtk );
        return NULL;
    }
    return pNtk;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadEqnNetwork( Extra_FileReader_t * p )
{
    ProgressBar * pProgress;
    Vec_Ptr_t * vTokens;
    Vec_Ptr_t * vCubes, * vLits, * vVars;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNode;
    char * pCubesCopy, * pSopCube, * pVarName;
    int iLine, iNum, i, k;
    
    // allocate the empty network
    pNtk = Abc_NtkStartRead( Extra_FileReaderGetFileName(p) );

    // go through the lines of the file
    vCubes = Vec_PtrAlloc( 100 );
    vVars  = Vec_PtrAlloc( 100 );
    vLits  = Vec_PtrAlloc( 100 );
    pProgress = Extra_ProgressBarStart( stdout, Extra_FileReaderGetFileSize(p) );
    for ( iLine = 0; vTokens = Extra_FileReaderGetTokens(p); iLine++ )
    {
        Extra_ProgressBarUpdate( pProgress, Extra_FileReaderGetCurPosition(p), NULL );

        // check if the first token contains anything
        Io_ReadEqnStrCompact( vTokens->pArray[0] );
        if ( strlen(vTokens->pArray[0]) == 0 )
            break;

        // if the number of tokens is different from two, error
        if ( vTokens->nSize != 2 )
        {
            printf( "%s: Wrong input file format.\n", Extra_FileReaderGetFileName(p) );
            Abc_NtkDelete( pNtk );
            return NULL;
        }

        // get the type of the line
        if ( strncmp( vTokens->pArray[0], "INORDER", 7 ) == 0 )
        {
            Io_ReadEqnStrCutAt( vTokens->pArray[1], " \n\r\t", 0, vVars );
            Vec_PtrForEachEntry( vVars, pVarName, i )
                Io_ReadCreatePi( pNtk, pVarName );
        }
        else if ( strncmp( vTokens->pArray[0], "OUTORDER", 8 ) == 0 )
        {
            Io_ReadEqnStrCutAt( vTokens->pArray[1], " \n\r\t", 0, vVars );
            Vec_PtrForEachEntry( vVars, pVarName, i )
                Io_ReadCreatePo( pNtk, pVarName );
        }
        else 
        {
            // remove spaces
            pCubesCopy = vTokens->pArray[1];
            Io_ReadEqnStrCompact( pCubesCopy );
            // consider the case of the constant node
            if ( (pCubesCopy[0] == '0' || pCubesCopy[0] == '1') && pCubesCopy[1] == 0 )
            {
                pNode = Io_ReadCreateNode( pNtk, vTokens->pArray[0], NULL, 0 );
                if ( pCubesCopy[0] == '0' )
                    pNode->pData = Abc_SopCreateConst0( pNtk->pManFunc );
                else
                    pNode->pData = Abc_SopCreateConst1( pNtk->pManFunc );
                continue;
            }
            // determine unique variables
            pCubesCopy = util_strsav( pCubesCopy );
            // find the names of the fanins of this node
            Io_ReadEqnStrCutAt( pCubesCopy, "!*+", 1, vVars );
            // create the node
            pNode = Io_ReadCreateNode( pNtk, vTokens->pArray[0], (char **)vVars->pArray, vVars->nSize );
            // split the string into cubes
            Io_ReadEqnStrCutAt( vTokens->pArray[1], "+", 0, vCubes );
            // start the sop
            pNode->pData = Abc_SopStart( pNtk->pManFunc, vCubes->nSize, vVars->nSize );
            // read the cubes
            i = 0;
            Abc_SopForEachCube( pNode->pData, vVars->nSize, pSopCube )
            {
                // split this cube into lits
                Io_ReadEqnStrCutAt( vCubes->pArray[i], "*", 0, vLits );
                // read the literals
                Vec_PtrForEachEntry( vLits, pVarName, k )
                {
                    iNum = Io_ReadEqnStrFind( vVars, pVarName + (pVarName[0] == '!') );
                    assert( iNum >= 0 );
                    pSopCube[iNum] = '1' - (pVarName[0] == '!');
                }
                i++;
            }
            assert( i == vCubes->nSize );
            // remove the cubes
            free( pCubesCopy );
        }
    }
    Extra_ProgressBarStop( pProgress );
    Vec_PtrFree( vCubes );
    Vec_PtrFree( vLits );
    Vec_PtrFree( vVars );
    Abc_NtkFinalizeRead( pNtk );
    return pNtk;
}



/**Function*************************************************************

  Synopsis    [Compacts the string by throwing away space-like chars.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_ReadEqnStrCompact( char * pStr )
{
    char * pCur, * pNew;
    for ( pNew = pCur = pStr; *pCur; pCur++ )
        if ( !(*pCur == ' ' || *pCur == '\n' || *pCur == '\r' || *pCur == '\t') )
            *pNew++ = *pCur;
    *pNew = 0;
}

/**Function*************************************************************

  Synopsis    [Determines unique variables in the string.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_ReadEqnStrFind( Vec_Ptr_t * vTokens, char * pName )
{
    char * pToken;
    int i;
    Vec_PtrForEachEntry( vTokens, pToken, i )
        if ( strcmp( pToken, pName ) == 0 )
            return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Cuts the string into pieces using stop chars.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_ReadEqnStrCutAt( char * pStr, char * pStop, int fUniqueOnly, Vec_Ptr_t * vTokens )
{
    char * pToken;
    Vec_PtrClear( vTokens );
    for ( pToken = strtok( pStr, pStop ); pToken; pToken = strtok( NULL, pStop ) )
        if ( !fUniqueOnly || Io_ReadEqnStrFind( vTokens, pToken ) == -1 )
            Vec_PtrPush( vTokens, pToken );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



