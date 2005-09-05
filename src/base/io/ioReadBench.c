/**CFile****************************************************************

  FileName    [ioReadBench.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to read BENCH files.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioReadBench.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t * Io_ReadBenchNetwork( Extra_FileReader_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads the network from a BENCH file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadBench( char * pFileName, int fCheck )
{
    Extra_FileReader_t * p;
    Abc_Ntk_t * pNtk;

    // start the file
    p = Extra_FileReaderAlloc( pFileName, "#", "\n", " \t\r,()=" );
    if ( p == NULL )
        return NULL;

    // read the network
    pNtk = Io_ReadBenchNetwork( p );
    Extra_FileReaderFree( p );
    if ( pNtk == NULL )
        return NULL;

    // make sure that everything is okay with the network structure
    if ( fCheck && !Abc_NtkCheckRead( pNtk ) )
    {
        printf( "Io_ReadBench: The network check has failed.\n" );
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
Abc_Ntk_t * Io_ReadBenchNetwork( Extra_FileReader_t * p )
{
    ProgressBar * pProgress;
    Vec_Ptr_t * vTokens;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNet, * pNode;
    Vec_Str_t * vString;
    char * pType, ** ppNames;
    int iLine, nNames;
    
    // allocate the empty network
    pNtk = Abc_NtkStartRead( Extra_FileReaderGetFileName(p) );

    // go through the lines of the file
    vString = Vec_StrAlloc( 100 );
    pProgress = Extra_ProgressBarStart( stdout, Extra_FileReaderGetFileSize(p) );
    for ( iLine = 0; vTokens = Extra_FileReaderGetTokens(p); iLine++ )
    {
        Extra_ProgressBarUpdate( pProgress, Extra_FileReaderGetCurPosition(p), NULL );

        if ( vTokens->nSize == 1 )
        {
            printf( "%s: Wrong input file format.\n", Extra_FileReaderGetFileName(p) );
            Abc_NtkDelete( pNtk );
            return NULL;
        }

        // get the type of the line
        if ( strncmp( vTokens->pArray[0], "INPUT", 5 ) == 0 )
            Io_ReadCreatePi( pNtk, vTokens->pArray[1] );
        else if ( strncmp( vTokens->pArray[0], "OUTPUT", 5 ) == 0 )
            Io_ReadCreatePo( pNtk, vTokens->pArray[1] );
        else 
        {
            // get the node name and the node type
            pType = vTokens->pArray[1];
            if ( strcmp(pType, "DFF") == 0 )
                Io_ReadCreateLatch( pNtk, vTokens->pArray[2], vTokens->pArray[0] );
            else
            {
                // create a new node and add it to the network
                ppNames = (char **)vTokens->pArray + 2;
                nNames  = vTokens->nSize - 2;
                pNode = Io_ReadCreateNode( pNtk, vTokens->pArray[0], ppNames, nNames );
                // assign the cover
                if ( strcmp(pType, "AND") == 0 )
                    Abc_ObjSetData( pNode, Abc_SopCreateAnd(pNtk->pManFunc, nNames) );
                else if ( strcmp(pType, "OR") == 0 )
                    Abc_ObjSetData( pNode, Abc_SopCreateOr(pNtk->pManFunc, nNames, NULL) );
                else if ( strcmp(pType, "NAND") == 0 )
                    Abc_ObjSetData( pNode, Abc_SopCreateNand(pNtk->pManFunc, nNames) );
                else if ( strcmp(pType, "NOR") == 0 )
                    Abc_ObjSetData( pNode, Abc_SopCreateNor(pNtk->pManFunc, nNames) );
                else if ( strcmp(pType, "XOR") == 0 )
                    Abc_ObjSetData( pNode, Abc_SopCreateXor(pNtk->pManFunc, nNames) );
                else if ( strcmp(pType, "NXOR") == 0 )
                    Abc_ObjSetData( pNode, Abc_SopCreateNxor(pNtk->pManFunc, nNames) );
                else if ( strncmp(pType, "BUF", 3) == 0 )
                    Abc_ObjSetData( pNode, Abc_SopCreateBuf(pNtk->pManFunc) );
                else if ( strcmp(pType, "NOT") == 0 )
                    Abc_ObjSetData( pNode, Abc_SopCreateInv(pNtk->pManFunc) );
                else 
                {
                    printf( "Cannot determine gate type \"%s\" in line %d.\n", pType, Extra_FileReaderGetLineNumber(p, 0) );
                    Abc_NtkDelete( pNtk );
                    return NULL;
                }
            }
        }
    }
    Extra_ProgressBarStop( pProgress );
    Vec_StrFree( vString );

    // check if constant have been added
    if ( pNet = Abc_NtkFindNet( pNtk, "vdd" ) )
        Io_ReadCreateConst( pNtk, "vdd", 1 );
    if ( pNet = Abc_NtkFindNet( pNtk, "gnd" ) )
        Io_ReadCreateConst( pNtk, "gnd", 0 );

    Abc_NtkFinalizeRead( pNtk );
    return pNtk;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



