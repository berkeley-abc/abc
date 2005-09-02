/**CFile****************************************************************

  FileName    [abcShow.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Visualization procedures using DOT software and GSView.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcShow.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifdef WIN32
#include <process.h> 
#endif

#include "abc.h"
#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Abc_ShowFile( char * FileNameDot );
static void Abc_ShowGetFileName( char * pName, char * pBuffer );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Visualizes BDD of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeShowBdd( Abc_Obj_t * pNode )
{
    FILE * pFile;
    Vec_Ptr_t * vNamesIn;
    char FileNameDot[200];
    char * pNameOut;

    assert( Abc_NtkIsBddLogic(pNode->pNtk) );
    // create the file name
    Abc_ShowGetFileName( Abc_ObjName(pNode), FileNameDot );
    // check that the file can be opened
    if ( (pFile = fopen( FileNameDot, "w" )) == NULL )
    {
        fprintf( stdout, "Cannot open the intermediate file \"%s\".\n", FileNameDot );
        return;
    }

    // set the node names 
    vNamesIn = Abc_NodeGetFaninNames( pNode );
    pNameOut = Abc_ObjName(pNode);
    Cudd_DumpDot( pNode->pNtk->pManFunc, 1, (DdNode **)&pNode->pData, (char **)vNamesIn->pArray, &pNameOut, pFile );
    Abc_NodeFreeNames( vNamesIn );
    Abc_NtkCleanCopy( pNode->pNtk );
    fclose( pFile );

    // visualize the file 
    Abc_ShowFile( FileNameDot );
}

/**Function*************************************************************

  Synopsis    [Visualizes AIG with choices.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkShowAig( Abc_Ntk_t * pNtk )
{
    FILE * pFile;
    Abc_Obj_t * pNode;
    Vec_Ptr_t * vNodes;
    char FileNameDot[200];
    int i;

    assert( Abc_NtkIsStrash(pNtk) );
    // create the file name
    Abc_ShowGetFileName( pNtk->pName, FileNameDot );
    // check that the file can be opened
    if ( (pFile = fopen( FileNameDot, "w" )) == NULL )
    {
        fprintf( stdout, "Cannot open the intermediate file \"%s\".\n", FileNameDot );
        return;
    }

    // collect all nodes in the network
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkForEachObj( pNtk, pNode, i )
        Vec_PtrPush( vNodes, pNode );
    // write the DOT file
    Io_WriteDot( pNtk, vNodes, NULL, FileNameDot );
    Vec_PtrFree( vNodes );

    // visualize the file 
    Abc_ShowFile( FileNameDot );
}

/**Function*************************************************************

  Synopsis    [Visualizes a reconvergence driven cut at the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeShowCut( Abc_Obj_t * pNode, int nNodeSizeMax, int nConeSizeMax )
{
    FILE * pFile;
    char FileNameDot[200];
    Abc_ManCut_t * p;
    Vec_Ptr_t * vCutSmall;
    Vec_Ptr_t * vCutLarge;
    Vec_Ptr_t * vInside;
    Vec_Ptr_t * vNodesTfo;
    Abc_Obj_t * pTemp;
    int i;

    assert( Abc_NtkIsStrash(pNode->pNtk) );

    // start the cut computation manager
    p = Abc_NtkManCutStart( nNodeSizeMax, nConeSizeMax, 2, ABC_INFINITY );
    // get the recovergence driven cut
    vCutSmall = Abc_NodeFindCut( p, pNode, 1 );
    // get the containing cut
    vCutLarge = Abc_NtkManCutReadCutLarge( p );
    // get the array for the inside nodes
    vInside = Abc_NtkManCutReadVisited( p );
    // get the inside nodes of the containing cone
    Abc_NodeConeCollect( &pNode, 1, vCutLarge, vInside, 1 );

    // add the nodes in the TFO 
    vNodesTfo = Abc_NodeCollectTfoCands( p, pNode, vCutSmall, ABC_INFINITY );
    Vec_PtrForEachEntry( vNodesTfo, pTemp, i )
        Vec_PtrPushUnique( vInside, pTemp );

    // create the file name
    Abc_ShowGetFileName( Abc_ObjName(pNode), FileNameDot );
    // check that the file can be opened
    if ( (pFile = fopen( FileNameDot, "w" )) == NULL )
    {
        fprintf( stdout, "Cannot open the intermediate file \"%s\".\n", FileNameDot );
        return;
    }
    // add the root node to the cone (for visualization)
    Vec_PtrPush( vCutSmall, pNode );
    // write the DOT file
    Io_WriteDot( pNode->pNtk, vInside, vCutSmall, FileNameDot );
    // stop the cut computation manager
    Abc_NtkManCutStop( p );

    // visualize the file 
    Abc_ShowFile( FileNameDot );
}


/**Function*************************************************************

  Synopsis    [Shows the given DOT file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ShowFile( char * FileNameDot )
{
    FILE * pFile;
    char * FileGeneric;
    char FileNamePs[200];
    char CommandDot[1000];
#ifndef WIN32
    char CommandPs[1000];
#endif
    char * pProgDotName;
    char * pProgGsViewName;
    int RetValue;

#ifdef WIN32
    pProgDotName = "dot.exe";
    pProgGsViewName = NULL;
#else
    pProgDotName = "dot";
    pProgGsViewName = "gv";
#endif

    // check that the input file is okay
    if ( (pFile = fopen( FileNameDot, "r" )) == NULL )
    {
        fprintf( stdout, "Cannot open the intermediate file \"%s\".\n", FileNameDot );
        return;
    }
    fclose( pFile );

    // get the generic file name
    FileGeneric = Extra_FileNameGeneric( FileNameDot );
    // create the PostScript file name
    sprintf( FileNamePs,  "%s.ps",  FileGeneric ); 
    free( FileGeneric );

    // generate the DOT file
    sprintf( CommandDot,  "%s -Tps -o %s %s", pProgDotName, FileNamePs, FileNameDot ); 
    RetValue = system( CommandDot );
#ifdef WIN32
        _unlink( FileNameDot );
#else
        unlink( FileNameDot );
#endif
    if ( RetValue == -1 )
    {
        fprintf( stdout, "Cannot find \"%s\".\n", pProgDotName );
        return;
    }

    // check that the input file is okay
    if ( (pFile = fopen( FileNamePs, "r" )) == NULL )
    {
        fprintf( stdout, "Cannot open intermediate file \"%s\".\n", FileNamePs );
        return;
    }
    fclose( pFile ); 

#ifdef WIN32
    if ( _spawnl( _P_NOWAIT, "gsview32.exe", "gsview32.exe", FileNamePs, NULL ) == -1 )
        if ( _spawnl( _P_NOWAIT, "C:\\Program Files\\Ghostgum\\gsview\\gsview32.exe", 
            "C:\\Program Files\\Ghostgum\\gsview\\gsview32.exe", FileNamePs, NULL ) == -1 )
        {
            fprintf( stdout, "Cannot find \"%s\".\n", "gsview32.exe" );
            return;
        }
#else
    sprintf( CommandPs,  "%s %s &", pProgGsViewName, FileNamePs ); 
    if ( system( CommandPs ) == -1 )
    {
        fprintf( stdout, "Cannot execute \"%s\".\n", FileNamePs );
        return;
    }
#endif
}

/**Function*************************************************************

  Synopsis    [Derives the DOT file name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ShowGetFileName( char * pName, char * pBuffer )
{
    char * pCur;
    // creat the file name
    sprintf( pBuffer, "%s.dot", pName );
    // get rid of not-alpha-numeric characters
    for ( pCur = pBuffer; *pCur; pCur++ )
        if ( !((*pCur >= '0' && *pCur <= '9') || (*pCur >= 'a' && *pCur <= 'z') || 
               (*pCur >= 'A' && *pCur <= 'Z') || (*pCur == '.')) )
            *pCur = '_';
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


