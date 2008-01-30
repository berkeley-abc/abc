/**CFile****************************************************************

  FileName    [decPrint.c]

  PackageName [MVSIS 2.0: Multi-valued logic synthesis system.]

  Synopsis    [Procedures to print the decomposition graphs (factored forms).]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - February 1, 2003.]

  Revision    [$Id: decPrint.c,v 1.1 2003/05/22 19:20:05 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "dec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void   Dec_GraphPrint_rec( FILE * pFile, Dec_Graph_t * pGraph, Dec_Node_t * pNode, int fCompl, char * pNamesIn[], int * pPos, int LitSizeMax );
static int    Dec_GraphPrintGetLeafName( FILE * pFile, int iLeaf, int fCompl, char * pNamesIn[] );
static void   Dec_GraphPrintUpdatePos( FILE * pFile, int * pPos, int LitSizeMax );
static int    Dec_GraphPrintOutputName( FILE * pFile, char * pNameOut, int fCompl );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prints the decomposition graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dec_GraphPrint( FILE * pFile, Dec_Graph_t * pGraph, char * pNamesIn[], char * pNameOut )
{
    Vec_Ptr_t * vNamesIn = NULL;
    int LitSizeMax, LitSizeCur, Pos, i;

    // create the names if not given by the user
    if ( pNamesIn == NULL )
    {
        vNamesIn = Abc_NodeGetFakeNames( Dec_GraphLeaveNum(pGraph) );
        pNamesIn = (char **)vNamesIn->pArray;
    }
    if ( pNameOut == NULL )
        pNameOut = "F";

    // get the size of the longest literal
    LitSizeMax = 0;
    for ( i = 0; i < Dec_GraphLeaveNum(pGraph); i++ )
    {
        LitSizeCur = strlen(pNamesIn[i]);
        if ( LitSizeMax < LitSizeCur )
            LitSizeMax = LitSizeCur;
    }
    if ( LitSizeMax > 50 )
        LitSizeMax = 20;

    // write the decomposition graph (factored form)
    if ( Dec_GraphIsConst(pGraph) ) // constant
    {
        Pos = Dec_GraphPrintOutputName( pFile, pNameOut, 0 );
        fprintf( pFile, "Constant %d", !Dec_GraphIsComplement(pGraph) );
    }
    else if ( Dec_GraphIsVar(pGraph) ) // literal
    {
        Pos = Dec_GraphPrintOutputName( pFile, pNameOut, 0 );
        Dec_GraphPrintGetLeafName( pFile, Dec_GraphVarInt(pGraph), Dec_GraphIsComplement(pGraph), pNamesIn );
    }
    else
    {
        Pos = Dec_GraphPrintOutputName( pFile, pNameOut, Dec_GraphIsComplement(pGraph) );
        Dec_GraphPrint_rec( pFile, pGraph, Dec_GraphNodeLast(pGraph), 0, pNamesIn, &Pos, LitSizeMax );
    }
    fprintf( pFile, "\n" );

    if ( vNamesIn )
        Abc_NodeFreeNames( vNamesIn );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dec_GraphPrint_rec( FILE * pFile, Dec_Graph_t * pGraph, Dec_Node_t * pNode, int fCompl, char * pNamesIn[], int * pPos, int LitSizeMax )
{
    Dec_Node_t * pNode0, * pNode1;
    pNode0 = Dec_GraphNode(pGraph, pNode->eEdge0.Node);
    pNode1 = Dec_GraphNode(pGraph, pNode->eEdge1.Node);
    if ( Dec_GraphNodeIsVar(pGraph, pNode) ) // FT_NODE_LEAF )
    {
        (*pPos) += Dec_GraphPrintGetLeafName( pFile, Dec_GraphNodeInt(pGraph,pNode), fCompl, pNamesIn );
        return;
    }
    if ( !pNode->fNodeOr ) // FT_NODE_AND )
    {
        if ( !pNode0->fNodeOr ) // != FT_NODE_OR )
            Dec_GraphPrint_rec( pFile, pGraph, pNode0, pNode->fCompl0, pNamesIn, pPos, LitSizeMax );
        else
        {
            fprintf( pFile, "(" );
            (*pPos)++;
            Dec_GraphPrint_rec( pFile, pGraph, pNode0, pNode->fCompl0, pNamesIn, pPos, LitSizeMax );
            fprintf( pFile, ")" );
            (*pPos)++;
        }
        fprintf( pFile, " " );
        (*pPos)++;

        Dec_GraphPrintUpdatePos( pFile, pPos, LitSizeMax );

        if ( !pNode1->fNodeOr ) // != FT_NODE_OR )
            Dec_GraphPrint_rec( pFile, pGraph, pNode1, pNode->fCompl1, pNamesIn, pPos, LitSizeMax );
        else
        {
            fprintf( pFile, "(" );
            (*pPos)++;
            Dec_GraphPrint_rec( pFile, pGraph, pNode1, pNode->fCompl1, pNamesIn, pPos, LitSizeMax );
            fprintf( pFile, ")" );
            (*pPos)++;
        }
        return;
    }
    if ( pNode->fNodeOr ) // FT_NODE_OR )
    {
        Dec_GraphPrint_rec( pFile, pGraph, pNode0, pNode->fCompl0, pNamesIn, pPos, LitSizeMax );
        fprintf( pFile, " + " );
        (*pPos) += 3;

        Dec_GraphPrintUpdatePos( pFile, pPos, LitSizeMax );

        Dec_GraphPrint_rec( pFile, pGraph, pNode1, pNode->fCompl1, pNamesIn, pPos, LitSizeMax );
        return;
    }
    assert( 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dec_GraphPrintGetLeafName( FILE * pFile, int iLeaf, int fCompl, char * pNamesIn[] )
{
    static char Buffer[100];
    sprintf( Buffer, "%s%s", pNamesIn[iLeaf], fCompl? "\'" : "" );
    fprintf( pFile, "%s", Buffer );
    return strlen( Buffer );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dec_GraphPrintUpdatePos( FILE * pFile, int * pPos, int LitSizeMax )
{
    int i;
    if ( *pPos + LitSizeMax < 77 )
        return;
    fprintf( pFile, "\n" );
    for ( i = 0; i < 10; i++ )
        fprintf( pFile, " " );
    *pPos = 10;
}

/**Function*************************************************************

  Synopsis    [Starts the printout for a decomposition graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dec_GraphPrintOutputName( FILE * pFile, char * pNameOut, int fCompl )
{
    if ( pNameOut == NULL )
        return 0;
    fprintf( pFile, "%6s%s = ", pNameOut, fCompl? "\'" : " " );
    return 10;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


