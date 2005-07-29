/**CFile****************************************************************

  FileName    [ftPrint.c]

  PackageName [MVSIS 2.0: Multi-valued logic synthesis system.]

  Synopsis    [Procedures to print the factored tree.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - February 1, 2003.]

  Revision    [$Id: ftPrint.c,v 1.1 2003/05/22 19:20:05 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void   Ft_FactorPrint_rec( FILE * pFile, Vec_Int_t * vForm, Ft_Node_t * pNode, int fCompl, char * pNamesIn[], int * pPos, int LitSizeMax );
static int    Ft_FactorPrintGetLeafName( FILE * pFile, Vec_Int_t * vForm, Ft_Node_t * pNode, int fCompl, char * pNamesIn[] );
static void   Ft_FactorPrintUpdatePos( FILE * pFile, int * pPos, int LitSizeMax );
static int    Ft_FactorPrintOutputName( FILE * pFile, char * pNameOut, int fCompl );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ft_FactorPrint( FILE * pFile, Vec_Int_t * vForm, char * pNamesIn[], char * pNameOut )
{
    Ft_Node_t * pNode;
    char Buffer[5];
    int Pos, i, LitSizeMax, LitSizeCur, nVars;
    int fMadeupNames;

    // sanity checks
    nVars = Ft_FactorGetNumVars( vForm );
    assert( nVars >= 0 );
    assert( vForm->nSize > nVars );

    // create the names if not given by the user
    fMadeupNames = 0;
    if ( pNamesIn == NULL )
    {
        fMadeupNames = 1;
        pNamesIn = ALLOC( char *, nVars );
        for ( i = 0; i < nVars; i++ )
        {
            if ( nVars < 26 )
            {
                Buffer[0] = 'a' + i;
                Buffer[1] = 0;
            }
            else
            {
                Buffer[0] = 'a' + i%26;
                Buffer[1] = '0' + i/26;
                Buffer[2] = 0;
            }
            pNamesIn[i] = util_strsav( Buffer );
        }
    }

    // get the size of the longest literal
    LitSizeMax = 0;
    for ( i = 0; i < nVars; i++ )
    {
        LitSizeCur = strlen(pNamesIn[i]);
        if ( LitSizeMax < LitSizeCur )
            LitSizeMax = LitSizeCur;
    }
    if ( LitSizeMax > 50 )
        LitSizeMax = 20;

    // print the output name
    pNode = Ft_NodeReadLast(vForm);
    if ( !pNode->fConst && pNode->iFanin0 == pNode->iFanin1 ) // literal
    {
        Pos = Ft_FactorPrintOutputName( pFile, pNameOut, 0 );
        Ft_FactorPrintGetLeafName( pFile, vForm, Ft_NodeFanin0(vForm,pNode), pNode->fCompl, pNamesIn );
    }
    else // constant or non-trivial form
    {
        Pos = Ft_FactorPrintOutputName( pFile, pNameOut, pNode->fCompl );
        Ft_FactorPrint_rec( pFile, vForm, pNode, 0, pNamesIn, &Pos, LitSizeMax );
    }
    fprintf( pFile, "\n" );

    if ( fMadeupNames )
    {
        for ( i = 0; i < nVars; i++ )
            free( pNamesIn[i] );
        free( pNamesIn );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ft_FactorPrint_rec( FILE * pFile, Vec_Int_t * vForm, Ft_Node_t * pNode, int fCompl, char * pNamesIn[], int * pPos, int LitSizeMax )
{
    Ft_Node_t * pNode0, * pNode1;

    if ( pNode->fConst ) // FT_NODE_0 )
    {
        if ( fCompl )
            fprintf( pFile, "Constant 0" );
        else
            fprintf( pFile, "Constant 1" );
        return;
    }
    if ( !pNode->fIntern ) // FT_NODE_LEAF )
    {
        (*pPos) += Ft_FactorPrintGetLeafName( pFile, vForm, pNode, fCompl, pNamesIn );
        return;
    }

    pNode0 = Ft_NodeFanin0( vForm, pNode );
    pNode1 = Ft_NodeFanin1( vForm, pNode );
    if ( !pNode->fNodeOr ) // FT_NODE_AND )
    {
        if ( !pNode0->fNodeOr ) // != FT_NODE_OR )
            Ft_FactorPrint_rec( pFile, vForm, pNode0, pNode->fEdge0, pNamesIn, pPos, LitSizeMax );
        else
        {
            fprintf( pFile, "(" );
            (*pPos)++;
            Ft_FactorPrint_rec( pFile, vForm, pNode0, pNode->fEdge0, pNamesIn, pPos, LitSizeMax );
            fprintf( pFile, ")" );
            (*pPos)++;
        }
        fprintf( pFile, " " );
        (*pPos)++;

        Ft_FactorPrintUpdatePos( pFile, pPos, LitSizeMax );

        if ( !pNode1->fNodeOr ) // != FT_NODE_OR )
            Ft_FactorPrint_rec( pFile, vForm, pNode1, pNode->fEdge1, pNamesIn, pPos, LitSizeMax );
        else
        {
            fprintf( pFile, "(" );
            (*pPos)++;
            Ft_FactorPrint_rec( pFile, vForm, pNode1, pNode->fEdge1, pNamesIn, pPos, LitSizeMax );
            fprintf( pFile, ")" );
            (*pPos)++;
        }
        return;
    }
    if ( pNode->fNodeOr ) // FT_NODE_OR )
    {
        Ft_FactorPrint_rec( pFile, vForm, pNode0, pNode->fEdge0, pNamesIn, pPos, LitSizeMax );
        fprintf( pFile, " + " );
        (*pPos) += 3;

        Ft_FactorPrintUpdatePos( pFile, pPos, LitSizeMax );

        Ft_FactorPrint_rec( pFile, vForm, pNode1, pNode->fEdge1, pNamesIn, pPos, LitSizeMax );
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
int Ft_FactorPrintGetLeafName( FILE * pFile, Vec_Int_t * vForm, Ft_Node_t * pNode, int fCompl, char * pNamesIn[] )
{
    static char Buffer[100];
    int iVar;
    assert( !Ptr_IsComplement(pNode) );
    iVar = (Ft_Node_t *)pNode - (Ft_Node_t *)vForm->pArray;
    sprintf( Buffer, "%s%s", pNamesIn[iVar], fCompl? "\'" : "" );
    fprintf( pFile, "%s", Buffer );
    return strlen( Buffer );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ft_FactorPrintUpdatePos( FILE * pFile, int * pPos, int LitSizeMax )
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

  Synopsis    [Starts the printout for a factored form or cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ft_FactorPrintOutputName( FILE * pFile, char * pNameOut, int fCompl )
{
    if ( pNameOut == NULL )
        return 0;
    fprintf( pFile, "%6s%s = ", pNameOut, fCompl? "\'" : " " );
    return 10;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


