/**CFile****************************************************************

  FileName    [fpgaLib.c]

  PackageName [MVSIS 1.3: Multi-valued logic synthesis system.]

  Synopsis    [Technology mapping for variable-size-LUT FPGAs.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 2.0. Started - August 18, 2004.]

  Revision    [$Id: fpgaLib.c,v 1.4 2005/01/23 06:59:41 alanmi Exp $]

***********************************************************************/

#include "fpgaInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads the description of LUTs from the LUT library file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fpga_LutLib_t * Fpga_LutLibCreate( char * FileName, int fVerbose )
{
    char pBuffer[1000], * pToken;
    Fpga_LutLib_t * p;
    FILE * pFile;
    int i;

    pFile = fopen( FileName, "r" );
    if ( pFile == NULL )
    {
        printf( "Cannot open LUT library file \"%s\".\n", FileName );
        return NULL;
    }

    p = ALLOC( Fpga_LutLib_t, 1 );
    memset( p, 0, sizeof(Fpga_LutLib_t) );
    p->pName = util_strsav( FileName );

    i = 1;
    while ( fgets( pBuffer, 1000, pFile ) != NULL )
    {
        pToken = strtok( pBuffer, " \t\n" );
        if ( pToken == NULL )
            continue;
        if ( pToken[0] == '#' )
            continue;
        if ( i != atoi(pToken) )
        {
            printf( "Error in the LUT library file \"%s\".\n", FileName );
            free( p );
            return NULL;
        }

        pToken = strtok( NULL, " \t\n" );
        p->pLutAreas[i] = (float)atof(pToken);

        pToken = strtok( NULL, " \t\n" );
        p->pLutDelays[i] = (float)atof(pToken);

        if ( i == FPGA_MAX_LUTSIZE )
        {
            printf( "Skipping LUTs of size more than %d.\n", i );
            break;
        }
        i++;
    }
    p->LutMax = i-1;
    if ( p->LutMax > FPGA_MAX_LEAVES )
    {
        p->LutMax = FPGA_MAX_LEAVES;
        printf( "Warning: LUTs with more than %d input will not be used.\n", FPGA_MAX_LEAVES );
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicates the LUT library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fpga_LutLib_t * Fpga_LutLibDup( Fpga_LutLib_t * p )
{
    Fpga_LutLib_t * pNew;
    pNew = ALLOC( Fpga_LutLib_t, 1 );
    *pNew = *p;
    pNew->pName = util_strsav( pNew->pName );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Frees the LUT library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fpga_LutLibFree( Fpga_LutLib_t * pLutLib )
{
    if ( pLutLib == NULL )
        return;
    FREE( pLutLib->pName );
    FREE( pLutLib );
}


/**Function*************************************************************

  Synopsis    [Prints the LUT library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fpga_LutLibPrint( Fpga_LutLib_t * pLutLib )
{
    int i;
    printf( "# The area/delay of k-variable LUTs:\n" );
    printf( "# k    area     delay\n" );
    for ( i = 1; i <= pLutLib->LutMax; i++ )
        printf( "%d   %7.2f   %7.2f\n", i, pLutLib->pLutAreas[i], pLutLib->pLutDelays[i] );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the delays are discrete.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fpga_LutLibDelaysAreDiscrete( Fpga_LutLib_t * pLutLib )
{
    float Delay;
    int i;
    for ( i = 1; i <= pLutLib->LutMax; i++ )
    {
        Delay = pLutLib->pLutDelays[i];
        if ( ((float)((int)Delay)) != Delay )
            return 0;
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


