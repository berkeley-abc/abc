/**CFile****************************************************************

  FileName    [ifTune.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Library tuning.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifTune.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManStrCheck( char * pStr )
{
    int i, Marks[32] = {0}, MaxVar = 0, MaxDef = 0;
    for ( i = 0; pStr[i]; i++ )
    {
        if ( pStr[i] == '=' || pStr[i] == ';' || 
             pStr[i] == '(' || pStr[i] == ')' || 
             pStr[i] == '[' || pStr[i] == ']' || 
             pStr[i] == '<' || pStr[i] == '>' || 
             pStr[i] == '{' || pStr[i] == '}' )
            continue;
        if ( pStr[i] >= 'a' && pStr[i] <= 'z' )
        {
            if ( pStr[i+1] == '=' )
                Marks[pStr[i] - 'a'] = 2, MaxDef = 1 + Abc_MaxInt(MaxDef, pStr[i] - 'a');
            else
                Marks[pStr[i] - 'a'] = 1, MaxVar = 1 + Abc_MaxInt(MaxVar, pStr[i] - 'a');
            continue;
        }
        printf( "String \"%s\" contains unrecognized symbol (%c).\n", pStr, pStr[i] );
    }
    for ( i = 0; i < MaxDef; i++ )
        if ( Marks[i] == 0 )
            printf( "String \"%s\" has no symbol (%c).\n", pStr, 'a' + Marks[i] );
    for ( i = 0; i < MaxVar; i++ )
        if ( Marks[i] == 2 )
            printf( "String \"%s\" defined input symbol (%c).\n", pStr, 'a' + Marks[i] );
    for ( i = MaxVar; i < MaxDef; i++ )
        if ( Marks[i] == 1 )
            printf( "String \"%s\" has no definition for symbol (%c).\n", pStr, 'a' + Marks[i] );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver * If_ManSatBuild( char * pStr )
{
    sat_solver * pSat = NULL;

    return pSat;
}

/**Function*************************************************************

  Synopsis    [Test procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManSatTest()
{
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

