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

// network types
typedef enum { 
    IF_DSD_NONE = 0,               // 0:  unknown
    IF_DSD_CONST0,                 // 1:  constant
    IF_DSD_VAR,                    // 2:  variable
    IF_DSD_AND,                    // 3:  AND
    IF_DSD_XOR,                    // 4:  XOR
    IF_DSD_MUX,                    // 5:  MUX
    IF_DSD_PRIME                   // 6:  PRIME
} If_DsdType_t;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManStrCheck( char * pStr, int * pnVars, int * pnObjs )
{
    int i, Marks[32] = {0}, MaxVar = 0, MaxDef = 0, RetValue = 1;
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
        RetValue = 0;
    }
    for ( i = 0; i < MaxDef; i++ )
        if ( Marks[i] == 0 )
            printf( "String \"%s\" has no symbol (%c).\n", pStr, 'a' + Marks[i] ), RetValue = 0;
    for ( i = 0; i < MaxVar; i++ )
        if ( Marks[i] == 2 )
            printf( "String \"%s\" has definition of input variable (%c).\n", pStr, 'a' + Marks[i] ), RetValue = 0;
    for ( i = MaxVar; i < MaxDef; i++ )
        if ( Marks[i] == 1 )
            printf( "String \"%s\" has no definition for internal variable (%c).\n", pStr, 'a' + Marks[i] ), RetValue = 0;
    *pnVars = RetValue ? MaxVar : 0;
    *pnObjs = RetValue ? MaxDef : 0;
    return RetValue;
}
int If_ManStrParse( char * pStr, int nVars, int nObjs, int * pTypes, int * pnFans, int ppFans[][6] )
{
    int i, k, n, f;
    char Next = 0;
    assert( nVars < nObjs );
    for ( i = nVars; i < nObjs; i++ )
    {
        for ( k = 0; pStr[k]; k++ )
            if ( pStr[k] == 'a' + i && pStr[k+1] == '=' )
                break;
        assert( pStr[k] );
        if ( pStr[k+2] == '(' )
            pTypes[i] = IF_DSD_AND, Next = ')';
        else if ( pStr[k+2] == '[' )
            pTypes[i] = IF_DSD_XOR, Next = ']';
        else if ( pStr[k+2] == '<' )
            pTypes[i] = IF_DSD_MUX, Next = '>';
        else if ( pStr[k+2] == '{' )
            pTypes[i] = IF_DSD_PRIME, Next = '}';
        else assert( 0 );
        for ( n = k + 3; pStr[n]; n++ )
            if ( pStr[n] == Next )
                break;
        assert( pStr[k] );
        pnFans[i] = n - k - 3;
        assert( pnFans[i] > 0 && pnFans[i] <= 6 );
        for ( f = 0; f < pnFans[i]; f++ )
        {
            ppFans[i][f] = pStr[k + 3 + f] - 'a';
            if ( ppFans[i][f] < 0 || ppFans[i][f] >= nObjs )
                printf( "Error!\n" );
        }
    }
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
    int nVars, nObjs;
    int pTypes[32] = {0};
    int pnFans[32] = {0};
    int ppFans[32][6] = {{0}};
    sat_solver * pSat = NULL;
    if ( !If_ManStrCheck(pStr, &nVars, &nObjs) )
        return NULL;
    if ( !If_ManStrParse(pStr, nVars, nObjs, pTypes, pnFans, ppFans) )
        return NULL;
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

