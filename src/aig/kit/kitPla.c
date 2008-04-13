/**CFile****************************************************************

  FileName    [kitPla.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Computation kit.]

  Synopsis    [Manipulating SOP in the form of a C-string.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Dec 6, 2006.]

  Revision    [$Id: kitPla.c,v 1.00 2006/12/06 00:00:00 alanmi Exp $]

***********************************************************************/

#include "kit.h"
#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks if the cover is constant 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Kit_PlaIsConst0( char * pSop )
{
    return pSop[0] == ' ' && pSop[1] == '0';
}

/**Function*************************************************************

  Synopsis    [Reads the number of variables in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Kit_PlaGetVarNum( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur != '\n'; pCur++ );
    return pCur - pSop - 2;
}

/**Function*************************************************************

  Synopsis    [Reads the number of cubes in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Kit_PlaGetCubeNum( char * pSop )
{
    char * pCur;
    int nCubes = 0;
    if ( pSop == NULL )
        return 0;
    for ( pCur = pSop; *pCur; pCur++ )
        nCubes += (*pCur == '\n');
    return nCubes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Kit_PlaIsComplement( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur; pCur++ )
        if ( *pCur == '\n' )
            return (int)(*(pCur - 1) == '0' || *(pCur - 1) == 'n');
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_PlaComplement( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur; pCur++ )
        if ( *pCur == '\n' )
        {
            if ( *(pCur - 1) == '0' )
                *(pCur - 1) = '1';
            else if ( *(pCur - 1) == '1' )
                *(pCur - 1) = '0';
            else if ( *(pCur - 1) == 'x' )
                *(pCur - 1) = 'n';
            else if ( *(pCur - 1) == 'n' )
                *(pCur - 1) = 'x';
            else
                assert( 0 );
        }
}

/**Function*************************************************************

  Synopsis    [Creates the constant 1 cover with the given number of variables and cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Kit_PlaStart( void * p, int nCubes, int nVars )
{
    Aig_MmFlex_t * pMan = p;
    char * pSopCover, * pCube;
    int i, Length;

    Length = nCubes * (nVars + 3);
    pSopCover = Aig_MmFlexEntryFetch( pMan, Length + 1 );
    memset( pSopCover, '-', Length );
    pSopCover[Length] = 0;

    for ( i = 0; i < nCubes; i++ )
    {
        pCube = pSopCover + i * (nVars + 3);
        pCube[nVars + 0] = ' ';
        pCube[nVars + 1] = '1';
        pCube[nVars + 2] = '\n';
    }
    return pSopCover;
}

/**Function*************************************************************

  Synopsis    [Creates the cover from the ISOP computed from TT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Kit_PlaCreateFromIsop( void * p, int nVars, Vec_Int_t * vCover )
{
    Aig_MmFlex_t * pMan = p;
    char * pSop, * pCube;
    int i, k, Entry, Literal;
    assert( Vec_IntSize(vCover) > 0 );
    if ( Vec_IntSize(vCover) == 0 )
        return NULL;
    // start the cover
    pSop = Kit_PlaStart( pMan, Vec_IntSize(vCover), nVars );
    // create cubes
    Vec_IntForEachEntry( vCover, Entry, i )
    {
        pCube = pSop + i * (nVars + 3);
        for ( k = 0; k < nVars; k++ )
        {
            Literal = 3 & (Entry >> (k << 1));
            if ( Literal == 1 )
                pCube[k] = '0';
            else if ( Literal == 2 )
                pCube[k] = '1';
            else if ( Literal != 0 )
                assert( 0 );
        }
    }
    return pSop;
}

/**Function*************************************************************

  Synopsis    [Creates the cover from the ISOP computed from TT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_PlaToIsop( char * pSop, Vec_Int_t * vCover )
{
    char * pCube;
    int k, nVars, Entry;
    nVars = Kit_PlaGetVarNum( pSop );
    assert( nVars > 0 );
    // create cubes
    Vec_IntClear( vCover );
    for ( pCube = pSop; *pCube; pCube += nVars + 3 )
    {
        Entry = 0;
        for ( k = nVars - 1; k >= 0; k-- )
            if ( pCube[k] == '0' )
                Entry = (Entry << 2) | 1;
            else if ( pCube[k] == '1' )
                Entry = (Entry << 2) | 2;
            else if ( pCube[k] == '-' )
                Entry = (Entry << 2);
            else 
                assert( 0 );
        Vec_IntPush( vCover, Entry );
    }
}

/**Function*************************************************************

  Synopsis    [Allocates memory and copies the SOP into it.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Kit_PlaStoreSop( void * p, char * pSop )
{
    Aig_MmFlex_t * pMan = p;
    char * pStore;
    pStore = Aig_MmFlexEntryFetch( pMan, strlen(pSop) + 1 );
    strcpy( pStore, pSop );
    return pStore;
}

/**Function*************************************************************

  Synopsis    [Transforms truth table into the SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Kit_PlaFromTruth( void * p, unsigned * pTruth, int nVars, Vec_Int_t * vCover )
{
    Aig_MmFlex_t * pMan = p;
    char * pSop;
    int RetValue;
    if ( Kit_TruthIsConst0(pTruth, nVars) )
        return Kit_PlaStoreSop( pMan, " 0\n" );
    if ( Kit_TruthIsConst1(pTruth, nVars) )
        return Kit_PlaStoreSop( pMan, " 1\n" );
    RetValue = Kit_TruthIsop( pTruth, nVars, vCover, 0 ); // 1 );
    assert( RetValue == 0 || RetValue == 1 );
    pSop = Kit_PlaCreateFromIsop( pMan, nVars, vCover );
    if ( RetValue )
        Kit_PlaComplement( pSop );
    return pSop;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


