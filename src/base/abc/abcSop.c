/**CFile****************************************************************

  FileName    [abcSop.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Implementation of a simple SOP representation of nodes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcSop.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

/* 
    The SOPs in this package are represented using char * strings.
    For example, the SOP of the node: 

       .names c d0 d1 MUX
       01- 1
       1-1 1

    is the string: "01- 1/n1-1 1/n" where '/n' is a single char.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Registers the cube string with the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopRegister( Extra_MmFlex_t * pMan, char * pName )
{
    char * pRegName;
    if ( pName == NULL ) return NULL;
    pRegName = Extra_MmFlexEntryFetch( pMan, strlen(pName) + 1 );
    strcpy( pRegName, pName );
    return pRegName;
}

/**Function*************************************************************

  Synopsis    [Starts the constant 1 cover with the given number of variables and cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopStart( Extra_MmFlex_t * pMan, int nCubes, int nVars )
{
    char * pSopCover, * pCube;
    int i, Length;

    Length = nCubes * (nVars + 3);
    pSopCover = Extra_MmFlexEntryFetch( pMan, Length + 1 );
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

  Synopsis    [Starts the constant 1 cover with 0 variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateConst1( Extra_MmFlex_t * pMan )
{
    return Abc_SopRegister( pMan, " 1\n" );
}

/**Function*************************************************************

  Synopsis    [Starts the constant 1 cover with 0 variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateConst0( Extra_MmFlex_t * pMan )
{
    return Abc_SopRegister( pMan, " 0\n" );
}

/**Function*************************************************************

  Synopsis    [Starts the AND2 cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateAnd2( Extra_MmFlex_t * pMan, int fCompl0, int fCompl1 )
{
    char Buffer[6];
    Buffer[0] = '1' - fCompl0;
    Buffer[1] = '1' - fCompl1;
    Buffer[2] = ' ';
    Buffer[3] = '1';
    Buffer[4] = '\n';
    Buffer[5] = 0;
    return Abc_SopRegister( pMan, Buffer );
}

/**Function*************************************************************

  Synopsis    [Starts the multi-input AND cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateAnd( Extra_MmFlex_t * pMan, int nVars )
{
    char * pSop;
    int i;
    pSop = Abc_SopStart( pMan, 1, nVars );
    for ( i = 0; i < nVars; i++ )
        pSop[i] = '1';
    return pSop;
}

/**Function*************************************************************

  Synopsis    [Starts the multi-input NAND cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateNand( Extra_MmFlex_t * pMan, int nVars )
{
    char * pSop;
    int i;
    pSop = Abc_SopStart( pMan, 1, nVars );
    for ( i = 0; i < nVars; i++ )
        pSop[i] = '1';
    pSop[nVars + 1] = '0';
    return pSop;
}

/**Function*************************************************************

  Synopsis    [Starts the multi-input OR cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateOr( Extra_MmFlex_t * pMan, int nVars, int * pfCompl )
{
    char * pSop;
    int i;
    pSop = Abc_SopStart( pMan, 1, nVars );
    for ( i = 0; i < nVars; i++ )
        pSop[i] = '0' + (pfCompl? pfCompl[i] : 0);
    pSop[nVars + 1] = '0';
    return pSop;
}

/**Function*************************************************************

  Synopsis    [Starts the multi-input OR cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateOrMultiCube( Extra_MmFlex_t * pMan, int nVars, int * pfCompl )
{
    char * pSop, * pCube;
    int i;
    pSop = Abc_SopStart( pMan, nVars, nVars );
    i = 0;
    Abc_SopForEachCube( pSop, nVars, pCube )
    {
        pCube[i] = '1' - (pfCompl? pfCompl[i] : 0);
        i++;
    }
    return pSop;
}

/**Function*************************************************************

  Synopsis    [Starts the multi-input NOR cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateNor( Extra_MmFlex_t * pMan, int nVars )
{
    char * pSop;
    int i;
    pSop = Abc_SopStart( pMan, 1, nVars );
    for ( i = 0; i < nVars; i++ )
        pSop[i] = '0';
    return pSop;
}

/**Function*************************************************************

  Synopsis    [Starts the multi-input XOR cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateXor( Extra_MmFlex_t * pMan, int nVars )
{
    assert( nVars == 2 );
    return Abc_SopRegister(pMan, "01 1\n10 1\n");
}

/**Function*************************************************************

  Synopsis    [Starts the multi-input XNOR cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateNxor( Extra_MmFlex_t * pMan, int nVars )
{
    assert( nVars == 2 );
    return Abc_SopRegister(pMan, "11 1\n11 1\n");
}

/**Function*************************************************************

  Synopsis    [Starts the inv cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateInv( Extra_MmFlex_t * pMan )
{
    return Abc_SopRegister(pMan, "0 1\n");
}

/**Function*************************************************************

  Synopsis    [Starts the buf cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SopCreateBuf( Extra_MmFlex_t * pMan )
{
    return Abc_SopRegister(pMan, "1 1\n");
}


/**Function*************************************************************

  Synopsis    [Reads the number of cubes in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SopGetCubeNum( char * pSop )
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

  Synopsis    [Reads the number of SOP literals in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SopGetLitNum( char * pSop )
{
    char * pCur;
    int nLits = 0;
    if ( pSop == NULL )
        return 0;
    for ( pCur = pSop; *pCur; pCur++ )
    {
        nLits  -= (*pCur == '\n');
        nLits  += (*pCur == '0' || *pCur == '1');
    }
    return nLits;
}

/**Function*************************************************************

  Synopsis    [Reads the number of variables in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SopGetVarNum( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur != '\n'; pCur++ );
    return pCur - pSop - 2;
}

/**Function*************************************************************

  Synopsis    [Reads the phase of the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SopGetPhase( char * pSop )
{
    int nVars = Abc_SopGetVarNum( pSop );
    if ( pSop[nVars+1] == '0' )
        return 0;
    if ( pSop[nVars+1] == '1' )
        return 1;
    assert( 0 );
    return -1;
}

/**Function*************************************************************

  Synopsis    [Returns the i-th literal of the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SopGetIthCareLit( char * pSop, int i )
{
    char * pCube;
    int nVars;
    nVars = Abc_SopGetVarNum( pSop );
    Abc_SopForEachCube( pSop, nVars, pCube )
        if ( pCube[i] != '-' )
            return pCube[i] - '0';
    return -1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SopComplement( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur; pCur++ )
        if ( *pCur == '\n' )
        {
            if ( *(pCur - 1) == '0' )
                *(pCur - 1) = '1';
            else if ( *(pCur - 1) == '1' )
                *(pCur - 1) = '0';
            else
                assert( 0 );
        }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_SopIsComplement( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur; pCur++ )
        if ( *pCur == '\n' )
            return (int)(*(pCur - 1) == '0');
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks if the cover is constant 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_SopIsConst0( char * pSop )
{
    return pSop[0] == ' ' && pSop[1] == '0';
}

/**Function*************************************************************

  Synopsis    [Checks if the cover is constant 1.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_SopIsConst1( char * pSop )
{
    return pSop[0] == ' ' && pSop[1] == '1';
}

/**Function*************************************************************

  Synopsis    [Checks if the cover is constant 1.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_SopIsBuf( char * pSop )
{
    if ( pSop[4] != 0 )
        return 0;
    if ( (pSop[0] == '1' && pSop[2] == '1') || (pSop[0] == '0' && pSop[2] == '0') )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks if the cover is constant 1.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_SopIsInv( char * pSop )
{
    if ( pSop[4] != 0 )
        return 0;
    if ( (pSop[0] == '0' && pSop[2] == '1') || (pSop[0] == '1' && pSop[2] == '0') )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks if the cover is AND with possibly complemented inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_SopIsAndType( char * pSop )
{
    char * pCur;
    if ( Abc_SopGetCubeNum(pSop) != 1 )
        return 0;
    for ( pCur = pSop; *pCur != ' '; pCur++ )
        if ( *pCur == '-' )
            return 0;
    if ( pCur[1] != '1' )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks if the cover is OR with possibly complemented inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_SopIsOrType( char * pSop )
{
    char * pCube, * pCur;
    int nVars, nLits;
    nVars = Abc_SopGetVarNum( pSop );
    if ( nVars != Abc_SopGetCubeNum(pSop) )
        return 0;
    Abc_SopForEachCube( pSop, nVars, pCube )
    {
        // count the number of literals in the cube
        nLits = 0;
        for ( pCur = pCube; *pCur != ' '; pCur++ )
            nLits += ( *pCur != '-' );
        if ( nLits != 1 )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_SopCheck( char * pSop, int nFanins )
{
    char * pCubes, * pCubesOld;
    int fFound0 = 0, fFound1 = 0;

    // check the logic function of the node
    for ( pCubes = pSop; *pCubes; pCubes++ )
    {
        // get the end of the next cube
        for ( pCubesOld = pCubes; *pCubes != ' '; pCubes++ );
        // compare the distance
        if ( pCubes - pCubesOld != nFanins )
        {
            fprintf( stdout, "Abc_SopCheck: SOP has a mismatch between its cover and its fanins.\n" );
            return 0;
        }
        // check the output values for this cube
        pCubes++;
        if ( *pCubes == '0' )
            fFound0 = 1;
        else if ( *pCubes == '1' )
            fFound1 = 1;
        else
        {
            fprintf( stdout, "Abc_SopCheck: SOP has a strange character in the output part of its cube.\n" );
            return 0;
        }
        // check the last symbol (new line)
        pCubes++;
        if ( *pCubes != '\n' )
        {
            fprintf( stdout, "Abc_SopCheck: SOP has a cube without new line in the end.\n" );
            return 0;
        }
    }
    if ( fFound0 && fFound1 )
    {
        fprintf( stdout, "Abc_SopCheck: SOP has cubes in both phases.\n" );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Writes the CNF of the SOP into file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SopWriteCnf( FILE * pFile, char * pClauses, Vec_Int_t * vVars )
{
    char * pChar;
    int i;
    // check the logic function of the node
    for ( pChar = pClauses; *pChar; pChar++ )
    {
        // write the clause
        for ( i = 0; i < vVars->nSize; i++, pChar++ )
            if ( *pChar == '0' )
                fprintf( pFile, "%d ", vVars->pArray[i] );
            else if ( *pChar == '1' )
                fprintf( pFile, "%d ", -vVars->pArray[i] );
        fprintf( pFile, "0\n" );
        // check that the remainig part is fine
        assert( *pChar == ' ' );
        pChar++;
        assert( *pChar == '1' );
        pChar++;
        assert( *pChar == '\n' );
    }
}

/**Function*************************************************************

  Synopsis    [Adds the clauses of for the CNF to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SopAddCnfToSolver( solver * pSat, char * pClauses, Vec_Int_t * vVars, Vec_Int_t * vTemp )
{
    char * pChar;
    int i, RetValue;
    // check the logic function of the node
    for ( pChar = pClauses; *pChar; pChar++ )
    {
        // add the clause
        vTemp->nSize = 0;
        for ( i = 0; i < vVars->nSize; i++, pChar++ )
            if ( *pChar == '0' )
                Vec_IntPush( vTemp, toLit(vVars->pArray[i]) );
            else if ( *pChar == '1' )
                Vec_IntPush( vTemp, neg(toLit(vVars->pArray[i])) );
        // add the clause to the solver
        RetValue = solver_addclause( pSat, vTemp->pArray, vTemp->pArray + vTemp->nSize );
        assert( RetValue != 1 );
        // check that the remainig part is fine
        assert( *pChar == ' ' );
        pChar++;
        assert( *pChar == '1' );
        pChar++;
        assert( *pChar == '\n' );
    }
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


