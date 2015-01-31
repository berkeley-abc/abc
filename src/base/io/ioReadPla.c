/**CFile****************************************************************

  FileName    [ioReadPla.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedure to read network from file.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioReadPla.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ioAbc.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t * Io_ReadPlaNetwork( Extra_FileReader_t * p, int fZeros );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_ReadPlaMarkIdentical( word ** pCs, int nCubes, int nWords, Vec_Bit_t * vMarks )
{
    int c1, c2;
    Vec_BitFill( vMarks, nCubes, 0 );
    for ( c1 = 0; c1 < nCubes; c1++ )
        if ( !Vec_BitEntry(vMarks, c1) )
            for ( c2 = c1 + 1; c2 < nCubes; c2++ )
                if ( !Vec_BitEntry(vMarks, c2) )
                    if ( Abc_TtEqual(pCs[c1], pCs[c2], nWords) )
                        Vec_BitWriteEntry( vMarks, c2, 1 );
}
void Io_ReadPlaMarkContained( word ** pCs, int nCubes, int nWords, Vec_Bit_t * vMarks )
{
    int c1, c2;
    Vec_BitFill( vMarks, nCubes, 0 );
    for ( c1 = 0; c1 < nCubes; c1++ )
        if ( !Vec_BitEntry(vMarks, c1) )
            for ( c2 = c1 + 1; c2 < nCubes; c2++ )
                if ( !Vec_BitEntry(vMarks, c2) )
                {
                    if ( Abc_TtImply(pCs[c1], pCs[c2], nWords) )
                        Vec_BitWriteEntry( vMarks, c2, 1 );
                    else if ( Abc_TtImply(pCs[c2], pCs[c1], nWords) )
                    {
                        Vec_BitWriteEntry( vMarks, c1, 1 );
                        break;
                    }
                }
}
int Io_ReadPlaRemoveMarked( word ** pCs, int nCubes, int nWords, Vec_Bit_t * vMarks )
{
    int c1, c;
    for ( c1 = c = 0; c1 < nCubes; c1++ )
        if ( !Vec_BitEntry(vMarks, c1) )
        {
            if ( c == c1 )
                c++;
            else
                Abc_TtCopy( pCs[c++], pCs[c1], nWords, 0 );
        }
    return c;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word ** Io_ReadPlaCubeSetup( Vec_Str_t * vSop )
{
    char * pSop = Vec_StrArray( vSop ), * pCube, Lit;
    int nCubes  = Abc_SopGetCubeNum( pSop );
    int nVars   = Abc_SopGetVarNum( pSop );
    int nWords  = Abc_Bit6WordNum( 2*nVars ), c, v;
    word ** pCs = ABC_ALLOC( word *, nCubes );
    pCs[0] = ABC_CALLOC( word, nCubes * nWords );
    for ( c = 1; c < nCubes; c++ )
        pCs[c] = pCs[c-1] + nWords;
    c = 0;
    Abc_SopForEachCube( pSop, nVars, pCube )
    {
        Abc_CubeForEachVar( pCube, Lit, v )
            if ( Lit == '0' )
                Abc_TtSetBit( pCs[c], Abc_Var2Lit(v,0) );
            else if ( Lit == '1' )
                Abc_TtSetBit( pCs[c], Abc_Var2Lit(v,1) );
        c++;
    }
    assert( c == nCubes );
    return pCs;
}
void Io_ReadPlaCubeSetdown( Vec_Str_t * vSop, word ** pCs, int nCubes, int nVars )
{
    char Symbs[3] = {'-', '0', '1'};
    int c, v, Lit;
    Vec_StrClear( vSop );
    for ( c = 0; c < nCubes; c++ )
    {
        for ( v = 0; v < nVars && ((Lit = Abc_TtGetQua(pCs[c], v)), 1); v++ )
        {
            assert( Lit < 3 );
            Vec_StrPush( vSop, Symbs[Lit] );
        }
        Vec_StrPrintStr( vSop, " 1\n" );
    }
    Vec_StrPush( vSop, 0 );
}
void Io_ReadPlaCubePreprocess( Vec_Str_t * vSop, int iCover, int fVerbose )
{
    word ** pCs = Io_ReadPlaCubeSetup( vSop );
    int nCubes  = Abc_SopGetCubeNum( Vec_StrArray(vSop) );
    int nVars   = Abc_SopGetVarNum( Vec_StrArray(vSop) );
    int nWords  = Abc_Bit6WordNum( 2*nVars ), nCubesNew;
    Vec_Bit_t * vMarks = Vec_BitStart( nCubes );
    if ( fVerbose )
        printf( "Cover %5d : V =%5d  C =%5d  P =%9d ", iCover, nVars, nCubes, nCubes*nCubes/2 );
    // check identical
    Io_ReadPlaMarkIdentical( pCs, nCubes, nWords, vMarks );
    nCubesNew = Io_ReadPlaRemoveMarked( pCs, nCubes, nWords, vMarks );
    if ( fVerbose )
        printf( "  Equal =%5d", nCubes - nCubesNew );
    nCubes = nCubesNew;
    // check contained
    Io_ReadPlaMarkContained( pCs, nCubes, nWords, vMarks );
    nCubesNew = Io_ReadPlaRemoveMarked( pCs, nCubes, nWords, vMarks );
    if ( fVerbose )
        printf( "  Contain =%5d", nCubes - nCubesNew );
    nCubes = nCubesNew;
    // check distance-1

    // translate
    Io_ReadPlaCubeSetdown( vSop, pCs, nCubes, nVars );
    // finalize
    if ( fVerbose )
        printf( "\n" );
    Vec_BitFree( vMarks );
    ABC_FREE( pCs[0] );
    ABC_FREE( pCs );
}

/**Function*************************************************************

  Synopsis    [Reads the network from a PLA file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadPla( char * pFileName, int fZeros, int fCheck )
{
    Extra_FileReader_t * p;
    Abc_Ntk_t * pNtk;

    // start the file
    p = Extra_FileReaderAlloc( pFileName, "#", "\n\r", " \t|" );
//    p = Extra_FileReaderAlloc( pFileName, "", "\n\r", " \t|" );
    if ( p == NULL )
        return NULL;

    // read the network
    pNtk = Io_ReadPlaNetwork( p, fZeros );
    Extra_FileReaderFree( p );
    if ( pNtk == NULL )
        return NULL;

    // make sure that everything is okay with the network structure
    if ( fCheck && !Abc_NtkCheckRead( pNtk ) )
    {
        printf( "Io_ReadPla: The network check has failed.\n" );
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
Abc_Ntk_t * Io_ReadPlaNetwork( Extra_FileReader_t * p, int fZeros )
{
    ProgressBar * pProgress;
    Vec_Ptr_t * vTokens;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pTermPi, * pTermPo, * pNode;
    Vec_Str_t ** ppSops = NULL;
    char Buffer[100];
    int nInputs = -1, nOutputs = -1, nProducts = -1;
    char * pCubeIn, * pCubeOut;
    int i, k, iLine, nDigits, nCubes;

    // allocate the empty network
    pNtk = Abc_NtkStartRead( Extra_FileReaderGetFileName(p) );

    // go through the lines of the file
    nCubes = 0;
    pProgress = Extra_ProgressBarStart( stdout, Extra_FileReaderGetFileSize(p) );
    while ( (vTokens = (Vec_Ptr_t *)Extra_FileReaderGetTokens(p)) )
    {
        Extra_ProgressBarUpdate( pProgress, Extra_FileReaderGetCurPosition(p), NULL );
        iLine = Extra_FileReaderGetLineNumber( p, 0 );

        // if it is the end of file, quit the loop
        if ( strncmp( (char *)vTokens->pArray[0], ".e", 2 ) == 0 )
            break;

        // if it is the model name, get the name
        if ( strcmp( (char *)vTokens->pArray[0], ".model" ) == 0 )
        {
            ABC_FREE( pNtk->pName );
            pNtk->pName = Extra_UtilStrsav( (char *)vTokens->pArray[1] );
            continue;
        }

        if ( vTokens->nSize == 1 )
        {
            printf( "%s (line %d): Wrong number of token.\n", 
                Extra_FileReaderGetFileName(p), iLine );
            Abc_NtkDelete( pNtk );
            Extra_ProgressBarStop( pProgress );
            ABC_FREE( ppSops );
            return NULL;
        }

        if ( strcmp( (char *)vTokens->pArray[0], ".i" ) == 0 )
            nInputs = atoi((char *)vTokens->pArray[1]);
        else if ( strcmp( (char *)vTokens->pArray[0], ".o" ) == 0 )
            nOutputs = atoi((char *)vTokens->pArray[1]);
        else if ( strcmp( (char *)vTokens->pArray[0], ".p" ) == 0 )
            nProducts = atoi((char *)vTokens->pArray[1]);
        else if ( strcmp( (char *)vTokens->pArray[0], ".ilb" ) == 0 )
        {
            if ( vTokens->nSize - 1 != nInputs )
                printf( "Warning: Mismatch between the number of PIs on the .i line (%d) and the number of PIs on the .ilb line (%d).\n", nInputs, vTokens->nSize - 1 );
            for ( i = 1; i < vTokens->nSize; i++ )
                Io_ReadCreatePi( pNtk, (char *)vTokens->pArray[i] );
        }
        else if ( strcmp( (char *)vTokens->pArray[0], ".ob" ) == 0 )
        {
            if ( vTokens->nSize - 1 != nOutputs )
                printf( "Warning: Mismatch between the number of POs on the .o line (%d) and the number of POs on the .ob line (%d).\n", nOutputs, vTokens->nSize - 1 );
            for ( i = 1; i < vTokens->nSize; i++ )
                Io_ReadCreatePo( pNtk, (char *)vTokens->pArray[i] );
        }
        else 
        {
            // check if the input/output names are given
            if ( Abc_NtkPiNum(pNtk) == 0 )
            {
                if ( nInputs == -1 )
                {
                    printf( "%s: The number of inputs is not specified.\n", Extra_FileReaderGetFileName(p) );
                    Abc_NtkDelete( pNtk );
                    Extra_ProgressBarStop( pProgress );
                    ABC_FREE( ppSops );
                    return NULL;
                }
                nDigits = Abc_Base10Log( nInputs );
                for ( i = 0; i < nInputs; i++ )
                {
                    sprintf( Buffer, "x%0*d", nDigits, i );
                    Io_ReadCreatePi( pNtk, Buffer );
                }
            }
            if ( Abc_NtkPoNum(pNtk) == 0 )
            {
                if ( nOutputs == -1 )
                {
                    printf( "%s: The number of outputs is not specified.\n", Extra_FileReaderGetFileName(p) );
                    Abc_NtkDelete( pNtk );
                    Extra_ProgressBarStop( pProgress );
                    ABC_FREE( ppSops );
                    return NULL;
                }
                nDigits = Abc_Base10Log( nOutputs );
                for ( i = 0; i < nOutputs; i++ )
                {
                    sprintf( Buffer, "z%0*d", nDigits, i );
                    Io_ReadCreatePo( pNtk, Buffer );
                }
            }
            if ( Abc_NtkNodeNum(pNtk) == 0 )
            { // first time here
                // create the PO drivers and add them
                // start the SOP covers
                ppSops = ABC_ALLOC( Vec_Str_t *, nOutputs );
                Abc_NtkForEachPo( pNtk, pTermPo, i )
                {
                    ppSops[i] = Vec_StrAlloc( 100 );
                    // create the node
                    pNode = Abc_NtkCreateNode(pNtk);
                    // connect the node to the PO net
                    Abc_ObjAddFanin( Abc_ObjFanin0Ntk(pTermPo), pNode );
                    // connect the node to the PI nets
                    Abc_NtkForEachPi( pNtk, pTermPi, k )
                        Abc_ObjAddFanin( pNode, Abc_ObjFanout0Ntk(pTermPi) );
                }
            }
            // read the cubes
            if ( vTokens->nSize != 2 )
            {
                printf( "%s (line %d): Input and output cubes are not specified.\n", 
                    Extra_FileReaderGetFileName(p), iLine );
                Abc_NtkDelete( pNtk );
                Extra_ProgressBarStop( pProgress );
                ABC_FREE( ppSops );
                return NULL;
            }
            pCubeIn  = (char *)vTokens->pArray[0];
            pCubeOut = (char *)vTokens->pArray[1];
            if ( strlen(pCubeIn) != (unsigned)nInputs )
            {
                printf( "%s (line %d): Input cube length (%zu) differs from the number of inputs (%d).\n",
                    Extra_FileReaderGetFileName(p), iLine, strlen(pCubeIn), nInputs );
                Abc_NtkDelete( pNtk );
                return NULL;
            }
            if ( strlen(pCubeOut) != (unsigned)nOutputs )
            {
                printf( "%s (line %d): Output cube length (%zu) differs from the number of outputs (%d).\n",
                    Extra_FileReaderGetFileName(p), iLine, strlen(pCubeOut), nOutputs );
                Abc_NtkDelete( pNtk );
                Extra_ProgressBarStop( pProgress );
                ABC_FREE( ppSops );
                return NULL;
            }
            if ( fZeros )
            {
                for ( i = 0; i < nOutputs; i++ )
                {
                    if ( pCubeOut[i] == '0' )
                    {
                        Vec_StrPrintStr( ppSops[i], pCubeIn );
                        Vec_StrPrintStr( ppSops[i], " 1\n" );
                    }
                }
            }
            else
            {
                for ( i = 0; i < nOutputs; i++ )
                {
                    if ( pCubeOut[i] == '1' )
                    {
                        Vec_StrPrintStr( ppSops[i], pCubeIn );
                        Vec_StrPrintStr( ppSops[i], " 1\n" );
                    }
                }
            }
            nCubes++;
        }
    }
    Extra_ProgressBarStop( pProgress );
    if ( nProducts != -1 && nCubes != nProducts )
        printf( "Warning: Mismatch between the number of cubes (%d) and the number on .p line (%d).\n", 
            nCubes, nProducts );

    // add the SOP covers
    Abc_NtkForEachPo( pNtk, pTermPo, i )
    {
        pNode = Abc_ObjFanin0Ntk( Abc_ObjFanin0(pTermPo) );
        if ( ppSops[i]->nSize == 0 )
        {
            Abc_ObjRemoveFanins(pNode);
            pNode->pData = Abc_SopRegister( (Mem_Flex_t *)pNtk->pManFunc, " 0\n" );
            Vec_StrFree( ppSops[i] );
            continue;
        }
        Vec_StrPush( ppSops[i], 0 );
        Io_ReadPlaCubePreprocess( ppSops[i], i, 0 );
        pNode->pData = Abc_SopRegister( (Mem_Flex_t *)pNtk->pManFunc, ppSops[i]->pArray );
        Vec_StrFree( ppSops[i] );
    }
    ABC_FREE( ppSops );
    Abc_NtkFinalizeRead( pNtk );
    return pNtk;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



ABC_NAMESPACE_IMPL_END

