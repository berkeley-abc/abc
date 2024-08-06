/**CFile****************************************************************

  FileName    [abcCas.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Decomposition of shared BDDs into LUT cascade.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcCas.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "bool/kit/kit.h"
#include "aig/miniaig/miniaig.h"

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#include "bdd/extrab/extraLutCas.h"
#endif

ABC_NAMESPACE_IMPL_START


/* 
    This LUT cascade synthesis algorithm is described in the paper:
    A. Mishchenko and T. Sasao, "Encoding of Boolean functions and its 
    application to LUT cascade synthesis", Proc. IWLS '02, pp. 115-120.
    http://www.eecs.berkeley.edu/~alanmi/publications/2002/iwls02_enc.pdf
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_CUDD

extern int Abc_CascadeExperiment( char * pFileGeneric, DdManager * dd, DdNode ** pOutputs, int nInputs, int nOutputs, int nLutSize, int fCheck, int fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCascade( Abc_Ntk_t * pNtk, int nLutSize, int fCheck, int fVerbose )
{
    DdManager * dd;
    DdNode ** ppOutputs;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode;
    char * pFileGeneric;
    int fBddSizeMax = 500000;
    int i, fReorder = 1;
    abctime clk = Abc_Clock();

    assert( Abc_NtkIsStrash(pNtk) );
    // compute the global BDDs
    if ( Abc_NtkBuildGlobalBdds(pNtk, fBddSizeMax, 1, fReorder, 0, fVerbose) == NULL )
        return NULL;

    if ( fVerbose )
    {
        DdManager * dd = (DdManager *)Abc_NtkGlobalBddMan( pNtk );
        printf( "Shared BDD size = %6d nodes.  ", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd) );
        ABC_PRT( "BDD construction time", Abc_Clock() - clk );
    }

    // collect global BDDs
    dd = (DdManager *)Abc_NtkGlobalBddMan( pNtk );
    ppOutputs = ABC_ALLOC( DdNode *, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
        ppOutputs[i] = (DdNode *)Abc_ObjGlobalBdd(pNode);

    // call the decomposition
    pFileGeneric = Extra_FileNameGeneric( pNtk->pSpec );
    if ( !Abc_CascadeExperiment( pFileGeneric, dd, ppOutputs, Abc_NtkCiNum(pNtk), Abc_NtkCoNum(pNtk), nLutSize, fCheck, fVerbose ) )
    {
        // the LUT size is too small
    }

    // for now, duplicate the network
    pNtkNew = Abc_NtkDup( pNtk );

    // cleanup
    Abc_NtkFreeGlobalBdds( pNtk, 1 );
    ABC_FREE( ppOutputs );
    ABC_FREE( pFileGeneric );

//    if ( pNtk->pExdc )
//        pNtkNew->pExdc = Abc_NtkDup( pNtk->pExdc );
    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkCollapse: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

#else

Abc_Ntk_t * Abc_NtkCascade( Abc_Ntk_t * pNtk, int nLutSize, int fCheck, int fVerbose ) { return NULL; }
word * Abc_LutCascade( Mini_Aig_t * p, int nLutSize, int fVerbose ) { return NULL; }

#endif


/*
    The decomposed structure of the LUT cascade is represented as an array of 64-bit integers (words).
    The first word in the record is the number of LUT info blocks in the record, which follow one by one.
    Each LUT info block contains the following:
    - the number of words in this block
    - the number of fanins
    - the list of fanins
    - the variable ID of the output (can be one of the fanin variables)
    - truth tables (one word for 6 vars or less; more words as needed for more than 6 vars)
    For a 6-input node, the LUT info block takes 10 words (block size, fanin count, 6 fanins, output ID, truth table).
    For a 4-input node, the LUT info block takes  8 words (block size, fanin count, 4 fanins, output ID, truth table).
    If the LUT cascade contains a 6-LUT followed by a 4-LUT, the record contains 1+10+8=19 words.
*/

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word * Abc_LutCascadeGenTest()
{
    word * pLuts = ABC_CALLOC( word, 20 ); int i;
    // node count    
    pLuts[0] = 2;
    // first node
    pLuts[1+0] = 10;
    pLuts[1+1] =  6;
    for ( i = 0; i < 6; i++ )
        pLuts[1+2+i] = i;
    pLuts[1+8] = 0;
    pLuts[1+9] = ABC_CONST(0x8000000000000000);
    // second node    
    pLuts[11+0] = 8;
    pLuts[11+1] = 4;
    for ( i = 0; i < 4; i++ )
        pLuts[11+2+i] = i ? i + 5 : 0;
    pLuts[11+6] = 1;
    pLuts[11+7] = ABC_CONST(0xFFFEFFFEFFFEFFFE);
    return pLuts;
}
void Abc_LutCascadePrint( word * pLuts )
{
    int n, i, k;
    printf( "Single-rail LUT cascade has %d nodes:\n", (int)pLuts[0] );
    for ( n = 0, i = 1; n < pLuts[0]; n++, i += pLuts[i] ) 
    {
        word nIns   = pLuts[i+1];
        word * pIns = pLuts+i+2;
        word * pT   = pLuts+i+2+nIns+1;
        printf( "LUT%d : ", n );
        printf( "%02d = F( ", (int)pIns[nIns] );
        for ( k = 0; k < nIns; k++ )
            printf( "%02d ", (int)pIns[k] );
        for ( ; k < 8; k++ )
            printf( "   " );
        printf( ")  " );
        Extra_PrintHex2( stdout, (unsigned *)pT, nIns );
        printf( "\n" );
    }    
}
word * Abc_LutCascadeTest( Mini_Aig_t * p, int nLutSize, int fVerbose )
{
    word * pLuts = Abc_LutCascadeGenTest();
    Abc_LutCascadePrint( pLuts );
    return pLuts;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkLutCascadeDeriveSop( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNodeNew, word * pT, int nIns, Vec_Int_t * vCover )
{
    int RetValue = Kit_TruthIsop( (unsigned *)pT, nIns, vCover, 1 );
    assert( RetValue == 0 || RetValue == 1 );
    if ( Vec_IntSize(vCover) == 0 || (Vec_IntSize(vCover) == 1 && Vec_IntEntry(vCover,0) == 0) ) {
        assert( RetValue == 0 );
        pNodeNew->pData = Abc_SopCreateAnd( (Mem_Flex_t *)pNtkNew->pManFunc, nIns, NULL );
        return (Vec_IntSize(vCover) == 0) ? Abc_NtkCreateNodeConst0(pNtkNew) : Abc_NtkCreateNodeConst1(pNtkNew);
    }
    else {
        char * pSop = Abc_SopCreateFromIsop( (Mem_Flex_t *)pNtkNew->pManFunc, nIns, vCover );
        if ( RetValue ) Abc_SopComplement( (char *)pSop );
        pNodeNew->pData = pSop;
        return pNodeNew;
    }    
}
Abc_Ntk_t * Abc_NtkLutCascadeFromLuts( word * pLuts, Abc_Ntk_t * pNtk, int nLutSize, int fVerbose )
{
    Abc_Ntk_t * pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    Vec_Int_t * vCover = Vec_IntAlloc( 1000 ); word n, i, k, iLastLut = -1;
    assert( Abc_NtkCoNum(pNtk) == 1 );
    for ( n = 0, i = 1; n < pLuts[0]; n++, i += pLuts[i] ) 
    {
        word nIns   = pLuts[i+1];
        word * pIns = pLuts+i+2;
        word * pT   = pLuts+i+2+nIns+1;
        Abc_Obj_t * pNodeNew = Abc_NtkCreateNode( pNtkNew );
        for ( k = 0; k < nIns; k++ )
            Abc_ObjAddFanin( pNodeNew, Abc_NtkCi(pNtk, pIns[k])->pCopy );
        Abc_NtkCi(pNtk, pIns[nIns])->pCopy = Abc_NtkLutCascadeDeriveSop( pNtkNew, pNodeNew, pT, nIns, vCover );
        iLastLut = pIns[nIns];
    }
    Vec_IntFree( vCover );
    Abc_ObjAddFanin( Abc_NtkCo(pNtk, 0)->pCopy, Abc_NtkCi(pNtk, iLastLut)->pCopy );    
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkLutCascadeFromLuts: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;    
}
Abc_Ntk_t * Abc_NtkLutCascade( Abc_Ntk_t * pNtk, int nLutSize, int fVerbose )
{
    extern Gia_Man_t *  Abc_NtkStrashToGia( Abc_Ntk_t * pNtk );
    extern Mini_Aig_t * Gia_ManToMiniAig( Gia_Man_t * pGia );
    extern word *       Abc_LutCascade( Mini_Aig_t * p, int nLutSize, int fVerbose );
    Gia_Man_t * pGia  = Abc_NtkStrashToGia( pNtk );
    Mini_Aig_t * pM   = Gia_ManToMiniAig( pGia );
    word * pLuts      = Abc_LutCascade( pM, nLutSize, fVerbose );
    Abc_Ntk_t * pNew  = pLuts ? Abc_NtkLutCascadeFromLuts( pLuts, pNtk, nLutSize, fVerbose ) : NULL;
    ABC_FREE( pLuts );
    Mini_AigStop( pM );
    Gia_ManStop( pGia );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

