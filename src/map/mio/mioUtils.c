/**CFile****************************************************************

  FileName    [mioUtils.c]

  PackageName [MVSIS 1.3: Multi-valued logic synthesis system.]

  Synopsis    [File reading/writing for technology mapping.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 8, 2003.]

  Revision    [$Id: mioUtils.c,v 1.6 2004/09/03 18:02:20 satrajit Exp $]

***********************************************************************/

#include "mioInt.h"
#include "src/base/main/main.h"
#include "exp.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Mio_WriteGate( FILE * pFile, Mio_Gate_t * pGate, int fPrintSops );
static void Mio_WritePin( FILE * pFile, Mio_Pin_t * pPin );
static int  Mio_DelayCompare( Mio_Gate_t ** ppG1, Mio_Gate_t ** ppG2 );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_LibraryDelete( Mio_Library_t * pLib )
{
    Mio_Gate_t * pGate, * pGate2;
    if ( pLib == NULL )
        return;
    // free the bindings of nodes to gates from this library for all networks
    Abc_FrameUnmapAllNetworks( Abc_FrameGetGlobalFrame() );
    // free the library
    ABC_FREE( pLib->pName );
    Mio_LibraryForEachGateSafe( pLib, pGate, pGate2 )
        Mio_GateDelete( pGate );
    Mem_FlexStop( pLib->pMmFlex, 0 );
    Vec_StrFree( pLib->vCube );
    if ( pLib->tName2Gate )
        st_free_table( pLib->tName2Gate );
//    if ( pLib->dd )
//        Cudd_Quit( pLib->dd );
    ABC_FREE( pLib->ppGates0 );
    ABC_FREE( pLib->ppGatesName );
    ABC_FREE( pLib );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_GateDelete( Mio_Gate_t * pGate )
{
    Mio_Pin_t * pPin, * pPin2;
    if ( pGate->nInputs > 6 )
        ABC_FREE( pGate->pTruth );
    Vec_IntFreeP( &pGate->vExpr );
    ABC_FREE( pGate->pOutName );
    ABC_FREE( pGate->pName );
    ABC_FREE( pGate->pForm );
//    if ( pGate->bFunc )
//        Cudd_RecursiveDeref( pGate->pLib->dd, pGate->bFunc );
    Mio_GateForEachPinSafe( pGate, pPin, pPin2 )
        Mio_PinDelete( pPin );   
    ABC_FREE( pGate );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_PinDelete( Mio_Pin_t * pPin )
{
    ABC_FREE( pPin->pName );
    ABC_FREE( pPin );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mio_Pin_t * Mio_PinDup( Mio_Pin_t * pPin )
{
    Mio_Pin_t * pPinNew;

    pPinNew = ABC_ALLOC( Mio_Pin_t, 1 );
    *pPinNew = *pPin;
    pPinNew->pName = (pPinNew->pName ? Mio_UtilStrsav(pPinNew->pName) : NULL);
    pPinNew->pNext = NULL;

    return pPinNew;
}




/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_WriteLibrary( FILE * pFile, Mio_Library_t * pLib, int fPrintSops )
{
//    Mio_Gate_t * pGate;
    int i;

    fprintf( pFile, "# The genlib library \"%s\".\n", pLib->pName );
//    Mio_LibraryForEachGate( pLib, pGate )
//        Mio_WriteGate( pFile, pGate, fPrintSops );
    for ( i = 0; i < pLib->nGates; i++ )
        Mio_WriteGate( pFile, pLib->ppGates0[i], fPrintSops );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_WriteGate( FILE * pFile, Mio_Gate_t * pGate, int fPrintSops )
{
    Mio_Pin_t * pPin;

    fprintf( pFile, "GATE " );
    fprintf( pFile, "%12s ",      pGate->pName );
    fprintf( pFile, "%10.2f   ",  pGate->dArea );
    fprintf( pFile, "%s=%s;\n",   pGate->pOutName,    pGate->pForm );
    // print the pins
    if ( fPrintSops )
        fprintf( pFile, "%s",       pGate->pSop? pGate->pSop : "unspecified\n" );
//    Extra_bddPrint( pGate->pLib->dd, pGate->bFunc );
//    fprintf( pFile, "\n" );
    Mio_GateForEachPin( pGate, pPin )
        Mio_WritePin( pFile, pPin );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_WritePin( FILE * pFile, Mio_Pin_t * pPin )
{
    char * pPhaseNames[10] = { "UNKNOWN", "INV", "NONINV" };
    fprintf( pFile, "    PIN " );
    fprintf( pFile, "%9s ",     pPin->pName );
    fprintf( pFile, "%10s ",    pPhaseNames[pPin->Phase] );
    fprintf( pFile, "%6d ",     (int)pPin->dLoadInput );
    fprintf( pFile, "%6d ",     (int)pPin->dLoadMax );
    fprintf( pFile, "%6.2f ",   pPin->dDelayBlockRise );
    fprintf( pFile, "%6.2f ",   pPin->dDelayFanoutRise );
    fprintf( pFile, "%6.2f ",   pPin->dDelayBlockFall );
    fprintf( pFile, "%6.2f",    pPin->dDelayFanoutFall );
    fprintf( pFile, "\n" );
}

/**Function*************************************************************

  Synopsis    [Collects the set of root gates.]

  Description [Only collects the gates with unique functionality, 
  which have fewer inputs and shorter delay than the given limits.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mio_Gate_t ** Mio_CollectRoots( Mio_Library_t * pLib, int nInputs, float tDelay, int fSkipInv, int * pnGates )
{
    Mio_Gate_t * pGate;
    Mio_Gate_t ** ppGates;
    /* st_table * tFuncs; */
    /* st_generator * gen; */
//    DdNode * bFunc;
//    DdManager * dd;
    int nGates, iGate;

//    dd     = Mio_LibraryReadDd( pLib );
    nGates = Mio_LibraryReadGateNum( pLib );

    /*

    // for each functionality select one gate; skip constants and buffers
    tFuncs = st_init_table( st_ptrcmp, st_ptrhash );
    Mio_LibraryForEachGate( pLib, pGate )
    {
        bFunc = Mio_GateReadFunc(pGate);
        if ( pGate->nInputs > nInputs )
            continue;
        if ( pGate->dDelayMax > (double)tDelay )
            continue;
        if ( bFunc == b0 || bFunc == b1 )
            continue;
        if ( bFunc == dd->vars[0] )
            continue;
        if ( bFunc == Cudd_Not(dd->vars[0]) && fSkipInv )
            continue;
        if ( st_is_member( tFuncs, (char *)bFunc ) )
            continue;
        st_insert( tFuncs, (char *)bFunc, (char *)pGate );
    }

    // collect the gates into the array
    ppGates = ABC_ALLOC( Mio_Gate_t *, nGates );
    iGate = 0;
    st_foreach_item( tFuncs, gen, (char **)&bFunc, (char **)&pGate )
        ppGates[ iGate++ ] = pGate;
    assert( iGate <= nGates );
    st_free_table( tFuncs );

    */

    ppGates = ABC_ALLOC( Mio_Gate_t *, nGates );
    iGate = 0;
    Mio_LibraryForEachGate( pLib, pGate )
    {
//        bFunc = Mio_GateReadFunc(pGate);
        if ( pGate->nInputs > nInputs )
            continue;
        if ( pGate->dDelayMax > (double)tDelay )
            continue;
//        if ( bFunc == b0 || bFunc == b1 )
        if ( pGate->uTruth == 0 || pGate->uTruth == ~0 )
            continue;
//        if ( bFunc == dd->vars[0] )
        if ( pGate->uTruth == 0xAAAAAAAAAAAAAAAA )
            continue;
//        if ( bFunc == Cudd_Not(dd->vars[0]) && fSkipInv )
        if ( pGate->uTruth == ~0xAAAAAAAAAAAAAAAA && fSkipInv )
            continue;

        assert( iGate < nGates );
        ppGates[ iGate++ ] = pGate;
    }

    if ( iGate > 0 )
    {
        // sort the gates by delay
        qsort( (void *)ppGates, iGate, sizeof(Mio_Gate_t *), 
                (int (*)(const void *, const void *)) Mio_DelayCompare );
        assert( Mio_DelayCompare( ppGates, ppGates + iGate - 1 ) <= 0 );
    }

    if ( pnGates )
        *pnGates = iGate;
    return ppGates;
}

/**Function*************************************************************

  Synopsis    [Compares the max delay of two gates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mio_DelayCompare( Mio_Gate_t ** ppG1, Mio_Gate_t ** ppG2 )
{
    if ( (*ppG1)->dDelayMax < (*ppG2)->dDelayMax )
        return -1;
    if ( (*ppG1)->dDelayMax > (*ppG2)->dDelayMax )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Derives the truth table of the gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Mio_DeriveTruthTable6( Mio_Gate_t * pGate )
{
    static unsigned uTruths6[6][2] = {
        { 0xAAAAAAAA, 0xAAAAAAAA },
        { 0xCCCCCCCC, 0xCCCCCCCC },
        { 0xF0F0F0F0, 0xF0F0F0F0 },
        { 0xFF00FF00, 0xFF00FF00 },
        { 0xFFFF0000, 0xFFFF0000 },
        { 0x00000000, 0xFFFFFFFF }
    };
    unsigned uTruthRes[2];
    assert( pGate->nInputs <= 6 );
    Mio_DeriveTruthTable( pGate, uTruths6, pGate->nInputs, 6, uTruthRes );
    return *((word *)uTruthRes);
}

#if 0

/**Function*************************************************************

  Synopsis    [Recursively derives the truth table of the gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_DeriveTruthTable_rec( DdNode * bFunc, unsigned uTruthsIn[][2], unsigned uTruthRes[] )
{
    unsigned uTruthsCof0[2];
    unsigned uTruthsCof1[2];

    // complement the resulting truth table, if the function is complemented
    if ( Cudd_IsComplement(bFunc) )
    {
        Mio_DeriveTruthTable_rec( Cudd_Not(bFunc), uTruthsIn, uTruthRes );
        uTruthRes[0] = ~uTruthRes[0];
        uTruthRes[1] = ~uTruthRes[1];
        return;
    }

    // if the function is constant 1, return the constant 1 truth table
    if ( bFunc->index == CUDD_CONST_INDEX )
    {
        uTruthRes[0] = MIO_FULL;
        uTruthRes[1] = MIO_FULL;
        return;
    }

    // solve the problem for both cofactors
    Mio_DeriveTruthTable_rec( cuddE(bFunc), uTruthsIn, uTruthsCof0 );
    Mio_DeriveTruthTable_rec( cuddT(bFunc), uTruthsIn, uTruthsCof1 );

    // derive the resulting truth table using the input truth tables
    uTruthRes[0] = (uTruthsCof0[0] & ~uTruthsIn[bFunc->index][0]) |
                   (uTruthsCof1[0] &  uTruthsIn[bFunc->index][0]);
    uTruthRes[1] = (uTruthsCof0[1] & ~uTruthsIn[bFunc->index][1]) |
                   (uTruthsCof1[1] &  uTruthsIn[bFunc->index][1]);
}

/**Function*************************************************************

  Synopsis    [Derives the truth table of the gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_DeriveTruthTable( Mio_Gate_t * pGate, unsigned uTruthsIn[][2], int nSigns, int nInputs, unsigned uTruthRes[] )
{
    Mio_DeriveTruthTable_rec( pGate->bFunc, uTruthsIn, uTruthRes );
}

#endif

/**Function*************************************************************

  Synopsis    [Derives the truth table of the gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_DeriveTruthTable( Mio_Gate_t * pGate, unsigned uTruthsIn[][2], int nSigns, int nInputs, unsigned uTruthRes[] )
{
    word uRes, uFanins[6];
    int i;
    assert( pGate->nInputs == nSigns );
    for ( i = 0; i < nSigns; i++ )
        uFanins[i] = (((word)uTruthsIn[i][1]) << 32) | (word)uTruthsIn[i][0];
    uRes = Exp_Truth6( nSigns, pGate->vExpr, (word *)uFanins );
    uTruthRes[0] = uRes & 0xFFFFFFFF;
    uTruthRes[1] = uRes >> 32;
}

/**Function*************************************************************

  Synopsis    [Reads the number of variables in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mio_SopGetVarNum( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur != '\n'; pCur++ )
        if ( *pCur == 0 )
            return -1;
    return pCur - pSop - 2;
}

/**Function*************************************************************

  Synopsis    [Derives the truth table of the root of the gate.]

  Description [Given the truth tables of the leaves of the gate,
  this procedure derives the truth table of the root.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_DeriveTruthTable2( Mio_Gate_t * pGate, unsigned uTruthsIn[][2], int nTruths, int nInputs, unsigned uTruthRes[] )
{
    unsigned uSignCube[2];
    int i, nFanins;
    char * pCube;

    // make sure that the number of input truth tables in equal to the number of gate inputs
    assert( pGate->nInputs == nTruths );
    assert( nInputs < 7 );

    nFanins = Mio_SopGetVarNum( pGate->pSop );
    assert( nFanins == nInputs );

    // clean the resulting truth table
    uTruthRes[0] = 0;
    uTruthRes[1] = 0;
    if ( nInputs < 6 )
    {
//        Abc_SopForEachCube( pGate->pSop, nFanins, pCube )
        for ( pCube = pGate->pSop; *pCube; pCube += (nFanins) + 3 )
        {
            // add the clause
            uSignCube[0] = MIO_FULL;
            for ( i = 0; i < nFanins; i++ )
            {
                if ( pCube[i] == '0' )
                    uSignCube[0] &= ~uTruthsIn[i][0];
                else if ( pCube[i] == '1' )
                    uSignCube[0] &=  uTruthsIn[i][0];
            }
        }
        if ( nInputs < 5 )
            uTruthRes[0] &= MIO_MASK(1<<nInputs);
    }
    else
    {
        // consider the case when two unsigneds should be used
//        Abc_SopForEachCube( pGate->pSop, nFanins, pCube )
        for ( pCube = pGate->pSop; *pCube; pCube += (nFanins) + 3 )
        {
            uSignCube[0] = MIO_FULL;
            uSignCube[1] = MIO_FULL;
            for ( i = 0; i < nFanins; i++ )
            {
                if ( pCube[i] == '0' )
                {
                    uSignCube[0] &= ~uTruthsIn[i][0];
                    uSignCube[1] &= ~uTruthsIn[i][1];
                }
                else if ( pCube[i] == '1' )
                {
                    uSignCube[0] &=  uTruthsIn[i][0];
                    uSignCube[1] &=  uTruthsIn[i][1];
                }
            }
            uTruthRes[0] |= uSignCube[0];
            uTruthRes[1] |= uSignCube[1];
        }
    }
}

/**Function*************************************************************

  Synopsis    [Derives the area and delay of the root of the gate.]

  Description [Array of the resulting delays should be initialized 
  to the (negative) SUPER_NO_VAR value.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mio_DeriveGateDelays( Mio_Gate_t * pGate, 
    float ** ptPinDelays, int nPins, int nInputs, float tDelayZero, 
    float * ptDelaysRes, float * ptPinDelayMax )
{
    Mio_Pin_t * pPin;
    float Delay, DelayMax;
    int i, k;
    assert( pGate->nInputs == nPins );
    // set all the delays to the unused delay
    for ( i = 0; i < nInputs; i++ )
        ptDelaysRes[i] = tDelayZero;
    // compute the delays for each input and the max delay at the same time
    DelayMax = 0;
    for ( i = 0; i < nInputs; i++ )
    {
        for ( k = 0, pPin = pGate->pPins; pPin; pPin = pPin->pNext, k++ )
        {
            if ( ptPinDelays[k][i] < 0 )
                continue;
            Delay = ptPinDelays[k][i] + (float)pPin->dDelayBlockMax;
            if ( ptDelaysRes[i] < Delay )
                ptDelaysRes[i] = Delay;
        }
        if ( k != nPins )
        {
            printf ("DEBUG: problem gate is %s\n", Mio_GateReadName( pGate ));
        }
        assert( k == nPins );
        if ( DelayMax < ptDelaysRes[i] )
            DelayMax = ptDelaysRes[i];
    }
    *ptPinDelayMax = DelayMax;
}


/**Function*************************************************************

  Synopsis    [Creates a pseudo-gate.]

  Description [The pseudo-gate is a N-input gate with all info set to 0.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mio_Gate_t * Mio_GateCreatePseudo( int nInputs )
{
    Mio_Gate_t * pGate;
    Mio_Pin_t * pPin;
    int i;
    // allocate the gate structure
    pGate = ABC_ALLOC( Mio_Gate_t, 1 );
    memset( pGate, 0, sizeof(Mio_Gate_t) );
    pGate->nInputs = nInputs;
    // create pins
    for ( i = 0; i < nInputs; i++ )
    {
        pPin = ABC_ALLOC( Mio_Pin_t, 1 );
        memset( pPin, 0, sizeof(Mio_Pin_t) );
        pPin->pNext = pGate->pPins;
        pGate->pPins = pPin;
    }
    return pGate;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

