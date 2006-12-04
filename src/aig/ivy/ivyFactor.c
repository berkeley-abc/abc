/**CFile****************************************************************

  FileName    [ivyFactor.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Factoring the cover up to 16 inputs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyFactor.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"
#include "dec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Dec_Edge_t  Dec_Factor32_rec( Dec_Graph_t * pFForm, Vec_Int_t * vCover, int nVars );
extern Dec_Edge_t  Dec_Factor32LF_rec( Dec_Graph_t * pFForm, Vec_Int_t * vCover, int nVars, Vec_Int_t * vSimple );
extern Dec_Edge_t  Dec_Factor32Trivial( Dec_Graph_t * pFForm, Vec_Int_t * vCover, int nVars );
extern Dec_Edge_t  Dec_Factor32TrivialCube( Dec_Graph_t * pFForm, Vec_Int_t * vCover, int nVars, Mvc_Cube_t * pCube, Vec_Int_t * vEdgeLits );
extern Dec_Edge_t  Dec_Factor32TrivialTree_rec( Dec_Graph_t * pFForm, Dec_Edge_t * peNodes, int nNodes, int fNodeOr );
extern Vec_Int_t * Dec_Factor32Divisor( Vec_Int_t * vCover, int nVars );
extern void        Dec_Factor32DivisorZeroKernel( Vec_Int_t * vCover, int nVars );
extern int         Dec_Factor32WorstLiteral( Vec_Int_t * vCover, int nVars );

extern Vec_Int_t * Mvc_CoverCommonCubeCover( Vec_Int_t * vCover );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Factors the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Dec_Factor32( Vec_Int_t * vCover, int nVars )
{
    Dec_Graph_t * pFForm;
    Dec_Edge_t eRoot;

    // check for trivial functions
    if ( Vec_IntSize(vCover) == 0 )
        return Dec_GraphCreateConst0();
    if ( Vec_IntSize(vCover) == 1 && /* tautology */ )
        return Dec_GraphCreateConst1();

    // perform CST
    Mvc_CoverInverse( vCover ); // CST
    // start the factored form
    pFForm = Dec_GraphCreate( Abc_SopGetVarNum(pSop) );
    // factor the cover
    eRoot = Dec_Factor32_rec( pFForm, vCover, nVars );
    // finalize the factored form
    Dec_GraphSetRoot( pFForm, eRoot );
    // verify the factored form
//    if ( !Dec_Factor32Verify( pSop, pFForm ) )
//        printf( "Verification has failed.\n" );
//    Mvc_CoverInverse( vCover ); // undo CST
    return pFForm;
}

/**Function*************************************************************

  Synopsis    [Internal recursive factoring procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Edge_t Dec_Factor32_rec( Dec_Graph_t * pFForm, Vec_Int_t * vCover, int nVars )
{
    Vec_Int_t * vDiv, * vQuo, * vRem, * vCom;
    Dec_Edge_t eNodeDiv, eNodeQuo, eNodeRem;
    Dec_Edge_t eNodeAnd, eNode;

    // make sure the cover contains some cubes
    assert( Vec_IntSize(vCover) );

    // get the divisor
    vDiv = Dec_Factor32Divisor( vCover, nVars );
    if ( vDiv == NULL )
        return Dec_Factor32Trivial( pFForm, vCover, nVars );

    // divide the cover by the divisor
    Mvc_CoverDivideInternal( vCover, nVars, vDiv, &vQuo, &vRem );
    assert( Vec_IntSize(vQuo) );

    Vec_IntFree( vDiv );
    Vec_IntFree( vRem );

    // check the trivial case
    if ( Vec_IntSize(vQuo) == 1 )
    {
        eNode = Dec_Factor32LF_rec( pFForm, vCover, nVars, vQuo );
        Vec_IntFree( vQuo );
        return eNode;
    }

    // make the quotient cube free
    Mvc_CoverMakeCubeFree( vQuo );

    // divide the cover by the quotient
    Mvc_CoverDivideInternal( vCover, nVars, vQuo, &vDiv, &vRem );

    // check the trivial case
    if ( Mvc_CoverIsCubeFree( vDiv ) )
    {
        eNodeDiv = Dec_Factor32_rec( pFForm, vDiv );
        eNodeQuo = Dec_Factor32_rec( pFForm, vQuo );
        Vec_IntFree( vDiv );
        Vec_IntFree( vQuo );
        eNodeAnd = Dec_GraphAddNodeAnd( pFForm, eNodeDiv, eNodeQuo );
        if ( Vec_IntSize(vRem) == 0 )
        {
            Vec_IntFree( vRem );
            return eNodeAnd;
        }
        else
        {
            eNodeRem = Dec_Factor32_rec( pFForm, vRem );
            Vec_IntFree( vRem );
            return Dec_GraphAddNodeOr( pFForm, eNodeAnd, eNodeRem );
        }
    }

    // get the common cube
    vCom = Mvc_CoverCommonCubeCover( vDiv );
    Vec_IntFree( vDiv );
    Vec_IntFree( vQuo );
    Vec_IntFree( vRem );

    // solve the simple problem
    eNode = Dec_Factor32LF_rec( pFForm, vCover, nVars, vCom );
    Vec_IntFree( vCom );
    return eNode;
}


/**Function*************************************************************

  Synopsis    [Internal recursive factoring procedure for the leaf case.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Edge_t Dec_Factor32LF_rec( Dec_Graph_t * pFForm, Vec_Int_t * vCover, int nVars, Vec_Int_t * vSimple )
{
    Dec_Man_t * pManDec = Abc_FrameReadManDec();
    Vec_Int_t * vEdgeLits  = pManDec->vLits;
    Vec_Int_t * vDiv, * vQuo, * vRem;
    Dec_Edge_t eNodeDiv, eNodeQuo, eNodeRem;
    Dec_Edge_t eNodeAnd;

    // get the most often occurring literal
    vDiv = Mvc_CoverBestLiteralCover( vCover, nVars, vSimple );
    // divide the cover by the literal
    Mvc_CoverDivideByLiteral( vCover, nVars, vDiv, &vQuo, &vRem );
    // get the node pointer for the literal
    eNodeDiv = Dec_Factor32TrivialCube( pFForm, vDiv, Mvc_CoverReadCubeHead(vDiv), vEdgeLits );
    Vec_IntFree( vDiv );
    // factor the quotient and remainder
    eNodeQuo = Dec_Factor32_rec( pFForm, vQuo );
    Vec_IntFree( vQuo );
    eNodeAnd = Dec_GraphAddNodeAnd( pFForm, eNodeDiv, eNodeQuo );
    if ( Vec_IntSize(vRem) == 0 )
    {
        Vec_IntFree( vRem );
        return eNodeAnd;
    }
    else
    {
        eNodeRem = Dec_Factor32_rec( pFForm, vRem );
        Vec_IntFree( vRem );
        return Dec_GraphAddNodeOr( pFForm, eNodeAnd, eNodeRem );
    }
}



/**Function*************************************************************

  Synopsis    [Factoring the cover, which has no algebraic divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Edge_t Dec_Factor32Trivial( Dec_Graph_t * pFForm, Vec_Int_t * vCover, int nVars )
{
    Dec_Man_t * pManDec = Abc_FrameReadManDec();
    Vec_Int_t * vEdgeCubes = pManDec->vCubes;
    Vec_Int_t * vEdgeLits  = pManDec->vLits;
    Mvc_Manager_t * pMem = pManDec->pMvcMem;
    Dec_Edge_t eNode;
    Mvc_Cube_t * pCube;
    int i;
    // create the factored form for each cube
    Vec_IntClear( vEdgeCubes );
    Mvc_CoverForEachCube( vCover, pCube )
    {
        eNode = Dec_Factor32TrivialCube( pFForm, vCover, nVars, pCube, vEdgeLits );
        Vec_IntPush( vEdgeCubes, Dec_EdgeToInt_(eNode) );
    }
    // balance the factored forms
    return Dec_Factor32TrivialTree_rec( pFForm, (Dec_Edge_t *)vEdgeCubes->pArray, vEdgeCubes->nSize, 1 );
}

/**Function*************************************************************

  Synopsis    [Factoring the cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Edge_t Dec_Factor32TrivialCube( Dec_Graph_t * pFForm, Vec_Int_t * vCover, Mvc_Cube_t * pCube, int nVars, Vec_Int_t * vEdgeLits )
{
    Dec_Edge_t eNode;
    int iBit, Value;
    // create the factored form for each literal
    Vec_IntClear( vEdgeLits );
    Mvc_CubeForEachBit( vCover, pCube, iBit, Value )
        if ( Value )
        {
            eNode = Dec_EdgeCreate( iBit/2, iBit%2 ); // CST
            Vec_IntPush( vEdgeLits, Dec_EdgeToInt_(eNode) );
        }
    // balance the factored forms
    return Dec_Factor32TrivialTree_rec( pFForm, (Dec_Edge_t *)vEdgeLits->pArray, vEdgeLits->nSize, 0 );
}

/**Function*************************************************************

  Synopsis    [Create the well-balanced tree of nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Edge_t Dec_Factor32TrivialTree_rec( Dec_Graph_t * pFForm, Dec_Edge_t * peNodes, int nNodes, int fNodeOr )
{
    Dec_Edge_t eNode1, eNode2;
    int nNodes1, nNodes2;

    if ( nNodes == 1 )
        return peNodes[0];

    // split the nodes into two parts
    nNodes1 = nNodes/2;
    nNodes2 = nNodes - nNodes1;
//    nNodes2 = nNodes/2;
//    nNodes1 = nNodes - nNodes2;

    // recursively construct the tree for the parts
    eNode1 = Dec_Factor32TrivialTree_rec( pFForm, peNodes,           nNodes1, fNodeOr );
    eNode2 = Dec_Factor32TrivialTree_rec( pFForm, peNodes + nNodes1, nNodes2, fNodeOr );

    if ( fNodeOr )
        return Dec_GraphAddNodeOr( pFForm, eNode1, eNode2 );
    else
        return Dec_GraphAddNodeAnd( pFForm, eNode1, eNode2 );
}

/**Function*************************************************************

  Synopsis    [Returns the quick divisor of the cover.]

  Description [Returns NULL, if there is not divisor other than
  trivial.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Dec_Factor32Divisor( Vec_Int_t * vCover, int nVars )
{
    Vec_Int_t * pKernel;
    if ( Vec_IntSize(vCover) <= 1 )
        return NULL;
    // allocate the literal array and count literals
    if ( Mvc_CoverAnyLiteral( vCover, NULL ) == -1 )
        return NULL;
    // duplicate the cover
    pKernel = Mvc_CoverDup(vCover);
    // perform the kerneling
    Dec_Factor32DivisorZeroKernel( pKernel );
    assert( Vec_IntSize(pKernel) );
    return pKernel;
}

/**Function*************************************************************

  Synopsis    [Computes a level-zero kernel.]

  Description [Modifies the cover to contain one level-zero kernel.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dec_Factor32DivisorZeroKernel( Vec_Int_t * vCover, int nVars )
{
    int iLit;
    // find any literal that occurs at least two times
//    iLit = Mvc_CoverAnyLiteral( vCover, NULL );
    iLit = Dec_Factor32WorstLiteral( vCover, NULL );
//    iLit = Mvc_CoverBestLiteral( vCover, NULL );
    if ( iLit == -1 )
        return;
    // derive the cube-free quotient
    Mvc_CoverDivideByLiteralQuo( vCover, iLit ); // the same cover
    Mvc_CoverMakeCubeFree( vCover );             // the same cover
    // call recursively
    Dec_Factor32DivisorZeroKernel( vCover );              // the same cover
}

/**Function*************************************************************

  Synopsis    [Find the most often occurring literal.]

  Description [Find the most often occurring literal among those
  that occur more than once.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dec_Factor32WorstLiteral( Vec_Int_t * vCover, int nVars )
{
    Mvc_Cube_t * pCube;
    int nWord, nBit;
    int i, iMin, nLitsMin, nLitsCur;
    int fUseFirst = 1;

    // go through each literal
    iMin = -1;
    nLitsMin = 1000000;
    for ( i = 0; i < vCover->nBits; i++ )
    {
        // get the word and bit of this literal
        nWord = Mvc_CubeWhichWord(i);
        nBit  = Mvc_CubeWhichBit(i);
        // go through all the cubes
        nLitsCur = 0;
        Mvc_CoverForEachCube( vCover, pCube )
            if ( pCube->pData[nWord] & (1<<nBit) )
                nLitsCur++;

        // skip the literal that does not occur or occurs once
        if ( nLitsCur < 2 )
            continue;

        // check if this is the best literal
        if ( fUseFirst )
        {
            if ( nLitsMin > nLitsCur )
            {
                nLitsMin = nLitsCur;
                iMin = i;
            }
        }
        else
        {
            if ( nLitsMin >= nLitsCur )
            {
                nLitsMin = nLitsCur;
                iMin = i;
            }
        }
    }

    if ( nLitsMin < 1000000 )
        return iMin;
    return -1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Mvc_CoverCommonCubeCover( Vec_Int_t * vCover )
{
    Vec_Int_t * vRes;
    unsigned uTemp, uCube;
    int i;
    uCube = ~(unsigned)0;
    Vec_IntForEachEntry( vCover, uTemp, i )
        uCube &= uTemp;
    vRes = Vec_IntAlloc( 1 );
    Vec_IntPush( vRes, uCube );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the support of cover2 is contained in the support of cover1.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mvc_CoverCheckSuppContainment( Vec_Int_t * vCover1, Vec_Int_t * vCover2 )
{
    unsigned uTemp, uSupp1, uSupp2;
    int i;
    // set the supports
    uSupp1 = 0;
    Vec_IntForEachEntry( vCover1, uTemp, i )
        uSupp1 |= uTemp;
    uSupp2 = 0;
    Vec_IntForEachEntry( vCover2, uTemp, i )
        uSupp2 |= uTemp;
    // return containment
    return uSupp1 & !uSupp2;
//    Mvc_CubeBitNotImpl( Result, vCover2->pMask, vCover1->pMask );
//    return !Result;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mvc_CoverDivide( Vec_Int_t * vCover, Vec_Int_t * vDiv, Vec_Int_t ** pvQuo, Vec_Int_t ** pvRem )
{
    // check the number of cubes
    if ( Vec_IntSize( vCover ) < Vec_IntSize( vDiv ) )
    {
        *pvQuo = NULL;
        *pvRem = NULL;
        return;
    }

    // make sure that support of vCover contains that of vDiv
    if ( !Mvc_CoverCheckSuppContainment( vCover, vDiv ) )
    {
        *pvQuo = NULL;
        *pvRem = NULL;
        return;
    }

    // perform the general division
    Mvc_CoverDivideInternal( vCover, vDiv, pvQuo, pvRem );
}


/**Function*************************************************************

  Synopsis    [Merge the cubes inside the groups.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mvc_CoverDivideInternal( Vec_Int_t * vCover, Vec_Int_t * vDiv, Vec_Int_t ** pvQuo, Vec_Int_t ** pvRem )
{
    Vec_Int_t * vQuo, * vRem;
    Mvc_Cube_t * pCubeC, * pCubeD, * pCubeCopy;
    Mvc_Cube_t * pCube1, * pCube2;
    int * pGroups, nGroups;    // the cube groups
    int nCubesC, nCubesD, nMerges, iCubeC, iCubeD, iMerge;
    int fSkipG, GroupSize, g, c, RetValue;
    int nCubes;

    // get cover sizes
    nCubesD = Vec_IntSize( vDiv );
    nCubesC = Vec_IntSize( vCover );

    // check trivial cases
    if ( nCubesD == 1 )
    {
        if ( Mvc_CoverIsOneLiteral( vDiv ) )
            Mvc_CoverDivideByLiteral( vCover, vDiv, pvQuo, pvRem );
        else
            Mvc_CoverDivideByCube( vCover, vDiv, pvQuo, pvRem );
        return;
    }

    // create the divisor and the remainder 
    vQuo = Mvc_CoverAlloc( vCover->pMem, vCover->nBits );
    vRem = Mvc_CoverAlloc( vCover->pMem, vCover->nBits );

    // get the support of the divisor
    Mvc_CoverAllocateMask( vDiv );
    Mvc_CoverSupport( vDiv, vDiv->pMask );

    // sort the cubes of the divisor
    Mvc_CoverSort( vDiv, NULL, Mvc_CubeCompareInt );
    // sort the cubes of the cover
    Mvc_CoverSort( vCover, vDiv->pMask, Mvc_CubeCompareIntOutsideAndUnderMask );

    // allocate storage for cube groups
    pGroups = MEM_ALLOC( vCover->pMem, int, nCubesC + 1 );

    // mask contains variables in the support of Div
    // split the cubes into groups using the mask
    Mvc_CoverList2Array( vCover );
    Mvc_CoverList2Array( vDiv );
    pGroups[0] = 0;
    nGroups    = 1;
    for ( c = 1; c < nCubesC; c++ )
    {
        // get the cubes
        pCube1 = vCover->pCubes[c-1];
        pCube2 = vCover->pCubes[c  ];
        // compare the cubes
        Mvc_CubeBitEqualOutsideMask( RetValue, pCube1, pCube2, vDiv->pMask );
        if ( !RetValue )
            pGroups[nGroups++] = c;
    }
    // finish off the last group
    pGroups[nGroups] = nCubesC;

    // consider each group separately and decide
    // whether it can produce a quotient cube
    nCubes = 0;
    for ( g = 0; g < nGroups; g++ )
    {
        // if the group has less than nCubesD cubes, 
        // there is no way it can produce the quotient cube
        // copy the cubes to the remainder
        GroupSize = pGroups[g+1] - pGroups[g];
        if ( GroupSize < nCubesD )
        {
            for ( c = pGroups[g]; c < pGroups[g+1]; c++ )
            {
                pCubeCopy = Mvc_CubeDup( vRem, vCover->pCubes[c] );
                Mvc_CoverAddCubeTail( vRem, pCubeCopy );
                nCubes++;
            }
            continue;
        }

        // mark the cubes as those that should be added to the remainder
        for ( c = pGroups[g]; c < pGroups[g+1]; c++ )
            Mvc_CubeSetSize( vCover->pCubes[c], 1 );

        // go through the cubes in the group and at the same time
        // go through the cubes in the divisor
        iCubeD  = 0;
        iCubeC  = 0;
        pCubeD  = vDiv->pCubes[iCubeD++];
        pCubeC  = vCover->pCubes[pGroups[g]+iCubeC++];
        fSkipG  = 0;
        nMerges = 0;

        while ( 1 )
        {
            // compare the topmost cubes in F and in D
            RetValue = Mvc_CubeCompareIntUnderMask( pCubeC, pCubeD, vDiv->pMask );
            // cube are ordered in increasing order of their int value
            if ( RetValue == -1 ) // pCubeC is above pCubeD
            {  // cube in C should be added to the remainder
                // check that there is enough cubes in the group
                if ( GroupSize - iCubeC < nCubesD - nMerges )
                {
                    fSkipG = 1;
                    break;
                }
                // get the next cube in the cover
                pCubeC = vCover->pCubes[pGroups[g]+iCubeC++];
                continue;
            }
            if ( RetValue == 1 ) // pCubeD is above pCubeC
            { // given cube in D does not have a corresponding cube in the cover
                fSkipG = 1;
                break;
            }
            // mark the cube as the one that should NOT be added to the remainder
            Mvc_CubeSetSize( pCubeC, 0 );
            // remember this merged cube
            iMerge = iCubeC-1;
            nMerges++;

            // stop if we considered the last cube of the group
            if ( iCubeD == nCubesD )
                break;

            // advance the cube of the divisor
            assert( iCubeD < nCubesD );
            pCubeD = vDiv->pCubes[iCubeD++];

            // advance the cube of the group
            assert( pGroups[g]+iCubeC < nCubesC );
            pCubeC = vCover->pCubes[pGroups[g]+iCubeC++];
        }

        if ( fSkipG )
        { 
            // the group has failed, add all the cubes to the remainder
            for ( c = pGroups[g]; c < pGroups[g+1]; c++ )
            {
                pCubeCopy = Mvc_CubeDup( vRem, vCover->pCubes[c] );
                Mvc_CoverAddCubeTail( vRem, pCubeCopy );
                nCubes++;
            }
            continue;
        }

        // the group has worked, add left-over cubes to the remainder
        for ( c = pGroups[g]; c < pGroups[g+1]; c++ )
        {
            pCubeC = vCover->pCubes[c];
            if ( Mvc_CubeReadSize(pCubeC) )
            {
                pCubeCopy = Mvc_CubeDup( vRem, pCubeC );
                Mvc_CoverAddCubeTail( vRem, pCubeCopy );
                nCubes++;
            }
        }

        // create the quotient cube
        pCube1 = Mvc_CubeAlloc( vQuo );
        Mvc_CubeBitSharp( pCube1, vCover->pCubes[pGroups[g]+iMerge], vDiv->pMask );
        // add the cube to the quotient
        Mvc_CoverAddCubeTail( vQuo, pCube1 );
        nCubes += nCubesD;
    }
    assert( nCubes == nCubesC );

    // deallocate the memory
    MEM_FREE( vCover->pMem, int, nCubesC + 1, pGroups );

    // return the results
    *pvRem = vRem;
    *pvQuo = vQuo;
//    Mvc_CoverVerifyDivision( vCover, vDiv, vQuo, vRem );
}


/**Function*************************************************************

  Synopsis    [Divides the cover by a cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mvc_CoverDivideByCube( Vec_Int_t * vCover, Vec_Int_t * vDiv, Vec_Int_t ** pvQuo, Vec_Int_t ** pvRem )
{
    Vec_Int_t * vQuo, * vRem;
    Mvc_Cube_t * pCubeC, * pCubeD, * pCubeCopy;
    int ComvResult;

    // get the only cube of D
    assert( Vec_IntSize(vDiv) == 1 );

    // start the quotient and the remainder
    vQuo = Mvc_CoverAlloc( vCover->pMem, vCover->nBits );
    vRem = Mvc_CoverAlloc( vCover->pMem, vCover->nBits );

    // get the first and only cube of the divisor
    pCubeD = Mvc_CoverReadCubeHead( vDiv );

    // iterate through the cubes in the cover
    Mvc_CoverForEachCube( vCover, pCubeC )
    {
        // check the containment of literals from pCubeD in pCube
        Mvc_Cube2BitNotImpl( ComvResult, pCubeD, pCubeC );
        if ( !ComvResult )
        { // this cube belongs to the quotient
            // alloc the cube
            pCubeCopy = Mvc_CubeAlloc( vQuo );
            // clean the support of D
            Mvc_CubeBitSharp( pCubeCopy, pCubeC, pCubeD );
            // add the cube to the quotient
            Mvc_CoverAddCubeTail( vQuo, pCubeCopy );
        }
        else
        { 
            // copy the cube
            pCubeCopy = Mvc_CubeDup( vRem, pCubeC );
            // add the cube to the remainder
            Mvc_CoverAddCubeTail( vRem, pCubeCopy );
        }
    }
    // return the results
    *pvRem = vRem;
    *pvQuo = vQuo;
}

/**Function*************************************************************

  Synopsis    [Divides the cover by a literal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mvc_CoverDivideByLiteral( Vec_Int_t * vCover, Vec_Int_t * vDiv, Vec_Int_t ** pvQuo, Vec_Int_t ** pvRem )
{
    Vec_Int_t * vQuo, * vRem;
    Mvc_Cube_t * pCubeC, * pCubeCopy;
    int iLit;

    // get the only cube of D
    assert( Vec_IntSize(vDiv) == 1 );

    // start the quotient and the remainder
    vQuo = Mvc_CoverAlloc( vCover->pMem, vCover->nBits );
    vRem = Mvc_CoverAlloc( vCover->pMem, vCover->nBits );

    // get the first and only literal in the divisor cube
    iLit = Mvc_CoverFirstCubeFirstLit( vDiv );

    // iterate through the cubes in the cover
    Mvc_CoverForEachCube( vCover, pCubeC )
    {
        // copy the cube
        pCubeCopy = Mvc_CubeDup( vCover, pCubeC );
        // add the cube to the quotient or to the remainder depending on the literal
        if ( Mvc_CubeBitValue( pCubeCopy, iLit ) )
        {   // remove the literal
            Mvc_CubeBitRemove( pCubeCopy, iLit );
            // add the cube ot the quotient
            Mvc_CoverAddCubeTail( vQuo, pCubeCopy );
        }
        else
        {   // add the cube ot the remainder
            Mvc_CoverAddCubeTail( vRem, pCubeCopy );
        }
    }
    // return the results
    *pvRem = vRem;
    *pvQuo = vQuo;
}


/**Function*************************************************************

  Synopsis    [Derives the quotient of division by literal.]

  Description [Reduces the cover to be the equal to the result of
  division of the given cover by the literal.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mvc_CoverDivideByLiteralQuo( Vec_Int_t * vCover, int iLit )
{
    Mvc_Cube_t * pCube, * pCube2, * pPrev;
    // delete those cubes that do not have this literal
    // remove this literal from other cubes
    pPrev = NULL;
    Mvc_CoverForEachCubeSafe( vCover, pCube, pCube2 )
    {
        if ( Mvc_CubeBitValue( pCube, iLit ) == 0 )
        { // delete the cube from the cover
            Mvc_CoverDeleteCube( vCover, pPrev, pCube );
            Mvc_CubeFree( vCover, pCube );
            // don't update the previous cube
        }
        else
        { // delete this literal from the cube
            Mvc_CubeBitRemove( pCube, iLit );
            // update the previous cube
            pPrev = pCube;
        }
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


