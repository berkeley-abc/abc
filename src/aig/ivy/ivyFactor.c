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

// ISOP computation fails if intermediate memory usage exceed this limit
#define IVY_FACTOR_MEM_LIMIT  16*4096

// intermediate ISOP representation
typedef struct Ivy_Sop_t_ Ivy_Sop_t;
struct Ivy_Sop_t_
{
    unsigned * uCubes;
    int        nCubes;
};

static inline int          Ivy_CubeHasLit( unsigned uCube, int i )              { return (uCube &  (unsigned)(1<<i)) > 0;}
static inline unsigned     Ivy_CubeSetLit( unsigned uCube, int i )              { return  uCube |  (unsigned)(1<<i);     }
static inline unsigned     Ivy_CubeXorLit( unsigned uCube, int i )              { return  uCube ^  (unsigned)(1<<i);     }
static inline unsigned     Ivy_CubeRemLit( unsigned uCube, int i )              { return  uCube & ~(unsigned)(1<<i);     }

static inline int          Ivy_CubeContains( unsigned uLarge, unsigned uSmall ) { return (uLarge & uSmall) == uSmall;    }
static inline unsigned     Ivy_CubeSharp( unsigned uCube, unsigned uPart )      { return uCube & ~uPart;                 }
static inline unsigned     Ivy_CubeMask( int nVar )                             { return (~(unsigned)0) >> (32-nVar);    }

static inline int          Ivy_CubeIsMarked( unsigned uCube )                   { return Ivy_CubeHasLit( uCube, 31 );    }
static inline void         Ivy_CubeMark( unsigned uCube )                       { Ivy_CubeSetLit( uCube, 31 );           }
static inline void         Ivy_CubeUnmark( unsigned uCube )                     { Ivy_CubeRemLit( uCube, 31 );           }

static inline int          Ivy_SopCubeNum( Ivy_Sop_t * cSop )                   { return cSop->nCubes;                   }
static inline unsigned     Ivy_SopCube( Ivy_Sop_t * cSop, int i )               { return cSop->uCubes[i];                }
static inline void         Ivy_SopAddCube( Ivy_Sop_t * cSop, unsigned uCube )   { cSop->uCubes[cSop->nCubes++] = uCube;  }
static inline void         Ivy_SopSetCube( Ivy_Sop_t * cSop, unsigned uCube, int i ) { cSop->uCubes[i] = uCube;          }
static inline void         Ivy_SopShrink( Ivy_Sop_t * cSop, int nCubesNew )     { cSop->nCubes = nCubesNew;              }

// iterators
#define Ivy_SopForEachCube( cSop, uCube, i )                                      \
    for ( i = 0; (i < Ivy_SopCubeNum(cSop)) && ((uCube) = Ivy_SopCube(cSop, i)); i++ )
#define Ivy_CubeForEachLiteral( uCube, Lit, nLits, i )                            \
    for ( i = 0; (i < (nLits)) && ((Lit) = Ivy_CubeHasLit(uCube, i)); i++ )

/**Function*************************************************************

  Synopsis    [Divides cover by one cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_SopDivideByCube( Vec_Int_t * vStore, int nVars, Ivy_Sop_t * cSop, Ivy_Sop_t * cDiv, Ivy_Sop_t * vQuo, Ivy_Sop_t * vRem )
{
    unsigned uCube, uDiv;
    int i;
    // get the only cube
    assert( Ivy_SopCubeNum(cDiv) == 1 );
    uDiv = Ivy_SopCube(cDiv, 0);
    // allocate covers
    vQuo->nCubes = 0;
    vQuo->uCubes = Vec_IntFetch( vStore, Ivy_SopCubeNum(cSop) );
    vRem->nCubes = 0;
    vRem->uCubes = Vec_IntFetch( vStore, Ivy_SopCubeNum(cSop) );
    // sort the cubes
    Ivy_SopForEachCube( cSop, uCube, i )
    {
        if ( Ivy_CubeContains( uCube, uDiv ) )
            Ivy_SopAddCube( vQuo, Ivy_CubeSharp(uCube, uDiv) );
        else
            Ivy_SopAddCube( vRem, uCube );
    }
}

/**Function*************************************************************

  Synopsis    [Divides cover by one cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_SopDivideInternal( Vec_Int_t * vStore, int nVars, Ivy_Sop_t * cSop, Ivy_Sop_t * cDiv, Ivy_Sop_t * vQuo, Ivy_Sop_t * vRem )
{
    unsigned uCube, uCube2, uDiv, uDiv2, uQuo;
    int i, i2, k, k2;
    assert( Ivy_SopCubeNum(cSop) >= Ivy_SopCubeNum(cDiv) );
    if ( Ivy_SopCubeNum(cDiv) == 1 )
    {
        Ivy_SopDivideByCube( cSop, cDiv, vQuo, vRem );
        return;
    }
    // allocate quotient
    vQuo->nCubes = 0;
    vQuo->uCubes = Vec_IntFetch( vStore, Ivy_SopCubeNum(cSop) / Ivy_SopCubeNum(cDiv) );
    // for each cube of the cover
    // it either belongs to the quotient or to the remainder
    Ivy_SopForEachCube( cSop, uCube, i )
    {
        // skip taken cubes
        if ( Ivy_CubeIsMarked(uCube) )
            continue;
        // mark the cube
        Ivy_SopSetCube( cSop, Ivy_CubeMark(uCube), i );
        // find a matching cube in the divisor
        Ivy_SopForEachCube( cDiv, uDiv, k )
            if ( Ivy_CubeContains( uCube, uDiv ) )
                break;
        // the case when the cube is not found
        // (later we will add marked cubes to the remainder)
        if ( k == Ivy_SopCubeNum(cDiv) )
            continue;
        // if the quotient cube exist, it will be 
        uQuo = Ivy_CubeSharp( uCube, uDiv );
        // try to find other cubes of the divisor
        Ivy_SopForEachCube( cDiv, uDiv2, k2 )
        {
            if ( k2 == k )
                continue;
            // find a matching cube
            Ivy_SopForEachCube( cSop, uCube2, i2 )
            {
                // skip taken cubes
                if ( Ivy_CubeIsMarked(uCube2) )
                    continue;
                // check if the cube can be used
                if ( Ivy_CubeContains( uCube2, uDiv2 ) && uQuo == Ivy_CubeSharp( uCube2, uDiv2 ) )
                    break;
            }
            // the case when the cube is not found
            if ( i2 == Ivy_SopCubeNum(cSop) )
                break;
            // the case when the cube is found - mark it and keep going
            Ivy_SopSetCube( cSop, Ivy_CubeMark(uCube2), i2 );
        }
        // if we did not find some cube, continue 
        // (later we will add marked cubes to the remainder)
        if ( k2 != Ivy_SopCubeNum(cDiv) )
            continue;
        // we found all cubes - add the quotient cube
        Ivy_SopAddCube( vQuo, uQuo );
    }
    // allocate remainder
    vRem->nCubes = 0;
    vRem->uCubes = Vec_IntFetch( vStore, Ivy_SopCubeNum(cSop) - Ivy_SopCubeNum(vQuo) * Ivy_SopCubeNum(cDiv) );
    // finally add the remaining cubes to the remainder 
    // and clean the marked cubes in the cover
    Ivy_SopForEachCube( cSop, uCube, i )
    {
        if ( !Ivy_CubeIsMarked(uCube) )
            continue;
        Ivy_SopSetCube( cSop, Ivy_CubeUnmark(uCube), i );
        Ivy_SopAddCube( vRem, Ivy_CubeUnmark(uCube) );
    }
}

/**Function*************************************************************

  Synopsis    [Derives the quotient of division by literal.]

  Description [Reduces the cover to be the equal to the result of
  division of the given cover by the literal.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_SopDivideByLiteralQuo( Ivy_Sop_t * cSop, int iLit )
{
    unsigned uCube;
    int i, k = 0;
    Ivy_SopForEachCube( cSop, uCube, i )
    {
        if ( Ivy_CubeHasLit(uCube, iLit) )
            Ivy_SopSetCube( cSop, Ivy_CubeRemLit(uCube, iLit), k++ );
    }
    Ivy_SopShrink( cSop, k );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_SopCommonCubeCover( Ivy_Sop_t * cSop, Ivy_Sop_t * vCommon, Vec_Int_t * vStore )
{
    unsigned uTemp, uCube;
    int i;
    uCube = ~(unsigned)0;
    Ivy_SopForEachCube( cSop, uTemp, i )
        uCube &= uTemp;
    vCommon->nCubes = 0;
    vCommon->uCubes = Vec_IntFetch( vStore, 1 );
    Ivy_SopPush( vCommon, uCube );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_SopCreateInverse( Ivy_Sop_t * cSop, Vec_Int_t * vInput, int nVars, Vec_Int_t * vStore )
{
    unsigned uCube, uMask;
    int i;
    // start the cover
    cSop->nCubes = 0;
    cSop->uCubes = Vec_IntFetch( vStore, Vec_IntSize(vInput) );
    // add the cubes
    uMask = Ivy_CubeMask( nVars );
    Vec_IntForEachEntry( vInput, uCube, i )
        Vec_IntPush( cSop, Ivy_CubeSharp(uMask, uCube) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_SopDup( Ivy_Sop_t * cSop, Ivy_Sop_t * vCopy, Vec_Int_t * vStore )
{
    unsigned uCube;
    int i;
    // start the cover
    vCopy->nCubes = 0;
    vCopy->uCubes = Vec_IntFetch( vStore, Vec_IntSize(cSop) );
    // add the cubes
    Ivy_SopForEachCube( cSop, uTemp, i )
        Ivy_SopPush( vCopy, uTemp );
}


/**Function*************************************************************

  Synopsis    [Find the least often occurring literal.]

  Description [Find the least often occurring literal among those
  that occur more than once.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_SopWorstLiteral( Ivy_Sop_t * cSop, int nLits )
{
    unsigned uCube;
    int nWord, nBit;
    int i, k, iMin, nLitsMin, nLitsCur;
    int fUseFirst = 1;

    // go through each literal
    iMin = -1;
    nLitsMin = 1000000;
    for ( i = 0; i < nLits; i++ )
    {
        // go through all the cubes
        nLitsCur = 0;
        Ivy_SopForEachCube( cSop, uCube, k )
            if ( Ivy_CubeHasLit(uCube, i) )
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

  Synopsis    [Computes a level-zero kernel.]

  Description [Modifies the cover to contain one level-zero kernel.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_SopMakeCubeFree( Ivy_Sop_t * cSop )
{
    unsigned uMask;
    int i;
    assert( Ivy_SopCubeNum(cSop) > 0 );
    // find the common cube
    uMask = ~(unsigned)0;
    Ivy_SopForEachCube( cSop, uCube, i )
        uMask &= uCube;
    if ( uMask == 0 )
        return;
    // remove the common cube
    Ivy_SopForEachCube( cSop, uCube, i )
        Ivy_SopSetCube( cSop, Ivy_CubeSharp(uCube, uMask), i );
}

/**Function*************************************************************

  Synopsis    [Computes a level-zero kernel.]

  Description [Modifies the cover to contain one level-zero kernel.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_SopDivisorZeroKernel_rec( Ivy_Sop_t * cSop, int nLits )
{
    int iLit;
    // find any literal that occurs at least two times
    iLit = Ivy_SopWorstLiteral( cSop, nLits );
    if ( iLit == -1 )
        return;
    // derive the cube-free quotient
    Ivy_SopDivideByLiteralQuo( cSop, iLit ); // the same cover
    Ivy_SopMakeCubeFree( cSop );             // the same cover
    // call recursively
    Ivy_SopDivisorZeroKernel_rec( cSop );    // the same cover
}

/**Function*************************************************************

  Synopsis    [Returns the quick divisor of the cover.]

  Description [Returns NULL, if there is not divisor other than
  trivial.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_SopDivisor( Ivy_Sop_t * cSop, int nLits, Ivy_Sop_t * cDiv, Vec_Int_t * vStore )
{
    if ( Ivy_SopCubeNum(cSop) <= 1 )
        return 0;
    if ( Ivy_SopWorstLiteral( cSop, nLits ) == -1 )
        return 0;
    // duplicate the cover
    Ivy_SopDup( cSop, cDiv, vStore );
    // perform the kerneling
    Ivy_SopDivisorZeroKernel_rec( cDiv, int nLits );
    assert( Ivy_SopCubeNum(cDiv) > 0 );
    return 1;
}





extern Dec_Edge_t  Dec_Factor32_rec( Dec_Graph_t * pFForm, Vec_Int_t * cSop, int nVars );
extern Dec_Edge_t  Dec_Factor32LF_rec( Dec_Graph_t * pFForm, Vec_Int_t * cSop, int nVars, Vec_Int_t * vSimple );
extern Dec_Edge_t  Dec_Factor32Trivial( Dec_Graph_t * pFForm, Vec_Int_t * cSop, int nVars );
extern Dec_Edge_t  Dec_Factor32TrivialCube( Dec_Graph_t * pFForm, Vec_Int_t * cSop, int nVars, unsigned uCube, Vec_Int_t * vEdgeLits );
extern Dec_Edge_t  Dec_Factor32TrivialTree_rec( Dec_Graph_t * pFForm, Dec_Edge_t * peNodes, int nNodes, int fNodeOr );
extern int         Dec_Factor32Verify( Vec_Int_t * cSop, Dec_Graph_t * pFForm )


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Factors the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Dec_Factor32( Vec_Int_t * cSop, int nVars, Vec_Int_t * vStore )
{
    Ivy_Sop_t cSop, cRes;
    Ivy_Sop_t * pcSop = &cSop, * pcRes = &cRes;
    Dec_Graph_t * pFForm;
    Dec_Edge_t eRoot;

    assert( nVars < 16 );

    // check for trivial functions
    if ( Vec_IntSize(cSop) == 0 )
        return Dec_GraphCreateConst0();
    if ( Vec_IntSize(cSop) == 1 && Vec_IntEntry(cSop, 0) == Ivy_CubeMask(nVars) )
        return Dec_GraphCreateConst1();

    // prepare memory manager
    Vec_IntClear( vStore );
    Vec_IntGrow( vStore, IVY_FACTOR_MEM_LIMIT );

    // perform CST
    Ivy_SopCreateInverse( cSop, pcSop, nVars, vStore ); // CST

    // start the factored form
    pFForm = Dec_GraphCreate( nVars );
    // factor the cover
    eRoot = Dec_Factor32_rec( pFForm, cSop, 2 * nVars );
    // finalize the factored form
    Dec_GraphSetRoot( pFForm, eRoot );

    // verify the factored form
    if ( !Dec_Factor32Verify( pSop, pFForm, nVars ) )
        printf( "Verification has failed.\n" );
    return pFForm;
}

/**Function*************************************************************

  Synopsis    [Internal recursive factoring procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Edge_t Dec_Factor32_rec( Dec_Graph_t * pFForm, Vec_Int_t * cSop, int nLits )
{
    Vec_Int_t * cDiv, * vQuo, * vRem, * vCom;
    Dec_Edge_t eNodeDiv, eNodeQuo, eNodeRem;
    Dec_Edge_t eNodeAnd, eNode;

    // make sure the cover contains some cubes
    assert( Vec_IntSize(cSop) );

    // get the divisor
    cDiv = Ivy_SopDivisor( cSop, nLits );
    if ( cDiv == NULL )
        return Dec_Factor32Trivial( pFForm, cSop, nLits );

    // divide the cover by the divisor
    Ivy_SopDivideInternal( cSop, nLits, cDiv, &vQuo, &vRem );
    assert( Vec_IntSize(vQuo) );

    Vec_IntFree( cDiv );
    Vec_IntFree( vRem );

    // check the trivial case
    if ( Vec_IntSize(vQuo) == 1 )
    {
        eNode = Dec_Factor32LF_rec( pFForm, cSop, nLits, vQuo );
        Vec_IntFree( vQuo );
        return eNode;
    }

    // make the quotient cube free
    Ivy_SopMakeCubeFree( vQuo );

    // divide the cover by the quotient
    Ivy_SopDivideInternal( cSop, nLits, vQuo, &cDiv, &vRem );

    // check the trivial case
    if ( Ivy_SopIsCubeFree( cDiv ) )
    {
        eNodeDiv = Dec_Factor32_rec( pFForm, cDiv );
        eNodeQuo = Dec_Factor32_rec( pFForm, vQuo );
        Vec_IntFree( cDiv );
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
    vCom = Ivy_SopCommonCubeCover( cDiv );
    Vec_IntFree( cDiv );
    Vec_IntFree( vQuo );
    Vec_IntFree( vRem );

    // solve the simple problem
    eNode = Dec_Factor32LF_rec( pFForm, cSop, nLits, vCom );
    Vec_IntFree( vCom );
    return eNode;
}


/**Function*************************************************************

  Synopsis    [Internal recursive factoring procedure for the leaf case.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Edge_t Dec_Factor32LF_rec( Dec_Graph_t * pFForm, Vec_Int_t * cSop, int nLits, Vec_Int_t * vSimple )
{
    Dec_Man_t * pManDec = Abc_FrameReadManDec();
    Vec_Int_t * vEdgeLits  = pManDec->vLits;
    Vec_Int_t * cDiv, * vQuo, * vRem;
    Dec_Edge_t eNodeDiv, eNodeQuo, eNodeRem;
    Dec_Edge_t eNodeAnd;

    // get the most often occurring literal
    cDiv = Ivy_SopBestLiteralCover( cSop, nLits, vSimple );
    // divide the cover by the literal
    Ivy_SopDivideByLiteral( cSop, nLits, cDiv, &vQuo, &vRem );
    // get the node pointer for the literal
    eNodeDiv = Dec_Factor32TrivialCube( pFForm, cDiv, Ivy_SopReadCubeHead(cDiv), vEdgeLits );
    Vec_IntFree( cDiv );
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
Dec_Edge_t Dec_Factor32Trivial( Dec_Graph_t * pFForm, Vec_Int_t * cSop, int nLits )
{
    Dec_Man_t * pManDec = Abc_FrameReadManDec();
    Vec_Int_t * vEdgeCubes = pManDec->vCubes;
    Vec_Int_t * vEdgeLits  = pManDec->vLits;
    Mvc_Manager_t * pMem = pManDec->pMvcMem;
    Dec_Edge_t eNode;
    unsigned uCube;
    int i;
    // create the factored form for each cube
    Vec_IntClear( vEdgeCubes );
    Ivy_SopForEachCube( cSop, uCube )
    {
        eNode = Dec_Factor32TrivialCube( pFForm, cSop, nLits, uCube, vEdgeLits );
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
Dec_Edge_t Dec_Factor32TrivialCube( Dec_Graph_t * pFForm, Vec_Int_t * cSop, unsigned uCube, int nLits, Vec_Int_t * vEdgeLits )
{
    Dec_Edge_t eNode;
    int iBit, Value;
    // create the factored form for each literal
    Vec_IntClear( vEdgeLits );
    Mvc_CubeForEachLit( cSop, uCube, iBit, Value )
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




// verification using temporary BDD package
#include "cuddInt.h"

/**Function*************************************************************

  Synopsis    [Verifies that the factoring is correct.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Ivy_SopCoverToBdd( DdManager * dd, Vec_Int_t * cSop, int nVars )
{
    DdNode * bSum, * bCube, * bTemp, * bVar;
    unsigned uCube;
    int Value, v;
    assert( nVars < 16 );
    // start the cover
    bSum = Cudd_ReadLogicZero(dd);   Cudd_Ref( bSum );
   // check the logic function of the node
    Vec_IntForEachEntry( cSop, uCube, i )
    {
        bCube = Cudd_ReadOne(dd);   Cudd_Ref( bCube );
        for ( v = 0; v < nVars; v++ )
        {
            Value = ((uCube >> 2*v) & 3);
            if ( Value == 1 )
                bVar = Cudd_Not( Cudd_bddIthVar( dd, v ) );
            else if ( Value == 2 )
                bVar = Cudd_bddIthVar( dd, v );
            else
                continue;
            bCube  = Cudd_bddAnd( dd, bTemp = bCube, bVar );   Cudd_Ref( bCube );
            Cudd_RecursiveDeref( dd, bTemp );
        }
        bSum = Cudd_bddOr( dd, bTemp = bSum, bCube );   
        Cudd_Ref( bSum );
        Cudd_RecursiveDeref( dd, bTemp );
        Cudd_RecursiveDeref( dd, bCube );
    }
    // complement the result if necessary
    Cudd_Deref( bSum );
    return bSum;
}

/**Function*************************************************************

  Synopsis    [Verifies that the factoring is correct.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dec_Factor32Verify( Vec_Int_t * cSop, Dec_Graph_t * pFForm, int nVars )
{
    static DdManager * dd = NULL;
    DdNode * bFunc1, * bFunc2;
    int RetValue;
    // get the manager
    if ( dd == NULL )
        dd = Cudd_Init( 16, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    // get the functions
    bFunc1 = Ivy_SopCoverToBdd( dd, cSop, nVars );   Cudd_Ref( bFunc1 );
    bFunc2 = Dec_GraphDeriveBdd( dd, pFForm );         Cudd_Ref( bFunc2 );
//Extra_bddPrint( dd, bFunc1 ); printf("\n");
//Extra_bddPrint( dd, bFunc2 ); printf("\n");
    RetValue = (bFunc1 == bFunc2);
    if ( bFunc1 != bFunc2 )
    {
        int s;
        Extra_bddPrint( dd, bFunc1 ); printf("\n");
        Extra_bddPrint( dd, bFunc2 ); printf("\n");
        s  = 0;
    }
    Cudd_RecursiveDeref( dd, bFunc1 );
    Cudd_RecursiveDeref( dd, bFunc2 );
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


