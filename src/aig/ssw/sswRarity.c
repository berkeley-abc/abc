/**CFile****************************************************************

  FileName    [sswRarity.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [Rarity-driven refinement of equivalence classes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswRarity.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ssw_RarMan_t_ Ssw_RarMan_t;
struct Ssw_RarMan_t_
{
    // parameters
    int            nWords;       // the number of words to simulate
    int            nFrames;      // the number of frames to simulate
    int            nBinSize;     // the number of flops in one group
    int            fVerbose;     // the verbosiness flag
    int            nGroups;      // the number of flop groups
    // internal data
    Aig_Man_t *    pAig;         // AIG with equivalence classes
    Ssw_Cla_t *    ppClasses;    // equivalence classes
    Ssw_Sml_t *    pSml;         // simulation manager
    Vec_Ptr_t *    vSimInfo;     // simulation info from pSml manager
    Vec_Int_t *    vInits;       // initial state
    // rarity data
    int *          pRarity;      // occur counts for patterns in groups
    int *          pGroupValues; // occur counts in each group
    double *       pPatCosts;    // pattern costs

};

static inline int  Ssw_RarGetBinPat( Ssw_RarMan_t * p, int iBin, int iPat ) 
{
    assert( iBin >= 0 && iBin < Aig_ManRegNum(p->pAig) / p->nBinSize );
    assert( iPat >= 0 && iPat < (1 << p->nBinSize) );
    return p->pRarity[iBin * (1 << p->nBinSize) + iPat];
}
static inline void Ssw_RarSetBinPat( Ssw_RarMan_t * p, int iBin, int iPat, int Value ) 
{
    assert( iBin >= 0 && iBin < Aig_ManRegNum(p->pAig) / p->nBinSize );
    assert( iPat >= 0 && iPat < (1 << p->nBinSize) );
    p->pRarity[iBin * (1 << p->nBinSize) + iPat] = Value;
}
static inline void Ssw_RarAddToBinPat( Ssw_RarMan_t * p, int iBin, int iPat ) 
{
    assert( iBin >= 0 && iBin < Aig_ManRegNum(p->pAig) / p->nBinSize );
    assert( iPat >= 0 && iPat < (1 << p->nBinSize) );
    p->pRarity[iBin * (1 << p->nBinSize) + iPat]++;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ssw_RarMan_t * Ssw_RarManStart( Aig_Man_t * pAig, int nWords, int nFrames, int nBinSize, int fVerbose )
{
    Ssw_RarMan_t * p;
    if ( Aig_ManRegNum(pAig) < nBinSize || nBinSize <= 0 )
        return NULL;
    p = ABC_CALLOC( Ssw_RarMan_t, 1 );
    p->pAig = pAig;
    p->nWords = nWords;
    p->nFrames = nFrames;
    p->nBinSize = nBinSize;
    p->fVerbose = fVerbose;
    p->nGroups = Aig_ManRegNum(pAig) / nBinSize;
    p->pRarity = ABC_CALLOC( int, (1 << nBinSize) * p->nGroups );
    p->pGroupValues = ABC_CALLOC( int, (Aig_ManRegNum(pAig) / nBinSize) );
    p->pPatCosts = ABC_CALLOC( double, p->nWords * 32 );
    p->pSml = Ssw_SmlStart( pAig, 0, nFrames, nWords );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_RarManStop( Ssw_RarMan_t * p )
{
    Ssw_SmlStop( p->pSml );
    Ssw_ClassesStop( p->ppClasses );
    Vec_PtrFreeP( &p->vSimInfo );
    Vec_IntFreeP( &p->vInits );
    ABC_FREE( p->pGroupValues );
    ABC_FREE( p->pPatCosts );
    ABC_FREE( p->pRarity );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Updates rarity counters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_RarUpdateCounters( Ssw_RarMan_t * p )
{
    Aig_Obj_t * pObj;
    unsigned * pData;
    int i, k;
    for ( k = 0; k < p->nWords * 32; k++ )
    {
        for ( i = 0; i < p->nGroups; i++ )
            p->pGroupValues[i] = 0;
        Saig_ManForEachLi( p->pAig, pObj, i )
        {
            pData = Vec_PtrEntry( p->vSimInfo, Aig_ObjId(pObj) );
            if ( Aig_InfoHasBit(pData, k) )
                p->pGroupValues[i / p->nBinSize] |= (1 << (i % p->nBinSize));
        }
        for ( i = 0; i < p->nGroups; i++ )
            Ssw_RarAddToBinPat( p, i, p->pGroupValues[i] );
    }
}

/**Function*************************************************************

  Synopsis    [Select best patterns.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_RarTransferPatterns( Ssw_RarMan_t * p, Vec_Int_t * vInits )
{
    Aig_Obj_t * pObj;
    unsigned * pData;
    int i, k, Value;
    for ( i = 0; i < p->nWords * 32; i++ )
        p->pPatCosts[i] = 0.0;
    for ( i = 0; i < p->nGroups; i++ )
    {
        for ( k = 0; k < p->nWords * 32; k++ )
        {
            Value = Ssw_RarGetBinPat( p, i, k );
            if ( Value == 0 )
                continue;
            p->pPatCosts[k] += 1.0/(Value*Value);
        }
    }
    // choose as many as there are words
    Vec_IntClear( vInits );
    for ( i = 0; i < p->nFrames; i++ )
    {
        // select the best
        int iPatBest = -1;
        double iCostBest = -ABC_INFINITY;
        for ( k = 0; k < p->nWords * 32; k++ )
            if ( iCostBest < p->pPatCosts[k] )
            {
                iCostBest = p->pPatCosts[k];
                iPatBest  = k;
            }
        // remove from costs
        assert( iPatBest >= 0 );
        p->pPatCosts[iPatBest] = -ABC_INFINITY;
        // set the flops
        Saig_ManForEachLo( p->pAig, pObj, k )
        {
            pData = Vec_PtrEntry( p->vSimInfo, Aig_ObjId(pObj) );
            Vec_IntPush( vInits, Aig_InfoHasBit(pData, iPatBest) );
        }
    }
    assert( Vec_IntSize(vInits) == Aig_ManRegNum(p->pAig) * p->nFrames );
}


/**Function*************************************************************

  Synopsis    [Performs fraiging for one node.]

  Description [Returns the fraiged node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ssw_RarFindStartingState( Aig_Man_t * pAig, Abc_Cex_t * pCex )
{ 
    Vec_Int_t * vInit;
    Aig_Obj_t * pObj, * pObjLi;
    int f, i, iBit;
    // assign register outputs
    Saig_ManForEachLi( pAig, pObj, i )
        pObj->fMarkB = 0;
    // simulate the timeframes
    iBit = pCex->nRegs;
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        // set the PI simulation information
        Aig_ManConst1(pAig)->fMarkB = 1;
        Saig_ManForEachPi( pAig, pObj, i )
            pObj->fMarkB = Aig_InfoHasBit( pCex->pData, iBit++ );
        Saig_ManForEachLiLo( pAig, pObjLi, pObj, i )
            pObj->fMarkB = pObjLi->fMarkB;
        // simulate internal nodes
        Aig_ManForEachNode( pAig, pObj, i )
            pObj->fMarkB = ( Aig_ObjFanin0(pObj)->fMarkB ^ Aig_ObjFaninC0(pObj) )
                         & ( Aig_ObjFanin1(pObj)->fMarkB ^ Aig_ObjFaninC1(pObj) );
        // assign the COs
        Aig_ManForEachPo( pAig, pObj, i )
            pObj->fMarkB = ( Aig_ObjFanin0(pObj)->fMarkB ^ Aig_ObjFaninC0(pObj) );
    }
    assert( iBit == pCex->nBits );
    // check that the output failed as expected -- cannot check because it is not an SRM!
//    pObj = Aig_ManPo( pAig, pCex->iPo );
//    if ( pObj->fMarkB != 1 )
//        printf( "The counter-example does not refine the output.\n" );
    // record the new pattern
    vInit = Vec_IntAlloc( Saig_ManRegNum(pAig) );
    Saig_ManForEachLo( pAig, pObj, i )
        Vec_IntPush( vInit, pObj->fMarkB );
    return vInit;
}

/**Function*************************************************************

  Synopsis    [Filter equivalence classes of nodes.]

  Description [Unrolls at most nFramesMax frames. Works with nConfMax 
  conflicts until the first undefined SAT call. Verbose prints the message.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_RarSignalFilter( Aig_Man_t * pAig, int nWords, int nFrames, int nBinSize, int nRounds, Abc_Cex_t * pCex, int fLatchOnly, int fVerbose )
{
    Ssw_RarMan_t * p;
    int r, i, k, clkTotal = clock();
    assert( Aig_ManRegNum(pAig) > 0 );
    assert( Aig_ManConstrNum(pAig) == 0 );
    // consider the case of empty AIG
    if ( Aig_ManNodeNum(pAig) == 0 )
        return;
    // reset random numbers
    Aig_ManRandom( 1 );
    // create manager
    p = Ssw_RarManStart( pAig, nWords, nFrames, nBinSize, fVerbose );
    // create trivial equivalence classes with all nodes being candidates for constant 1
    if ( pAig->pReprs == NULL )
        p->ppClasses = Ssw_ClassesPrepareSimple( pAig, fLatchOnly, 0 );
    else
        p->ppClasses = Ssw_ClassesPrepareFromReprs( pAig );
    Ssw_ClassesSetData( p->ppClasses, NULL, NULL, Ssw_SmlObjIsConstWord, Ssw_SmlObjsAreEqualWord );
    // compute starting state if needed
    assert( p->vInits == NULL );
    if ( pCex )
        p->vInits = Ssw_RarFindStartingState( pAig, pCex );
    else
        p->vInits = Vec_IntStart( Aig_ManRegNum(pAig) );
    // duplicate the array
    for ( i = 1; i < nFrames; i++ )
        for ( k = 0; k < Aig_ManRegNum(pAig); k++ )
            Vec_IntPush( p->vInits, Vec_IntEntry(p->vInits, k) );
    assert( Vec_IntSize(p->vInits) == Aig_ManRegNum(pAig) * nFrames );
    // initialize simulation manager
    p->pSml = Ssw_SmlStart( pAig, 0, nFrames, nWords );
    p->vSimInfo = Ssw_SmlSimDataPointers( p->pSml );
    Ssw_SmlInitializeSpecial( p->pSml, p->vInits );
    // print the stats
    if ( fVerbose )
    {
        printf( "Initial  :  " );
        Ssw_ClassesPrint( p->ppClasses, 0 );
    }
    // refine classes using BMC
    for ( r = 0; r < nRounds; r++ )
    {
        // start filtering equivalence classes
        if ( Ssw_ClassesCand1Num(p->ppClasses) == 0 && Ssw_ClassesClassNum(p->ppClasses) == 0 )
        {
            printf( "All equivalences are refined away.\n" );
            break;
        }
        // simulate
        Ssw_SmlSimulateOne( p->pSml );
        // check equivalence classes
        Ssw_ClassesRefineConst1( p->ppClasses, 1 );
        Ssw_ClassesRefine( p->ppClasses, 1 );
        // printout
        if ( fVerbose )
        {
            printf( "Round %3d:  ", r );
            Ssw_ClassesPrint( p->ppClasses, 0 );
        }
        // get initialization patterns
        Ssw_RarUpdateCounters( p );
        Ssw_RarTransferPatterns( p, p->vInits );
        Ssw_SmlInitializeSpecial( p->pSml, p->vInits );

/*
        // check timeout
        if ( TimeLimit && ((float)TimeLimit <= (float)(clock()-clkTotal)/(float)(CLOCKS_PER_SEC)) )
        {
            printf( "Reached timeout (%d seconds).\n",  TimeLimit );
            break;
        }
*/
    }
    // cleanup
    Ssw_RarManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

