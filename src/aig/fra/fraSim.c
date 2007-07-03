/**CFile****************************************************************

  FileName    [fraSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraSim.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Assigns random patterns to the PI node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_NodeAssignRandom( Fra_Man_t * p, Dar_Obj_t * pObj )
{
    unsigned * pSims;
    int i;
    assert( Dar_ObjIsPi(pObj) );
    pSims = Fra_ObjSim(pObj);
    for ( i = 0; i < p->nSimWords; i++ )
        pSims[i] = Fra_ObjRandomSim();
}

/**Function*************************************************************

  Synopsis    [Assigns constant patterns to the PI node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_NodeAssignConst( Fra_Man_t * p, Dar_Obj_t * pObj, int fConst1 )
{
    unsigned * pSims;
    int i;
    assert( Dar_ObjIsPi(pObj) );
    pSims = Fra_ObjSim(pObj);
    for ( i = 0; i < p->nSimWords; i++ )
        pSims[i] = fConst1? ~(unsigned)0 : 0;
}

/**Function*************************************************************

  Synopsis    [Assings random simulation info for the PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_AssignRandom( Fra_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i;
    Dar_ManForEachPi( p->pManAig, pObj, i )
        Fra_NodeAssignRandom( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Assings distance-1 simulation info for the PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_AssignDist1( Fra_Man_t * p, unsigned * pPat )
{
    Dar_Obj_t * pObj;
    int i, Limit;
    Dar_ManForEachPi( p->pManAig, pObj, i )
        Fra_NodeAssignConst( p, pObj, Dar_InfoHasBit(pPat, i) );
    Limit = DAR_MIN( Dar_ManPiNum(p->pManAig), p->nSimWords * 32 - 1 );
    for ( i = 0; i < Limit; i++ )
        Dar_InfoXorBit( Fra_ObjSim( Dar_ManPi(p->pManAig,i) ), i+1 );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if simulation info is composed of all zeros.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_NodeHasZeroSim( Fra_Man_t * p, Dar_Obj_t * pObj )
{
    unsigned * pSims;
    int i;
    pSims = Fra_ObjSim(pObj);
    for ( i = 0; i < p->nSimWords; i++ )
        if ( pSims[i] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if simulation info is composed of all zeros.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_NodeComplementSim( Fra_Man_t * p, Dar_Obj_t * pObj )
{
    unsigned * pSims;
    int i;
    pSims = Fra_ObjSim(pObj);
    for ( i = 0; i < p->nSimWords; i++ )
        pSims[i] = ~pSims[i];
}

/**Function*************************************************************

  Synopsis    [Returns 1 if simulation infos are equal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_NodeCompareSims( Fra_Man_t * p, Dar_Obj_t * pObj0, Dar_Obj_t * pObj1 )
{
    unsigned * pSims0, * pSims1;
    int i;
    pSims0 = Fra_ObjSim(pObj0);
    pSims1 = Fra_ObjSim(pObj1);
    for ( i = 0; i < p->nSimWords; i++ )
        if ( pSims0[i] != pSims1[i] )
            return 0;
    return 1;
}


/**Function*************************************************************

  Synopsis    [Simulates one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_NodeSimulate( Fra_Man_t * p, Dar_Obj_t * pObj )
{
    unsigned * pSims, * pSims0, * pSims1;
    int fCompl, fCompl0, fCompl1, i;
    assert( !Dar_IsComplement(pObj) );
    assert( Dar_ObjIsNode(pObj) );
    // get hold of the simulation information
    pSims  = Fra_ObjSim(pObj);
    pSims0 = Fra_ObjSim(Dar_ObjFanin0(pObj));
    pSims1 = Fra_ObjSim(Dar_ObjFanin1(pObj));
    // get complemented attributes of the children using their random info
    fCompl  = pObj->fPhase;
    fCompl0 = Dar_ObjFaninPhase(Dar_ObjChild0(pObj));
    fCompl1 = Dar_ObjFaninPhase(Dar_ObjChild1(pObj));
    // simulate
    if ( fCompl0 && fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < p->nSimWords; i++ )
                pSims[i] = (pSims0[i] | pSims1[i]);
        else
            for ( i = 0; i < p->nSimWords; i++ )
                pSims[i] = ~(pSims0[i] | pSims1[i]);
    }
    else if ( fCompl0 && !fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < p->nSimWords; i++ )
                pSims[i] = (pSims0[i] | ~pSims1[i]);
        else
            for ( i = 0; i < p->nSimWords; i++ )
                pSims[i] = (~pSims0[i] & pSims1[i]);
    }
    else if ( !fCompl0 && fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < p->nSimWords; i++ )
                pSims[i] = (~pSims0[i] | pSims1[i]);
        else
            for ( i = 0; i < p->nSimWords; i++ )
                pSims[i] = (pSims0[i] & ~pSims1[i]);
    }
    else // if ( !fCompl0 && !fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < p->nSimWords; i++ )
                pSims[i] = ~(pSims0[i] & pSims1[i]);
        else
            for ( i = 0; i < p->nSimWords; i++ )
                pSims[i] = (pSims0[i] & pSims1[i]);
    }
}

/**Function*************************************************************

  Synopsis    [Generated const 0 pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_SavePattern0( Fra_Man_t * p )
{
    memset( p->pPatWords, 0, sizeof(unsigned) * p->nPatWords );
}

/**Function*************************************************************

  Synopsis    [[Generated const 1 pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_SavePattern1( Fra_Man_t * p )
{
    memset( p->pPatWords, 0xff, sizeof(unsigned) * p->nPatWords );
}

/**Function*************************************************************

  Synopsis    [Copy pattern from the solver into the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_SavePattern( Fra_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i;
    memset( p->pPatWords, 0, sizeof(unsigned) * p->nPatWords );
    Dar_ManForEachPi( p->pManFraig, pObj, i )
//    Vec_PtrForEachEntry( p->vPiVars, pObj, i )
        if ( p->pSat->model.ptr[Fra_ObjSatNum(pObj)] == l_True )
            Dar_InfoSetBit( p->pPatWords, i );
//            Ivy_InfoSetBit( p->pPatWords, pObj->Id - 1 );
}

/**Function*************************************************************

  Synopsis    [Cleans pattern scores.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_CleanPatScores( Fra_Man_t * p )
{
    int i, nLimit = p->nSimWords * 32;
    for ( i = 0; i < nLimit; i++ )
        p->pPatScores[i] = 0;
}

/**Function*************************************************************

  Synopsis    [Adds to pattern scores.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_AddToPatScores( Fra_Man_t * p, Dar_Obj_t * pClass, Dar_Obj_t * pClassNew )
{
    unsigned * pSims0, * pSims1;
    unsigned uDiff;
    int i, w;
    // get hold of the simulation information
    pSims0 = Fra_ObjSim(pClass);
    pSims1 = Fra_ObjSim(pClassNew);
    // iterate through the differences and record the score
    for ( w = 0; w < p->nSimWords; w++ )
    {
        uDiff = pSims0[w] ^ pSims1[w];
        if ( uDiff == 0 )
            continue;
        for ( i = 0; i < 32; i++ )
            if ( uDiff & ( 1 << i ) )
                p->pPatScores[w*32+i]++;
    }
}

/**Function*************************************************************

  Synopsis    [Selects the best pattern.]

  Description [Returns 1 if such pattern is found.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_SelectBestPat( Fra_Man_t * p )
{
    unsigned * pSims;
    Dar_Obj_t * pObj;
    int i, nLimit = p->nSimWords * 32, MaxScore = 0, BestPat = -1;
    for ( i = 1; i < nLimit; i++ )
    {
        if ( MaxScore < p->pPatScores[i] )
        {
            MaxScore = p->pPatScores[i];
            BestPat = i;
        }
    }
    if ( MaxScore == 0 )
        return 0;
//    if ( MaxScore > p->pPars->MaxScore )
//    printf( "Max score is %3d.  ", MaxScore );
    // copy the best pattern into the selected pattern
    memset( p->pPatWords, 0, sizeof(unsigned) * p->nPatWords );
    Dar_ManForEachPi( p->pManAig, pObj, i )
    {
        pSims = Fra_ObjSim(pObj);
        if ( Dar_InfoHasBit(pSims, BestPat) )
            Dar_InfoSetBit(p->pPatWords, i);
    }
    return MaxScore;
}

/**Function*************************************************************

  Synopsis    [Simulates AIG manager.]

  Description [Assumes that the PI simulation info is attached.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_SimulateOne( Fra_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i, clk;
clk = clock();
    Dar_ManForEachNode( p->pManAig, pObj, i )
    {
        Fra_NodeSimulate( p, pObj );
/*
        if ( Dar_ObjFraig(pObj) == NULL )
            printf( "%3d --- -- %d  :  ", pObj->Id, pObj->fPhase );
        else
            printf( "%3d %3d %2d %d  :  ", pObj->Id, Dar_Regular(Dar_ObjFraig(pObj))->Id, Dar_ObjSatNum(Dar_Regular(Dar_ObjFraig(pObj))), pObj->fPhase );
        Extra_PrintBinary( stdout, Fra_ObjSim(pObj), 30 );
        printf( "\n" );
*/
    }
p->timeSim += clock() - clk;
p->nSimRounds++;
}

/**Function*************************************************************

  Synopsis    [Resimulates fraiging manager after finding a counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_Resimulate( Fra_Man_t * p )
{
    int nChanges;
    Fra_AssignDist1( p, p->pPatWords );
    Fra_SimulateOne( p );
    if ( p->pPars->fPatScores )
        Fra_CleanPatScores( p );
    nChanges = Fra_RefineClasses( p );
    nChanges += Fra_RefineClasses1( p );
    if ( p->pManFraig->pData )
        return;
    if ( nChanges < 1 )
        printf( "Error: A counter-example did not refine classes!\n" );
    assert( nChanges >= 1 );
//printf( "Refined classes! = %5d.   Changes = %4d.\n", p->lClasses.nItems, nChanges );

    if ( !p->pPars->fPatScores )
        return;

    // perform additional simulation using dist1 patterns derived from successful patterns
    while ( Fra_SelectBestPat(p) > p->pPars->MaxScore )
    {
        Fra_AssignDist1( p, p->pPatWords );
        Fra_SimulateOne( p );
        Fra_CleanPatScores( p );
        nChanges = Fra_RefineClasses( p );
        nChanges += Fra_RefineClasses1( p );
        if ( p->pManFraig->pData )
            return;
//printf( "Refined class!!! = %5d.   Changes = %4d.   Pairs = %6d.\n", p->lClasses.nItems, nChanges, Fra_CountPairsClasses(p) );
        if ( nChanges == 0 )
            break;
    }
}

/**Function*************************************************************

  Synopsis    [Performs simulation of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_Simulate( Fra_Man_t * p )
{
    int nChanges, nClasses;
    // start the classes
    Fra_AssignRandom( p );
    Fra_SimulateOne( p );
    Fra_CreateClasses( p );
//printf( "Starting classes = %5d.   Pairs = %6d.\n", p->lClasses.nItems, Fra_CountPairsClasses(p) );
    // refine classes by walking 0/1 patterns
    Fra_SavePattern0( p );
    Fra_AssignDist1( p, p->pPatWords );
    Fra_SimulateOne( p );
    nChanges = Fra_RefineClasses( p );
    nChanges += Fra_RefineClasses1( p );
    if ( p->pManFraig )
        return;
//printf( "Refined classes  = %5d.   Changes = %4d.   Pairs = %6d.\n", p->lClasses.nItems, nChanges, Fra_CountPairsClasses(p) );
    Fra_SavePattern1( p );
    Fra_AssignDist1( p, p->pPatWords );
    Fra_SimulateOne( p );
    nChanges = Fra_RefineClasses( p );
    nChanges += Fra_RefineClasses1( p );
    if ( p->pManFraig )
        return;
//printf( "Refined classes  = %5d.   Changes = %4d.   Pairs = %6d.\n", p->lClasses.nItems, nChanges, Fra_CountPairsClasses(p) );
    // refine classes by random simulation
    do {
        Fra_AssignRandom( p );
        Fra_SimulateOne( p );
        nClasses = Vec_PtrSize(p->vClasses);
        nChanges = Fra_RefineClasses( p );
        nChanges += Fra_RefineClasses1( p );
        if ( p->pManFraig )
            return;
//printf( "Refined classes  = %5d.   Changes = %4d.   Pairs = %6d.\n", p->lClasses.nItems, nChanges, Fra_CountPairsClasses(p) );
    } while ( (double)nChanges / nClasses > p->pPars->dSimSatur );
//    Fra_PrintSimClasses( p );
}
 
/**Function*************************************************************

  Synopsis    [Creates the counter-example from the successful pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_CheckOutputSimsSavePattern( Fra_Man_t * p, Dar_Obj_t * pObj )
{ 
    unsigned * pSims;
    int i, k, BestPat, * pModel;
    // find the word of the pattern
    pSims = Fra_ObjSim(pObj);
    for ( i = 0; i < p->nSimWords; i++ )
        if ( pSims[i] )
            break;
    assert( i < p->nSimWords );
    // find the bit of the pattern
    for ( k = 0; k < 32; k++ )
        if ( pSims[i] & (1 << k) )
            break;
    assert( k < 32 );
    // determine the best pattern
    BestPat = i * 32 + k;
    // fill in the counter-example data
    pModel = ALLOC( int, Dar_ManPiNum(p->pManFraig) );
    Dar_ManForEachPi( p->pManAig, pObj, i )
    {
        pModel[i] = Dar_InfoHasBit(Fra_ObjSim(pObj), BestPat);
//        printf( "%d", pModel[i] );
    }
//    printf( "\n" );
    // set the model
    assert( p->pManFraig->pData == NULL );
    p->pManFraig->pData = pModel;
    return;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the one of the output is already non-constant 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_CheckOutputSims( Fra_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i;
    // make sure the reference simulation pattern does not detect the bug
    pObj = Dar_ManPo( p->pManAig, 0 );
    assert( Dar_ObjFanin0(pObj)->fPhase == (unsigned)Dar_ObjFaninC0(pObj) ); // Dar_ObjFaninPhase(Dar_ObjChild0(pObj)) == 0
    Dar_ManForEachPo( p->pManAig, pObj, i )
    {
        // complement simulation info
//        if ( Dar_ObjFanin0(pObj)->fPhase ^ Dar_ObjFaninC0(pObj) ) // Dar_ObjFaninPhase(Dar_ObjChild0(pObj))
//            Fra_NodeComplementSim( p, Dar_ObjFanin0(pObj) );
        // check 
        if ( !Fra_NodeHasZeroSim( p, Dar_ObjFanin0(pObj) ) )
        {
            // create the counter-example from this pattern
            Fra_CheckOutputSimsSavePattern( p, Dar_ObjFanin0(pObj) );
            return 1;
        }
        // complement simulation info
//        if ( Dar_ObjFanin0(pObj)->fPhase ^ Dar_ObjFaninC0(pObj) )
//            Fra_NodeComplementSim( p, Dar_ObjFanin0(pObj) );
    }
    return 0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


