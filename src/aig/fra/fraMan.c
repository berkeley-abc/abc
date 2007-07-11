/**CFile****************************************************************

  FileName    [fraMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    [Starts the FRAIG manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraMan.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets the default solving parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ParamsDefault( Fra_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Fra_Par_t) );
    pPars->nSimWords        =      32;  // the number of words in the simulation info
    pPars->dSimSatur        =   0.005;  // the ratio of refined classes when saturation is reached
    pPars->fPatScores       =       0;  // enables simulation pattern scoring
    pPars->MaxScore         =      25;  // max score after which resimulation is used
    pPars->fDoSparse        =       1;  // skips sparse functions
//    pPars->dActConeRatio    =    0.05;  // the ratio of cone to be bumped
//    pPars->dActConeBumpMax  =     5.0;  // the largest bump of activity
    pPars->dActConeRatio    =     0.3;  // the ratio of cone to be bumped
    pPars->dActConeBumpMax  =    10.0;  // the largest bump of activity
    pPars->nBTLimitNode     =     100;  // conflict limit at a node
    pPars->nBTLimitMiter    =  500000;  // conflict limit at an output
}

/**Function*************************************************************

  Synopsis    [Starts the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fra_Man_t * Fra_ManStart( Dar_Man_t * pManAig, Fra_Par_t * pPars )
{
    Fra_Man_t * p;
    // allocate the fraiging manager
    p = ALLOC( Fra_Man_t, 1 );
    memset( p, 0, sizeof(Fra_Man_t) );
    p->pPars      = pPars;
    p->pManAig    = pManAig;
    p->pManFraig  = Dar_ManStartFrom( pManAig );
    assert( Dar_ManPiNum(p->pManAig) == Dar_ManPiNum(p->pManFraig) );
    // allocate simulation info
    p->nSimWords  = pPars->nSimWords;
    p->pSimWords  = ALLOC( unsigned, (Dar_ManObjIdMax(pManAig) + 1) * p->nSimWords );
    // clean simulation info of the constant node
    memset( p->pSimWords, 0, sizeof(unsigned) * ((Dar_ManPiNum(pManAig) + 1) * p->nSimWords) );
    // allocate storage for sim pattern
    p->nPatWords  = Dar_BitWordNum( Dar_ManPiNum(pManAig) );
    p->pPatWords  = ALLOC( unsigned, p->nPatWords ); 
    p->pPatScores = ALLOC( int, 32 * p->nSimWords ); 
    p->vPiVars    = Vec_PtrAlloc( 100 );
    p->vClasses   = Vec_PtrAlloc( 100 );
    p->vClasses1  = Vec_PtrAlloc( 100 );
    p->vClassOld  = Vec_PtrAlloc( 100 );
    p->vClassNew  = Vec_PtrAlloc( 100 );
    p->vClassesTemp = Vec_PtrAlloc( 100 );
    // allocate other members
    p->nSizeAlloc = Dar_ManObjIdMax(pManAig) + 1;
    p->pMemFraig  = ALLOC( Dar_Obj_t *, p->nSizeAlloc );
    memset( p->pMemFraig, 0, p->nSizeAlloc * sizeof(Dar_Obj_t *) );
    p->pMemRepr  = ALLOC( Dar_Obj_t *, p->nSizeAlloc );
    memset( p->pMemRepr, 0, p->nSizeAlloc * sizeof(Dar_Obj_t *) );
    p->pMemFanins  = ALLOC( Vec_Ptr_t *, p->nSizeAlloc );
    memset( p->pMemFanins, 0, p->nSizeAlloc * sizeof(Vec_Ptr_t *) );
    p->pMemSatNums  = ALLOC( int, p->nSizeAlloc );
    memset( p->pMemSatNums, 0, p->nSizeAlloc * sizeof(int) );
    // set random number generator
    srand( 0xABCABC );
    // make sure the satisfying assignment is node assigned
    assert( p->pManFraig->pData == NULL );
    // connect AIG managers to the FRAIG manager
    Fra_ManPrepare( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Prepares managers by transfering pointers to the objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ManPrepare( Fra_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i;
    // set the pointers to the manager
    Dar_ManForEachObj( p->pManFraig, pObj, i )
        pObj->pData = p;
    // set the pointer to the manager
    Dar_ManForEachObj( p->pManAig, pObj, i )
        pObj->pData = p;
    // set the pointers to the available fraig nodes
    Fra_ObjSetFraig( Dar_ManConst1(p->pManAig), Dar_ManConst1(p->pManFraig) );
    Dar_ManForEachPi( p->pManAig, pObj, i )
        Fra_ObjSetFraig( pObj, Dar_ManPi(p->pManFraig, i) );
}

/**Function*************************************************************

  Synopsis    [Stops the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ManStop( Fra_Man_t * p )
{
    int i;
    for ( i = 0; i < p->nSizeAlloc; i++ )
        if ( p->pMemFanins[i] )
            Vec_PtrFree( p->pMemFanins[i] );
    if ( p->pPars->fVerbose )
        Fra_ManPrint( p );
    if ( p->vClassesTemp ) Vec_PtrFree( p->vClassesTemp );
    if ( p->vClassNew )    Vec_PtrFree( p->vClassNew );
    if ( p->vClassOld )    Vec_PtrFree( p->vClassOld );
    if ( p->vClasses1 )    Vec_PtrFree( p->vClasses1 );
    if ( p->vClasses )     Vec_PtrFree( p->vClasses );
    if ( p->vPiVars )      Vec_PtrFree( p->vPiVars );
    if ( p->pSat )         sat_solver_delete( p->pSat );
    FREE( p->pMemSatNums );
    FREE( p->pMemFanins );
    FREE( p->pMemRepr );
    FREE( p->pMemFraig );
    FREE( p->pMemClasses );
    FREE( p->pPatScores );
    FREE( p->pPatWords );
    FREE( p->pSimWords );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Prints stats for the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ManPrint( Fra_Man_t * p )
{
    double nMemory = 1.0*Dar_ManObjIdMax(p->pManAig)*((p->nSimWords+2)*sizeof(unsigned)+6*sizeof(void*))/(1<<20);
    printf( "SimWords = %d. Rounds = %d. Mem = %0.2f Mb.  ", p->nSimWords, p->nSimRounds, nMemory );
    printf( "Classes: Beg = %d. End = %d.\n", p->nClassesBeg, p->nClassesEnd );
    printf( "Limits: BTNode = %d. BTMiter = %d.\n", p->pPars->nBTLimitNode, p->pPars->nBTLimitMiter );
    printf( "Proof = %d. Counter-example = %d. Fail = %d. FailReal = %d. Zero = %d.\n", 
        p->nSatProof, p->nSatCallsSat, p->nSatFails, p->nSatFailsReal, p->nClassesZero );
    printf( "Final = %d. Miter = %d. Total = %d. Mux = %d. (Exor = %d.) SatVars = %d.\n", 
        Dar_ManNodeNum(p->pManFraig), p->nNodesMiter, Dar_ManNodeNum(p->pManAig), 0, 0, p->nSatVars );
    if ( p->pSat ) Sat_SolverPrintStats( stdout, p->pSat );
    PRT( "AIG simulation  ", p->timeSim  );
    PRT( "AIG traversal   ", p->timeTrav  );
    PRT( "SAT solving     ", p->timeSat   );
    PRT( "    Unsat       ", p->timeSatUnsat );
    PRT( "    Sat         ", p->timeSatSat   );
    PRT( "    Fail        ", p->timeSatFail  );
    PRT( "Class refining  ", p->timeRef   );
    PRT( "TOTAL RUNTIME   ", p->timeTotal );
    if ( p->time1 ) { PRT( "time1           ", p->time1 ); }
    printf( "Speculations = %d.\n", p->nSpeculs );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


