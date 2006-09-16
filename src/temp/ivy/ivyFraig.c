/**CFile****************************************************************

  FileName    [ivyFraig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Functional reduction of AIGs]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyFraig.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"
#include "satSolver.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ivy_Fraig_t_        Ivy_Fraig_t;
struct Ivy_Fraig_t_
{
    // general info 
    Ivy_FraigParams_t * pParams;        // various parameters
    // AIG manager
    Ivy_Man_t *         pManAig;        // the starting AIG manager
    Ivy_Man_t *         pManFraig;      // the final AIG manager
    // simulation information
    int                 nWords;         // the number of words
    unsigned *          pWords;         // the simulation info
    // counter example storage
    int                 nPatWords;      // the number of words in the counter example
    unsigned *          pPatWords;      // the counter example
    // equivalence classes 
    int                 nClasses;       // the number of equivalence classes
    Ivy_Obj_t *         pClassesHead;   // the linked list of classes
    Ivy_Obj_t *         pClassesTail;   // the linked list of classes
    // equivalence checking
    sat_solver *        pSat;           // SAT solver
    int                 nSatVars;       // the number of variables currently used
    // statistics
    int                 nSimRounds;
    int                 nClassesZero;
    int                 nClassesBeg;
    int                 nClassesEnd;
    int                 nSatCalls;
    int                 nSatCallsSat;
    int                 nSatCallsUnsat;
    int                 nSatProof;
    int                 nSatFails;
    int                 nSatFailsReal;
    // runtime
    int                 timeSim;
    int                 timeTrav;
    int                 timeSat;
    int                 timeRef;
    int                 timeTotal;
};

static inline unsigned *  Ivy_ObjSim( Ivy_Obj_t * pObj )                                 { return (unsigned *)pObj->pFanout;  }
static inline Ivy_Obj_t * Ivy_ObjClassNodeLast( Ivy_Obj_t * pObj )                       { return pObj->pNextFan0;  }
static inline Ivy_Obj_t * Ivy_ObjClassNodeRepr( Ivy_Obj_t * pObj )                       { return pObj->pNextFan0;  }
static inline Ivy_Obj_t * Ivy_ObjClassNodeNext( Ivy_Obj_t * pObj )                       { return pObj->pNextFan1;  }
static inline Ivy_Obj_t * Ivy_ObjNodeHashNext( Ivy_Obj_t * pObj )                        { return pObj->pPrevFan0;  }
static inline Ivy_Obj_t * Ivy_ObjEquivListNext( Ivy_Obj_t * pObj )                       { return pObj->pPrevFan0;  }
static inline Ivy_Obj_t * Ivy_ObjEquivListPrev( Ivy_Obj_t * pObj )                       { return pObj->pPrevFan1;  }
static inline Ivy_Obj_t * Ivy_ObjFraig( Ivy_Obj_t * pObj )                               { return pObj->pEquiv;     }
static inline int         Ivy_ObjSatNum( Ivy_Obj_t * pObj )                              { return (int)pObj->pNextFan0;         }
static inline Vec_Ptr_t * Ivy_ObjFaninVec( Ivy_Obj_t * pObj )                            { return (Vec_Ptr_t *)pObj->pNextFan1; }

static inline void        Ivy_ObjSetSim( Ivy_Obj_t * pObj, unsigned * pSim )             { pObj->pFanout = (Ivy_Obj_t *)pSim; }
static inline void        Ivy_ObjSetClassNodeLast( Ivy_Obj_t * pObj, Ivy_Obj_t * pLast ) { pObj->pNextFan0 = pLast; }
static inline void        Ivy_ObjSetClassNodeRepr( Ivy_Obj_t * pObj, Ivy_Obj_t * pRepr ) { pObj->pNextFan0 = pRepr; }
static inline void        Ivy_ObjSetClassNodeNext( Ivy_Obj_t * pObj, Ivy_Obj_t * pNext ) { pObj->pNextFan1 = pNext; }
static inline void        Ivy_ObjSetNodeHashNext( Ivy_Obj_t * pObj, Ivy_Obj_t * pNext )  { pObj->pPrevFan0 = pNext; }
static inline void        Ivy_ObjSetEquivListNext( Ivy_Obj_t * pObj, Ivy_Obj_t * pNext ) { pObj->pPrevFan0 = pNext; }
static inline void        Ivy_ObjSetEquivListPrev( Ivy_Obj_t * pObj, Ivy_Obj_t * pPrev ) { pObj->pPrevFan1 = pPrev; }
static inline void        Ivy_ObjSetFraig( Ivy_Obj_t * pObj, Ivy_Obj_t * pNode )         { pObj->pEquiv    = pNode; }
static inline void        Ivy_ObjSetSatNum( Ivy_Obj_t * pObj, int Num )                  { pObj->pNextFan0 = (Ivy_Obj_t *)Num;     }
static inline void        Ivy_ObjSetFaninVec( Ivy_Obj_t * pObj, Vec_Ptr_t * vFanins )    { pObj->pNextFan1 = (Ivy_Obj_t *)vFanins; }

static inline unsigned    Ivy_ObjRandomSim()                       { return (rand() << 24) ^ (rand() << 12) ^ rand(); }

// iterate through equivalence classes
#define Ivy_FraigForEachEquivClass( pList, pEnt )                 \
    for ( pEnt = pList;                                           \
          pEnt;                                                   \
          pEnt = Ivy_ObjEquivListNext(pEnt) )
#define Ivy_FraigForEachEquivClassSafe( pList, pEnt, pEnt2 )      \
    for ( pEnt = pList,                                           \
          pEnt2 = pEnt? Ivy_ObjEquivListNext(pEnt): NULL;         \
          pEnt;                                                   \
          pEnt = pEnt2,                                           \
          pEnt2 = pEnt? Ivy_ObjEquivListNext(pEnt): NULL )
// iterate through nodes in one class
#define Ivy_FraigForEachClassNode( pClass, pEnt )                 \
    for ( pEnt = pClass;                                          \
          pEnt;                                                   \
          pEnt = Ivy_ObjClassNodeNext(pEnt) )
#define Ivy_FraigForEachClassNodeSafe( pClass, pEnt, pEnt2 )      \
    for ( pEnt = pClass,                                          \
          pEnt2 = pEnt? Ivy_ObjClassNodeNext(pEnt): NULL;         \
          pEnt;                                                   \
          pEnt = pEnt2,                                           \
          pEnt2 = pEnt? Ivy_ObjClassNodeNext(pEnt): NULL )
// iterate through nodes in the hash table
#define Ivy_FraigForEachBinNode( pBin, pEnt )                     \
    for ( pEnt = pBin;                                            \
          pEnt;                                                   \
          pEnt = Ivy_ObjNodeHashNext(pEnt) )
#define Ivy_FraigForEachBinNodeSafe( pBin, pEnt, pEnt2 )          \
    for ( pEnt = pBin,                                            \
          pEnt2 = pEnt? Ivy_ObjNodeHashNext(pEnt): NULL;          \
          pEnt;                                                   \
          pEnt = pEnt2,                                           \
          pEnt2 = pEnt? Ivy_ObjNodeHashNext(pEnt): NULL )

static Ivy_Fraig_t * Ivy_FraigStart( Ivy_Man_t * pManAig, Ivy_FraigParams_t * pParams );
static void          Ivy_FraigPrint( Ivy_Fraig_t * p );
static void          Ivy_FraigStop( Ivy_Fraig_t * p );
static void          Ivy_FraigSimulate( Ivy_Fraig_t * p );
static void          Ivy_FraigSweep( Ivy_Fraig_t * p );
static Ivy_Obj_t *   Ivy_FraigAnd( Ivy_Fraig_t * p, Ivy_Obj_t * pObjOld );
static int           Ivy_FraigNodesAreEquiv( Ivy_Fraig_t * p, Ivy_Obj_t * pObj0, Ivy_Obj_t * pObj1, int nBTLimit );
static void          Ivy_FraigNodeAddToSolver( Ivy_Fraig_t * p, Ivy_Obj_t * pObj0, Ivy_Obj_t * pObj1 );
static int           Ivy_FraigMarkConeSetActivity_rec( Ivy_Fraig_t * p, Ivy_Obj_t * pObj, int * pTravIds, int TravId, double * pFactors, int LevelMax );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs fraiging of the initial AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Man_t * Ivy_FraigPerform( Ivy_Man_t * pManAig, Ivy_FraigParams_t * pParams )
{
    Ivy_Fraig_t * p;
    Ivy_Man_t * pManAigNew;
    int clk;
clk = clock();
    assert( Ivy_ManLatchNum(pManAig) == 0 );
    p = Ivy_FraigStart( pManAig, pParams );
    Ivy_FraigSimulate( p );
    Ivy_FraigSweep( p );
    pManAigNew = p->pManFraig;
p->timeTotal = clock() - clk;
    Ivy_FraigStop( p );
    return pManAigNew;
}

/**Function*************************************************************

  Synopsis    [Performs fraiging of the initial AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigParamsDefault( Ivy_FraigParams_t * pParams )
{
    memset( pParams, 0, sizeof(Ivy_FraigParams_t) );
    pParams->nSimWords =     32;
    pParams->SimSatur  =  0.005;
}

/**Function*************************************************************

  Synopsis    [Starts the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Fraig_t * Ivy_FraigStart( Ivy_Man_t * pManAig, Ivy_FraigParams_t * pParams )
{
    Ivy_Fraig_t * p;
    Ivy_Obj_t * pObj;
    int i, k;
    // clean the fanout representation
    Ivy_ManForEachObj( pManAig, pObj, i )
//        pObj->pEquiv = pObj->pFanout = pObj->pNextFan0 = pObj->pNextFan1 = pObj->pPrevFan0 = pObj->pPrevFan1 = NULL;
        assert( !pObj->pEquiv && !pObj->pFanout );
    // allocat the fraiging manager
    p = ALLOC( Ivy_Fraig_t, 1 );
    memset( p, 0, sizeof(Ivy_Fraig_t) );
    p->pParams   = pParams;
    p->pManAig   = pManAig;
    p->pManFraig = Ivy_ManStartFrom( pManAig );
    // allocate simulation info
    p->nWords    = pParams->nSimWords;
    p->pWords    = ALLOC( unsigned, Ivy_ManObjNum(pManAig) * p->nWords ); 
    k = 0;
    Ivy_ManForEachObj( pManAig, pObj, i )
        Ivy_ObjSetSim( pObj, p->pWords + p->nWords * k++ );
    assert( k == Ivy_ManObjNum(pManAig) );
    // allocate storage for sim pattern
    p->nPatWords = Ivy_BitWordNum( Ivy_ManPiNum(pManAig) );
    p->pPatWords = ALLOC( unsigned, p->nPatWords ); 
    // set random number generator
    srand( 0xABCABC );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigPrint( Ivy_Fraig_t * p )
{
    double nMemory;
    nMemory = (double)Ivy_ManObjNum(p->pManAig)*p->nWords*sizeof(unsigned)/(1<<20);
    printf( "SimWords = %d. Rounds = %d. Mem = %0.2f Mb.  ", p->nWords, p->nSimRounds, nMemory );
    printf( "Classes: Beg = %d. End = %d.\n", p->nClassesBeg, p->nClassesEnd );
    printf( "Proof = %d. Counter-example = %d. Fail = %d. FailReal = %d. Zero = %d.\n", 
        p->nSatProof, p->nSatCallsSat, p->nSatFails, p->nSatFailsReal, p->nClassesZero );
    printf( "Nodes: Final = %d. Total = %d. Mux = %d. (Exor = %d.) SatVars = %d.\n", 
        Ivy_ManNodeNum(p->pManFraig), Ivy_ManNodeNum(p->pManAig), 0, 0, p->nSatVars );
    if ( p->pSat ) Sat_SolverPrintStats( stdout, p->pSat );
    PRT( "AIG simulation  ", p->timeSim  );
    PRT( "AIG traversal   ", p->timeTrav  );
    PRT( "SAT solving     ", p->timeSat   );
    PRT( "Class refining  ", p->timeRef   );
    PRT( "TOTAL RUNTIME   ", p->timeTotal );
}

/**Function*************************************************************

  Synopsis    [Stops the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigStop( Ivy_Fraig_t * p )
{
    Ivy_FraigPrint( p );
    if ( p->pSat ) sat_solver_delete( p->pSat );
    free( p->pPatWords );
    free( p->pWords );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Simulates one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_NodeAssignRandom( Ivy_Fraig_t * p, Ivy_Obj_t * pObj )
{
    unsigned * pSims;
    int i;
    pSims = Ivy_ObjSim(pObj);
    for ( i = 0; i < p->nWords; i++ )
        pSims[i] = Ivy_ObjRandomSim();
}

/**Function*************************************************************

  Synopsis    [Simulates one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_NodeAssignConst( Ivy_Fraig_t * p, Ivy_Obj_t * pObj, int fConst1 )
{
    unsigned * pSims;
    int i;
    pSims = Ivy_ObjSim(pObj);
    for ( i = 0; i < p->nWords; i++ )
        pSims[i] = fConst1? ~(unsigned)0 : 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if simulation info is composed of all zeros.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_NodeHasZeroSim( Ivy_Fraig_t * p, Ivy_Obj_t * pObj )
{
    unsigned * pSims;
    int i;
    pSims = Ivy_ObjSim(pObj);
    for ( i = 0; i < p->nWords; i++ )
        if ( pSims[i] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if simulation infos are equal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_NodeCompareSims( Ivy_Fraig_t * p, Ivy_Obj_t * pObj0, Ivy_Obj_t * pObj1 )
{
    unsigned * pSims0, * pSims1;
    int i;
    pSims0 = Ivy_ObjSim(pObj0);
    pSims1 = Ivy_ObjSim(pObj1);
    for ( i = 0; i < p->nWords; i++ )
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
void Ivy_NodeSimulate( Ivy_Fraig_t * p, Ivy_Obj_t * pObj )
{
    unsigned * pSims, * pSims0, * pSims1;
    int fCompl, fCompl0, fCompl1, i;
    assert( !Ivy_IsComplement(pObj) );
    // get hold of the simulation information
    pSims  = Ivy_ObjSim(pObj);
    pSims0 = Ivy_ObjSim(Ivy_ObjFanin0(pObj));
    pSims1 = Ivy_ObjSim(Ivy_ObjFanin1(pObj));
    // get complemented attributes of the children using their random info
    fCompl  = pObj->fPhase;
    fCompl0 = Ivy_ObjFaninPhase(Ivy_ObjChild0(pObj));
    fCompl1 = Ivy_ObjFaninPhase(Ivy_ObjChild1(pObj));
    // simulate
    if ( fCompl0 && fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < p->nWords; i++ )
                pSims[i] = (pSims0[i] | pSims1[i]);
        else
            for ( i = 0; i < p->nWords; i++ )
                pSims[i] = ~(pSims0[i] | pSims1[i]);
    }
    else if ( fCompl0 && !fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < p->nWords; i++ )
                pSims[i] = (pSims0[i] | ~pSims1[i]);
        else
            for ( i = 0; i < p->nWords; i++ )
                pSims[i] = (~pSims0[i] & pSims1[i]);
    }
    else if ( !fCompl0 && fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < p->nWords; i++ )
                pSims[i] = (~pSims0[i] | pSims1[i]);
        else
            for ( i = 0; i < p->nWords; i++ )
                pSims[i] = (pSims0[i] & ~pSims1[i]);
    }
    else // if ( !fCompl0 && !fCompl1 )
    {
        if ( fCompl )
            for ( i = 0; i < p->nWords; i++ )
                pSims[i] = ~(pSims0[i] & pSims1[i]);
        else
            for ( i = 0; i < p->nWords; i++ )
                pSims[i] = (pSims0[i] & pSims1[i]);
    }
}

/**Function*************************************************************

  Synopsis    [Computes hash value using simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Ivy_NodeHash( Ivy_Fraig_t * p, Ivy_Obj_t * pObj )
{
    static int s_FPrimes[128] = { 
        1009, 1049, 1093, 1151, 1201, 1249, 1297, 1361, 1427, 1459, 
        1499, 1559, 1607, 1657, 1709, 1759, 1823, 1877, 1933, 1997, 
        2039, 2089, 2141, 2213, 2269, 2311, 2371, 2411, 2467, 2543, 
        2609, 2663, 2699, 2741, 2797, 2851, 2909, 2969, 3037, 3089, 
        3169, 3221, 3299, 3331, 3389, 3461, 3517, 3557, 3613, 3671, 
        3719, 3779, 3847, 3907, 3943, 4013, 4073, 4129, 4201, 4243, 
        4289, 4363, 4441, 4493, 4549, 4621, 4663, 4729, 4793, 4871, 
        4933, 4973, 5021, 5087, 5153, 5227, 5281, 5351, 5417, 5471, 
        5519, 5573, 5651, 5693, 5749, 5821, 5861, 5923, 6011, 6073, 
        6131, 6199, 6257, 6301, 6353, 6397, 6481, 6563, 6619, 6689, 
        6737, 6803, 6863, 6917, 6977, 7027, 7109, 7187, 7237, 7309, 
        7393, 7477, 7523, 7561, 7607, 7681, 7727, 7817, 7877, 7933, 
        8011, 8039, 8059, 8081, 8093, 8111, 8123, 8147
    };
    unsigned uHash, * pSims;
    int i;
    assert( p->nWords <= 128 );
    uHash = 0;
    pSims  = Ivy_ObjSim(pObj);
    for ( i = 0; i < p->nWords; i++ )
        uHash ^= pSims[i] * s_FPrimes[i];
    return uHash;
}

/**Function*************************************************************

  Synopsis    [Simulates AIG manager.]

  Description [Assumes that the PI simulation info is attached.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigSimulateOne( Ivy_Fraig_t * p )
{
    Ivy_Obj_t * pObj;
    int i, clk;
clk = clock();
    Ivy_ManForEachNode( p->pManAig, pObj, i )
    {
        Ivy_NodeSimulate( p, pObj );
/*
        if ( Ivy_ObjFraig(pObj) == NULL )
            printf( "%3d --- -- %d  :  ", pObj->Id, pObj->fPhase );
        else
            printf( "%3d %3d %2d %d  :  ", pObj->Id, Ivy_Regular(Ivy_ObjFraig(pObj))->Id, Ivy_ObjSatNum(Ivy_Regular(Ivy_ObjFraig(pObj))), pObj->fPhase );
        Extra_PrintBinary( stdout, Ivy_ObjSim(pObj), 30 );
        printf( "\n" );
*/
    }
p->timeSim += clock() - clk;
p->nSimRounds++;
}

/**Function*************************************************************

  Synopsis    [Simulates AIG manager.]

  Description [Assumes that the PI simulation info is attached.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigAssignRandom( Ivy_Fraig_t * p )
{
    Ivy_Obj_t * pObj;
    int i;
    Ivy_ManForEachPi( p->pManAig, pObj, i )
        Ivy_NodeAssignRandom( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Simulates AIG manager.]

  Description [Assumes that the PI simulation info is attached.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigAssignDist1( Ivy_Fraig_t * p, unsigned * pPat )
{
    Ivy_Obj_t * pObj;
    int i, Limit;
    Ivy_ManForEachPi( p->pManAig, pObj, i )
        Ivy_NodeAssignConst( p, pObj, Ivy_InfoHasBit(pPat, i) );
    Limit = IVY_MIN( Ivy_ManPiNum(p->pManAig), p->nWords * 32 - 1 );
    for ( i = 0; i < Limit; i++ )
        Ivy_InfoXorBit( Ivy_ObjSim( Ivy_ManPi(p->pManAig,i) ), i+1 );
/*
    for ( i = 0; i < Limit; i++ )
        Extra_PrintBinary( stdout, Ivy_ObjSim( Ivy_ManPi(p->pManAig,i) ), 30 ), printf( "\n" );
*/
}

/**Function*************************************************************

  Synopsis    [Adds new nodes to the equivalence class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_NodeAddToClass( Ivy_Obj_t * pClass, Ivy_Obj_t * pObj )
{
    if ( Ivy_ObjClassNodeNext(pClass) == NULL )
        Ivy_ObjSetClassNodeNext( pClass, pObj );
    else
        Ivy_ObjSetClassNodeNext( Ivy_ObjClassNodeLast(pClass), pObj );
    Ivy_ObjSetClassNodeLast( pClass, pObj );
    Ivy_ObjSetClassNodeRepr( pObj, pClass );
    Ivy_ObjSetClassNodeNext( pObj, NULL );
}

/**Function*************************************************************

  Synopsis    [Adds new nodes to the equivalence class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigAddClass( Ivy_Fraig_t * p, Ivy_Obj_t * pClass )
{
    if ( p->pClassesHead == NULL )
    {
        p->pClassesHead = pClass;
        p->pClassesTail = pClass;
        Ivy_ObjSetEquivListPrev( pClass, NULL );
        Ivy_ObjSetEquivListNext( pClass, NULL ); 
    }
    else
    {
        Ivy_ObjSetEquivListNext( p->pClassesTail, pClass ); 
        Ivy_ObjSetEquivListPrev( pClass, p->pClassesTail );
        Ivy_ObjSetEquivListNext( pClass, NULL ); 
        p->pClassesTail = pClass;
    }
    p->nClasses++;
}
 
/**Function*************************************************************

  Synopsis    [Updates the list of classes after base class has split.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigInsertClass( Ivy_Fraig_t * p, Ivy_Obj_t * pBase, Ivy_Obj_t * pClass )
{
    Ivy_ObjSetEquivListPrev( pClass, pBase );
    Ivy_ObjSetEquivListNext( pClass, Ivy_ObjEquivListNext(pBase) ); 
    if ( Ivy_ObjEquivListNext(pBase) )
        Ivy_ObjSetEquivListPrev( Ivy_ObjEquivListNext(pBase), pClass );
    Ivy_ObjSetEquivListNext( pBase, pClass ); 
    if ( p->pClassesTail == pBase )
        p->pClassesTail = pClass;
    p->nClasses++;
}

/**Function*************************************************************

  Synopsis    [Updates the list of classes after base class has split.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigRemoveClass( Ivy_Fraig_t * p, Ivy_Obj_t * pClass )
{
    if ( p->pClassesHead == pClass )
        p->pClassesHead = Ivy_ObjEquivListNext(pClass);
    if ( p->pClassesTail == pClass )
        p->pClassesTail = Ivy_ObjEquivListPrev(pClass);
    if ( Ivy_ObjEquivListPrev(pClass) )
        Ivy_ObjSetEquivListNext( Ivy_ObjEquivListPrev(pClass), Ivy_ObjEquivListNext(pClass) ); 
    if ( Ivy_ObjEquivListNext(pClass) )
        Ivy_ObjSetEquivListPrev( Ivy_ObjEquivListNext(pClass), Ivy_ObjEquivListPrev(pClass) );
    Ivy_ObjSetEquivListNext( pClass, NULL ); 
    Ivy_ObjSetEquivListPrev( pClass, NULL );
    p->nClasses--;
}

/**Function*************************************************************

  Synopsis    [Creates initial simulation classes.]

  Description [Assumes that simulation info is assigned.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigCreateClasses( Ivy_Fraig_t * p )
{
    Ivy_Obj_t ** pTable;
    Ivy_Obj_t * pObj, * pConst1, * pBin, * pEntry, * pEntry2;
    int i, nTableSize;
    unsigned Hash;
    pConst1 = Ivy_ManConst1(p->pManAig);
    // allocate the table
    nTableSize = Ivy_ManObjNum(p->pManAig) / 2 + 13;
    pTable = ALLOC( Ivy_Obj_t *, nTableSize ); 
    memset( pTable, 0, sizeof(Ivy_Obj_t *) * nTableSize );
    // collect nodes into the table
    Ivy_ManForEachObj( p->pManAig, pObj, i )
    {
        if ( !Ivy_ObjIsPi(pObj) && !Ivy_ObjIsNode(pObj) )
            continue;
        Hash = Ivy_NodeHash( p, pObj );
        if ( Hash == 0 && Ivy_NodeHasZeroSim( p, pObj ) )
        {
            Ivy_NodeAddToClass( pConst1, pObj );
            continue;
        }
        // add the node to the table
        pBin = pTable[Hash % nTableSize];
        Ivy_FraigForEachBinNode( pBin, pEntry )
            if ( Ivy_NodeCompareSims( p, pEntry, pObj ) )
            {
                Ivy_NodeAddToClass( pEntry, pObj );
                break;
            }
        // check if the entry was added
        if ( pEntry )
            continue;
        Ivy_ObjSetNodeHashNext( pObj, pBin );
        pTable[Hash % nTableSize] = pObj;
    }
    // collect non-trivial classes
    assert( p->pClassesHead == NULL );
    if ( Ivy_ObjClassNodeNext(pConst1) )
    {
        Ivy_FraigAddClass( p, pConst1 );
        Ivy_ObjSetClassNodeLast( pConst1, NULL );
    }
    for ( i = 0; i < nTableSize; i++ )
        Ivy_FraigForEachBinNodeSafe( pTable[i], pEntry, pEntry2 )
            if ( Ivy_ObjClassNodeNext(pEntry) )
            {
                Ivy_FraigAddClass( p, pEntry );
                Ivy_ObjSetClassNodeLast( pEntry, NULL );
            }
            else
                Ivy_ObjSetNodeHashNext( pEntry, NULL );
    // free the table
    free( pTable );
}

/**Function*************************************************************

  Synopsis    [Recursively refines the class after simulation.]

  Description [Returns 1 if the class has changed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_FraigRefineClass_rec( Ivy_Fraig_t * p, Ivy_Obj_t * pClass )
{
    Ivy_Obj_t * pClassNew, * pListOld, * pListNew, * pNode;
    // check if there is refinement
    pListOld = pClass;
    Ivy_FraigForEachClassNode( Ivy_ObjClassNodeNext(pClass), pClassNew )
    {
        if ( !Ivy_NodeCompareSims(p, pClass, pClassNew) )
            break;
        pListOld = pClassNew;
    }
    if ( pClassNew == NULL )
        return 0;
    // set representative of the new class
    Ivy_ObjSetClassNodeRepr( pClassNew, NULL );
    // start the new list
    pListNew = pClassNew;
    // go through the remaining nodes and sort them into two groups:
    // (1) matches of the old node; (2) non-matches of the old node
    Ivy_FraigForEachClassNode( Ivy_ObjClassNodeNext(pClassNew), pNode )
        if ( Ivy_NodeCompareSims( p, pClass, pNode ) )
        {
            Ivy_ObjSetClassNodeNext( pListOld, pNode );
            pListOld = pNode;
        }
        else
        {
            Ivy_ObjSetClassNodeNext( pListNew, pNode );
            Ivy_ObjSetClassNodeRepr( pNode, pClassNew );
            pListNew = pNode;
        }
    // finish both lists
    Ivy_ObjSetClassNodeNext( pListNew, NULL );
    Ivy_ObjSetClassNodeNext( pListOld, NULL );
    // update the list of classes
    Ivy_FraigInsertClass( p, pClass, pClassNew );
    // if the old class is trivial, remove it
    if ( Ivy_ObjClassNodeNext(pClass) == NULL )
        Ivy_FraigRemoveClass( p, pClass );
    // if the new class is trivial, remove it; otherwise, try to refine it
    if ( Ivy_ObjClassNodeNext(pClassNew) == NULL )
        Ivy_FraigRemoveClass( p, pClassNew );
    else
        Ivy_FraigRefineClass_rec( p, pClassNew );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Refines the classes after simulation.]

  Description [Assumes that simulation info is assigned. Returns the
  number of classes refined.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_FraigRefineClasses( Ivy_Fraig_t * p )
{
    Ivy_Obj_t * pClass, * pClass2;
    int clk, RetValue = 0;
clk = clock();
    Ivy_FraigForEachEquivClassSafe( p->pClassesHead, pClass, pClass2 )
        RetValue += Ivy_FraigRefineClass_rec( p, pClass );
p->timeRef += clock() - clk;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Print the class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigPrintClass( Ivy_Obj_t * pClass )
{
    Ivy_Obj_t * pObj;
    printf( "Class {" );
    Ivy_FraigForEachClassNode( pClass, pObj )
        printf( " %d(%d)%c", pObj->Id, pObj->Level, pObj->fPhase? '+' : '-' );
    printf( " }\n" );
}

/**Function*************************************************************

  Synopsis    [Count the number of elements in the class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_FraigCountClassNodes( Ivy_Obj_t * pClass )
{
    Ivy_Obj_t * pObj;
    int Counter = 0;
    Ivy_FraigForEachClassNode( pClass, pObj )
        Counter++;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Stops the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_FraigCountClasses( Ivy_Fraig_t * p )
{
    Ivy_Obj_t * pClass;
    int Counter = 0;
    Ivy_FraigForEachEquivClass( p->pClassesHead, pClass )
        Counter++;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Stops the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigPrintSimClasses( Ivy_Fraig_t * p )
{
    Ivy_Obj_t * pClass;
    Ivy_FraigForEachEquivClass( p->pClassesHead, pClass )
    {
//        Ivy_FraigPrintClass( pClass );
        printf( "%d ", Ivy_FraigCountClassNodes( pClass ) );
    }
//    printf( "\n" );
}


/**Function*************************************************************

  Synopsis    [Stops the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigSimulate( Ivy_Fraig_t * p )
{
    int nChanges, nClasses;
    Ivy_FraigAssignRandom( p );
    Ivy_FraigSimulateOne( p );
    Ivy_FraigCreateClasses( p );
//printf( "Starting classes = %5d.\n", p->nClasses );
    do {
        Ivy_FraigAssignRandom( p );
        Ivy_FraigSimulateOne( p );
        nClasses = p->nClasses;
        nChanges = Ivy_FraigRefineClasses( p );
//printf( "Refined classes  = %5d.   Changes = %4d.\n", p->nClasses, nChanges );
    } while ( (double)nChanges / nClasses > p->pParams->SimSatur );
//    Ivy_FraigPrintSimClasses( p );
}

/**Function*************************************************************

  Synopsis    [Stops the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigResimulate( Ivy_Fraig_t * p )
{
    int nChanges;
    Ivy_FraigAssignDist1( p, p->pPatWords );
    Ivy_FraigSimulateOne( p );
    nChanges = Ivy_FraigRefineClasses( p );
    assert( nChanges >= 1 );
//printf( "Refined classes! = %5d.   Changes = %4d.\n", p->nClasses, nChanges );
}


/**Function*************************************************************

  Synopsis    [Performs fraiging for the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigSweep( Ivy_Fraig_t * p )
{
    Ivy_Obj_t * pObj;
    int i;
p->nClassesZero = Ivy_ObjIsConst1(p->pClassesHead) ? Ivy_FraigCountClassNodes(p->pClassesHead) : 0;
p->nClassesBeg  = Ivy_FraigCountClasses(p);
    // duplicate internal nodes
    Ivy_ManForEachNode( p->pManAig, pObj, i )
        pObj->pEquiv = Ivy_FraigAnd( p, pObj );
p->nClassesEnd = Ivy_FraigCountClasses(p);
    // add the POs
    Ivy_ManForEachPo( p->pManAig, pObj, i )
        Ivy_ObjCreatePo( p->pManFraig, Ivy_ObjChild0Equiv(pObj) );
    // clean the old manager
    Ivy_ManForEachObj( p->pManAig, pObj, i )
        pObj->pFanout = pObj->pNextFan0 = pObj->pNextFan1 = pObj->pPrevFan0 = pObj->pPrevFan1 = NULL;
    // clean the new manager
    Ivy_ManForEachObj( p->pManFraig, pObj, i )
    {
        if ( Ivy_ObjFaninVec(pObj) )
            Vec_PtrFree( Ivy_ObjFaninVec(pObj) );
        pObj->pNextFan0 = pObj->pNextFan1 = NULL;
    }
    // remove dangling nodes 
    Ivy_ManCleanup( p->pManFraig );
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for one node.]

  Description [Returns the fraiged node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_FraigAnd( Ivy_Fraig_t * p, Ivy_Obj_t * pObjOld )
{
    Ivy_Obj_t * pObjNew, * pFanin0New, * pFanin1New, * pObjReprNew;
    int RetValue;
    // get the fraiged fanins
    pFanin0New = Ivy_ObjChild0Equiv(pObjOld);
    pFanin1New = Ivy_ObjChild1Equiv(pObjOld);
    // get the candidate fraig node
    pObjNew = Ivy_And( p->pManFraig, pFanin0New, pFanin1New );
    // get representative of this class
    if ( Ivy_ObjClassNodeRepr(pObjOld) == NULL ) // this is a unique node
    {
        assert( Ivy_Regular(pFanin0New) != Ivy_Regular(pFanin1New) );
        assert( pObjNew != Ivy_Regular(pFanin0New) );
        assert( pObjNew != Ivy_Regular(pFanin1New) );
        return pObjNew;
    }
    // get the fraiged representative
    pObjReprNew = Ivy_ObjFraig(Ivy_ObjClassNodeRepr(pObjOld));
    // if the fraiged nodes are the same return
    if ( Ivy_Regular(pObjNew) == Ivy_Regular(pObjReprNew) )
        return pObjNew;
    // they are different (the counter-example is in p->pPatWords)
    RetValue = Ivy_FraigNodesAreEquiv( p, Ivy_Regular(pObjReprNew), Ivy_Regular(pObjNew), 1000 );
    if ( RetValue == 1 )  // proved equivalent
        return Ivy_NotCond( pObjReprNew, pObjOld->fPhase ^ Ivy_ObjClassNodeRepr(pObjOld)->fPhase );
    if ( RetValue == -1 ) // failed
        return pObjNew;
    // simulate the counter-example and return the new node
    Ivy_FraigResimulate( p );
    return pObjNew;
}

/**Function*************************************************************

  Synopsis    [Copy pattern from the solver into the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigSavePattern( Ivy_Fraig_t * p )
{
    Ivy_Obj_t * pObj;
    int i;
    memset( p->pPatWords, 0, sizeof(unsigned) * p->nPatWords );
    Ivy_ManForEachPi( p->pManFraig, pObj, i )
        if ( p->pSat->model.ptr[Ivy_ObjSatNum(pObj)] == l_True )
            Ivy_InfoSetBit( p->pPatWords, i );
/*
    // print sat variables
    for ( i = 0; i < p->nSatVars; i++ )
        printf( "%d=%d ", i, p->pSat->model.ptr[i] );
    printf( "\n" );
*/
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for one node.]

  Description [Returns the fraiged node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_FraigNodesAreEquiv( Ivy_Fraig_t * p, Ivy_Obj_t * pOld, Ivy_Obj_t * pNew, int nBTLimit )
{
    int pLits[4], RetValue, RetValue1, clk, Counter;

//    printf( "Trying to prove nodes %d and %d\n", pOld->Id, pNew->Id );

    // make sure the nodes are not complemented
    assert( !Ivy_IsComplement(pNew) );
    assert( !Ivy_IsComplement(pOld) );
    assert( pNew != pOld );

    // if at least one of the nodes is a failed node, perform adjustments:
    // if the backtrack limit is small, simply skip this node
    // if the backtrack limit is > 10, take the quare root of the limit
    if ( nBTLimit > 0 && (pOld->fFailTfo || pNew->fFailTfo) )
    {
        p->nSatFails++;
        if ( nBTLimit <= 10 )
            return -1;
        nBTLimit = (int)sqrt(nBTLimit);
    }
    p->nSatCalls++;

    // make sure the solver is allocated and has enough variables
    if ( p->pSat == NULL )
    {
        p->pSat = sat_solver_new();
        p->nSatVars = 1;
        sat_solver_setnvars( p->pSat, 1000 );
    }

    // if the nodes do not have SAT variables, allocate them
    Ivy_FraigNodeAddToSolver( p, pOld, pNew );

    // prepare variable activity
clk = clock();
    Ivy_ManIncrementTravId( p->pManFraig );
    Counter  = Ivy_FraigMarkConeSetActivity_rec( p, pOld, NULL, 0, NULL, 0 );
    Counter += Ivy_FraigMarkConeSetActivity_rec( p, pNew, NULL, 0, NULL, 0 );
//    printf( "%d ", Counter );
p->timeTrav += clock() - clk;


    // solve under assumptions
    // A = 1; B = 0     OR     A = 1; B = 1 
clk = clock();
    pLits[0] = toLitCond( Ivy_ObjSatNum(pOld), 0 );
    pLits[1] = toLitCond( Ivy_ObjSatNum(pNew), pOld->fPhase == pNew->fPhase );
//Sat_SolverWriteDimacs( p->pSat, "temp.cnf", pLits, pLits + 2, 1 );
    RetValue1 = sat_solver_solve( p->pSat, pLits, pLits + 2 );
p->timeSat += clock() - clk;
    if ( RetValue1 == l_False )
    {
        pLits[0] = lit_neg( pLits[0] );
        pLits[1] = lit_neg( pLits[1] );
        RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 2 );
        assert( RetValue );
        // continue solving the other implication
        p->nSatCallsUnsat++;
    }
    else if ( RetValue1 == l_True )
    {
        Ivy_FraigSavePattern( p );
        p->nSatCallsSat++;
        return 0;
    }
    else // if ( RetValue1 == l_Undef )
    {
        // mark the node as the failed node
        if ( pOld != p->pManFraig->pConst1 ) 
            pOld->fFailTfo = 1;
        pNew->fFailTfo = 1;
        p->nSatFailsReal++;
        return -1;
    }

    // if the old node was constant 0, we already know the answer
    if ( pOld == p->pManFraig->pConst1 )
    {
        p->nSatProof++;
        return 1;
    }

    // solve under assumptions
    // A = 0; B = 1     OR     A = 0; B = 0 
clk = clock();
    pLits[0] = toLitCond( Ivy_ObjSatNum(pOld), 1 );
    pLits[1] = toLitCond( Ivy_ObjSatNum(pNew), pOld->fPhase ^ pNew->fPhase );
    RetValue1 = sat_solver_solve( p->pSat, pLits, pLits + 2 );
p->timeSat += clock() - clk;
    if ( RetValue1 == l_False )
    {
        pLits[0] = lit_neg( pLits[0] );
        pLits[1] = lit_neg( pLits[1] );
        RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 2 );
        assert( RetValue );
        p->nSatCallsUnsat++;
    }
    else if ( RetValue1 == l_True )
    {
        Ivy_FraigSavePattern( p );
        p->nSatCallsSat++;
        return 0;
    }
    else // if ( RetValue1 == l_Undef )
    {
        // mark the node as the failed node
        pOld->fFailTfo = 1;
        pNew->fFailTfo = 1;
        p->nSatFailsReal++;
        return -1;
    }

    // return SAT proof
    p->nSatProof++;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Addes clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigAddClausesMux( Ivy_Fraig_t * p, Ivy_Obj_t * pNode )
{
    Ivy_Obj_t * pNodeI, * pNodeT, * pNodeE;
    int pLits[4], RetValue, VarF, VarI, VarT, VarE, fCompT, fCompE;

    assert( !Ivy_IsComplement( pNode ) );
    assert( Ivy_ObjIsMuxType( pNode ) );
    // get nodes (I = if, T = then, E = else)
    pNodeI = Ivy_ObjRecognizeMux( pNode, &pNodeT, &pNodeE );
    // get the variable numbers
    VarF = Ivy_ObjSatNum(pNode);
    VarI = Ivy_ObjSatNum(pNodeI);
    VarT = Ivy_ObjSatNum(Ivy_Regular(pNodeT));
    VarE = Ivy_ObjSatNum(Ivy_Regular(pNodeE));
    // get the complementation flags
    fCompT = Ivy_IsComplement(pNodeT);
    fCompE = Ivy_IsComplement(pNodeE);

    // f = ITE(i, t, e)

    // i' + t' + f
    // i' + t  + f'
    // i  + e' + f
    // i  + e  + f'

    // create four clauses
    pLits[0] = toLitCond(VarI, 1);
    pLits[1] = toLitCond(VarT, 1^fCompT);
    pLits[2] = toLitCond(VarF, 0);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarI, 1);
    pLits[1] = toLitCond(VarT, 0^fCompT);
    pLits[2] = toLitCond(VarF, 1);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarI, 0);
    pLits[1] = toLitCond(VarE, 1^fCompE);
    pLits[2] = toLitCond(VarF, 0);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarI, 0);
    pLits[1] = toLitCond(VarE, 0^fCompE);
    pLits[2] = toLitCond(VarF, 1);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );

    // two additional clauses
    // t' & e' -> f'
    // t  & e  -> f 

    // t  + e   + f'
    // t' + e'  + f 

    if ( VarT == VarE )
    {
//        assert( fCompT == !fCompE );
        return;
    }

    pLits[0] = toLitCond(VarT, 0^fCompT);
    pLits[1] = toLitCond(VarE, 0^fCompE);
    pLits[2] = toLitCond(VarF, 1);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarT, 1^fCompT);
    pLits[1] = toLitCond(VarE, 1^fCompE);
    pLits[2] = toLitCond(VarF, 0);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
}

/**Function*************************************************************

  Synopsis    [Addes clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigAddClausesSuper( Ivy_Fraig_t * p, Ivy_Obj_t * pNode, Vec_Ptr_t * vSuper )
{
    Ivy_Obj_t * pFanin;
    int * pLits, nLits, RetValue, i;
    assert( !Ivy_IsComplement(pNode) );
    assert( Ivy_ObjIsNode( pNode ) );
    // create storage for literals
    nLits = Vec_PtrSize(vSuper) + 1;
    pLits = ALLOC( int, nLits );
    // suppose AND-gate is A & B = C
    // add !A => !C   or   A + !C
    Vec_PtrForEachEntry( vSuper, pFanin, i )
    {
        pLits[0] = toLitCond(Ivy_ObjSatNum(Ivy_Regular(pFanin)), Ivy_IsComplement(pFanin));
        pLits[1] = toLitCond(Ivy_ObjSatNum(pNode), 1);
        RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 2 );
        assert( RetValue );
    }
    // add A & B => C   or   !A + !B + C
    Vec_PtrForEachEntry( vSuper, pFanin, i )
        pLits[i] = toLitCond(Ivy_ObjSatNum(Ivy_Regular(pFanin)), !Ivy_IsComplement(pFanin));
    pLits[nLits-1] = toLitCond(Ivy_ObjSatNum(pNode), 0);
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + nLits );
    assert( RetValue );
    free( pLits );
}

/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigCollectSuper_rec( Ivy_Obj_t * pObj, Vec_Ptr_t * vSuper, int fFirst, int fUseMuxes )
{
    // if the new node is complemented or a PI, another gate begins
    if ( Ivy_IsComplement(pObj) || Ivy_ObjIsPi(pObj) || (!fFirst && Ivy_ObjRefs(pObj) > 1) || 
         (fUseMuxes && Ivy_ObjIsMuxType(pObj)) )
    {
        Vec_PtrPushUnique( vSuper, pObj );
        return;
    }
    // go through the branches
    Ivy_FraigCollectSuper_rec( Ivy_ObjChild0(pObj), vSuper, 0, fUseMuxes );
    Ivy_FraigCollectSuper_rec( Ivy_ObjChild1(pObj), vSuper, 0, fUseMuxes );
}

/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ivy_FraigCollectSuper( Ivy_Obj_t * pObj, int fUseMuxes )
{
    Vec_Ptr_t * vSuper;
    assert( !Ivy_IsComplement(pObj) );
    assert( !Ivy_ObjIsPi(pObj) );
    vSuper = Vec_PtrAlloc( 4 );
    Ivy_FraigCollectSuper_rec( pObj, vSuper, 1, fUseMuxes );
    return vSuper;
}

/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigObjAddToFrontier( Ivy_Fraig_t * p, Ivy_Obj_t * pObj, Vec_Ptr_t * vFrontier )
{
    assert( !Ivy_IsComplement(pObj) );
    if ( Ivy_ObjSatNum(pObj) )
        return;
    assert( Ivy_ObjSatNum(pObj) == 0 );
    assert( Ivy_ObjFaninVec(pObj) == NULL );
    if ( Ivy_ObjIsConst1(pObj) )
        return;
//printf( "Assigning node %d number %d\n", pObj->Id, p->nSatVars );
    Ivy_ObjSetSatNum( pObj, p->nSatVars++ );
    if ( Ivy_ObjIsNode(pObj) )
        Vec_PtrPush( vFrontier, pObj );
}

/**Function*************************************************************

  Synopsis    [Addes clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_FraigNodeAddToSolver( Ivy_Fraig_t * p, Ivy_Obj_t * pOld, Ivy_Obj_t * pNew )
{
    Vec_Ptr_t * vFrontier, * vFanins;
    Ivy_Obj_t * pNode, * pFanin;
    int i, k, fUseMuxes = 1;
    // quit if CNF is ready
    if ( Ivy_ObjFaninVec(pOld) && Ivy_ObjFaninVec(pNew) )
        return;
    // start the frontier
    vFrontier = Vec_PtrAlloc( 100 );
    Ivy_FraigObjAddToFrontier( p, pOld, vFrontier );
    Ivy_FraigObjAddToFrontier( p, pNew, vFrontier );
    // explore nodes in the frontier
    Vec_PtrForEachEntry( vFrontier, pNode, i )
    {
        // create the supergate
        assert( Ivy_ObjSatNum(pNode) );
        assert( Ivy_ObjFaninVec(pNode) == NULL );
        if ( fUseMuxes && Ivy_ObjIsMuxType(pNode) )
        {
            vFanins = Vec_PtrAlloc( 4 );
            Vec_PtrPushUnique( vFanins, Ivy_ObjFanin0( Ivy_ObjFanin0(pNode) ) );
            Vec_PtrPushUnique( vFanins, Ivy_ObjFanin0( Ivy_ObjFanin1(pNode) ) );
            Vec_PtrPushUnique( vFanins, Ivy_ObjFanin1( Ivy_ObjFanin0(pNode) ) );
            Vec_PtrPushUnique( vFanins, Ivy_ObjFanin1( Ivy_ObjFanin1(pNode) ) );
            Vec_PtrForEachEntry( vFanins, pFanin, k )
                Ivy_FraigObjAddToFrontier( p, Ivy_Regular(pFanin), vFrontier );
            Ivy_FraigAddClausesMux( p, pNode );
        }
        else
        {
            vFanins = Ivy_FraigCollectSuper( pNode, fUseMuxes );
            Vec_PtrForEachEntry( vFanins, pFanin, k )
                Ivy_FraigObjAddToFrontier( p, Ivy_Regular(pFanin), vFrontier );
            Ivy_FraigAddClausesSuper( p, pNode, vFanins );
        }
        assert( Vec_PtrSize(vFanins) > 1 );
        Ivy_ObjSetFaninVec( pNode, vFanins );
    }
    Vec_PtrFree( vFrontier );
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for one node.]

  Description [Returns the fraiged node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_FraigMarkConeSetActivity_rec( Ivy_Fraig_t * p, Ivy_Obj_t * pObj, int * pTravIds, int TravId, double * pFactors, int LevelMax )
{
    Vec_Ptr_t * vFanins;
    Ivy_Obj_t * pFanin;
    int i, Counter;
    assert( !Ivy_IsComplement(pObj) );
    if ( Ivy_ObjIsConst1(pObj) )
        return 0;
    assert( Ivy_ObjSatNum(pObj) );
//    if ( pTravIds[Ivy_ObjSatNum(pObj)] == TravId )
//        return;
//    pTravIds[Ivy_ObjSatNum(pObj)] = TravId;
//    pFactors[Ivy_ObjSatNum(pObj)] = pow( 0.97, LevelMax - pObj->Level );
    if ( Ivy_ObjIsTravIdCurrent(p->pManFraig, pObj) )
        return 0;
    Ivy_ObjSetTravIdCurrent(p->pManFraig, pObj);
    if ( Ivy_ObjIsPi(pObj) )
        return 0;

    vFanins = Ivy_ObjFaninVec( pObj );
    Counter = 1;
    Vec_PtrForEachEntry( vFanins, pFanin, i )
        Counter += Ivy_FraigMarkConeSetActivity_rec( p, Ivy_Regular(pFanin), pTravIds, TravId, pFactors, LevelMax );
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


