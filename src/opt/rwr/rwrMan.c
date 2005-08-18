/**CFile****************************************************************

  FileName    [rwrMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    [Rewriting manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the following practical NPN classes of 4-variable functions were computed
// by considering all 4-input cuts appearing in IWLS, MCNC, and ISCAS benchmarks
#define RWR_NUM_CLASSES  135
static int s_PracticalClasses[RWR_NUM_CLASSES] = {
    0x0000, 0x0001, 0x0003, 0x0006, 0x0007, 0x000f, 0x0016, 0x0017, 0x0018, 0x0019, 0x001b, 
    0x001e, 0x001f, 0x003c, 0x003d, 0x003f, 0x0069, 0x006b, 0x006f, 0x007e, 0x007f, 0x00ff, 
    0x0116, 0x0118, 0x0119, 0x011a, 0x011b, 0x011e, 0x011f, 0x012c, 0x012d, 0x012f, 0x013c, 
    0x013d, 0x013e, 0x013f, 0x0168, 0x0169, 0x016f, 0x017f, 0x0180, 0x0181, 0x0182, 0x0183, 
    0x0186, 0x0189, 0x018b, 0x018f, 0x0198, 0x0199, 0x019b, 0x01a8, 0x01a9, 0x01aa, 0x01ab, 
    0x01ac, 0x01ad, 0x01ae, 0x01af, 0x01bf, 0x01e9, 0x01ea, 0x01eb, 0x01ee, 0x01ef, 0x01fe, 
    0x033c, 0x033d, 0x033f, 0x0356, 0x0357, 0x0358, 0x0359, 0x035a, 0x035b, 0x035f, 0x0368, 
    0x0369, 0x036c, 0x036e, 0x037d, 0x03c0, 0x03c1, 0x03c3, 0x03c7, 0x03cf, 0x03d4, 0x03d5, 
    0x03d7, 0x03d8, 0x03d9, 0x03dc, 0x03dd, 0x03de, 0x03fc, 0x0660, 0x0661, 0x0666, 0x0669, 
    0x066f, 0x0676, 0x067e, 0x0690, 0x0696, 0x0697, 0x069f, 0x06b1, 0x06b6, 0x06f0, 0x06f2, 
    0x06f6, 0x06f9, 0x0776, 0x0778, 0x07b0, 0x07b1, 0x07b4, 0x07bc, 0x07f0, 0x07f2, 0x07f8, 
    0x0ff0, 0x1683, 0x1696, 0x1698, 0x169e, 0x16e9, 0x178e, 0x17e8, 0x18e7, 0x19e6, 0x1be4, 
    0x1ee1, 0x3cc3, 0x6996 
};

static unsigned short  Rwr_FunctionPerm( unsigned uTruth, int Phase );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rwr_Man_t * Rwr_ManStart( char * pFileName )
{
    Rwr_Man_t * p;
    int i, k, nClasses;
    int clk = clock();
    int TableSize;

    p = ALLOC( Rwr_Man_t, 1 );
    memset( p, 0, sizeof(Rwr_Man_t) );
    p->nFuncs    = (1<<16);
    // create the table
    TableSize = pFileName? 222: (1<<16);
    p->pTable = ALLOC( Rwr_Node_t *, TableSize );
    memset( p->pTable, 0, sizeof(Rwr_Node_t *) * TableSize );
    // canonical forms, phases, perms
    Extra_Truth4VarNPN( &p->puCanons, &p->pPhases, &p->pPerms );
    // initialize practical classes
    p->pPractical  = ALLOC( char, p->nFuncs );
    memset( p->pPractical, 0, sizeof(char) * p->nFuncs );
    for ( i = 0; i < RWR_NUM_CLASSES; i++ )
        p->pPractical[ s_PracticalClasses[i] ] = 1;
    // set the mapping of classes
    nClasses = 0;
    p->pMap = ALLOC( unsigned char, p->nFuncs );
    for ( i = 0; i < p->nFuncs; i++ )
    {
        if ( i != p->puCanons[i] )
        {
            assert( i > p->puCanons[i] );
            p->pMap[i] = p->pMap[p->puCanons[i]];
            continue;
        }
        p->pMap[i] = nClasses++;
    }
    printf( "The number of NPN-canonical forms = %d.\n", nClasses );

    // initialize permutations
    for ( i = 0; i < 256; i++ )
        for ( k = 0; k < 16; k++ )
            p->puPerms[i][k] = Rwr_FunctionPerm( i, k );

    // other stuff
    p->nTravIds = 1;
    p->vForest  = Vec_PtrAlloc( 100 );
    p->vForm    = Vec_IntAlloc( 50 );
    p->vFanins  = Vec_PtrAlloc( 50 );
    p->vTfo     = Vec_PtrAlloc( 50 );
    p->vTfoFor  = Vec_PtrAlloc( 50 );
    p->vLevels  = Vec_VecAlloc( 50 );
    p->pMmNode  = Extra_MmFixedStart( sizeof(Rwr_Node_t) );
    assert( sizeof(Rwr_Node_t) == sizeof(Rwr_Cut_t) );

    // initialize forest
    Rwr_ManAddVar( p, 0x0000, pFileName ); // constant 0
    Rwr_ManAddVar( p, 0xAAAA, pFileName ); // var A
    Rwr_ManAddVar( p, 0xCCCC, pFileName ); // var B
    Rwr_ManAddVar( p, 0xF0F0, pFileName ); // var C
    Rwr_ManAddVar( p, 0xFF00, pFileName ); // var D
    p->nClasses = 5;
PRT( "Manager startup time", clock() - clk ); 

    // create the nodes
    if ( pFileName == NULL )
    {   // precompute
        Rwr_ManPrecompute( p );
        Rwr_ManWriteToFile( p, "data.aaa" );
        Rwr_ManPrintFirst( p );
    }
    else
    {   // load previously saved nodes
        Rwr_ManLoadFromFile( p, pFileName );
        Rwr_ManPrintNext( p );
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManStop( Rwr_Man_t * p )
{
    if ( p->vFanNums )  Vec_IntFree( p->vFanNums );
    if ( p->vReqTimes ) Vec_IntFree( p->vReqTimes );
    Vec_IntFree( p->vForm );
    Vec_PtrFree( p->vFanins );
    Vec_PtrFree( p->vTfoFor );
    Vec_PtrFree( p->vTfo );
    Vec_VecFree( p->vLevels );
    Vec_PtrFree( p->vForest );
    Extra_MmFixedStop( p->pMmNode,   0 );
    free( p->pPractical );
    free( p->puCanons );
    free( p->pPhases );
    free( p->pPerms );
    free( p->pMap );
    free( p->pTable );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Assigns elementary cuts to the PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManPrepareNetwork( Rwr_Man_t * p, Abc_Ntk_t * pNtk )
{
    // save the fanout counters for all internal nodes
    p->vFanNums = Rwt_NtkFanoutCounters( pNtk );
    // precompute the required times for all internal nodes
    p->vReqTimes = Abc_NtkGetRequiredLevels( pNtk );
    // start the cut computation
    Rwr_NtkStartCuts( p, pNtk );
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Rwr_ManReadFanins( Rwr_Man_t * p )
{
    return p->vFanins;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Rwr_ManReadDecs( Rwr_Man_t * p )
{
    return p->vForm;
}

/**Function*************************************************************

  Synopsis    [Computes a phase of the 3-var function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned short Rwr_FunctionPerm( unsigned uTruth, int Phase )
{
    static int Perm[16][4] = {
        { 0, 1, 2, 3 }, // 0000  - skip
        { 0, 1, 2, 3 }, // 0001  - skip
        { 1, 0, 2, 3 }, // 0010
        { 0, 1, 2, 3 }, // 0011  - skip
        { 2, 1, 0, 3 }, // 0100
        { 0, 2, 1, 3 }, // 0101
        { 2, 0, 1, 3 }, // 0110
        { 0, 1, 2, 3 }, // 0111  - skip
        { 3, 1, 2, 0 }, // 1000
        { 0, 3, 2, 1 }, // 1001
        { 3, 0, 2, 1 }, // 1010
        { 0, 1, 3, 2 }, // 1011
        { 2, 3, 0, 1 }, // 1100
        { 0, 3, 1, 2 }, // 1101
        { 3, 0, 1, 2 }, // 1110
        { 0, 1, 2, 3 }  // 1111  - skip
    };
    int i, k, iRes;
    unsigned uTruthRes;
    assert( Phase < 16 );
    uTruthRes = 0;
    for ( i = 0; i < 16; i++ )
        if ( uTruth & (1 << i) )
        {
            for ( iRes = 0, k = 0; k < 4; k++ )
                if ( i & (1 << k) )
                    iRes |= (1 << Perm[Phase][k]);
            uTruthRes |= (1 << iRes);
        }
    return uTruthRes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


