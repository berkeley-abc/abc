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
#include "main.h"
#include "dec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts rewriting manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rwr_Man_t * Rwr_ManStart( bool fPrecompute )
{
    Dec_Man_t * pManDec;
    Rwr_Man_t * p;
    int clk = clock();
clk = clock();
    p = ALLOC( Rwr_Man_t, 1 );
    memset( p, 0, sizeof(Rwr_Man_t) );
    p->nFuncs = (1<<16);
    pManDec   = Abc_FrameReadManDec(Abc_FrameGetGlobalFrame());
    p->puCanons = pManDec->puCanons; 
    p->pPhases  = pManDec->pPhases; 
    p->pPerms   = pManDec->pPerms; 
    p->pMap     = pManDec->pMap; 
    // initialize practical NPN classes
    p->pPractical  = Rwr_ManGetPractical( p );
    // create the table
    p->pTable = ALLOC( Rwr_Node_t *, p->nFuncs );
    memset( p->pTable, 0, sizeof(Rwr_Node_t *) * p->nFuncs );
    // create the elementary nodes
    p->pMmNode  = Extra_MmFixedStart( sizeof(Rwr_Node_t) );
    p->vForest  = Vec_PtrAlloc( 100 );
    Rwr_ManAddVar( p, 0x0000, fPrecompute ); // constant 0
    Rwr_ManAddVar( p, 0xAAAA, fPrecompute ); // var A
    Rwr_ManAddVar( p, 0xCCCC, fPrecompute ); // var B
    Rwr_ManAddVar( p, 0xF0F0, fPrecompute ); // var C
    Rwr_ManAddVar( p, 0xFF00, fPrecompute ); // var D
    p->nClasses = 5;
    // other stuff
    p->nTravIds   = 1;
    p->pPerms4    = Extra_Permutations( 4 );
    p->vLevNums   = Vec_IntAlloc( 50 );
    p->vFanins    = Vec_PtrAlloc( 50 );
    p->vFaninsCur = Vec_PtrAlloc( 50 );
    if ( fPrecompute )
    {   // precompute subgraphs
        Rwr_ManPrecompute( p );
//        Rwr_ManPrint( p );
        Rwr_ManWriteToArray( p );
    }
    else
    {   // load saved subgraphs
        Rwr_ManLoadFromArray( p, 0 );
//        Rwr_ManPrint( p );
        Rwr_ManPreprocess( p );
    }
p->timeStart = clock() - clk;
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops rewriting manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManStop( Rwr_Man_t * p )
{
    if ( p->vClasses )
    {
        Rwr_Node_t * pNode;
        int i, k;
        Vec_VecForEachEntry( p->vClasses, pNode, i, k )
            Dec_GraphFree( (Dec_Graph_t *)pNode->pNext );
    }
    if ( p->vClasses )  Vec_VecFree( p->vClasses );
    Vec_PtrFree( p->vForest );
    Vec_IntFree( p->vLevNums );
    Vec_PtrFree( p->vFanins );
    Vec_PtrFree( p->vFaninsCur );
    Extra_MmFixedStop( p->pMmNode, 0 );
    free( p->pTable );
    free( p->pPractical );
    free( p->pPerms4 );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManPrintStats( Rwr_Man_t * p )
{
    int i, Counter = 0;
    for ( i = 0; i < 222; i++ )
        Counter += (p->nScores[i] > 0);

    printf( "Rewriting statistics:\n" );
    printf( "Total cuts tries  = %8d.\n", p->nCutsGood );
    printf( "Bad cuts found    = %8d.\n", p->nCutsBad );
    printf( "Total subgraphs   = %8d.\n", p->nSubgraphs );
    printf( "Used NPN classes  = %8d.\n", Counter );
    printf( "Nodes considered  = %8d.\n", p->nNodesConsidered );
    printf( "Nodes rewritten   = %8d.\n", p->nNodesRewritten );
    printf( "Calculated gain   = %8d.\n", p->nNodesGained     );
    PRT( "Start       ", p->timeStart );
    PRT( "Cuts        ", p->timeCut );
    PRT( "Resynthesis ", p->timeRes );
    PRT( "    Eval    ", p->timeEval );
    PRT( "TOTAL       ", p->timeTotal );

/*
    printf( "The scores are : " );
    for ( i = 0; i < 222; i++ )
        if ( p->nScores[i] > 0 )
            printf( "%d=%d ", i, p->nScores[i] );
    printf( "\n" );
*/
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Rwr_ManReadDecs( Rwr_Man_t * p )
{
    return p->pGraph;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rwr_ManReadCompl( Rwr_Man_t * p )
{
    return p->fCompl;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManAddTimeCuts( Rwr_Man_t * p, int Time )
{
    p->timeCut += Time;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManAddTimeTotal( Rwr_Man_t * p, int Time )
{
    p->timeTotal += Time;
}


/**Function*************************************************************

  Synopsis    [Precomputes AIG subgraphs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_Precompute()
{
    Rwr_Man_t * p;
    p = Rwr_ManStart( 1 );
    Rwr_ManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


