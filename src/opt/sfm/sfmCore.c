/**CFile****************************************************************

  FileName    [sfmCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_ParSetDefault( Sfm_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Sfm_Par_t) );
    pPars->nTfoLevMax   =    2;  // the maximum fanout levels
    pPars->nFanoutMax   =   10;  // the maximum number of fanouts
    pPars->nDepthMax    =    0;  // the maximum depth to try  
    pPars->nDivNumMax   =  200;  // the maximum number of divisors
    pPars->nWinSizeMax  =  500;  // the maximum window size
    pPars->nBTLimit     =    0;  // the maximum number of conflicts in one SAT run
    pPars->fFixLevel    =    0;  // does not allow level to increase
    pPars->fArea        =    0;  // performs optimization for area
    pPars->fMoreEffort  =    0;  // performs high-affort minimization
    pPars->fVerbose     =    0;  // enable basic stats
    pPars->fVeryVerbose =    0;  // enable detailed stats
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkPrintStats( Sfm_Ntk_t * p )
{
    printf( "Attempts :  " );
    printf( "Remove %5d (%6.2f%%)  ", p->nRemoves, 100.0*p->nRemoves/p->nTryRemoves );
    printf( "Resub  %5d (%6.2f%%)  ", p->nResubs,  100.0*p->nResubs /p->nTryResubs  );
    printf( "\n" );

    printf( "Reduction:  " );
    printf( "Nodes  %5d (%6.2f%%)  ", p->nTotalNodesBeg-p->nTotalNodesEnd, 100.0*(p->nTotalNodesBeg-p->nTotalNodesEnd)/p->nTotalNodesBeg );
    printf( "Edges  %5d (%6.2f%%)  ", p->nTotalEdgesBeg-p->nTotalEdgesEnd, 100.0*(p->nTotalEdgesBeg-p->nTotalEdgesEnd)/p->nTotalEdgesBeg );
    printf( "\n" );

    ABC_PRTP( "Win", p->timeWin  ,  p->timeTotal );
    ABC_PRTP( "Div", p->timeDiv  ,  p->timeTotal );
    ABC_PRTP( "Cnf", p->timeCnf  ,  p->timeTotal );
    ABC_PRTP( "Sat", p->timeSat  ,  p->timeTotal );
    ABC_PRTP( "ALL", p->timeTotal,  p->timeTotal );
}

/**Function*************************************************************

  Synopsis    [Performs resubstitution for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_NodeResubSolve( Sfm_Ntk_t * p, int iNode, int f, int fRemoveOnly )
{
    int fSkipUpdate  = 1;
    int fVeryVerbose = p->pPars->fVeryVerbose && Vec_IntSize(p->vDivs) < 200;// || pNode->Id == 556;
    int i, iFanin, iVar = -1;
    word uTruth, uSign, uMask;
    clock_t clk;
    assert( Sfm_ObjIsNode(p, iNode) );
    assert( f >= 0 && f < Sfm_ObjFaninNum(p, iNode) );
    if ( fRemoveOnly )
        p->nTryRemoves++;
    else
        p->nTryResubs++;
    // report init stats
    if ( p->pPars->fVeryVerbose )
        printf( "Node %5d : Level = %2d. Divs = %3d.  Fanin = %d (out of %d). MFFC = %d\n", 
            iNode, Sfm_ObjLevel(p, iNode), Vec_IntSize(p->vDivs), f, Sfm_ObjFaninNum(p, iNode), 
            Sfm_ObjFanoutNum(p, Sfm_ObjFanin(p, iNode, f)) == 1 ? Sfm_ObjMffcSize(p, iNode) : 0 );
    // clean simulation info
    p->nCexes = 0;
    Vec_WrdFill( p->vDivCexes, Vec_IntSize(p->vDivs), 0 );
    // try removing the critical fanin
clk = clock();
    Vec_IntClear( p->vDivIds );
    Sfm_ObjForEachFanin( p, iNode, iFanin, i )
        if ( i != f )
            Vec_IntPush( p->vDivIds, Sfm_ObjSatVar(p, iFanin) );
    uTruth = Sfm_ComputeInterpolant( p );
p->timeSat += clock() - clk;
    // analyze outcomes
    if ( uTruth == SFM_SAT_UNDEC )
        return 0;
    if ( uTruth == SFM_SAT_SAT )
        goto finish;
    if ( fRemoveOnly )
        return 0;
    if ( fVeryVerbose )
    {
        for ( i = 0; i < 9; i++ )
            printf( " " );
        for ( i = 0; i < Vec_IntSize(p->vDivs); i++ )
            printf( "%d", i % 10 );
        printf( "\n" );
    }
    while ( 1 ) 
    {
        if ( fVeryVerbose )
        {
            printf( "%3d: %3d ", p->nCexes, iVar );
            Vec_WrdForEachEntry( p->vDivCexes, uSign, i )
                printf( "%d", Abc_InfoHasBit((unsigned *)&uSign, p->nCexes-1) );
            printf( "\n" );
        }
        // find the next divisor to try
        uMask = (~(word)0) >> (64 - p->nCexes);
        Vec_WrdForEachEntry( p->vDivCexes, uSign, iVar )
            if ( uSign == uMask )
                break;
        if ( iVar == Vec_IntSize(p->vDivs) )
            return 0;
        // try replacing the critical fanin
clk = clock();
        Vec_IntPush( p->vDivIds, Sfm_ObjSatVar(p, Vec_IntEntry(p->vDivs, iVar)) );
        uTruth = Sfm_ComputeInterpolant( p );
p->timeSat += clock() - clk;
        // analyze outcomes
        if ( uTruth == SFM_SAT_UNDEC )
            return 0;
        if ( uTruth == SFM_SAT_SAT )
            goto finish;
        if ( p->nCexes == 64 )
            return 0;
        // remove the last variable
        Vec_IntPop( p->vDivIds );
    }
finish:
    if ( p->pPars->fVeryVerbose )
    {
        if ( iVar == -1 )
            printf( "Node %d: Fanin %d can be removed.  ", iNode, f );
        else
            printf( "Node %d: Fanin %d can be replaced by divisor %d.   ", iNode, f, iVar );
        Kit_DsdPrintFromTruth( (unsigned *)&uTruth, Vec_IntSize(p->vDivIds) ); printf( "\n" );
    }
    if ( iVar == -1 )
        p->nRemoves++;
    else
        p->nResubs++;
    if ( fSkipUpdate )
        return 1;
    // update the network
    Sfm_NtkUpdate( p, iNode, f, (iVar == -1 ? iVar : Vec_IntEntry(p->vDivs, iVar)), uTruth );
    return 1;
 }
int Sfm_NodeResub( Sfm_Ntk_t * p, int iNode )
{
    int i, iFanin;
    // prepare SAT solver
    Sfm_NtkCreateWindow( p, iNode, p->pPars->fVeryVerbose );
    Sfm_NtkWindowToSolver( p );
    Sfm_NtkPrepareDivisors( p, iNode );
    // try replacing area critical fanins
    Sfm_ObjForEachFanin( p, iNode, iFanin, i )
        if ( Sfm_ObjIsNode(p, iFanin) && Sfm_ObjFanoutNum(p, iFanin) == 1 )
        {
            if ( Sfm_NodeResubSolve( p, iNode, i, 0 ) )
                return 1;
        }
    // try removing redundant edges
    Sfm_ObjForEachFanin( p, iNode, iFanin, i )
        if ( !(Sfm_ObjIsNode(p, iFanin) && Sfm_ObjFanoutNum(p, iFanin) == 1) )
        {
            if ( Sfm_NodeResubSolve( p, iNode, i, 1 ) )
                return 1;
        }
/*
    // try replacing area critical fanins while adding two new fanins
    if ( Sfm_ObjFaninNum(p, iNode) < p->nFaninMax )
        Abc_ObjForEachFanin( pNode, pFanin, i )
            if ( !Abc_ObjIsCi(pFanin) && Abc_ObjFanoutNum(pFanin) == 1 )
            {
                if ( Abc_NtkMfsSolveSatResub2( p, pNode, i, -1 ) )
                    return 1;
            }
*/
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_NtkPerform( Sfm_Ntk_t * p, Sfm_Par_t * pPars )
{
    int i;
    p->timeTotal = clock();
    p->pPars = pPars;
    Sfm_NtkPrepare( p );
    p->nTotalNodesBeg = Vec_WecSizeUsed(&p->vFanins) - Sfm_NtkPoNum(p);
    p->nTotalEdgesBeg = Vec_WecSizeSize(&p->vFanins);
    Sfm_NtkForEachNode( p, i )
    {
        if ( p->pPars->nDepthMax && Sfm_ObjLevel(p, i) > p->pPars->nDepthMax )
            continue;
        if ( Sfm_ObjFaninNum(p, i) < 2 || Sfm_ObjFaninNum(p, i) > 6 )
            continue;
        Sfm_NodeResub( p, i );
    }
    p->nTotalNodesEnd = Vec_WecSizeUsed(&p->vFanins) - Sfm_NtkPoNum(p);
    p->nTotalEdgesEnd = Vec_WecSizeSize(&p->vFanins);
    p->timeTotal = clock() - p->timeTotal;
    if ( pPars->fVerbose )
        Sfm_NtkPrintStats( p );
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

