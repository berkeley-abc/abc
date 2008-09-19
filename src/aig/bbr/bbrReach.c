/**CFile****************************************************************

  FileName    [bbrReach.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [BDD-based reachability analysis.]

  Synopsis    [Procedures to perform reachability analysis.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bbrReach.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bbr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern void * Aig_ManVerifyUsingBddsCountExample( Aig_Man_t * p, DdManager * dd, 
    DdNode ** pbParts, Vec_Ptr_t * vOnionRings, DdNode * bCubeFirst, 
    int iOutput, int fVerbose, int fSilent );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function********************************************************************

  Synopsis    [Performs the reordering-sensitive step of Extra_bddMove().]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
DdNode * Bbr_bddComputeRangeCube( DdManager * dd, int iStart, int iStop )
{
    DdNode * bTemp, * bProd;
    int i;
    assert( iStart <= iStop );
    assert( iStart >= 0 && iStart <= dd->size );
    assert( iStop >= 0  && iStop  <= dd->size );
    bProd = (dd)->one;         Cudd_Ref( bProd );
    for ( i = iStart; i < iStop; i++ )
    {
        bProd = Cudd_bddAnd( dd, bTemp = bProd, dd->vars[i] );      Cudd_Ref( bProd );
        Cudd_RecursiveDeref( dd, bTemp ); 
    }
    Cudd_Deref( bProd );
    return bProd;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bbr_StopManager( DdManager * dd )
{
    int RetValue;
    // check for remaining references in the package
    RetValue = Cudd_CheckZeroRef( dd );
    if ( RetValue > 0 )
        printf( "\nThe number of referenced nodes = %d\n\n", RetValue );
//  Cudd_PrintInfo( dd, stdout );
    Cudd_Quit( dd );
}

/**Function*************************************************************

  Synopsis    [Computes the initial state and sets up the variable map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Aig_ManInitStateVarMap( DdManager * dd, Aig_Man_t * p, int fVerbose )
{
    DdNode ** pbVarsX, ** pbVarsY;
    DdNode * bTemp, * bProd;
    Aig_Obj_t * pLatch;
    int i;

    // set the variable mapping for Cudd_bddVarMap()
    pbVarsX = ALLOC( DdNode *, dd->size );
    pbVarsY = ALLOC( DdNode *, dd->size );
    bProd = (dd)->one;         Cudd_Ref( bProd );
    Saig_ManForEachLo( p, pLatch, i )
    {
        pbVarsX[i] = dd->vars[ Saig_ManPiNum(p) + i ];
        pbVarsY[i] = dd->vars[ Saig_ManCiNum(p) + i ];
        // get the initial value of the latch
        bProd = Cudd_bddAnd( dd, bTemp = bProd, Cudd_Not(pbVarsX[i]) );      Cudd_Ref( bProd );
        Cudd_RecursiveDeref( dd, bTemp ); 
    }
    Cudd_SetVarMap( dd, pbVarsX, pbVarsY, Saig_ManRegNum(p) );
    FREE( pbVarsX );
    FREE( pbVarsY );

    Cudd_Deref( bProd );
    return bProd;
}

/**Function*************************************************************

  Synopsis    [Collects the array of output BDDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode ** Aig_ManCreateOutputs( DdManager * dd, Aig_Man_t * p )
{
    DdNode ** pbOutputs;
    Aig_Obj_t * pNode;
    int i;
    // compute the transition relation
    pbOutputs = ALLOC( DdNode *, Saig_ManPoNum(p) );
    Saig_ManForEachPo( p, pNode, i )
    {
        pbOutputs[i] = Aig_ObjGlobalBdd(pNode);  Cudd_Ref( pbOutputs[i] );
    }
    return pbOutputs;
}

/**Function*************************************************************

  Synopsis    [Collects the array of partition BDDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode ** Aig_ManCreatePartitions( DdManager * dd, Aig_Man_t * p, int fReorder, int fVerbose )
{
    DdNode ** pbParts;
    DdNode * bVar;
    Aig_Obj_t * pNode;
    int i;

    // extand the BDD manager to represent NS variables
    assert( dd->size == Saig_ManCiNum(p) );
    Cudd_bddIthVar( dd, Saig_ManCiNum(p) + Saig_ManRegNum(p) - 1 );

    // enable reordering
    if ( fReorder )
        Cudd_AutodynEnable( dd, CUDD_REORDER_SYMM_SIFT );
    else
        Cudd_AutodynDisable( dd );

    // compute the transition relation
    pbParts = ALLOC( DdNode *, Saig_ManRegNum(p) );
    Saig_ManForEachLi( p, pNode, i )
    {
        bVar  = Cudd_bddIthVar( dd, Saig_ManCiNum(p) + i );
        pbParts[i] = Cudd_bddXnor( dd, bVar, Aig_ObjGlobalBdd(pNode) );  Cudd_Ref( pbParts[i] );
    }
    // free global BDDs
    Aig_ManFreeGlobalBdds( p, dd );

    // reorder and disable reordering
    if ( fReorder )
    {
        if ( fVerbose )
            fprintf( stdout, "BDD nodes in the partitions before reordering %d.\n", Cudd_SharingSize(pbParts,Saig_ManRegNum(p)) );
        Cudd_ReduceHeap( dd, CUDD_REORDER_SYMM_SIFT, 100 );
        Cudd_AutodynDisable( dd );
        if ( fVerbose )
            fprintf( stdout, "BDD nodes in the partitions after reordering %d.\n", Cudd_SharingSize(pbParts,Saig_ManRegNum(p)) );
    }
    return pbParts;
}

/**Function*************************************************************

  Synopsis    [Computes the set of unreachable states.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManComputeReachable( DdManager * dd, Aig_Man_t * p, DdNode ** pbParts, DdNode * bInitial, DdNode ** pbOutputs, int nBddMax, int nIterMax, int fPartition, int fReorder, int fVerbose, int fSilent )
{
    int fInternalReorder = 0;
    Bbr_ImageTree_t * pTree = NULL; // Suppress "might be used uninitialized"
    Bbr_ImageTree2_t * pTree2 = NULL; // Supprses "might be used uninitialized"
    DdNode * bReached, * bCubeCs;
    DdNode * bCurrent;
    DdNode * bNext = NULL; // Suppress "might be used uninitialized"
    DdNode * bTemp;
    int i, nIters, nBddSize;
    int nThreshold = 10000;
    Vec_Ptr_t * vOnionRings;

    // start the onion rings
    vOnionRings = Vec_PtrAlloc( 1000 );

    // start the image computation
    bCubeCs  = Bbr_bddComputeRangeCube( dd, Saig_ManPiNum(p), Saig_ManCiNum(p) );    Cudd_Ref( bCubeCs );
    if ( fPartition )
        pTree = Bbr_bddImageStart( dd, bCubeCs, Saig_ManRegNum(p), pbParts, Saig_ManRegNum(p), dd->vars+Saig_ManCiNum(p), fVerbose );
    else
        pTree2 = Bbr_bddImageStart2( dd, bCubeCs, Saig_ManRegNum(p), pbParts, Saig_ManRegNum(p), dd->vars+Saig_ManCiNum(p), fVerbose );
    Cudd_RecursiveDeref( dd, bCubeCs );
    if ( pTree == NULL )
    {
        if ( !fSilent )
            printf( "BDDs blew up during qualitification scheduling.  " );
        return -1;
    }

    // perform reachability analisys
    bCurrent = bInitial;   Cudd_Ref( bCurrent );
    bReached = bInitial;   Cudd_Ref( bReached );
    Vec_PtrPush( vOnionRings, bCurrent );  Cudd_Ref( bCurrent );
    for ( nIters = 1; nIters <= nIterMax; nIters++ )
    { 
        // compute the next states
        if ( fPartition )
            bNext = Bbr_bddImageCompute( pTree, bCurrent );           
        else
            bNext = Bbr_bddImageCompute2( pTree2, bCurrent );  
        if ( bNext == NULL )
        {
            if ( !fSilent )
                printf( "BDDs blew up during image computation.  " );
            if ( fPartition )
                Bbr_bddImageTreeDelete( pTree );
            else
                Bbr_bddImageTreeDelete2( pTree2 );
            return -1;
        }
        Cudd_Ref( bNext );
        Cudd_RecursiveDeref( dd, bCurrent );
        // remap these states into the current state vars
        bNext = Cudd_bddVarMap( dd, bTemp = bNext );                    Cudd_Ref( bNext );
        Cudd_RecursiveDeref( dd, bTemp );
        // check if there are any new states
        if ( Cudd_bddLeq( dd, bNext, bReached ) )
            break;
        // check the BDD size
        nBddSize = Cudd_DagSize(bNext);
        if ( nBddSize > nBddMax )
            break;
        // check the result
        for ( i = 0; i < Saig_ManPoNum(p); i++ )
        {
            if ( !Cudd_bddLeq( dd, bNext, Cudd_Not(pbOutputs[i]) ) )
            {
                DdNode * bIntersect;
                bIntersect = Cudd_bddIntersect( dd, bNext, pbOutputs[i] );  Cudd_Ref( bIntersect );
                assert( p->pSeqModel == NULL );
                p->pSeqModel = Aig_ManVerifyUsingBddsCountExample( p, dd, pbParts, 
                    vOnionRings, bIntersect, i, fVerbose, fSilent ); 
                Cudd_RecursiveDeref( dd, bIntersect );
                if ( !fSilent )
                    printf( "Output %d was asserted in frame %d (use \"write_counter\" to dump a witness). ", i, Vec_PtrSize(vOnionRings) );
                Cudd_RecursiveDeref( dd, bReached );
                bReached = NULL;
                break;
            }
        }
        if ( i < Saig_ManPoNum(p) )
            break;
        // get the new states
        bCurrent = Cudd_bddAnd( dd, bNext, Cudd_Not(bReached) );        Cudd_Ref( bCurrent );
        Vec_PtrPush( vOnionRings, bCurrent );  Cudd_Ref( bCurrent );
        // minimize the new states with the reached states
//        bCurrent = Cudd_bddConstrain( dd, bTemp = bCurrent, Cudd_Not(bReached) ); Cudd_Ref( bCurrent );
//        Cudd_RecursiveDeref( dd, bTemp );
        // add to the reached states
        bReached = Cudd_bddOr( dd, bTemp = bReached, bNext );           Cudd_Ref( bReached );
        Cudd_RecursiveDeref( dd, bTemp );
        Cudd_RecursiveDeref( dd, bNext );
        if ( fVerbose )
            fprintf( stdout, "Frame = %3d. BDD = %5d. ", nIters, nBddSize );
        if ( fInternalReorder && fReorder && nBddSize > nThreshold )
        {
            if ( fVerbose )
                fprintf( stdout, "Reordering... Before = %5d. ", Cudd_DagSize(bReached) );
            Cudd_ReduceHeap( dd, CUDD_REORDER_SYMM_SIFT, 100 );
            Cudd_AutodynDisable( dd );
            if ( fVerbose )
                fprintf( stdout, "After = %5d.\r", Cudd_DagSize(bReached) );
            nThreshold *= 2;
        }
        if ( fVerbose )
            fprintf( stdout, "\r" );
    }
    Cudd_RecursiveDeref( dd, bNext );
    // free the onion rings
    Vec_PtrForEachEntry( vOnionRings, bTemp, i )
        Cudd_RecursiveDeref( dd, bTemp );
    Vec_PtrFree( vOnionRings );
    // undo the image tree
    if ( fPartition )
        Bbr_bddImageTreeDelete( pTree );
    else
        Bbr_bddImageTreeDelete2( pTree2 );
    if ( bReached == NULL )
        return 0; // proved reachable
    // report the stats
    if ( fVerbose )
    {
        double nMints = Cudd_CountMinterm(dd, bReached, Saig_ManRegNum(p) );
        if ( nIters > nIterMax || Cudd_DagSize(bReached) > nBddMax )
            fprintf( stdout, "Reachability analysis is stopped after %d frames.\n", nIters );
        else
            fprintf( stdout, "Reachability analysis completed after %d frames.\n", nIters );
        fprintf( stdout, "Reachable states = %.0f. (Ratio = %.4f %%)\n", nMints, 100.0*nMints/pow(2.0, Saig_ManRegNum(p)) );
        fflush( stdout );
    }
//PRB( dd, bReached );
    Cudd_RecursiveDeref( dd, bReached );
    if ( nIters > nIterMax || Cudd_DagSize(bReached) > nBddMax )
    {
        if ( !fSilent )
            printf( "Verified only for states reachable in %d frames.  ", nIters );
        return -1; // undecided
    }
    if ( !fSilent )
        printf( "The miter is proved unreachable after %d iterations.  ", nIters );
    return 1; // unreachable
}

/**Function*************************************************************

  Synopsis    [Performs reachability to see if any .]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManVerifyUsingBdds( Aig_Man_t * p, int nBddMax, int nIterMax, int fPartition, int fReorder, int fVerbose, int fSilent )
{
    DdManager * dd;
    DdNode ** pbParts, ** pbOutputs;
    DdNode * bInitial, * bTemp;
    int RetValue, i, clk = clock();
    Vec_Ptr_t * vOnionRings;

    assert( Saig_ManRegNum(p) > 0 );

    // start the onion rings
    vOnionRings = Vec_PtrAlloc( 1000 );

    // compute the global BDDs of the latches
    dd = Aig_ManComputeGlobalBdds( p, nBddMax, 1, fReorder, fVerbose );    
    if ( dd == NULL )
    {
        if ( !fSilent )
            printf( "The number of intermediate BDD nodes exceeded the limit (%d).\n", nBddMax );
        return -1;
    }
    if ( fVerbose )
        printf( "Shared BDD size is %6d nodes.\n", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd) );

    // save outputs
    pbOutputs = Aig_ManCreateOutputs( dd, p );

    // create partitions
    pbParts = Aig_ManCreatePartitions( dd, p, fReorder, fVerbose );

    // create the initial state and the variable map
    bInitial  = Aig_ManInitStateVarMap( dd, p, fVerbose );  Cudd_Ref( bInitial );

    // check the result
    RetValue = -1;
    for ( i = 0; i < Saig_ManPoNum(p); i++ )
    {
        if ( !Cudd_bddLeq( dd, bInitial, Cudd_Not(pbOutputs[i]) ) )
        {
            DdNode * bIntersect;
            bIntersect = Cudd_bddIntersect( dd, bInitial, pbOutputs[i] );  Cudd_Ref( bIntersect );
            assert( p->pSeqModel == NULL );
            p->pSeqModel = Aig_ManVerifyUsingBddsCountExample( p, dd, pbParts, 
                vOnionRings, bIntersect, i, fVerbose, fSilent ); 
            Cudd_RecursiveDeref( dd, bIntersect );
            if ( !fSilent )
                printf( "The miter output %d is proved REACHABLE in the initial state (use \"write_counter\" to dump a witness). ", i );
            RetValue = 0;
            break;
        }
    }
    // free the onion rings
    Vec_PtrForEachEntry( vOnionRings, bTemp, i )
        Cudd_RecursiveDeref( dd, bTemp );
    Vec_PtrFree( vOnionRings );
    // explore reachable states
    if ( RetValue == -1 )
        RetValue = Aig_ManComputeReachable( dd, p, pbParts, bInitial, pbOutputs, nBddMax, nIterMax, fPartition, fReorder, fVerbose, fSilent ); 

    // cleanup
    Cudd_RecursiveDeref( dd, bInitial );
    for ( i = 0; i < Saig_ManRegNum(p); i++ )
        Cudd_RecursiveDeref( dd, pbParts[i] );
    free( pbParts );
    for ( i = 0; i < Saig_ManPoNum(p); i++ )
        Cudd_RecursiveDeref( dd, pbOutputs[i] );
    free( pbOutputs );
    if ( RetValue == -1 )
        Cudd_Quit( dd );
    else
        Bbr_StopManager( dd );

    // report the runtime
    if ( !fSilent )
    {
    PRT( "Time", clock() - clk );
    fflush( stdout );
    }
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


