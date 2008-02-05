/**CFile****************************************************************

  FileName    [mfsCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Core procedures of this package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfsCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfsInt.h"

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
int Abc_NtkMfsResub( Mfs_Man_t * p, Abc_Obj_t * pNode )
{
    int clk;
    p->nNodesTried++;
    // prepare data structure for this node
    Mfs_ManClean( p ); 
    // compute window roots, window support, and window nodes
clk = clock();
    p->vRoots = Abc_MfsComputeRoots( pNode, p->pPars->nWinTfoLevs, p->pPars->nFanoutsMax );
    p->vSupp  = Abc_NtkNodeSupport( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
    p->vNodes = Abc_NtkDfsNodes( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
p->timeWin += clock() - clk;
    if ( p->pPars->nWinSizeMax && Vec_PtrSize(p->vNodes) > p->pPars->nWinSizeMax )
        return 1;
    // compute the divisors of the window
clk = clock();
    p->vDivs  = Abc_MfsComputeDivisors( p, pNode, Abc_ObjRequiredLevel(pNode) - 1 );
p->timeDiv += clock() - clk;
    // construct AIG for the window
clk = clock();
    p->pAigWin = Abc_NtkConstructAig( p, pNode );
p->timeAig += clock() - clk;
    // translate it into CNF
clk = clock();
    p->pCnf = Cnf_DeriveSimple( p->pAigWin, 1 + Vec_PtrSize(p->vDivs) );
p->timeCnf += clock() - clk;
    // create the SAT problem
clk = clock();
    p->pSat = Abc_MfsCreateSolverResub( p, NULL, 0 );
    if ( p->pSat == NULL )
    {
        p->nNodesBad++;
        return 1;
    }
    // solve the SAT problem
    if ( p->pPars->fArea )
        Abc_NtkMfsResubArea( p, pNode );
    else
        Abc_NtkMfsResubEdge( p, pNode );
p->timeSat += clock() - clk;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMfsNode( Mfs_Man_t * p, Abc_Obj_t * pNode )
{
    int clk;
    p->nNodesTried++;
    // prepare data structure for this node
    Mfs_ManClean( p );
    // compute window roots, window support, and window nodes
clk = clock();
    p->vRoots = Abc_MfsComputeRoots( pNode, p->pPars->nWinTfoLevs, p->pPars->nFanoutsMax );
    p->vSupp  = Abc_NtkNodeSupport( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
    p->vNodes = Abc_NtkDfsNodes( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
p->timeWin += clock() - clk;
    // construct AIG for the window
clk = clock();
    p->pAigWin = Abc_NtkConstructAig( p, pNode );
p->timeAig += clock() - clk;
    // translate it into CNF
clk = clock();
    p->pCnf = Cnf_DeriveSimple( p->pAigWin, Abc_ObjFaninNum(pNode) );
p->timeCnf += clock() - clk;
    // create the SAT problem
clk = clock();
    p->pSat = Cnf_DataWriteIntoSolver( p->pCnf, 1, 0 );
    // solve the SAT problem
    Abc_NtkMfsSolveSat( p, pNode );
p->timeSat += clock() - clk;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMfs( Abc_Ntk_t * pNtk, Mfs_Par_t * pPars )
{
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fRegisters );

    ProgressBar * pProgress;
    Mfs_Man_t * p;
    Abc_Obj_t * pObj;
    int i, clk = clock();
    int nTotalNodesBeg = Abc_NtkNodeNum(pNtk);
    int nTotalEdgesBeg = Abc_NtkGetTotalFanins(pNtk);

    assert( Abc_NtkIsLogic(pNtk) );
    if ( Abc_NtkGetFaninMax(pNtk) > MFS_FANIN_MAX )
    {
        printf( "Some nodes have more than %d fanins. Quitting.\n", MFS_FANIN_MAX );
        return 1;
    }
    // perform the network sweep
    Abc_NtkSweep( pNtk, 0 );
    // convert into the AIG
    if ( !Abc_NtkToAig(pNtk) )
    {
        fprintf( stdout, "Converting to BDD has failed.\n" );
        return 0;
    }
    assert( Abc_NtkHasAig(pNtk) );

    // start the manager
    p = Mfs_ManAlloc( pPars );
    p->pNtk  = pNtk;
    if ( pNtk->pExcare )
    {
        Abc_Ntk_t * pTemp;
        pTemp = Abc_NtkStrash( pNtk->pExcare, 0, 0, 0 );
        p->pCare = Abc_NtkToDar( pTemp, 0 );
        Abc_NtkDelete( pTemp );
    }
    if ( pPars->fVerbose )
    {
        if ( p->pCare != NULL )
            printf( "Performing optimization with %d external care clauses.\n", Aig_ManPoNum(p->pCare) );
        else
            printf( "Performing optimization without constraints.\n" );
    }
    if ( !pPars->fResub )
        printf( "Currently don't-cares are not used but the stats are printed.\n" );

    // label the register outputs
    if ( p->pCare )
    {
        Abc_NtkForEachCi( pNtk, pObj, i )
            pObj->pData = (void *)i;
    }
 
    // compute levels
    Abc_NtkLevel( pNtk );
    Abc_NtkStartReverseLevels( pNtk, pPars->nGrowthLevel );

    // compute don't-cares for each node
    p->nTotalNodesBeg = nTotalNodesBeg;
    p->nTotalEdgesBeg = nTotalEdgesBeg;
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( p->pPars->nDepthMax && (int)pObj->Level > p->pPars->nDepthMax )
            continue;
        if ( !p->pPars->fVeryVerbose )
            Extra_ProgressBarUpdate( pProgress, i, NULL );
        if ( pPars->fResub )
            Abc_NtkMfsResub( p, pObj );
        else
            Abc_NtkMfsNode( p, pObj );
    }
    Extra_ProgressBarStop( pProgress );
    Abc_NtkStopReverseLevels( pNtk );
    p->nTotalNodesEnd = Abc_NtkNodeNum(pNtk);
    p->nTotalEdgesEnd = Abc_NtkGetTotalFanins(pNtk);

    // undo labesl
    if ( p->pCare )
    {
        Abc_NtkForEachCi( pNtk, pObj, i )
            pObj->pData = NULL;
    }

    // free the manager
    p->timeTotal = clock() - clk;
    Mfs_ManStop( p );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


