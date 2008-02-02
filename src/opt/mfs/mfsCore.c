/**CFile****************************************************************

  FileName    [mfsCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    []

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
int Abc_NtkMfsNode( Mfs_Man_t * p, Abc_Obj_t * pNode )
{
    int clk;
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
    Mfs_Man_t * p;
    Abc_Obj_t * pObj;
    int i, Counter;

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
    if ( pNtk->pManExdc != NULL )
        printf( "Performing don't-care computation with don't-cares.\n" );

    // start the manager
    p = Mfs_ManAlloc();
    p->pPars = pPars;
    p->pNtk  = pNtk;
    p->pCare = pNtk->pManExdc;

    // label the register outputs
    if ( p->pCare )
    {
        Counter = 1;
        Abc_NtkForEachCi( pNtk, pObj, i )
            if ( Abc_ObjFaninNum(pObj) == 0 )
                pObj->pData = NULL;
            else
                pObj->pData = (void *)Counter++;
        assert( Counter == Abc_NtkLatchNum(pNtk) + 1 );
    }

    // compute don't-cares for each node
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_NtkMfsNode( p, pObj );

    // undo labesl
    if ( p->pCare )
    {
        Abc_NtkForEachCi( pNtk, pObj, i )
            pObj->pData = NULL;
    }

    // free the manager
    Mfs_ManStop( p );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


