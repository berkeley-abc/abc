/**CFile****************************************************************

  FileName    [saigUnique.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Containment checking with unique state constraints.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigUnique.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "cnf.h"
#include "satSolver.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Create timeframes of the manager for interpolation.]

  Description [The resulting manager is combinational. The primary inputs
  corresponding to register outputs are ordered first.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManFramesLatches( Aig_Man_t * pAig, int nFrames, Vec_Ptr_t ** pvMapReg )
{
    Aig_Man_t * pFrames;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, f;
    assert( Saig_ManRegNum(pAig) > 0 );
    pFrames = Aig_ManStart( Aig_ManNodeNum(pAig) * nFrames );
    // map the constant node
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pFrames );
    // create variables for register outputs
    *pvMapReg = Vec_PtrAlloc( (nFrames+1) * Saig_ManRegNum(pAig) );
    Saig_ManForEachLo( pAig, pObj, i )
    {
        pObj->pData = Aig_ObjCreatePi( pFrames );
        Vec_PtrPush( *pvMapReg, pObj->pData );
    }
    // add timeframes
    for ( f = 0; f < nFrames; f++ )
    {
        // create PI nodes for this frame
        Saig_ManForEachPi( pAig, pObj, i )
            pObj->pData = Aig_ObjCreatePi( pFrames );
        // add internal nodes of this frame
        Aig_ManForEachNode( pAig, pObj, i )
            pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        // save register inputs
        Saig_ManForEachLi( pAig, pObj, i )
            pObj->pData = Aig_ObjChild0Copy(pObj);
        // transfer to register outputs
        Saig_ManForEachLiLo(  pAig, pObjLi, pObjLo, i )
        {
            pObjLo->pData = pObjLi->pData;
            Vec_PtrPush( *pvMapReg, pObjLo->pData );
        }
    }
    return pFrames;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG while mapping PIs into the given array.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManAppendCone( Aig_Man_t * pOld, Aig_Man_t * pNew, Aig_Obj_t ** ppNewPis, int fCompl )
{
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManPoNum(pOld) == 1 );
    // create the PIs
    Aig_ManCleanData( pOld );
    Aig_ManConst1(pOld)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( pOld, pObj, i )
        pObj->pData = ppNewPis[i];
    // duplicate internal nodes
    Aig_ManForEachNode( pOld, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // add one PO to new
    pObj = Aig_ManPo( pOld, 0 );
    Aig_ObjCreatePo( pNew, Aig_NotCond( Aig_ObjChild0Copy(pObj), fCompl ) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManUniqueState( Aig_Man_t * pTrans, Vec_Ptr_t * vInters )
{
    Aig_Man_t * pFrames, * pInterNext, * pInterThis;
    Aig_Obj_t ** ppNodes;
    Vec_Ptr_t * vMapRegs;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    int f, nRegs, status;
    nRegs = Saig_ManRegNum(pTrans);
    assert( nRegs > 0 );
    assert( Vec_PtrSize(vInters) > 1 );
    // generate the timeframes
    pFrames = Saig_ManFramesLatches( pTrans, Vec_PtrSize(vInters)-1, &vMapRegs );
    assert( Vec_PtrSize(vMapRegs) == Vec_PtrSize(vInters) * nRegs );
    // add main constraints to the timeframes
    ppNodes = (Aig_Obj_t **)Vec_PtrArray(vMapRegs);
    Vec_PtrForEachEntryStop( vInters, pInterThis, f, Vec_PtrSize(vInters)-1 )
    {
        assert( nRegs == Aig_ManPiNum(pInterThis) );
        pInterNext = Vec_PtrEntry( vInters, f+1 );
        Saig_ManAppendCone( pInterNext, pFrames, ppNodes + f * nRegs, 0 );
        Saig_ManAppendCone( pInterThis, pFrames, ppNodes + f * nRegs, 1 );
    }
    Saig_ManAppendCone( Vec_PtrEntryLast(vInters), pFrames, ppNodes + f * nRegs, 1 );
    Aig_ManCleanup( pFrames );
    Vec_PtrFree( vMapRegs );

    // convert to CNF
    pCnf = Cnf_Derive( pFrames, 0 ); 
    pSat = Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
    Cnf_DataFree( pCnf );
    Aig_ManStop( pFrames );

    if ( pSat == NULL )
        return 1;

     // solve the problem
    status = sat_solver_solve( pSat, NULL, NULL, (sint64)0, (sint64)0, (sint64)0, (sint64)0 );
    sat_solver_delete( pSat );
    return status == l_False;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


