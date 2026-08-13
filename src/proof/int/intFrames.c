/**CFile****************************************************************

  FileName    [intFrames.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation engine.]

  Synopsis    [Sequential AIG unrolling for interpolation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 24, 2008.]

  Revision    [$Id: intFrames.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "intInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Create timeframes of the manager for interpolation.]

  Description [The resulting manager is combinational. The primary inputs
  corresponding to register outputs are ordered first. The only POs of the 
  manager is the requested final/two-frame/all-frame property output.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Inter_ManFramesInter( Aig_Man_t * pAig, int nFrames, int fAddRegOuts, int fUseTwoFrames, int fUseAllFrames )
{
    Aig_Man_t * pFrames;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    Aig_Obj_t * pCurPo = NULL, * pLastPo = NULL, * pAllPo = NULL;
    int i, f;
    assert( Saig_ManRegNum(pAig) > 0 );
    assert( Saig_ManPoNum(pAig)-Saig_ManConstrNum(pAig) == 1 );
    pFrames = Aig_ManStart( Aig_ManNodeNum(pAig) * nFrames );
    // map the constant node
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pFrames );
    // create variables for register outputs
    if ( fAddRegOuts )
    {
        Saig_ManForEachLo( pAig, pObj, i )
            pObj->pData = Aig_ManConst0( pFrames );
    }
    else
    {
        Saig_ManForEachLo( pAig, pObj, i )
            pObj->pData = Aig_ObjCreateCi( pFrames );
    }
    // add timeframes
    for ( f = 0; f < nFrames; f++ )
    {
        // create PI nodes for this frame
        Saig_ManForEachPi( pAig, pObj, i )
            pObj->pData = Aig_ObjCreateCi( pFrames );
        // add internal nodes of this frame
        Aig_ManForEachNode( pAig, pObj, i )
            pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        pCurPo = Aig_ObjChild0Copy( Aig_ManCo(pAig, 0) );
        if ( fUseAllFrames )
            pAllPo = pAllPo == NULL ? pCurPo : Aig_Or( pFrames, pAllPo, pCurPo );
        // add outputs for constraints
        Saig_ManForEachPo( pAig, pObj, i )
        {
            if ( i < Saig_ManPoNum(pAig)-Saig_ManConstrNum(pAig) )
                continue;
            Aig_ObjCreateCo( pFrames, Aig_Not( Aig_ObjChild0Copy(pObj) ) );
        }
        if ( f == nFrames - 1 )
            break;
        // remember the last PO
        pLastPo = pCurPo;
        // save register inputs
        Saig_ManForEachLi( pAig, pObj, i )
            pObj->pData = Aig_ObjChild0Copy(pObj);
        // transfer to register outputs
        Saig_ManForEachLiLo(  pAig, pObjLi, pObjLo, i )
            pObjLo->pData = pObjLi->pData;
    }
    // create POs for each register output
    if ( fAddRegOuts )
    {
        Saig_ManForEachLi( pAig, pObj, i )
            Aig_ObjCreateCo( pFrames, Aig_ObjChild0Copy(pObj) );
    }
    // create the only PO of the manager
    else
    {
        assert( pCurPo != NULL );
        // add the selected suffix property
        if ( fUseAllFrames )
            pLastPo = pAllPo;
        else if ( pLastPo == NULL || !fUseTwoFrames )
            pLastPo = pCurPo;
        else
            pLastPo = Aig_Or( pFrames, pLastPo, pCurPo );
        Aig_ObjCreateCo( pFrames, pLastPo );
    }
    Aig_ManCleanup( pFrames );
    return pFrames;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
