/**CFile****************************************************************

  FileName    [saigTempor.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Temporal decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigTempor.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates initialized timeframes for temporal decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManTemporFrames( Aig_Man_t * pAig, int nFrames )
{
    Aig_Man_t * pFrames;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, f;
    // start the frames package
    Aig_ManCleanData( pAig );
    pFrames = Aig_ManStart( Aig_ManObjNumMax(pAig) * nFrames );
    pFrames->pName = Aig_UtilStrsav( pAig->pName );
    // initiliaze the flops
    Saig_ManForEachLo( pAig, pObj, i )
        pObj->pData = Aig_ManConst0(pFrames);
    // for each timeframe
    for ( f = 0; f < nFrames; f++ )
    {
        Aig_ManConst1(pAig)->pData = Aig_ManConst1(pFrames);
        Saig_ManForEachPi( pAig, pObj, i )
            pObj->pData = Aig_ObjCreatePi(pFrames);
        Aig_ManForEachNode( pAig, pObj, i )
            pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        Aig_ManForEachPo( pAig, pObj, i )
            pObj->pData = Aig_ObjChild0Copy(pObj);
        Saig_ManForEachLiLo( pAig, pObjLi, pObjLo, i )
            pObjLo->pData = pObjLi->pData;
    }
    // create POs for the flop inputs
    Saig_ManForEachLi( pAig, pObj, i )
        Aig_ObjCreatePo( pFrames, pObj->pData );
    Aig_ManCleanup( pFrames );
    return pFrames;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManTemporDecompose( Aig_Man_t * pAig, int nFrames )
{
    Aig_Man_t * pAigNew, * pFrames;
    Aig_Obj_t * pObj, * pReset;
    int i;
    if ( pAig->nConstrs > 0 )
    {
        printf( "The AIG manager should have no constraints.\n" );
        return NULL;
    }
    // create initialized timeframes
    pFrames = Saig_ManTemporFrames( pAig, nFrames );
    assert( Aig_ManPoNum(pFrames) == Aig_ManRegNum(pAig) );

    // start the new manager
    Aig_ManCleanData( pAig );
    pAigNew = Aig_ManStart( Aig_ManNodeNum(pAig) );
    pAigNew->pName = Aig_UtilStrsav( pAig->pName );
    // map the constant node and primary inputs
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pAigNew );
    Saig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pAigNew );

    // insert initialization logic
    Aig_ManConst1(pFrames)->pData = Aig_ManConst1( pAigNew );
    Aig_ManForEachPi( pFrames, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pAigNew );
    Aig_ManForEachNode( pFrames, pObj, i )
        pObj->pData = Aig_And( pAigNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Aig_ManForEachPo( pFrames, pObj, i )
        pObj->pData = Aig_ObjChild0Copy(pObj);

    // create reset latch (the first one among the latches)
    pReset = Aig_ObjCreatePi( pAigNew );

    // create flop output values
    Saig_ManForEachLo( pAig, pObj, i )
        pObj->pData = Aig_Mux( pAigNew, pReset, Aig_ObjCreatePi(pAigNew), Aig_ManPo(pFrames, i)->pData );
    Aig_ManStop( pFrames );

    // add internal nodes of this frame
    Aig_ManForEachNode( pAig, pObj, i )
        pObj->pData = Aig_And( pAigNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create primary outputs
    Saig_ManForEachPo( pAig, pObj, i )
        Aig_ObjCreatePo( pAigNew, Aig_ObjChild0Copy(pObj) );

    // create reset latch (the first one among the latches)
    Aig_ObjCreatePo( pAigNew, Aig_ManConst1(pAigNew) );
    // create latch inputs
    Saig_ManForEachLi( pAig, pObj, i )
        Aig_ObjCreatePo( pAigNew, Aig_ObjChild0Copy(pObj) );

    // finalize
    Aig_ManCleanup( pAigNew );
    Aig_ManSetRegNum( pAigNew, Aig_ManRegNum(pAig)+1 ); // + reset latch (011111...)
    return pAigNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManTempor( Aig_Man_t * pAig, int nFrames, int TimeOut, int nConfLimit, int fUseBmc, int fVerbose, int fVeryVerbose )
{ 
    extern int Saig_ManPhasePrefixLength( Aig_Man_t * p, int fVerbose, int fVeryVerbose );
    int RetValue, nFramesFinished = -1;
    assert( nFrames >= 0 ); 
    if ( nFrames == 0 )
    {
        nFrames = Saig_ManPhasePrefixLength( pAig, fVerbose, fVeryVerbose );
        if ( nFrames == 1 )
        {
            printf( "The leading sequence has length 1. Temporal decomposition is not performed.\n" );
            return NULL;
        }
        Abc_Print( 1, "Using computed frame number (%d).\n", nFrames );
    }
    else
        Abc_Print( 1, "Using user-given frame number (%d).\n", nFrames );
    // run BMC2
    if ( fUseBmc )
    {
        RetValue = Saig_BmcPerform( pAig, 0, nFrames, 5000, TimeOut, nConfLimit, 0, fVerbose, 0, &nFramesFinished );
        if ( RetValue == 0 )
        {
            printf( "A cex found in the first %d frames.\n", nFrames );
            return NULL;
        }
        if ( nFramesFinished < nFrames )
        {
            printf( "BMC for %d frames could not be completed. A cex may exist!\n", nFrames );
            return NULL;
        }
    }
    return Saig_ManTemporDecompose( pAig, nFrames );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

