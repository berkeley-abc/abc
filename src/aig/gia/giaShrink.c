/**CFile****************************************************************

  FileName    [giaShrink.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Implementation of mapShrink based on ideas of Niklas Een.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaShrink.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "src/aig/aig/aig.h"
#include "src/opt/dar/dar.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int  Dar_LibEvalBuild( Gia_Man_t * p, Vec_Int_t * vCut, unsigned uTruth, int fKeepLevel, Vec_Int_t * vLeavesBest );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs AIG shrinking using the current mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManPerformMapShrink( Gia_Man_t * p, int fKeepLevel, int fVerbose )
{
    Vec_Int_t * vLeaves, * vTruth, * vVisited, * vLeavesBest;
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pFanin;
    unsigned * pTruth;
    int i, k, iFan, clk = clock();
    int ClassCounts[222] = {0};
    int * pLutClass, Counter = 0;
    assert( p->pMapping != NULL );
    if ( Gia_ManLutSizeMax( p ) > 4 )
    {
        printf( "Resynthesis is not performed when nodes have more than 4 inputs.\n" );
        return NULL;
    }
    pLutClass   = ABC_CALLOC( int, Gia_ManObjNum(p) );
    vLeaves     = Vec_IntAlloc( 0 );
    vTruth      = Vec_IntAlloc( (1<<16) );
    vVisited    = Vec_IntAlloc( 0 );
    vLeavesBest = Vec_IntAlloc( 4 );
    // prepare the library
    Dar_LibPrepare( 5 ); 
    // clean the old manager
    Gia_ManCleanTruth( p );
    Gia_ManSetPhase( p );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    // start the new manager
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManCleanLevels( pNew, Gia_ManObjNum(p) );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
        {
            pObj->Value = Gia_ManAppendCi( pNew );
            Gia_ObjSetLevel( pNew, Gia_ObjFromLit(pNew, Gia_ObjValue(pObj)), Gia_ObjLevel(p, pObj) );
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        }
        else if ( Gia_ObjIsLut(p, i) )
        {
            Counter++;
            // collect leaves of this gate
            Vec_IntClear( vLeaves );
            Gia_LutForEachFanin( p, i, iFan, k )
                Vec_IntPush( vLeaves, iFan );
            for ( ; k < 4; k++ )
                Vec_IntPush( vLeaves, 0 );
            //.compute the truth table 
            pTruth = Gia_ManConvertAigToTruth( p, pObj, vLeaves, vTruth, vVisited );
            // change from node IDs to their literals
            Gia_ManForEachObjVec( vLeaves, p, pFanin, k )
            {
                assert( Gia_ObjValue(pFanin) != ~0 ); 
                Vec_IntWriteEntry( vLeaves, k, Gia_ObjValue(pFanin) );
            }
            // derive new structre
            if ( Gia_ManTruthIsConst0(pTruth, Vec_IntSize(vLeaves)) )
                pObj->Value = 0;
            else if ( Gia_ManTruthIsConst1(pTruth, Vec_IntSize(vLeaves)) )
                pObj->Value = 1;
            else
            {
                pObj->Value = Dar_LibEvalBuild( pNew, vLeaves, 0xffff & *pTruth, fKeepLevel, vLeavesBest );
                pObj->Value = Abc_LitNotCond( pObj->Value, Gia_ObjPhaseRealLit(pNew, pObj->Value) ^ pObj->fPhase );
            }
        }
    }
    // cleanup the AIG
    Gia_ManHashStop( pNew );
    // check the presence of dangling nodes
    if ( Gia_ManHasDangling(pNew) )
    {
        pNew = Gia_ManCleanup( pTemp = pNew );
        if ( Gia_ManAndNum(pNew) != Gia_ManAndNum(pTemp) )
            printf( "Gia_ManPerformMapShrink() node reduction after sweep %6d -> %6d.\n", Gia_ManAndNum(pTemp), Gia_ManAndNum(pNew) );
        Gia_ManStop( pTemp );
    }
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Vec_IntFree( vLeaves );
    Vec_IntFree( vTruth );
    Vec_IntFree( vVisited );
    Vec_IntFree( vLeavesBest );
    if ( fVerbose )
    {
        printf( "Total gain in AIG nodes = %d.  ", Gia_ManObjNum(p)-Gia_ManObjNum(pNew) );
        ABC_PRT( "Total runtime", clock() - clk );
    }
    ABC_FREE( pLutClass );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

