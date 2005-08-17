/**CFile****************************************************************

  FileName    [rwrUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the array of fanout counters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Rwt_NtkFanoutCounters( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vFanNums;
    Abc_Obj_t * pObj;
    int i;
    vFanNums = Vec_IntAlloc( 0 );
    Vec_IntFill( vFanNums, Abc_NtkObjNumMax(pNtk), -1 );
    Abc_NtkForEachObj( pNtk, pObj, i )
        if ( Abc_ObjIsNode( pObj ) )
            Vec_IntWriteEntry( vFanNums, i, Abc_ObjFanoutNum(pObj) );
    return vFanNums;
}

/**Function*************************************************************

  Synopsis    [Creates the array of required times.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Rwt_NtkRequiredLevels( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vReqTimes;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pFanout;
    int i, k, nLevelsMax, nLevelsCur;
    // start the required times
    vReqTimes = Vec_IntAlloc( 0 );
    Vec_IntFill( vReqTimes, Abc_NtkObjNumMax(pNtk), ABC_INFINITY );
    // compute levels in reverse topological order
    Abc_NtkForEachCo( pNtk, pObj, i )
        Vec_IntWriteEntry( vReqTimes, pObj->Id, 0 );
    vNodes = Abc_NtkDfsReverse( pNtk );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        nLevelsCur = 0;
        Abc_ObjForEachFanout( pObj, pFanout, k )
            if ( nLevelsCur < Vec_IntEntry(vReqTimes, pFanout->Id) )
                nLevelsCur = Vec_IntEntry(vReqTimes, pFanout->Id);
        Vec_IntWriteEntry( vReqTimes, pObj->Id, nLevelsCur + 1 );
    }
    Vec_PtrFree( vNodes );
    // convert levels into required times: RetTime = NumLevels + 1 - Level
    nLevelsMax = Abc_AigGetLevelNum(pNtk) + 1;
    Abc_NtkForEachNode( pNtk, pObj, i )
        Vec_IntWriteEntry( vReqTimes, pObj->Id, nLevelsMax - Vec_IntEntry(vReqTimes, pObj->Id) );
//    Abc_NtkForEachNode( pNtk, pObj, i )
//        printf( "(%d,%d)", pObj->Level, Vec_IntEntry(vReqTimes, pObj->Id) );
//    printf( "\n" );
    return vReqTimes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


