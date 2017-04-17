/**CFile****************************************************************

  FileName    [acbPush.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Implementation of logic pushing.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 21, 2015.]

  Revision    [$Id: acbPush.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acb.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Check if the node can have its logic pushed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_ObjCheckFaninDsd( Acb_Ntk_t * p, int iObj, int iFanIndex )
{
    int k, iFanin, * pFanins;
    Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
        if ( Abc_TtCheckDsdAnd(Acb_ObjTruth(p, iObj), iFanIndex, k, NULL) >= 0 )
            return 1;
    return 0;
}
int Acb_ObjCountFaninAbsorb( Acb_Ntk_t * p, int iObj, int iFanin, int iFanIndex, int nLutSize )
{
    if ( Acb_ObjSetTravIdCur(p, iFanin) )
        return 0;
    if ( Acb_ObjIsCi(p, iFanin) )
        return 0;
    if ( Acb_ObjFanoutNum(p, iFanin) > 1 )
        return 0;
    if ( !Acb_ObjCheckFaninDsd(p, iObj, iFanIndex) ) 
        return 0;
    if ( Acb_ObjFaninNum(p, iFanin) == nLutSize )
        return 0;
    return 1;
}
int Acb_NtkObjPushEstimate( Acb_Ntk_t * p, int iObj, int nLutSize )
{
    int k, iFanin, * pFanins;
    int Count = Acb_ObjFaninNum(p, iObj);
    Acb_NtkIncTravId( p );
    Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
    {
        Count -= Acb_ObjCountFaninAbsorb( p, iObj, iFanin, k, nLutSize );
        if ( Count <= 0 )
            return 1;
    }
    if ( Acb_ObjFanoutNum(p, iObj) > 1 )
        return 0;
    Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
        if ( Abc_TtCheckOutAnd(Acb_ObjTruth(p, iObj), k, NULL) )
            break;
    if ( k == Acb_ObjFaninNum(p, iFanin) )
        return 0;
    iFanin = Vec_IntEntry( Acb_ObjFanout(p, iObj), 0 );
    if ( Acb_ObjFaninNum(p, iFanin) == nLutSize )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkPushLogic( Acb_Ntk_t * p, int nLutSize, int fVerbose )
{
    //Vec_Bit_t * vVisited = Vec_BitStart( Acb_NtkObjNumMax(p) );
    int n = 0, iObj, nNodes = 0;
    Acb_NtkCreateFanout( p );  // fanout data structure
    for ( n = 2; n <= nLutSize; n++ )
        Acb_NtkForEachNode( p, iObj )
        {
            if ( !Acb_NtkObjPushEstimate(p, iObj, nLutSize) )
                continue;
            nNodes++;
        }
    printf( "Performed optimization at %d nodes.\n", nNodes );
    //Vec_BitFree( vVisited );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

