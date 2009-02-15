/**CFile****************************************************************

  FileName    [giaAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Transformation between AIG manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int Gia_ObjChild0Copy( Aig_Obj_t * pObj )  { return Gia_LitNotCond( Aig_ObjFanin0(pObj)->iData, Aig_ObjFaninC0(pObj) ); }
static inline int Gia_ObjChild1Copy( Aig_Obj_t * pObj )  { return Gia_LitNotCond( Aig_ObjFanin1(pObj)->iData, Aig_ObjFaninC1(pObj) ); }

static inline Aig_Obj_t * Gia_ObjChild0Copy2( Aig_Obj_t ** ppNodes, Gia_Obj_t * pObj, int Id )  { return Aig_NotCond( ppNodes[Gia_ObjFaninId0(pObj, Id)], Gia_ObjFaninC0(pObj) ); }
static inline Aig_Obj_t * Gia_ObjChild1Copy2( Aig_Obj_t ** ppNodes, Gia_Obj_t * pObj, int Id )  { return Aig_NotCond( ppNodes[Gia_ObjFaninId1(pObj, Id)], Gia_ObjFaninC1(pObj) ); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derives combinational miter of the two AIGs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFromAig_rec( Gia_Man_t * pNew, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return;
    if ( Aig_ObjIsPi(pObj) )
    {
        pObj->iData = Gia_ManAppendCi( pNew );
        return;
    }
    assert( Aig_ObjIsNode(pObj) );
    Gia_ManFromAig_rec( pNew, Aig_ObjFanin0(pObj) );
    Gia_ManFromAig_rec( pNew, Aig_ObjFanin1(pObj) );
    pObj->iData = Gia_ManAppendAnd( pNew, Gia_ObjChild0Copy(pObj), Gia_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFromAig( Aig_Man_t * p )
{
    Gia_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // add fake POs to all the dangling nodes (choices)
    Aig_ManForEachNode( p, pObj, i )
        assert( Aig_ObjRefs(pObj) > 0 );
    // create the new manager
    pNew = Gia_ManStart( Aig_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->iData = 1;
    Aig_ManForEachPi( p, pObj, i )
    {
//        if ( Aig_ObjRefs(pObj) == 0 )
            pObj->iData = Gia_ManAppendCi( pNew );
    }
    // add logic for the POs
    Aig_ManForEachPo( p, pObj, i )
    {
        Gia_ManFromAig_rec( pNew, Aig_ObjFanin0(pObj) );        
        Gia_ManAppendCo( pNew, Gia_ObjChild0Copy(pObj) );
    }
    Gia_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Handles choices as additional combinational outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFromAigSwitch( Aig_Man_t * p )
{
    Gia_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Gia_ManStart( Aig_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->iData = 1;
    Aig_ManForEachPi( p, pObj, i )
        pObj->iData = Gia_ManAppendCi( pNew );
    // add POs corresponding to the nodes with choices
    Aig_ManForEachNode( p, pObj, i )
        if ( Aig_ObjRefs(pObj) == 0 )
        {
            Gia_ManFromAig_rec( pNew, pObj );        
            Gia_ManAppendCo( pNew, pObj->iData );
        }
    // add logic for the POs
    Aig_ManForEachPo( p, pObj, i )
    {
        Gia_ManFromAig_rec( pNew, Aig_ObjFanin0(pObj) );        
        Gia_ManAppendCo( pNew, Gia_ObjChild0Copy(pObj) );
    }
    Gia_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives combinational miter of the two AIGs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManToAig_rec( Aig_Man_t * pNew, Aig_Obj_t ** ppNodes, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ppNodes[Gia_ObjId(p, pObj)] )
        return;
    if ( Gia_ObjIsCi(pObj) )
    {
        ppNodes[Gia_ObjId(p, pObj)] = Aig_ObjCreatePi( pNew );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManToAig_rec( pNew, ppNodes, p, Gia_ObjFanin0(pObj) );
    Gia_ManToAig_rec( pNew, ppNodes, p, Gia_ObjFanin1(pObj) );
    ppNodes[Gia_ObjId(p, pObj)] = Aig_And( pNew, Gia_ObjChild0Copy2(ppNodes, pObj, Gia_ObjId(p, pObj)), Gia_ObjChild1Copy2(ppNodes, pObj, Gia_ObjId(p, pObj)) );
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Gia_ManToAig( Gia_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t ** ppNodes;
    Gia_Obj_t * pObj;
    int i;

    // create the new manager
    pNew = Aig_ManStart( Gia_ManAndNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    ppNodes = ABC_CALLOC( Aig_Obj_t *, Gia_ManObjNum(p) );
    // create the PIs
    ppNodes[0] = Aig_ManConst0(pNew);
    Gia_ManForEachCi( p, pObj, i )
    {
//        if ( Aig_ObjRefs(pObj) == 0 )
            ppNodes[Gia_ObjId(p, pObj)] = Aig_ObjCreatePi( pNew );
    }
    // add logic for the POs
    Gia_ManForEachCo( p, pObj, i )
    {
        Gia_ManToAig_rec( pNew, ppNodes, p, Gia_ObjFanin0(pObj) );        
        ppNodes[Gia_ObjId(p, pObj)] = Aig_ObjCreatePo( pNew, Gia_ObjChild0Copy2(ppNodes, pObj, Gia_ObjId(p, pObj)) );
    }
    Aig_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    ABC_FREE( ppNodes );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


