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

#include "giaAig.h"

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
void Gia_ManFromAig_rec( Gia_Man_t * pNew, Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pNext;
    if ( pObj->iData )
        return;
    assert( Aig_ObjIsNode(pObj) );
    Gia_ManFromAig_rec( pNew, p, Aig_ObjFanin0(pObj) );
    Gia_ManFromAig_rec( pNew, p, Aig_ObjFanin1(pObj) );
    pObj->iData = Gia_ManAppendAnd( pNew, Gia_ObjChild0Copy(pObj), Gia_ObjChild1Copy(pObj) );
    if ( p->pEquivs && (pNext = Aig_ObjEquiv(p, pObj)) )
    {
        int iObjNew, iNextNew;
        Gia_ManFromAig_rec( pNew, p, pNext );
        iObjNew  = Gia_Lit2Var(pObj->iData);
        iNextNew = Gia_Lit2Var(pNext->iData);
        if ( pNew->pNexts )
            pNew->pNexts[iObjNew] = iNextNew;        
    }
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
    // create the new manager
    pNew = Gia_ManStart( Aig_ManObjNum(p) );
    pNew->pName = Gia_UtilStrsav( p->pName );
    // create room to store equivalences
    if ( p->pEquivs )
        pNew->pNexts = ABC_CALLOC( int, Aig_ManObjNum(p) );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->iData = 1;
    Aig_ManForEachPi( p, pObj, i )
        pObj->iData = Gia_ManAppendCi( pNew );
    // add logic for the POs
    Aig_ManForEachPo( p, pObj, i )
        Gia_ManFromAig_rec( pNew, p, Aig_ObjFanin0(pObj) );        
    Aig_ManForEachPo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjChild0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    if ( pNew->pNexts )
        Gia_ManDeriveReprs( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFromAigSimple( Aig_Man_t * p )
{
    Gia_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Gia_ManStart( Aig_ManObjNum(p) );
    pNew->pName = Gia_UtilStrsav( p->pName );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsAnd(pObj) )
            pObj->iData = Gia_ManAppendAnd( pNew, Gia_ObjChild0Copy(pObj), Gia_ObjChild1Copy(pObj) );
        else if ( Aig_ObjIsPi(pObj) )
            pObj->iData = Gia_ManAppendCi( pNew );
        else if ( Aig_ObjIsPo(pObj) )
            pObj->iData = Gia_ManAppendCo( pNew, Gia_ObjChild0Copy(pObj) );
        else if ( Aig_ObjIsConst1(pObj) )
            pObj->iData = 1;
        else
            assert( 0 );
    }
    Gia_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    if ( pNew->pNexts )
        Gia_ManDeriveReprs( pNew );
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
    pNew->pName = Gia_UtilStrsav( p->pName );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->iData = 1;
    Aig_ManForEachPi( p, pObj, i )
        pObj->iData = Gia_ManAppendCi( pNew );
    // add POs corresponding to the nodes with choices
    Aig_ManForEachNode( p, pObj, i )
        if ( Aig_ObjRefs(pObj) == 0 )
        {
            Gia_ManFromAig_rec( pNew, p, pObj );        
            Gia_ManAppendCo( pNew, pObj->iData );
        }
    // add logic for the POs
    Aig_ManForEachPo( p, pObj, i )
        Gia_ManFromAig_rec( pNew, p, Aig_ObjFanin0(pObj) );        
    Aig_ManForEachPo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjChild0Copy(pObj) );
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
    Gia_Obj_t * pNext;
    if ( ppNodes[Gia_ObjId(p, pObj)] )
        return;
    if ( Gia_ObjIsCi(pObj) )
        ppNodes[Gia_ObjId(p, pObj)] = Aig_ObjCreatePi( pNew );
    else
    {
        assert( Gia_ObjIsAnd(pObj) );
        Gia_ManToAig_rec( pNew, ppNodes, p, Gia_ObjFanin0(pObj) );
        Gia_ManToAig_rec( pNew, ppNodes, p, Gia_ObjFanin1(pObj) );
        ppNodes[Gia_ObjId(p, pObj)] = Aig_And( pNew, Gia_ObjChild0Copy2(ppNodes, pObj, Gia_ObjId(p, pObj)), Gia_ObjChild1Copy2(ppNodes, pObj, Gia_ObjId(p, pObj)) );
    }
    if ( pNew->pEquivs && (pNext = Gia_ObjNextObj(p, Gia_ObjId(p, pObj))) )
    {
        Aig_Obj_t * pObjNew, * pNextNew;
        Gia_ManToAig_rec( pNew, ppNodes, p, pNext );
        pObjNew  = ppNodes[Gia_ObjId(p, pObj)];
        pNextNew = ppNodes[Gia_ObjId(p, pNext)];
        if ( pNew->pEquivs )
            pNew->pEquivs[Aig_Regular(pObjNew)->Id] = Aig_Regular(pNextNew);        
    }
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Gia_ManToAig( Gia_Man_t * p, int fChoices )
{
    Aig_Man_t * pNew;
    Aig_Obj_t ** ppNodes;
    Gia_Obj_t * pObj;
    int i;
    assert( !fChoices || (p->pNexts && p->pReprs) );
    // create the new manager
    pNew = Aig_ManStart( Gia_ManAndNum(p) );
    pNew->pName = Gia_UtilStrsav( p->pName );
//    pNew->pSpec = Gia_UtilStrsav( p->pName );
    // duplicate representation of choice nodes
    if ( fChoices )
        pNew->pEquivs = ABC_CALLOC( Aig_Obj_t *, Gia_ManObjNum(p) );
    // create the PIs
    ppNodes = ABC_CALLOC( Aig_Obj_t *, Gia_ManObjNum(p) );
    ppNodes[0] = Aig_ManConst0(pNew);
    Gia_ManForEachCi( p, pObj, i )
        ppNodes[Gia_ObjId(p, pObj)] = Aig_ObjCreatePi( pNew );
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

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Gia_ManCofactorAig( Aig_Man_t * p, int nFrames, int nCofFanLit )
{
    Aig_Man_t * pMan;
    Gia_Man_t * pGia, * pTemp;
    pGia = Gia_ManFromAig( p );
    pGia = Gia_ManUnrollAndCofactor( pTemp = pGia, nFrames, nCofFanLit, 1 );
    Gia_ManStop( pTemp );
    pMan = Gia_ManToAig( pGia, 0 );
    Gia_ManStop( pGia );
    return pMan;
}


/**Function*************************************************************

  Synopsis    [Transfers representatives from pGia to pAig.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManReprToAigRepr( Aig_Man_t * p, Gia_Man_t * pGia )
{
    Aig_Obj_t * pObj;
    Gia_Obj_t * pGiaObj, * pGiaRepr;
    int i;
    assert( p->pReprs == NULL );
    assert( pGia->pReprs != NULL );
    // move pointers from AIG to GIA
    Aig_ManForEachObj( p, pObj, i )
    {
        assert( i == 0 || !Gia_LitIsCompl(pObj->iData) );
        pGiaObj = Gia_ManObj( pGia, Gia_Lit2Var(pObj->iData) );
        pGiaObj->Value = i;
    }
    // set the pointers to the nodes in AIG
    Aig_ManReprStart( p, Aig_ManObjNumMax(p) );
    Gia_ManForEachObj( pGia, pGiaObj, i )
    {
        pGiaRepr = Gia_ObjReprObj( pGia, i );
        if ( pGiaRepr == NULL )
            continue;
        Aig_ObjCreateRepr( p, Aig_ManObj(p, pGiaRepr->Value), Aig_ManObj(p, pGiaObj->Value) );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


