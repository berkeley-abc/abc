/**CFile****************************************************************

  FileName    [aigDup.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [AIG duplication (re-strashing).]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigDup.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "src/aig/saig/saig.h"
#include "src/misc/tim/tim.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [Orders nodes as follows: PIs, ANDs, POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupSimple( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i;
    assert( p->pManTime == NULL );
    assert( p->pManHaig == NULL || Aig_ManBufNum(p) == 0 );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nAsserts = p->nAsserts;
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pNew)->pHaig = Aig_ManConst1(p)->pHaig;
    Aig_ManForEachPi( p, pObj, i )
    {
        pObjNew = Aig_ObjCreatePi( pNew );
        pObjNew->pHaig = pObj->pHaig;
        pObjNew->Level = pObj->Level;
        pObj->pData = pObjNew;
    }
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
        {
            pObjNew = Aig_ObjChild0Copy(pObj);
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
        else if ( Aig_ObjIsNode(pObj) )
        {
            pObjNew = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
    // add the POs
    Aig_ManForEachPo( p, pObj, i )
    {
        pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        pObjNew->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // pass the HAIG manager
    if ( p->pManHaig != NULL )
    {
        pNew->pManHaig = p->pManHaig;  
        p->pManHaig = NULL;
    }
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupSimple(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives AIG with hints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupSimpleWithHints( Aig_Man_t * p, Vec_Int_t * vHints )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i, Entry;
    assert( p->pManHaig == NULL || Aig_ManBufNum(p) == 0 );
    assert( p->nAsserts == 0 || p->nConstrs == 0 );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
    {
        pObj->pData = Aig_ObjCreatePi( pNew );
        Entry = Vec_IntEntry( vHints, Aig_ObjId(pObj) );
        if ( Entry == 0 || Entry == 1 )
            pObj->pData = Aig_NotCond( Aig_ManConst1(pNew), Entry ); // restrict to the complement of constraint!!!
    }
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
    {
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        Entry = Vec_IntEntry( vHints, Aig_ObjId(pObj) );
        if ( Entry == 0 || Entry == 1 )
            pObj->pData = Aig_NotCond( Aig_ManConst1(pNew), Entry ); // restrict to the complement of constraint!!!
    }
    // add the POs
    Aig_ManForEachPo( p, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pNew );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Llb_ManDeriveAigWithHints(): The check has failed.\n" );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDupSimpleDfs_rec( Aig_Man_t * pNew, Aig_Man_t * p, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return (Aig_Obj_t *)pObj->pData;
    Aig_ManDupSimpleDfs_rec( pNew, p, Aig_ObjFanin0(pObj) );
    if ( Aig_ObjIsBuf(pObj) )
        return (Aig_Obj_t *)(pObj->pData = Aig_ObjChild0Copy(pObj));
    Aig_ManDupSimpleDfs_rec( pNew, p, Aig_ObjFanin1(pObj) );
    pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Aig_Regular((Aig_Obj_t *)pObj->pData)->pHaig = pObj->pHaig;
    return (Aig_Obj_t *)pObj->pData;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [Orders nodes as follows: PIs, ANDs, POs.]
               
  SideEffects [This procedure assumes that buffers are not used during
  HAIG recording. This way, each HAIG node is in one-to-one correspondence 
  with old HAIG node. There is no need to create new nodes, just reassign 
  the pointers. If it were not the case, we would need to create HAIG nodes 
  for each new node duplicated. ]

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupSimpleDfs( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i;
    assert( p->pManTime == NULL );
    assert( p->pManHaig == NULL || Aig_ManBufNum(p) == 0 );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nAsserts = p->nAsserts;
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pNew)->pHaig = Aig_ManConst1(p)->pHaig;
    Aig_ManForEachPi( p, pObj, i )
    {
        pObjNew = Aig_ObjCreatePi( pNew );
        pObjNew->pHaig = pObj->pHaig;
        pObjNew->Level = pObj->Level;
        pObj->pData = pObjNew;
    }
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
        if ( !Aig_ObjIsPo(pObj) )
        {
            Aig_ManDupSimpleDfs_rec( pNew, p, pObj );        
            assert( pObj->Level == ((Aig_Obj_t*)pObj->pData)->Level );
        }
    // add the POs
    Aig_ManForEachPo( p, pObj, i )
    {
        pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        pObjNew->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // pass the HAIG manager
    if ( p->pManHaig != NULL )
    {
        pNew->pManHaig = p->pManHaig;  
        p->pManHaig = NULL;
    }
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupSimple(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates part of the AIG manager.]

  Description [Orders nodes as follows: PIs, ANDs, POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupSimpleDfsPart( Aig_Man_t * p, Vec_Ptr_t * vPis, Vec_Ptr_t * vPos )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1( pNew );
    Vec_PtrForEachEntry( Aig_Obj_t *, vPis, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // duplicate internal nodes
    Vec_PtrForEachEntry( Aig_Obj_t *, vPos, pObj, i )
    {
        pObjNew = Aig_ManDupSimpleDfs_rec( pNew, p, Aig_ObjFanin0(pObj) );        
        pObjNew = Aig_NotCond( pObjNew, Aig_ObjFaninC0(pObj) );
        Aig_ObjCreatePo( pNew, pObjNew );
    }
    Aig_ManSetRegNum( pNew, 0 );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupSimple(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [Assumes topological ordering of the nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupOrdered( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i, nNodes;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nAsserts = p->nAsserts;
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // create the PIs
    Aig_ManCleanData( p );
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsBuf(pObj) )
        {
            pObjNew = Aig_ObjChild0Copy(pObj);
        }
        else if ( Aig_ObjIsNode(pObj) )
        {
            pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
        }
        else if ( Aig_ObjIsPi(pObj) )
        {
            pObjNew = Aig_ObjCreatePi( pNew );
            pObjNew->Level = pObj->Level;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        }
        else if ( Aig_ObjIsConst1(pObj) )
        {
            pObjNew = Aig_ManConst1(pNew);
        }
        else
            assert( 0 );
        Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    if ( (nNodes = Aig_ManCleanup( pNew )) )
        printf( "Aig_ManDupOrdered(): Cleanup after AIG duplication removed %d nodes.\n", nNodes );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( (Tim_Man_t *)p->pManTime, 0 );
    // pass the HAIG manager
    if ( p->pManHaig != NULL )
    {
        pNew->pManHaig = p->pManHaig;  
        p->pManHaig = NULL;
    }
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupOrdered(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [Orders nodes as follows: PIs, ANDs, POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupCof( Aig_Man_t * p, int iInput, int Value )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i;
    assert( p->pManTime == NULL );
    assert( p->pManHaig == NULL || Aig_ManBufNum(p) == 0 );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nAsserts = p->nAsserts;
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pNew)->pHaig = Aig_ManConst1(p)->pHaig;
    Aig_ManForEachPi( p, pObj, i )
    {
        if ( i == iInput )
            pObjNew = Value ? Aig_ManConst1(pNew) : Aig_ManConst0(pNew);
        else
        {
            pObjNew = Aig_ObjCreatePi( pNew );
            pObjNew->pHaig = pObj->pHaig;
            pObjNew->Level = pObj->Level;
        }
        pObj->pData = pObjNew;
    }
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
        {
            pObjNew = Aig_ObjChild0Copy(pObj);
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
        else if ( Aig_ObjIsNode(pObj) )
        {
            pObjNew = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
    // add the POs
    Aig_ManForEachPo( p, pObj, i )
    {
        pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        pObjNew->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
//    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    Aig_ManCleanup( pNew );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // pass the HAIG manager
    if ( p->pManHaig != NULL )
    {
        pNew->pManHaig = p->pManHaig;  
        p->pManHaig = NULL;
    }
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupSimple(): The check has failed.\n" );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [Assumes topological ordering of the nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupTrim( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i, nNodes;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nConstrs = p->nConstrs;
    // create the PIs
    Aig_ManCleanData( p );
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsNode(pObj) )
            pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
        else if ( Aig_ObjIsPi(pObj) )
            pObjNew = (Aig_ObjRefs(pObj) > 0 || Saig_ObjIsLo(p, pObj)) ? Aig_ObjCreatePi(pNew) : NULL;
        else if ( Aig_ObjIsPo(pObj) )
            pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        else if ( Aig_ObjIsConst1(pObj) )
            pObjNew = Aig_ManConst1(pNew);
        else
            assert( 0 );
        pObj->pData = pObjNew;
    }
    assert( Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    if ( (nNodes = Aig_ManCleanup( pNew )) )
        printf( "Aig_ManDupTrim(): Cleanup after AIG duplication removed %d nodes.\n", nNodes );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupTrim(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager to have EXOR gates.]

  Description [Assumes topological ordering of the nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupExor( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->fCatchExor = 1;
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nAsserts = p->nAsserts;
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // create the PIs
    Aig_ManCleanData( p );
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsBuf(pObj) )
        {
            pObjNew = Aig_ObjChild0Copy(pObj);
        }
        else if ( Aig_ObjIsNode(pObj) )
        {
            pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
        }
        else if ( Aig_ObjIsPi(pObj) )
        {
            pObjNew = Aig_ObjCreatePi( pNew );
            pObjNew->Level = pObj->Level;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        }
        else if ( Aig_ObjIsConst1(pObj) )
        {
            pObjNew = Aig_ManConst1(pNew);
        }
        else
            assert( 0 );
        Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    Aig_ManCleanup( pNew );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( (Tim_Man_t *)p->pManTime, 0 );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupExor(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDupDfs_rec( Aig_Man_t * pNew, Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pObjNew, * pEquivNew = NULL;
    if ( pObj->pData )
        return (Aig_Obj_t *)pObj->pData;
    if ( p->pEquivs && Aig_ObjEquiv(p, pObj) )
        pEquivNew = Aig_ManDupDfs_rec( pNew, p, Aig_ObjEquiv(p, pObj) );
    Aig_ManDupDfs_rec( pNew, p, Aig_ObjFanin0(pObj) );
    if ( Aig_ObjIsBuf(pObj) )
        return (Aig_Obj_t *)(pObj->pData = Aig_ObjChild0Copy(pObj));
    Aig_ManDupDfs_rec( pNew, p, Aig_ObjFanin1(pObj) );
    pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
    if ( p->pManHaig != NULL )
        Aig_Regular(pObjNew)->pHaig = Aig_NotCond( pObj->pHaig, Aig_IsComplement(pObjNew) );
    else if ( pObj->pHaig )
        Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
    if ( pEquivNew )
    {
        if ( pNew->pEquivs )
            pNew->pEquivs[Aig_Regular(pObjNew)->Id] = Aig_Regular(pEquivNew);        
        if ( pNew->pReprs )
            pNew->pReprs[Aig_Regular(pEquivNew)->Id] = Aig_Regular(pObjNew);
    }
    return (Aig_Obj_t *)(pObj->pData = pObjNew);
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [This duplicator works for AIGs with choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupDfs( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i, nNodes;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nAsserts = p->nAsserts;
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // duplicate representation of choice nodes
    if ( p->pEquivs )
        pNew->pEquivs = ABC_CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
    if ( p->pReprs )
        pNew->pReprs = ABC_CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
    // create the PIs
    Aig_ManCleanData( p );
    // duplicate internal nodes
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pNew)->pHaig = Aig_ManConst1(p)->pHaig;
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsPi(pObj) )
        {
            pObjNew = Aig_ObjCreatePi( pNew );
            pObjNew->Level = pObj->Level;
            pObjNew->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            Aig_ManDupDfs_rec( pNew, p, Aig_ObjFanin0(pObj) );        
//            assert( pObj->Level == ((Aig_Obj_t*)pObj->pData)->Level );
            pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
            pObjNew->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
    }
    assert( p->pEquivs != NULL || Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    if ( p->pEquivs == NULL && p->pReprs == NULL && (nNodes = Aig_ManCleanup( pNew )) )
        printf( "Aig_ManDupDfs(): Cleanup after AIG duplication removed %d nodes.\n", nNodes );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( (Tim_Man_t *)p->pManTime, 0 );
    // pass the HAIG manager
    if ( p->pManHaig != NULL )
    {
        pNew->pManHaig = p->pManHaig;  
        p->pManHaig = NULL;
    }
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupDfs(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [This duplicator works for AIGs with choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManOrderPios( Aig_Man_t * p, Aig_Man_t * pOrder )
{
    Vec_Ptr_t * vPios;
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManPiNum(p) == Aig_ManPiNum(pOrder) );
    assert( Aig_ManPoNum(p) == Aig_ManPoNum(pOrder) );
    Aig_ManSetPioNumbers( pOrder );
    vPios = Vec_PtrAlloc( Aig_ManPiNum(p) + Aig_ManPoNum(p) );
    Aig_ManForEachObj( pOrder, pObj, i )
    {
        if ( Aig_ObjIsPi(pObj) )
            Vec_PtrPush( vPios, Aig_ManPi(p, Aig_ObjPioNum(pObj)) );
        else if ( Aig_ObjIsPo(pObj) )
            Vec_PtrPush( vPios, Aig_ManPo(p, Aig_ObjPioNum(pObj)) );
    }
    Aig_ManCleanPioNumbers( pOrder );
    return vPios;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDupDfsGuided_rec( Aig_Man_t * pNew, Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pObjNew, * pEquivNew = NULL;
    if ( pObj->pData )
        return (Aig_Obj_t *)pObj->pData;
    if ( Aig_ObjIsPi(pObj) )
        return NULL;
    if ( p->pEquivs && Aig_ObjEquiv(p, pObj) )
        pEquivNew = Aig_ManDupDfsGuided_rec( pNew, p, Aig_ObjEquiv(p, pObj) );
    if ( !Aig_ManDupDfsGuided_rec( pNew, p, Aig_ObjFanin0(pObj) ) )
        return NULL;
    if ( Aig_ObjIsBuf(pObj) )
        return (Aig_Obj_t *)(pObj->pData = Aig_ObjChild0Copy(pObj));
    if ( !Aig_ManDupDfsGuided_rec( pNew, p, Aig_ObjFanin1(pObj) ) )
        return NULL;
    pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
    if ( pObj->pHaig )
        Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
    if ( pEquivNew )
    {
        if ( pNew->pEquivs )
            pNew->pEquivs[Aig_Regular(pObjNew)->Id] = Aig_Regular(pEquivNew);        
        if ( pNew->pReprs )
            pNew->pReprs[Aig_Regular(pEquivNew)->Id] = Aig_Regular(pObjNew);
    }
    return (Aig_Obj_t *)(pObj->pData = pObjNew);
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [This duplicator works for AIGs with choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupDfsGuided( Aig_Man_t * p, Vec_Ptr_t * vPios )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i, nNodes;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nAsserts = p->nAsserts;
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // duplicate representation of choice nodes
    if ( p->pEquivs )
    {
        pNew->pEquivs = ABC_ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pEquivs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    if ( p->pReprs )
    {
        pNew->pReprs = ABC_ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pReprs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    // create the PIs
    Aig_ManCleanData( p );
    // duplicate internal nodes
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pNew)->pHaig = Aig_ManConst1(p)->pHaig;
    Vec_PtrForEachEntry( Aig_Obj_t *, vPios, pObj, i )
    {
        if ( Aig_ObjIsPi(pObj) )
        {
            pObjNew = Aig_ObjCreatePi( pNew );
            pObjNew->Level = pObj->Level;
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            Aig_ManDupDfsGuided_rec( pNew, p, Aig_ObjFanin0(pObj) );        
//            assert( pObj->Level == ((Aig_Obj_t*)pObj->pData)->Level );
            pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
            Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
            pObj->pData = pObjNew;
        }
    }
//    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    if ( p->pEquivs == NULL && p->pReprs == NULL && (nNodes = Aig_ManCleanup( pNew )) )
        printf( "Aig_ManDupDfs(): Cleanup after AIG duplication removed %d nodes.\n", nNodes );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( (Tim_Man_t *)p->pManTime, 0 );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupDfs(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [This duplicator works for AIGs with choices.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupLevelized( Aig_Man_t * p )
{
    Vec_Vec_t * vLevels;
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i, k;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nAsserts = p->nAsserts;
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // duplicate representation of choice nodes
    if ( p->pEquivs )
    {
        pNew->pEquivs = ABC_ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pEquivs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    if ( p->pReprs )
    {
        pNew->pReprs = ABC_ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
        memset( pNew->pReprs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    }
    // create the PIs
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManConst1(pNew)->pHaig = Aig_ManConst1(p)->pHaig;
    Aig_ManForEachPi( p, pObj, i )
    {
        pObjNew = Aig_ObjCreatePi( pNew );
        pObjNew->pHaig = pObj->pHaig;
        pObjNew->Level = pObj->Level;
        pObj->pData = pObjNew;
    }
    // duplicate internal nodes
    vLevels = Aig_ManLevelize( p );
    Vec_VecForEachEntry( Aig_Obj_t *, vLevels, pObj, i, k )
    {
        pObjNew = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
        Aig_Regular(pObjNew)->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    Vec_VecFree( vLevels );
    // duplicate POs
    Aig_ManForEachPo( p, pObj, i )
    {
        pObjNew = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        pObjNew->pHaig = pObj->pHaig;
        pObj->pData = pObjNew;
    }
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
//    if ( (nNodes = Aig_ManCleanup( pNew )) )
//        printf( "Aig_ManDupLevelized(): Cleanup after AIG duplication removed %d nodes.\n", nNodes );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // duplicate the timing manager
    if ( p->pManTime )
        pNew->pManTime = Tim_ManDup( (Tim_Man_t *)p->pManTime, 0 );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupLevelized(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [Assumes topological ordering of nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupWithoutPos( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // duplicate internal nodes
    Aig_ManForEachObj( p, pObj, i )
    {
        assert( !Aig_ObjIsBuf(pObj) );
        if ( Aig_ObjIsNode(pObj) )
            pObj->pData = Aig_Oper( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj), Aig_ObjType(pObj) );
    }
    assert( Aig_ManBufNum(p) != 0 || Aig_ManNodeNum(p) == Aig_ManNodeNum(pNew) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager.]

  Description [Assumes topological ordering of nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupFlopsOnly( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    pNew = Aig_ManDupWithoutPos( p );
    Saig_ManForEachLi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pNew );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupFlopsOnly(): The check has failed.\n" );
    return pNew;

}


/**Function*************************************************************

  Synopsis    [Returns representatives of fanin in approapriate polarity.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Aig_Obj_t * Aig_ObjGetRepres( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pRepr;
    if ( (pRepr = Aig_ObjRepr(p, pObj)) )
        return Aig_NotCond( (Aig_Obj_t *)pRepr->pData, pObj->fPhase ^ pRepr->fPhase );
    return (Aig_Obj_t *)pObj->pData;
}
static inline Aig_Obj_t * Aig_ObjChild0Repres( Aig_Man_t * p, Aig_Obj_t * pObj ) { return Aig_NotCond( Aig_ObjGetRepres(p, Aig_ObjFanin0(pObj)), Aig_ObjFaninC0(pObj) ); }
static inline Aig_Obj_t * Aig_ObjChild1Repres( Aig_Man_t * p, Aig_Obj_t * pObj ) { return Aig_NotCond( Aig_ObjGetRepres(p, Aig_ObjFanin1(pObj)), Aig_ObjFaninC1(pObj) ); }

/**Function*************************************************************

  Synopsis    [Duplicates AIG while substituting representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupRepres( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // start the HOP package
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // map the const and primary inputs
    Aig_ManCleanData( p );
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsNode(pObj) )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Repres(p, pObj), Aig_ObjChild1Repres(p, pObj) );
        else if ( Aig_ObjIsPi(pObj) )
        {
            pObj->pData = Aig_ObjCreatePi(pNew);
            pObj->pData = Aig_ObjGetRepres( p, pObj );
        }
        else if ( Aig_ObjIsPo(pObj) )
            pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Repres(p, pObj) );
        else if ( Aig_ObjIsConst1(pObj) )
            pObj->pData = Aig_ManConst1(pNew);
        else
            assert( 0 );
    }
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // check the new manager
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupRepres: Check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDupRepres_rec( Aig_Man_t * pNew, Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pRepr;
    if ( pObj->pData )
        return (Aig_Obj_t *)pObj->pData;
    if ( (pRepr = Aig_ObjRepr(p, pObj)) )
    {
        Aig_ManDupRepres_rec( pNew, p, pRepr );
        return (Aig_Obj_t *)(pObj->pData = Aig_NotCond( (Aig_Obj_t *)pRepr->pData, pRepr->fPhase ^ pObj->fPhase ));
    }
    Aig_ManDupRepres_rec( pNew, p, Aig_ObjFanin0(pObj) );
    Aig_ManDupRepres_rec( pNew, p, Aig_ObjFanin1(pObj) );
    return (Aig_Obj_t *)(pObj->pData = Aig_And( pNew, Aig_ObjChild0Repres(p, pObj), Aig_ObjChild1Repres(p, pObj) ));
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG while substituting representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupRepresDfs( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // start the HOP package
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nConstrs = p->nConstrs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // map the const and primary inputs
    Aig_ManCleanData( p );
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsNode(pObj) )
            continue;
        if ( Aig_ObjIsPi(pObj) )
            pObj->pData = Aig_ObjCreatePi(pNew);
        else if ( Aig_ObjIsPo(pObj) )
        {
            Aig_ManDupRepres_rec( pNew, p, Aig_ObjFanin0(pObj) );
            pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Repres(p, pObj) );
        }
        else if ( Aig_ObjIsConst1(pObj) )
            pObj->pData = Aig_ManConst1(pNew);
        else 
            assert( 0 );
    }
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // check the new manager
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupRepresDfs: Check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Creates the miter of the two AIG managers.]

  Description [Oper is the operation to perform on the outputs of the miter.
  Oper == 0 is XOR
  Oper == 1 is complemented implication (p1 => p2)
  Oper == 2 is OR
  Oper == 3 is AND
  ]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManCreateMiter( Aig_Man_t * p1, Aig_Man_t * p2, int Oper )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManRegNum(p1) == 0 );
    assert( Aig_ManRegNum(p2) == 0 );
    assert( Aig_ManPoNum(p1) == 1 );
    assert( Aig_ManPoNum(p2) == 1 );
    assert( Aig_ManPiNum(p1) == Aig_ManPiNum(p2) );
    pNew = Aig_ManStart( Aig_ManObjNumMax(p1) + Aig_ManObjNumMax(p2) );
    // add first AIG
    Aig_ManConst1(p1)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p1, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Aig_ManForEachNode( p1, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // add second AIG
    Aig_ManConst1(p2)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p2, pObj, i )
        pObj->pData = Aig_ManPi( pNew, i );
    Aig_ManForEachNode( p2, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // add the output
    if ( Oper == 0 ) // XOR
        pObj = Aig_Exor( pNew, Aig_ObjChild0Copy(Aig_ManPo(p1,0)), Aig_ObjChild0Copy(Aig_ManPo(p2,0)) );
    else if ( Oper == 1 ) // implication is PO(p1) -> PO(p2)  ...  complement is PO(p1) & !PO(p2) 
        pObj = Aig_And( pNew, Aig_ObjChild0Copy(Aig_ManPo(p1,0)), Aig_Not(Aig_ObjChild0Copy(Aig_ManPo(p2,0))) );
    else if ( Oper == 2 ) // OR
        pObj = Aig_Or( pNew, Aig_ObjChild0Copy(Aig_ManPo(p1,0)), Aig_ObjChild0Copy(Aig_ManPo(p2,0)) );
    else if ( Oper == 3 ) // AND
        pObj = Aig_And( pNew, Aig_ObjChild0Copy(Aig_ManPo(p1,0)), Aig_ObjChild0Copy(Aig_ManPo(p2,0)) );
    else
        assert( 0 );
    Aig_ObjCreatePo( pNew, pObj );
    Aig_ManCleanup( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG with only one primary output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupOrpos( Aig_Man_t * p, int fAddRegs )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pMiter;
    int i;
    assert( Aig_ManRegNum(p) > 0 );
    if ( p->nConstrs > 0 )
    {
        printf( "The AIG manager should have no constraints.\n" );
        return NULL;
    }
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // set registers
    pNew->nRegs    = fAddRegs? p->nRegs : 0;
    pNew->nTruePis = fAddRegs? p->nTruePis : p->nTruePis + p->nRegs;
    pNew->nTruePos = 1;
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create the PO
    pMiter = Aig_ManConst0(pNew);
    Aig_ManForEachPoSeq( p, pObj, i )
        pMiter = Aig_Or( pNew, pMiter, Aig_ObjChild0Copy(pObj) ); 
    Aig_ObjCreatePo( pNew, pMiter );
    // create register inputs with MUXes
    if ( fAddRegs )
    {
        Aig_ManForEachLiSeq( p, pObj, i )
            Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Aig_ManCleanup( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG with only one primary output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupOneOutput( Aig_Man_t * p, int iPoNum, int fAddRegs )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManRegNum(p) > 0 );
    assert( iPoNum < Aig_ManPoNum(p)-Aig_ManRegNum(p) );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // set registers
    pNew->nRegs    = fAddRegs? p->nRegs : 0;
    pNew->nTruePis = fAddRegs? p->nTruePis : p->nTruePis + p->nRegs;
    pNew->nTruePos = 1;
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create the PO
    pObj = Aig_ManPo( p, iPoNum );
    Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    // create register inputs with MUXes
    if ( fAddRegs )
    {
        Aig_ManForEachLiSeq( p, pObj, i )
            Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Aig_ManCleanup( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG with only one primary output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupUnsolvedOutputs( Aig_Man_t * p, int fAddRegs )
{ 
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i, nOuts = 0;
    assert( Aig_ManRegNum(p) > 0 );
    if ( p->nConstrs > 0 )
    {
        printf( "The AIG manager should have no constraints.\n" );
        return NULL;
    }
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    // create the POs
    nOuts = 0;
    Aig_ManForEachPoSeq( p, pObj, i )
        nOuts += ( Aig_ObjFanin0(pObj) != Aig_ManConst1(p) );
    // set registers
    pNew->nRegs    = fAddRegs? p->nRegs : 0;
    pNew->nTruePis = fAddRegs? p->nTruePis : p->nTruePis + p->nRegs;
    pNew->nTruePos = nOuts;
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create the PO
    Aig_ManForEachPoSeq( p, pObj, i )
        if ( Aig_ObjFanin0(pObj) != Aig_ManConst1(p) )
            Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    // create register inputs with MUXes
    if ( fAddRegs )
    {
        Aig_ManForEachLiSeq( p, pObj, i )
            Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Aig_ManCleanup( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG with only one primary output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupArray( Vec_Ptr_t * vArray )
{
    Aig_Man_t * p, * pNew;
    Aig_Obj_t * pObj;
    int i, k;
    if ( Vec_PtrSize(vArray) == 0 )
        return NULL;
    p = (Aig_Man_t *)Vec_PtrEntry( vArray, 0 );
    Vec_PtrForEachEntry( Aig_Man_t *, vArray, pNew, k )
    {
        assert( Aig_ManRegNum(pNew) == 0 );
        assert( Aig_ManPiNum(pNew) == Aig_ManPiNum(p) );
    }
    // create the new manager
    pNew = Aig_ManStart( 10000 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    Aig_ManForEachPi( p, pObj, i )
        Aig_ObjCreatePi(pNew);
    // create the PIs
    Vec_PtrForEachEntry( Aig_Man_t *, vArray, p, k )
    {
        Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
        Aig_ManForEachPi( p, pObj, i )
            pObj->pData = Aig_ManPi( pNew, i );
        Aig_ManForEachNode( p, pObj, i )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        Aig_ManForEachPo( p, pObj, i )
            Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupSimple(): The check has failed.\n" );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

