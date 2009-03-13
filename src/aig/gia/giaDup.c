/**CFile****************************************************************

  FileName    [giaDup.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Duplication procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaDup.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Duplicates AIG without any changes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDup( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates while adding self-loops to the registers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupSelf( Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pTemp; 
    Gia_Obj_t * pObj;
    int i, iCtrl;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    iCtrl = Gia_ManAppendCi( pNew );
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachPo( p, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy(pObj);
    Gia_ManForEachRi( p, pObj, i )
        pObj->Value = Gia_ManHashMux( pNew, iCtrl, Gia_ObjFanin0Copy(pObj), Gia_ObjRiToRo(p, pObj)->Value );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, pObj->Value );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG without any changes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupMarked( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, nRos = 0, nRis = 0;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( pObj->fMark0 )
            continue;
        if ( Gia_ObjIsAnd(pObj) )
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else if ( Gia_ObjIsCi(pObj) )
        {
            pObj->Value = Gia_ManAppendCi( pNew );
            nRos += Gia_ObjIsRo(p, pObj);
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
            nRis += Gia_ObjIsRi(p, pObj);
        }
    }
    assert( nRos == nRis );
    Gia_ManSetRegNum( pNew, nRos );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG while creating "parallel" copies.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupTimes( Gia_Man_t * p, int nTimes )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vPis, * vPos, * vRis, * vRos;
    int i, t, Entry;
    assert( nTimes > 0 );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    vPis = Vec_IntAlloc( Gia_ManPiNum(p) * nTimes );
    vPos = Vec_IntAlloc( Gia_ManPoNum(p) * nTimes );
    vRis = Vec_IntAlloc( Gia_ManRegNum(p) * nTimes );
    vRos = Vec_IntAlloc( Gia_ManRegNum(p) * nTimes );
    for ( t = 0; t < nTimes; t++ )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsAnd(pObj) )
                pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
            else if ( Gia_ObjIsCi(pObj) )
            {
                pObj->Value = Gia_ManAppendCi( pNew );
                if ( Gia_ObjIsPi(p, pObj) )
                    Vec_IntPush( vPis, Gia_Lit2Var(pObj->Value) );
                else
                    Vec_IntPush( vRos, Gia_Lit2Var(pObj->Value) );
            }
            else if ( Gia_ObjIsCo(pObj) )
            {
                pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
                if ( Gia_ObjIsPo(p, pObj) )
                    Vec_IntPush( vPos, Gia_Lit2Var(pObj->Value) );
                else
                    Vec_IntPush( vRis, Gia_Lit2Var(pObj->Value) );
            }
        }
    }
    Vec_IntClear( pNew->vCis );
    Vec_IntForEachEntry( vPis, Entry, i )
    {
        Gia_ObjSetCioId( Gia_ManObj(pNew, Entry), Vec_IntSize(pNew->vCis) );
        Vec_IntPush( pNew->vCis, Entry );
    }
    Vec_IntForEachEntry( vRos, Entry, i )
    {
        Gia_ObjSetCioId( Gia_ManObj(pNew, Entry), Vec_IntSize(pNew->vCis) );
        Vec_IntPush( pNew->vCis, Entry );
    }
    Vec_IntClear( pNew->vCos );
    Vec_IntForEachEntry( vPos, Entry, i )
    {
        Gia_ObjSetCioId( Gia_ManObj(pNew, Entry), Vec_IntSize(pNew->vCos) );
        Vec_IntPush( pNew->vCos, Entry );
    }
    Vec_IntForEachEntry( vRis, Entry, i )
    {
        Gia_ObjSetCioId( Gia_ManObj(pNew, Entry), Vec_IntSize(pNew->vCos) );
        Vec_IntPush( pNew->vCos, Entry );
    }
    Vec_IntFree( vPis );
    Vec_IntFree( vPos );
    Vec_IntFree( vRis );
    Vec_IntFree( vRos );
    Gia_ManSetRegNum( pNew, nTimes * Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManDupDfs2_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return pObj->Value;
    if ( p->pReprsOld && ~p->pReprsOld[Gia_ObjId(p, pObj)] )
    {
        Gia_Obj_t * pRepr = Gia_ManObj( p, p->pReprsOld[Gia_ObjId(p, pObj)] );
        pRepr->Value = Gia_ManDupDfs2_rec( pNew, p, pRepr );
        return pObj->Value = Gia_LitNotCond( pRepr->Value, Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) );
    }
    if ( Gia_ObjIsCi(pObj) )
        return pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManDupDfs2_rec( pNew, p, Gia_ObjFanin0(pObj) );
    if ( Gia_ObjIsCo(pObj) )
        return pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManDupDfs2_rec( pNew, p, Gia_ObjFanin1(pObj) );
    if ( pNew->pHTable )
        return pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    return pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupDfs2( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj, * pObjNew;
    int i;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManDupDfs2_rec( pNew, p, pObj );
    Gia_ManForEachCi( p, pObj, i )
        if ( ~pObj->Value == 0 )
            pObj->Value = Gia_ManAppendCi(pNew);
    assert( Gia_ManCiNum(pNew) == Gia_ManCiNum(p) );
    // remap combinational inputs
    Gia_ManForEachCi( p, pObj, i )
    {
        pObjNew = Gia_ObjFromLit( pNew, pObj->Value );
        assert( !Gia_IsComplement(pObjNew) );
        Vec_IntWriteEntry( pNew->vCis, Gia_ObjCioId(pObj), Gia_ObjId(pNew, pObjNew) );
        Gia_ObjSetCioId( pObjNew, Gia_ObjCioId(pObj) );
    }
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDupDfs_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManDupDfs_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManDupDfs_rec( pNew, p, Gia_ObjFanin1(pObj) );
    pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupDfs( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManDupDfs_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order while putting CIs first.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupDfsSkip( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachCo( p, pObj, i )
        if ( pObj->fMark1 == 0 )
            Gia_ManDupDfs_rec( pNew, p, pObj );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order while putting CIs first.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupDfsCone( Gia_Man_t * p, Gia_Obj_t * pRoot )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    assert( Gia_ObjIsCo(pRoot) );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManDupDfs_rec( pNew, p, pRoot );
    Gia_ManSetRegNum( pNew, 0 );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order while putting CIs first.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupDfsLitArray( Gia_Man_t * p, Vec_Int_t * vLits )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, iLit, iLitRes;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Vec_IntForEachEntry( vLits, iLit, i )
    {
        iLitRes = Gia_ManDupDfs2_rec( pNew, p, Gia_ManObj(p, Gia_Lit2Var(iLit)) );
        Gia_ManAppendCo( pNew, Gia_LitNotCond( iLitRes, Gia_LitIsCompl(iLit)) );
    }
    Gia_ManSetRegNum( pNew, 0 );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order while putting CIs first.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupNormalized( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    assert( Gia_ManIsNormalized(pNew) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order while putting CIs first.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupTrimmed( Gia_Man_t * p, int fTrimCis, int fTrimCos )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManSetRefs( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        if ( !fTrimCis || pObj->Value > 0 || Gia_ObjIsRo(p, pObj) )
            pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        if ( !fTrimCos || !Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) || Gia_ObjIsRi(p, pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Print representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintRepr( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
        if ( ~p->pReprsOld[i] )
            printf( "%d->%d ", i, p->pReprs[i] );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupDfsCiMap( Gia_Man_t * p, int * pCi2Lit, Vec_Int_t * vLits )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
    {
        pObj->Value = Gia_ManAppendCi(pNew);
        if ( ~pCi2Lit[i] )
            pObj->Value = Gia_LitNotCond( Gia_ManObj(p, Gia_Lit2Var(pCi2Lit[i]))->Value, Gia_LitIsCompl(pCi2Lit[i]) );
    }
    Gia_ManHashAlloc( pNew );
    if ( vLits )
    {
        int iLit, iLitRes;
        Vec_IntForEachEntry( vLits, iLit, i )
        {
            iLitRes = Gia_ManDupDfs2_rec( pNew, p, Gia_ManObj(p, Gia_Lit2Var(iLit)) );
            Gia_ManAppendCo( pNew, Gia_LitNotCond( iLitRes, Gia_LitIsCompl(iLit)) );
        }
    }
    else
    {
        Gia_ManForEachCo( p, pObj, i )
            Gia_ManDupDfs_rec( pNew, p, pObj );
    }
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupDfsClasses( Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    assert( p->pReprsOld != NULL );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManDupDfs_rec( pNew, p, pObj );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Detect topmost gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupTopAnd_iter( Gia_Man_t * p, int fVerbose )  
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vFront, * vLeaves;
    int i, iLit, iObjId, nCiLits, * pCi2Lit;
    char * pVar2Val;
    // collect the frontier
    vFront = Vec_IntAlloc( 1000 );
    vLeaves = Vec_IntAlloc( 1000 );
    Gia_ManForEachCo( p, pObj, i )
    {
        if ( Gia_ObjIsConst0( Gia_ObjFanin0(pObj) ) )
            continue;
        if ( Gia_ObjFaninC0(pObj) )
            Vec_IntPush( vLeaves, Gia_ObjFaninLit0p(p, pObj) );
        else
            Vec_IntPush( vFront, Gia_ObjFaninId0p(p, pObj) );
    }
    if ( Vec_IntSize(vFront) == 0 )
    {
        if ( fVerbose )
            printf( "The AIG cannot be decomposed using AND-decomposition.\n" );
        Vec_IntFree( vFront );
        Vec_IntFree( vLeaves );
        return Gia_ManDupNormalized( p );
    }
    // expand the frontier
    Gia_ManForEachObjVec( vFront, p, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
        {
            Vec_IntPush( vLeaves, Gia_Var2Lit( Gia_ObjId(p, pObj), 0 ) );
            continue;
        }
        assert( Gia_ObjIsAnd(pObj) );
        if ( Gia_ObjFaninC0(pObj) )
            Vec_IntPush( vLeaves, Gia_ObjFaninLit0p(p, pObj) );
        else
            Vec_IntPush( vFront, Gia_ObjFaninId0p(p, pObj) );
        if ( Gia_ObjFaninC1(pObj) )
            Vec_IntPush( vLeaves, Gia_ObjFaninLit1p(p, pObj) );
        else
            Vec_IntPush( vFront, Gia_ObjFaninId1p(p, pObj) );
    }
    Vec_IntFree( vFront );
    // sort the literals
    nCiLits = 0;
    pCi2Lit = ABC_FALLOC( int, Gia_ManObjNum(p) );
    pVar2Val = ABC_FALLOC( char, Gia_ManObjNum(p) );
    Vec_IntForEachEntry( vLeaves, iLit, i )
    {
        iObjId = Gia_Lit2Var(iLit);
        pObj = Gia_ManObj(p, iObjId);
        if ( Gia_ObjIsCi(pObj) )
        {
            pCi2Lit[Gia_ObjCioId(pObj)] = !Gia_LitIsCompl(iLit);
            nCiLits++;
        }
        if ( pVar2Val[iObjId] != 0 && pVar2Val[iObjId] != 1 )
            pVar2Val[iObjId] = Gia_LitIsCompl(iLit);
        else if ( pVar2Val[iObjId] != Gia_LitIsCompl(iLit) )
            break;
    }
    if ( i < Vec_IntSize(vLeaves) )
    {
        printf( "Problem is trivially UNSAT.\n" );
        ABC_FREE( pCi2Lit );
        ABC_FREE( pVar2Val );
        Vec_IntFree( vLeaves );
        return Gia_ManDupNormalized( p );
    }
    // create array of input literals
    Vec_IntClear( vLeaves );
    Gia_ManForEachObj( p, pObj, i )
        if ( !Gia_ObjIsCi(pObj) && (pVar2Val[i] == 0 || pVar2Val[i] == 1) )
            Vec_IntPush( vLeaves, Gia_Var2Lit(i, pVar2Val[i]) );
    if ( fVerbose )
        printf( "Detected %6d AND leaves and %6d CI leaves.\n", Vec_IntSize(vLeaves), nCiLits );
    // create the input map
    if ( nCiLits == 0 )
        pNew = Gia_ManDupDfsLitArray( p, vLeaves );
    else
        pNew = Gia_ManDupDfsCiMap( p, pCi2Lit, vLeaves );
    ABC_FREE( pCi2Lit );
    ABC_FREE( pVar2Val );
    Vec_IntFree( vLeaves );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Detect topmost gate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupTopAnd( Gia_Man_t * p, int fVerbose )  
{
    Gia_Man_t * pNew, * pTemp;
    int fContinue, iIter = 0;
    pNew = Gia_ManDupNormalized( p );
    for ( fContinue = 1; fContinue; )
    {
        pNew = Gia_ManDupTopAnd_iter( pTemp = pNew, fVerbose );
        if ( Gia_ManCoNum(pNew) == Gia_ManCoNum(pTemp) && Gia_ManAndNum(pNew) == Gia_ManAndNum(pTemp) )
            fContinue = 0;
        Gia_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "Iter %2d : ", ++iIter );
            Gia_ManPrintStatsShort( pNew );
        }
    }
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManMiter_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return pObj->Value;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManMiter_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManMiter_rec( pNew, p, Gia_ObjFanin1(pObj) );
    return pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Creates miter of two designs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManMiter( Gia_Man_t * p0, Gia_Man_t * p1, int fDualOut, int fSeq, int fVerbose )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, iLit;
    if ( fSeq )
    {
        if ( Gia_ManPiNum(p0) != Gia_ManPiNum(p1) )
        {
            printf( "Gia_ManMiter(): Designs have different number of PIs.\n" );
            return NULL;
        }
        if ( Gia_ManPoNum(p0) != Gia_ManPoNum(p1) )
        {
            printf( "Gia_ManMiter(): Designs have different number of POs.\n" );
            return NULL;
        }
        if ( Gia_ManRegNum(p0) == 0 || Gia_ManRegNum(p1) == 0 )
        {
            printf( "Gia_ManMiter(): At least one of the designs has no registers.\n" );
            return NULL;
        }
    }
    else
    {
        if ( Gia_ManCiNum(p0) != Gia_ManCiNum(p1) )
        {
            printf( "Gia_ManMiter(): Designs have different number of CIs.\n" );
            return NULL;
        }
        if ( Gia_ManCoNum(p0) != Gia_ManCoNum(p1) )
        {
            printf( "Gia_ManMiter(): Designs have different number of COs.\n" );
            return NULL;
        }
    }
    // start the manager
    pNew = Gia_ManStart( Gia_ManObjNum(p0) + Gia_ManObjNum(p1) );
    pNew->pName = Aig_UtilStrsav( "miter" );
    // map combinational inputs
    Gia_ManFillValue( p0 );
    Gia_ManFillValue( p1 );
    Gia_ManConst0(p0)->Value = 0;
    Gia_ManConst0(p1)->Value = 0;
    // map internal nodes and outputs
    Gia_ManHashAlloc( pNew );
    if ( fSeq )
    {
        // create primary inputs
        Gia_ManForEachPi( p0, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
        Gia_ManForEachPi( p1, pObj, i )
            pObj->Value = Gia_ObjToLit( pNew, Gia_ManPi(pNew, i) );
        // create latch outputs
        Gia_ManForEachRo( p0, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
        Gia_ManForEachRo( p1, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
        // create primary outputs
        Gia_ManForEachPo( p0, pObj, i )
        {
            Gia_ManMiter_rec( pNew, p0, Gia_ObjFanin0(pObj) );
            Gia_ManMiter_rec( pNew, p1, Gia_ObjFanin0(Gia_ManPo(p1,i)) );
            if ( fDualOut )
            {
                Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
                Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(Gia_ManPo(p1,i)) );
            }
            else
            {
                iLit = Gia_ManHashXor( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin0Copy(Gia_ManPo(p1,i)) );
                Gia_ManAppendCo( pNew, iLit );
            }
        }
        // create register inputs
        Gia_ManForEachRi( p0, pObj, i )
        {
            Gia_ManMiter_rec( pNew, p0, Gia_ObjFanin0(pObj) );
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        }
        Gia_ManForEachRi( p1, pObj, i )
        {
            Gia_ManMiter_rec( pNew, p1, Gia_ObjFanin0(pObj) );
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        }
        Gia_ManSetRegNum( pNew, Gia_ManRegNum(p0) + Gia_ManRegNum(p1) );
    }
    else
    {
        // create combinational inputs
        Gia_ManForEachCi( p0, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
        Gia_ManForEachCi( p1, pObj, i )
            pObj->Value = Gia_ObjToLit( pNew, Gia_ManCi(pNew, i) );
        // create combinational outputs
        Gia_ManForEachCo( p0, pObj, i )
        {
            Gia_ManMiter_rec( pNew, p0, Gia_ObjFanin0(pObj) );
            Gia_ManMiter_rec( pNew, p1, Gia_ObjFanin0(Gia_ManCo(p1,i)) );
            if ( fDualOut )
            {
                Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
                Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(Gia_ManCo(p1,i)) );
            }
            else
            {
                iLit = Gia_ManHashXor( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin0Copy(Gia_ManCo(p1,i)) );
                Gia_ManAppendCo( pNew, iLit );
            }
        }
    }
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Transforms the circuit into a regular miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManTransformMiter( Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pObj2;
    int i, iLit;
    assert( (Gia_ManPoNum(p) & 1) == 0 );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachPo( p, pObj, i )
    {
        pObj2 = Gia_ManPo( p, ++i );
        iLit = Gia_ManHashXor( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin0Copy(pObj2) );
        Gia_ManAppendCo( pNew, iLit );
    }
    Gia_ManForEachRi( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


