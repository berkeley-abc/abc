/**CFile****************************************************************

  FileName    [giaMfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Interface with the MFS package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaMfs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "bool/kit/kit.h"
#include "opt/sfm/sfm.h"
#include "misc/tim/tim.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static word s_ElemVar  = ABC_CONST(0xAAAAAAAAAAAAAAAA);
static word s_ElemVar2 = ABC_CONST(0xCCCCCCCCCCCCCCCC);

extern int Kit_TruthToGia( Gia_Man_t * pMan, unsigned * pTruth, int nVars, Vec_Int_t * vMemory, Vec_Int_t * vLeaves, int fHash );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManExtractMfs_rec( Gia_Man_t * p, int iObj, Vec_Int_t * vId2Mfs, Vec_Wec_t * vFanins, Vec_Str_t * vFixed, Vec_Wrd_t * vTruths, Vec_Wrd_t * vTruthsTemp )
{
    Vec_Int_t * vArray;
    int i, Fanin;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    assert( Gia_ObjIsLut(p, iObj) );
    if ( !~pObj->Value )
        return;
    Gia_LutForEachFanin( p, iObj, Fanin, i )
        Gia_ManExtractMfs_rec( p, Fanin, vId2Mfs, vFanins, vFixed, vTruths, vTruthsTemp );
    pObj->Value = Vec_WecSize(vFanins);
    vArray = Vec_WecPushLevel( vFanins );
    Vec_IntGrow( vArray, Gia_ObjLutSize(p, iObj) );
    Gia_LutForEachFanin( p, iObj, Fanin, i )
        Vec_IntPush( vArray, Gia_ManObj(p, Fanin)->Value );
    Vec_StrPush( vFixed, (char)0 );
    Vec_WrdPush( vTruths, Gia_ObjComputeTruthTable6Lut(p, iObj, vTruthsTemp) );
    Vec_IntWriteEntry( vId2Mfs, iObj, pObj->Value );
}
void Gia_ManExtractMfs_rec2( Gia_Man_t * p, int iObj, Vec_Int_t * vId2Mfs, Vec_Wec_t * vFanins, Vec_Str_t * vFixed, Vec_Wrd_t * vTruths )
{
    Vec_Int_t * vArray;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManExtractMfs_rec2( p, Gia_ObjFaninId0(pObj, iObj), vId2Mfs, vFanins, vFixed, vTruths );
    Gia_ManExtractMfs_rec2( p, Gia_ObjFaninId1(pObj, iObj), vId2Mfs, vFanins, vFixed, vTruths );
    pObj->Value = Vec_WecSize(vFanins);
    vArray = Vec_WecPushLevel( vFanins );
    Vec_IntGrow( vArray, 2 );
    Vec_IntPush( vArray, Gia_ObjFanin0(pObj)->Value );
    Vec_IntPush( vArray, Gia_ObjFanin1(pObj)->Value );
    Vec_StrPush( vFixed, (char)1 );
    Vec_WrdPush( vTruths, (Gia_ObjFaninC0(pObj) ? ~s_ElemVar : s_ElemVar) & (Gia_ObjFaninC1(pObj) ? ~s_ElemVar2 : s_ElemVar2) );
    Vec_IntWriteEntry( vId2Mfs, iObj, pObj->Value );
}
Sfm_Ntk_t * Gia_ManExtractMfs( Gia_Man_t * p, Gia_Man_t * pBoxes, Vec_Int_t ** pvId2Mfs )
{
    Tim_Man_t * pManTime = (Tim_Man_t *)p->pManTime;
    Vec_Int_t * vPoNodes;
    Vec_Int_t * vId2Mfs;
    Vec_Wec_t * vFanins;
    Vec_Str_t * vFixed;
    Vec_Wrd_t * vTruths, * vTruthsTemp;
    Vec_Int_t * vArray;
    Gia_Obj_t * pObj, * pObjBox;
    int i, k, nRealPis, nRealPos, nPiNum, nPoNum, curCi, curCo;
    assert( pManTime == NULL || Tim_ManCiNum(pManTime) == Gia_ManCiNum(p) );
    assert( pManTime == NULL || Tim_ManCoNum(pManTime) == Gia_ManCoNum(p) );
    // get the real number of PIs and POs
    nRealPis = pManTime ? Tim_ManPiNum(pManTime) : Gia_ManCiNum(p);
    nRealPos = pManTime ? Tim_ManPoNum(pManTime) : Gia_ManCoNum(p);
    // create mapping from GIA into MFS
    vId2Mfs  = Vec_IntStartFull( Gia_ManObjNum(p) );
    // collect PO nodes
    vPoNodes = Vec_IntAlloc( 1000 );
    // create the arrays
    vFanins  = Vec_WecAlloc( 1000 );
    vFixed   = Vec_StrAlloc( 1000 );
    vTruths  = Vec_WrdAlloc( 1000 );
    vTruthsTemp = Vec_WrdStart( Gia_ManObjNum(p) );
    // assign MFS ids to primary inputs
    Gia_ManFillValue( p );
    for ( i = 0; i < nRealPis; i++ )
    {
        pObj = Gia_ManPi( p, i );
        pObj->Value = Vec_WecSize(vFanins);
        Vec_WecPushLevel( vFanins );
        Vec_StrPush( vFixed, (char)0 );
        Vec_WrdPush( vTruths, (word)0 );
        Vec_IntWriteEntry( vId2Mfs, Gia_ObjId(p, pObj), pObj->Value );
    }
    // assign MFS ids to black box outputs
    curCi = nRealPis;
    curCo = 0;
    if ( pManTime )
    for ( i = 0; i < Tim_ManBoxNum(pManTime); i++ )
    {
        if ( !Tim_ManBoxIsBlack(pManTime, i) )
        {
            // collect POs
            for ( k = 0; k < Tim_ManBoxInputNum(pManTime, i); k++ )
            {
                pObj = Gia_ManPo( p, curCo + k );
                Vec_IntPush( vPoNodes, Gia_ObjId(p, pObj) );
            }
            // assign values to the PIs
            for ( k = 0; k < Tim_ManBoxOutputNum(pManTime, i); k++ )
            {
                pObj = Gia_ManPi( p, curCi + k );
                pObj->Value = Vec_WecSize(vFanins);
                Vec_WecPushLevel( vFanins );
                Vec_StrPush( vFixed, (char)1 );
                Vec_WrdPush( vTruths, (word)0 );
                Vec_IntWriteEntry( vId2Mfs, Gia_ObjId(p, pObj), pObj->Value );
            }
        }
        curCo += Tim_ManBoxInputNum(pManTime, i);
        curCi += Tim_ManBoxOutputNum(pManTime, i);
    }
    // collect POs
//    for ( i = Tim_ManCoNum(pManTime) - Tim_ManPoNum(pManTime); i < Tim_ManCoNum(pManTime); i++ )
    for ( i = Gia_ManCoNum(p) - nRealPos; i < Gia_ManCoNum(p); i++ )
    {
        pObj = Gia_ManPo( p, i );
        Vec_IntPush( vPoNodes, Gia_ObjId(p, pObj) );
    }
    curCo += nRealPos;
    // verify counts
    assert( curCi == Gia_ManPiNum(p) );
    assert( curCo == Gia_ManPoNum(p) );
    // remeber the end of PIs
    nPiNum = Vec_WecSize(vFanins);
    nPoNum = Vec_IntSize(vPoNodes);
    // assign value to constant node
    pObj = Gia_ManConst0(p);
    Vec_IntWriteEntry( vId2Mfs, Gia_ObjId(p, pObj), Vec_WecSize(vFanins) );
    pObj->Value = Vec_WecSize(vFanins);
    Vec_WecPushLevel( vFanins );
    Vec_StrPush( vFixed, (char)0 );
    Vec_WrdPush( vTruths, (word)0 );
    Vec_IntWriteEntry( vId2Mfs, Gia_ObjId(p, pObj), pObj->Value );
    // create internal nodes
    curCi = nRealPis;
    curCo = 0;
    if ( pManTime )
    for ( i = 0; i < Tim_ManBoxNum(pManTime); i++ )
    {
        // recursively add for box inputs
        Gia_ManIncrementTravId( pBoxes );
        for ( k = 0; k < Tim_ManBoxInputNum(pManTime, i); k++ )
        {
            // build logic
            pObj = Gia_ManPo( p, curCo + k );
            Gia_ManExtractMfs_rec( p, Gia_ObjFaninId0p(p, pObj), vId2Mfs, vFanins, vFixed, vTruths, vTruthsTemp );
            // add buffer/inverter
            pObj->Value = Vec_WecSize(vFanins);
            vArray = Vec_WecPushLevel( vFanins );
            Vec_IntGrow( vArray, 1 );
            assert( !~Gia_ObjFanin0(pObj)->Value );
            Vec_IntPush( vArray, Gia_ObjFanin0(pObj)->Value );
            Vec_StrPush( vFixed, (char)0 );
            Vec_WrdPush( vTruths, Gia_ObjFaninC0(pObj) ? ~s_ElemVar : s_ElemVar );
            Vec_IntWriteEntry( vId2Mfs, Gia_ObjId(p, pObj), pObj->Value );
            // transfer to the PI
            pObjBox = Gia_ManPi( pBoxes, k );
            pObjBox->Value = pObj->Value;
            Gia_ObjSetTravIdCurrent( pBoxes, pObjBox );
        }
        if ( !Tim_ManBoxIsBlack(pManTime, i) )
        {
            pObjBox = Gia_ManConst0(pBoxes);
            pObjBox->Value = Vec_WecSize(vFanins);
            Vec_WecPushLevel( vFanins );
            Vec_StrPush( vFixed, (char)0 );
            Vec_WrdPush( vTruths, (word)0 );
            Gia_ObjSetTravIdCurrent( pBoxes, pObjBox );
            // add internal nodes and transfer
            for ( k = 0; k < Tim_ManBoxOutputNum(pManTime, i); k++ )
            {
                // build logic
                pObjBox = Gia_ManPo( pBoxes, curCi - Tim_ManPiNum(pManTime) + k );
                Gia_ManExtractMfs_rec2( pBoxes, Gia_ObjFaninId0p(pBoxes, pObjBox), vId2Mfs, vFanins, vFixed, vTruths );
                // add buffer/inverter
                vArray = Vec_WecPushLevel( vFanins );
                Vec_IntGrow( vArray, 1 );
                assert( !~Gia_ObjFanin0(pObjBox)->Value );
                Vec_IntPush( vArray, Gia_ObjFanin0(pObjBox)->Value );
                Vec_StrPush( vFixed, (char)1 );
                Vec_WrdPush( vTruths, Gia_ObjFaninC0(pObjBox) ? ~s_ElemVar : s_ElemVar );
                // transfer to the PI
                pObj = Gia_ManPi( p, curCi + k );
                pObj->Value = pObjBox->Value;
            }
        }
        curCo += Tim_ManBoxInputNum(pManTime, i);
        curCi += Tim_ManBoxOutputNum(pManTime, i);
    }
    // create POs with buffers
    Gia_ManForEachObjVec( vPoNodes, p, pObj, i )
    {
        Gia_ManExtractMfs_rec( p, Gia_ObjFaninId0p(p, pObj), vId2Mfs, vFanins, vFixed, vTruths, vTruthsTemp );
        pObj->Value = Vec_WecSize(vFanins);
        // add buffer/inverter
        vArray = Vec_WecPushLevel( vFanins );
        Vec_IntGrow( vArray, 1 );
        assert( !~Gia_ObjFanin0(pObj)->Value );
        Vec_IntPush( vArray, Gia_ObjFanin0(pObj)->Value );
        Vec_StrPush( vFixed, (char)0 );
        Vec_WrdPush( vTruths, Gia_ObjFaninC0(pObj) ? ~s_ElemVar : s_ElemVar );
        Vec_IntWriteEntry( vId2Mfs, Gia_ObjId(p, pObj), pObj->Value );
    }
    Vec_IntFree( vPoNodes );
    Vec_WrdFree( vTruthsTemp );
    *pvId2Mfs = vId2Mfs;
    return Sfm_NtkConstruct( vFanins, nPiNum, nPoNum, vFixed, vTruths );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManInsertMfs( Gia_Man_t * p, Sfm_Ntk_t * pNtk, Vec_Int_t * vId2Mfs )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vMfsTopo, * vMfs2New, * vArray, * vCover;
    int i, k, Fanin, iMfsId, iLitNew;
    word * pTruth;
    // collect MFS nodes in the topo order
    vMfsTopo = Sfm_NtkDfs( pNtk );
    // create mapping from MFS to new GIA literals
    vMfs2New = Vec_IntStartFull( Vec_IntCap(vMfsTopo) );
    // start new GIA
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // map primary inputs
    Gia_ManForEachCi( p, pObj, i )
    {
        iMfsId = Vec_IntEntry( vId2Mfs, Gia_ObjId(p, pObj) );
        assert( iMfsId >= 0 );
        Vec_IntWriteEntry( vMfs2New, iMfsId, Gia_ManAppendCi(pNew) );
    }
    // map internal nodes
    vCover = Vec_IntAlloc( 1 << 16 );
    Vec_IntForEachEntry( vMfsTopo, iMfsId, i )
    {
        assert( Sfm_NodeReadUsed(pNtk, iMfsId) );
        pTruth = Sfm_NodeReadTruth( pNtk, iMfsId );
        if ( pTruth[0] == 0 || ~pTruth[0] == 0 )
        {
            Vec_IntWriteEntry( vMfs2New, iMfsId, 0 );
            continue;
        }
        vArray = Sfm_NodeReadFanins( pNtk, iMfsId ); // belongs to pNtk
        Vec_IntForEachEntry( vArray, Fanin, k )
        {
            iLitNew = Vec_IntEntry( vMfs2New, Fanin );
            assert( iLitNew >= 0 );
            Vec_IntWriteEntry( vArray, k, iLitNew );            
        }
        // derive new function
        iLitNew = Kit_TruthToGia( pNew, (unsigned *)pTruth, Vec_IntSize(vArray), vCover, vArray, 0 );
        Vec_IntWriteEntry( vMfs2New, iMfsId, iLitNew );
    }
    Vec_IntFree( vCover );
    // map output nodes
    Gia_ManForEachCo( p, pObj, i )
    {
        iMfsId = Vec_IntEntry( vId2Mfs, Gia_ObjId(p, pObj) );
        assert( iMfsId >= 0 );
        vArray = Sfm_NodeReadFanins( pNtk, iMfsId ); // belongs to pNtk
        assert( Vec_IntSize(vArray) == 1 );
        // get the fanin
        iLitNew = Vec_IntEntry( vMfs2New, Vec_IntEntry(vArray, 0) );
        assert( iLitNew >= 0 );
        // create CO
        assert( pTruth[0] == s_ElemVar || ~pTruth[0] == s_ElemVar );
        Gia_ManAppendCo( pNew, Abc_LitNotCond(iLitNew, (int)(pTruth[0] != s_ElemVar)) );
    }
    Vec_IntFree( vMfs2New );
    Vec_IntFree( vMfsTopo );
    return pNew;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManPerformMfs( Gia_Man_t * p, Sfm_Par_t * pPars )
{
    Sfm_Ntk_t * pNtk;
    Vec_Int_t * vId2Mfs;
    Gia_Man_t * pNew;
    int nFaninMax, nNodes;
    assert( Gia_ManRegNum(p) == 0 );
    assert( p->vMapping != NULL );
    if ( p->pManTime != NULL && p->pAigExtra == NULL )
    {
        Abc_Print( 1, "Timing manager is given but there is no GIA of boxes.\n" );
        return NULL;
    }
    // count fanouts
    nFaninMax = Gia_ManLutSizeMax( p );
    if ( nFaninMax > 6 )
    {
        Abc_Print( 1, "Currently \"&mfs\" cannot process the network containing nodes with more than 6 fanins.\n" );
        return NULL;
    }
    // collect information
    pNtk = Gia_ManExtractMfs( p, p->pAigExtra, &vId2Mfs );
    // perform optimization
    nNodes = Sfm_NtkPerform( pNtk, pPars );
    // call the fast extract procedure
    if ( nNodes == 0 )
    {
        Abc_Print( 1, "The network is not changed by \"&mfs\".\n" );
        pNew = Gia_ManDup( p );
        pNew->vMapping = Vec_IntDup( p->vMapping );
    }
    else
    {
        pNew = Gia_ManInsertMfs( p, pNtk, vId2Mfs );
        if( pPars->fVerbose )
            Abc_Print( 1, "The network has %d nodes changed by \"&mfs\".\n", nNodes );
    }
    Vec_IntFree( vId2Mfs );
    Sfm_NtkFree( pNtk );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

