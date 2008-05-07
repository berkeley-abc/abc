/**CFile****************************************************************

  FileName    [ntlInsert.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Procedures to insert mapping into a design.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlInsert.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"
#include "kit.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Inserts the given mapping into the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManInsertMapping( Ntl_Man_t * p, Vec_Ptr_t * vMapping, Aig_Man_t * pAig )
{
    char Buffer[100];
    Vec_Ptr_t * vCopies;
    Vec_Int_t * vCover;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pNode;
    Ntl_Net_t * pNet, * pNetCo;
    Ntl_Lut_t * pLut;
    int i, k, nDigits;
    assert( Vec_PtrSize(p->vCis) == Aig_ManPiNum(pAig) );
    assert( Vec_PtrSize(p->vCos) == Aig_ManPoNum(pAig) );
    p = Ntl_ManStartFrom( p );
    pRoot = Ntl_ManRootModel( p );
    assert( Ntl_ModelNodeNum(pRoot) == 0 );
    // map the AIG back onto the design
    Ntl_ManForEachCiNet( p, pNet, i )
        pNet->pCopy = Aig_ManPi( pAig, i );
    // start mapping of AIG nodes into their copies
    vCopies = Vec_PtrStart( Aig_ManObjNumMax(pAig) );
    Ntl_ManForEachCiNet( p, pNet, i )
        Vec_PtrWriteEntry( vCopies, ((Aig_Obj_t *)pNet->pCopy)->Id, pNet );
    // create a new node for each LUT
    vCover = Vec_IntAlloc( 1 << 16 );
    nDigits = Aig_Base10Log( Vec_PtrSize(vMapping) );
    Vec_PtrForEachEntry( vMapping, pLut, i )
    {
        pNode = Ntl_ModelCreateNode( pRoot, pLut->nFanins );
        pNode->pSop = Kit_PlaFromTruth( p->pMemSops, pLut->pTruth, pLut->nFanins, vCover );
        if ( !Kit_TruthIsConst0(pLut->pTruth, pLut->nFanins) && !Kit_TruthIsConst1(pLut->pTruth, pLut->nFanins) )
        {
            for ( k = 0; k < pLut->nFanins; k++ )
            {
                pNet = Vec_PtrEntry( vCopies, pLut->pFanins[k] );
                if ( pNet == NULL )
                {
                    printf( "Ntl_ManInsert(): Internal error: Net not found.\n" );
                    return 0;
                }
                Ntl_ObjSetFanin( pNode, pNet, k );
            }
        }
        else
            pNode->nFanins = 0;
        sprintf( Buffer, "lut%0*d", nDigits, i );
        if ( (pNet = Ntl_ModelFindNet( pRoot, Buffer )) )
        {
            printf( "Ntl_ManInsert(): Internal error: Intermediate net name is not unique.\n" );
            return 0;
        }
        pNet = Ntl_ModelFindOrCreateNet( pRoot, Buffer );
        if ( !Ntl_ModelSetNetDriver( pNode, pNet ) )
        {
            printf( "Ntl_ManInsert(): Internal error: Net has more than one fanin.\n" );
            return 0;
        }
        Vec_PtrWriteEntry( vCopies, pLut->Id, pNet );
    }
    Vec_IntFree( vCover );
    // mark CIs and outputs of the registers
    Ntl_ManForEachCiNet( p, pNetCo, i )
        pNetCo->fMark = 1;
    // update the CO pointers
    Ntl_ManForEachCoNet( p, pNetCo, i )
    {
        if ( pNetCo->fMark )
            continue;
        pNetCo->fMark = 1;
        pNet = Vec_PtrEntry( vCopies, Aig_Regular(pNetCo->pCopy)->Id );
        pNode = Ntl_ModelCreateNode( pRoot, 1 );
        pNode->pSop = Aig_IsComplement(pNetCo->pCopy)? Ntl_ManStoreSop( p->pMemSops, "0 1\n" ) : Ntl_ManStoreSop( p->pMemSops, "1 1\n" );
        Ntl_ObjSetFanin( pNode, pNet, 0 );
        // update the CO driver net
        assert( pNetCo->pDriver == NULL );
        if ( !Ntl_ModelSetNetDriver( pNode, pNetCo ) )
        {
            printf( "Ntl_ManInsert(): Internal error: PO net has more than one fanin.\n" );
            return 0;
        }
    }
    Vec_PtrFree( vCopies );
    // clean CI/CO marks
    Ntl_ManUnmarkCiCoNets( p );
    if ( !Ntl_ManCheck( p ) )
        printf( "Ntl_ManInsertNtk: The check has failed for design %s.\n", p->pName );
    return p;
}

/**Function*************************************************************

  Synopsis    [Inserts the given mapping into the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManInsertAig( Ntl_Man_t * p, Aig_Man_t * pAig )
{
    char Buffer[100];
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pNode;
    Ntl_Net_t * pNet, * pNetCo;
    Aig_Obj_t * pObj, * pFanin;
    int i, nDigits, Counter;
    assert( Vec_PtrSize(p->vCis) == Aig_ManPiNum(pAig) );
    assert( Vec_PtrSize(p->vCos) == Aig_ManPoNum(pAig) );
    p = Ntl_ManStartFrom( p );
    pRoot = Ntl_ManRootModel( p );
    assert( Ntl_ModelNodeNum(pRoot) == 0 );
    // set the correspondence between the PI/PO nodes
    Aig_ManCleanData( pAig );
    Ntl_ManForEachCiNet( p, pNet, i )
        Aig_ManPi( pAig, i )->pData = pNet;
    // create constant node if needed
    if ( Aig_ManConst1(pAig)->nRefs > 0 )
    {
        pNode = Ntl_ModelCreateNode( pRoot, 0 );
        pNode->pSop = Ntl_ManStoreSop( p->pMemSops, " 1\n" );
        if ( (pNet = Ntl_ModelFindNet( pRoot, "Const1" )) )
        {
            printf( "Ntl_ManInsertAig(): Internal error: Intermediate net name is not unique.\n" );
            return 0;
        }
        pNet = Ntl_ModelFindOrCreateNet( pRoot, "Const1" );
        if ( !Ntl_ModelSetNetDriver( pNode, pNet ) )
        {
            printf( "Ntl_ManInsertAig(): Internal error: Net has more than one fanin.\n" );
            return 0;
        }
        Aig_ManConst1(pAig)->pData = pNet;
    }
    // create a new node for each LUT
    Counter = 0;
    nDigits = Aig_Base10Log( Aig_ManNodeNum(pAig) );
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( !Aig_ObjIsNode(pObj) )
            continue;
        if ( Aig_ObjFanin0(pObj)->pData == NULL || Aig_ObjFanin1(pObj)->pData == NULL )
        {
            printf( "Ntl_ManInsertAig(): Internal error: Net not found.\n" );
            return 0;
        }
        pNode = Ntl_ModelCreateNode( pRoot, 2 );
        Ntl_ObjSetFanin( pNode, Aig_ObjFanin0(pObj)->pData, 0 );
        Ntl_ObjSetFanin( pNode, Aig_ObjFanin1(pObj)->pData, 1 );
        if ( Aig_ObjFaninC0(pObj) && Aig_ObjFaninC1(pObj) )
            pNode->pSop = Ntl_ManStoreSop( p->pMemSops, "00 1\n" );
        else if ( Aig_ObjFaninC0(pObj) && !Aig_ObjFaninC1(pObj) )
            pNode->pSop = Ntl_ManStoreSop( p->pMemSops, "01 1\n" );
        else if ( !Aig_ObjFaninC0(pObj) && Aig_ObjFaninC1(pObj) )
            pNode->pSop = Ntl_ManStoreSop( p->pMemSops, "10 1\n" );
        else // if ( Aig_ObjFaninC0(pObj) && Aig_ObjFaninC1(pObj) )
            pNode->pSop = Ntl_ManStoreSop( p->pMemSops, "11 1\n" );
        sprintf( Buffer, "and%0*d", nDigits, Counter++ );
        if ( (pNet = Ntl_ModelFindNet( pRoot, Buffer )) )
        {
            printf( "Ntl_ManInsertAig(): Internal error: Intermediate net name is not unique.\n" );
            return 0;
        }
        pNet = Ntl_ModelFindOrCreateNet( pRoot, Buffer );
        if ( !Ntl_ModelSetNetDriver( pNode, pNet ) )
        {
            printf( "Ntl_ManInsertAig(): Internal error: Net has more than one fanin.\n" );
            return 0;
        }
        pObj->pData = pNet;
    }
    // mark CIs and outputs of the registers
    Ntl_ManForEachCiNet( p, pNetCo, i )
        pNetCo->fMark = 1;
    // update the CO pointers
    Ntl_ManForEachCoNet( p, pNetCo, i )
    {
        if ( pNetCo->fMark )
            continue;
        pNetCo->fMark = 1;
        // get the corresponding PO and its driver
        pObj = Aig_ManPo( pAig, i );
        pFanin = Aig_ObjFanin0( pObj );
        // get the net driving the driver
        pNet = pFanin->pData; 
        pNode = Ntl_ModelCreateNode( pRoot, 1 );
        pNode->pSop = Aig_ObjFaninC0(pObj)? Ntl_ManStoreSop( p->pMemSops, "0 1\n" ) : Ntl_ManStoreSop( p->pMemSops, "1 1\n" );
        Ntl_ObjSetFanin( pNode, pNet, 0 );
        // update the CO driver net
        assert( pNetCo->pDriver == NULL );
        if ( !Ntl_ModelSetNetDriver( pNode, pNetCo ) )
        {
            printf( "Ntl_ManInsertAig(): Internal error: PO net has more than one fanin.\n" );
            return 0;
        }
    }
    // clean CI/CO marks
    Ntl_ManUnmarkCiCoNets( p );
    if ( !Ntl_ManCheck( p ) )
        printf( "Ntl_ManInsertAig: The check has failed for design %s.\n", p->pName );
    return p;
}


/**Function*************************************************************

  Synopsis    [Inserts the given mapping into the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManInsertNtk( Ntl_Man_t * p, Nwk_Man_t * pNtk )
{
    char Buffer[100];
    Vec_Ptr_t * vObjs;
    Vec_Int_t * vTruth;
    Vec_Int_t * vCover;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pNode;
    Ntl_Net_t * pNet, * pNetCo;
    Nwk_Obj_t * pObj, * pFanin;
    int i, k, nDigits;
    unsigned * pTruth;
    assert( Vec_PtrSize(p->vCis) == Nwk_ManCiNum(pNtk) );
    assert( Vec_PtrSize(p->vCos) == Nwk_ManCoNum(pNtk) );
    p = Ntl_ManStartFrom( p );
    pRoot = Ntl_ManRootModel( p );
    assert( Ntl_ModelNodeNum(pRoot) == 0 );
    // set the correspondence between the PI/PO nodes
    Ntl_ManForEachCiNet( p, pNet, i )
        Nwk_ManCi( pNtk, i )->pCopy = pNet;
    // create a new node for each LUT
    vTruth = Vec_IntAlloc( 1 << 16 );
    vCover = Vec_IntAlloc( 1 << 16 );
    nDigits = Aig_Base10Log( Nwk_ManNodeNum(pNtk) );
//    Nwk_ManForEachObj( pNtk, pObj, i )
    vObjs = Nwk_ManDfs( pNtk );
    Vec_PtrForEachEntry( vObjs, pObj, i )
//    Nwk_ManForEachNode( pNtk, pObj, i )
    {
        if ( !Nwk_ObjIsNode(pObj) )
            continue;
        pNode = Ntl_ModelCreateNode( pRoot, Nwk_ObjFaninNum(pObj) );
        pTruth = Hop_ManConvertAigToTruth( pNtk->pManHop, Hop_Regular(pObj->pFunc), Nwk_ObjFaninNum(pObj), vTruth, 0 );
        if ( Hop_IsComplement(pObj->pFunc) )
            Kit_TruthNot( pTruth, pTruth, Nwk_ObjFaninNum(pObj) );
        pNode->pSop = Kit_PlaFromTruth( p->pMemSops, pTruth, Nwk_ObjFaninNum(pObj), vCover );
        if ( !Kit_TruthIsConst0(pTruth, Nwk_ObjFaninNum(pObj)) && !Kit_TruthIsConst1(pTruth, Nwk_ObjFaninNum(pObj)) )
        {
            Nwk_ObjForEachFanin( pObj, pFanin, k )
            {
                pNet = pFanin->pCopy;
                if ( pNet == NULL )
                {
                    printf( "Ntl_ManInsertNtk(): Internal error: Net not found.\n" );
                    return 0;
                }
                Ntl_ObjSetFanin( pNode, pNet, k );
            }
        }
        else
            pNode->nFanins = 0;
        sprintf( Buffer, "lut%0*d", nDigits, i );
        if ( (pNet = Ntl_ModelFindNet( pRoot, Buffer )) )
        {
            printf( "Ntl_ManInsertNtk(): Internal error: Intermediate net name is not unique.\n" );
            return 0;
        }
        pNet = Ntl_ModelFindOrCreateNet( pRoot, Buffer );
        if ( !Ntl_ModelSetNetDriver( pNode, pNet ) )
        {
            printf( "Ntl_ManInsertNtk(): Internal error: Net has more than one fanin.\n" );
            return 0;
        }
        pObj->pCopy = pNet;
    }
    Vec_PtrFree( vObjs );
    Vec_IntFree( vCover );
    Vec_IntFree( vTruth );
    // mark CIs and outputs of the registers
    Ntl_ManForEachCiNet( p, pNetCo, i )
        pNetCo->fMark = 1;
    // update the CO pointers
    Ntl_ManForEachCoNet( p, pNetCo, i )
    {
        if ( pNetCo->fMark )
            continue;
        pNetCo->fMark = 1;
        // get the corresponding PO and its driver
        pObj = Nwk_ManCo( pNtk, i );
        pFanin = Nwk_ObjFanin0( pObj );
        // get the net driving the driver
        pNet = pFanin->pCopy;
        pNode = Ntl_ModelCreateNode( pRoot, 1 );
        pNode->pSop = pObj->fInvert? Ntl_ManStoreSop( p->pMemSops, "0 1\n" ) : Ntl_ManStoreSop( p->pMemSops, "1 1\n" );
        Ntl_ObjSetFanin( pNode, pNet, 0 );
        // update the CO driver net
        assert( pNetCo->pDriver == NULL );
        if ( !Ntl_ModelSetNetDriver( pNode, pNetCo ) )
        {
            printf( "Ntl_ManInsertNtk(): Internal error: PO net has more than one fanin.\n" );
            return NULL;
        }
    }
    // clean CI/CO marks
    Ntl_ManUnmarkCiCoNets( p );
    if ( !Ntl_ManCheck( p ) )
    {
        printf( "Ntl_ManInsertNtk: The check has failed for design %s.\n", p->pName );
        return NULL;
    }
    return p;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


