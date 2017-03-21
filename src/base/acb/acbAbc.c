/**CFile****************************************************************

  FileName    [acbAbc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Bridge.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 21, 2015.]

  Revision    [$Id: acbAbc.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acb.h"
#include "base/abc/abc.h"
#include "aig/miniaig/ndr.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Acb_Ntk_t * Acb_NtkFromAbc( Abc_Ntk_t * p )
{
    Acb_Man_t * pMan = Acb_ManAlloc( Abc_NtkSpec(p), 1, NULL, NULL, NULL, NULL );
    int i, k, NameId = Abc_NamStrFindOrAdd( pMan->pStrs, Abc_NtkName(p), NULL );
    Acb_Ntk_t * pNtk = Acb_NtkAlloc( pMan, NameId, Abc_NtkCiNum(p), Abc_NtkCoNum(p), Abc_NtkObjNum(p) );
    Abc_Obj_t * pObj, * pFanin;
    assert( Abc_NtkIsSopLogic(p) );
    Abc_NtkForEachCi( p, pObj, i )
        pObj->iTemp = Acb_ObjAlloc( pNtk, ABC_OPER_CI, 0, 0 );
    Abc_NtkForEachNode( p, pObj, i )
        pObj->iTemp = Acb_ObjAlloc( pNtk, ABC_OPER_LUT, Abc_ObjFaninNum(pObj), 0 );
    Abc_NtkForEachCo( p, pObj, i )
        pObj->iTemp = Acb_ObjAlloc( pNtk, ABC_OPER_CO, 1, 0 );
    Abc_NtkForEachNode( p, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Acb_ObjAddFanin( pNtk, pObj->iTemp, pFanin->iTemp );
    Abc_NtkForEachCo( p, pObj, i )
        Acb_ObjAddFanin( pNtk, pObj->iTemp, Abc_ObjFanin(pObj, 0)->iTemp );
    Acb_NtkCleanObjTruths( pNtk );
    Abc_NtkForEachNode( p, pObj, i )
        Acb_ObjSetTruth( pNtk, pObj->iTemp, Abc_SopToTruth((char *)pObj->pData, Abc_ObjFaninNum(pObj)) );
    Acb_NtkSetRegNum( pNtk, Abc_NtkLatchNum(p) );
    Acb_NtkAdd( pMan, pNtk );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Acb_Ntk_t * Acb_NtkFromNdr( char * pFileName, void * pModule, Abc_Nam_t * pNames, Vec_Int_t * vWeights, int nNameIdMax )
{
    Ndr_Data_t * p   = (Ndr_Data_t *)pModule; 
    Acb_Man_t * pMan = Acb_ManAlloc( pFileName, 1, Abc_NamRef(pNames), NULL, NULL, NULL );
    int k, NameId = Abc_NamStrFindOrAdd( pMan->pStrs, pMan->pName, NULL );
    int Mod = 0, Obj, Type, nArray, * pArray, ObjId;
    Acb_Ntk_t * pNtk = Acb_NtkAlloc( pMan, NameId, Ndr_DataCiNum(p, Mod), Ndr_DataCoNum(p, Mod), Ndr_DataObjNum(p, Mod) );
    Vec_Int_t * vMap = Vec_IntStart( nNameIdMax );
    Acb_NtkCleanObjWeights( pNtk );
    Acb_NtkCleanObjNames( pNtk );
    Ndr_ModForEachPi( p, Mod, Obj )
    {
        NameId = Ndr_ObjReadBody( p, Obj, NDR_OUTPUT );
        ObjId  = Acb_ObjAlloc( pNtk, ABC_OPER_CI, 0, 0 );
        Vec_IntWriteEntry( vMap, NameId, ObjId );
        Acb_ObjSetName( pNtk, ObjId, NameId );
        Acb_ObjSetWeight( pNtk, ObjId, vWeights ? Vec_IntEntry(vWeights, NameId) : 0 );
    }
    Ndr_ModForEachTarget( p, Mod, Obj )
    {
        NameId = Ndr_DataEntry( p, Obj );
        ObjId  = Acb_ObjAlloc( pNtk, ABC_OPER_CONST_F, 0, 0 );
        Vec_IntWriteEntry( vMap, NameId, ObjId );
        Acb_ObjSetName( pNtk, ObjId, NameId );
        Vec_IntPush( &pNtk->vTargets, ObjId );
    }
    Ndr_ModForEachNode( p, Mod, Obj )
    {
        NameId = Ndr_ObjReadBody( p, Obj, NDR_OUTPUT );
        nArray = Ndr_ObjReadArray( p, Obj, NDR_INPUT, &pArray );
        Type   = Ndr_ObjReadBody( p, Obj, NDR_OPERTYPE );
        ObjId  = Acb_ObjAlloc( pNtk, Type, nArray, 0 );
        Vec_IntWriteEntry( vMap, NameId, ObjId );
        Acb_ObjSetName( pNtk, ObjId, NameId );
    }
    Ndr_ModForEachNode( p, Mod, Obj )
    {
        NameId = Ndr_ObjReadBody( p, Obj, NDR_OUTPUT );
        ObjId  = Vec_IntEntry( vMap, NameId );
        nArray = Ndr_ObjReadArray( p, Obj, NDR_INPUT, &pArray );
        for ( k = 0; k < nArray; k++ )
            Acb_ObjAddFanin( pNtk, ObjId, Vec_IntEntry(vMap, pArray[k]) );
        Acb_ObjSetWeight( pNtk, ObjId, vWeights ? Vec_IntEntry(vWeights, NameId) : 0 );
    }
    Ndr_ModForEachPo( p, Mod, Obj )
    {
        nArray = Ndr_ObjReadArray( p, Obj, NDR_INPUT, &pArray );
        assert( nArray == 1 );
        ObjId  = Acb_ObjAlloc( pNtk, ABC_OPER_CO, 1, 0 );
        Acb_ObjAddFanin( pNtk, ObjId, Vec_IntEntry(vMap, pArray[0]) );
        Acb_ObjSetName( pNtk, ObjId, pArray[0] );
    }
    Vec_IntFree( vMap );
    Acb_NtkSetRegNum( pNtk, 0 );
    Acb_NtkAdd( pMan, pNtk );
    return pNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

