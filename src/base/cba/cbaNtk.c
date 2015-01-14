/**CFile****************************************************************

  FileName    [cbaNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaNtk.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"

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
void Cba_ManAssignInternNamesNtk( Cba_Ntk_t * p )
{
    int i, Type, NameId;
    int nDigits = Abc_Base10Log( Cba_NtkObjNum(p) );
    Cba_NtkForEachObjType( p, Type, i )
    {
        if ( Type == CBA_OBJ_NODE )
        {
            char Buffer[100];
            sprintf( Buffer, "%s%0*d", "_n_", nDigits, i );
            NameId = Abc_NamStrFindOrAdd( p->pDesign->pNames, Buffer, NULL );
            Vec_IntWriteEntry( &p->vNameIds, i, NameId );
        }
    }
}
void Cba_ManAssignInternNames( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManAssignInternNamesNtk( pNtk );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_NtkNodeNum( Cba_Ntk_t * p )
{ 
    int iObj, Count = 0;
    Cba_NtkForEachNode( p, iObj )
        Count++;
    return Count;
}
int Cba_ManObjNum( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; 
    int i, Count = 0;
    Cba_ManForEachNtk( p, pNtk, i )
    {
        pNtk->iObjStart = Count;
        Count += Cba_NtkObjNum(pNtk);
    }
    return Count;
}
void Cba_ManSetNtkBoxes( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk, * pBox; 
    int i, k, Type;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkForEachObjType( pNtk, Type, k )
            if ( Type == CBA_OBJ_BOX )
            {
                pBox = Cba_ObjBoxModel(pNtk, k);
                assert( pBox->iBoxNtk == 0 );
                pBox->iBoxNtk = i;
                pBox->iBoxObj = k;
            }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_ObjDup( Cba_Ntk_t * pNew, Cba_Ntk_t * p, int iObj )
{
    if ( Cba_ObjIsPi(p, iObj) )
        Vec_IntWriteEntry( &pNew->vInputs, Cba_ObjFuncId(pNew, iObj), pNew->nObjs );
    if ( Cba_ObjIsPo(p, iObj) )
        Vec_IntWriteEntry( &pNew->vOutputs, Cba_ObjFuncId(pNew, iObj), pNew->nObjs );
    if ( Cba_ObjIsBox(p, iObj) )
        Vec_IntPush( &pNew->vBoxes, pNew->nObjs );
    Vec_IntWriteEntry( &pNew->vTypes,   pNew->nObjs, Cba_ObjType(p, iObj) );
    Vec_IntWriteEntry( &pNew->vFuncs,   pNew->nObjs, Cba_ObjFuncId(pNew, iObj) );
    Vec_IntWriteEntry( &pNew->vNameIds, pNew->nObjs, Cba_ObjNameId(p, iObj) );
    Cba_NtkSetCopy( p, iObj, pNew->nObjs++ );
}

// allocates memory
Cba_Ntk_t * Cba_NtkDupAlloc( Cba_Man_t * pNew, Cba_Ntk_t * pNtk, int nObjs )
{
    Cba_Ntk_t * pNtkNew = Cba_NtkAlloc( pNew, Cba_NtkName(pNtk) );
    Cba_ManFetchArray( pNew, &pNtkNew->vInputs,  Cba_NtkPiNum(pNtk) );
    Cba_ManFetchArray( pNew, &pNtkNew->vOutputs, Cba_NtkPoNum(pNtk) );
    Cba_ManFetchArray( pNew, &pNtkNew->vTypes,   nObjs );
    Cba_ManFetchArray( pNew, &pNtkNew->vFuncs,   nObjs );
    Cba_ManFetchArray( pNew, &pNtkNew->vFanins,  nObjs );
    Cba_ManFetchArray( pNew, &pNtkNew->vNameIds, nObjs );
    Cba_ManFetchArray( pNew, &pNtkNew->vBoxes,   Cba_NtkBoxNum(pNtk) );
    Vec_IntShrink( &pNtkNew->vBoxes, 0 );
    return pNtkNew;
}
// duplicate PI/PO/boxes
int Cba_NtkDupStart( Cba_Ntk_t * pNew, Cba_Ntk_t * p )
{
    int i, k, iObj;
    pNew->nObjs = 0;
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjDup( pNew, p, iObj );
    Cba_NtkForEachPo( p, iObj, i )
        Cba_ObjDup( pNew, p, iObj );
    Cba_NtkForEachBox( p, iObj, i )
    {
        Cba_Ntk_t * pBox = Cba_ObjBoxModel( p, iObj );
        for ( k = 0; k < Cba_NtkPiNum(pBox); k++ )
            Cba_ObjDup( pNew, p, Cba_ObjBoxBi(p, iObj, k) );
        Cba_ObjDup( pNew, p, iObj );
        for ( k = 0; k < Cba_NtkPoNum(pBox); k++ )
            Cba_ObjDup( pNew, p, Cba_ObjBoxBo(p, iObj, k) );
    }
    return pNew->nObjs;
}
// duplicate internal nodes
void Cba_NtkDupNodes( Cba_Ntk_t * pNew, Cba_Ntk_t * p, Vec_Int_t * vTemp )
{
    Vec_Int_t * vFanins;
    int i, k, Type, iTerm, iObj;
    Cba_NtkForEachNode( p, iObj )
        Cba_ObjDup( pNew, p, iObj );
    // connect
    Cba_NtkForEachObjType( p, Type, i )
    {
        if ( Type == CBA_OBJ_PI || Type == CBA_OBJ_BOX )
            continue;
        if ( Type == CBA_OBJ_PO || Type == CBA_OBJ_BI || Type == CBA_OBJ_BO )
        {
            Vec_IntWriteEntry( &pNew->vFanins, Cba_NtkCopy(p, i), Cba_NtkCopy(p, Cba_ObjFanin0(p, i)) );
            continue;
        }
        assert( Type == CBA_OBJ_NODE );
        Vec_IntClear( vTemp );
        vFanins = Cba_ObjFaninVec( p, i );
        Vec_IntForEachEntry( vFanins, iTerm, k )
            Vec_IntPush( vTemp, Cba_NtkCopy(p, iTerm) );
        Vec_IntWriteEntry( &pNew->vFanins, Cba_NtkCopy(p, i), Cba_ManHandleArray(pNew->pDesign, vTemp) );
    }

}
// finalize network 
void Cba_NtkDupFinish( Cba_Ntk_t * pNew )
{
    int iObj;
    // add constant drivers
    Cba_NtkForEachCo( pNew, iObj )
    {
    }
    // restrict
    Vec_IntShrink( &pNew->vTypes,   pNew->nObjs );
    Vec_IntShrink( &pNew->vFuncs,   pNew->nObjs );
    Vec_IntShrink( &pNew->vFanins,  pNew->nObjs );
    Vec_IntShrink( &pNew->vNameIds, pNew->nObjs );
}

Cba_Man_t * Cba_ManDupStart( Cba_Man_t * p, Vec_Int_t * vObjCounts )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_Man_t * pNew = Cba_ManAlloc( Cba_ManName(p) );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDupAlloc( pNew, pNtk, vObjCounts ? Cba_NtkObjNum(pNtk) : Vec_IntEntry(vObjCounts, i) );
    Vec_IntFill( &p->vCopies, Cba_ManObjNum(pNew), -1 );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDupStart( Cba_ManNtk(pNew, i), pNtk );
    return pNew;
}
Cba_Man_t * Cba_ManDup( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Vec_Int_t * vTemp = Vec_IntAlloc( 100 );
    Cba_Man_t * pNew = Cba_ManDupStart( p, NULL );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDupNodes( Cba_ManNtk(pNew, i), pNtk, vTemp );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDupFinish( Cba_ManNtk(pNew, i) );
    Vec_IntClear( vTemp );
    return pNew;

}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

