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
    int i, NameId;
    int nDigits = Abc_Base10Log( Cba_NtkObjNum(p) );
    Cba_NtkForEachNode( p, i )
    {
        if ( Cba_ObjNameId(p, i) == -1 )
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

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// duplicate PI/PO/boxes
void Cba_ObjDupStart( Cba_Ntk_t * pNew, Cba_Ntk_t * p, int iObj )
{
    if ( Cba_ObjIsPi(p, iObj) )
        Vec_IntWriteEntry( &pNew->vInputs, Cba_ObjFuncId(p, iObj), pNew->nObjs );
    if ( Cba_ObjIsPo(p, iObj) )
        Vec_IntWriteEntry( &pNew->vOutputs, Cba_ObjFuncId(p, iObj), pNew->nObjs );
    Vec_IntWriteEntry( &pNew->vTypes,   pNew->nObjs, Cba_ObjType(p, iObj) );
    Vec_IntWriteEntry( &pNew->vFuncs,   pNew->nObjs, Cba_ObjFuncId(p, iObj) );
    Vec_IntWriteEntry( &pNew->vNameIds, pNew->nObjs, Cba_ObjNameId(p, iObj) );
    if ( Cba_ObjIsBox(p, iObj) )
        Cba_NtkSetHost( Cba_ObjBoxModel(pNew, pNew->nObjs), Cba_NtkId(pNew), pNew->nObjs );
    Cba_NtkSetCopy( p, iObj, pNew->nObjs++ );
}
void Cba_NtkDupStart( Cba_Ntk_t * pNew, Cba_Ntk_t * p )
{
    int i, iObj, iTerm;
    pNew->nObjs = 0;
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjDupStart( pNew, p, iObj );
    Cba_NtkForEachPo( p, iObj, i )
        Cba_ObjDupStart( pNew, p, iObj );
    Cba_NtkForEachBox( p, iObj )
    {
        Cba_BoxForEachBi( p, iObj, iTerm, i )
            Cba_ObjDupStart( pNew, p, iTerm );
        Cba_ObjDupStart( pNew, p, iObj );
        Cba_BoxForEachBo( p, iObj, iTerm, i )
            Cba_ObjDupStart( pNew, p, iTerm );
        // connect box outputs to boxes
        Cba_BoxForEachBo( p, iObj, iTerm, i )
            Vec_IntWriteEntry( &pNew->vFanins, Cba_NtkCopy(p, iTerm), Cba_NtkCopy(p, Cba_ObjFanin0(p, iTerm)) );
    }
    assert( Cba_NtkBoxNum(p) == Cba_NtkBoxNum(pNew) );
}
Cba_Man_t * Cba_ManDupStart( Cba_Man_t * p, Vec_Int_t * vNtkSizes )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_Man_t * pNew = Cba_ManClone( p );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkResize( Cba_ManNtk(pNew, i), vNtkSizes ? Vec_IntEntry(vNtkSizes, i) : Cba_NtkObjNum(pNtk), Cba_NtkIsWordLevel(pNtk) );
    Vec_IntFill( &p->vCopies, Cba_ManObjNum(p), -1 );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDupStart( Cba_ManNtk(pNew, i), pNtk );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// duplicate internal nodes
void Cba_NtkDupNodes( Cba_Ntk_t * pNew, Cba_Ntk_t * p, Vec_Int_t * vTemp )
{
    Vec_Int_t * vFanins;
    int i, k, Type, iTerm, iObj;
    // dup nodes
    Cba_NtkForEachNode( p, iObj )
        Cba_ObjDupStart( pNew, p, iObj );
    assert( pNew->nObjs == Cba_NtkObjNum(pNew) ); 
    // connect
    Cba_NtkForEachObjType( p, Type, i )
    {
        if ( Type == CBA_OBJ_PI || Type == CBA_OBJ_BOX || Type == CBA_OBJ_BO )
            continue;
        if ( Type == CBA_OBJ_PO || Type == CBA_OBJ_BI )
        {
            assert( Vec_IntEntry(&pNew->vFanins, Cba_NtkCopy(p, i)) == -1 );
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
Cba_Man_t * Cba_ManDup( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Vec_Int_t * vTemp = Vec_IntAlloc( 100 );
    Cba_Man_t * pNew = Cba_ManDupStart( p, NULL );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDupNodes( Cba_ManNtk(pNew, i), pNtk, vTemp );
    Vec_IntFree( vTemp );
    return pNew;

}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

