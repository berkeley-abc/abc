/**CFile****************************************************************

  FileName    [cbaBuild.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaBuild.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

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
// replaces NameIds of formal names by their index in the box model
void Cba_BoxRemap( Cba_Ntk_t * pNtk, int iBox, Vec_Int_t * vMap )
{
    Cba_Ntk_t * pBoxModel = Cba_ObjBoxModel( pNtk, iBox );
    Vec_Int_t * vFanins = Cba_ObjFaninVec( pNtk, iBox );
    int i, NameId;
    // map formal names into I/O indexes
    Cba_NtkForEachPi( pBoxModel, NameId, i )
    {
        assert( Vec_IntEntry(vMap, NameId) == -1 );
        Vec_IntWriteEntry( vMap, NameId, i );
    }
    Cba_NtkForEachPo( pBoxModel, NameId, i )
    {
        assert( Vec_IntEntry(vMap, NameId) == -1 );
        Vec_IntWriteEntry( vMap, NameId, Cba_NtkPiNum(pBoxModel) + i );
    }
    // remap box
    assert( Vec_IntSize(vFanins) % 2 == 0 );
    Vec_IntForEachEntry( vFanins, NameId, i )
    {
        assert( Vec_IntEntry(vMap, NameId) != -1 );
        Vec_IntWriteEntry( vFanins, i++, Vec_IntEntry(vMap, NameId) );
    }
    // unmap formal inputs
    Cba_NtkForEachPi( pBoxModel, NameId, i )
        Vec_IntWriteEntry( vMap, NameId, -1 );
    Cba_NtkForEachPo( pBoxModel, NameId, i )
        Vec_IntWriteEntry( vMap, NameId, -1 );
}
void Cba_NtkRemapBoxes( Cba_Ntk_t * pNtk, Vec_Int_t * vMap )
{
    int iBox;
    Cba_NtkForEachBox( pNtk, iBox )
        Cba_BoxRemap( pNtk, iBox, vMap );
}
// create maps of NameId and boxes
void Cba_NtkFindNonDriven( Cba_Ntk_t * pNtk, Vec_Int_t * vMap, int nObjCount, Vec_Int_t * vNonDriven )
{
    int i, iObj, Type, NameId, Index;
    // consider input node names
    Vec_IntClear( vNonDriven );
    Cba_NtkForEachObjType( pNtk, Type, iObj )
    {
        if ( Type == CBA_OBJ_NODE )
        {
            Vec_Int_t * vFanins = Cba_ObjFaninVec( pNtk, iObj );
            Vec_IntForEachEntryStart( vFanins, NameId, i, 1 )
                if ( Vec_IntEntry(vMap, NameId) == -1 )
                    Vec_IntWriteEntry( vMap, NameId, nObjCount++ ), Vec_IntPush(vNonDriven, NameId);
        }
        else if ( Type == CBA_OBJ_BOX )
        {
            Cba_Ntk_t * pNtkBox = Cba_ObjBoxModel( pNtk, iObj );
            Vec_Int_t * vFanins = Cba_ObjFaninVec( pNtk, iObj );
            Vec_IntForEachEntry( vFanins, Index, i )
            {
                i++;
                if ( Index >= Cba_NtkPiNum(pNtkBox) )
                    continue;
                NameId = Vec_IntEntry( vFanins, i );
                if ( Vec_IntEntry(vMap, NameId) == -1 )
                    Vec_IntWriteEntry( vMap, NameId, nObjCount++ ), Vec_IntPush(vNonDriven, NameId);
            }
        }
    }
    Cba_NtkForEachPo( pNtk, NameId, i )
        if ( Vec_IntEntry(vMap, NameId) == -1 )
            Vec_IntWriteEntry( vMap, NameId, nObjCount++ ), Vec_IntPush(vNonDriven, NameId);
    if ( Vec_IntSize(vNonDriven) > 0 )
        printf( "Module %s has %d non-driven nets (for example, %s).\n", Cba_NtkName(pNtk), Vec_IntSize(vNonDriven), Cba_NtkStr(pNtk, Vec_IntEntry(vNonDriven, 0)) );
}
int Cba_NtkCreateMap( Cba_Ntk_t * pNtk, Vec_Int_t * vMap, Vec_Int_t * vBoxes, Vec_Int_t * vNonDriven )
{
    int i, iObj, Type, Index, NameId;
    int nObjCount = 0;
    // map old name IDs into new object IDs
    Vec_IntClear( vBoxes );
    Cba_NtkForEachPi( pNtk, NameId, i )
    {
        if ( Vec_IntEntry(vMap, NameId) != -1 )
            printf( "Primary inputs %d and %d have the same name.\n", Vec_IntEntry(vMap, NameId), i );
        Vec_IntWriteEntry( vMap, NameId, nObjCount++ );
    }
    Cba_NtkForEachObjType( pNtk, Type, iObj )
    {
        if ( Type == CBA_OBJ_NODE )
        {
            // consider node output name
            Vec_Int_t * vFanins = Cba_ObjFaninVec( pNtk, iObj );
            NameId = Vec_IntEntry( vFanins, 0 ); 
            if ( Vec_IntEntry(vMap, NameId) != -1 )
                printf( "Node output name %d is already driven.\n", NameId );
            Vec_IntWriteEntry( vMap, NameId, nObjCount++ );
        }
        else if ( Type == CBA_OBJ_BOX )
        {
            Vec_Int_t * vFanins = Cba_ObjFaninVec( pNtk, iObj );
            Cba_Ntk_t * pNtkBox = Cba_ObjBoxModel( pNtk, iObj );
            nObjCount += Cba_NtkPiNum(pNtkBox);
            Vec_IntPush( vBoxes, nObjCount++ );
            Vec_IntForEachEntry( vFanins, Index, i )
            {
                i++;
                if ( Index < Cba_NtkPiNum(pNtkBox) )
                    continue;
                assert( Index - Cba_NtkPiNum(pNtkBox) < Cba_NtkPoNum(pNtkBox) );
                // consider box output name
                NameId = Vec_IntEntry( vFanins, i );
                if ( Vec_IntEntry(vMap, NameId) != -1 )
                    printf( "Box output name %d is already driven.\n", NameId );
                Vec_IntWriteEntry( vMap, NameId, nObjCount + Index - Cba_NtkPiNum(pNtkBox) );
            }
            nObjCount += Cba_NtkPoNum(pNtkBox);
        }
    }
    Cba_NtkFindNonDriven( pNtk, vMap, nObjCount, vNonDriven );
    nObjCount += Vec_IntSize(vNonDriven) + Cba_NtkPoNum(pNtk);
    return nObjCount;
}
Cba_Ntk_t * Cba_NtkBuild( Cba_Man_t * pNew, Cba_Ntk_t * pNtk, Vec_Int_t * vMap, Vec_Int_t * vBoxes, Vec_Int_t * vNonDriven, Vec_Int_t * vTemp, int nObjCount )
{
    Vec_Int_t * vFanins;
    Cba_Ntk_t * pNtkNew, * pNtkBox;
    int i, iObj, ObjId, FaninId, Type, Index, NameId, nBoxes = 0;

    // start network
    pNtkNew = Cba_ManNtk( pNew, Cba_NtkId(pNtk) );
    Cba_NtkResize( pNtkNew, nObjCount, 0 );

    // fill object information
    Cba_NtkForEachPi( pNtk, NameId, i )
    {
        ObjId = Vec_IntEntry( vMap, NameId );
        Vec_IntWriteEntry( &pNtkNew->vInputs,  i, ObjId );
        Vec_IntWriteEntry( &pNtkNew->vTypes,   ObjId, CBA_OBJ_PI );
        Vec_IntWriteEntry( &pNtkNew->vFuncs,   ObjId, i );
        Vec_IntWriteEntry( &pNtkNew->vNameIds, ObjId, NameId );
    }
    Cba_NtkForEachObjType( pNtk, Type, iObj )
    {
        vFanins = Cba_ObjFaninVec( pNtk, iObj );
        if ( Type == CBA_OBJ_NODE )
        {
            ObjId = Vec_IntEntry( vMap, Vec_IntEntry(vFanins, 0) );
            Vec_IntClear( vTemp );
            Vec_IntForEachEntryStart( vFanins, NameId, i, 1 )
            {
                assert( Vec_IntEntry(vMap, NameId) != -1 );
                Vec_IntPush( vTemp, Vec_IntEntry(vMap, NameId) );
            }
            Vec_IntWriteEntry( &pNtkNew->vTypes,   ObjId, CBA_OBJ_NODE );
            Vec_IntWriteEntry( &pNtkNew->vFuncs,   ObjId, Cba_ObjFuncId(pNtk, iObj) );
            Vec_IntWriteEntry( &pNtkNew->vFanins,  ObjId, Cba_ManHandleArray(pNew, vTemp) );
            Vec_IntWriteEntry( &pNtkNew->vNameIds, ObjId, Vec_IntEntry(vFanins, 0) );
        }
        else if ( Type == CBA_OBJ_BOX )
        {
            ObjId = Vec_IntEntry( vBoxes, nBoxes++ );
            pNtkBox = Cba_ObjBoxModel( pNtk, iObj );
            // collect fanins
            Vec_IntFill( vTemp, Cba_NtkPiNum(pNtkBox), -1 );
            Vec_IntForEachEntry( vFanins, Index, i )
            {
                i++; NameId = Vec_IntEntry( vFanins, i );
                assert( Vec_IntEntry(vMap, NameId) != -1 );
                if ( Index < Cba_NtkPiNum(pNtkBox) )
                {
                    Vec_IntWriteEntry( vTemp, Index, Vec_IntEntry(vMap, NameId) );
                    Vec_IntWriteEntry( &pNtkNew->vNameIds, ObjId - Cba_NtkPiNum(pNtkBox) + Index, NameId );
                }
                else
                {
                    assert( Vec_IntEntry(vMap, NameId) == ObjId + 1 + Index - Cba_NtkPiNum(pNtkBox) );
                    Vec_IntWriteEntry( &pNtkNew->vNameIds, Vec_IntEntry(vMap, NameId), NameId );
                }
            }
            Vec_IntForEachEntry( vTemp, Index, i )
                assert( Index >= 0 );
            // create box
            Vec_IntWriteEntry( &pNtkNew->vTypes,  ObjId, CBA_OBJ_BOX );
            Vec_IntWriteEntry( &pNtkNew->vFuncs,  ObjId, Cba_ManNtkId(pNew, Cba_NtkName(pNtkBox)) );
            Cba_NtkSetHost( Cba_ObjBoxModel(pNtkNew, ObjId), Cba_NtkId(pNtkNew), ObjId );
            // create box inputs
            Cba_BoxForEachBi( pNtkNew, ObjId, FaninId, i )
            {
                Vec_IntWriteEntry( &pNtkNew->vTypes,  FaninId, CBA_OBJ_BI );
                Vec_IntWriteEntry( &pNtkNew->vFuncs,  FaninId, i );
                Vec_IntWriteEntry( &pNtkNew->vFanins, FaninId, Vec_IntEntry(vTemp, i) );
            }
            // create box outputs
            Cba_BoxForEachBo( pNtkNew, ObjId, FaninId, i )
            {
                Vec_IntWriteEntry( &pNtkNew->vTypes,  FaninId, CBA_OBJ_BO );
                Vec_IntWriteEntry( &pNtkNew->vFuncs,  FaninId, i );
                Vec_IntWriteEntry( &pNtkNew->vFanins, FaninId, ObjId );
            }
        }
    }
    assert( nBoxes == Vec_IntSize(vBoxes) );
    // add constants for nondriven nodes
    Vec_IntForEachEntry( vNonDriven, NameId, i )
    {
        ObjId = Vec_IntEntry( vMap, NameId );
        Vec_IntWriteEntry( &pNtkNew->vOutputs, i, ObjId );
        Vec_IntWriteEntry( &pNtkNew->vTypes,   ObjId, CBA_OBJ_NODE );
        Vec_IntWriteEntry( &pNtkNew->vFuncs,   ObjId, CBA_NODE_C0 );
        Vec_IntWriteEntry( &pNtkNew->vFanins,  ObjId, Cba_ManHandleBuffer(pNew, -1) );
        Vec_IntWriteEntry( &pNtkNew->vNameIds, ObjId, NameId );
    }
    // add PO nodes
    Cba_NtkForEachPo( pNtk, NameId, i )
    {
        ObjId = nObjCount - Cba_NtkPoNum(pNtk) + i;
        FaninId = Vec_IntEntry( vMap, NameId );
        assert( FaninId != -1 );
        Vec_IntWriteEntry( &pNtkNew->vOutputs, i, ObjId );
        Vec_IntWriteEntry( &pNtkNew->vTypes,   ObjId, CBA_OBJ_PO );
        Vec_IntWriteEntry( &pNtkNew->vFuncs,   ObjId, i );
        Vec_IntWriteEntry( &pNtkNew->vFanins,  ObjId, FaninId );
        // remove NameId from the driver and assign it to the output
        //Vec_IntWriteEntry( &pNtkNew->vNameIds, FaninId, -1 );
        Vec_IntWriteEntry( &pNtkNew->vNameIds, ObjId, NameId );
    }
    return pNtkNew;
}
void Cba_NtkCleanMap( Cba_Ntk_t * pNtk, Vec_Int_t * vMap )
{
    Vec_Int_t * vFanins;
    int i, iObj, Type, NameId;
    Cba_NtkForEachPi( pNtk, NameId, i )
        Vec_IntWriteEntry( vMap, NameId, -1 );
    Cba_NtkForEachObjType( pNtk, Type, iObj )
    {
        vFanins = Cba_ObjFaninVec( pNtk, iObj );
        if ( Type == CBA_OBJ_NODE )
        {
            Vec_IntForEachEntry( vFanins, NameId, i )
                Vec_IntWriteEntry( vMap, NameId, -1 );
        }
        else if ( Type == CBA_OBJ_BOX )
        {
            Vec_IntForEachEntry( vFanins, NameId, i )
                Vec_IntWriteEntry( vMap, Vec_IntEntry(vFanins, ++i), -1 );
        }
    }
    Cba_NtkForEachPo( pNtk, NameId, i )
        Vec_IntWriteEntry( vMap, NameId, -1 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cba_Man_t * Cba_ManBuild( Cba_Man_t * p )
{
    Cba_Man_t * pNew   = Cba_ManClone( p );
    Vec_Int_t * vMap   = Vec_IntStartFull( Abc_NamObjNumMax(p->pNames) + 1 );
    Vec_Int_t * vBoxes = Vec_IntAlloc( 1000 );
    Vec_Int_t * vNonDr = Vec_IntAlloc( 1000 );
    Vec_Int_t * vTemp  = Vec_IntAlloc( 1000 );
    Cba_Ntk_t * pNtk;  
    int i, nObjs;
    assert( Abc_NamObjNumMax(p->pModels) == Cba_ManNtkNum(p) + 1 );
    Cba_ManForEachNtk( p, pNtk, i )
    {
        Cba_NtkRemapBoxes( pNtk, vMap );
        nObjs = Cba_NtkCreateMap( pNtk, vMap, vBoxes, vNonDr );
        Cba_NtkBuild( pNew, pNtk, vMap, vBoxes, vNonDr, vTemp, nObjs );
        Cba_NtkCleanMap( pNtk, vMap );
    }
    assert( Vec_IntCountEntry(vMap, -1) == Vec_IntSize(vMap) );
    Vec_IntFree( vMap );
    Vec_IntFree( vBoxes );
    Vec_IntFree( vNonDr );
    Vec_IntFree( vTemp );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

