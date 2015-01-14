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

/*
    Elaboration input data:
    Vec_Int_t    vInputs;  // inputs          (used by parser to store signals as NameId)
    Vec_Int_t    vOutputs; // outputs         (used by parser to store signals as NameId) 
    Vec_Int_t    vTypes;   // types           (used by parser to store Cba_PrsType_t)
    Vec_Int_t    vFuncs;   // functions       (used by parser to store function)
    Vec_Int_t    vFanins;  // fanins          (used by parser to store fanin/fanout signals as NameId)      
*/

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
    Vec_IntForEachEntry( vMap, NameId, i )
        assert( NameId == -1 );
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
    int Type, iBox;
    Cba_NtkForEachObjType( pNtk, Type, iBox )
        if ( Type == CBA_OBJ_BOX )
            Cba_BoxRemap( pNtk, iBox, vMap );
}
// create maps of NameId and boxes
int Cba_NtkCreateMap( Cba_Ntk_t * pNtk, Vec_Int_t * vMap, Vec_Int_t * vBoxes )
{
    Vec_Int_t * vFanins;
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
            vFanins = Cba_ObjFaninVec( pNtk, iObj );
            NameId = Vec_IntEntry( vFanins, 0 ); 
            if ( Vec_IntEntry(vMap, NameId) != -1 )
                printf( "Node output name %d is already driven.\n", NameId );
            Vec_IntWriteEntry( vMap, NameId, nObjCount++ );
        }
        else if ( Type == CBA_OBJ_BOX )
        {
            Cba_Ntk_t * pNtkBox = Cba_ObjBoxModel( pNtk, iObj );
            nObjCount += Cba_NtkPiNum(pNtkBox);
            Vec_IntPush( vBoxes, nObjCount++ );
            vFanins = Cba_ObjFaninVec( pNtk, iObj );
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
    // add outputs
    nObjCount += Cba_NtkPoNum(pNtk);
    return nObjCount;
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
int Cba_NtkCheckNonDriven( Cba_Ntk_t * pNtk, Vec_Int_t * vMap, int nObjCount )
{
    Vec_Int_t * vFanins;
    int i, iObj, Type, NameId, Index;
    int NonDriven = 0;
    // check non-driven nets
    Cba_NtkForEachObjType( pNtk, Type, iObj )
    {
        if ( Type == CBA_OBJ_NODE )
        {
            // consider node input names
            vFanins = Cba_ObjFaninVec( pNtk, iObj );
            Vec_IntForEachEntryStart( vFanins, NameId, i, 1 )
            {
                if ( Vec_IntEntry(vMap, NameId) != -1 )
                    continue;
                if ( NonDriven++ == 0 ) nObjCount++;
                Vec_IntWriteEntry( vMap, NameId, nObjCount-1 );
            }
        }
        else if ( Type == CBA_OBJ_BOX )
        {
            Cba_Ntk_t * pNtkBox = Cba_ObjBoxModel( pNtk, iObj );
            vFanins = Cba_ObjFaninVec( pNtk, iObj );
            Vec_IntForEachEntry( vFanins, Index, i )
            {
                i++;
                if ( Index >= Cba_NtkPiNum(pNtkBox) )
                    continue;
                // consider box input name
                NameId = Vec_IntEntry( vFanins, i );
                if ( Vec_IntEntry(vMap, NameId) != -1 )
                    continue;
                if ( NonDriven++ == 0 ) nObjCount++;
                Vec_IntWriteEntry( vMap, NameId, nObjCount-1 );
            }
        }
    }
    Cba_NtkForEachPo( pNtk, NameId, i )
    {
        if ( Vec_IntEntry(vMap, NameId) != -1 )
            continue;
        if ( NonDriven++ == 0 ) nObjCount++;
        Vec_IntWriteEntry( vMap, NameId, nObjCount-1 );
    }
    if ( NonDriven > 0 )
        printf( "Detected %d non-driven nets.\n", NonDriven );
    return NonDriven;
}
Cba_Ntk_t * Cba_NtkBuild( Cba_Man_t * pNew, Cba_Ntk_t * pNtk, Vec_Int_t * vMap, Vec_Int_t * vBoxes, Vec_Int_t * vTemp, int nObjCount )
{
    Vec_Int_t * vFanins;
    Cba_Ntk_t * pNtkNew, * pNtkBox;
    int i, iObj, ObjId, FaninId, Type, Index, NameId, nBoxes = 0;

    // start network
    pNtkNew = Cba_ManNtk( pNew, Cba_NtkId(pNtk) );
    Cba_ManFetchArray( pNew, &pNtkNew->vTypes,   nObjCount );
    Cba_ManFetchArray( pNew, &pNtkNew->vFuncs,   nObjCount );
    Cba_ManFetchArray( pNew, &pNtkNew->vFanins,  nObjCount );
    Cba_ManFetchArray( pNew, &pNtkNew->vNameIds, nObjCount );
    Cba_ManSetupArray( pNew, &pNtkNew->vBoxes,   vBoxes );

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
            ObjId = Vec_IntEntry( &pNtkNew->vBoxes, nBoxes++ );
            pNtkBox = Cba_ObjBoxModel( pNtk, iObj );
            Cba_NtkSetHost( pNtkBox, Cba_NtkId(pNtk), ObjId );
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
            // create box inputs
            Cba_BoxForEachBi( pNtkNew, ObjId, FaninId, i )
            {
                Vec_IntWriteEntry( &pNtkNew->vTypes,  FaninId, CBA_OBJ_BI );
                Vec_IntWriteEntry( &pNtkNew->vFuncs,  FaninId, i );
                Vec_IntWriteEntry( &pNtkNew->vFanins, FaninId, Cba_ManHandleBuffer(pNew, Vec_IntEntry(vTemp, i)) );
            }
            // create box outputs
            Cba_BoxForEachBo( pNtkNew, ObjId, FaninId, i )
            {
                Vec_IntWriteEntry( &pNtkNew->vTypes,  FaninId, CBA_OBJ_BO );
                Vec_IntWriteEntry( &pNtkNew->vFuncs,  FaninId, i );
                Vec_IntWriteEntry( &pNtkNew->vFanins, FaninId, Cba_ManHandleBuffer(pNew, ObjId) );
            }
        }
    }
    assert( nBoxes == Vec_IntSize(&pNtkNew->vBoxes) );
    Cba_NtkForEachPo( pNtk, NameId, i )
    {
        ObjId = nObjCount - Cba_NtkPoNum(pNtk) + i;
        FaninId = Vec_IntEntry( vMap, NameId );
        assert( FaninId != -1 );
        Vec_IntWriteEntry( &pNtkNew->vOutputs, i, ObjId );
        Vec_IntWriteEntry( &pNtkNew->vTypes,   ObjId, CBA_OBJ_PO );
        Vec_IntWriteEntry( &pNtkNew->vFuncs,   ObjId, i );
        Vec_IntWriteEntry( &pNtkNew->vFanins,  ObjId, Cba_ManHandleBuffer(pNew, FaninId) );
        // remove NameId from the driver and assign it to the output
        //Vec_IntWriteEntry( &pNtkNew->vNameIds, FaninId, -1 );
        Vec_IntWriteEntry( &pNtkNew->vNameIds, ObjId, NameId );
    }
    return pNtkNew;
}
Cba_Man_t * Cba_ManPreBuild( Cba_Man_t * p )
{
    Cba_Man_t * pNew = Cba_ManClone( p );
    Cba_Ntk_t * pNtk, * pNtkNew; int i;
    Cba_ManForEachNtk( p, pNtk, i )
    {
        pNtkNew = Cba_NtkAlloc( pNew, Cba_NtkName(pNtk) );
        Cba_ManFetchArray( pNew, &pNtkNew->vInputs,  Cba_NtkPiNum(pNtk) );
        Cba_ManFetchArray( pNew, &pNtkNew->vOutputs, Cba_NtkPoNum(pNtk) );
    }
    assert( Cba_ManNtkNum(pNew) == Cba_ManNtkNum(p) );
    return pNew;
}
Cba_Man_t * Cba_ManBuild( Cba_Man_t * p )
{
    Cba_Man_t * pNew   = Cba_ManPreBuild( p );
    Vec_Int_t * vMap   = Vec_IntStartFull( Abc_NamObjNumMax(p->pNames) + 1 );
    Vec_Int_t * vBoxes = Vec_IntAlloc( 1000 );
    Vec_Int_t * vTemp  = Vec_IntAlloc( 1000 );
    Cba_Ntk_t * pNtk; int i, nObjs;
    assert( Abc_NamObjNumMax(p->pModels) == Cba_ManNtkNum(p) + 1 );
    Cba_ManForEachNtk( p, pNtk, i )
    {
        Cba_NtkRemapBoxes( pNtk, vMap );
        nObjs = Cba_NtkCreateMap( pNtk, vMap, vBoxes );
        Cba_NtkCheckNonDriven( pNtk, vMap, nObjs );
        Cba_NtkBuild( pNew, pNtk, vMap, vBoxes, vTemp, nObjs );
        Cba_NtkCleanMap( pNtk, vMap );
    }
    Vec_IntFree( vTemp );
    Vec_IntFree( vBoxes );
    Vec_IntFree( vMap );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

