/**CFile****************************************************************

  FileName    [cbaPrsBuild.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Parse tree to netlist transformation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaPrsBuild.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "cbaPrs.h"
#include "map/mio/mio.h"
#include "base/main/main.h"

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
int Prs_ManIsMapped( Prs_Ntk_t * pNtk )
{
    Vec_Int_t * vSigs; int iBox;
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen( Abc_FrameGetGlobalFrame() );
    if ( pLib == NULL )
        return 0;
    Prs_NtkForEachBox( pNtk, vSigs, iBox )
        if ( !Prs_BoxIsNode(pNtk, iBox) )
        {
            int NtkId = Prs_BoxNtk( pNtk, iBox );
            if ( Mio_LibraryReadGateByName(pLib, Prs_NtkStr(pNtk, NtkId), NULL) )
                return 1;
        }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Prs_ManVecFree( Vec_Ptr_t * vPrs )
{
    Prs_Ntk_t * pNtk; int i;
    Vec_PtrForEachEntry( Prs_Ntk_t *, vPrs, pNtk, i )
        Prs_NtkFree( pNtk );
    Vec_PtrFree( vPrs );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Prs_NtkCountObjects( Prs_Ntk_t * pNtk )
{
    Vec_Int_t * vFanins; 
    int i, Count = Prs_NtkObjNum(pNtk);
    Prs_NtkForEachBox( pNtk, vFanins, i )
        Count += Prs_BoxIONum(pNtk, i);
    return Count;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// replaces NameIds of formal names by their index in the box model
void Prs_ManRemapOne( Vec_Int_t * vSigs, Prs_Ntk_t * pNtkBox, Vec_Int_t * vMap )
{
    int i, NameId;
    // map formal names into I/O indexes
    Prs_NtkForEachPi( pNtkBox, NameId, i )
    {
        assert( Vec_IntEntry(vMap, NameId) == -1 );
        Vec_IntWriteEntry( vMap, NameId, i + 1 ); // +1 to keep 1st form input non-zero
    }
    Prs_NtkForEachPo( pNtkBox, NameId, i )
    {
        assert( Vec_IntEntry(vMap, NameId) == -1 );
        Vec_IntWriteEntry( vMap, NameId, Prs_NtkPiNum(pNtkBox) + i + 1 ); // +1 to keep 1st form input non-zero
    }
    // remap box
    assert( Vec_IntSize(vSigs) % 2 == 0 );
    Vec_IntForEachEntry( vSigs, NameId, i )
    {
        assert( Vec_IntEntry(vMap, NameId) != -1 );
        Vec_IntWriteEntry( vSigs, i++, Vec_IntEntry(vMap, NameId) );
    }
    // unmap formal inputs
    Prs_NtkForEachPi( pNtkBox, NameId, i )
        Vec_IntWriteEntry( vMap, NameId, -1 );
    Prs_NtkForEachPo( pNtkBox, NameId, i )
        Vec_IntWriteEntry( vMap, NameId, -1 );
}
void Prs_ManRemapGate( Vec_Int_t * vSigs )
{
    int i, FormId;
    Vec_IntForEachEntry( vSigs, FormId, i )
        Vec_IntWriteEntry( vSigs, i, i/2 + 1 ), i++;
}
void Prs_ManRemapBoxes( Cba_Man_t * pNew, Vec_Ptr_t * vDes, Prs_Ntk_t * pNtk, Vec_Int_t * vMap )
{
    Vec_Int_t * vSigs; int iBox;
    Prs_NtkForEachBox( pNtk, vSigs, iBox )
        if ( !Prs_BoxIsNode(pNtk, iBox) )
        {
            int NtkId = Prs_BoxNtk( pNtk, iBox );
            int NtkIdNew = Cba_ManNtkFindId( pNew, Prs_NtkStr(pNtk, NtkId) );
            Prs_BoxSetNtk( pNtk, iBox, NtkIdNew );
            if ( NtkId < Cba_ManNtkNum(pNew) )
                Prs_ManRemapOne( vSigs, Prs_ManNtk(vDes, NtkIdNew), vMap );
            else
                Prs_ManRemapGate( vSigs );
        }
}
void Prs_ManCleanMap( Prs_Ntk_t * pNtk, Vec_Int_t * vMap )
{
    Vec_Int_t * vSigs; 
    int i, k, NameId, Sig;
    Prs_NtkForEachPi( pNtk, NameId, i )
        Vec_IntWriteEntry( vMap, NameId, -1 );
    Prs_NtkForEachBox( pNtk, vSigs, i )
        Vec_IntForEachEntryDouble( vSigs, NameId, Sig, k )
            Vec_IntWriteEntry( vMap, Prs_NtkSigName(pNtk, Sig), -1 );
    Prs_NtkForEachPo( pNtk, NameId, i )
        Vec_IntWriteEntry( vMap, NameId, -1 );
}
// create maps of NameId and boxes
void Prs_ManBuildNtk( Cba_Ntk_t * pNew, Vec_Ptr_t * vDes, Prs_Ntk_t * pNtk, Vec_Int_t * vMap, Vec_Int_t * vBoxes )
{
    Prs_Ntk_t * pNtkBox; Vec_Int_t * vSigs; int iBox;
    int i, Index, NameId, iObj, iConst0, iTerm;
    int iNonDriven = -1, nNonDriven = 0;
    assert( Prs_NtkPioNum(pNtk) == 0 );
    Prs_ManRemapBoxes( pNew->pDesign, vDes, pNtk, vMap );
    Cba_NtkStartNames( pNew );
    // create primary inputs 
    Prs_NtkForEachPi( pNtk, NameId, i )
    {
        if ( Vec_IntEntry(vMap, NameId) != -1 )
            printf( "Primary inputs %d and %d have the same name.\n", Vec_IntEntry(vMap, NameId), i );
        iObj = Cba_ObjAlloc( pNew, CBA_OBJ_PI, -1 );
        Cba_ObjSetName( pNew, iObj, NameId );
        Vec_IntWriteEntry( vMap, NameId, iObj );
    }
    // create box outputs
    Vec_IntClear( vBoxes );
    Prs_NtkForEachBox( pNtk, vSigs, iBox )
        if ( !Prs_BoxIsNode(pNtk, iBox) )
        {
            pNtkBox = Prs_ManNtk( vDes, Prs_BoxNtk(pNtk, iBox) );
            if ( pNtkBox == NULL )
            {
                iObj = Cba_BoxAlloc( pNew, CBA_BOX_GATE, Vec_IntSize(vSigs)/2-1, 1, Prs_BoxNtk(pNtk, iBox) + 1 ); // +1 to map NtkId into gate name
                Cba_ObjSetName( pNew, iObj, Prs_BoxName(pNtk, iBox) );
                // consider box output 
                NameId = Vec_IntEntryLast( vSigs );
                NameId = Prs_NtkSigName( pNtk, NameId );
                if ( Vec_IntEntry(vMap, NameId) != -1 )
                    printf( "Box output name %d is already driven.\n", NameId );
                iTerm = Cba_BoxBo( pNew, iObj, 0 );
                Cba_ObjSetName( pNew, iTerm, NameId );
                Vec_IntWriteEntry( vMap, NameId, iTerm );
            }
            else
            {
                iObj = Cba_BoxAlloc( pNew, CBA_OBJ_BOX, Prs_NtkPiNum(pNtkBox), Prs_NtkPoNum(pNtkBox), Prs_BoxNtk(pNtk, iBox) );
                Cba_ObjSetName( pNew, iObj, Prs_BoxName(pNtk, iBox) );
                Cba_NtkSetHost( Cba_ManNtk(pNew->pDesign, Prs_BoxNtk(pNtk, iBox)), Cba_NtkId(pNew), iObj );
                Vec_IntForEachEntry( vSigs, Index, i )
                {
                    i++;
                    if ( --Index < Prs_NtkPiNum(pNtkBox) )
                        continue;
                    assert( Index - Prs_NtkPiNum(pNtkBox) < Prs_NtkPoNum(pNtkBox) );
                    // consider box output 
                    NameId = Vec_IntEntry( vSigs, i );
                    NameId = Prs_NtkSigName( pNtk, NameId );
                    if ( Vec_IntEntry(vMap, NameId) != -1 )
                        printf( "Box output name %d is already driven.\n", NameId );
                    iTerm = Cba_BoxBo( pNew, iObj, Index - Prs_NtkPiNum(pNtkBox) );
                    Cba_ObjSetName( pNew, iTerm, NameId );
                    Vec_IntWriteEntry( vMap, NameId, iTerm );
                }
            }
            // remember box
            Vec_IntPush( vBoxes, iObj );
        }
        else
        {
            iObj = Cba_BoxAlloc( pNew, Prs_BoxNtk(pNtk, iBox), Prs_BoxIONum(pNtk, iBox)-1, 1, -1 );
            // consider box output 
            NameId = Vec_IntEntryLast( vSigs );
            NameId = Prs_NtkSigName( pNtk, NameId );
            if ( Vec_IntEntry(vMap, NameId) != -1 )
                printf( "Node output name %d is already driven.\n", NameId );
            iTerm = Cba_BoxBo( pNew, iObj, 0 );
            Cba_ObjSetName( pNew, iTerm, NameId );
            Vec_IntWriteEntry( vMap, NameId, iTerm );
            // remember box
            Vec_IntPush( vBoxes, iObj );
        }
    // add fanins for box inputs
    Prs_NtkForEachBox( pNtk, vSigs, iBox )
        if ( !Prs_BoxIsNode(pNtk, iBox) )
        {
            pNtkBox = Prs_ManNtk( vDes, Prs_BoxNtk(pNtk, iBox) );
            iObj = Vec_IntEntry( vBoxes, iBox );
            if ( pNtkBox == NULL )
            {
                Vec_IntForEachEntryStop( vSigs, Index, i, Vec_IntSize(vSigs)-2 )
                {
                    i++;
                    NameId = Vec_IntEntry( vSigs, i );
                    NameId = Prs_NtkSigName( pNtk, NameId );
                    iTerm = Cba_BoxBi( pNew, iObj, i/2 );
                    if ( Vec_IntEntry(vMap, NameId) == -1 )
                    {
                        iConst0 = Cba_BoxAlloc( pNew, CBA_BOX_C0, 0, 1, -1 );
                        Vec_IntWriteEntry( vMap, NameId, iConst0+1 );
                        if ( iNonDriven == -1 )
                            iNonDriven = NameId;
                        nNonDriven++;
                    }
                    Cba_ObjSetFanin( pNew, iTerm, Vec_IntEntry(vMap, NameId) );
                    Cba_ObjSetName( pNew, iTerm, NameId );
                }
            }
            else
            {
                Vec_IntForEachEntry( vSigs, Index, i )
                {
                    i++;
                    if ( --Index >= Prs_NtkPiNum(pNtkBox) )
                        continue;
                    NameId = Vec_IntEntry( vSigs, i );
                    NameId = Prs_NtkSigName( pNtk, NameId );
                    iTerm = Cba_BoxBi( pNew, iObj, Index );
                    if ( Vec_IntEntry(vMap, NameId) == -1 )
                    {
                        iConst0 = Cba_BoxAlloc( pNew, CBA_BOX_C0, 0, 1, -1 );
                        Vec_IntWriteEntry( vMap, NameId, iConst0+1 );
                        if ( iNonDriven == -1 )
                            iNonDriven = NameId;
                        nNonDriven++;
                    }
                    Cba_ObjSetFanin( pNew, iTerm, Vec_IntEntry(vMap, NameId) );
                    Cba_ObjSetName( pNew, iTerm, NameId );
                }
            }
        }
        else
        {
            iObj = Vec_IntEntry( vBoxes, iBox );
            Vec_IntForEachEntryStop( vSigs, Index, i, Vec_IntSize(vSigs)-2 )
            {
                NameId = Vec_IntEntry( vSigs, ++i );
                NameId = Prs_NtkSigName( pNtk, NameId );
                iTerm = Cba_BoxBi( pNew, iObj, i/2 );
                if ( Vec_IntEntry(vMap, NameId) == -1 )
                {
                    iConst0 = Cba_BoxAlloc( pNew, CBA_BOX_C0, 0, 1, -1 );
                    Vec_IntWriteEntry( vMap, NameId, iConst0+1 );
                    if ( iNonDriven == -1 )
                        iNonDriven = NameId;
                    nNonDriven++;
                }
                Cba_ObjSetFanin( pNew, iTerm, Vec_IntEntry(vMap, NameId) );
                Cba_ObjSetName( pNew, iTerm, NameId );
            }
        }
    // add fanins for primary outputs
    Prs_NtkForEachPo( pNtk, NameId, i )
        if ( Vec_IntEntry(vMap, NameId) == -1 )
        {
            iConst0 = Cba_BoxAlloc( pNew, CBA_BOX_C0, 0, 1, -1 );
            Vec_IntWriteEntry( vMap, NameId, iConst0+1 );
            if ( iNonDriven == -1 )
                iNonDriven = NameId;
            nNonDriven++;
        }
    Prs_NtkForEachPo( pNtk, NameId, i )
    {
        iObj = Cba_ObjAlloc( pNew, CBA_OBJ_PO, Vec_IntEntry(vMap, NameId) );
        Cba_ObjSetName( pNew, iObj, NameId );
    }
    if ( nNonDriven )
        printf( "Module %s has %d non-driven nets (for example, %s).\n", Prs_NtkName(pNtk), nNonDriven, Prs_NtkStr(pNtk, iNonDriven) );
    Prs_ManCleanMap( pNtk, vMap );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cba_Man_t * Prs_ManBuildCba( char * pFileName, Vec_Ptr_t * vDes )
{
    Prs_Ntk_t * pNtk = Prs_ManRoot( vDes );  int i;
    Cba_Man_t * pNew = Cba_ManAlloc( pFileName, Vec_PtrSize(vDes) );
    Vec_Int_t * vMap = Vec_IntStartFull( Abc_NamObjNumMax(pNtk->pStrs) + 1 );
    Vec_Int_t * vTmp = Vec_IntAlloc( Prs_NtkBoxNum(pNtk) );
    Abc_NamDeref( pNew->pStrs );
    pNew->pStrs = Abc_NamRef( pNtk->pStrs );  
    Vec_PtrForEachEntry( Prs_Ntk_t *, vDes, pNtk, i )
        Cba_NtkAlloc( Cba_ManNtk(pNew, i), Prs_NtkId(pNtk), Prs_NtkPiNum(pNtk), Prs_NtkPoNum(pNtk), Prs_NtkCountObjects(pNtk) );
    if ( (pNtk->fMapped || (pNtk->fSlices && Prs_ManIsMapped(pNtk))) && !Cba_NtkBuildLibrary(pNew) )
        Cba_ManFree(pNew), pNew = NULL;
    else 
        Vec_PtrForEachEntry( Prs_Ntk_t *, vDes, pNtk, i )
            Prs_ManBuildNtk( Cba_ManNtk(pNew, i), vDes, pNtk, vMap, vTmp );
    assert( Vec_IntCountEntry(vMap, -1) == Vec_IntSize(vMap) );
    Vec_IntFree( vMap );
    Vec_IntFree( vTmp );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

