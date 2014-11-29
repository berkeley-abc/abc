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

typedef struct Int_Des_t_ Int_Des_t;
struct Int_Des_t_
{
    char *           pName;   // design name
    Abc_Nam_t *      pNames;  // name manager
    Vec_Ptr_t        vModels; // models
};
typedef struct Int_Obj_t_ Int_Obj_t;
struct Int_Obj_t_
{
    int              iModel;
    int              iFunc;
    Vec_Wrd_t        vFanins;
};
typedef struct Int_Ntk_t_ Int_Ntk_t;
struct Int_Ntk_t_
{
    int              iName;
    int              nObjs;
    Int_Des_t *      pMan;
    Vec_Ptr_t        vInstances;
    Vec_Wrd_t        vOutputs;
    Vec_Int_t        vInputNames;
    Vec_Int_t        vOutputNames;
    Vec_Int_t *      vCopies;
    Vec_Int_t *      vCopies2;
};

static inline char *      Int_DesName( Int_Des_t * p )       { return p->pName;                                     }
static inline int         Int_DesNtkNum( Int_Des_t * p )     { return Vec_PtrSize( &p->vModels ) - 1;               }
static inline Int_Ntk_t * Int_DesNtk( Int_Des_t * p, int i ) { return (Int_Ntk_t *)Vec_PtrEntry( &p->vModels, i );  }

static inline char *      Int_NtkName( Int_Ntk_t * p )       { return Abc_NamStr( p->pMan->pNames, p->iName );      }
static inline int         Int_NtkPiNum( Int_Ntk_t * p )      { return Vec_IntSize( &p->vInputNames );               }
static inline int         Int_NtkPoNum( Int_Ntk_t * p )      { return Vec_IntSize( &p->vOutputNames );              }

static inline int         Int_ObjInputNum( Int_Ntk_t * p, Int_Obj_t * pObj )  { return pObj->iModel ? Int_NtkPiNum(Int_DesNtk(p->pMan, pObj->iModel)) : Vec_WrdSize(&pObj->vFanins); }
static inline int         Int_ObjOutputNum( Int_Ntk_t * p, Int_Obj_t * pObj ) { return pObj->iModel ? Int_NtkPoNum(Int_DesNtk(p->pMan, pObj->iModel)) : 1;                           }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transform Ptr into Int.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ptr_ManCheckArray( Vec_Ptr_t * vArray )
{
    if ( Vec_PtrSize(vArray) == 0 )
        return 1;
    if ( Abc_MaxInt(8, Vec_PtrSize(vArray)) == Vec_PtrCap(vArray) )
        return 1;
    assert( 0 );
    return 0;
}
Vec_Int_t * Ptr_ManDumpArrayToInt( Abc_Nam_t * pNames, Vec_Ptr_t * vVec, int fNode )
{
    char * pName; int i;
    Vec_Int_t * vNew = Vec_IntAlloc( Vec_PtrSize(vVec) );
    Vec_PtrForEachEntry( char *, vVec, pName, i )
        Vec_IntPush( vNew, (fNode && i == 1) ? Abc_Ptr2Int(pName) : Abc_NamStrFind(pNames, pName) );
    return vNew;
}
Vec_Ptr_t * Ptr_ManDumpArrarArrayToInt( Abc_Nam_t * pNames, Vec_Ptr_t * vNodes, int fNode )
{
    Vec_Ptr_t * vNode; int i;
    Vec_Ptr_t * vNew = Vec_PtrAlloc( Vec_PtrSize(vNodes) );
    Vec_PtrForEachEntry( Vec_Ptr_t *, vNodes, vNode, i )
        Vec_PtrPush( vNew, Ptr_ManDumpArrayToInt(pNames, vNode, fNode) );
    assert( Ptr_ManCheckArray(vNew) );
    return vNew;
}
Vec_Ptr_t * Ptr_ManDumpNtkToInt( Abc_Nam_t * pNames, Vec_Ptr_t * vNtk, int i )
{
    Vec_Ptr_t * vNew   = Vec_PtrAlloc( 5 );
    assert( Abc_NamStrFind(pNames, (char *)Vec_PtrEntry(vNtk, 0)) == i );
    Vec_PtrPush( vNew, Abc_Int2Ptr(i) );
    Vec_PtrPush( vNew, Ptr_ManDumpArrayToInt(pNames, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1), 0) );
    Vec_PtrPush( vNew, Ptr_ManDumpArrayToInt(pNames, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2), 0) );
    Vec_PtrPush( vNew, Ptr_ManDumpArrarArrayToInt(pNames, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3), 1) );
    Vec_PtrPush( vNew, Ptr_ManDumpArrarArrayToInt(pNames, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4), 0) );
    assert( Ptr_ManCheckArray(vNew) );
    return vNew;
}
Vec_Ptr_t * Ptr_ManDumpToInt( Vec_Ptr_t * vDes )
{
    Vec_Ptr_t * vNew = Vec_PtrAlloc( Vec_PtrSize(vDes) );
    Vec_Ptr_t * vNtk; int i;
    // create module names
    Abc_Nam_t * pNames = Abc_NamStart( 1000, 20 );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Abc_NamStrFind( pNames, (char *)Vec_PtrEntry(vNtk, 0) );
    assert( i == Abc_NamObjNumMax(pNames) );
    // create resulting array
    Vec_PtrPush( vNew, pNames );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Vec_PtrPush( vNew, Ptr_ManDumpNtkToInt(pNames, vNtk, i) );
    assert( Ptr_ManCheckArray(vNew) );
    return vNew;
}

/**Function*************************************************************

  Synopsis    [Transform Ptr into Int.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Int_Obj_t * Int_ObjAlloc( int nFanins )
{
    Int_Obj_t * p = (Int_Obj_t *)ABC_CALLOC( char, sizeof(Int_Obj_t) + sizeof(word) * nFanins );
    p->vFanins.pArray = (word *)((char *)p + sizeof(Int_Obj_t));
    p->vFanins.nCap = nFanins;
    return p;
}
void Int_ObjFree( Int_Obj_t * p )
{
    ABC_FREE( p );
}
Int_Ntk_t * Int_NtkAlloc( Int_Des_t * pMan, int Id, int nPis, int nPos, int nInsts )
{
    Int_Ntk_t * p = ABC_CALLOC( Int_Ntk_t, 1 );
    p->iName = Id;
    p->nObjs = nPis + nInsts;
    p->pMan  = pMan;
    Vec_PtrGrow( &p->vInstances,   nInsts );
    Vec_WrdGrow( &p->vOutputs,     nPos );
    Vec_IntGrow( &p->vInputNames,  nPis );
    Vec_IntGrow( &p->vOutputNames, nPos );
    return p;
}
void Int_NtkFree( Int_Ntk_t * p )
{
    Int_Obj_t * pObj; int i;
    Vec_PtrForEachEntry( Int_Obj_t *, &p->vInstances, pObj, i )
        Int_ObjFree( pObj );
    ABC_FREE( p->vInstances.pArray );
    ABC_FREE( p->vOutputs.pArray );
    ABC_FREE( p->vInputNames.pArray );
    ABC_FREE( p->vOutputNames.pArray );
    Vec_IntFreeP( &p->vCopies );
    Vec_IntFreeP( &p->vCopies2 );
    ABC_FREE( p );
}
Int_Des_t * Int_DesAlloc( char * pName, Abc_Nam_t * pNames, int nModels )
{
    Int_Des_t * p = ABC_CALLOC( Int_Des_t, 1 );
    p->pName  = pName;
    p->pNames = pNames;
    Vec_PtrGrow( &p->vModels, nModels );
    return p;
}
void Int_DesFree( Int_Des_t * p )
{
    Int_Ntk_t * pTemp; int i;
    Vec_PtrForEachEntry( Int_Ntk_t *, &p->vModels, pTemp, i )
        Int_NtkFree( pTemp );
    ABC_FREE( p );
}

// replaces formal inputs by their indixes
void Ptr_ManFindInputOutputNumbers( Int_Ntk_t * pModel, Vec_Int_t * vBox, Vec_Int_t * vMap ) 
{
    int i, iFormal, iName, nPis = Int_NtkPiNum(pModel);
    Vec_IntForEachEntry( &pModel->vInputNames, iFormal, i )
        Vec_IntWriteEntry( vMap, iFormal, i );
    Vec_IntForEachEntry( &pModel->vOutputNames, iFormal, i )
        Vec_IntWriteEntry( vMap, iFormal, nPis+i );
    Vec_IntForEachEntryDouble( vBox, iFormal, iName, i )
    {
        if ( i == 0 ) continue;
        assert( Vec_IntEntry(vMap, iFormal) >= 0 );
        Vec_IntWriteEntry( vBox, i, Vec_IntEntry(vMap, iFormal) );
    }
    Vec_IntForEachEntry( &pModel->vInputNames, iFormal, i )
        Vec_IntWriteEntry( vMap, iFormal, -1 );
    Vec_IntForEachEntry( &pModel->vOutputNames, iFormal, i )
        Vec_IntWriteEntry( vMap, iFormal, -1 );
}
void Ptr_ManConvertNtk( Int_Ntk_t * pNtk, Vec_Ptr_t * vNtk, Vec_Wrd_t * vMap, Vec_Int_t * vMap2 )
{
    Vec_Int_t * vInputs  = (Vec_Int_t *)Vec_PtrEntry(vNtk, 1);
    Vec_Int_t * vOutputs = (Vec_Int_t *)Vec_PtrEntry(vNtk, 2);
    Vec_Ptr_t * vNodes   = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3);
    Vec_Ptr_t * vBoxes   = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4);
    Vec_Int_t * vNode, * vBox;
    Int_Ntk_t * pModel;
    Int_Obj_t * pObj;
    int i, k, iFormal, iName, nPis, nOffset, nNonDriven = 0;

    // map primary inputs
    Vec_IntForEachEntry( vInputs, iName, i )
    {
        assert( ~Vec_WrdEntry(vMap, iName) == 0 ); // driven twice
        Vec_WrdWriteEntry( vMap, iName, i );
    }
    // map internal nodes
    nOffset = Vec_IntSize(vInputs);
    Vec_PtrForEachEntry( Vec_Int_t *, vNodes, vNode, i )
    {
        iName = Vec_IntEntry(vNode, 0);
        assert( ~Vec_WrdEntry(vMap, iName) == 0 ); // driven twice
        Vec_WrdWriteEntry( vMap, iName, nOffset + i );
    }
    // map internal boxes
    nOffset += Vec_PtrSize(vNodes);
    Vec_PtrForEachEntry( Vec_Int_t *, vBoxes, vBox, i )
    {
        // get model name
        iName = Vec_IntEntry( vBox, 0 );
        assert( iName >= 1 && iName <= Int_DesNtkNum(pNtk->pMan) ); // bad model name
        pModel = Int_DesNtk( pNtk->pMan, iName );
        nPis = Int_NtkPiNum( pModel );
        // replace inputs/outputs by their IDs
        Ptr_ManFindInputOutputNumbers( pModel, vBox, vMap2 );
        // go through outputs of this box
        Vec_IntForEachEntryDouble( vBox, iFormal, iName, k )
            if ( k > 0 && i >= nPis )  // output
            {
                assert( ~Vec_WrdEntry(vMap, iName) == 0 ); // driven twice
                Vec_WrdWriteEntry( vMap, iName, (nOffset + i) | ((word)iFormal << 32) );
            }
    }

    // save input names
    Vec_IntForEachEntry( vInputs, iName, i )
        Vec_IntPush( &pNtk->vInputNames, iName );
    // create nodes with the given connectivity
    Vec_PtrForEachEntry( Vec_Int_t *, vNodes, vNode, i )
    {
        pObj = Int_ObjAlloc( Vec_IntSize(vNode) - 2 );
        pObj->iFunc = Vec_IntEntry(vNode, 1);
        Vec_IntForEachEntryStart( vNode, iName, k, 2 )
        {
            Vec_WrdPush( &pObj->vFanins, Vec_WrdEntry(vMap, iName) );
            nNonDriven += (~Vec_WrdEntry(vMap, iName) == 0);
        }
        Vec_PtrPush( &pNtk->vInstances, pObj );
    }
    // create boxes with the given connectivity
    Vec_PtrForEachEntry( Vec_Int_t *, vBoxes, vBox, i )
    {
        pModel = Int_DesNtk( pNtk->pMan, Vec_IntEntry(vBox, 0) );
        nPis = Int_NtkPiNum( pModel );
        pObj = Int_ObjAlloc( nPis );
        Vec_IntForEachEntryDouble( vBox, iFormal, iName, k )
            if ( k > 0 && iFormal < nPis ) // input
            {
                Vec_WrdPush( &pObj->vFanins, Vec_WrdEntry(vMap, iName) );
                nNonDriven += (~Vec_WrdEntry(vMap, iName) == 0);
            }
        Vec_PtrPush( &pNtk->vInstances, pObj );
    }
    // save output names
    Vec_IntForEachEntry( vOutputs, iName, i )
    {
        Vec_IntPush( &pNtk->vOutputNames, iName );
        Vec_WrdPush( &pNtk->vOutputs, Vec_WrdEntry(vMap, iName) );
        nNonDriven += (~Vec_WrdEntry(vMap, iName) == 0);
    }
    if ( nNonDriven )
        printf( "Model %s has %d non-driven nets.\n", Int_NtkName(pNtk), nNonDriven );
}
Int_Ntk_t * Ptr_ManConvertNtkInter( Int_Des_t * pDes, Vec_Ptr_t * vNtk, int Id )
{
    Vec_Int_t * vInputs  = (Vec_Int_t *)Vec_PtrEntry(vNtk, 1);
    Vec_Int_t * vOutputs = (Vec_Int_t *)Vec_PtrEntry(vNtk, 2);
    Vec_Ptr_t * vNodes   = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3);
    Vec_Ptr_t * vBoxes   = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4);
    return Int_NtkAlloc( pDes, Id, Vec_IntSize(vInputs), Vec_IntSize(vOutputs), Vec_PtrSize(vNodes) + Vec_PtrSize(vBoxes) );
}
Int_Des_t * Ptr_ManConvert( Vec_Ptr_t * vDesPtr )
{
    Vec_Ptr_t * vNtk; int i;
    char * pName = (char *)Vec_PtrEntry(vDesPtr, 0);
    Vec_Ptr_t * vDes = Ptr_ManDumpToInt( vDesPtr );
    Abc_Nam_t * pNames = (Abc_Nam_t *)Vec_PtrEntry(vDes, 0);
    Vec_Wrd_t * vMap = Vec_WrdStartFull( Abc_NamObjNumMax(pNames) + 1 );
    Vec_Int_t * vMap2 = Vec_IntStartFull( Abc_NamObjNumMax(pNames) + 1 );
    Int_Des_t * pDes = Int_DesAlloc( pName, pNames, Vec_PtrSize(vDes)-1 );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Vec_PtrPush( &pDes->vModels, Ptr_ManConvertNtkInter(pDes, vNtk, i) );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Ptr_ManConvertNtk( Int_DesNtk(pDes, i), vNtk, vMap, vMap2 );
//    Ptr_ManFreeDes( vDes );
    Vec_IntFree( vMap2 );
    Vec_WrdFree( vMap );
    return pDes;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

