/**CFile****************************************************************

  FileName    [sswClass.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [Representation of candidate equivalence classes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswClass.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"

/*
    The candidate equivalence classes are stored as a vector of pointers 
    to the array of pointers to the nodes in each class.
    The first node of the class is its representative node.
    The representative has the smallest topological order among the class nodes.
    The nodes inside each class are ordered according to their topological order.
    The classes are ordered according to the topo order of their representatives.
*/

// internal representation of candidate equivalence classes
struct Ssw_Cla_t_
{
    // class information
    Aig_Man_t *      pAig;             // original AIG manager
    Aig_Obj_t ***    pId2Class;        // non-const classes by ID of repr node
    int *            pClassSizes;      // sizes of each equivalence class
    // statistics
    int              nClasses;         // the total number of non-const classes
    int              nCands1;          // the total number of const candidates
    int              nLits;            // the number of literals in all classes
    // memory
    Aig_Obj_t **     pMemClasses;      // memory allocated for equivalence classes
    Aig_Obj_t **     pMemClassesFree;  // memory allocated for equivalence classes to be used
    // temporary data
    Vec_Ptr_t *      vClassOld;        // old equivalence class after splitting
    Vec_Ptr_t *      vClassNew;        // new equivalence class(es) after splitting
    // procedures used for class refinement
    void *           pManData;
    unsigned (*pFuncNodeHash) (void *,Aig_Obj_t *);              // returns hash key of the node
    int (*pFuncNodeIsConst)   (void *,Aig_Obj_t *);              // returns 1 if the node is a constant
    int (*pFuncNodesAreEqual) (void *,Aig_Obj_t *, Aig_Obj_t *); // returns 1 if nodes are equal up to a complement
};

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Aig_Obj_t *  Ssw_ObjNext( Aig_Obj_t ** ppNexts, Aig_Obj_t * pObj )                       { return ppNexts[pObj->Id];  }
static inline void         Ssw_ObjSetNext( Aig_Obj_t ** ppNexts, Aig_Obj_t * pObj, Aig_Obj_t * pNext ) { ppNexts[pObj->Id] = pNext; }

// iterator through the equivalence classes
#define Ssw_ManForEachClass( p, ppClass, i )                 \
    for ( i = 0; i < Aig_ManObjNumMax(p->pAig); i++ )        \
        if ( ((ppClass) = p->pId2Class[i]) == NULL ) {} else
// iterator through the nodes in one class
#define Ssw_ClassForEachNode( p, pRepr, pNode, i )           \
    for ( i = 0; i < p->pClassSizes[pRepr->Id]; i++ )        \
        if ( ((pNode) = p->pId2Class[pRepr->Id][i]) == NULL ) {} else

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates one equivalence class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Ssw_ObjAddClass( Ssw_Cla_t * p, Aig_Obj_t * pRepr, Aig_Obj_t ** pClass, int nSize ) 
{
    assert( p->pId2Class[pRepr->Id] == NULL );
    p->pId2Class[pRepr->Id] = pClass; 
    assert( p->pClassSizes[pRepr->Id] == 0 );
    assert( nSize > 1 );
    p->pClassSizes[pRepr->Id] = nSize;
    p->nClasses++;
    p->nLits += nSize - 1;
}

/**Function*************************************************************

  Synopsis    [Removes one equivalence class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Aig_Obj_t ** Ssw_ObjRemoveClass( Ssw_Cla_t * p, Aig_Obj_t * pRepr ) 
{
    Aig_Obj_t ** pClass = p->pId2Class[pRepr->Id];
    int nSize;
    assert( pClass != NULL );
    p->pId2Class[pRepr->Id] = NULL; 
    nSize = p->pClassSizes[pRepr->Id];
    assert( nSize > 1 );
    p->nClasses--;
    p->nLits -= nSize - 1;
    p->pClassSizes[pRepr->Id] = 0;
    return pClass;
}

/**Function*************************************************************

  Synopsis    [Starts representation of equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ssw_Cla_t * Ssw_ClassesStart( Aig_Man_t * pAig )
{
    Ssw_Cla_t * p;
    p = ALLOC( Ssw_Cla_t, 1 );
    memset( p, 0, sizeof(Ssw_Cla_t) );
    p->pAig         = pAig;
    p->pId2Class    = CALLOC( Aig_Obj_t **, Aig_ManObjNumMax(pAig) );
    p->pClassSizes  = CALLOC( int, Aig_ManObjNumMax(pAig) );
    p->vClassOld    = Vec_PtrAlloc( 100 );
    p->vClassNew    = Vec_PtrAlloc( 100 );
    assert( pAig->pReprs == NULL );
    Aig_ManReprStart( pAig, Aig_ManObjNumMax(pAig) );
    return p;
}

/**Function*************************************************************

  Synopsis    [Starts representation of equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ClassesSetData( Ssw_Cla_t * p, void * pManData, 
    unsigned (*pFuncNodeHash)(void *,Aig_Obj_t *),               // returns hash key of the node
    int (*pFuncNodeIsConst)(void *,Aig_Obj_t *),                 // returns 1 if the node is a constant
    int (*pFuncNodesAreEqual)(void *,Aig_Obj_t *, Aig_Obj_t *) ) // returns 1 if nodes are equal up to a complement
{
    p->pManData           = pManData;
    p->pFuncNodeHash      = pFuncNodeHash;
    p->pFuncNodeIsConst   = pFuncNodeIsConst;
    p->pFuncNodesAreEqual = pFuncNodesAreEqual;
}

/**Function*************************************************************

  Synopsis    [Stop representation of equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ClassesStop( Ssw_Cla_t * p )
{
    if ( p->vClassNew )    Vec_PtrFree( p->vClassNew );
    if ( p->vClassOld )    Vec_PtrFree( p->vClassOld );
    FREE( p->pId2Class );
    FREE( p->pClassSizes );
    FREE( p->pMemClasses );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Stop representation of equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ClassesCand1Num( Ssw_Cla_t * p )
{
    return p->nCands1;
}

/**Function*************************************************************

  Synopsis    [Stop representation of equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ClassesClassNum( Ssw_Cla_t * p )
{
    return p->nClasses;
}

/**Function*************************************************************

  Synopsis    [Stop representation of equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ClassesLitNum( Ssw_Cla_t * p )
{
    return p->nLits;
}

/**Function*************************************************************

  Synopsis    [Stop representation of equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t ** Ssw_ClassesReadClass( Ssw_Cla_t * p, Aig_Obj_t * pRepr, int * pnSize )
{
    assert( p->pId2Class[pRepr->Id] != NULL );
    assert( p->pClassSizes[pRepr->Id] > 1 );
    *pnSize = p->pClassSizes[pRepr->Id];
    return p->pId2Class[pRepr->Id];
}

/**Function*************************************************************

  Synopsis    [Checks candidate equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ClassesCheck( Ssw_Cla_t * p )
{
    Aig_Obj_t * pObj, * pPrev, ** ppClass;
    int i, k, nLits, nClasses, nCands1;
    nClasses = nLits = 0;
    Ssw_ManForEachClass( p, ppClass, k )
    {
        pPrev = NULL;
        Ssw_ClassForEachNode( p, ppClass[0], pObj, i )
        {
            if ( i == 0 )
                assert( Aig_ObjRepr(p->pAig, pObj) == NULL );
            else
            {
                assert( Aig_ObjRepr(p->pAig, pObj) == ppClass[0] );
                assert( pPrev->Id < pObj->Id );
                nLits++;
            }
            pPrev = pObj;
        }
        nClasses++;
    }
    nCands1 = 0;
    Aig_ManForEachObj( p->pAig, pObj, i )
        nCands1 += Ssw_ObjIsConst1Cand( p->pAig, pObj );
    assert( p->nLits == nLits );
    assert( p->nCands1 == nCands1 );
    assert( p->nClasses == nClasses );
}

/**Function*************************************************************

  Synopsis    [Prints simulation classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ClassesPrintOne( Ssw_Cla_t * p, Aig_Obj_t * pRepr )
{
    Aig_Obj_t * pObj;
    int i;
    printf( "{ " );
    Ssw_ClassForEachNode( p, pRepr, pObj, i )
        printf( "%d(%d,%d) ", pObj->Id, pObj->Level, Aig_SupportSize(p->pAig,pObj) );
    printf( "}\n" );
}

/**Function*************************************************************

  Synopsis    [Prints simulation classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ClassesPrint( Ssw_Cla_t * p, int fVeryVerbose )
{
    Aig_Obj_t ** ppClass;
    Aig_Obj_t * pObj;
    int i;
    printf( "Equivalence classes: Const1 = %5d. Class = %5d. Lit = %5d.\n", 
        p->nCands1, p->nClasses, p->nLits );
    if ( !fVeryVerbose )
        return;
    printf( "Constants { " );
    Aig_ManForEachObj( p->pAig, pObj, i )
        if ( Ssw_ObjIsConst1Cand( p->pAig, pObj ) )
            printf( "%d(%d,%d) ", pObj->Id, pObj->Level, Aig_SupportSize(p->pAig,pObj) );
    printf( "}\n" );
    Ssw_ManForEachClass( p, ppClass, i )
    {
        printf( "%3d (%3d) : ", i, p->pClassSizes[i] );
        Ssw_ClassesPrintOne( p, ppClass[0] );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Prints simulation classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ClassesRemoveNode( Ssw_Cla_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pRepr, * pTemp;
    assert( p->pId2Class[pObj->Id] == NULL );
    pRepr = Aig_ObjRepr( p->pAig, pObj );
    assert( pRepr != NULL );
    Aig_ObjSetRepr( p->pAig, pObj, NULL );
    if ( Ssw_ObjIsConst1Cand( p->pAig, pObj ) )
    {
        p->nCands1--;
        return;
    }
    assert( p->pId2Class[pRepr->Id][0] == pRepr );
    assert( p->pClassSizes[pRepr->Id] >= 2 );
    if ( p->pClassSizes[pRepr->Id] == 2 )
    {
        p->pId2Class[pObj->Id] = NULL;
        p->nClasses--;
        p->pClassSizes[pRepr->Id] = 0;
        p->nLits--;
    }
    else
    {
        int i, k = 0;
        // remove the entry from the class
        Ssw_ClassForEachNode( p, pRepr, pTemp, i )
            if ( pTemp != pObj )
                p->pId2Class[pRepr->Id][k++] = pTemp;
        assert( k + 1 == p->pClassSizes[pRepr->Id] );
        // reduce the class
        p->pClassSizes[pRepr->Id]--;
        p->nLits--;
    }
}

/**Function*************************************************************

  Synopsis    [Creates initial simulation classes.]

  Description [Assumes that simulation info is assigned.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ClassesPrepare( Ssw_Cla_t * p, int fLatchCorr, int nMaxLevs )
{
    Aig_Obj_t ** ppTable, ** ppNexts, ** ppClassNew;
    Aig_Obj_t * pObj, * pTemp, * pRepr;
    int i, k, nTableSize, nNodes, iEntry, nEntries, nEntries2;

    // allocate the hash table hashing simulation info into nodes
    nTableSize = Aig_PrimeCudd( Aig_ManObjNumMax(p->pAig)/4 );
    ppTable = CALLOC( Aig_Obj_t *, nTableSize ); 
    ppNexts = CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p->pAig) ); 

    // add all the nodes to the hash table
    nEntries = 0;
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( fLatchCorr )
        {
            if ( !Aig_ObjIsPi(pObj) )
                continue;
        }
        else
        {
            if ( !Aig_ObjIsNode(pObj) && !Aig_ObjIsPi(pObj) )
                continue;
            // skip the node with more that the given number of levels
            if ( nMaxLevs && (int)pObj->Level >= nMaxLevs )
                continue;
        }
        // check if the node belongs to the class of constant 1
        if ( p->pFuncNodeIsConst( p->pManData, pObj ) )
        {
            Ssw_ObjSetConst1Cand( p->pAig, pObj );
            p->nCands1++;
            continue;
        }
        // hash the node by its simulation info
        iEntry = p->pFuncNodeHash( p->pManData, pObj ) % nTableSize;
        // add the node to the class
        if ( ppTable[iEntry] == NULL )
            ppTable[iEntry] = pObj;
        else
        {
            // set the representative of this node
            pRepr = ppTable[iEntry];
            Aig_ObjSetRepr( p->pAig, pObj, pRepr );
            // add node to the table
            if ( Ssw_ObjNext( ppNexts, pRepr ) == NULL )
            { // this will be the second entry
                p->pClassSizes[pRepr->Id]++;
                nEntries++;
            }
            // add the entry to the list
            Ssw_ObjSetNext( ppNexts, pObj, Ssw_ObjNext( ppNexts, pRepr ) );
            Ssw_ObjSetNext( ppNexts, pRepr, pObj );
            p->pClassSizes[pRepr->Id]++;
            nEntries++;
        }
    }

    // allocate room for classes
    p->pMemClasses = ALLOC( Aig_Obj_t *, nEntries + p->nCands1 );
    p->pMemClassesFree = p->pMemClasses + nEntries;
 
    // copy the entries into storage in the topological order
    nEntries2 = 0;
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( !Aig_ObjIsNode(pObj) && !Aig_ObjIsPi(pObj) )
            continue;
        nNodes = p->pClassSizes[pObj->Id];
        // skip the nodes that are not representatives of non-trivial classes
        if ( nNodes == 0 )
            continue;
        assert( nNodes > 1 );
        // add the nodes to the class in the topological order
        ppClassNew = p->pMemClasses + nEntries2;
        ppClassNew[0] = pObj;
        for ( pTemp = Ssw_ObjNext(ppNexts, pObj), k = 1; pTemp; 
              pTemp = Ssw_ObjNext(ppNexts, pTemp), k++ )
        {
            ppClassNew[nNodes-k] = pTemp;
        }
        // add the class of nodes
        p->pClassSizes[pObj->Id] = 0;
        Ssw_ObjAddClass( p, pObj, ppClassNew, nNodes );
        // increment the number of entries
        nEntries2 += nNodes;
    }
    assert( nEntries == nEntries2 );
    free( ppTable );
    free( ppNexts );
    // now it is time to refine the classes
    Ssw_ClassesRefine( p );
    Ssw_ClassesCheck( p );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node appears to be constant 1 candidate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_NodeIsConstCex( void * p, Aig_Obj_t * pObj )
{
    return pObj->fPhase == pObj->fMarkB;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the nodes appear equal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_NodesAreEqualCex( void * p, Aig_Obj_t * pObj0, Aig_Obj_t * pObj1 )
{
    return (pObj0->fPhase == pObj1->fPhase) == (pObj0->fMarkB == pObj1->fMarkB);
}

/**Function*************************************************************

  Synopsis    [Creates initial simulation classes.]

  Description [Assumes that simulation info is assigned.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ssw_Cla_t * Ssw_ClassesPrepareSimple( Aig_Man_t * pAig, int fLatchCorr, int nMaxLevs )
{
    Ssw_Cla_t * p;
    Aig_Obj_t * pObj;
    int i;
    // start the classes
    p = Ssw_ClassesStart( pAig );
    // go through the nodes
    p->nCands1 = 0;
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( fLatchCorr )
        {
            if ( !Saig_ObjIsLo(pAig, pObj) )
                continue;
        }
        else
        {
            if ( !Aig_ObjIsNode(pObj) && !Saig_ObjIsLo(pAig, pObj) )
                continue;
            // skip the node with more that the given number of levels
            if ( nMaxLevs && (int)pObj->Level >= nMaxLevs )
                continue;
        }
        Ssw_ObjSetConst1Cand( p->pAig, pObj );
        p->nCands1++;
    }
    // allocate room for classes
    p->pMemClassesFree = p->pMemClasses = ALLOC( Aig_Obj_t *, p->nCands1 );
    // set comparison procedures
    Ssw_ClassesSetData( p, NULL, NULL, Ssw_NodeIsConstCex, Ssw_NodesAreEqualCex );
//    Ssw_ClassesPrint( p, 0 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Iteratively refines the classes after simulation.]

  Description [Returns the number of refinements performed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ClassesRefineOneClass( Ssw_Cla_t * p, Aig_Obj_t * pReprOld, int fRecursive )
{
    Aig_Obj_t ** pClassOld, ** pClassNew;
    Aig_Obj_t * pObj, * pReprNew;
    int i;

    // split the class
    Vec_PtrClear( p->vClassOld );
    Vec_PtrClear( p->vClassNew );
    Ssw_ClassForEachNode( p, pReprOld, pObj, i )
        if ( p->pFuncNodesAreEqual(p->pManData, pReprOld, pObj) )
            Vec_PtrPush( p->vClassOld, pObj );
        else
            Vec_PtrPush( p->vClassNew, pObj );
    // check if splitting happened
    if ( Vec_PtrSize(p->vClassNew) == 0 )
        return 0;

    // get the new representative
    pReprNew = Vec_PtrEntry( p->vClassNew, 0 );
    assert( Vec_PtrSize(p->vClassOld) > 0 );
    assert( Vec_PtrSize(p->vClassNew) > 0 );

    // create old class
    pClassOld = Ssw_ObjRemoveClass( p, pReprOld );
    Vec_PtrForEachEntry( p->vClassOld, pObj, i )
    {
        pClassOld[i] = pObj;
        Aig_ObjSetRepr( p->pAig, pObj, i? pReprOld : NULL );
    }
    // create new class
    pClassNew = pClassOld + i;
    Vec_PtrForEachEntry( p->vClassNew, pObj, i )
    {
        pClassNew[i] = pObj;
        Aig_ObjSetRepr( p->pAig, pObj, i? pReprNew : NULL );
    }

    // put classes back
    if ( Vec_PtrSize(p->vClassOld) > 1 )
        Ssw_ObjAddClass( p, pReprOld, pClassOld, Vec_PtrSize(p->vClassOld) );
    if ( Vec_PtrSize(p->vClassNew) > 1 )
        Ssw_ObjAddClass( p, pReprNew, pClassNew, Vec_PtrSize(p->vClassNew) );

    // check if the class should be recursively refined
    if ( fRecursive && Vec_PtrSize(p->vClassNew) > 1 )
        return 1 + Ssw_ClassesRefineOneClass( p, pReprNew, 1 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Refines the classes after simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ClassesRefine( Ssw_Cla_t * p )
{
    Aig_Obj_t ** ppClass;
    int i, nRefis = 0;
    Ssw_ManForEachClass( p, ppClass, i )
        nRefis += Ssw_ClassesRefineOneClass( p, ppClass[0], 0 );
    return nRefis;
}

/**Function*************************************************************

  Synopsis    [Refine the group of constant 1 nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ClassesRefineConst1Group( Ssw_Cla_t * p, Vec_Ptr_t * vRoots, int fRecursive )
{
    Aig_Obj_t * pObj, * pReprNew, ** ppClassNew;
    int i;
    if ( Vec_PtrSize(vRoots) == 0 )
        return 0;
    // collect the nodes to be refined
    Vec_PtrClear( p->vClassNew );
    Vec_PtrForEachEntry( vRoots, pObj, i )
        if ( !p->pFuncNodeIsConst( p->pManData, pObj ) )
            Vec_PtrPush( p->vClassNew, pObj );
    // check if there is a new class
    if ( Vec_PtrSize(p->vClassNew) == 0 )
        return 0;
    p->nCands1 -= Vec_PtrSize(p->vClassNew);
    pReprNew = Vec_PtrEntry( p->vClassNew, 0 );
    Aig_ObjSetRepr( p->pAig, pReprNew, NULL );
    if ( Vec_PtrSize(p->vClassNew) == 1 )
        return 1;
    // create a new class composed of these nodes
    ppClassNew = p->pMemClassesFree;
    p->pMemClassesFree += Vec_PtrSize(p->vClassNew);
    Vec_PtrForEachEntry( p->vClassNew, pObj, i )
    {
        ppClassNew[i] = pObj;
        Aig_ObjSetRepr( p->pAig, pObj, i? pReprNew : NULL );
    }
    Ssw_ObjAddClass( p, pReprNew, ppClassNew, Vec_PtrSize(p->vClassNew) );
    // refine them recursively
    if ( fRecursive )
        return 1 + Ssw_ClassesRefineOneClass( p, pReprNew, 1 );
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


