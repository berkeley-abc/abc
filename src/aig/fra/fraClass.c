/**CFile****************************************************************

  FileName    [fraClass.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraClass.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

/*
    The candidate equivalence classes are stored as a vector of pointers 
    to the array of pointers to the nodes in each class.
    The first node of the class is its representative node.
    The representative has the smallest topological order among the class nodes.
    The nodes inside each class are ordered according to their topological order.
    The classes are ordered according to the topological order of their representatives.
    The array of pointers to the class nodes is terminated with a NULL pointer.
    To enable dynamic addition of new classes (during class refinement),
    each array has at least as many NULLs in the end, as there are nodes in the class.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Dar_Obj_t *  Fra_ObjNext( Dar_Obj_t ** ppNexts, Dar_Obj_t * pObj )                       { return ppNexts[pObj->Id];  }
static inline void         Fra_ObjSetNext( Dar_Obj_t ** ppNexts, Dar_Obj_t * pObj, Dar_Obj_t * pNext ) { ppNexts[pObj->Id] = pNext; }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prints simulation classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_PrintClass( Dar_Obj_t ** pClass )
{
    Dar_Obj_t * pTemp;
    int i;
    printf( "{ " );
    for ( i = 0; pTemp = pClass[i]; i++ )
        printf( "%d ", pTemp->Id );
    printf( "}\n" );
}

/**Function*************************************************************

  Synopsis    [Prints simulation classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_CountClass( Dar_Obj_t ** pClass )
{
    Dar_Obj_t * pTemp;
    int i;
    for ( i = 0; pTemp = pClass[i]; i++ );
    return i;
}

/**Function*************************************************************

  Synopsis    [Count the number of pairs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_CountPairsClasses( Fra_Man_t * p )
{
    Dar_Obj_t ** pClass;
    int i, nNodes, nPairs = 0;
    Vec_PtrForEachEntry( p->vClasses, pClass, i )
    {
        nNodes = Fra_CountClass( pClass );
        assert( nNodes > 1 );
        nPairs += nNodes * (nNodes - 1) / 2;
    }
    return nPairs;
}

/**Function*************************************************************

  Synopsis    [Prints simulation classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_PrintClasses( Fra_Man_t * p )
{
    Dar_Obj_t ** pClass;
    int i;
    printf( "Total classes = %d. Total pairs = %d.\n", Vec_PtrSize(p->vClasses), Fra_CountPairsClasses(p) );
    Vec_PtrForEachEntry( p->vClasses, pClass, i )
    {
//        printf( "%3d (%3d) : ", Fra_CountClass(pClass) );
//        Fra_PrintClass( pClass );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Computes hash value of the node using its simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Fra_NodeHash( Fra_Man_t * p, Dar_Obj_t * pObj )
{
    static int s_FPrimes[128] = { 
        1009, 1049, 1093, 1151, 1201, 1249, 1297, 1361, 1427, 1459, 
        1499, 1559, 1607, 1657, 1709, 1759, 1823, 1877, 1933, 1997, 
        2039, 2089, 2141, 2213, 2269, 2311, 2371, 2411, 2467, 2543, 
        2609, 2663, 2699, 2741, 2797, 2851, 2909, 2969, 3037, 3089, 
        3169, 3221, 3299, 3331, 3389, 3461, 3517, 3557, 3613, 3671, 
        3719, 3779, 3847, 3907, 3943, 4013, 4073, 4129, 4201, 4243, 
        4289, 4363, 4441, 4493, 4549, 4621, 4663, 4729, 4793, 4871, 
        4933, 4973, 5021, 5087, 5153, 5227, 5281, 5351, 5417, 5471, 
        5519, 5573, 5651, 5693, 5749, 5821, 5861, 5923, 6011, 6073, 
        6131, 6199, 6257, 6301, 6353, 6397, 6481, 6563, 6619, 6689, 
        6737, 6803, 6863, 6917, 6977, 7027, 7109, 7187, 7237, 7309, 
        7393, 7477, 7523, 7561, 7607, 7681, 7727, 7817, 7877, 7933, 
        8011, 8039, 8059, 8081, 8093, 8111, 8123, 8147
    };
    unsigned * pSims;
    unsigned uHash;
    int i;
    assert( p->nSimWords <= 128 );
    uHash = 0;
    pSims = Fra_ObjSim(pObj);
    for ( i = 0; i < p->nSimWords; i++ )
        uHash ^= pSims[i] * s_FPrimes[i];
    return uHash;
}

/**Function********************************************************************

  Synopsis    [Returns the next prime >= p.]

  Description [Copied from CUDD, for stand-aloneness.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
unsigned int Cudd_PrimeFra( unsigned int p )
{
    int i,pn;

    p--;
    do {
        p++;
        if (p&1) {
        pn = 1;
        i = 3;
        while ((unsigned) (i * i) <= p) {
        if (p % i == 0) {
            pn = 0;
            break;
        }
        i += 2;
        }
    } else {
        pn = 0;
    }
    } while (!pn);
    return(p);

} /* end of Cudd_Prime */


/**Function*************************************************************

  Synopsis    [Creates initial simulation classes.]

  Description [Assumes that simulation info is assigned.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_CreateClasses( Fra_Man_t * p )
{
    Dar_Obj_t ** ppTable, ** ppNexts;
    Dar_Obj_t * pObj, * pTemp;
    int i, k, nTableSize, nEntries, nNodes, iEntry;

    // allocate the hash table hashing simulation info into nodes
    nTableSize = Cudd_PrimeFra( Dar_ManObjIdMax(p->pManAig) + 1 );
    ppTable = ALLOC( Dar_Obj_t *, nTableSize ); 
    ppNexts = ALLOC( Dar_Obj_t *, nTableSize ); 
    memset( ppTable, 0, sizeof(Dar_Obj_t *) * nTableSize );

    // add all the nodes to the hash table
    Vec_PtrClear( p->vClasses1 );
    Dar_ManForEachObj( p->pManAig, pObj, i )
    {
        if ( !Dar_ObjIsNode(pObj) && !Dar_ObjIsPi(pObj) )
            continue;
        // hash the node by its simulation info
        iEntry = Fra_NodeHash( p, pObj ) % nTableSize;
        // check if the node belongs to the class of constant 1
        if ( iEntry == 0 && Fra_NodeHasZeroSim( p, pObj ) )
        {
            Vec_PtrPush( p->vClasses1, pObj );
            Fra_ObjSetRepr( pObj, Dar_ManConst1(p->pManAig) );
            continue;
        }
        // add the node to the class
        if ( ppTable[iEntry] == NULL )
        {
            ppTable[iEntry] = pObj;
            Fra_ObjSetNext( ppNexts, pObj, pObj );
        }
        else
        {
            Fra_ObjSetNext( ppNexts, pObj, Fra_ObjNext(ppNexts,ppTable[iEntry]) );
            Fra_ObjSetNext( ppNexts, ppTable[iEntry], pObj );
        }
    }

    // count the total number of nodes in the non-trivial classes
    // mark the representative nodes of each equivalence class
    nEntries = 0;
    for ( i = 0; i < nTableSize; i++ )
        if ( ppTable[i] && ppTable[i] != Fra_ObjNext(ppNexts, ppTable[i]) )
        {
            for ( pTemp = Fra_ObjNext(ppNexts, ppTable[i]), k = 1; 
                  pTemp != ppTable[i]; 
                  pTemp = Fra_ObjNext(ppNexts, pTemp), k++ );
            assert( k > 1 );
            nEntries += k;
            // mark the node
            assert( ppTable[i]->fMarkA == 0 );
            ppTable[i]->fMarkA = 1;
        }

    // allocate room for classes
    p->pMemClasses = ALLOC( Dar_Obj_t *, 2*(nEntries + Vec_PtrSize(p->vClasses1)) );
    p->pMemClassesFree = p->pMemClasses + 2*nEntries;

    // copy the entries into storage in the topological order
    Vec_PtrClear( p->vClasses );
    nEntries = 0;
    Dar_ManForEachObj( p->pManAig, pObj, i )
    {
        if ( !Dar_ObjIsNode(pObj) && !Dar_ObjIsPi(pObj) )
            continue;
        // skip the nodes that are not representatives of non-trivial classes
        if ( pObj->fMarkA == 0 )
            continue;
        pObj->fMarkA = 0;
        // add the class of nodes
        Vec_PtrPush( p->vClasses, p->pMemClasses + 2*nEntries );
        // count the number of entries in this class
        for ( pTemp = Fra_ObjNext(ppNexts, pObj), k = 1; 
              pTemp != pObj; 
              pTemp = Fra_ObjNext(ppNexts, pTemp), k++ );
        nNodes = k;
        assert( nNodes > 1 );
        // add the nodes to the class in the topological order
        p->pMemClasses[2*nEntries] = pObj;
        for ( pTemp = Fra_ObjNext(ppNexts, pObj), k = 1; 
              pTemp != pObj; 
              pTemp = Fra_ObjNext(ppNexts, pTemp), k++ )
        {
            p->pMemClasses[2*nEntries+nNodes-k] = pTemp;
            Fra_ObjSetRepr( pTemp, pObj );
        }
        // add as many empty entries
//        memset( p->pMemClasses + 2*nEntries + nNodes, 0, sizeof(Dar_Obj_t *) * nNodes );
        p->pMemClasses[2*nEntries + nNodes] = NULL;
        // increment the number of entries
        nEntries += k;
    }
    free( ppTable );
    free( ppNexts );
    // now it is time to refine the classes
    Fra_RefineClasses( p );
}

/**Function*************************************************************

  Synopsis    [Refines one class using simulation info.]

  Description [Returns the new class if refinement happened.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t ** Fra_RefineClassOne( Fra_Man_t * p, Dar_Obj_t ** ppClass )
{
    Dar_Obj_t * pObj, ** ppThis;
    int i;
    assert( ppClass[0] != NULL && ppClass[1] != NULL );
    // check if the class is going to be refined
    for ( ppThis = ppClass + 1; pObj = *ppThis; ppThis++ )        
        if ( !Fra_NodeCompareSims(p, ppClass[0], pObj) )
            break;
    if ( pObj == NULL )
        return NULL;
    // split the class
    Vec_PtrClear( p->vClassOld );
    Vec_PtrClear( p->vClassNew );
    Vec_PtrPush( p->vClassOld, ppClass[0] );
    for ( ppThis = ppClass + 1; pObj = *ppThis; ppThis++ )        
        if ( Fra_NodeCompareSims(p, ppClass[0], pObj) )
            Vec_PtrPush( p->vClassOld, pObj );
        else
            Vec_PtrPush( p->vClassNew, pObj );
    // put the nodes back into the class memory
    Vec_PtrForEachEntry( p->vClassOld, pObj, i )
    {
        ppClass[i] = pObj;
        ppClass[Vec_PtrSize(p->vClassOld)+i] = NULL;
        Fra_ObjSetRepr( pObj, i? ppClass[0] : NULL );
    }
    ppClass += 2*Vec_PtrSize(p->vClassOld);
    // put the new nodes into the class memory
    Vec_PtrForEachEntry( p->vClassNew, pObj, i )
    {
        ppClass[i] = pObj;
        ppClass[Vec_PtrSize(p->vClassNew)+i] = NULL;
        Fra_ObjSetRepr( pObj, i? ppClass[0] : NULL );
    }
    return ppClass;
}

/**Function*************************************************************

  Synopsis    [Iteratively refines the classes after simulation.]

  Description [Returns the number of refinements performed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_RefineClassLastIter( Fra_Man_t * p, Vec_Ptr_t * vClasses )
{
    Dar_Obj_t ** pClass, ** pClass2;
    int nRefis;
    pClass = Vec_PtrEntryLast( vClasses );
    for ( nRefis = 0; pClass2 = Fra_RefineClassOne( p, pClass ); nRefis++ )
    {
        // if the original class is trivial, remove it
        if ( pClass[1] == NULL )
            Vec_PtrPop( vClasses );
        // if the new class is trivial, stop
        if ( pClass2[1] == NULL )
        {
            nRefis++;
            break;
        }
        // othewise, add the class and continue
        Vec_PtrPush( vClasses, pClass2 );
        pClass = pClass2;
    }
    return nRefis;
}

/**Function*************************************************************

  Synopsis    [Refines the classes after simulation.]

  Description [Assumes that simulation info is assigned. Returns the
  number of classes refined.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_RefineClasses( Fra_Man_t * p )
{
    Vec_Ptr_t * vTemp;
    Dar_Obj_t ** pClass;
    int clk, i, nRefis;
    // check if some outputs already became non-constant
    // this is a special case when computation can be stopped!!!
    if ( p->pPars->fProve )
        Fra_CheckOutputSims( p );
    if ( p->pManFraig->pData )
        return 0;
    // refine the classes
clk = clock();
    nRefis = 0;
    Vec_PtrClear( p->vClassesTemp );
    Vec_PtrForEachEntry( p->vClasses, pClass, i )
    {
        // add the class to the new array
        Vec_PtrPush( p->vClassesTemp, pClass );
        // refine the class iteratively
        nRefis += Fra_RefineClassLastIter( p, p->vClassesTemp );
    }
    // exchange the class representation
    vTemp = p->vClassesTemp;
    p->vClassesTemp = p->vClasses;
    p->vClasses = vTemp;
p->timeRef += clock() - clk;
    return nRefis;
}

/**Function*************************************************************

  Synopsis    [Refines constant 1 equivalence class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_RefineClasses1( Fra_Man_t * p )
{
    Dar_Obj_t * pObj, ** ppClass;
    int i, k, nRefis, clk;
    // check if there is anything to refine
    if ( Vec_PtrSize(p->vClasses1) == 0 )
        return 0;
clk = clock();
    // make sure constant 1 class contains only non-constant nodes
    assert( Vec_PtrEntry(p->vClasses1,0) != Dar_ManConst1(p->pManAig) );
    // collect all the nodes to be refined
    k = 0;
    Vec_PtrClear( p->vClassNew );
    Vec_PtrForEachEntry( p->vClasses1, pObj, i )
    {
        if ( Fra_NodeHasZeroSim( p, pObj ) )
            Vec_PtrWriteEntry( p->vClasses1, k++, pObj );
        else 
            Vec_PtrPush( p->vClassNew, pObj );
    }
    Vec_PtrShrink( p->vClasses1, k );
    if ( Vec_PtrSize(p->vClassNew) == 0 )
        return 0;
    if ( Vec_PtrSize(p->vClassNew) == 1 )
    {
        Fra_ObjSetRepr( Vec_PtrEntry(p->vClassNew,0), NULL );
        return 1;
    }
    // create a new class composed of these nodes
    ppClass = p->pMemClassesFree;
    p->pMemClassesFree += 2 * Vec_PtrSize(p->vClassNew);
    Vec_PtrForEachEntry( p->vClassNew, pObj, i )
    {
        ppClass[i] = pObj;
        ppClass[Vec_PtrSize(p->vClassNew)+i] = NULL;
        Fra_ObjSetRepr( pObj, i? ppClass[0] : NULL );
    }
    Vec_PtrPush( p->vClasses, ppClass );
    // iteratively refine this class
    nRefis = 1 + Fra_RefineClassLastIter( p, p->vClasses );
p->timeRef += clock() - clk;
    return nRefis;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


