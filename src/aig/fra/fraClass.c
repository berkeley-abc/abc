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
    The classes are ordered according to the topological order of their representatives.
    The array of pointers to the class nodes is terminated with a NULL pointer.
    To enable dynamic addition of new classes (during class refinement),
    each array has at least as many NULLs in the end, as there are nodes in the class.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

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
        for ( nNodes = 0; pClass[nNodes]; nNodes++ )
        {
            if ( nNodes > DAR_INFINITY )
            {
                printf( "Error in equivalence classes.\n" );
                break;
            }
        }
        nPairs += (nNodes - 1) * (nNodes - 2) / 2;
    }
    return nPairs;
}

/**Function*************************************************************

  Synopsis    [Computes hash value using simulation info.]

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
    pSims  = Fra_ObjSim(pObj);
    for ( i = 0; i < p->nSimWords; i++ )
        uHash ^= pSims[i] * s_FPrimes[i];
    return uHash;
}

/**Function********************************************************************

  Synopsis    [Returns the next prime &gt;= p.]

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
    Dar_Obj_t ** pTable;
    Dar_Obj_t * pObj;
    int i, k, k2, nTableSize, nEntries, iEntry;
    // allocate the table
    nTableSize = Cudd_PrimeFra( Dar_ManNodeNum(p->pManAig) );
    pTable = ALLOC( Dar_Obj_t *, nTableSize ); 
    memset( pTable, 0, sizeof(Dar_Obj_t *) * nTableSize );
    // collect nodes into the table
    Vec_PtrClear( p->vClasses1 );
    Dar_ManForEachObj( p->pManAig, pObj, i )
    {
        if ( !Dar_ObjIsPi(pObj) && !Dar_ObjIsNode(pObj) )
            continue;
        // hash the node by its simulation info
        iEntry = Fra_NodeHash( p, pObj ) % nTableSize;
        // check if the node belongs to the class of constant 1
        if ( iEntry == 0 && Fra_NodeHasZeroSim( p, pObj ) )
        {
            Vec_PtrPush( p->vClasses1, pObj );
            continue;
        }
        // add the node to the table
        pObj->pData = pTable[iEntry];
        pTable[iEntry] = pObj;
    }
    // count the total number of nodes in the non-trivial classes
    nEntries = 0;
    for ( i = 0; i < nTableSize; i++ )
        if ( pTable[i] && pTable[i]->pData )
        {
            k = 0;
            for ( pObj = pTable[i]; pObj; pObj = pObj->pData )
                k++;
            nEntries += 2*k;
        }
    // allocate room for classes
    p->pMemClasses = ALLOC( Dar_Obj_t *, nEntries + 2*Vec_PtrSize(p->vClasses1) );
    p->pMemClassesFree = p->pMemClasses + nEntries;
    // copy the entries into storage
    Vec_PtrClear( p->vClasses );
    nEntries = 0;
    for ( i = 0; i < nTableSize; i++ )
        if ( pTable[i] && pTable[i]->pData )
        {
            k = 0;
            for ( pObj = pTable[i]; pObj; pObj = pObj->pData )
                k++;
            // write entries in the topological order
            k2 = k;
            for ( pObj = pTable[i]; pObj; pObj = pObj->pData )
            {
                k2--;
                p->pMemClasses[nEntries+k2] = pObj;
                p->pMemClasses[nEntries+k+k2] = NULL;
            }
            assert( k2 == 0 );
            Vec_PtrPush( p->vClasses, p->pMemClasses + nEntries );
            nEntries += 2*k;
        }
    free( pTable );
    // now it is time to refine the classes
    Fra_RefineClasses( p );
    // set the pointer to the manager
    Dar_ManForEachObj( p->pManAig, pObj, i )
        pObj->pData = p->pManAig;
}

/**Function*************************************************************

  Synopsis    [Refines one class using simulation info.]

  Description [Returns the new class if refinement happened.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t ** Fra_RefineClassOne( Fra_Man_t * p, Dar_Obj_t ** pClass )
{
    Dar_Obj_t * pObj;
    int i;
    assert( pClass[1] != NULL );
    // check if the class is going to be refined
    for ( pObj = pClass[1]; pObj; pObj++ )        
        if ( !Fra_NodeCompareSims(p, pClass[0], pObj) )
            break;
    if ( pObj == NULL )
        return NULL;
    // split the class
    Vec_PtrClear( p->vClassOld );
    Vec_PtrClear( p->vClassNew );
    Vec_PtrPush( p->vClassOld, pClass[0] );
    for ( pObj = pClass[1]; pObj; pObj++ )        
        if ( Fra_NodeCompareSims(p, pClass[0], pObj) )
            Vec_PtrPush( p->vClassOld, pObj );
        else
            Vec_PtrPush( p->vClassNew, pObj );
    // put the nodes back into the class memory
    Vec_PtrForEachEntry( p->vClassOld, pObj, i )
    {
        pClass[i] = pObj;
        pClass[Vec_PtrSize(p->vClassOld)+i] = NULL;
    }
    pClass += 2*Vec_PtrSize(p->vClassOld);
    // put the new nodes into the class memory
    Vec_PtrForEachEntry( p->vClassNew, pObj, i )
    {
        pClass[i] = pObj;
        pClass[Vec_PtrSize(p->vClassNew)+i] = NULL;
    }
    return pClass;
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
            break;
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
    int clk, i, nRefis = 0;
    // check if some outputs already became non-constant
    // this is a special case when computation can be stopped!!!
    if ( p->pPars->fProve )
        Fra_CheckOutputSims( p );
    if ( p->pManFraig->pData )
        return 0;
    // refine the classes
clk = clock();
    Vec_PtrClear( p->vClassesTemp );
    Vec_PtrForEachEntry( p->vClasses, pClass, i )
    {
        // add the class to the new array
        Vec_PtrPush( p->vClassesTemp, pClass );
        // refine the class interatively
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
    Dar_Obj_t * pObj, ** pClass;
    int i, k;
    // collect all the nodes to be refined
    Vec_PtrClear( p->vClassNew );
    k = 0;
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
        return 1;
    // create a new class composed of these nodes
    pClass = p->pMemClassesFree;
    p->pMemClassesFree += 2 * Vec_PtrSize(p->vClassNew);
    Vec_PtrForEachEntry( p->vClassNew, pObj, i )
    {
        pClass[i] = pObj;
        pClass[Vec_PtrSize(p->vClassNew)+i] = NULL;
    }
    Vec_PtrPush( p->vClasses, pClass );
    // iteratively refine this class
    return 1 + Fra_RefineClassLastIter( p, p->vClasses );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


