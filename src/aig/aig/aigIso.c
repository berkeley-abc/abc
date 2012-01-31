/**CFile****************************************************************

  FileName    [aigIso.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Graph isomorphism package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigIso.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ISO_NUM_INTS 3

typedef struct Iso_Obj_t_ Iso_Obj_t;
struct Iso_Obj_t_
{
    // hashing entries (related to the parameter ISO_NUM_INTS!)
    unsigned      fFlop    :  1;
    unsigned      nFinPos  :  2;
    unsigned      nFoutPos : 29;
    unsigned      fMux     :  1;
    unsigned      nFinNeg  :  2;
    unsigned      nFoutNeg : 29;
    int           Level;
    // other data
    int           iNext;          // hash table entry
    int           iClass;         // next one in class
    int           Id;             // unique ID
    Vec_Int_t *   vAllies;        // solved neighbors
};

typedef struct Iso_Man_t_ Iso_Man_t;
struct Iso_Man_t_
{
    Aig_Man_t *   pAig;           // user's AIG manager
    Iso_Obj_t *   pObjs;          // isomorphism objects
    int           nObjIds;        // counter of object IDs
    int           nClasses;       // total number of classes
    int           nEntries;       // total number of entries
    int           nSingles;       // total number of singletons
    int           nObjs;          // total objects
    int           nBins;          // hash table size
    int *         pBins;          // hash table 
    Vec_Int_t *   vPolRefs;       // polarity references
    Vec_Ptr_t *   vSingles;       // singletons 
    Vec_Ptr_t *   vClasses;       // other classes
};

static inline Iso_Obj_t *  Iso_ManObj( Iso_Man_t * p, int i )            { assert( i >= 0 && i < p->nObjs ); return i ? p->pObjs + i : NULL;                     }
static inline int          Iso_ObjId( Iso_Man_t * p, Iso_Obj_t * pObj )  { assert( pObj > p->pObjs && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs;      }

static inline void Iso_ObjIncPolRef0( Vec_Int_t * vPolRefs, Aig_Obj_t * pObj ) { Vec_IntAddToEntry( vPolRefs, 2*Aig_ObjFaninId0(pObj)+Aig_ObjFaninC0(pObj), 1 ); }
static inline void Iso_ObjIncPolRef1( Vec_Int_t * vPolRefs, Aig_Obj_t * pObj ) { Vec_IntAddToEntry( vPolRefs, 2*Aig_ObjFaninId1(pObj)+Aig_ObjFaninC1(pObj), 1 ); }

#define Iso_ManForEachObj( p, pObj, i )   \
    for ( i = 1; (i < p->nObjs) && ((pObj) = Iso_ManObj(p, i)); i++ ) if ( pIso->Level == -1 ) {} else

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Iso_ManNegEdgeNum( Aig_Man_t * pAig )
{
    Aig_Obj_t * pObj;
    int i, Counter = 0;
    if ( pAig->nComplEdges > 0 )
        return pAig->nComplEdges;
    Aig_ManForEachObj( pAig, pObj, i )
        if ( Aig_ObjIsNode(pObj) )
        {
            Counter += Aig_ObjFaninC0(pObj);
            Counter += Aig_ObjFaninC1(pObj);
        }
        else if ( Aig_ObjIsPo(pObj) )
            Counter += Aig_ObjFaninC0(pObj);
    return (pAig->nComplEdges = Counter);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Iso_ManComputePolRefs( Aig_Man_t * pAig )
{
    Vec_Int_t * vPolRefs;
    Aig_Obj_t * pObj;
    int i;
    vPolRefs = Vec_IntStart( 2 * Aig_ManObjNumMax( pAig ) );
    Aig_ManForEachObj( pAig, pObj, i )
        if ( Aig_ObjIsNode(pObj) )
        {
            Iso_ObjIncPolRef0( vPolRefs, pObj );
            Iso_ObjIncPolRef1( vPolRefs, pObj );
        }
        else if ( Aig_ObjIsPo(pObj) )
            Iso_ObjIncPolRef0( vPolRefs, pObj );
    return vPolRefs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Iso_Man_t * Iso_ManStart( Aig_Man_t * pAig )
{
    Iso_Man_t * p;
    p = ABC_CALLOC( Iso_Man_t, 1 );
    p->pAig     = pAig;
    p->nObjs    = Aig_ManObjNumMax( pAig );
    p->pObjs    = ABC_CALLOC( Iso_Obj_t, p->nObjs );
    p->nBins    = Abc_PrimeCudd( p->nObjs );
    p->pBins    = ABC_CALLOC( int, p->nBins );    
    p->vPolRefs = Iso_ManComputePolRefs( pAig );
    p->vSingles = Vec_PtrAlloc( 1000 );
    p->vClasses = Vec_PtrAlloc( 1000 );
    p->nObjIds  = 1;
    return p;
}
void Iso_ManStop( Iso_Man_t * p )
{
    Iso_Obj_t * pIso;
    int i;
    Iso_ManForEachObj( p, pIso, i )
        Vec_IntFreeP( &pIso->vAllies );
    Vec_PtrFree( p->vClasses );
    Vec_PtrFree( p->vSingles );
    Vec_IntFree( p->vPolRefs );
    ABC_FREE( p->pBins );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Compares two objects by their signature.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Iso_ObjCompare( Iso_Obj_t ** pp1, Iso_Obj_t ** pp2 )
{
    Iso_Obj_t * pIso1 = *pp1;
    Iso_Obj_t * pIso2 = *pp2;
    int Diff = memcmp( pIso1, pIso2, sizeof(int) * ISO_NUM_INTS );
    if ( Diff )
        return Diff;
//    return 0;
    if ( pIso1->vAllies == NULL && pIso2->vAllies == NULL )
        return  0;
    if ( pIso1->vAllies == NULL && pIso2->vAllies != NULL )
        return -1;
    if ( pIso1->vAllies != NULL && pIso2->vAllies == NULL )
        return  1;
    Diff = Vec_IntSize(pIso1->vAllies) - Vec_IntSize(pIso2->vAllies);
    if ( Diff )
        return Diff;
    return memcmp( Vec_IntArray(pIso1->vAllies), Vec_IntArray(pIso2->vAllies), Vec_IntSize(pIso1->vAllies) * sizeof(int) );
}

/**Function*************************************************************

  Synopsis    [Compares two objects by their ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Iso_ObjCompareById( Iso_Obj_t ** pp1, Iso_Obj_t ** pp2 )
{
    Iso_Obj_t * pIso1 = *pp1;
    Iso_Obj_t * pIso2 = *pp2;
    return pIso1->Id - pIso2->Id;
}

/**Function*************************************************************

  Synopsis    [Compares two objects by their ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Iso_ObjCompareAigObjByData( Aig_Obj_t ** pp1, Aig_Obj_t ** pp2 )
{
    Aig_Obj_t * pIso1 = *pp1;
    Aig_Obj_t * pIso2 = *pp2;
    assert( Aig_ObjIsPi(pIso1) && Aig_ObjIsPi(pIso2) );
    return pIso1->iData - pIso2->iData;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Iso_ObjHash( Iso_Obj_t * pIso, int nBins )
{
    static unsigned BigPrimes[8] = {12582917, 25165843, 50331653, 100663319, 201326611, 402653189, 805306457, 1610612741};
    unsigned * pArray = (unsigned *)pIso;
    unsigned i, Value = 0;
    assert( ISO_NUM_INTS < 8 );
    for ( i = 0; i < ISO_NUM_INTS; i++ )
        Value ^= BigPrimes[i] * pArray[i];
    return Value % nBins;
}
static inline int Iso_ObjHashAdd( Iso_Man_t * p, Iso_Obj_t * pIso )
{
    Iso_Obj_t * pThis;
    int * pPlace = p->pBins + Iso_ObjHash( pIso, p->nBins );
    p->nEntries++;
    for ( pThis = Iso_ManObj(p, *pPlace); 
          pThis; pPlace = &pThis->iNext, 
          pThis = Iso_ManObj(p, *pPlace) )
        if ( Iso_ObjCompare( &pThis, &pIso ) == 0 ) // equal signatures
        {
            if ( pThis->iClass == 0 )
            {
                p->nClasses++;
                p->nSingles--;
            }
            // add to the list
            pIso->iClass = pThis->iClass;
            pThis->iClass = Iso_ObjId( p, pIso );
            return 1;
        }
    // create new list
    *pPlace = Iso_ObjId( p, pIso );
    p->nSingles++;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Iso_Man_t * Iso_ManCreate( Aig_Man_t * pAig )
{
    Iso_Man_t * p;
    Iso_Obj_t * pIso;
    Aig_Obj_t * pObj;
    int i;
    p = Iso_ManStart( pAig );
    Iso_ManForEachObj( p, pIso, i )
        pIso->Level = -1;
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( !Aig_ObjIsPi(pObj) && !Aig_ObjIsNode(pObj) )
            continue;
        pIso = p->pObjs + i;
        if ( Aig_ObjIsNode(pObj) )
        {
            pIso->nFinNeg  = Aig_ObjFaninC0(pObj) + Aig_ObjFaninC1(pObj);
            pIso->nFinPos  = 2 - pIso->nFinNeg;
            pIso->fMux  = Aig_ObjIsMuxType( pObj );
        }
        else
            pIso->fFlop = (int)(Aig_ObjPioNum(pObj) >= Aig_ManPiNum(pAig) - Aig_ManRegNum(pAig));
        pIso->nFoutPos = Vec_IntEntry( p->vPolRefs, 2*i );
        pIso->nFoutNeg = Vec_IntEntry( p->vPolRefs, 2*i+1 );
        pIso->Level = pObj->Level;
        // add to the hash table
        Iso_ObjHashAdd( p, pIso );
    }
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManCollectClasses( Iso_Man_t * p )
{
    Iso_Obj_t * pIso;
    int i;
    Vec_PtrClear( p->vSingles );
    Vec_PtrClear( p->vClasses );
    for ( i = 0; i < p->nBins; i++ )
        for ( pIso = Iso_ManObj(p, p->pBins[i]); pIso; pIso = Iso_ManObj(p, pIso->iNext) )
        {
            assert( pIso->Id == 0 );
            if ( pIso->iClass )
                Vec_PtrPush( p->vClasses, pIso );
            else 
                Vec_PtrPush( p->vSingles, pIso );
        }
    Vec_PtrSort( p->vSingles, (int (*)(void))Iso_ObjCompare );
    Vec_PtrSort( p->vClasses, (int (*)(void))Iso_ObjCompare );
    assert( Vec_PtrSize(p->vSingles) == p->nSingles );
    assert( Vec_PtrSize(p->vClasses) == p->nClasses );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManPrintClasses( Iso_Man_t * p, int fVerbose )
{
    int fOnlyCis = 1;
    int fVeryVerbose = 0;
    Iso_Obj_t * pIso, * pTemp;
    int i;

    // count unique objects
    if ( fVerbose )
        printf( "Total objects =%7d.  Entries =%7d.  Classes =%7d.  Singles =%7d.\n", 
            p->nObjs, p->nEntries, p->nClasses, p->nSingles );

    if ( !fVeryVerbose )
        return;

    Iso_ManCollectClasses( p );

    printf( "Non-trivial classes:\n" );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
    {
        if ( fOnlyCis && pIso->Level > 0 )
            continue;

        printf( "%5d : {", i );
        for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
        {
            if ( fOnlyCis )
                printf( " %d", Aig_ObjPioNum(Aig_ManObj(p->pAig, Iso_ObjId(p, pTemp))) );
            else
                printf( " %d", Iso_ObjId(p, pTemp) );
            printf( "(%d,%d,%d)", pTemp->Level, pTemp->nFoutPos, pTemp->nFoutNeg );
            if ( pTemp->vAllies )
            {
                int Entry, k;
                printf( "[" );
                Vec_IntForEachEntry( pTemp->vAllies, Entry, k )
                    printf( "%s%d", k?",":"", Entry );
                printf( "]" );
            }
        }        
        printf( " }\n" );
    }
}


/**Function*************************************************************

  Synopsis    [Creates adjacency lists.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Iso_ObjAddToAllies( Iso_Obj_t * pIso, int Id )
{
    assert( pIso->Id == 0 );
    if ( pIso->vAllies == NULL )
        pIso->vAllies = Vec_IntAlloc( 8 );
    Vec_IntPush( pIso->vAllies, Id );        
}
void Iso_ManAssignAdjacency( Iso_Man_t * p )
{
    Iso_Obj_t * pIso, * pIso0, * pIso1;
    Aig_Obj_t * pObj, * pObjLi;
    int i;
    // clean
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( i == 0 ) continue;
        pIso = Iso_ManObj( p, i );
        if ( pIso->vAllies )
            Vec_IntClear( pIso->vAllies );
    }
    // create
    Aig_ManForEachNode( p->pAig, pObj, i )
    {
        pIso  = Iso_ManObj( p, i );
        pIso0 = Iso_ManObj( p, Aig_ObjFaninId0(pObj) );
        pIso1 = Iso_ManObj( p, Aig_ObjFaninId1(pObj) );
        if ( pIso->Id ) // unique - add to non-unique fanins
        {
            if ( pIso0->Id == 0 )
                Iso_ObjAddToAllies( pIso0, pIso->Id );
            if ( pIso1->Id == 0 )
                Iso_ObjAddToAllies( pIso1, pIso->Id );
        }
        else // non-unique - assign unique fanins to it
        {
            if ( pIso0->Id != 0 )
                Iso_ObjAddToAllies( pIso, pIso0->Id );
            if ( pIso1->Id != 0 )
                Iso_ObjAddToAllies( pIso, pIso1->Id );
        }
    }
    // consider flops
    Aig_ManForEachLiLoSeq( p->pAig, pObjLi, pObj, i )
    {
        if ( Aig_ObjFaninId0(pObjLi) == 0 ) // ignore!
            continue;
        pIso  = Iso_ManObj( p, Aig_ObjId(pObj) );
        pIso0 = Iso_ManObj( p, Aig_ObjFaninId0(pObjLi) );
        if ( pIso->Id ) // unique - add to non-unique fanins
        {
            if ( pIso0->Id == 0 )
                Iso_ObjAddToAllies( pIso0, pIso->Id );
        }
        else // non-unique - assign unique fanins to it
        {
            if ( pIso0->Id != 0 )
                Iso_ObjAddToAllies( pIso, pIso0->Id );
        }
    }
    // sort
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( i == 0 ) continue;
        pIso = Iso_ManObj( p, i );
        if ( pIso->vAllies )
            Vec_IntSort( pIso->vAllies, 0 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManRehashClassNodes( Iso_Man_t * p )
{
    Iso_Obj_t * pIso, * pTemp;
    int i;
    // collect nodes
    Vec_PtrClear( p->vSingles );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
        for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
            Vec_PtrPush( p->vSingles, pTemp );
    // clean and add nodes
    p->nClasses = 0;       // total number of classes
    p->nEntries = 0;       // total number of entries
    p->nSingles = 0;       // total number of singletons
    memset( p->pBins, 0, sizeof(int) * p->nBins );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vSingles, pIso, i )
    {
        pIso->iClass = pIso->iNext = 0;
        Iso_ObjHashAdd( p, pIso );
    }
    Vec_PtrClear( p->vSingles );
}

/**Function*************************************************************

  Synopsis    [Returns one if there are unclassified CIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Iso_ManCheckCis( Iso_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManForEachPi( p->pAig, pObj, i )
        if ( Aig_ObjRefs(pObj) > 0 && Iso_ManObj(p, Aig_ObjId(pObj))->Id == 0 )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Finalizes unification of combinational outputs.]

  Description [Assigns IDs to the unclassified CIs in the order of obj IDs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Iso_ManFinalize( Iso_Man_t * p )
{
    Vec_Int_t * vRes;
    Vec_Ptr_t * vClass, * vClass2;
    Iso_Obj_t * pIso, * pTemp;
    Aig_Obj_t * pObj;
    int i, k;

    vClass  = Vec_PtrAlloc( Aig_ManPiNum(p->pAig)-Aig_ManRegNum(p->pAig) );
    vClass2 = Vec_PtrAlloc( Aig_ManRegNum(p->pAig) );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
    {
        if ( pIso->Level > 0 )
            continue;
        Vec_PtrClear( vClass );
        for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
        {
            assert( pTemp->Id == 0 );
            pTemp->Id = Aig_ObjPioNum(Aig_ManObj(p->pAig, Iso_ObjId(p, pTemp)));
            Vec_PtrPush( vClass, pTemp );
        }
        Vec_PtrSort( vClass, (int (*)(void))Iso_ObjCompareById );
        // assign IDs in this order
        Vec_PtrForEachEntry( Iso_Obj_t *, vClass, pIso, k )
            pIso->Id = p->nObjIds++;
    }

    // assign unique IDs to the CIs
    Vec_PtrClear( vClass );
    Vec_PtrClear( vClass2 );
    Aig_ManForEachPi( p->pAig, pObj, i )
    {
        pObj->iData = Iso_ManObj(p, Aig_ObjId(pObj))->Id;
        if ( Aig_ObjPioNum(pObj) >= Aig_ManPiNum(p->pAig) - Aig_ManRegNum(p->pAig) )
            Vec_PtrPush( vClass2, pObj );
        else
            Vec_PtrPush( vClass, pObj );
    }
    // sort CIs by their IDs
    Vec_PtrSort( vClass, (int (*)(void))Iso_ObjCompareAigObjByData );
    Vec_PtrSort( vClass2, (int (*)(void))Iso_ObjCompareAigObjByData );

    // create the result
    vRes = Vec_IntAlloc( Aig_ManPiNum(p->pAig) );
    Vec_PtrForEachEntry( Aig_Obj_t *, vClass, pObj, i )
        Vec_IntPush( vRes, Aig_ObjPioNum(pObj) );
    Vec_PtrForEachEntry( Aig_Obj_t *, vClass2, pObj, i )
        Vec_IntPush( vRes, Aig_ObjPioNum(pObj) );

    Vec_PtrFree( vClass );
    Vec_PtrFree( vClass2 );
    return vRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Iso_ManFindPerm( Aig_Man_t * pAig, int fVerbose )
{
    Iso_Man_t * p;
    Iso_Obj_t * pIso;
    Vec_Int_t * vRes;
    int i;
    p = Iso_ManCreate( pAig );
    Iso_ManPrintClasses( p, fVerbose );
    while ( p->nSingles )
    {
        // collect singletons and classes
        Iso_ManCollectClasses( p );
        // assign IDs to singletons
        Vec_PtrForEachEntry( Iso_Obj_t *, p->vSingles, pIso, i )
            pIso->Id = p->nObjIds++;
        // check termination
        if ( p->nClasses == 0 )
            break;
        // assign adjacency to classes
        Iso_ManAssignAdjacency( p );
        // rehash the class nodes
        Iso_ManRehashClassNodes( p );
        Iso_ManPrintClasses( p, fVerbose );
    }
    vRes = Iso_ManFinalize( p );
    Iso_ManStop( p );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Checks structural equivalence of AIG1 and AIG2.]

  Description [Returns 1 if AIG1 and AIG2 are structurally equivalent 
  under this mapping.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Iso_ManCheckMapping( Aig_Man_t * pAig1, Aig_Man_t * pAig2, Vec_Int_t * vMap2to1, int fVerbose )
{
    Aig_Obj_t * pObj, * pFanin0, * pFanin1;
    int i;
    assert( Aig_ManPiNum(pAig1) == Aig_ManPiNum(pAig2) );
    assert( Aig_ManPoNum(pAig1) == Aig_ManPoNum(pAig2) );
    assert( Aig_ManRegNum(pAig1) == Aig_ManRegNum(pAig2) );
    assert( Aig_ManNodeNum(pAig1) == Aig_ManNodeNum(pAig2) );
    Aig_ManCleanData( pAig1 );
    // map const and PI nodes
    Aig_ManConst1(pAig2)->pData = Aig_ManConst1(pAig1);
    Aig_ManForEachPi( pAig2, pObj, i )
        pObj->pData = Aig_ManPi( pAig1, Vec_IntEntry(vMap2to1, i) );
    // try internal nodes
    Aig_ManForEachNode( pAig2, pObj, i )
    {
        pFanin0 = Aig_ObjChild0Copy( pObj );
        pFanin1 = Aig_ObjChild1Copy( pObj );
        pObj->pData = Aig_TableLookupTwo( pAig1, pFanin0, pFanin1 );
        if ( pObj->pData == NULL )
        {
            if ( fVerbose )
                printf( "Structural equivalence failed at node %d.\n", i );
            return 0;
        }
    }
    // make sure the first PO points to the same node
    if ( Aig_ManPoNum(pAig1)-Aig_ManRegNum(pAig1) == 1 && Aig_ObjChild0Copy(Aig_ManPo(pAig2, 0)) != Aig_ObjChild0(Aig_ManPo(pAig1, 0)) )
    {
        if ( fVerbose )
            printf( "Structural equivalence failed at primary output 0.\n" );
        return 0;
    }
    return 1;    
}

/**Function*************************************************************

  Synopsis    [Finds mapping of CIs of AIG2 into those of AIG1.]

  Description [Returns the mapping of CIs of the two AIGs, or NULL
  if there is no mapping.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Iso_ManFindMapping( Aig_Man_t * pAig1, Aig_Man_t * pAig2, Vec_Int_t * vPerm1_, Vec_Int_t * vPerm2_, int fVerbose )
{
    Vec_Int_t * vPerm1, * vPerm2, * vInvPerm2;
    int i, Entry;
    if ( Aig_ManPiNum(pAig1) != Aig_ManPiNum(pAig2) )
        return NULL;
    if ( Aig_ManPoNum(pAig1) != Aig_ManPoNum(pAig2) )
        return NULL;
    if ( Aig_ManRegNum(pAig1) != Aig_ManRegNum(pAig2) )
        return NULL;
    if ( Aig_ManNodeNum(pAig1) != Aig_ManNodeNum(pAig2) )
        return NULL;
    if ( Aig_ManLevelNum(pAig1) != Aig_ManLevelNum(pAig2) )
        return NULL;
    if ( Iso_ManNegEdgeNum(pAig1) != Iso_ManNegEdgeNum(pAig2) )
        return NULL;
    if ( fVerbose ) 
        printf( "AIG1:\n" );
    vPerm1 = vPerm1_ ? vPerm1_ : Iso_ManFindPerm( pAig1, fVerbose );
    if ( fVerbose )
        printf( "AIG1:\n" );
    vPerm2 = vPerm2_ ? vPerm2_ : Iso_ManFindPerm( pAig2, fVerbose );
    if ( vPerm1_ )
        assert( Vec_IntSize(vPerm1_) == Aig_ManPiNum(pAig1) );
    if ( vPerm2_ )
        assert( Vec_IntSize(vPerm2_) == Aig_ManPiNum(pAig2) );
    // find canonical permutation
    // vPerm1/vPerm2 give canonical order of CIs of AIG1/AIG2
    vInvPerm2 = Vec_IntInvert( vPerm2, -1 );
    Vec_IntForEachEntry( vInvPerm2, Entry, i )
    {
        assert( Entry >= 0 && Entry < Aig_ManPiNum(pAig1) );
        Vec_IntWriteEntry( vInvPerm2, i, Vec_IntEntry(vPerm1, Entry) );
    }
    if ( vPerm1_ == NULL )
        Vec_IntFree( vPerm1 );
    if ( vPerm2_ == NULL )
        Vec_IntFree( vPerm2 );
    // check if they are indeed equivalent
    if ( !Iso_ManCheckMapping( pAig1, pAig2, vInvPerm2, fVerbose ) )
        Vec_IntFreeP( &vInvPerm2 );
    return vInvPerm2;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManTestOne( Aig_Man_t * pAig, int fVerbose )
{
    Vec_Int_t * vPerm;
    vPerm = Iso_ManFindPerm( pAig, fVerbose );
    Vec_IntFree( vPerm );
}



#include "src/aig/saig/saig.h"

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Iso_ManFilterPos( Aig_Man_t * pAig, int fVerbose )
{
    int fVeryVerbose = 0;
    Vec_Ptr_t * vParts, * vPerms, * vAigs;
    Vec_Int_t * vPos, * vMap;
    Aig_Man_t * pPart, * pTemp;
    int i, k, nPos;

    // derive AIG for each PO
    nPos = Aig_ManPoNum(pAig) - Aig_ManRegNum(pAig);
    vParts = Vec_PtrAlloc( nPos );
    vPerms = Vec_PtrAlloc( nPos );
    for ( i = 0; i < nPos; i++ )
    {
        pPart = Saig_ManDupCones( pAig, &i, 1 );
        vMap  = Iso_ManFindPerm( pPart, fVeryVerbose );
        Vec_PtrPush( vParts, pPart ); 
        Vec_PtrPush( vPerms, vMap );
    }

    // check AIGs for each PO
    vAigs = Vec_PtrAlloc( 1000 );
    vPos  = Vec_IntAlloc( 1000 );
    Vec_PtrForEachEntry( Aig_Man_t *, vParts, pPart, i )
    {
        if ( fVeryVerbose )
        {
            printf( "AIG %4d : ", i );
            Aig_ManPrintStats( pPart );
        }
        Vec_PtrForEachEntry( Aig_Man_t *, vAigs, pTemp, k )
        {
            if ( fVeryVerbose )
                printf( "Comparing AIG %4d and AIG %4d.  ", Vec_IntEntry(vPos,k), i );
            vMap = Iso_ManFindMapping( pTemp, pPart, 
                (Vec_Int_t *)Vec_PtrEntry(vPerms, Vec_IntEntry(vPos,k)), 
                (Vec_Int_t *)Vec_PtrEntry(vPerms, i),
                fVeryVerbose );
            if ( vMap != NULL )
            {
                if ( fVeryVerbose )
                    printf( "Found match\n" );
                if ( fVerbose )
                    printf( "Found match for AIG %4d and AIG %4d.\n", Vec_IntEntry(vPos,k), i );
                Vec_IntFree( vMap );
                break;
            }
            if ( fVeryVerbose )
                printf( "No match.\n" );
        }
        if ( k == Vec_PtrSize(vAigs) )
        {
            Vec_PtrPush( vAigs, pPart );
            Vec_IntPush( vPos, i );
        }
    }
    // delete AIGs
    Vec_PtrForEachEntry( Aig_Man_t *, vParts, pPart, i )
        Aig_ManStop( pPart );
    Vec_PtrFree( vParts );
    Vec_PtrForEachEntry( Vec_Int_t *, vPerms, vMap, i )
        Vec_IntFree( vMap );
    Vec_PtrFree( vPerms );
    // derive the resulting AIG
    pPart = Saig_ManDupCones( pAig, Vec_IntArray(vPos), Vec_IntSize(vPos) );
    Vec_PtrFree( vAigs );
    Vec_IntFree( vPos );
    return pPart;
}


#include "src/base/abc/abc.h"

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManTestOld( Aig_Man_t * pAig1, int fVerbose )
{
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
    Abc_Ntk_t * pNtk;
    Aig_Man_t * pAig2;
    Vec_Int_t * vMap;
    
    pNtk = Abc_NtkFromAigPhase( pAig1 );
    Abc_NtkPermute( pNtk, 1, 0, 1 );
    pAig2 = Abc_NtkToDar( pNtk, 0, 1 );
    Abc_NtkDelete( pNtk );

    vMap = Iso_ManFindMapping( pAig1, pAig2, NULL, NULL, fVerbose );
    Aig_ManStop( pAig2 );

    if ( vMap != NULL )
    {
        printf( "Mapping of AIGs is found.\n" );
        if ( fVerbose )
            Vec_IntPrint( vMap );
    }
    else
        printf( "Mapping of AIGs is NOT found.\n" );
    Vec_IntFreeP( &vMap );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Iso_ManTest( Aig_Man_t * pAig, int fVerbose )
{ 
    Aig_Man_t * pPart;
    int clk = clock();
    pPart = Iso_ManFilterPos( pAig, fVerbose );
    printf( "Reduced %d outputs to %d outputs.  ", Saig_ManPoNum(pAig), Saig_ManPoNum(pPart) );
    Abc_PrintTime( 1, "Time", clock() - clk );
//    Aig_ManStop( pPart );
    return pPart;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

