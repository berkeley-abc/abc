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

#include "saig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ISO_NUM_INTS 3

typedef struct Iso_Obj_t_ Iso_Obj_t;
struct Iso_Obj_t_
{
    // hashing entries (related to the parameter ISO_NUM_INTS!)
    unsigned      Level    : 30;
    unsigned      nFinNeg  :  2;
    unsigned      nFoutPos : 16;
    unsigned      nFoutNeg : 16;
    unsigned      nFinLev0 : 16;
    unsigned      nFinLev1 : 16;
//    unsigned      nNodes   : 16;
//    unsigned      nEdges   : 16;
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
    Vec_Ptr_t *   vSingles;       // singletons 
    Vec_Ptr_t *   vClasses;       // other classes
    Vec_Ptr_t *   vTemp1;         // other classes
    Vec_Ptr_t *   vTemp2;         // other classes
    int           timeHash;
    int           timeFout;
    int           timeOther;
    int           timeTotal;
};

static inline Iso_Obj_t *  Iso_ManObj( Iso_Man_t * p, int i )            { assert( i >= 0 && i < p->nObjs ); return i ? p->pObjs + i : NULL;                     }
static inline int          Iso_ObjId( Iso_Man_t * p, Iso_Obj_t * pObj )  { assert( pObj > p->pObjs && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs;      }
static inline Aig_Obj_t *  Iso_AigObj( Iso_Man_t * p, Iso_Obj_t * q )    { return Aig_ManObj( p->pAig, Iso_ObjId(p, q) );                                        }

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
void Iso_ManObjCount_rec( Aig_Man_t * p, Aig_Obj_t * pObj, int * pnNodes, int * pnEdges )
{
    if ( Aig_ObjIsPi(pObj) )
        return;
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    Iso_ManObjCount_rec( p, Aig_ObjFanin0(pObj), pnNodes, pnEdges );
    Iso_ManObjCount_rec( p, Aig_ObjFanin1(pObj), pnNodes, pnEdges );
    (*pnEdges) += Aig_ObjFaninC0(pObj) + Aig_ObjFaninC1(pObj);
    (*pnNodes)++;
}
void Iso_ManObjCount( Aig_Man_t * p, Aig_Obj_t * pObj, int * pnNodes, int * pnEdges )
{
    assert( Aig_ObjIsNode(pObj) );
    *pnNodes = *pnEdges = 0;
    Aig_ManIncrementTravId( p );
    Iso_ManObjCount_rec( p, pObj, pnNodes, pnEdges );
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
    p->vSingles = Vec_PtrAlloc( 1000 );
    p->vClasses = Vec_PtrAlloc( 1000 );
    p->vTemp1   = Vec_PtrAlloc( 1000 );
    p->vTemp2   = Vec_PtrAlloc( 1000 );
    p->nObjIds  = 1;
    return p;
}
void Iso_ManStop( Iso_Man_t * p, int fVerbose )
{
    Iso_Obj_t * pIso;
    int i;

    if ( fVerbose )
    {
        p->timeOther = p->timeTotal - p->timeHash - p->timeFout;
        ABC_PRTP( "Building ", p->timeFout,   p->timeTotal );
        ABC_PRTP( "Hashing  ", p->timeHash,   p->timeTotal );
        ABC_PRTP( "Other    ", p->timeOther,  p->timeTotal );
        ABC_PRTP( "TOTAL    ", p->timeTotal,  p->timeTotal );
    }

    Iso_ManForEachObj( p, pIso, i )
        Vec_IntFreeP( &pIso->vAllies );
    Vec_PtrFree( p->vTemp1 );
    Vec_PtrFree( p->vTemp2 );
    Vec_PtrFree( p->vClasses );
    Vec_PtrFree( p->vSingles );
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
    int Diff = -memcmp( pIso1, pIso2, sizeof(int) * ISO_NUM_INTS );
    if ( Diff )
        return Diff;
    return -Vec_IntCompareVec( pIso1->vAllies, pIso2->vAllies );
}

/**Function*************************************************************

  Synopsis    [Compares two objects by their ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Iso_ObjCompareByData( Aig_Obj_t ** pp1, Aig_Obj_t ** pp2 )
{
    Aig_Obj_t * pIso1 = *pp1;
    Aig_Obj_t * pIso2 = *pp2;
    assert( Aig_ObjIsPi(pIso1) || Aig_ObjIsPo(pIso1) );
    assert( Aig_ObjIsPi(pIso2) || Aig_ObjIsPo(pIso2) );
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
    if ( pIso->vAllies )
    {
        pArray = (unsigned *)Vec_IntArray(pIso->vAllies);
        for ( i = 0; i < (unsigned)Vec_IntSize(pIso->vAllies); i++ )
            Value ^= BigPrimes[i&7] * pArray[i];
    }
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
void Iso_ManCollectClasses( Iso_Man_t * p )
{
    Iso_Obj_t * pIso;
    int i;
    Vec_PtrClear( p->vSingles );
    Vec_PtrClear( p->vClasses );
    for ( i = 0; i < p->nBins; i++ )
    {
//        int Counter = 0;
        for ( pIso = Iso_ManObj(p, p->pBins[i]); pIso; pIso = Iso_ManObj(p, pIso->iNext) )
        {
            assert( pIso->Id == 0 );
            if ( pIso->iClass )
                Vec_PtrPush( p->vClasses, pIso );
            else 
                Vec_PtrPush( p->vSingles, pIso );
//            Counter++;
        }
//        if ( Counter )
//        printf( "%d ", Counter );
    }
//    printf( "\n" );
    Vec_PtrSort( p->vSingles, (int (*)(void))Iso_ObjCompare );
    Vec_PtrSort( p->vClasses, (int (*)(void))Iso_ObjCompare );
    assert( Vec_PtrSize(p->vSingles) == p->nSingles );
    assert( Vec_PtrSize(p->vClasses) == p->nClasses );
    // assign IDs to singletons
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vSingles, pIso, i )
        if ( pIso->Id == 0 )
            pIso->Id = p->nObjIds++;
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
    int i;//, nNodes = 0, nEdges = 0;
    p = Iso_ManStart( pAig );
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( Aig_ObjIsNode(pObj) )
        {
            pIso = p->pObjs + Aig_ObjFaninId0(pObj);
            if ( Aig_ObjFaninC0(pObj) )
                pIso->nFoutNeg++;
            else
                pIso->nFoutPos++;
            pIso = p->pObjs + Aig_ObjFaninId1(pObj);
            if ( Aig_ObjFaninC1(pObj) )
                pIso->nFoutNeg++;
            else
                pIso->nFoutPos++;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            pIso = p->pObjs + Aig_ObjFaninId0(pObj);
            if ( Aig_ObjFaninC0(pObj) )
                pIso->nFoutNeg++;
            else
                pIso->nFoutPos++;
        }
    }
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( !Aig_ObjIsPi(pObj) && !Aig_ObjIsNode(pObj) )
            continue;
        pIso = p->pObjs + i;
        pIso->Level = pObj->Level;
        pIso->nFinNeg = Aig_ObjFaninC0(pObj) + Aig_ObjFaninC1(pObj);
        if ( Aig_ObjIsNode(pObj) )
        {
            if ( Aig_ObjIsMuxType(pObj) ) // uniqify MUX/XOR
                pIso->nFinNeg = 3;
            if ( Aig_ObjFaninC0(pObj) < Aig_ObjFaninC1(pObj) || (Aig_ObjFaninC0(pObj) == Aig_ObjFaninC1(pObj) && Aig_ObjFanin0(pObj)->Level < Aig_ObjFanin1(pObj)->Level) )
            {
                pIso->nFinLev0 = Aig_ObjFanin0(pObj)->Level;
                pIso->nFinLev1 = Aig_ObjFanin1(pObj)->Level;
            }
            else
            {
                pIso->nFinLev0 = Aig_ObjFanin1(pObj)->Level;
                pIso->nFinLev1 = Aig_ObjFanin0(pObj)->Level;
            }
//            Iso_ManObjCount( pAig, pObj, &nNodes, &nEdges );
//            pIso->nNodes = nNodes;
//            pIso->nEdges = nEdges;
        }
        else
        {  
            pIso->nFinLev0 = (int)(Aig_ObjPioNum(pObj) >= Aig_ManPiNum(pAig) - Aig_ManRegNum(pAig)); // uniqify flop
        }
        // add to the hash table
        Iso_ObjHashAdd( p, pIso );
    }
    Iso_ManCollectClasses( p );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManPrintClasses( Iso_Man_t * p, int fVerbose, int fVeryVerbose )
{
    int fOnlyCis = 0;
    Iso_Obj_t * pIso, * pTemp;
    int i;

    // count unique objects
    if ( fVerbose )
        printf( "Total objects =%7d.  Entries =%7d.  Classes =%7d.  Singles =%7d.\n", 
            p->nObjs, p->nEntries, p->nClasses, p->nSingles );

    if ( !fVeryVerbose )
        return;

    printf( "Non-trivial classes:\n" );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
    {
        if ( fOnlyCis && pIso->Level > 0 )
            continue;

        printf( "%5d : {", i );
        for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
        {
            if ( fOnlyCis )
                printf( " %d", Aig_ObjPioNum( Iso_AigObj(p, pTemp) ) );
            else
            {
                Aig_Obj_t * pObj = Iso_AigObj(p, pTemp);
                if ( Aig_ObjIsNode(pObj) )
                    printf( " %d{%s%d(%d),%s%d(%d)}", Iso_ObjId(p, pTemp), 
                        Aig_ObjFaninC0(pObj)? "-": "+", Aig_ObjFaninId0(pObj), Aig_ObjLevel(Aig_ObjFanin0(pObj)), 
                        Aig_ObjFaninC1(pObj)? "-": "+", Aig_ObjFaninId1(pObj), Aig_ObjLevel(Aig_ObjFanin1(pObj)) );
                else
                    printf( " %d", Iso_ObjId(p, pTemp) );
            }
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
static inline void Iso_ObjAddToAllies( Iso_Obj_t * pIso, int Id, int fCompl )
{
    assert( pIso->Id == 0 );
    if ( pIso->vAllies == NULL )
        pIso->vAllies = Vec_IntAlloc( 8 );
    Vec_IntPush( pIso->vAllies, fCompl ? -Id : Id );        
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
                Iso_ObjAddToAllies( pIso0, pIso->Id, Aig_ObjFaninC0(pObj) );
            if ( pIso1->Id == 0 )
                Iso_ObjAddToAllies( pIso1, pIso->Id, Aig_ObjFaninC1(pObj) );
        }
        else // non-unique - assign unique fanins to it
        {
            if ( pIso0->Id != 0 )
                Iso_ObjAddToAllies( pIso, pIso0->Id, Aig_ObjFaninC0(pObj) );
            if ( pIso1->Id != 0 )
                Iso_ObjAddToAllies( pIso, pIso1->Id, Aig_ObjFaninC1(pObj) );
        }
    }
    // consider flops
    Aig_ManForEachLiLoSeq( p->pAig, pObjLi, pObj, i )
    {
        if ( Aig_ObjFaninId0(pObjLi) == 0 ) // ignore constant!
            continue;
        pIso  = Iso_ManObj( p, Aig_ObjId(pObj) );
        pIso0 = Iso_ManObj( p, Aig_ObjFaninId0(pObjLi) );
        if ( pIso->Id ) // unique - add to non-unique fanins
        {
            if ( pIso0->Id == 0 )
                Iso_ObjAddToAllies( pIso0, pIso->Id, Aig_ObjFaninC0(pObjLi) );
        }
        else // non-unique - assign unique fanins to it
        {
            if ( pIso0->Id != 0 )
                Iso_ObjAddToAllies( pIso, pIso0->Id, Aig_ObjFaninC0(pObjLi) );
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
    Vec_PtrClear( p->vTemp1 );
    Vec_PtrClear( p->vTemp2 );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
    {
        for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
            if ( pTemp->Id == 0 )
                Vec_PtrPush( p->vTemp1, pTemp );
            else
                Vec_PtrPush( p->vTemp2, pTemp );
    }
    // clean and add nodes
    p->nClasses = 0;       // total number of classes
    p->nEntries = 0;       // total number of entries
    p->nSingles = 0;       // total number of singletons
    memset( p->pBins, 0, sizeof(int) * p->nBins );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vTemp1, pTemp, i )
    {
        assert( pTemp->Id == 0 );
        pTemp->iClass = pTemp->iNext = 0;
        Iso_ObjHashAdd( p, pTemp );
    }
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vTemp2, pTemp, i )
    {
        assert( pTemp->Id != 0 );
        pTemp->iClass = pTemp->iNext = 0;
    }
    // collect new classes
    Iso_ManCollectClasses( p );
}

/**Function*************************************************************

  Synopsis    [Find nodes with the min number of edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Iso_Obj_t * Iso_ManFindBestObj( Iso_Man_t * p, Iso_Obj_t * pIso )
{
    Iso_Obj_t * pTemp, * pBest = NULL;
    int nNodesBest = -1, nNodes;
    int nEdgesBest = -1, nEdges;
    assert( pIso->Id == 0 );
    if ( pIso->Level == 0 )
        return pIso;
    for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
    {
        assert( pTemp->Id == 0 );
        Iso_ManObjCount( p->pAig, Iso_AigObj(p, pTemp), &nNodes, &nEdges );
//        printf( "%d,%d ", nNodes, nEdges );
        if ( nNodesBest < nNodes || (nNodesBest == nNodes && nEdgesBest < nEdges) )
        {
            nNodesBest = nNodes;
            nEdgesBest = nEdges;
            pBest = pTemp;
        }
    }
//    printf( "\n" );
    return pBest;
}

/**Function*************************************************************

  Synopsis    [Find nodes with the min number of edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManBreakTies( Iso_Man_t * p, int fVerbose )
{
    int fUseOneBest = 0;
    Iso_Obj_t * pIso, * pTemp;
    int i, LevelStart = 0;
    pIso = (Iso_Obj_t *)Vec_PtrEntry( p->vClasses, 0 );
    LevelStart = pIso->Level;
    if ( fVerbose )
        printf( "Best level %d\n", LevelStart ); 
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
    {
        if ( (int)pIso->Level < LevelStart )
            break;
        if ( !fUseOneBest )
        {
            for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
            {
                assert( pTemp->Id ==  0 );
                pTemp->Id = p->nObjIds++;
            }
            continue;
        }
        if ( pIso->Level == 0 && pIso->nFoutPos + pIso->nFoutNeg == 0 )
        {
            for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
                pTemp->Id = p->nObjIds++;
            continue;
        }
        pIso = Iso_ManFindBestObj( p, pIso );
        pIso->Id = p->nObjIds++;
    }
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
    Aig_Obj_t * pObj;
    int i;
    assert( p->nClasses == 0 );
    assert( Vec_PtrSize(p->vClasses) == 0 );
    // set canonical numbers
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( !Aig_ObjIsPi(pObj) && !Aig_ObjIsNode(pObj) )
        {
            pObj->iData = -1;
            continue;
        }
        pObj->iData = Iso_ManObj(p, Aig_ObjId(pObj))->Id;
        assert( pObj->iData > 0 );
    }
    Aig_ManConst1(p->pAig)->iData = 0;
    // assign unique IDs to the CIs
    Vec_PtrClear( p->vTemp1 );
    Vec_PtrClear( p->vTemp2 );
    Aig_ManForEachPi( p->pAig, pObj, i )
    {
        assert( pObj->iData > 0 );
        if ( Aig_ObjPioNum(pObj) >= Aig_ManPiNum(p->pAig) - Aig_ManRegNum(p->pAig) ) // flop
            Vec_PtrPush( p->vTemp2, pObj );
        else // PI
            Vec_PtrPush( p->vTemp1, pObj );
    }
    // sort CIs by their IDs
    Vec_PtrSort( p->vTemp1, (int (*)(void))Iso_ObjCompareByData );
    Vec_PtrSort( p->vTemp2, (int (*)(void))Iso_ObjCompareByData );
    // create the result
    vRes = Vec_IntAlloc( Aig_ManPiNum(p->pAig) );
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vTemp1, pObj, i )
        Vec_IntPush( vRes, Aig_ObjPioNum(pObj) );
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vTemp2, pObj, i )
        Vec_IntPush( vRes, Aig_ObjPioNum(pObj) );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Find nodes with the min number of edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManDumpOneClass( Iso_Man_t * p )
{
    Vec_Ptr_t * vNodes = Vec_PtrAlloc( 100 );
    Iso_Obj_t * pIso, * pTemp;
    Aig_Man_t * pNew = NULL;
    assert( p->nClasses > 0 );
    pIso = (Iso_Obj_t *)Vec_PtrEntry( p->vClasses, 0 );
    assert( pIso->Id == 0 );
    for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
    {
        assert( pTemp->Id == 0 );
        Vec_PtrPush( vNodes, Iso_AigObj(p, pTemp) );
    }
    pNew = Aig_ManDupNodes( p->pAig, vNodes );
    Vec_PtrFree( vNodes );
    Aig_ManShow( pNew, 0, NULL ); 
    Aig_ManStopP( &pNew );
}

/**Function*************************************************************

  Synopsis    [Finds canonical permutation of CIs and assigns unique IDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManFindIsoPerm( Aig_Man_t * pAig, int fVerbose )
{
    Vec_Int_t * vRes;
    Iso_Man_t * p;
    int clk, clk2 = clock();
    p = Iso_ManCreate( pAig );
    Iso_ManPrintClasses( p, fVerbose, 0 );
    while ( p->nClasses )
    {
        // assign adjacency to classes
        clk = clock();
        Iso_ManAssignAdjacency( p );
        p->timeFout += clock() - clk;
        // rehash the class nodes
        clk = clock();
        Iso_ManRehashClassNodes( p );
        p->timeHash += clock() - clk;
        Iso_ManPrintClasses( p, fVerbose, 0 );
        // force refinement
        while ( p->nSingles == 0 && p->nClasses )
        {
            // assign IDs to the topmost level of classes
            Iso_ManBreakTies( p, fVerbose );
            // assign adjacency to classes
            clk = clock();
            Iso_ManAssignAdjacency( p );
            p->timeFout += clock() - clk;
            // rehash the class nodes
            clk = clock();
            Iso_ManRehashClassNodes( p );
            p->timeHash += clock() - clk;
            Iso_ManPrintClasses( p, fVerbose, 0 );
        }
    }
    p->timeTotal = clock() - clk2;
//    printf( "IDs assigned = %d.  Objects = %d.\n", p->nObjIds, 1+Aig_ManPiNum(p->pAig)+Aig_ManNodeNum(p->pAig) );
    assert( p->nObjIds == 1+Aig_ManPiNum(p->pAig)+Aig_ManNodeNum(p->pAig) );
//    if ( p->nClasses )
//        Iso_ManDumpOneClass( p );
    vRes = Iso_ManFinalize( p );
    Iso_ManStop( p, fVerbose );
    return vRes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

