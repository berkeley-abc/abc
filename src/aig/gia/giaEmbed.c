/**CFile****************************************************************

  FileName    [giaLogic.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Logic network derived from AIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaLogic.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <math.h>
#include "gia.h"

/* 
    The code is based on the paper by D. Harel and Y. Koren, 
    "Graph drawing by high-dimensional embedding", 
    J. Graph Algs & Apps, Vol 8(2), pp. 195-217 (2004)
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Emb_Obj_t_ Emb_Obj_t;
struct Emb_Obj_t_
{
    unsigned       fCi      :  1;    // terminal node CI
    unsigned       fCo      :  1;    // terminal node CO
    unsigned       fMark0   :  1;    // first user-controlled mark
    unsigned       fMark1   :  1;    // second user-controlled mark
    unsigned       nFanins  : 28;    // the number of fanins
    unsigned       nFanouts;         // the number of fanouts
    int            hHandle;          // the handle of the node
    union {
    unsigned       TravId;           // user-specified value
    unsigned       iFanin; 
    };
    union {
    unsigned       Value;            // user-specified value
    unsigned       iFanout; 
    };
    int            Fanios[0];        // the array of fanins/fanouts
};

typedef struct Emb_Man_t_ Emb_Man_t;
struct Emb_Man_t_
{
    Gia_Man_t *    pGia;             // the original AIG manager
    Vec_Int_t *    vCis;             // the vector of CIs (PIs + LOs)
    Vec_Int_t *    vCos;             // the vector of COs (POs + LIs)
    int            nObjs;            // the number of objects
    int            nRegs;            // the number of registers
    int            nTravIds;         // traversal ID of the network
    int *          pObjData;         // the array containing data for objects
    int            nObjData;         // the size of array to store the logic network
    unsigned char* pVecs;            // array of vectors of size nObjs * nDims
    int            nReached;         // the number of nodes reachable from the pivot
    int            nDistMax;         // the maximum distance from the node
    float **       pMatr;            // covariance matrix nDims * nDims
    float **       pEigen;           // the first several eigen values of the matrix
    float *        pSols;            // solutions to the problem nObjs * nSols;
};

static inline int         Emb_ManRegNum( Emb_Man_t * p )                              { return p->nRegs;                                    }
static inline int         Emb_ManCiNum( Emb_Man_t * p )                               { return Vec_IntSize(p->vCis);                        }
static inline int         Emb_ManCoNum( Emb_Man_t * p )                               { return Vec_IntSize(p->vCos);                        }
static inline int         Emb_ManPiNum( Emb_Man_t * p )                               { return Vec_IntSize(p->vCis) - p->nRegs;             }
static inline int         Emb_ManPoNum( Emb_Man_t * p )                               { return Vec_IntSize(p->vCos) - p->nRegs;             }
static inline int         Emb_ManObjNum( Emb_Man_t * p )                              { return p->nObjs;                                    } 
static inline int         Emb_ManNodeNum( Emb_Man_t * p )                             { return p->nObjs - Vec_IntSize(p->vCis) - Vec_IntSize(p->vCos); } 

static inline Emb_Obj_t * Emb_ManObj( Emb_Man_t * p, unsigned hHandle )               { return (Emb_Obj_t *)(p->pObjData + hHandle);        } 
static inline Emb_Obj_t * Emb_ManCi( Emb_Man_t * p, int i )                           { return Emb_ManObj( p, Vec_IntEntry(p->vCis,i) );    }
static inline Emb_Obj_t * Emb_ManCo( Emb_Man_t * p, int i )                           { return Emb_ManObj( p, Vec_IntEntry(p->vCos,i) );    }

static inline int         Emb_ObjIsTerm( Emb_Obj_t * pObj )                           { return pObj->fCi || pObj->fCo;                      } 
static inline int         Emb_ObjIsCi( Emb_Obj_t * pObj )                             { return pObj->fCi;                                   } 
static inline int         Emb_ObjIsCo( Emb_Obj_t * pObj )                             { return pObj->fCo;                                   } 
static inline int         Emb_ObjIsPi( Emb_Obj_t * pObj )                             { return pObj->fCi && pObj->nFanins == 0;             } 
static inline int         Emb_ObjIsPo( Emb_Obj_t * pObj )                             { return pObj->fCo && pObj->nFanouts == 0;            } 
static inline int         Emb_ObjIsNode( Emb_Obj_t * pObj )                           { return!Emb_ObjIsTerm(pObj) && pObj->nFanins > 0;    } 
static inline int         Emb_ObjIsConst0( Emb_Obj_t * pObj )                         { return!Emb_ObjIsTerm(pObj) && pObj->nFanins == 0;   } 

static inline int         Emb_ObjSize( Emb_Obj_t * pObj )                             { return sizeof(Emb_Obj_t) / 4 + pObj->nFanins + pObj->nFanouts;  } 
static inline int         Emb_ObjFaninNum( Emb_Obj_t * pObj )                         { return pObj->nFanins;                               } 
static inline int         Emb_ObjFanoutNum( Emb_Obj_t * pObj )                        { return pObj->nFanouts;                              } 
static inline Emb_Obj_t * Emb_ObjFanin( Emb_Obj_t * pObj, int i )                     { return (Emb_Obj_t *)(((int *)pObj) - pObj->Fanios[i]);               } 
static inline Emb_Obj_t * Emb_ObjFanout( Emb_Obj_t * pObj, int i )                    { return (Emb_Obj_t *)(((int *)pObj) + pObj->Fanios[pObj->nFanins+i]); } 

static inline void        Emb_ManResetTravId( Emb_Man_t * p )                         { extern void Emb_ManCleanTravId( Emb_Man_t * p ); Emb_ManCleanTravId( p ); p->nTravIds = 1;  }
static inline void        Emb_ManIncrementTravId( Emb_Man_t * p )                     { p->nTravIds++;                                      }
static inline void        Emb_ObjSetTravId( Emb_Obj_t * pObj, int TravId )            { pObj->TravId = TravId;                              }
static inline void        Emb_ObjSetTravIdCurrent( Emb_Man_t * p, Emb_Obj_t * pObj )  { pObj->TravId = p->nTravIds;                         }
static inline void        Emb_ObjSetTravIdPrevious( Emb_Man_t * p, Emb_Obj_t * pObj ) { pObj->TravId = p->nTravIds - 1;                     }
static inline int         Emb_ObjIsTravIdCurrent( Emb_Man_t * p, Emb_Obj_t * pObj )   { return ((int)pObj->TravId == p->nTravIds);          }
static inline int         Emb_ObjIsTravIdPrevious( Emb_Man_t * p, Emb_Obj_t * pObj )  { return ((int)pObj->TravId == p->nTravIds - 1);      }

static inline unsigned char * Emb_ManVec( Emb_Man_t * p, int v )                      { return p->pVecs + v * p->nObjs;                     }
static inline float *         Emb_ManSol( Emb_Man_t * p, int v )                      { return p->pSols + v * p->nObjs;                     }

#define Emb_ManForEachObj( p, pObj, i )               \
    for ( i = 0; (i < p->nObjData) && (pObj = Emb_ManObj(p,i)); i += Emb_ObjSize(pObj) )
#define Emb_ManForEachNode( p, pObj, i )              \
    for ( i = 0; (i < p->nObjData) && (pObj = Emb_ManObj(p,i)); i += Emb_ObjSize(pObj) ) if ( Emb_ObjIsTerm(pObj) ) {} else
#define Emb_ManForEachObjVec( vVec, p, pObj, i )                        \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pObj) = Emb_ManObj(p, Vec_IntEntry(vVec,i))); i++ )
#define Emb_ObjForEachFanin( pObj, pNext, i )         \
    for ( i = 0; (i < (int)pObj->nFanins) && (pNext = Emb_ObjFanin(pObj,i)); i++ )
#define Emb_ObjForEachFanout( pObj, pNext, i )        \
    for ( i = 0; (i < (int)pObj->nFanouts) && (pNext = Emb_ObjFanout(pObj,i)); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect the fanin IDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManCollectSuper_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSuper, Vec_Int_t * vVisit )  
{
    if ( pObj->fMark1 )
        return;
    pObj->fMark1 = 1;
    Vec_IntPush( vVisit, Gia_ObjId(p, pObj) );
    if ( pObj->fMark0 )
    {
        Vec_IntPush( vSuper, Gia_ObjId(p, pObj) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Emb_ManCollectSuper_rec( p, Gia_ObjFanin0(pObj), vSuper, vVisit );
    Emb_ManCollectSuper_rec( p, Gia_ObjFanin1(pObj), vSuper, vVisit );
    
}

/**Function*************************************************************

  Synopsis    [Collect the fanin IDs.]

  Description []
               
  SideEffects []

  SeeAlso     [] 

***********************************************************************/
void Emb_ManCollectSuper( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSuper, Vec_Int_t * vVisit )  
{
    int Entry, i;
    Vec_IntClear( vSuper );
    Vec_IntClear( vVisit );
    assert( pObj->fMark0 == 1 );
    pObj->fMark0 = 0;
    Emb_ManCollectSuper_rec( p, pObj, vSuper, vVisit );
    pObj->fMark0 = 1;
    Vec_IntForEachEntry( vVisit, Entry, i )
        Gia_ManObj(p, Entry)->fMark1 = 0;
}

/**Function*************************************************************

  Synopsis    [Assigns references while removing the MUX/XOR ones.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManCreateRefsSpecial( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj, * pFan0, * pFan1;
    Gia_Obj_t * pObjC, * pObjD0, * pObjD1;
    int i;
    assert( p->pRefs == NULL );
    Gia_ManCleanMark0( p );
    Gia_ManCreateRefs( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        assert( pObj->fMark0 == 0 );
        pFan0 = Gia_ObjFanin0(pObj);
        pFan1 = Gia_ObjFanin1(pObj);
        // skip nodes whose fanins are PIs or are already marked
        if ( Gia_ObjIsCi(pFan0) || pFan0->fMark0 || 
             Gia_ObjIsCi(pFan1) || pFan1->fMark0 )
             continue;
        // skip nodes that are not MUX type
        if ( !Gia_ObjIsMuxType(pObj) )
            continue;
        // the node is MUX type, mark it and its fanins
        pObj->fMark0  = 1;
        pFan0->fMark0 = 1;
        pFan1->fMark0 = 1;
        // deref the control 
        pObjC = Gia_ObjRecognizeMux( pObj, &pObjD1, &pObjD0 );
        Gia_ObjRefDec( p, Gia_Regular(pObjC) );
        if ( Gia_Regular(pObjD0) == Gia_Regular(pObjD1) )
            Gia_ObjRefDec( p, Gia_Regular(pObjD0) );
    }
    Gia_ManForEachAnd( p, pObj, i )
        assert( Gia_ObjRefs(p, pObj) > 0 );
    Gia_ManCleanMark0( p );
}

/**Function*************************************************************

  Synopsis    [Assigns references while removing the MUX/XOR ones.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManTransformRefs( Gia_Man_t * p, int * pnObjs, int * pnFanios )  
{
    Vec_Int_t * vSuper, * vVisit;
    Gia_Obj_t * pObj, * pFanin;
    int i, k, Counter;
    assert( p->pRefs != NULL );

    // mark nodes to be used in the logic network
    Gia_ManCleanMark0( p );
    Gia_ManConst0(p)->fMark0 = 1;
    // mark the inputs
    Gia_ManForEachCi( p, pObj, i )
        pObj->fMark0 = 1;
    // mark those nodes that have ref count more than 1
    Gia_ManForEachAnd( p, pObj, i )
        pObj->fMark0 = (Gia_ObjRefs(p, pObj) > 1);
    // mark the output drivers
    Gia_ManForEachCoDriver( p, pObj, i )
        pObj->fMark0 = 1;

    // count the number of nodes
    Counter = 0;
    Gia_ManForEachObj( p, pObj, i )
        Counter += pObj->fMark0;
    *pnObjs = Counter + Gia_ManCoNum(p);

    // reset the references
    ABC_FREE( p->pRefs );
    p->pRefs = ABC_CALLOC( int, Gia_ManObjNum(p) );
    // reference from internal nodes
    Counter = 0;
    vSuper = Vec_IntAlloc( 100 );
    vVisit = Vec_IntAlloc( 100 );
    Gia_ManCleanMark1( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( pObj->fMark0 == 0 )
            continue;
        Emb_ManCollectSuper( p, pObj, vSuper, vVisit );
        Gia_ManForEachObjVec( vSuper, p, pFanin, k )
        {
            assert( pFanin->fMark0 );
            Gia_ObjRefInc( p, pFanin );
        }
        Counter += Vec_IntSize( vSuper );
    }
    Gia_ManCheckMark1( p );
    Vec_IntFree( vSuper );
    Vec_IntFree( vVisit );
    // reference from outputs
    Gia_ManForEachCoDriver( p, pObj, i )
    {
        assert( pObj->fMark0 );
        Gia_ObjRefInc( p, pObj );
    }
    *pnFanios = Counter + Gia_ManCoNum(p);
}

/**Function*************************************************************

  Synopsis    [Cleans the value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManCleanTravId( Emb_Man_t * p )  
{
    Emb_Obj_t * pObj;
    int i;
    Emb_ManForEachObj( p, pObj, i )
        pObj->TravId = 0;
}

/**Function*************************************************************

  Synopsis    [Cleans the value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManSetValue( Emb_Man_t * p )  
{
    Emb_Obj_t * pObj;
    int i, Counter = 0;
    Emb_ManForEachObj( p, pObj, i )
    {
        pObj->Value = Counter++;
//        if ( pObj->fCi && pObj->nFanins == 0 ) 
//            printf( "CI:  Handle = %8d.  Value = %6d. Fanins = %d.\n", pObj->hHandle, pObj->Value, pObj->nFanins );
    }
}

/**Function*************************************************************

  Synopsis    [Creates fanin/fanout pair.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ObjAddFanin( Emb_Obj_t * pObj, Emb_Obj_t * pFanin )
{ 
    assert( pObj->iFanin < pObj->nFanins );
    assert( pFanin->iFanout < pFanin->nFanouts );
    pFanin->Fanios[pFanin->nFanins + pFanin->iFanout++] = 
    pObj->Fanios[pObj->iFanin++] = pObj->hHandle - pFanin->hHandle;
}

/**Function*************************************************************

  Synopsis    [Creates logic network isomorphic to the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Emb_Man_t * Emb_ManStart( Gia_Man_t * pGia )
{
    Emb_Man_t * p;
    Emb_Obj_t * pObjLog, * pFanLog;
    Gia_Obj_t * pObj, * pObjRi, * pObjRo, * pFanin;
    Vec_Int_t * vSuper, * vVisit;
    int nObjs, nFanios, nNodes = 0;
    int i, k, hHandle = 0;
    // prepare the AIG
//    Gia_ManCreateRefs( pGia );
    Emb_ManCreateRefsSpecial( pGia );
    Emb_ManTransformRefs( pGia, &nObjs, &nFanios );
    Gia_ManFillValue( pGia );
    // create logic network
    p = ABC_CALLOC( Emb_Man_t, 1 );
    p->pGia  = pGia;
    p->nRegs = Gia_ManRegNum(pGia);
    p->vCis  = Vec_IntAlloc( Gia_ManCiNum(pGia) );
    p->vCos  = Vec_IntAlloc( Gia_ManCoNum(pGia) );
    p->nObjData = (sizeof(Emb_Obj_t) / 4) * nObjs + 2 * (nFanios + Gia_ManRegNum(pGia));
    p->pObjData = ABC_CALLOC( int, p->nObjData );
    // create constant node
    Gia_ManConst0(pGia)->Value = hHandle;
    pObjLog = Emb_ManObj( p, hHandle );
    pObjLog->hHandle  = hHandle;
    pObjLog->nFanins  = 0;
    pObjLog->nFanouts = Gia_ObjRefs( pGia, Gia_ManConst0(pGia) );
    // count objects
    hHandle += Emb_ObjSize( pObjLog );
    nNodes++;
    p->nObjs++;
    // create the PIs
    Gia_ManForEachCi( pGia, pObj, i )
    {
        // create PI object
        pObj->Value = hHandle;
        Vec_IntPush( p->vCis, hHandle );
        pObjLog = Emb_ManObj( p, hHandle );
        pObjLog->hHandle  = hHandle;
        pObjLog->nFanins  = Gia_ObjIsRo( pGia, pObj );
        pObjLog->nFanouts = Gia_ObjRefs( pGia, pObj );
        pObjLog->fCi = 1;
        // count objects
        hHandle += Emb_ObjSize( pObjLog );
        p->nObjs++;
    }
    // create internal nodes
    vSuper = Vec_IntAlloc( 100 );
    vVisit = Vec_IntAlloc( 100 );
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( pObj->fMark0 == 0 )
        {
            assert( Gia_ObjRefs( pGia, pObj ) == 0 );
            continue;
        }
        assert( Gia_ObjRefs( pGia, pObj ) > 0 );
        Emb_ManCollectSuper( pGia, pObj, vSuper, vVisit );
        // create node object
        pObj->Value = hHandle;
        pObjLog = Emb_ManObj( p, hHandle );
        pObjLog->hHandle  = hHandle;
        pObjLog->nFanins  = Vec_IntSize( vSuper );
        pObjLog->nFanouts = Gia_ObjRefs( pGia, pObj );
        // add fanins
        Gia_ManForEachObjVec( vSuper, pGia, pFanin, k )
        {
            pFanLog = Emb_ManObj( p, Gia_ObjValue(pFanin) ); 
            Emb_ObjAddFanin( pObjLog, pFanLog );
        }
        // count objects
        hHandle += Emb_ObjSize( pObjLog );
        nNodes++;
        p->nObjs++;
    }
    Vec_IntFree( vSuper );
    Vec_IntFree( vVisit );
    // create the POs
    Gia_ManForEachCo( pGia, pObj, i )
    {
        // create PO object
        pObj->Value = hHandle;
        Vec_IntPush( p->vCos, hHandle );
        pObjLog = Emb_ManObj( p, hHandle );
        pObjLog->hHandle  = hHandle;
        pObjLog->nFanins  = 1;
        pObjLog->nFanouts = Gia_ObjIsRi( pGia, pObj );
        pObjLog->fCo = 1;
        // add fanins
        pFanLog = Emb_ManObj( p, Gia_ObjValue(Gia_ObjFanin0(pObj)) );
        Emb_ObjAddFanin( pObjLog, pFanLog );
        // count objects
        hHandle += Emb_ObjSize( pObjLog );
        p->nObjs++;
    }
    // connect registers
    Gia_ManForEachRiRo( pGia, pObjRi, pObjRo, i )
        Emb_ObjAddFanin( Emb_ManObj(p,Gia_ObjValue(pObjRo)), Emb_ManObj(p,Gia_ObjValue(pObjRi)) );
    Gia_ManCleanMark0( pGia );
    assert( nNodes  == Emb_ManNodeNum(p) );
    assert( nObjs   == p->nObjs );
    assert( hHandle == p->nObjData );
    if ( hHandle != p->nObjData )
        printf( "Emb_ManStart(): Fatal error in internal representation.\n" );
    // make sure the fanin/fanout counters are correct
    Gia_ManForEachObj( pGia, pObj, i )
    {
        if ( !~Gia_ObjValue(pObj) )
            continue;
        pObjLog = Emb_ManObj( p, Gia_ObjValue(pObj) );
        assert( pObjLog->nFanins  == pObjLog->iFanin );
        assert( pObjLog->nFanouts == pObjLog->iFanout );
        pObjLog->iFanin = pObjLog->iFanout = 0;
    }
    ABC_FREE( pGia->pRefs );
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates logic network isomorphic to the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManPrintStats( Emb_Man_t * p )
{
//    if ( p->pName )
//        printf( "%8s : ", p->pName );
    printf( "i/o =%7d/%7d  ", Emb_ManPiNum(p), Emb_ManPoNum(p) );
    if ( Emb_ManRegNum(p) )
        printf( "ff =%7d  ", Emb_ManRegNum(p) );
    printf( "node =%8d  ", Emb_ManNodeNum(p) );
    printf( "obj =%8d  ", Emb_ManObjNum(p) );
//    printf( "lev =%5d  ", Emb_ManLevelNum(p) );
//    printf( "cut =%5d  ", Emb_ManCrossCut(p) );
    printf( "mem =%5.2f Mb", 4.0*p->nObjData/(1<<20) );
//    printf( "obj =%5d  ", Emb_ManObjNum(p) );
    printf( "\n" );

//    Emb_ManSatExperiment( p );
}

/**Function*************************************************************

  Synopsis    [Creates logic network isomorphic to the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManStop( Emb_Man_t * p )
{
    Vec_IntFree( p->vCis );
    Vec_IntFree( p->vCos );
    ABC_FREE( p->pVecs );
    ABC_FREE( p->pSols );
    ABC_FREE( p->pMatr );
    ABC_FREE( p->pEigen );
    ABC_FREE( p->pObjData );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Prints the distribution of fanins/fanouts in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManPrintFanio( Emb_Man_t * p )
{
    char Buffer[100];
    Emb_Obj_t * pNode;
    Vec_Int_t * vFanins, * vFanouts;
    int nFanins, nFanouts, nFaninsMax, nFanoutsMax, nFaninsAll, nFanoutsAll;
    int i, k, nSizeMax;

    // determine the largest fanin and fanout
    nFaninsMax = nFanoutsMax = 0;
    nFaninsAll = nFanoutsAll = 0;
    Emb_ManForEachNode( p, pNode, i )
    {
        if ( i == 0 ) continue; // skip const 0 obj
        nFanins  = Emb_ObjFaninNum(pNode);
        nFanouts = Emb_ObjFanoutNum(pNode);
        nFaninsAll  += nFanins;
        nFanoutsAll += nFanouts;
        nFaninsMax   = ABC_MAX( nFaninsMax, nFanins );
        nFanoutsMax  = ABC_MAX( nFanoutsMax, nFanouts );
    }

    // allocate storage for fanin/fanout numbers
    nSizeMax = AIG_MAX( 10 * (Aig_Base10Log(nFaninsMax) + 1), 10 * (Aig_Base10Log(nFanoutsMax) + 1) );
    vFanins  = Vec_IntStart( nSizeMax );
    vFanouts = Vec_IntStart( nSizeMax );

    // count the number of fanins and fanouts
    Emb_ManForEachNode( p, pNode, i )
    {
        if ( i == 0 ) continue; // skip const 0 obj
        nFanins  = Emb_ObjFaninNum(pNode);
        nFanouts = Emb_ObjFanoutNum(pNode);

        if ( nFanins < 10 )
            Vec_IntAddToEntry( vFanins, nFanins, 1 );
        else if ( nFanins < 100 )
            Vec_IntAddToEntry( vFanins, 10 + nFanins/10, 1 );
        else if ( nFanins < 1000 )
            Vec_IntAddToEntry( vFanins, 20 + nFanins/100, 1 );
        else if ( nFanins < 10000 )
            Vec_IntAddToEntry( vFanins, 30 + nFanins/1000, 1 );
        else if ( nFanins < 100000 )
            Vec_IntAddToEntry( vFanins, 40 + nFanins/10000, 1 );
        else if ( nFanins < 1000000 )
            Vec_IntAddToEntry( vFanins, 50 + nFanins/100000, 1 );
        else if ( nFanins < 10000000 )
            Vec_IntAddToEntry( vFanins, 60 + nFanins/1000000, 1 );

        if ( nFanouts < 10 )
            Vec_IntAddToEntry( vFanouts, nFanouts, 1 );
        else if ( nFanouts < 100 )
            Vec_IntAddToEntry( vFanouts, 10 + nFanouts/10, 1 );
        else if ( nFanouts < 1000 )
            Vec_IntAddToEntry( vFanouts, 20 + nFanouts/100, 1 );
        else if ( nFanouts < 10000 )
            Vec_IntAddToEntry( vFanouts, 30 + nFanouts/1000, 1 );
        else if ( nFanouts < 100000 )
            Vec_IntAddToEntry( vFanouts, 40 + nFanouts/10000, 1 );
        else if ( nFanouts < 1000000 )
            Vec_IntAddToEntry( vFanouts, 50 + nFanouts/100000, 1 );
        else if ( nFanouts < 10000000 )
            Vec_IntAddToEntry( vFanouts, 60 + nFanouts/1000000, 1 );
    }

    printf( "The distribution of fanins and fanouts in the network:\n" );
    printf( "         Number   Nodes with fanin  Nodes with fanout\n" );
    for ( k = 0; k < nSizeMax; k++ )
    {
        if ( vFanins->pArray[k] == 0 && vFanouts->pArray[k] == 0 )
            continue;
        if ( k < 10 )
            printf( "%15d : ", k );
        else
        {
            sprintf( Buffer, "%d - %d", (int)pow(10, k/10) * (k%10), (int)pow(10, k/10) * (k%10+1) - 1 ); 
            printf( "%15s : ", Buffer );
        }
        if ( vFanins->pArray[k] == 0 )
            printf( "              " );
        else
            printf( "%12d  ", vFanins->pArray[k] );
        printf( "    " );
        if ( vFanouts->pArray[k] == 0 )
            printf( "              " );
        else
            printf( "%12d  ", vFanouts->pArray[k] );
        printf( "\n" );
    }
    Vec_IntFree( vFanins );
    Vec_IntFree( vFanouts );

    printf( "Fanins: Max = %d. Ave = %.2f.  Fanouts: Max = %d. Ave =  %.2f.\n", 
        nFaninsMax,  1.0*nFaninsAll/Emb_ManNodeNum(p), 
        nFanoutsMax, 1.0*nFanoutsAll/Emb_ManNodeNum(p)  );
}

/**Function*************************************************************

  Synopsis    [Computes the distance from the given object]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Emb_ManComputeDistance_old( Emb_Man_t * p, Emb_Obj_t * pPivot )
{
    Vec_Int_t * vThis, * vNext, * vTemp;
    Emb_Obj_t * pThis, * pNext;
    int i, k, d, nVisited = 0;
//    assert( Emb_ObjIsTerm(pPivot) );
    vThis = Vec_IntAlloc( 1000 );
    vNext = Vec_IntAlloc( 1000 );
    Emb_ManIncrementTravId( p );
    Emb_ObjSetTravIdCurrent( p, pPivot );
    Vec_IntPush( vThis, pPivot->hHandle );
    for ( d = 0; Vec_IntSize(vThis) > 0; d++ )
    {
        nVisited += Vec_IntSize(vThis);
        Vec_IntClear( vNext );
        Emb_ManForEachObjVec( vThis, p, pThis, i )
        {
            Emb_ObjForEachFanin( pThis, pNext, k )
            {
                if ( Emb_ObjIsTravIdCurrent(p, pNext) )
                    continue;
                Emb_ObjSetTravIdCurrent(p, pNext);
                Vec_IntPush( vNext, pNext->hHandle );
                nVisited += !Emb_ObjIsTerm(pNext);
            }
            Emb_ObjForEachFanout( pThis, pNext, k )
            {
                if ( Emb_ObjIsTravIdCurrent(p, pNext) )
                    continue;
                Emb_ObjSetTravIdCurrent(p, pNext);
                Vec_IntPush( vNext, pNext->hHandle );
                nVisited += !Emb_ObjIsTerm(pNext);
            }
        }
        vTemp = vThis; vThis = vNext; vNext = vTemp;
    }
    Vec_IntFree( vThis );
    Vec_IntFree( vNext );
    // check if there are several strongly connected components
//    if ( nVisited < Emb_ManNodeNum(p) )
//        printf( "Visited less nodes (%d) than present (%d).\n", nVisited, Emb_ManNodeNum(p) );
    return d;
}

/**Function*************************************************************

  Synopsis    [Traverses from the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void Gia_ManTestDistanceInternal( Emb_Man_t * p )
{
    int nAttempts = 20;
    int i, iNode, Dist, clk;
    Emb_Obj_t * pPivot, * pNext;
    Aig_ManRandom( 1 );
    Emb_ManResetTravId( p );
    // compute distances from several randomly selected PIs
    clk = clock();
    printf( "From inputs: " );
    for ( i = 0; i < nAttempts; i++ )
    {
        iNode = Aig_ManRandom( 0 ) % Emb_ManCiNum(p);
        pPivot = Emb_ManCi( p, iNode );
        if ( Emb_ObjFanoutNum(pPivot) == 0 )
            { i--; continue; }
        pNext = Emb_ObjFanout( pPivot, 0 );
        if ( !Emb_ObjIsNode(pNext) )
            { i--; continue; }
        Dist = Emb_ManComputeDistance_old( p, pPivot );
        printf( "%d ", Dist );
    }
    ABC_PRT( "Time", clock() - clk );
    // compute distances from several randomly selected POs
    clk = clock();
    printf( "From outputs: " );
    for ( i = 0; i < nAttempts; i++ )
    {
        iNode = Aig_ManRandom( 0 ) % Emb_ManCoNum(p);
        pPivot = Emb_ManCo( p, iNode );
        pNext = Emb_ObjFanin( pPivot, 0 );
        if ( !Emb_ObjIsNode(pNext) )
            { i--; continue; }
        Dist = Emb_ManComputeDistance_old( p, pPivot );
        printf( "%d ", Dist );
    }
    ABC_PRT( "Time", clock() - clk );
    // compute distances from several randomly selected nodes
    clk = clock();
    printf( "From nodes: " );
    for ( i = 0; i < nAttempts; i++ )
    {
        iNode = Aig_ManRandom( 0 ) % Gia_ManObjNum(p->pGia);
        if ( !~Gia_ManObj(p->pGia, iNode)->Value )
            { i--; continue; }
        pPivot = Emb_ManObj( p, Gia_ManObj(p->pGia, iNode)->Value );
        if ( !Emb_ObjIsNode(pPivot) )
            { i--; continue; }
        Dist = Emb_ManComputeDistance_old( p, pPivot );
        printf( "%d ", Dist );
    }
    ABC_PRT( "Time", clock() - clk );
}

/**Function*************************************************************

  Synopsis    [Returns sorted array of node handles with largest fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManTestDistance( Gia_Man_t * pGia )
{
    Emb_Man_t * p;
    int clk = clock();
    p = Emb_ManStart( pGia );
//    Emb_ManPrintFanio( p );
    Emb_ManPrintStats( p );
ABC_PRT( "Time", clock() - clk );
    Gia_ManTestDistanceInternal( p );
    Emb_ManStop( p );
}




/**Function*************************************************************

  Synopsis    [Computes the distances from the given set of objects.]

  Description [Returns one of the most distant objects.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Emb_Obj_t * Emb_ManFindDistances( Emb_Man_t * p, Vec_Int_t * vStart, unsigned char * pDist )
{
    Vec_Int_t * vThis, * vNext, * vTemp;
    Emb_Obj_t * pThis, * pNext, * pResult;
    int i, k;
    p->nReached = p->nDistMax = 0;
    vThis = Vec_IntAlloc( 1000 );
    vNext = Vec_IntAlloc( 1000 );
    Emb_ManIncrementTravId( p );
    Emb_ManForEachObjVec( vStart, p, pThis, i )
    {
        Emb_ObjSetTravIdCurrent( p, pThis );
        Vec_IntPush( vThis, pThis->hHandle );
    }
    assert( Vec_IntSize(vThis) > 0 );
    for ( p->nDistMax = 0; Vec_IntSize(vThis) > 0; p->nDistMax++ )
    {
        p->nReached += Vec_IntSize(vThis);
        Vec_IntClear( vNext );
        Emb_ManForEachObjVec( vThis, p, pThis, i )
        {
            assert( p->nDistMax < 255 ); // current data-structure used unsigned char
            if ( p->nDistMax > 254 )
                p->nDistMax = 254;
            if ( pDist ) pDist[pThis->Value] = p->nDistMax;
            Emb_ObjForEachFanin( pThis, pNext, k )
            {
                if ( Emb_ObjIsTravIdCurrent(p, pNext) )
                    continue;
                Emb_ObjSetTravIdCurrent(p, pNext);
                Vec_IntPush( vNext, pNext->hHandle );
            }
            Emb_ObjForEachFanout( pThis, pNext, k )
            {
                if ( Emb_ObjIsTravIdCurrent(p, pNext) )
                    continue;
                Emb_ObjSetTravIdCurrent(p, pNext);
                Vec_IntPush( vNext, pNext->hHandle );
            }
        }
        vTemp = vThis; vThis = vNext; vNext = vTemp;
    }
    assert( Vec_IntSize(vNext) > 0 );
    pResult = Emb_ManObj( p, Vec_IntEntry(vNext, 0) );
    assert( pDist == NULL || pDist[pResult->Value] == p->nDistMax - 1 );
    Vec_IntFree( vThis );
    Vec_IntFree( vNext );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Traverses from the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Emb_Obj_t * Emb_ManRandomVertex( Emb_Man_t * p )
{
    Emb_Obj_t * pPivot;
    do {
        int iNode = Aig_ManRandom( 0 ) % Gia_ManObjNum(p->pGia);
        if ( ~Gia_ManObj(p->pGia, iNode)->Value )
            pPivot = Emb_ManObj( p, Gia_ManObj(p->pGia, iNode)->Value );
        else
            pPivot = NULL;
    }
    while ( pPivot == NULL || !Emb_ObjIsNode(pPivot) );
    return pPivot;
}

/**Function*************************************************************

  Synopsis    [Computes dimentions of the graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManComputeDimensions( Emb_Man_t * p, int nDims )
{
    Emb_Obj_t * pRandom, * pPivot;
    Vec_Int_t * vStart;
    int d, nReached;
    int i, Counter;
    assert( p->pVecs == NULL );
    p->pVecs = ABC_FALLOC( unsigned char, p->nObjs * nDims );
    vStart = Vec_IntAlloc( nDims );
    // get the pivot vertex
    pRandom = Emb_ManRandomVertex( p );
    Vec_IntPush( vStart, pRandom->hHandle );
    // get the most distant vertex from the pivot
    pPivot = Emb_ManFindDistances( p, vStart, NULL );
    nReached = p->nReached;
    if ( nReached < Emb_ManObjNum(p) )
        printf( "Visited less objects (%d) than present (%d).\n", p->nReached, Emb_ManObjNum(p) );
    // start dimensions with this vertex
    Vec_IntClear( vStart );
    for ( d = 0; d < nDims; d++ )
    {
//        printf( "%3d : Adding vertex %7d with distance %3d.\n", d+1, pPivot->Value, p->nDistMax ); 
        Vec_IntPush( vStart, pPivot->hHandle );
        if ( d+1 == nReached )
            break;
        pPivot = Emb_ManFindDistances( p, vStart, Emb_ManVec(p, d) );
        assert( nReached == p->nReached );
    }
    Vec_IntFree( vStart );
    // make sure the number of reached objects is correct
    Counter = 0;
    for ( i = 0; i < p->nObjs; i++ )
        if ( p->pVecs[i] < 255 )
            Counter++;
    assert( Counter == nReached );
}

/**Function*************************************************************

  Synopsis    [Allocated square matrix of floats.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float ** Emb_ManMatrAlloc( int nDims )
{
    int i;
    float ** pMatr = (float **)ABC_ALLOC( char, sizeof(float *) * nDims + sizeof(float) * nDims * nDims );
    pMatr[0] = (float *)(pMatr + nDims);
    for ( i = 1; i < nDims; i++ )
        pMatr[i] = pMatr[i-1] + nDims;
    return pMatr;
}

/**Function*************************************************************

  Synopsis    [Computes covariance matrix.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManComputeCovariance( Emb_Man_t * p, int nDims )
{
    unsigned char * pOne, * pTwo;
    float * pAves, * pCol;
    int d, i, k, v;
    // compute averages of vectors
    pAves = ABC_ALLOC( float, nDims );
    for ( d = 0; d < nDims; d++ )
    {
        pAves[d] = 0.0;
        pOne = Emb_ManVec( p, d );
        for ( v = 0; v < p->nObjs; v++ )
            if ( pOne[v] < 255 )
                pAves[d] += pOne[v];
        pAves[d] /= p->nReached;
    }
    // compute the matrix
    assert( p->pMatr == NULL );
    assert( p->pEigen == NULL );
    p->pMatr = Emb_ManMatrAlloc( nDims );
    p->pEigen = Emb_ManMatrAlloc( nDims );
    for ( i = 0; i < nDims; i++ )
    {
        pOne = Emb_ManVec( p, i );
        pCol = p->pMatr[i];
        for ( k = 0; k < nDims; k++ )
        {
            pTwo = Emb_ManVec( p, k );
            pCol[k] = 0.0;
            for ( v = 0; v < p->nObjs; v++ )
                if ( pOne[i] < 255 && pOne[k] < 255 )
                    pCol[k] += (pOne[i] - pAves[i])*(pOne[k] - pAves[k]);
        }
    }
    ABC_FREE( pAves );
}

/**Function*************************************************************

  Synopsis    [Returns random vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManVecRandom( float * pVec, int nDims )
{
    int i;
    for ( i = 0; i < nDims; i++ )
        pVec[i] = Aig_ManRandom( 0 );
}

/**Function*************************************************************

  Synopsis    [Returns normalized vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManVecNormal( float * pVec, int nDims )
{
    int i;
    double Norm = 0.0;
    for ( i = 0; i < nDims; i++ )
        Norm += pVec[i] * pVec[i];
    Norm = pow( Norm, 0.5 );
    for ( i = 0; i < nDims; i++ )
        pVec[i] /= Norm;
}

/**Function*************************************************************

  Synopsis    [Multiplies vector by vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Emb_ManVecMultiplyOne( float * pVec0, float * pVec1, int nDims )
{
    float Res = 0.0;
    int i;
    for ( i = 0; i < nDims; i++ )
        Res += pVec0[i] * pVec1[i];
    return Res;
}

/**Function*************************************************************

  Synopsis    [Copies the vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManVecCopyOne( float * pVecDest, float * pVecSour, int nDims )
{
    int i;
    for ( i = 0; i < nDims; i++ )
        pVecDest[i] = pVecSour[i];
}

/**Function*************************************************************

  Synopsis    [Multiplies matrix by vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManVecMultiply( float ** pMatr, float * pVec, int nDims, float * pRes )
{
    int i;
    for ( i = 0; i < nDims; i++ )
        pRes[i] = Emb_ManVecMultiplyOne( pMatr[i], pVec, nDims );
}

/**Function*************************************************************

  Synopsis    [Multiplies vector by matrix.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManVecOrthogonolize( float ** pEigen, int nVecs, float * pVec, int nDims )
{
    int i, k;
    for ( k = 0; k < nVecs; k++ )
        for ( i = 0; i < nDims; i++ )
            pVec[i] -= pEigen[k][i] * Emb_ManVecMultiplyOne( pEigen[k], pVec, nDims );
}

/**Function*************************************************************

  Synopsis    [Computes the first eigen-vectors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Emb_ManComputeSolutions( Emb_Man_t * p, int nDims, int nSols )
{
    float * pVecTemp, * pVecCur;
    int i, k, j;
    assert( nSols < nDims );
    pVecTemp = p->pEigen[nSols];
    for ( i = 0; i < nSols; i++ )
    {
        pVecCur = p->pEigen[i];
        Emb_ManVecRandom( pVecTemp, nDims );
        Emb_ManVecNormal( pVecTemp, nDims );
        do {
            Emb_ManVecCopyOne( pVecCur, pVecTemp, nDims );
            for ( j = 0; j < i; j++ )
                Emb_ManVecOrthogonolize( p->pEigen, i, pVecCur, nDims );
            Emb_ManVecMultiply( p->pMatr, pVecCur, nDims, pVecTemp );
            Emb_ManVecNormal( pVecTemp, nDims );
        } while ( Emb_ManVecMultiplyOne(pVecTemp, pVecCur, nDims) < 0.999 );
        Emb_ManVecCopyOne( pVecCur, pVecTemp, nDims );
    }
    assert( p->pSols == NULL );
    p->pSols = ABC_CALLOC( float, p->nObjs * nSols );
    for ( i = 0; i < nSols; i++ )
        for ( k = 0; k < nDims; k++ )
            for ( j = 0; j < p->nObjs; j++ )
                Emb_ManSol(p, i)[j] += Emb_ManVec(p, k)[j] * p->pEigen[i][k];
}

/**Function*************************************************************

  Synopsis    [Computes dimentions of the graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSolveProblem( Gia_Man_t * pGia, int nDims, int nSols )
{
    Emb_Man_t * p;
    int clk;
//   Gia_ManTestDistance( pGia );

clk = clock();
    p = Emb_ManStart( pGia );
//    Emb_ManPrintFanio( p );
    Emb_ManPrintStats( p );
    Aig_ManRandom( 1 );
    Emb_ManResetTravId( p );
    // set all nodes to have their IDs
    Emb_ManSetValue( p );
ABC_PRT( "Setup     ", clock() - clk );

clk = clock();
    Emb_ManComputeDimensions( p, nDims );
ABC_PRT( "Dimensions", clock() - clk );

clk = clock();
    Emb_ManComputeCovariance( p, nDims );
ABC_PRT( "Matrix    ", clock() - clk );

clk = clock();
//    Emb_ManComputeSolutions( p, nDims, nSols );
ABC_PRT( "Eigenvecs ", clock() - clk );

    Emb_ManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


