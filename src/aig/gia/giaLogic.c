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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Log_Obj_t_ Log_Obj_t;
struct Log_Obj_t_
{
    unsigned       fTerm    :  1;    // terminal node (CI/CO)
    unsigned       fMark0   :  1;    // first user-controlled mark
    unsigned       fMark1   :  1;    // second user-controlled mark
    unsigned       nFanins  : 28;    // the number of fanins
    unsigned       nFanouts;         // the number of fanouts
    unsigned       hHandle;          // the handle of the node
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

typedef struct Log_Man_t_ Log_Man_t;
struct Log_Man_t_
{
    Gia_Man_t *    pGia;             // the original AIG manager
    Vec_Int_t *    vCis;             // the vector of CIs (PIs + LOs)
    Vec_Int_t *    vCos;             // the vector of COs (POs + LIs)
    int            nObjs;            // the number of objects
    int            nNodes;           // the number of nodes
    int            nTravIds;         // traversal ID of the network
    int *          pObjData;         // the array containing data for objects
    int            nObjData;         // the size of array to store the logic network
};

static inline int         Log_ManCiNum( Log_Man_t * p )                               { return Vec_IntSize(p->vCis);  }
static inline int         Log_ManCoNum( Log_Man_t * p )                               { return Vec_IntSize(p->vCos);  }
static inline int         Log_ManObjNum( Log_Man_t * p )                              { return p->nObjs;                                    } 
static inline int         Log_ManNodeNum( Log_Man_t * p )                             { return p->nNodes;                                   } 

static inline Log_Obj_t * Log_ManObj( Log_Man_t * p, unsigned hHandle )               { return (Log_Obj_t *)(p->pObjData + hHandle);        } 
static inline Log_Obj_t * Log_ManCi( Log_Man_t * p, int i )                           { return Log_ManObj( p, Vec_IntEntry(p->vCis,i) );    }
static inline Log_Obj_t * Log_ManCo( Log_Man_t * p, int i )                           { return Log_ManObj( p, Vec_IntEntry(p->vCos,i) );    }

static inline int         Log_ObjIsTerm( Log_Obj_t * pObj )                           { return pObj->fTerm;                                 } 
static inline int         Log_ObjIsCi( Log_Obj_t * pObj )                             { return pObj->fTerm && pObj->nFanins == 0;           } 
static inline int         Log_ObjIsCo( Log_Obj_t * pObj )                             { return pObj->fTerm && pObj->nFanins == 1;           } 
static inline int         Log_ObjIsNode( Log_Obj_t * pObj )                           { return!pObj->fTerm && pObj->nFanins > 0;            } 
static inline int         Log_ObjIsConst0( Log_Obj_t * pObj )                         { return!pObj->fTerm && pObj->nFanins == 0;           } 

static inline int         Log_ObjFaninNum( Log_Obj_t * pObj )                         { return pObj->nFanins;                               } 
static inline int         Log_ObjFanoutNum( Log_Obj_t * pObj )                        { return pObj->nFanouts;                              } 
static inline int         Log_ObjSize( Log_Obj_t * pObj )                             { return sizeof(Log_Obj_t) / 4 + pObj->nFanins + pObj->nFanouts;  } 
static inline Log_Obj_t * Log_ObjFanin( Log_Obj_t * pObj, int i )                     { return (Log_Obj_t *)(((int *)pObj) - pObj->Fanios[i]);               } 
static inline Log_Obj_t * Log_ObjFanout( Log_Obj_t * pObj, int i )                    { return (Log_Obj_t *)(((int *)pObj) + pObj->Fanios[pObj->nFanins+i]); } 

static inline void        Log_ManResetTravId( Log_Man_t * p )                         { extern void Log_ManCleanTravId( Log_Man_t * p ); Log_ManCleanTravId( p ); p->nTravIds = 1;  }
static inline void        Log_ManIncrementTravId( Log_Man_t * p )                     { p->nTravIds++;                                      }
static inline void        Log_ObjSetTravId( Log_Obj_t * pObj, int TravId )            { pObj->TravId = TravId;                              }
static inline void        Log_ObjSetTravIdCurrent( Log_Man_t * p, Log_Obj_t * pObj )  { pObj->TravId = p->nTravIds;                         }
static inline void        Log_ObjSetTravIdPrevious( Log_Man_t * p, Log_Obj_t * pObj ) { pObj->TravId = p->nTravIds - 1;                     }
static inline int         Log_ObjIsTravIdCurrent( Log_Man_t * p, Log_Obj_t * pObj )   { return ((int)pObj->TravId == p->nTravIds);          }
static inline int         Log_ObjIsTravIdPrevious( Log_Man_t * p, Log_Obj_t * pObj )  { return ((int)pObj->TravId == p->nTravIds - 1);      }

#define Log_ManForEachObj( p, pObj, i )               \
    for ( i = 0; (i < p->nObjData) && (pObj = Log_ManObj(p,i)); i += Log_ObjSize(pObj) )
#define Log_ManForEachNode( p, pObj, i )              \
    for ( i = 0; (i < p->nObjData) && (pObj = Log_ManObj(p,i)); i += Log_ObjSize(pObj) ) if ( Log_ObjIsTerm(pObj) ) {} else
#define Log_ManForEachObjVec( vVec, p, pObj, i )                        \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pObj) = Log_ManObj(p, Vec_IntEntry(vVec,i))); i++ )
#define Log_ObjForEachFanin( pObj, pNext, i )         \
    for ( i = 0; (i < (int)pObj->nFanins) && (pNext = Log_ObjFanin(pObj,i)); i++ )
#define Log_ObjForEachFanout( pObj, pNext, i )        \
    for ( i = 0; (i < (int)pObj->nFanouts) && (pNext = Log_ObjFanout(pObj,i)); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect the fanin IDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Log_ManCollectSuper( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSuper )  
{
    if ( pObj->fMark0 )
    {
        Vec_IntPushUnique( vSuper, Gia_ObjId(p, pObj) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Log_ManCollectSuper( p, Gia_ObjFanin0(pObj), vSuper );
    Log_ManCollectSuper( p, Gia_ObjFanin1(pObj), vSuper );
}

/**Function*************************************************************

  Synopsis    [Assigns references while removing the MUX/XOR ones.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Log_ManCreateRefsSpecial( Gia_Man_t * p )  
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
void Log_ManTransformRefs( Gia_Man_t * p, int * pnObjs, int * pnFanios )  
{
    Vec_Int_t * vSuper;
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
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( pObj->fMark0 == 0 )
            continue;
        Vec_IntClear( vSuper );
        pObj->fMark0 = 0;
        Log_ManCollectSuper( p, pObj, vSuper );
        pObj->fMark0 = 1;
        Gia_ManForEachObjVec( vSuper, p, pFanin, k )
        {
            assert( pFanin->fMark0 );
            Gia_ObjRefInc( p, pFanin );
        }
        Counter += Vec_IntSize( vSuper );
    }
    Vec_IntFree( vSuper );
    // reference from outputs
    Gia_ManForEachCoDriver( p, pObj, i )
    {
        assert( pObj->fMark0 );
        Gia_ObjRefInc( p, pObj );
    }
    *pnFanios = Counter + Gia_ManCoNum(p);
}

/**Function*************************************************************

  Synopsis    [Creates fanin/fanout pair.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Log_ObjAddFanin( Log_Obj_t * pObj, Log_Obj_t * pFanin )
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
Log_Man_t * Log_ManStart( Gia_Man_t * pGia )
{
    Log_Man_t * p;
    Log_Obj_t * pObjLog, * pFanLog;
    Gia_Obj_t * pObj, * pFanin;
    Vec_Int_t * vSuper;
    int nObjs, nFanios;
    int i, k, hHandle = 0;
    // prepare the AIG
//    Gia_ManCreateRefs( pGia );
    Log_ManCreateRefsSpecial( pGia );
    Log_ManTransformRefs( pGia, &nObjs, &nFanios );
    Gia_ManFillValue( pGia );
    // create logic network
    p = ABC_CALLOC( Log_Man_t, 1 );
    p->pGia = pGia;
    p->vCis = Vec_IntAlloc( Gia_ManCiNum(pGia) );
    p->vCos = Vec_IntAlloc( Gia_ManCoNum(pGia) );
    p->nObjData = (sizeof(Log_Obj_t) / 4) * nObjs + 2 * nFanios;
    p->pObjData = ABC_CALLOC( int, p->nObjData );
    // create constant node
    Gia_ManConst0(pGia)->Value = hHandle;
    pObjLog = Log_ManObj( p, hHandle );
    pObjLog->hHandle  = hHandle;
    pObjLog->nFanins  = 0;
    pObjLog->nFanouts = Gia_ObjRefs( pGia, Gia_ManConst0(pGia) );
    // count objects
    hHandle += Log_ObjSize( pObjLog );
    p->nNodes++;
    p->nObjs++;
    // create the PIs
    Gia_ManForEachCi( pGia, pObj, i )
    {
        // create PI object
        pObj->Value = hHandle;
        Vec_IntPush( p->vCis, hHandle );
        pObjLog = Log_ManObj( p, hHandle );
        pObjLog->hHandle  = hHandle;
        pObjLog->nFanins  = 0;
        pObjLog->nFanouts = Gia_ObjRefs( pGia, pObj );
        pObjLog->fTerm = 1;
        // count objects
        hHandle += Log_ObjSize( pObjLog );
        p->nObjs++;
    }
    // create internal nodes
    vSuper = Vec_IntAlloc( 100 );
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( pObj->fMark0 == 0 )
        {
            assert( Gia_ObjRefs( pGia, pObj ) == 0 );
            continue;
        }
        assert( Gia_ObjRefs( pGia, pObj ) > 0 );
        // collect fanins
        Vec_IntClear( vSuper );
        pObj->fMark0 = 0;
        Log_ManCollectSuper( pGia, pObj, vSuper );
        pObj->fMark0 = 1;
        // create node object
        pObj->Value = hHandle;
        pObjLog = Log_ManObj( p, hHandle );
        pObjLog->hHandle  = hHandle;
        pObjLog->nFanins  = Vec_IntSize( vSuper );
        pObjLog->nFanouts = Gia_ObjRefs( pGia, pObj );
        // add fanins
        Gia_ManForEachObjVec( vSuper, pGia, pFanin, k )
        {
            pFanLog = Log_ManObj( p, Gia_ObjValue(pFanin) ); 
            Log_ObjAddFanin( pObjLog, pFanLog );
        }
        // count objects
        hHandle += Log_ObjSize( pObjLog );
        p->nNodes++;
        p->nObjs++;
    }
    Vec_IntFree( vSuper );
    // create the POs
    Gia_ManForEachCo( pGia, pObj, i )
    {
        // create PO object
        pObj->Value = hHandle;
        Vec_IntPush( p->vCos, hHandle );
        pObjLog = Log_ManObj( p, hHandle );
        pObjLog->hHandle  = hHandle;
        pObjLog->nFanins  = 1;
        pObjLog->nFanouts = 0;
        pObjLog->fTerm = 1;
        // add fanins
        pFanLog = Log_ManObj( p, Gia_ObjValue(Gia_ObjFanin0(pObj)) );
        Log_ObjAddFanin( pObjLog, pFanLog );
        // count objects
        hHandle += Log_ObjSize( pObjLog );
        p->nObjs++;
    }
    Gia_ManCleanMark0( pGia );
    assert( nObjs == p->nObjs );
    assert( hHandle == p->nObjData );
    // make sure the fanin/fanout counters are correct
    Gia_ManForEachObj( pGia, pObj, i )
    {
        if ( !~Gia_ObjValue(pObj) )
            continue;
        pObjLog = Log_ManObj( p, Gia_ObjValue(pObj) );
        assert( pObjLog->nFanins == pObjLog->iFanin );
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
void Log_ManPrintStats( Log_Man_t * p )
{
//    if ( p->pName )
//        printf( "%8s : ", p->pName );
    printf( "i/o =%7d/%7d  ", Log_ManCiNum(p), Log_ManCoNum(p) );
//    if ( Log_ManRegNum(p) )
//        printf( "ff =%7d  ", Log_ManRegNum(p) );
    printf( "node =%8d  ", Log_ManNodeNum(p) );
//    printf( "lev =%5d  ", Log_ManLevelNum(p) );
//    printf( "cut =%5d  ", Log_ManCrossCut(p) );
    printf( "mem =%5.2f Mb", 4.0*p->nObjData/(1<<20) );
//    printf( "obj =%5d  ", Log_ManObjNum(p) );
    printf( "\n" );

//    Log_ManSatExperiment( p );
}

/**Function*************************************************************

  Synopsis    [Creates logic network isomorphic to the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Log_ManStop( Log_Man_t * p )
{
    Vec_IntFree( p->vCis );
    Vec_IntFree( p->vCos );
    ABC_FREE( p->pObjData );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Cleans the value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Log_ManCleanTravId( Log_Man_t * p )  
{
    Log_Obj_t * pObj;
    int i;
    Log_ManForEachObj( p, pObj, i )
        pObj->TravId = 0;
}

/**Function*************************************************************

  Synopsis    [Cleans the value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Log_ManCleanValue( Log_Man_t * p )  
{
    Log_Obj_t * pObj;
    int i;
    Log_ManForEachObj( p, pObj, i )
        pObj->Value = 0;
}

/**Function*************************************************************

  Synopsis    [Prints the distribution of fanins/fanouts in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Log_ManPrintFanio( Log_Man_t * p )
{
    char Buffer[100];
    Log_Obj_t * pNode;
    Vec_Int_t * vFanins, * vFanouts;
    int nFanins, nFanouts, nFaninsMax, nFanoutsMax, nFaninsAll, nFanoutsAll;
    int i, k, nSizeMax;

    // determine the largest fanin and fanout
    nFaninsMax = nFanoutsMax = 0;
    nFaninsAll = nFanoutsAll = 0;
    Log_ManForEachNode( p, pNode, i )
    {
        if ( i == 0 ) continue; // skip const 0 obj
        nFanins  = Log_ObjFaninNum(pNode);
        nFanouts = Log_ObjFanoutNum(pNode);
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
    Log_ManForEachNode( p, pNode, i )
    {
        if ( i == 0 ) continue; // skip const 0 obj
        nFanins  = Log_ObjFaninNum(pNode);
        nFanouts = Log_ObjFanoutNum(pNode);

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
        nFaninsMax,  1.0*nFaninsAll/Log_ManNodeNum(p), 
        nFanoutsMax, 1.0*nFanoutsAll/Log_ManNodeNum(p)  );
}

/**Function*************************************************************

  Synopsis    [Computes the distance from the given object]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Log_ManComputeDistance( Log_Man_t * p, Log_Obj_t * pPivot )
{
    Vec_Int_t * vThis, * vNext, * vTemp;
    Log_Obj_t * pThis, * pNext;
    int i, k, d, nVisited = 0;
//    assert( Log_ObjIsTerm(pPivot) );
    vThis = Vec_IntAlloc( 1000 );
    vNext = Vec_IntAlloc( 1000 );
    Log_ManIncrementTravId( p );
    Log_ObjSetTravIdCurrent( p, pPivot );
    Vec_IntPush( vThis, pPivot->hHandle );
    for ( d = 0; Vec_IntSize(vThis) > 0; d++ )
    {
        nVisited += Vec_IntSize(vThis);
        Vec_IntClear( vNext );
        Log_ManForEachObjVec( vThis, p, pThis, i )
        {
            Log_ObjForEachFanin( pThis, pNext, k )
            {
                if ( Log_ObjIsTravIdCurrent(p, pNext) )
                    continue;
                Log_ObjSetTravIdCurrent(p, pNext);
                Vec_IntPush( vNext, pNext->hHandle );
                nVisited += !Log_ObjIsTerm(pNext);
            }
            Log_ObjForEachFanout( pThis, pNext, k )
            {
                if ( Log_ObjIsTravIdCurrent(p, pNext) )
                    continue;
                Log_ObjSetTravIdCurrent(p, pNext);
                Vec_IntPush( vNext, pNext->hHandle );
                nVisited += !Log_ObjIsTerm(pNext);
            }
        }
        vTemp = vThis; vThis = vNext; vNext = vTemp;
    }
    Vec_IntFree( vThis );
    Vec_IntFree( vNext );
    // check if there are several strongly connected components
//    if ( nVisited < Log_ManNodeNum(p) )
//        printf( "Visited less nodes (%d) than present (%d).\n", nVisited, Log_ManNodeNum(p) );
    return d;
}

/**Function*************************************************************

  Synopsis    [Traverses from the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void Gia_ManTestDistanceInternal( Log_Man_t * p )
{
    int nAttempts = 20;
    int i, iNode, Dist, clk;
    Log_Obj_t * pPivot, * pNext;
    Aig_ManRandom( 1 );
    Log_ManResetTravId( p );
    // compute distances from several randomly selected PIs
    clk = clock();
    printf( "From inputs: " );
    for ( i = 0; i < nAttempts; i++ )
    {
        iNode = Aig_ManRandom( 0 ) % Log_ManCiNum(p);
        pPivot = Log_ManCi( p, iNode );
        if ( Log_ObjFanoutNum(pPivot) == 0 )
            { i--; continue; }
        pNext = Log_ObjFanout( pPivot, 0 );
        if ( !Log_ObjIsNode(pNext) )
            { i--; continue; }
        Dist = Log_ManComputeDistance( p, pPivot );
        printf( "%d ", Dist );
    }
    ABC_PRT( "Time", clock() - clk );
    // compute distances from several randomly selected POs
    clk = clock();
    printf( "From outputs: " );
    for ( i = 0; i < nAttempts; i++ )
    {
        iNode = Aig_ManRandom( 0 ) % Log_ManCoNum(p);
        pPivot = Log_ManCo( p, iNode );
        pNext = Log_ObjFanin( pPivot, 0 );
        if ( !Log_ObjIsNode(pNext) )
            { i--; continue; }
        Dist = Log_ManComputeDistance( p, pPivot );
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
        pPivot = Log_ManObj( p, Gia_ManObj(p->pGia, iNode)->Value );
        if ( !Log_ObjIsNode(pPivot) )
            { i--; continue; }
        Dist = Log_ManComputeDistance( p, pPivot );
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
    Log_Man_t * p;
    int clk = clock();
    p = Log_ManStart( pGia );
//    Log_ManPrintFanio( p );
    Log_ManPrintStats( p );
ABC_PRT( "Time", clock() - clk );
    Gia_ManTestDistanceInternal( p );
    Log_ManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


