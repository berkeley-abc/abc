/**CFile****************************************************************

  FileName    [aigRet.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Retiming of AIGs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigRet.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// init values
typedef enum { 
    RTM_VAL_NONE,                    // 0: non-existent value
    RTM_VAL_ZERO,                    // 1: initial value 0
    RTM_VAL_ONE,                     // 2: initial value 1
    RTM_VAL_VOID                     // 3: unused value
} Rtm_Init_t;

typedef struct Rtm_Man_t_    Rtm_Man_t;
struct Rtm_Man_t_
{
    // network representation
    Vec_Ptr_t *      vObjs;          // retiming objects
    Vec_Ptr_t *      vPis;           // PIs only
    Vec_Ptr_t *      vPos;           // POs only
    Aig_MmFlex_t *   pMem;           // the memory manager
    // storage for overflow latches
    unsigned *       pExtra;       
    unsigned *       pExtraFree;
};

typedef struct Rtm_Edg_t_    Rtm_Edg_t;
struct Rtm_Edg_t_
{
    unsigned long    nLats   :  12;  // the number of latches
    unsigned long    LData   :  20;  // the latches themselves
};

typedef struct Rtm_Obj_t_    Rtm_Obj_t;
struct Rtm_Obj_t_
{
    void *           pCopy;          // the copy of this object
    unsigned long    Type    :  3;   // object type
    unsigned long    fMark   :  1;   // multipurpose mark
    unsigned long    fCompl0 :  1;   // complemented attribute of the first edge
    unsigned long    fCompl1 :  1;   // complemented attribute of the second edge
    unsigned long    nFanins :  8;   // the number of fanins
    unsigned         Num     : 18;   // the retiming number of this node
    int              Id;             // ID of this object
    int              Temp;           // temporary usage
    int              nFanouts;       // the number of fanouts
    void *           pFanio[0];      // fanins and their edges (followed by fanouts and pointers to their edges)
};

static Rtm_Init_t  Rtm_InitNot( Rtm_Init_t Val )                 { if ( Val == RTM_VAL_ZERO ) return RTM_VAL_ONE; if ( Val == RTM_VAL_ONE ) return RTM_VAL_ZERO; assert( 0 ); return -1; }
static Rtm_Init_t  Rtm_InitNotCond( Rtm_Init_t Val, int c )      { return c ? Rtm_InitNot(Val) : Val;                         }
static Rtm_Init_t  Rtm_InitAnd(Rtm_Init_t ValA, Rtm_Init_t ValB) { if ( ValA == RTM_VAL_ONE && ValB == RTM_VAL_ONE ) return RTM_VAL_ONE;  if ( ValA == RTM_VAL_ZERO || ValB == RTM_VAL_ZERO ) return RTM_VAL_ZERO; assert( 0 ); return -1;   }

static Rtm_Obj_t * Rtm_ObjFanin( Rtm_Obj_t * pObj, int i )       { return (Rtm_Obj_t *)pObj->pFanio[2*i];                     }
static Rtm_Obj_t * Rtm_ObjFanout( Rtm_Obj_t * pObj, int i )      { return (Rtm_Obj_t *)pObj->pFanio[2*(pObj->nFanins+i)];     }
static Rtm_Edg_t * Rtm_ObjEdge( Rtm_Obj_t * pObj, int i )        { return (Rtm_Edg_t *)(pObj->pFanio + 2*i + 1);              }
static Rtm_Edg_t * Rtm_ObjFanoutEdge( Rtm_Obj_t * pObj, int i )  { return (Rtm_Edg_t *)pObj->pFanio[2*(pObj->nFanins+i) + 1]; }

static Rtm_Init_t  Rtm_ObjGetFirst( Rtm_Edg_t * pEdge )          { return pEdge->LData & 3;                                    }
static Rtm_Init_t  Rtm_ObjGetLast( Rtm_Edg_t * pEdge )           { return (pEdge->LData >> (2 *(pEdge->nLats-1))) & 3;         }
static Rtm_Init_t  Rtm_ObjGetOne( Rtm_Edg_t * pEdge, int i )     { assert( i < (int)pEdge->nLats ); return (pEdge->LData >> (2 * i)) & 3;  }
static Rtm_Init_t  Rtm_ObjRemFirst( Rtm_Edg_t * pEdge )          { int Val = pEdge->LData & 3; pEdge->LData >>= 2; assert(pEdge->nLats > 0); pEdge->nLats--; return Val;  }
static Rtm_Init_t  Rtm_ObjRemLast( Rtm_Edg_t * pEdge )           { int Val = (pEdge->LData >> (2 *(pEdge->nLats-1))) & 3; pEdge->LData ^= Val << (2 *(pEdge->nLats-1)); assert(pEdge->nLats > 0); pEdge->nLats--; return Val;  }
static void        Rtm_ObjAddFirst( Rtm_Edg_t * pEdge, Rtm_Init_t Lat ) { assert( Lat < 4 ); pEdge->LData = (pEdge->LData << 2) | Lat;  pEdge->nLats++;   }
static void        Rtm_ObjAddLast( Rtm_Edg_t * pEdge, Rtm_Init_t Lat )  { assert( Lat < 4 ); pEdge->LData |= Lat << (2*pEdge->nLats);  pEdge->nLats++;   }

// iterator over the primary inputs
#define Rtm_ManForEachPi( p, pObj, i )                                          \
    Vec_PtrForEachEntry( p->vPis, pObj, i )
// iterator over the primary outputs
#define Rtm_ManForEachPo( p, pObj, i )                                          \
    Vec_PtrForEachEntry( p->vPos, pObj, i )
// iterator over all objects, including those currently not used
#define Rtm_ManForEachObj( p, pObj, i )                                         \
    Vec_PtrForEachEntry( p->vObjs, pObj, i ) 
// iterate through the fanins
#define Rtm_ObjForEachFanin( pObj, pFanin, i )                                  \
    for ( i = 0; i < (int)(pObj)->nFanins && ((pFanin = Rtm_ObjFanin(pObj, i)), 1); i++ )
// iterate through the fanouts
#define Rtm_ObjForEachFanout( pObj, pFanout, i )                                \
    for ( i = 0; i < (int)(pObj)->nFanouts && ((pFanout = Rtm_ObjFanout(pObj, i)), 1); i++ )
// iterate through the fanin edges
#define Rtm_ObjForEachFaninEdge( pObj, pEdge, i )                               \
    for ( i = 0; i < (int)(pObj)->nFanins && ((pEdge = Rtm_ObjEdge(pObj, i)), 1); i++ )
// iterate through the fanout edges
#define Rtm_ObjForEachFanoutEdge( pObj, pEdge, i )                              \
    for ( i = 0; i < (int)(pObj)->nFanouts && ((pEdge = Rtm_ObjFanoutEdge(pObj, i)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the retiming manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rtm_Man_t * Rtm_ManAlloc( Aig_Man_t * p )
{
    Rtm_Man_t * pRtm;
    // start the manager
    pRtm = ALLOC( Rtm_Man_t, 1 );
    memset( pRtm, 0, sizeof(Rtm_Man_t) );
    // perform initializations
    pRtm->vObjs = Vec_PtrAlloc( Aig_ManObjNum(p) );
    pRtm->vPis  = Vec_PtrAlloc( Aig_ManPiNum(p) );
    pRtm->vPos  = Vec_PtrAlloc( Aig_ManPoNum(p) );
    pRtm->pMem  = Aig_MmFlexStart();
    return pRtm;
}

/**Function*************************************************************

  Synopsis    [Allocates the retiming manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rtm_ManFree( Rtm_Man_t * p )
{
    Vec_PtrFree( p->vObjs );
    Vec_PtrFree( p->vPis );
    Vec_PtrFree( p->vPos );
    Aig_MmFlexStop( p->pMem, 0 );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Counts the maximum number of latches on an edge.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rtm_ManLatchMax( Rtm_Man_t * p )
{
    Rtm_Obj_t * pObj;
    Rtm_Edg_t * pEdge;
    int nLatchMax = 0, i, k;
    Rtm_ManForEachObj( p, pObj, i )
    Rtm_ObjForEachFaninEdge( pObj, pEdge, k )
        nLatchMax = AIG_MAX( nLatchMax, (int)pEdge->nLats );
    return nLatchMax;
}

/**Function*************************************************************

  Synopsis    [Allocates the retiming object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rtm_Obj_t * Rtm_ObjAlloc( Rtm_Man_t * pRtm, int nFanins, int nFanouts )
{
    Rtm_Obj_t * pObj;
    int Size = sizeof(Rtm_Obj_t) + sizeof(Rtm_Obj_t *) * (nFanins + nFanouts) * 2;
    pObj = (Rtm_Obj_t *)Aig_MmFlexEntryFetch( pRtm->pMem, Size );
    memset( pObj, 0, sizeof(Rtm_Obj_t) );
    pObj->Type = (int)(nFanins == 1 && nFanouts == 0); // mark PO
    pObj->Num  = nFanins;  // temporary
    pObj->Temp = nFanouts;
    pObj->Id = Vec_PtrSize(pRtm->vObjs);
    Vec_PtrPush( pRtm->vObjs, pObj );
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Allocates the retiming object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rtm_ObjAddFanin( Rtm_Obj_t * pObj, Rtm_Obj_t * pFanin, int fCompl )
{
    pObj->pFanio[ 2*pObj->nFanins ] = pFanin;
    pObj->pFanio[ 2*pObj->nFanins + 1 ] = NULL;
    pFanin->pFanio[ 2*(pFanin->Num + pFanin->nFanouts) ] = pObj;
    pFanin->pFanio[ 2*(pFanin->Num + pFanin->nFanouts) + 1 ] = pObj->pFanio + 2*pObj->nFanins + 1;
    if ( pObj->nFanins == 0 )
        pObj->fCompl0 = fCompl;
    else if ( pObj->nFanins == 1 )
        pObj->fCompl1 = fCompl;
    else
        assert( 0 );
    pObj->nFanins++;
    pFanin->nFanouts++;
    assert( pObj->nFanins <= pObj->Num );
    assert( pFanin->nFanouts <= pFanin->Temp );
}

/**Function*************************************************************

  Synopsis    [Check the possibility of forward retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rtm_ObjCheckRetimeFwd( Rtm_Obj_t * pObj )
{
    Rtm_Edg_t * pEdge;
    int i;
    Rtm_ObjForEachFaninEdge( pObj, pEdge, i )
        if ( pEdge->nLats == 0 )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Check the possibility of forward retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rtm_ObjGetDegreeFwd( Rtm_Obj_t * pObj )
{
    Rtm_Obj_t * pFanin;
    int i, Degree = 0;
    Rtm_ObjForEachFanin( pObj, pFanin, i )
        Degree = AIG_MAX( Degree, (int)pFanin->Num );
    return Degree + 1;
}

/**Function*************************************************************

  Synopsis    [Performs forward retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rtm_ObjRetimeFwd( Rtm_Obj_t * pObj )
{
    Rtm_Init_t ValTotal, ValCur;
    Rtm_Edg_t * pEdge;
    int i;
    assert( Rtm_ObjCheckRetimeFwd(pObj) );
    // extract values and compute the result
    ValTotal = RTM_VAL_ONE;
    Rtm_ObjForEachFaninEdge( pObj, pEdge, i )
    {
        ValCur = Rtm_ObjRemFirst( pEdge );
        ValCur = Rtm_InitNotCond( ValCur, i? pObj->fCompl1 : pObj->fCompl0 );
        ValTotal = Rtm_InitAnd( ValTotal, ValCur );
    }
    // insert the result in the fanout values
    Rtm_ObjForEachFanoutEdge( pObj, pEdge, i )
    {
        if ( pEdge->nLats >= 10 )
            printf( "Rtm_ObjRetimeFwd(); More than 10 latches on the edge!\n" );
        Rtm_ObjAddLast( pEdge, ValTotal );
    }
}

/**Function*************************************************************

  Synopsis    [Derive retiming manager from the given AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rtm_Man_t * Rtm_ManFromAig( Aig_Man_t * p )
{
    Rtm_Man_t * pRtm;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i;
    assert( Aig_ManRegNum(p) > 0 );
    assert( Aig_ManBufNum(p) == 0 );
    // allocate the manager
    pRtm = Rtm_ManAlloc( p );
    // allocate objects
    pObj = Aig_ManConst1(p);
    pObj->pData = Rtm_ObjAlloc( pRtm, 0, pObj->nRefs );
    Aig_ManForEachPiSeq( p, pObj, i )
    {
        pObj->pData = Rtm_ObjAlloc( pRtm, 0, pObj->nRefs );
        Vec_PtrPush( pRtm->vPis, pObj->pData );
    }
    Aig_ManForEachPoSeq( p, pObj, i )
    {
        pObj->pData = Rtm_ObjAlloc( pRtm, 1, 0 );
        Vec_PtrPush( pRtm->vPos, pObj->pData );
    }
    Aig_ManForEachLoSeq( p, pObj, i )
        pObj->pData = Rtm_ObjAlloc( pRtm, 1, pObj->nRefs );
    Aig_ManForEachLiSeq( p, pObj, i )
        pObj->pData = Rtm_ObjAlloc( pRtm, 1, 1 );
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Rtm_ObjAlloc( pRtm, 2, pObj->nRefs );
    // connect objects
    Aig_ManForEachPoSeq( p, pObj, i )
        Rtm_ObjAddFanin( pObj->pData, Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj) );
    Aig_ManForEachLiSeq( p, pObj, i )
        Rtm_ObjAddFanin( pObj->pData, Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj) );
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        Rtm_ObjAddFanin( pObjLo->pData, pObjLi->pData, 0 );
    Aig_ManForEachNode( p, pObj, i )
    {
        Rtm_ObjAddFanin( pObj->pData, Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj) );
        Rtm_ObjAddFanin( pObj->pData, Aig_ObjFanin1(pObj)->pData, Aig_ObjFaninC1(pObj) );
    }
    // set registers
    Aig_ManForEachLoSeq( p, pObj, i )
        Rtm_ObjAddFirst( Rtm_ObjEdge(pObj->pData, 0), RTM_VAL_ZERO );
    return pRtm;
}

/**Function*************************************************************

  Synopsis    [Derive AIG manager after retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Rtm_ManToAig_rec( Aig_Man_t * pNew, Rtm_Obj_t * pObjRtm, int * pLatches )
{
    Rtm_Edg_t * pEdge;
    Aig_Obj_t * pRes, * pFanin;
    int k, Val;
    if ( pObjRtm->pCopy )
        return pObjRtm->pCopy;
    // get the inputs
    pRes = Aig_ManConst1( pNew );
    Rtm_ObjForEachFaninEdge( pObjRtm, pEdge, k )
    {
        if ( pEdge->nLats == 0 )
            pFanin = Rtm_ManToAig_rec( pNew, Rtm_ObjFanin(pObjRtm, k), pLatches );
        else
        {
            Val = Rtm_ObjGetFirst( pEdge );
            pFanin = Aig_ManPi( pNew, pLatches[2*pObjRtm->Id + k] + pEdge->nLats - 1 );
            pFanin = Aig_NotCond( pFanin, Val == RTM_VAL_ONE );
        }
        pFanin = Aig_NotCond( pFanin, k ? pObjRtm->fCompl1 : pObjRtm->fCompl0 );
        pRes = Aig_And( pNew, pRes, pFanin );
    }
    return pObjRtm->pCopy = pRes;
}

/**Function*************************************************************

  Synopsis    [Derive AIG manager after retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Rtm_ManToAig( Rtm_Man_t * pRtm )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObjNew;
    Rtm_Obj_t * pObjRtm;
    Rtm_Edg_t * pEdge;
    int i, k, m, Val, nLatches, * pLatches;
    // count latches and mark the first latch on each edge
    pLatches = ALLOC( int, 2 * Vec_PtrSize(pRtm->vObjs) );
    nLatches = 0;
    Rtm_ManForEachObj( pRtm, pObjRtm, i )
    Rtm_ObjForEachFaninEdge( pObjRtm, pEdge, k )
    {
        pLatches[2*pObjRtm->Id + k] = Vec_PtrSize(pRtm->vPis) + nLatches;
        nLatches += pEdge->nLats;
    }
    // create the new manager
    pNew = Aig_ManStart( Vec_PtrSize(pRtm->vObjs) + nLatches );
    // create PIs/POs and latches
    pObjRtm = Vec_PtrEntry( pRtm->vObjs, 0 );
    pObjRtm->pCopy = Aig_ManConst1(pNew);
    Rtm_ManForEachPi( pRtm, pObjRtm, i )
        pObjRtm->pCopy = Aig_ObjCreatePi(pNew);
    for ( i = 0; i < nLatches; i++ )
        Aig_ObjCreatePi(pNew);
    // create internal nodes
    Rtm_ManForEachObj( pRtm, pObjRtm, i )
        Rtm_ManToAig_rec( pNew, pObjRtm, pLatches );
    // create POs
    Rtm_ManForEachPo( pRtm, pObjRtm, i )
        Aig_ObjCreatePo( pNew, pObjRtm->pCopy );
    // connect latches 
    Rtm_ManForEachObj( pRtm, pObjRtm, i )
    Rtm_ObjForEachFaninEdge( pObjRtm, pEdge, k )
    {
        if ( pEdge->nLats == 0 )
            continue;
        pObjNew = Rtm_ObjFanin( pObjRtm, k )->pCopy;
        for ( m = 0; m < (int)pEdge->nLats; m++ )
        {
            Val = Rtm_ObjGetOne( pEdge, pEdge->nLats - 1 - m );
            pObjNew = Aig_NotCond( pObjNew, Val == RTM_VAL_ONE );
            Aig_ObjCreatePo( pNew, pObjNew );
            pObjNew = Aig_ManPi( pNew, pLatches[2*pObjRtm->Id + k] + m );
            pObjNew = Aig_NotCond( pObjNew, Val == RTM_VAL_ONE );
        }
        assert( Aig_Regular(pObjNew)->nRefs > 0 );
    }
    free( pLatches );
    pNew->nRegs = nLatches;
    // remove useless nodes
    Aig_ManCleanup( pNew );
    if ( !Aig_ManCheck( pNew ) )
        printf( "Rtm_ManToAig: The network check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Performs forward retiming with the given limit on depth.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Rtm_ManRetimeFwd( Aig_Man_t * p, int nStepsMax, int fVerbose )
{
    Vec_Ptr_t * vQueue;
    Aig_Man_t * pNew;
    Rtm_Man_t * pRtm;
    Rtm_Obj_t * pObj, * pFanout;
    Aig_Obj_t * pObjAig;
    int i, k, Degree, DegreeMax = 0; 
    // create the retiming manager
    pRtm = Rtm_ManFromAig( p );
    // set the current retiming number
    Rtm_ManForEachObj( pRtm, pObj, i )
    {
        assert( pObj->nFanins == pObj->Num );
        assert( pObj->nFanouts == pObj->Temp );
        pObj->Num = 0;
    }

    // put the LOs on the queue
    vQueue = Vec_PtrAlloc( 1000 );
    Aig_ManForEachLoSeq( p, pObjAig, i )
    {
        pObj = pObjAig->pData;
        pObj->fMark = 1;
        Vec_PtrPush( vQueue, pObj );
    }
    // perform retiming 
    DegreeMax = 0;
    Vec_PtrForEachEntry( vQueue, pObj, i )
    {
        pObj->fMark = 0;
        // retime the node 
        Rtm_ObjRetimeFwd( pObj );
        // check if its fanouts should be retimed
        Rtm_ObjForEachFanout( pObj, pFanout, k )
        {
            if ( pFanout->fMark ) // skip aleady scheduled
                continue;
            if ( pFanout->Type ) // skip POs
                continue;
            if ( !Rtm_ObjCheckRetimeFwd( pFanout ) ) // skip non-retimable
                continue;
            Degree = Rtm_ObjGetDegreeFwd( pFanout );
            DegreeMax = AIG_MAX( DegreeMax, Degree );
            if ( Degree > nStepsMax ) // skip nodes with high degree
                continue;
            pFanout->fMark = 1;
            pFanout->Num = Degree;
            Vec_PtrPush( vQueue, pFanout );
        }
    }

    if ( fVerbose )
        printf( "Performed %d fwd latch moves of max depth %d and max latch count %d.\n", 
            Vec_PtrSize(vQueue), DegreeMax, Rtm_ManLatchMax(pRtm) );
    Vec_PtrFree( vQueue );

    // get the new manager
    pNew = Rtm_ManToAig( pRtm );
    Rtm_ManFree( pRtm );
    // group the registers
    pNew = Aig_ManReduceLaches( pNew, fVerbose );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


