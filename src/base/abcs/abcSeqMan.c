/**CFile****************************************************************

  FileName    [abcSeqMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Manager of sequential AIGs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcSeqMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abcs.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abc_SeqLat_t_  Abc_SeqLat_t;
struct Abc_SeqLat_t_
{
    Abc_SeqLat_t *      pNext;    // the next Lat in the ring
    Abc_SeqLat_t *      pPrev;    // the prev Lat in the ring 
};

typedef struct Abc_SeqMan_t_  Abc_SeqMan_t;
struct Abc_SeqMan_t_
{
    int                 nSize;           // the number of entries in all internal arrays
    Vec_Ptr_t *         vInits;          // the initial states for each edge in the AIG
    Extra_MmFixed_t *   pMmInits;        // memory manager for initial states of the Lates

};

// reading the contents of the lat
static inline Abc_InitType_t Abc_SeqLatInit( Abc_SeqLat_t * pLat )  {  return ((unsigned)pLat->pPrev) & 3;                                 }
static inline Abc_SeqLat_t * Abc_SeqLatNext( Abc_SeqLat_t * pLat )  {  return pLat->pNext;                                                 }
static inline Abc_SeqLat_t * Abc_SeqLatPrev( Abc_SeqLat_t * pLat )  {  return (void *)(((unsigned)pLat->pPrev) & (ABC_FULL_MASK << 2));    }

// setting the contents of the lat
static inline void           Abc_SeqLatSetInit( Abc_SeqLat_t * pLat, Abc_InitType_t Init )  { pLat->pPrev = (void *)( (3 & Init) | (((unsigned)pLat->pPrev) & (ABC_FULL_MASK << 2)) );          }
static inline void           Abc_SeqLatSetNext( Abc_SeqLat_t * pLat, Abc_SeqLat_t * pNext ) { pLat->pNext = pNext;                                                                              }
static inline void           Abc_SeqLatSetPrev( Abc_SeqLat_t * pLat, Abc_SeqLat_t * pPrev ) { Abc_InitType_t Init = Abc_SeqLatInit(pLat);  pLat->pPrev = pPrev;  Abc_SeqLatSetInit(pLat, Init); }

// accessing initial state datastructure
static inline Vec_Ptr_t *    Abc_SeqNodeInits( Abc_Obj_t * pObj )                                    { return ((Abc_SeqMan_t*)pObj->pNtk->pManFunc)->vInits;                           }
static inline Abc_SeqLat_t * Abc_SeqNodeReadInit( Abc_Obj_t * pObj, int Edge )                       { return Vec_PtrEntry( Abc_SeqNodeInits(pObj), (pObj->Id<<1)+Edge );              }
static inline void           Abc_SeqNodeSetInit ( Abc_Obj_t * pObj, int Edge, Abc_SeqLat_t * pInit ) { Vec_PtrWriteEntry( Abc_SeqNodeInits(pObj), (pObj->Id<<1)+Edge, pInit );         }
static inline Abc_SeqLat_t * Abc_SeqNodeCreateLat( Abc_Obj_t * pObj )                                { return (Abc_SeqLat_t *)Extra_MmFixedEntryFetch( ((Abc_SeqMan_t*)pObj->pNtk->pManFunc)->pMmInits );  }
static inline void           Abc_SeqNodeRecycleLat( Abc_Obj_t * pObj, Abc_SeqLat_t * pLat )          { Extra_MmFixedEntryRecycle( ((Abc_SeqMan_t*)pObj->pNtk->pManFunc)->pMmInits, (char *)pLat );         }

// getting the Lat with the given number
static inline Abc_SeqLat_t * Abc_SeqNodeGetLat( Abc_Obj_t * pObj, int Edge, int iLat )  
{
    int Counter;
    Abc_SeqLat_t * pLat = Abc_SeqNodeReadInit(pObj, Edge);  
    for ( Counter = 0; Counter != iLat; Counter++ )
        pLat = pLat->pNext;
    return pLat;
}
// getting the first Lat
static inline Abc_SeqLat_t * Abc_SeqNodeGetLatFirst( Abc_Obj_t * pObj, int Edge )  
{
    return Abc_SeqNodeReadInit(pObj, Edge);
}
// getting the last Lat
static inline Abc_SeqLat_t * Abc_SeqNodeGetLatLast( Abc_Obj_t * pObj, int Edge )  
{
    return Abc_SeqLatPrev( Abc_SeqNodeReadInit(pObj, Edge) );
}

// getting the init value of the given Lat on the edge
static inline Abc_InitType_t Abc_SeqNodeGetInitOne( Abc_Obj_t * pObj, int Edge, int iLat )             
{  
    return Abc_SeqLatInit( Abc_SeqNodeGetLat(pObj, Edge, iLat) );  
}
// geting the init value of the first Lat on the edge
static inline Abc_InitType_t Abc_SeqNodeGetInitFirst( Abc_Obj_t * pObj, int Edge )  
{
    return Abc_SeqLatInit( Abc_SeqNodeGetLatFirst(pObj, Edge) );  
}
// geting the init value of the last Lat on the edge
static inline Abc_InitType_t Abc_SeqNodeGetInitLast( Abc_Obj_t * pObj, int Edge )  
{
    return Abc_SeqLatInit( Abc_SeqNodeGetLatLast(pObj, Edge) );  
}


// setting the init value of the given Lat on the edge
static inline void Abc_SeqNodeSetInitOne( Abc_Obj_t * pObj, int Edge, int iLat, Abc_InitType_t Init )  
{
    Abc_SeqLatSetInit( Abc_SeqNodeGetLat(pObj, Edge, iLat), Init );  
}


// insert the first Lat on the edge
static inline void Abc_SeqNodeInsertFirst( Abc_Obj_t * pObj, int Edge, Abc_InitType_t Init )  
{ 
    Abc_SeqLat_t * pLat, * pRing, * pPrev;
    pLat  = Abc_SeqNodeCreateLat( pObj );
    pRing = Abc_SeqNodeReadInit( pObj, Edge );
    if ( pRing == NULL )
    {
        pLat->pNext = pLat->pPrev = pLat;
        Abc_SeqNodeSetInit( pObj, Edge, pLat );
    }
    else
    {
        Abc_SeqLatSetPrev( pRing, pLat );
        Abc_SeqLatSetNext( pLat, pRing );
        pPrev = Abc_SeqLatPrev( pRing );
        Abc_SeqLatSetPrev( pLat, pPrev );
        Abc_SeqLatSetNext( pPrev, pLat );
        Abc_SeqNodeSetInit( pObj, Edge, pLat );  // rotate the ring to make pLat the first
    }
    Abc_SeqLatSetInit( pLat, Init );
}

// insert the last Lat on the edge
static inline void Abc_SeqNodeInsertLast( Abc_Obj_t * pObj, int Edge, Abc_InitType_t Init )  
{ 
    Abc_SeqLat_t * pLat, * pRing, * pPrev;
    pLat  = Abc_SeqNodeCreateLat( pObj );
    pRing = Abc_SeqNodeReadInit( pObj, Edge );
    if ( pRing == NULL )
    {
        pLat->pNext = pLat->pPrev = pLat;
        Abc_SeqNodeSetInit( pObj, Edge, pLat );
    }
    else
    {
        Abc_SeqLatSetPrev( pRing, pLat );
        Abc_SeqLatSetNext( pLat, pRing );
        pPrev = Abc_SeqLatPrev( pRing );
        Abc_SeqLatSetPrev( pLat, pPrev );
        Abc_SeqLatSetNext( pPrev, pLat );
    }
    Abc_SeqLatSetInit( pLat, Init );
}

// delete the first Lat on the edge
static inline Abc_InitType_t Abc_SeqNodeDeleteFirst( Abc_Obj_t * pObj, int Edge )  
{ 
    Abc_SeqLat_t * pLat, * pRing, * pPrev, * pNext;
    pRing = Abc_SeqNodeReadInit( pObj, Edge );
    pLat  = pRing; // consider the first latch
    if ( pLat->pNext == pLat )
        Abc_SeqNodeSetInit( pObj, Edge, NULL );
    else
    {
        pPrev = Abc_SeqLatPrev( pLat );
        pNext = Abc_SeqLatNext( pLat );
        Abc_SeqLatSetPrev( pNext, pPrev );
        Abc_SeqLatSetNext( pPrev, pNext );
        Abc_SeqNodeSetInit( pObj, Edge, pNext ); // rotate the ring
    }
    Abc_SeqNodeRecycleLat( pObj, pLat );
}

// delete the last Lat on the edge
static inline Abc_InitType_t Abc_SeqNodeDeleteLast( Abc_Obj_t * pObj, int Edge )  
{
    Abc_SeqLat_t * pLat, * pRing, * pPrev, * pNext;
    pRing = Abc_SeqNodeReadInit( pObj, Edge );
    pLat  = Abc_SeqLatPrev( pRing ); // consider the last latch
    if ( pLat->pNext == pLat )
        Abc_SeqNodeSetInit( pObj, Edge, NULL );
    else
    {
        pPrev = Abc_SeqLatPrev( pLat );
        pNext = Abc_SeqLatNext( pLat );
        Abc_SeqLatSetPrev( pNext, pPrev );
        Abc_SeqLatSetNext( pPrev, pNext );
    }
    Abc_SeqNodeRecycleLat( pObj, pLat ); 
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_SeqMan_t * Abc_SeqCreate( int nMaxId )
{
    Abc_SeqMan_t * p;
    // start the manager
    p = ALLOC( Abc_SeqMan_t, 1 );
    memset( p, 0, sizeof(Abc_SeqMan_t) );
    p->nSize = nMaxId + 1;
    // create internal data structures
    p->vInits = Vec_PtrStart( 2 * p->nSize ); 
    p->pMmInits = Extra_MmFixedStart( sizeof(Abc_SeqLat_t) );
    return p;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


