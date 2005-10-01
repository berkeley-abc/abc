/**CFile****************************************************************

  FileName    [cutList.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Implementation of layered listed list of cuts.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cutList.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __CUT_LIST_H__
#define __CUT_LIST_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Cut_ListStruct_t_         Cut_List_t;
struct Cut_ListStruct_t_
{
    Cut_Cut_t *  pHead[CUT_SIZE_MAX+1];
    Cut_Cut_t ** ppTail[CUT_SIZE_MAX+1];
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Start the cut list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cut_ListStart( Cut_List_t * p )
{
    int i;
    for ( i = 1; i <= CUT_SIZE_MAX; i++ )
    {
        p->pHead[i] = 0;
        p->ppTail[i] = &p->pHead[i];
    }
}

/**Function*************************************************************

  Synopsis    [Adds one cut to the cut list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cut_ListAdd( Cut_List_t * p, Cut_Cut_t * pCut )
{
    assert( pCut->nLeaves > 0 && pCut->nLeaves <= CUT_SIZE_MAX );
    *p->ppTail[pCut->nLeaves] = pCut;
    p->ppTail[pCut->nLeaves] = &pCut->pNext;
}

/**Function*************************************************************

  Synopsis    [Adds one cut to the cut list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cut_ListDerive( Cut_List_t * p, Cut_Cut_t * pList )
{
    Cut_Cut_t * pPrev;
    int nLeaves;
    Cut_ListStart( p );
    while ( pList != NULL )
    {
        nLeaves = pList->nLeaves;
        p->pHead[nLeaves] = pList;
        for ( pPrev = pList, pList = pList->pNext; pList; pPrev = pList, pList = pList->pNext )
            if ( nLeaves < (int)pList->nLeaves )
                break;
        p->ppTail[nLeaves] = &pPrev->pNext;
        pPrev->pNext = NULL;
    }
}

/**Function*************************************************************

  Synopsis    [Adds the second list to the first list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cut_ListAddList( Cut_List_t * pOld, Cut_List_t * pNew )
{
    int i;
    for ( i = 1; i <= CUT_SIZE_MAX; i++ )
    {
        if ( pNew->pHead[i] == NULL )
            continue;
        *pOld->ppTail[i] = pNew->pHead[i];
        pOld->ppTail[i] = pNew->ppTail[i];
    }
}

/**Function*************************************************************

  Synopsis    [Returns the cut list linked into one sequence of cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Cut_Cut_t * Cut_ListFinish( Cut_List_t * p )
{
    Cut_Cut_t * pHead = NULL, ** ppTail = &pHead;
    int i;
    for ( i = 1; i < CUT_SIZE_MAX; i++ )
    {
        if ( p->pHead[i] == NULL )
            continue;
        *ppTail = p->pHead[i];
        ppTail = p->ppTail[i];
    }
    *ppTail = NULL;
    return pHead;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

