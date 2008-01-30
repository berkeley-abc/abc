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
    Cut_Cut_t *  pHead[7];
    Cut_Cut_t ** ppTail[7];
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cut_ListStart( Cut_List_t * p )
{
    int i;
    for ( i = 1; i <= 6; i++ )
    {
        p->pHead[i] = 0;
        p->ppTail[i] = &p->pHead[i];
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cut_ListAdd( Cut_List_t * p, Cut_Cut_t * pCut )
{
    assert( pCut->nLeaves > 0 && pCut->nLeaves < 7 );
    *p->ppTail[pCut->nLeaves] = pCut;
    p->ppTail[pCut->nLeaves] = &pCut->pNext;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Cut_Cut_t * Cut_ListFinish( Cut_List_t * p )
{
    int i;
    for ( i = 1; i < 6; i++ )
        *p->ppTail[i] = p->pHead[i+1];
    *p->ppTail[6] = NULL;
    return p->pHead[1];
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

