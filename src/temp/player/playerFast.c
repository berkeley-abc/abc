/**CFile****************************************************************

  FileName    [playerFast.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [PLA decomposition package.]

  Synopsis    [Fast 8-LUT mapper.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: playerFast.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "player.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ivy_SuppMan_t_ Ivy_SuppMan_t;
struct Ivy_SuppMan_t_ 
{
    int    nLimit;    // the limit on the number of inputs
    int    nObjs;     // the number of entries
    int    nSize;     // size of each entry in bytes
    char * pMem;      // memory allocated
};

typedef struct Ivy_Supp_t_ Ivy_Supp_t;
struct Ivy_Supp_t_ 
{
    char  nSize;      // the number of support nodes
    char  fMark;      // the node was processed for area counting
    short Delay;      // the delay of the node
    int   pArray[0];  // the support nodes
};

static inline Ivy_Supp_t * Ivy_ObjSupp( Ivy_Man_t * pAig, Ivy_Obj_t * pObj )      
{ 
    return (Ivy_Supp_t *)(((Ivy_SuppMan_t*)pAig->pData)->pMem + pObj->Id * ((Ivy_SuppMan_t*)pAig->pData)->nSize); 
}
static inline Ivy_Supp_t * Ivy_ObjSuppStart( Ivy_Man_t * pAig, Ivy_Obj_t * pObj ) 
{ 
    Ivy_Supp_t * pSupp;
    pSupp = Ivy_ObjSupp( pAig, pObj );
    pSupp->fMark = 0;
    pSupp->Delay = 0;
    pSupp->nSize = 1;
    pSupp->pArray[0] = pObj->Id;
    return pSupp;
}

static int  Pla_ManFastLutMapDelay( Ivy_Man_t * pAig );
static int  Pla_ManFastLutMapArea( Ivy_Man_t * pAig );
static void Pla_ManFastLutMapNode( Ivy_Man_t * pAig, Ivy_Obj_t * pObj, int nLimit );
static int  Pla_ManFastLutMapMerge( Ivy_Supp_t * pSupp0, Ivy_Supp_t * pSupp1, Ivy_Supp_t * pSupp, int nLimit );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs fast K-LUT mapping of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pla_ManFastLutMap( Ivy_Man_t * pAig, int nLimit )
{
    Ivy_SuppMan_t * pMan;
    Ivy_Obj_t * pObj;
    int i, Delay, Area;
    int clk = clock(), clk2;
    // start the memory for supports
    pMan = ALLOC( Ivy_SuppMan_t, 1 );
    memset( pMan, 0, sizeof(Ivy_SuppMan_t) );
    pMan->nLimit = nLimit;
    pMan->nObjs  = Ivy_ManObjIdMax(pAig) + 1;
    pMan->nSize  = sizeof(Ivy_Supp_t) + nLimit * sizeof(int);
    pMan->pMem   = (char *)malloc( pMan->nObjs * pMan->nSize );
    pAig->pData  = pMan;
clk2 = clock();
    // set the PI mapping
    Ivy_ObjSuppStart( pAig, Ivy_ManConst1(pAig) );
    Ivy_ManForEachPi( pAig, pObj, i )
        Ivy_ObjSuppStart( pAig, pObj );
    // iterate through all nodes in the topological order
    Ivy_ManForEachNode( pAig, pObj, i )
        Pla_ManFastLutMapNode( pAig, pObj, nLimit );
    // find the best arrival time and area
    Delay = Pla_ManFastLutMapDelay( pAig );
    Area  = Pla_ManFastLutMapArea( pAig );
clk2 = clock() - clk2;
    // print the report
    printf( "LUT levels = %3d. LUT number = %6d. ", Delay, Area );
    PRT( "Mapping time", clk2 );
//    PRT( "Total", clock() - clk );
//    Pla_ManFastLutMapStop( pAig );
}

/**Function*************************************************************

  Synopsis    [Cleans memory used for decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pla_ManFastLutMapStop( Ivy_Man_t * pAig )
{
    free( ((Ivy_SuppMan_t*)pAig->pData)->pMem );
    free( pAig->pData );
    pAig->pData = NULL;
}

/**Function*************************************************************

  Synopsis    [Computes delay after LUT mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pla_ManFastLutMapDelay( Ivy_Man_t * pAig )
{
    Ivy_Supp_t * pSupp;
    Ivy_Obj_t * pObj;
    int i, DelayMax = 0;
    Ivy_ManForEachPo( pAig, pObj, i )
    {
        pObj = Ivy_ObjFanin0(pObj);
        if ( !Ivy_ObjIsNode(pObj) )
            continue;
        pSupp = Ivy_ObjSupp( pAig, pObj );
        if ( DelayMax < pSupp->Delay )
            DelayMax = pSupp->Delay;
    }
    return DelayMax;
}

/**Function*************************************************************

  Synopsis    [Computes area after mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pla_ManFastLutMapArea_rec( Ivy_Man_t * pAig, Ivy_Obj_t * pObj )
{
    Ivy_Supp_t * pSupp;
    int i, Counter;
    pSupp = Ivy_ObjSupp( pAig, pObj );
    // skip visited nodes and PIs
    if ( pSupp->fMark || pSupp->nSize == 1 )
        return 0;
    pSupp->fMark = 1;
    // compute the area of this node
    Counter = 0;
    for ( i = 0; i < pSupp->nSize; i++ )
        Counter += Pla_ManFastLutMapArea_rec( pAig, Ivy_ManObj(pAig, pSupp->pArray[i]) );
    return 1 + Counter;
}

/**Function*************************************************************

  Synopsis    [Computes area after mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pla_ManFastLutMapArea( Ivy_Man_t * pAig )
{
    Ivy_Obj_t * pObj;
    int i, Counter = 0;
    Ivy_ManForEachPo( pAig, pObj, i )
        Counter += Pla_ManFastLutMapArea_rec( pAig, Ivy_ObjFanin0(pObj) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Performs fast mapping for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pla_ManFastLutMapNode( Ivy_Man_t * pAig, Ivy_Obj_t * pObj, int nLimit )
{
    Ivy_Supp_t * pSupp0, * pSupp1, * pSupp;
    int RetValue;
    assert( Ivy_ObjIsNode(pObj) );
    // get the supports
    pSupp0 = Ivy_ObjSupp( pAig, Ivy_ObjFanin0(pObj) );
    pSupp1 = Ivy_ObjSupp( pAig, Ivy_ObjFanin1(pObj) );
    pSupp  = Ivy_ObjSupp( pAig, pObj );
    pSupp->fMark = 0;
    // get the delays
    if ( pSupp0->Delay == pSupp1->Delay )
        pSupp->Delay = (pSupp0->Delay == 0) ? pSupp0->Delay + 1: pSupp0->Delay;
    else if ( pSupp0->Delay > pSupp1->Delay )
    {
        pSupp->Delay = pSupp0->Delay;
        pSupp1 = Ivy_ObjSupp( pAig, Ivy_ManConst1(pAig) );
        pSupp1->pArray[0] = Ivy_ObjFaninId1(pObj);
    }
    else // if ( pSupp0->Delay < pSupp1->Delay )
    {
        pSupp->Delay = pSupp1->Delay;
        pSupp0 = Ivy_ObjSupp( pAig, Ivy_ManConst1(pAig) );
        pSupp0->pArray[0] = Ivy_ObjFaninId0(pObj);
    }
    // merge the cuts
    if ( pSupp0->nSize < pSupp1->nSize )
        RetValue = Pla_ManFastLutMapMerge( pSupp1, pSupp0, pSupp, nLimit );
    else
        RetValue = Pla_ManFastLutMapMerge( pSupp0, pSupp1, pSupp, nLimit );
    if ( !RetValue )
    {
        pSupp->Delay++;
        pSupp->nSize = 2;
        pSupp->pArray[0] = Ivy_ObjFaninId0(pObj);
        pSupp->pArray[1] = Ivy_ObjFaninId1(pObj);
    }
    assert( pSupp->Delay > 0 );
}

/**Function*************************************************************

  Synopsis    [Merges two supports]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pla_ManFastLutMapMerge( Ivy_Supp_t * pSupp0, Ivy_Supp_t * pSupp1, Ivy_Supp_t * pSupp, int nLimit )
{ 
    int i, k, c;
    assert( pSupp0->nSize >= pSupp1->nSize );
    // the case of the largest cut sizes
    if ( pSupp0->nSize == nLimit && pSupp1->nSize == nLimit )
    {
        for ( i = 0; i < pSupp0->nSize; i++ )
            if ( pSupp0->pArray[i] != pSupp1->pArray[i] )
                return 0;
        for ( i = 0; i < pSupp0->nSize; i++ )
            pSupp->pArray[i] = pSupp0->pArray[i];
        pSupp->nSize = pSupp0->nSize;
        return 1;
    }
    // the case when one of the cuts is the largest
    if ( pSupp0->nSize == nLimit )
    {
        for ( i = 0; i < pSupp1->nSize; i++ )
        {
            for ( k = pSupp0->nSize - 1; k >= 0; k-- )
                if ( pSupp0->pArray[k] == pSupp1->pArray[i] )
                    break;
            if ( k == -1 ) // did not find
                return 0;
        }
        for ( i = 0; i < pSupp0->nSize; i++ )
            pSupp->pArray[i] = pSupp0->pArray[i];
        pSupp->nSize = pSupp0->nSize;
        return 1;
    }

    // compare two cuts with different numbers
    i = k = 0;
    for ( c = 0; c < nLimit; c++ )
    {
        if ( k == pSupp1->nSize )
        {
            if ( i == pSupp0->nSize )
            {
                pSupp->nSize = c;
                return 1;
            }
            pSupp->pArray[c] = pSupp0->pArray[i++];
            continue;
        }
        if ( i == pSupp0->nSize )
        {
            if ( k == pSupp1->nSize )
            {
                pSupp->nSize = c;
                return 1;
            }
            pSupp->pArray[c] = pSupp1->pArray[k++];
            continue;
        }
        if ( pSupp0->pArray[i] < pSupp1->pArray[k] )
        {
            pSupp->pArray[c] = pSupp0->pArray[i++];
            continue;
        }
        if ( pSupp0->pArray[i] > pSupp1->pArray[k] )
        {
            pSupp->pArray[c] = pSupp1->pArray[k++];
            continue;
        }
        pSupp->pArray[c] = pSupp0->pArray[i++]; 
        k++;
    }
    if ( i < pSupp0->nSize || k < pSupp1->nSize )
        return 0;
    pSupp->nSize = c;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Creates integer vector with the support of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pla_ManFastLutMapReadSupp( Ivy_Man_t * pAig, Ivy_Obj_t * pObj, Vec_Int_t * vLeaves )
{
    Ivy_Supp_t * pSupp;
    pSupp = Ivy_ObjSupp( pAig, pObj );
    vLeaves->nCap   = 8;
    vLeaves->nSize  = pSupp->nSize;
    vLeaves->pArray = pSupp->pArray;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


