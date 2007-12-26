/**CFile****************************************************************

  FileName    [tim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [A timing manager.]

  Synopsis    [Representation of timing information.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: tim.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "vec.h"
#include "mem.h"
#include "tim.h"

#define AIG_MIN(a,b)       (((a) < (b))? (a) : (b))
#define AIG_MAX(a,b)       (((a) > (b))? (a) : (b))
#define AIG_ABS(a)         (((a) >= 0)?  (a) :-(a))
#define AIG_INFINITY       (100000000)

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Tim_Box_t_           Tim_Box_t;
typedef struct Tim_Obj_t_           Tim_Obj_t;

// timing manager
struct Tim_Man_t_
{
    Vec_Ptr_t *      vBoxes;         // the timing boxes
    Vec_Ptr_t *      vDelayTables;   // pointers to the delay tables
    Mem_Flex_t *   pMemObj;        // memory manager for boxes
    int              nTravIds;       // traversal ID of the manager
    int              nPis;           // the number of PIs
    int              nPos;           // the number of POs
    Tim_Obj_t *      pPis;           // timing info for the PIs
    Tim_Obj_t *      pPos;           // timing info for the POs
};

// timing box
struct Tim_Box_t_
{
    int              iBox;           // the unique ID of this box
    int              TravId;         // traversal ID of this box
    int              nInputs;        // the number of box inputs (POs)
    int              nOutputs;       // the number of box outputs (PIs)
    float *          pDelayTable;    // delay for each input->output path
    int              Inouts[0];      // the int numbers of PIs and POs
};

// timing object
struct Tim_Obj_t_
{
    int              TravId;         // traversal ID of this object
    int              iObj2Box;       // mapping of the object into its box
    int              iObj2Num;       // mapping of the object into its number in the box
    float            timeArr;        // arrival time of the object
    float            timeReq;        // required time of the object
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the network manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Tim_Man_t * Tim_ManStart( int nPis, int nPos )
{
    Tim_Man_t * p;
    int i;
    p = ALLOC( Tim_Man_t, 1 );
    memset( p, 0, sizeof(Tim_Man_t) );
    p->pMemObj = Mem_FlexStart();
    p->vBoxes  = Vec_PtrAlloc( 100 );
    Vec_PtrPush( p->vBoxes, NULL );
    p->nPis = nPis;
    p->nPos = nPos;
    p->pPis = ALLOC( Tim_Obj_t, nPis );
    memset( p->pPis, 0, sizeof(Tim_Obj_t) * nPis );
    p->pPos = ALLOC( Tim_Obj_t, nPos );
    memset( p->pPos, 0, sizeof(Tim_Obj_t) * nPos );
    for ( i = 0; i < nPis; i++ )
        p->pPis[i].iObj2Box = p->pPis[i].iObj2Num = -1;
    for ( i = 0; i < nPos; i++ )
        p->pPos[i].iObj2Box = p->pPos[i].iObj2Num = -1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the network manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManStop( Tim_Man_t * p )
{
    float * pTable;
    int i;
    if ( p->vDelayTables )
    {
        Vec_PtrForEachEntry( p->vDelayTables, pTable, i )
            FREE( pTable );
        Vec_PtrFree( p->vDelayTables );
    }
    Vec_PtrFree( p->vBoxes );
    Mem_FlexStop( p->pMemObj, 0 );
    free( p->pPis );
    free( p->pPos );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Increments the trav ID of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetDelayTables( Tim_Man_t * p, Vec_Ptr_t * vDelayTables )
{
    assert( p->vDelayTables == NULL );
    p->vDelayTables = vDelayTables;
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManCreateBox( Tim_Man_t * p, int * pIns, int nIns, int * pOuts, int nOuts, float * pDelayTable )
{
    Tim_Box_t * pBox;
    int i;
    pBox = (Tim_Box_t *)Mem_FlexEntryFetch( p->pMemObj, sizeof(Tim_Box_t) + sizeof(int) * (nIns+nOuts) );
    memset( pBox, 0, sizeof(Tim_Box_t) );
    pBox->iBox = Vec_PtrSize( p->vBoxes );
    Vec_PtrPush( p->vBoxes, pBox );
    pBox->pDelayTable = pDelayTable;
    pBox->nInputs  = nIns;
    pBox->nOutputs = nOuts;
    for ( i = 0; i < nIns; i++ )
    {
        assert( pIns[i] < p->nPos );
        pBox->Inouts[i] = pIns[i];
        p->pPos[pIns[i]].iObj2Box = pBox->iBox;
        p->pPos[pIns[i]].iObj2Num = i;
    }
    for ( i = 0; i < nOuts; i++ )
    {
        assert( pOuts[i] < p->nPis );
        pBox->Inouts[nIns+i] = pOuts[i];
        p->pPis[pOuts[i]].iObj2Box = pBox->iBox;
        p->pPis[pOuts[i]].iObj2Num = i;
    }
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManCreateBoxFirst( Tim_Man_t * p, int firstIn, int nIns, int firstOut, int nOuts, float * pDelayTable )
{
    Tim_Box_t * pBox;
    int i;
    pBox = (Tim_Box_t *)Mem_FlexEntryFetch( p->pMemObj, sizeof(Tim_Box_t) + sizeof(int) * (nIns+nOuts) );
    memset( pBox, 0, sizeof(Tim_Box_t) );
    pBox->iBox = Vec_PtrSize( p->vBoxes );
    Vec_PtrPush( p->vBoxes, pBox );
    pBox->pDelayTable = pDelayTable;
    pBox->nInputs  = nIns;
    pBox->nOutputs = nOuts;
    for ( i = 0; i < nIns; i++ )
    {
        assert( firstIn+i < p->nPos );
        pBox->Inouts[i] = firstIn+i;
        p->pPos[firstIn+i].iObj2Box = pBox->iBox;
        p->pPos[firstIn+i].iObj2Num = i;
    }
    for ( i = 0; i < nOuts; i++ )
    {
        assert( firstOut+i < p->nPis );
        pBox->Inouts[nIns+i] = firstOut+i;
        p->pPis[firstOut+i].iObj2Box = pBox->iBox;
        p->pPis[firstOut+i].iObj2Num = i;
    }
}



/**Function*************************************************************

  Synopsis    [Increments the trav ID of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManIncrementTravId( Tim_Man_t * p )
{
    p->nTravIds++;
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManInitPiArrival( Tim_Man_t * p, int iPi, float Delay )
{
    assert( iPi < p->nPis );
    p->pPis[iPi].timeArr = Delay;
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManInitPoRequired( Tim_Man_t * p, int iPo, float Delay )
{
    assert( iPo < p->nPos );
    p->pPos[iPo].timeArr = Delay;
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetPoArrival( Tim_Man_t * p, int iPo, float Delay )
{
    assert( iPo < p->nPos );
    assert( p->pPos[iPo].TravId != p->nTravIds );
    p->pPos[iPo].timeArr = Delay;
    p->pPos[iPo].TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Returns PI arrival time.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Tim_ManGetPiArrival( Tim_Man_t * p, int iPi )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObj;
    float * pDelays;
    float DelayMax;
    int i, k;
    assert( iPi < p->nPis );
    if ( p->pPis[iPi].iObj2Box < 0 )
        return p->pPis[iPi].timeArr;
    pBox = Vec_PtrEntry( p->vBoxes, p->pPis[iPi].iObj2Box );
    // check if box timing is updated
    if ( pBox->TravId == p->nTravIds )
    {
        assert( pBox->TravId == p->nTravIds );
        return p->pPis[iPi].timeArr;
    }
    pBox->TravId = p->nTravIds;
    // update box timing
    // get the arrival times of the inputs of the box (POs)
    for ( i = 0; i < pBox->nInputs; i++ )
    {
        pObj = p->pPos + pBox->Inouts[i];
        if ( pObj->TravId != p->nTravIds )
            printf( "Tim_ManGetPiArrival(): PO arrival times of the box are not up to date!\n" );
    }
    // compute the required times for each output of the box (PIs)
    for ( i = 0; i < pBox->nOutputs; i++ )
    {
        pDelays = pBox->pDelayTable + i * pBox->nInputs;
        DelayMax = -AIG_INFINITY;
        for ( k = 0; k < pBox->nInputs; k++ )
        {
            pObj = p->pPos + pBox->Inouts[k];
            DelayMax = AIG_MAX( DelayMax, pObj->timeArr + pDelays[k] );
        }
        pObj = p->pPis + pBox->Inouts[pBox->nInputs+i];
        pObj->timeArr = DelayMax;
        pObj->TravId = p->nTravIds;
    }
    return p->pPis[iPi].timeArr;
}

/**Function*************************************************************

  Synopsis    [Returns PO required time.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetPiRequired( Tim_Man_t * p, int iPi, float Delay )
{
    assert( iPi < p->nPis );
    assert( p->pPis[iPi].TravId != p->nTravIds );
    p->pPis[iPi].timeReq = Delay;
    p->pPis[iPi].TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Returns PO required time.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Tim_ManGetPoRequired( Tim_Man_t * p, int iPo )
{
    return 0.0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


