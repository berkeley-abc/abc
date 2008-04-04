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
    Mem_Flex_t *     pMemObj;        // memory manager for boxes
    int              nTravIds;       // traversal ID of the manager
    int              fUseTravId;     // enables the use of traversal ID
    int              nCis;           // the number of PIs
    int              nCos;           // the number of POs
    Tim_Obj_t *      pCis;           // timing info for the PIs
    Tim_Obj_t *      pCos;           // timing info for the POs
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
    int              Id;             // the ID of this object
    int              TravId;         // traversal ID of this object
    int              iObj2Box;       // mapping of the object into its box
    int              iObj2Num;       // mapping of the object into its number in the box
    float            timeArr;        // arrival time of the object
    float            timeReq;        // required time of the object
};

static inline Tim_Obj_t * Tim_ManCi( Tim_Man_t * p, int i )                           { assert( i < p->nCis ); return p->pCis + i;    }
static inline Tim_Obj_t * Tim_ManCo( Tim_Man_t * p, int i )                           { assert( i < p->nCos ); return p->pCos + i;    }
static inline Tim_Box_t * Tim_ManBox( Tim_Man_t * p, int i )                          { return Vec_PtrEntry(p->vBoxes, i);            }

static inline Tim_Box_t * Tim_ManCiBox( Tim_Man_t * p, int i )                        { return Tim_ManCi(p,i)->iObj2Box < 0 ? NULL : Vec_PtrEntry( p->vBoxes, Tim_ManCi(p,i)->iObj2Box ); }
static inline Tim_Box_t * Tim_ManCoBox( Tim_Man_t * p, int i )                        { return Tim_ManCo(p,i)->iObj2Box < 0 ? NULL : Vec_PtrEntry( p->vBoxes, Tim_ManCo(p,i)->iObj2Box ); }

static inline Tim_Obj_t * Tim_ManBoxInput( Tim_Man_t * p, Tim_Box_t * pBox, int i )   { assert( i < pBox->nInputs  ); return p->pCos + pBox->Inouts[i];               }
static inline Tim_Obj_t * Tim_ManBoxOutput( Tim_Man_t * p, Tim_Box_t * pBox, int i )  { assert( i < pBox->nOutputs ); return p->pCis + pBox->Inouts[pBox->nInputs+i]; }

#define Tim_ManBoxForEachInput( p, pBox, pObj, i )                               \
    for ( i = 0; (i < (pBox)->nInputs) && ((pObj) = Tim_ManBoxInput(p, pBox, i)); i++ )
#define Tim_ManBoxForEachOutput( p, pBox, pObj, i )                              \
    for ( i = 0; (i < (pBox)->nOutputs) && ((pObj) = Tim_ManBoxOutput(p, pBox, i)); i++ )

#define Tim_ManForEachCi( p, pObj, i )                                           \
    for ( i = 0; (i < (p)->nCis) && ((pObj) = (p)->pCis + i); i++ )              \
        if ( pObj->iObj2Box >= 0 ) {} else 
#define Tim_ManForEachCo( p, pObj, i )                                           \
    for ( i = 0; (i < (p)->nCos) && ((pObj) = (p)->pCos + i); i++ )              \
        if ( pObj->iObj2Box >= 0 ) {} else 
#define Tim_ManForEachBox( p, pBox, i )                                          \
    Vec_PtrForEachEntry( p->vBoxes, pBox, i )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Tim_Man_t * Tim_ManStart( int nCis, int nCos )
{
    Tim_Man_t * p;
    int i;
    p = ALLOC( Tim_Man_t, 1 );
    memset( p, 0, sizeof(Tim_Man_t) );
    p->pMemObj = Mem_FlexStart();
    p->vBoxes  = Vec_PtrAlloc( 100 );
    p->nCis = nCis;
    p->nCos = nCos;
    p->pCis = ALLOC( Tim_Obj_t, nCis );
    memset( p->pCis, 0, sizeof(Tim_Obj_t) * nCis );
    p->pCos = ALLOC( Tim_Obj_t, nCos );
    memset( p->pCos, 0, sizeof(Tim_Obj_t) * nCos );
    for ( i = 0; i < nCis; i++ )
    {
        p->pCis[i].Id = i;
        p->pCis[i].iObj2Box = p->pCis[i].iObj2Num = -1;
        p->pCis[i].timeReq = TIM_ETERNITY;
        p->pCis[i].timeArr = 0.0;
        p->pCis[i].TravId = 0;
    }
    for ( i = 0; i < nCos; i++ )
    {
        p->pCos[i].Id = i;
        p->pCos[i].iObj2Box = p->pCos[i].iObj2Num = -1;
        p->pCos[i].timeReq = TIM_ETERNITY;
        p->pCos[i].timeArr = 0.0;
        p->pCos[i].TravId = 0;
    }
    p->fUseTravId = 1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicates the timing manager.]

  Description [Derives discrete-delay-model timing manager. 
  Useful for AIG optimization with approximate timing information.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Tim_Man_t * Tim_ManDup( Tim_Man_t * p, int fDiscrete )
{
    Tim_Man_t * pNew;
    Tim_Box_t * pBox;
    float * pDelayTableNew;
    int i, k;
    pNew = Tim_ManStart( p->nCis, p->nCos );
    memcpy( pNew->pCis, p->pCis, sizeof(Tim_Obj_t) * p->nCis );
    memcpy( pNew->pCos, p->pCos, sizeof(Tim_Obj_t) * p->nCos );
    for ( k = 0; k < p->nCis; k++ )
        pNew->pCis[k].TravId = 0;
    for ( k = 0; k < p->nCos; k++ )
        pNew->pCos[k].TravId = 0;
    if ( fDiscrete )
    {
        for ( k = 0; k < p->nCis; k++ )
            pNew->pCis[k].timeArr = 0.0; // modify here
        // modify the required times
    }
    pNew->vDelayTables = Vec_PtrAlloc( 100 );
    Tim_ManForEachBox( p, pBox, i )
    {
        pDelayTableNew = ALLOC( float, pBox->nInputs * pBox->nOutputs );
        Vec_PtrPush( pNew->vDelayTables, pDelayTableNew );
        if ( fDiscrete )
        {
            for ( k = 0; k < pBox->nInputs * pBox->nOutputs; k++ )
                pDelayTableNew[k] = 1.0; // modify here
        }
        else
            memcpy( pDelayTableNew, pBox->pDelayTable, sizeof(float) * pBox->nInputs * pBox->nOutputs );
        Tim_ManCreateBoxFirst( pNew, pBox->Inouts[0], pBox->nInputs, 
            pBox->Inouts[pBox->nInputs], pBox->nOutputs, pDelayTableNew );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the timing manager.]

  Description [Derives unit-delay-model timing manager. 
  Useful for levelizing the network.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Tim_Man_t * Tim_ManDupUnit( Tim_Man_t * p )
{
    Tim_Man_t * pNew;
    Tim_Box_t * pBox;
    float * pDelayTableNew;
    int i, k;
    pNew = Tim_ManStart( p->nCis, p->nCos );
    memcpy( pNew->pCis, p->pCis, sizeof(Tim_Obj_t) * p->nCis );
    memcpy( pNew->pCos, p->pCos, sizeof(Tim_Obj_t) * p->nCos );
    for ( k = 0; k < p->nCis; k++ )
    {
        pNew->pCis[k].TravId = 0;
        pNew->pCis[k].timeArr = 0.0; 
    }
    for ( k = 0; k < p->nCos; k++ )
        pNew->pCos[k].TravId = 0;
    pNew->vDelayTables = Vec_PtrAlloc( 100 );
    Tim_ManForEachBox( p, pBox, i )
    {
        pDelayTableNew = ALLOC( float, pBox->nInputs * pBox->nOutputs );
        Vec_PtrPush( pNew->vDelayTables, pDelayTableNew );
        for ( k = 0; k < pBox->nInputs * pBox->nOutputs; k++ )
            pDelayTableNew[k] = 1.0;
        Tim_ManCreateBoxFirst( pNew, pBox->Inouts[0], pBox->nInputs, 
            pBox->Inouts[pBox->nInputs], pBox->nOutputs, pDelayTableNew );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the timing manager.]

  Description [Derives the approximate timing manager with realistic delays
  but without white-boxes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Tim_Man_t * Tim_ManDupApprox( Tim_Man_t * p )
{
    Tim_Man_t * pNew;
    int k;
    pNew = Tim_ManStart( p->nCis, p->nCos );
    for ( k = 0; k < p->nCis; k++ )
        if ( p->pCis[k].iObj2Box == -1 )
            pNew->pCis[k].timeArr = p->pCis[k].timeArr;
        else
            pNew->pCis[k].timeArr = p->pCis[k].timeReq;
    for ( k = 0; k < p->nCos; k++ )
        pNew->pCos[k].timeReq = p->pCos[k].timeReq;
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Stops the timing manager.]

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
    free( p->pCis );
    free( p->pCos );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Stops the timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManPrint( Tim_Man_t * p )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObj;
    int i;
    printf( "TIMING INFORMATION:\n" );
    Tim_ManForEachCi( p, pObj, i )
        printf( "pi%5d :  arr = %5.3f  req = %5.3f\n", i, pObj->timeArr, pObj->timeReq );
    Tim_ManForEachCo( p, pObj, i )
        printf( "po%5d :  arr = %5.3f  req = %5.3f\n", i, pObj->timeArr, pObj->timeReq );
    Tim_ManForEachBox( p, pBox, i )
    {
        printf( "*** Box %3d :  Ins = %d. Outs = %d.\n", i, pBox->nInputs, pBox->nOutputs );
        printf( "Delay table:" );
        for ( i = 0; i < pBox->nInputs * pBox->nOutputs; i++ )
            printf( " %5.3f", pBox->pDelayTable[i] );
        printf( "\n" );
        Tim_ManBoxForEachInput( p, pBox, pObj, i )
            printf( "box-inp%3d :  arr = %5.3f  req = %5.3f\n", i, pObj->timeArr, pObj->timeReq );
        Tim_ManBoxForEachOutput( p, pBox, pObj, i )
            printf( "box-out%3d :  arr = %5.3f  req = %5.3f\n", i, pObj->timeArr, pObj->timeReq );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Disables the use of the traversal ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManTravIdDisable( Tim_Man_t * p )
{
    p->fUseTravId = 0;
}

/**Function*************************************************************

  Synopsis    [Enables the use of the traversal ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManTravIdEnable( Tim_Man_t * p )
{
    p->fUseTravId = 1;
}

/**Function*************************************************************

  Synopsis    [Label box inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetCurrentTravIdBoxInputs( Tim_Man_t * p, int iBox )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObj;
    int i;
    pBox = Tim_ManBox( p, iBox );
    Tim_ManBoxForEachInput( p, pBox, pObj, i )
        pObj->TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Label box outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetCurrentTravIdBoxOutputs( Tim_Man_t * p, int iBox )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObj;
    int i;
    pBox = Tim_ManBox( p, iBox );
    Tim_ManBoxForEachOutput( p, pBox, pObj, i )
        pObj->TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Label box inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetPreviousTravIdBoxInputs( Tim_Man_t * p, int iBox )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObj;
    int i;
    pBox = Tim_ManBox( p, iBox );
    Tim_ManBoxForEachInput( p, pBox, pObj, i )
        pObj->TravId = p->nTravIds - 1;
}

/**Function*************************************************************

  Synopsis    [Label box outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetPreviousTravIdBoxOutputs( Tim_Man_t * p, int iBox )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObj;
    int i;
    pBox = Tim_ManBox( p, iBox );
    Tim_ManBoxForEachOutput( p, pBox, pObj, i )
        pObj->TravId = p->nTravIds - 1;
}

/**Function*************************************************************

  Synopsis    [Updates required time of the PO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManIsCiTravIdCurrent( Tim_Man_t * p, int iCi )
{
    assert( iCi < p->nCis );
    assert( p->fUseTravId );
    return p->pCis[iCi].TravId == p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Updates required time of the PO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManIsCoTravIdCurrent( Tim_Man_t * p, int iCo )
{
    assert( iCo < p->nCos );
    assert( p->fUseTravId );
    return p->pCos[iCo].TravId == p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Sets the vector of timing tables associated with the manager.]

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
        assert( pIns[i] < p->nCos );
        pBox->Inouts[i] = pIns[i];
        p->pCos[pIns[i]].iObj2Box = pBox->iBox;
        p->pCos[pIns[i]].iObj2Num = i;
    }
    for ( i = 0; i < nOuts; i++ )
    {
        assert( pOuts[i] < p->nCis );
        pBox->Inouts[nIns+i] = pOuts[i];
        p->pCis[pOuts[i]].iObj2Box = pBox->iBox;
        p->pCis[pOuts[i]].iObj2Num = i;
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
        assert( firstIn+i < p->nCos );
        pBox->Inouts[i] = firstIn+i;
        p->pCos[firstIn+i].iObj2Box = pBox->iBox;
        p->pCos[firstIn+i].iObj2Num = i;
    }
    for ( i = 0; i < nOuts; i++ )
    {
        assert( firstOut+i < p->nCis );
        pBox->Inouts[nIns+i] = firstOut+i;
        p->pCis[firstOut+i].iObj2Box = pBox->iBox;
        p->pCis[firstOut+i].iObj2Num = i;
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
    int i;
    if ( p->nTravIds >= (1<<30)-1 )
    {
        p->nTravIds = 0;
        for ( i = 0; i < p->nCis; i++ )
            p->pCis[i].TravId = 0;
        for ( i = 0; i < p->nCos; i++ )
            p->pCos[i].TravId = 0;
    }
    assert( p->nTravIds < (1<<30)-1 );
    p->nTravIds++;
}

/**Function*************************************************************

  Synopsis    [Initializes arrival time of the PI.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManInitCiArrival( Tim_Man_t * p, int iCi, float Delay )
{
    assert( iCi < p->nCis );
    p->pCis[iCi].timeArr = Delay;
}

/**Function*************************************************************

  Synopsis    [Initializes required time of the PO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManInitCoRequired( Tim_Man_t * p, int iCo, float Delay )
{
    assert( iCo < p->nCos );
    p->pCos[iCo].timeReq = Delay;
}

/**Function*************************************************************

  Synopsis    [Updates required time of the PO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetCoArrival( Tim_Man_t * p, int iCo, float Delay )
{
    assert( iCo < p->nCos );
    assert( !p->fUseTravId || p->pCos[iCo].TravId != p->nTravIds );
    p->pCos[iCo].timeArr = Delay;
    p->pCos[iCo].TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Updates arrival time of the PI.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetCiRequired( Tim_Man_t * p, int iCi, float Delay )
{
    assert( iCi < p->nCis );
    assert( !p->fUseTravId || p->pCis[iCi].TravId != p->nTravIds );
    p->pCis[iCi].timeReq = Delay;
    p->pCis[iCi].TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Updates required time of the PO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetCoRequired( Tim_Man_t * p, int iCo, float Delay )
{
    assert( iCo < p->nCos );
    assert( !p->fUseTravId || p->pCos[iCo].TravId != p->nTravIds );
    p->pCos[iCo].timeReq = Delay;
    p->pCos[iCo].TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Sets the correct required times for all POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetCoRequiredAll( Tim_Man_t * p, float Delay )
{
    Tim_Obj_t * pObj;
    int i;
    Tim_ManForEachCo( p, pObj, i )
        Tim_ManSetCoRequired( p, i, Delay );
}


/**Function*************************************************************

  Synopsis    [Returns PI arrival time.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Tim_ManGetCiArrival( Tim_Man_t * p, int iCi )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObjThis, * pObj, * pObjRes;
    float * pDelays, DelayBest;
    int i, k;
    // consider the already processed PI
    pObjThis = Tim_ManCi( p, iCi );
    if ( p->fUseTravId && pObjThis->TravId == p->nTravIds )
        return pObjThis->timeArr;
    pObjThis->TravId = p->nTravIds;
    // consider the main PI
    pBox = Tim_ManCiBox( p, iCi );
    if ( pBox == NULL )
        return pObjThis->timeArr;
    // update box timing
    pBox->TravId = p->nTravIds;
    // get the arrival times of the inputs of the box (POs)
    if ( p->fUseTravId )
    Tim_ManBoxForEachInput( p, pBox, pObj, i )
        if ( pObj->TravId != p->nTravIds )
            printf( "Tim_ManGetCiArrival(): Input arrival times of the box are not up to date!\n" );
    // compute the arrival times for each output of the box (PIs)
    Tim_ManBoxForEachOutput( p, pBox, pObjRes, i )
    {
        pDelays = pBox->pDelayTable + i * pBox->nInputs;
        DelayBest = -TIM_ETERNITY;
        Tim_ManBoxForEachInput( p, pBox, pObj, k )
            DelayBest = AIG_MAX( DelayBest, pObj->timeArr + pDelays[k] );
        pObjRes->timeArr = DelayBest;
        pObjRes->TravId = p->nTravIds;
    }
    return pObjThis->timeArr;
}

/**Function*************************************************************

  Synopsis    [Returns PO required time.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Tim_ManGetCoRequired( Tim_Man_t * p, int iCo )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObjThis, * pObj, * pObjRes;
    float * pDelays, DelayBest;
    int i, k;
    // consider the already processed PO
    pObjThis = Tim_ManCo( p, iCo );
    if ( p->fUseTravId && pObjThis->TravId == p->nTravIds )
        return pObjThis->timeReq;
    pObjThis->TravId = p->nTravIds;
    // consider the main PO
    pBox = Tim_ManCoBox( p, iCo );
    if ( pBox == NULL )
        return pObjThis->timeReq;
    // update box timing
    pBox->TravId = p->nTravIds;
    // get the required times of the outputs of the box (PIs)
    if ( p->fUseTravId )
    Tim_ManBoxForEachOutput( p, pBox, pObj, i )
        if ( pObj->TravId != p->nTravIds )
            printf( "Tim_ManGetCoRequired(): Output required times of the box are not up to date!\n" );
    // compute the required times for each input of the box (POs)
    Tim_ManBoxForEachInput( p, pBox, pObjRes, i )
    {
        DelayBest = TIM_ETERNITY;
        Tim_ManBoxForEachOutput( p, pBox, pObj, k )
        {
            pDelays = pBox->pDelayTable + k * pBox->nInputs;
            DelayBest = AIG_MIN( DelayBest, pObj->timeReq - pDelays[i] );
        }
        pObjRes->timeReq = DelayBest;
        pObjRes->TravId = p->nTravIds;
    }
    return pObjThis->timeReq;
}

/**Function*************************************************************

  Synopsis    [Returns the box number for the given input.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManBoxForCi( Tim_Man_t * p, int iCi )
{
    if ( iCi >= p->nCis )
        return -1;
    return p->pCis[iCi].iObj2Box;
}

/**Function*************************************************************

  Synopsis    [Returns the box number for the given output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManBoxForCo( Tim_Man_t * p, int iCo )
{
    if ( iCo >= p->nCos )
        return -1;
    return p->pCos[iCo].iObj2Box;
}

/**Function*************************************************************

  Synopsis    [Returns the first input of the box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManBoxInputFirst( Tim_Man_t * p, int iBox )
{
    Tim_Box_t * pBox = Vec_PtrEntry( p->vBoxes, iBox );
    return pBox->Inouts[0];
}

/**Function*************************************************************

  Synopsis    [Returns the first input of the box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManBoxOutputFirst( Tim_Man_t * p, int iBox )
{
    Tim_Box_t * pBox = Vec_PtrEntry( p->vBoxes, iBox );
    return pBox->Inouts[pBox->nInputs];
}

/**Function*************************************************************

  Synopsis    [Returns the first input of the box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManBoxInputNum( Tim_Man_t * p, int iBox )
{
    Tim_Box_t * pBox = Vec_PtrEntry( p->vBoxes, iBox );
    return pBox->nInputs;
}

/**Function*************************************************************

  Synopsis    [Returns the first input of the box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManBoxOutputNum( Tim_Man_t * p, int iBox )
{
    Tim_Box_t * pBox = Vec_PtrEntry( p->vBoxes, iBox );
    return pBox->nOutputs;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


