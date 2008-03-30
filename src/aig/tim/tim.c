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
    Mem_Flex_t *     pMemObj;        // memory manager for boxes
    int              nTravIds;       // traversal ID of the manager
    int              fUseTravId;     // enables the use of traversal ID
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
    int              Id;             // the ID of this object
    int              TravId;         // traversal ID of this object
    int              iObj2Box;       // mapping of the object into its box
    int              iObj2Num;       // mapping of the object into its number in the box
    float            timeArr;        // arrival time of the object
    float            timeReq;        // required time of the object
};

static inline Tim_Obj_t * Tim_ManPi( Tim_Man_t * p, int i )                           { assert( i < p->nPis ); return p->pPis + i;    }
static inline Tim_Obj_t * Tim_ManPo( Tim_Man_t * p, int i )                           { assert( i < p->nPos ); return p->pPos + i;    }

static inline Tim_Box_t * Tim_ManPiBox( Tim_Man_t * p, int i )                        { return Tim_ManPi(p,i)->iObj2Box < 0 ? NULL : Vec_PtrEntry( p->vBoxes, Tim_ManPi(p,i)->iObj2Box ); }
static inline Tim_Box_t * Tim_ManPoBox( Tim_Man_t * p, int i )                        { return Tim_ManPo(p,i)->iObj2Box < 0 ? NULL : Vec_PtrEntry( p->vBoxes, Tim_ManPo(p,i)->iObj2Box ); }

static inline Tim_Obj_t * Tim_ManBoxInput( Tim_Man_t * p, Tim_Box_t * pBox, int i )   { assert( i < pBox->nInputs  ); return p->pPos + pBox->Inouts[i];               }
static inline Tim_Obj_t * Tim_ManBoxOutput( Tim_Man_t * p, Tim_Box_t * pBox, int i )  { assert( i < pBox->nOutputs ); return p->pPis + pBox->Inouts[pBox->nInputs+i]; }

#define Tim_ManBoxForEachInput( p, pBox, pObj, i )                               \
    for ( i = 0; (i < (pBox)->nInputs) && ((pObj) = Tim_ManBoxInput(p, pBox, i)); i++ )
#define Tim_ManBoxForEachOutput( p, pBox, pObj, i )                              \
    for ( i = 0; (i < (pBox)->nOutputs) && ((pObj) = Tim_ManBoxOutput(p, pBox, i)); i++ )

#define Tim_ManForEachPi( p, pObj, i )                                           \
    for ( i = 0; (i < (p)->nPis) && ((pObj) = (p)->pPis + i); i++ )              \
        if ( pObj->iObj2Box >= 0 ) {} else 
#define Tim_ManForEachPo( p, pObj, i )                                           \
    for ( i = 0; (i < (p)->nPos) && ((pObj) = (p)->pPos + i); i++ )              \
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
Tim_Man_t * Tim_ManStart( int nPis, int nPos )
{
    Tim_Man_t * p;
    int i;
    p = ALLOC( Tim_Man_t, 1 );
    memset( p, 0, sizeof(Tim_Man_t) );
    p->pMemObj = Mem_FlexStart();
    p->vBoxes  = Vec_PtrAlloc( 100 );
    p->nPis = nPis;
    p->nPos = nPos;
    p->pPis = ALLOC( Tim_Obj_t, nPis );
    memset( p->pPis, 0, sizeof(Tim_Obj_t) * nPis );
    p->pPos = ALLOC( Tim_Obj_t, nPos );
    memset( p->pPos, 0, sizeof(Tim_Obj_t) * nPos );
    for ( i = 0; i < nPis; i++ )
    {
        p->pPis[i].Id = i;
        p->pPis[i].iObj2Box = p->pPis[i].iObj2Num = -1;
        p->pPis[i].timeReq = AIG_INFINITY;
        p->pPis[i].timeArr = 0.0;
        p->pPis[i].TravId = 0;
    }
    for ( i = 0; i < nPos; i++ )
    {
        p->pPos[i].Id = i;
        p->pPos[i].iObj2Box = p->pPos[i].iObj2Num = -1;
        p->pPos[i].timeReq = AIG_INFINITY;
        p->pPos[i].timeArr = 0.0;
        p->pPos[i].TravId = 0;
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
    pNew = Tim_ManStart( p->nPis, p->nPos );
    memcpy( pNew->pPis, p->pPis, sizeof(Tim_Obj_t) * p->nPis );
    memcpy( pNew->pPos, p->pPos, sizeof(Tim_Obj_t) * p->nPos );
    for ( k = 0; k < p->nPis; k++ )
        pNew->pPis[k].TravId = 0;
    for ( k = 0; k < p->nPos; k++ )
        pNew->pPos[k].TravId = 0;
    if ( fDiscrete )
    {
        for ( k = 0; k < p->nPis; k++ )
            pNew->pPis[k].timeArr = 0.0; // modify here
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
    pNew = Tim_ManStart( p->nPis, p->nPos );
    memcpy( pNew->pPis, p->pPis, sizeof(Tim_Obj_t) * p->nPis );
    memcpy( pNew->pPos, p->pPos, sizeof(Tim_Obj_t) * p->nPos );
    for ( k = 0; k < p->nPis; k++ )
    {
        pNew->pPis[k].TravId = 0;
        pNew->pPis[k].timeArr = 0.0; 
    }
    for ( k = 0; k < p->nPos; k++ )
        pNew->pPos[k].TravId = 0;
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
    pNew = Tim_ManStart( p->nPis, p->nPos );
    for ( k = 0; k < p->nPis; k++ )
        if ( p->pPis[k].iObj2Box == -1 )
            pNew->pPis[k].timeArr = p->pPis[k].timeArr;
        else
            pNew->pPis[k].timeArr = p->pPis[k].timeReq;
    for ( k = 0; k < p->nPos; k++ )
        pNew->pPos[k].timeReq = p->pPos[k].timeReq;
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
    free( p->pPis );
    free( p->pPos );
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
    Tim_ManForEachPi( p, pObj, i )
        printf( "pi%5d :  arr = %5.3f  req = %5.3f\n", i, pObj->timeArr, pObj->timeReq );
    Tim_ManForEachPo( p, pObj, i )
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

  Synopsis    [Initializes arrival time of the PI.]

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

  Synopsis    [Initializes required time of the PO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManInitPoRequired( Tim_Man_t * p, int iPo, float Delay )
{
    assert( iPo < p->nPos );
    p->pPos[iPo].timeReq = Delay;
}

/**Function*************************************************************

  Synopsis    [Updates required time of the PO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetPoArrival( Tim_Man_t * p, int iPo, float Delay )
{
    assert( iPo < p->nPos );
    assert( !p->fUseTravId || p->pPos[iPo].TravId != p->nTravIds );
    p->pPos[iPo].timeArr = Delay;
    p->pPos[iPo].TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Updates arrival time of the PI.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetPiRequired( Tim_Man_t * p, int iPi, float Delay )
{
    assert( iPi < p->nPis );
    assert( !p->fUseTravId || p->pPis[iPi].TravId != p->nTravIds );
    p->pPis[iPi].timeReq = Delay;
    p->pPis[iPi].TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Updates required time of the PO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetPoRequired( Tim_Man_t * p, int iPo, float Delay )
{
    assert( iPo < p->nPos );
    assert( !p->fUseTravId || p->pPos[iPo].TravId != p->nTravIds );
    p->pPos[iPo].timeReq = Delay;
    p->pPos[iPo].TravId = p->nTravIds;
}

/**Function*************************************************************

  Synopsis    [Sets the correct required times for all POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetPoRequiredAll( Tim_Man_t * p, float Delay )
{
    Tim_Obj_t * pObj;
    int i;
    Tim_ManForEachPo( p, pObj, i )
        Tim_ManSetPoRequired( p, i, Delay );
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
    Tim_Obj_t * pObjThis, * pObj, * pObjRes;
    float * pDelays, DelayBest;
    int i, k;
    // consider the already processed PI
    pObjThis = Tim_ManPi( p, iPi );
    if ( p->fUseTravId && pObjThis->TravId == p->nTravIds )
        return pObjThis->timeArr;
    pObjThis->TravId = p->nTravIds;
    // consider the main PI
    pBox = Tim_ManPiBox( p, iPi );
    if ( pBox == NULL )
        return pObjThis->timeArr;
    // update box timing
    pBox->TravId = p->nTravIds;
    // get the arrival times of the inputs of the box (POs)
    if ( p->fUseTravId )
    Tim_ManBoxForEachInput( p, pBox, pObj, i )
        if ( pObj->TravId != p->nTravIds )
            printf( "Tim_ManGetPiArrival(): Input arrival times of the box are not up to date!\n" );
    // compute the arrival times for each output of the box (PIs)
    Tim_ManBoxForEachOutput( p, pBox, pObjRes, i )
    {
        pDelays = pBox->pDelayTable + i * pBox->nInputs;
        DelayBest = -AIG_INFINITY;
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
float Tim_ManGetPoRequired( Tim_Man_t * p, int iPo )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObjThis, * pObj, * pObjRes;
    float * pDelays, DelayBest;
    int i, k;
    // consider the already processed PO
    pObjThis = Tim_ManPo( p, iPo );
    if ( p->fUseTravId && pObjThis->TravId == p->nTravIds )
        return pObjThis->timeReq;
    pObjThis->TravId = p->nTravIds;
    // consider the main PO
    pBox = Tim_ManPoBox( p, iPo );
    if ( pBox == NULL )
        return pObjThis->timeReq;
    // update box timing
    pBox->TravId = p->nTravIds;
    // get the required times of the outputs of the box (PIs)
    if ( p->fUseTravId )
    Tim_ManBoxForEachOutput( p, pBox, pObj, i )
        if ( pObj->TravId != p->nTravIds )
            printf( "Tim_ManGetPoRequired(): Output required times of the box are not up to date!\n" );
    // compute the required times for each input of the box (POs)
    Tim_ManBoxForEachInput( p, pBox, pObjRes, i )
    {
        DelayBest = AIG_INFINITY;
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
    if ( iCi >= p->nPis )
        return -1;
    return p->pPis[iCi].iObj2Box;
}

/**Function*************************************************************

  Synopsis    [Returns the box number for the given output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManBoxForCo( Tim_Man_t * p, int iCo )
{
    if ( iCo >= p->nPos )
        return -1;
    return p->pPos[iCo].iObj2Box;
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


