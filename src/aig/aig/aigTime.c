/**CFile****************************************************************

  FileName    [aigTime.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Representation of timing information.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigTime.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Aig_TBox_t_           Aig_TBox_t;
typedef struct Aig_TObj_t_           Aig_TObj_t;

// timing manager
struct Aig_TMan_t_
{
    Vec_Ptr_t *      vBoxes;         // the timing boxes
    Aig_MmFlex_t *   pMemObj;        // memory manager for boxes
    int              nTravIds;       // traversal ID of the manager
    int              nPis;           // the number of PIs
    int              nPos;           // the number of POs
    Aig_TObj_t *     pPis;           // timing info for the PIs
    Aig_TObj_t *     pPos;           // timing info for the POs
};

// timing box
struct Aig_TBox_t_
{
    int              iBox;           // the unique ID of this box
    int              TravId;         // traversal ID of this box
    int              nInputs;        // the number of box inputs 
    int              nOutputs;       // the number of box outputs
    int              Inouts[0];      // the int numbers of PIs and POs
};

// timing object
struct Aig_TObj_t_
{
    int              iObj2Box;       // mapping of the object into its box
    float            timeOffset;     // the static timing of the node
    float            timeActual;     // the actual timing of the node
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
Aig_TMan_t * Aig_TManStart( int nPis, int nPos )
{
    Aig_TMan_t * p;
    int i;
    p = ALLOC( Aig_TMan_t, 1 );
    memset( p, 0, sizeof(Aig_TMan_t) );
    p->pMemObj = Aig_MmFlexStart();
    p->vBoxes  = Vec_PtrAlloc( 100 );
    Vec_PtrPush( p->vBoxes, NULL );
    p->nPis = nPis;
    p->nPos = nPos;
    p->pPis = ALLOC( Aig_TObj_t, nPis );
    memset( p->pPis, 0, sizeof(Aig_TObj_t) * nPis );
    p->pPos = ALLOC( Aig_TObj_t, nPos );
    memset( p->pPos, 0, sizeof(Aig_TObj_t) * nPos );
    for ( i = 0; i < nPis; i++ )
        p->pPis[i].iObj2Box = -1;
    for ( i = 0; i < nPos; i++ )
        p->pPos[i].iObj2Box = -1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the network manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TManStop( Aig_TMan_t * p )
{
    Vec_PtrFree( p->vBoxes );
    Aig_MmFlexStop( p->pMemObj, 0 );
    free( p->pPis );
    free( p->pPos );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TManCreateBox( Aig_TMan_t * p, int * pPis, int nPis, int * pPos, int nPos, float * pPiTimes, float * pPoTimes )
{
    Aig_TBox_t * pBox;
    int i;
    pBox = (Aig_TBox_t *)Aig_MmFlexEntryFetch( p->pMemObj, sizeof(Aig_TBox_t) + sizeof(int) * (nPis+nPos) );
    memset( pBox, 0, sizeof(Aig_TBox_t) );
    pBox->iBox = Vec_PtrSize( p->vBoxes );
    Vec_PtrPush( p->vBoxes, pBox );
    pBox->nInputs = nPis;
    pBox->nOutputs = nPos;
    for ( i = 0; i < nPis; i++ )
    {
        assert( pPis[i] < p->nPis );
        pBox->Inouts[i] = pPis[i];
        Aig_TManSetPiArrival( p, pPis[i], pPiTimes[i] );
        p->pPis[pPis[i]].iObj2Box = pBox->iBox;
    }
    for ( i = 0; i < nPos; i++ )
    {
        assert( pPos[i] < p->nPos );
        pBox->Inouts[nPis+i] = pPos[i];
        Aig_TManSetPoRequired( p, pPos[i], pPoTimes[i] );
        p->pPos[pPos[i]].iObj2Box = pBox->iBox;
    }
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TManSetPiDelay( Aig_TMan_t * p, int iPi, float Delay )
{
    assert( iPi < p->nPis );
    p->pPis[iPi].timeActual = Delay;
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TManSetPoDelay( Aig_TMan_t * p, int iPo, float Delay )
{
    assert( iPo < p->nPos );
    p->pPos[iPo].timeActual = Delay;
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TManSetPiArrival( Aig_TMan_t * p, int iPi, float Delay )
{
    assert( iPi < p->nPis );
    p->pPis[iPi].timeOffset = Delay;
}

/**Function*************************************************************

  Synopsis    [Creates the new timing box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TManSetPoRequired( Aig_TMan_t * p, int iPo, float Delay )
{
    assert( iPo < p->nPos );
    p->pPos[iPo].timeOffset = Delay;
}

/**Function*************************************************************

  Synopsis    [Increments the trav ID of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TManIncrementTravId( Aig_TMan_t * p )
{
    p->nTravIds++;
}

/**Function*************************************************************

  Synopsis    [Returns PI arrival time.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Aig_TManGetPiArrival( Aig_TMan_t * p, int iPi )
{
    Aig_TBox_t * pBox;
    Aig_TObj_t * pObj;
    float DelayMax;
    int i;
    assert( iPi < p->nPis );
    if ( p->pPis[iPi].iObj2Box < 0 )
        return p->pPis[iPi].timeOffset;
    pBox = Vec_PtrEntry( p->vBoxes, p->pPis[iPi].iObj2Box );
    // check if box timing is updated
    if ( pBox->TravId == p->nTravIds )
        return p->pPis[iPi].timeOffset;
    pBox->TravId = p->nTravIds;
    // update box timing
    DelayMax = -1.0e+20F;
    for ( i = 0; i < pBox->nOutputs; i++ )
    {
        pObj = p->pPos + pBox->Inouts[pBox->nInputs+i];
        DelayMax = AIG_MAX( DelayMax, pObj->timeActual + pObj->timeOffset );
    }
    for ( i = 0; i < pBox->nInputs; i++ )
    {
        pObj = p->pPis + pBox->Inouts[i];
        pObj->timeActual = DelayMax + pObj->timeOffset;
    }
    return p->pPis[iPi].timeActual;
}

/**Function*************************************************************

  Synopsis    [Returns PO required time.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Aig_TManGetPoRequired( Aig_TMan_t * p, int iPo )
{
    return 0.0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


