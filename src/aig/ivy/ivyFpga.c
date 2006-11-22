/**CFile****************************************************************

  FileName    [ivyFpga.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Prepares the AIG package to work as an FPGA mapper.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyFpga.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"
#include "attr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ivy_FpgaMan_t_     Ivy_FpgaMan_t;
typedef struct Ivy_FpgaObj_t_     Ivy_FpgaObj_t;
typedef struct Ivy_FpgaCut_t_     Ivy_FpgaCut_t;

// manager
struct Ivy_FpgaMan_t_
{
    Ivy_Man_t *        pManIvy;       // the AIG manager
    Attr_Man_t *       pManAttr;      // the attribute manager
    int                nLutSize;      // the LUT size
    int                nCutsMax;      // the max number of cuts
    int                nEntrySize;    // the size of the entry
    int                nEntryBase;    // the size of the entry minus cut leaf arrays
    int                fVerbose;      // the verbosity flag
    // temporary cut storage
    Ivy_FpgaCut_t *    pCutStore;     // the temporary cuts
};

// priority cut
struct Ivy_FpgaCut_t_
{
    float              Delay;         // the delay of the cut
    float              AreaFlow;      // the area flow of the cut
    float              Area;          // the area of the cut
    int                nLeaves;       // the number of leaves
    int *              pLeaves;       // the array of fanins
};

// node extension
struct Ivy_FpgaObj_t_
{
    unsigned           Type   :  4;   // type
    unsigned           nCuts  : 28;   // the number of cuts
    int                Id;            // integer ID
    int                nRefs;         // the number of references
    Ivy_FpgaObj_t *    pFanin0;       // the first fanin 
    Ivy_FpgaObj_t *    pFanin1;       // the second fanin
    float              Required;      // required time of the onde
    Ivy_FpgaCut_t *    pCut;          // the best cut
    Ivy_FpgaCut_t      Cuts[0];       // the cuts of the node
};


static Ivy_FpgaMan_t * Ivy_ManFpgaPrepare( Ivy_Man_t * p, int nLutSize, int nCutsMax, int fVerbose );
static void Ivy_ManFpgaUndo( Ivy_FpgaMan_t * pFpga );
static void Ivy_ObjFpgaCreate( Ivy_FpgaMan_t * pFpga, int ObjId );
static void Ivy_ManFpgaDelay( Ivy_FpgaMan_t * pFpga );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManFpga( Ivy_Man_t * p, int nLutSize, int nCutsMax, int fVerbose )
{
    Ivy_FpgaMan_t * pFpga;
    pFpga = Ivy_ManFpgaPrepare( p, nLutSize, nCutsMax, fVerbose );
    Ivy_ManFpgaDelay( pFpga );
    Ivy_ManFpgaUndo( pFpga );
}

/**Function*************************************************************

  Synopsis    [Prepares manager for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_FpgaMan_t * Ivy_ManFpgaPrepare( Ivy_Man_t * p, int nLutSize, int nCutsMax, int fVerbose )
{
    Ivy_FpgaMan_t * pFpga;
    Ivy_Obj_t * pObj;
    int i;
    pFpga = ALLOC( Ivy_FpgaMan_t, 1 );
    memset( pFpga, 0, sizeof(Ivy_FpgaMan_t) );
    // compute the size of the node
    pFpga->pManIvy    = p;
    pFpga->nLutSize   = nLutSize; 
    pFpga->nCutsMax   = nCutsMax; 
    pFpga->fVerbose   = fVerbose;
    pFpga->nEntrySize = sizeof(Ivy_FpgaObj_t) + (nCutsMax + 1) * (sizeof(Ivy_FpgaCut_t) + sizeof(int) * nLutSize);
    pFpga->nEntryBase = sizeof(Ivy_FpgaObj_t) + (nCutsMax + 1) * (sizeof(Ivy_FpgaCut_t));
    pFpga->pManAttr   = Attr_ManStartPtrMem( Ivy_ManObjIdMax(p) + 1, pFpga->nEntrySize );
    if ( fVerbose )
        printf( "Entry size = %d. Total memory = %5.2f Mb.\n", pFpga->nEntrySize, 
            1.0 * pFpga->nEntrySize * (Ivy_ManObjIdMax(p) + 1) / (1<<20) );
    // connect memory for cuts
    Ivy_ManForEachObj( p, pObj, i )
        Ivy_ObjFpgaCreate( pFpga, pObj->Id );
    // create temporary cuts
    pFpga->pCutStore  = (Ivy_FpgaCut_t *)ALLOC( char, pFpga->nEntrySize * (nCutsMax + 1) * (nCutsMax + 1) );
    memset( pFpga->pCutStore, 0, pFpga->nEntrySize * (nCutsMax + 1) * (nCutsMax + 1) );
    {
        int i, * pArrays;
        pArrays = (int *)((char *)pFpga->pCutStore + sizeof(Ivy_FpgaCut_t) * (nCutsMax + 1) * (nCutsMax + 1));
        for ( i = 0; i < (nCutsMax + 1) * (nCutsMax + 1); i++ )
            pFpga->pCutStore[i].pLeaves = pArrays + i * pFpga->nLutSize;
    }
    return pFpga;
}

/**Function*************************************************************

  Synopsis    [Quits the manager for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManFpgaUndo( Ivy_FpgaMan_t * pFpga )
{
    Attr_ManStop( pFpga->pManAttr );
    free( pFpga );
}


/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ObjFpgaCreate( Ivy_FpgaMan_t * pFpga, int ObjId )
{
    Ivy_FpgaObj_t * pObjFpga;
    int i, * pArrays;
    pObjFpga = Attr_ManReadAttrPtr( pFpga->pManAttr, ObjId );
    pArrays = (int *)((char *)pObjFpga + pFpga->nEntryBase);
    for ( i = 0; i <= pFpga->nCutsMax; i++ )
        pObjFpga->Cuts[i].pLeaves = pArrays + i * pFpga->nLutSize;
}


/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ObjFpgaMerge( Ivy_FpgaCut_t * pC0, Ivy_FpgaCut_t * pC1, Ivy_FpgaCut_t * pC, int nLimit )
{
    int i, k, c;
    assert( pC0->nLeaves >= pC1->nLeaves );
    // the case of the largest cut sizes
    if ( pC0->nLeaves == nLimit && pC1->nLeaves == nLimit )
    {
        for ( i = 0; i < pC0->nLeaves; i++ )
            if ( pC0->pLeaves[i] != pC1->pLeaves[i] )
                return 0;
        for ( i = 0; i < pC0->nLeaves; i++ )
            pC->pLeaves[i] = pC0->pLeaves[i];
        pC->nLeaves = pC0->nLeaves;
        pC->Delay = 1 + IVY_MAX( pC0->Delay, pC1->Delay );
        return 1;
    }
    // the case when one of the cuts is the largest
    if ( pC0->nLeaves == nLimit )
    {
        for ( i = 0; i < pC1->nLeaves; i++ )
        {
            for ( k = pC0->nLeaves - 1; k >= 0; k-- )
                if ( pC0->pLeaves[k] == pC1->pLeaves[i] )
                    break;
            if ( k == -1 ) // did not find
                return 0;
        }
        for ( i = 0; i < pC0->nLeaves; i++ )
            pC->pLeaves[i] = pC0->pLeaves[i];
        pC->nLeaves = pC0->nLeaves;
        pC->Delay = 1 + IVY_MAX( pC0->Delay, pC1->Delay );
        return 1;
    }

    // compare two cuts with different numbers
    i = k = 0;
    for ( c = 0; c < nLimit; c++ )
    {
        if ( k == pC1->nLeaves )
        {
            if ( i == pC0->nLeaves )
            {
                pC->nLeaves = c;
                pC->Delay = 1 + IVY_MAX( pC0->Delay, pC1->Delay );
                return 1;
            }
            pC->pLeaves[c] = pC0->pLeaves[i++];
            continue;
        }
        if ( i == pC0->nLeaves )
        {
            if ( k == pC1->nLeaves )
            {
                pC->nLeaves = c;
                pC->Delay = 1 + IVY_MAX( pC0->Delay, pC1->Delay );
                return 1;
            }
            pC->pLeaves[c] = pC1->pLeaves[k++];
            continue;
        }
        if ( pC0->pLeaves[i] < pC1->pLeaves[k] )
        {
            pC->pLeaves[c] = pC0->pLeaves[i++];
            continue;
        }
        if ( pC0->pLeaves[i] > pC1->pLeaves[k] )
        {
            pC->pLeaves[c] = pC1->pLeaves[k++];
            continue;
        }
        pC->pLeaves[c] = pC0->pLeaves[i++]; 
        k++;
    }
    if ( i < pC0->nLeaves || k < pC1->nLeaves )
        return 0;
    pC->nLeaves = c;
    pC->Delay = 1 + IVY_MAX( pC0->Delay, pC1->Delay );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_FpgaCutCompare( Ivy_FpgaCut_t * pC0, Ivy_FpgaCut_t * pC1 )
{
    if ( pC0->Delay < pC1->Delay )
        return -1;
    if ( pC0->Delay > pC1->Delay )
        return 1;
    if ( pC0->nLeaves < pC1->nLeaves )
        return -1;
    if ( pC0->nLeaves > pC1->nLeaves )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Prepares the object for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ObjFpgaDelay( Ivy_FpgaMan_t * pFpga, int ObjId, int Fan0Id, int Fan1Id )
{
    Ivy_FpgaObj_t * pObjFpga, * pObjFpga0, * pObjFpga1;
    int nCuts, i, k;
    pObjFpga  = Attr_ManReadAttrPtr( pFpga->pManAttr, ObjId );
    pObjFpga0 = Attr_ManReadAttrPtr( pFpga->pManAttr, Fan0Id );
    pObjFpga1 = Attr_ManReadAttrPtr( pFpga->pManAttr, Fan1Id );
    // create cross-product of the cuts
    nCuts = 0;
    for ( i = 0; pObjFpga0->Cuts[i].nLeaves > 0 && i < pFpga->nCutsMax; i++ )
    for ( k = 0; pObjFpga1->Cuts[k].nLeaves > 0 && k < pFpga->nCutsMax; k++ )
        if ( Ivy_ObjFpgaMerge( pObjFpga0->Cuts + i, pObjFpga1->Cuts + k, pFpga->pCutStore + nCuts, pFpga->nLutSize ) )
            nCuts++;
    // sort the cuts
    qsort( pFpga->pCutStore, nCuts, sizeof(Ivy_FpgaCut_t), (int (*)(const void *, const void *))Ivy_FpgaCutCompare );
    // take the first
    pObjFpga->Cuts[0].nLeaves    = 1;
    pObjFpga->Cuts[0].pLeaves[0] = ObjId;
    pObjFpga->Cuts[0].Delay      = pFpga->pCutStore[0].Delay;
    pObjFpga->Cuts[1] = pFpga->pCutStore[0];
}

/**Function*************************************************************

  Synopsis    [Maps the nodes for delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManFpgaDelay( Ivy_FpgaMan_t * pFpga )
{
    Ivy_FpgaObj_t * pObjFpga;
    Ivy_Obj_t * pObj;
    int i, DelayBest;
    int clk = clock();
    // set arrival times and trivial cuts at const 1 and PIs
    pObjFpga = Attr_ManReadAttrPtr( pFpga->pManAttr, 0 );
    pObjFpga->Cuts[0].nLeaves = 1;
    Ivy_ManForEachPi( pFpga->pManIvy, pObj, i )
    {
        pObjFpga = Attr_ManReadAttrPtr( pFpga->pManAttr, pObj->Id );
        pObjFpga->Cuts[0].nLeaves    = 1;
        pObjFpga->Cuts[0].pLeaves[0] = pObj->Id;
    }
    // map the internal nodes
    Ivy_ManForEachNode( pFpga->pManIvy, pObj, i )
    {
        Ivy_ObjFpgaDelay( pFpga, pObj->Id, Ivy_ObjFaninId0(pObj), Ivy_ObjFaninId1(pObj) );
    }
    // get the best arrival time of the POs
    DelayBest = 0;
    Ivy_ManForEachPo( pFpga->pManIvy, pObj, i )
    {
        pObjFpga = Attr_ManReadAttrPtr( pFpga->pManAttr, Ivy_ObjFanin0(pObj)->Id );
        if ( DelayBest < (int)pObjFpga->Cuts[1].Delay )
            DelayBest = (int)pObjFpga->Cuts[1].Delay;
    }
    printf( "Best delay = %d. ", DelayBest );
    PRT( "Time", clock() - clk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


