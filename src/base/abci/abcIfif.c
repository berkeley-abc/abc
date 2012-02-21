/**CFile****************************************************************

  FileName    [abcIfif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Experiment with technology mapping.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcIfif.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "src/base/abc/abc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abc_IffObj_t_       Abc_IffObj_t;
struct Abc_IffObj_t_ 
{
    int              Delay0;       // separate delay 
    int              Delay1;       // combined delay
    int              nLeaves;
    int              pLeaves[6];
};

typedef struct Abc_IffMan_t_       Abc_IffMan_t;
struct Abc_IffMan_t_ 
{
    Abc_Ntk_t *      pNtk;
    int              nObjs;
    int              nDelayLut;
    int              nDegree;
    int              fVerbose;
    // internal data
    Abc_IffObj_t *   pObjs;
};

static inline Abc_IffObj_t *  Abc_IffObj( Abc_IffMan_t * p, int i )      { assert( i >= 0 && i < p->nObjs ); return p->pObjs + i;   }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_IffMan_t * Abc_NtkIfifStart( Abc_Ntk_t * pNtk, int nDelayLut, int nDegree, int fVerbose )
{
    Abc_IffMan_t * p;
    p = ABC_CALLOC( Abc_IffMan_t, 1 );
    p->pNtk       = pNtk;
    p->nObjs      = Abc_NtkObjNumMax( pNtk );
    p->nDelayLut  = nDelayLut;
    p->nDegree    = nDegree; 
    p->fVerbose   = fVerbose;
    // internal data
    p->pObjs      = ABC_CALLOC( Abc_IffObj_t, p->nObjs );
    return p;
}
void Abc_NtkIfifStop( Abc_IffMan_t * p )
{
    // internal data
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Compare nodes by Delay1 stored in pObj->iTemp.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjIfifCompare( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 )
{
    Abc_Obj_t * pObj1 = *pp1;
    Abc_Obj_t * pObj2 = *pp2;
    assert( Abc_ObjIsNode(pObj1) && Abc_ObjIsNode(pObj2) );
    return (int)pObj2->iTemp - (int)pObj1->iTemp;
}

/**Function*************************************************************

  Synopsis    [This is the delay which object may have all by itself.]

  Description [This delay is stored in Delay0.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjDelay0( Abc_IffMan_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i, Delay0 = 0;
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Delay0 = Abc_MaxInt( Delay0, Abc_IffObj(p, Abc_ObjId(pFanin))->Delay1 );
    return p->nDelayLut + Delay0;
}

/**Function*************************************************************

  Synopsis    [This is the delay object may have in a group.]

  Description [This delay is stored in Delay1 and pObj->iTemp.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjDelay1( Abc_IffMan_t * p, Abc_Obj_t * pObj )
{
    Abc_IffObj_t * pIfif;
    Abc_Obj_t * pNodes[6], * pFanin;
    int i, nNodes, Delay1, DelayWorst;

    // find the object structure
    pIfif = Abc_IffObj( p, Abc_ObjId(pObj) );

    // collect relevant nodes
    nNodes = 0;
    Abc_ObjForEachFanin( pObj, pFanin, i )
        if ( Abc_ObjIsNode(pFanin) )
        {
            assert( pFanin->iTemp >= p->nDelayLut );
            pNodes[nNodes++] = pFanin;
        }

    // process the result
    Delay1 = 0;
    pIfif->nLeaves = 0;
    if ( nNodes > 0 )
    {
        int fVerbose = 0;

        // sort fanins by delay
        qsort( (void *)pNodes, nNodes, sizeof(Abc_Obj_t *), (int (*)(const void *, const void *)) Abc_ObjIfifCompare );
        assert( pNodes[0]->iTemp >= pNodes[nNodes-1]->iTemp );

        if ( fVerbose )
        {
            for ( i = 0; i < nNodes; i++ )
            {
                printf( "Fanin %d : ", i );
                printf( "D0 %4d  ",    Abc_IffObj(p, Abc_ObjId(pNodes[i]))->Delay0 );
                printf( "D0* %4d    ", Abc_IffObj(p, Abc_ObjId(pNodes[0]))->Delay0 - (p->nDelayLut-1) );
                printf( "D1 %4d  ",    Abc_IffObj(p, Abc_ObjId(pNodes[i]))->Delay1 );
                printf( "\n" );
            }
            printf( "\n" );
        }

        // get the worst-case fanin delay
//        DelayWorst = Abc_IffObj(p, Abc_ObjId(pNodes[0]))->Delay0 - (p->nDelayLut-1);
        DelayWorst = -1;
        // find the delay and remember fanins
        for ( i = 0; i < nNodes; i++ )
        {
            if ( pIfif->nLeaves < p->nDegree && Abc_IffObj(p, Abc_ObjId(pNodes[i]))->Delay1 > DelayWorst )
            {
                Delay1 = Abc_MaxInt( Delay1, Abc_IffObj(p, Abc_ObjId(pNodes[i]))->Delay0 - (p->nDelayLut-1) );
                pIfif->pLeaves[pIfif->nLeaves++] = Abc_ObjId(pNodes[i]);
            }
            else
                Delay1 = Abc_MaxInt( Delay1, Abc_IffObj(p, Abc_ObjId(pNodes[i]))->Delay1 );
        }
//        assert( pIfif->nLeaves > 0 );
        assert( Delay1 > 0 );
    }
    return p->nDelayLut + Delay1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPerformIfif( Abc_Ntk_t * pNtk, int nDelayLut, int nDegree, int fVerbose )
{
    Abc_IffMan_t * p;
    Abc_IffObj_t * pIffObj;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i, Delay, nLutSize = Abc_NtkGetFaninMax( pNtk );
    if ( nLutSize > 6 )
    {
        printf( "LUT size (%d) is more than 6.\n", nLutSize );
        return;
    }
    // convert to AIGs
    Abc_NtkToAig( pNtk );

    assert( nDegree >= 0 && nDegree <= 6 );

    // start manager
    p = Abc_NtkIfifStart( pNtk, nDelayLut, nDegree, fVerbose );
//    printf( "Running experiment with LUT delay %d and degree %d (LUT size is %d).\n", nDelayLut, nDegree, nLutSize );

    // compute the delay
    vNodes = Abc_NtkDfs( pNtk, 0 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        assert( Abc_ObjIsNode(pObj) );
        pIffObj = Abc_IffObj( p, Abc_ObjId(pObj) );
        pIffObj->Delay0 = Abc_ObjDelay0( p, pObj );
        pIffObj->Delay1 = Abc_ObjDelay1( p, pObj );
        pObj->iTemp = pIffObj->Delay1;

//        printf( "Node %3d : Lev =%3d  Delay0 =%4d  Delay1 =%4d  Leaves =%3d.\n", 
//            Abc_ObjId(pObj), Abc_ObjLevel(pObj), pIffObj->Delay0, pIffObj->Delay1, pIffObj->nLeaves );
    }
    Vec_PtrFree( vNodes );

    // consider delay at the outputs
    Delay = 0;
    Abc_NtkForEachCo( pNtk, pObj, i )
        Delay = Abc_MaxInt( Delay, Abc_IffObj(p, Abc_ObjId(Abc_ObjFanin0(pObj)))->Delay1 );

    printf( "Critical delay is %5d (%7.2f).\n", Delay, 1.0 * Delay / nDelayLut );

    // derive a new network

    // stop manager
    Abc_NtkIfifStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

