/**CFile****************************************************************

  FileName    [bdcCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Truth-table-based bi-decomposition engine.]

  Synopsis    [The gateway to bi-decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 30, 2007.]

  Revision    [$Id: bdcCore.c,v 1.00 2007/01/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "bdcInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocate resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Bdc_Man_t * Bdc_ManAlloc( Bdc_Par_t * pPars )
{
    Bdc_Man_t * p;
    int i;
    p = ALLOC( Bdc_Man_t, 1 );
    memset( p, 0, sizeof(Bdc_Man_t) );
    assert( pPars->nVarsMax > 3 && pPars->nVarsMax < 16 );
    p->pPars = pPars;
    // memory
    p->vMemory = Vec_IntStart( 1 << 16 );
    // internal nodes
    p->nNodesAlloc = 256;
    p->pNodes = ALLOC( Bdc_Fun_t, p->nNodesAlloc );
    // set up hash table
    p->nTableSize = (1 << p->pPars->nVarsMax);
    p->pTable = ALLOC( Bdc_Fun_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Bdc_Fun_t *) * p->nTableSize );
    p->vSpots = Vec_IntAlloc( 256 );
    // set up constant 1 and elementary variables
    for ( i = 0; i < pPars->nVarsMax; i++ )
    {
    }
    p->nNodes = pPars->nVarsMax + 1;
    // remember the current place in memory
    p->nMemStart = Vec_IntSize( p->vMemory );
    return p;
}


/**Function*************************************************************

  Synopsis    [Deallocate resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_ManAlloc( Bdc_Man_t * p )
{
}

/**Function*************************************************************

  Synopsis    [Sets up the divisors.]

  Description [The first n+1 entries are const1 and elem variables.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_ManPrepare( Bdc_Man_t * p, Vec_Ptr_t * vDivs )
{
    Bdc_Fun_t ** pSpot, * pFunc;
    unsigned * puTruth;
    int i;
    // clean hash table
    Vec_PtrForEachEntry( p->vSpots, pSpot, i )
        *pSpot = NULL;
    // reset nodes
    p->nNodes = p->pPars->nVarsMax + 1;
    // reset memory
    Vec_IntShrink( p->vMemory, p->nMemStart );
    // add new nodes to the hash table
    Vec_PtrForEachEntry( vDivs, puTruth, i )
    {
        pFunc = Bdc_ManNewNode( p );
        pFunc->Type = BDC_TYPE_PI;
        pFunc->puFunc = puTruth;
        pFunc->uSupp = Kit_TruthSupport( puTruth, p->nVars );
    }
}

/**Function*************************************************************

  Synopsis    [Performs decomposition of one function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bdc_ManDecompose( Bdc_Man_t * p, unsigned * puFunc, unsigned * puCare, int nVars, Vec_Ptr_t * vDivs, int nNodeLimit )
{
    Bdc_Isf_t Isf, * pIsf = &Isf;
    // set current manager parameters
    p->nVars = nVars;
    p->nWords = Kit_TruthWordNum( nVars );
    p->nNodeLimit = nNodeLimit;
    Bdc_ManPrepare( p, vDivs );
    // copy the function
    pIsf->uSupp = Kit_TruthSupport( puFunc, p->nVars ) | Kit_TruthSupport( puCare, p->nVars );
    pIsf->puOn = Vec_IntFetch( p->vMemory, p->nWords );
    pIsf->puOff = Vec_IntFetch( p->vMemory, p->nWords );
    Kit_TruthAnd( pIsf->puOn, puCare, puFunc, p->nVars );
    Kit_TruthSharp( pIsf->puOff, puCare, puFunc, p->nVars );
    // call decomposition
    p->pRoot = Bdc_ManDecompose_rec( p, pIsf );
    if ( p->pRoot == NULL )
        return -1;
    return p->nNodes - (p->pPars->nVarsMax + 1);
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


