/**CFile****************************************************************

  FileName    [aigOper.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigOper.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_And( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1 )
{
    Aig_Node_t * pAnd;
    // check for trivial cases
    if ( p0 == p1 )
        return p0;
    if ( p0 == Aig_Not(p1) )
        return Aig_Not(pMan->pConst1);
    if ( Aig_Regular(p0) == pMan->pConst1 )
    {
        if ( p0 == pMan->pConst1 )
            return p1;
        return Aig_Not(pMan->pConst1);
    }
    if ( Aig_Regular(p1) == pMan->pConst1 )
    {
        if ( p1 == pMan->pConst1 )
            return p0;
        return Aig_Not(pMan->pConst1);
    }
    // order the arguments
    if ( Aig_Regular(p0)->Id > Aig_Regular(p1)->Id )
    {
        if ( pAnd = Aig_TableLookupNode( pMan, p1, p0 ) )
            return pAnd;
        return Aig_NodeCreateAnd( pMan, p1, p0 );
    }
    else
    {
        if ( pAnd = Aig_TableLookupNode( pMan, p0, p1 ) )
            return pAnd;
        return Aig_NodeCreateAnd( pMan, p0, p1 );
    }
}

/**Function*************************************************************

  Synopsis    [Implements Boolean OR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_Or( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1 )
{
    return Aig_Not( Aig_And( pMan, Aig_Not(p0), Aig_Not(p1) ) );
}

/**Function*************************************************************

  Synopsis    [Implements Boolean XOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_Xor( Aig_Man_t * pMan, Aig_Node_t * p0, Aig_Node_t * p1 )
{
    return Aig_Or( pMan, Aig_And(pMan, p0, Aig_Not(p1)), 
                         Aig_And(pMan, p1, Aig_Not(p0)) );
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_Mux( Aig_Man_t * pMan, Aig_Node_t * pC, Aig_Node_t * p1, Aig_Node_t * p0 )
{
    return Aig_Or( pMan, Aig_And(pMan, pC, p1), Aig_And(pMan, Aig_Not(pC), p0) );
}

/**Function*************************************************************

  Synopsis    [Implements the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_Miter_rec( Aig_Man_t * pMan, Aig_Node_t ** ppObjs, int nObjs )
{
    Aig_Node_t * pObj1, * pObj2;
    if ( nObjs == 1 )
        return ppObjs[0];
    pObj1 = Aig_Miter_rec( pMan, ppObjs,           nObjs/2         );
    pObj2 = Aig_Miter_rec( pMan, ppObjs + nObjs/2, nObjs - nObjs/2 );
    return Aig_Or( pMan, pObj1, pObj2 );
}
 
/**Function*************************************************************

  Synopsis    [Implements the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_Miter( Aig_Man_t * pMan, Vec_Ptr_t * vPairs )
{
    int i;
    if ( vPairs->nSize == 0 )
        return Aig_Not( pMan->pConst1 );
    assert( vPairs->nSize % 2 == 0 );
    // go through the cubes of the node's SOP
    for ( i = 0; i < vPairs->nSize; i += 2 )
        vPairs->pArray[i/2] = Aig_Xor( pMan, vPairs->pArray[i], vPairs->pArray[i+1] );
    vPairs->nSize = vPairs->nSize/2;
    return Aig_Miter_rec( pMan, (Aig_Node_t **)vPairs->pArray, vPairs->nSize );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


