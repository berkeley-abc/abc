/**CFile****************************************************************

  FileName    [bbrCex.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [BDD-based reachability analysis.]

  Synopsis    [Procedures to derive a satisfiable counter-example.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bbrCex.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bbr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the initial state and sets up the variable map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManStateVarMap( DdManager * dd, Aig_Man_t * p, int fVerbose )
{
    DdNode ** pbVarsX, ** pbVarsY;
    Aig_Obj_t * pLatch;
    int i;

    // set the variable mapping for Cudd_bddVarMap()
    pbVarsX = ALLOC( DdNode *, dd->size );
    pbVarsY = ALLOC( DdNode *, dd->size );
    Saig_ManForEachLo( p, pLatch, i )
    {
        pbVarsY[i] = dd->vars[ Saig_ManPiNum(p) + i ];
        pbVarsX[i] = dd->vars[ Saig_ManCiNum(p) + i ];
    }
    Cudd_SetVarMap( dd, pbVarsX, pbVarsY, Saig_ManRegNum(p) );
    FREE( pbVarsX );
    FREE( pbVarsY );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManComputeCountExample( Aig_Man_t * p, DdManager * dd, DdNode ** pbParts, Vec_Ptr_t * vCareSets, int nBddMax, int fVerbose, int fSilent )
{
/*
    Bbr_ImageTree_t * pTree = NULL; // Suppress "might be used uninitialized"
    DdNode * bCubeCs;
    DdNode * bCurrent;
    DdNode * bNext = NULL; // Suppress "might be used uninitialized"
    DdNode * bTemp;
    DdNode ** pbVarsY;
    Aig_Obj_t * pObj;
    int i, nIters, nBddSize;
    int nThreshold = 10000;
    int * pCex;
    char * pValues;

    // allocate room for the counter-example
    pCex = ALLOC( int, Vec_PtrSize(vCareSets) );

    // allocate room for the cube
    pValues = ALLOC( char, dd->size );

    // collect the NS variables
    // set the variable mapping for Cudd_bddVarMap()
    pbVarsY = ALLOC( DdNode *, dd->size );
    Aig_ManForEachPi( p, pObj, i )
        pbVarsY[i] = dd->vars[ i ];

    // create the initial state and the variable map
    Aig_ManStateVarMap( dd, p, fVerbose );

    // start the image computation
    bCubeCs  = Bbr_bddComputeRangeCube( dd, Aig_ManPiNum(p), 2*Saig_ManCiNum(p) );    Cudd_Ref( bCubeCs );
    pTree = Bbr_bddImageStart( dd, bCubeCs, Saig_ManRegNum(p), pbParts, Saig_ManRegNum(p), pbVarsY, fVerbose );
    Cudd_RecursiveDeref( dd, bCubeCs );
    free( pbVarsY );
    if ( pTree == NULL )
    {
        if ( !fSilent )
            printf( "BDDs blew up during qualitification scheduling.  " );
        return -1;
    }

    // create counter-example in terms of next state variables
    // pNext = ...

    // perform reachability analisys
    Vec_PtrForEachEntryReverse( vCareSets, pCurrent, i )
    { 
        // compute the next states
        bImage = Bbr_bddImageCompute( pTree, bCurrent );           
        if ( bImage == NULL )
        {
            if ( !fSilent )
                printf( "BDDs blew up during image computation.  " );
            Bbr_bddImageTreeDelete( pTree );
            return -1;
        }
        Cudd_Ref( bImage );

        // intersect with the previous set
        bImage = Cudd_bddAnd( dd, pTemp = bImage, pCurrent );
        Cudd_RecursiveDeref( dd, pTemp );

        // find any assignment of the BDD
        RetValue = Cudd_bddPickOneCube( dd, bImage, pValues );

        // transform the assignment into the cube in terms of the next state vars


        
        // pCurrent = ...

        // save values of the PI variables


        // check if there are any new states
        if ( Cudd_bddLeq( dd, bNext, bReached ) )
            break;
        // check the BDD size
        nBddSize = Cudd_DagSize(bNext);
        if ( nBddSize > nBddMax )
            break;
        // check the result
        for ( i = 0; i < Saig_ManPoNum(p); i++ )
        {
            if ( !Cudd_bddLeq( dd, bNext, Cudd_Not(pbOutputs[i]) ) )
            {
                if ( !fSilent )
                    printf( "Output %d was asserted in frame %d.  ", i, nIters );
                Cudd_RecursiveDeref( dd, bReached );
                bReached = NULL;
                break;
            }
        }
        if ( i < Saig_ManPoNum(p) )
            break;
        // get the new states
        bCurrent = Cudd_bddAnd( dd, bNext, Cudd_Not(bReached) );        Cudd_Ref( bCurrent );
*/
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


