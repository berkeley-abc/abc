/**CFile****************************************************************

  FileName    [simSymSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Satisfiability to determine two variable symmetries.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: simSymSat.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "sim.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int   Fraig_SymmsSatProveOne( Fraig_Man_t * p, int Var1, int Var2 );
static int   Fraig_SymmsIsCliqueMatrix( Fraig_Man_t * p, Extra_BitMat_t * pMat );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs the SAT based check.]

  Description [Given two bit matrices, with symm info and non-symm info, 
  checks the remaining pairs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fraig_SymmsSatComputeOne( Fraig_Man_t * p, Extra_BitMat_t * pMatSym, Extra_BitMat_t * pMatNonSym )
{
    int VarsU[512], VarsV[512];
    int nVarsU, nVarsV;
    int v, u, i, k;
    int Counter = 0;
    int satCalled = 0;
    int satProved = 0;
    double Density;
    int clk = clock();

    extern int symsSat;
    extern int Fraig_CountBits( Fraig_Man_t * pMan, Fraig_Node_t * pNode );


    // count undecided pairs
    for ( v = 0; v < p->vInputs->nSize; v++ )
    for ( u = v+1; u < p->vInputs->nSize; u++ )
    {
        if ( Extra_BitMatrixLookup1( pMatSym, v, u ) || Extra_BitMatrixLookup1( pMatNonSym, v, u ) )
            continue;
        Counter++;
    }
    // compute the density of 1's in the input space of the functions
    Density = (double)Fraig_CountBits(p, Fraig_Regular(p->vOutputs->pArray[0])) * 100.0 / FRAIG_SIM_ROUNDS / 32;

    printf( "Ins = %3d. Pairs to test = %4d. Dens = %5.2f %%. ", 
        p->vInputs->nSize, Counter, Density );


    // go through the remaining variable pairs
    for ( v = 0; v < p->vInputs->nSize; v++ )
    for ( u = v+1; u < p->vInputs->nSize; u++ )
    {
        if ( Extra_BitMatrixLookup1( pMatSym, v, u ) || Extra_BitMatrixLookup1( pMatNonSym, v, u ) )
            continue;
        symsSat++;
        satCalled++;

        // collect the variables that are symmetric with each
        nVarsU = nVarsV = 0;
        for ( i = 0; i < p->vInputs->nSize; i++ )
        {
            if ( Extra_BitMatrixLookup1( pMatSym, u, i ) )
                VarsU[nVarsU++] = i;
            if ( Extra_BitMatrixLookup1( pMatSym, v, i ) )
                VarsV[nVarsV++] = i;
        }

        if ( Fraig_SymmsSatProveOne( p, v, u ) )
        { // update the symmetric variable info            
//printf( "%d sym %d\n", v, u );
            for ( i = 0; i < nVarsU; i++ )
            for ( k = 0; k < nVarsV; k++ )
            {
                Extra_BitMatrixInsert1( pMatSym, VarsU[i], VarsV[k] );   // Theorem 1
                Extra_BitMatrixInsert2( pMatSym, VarsU[i], VarsV[k] );   // Theorem 1
                Extra_BitMatrixOrTwo( pMatNonSym, VarsU[i], VarsV[k] );  // Theorem 2
            }
            satProved++;
        }
        else
        { // update the assymmetric variable info
//printf( "%d non-sym %d\n", v, u );
            for ( i = 0; i < nVarsU; i++ )
            for ( k = 0; k < nVarsV; k++ )
            {
                Extra_BitMatrixInsert1( pMatNonSym, VarsU[i], VarsV[k] );   // Theorem 3
                Extra_BitMatrixInsert2( pMatNonSym, VarsU[i], VarsV[k] );   // Theorem 3
            }
        }
//Extra_BitMatrixPrint( pMatSym );
//Extra_BitMatrixPrint( pMatNonSym );
    }
printf( "SAT calls = %3d. Proved = %3d. ", satCalled, satProved );
PRT( "Time", clock() - clk );

    // make sure that the symmetry matrix contains only cliques
    assert( Fraig_SymmsIsCliqueMatrix( p, pMatSym ) );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the variables are symmetric; 0 otherwise.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fraig_SymmsSatProveOne( Fraig_Man_t * p, int Var1, int Var2 )
{
    Fraig_Node_t * pCof01, * pCof10, * pVar1, * pVar2;
    int RetValue;
    int nSatRuns = p->nSatCalls;
    int nSatProof = p->nSatProof;

    p->nBTLimit = 10;  // set the backtrack limit

    pVar1 = p->vInputs->pArray[Var1];
    pVar2 = p->vInputs->pArray[Var2];
    pCof01 = Fraig_CofactorTwo( p, p->vOutputs->pArray[0], pVar1, Fraig_Not(pVar2) );
    pCof10 = Fraig_CofactorTwo( p, p->vOutputs->pArray[0], Fraig_Not(pVar1), pVar2 );

//printf( "(%d,%d)", p->nSatCalls - nSatRuns, p->nSatProof - nSatProof );

//    RetValue = (pCof01 == pCof10);
//    RetValue = Fraig_NodesAreaEqual( p, pCof01, pCof10 );
    RetValue = Fraig_NodesAreEqual( p, pCof01, pCof10, -1 );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [A sanity check procedure.]

  Description [Makes sure that the symmetry information in the matrix
  is closed w.r.t. the relationship of transitivity (that is the symmetry
  graph is composed of cliques).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fraig_SymmsIsCliqueMatrix( Fraig_Man_t * p, Extra_BitMat_t * pMat )
{
    int v, u, i;
    for ( v = 0; v < p->vInputs->nSize; v++ )
    for ( u = v+1; u < p->vInputs->nSize; u++ )
    {
        if ( !Extra_BitMatrixLookup1( pMat, v, u ) )
            continue;
        // v and u are symmetric
        for ( i = 0; i < p->vInputs->nSize; i++ )
        {
            if ( i == v || i == u )
                continue;
            // i is neither v nor u
            // the symmetry status of i is the same w.r.t. to v and u
            if ( Extra_BitMatrixLookup1( pMat, i, v ) != Extra_BitMatrixLookup1( pMat, i, u ) )
                return 0;
        }
    }
    return 1;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


