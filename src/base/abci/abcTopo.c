/**CFile****************************************************************

  FileName    [abcTopo.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Topologically constrained exact synthesis.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcTopo.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "misc/util/utilTruth.h"
#include "sat/kissat/kissat.h"

#define KISSAT_UNSAT 20
#define KISSAT_SAT   10
#define KISSAT_UNDEC  0

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static int AbcTopo_KissatTerminate( void * pData )
{
    abctime * pTimeStop = (abctime *)pData;
    return pTimeStop && *pTimeStop && Abc_Clock() > *pTimeStop;
}

/**Function*************************************************************

  Synopsis    [Exact synthesis of the MO function into a fixed-topology network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkTopoDup( Abc_Ntk_t * pTopo, Vec_Wrd_t * vTruths )
{
    Abc_Ntk_t * pNew = Abc_NtkDup(pTopo);
    Abc_Obj_t * pObj; int i;
    Abc_NtkForEachNode( pTopo, pObj, i ) {
      extern char * Bbl_ManTruthToSop( unsigned * pTruth, int nVars );
      char * pSop = Bbl_ManTruthToSop( (unsigned *)Vec_WrdEntryP(vTruths, i), Abc_ObjFaninNum(pObj) );
      pObj->pData = Abc_SopRegister( (Mem_Flex_t *)pNew->pManFunc, pSop );
      ABC_FREE( pSop );
    }
    return pNew;
}
Abc_Ntk_t * Abc_NtkTopoExact( Abc_Ntk_t * pFunc, Abc_Ntk_t * pTopo, int nTimeOut, int nSeed, int fAndGates, int fVerbose )
{
    Abc_Ntk_t * pRes = NULL;
    abctime clkTotal = Abc_Clock();
    assert( Abc_NtkIsSopLogic(pTopo) );
    // count how many variables we need to encode minterms of each node
    Abc_Obj_t * pObj; int i, nMints = 0, nNodeClausesPerMint = 0, nTwoFaninNodes = 0;
    Abc_NtkForEachNode( pTopo, pObj, i ) {
        assert( Abc_ObjFaninNum(pObj) <= 6 );
        nMints += 1 << Abc_ObjFaninNum(pObj);
        nNodeClausesPerMint += 2 * (1 << Abc_ObjFaninNum(pObj)); // two clauses per minterm
        nTwoFaninNodes += (Abc_ObjFaninNum(pObj) == 2);
    }
    // derive input/output mapping of the original function, which will be synthesized
    Gia_Man_t * pGia    = Abc_NtkClpGia( pFunc );
    Vec_Wrd_t * vSimsPi = Vec_WrdStartTruthTables( Gia_ManCiNum(pGia) );
    Vec_Wrd_t * vSims   = Gia_ManSimPatSimOut( pGia, vSimsPi, 1 );
    int nWords = Vec_WrdSize(vSimsPi) / Gia_ManCiNum(pGia);
    assert( Abc_NtkCiNum(pTopo) == Gia_ManCiNum(pGia) );
    assert( Abc_NtkPoNum(pTopo) == Gia_ManPoNum(pGia) );
    assert( Vec_WrdSize(vSims) == Gia_ManPoNum(pGia) * nWords );
    // map network objects to compact variable IDs (PIs first, then internal nodes)
    Vec_Int_t * vObj2Var = Vec_IntStart( Abc_NtkObjNumMax(pTopo) );
    int iMap = 0;
    Abc_NtkForEachCi( pTopo, pObj, i )
        Vec_IntWriteEntry( vObj2Var, Abc_ObjId(pObj), iMap++ );
    Abc_NtkForEachNode( pTopo, pObj, i )
        Vec_IntWriteEntry( vObj2Var, Abc_ObjId(pObj), iMap++ );
    assert( iMap == Abc_NtkCiNum(pTopo) + Abc_NtkNodeNum(pTopo) );
    // create Kissat SAT solver with as many variables as there are minterms
    // plus additionally allocate vars to represent values of each node under each input minterm
    kissat * pSat = kissat_init();
    int nVarsAlloc = nMints + (1 << Abc_NtkCiNum(pTopo)) * (Abc_NtkCiNum(pTopo) + Abc_NtkNodeNum(pTopo));
    kissat_reserve( pSat, nVarsAlloc );
    if ( nSeed > 0 )
        kissat_set_option( pSat, "seed", nSeed );
    if ( fVerbose )
        printf( "Running fixed-topology exact synthesis:  PI = %d  Nodes = %d  PO = %d\n",
            Abc_NtkCiNum(pTopo), Abc_NtkNodeNum(pTopo), Abc_NtkPoNum(pTopo) );
    // for each minterm, iterate through each PI, each internal node, and each outputs
    // and add constraints that tell us that the value of the node's output agrees with the values of its fanins
    // while the value of the primary outputs is realized correctly by those internal nodes that drive the outputs
    int m, n, k, f, nTopoMints = 1 << Abc_NtkCiNum(pTopo);
    int nClauses = nTopoMints * (Abc_NtkCiNum(pTopo) + Abc_NtkPoNum(pTopo) + nNodeClausesPerMint) +
        (fAndGates ? 2 * nTwoFaninNodes : 0);
    if ( fAndGates && nTwoFaninNodes )
    {
        // block XOR/XNOR truth tables for two-input nodes
        int iMint = 0;
        Abc_NtkForEachNode( pTopo, pObj, i )
        {
            int nFanins = Abc_ObjFaninNum(pObj);
            if ( nFanins == 2 )
            {
                int pLits[4], j;
                // forbid 0110
                pLits[0] = Abc_Var2Lit( iMint + 0, 0 );
                pLits[1] = Abc_Var2Lit( iMint + 1, 1 );
                pLits[2] = Abc_Var2Lit( iMint + 2, 1 );
                pLits[3] = Abc_Var2Lit( iMint + 3, 0 );
                for ( j = 0; j < 4; j++ )
                    kissat_add( pSat, Abc_LitIsCompl(pLits[j]) ? -(Abc_Lit2Var(pLits[j]) + 1) : (Abc_Lit2Var(pLits[j]) + 1) );
                kissat_add( pSat, 0 );
                // forbid 1001
                pLits[0] = Abc_Var2Lit( iMint + 0, 1 );
                pLits[1] = Abc_Var2Lit( iMint + 1, 0 );
                pLits[2] = Abc_Var2Lit( iMint + 2, 0 );
                pLits[3] = Abc_Var2Lit( iMint + 3, 1 );
                for ( j = 0; j < 4; j++ )
                    kissat_add( pSat, Abc_LitIsCompl(pLits[j]) ? -(Abc_Lit2Var(pLits[j]) + 1) : (Abc_Lit2Var(pLits[j]) + 1) );
                kissat_add( pSat, 0 );
            }
            iMint += 1 << nFanins;
        }
    }
    for ( m = 0; m < nTopoMints; m++ ) {
        int iVarBase = nMints + m * (Abc_NtkCiNum(pTopo) + Abc_NtkNodeNum(pTopo));
        // set PI values for this minterm
        Abc_NtkForEachCi( pTopo, pObj, k ) {
            int fPiVal = Abc_TtGetBit( Vec_WrdArray(vSimsPi) + k * nWords, m );
            int iPiVar = iVarBase + Vec_IntEntry( vObj2Var, Abc_ObjId(pObj) );
            int Lit = Abc_Var2Lit( iPiVar, !fPiVal );
            kissat_add( pSat, Abc_LitIsCompl(Lit) ? -(Abc_Lit2Var(Lit) + 1) : (Abc_Lit2Var(Lit) + 1) );
            kissat_add( pSat, 0 );
        }
        // for each internal node
        int iMint = 0;
        Abc_NtkForEachNode( pTopo, pObj, n ) {
            int nFanins = Abc_ObjFaninNum(pObj);
            int iNodeMintBase = iMint;
            int iNodeVar = iVarBase + Vec_IntEntry( vObj2Var, Abc_ObjId(pObj) );
            // for each configuration of fanin values
            for ( k = 0; k < (1 << nFanins); k++ ) {
                // add clauses for both polarities of the node output
                for ( int v = 0; v < 2; v++ ) {
                    int pLits[8], nLits = 0;
                    // add literal for the truth table variable (minterm k of this node)
                    pLits[nLits++] = Abc_Var2Lit( iNodeMintBase + k, v );
                    // add literal for the node output value
                    pLits[nLits++] = Abc_Var2Lit( iNodeVar, !v );
                    // check fanin values match minterm k
                    Abc_Obj_t * pFanin;
                    Abc_ObjForEachFanin( pObj, pFanin, f ) {
                        int iFaninVar = iVarBase + Vec_IntEntry( vObj2Var, Abc_ObjId(pFanin) );
                        int fFaninVal = (k >> f) & 1;
                        pLits[nLits++] = Abc_Var2Lit( iFaninVar, !fFaninVal );
                    }
                    // add clause
                    for ( i = 0; i < nLits; i++ )
                        kissat_add( pSat, Abc_LitIsCompl(pLits[i]) ? -(Abc_Lit2Var(pLits[i]) + 1) : (Abc_Lit2Var(pLits[i]) + 1) );
                    kissat_add( pSat, 0 );
                }
            }
            iMint += 1 << nFanins;
        }
        assert( iMint == nMints );
        // constrain primary outputs to match the target function
        Abc_NtkForEachPo( pTopo, pObj, n ) {
            Abc_Obj_t * pDriver = Abc_ObjFanin0(pObj);
            int iDriverVar = iVarBase + Vec_IntEntry( vObj2Var, Abc_ObjId(pDriver) );
            // get expected output value from simulation and add unit clause
            int fExpected = Abc_TtGetBit( Vec_WrdArray(vSims) + n * nWords, m );
            int Lit = Abc_Var2Lit( iDriverVar, !fExpected );
            kissat_add( pSat, Abc_LitIsCompl(Lit) ? -(Abc_Lit2Var(Lit) + 1) : (Abc_Lit2Var(Lit) + 1) );
            kissat_add( pSat, 0 );
        }
    }
    if ( fVerbose )
        printf( "Minterm variables = %d.  Internal variables = %d.  Clauses = %d.\n", nMints, nVarsAlloc - nMints, nClauses );

    abctime timeStop = 0;
    if ( nTimeOut )
    {
        timeStop = Abc_Clock() + (abctime)nTimeOut * CLOCKS_PER_SEC;
        kissat_set_terminate( pSat, &timeStop, AbcTopo_KissatTerminate );
    }
    else
        kissat_set_terminate( pSat, NULL, NULL );
    int status = kissat_solve( pSat );
    if ( status == KISSAT_SAT )
    {
        // if it is satisfiable, collect the satisfying assignment into the array
        Vec_Wrd_t * vTruths = Vec_WrdStart( Abc_NtkObjNumMax(pTopo) );
        int iMint = 0;
        Abc_NtkForEachNode( pTopo, pObj, i ) {
          // iMint shows the first SAT variable of this node
          // collect values into Truth
          word TruthSmall = 0;
          for ( int v = 0; v < (1 << Abc_ObjFaninNum(pObj)); v++ )
              if ( kissat_value( pSat, iMint + v + 1 ) > 0 )
                  TruthSmall |= (word)1 << v;
          // increment the minterm counter
          iMint += 1 << Abc_ObjFaninNum(pObj);
          // save the result into the array of truth tables
          Vec_WrdWriteEntry( vTruths, i, Abc_Tt6Stretch( TruthSmall, Abc_ObjFaninNum(pObj) ) );
          if ( fVerbose ) {
              int nDigits = 1 << (Abc_ObjFaninNum(pObj)-2);
              printf( "Node %2d (fanins = %d) 0x%0*lx\n", i, Abc_ObjFaninNum(pObj), nDigits, TruthSmall );
          }
        }
        assert( iMint == nMints );
        // create network with the corresponding truth tables
        pRes = Abc_NtkTopoDup( pTopo, vTruths );
        Vec_WrdFree( vTruths );
        if ( fVerbose )
            printf( "The problem has a solution.\n" );
    }
    else if ( status == KISSAT_UNSAT && fVerbose )
        printf( "The problem has no solution.\n" );
    else if ( status == KISSAT_UNDEC && fVerbose )
        printf( "The solver returned unknown.\n" );
    kissat_release( pSat );
    Vec_WrdFree( vSims );
    Vec_WrdFree( vSimsPi );
    Vec_IntFree( vObj2Var );
    Gia_ManStop( pGia );
    if ( fVerbose )
        Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
    return pRes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
