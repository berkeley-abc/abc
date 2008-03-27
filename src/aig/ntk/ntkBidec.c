/**CFile****************************************************************

  FileName    [ntkBidec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Bi-decomposition of local functions.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntkBidec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntk.h"
#include "bdc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Hop_Obj_t * Bdc_FunCopyHop( Bdc_Fun_t * pObj )  { return Hop_NotCond( Bdc_FuncCopy(Bdc_Regular(pObj)), Bdc_IsComplement(pObj) );  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Resynthesizes nodes using bi-decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Ntk_NodeIfNodeResyn( Bdc_Man_t * p, Hop_Man_t * pHop, Hop_Obj_t * pRoot, int nVars, Vec_Int_t * vTruth, unsigned * puCare )
{
    unsigned * pTruth;
    Bdc_Fun_t * pFunc;
    int nNodes, i;
    assert( nVars <= 16 );
    // derive truth table
    pTruth = Hop_ManConvertAigToTruth( pHop, Hop_Regular(pRoot), nVars, vTruth, 0 );
    if ( Hop_IsComplement(pRoot) )
        for ( i = Aig_TruthWordNum(nVars)-1; i >= 0; i-- )
            pTruth[i] = ~pTruth[i];
    // decompose truth table
    Bdc_ManDecompose( p, pTruth, puCare, nVars, NULL, 1000 );
    // convert back into HOP
    Bdc_FuncSetCopy( Bdc_ManFunc( p, 0 ), Hop_ManConst1( pHop ) );
    for ( i = 0; i < nVars; i++ )
        Bdc_FuncSetCopy( Bdc_ManFunc( p, i+1 ), Hop_ManPi( pHop, i ) );
    nNodes = Bdc_ManNodeNum(p);
    for ( i = nVars + 1; i < nNodes; i++ )
    {
        pFunc = Bdc_ManFunc( p, i );
        Bdc_FuncSetCopy( pFunc, Hop_And( pHop, Bdc_FunCopyHop(Bdc_FuncFanin0(pFunc)), Bdc_FunCopyHop(Bdc_FuncFanin1(pFunc)) ) );
    }
    return Bdc_FunCopyHop( Bdc_ManRoot(p) );
}

/**Function*************************************************************

  Synopsis    [Resynthesizes nodes using bi-decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManBidecResyn( Ntk_Man_t * pNtk, int fVerbose )
{
    Bdc_Par_t Pars = {0}, * pPars = &Pars;
    Bdc_Man_t * p;
    Ntk_Obj_t * pObj;
    Vec_Int_t * vTruth;
    int i, nGainTotal = 0, nNodes1, nNodes2;
    int clk = clock();
    pPars->nVarsMax = Ntk_ManGetFaninMax( pNtk );
    pPars->fVerbose = fVerbose;
    if ( pPars->nVarsMax > 15 )
    {
        if ( fVerbose )
        printf( "Resynthesis is not performed for nodes with more than 15 inputs.\n" );
        pPars->nVarsMax = 15;
    }
    vTruth = Vec_IntAlloc( 0 );
    p = Bdc_ManAlloc( pPars );
    Ntk_ManForEachNode( pNtk, pObj, i )
    {
        if ( Ntk_ObjFaninNum(pObj) > 15 )
            continue;
        nNodes1 = Hop_DagSize(pObj->pFunc);
        pObj->pFunc = Ntk_NodeIfNodeResyn( p, pNtk->pManHop, pObj->pFunc, Ntk_ObjFaninNum(pObj), vTruth, NULL );
        nNodes2 = Hop_DagSize(pObj->pFunc);
        nGainTotal += nNodes1 - nNodes2;
    }
    Bdc_ManFree( p );
    Vec_IntFree( vTruth );
    if ( fVerbose )
    {
    printf( "Total gain in AIG nodes = %d.  ", nGainTotal );
    PRT( "Total runtime", clock() - clk );
    }
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


