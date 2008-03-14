/**CFile****************************************************************

  FileName    [abcBidec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface to bi-decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcBidec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

#include "bdc.h"
#include "bdcInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Hop_Obj_t * Bdc_FunCopyHop( Bdc_Fun_t * pObj )  { return Hop_NotCond( Bdc_Regular(pObj)->pCopy, Bdc_IsComplement(pObj) );  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Resynthesizes nodes using bi-decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NodeIfNodeResyn( Bdc_Man_t * p, Hop_Man_t * pHop, Hop_Obj_t * pRoot, int nVars, Vec_Int_t * vTruth, unsigned * puCare )
{
    unsigned * pTruth;
    Bdc_Fun_t * pFunc;
    int i;
    assert( nVars <= 16 );
    // derive truth table
    pTruth = Abc_ConvertAigToTruth( pHop, Hop_Regular(pRoot), nVars, vTruth, 0 );
    if ( Hop_IsComplement(pRoot) )
        Extra_TruthNot( pTruth, pTruth, nVars );
    // decompose truth table
    Bdc_ManDecompose( p, pTruth, puCare, nVars, NULL, 1000 );
    // convert back into HOP
    Bdc_FunWithId( p, 0 )->pCopy = Hop_ManConst1( pHop );
    for ( i = 0; i < nVars; i++ )
        Bdc_FunWithId( p, i+1 )->pCopy = Hop_ManPi( pHop, i );
    for ( i = nVars + 1; i < p->nNodes; i++ )
    {
        pFunc = Bdc_FunWithId( p, i );
        pFunc->pCopy = Hop_And( pHop, Bdc_FunCopyHop(pFunc->pFan0), Bdc_FunCopyHop(pFunc->pFan1) );
    }
    return Bdc_FunCopyHop(p->pRoot);
}

/**Function*************************************************************

  Synopsis    [Resynthesizes nodes using bi-decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBidecResyn( Abc_Ntk_t * pNtk, int fVerbose )
{
    Bdc_Par_t Pars = {0}, * pPars = &Pars;
    Bdc_Man_t * p;
    Abc_Obj_t * pObj;
    Vec_Int_t * vTruth;
    int i, nGainTotal = 0, nNodes1, nNodes2;
    int clk = clock();
    assert( Abc_NtkIsLogic(pNtk) );
    if ( !Abc_NtkToAig(pNtk) )
        return;
    pPars->nVarsMax = Abc_NtkGetFaninMax( pNtk );
    pPars->fVerbose = fVerbose;
    if ( pPars->nVarsMax > 15 )
    {
        if ( fVerbose )
        printf( "Resynthesis is not performed for nodes with more than 15 inputs.\n" );
        pPars->nVarsMax = 15;
    }
    vTruth = Vec_IntAlloc( 0 );
    p = Bdc_ManAlloc( pPars );
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) > 15 )
            continue;
        nNodes1 = Hop_DagSize(pObj->pData);
        pObj->pData = Abc_NodeIfNodeResyn( p, pNtk->pManFunc, pObj->pData, Abc_ObjFaninNum(pObj), vTruth, NULL );
        nNodes2 = Hop_DagSize(pObj->pData);
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


