/**CFile****************************************************************

  FileName    [saigAbs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Intergrated abstraction procedure.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigAbs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transform flop map into flop list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManClasses2Flops( Vec_Int_t * vFlopClasses )
{
    Vec_Int_t * vFlops;
    int i, Entry;
    vFlops = Vec_IntAlloc( 100 );
    Vec_IntForEachEntry( vFlopClasses, Entry, i )
        if ( Entry )
            Vec_IntPush( vFlops, i );
    return vFlops;
}

/**Function*************************************************************

  Synopsis    [Transform flop list into flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManFlops2Classes( int nRegs, Vec_Int_t * vFlops )
{
    Vec_Int_t * vFlopClasses;
    int i, Entry;
    vFlopClasses = Vec_IntStart( nRegs );
    Vec_IntForEachEntry( vFlops, Entry, i )
        Vec_IntWriteEntry( vFlopClasses, Entry, 1 );
    return vFlopClasses;
}

/**Function*************************************************************

  Synopsis    [Derive a new counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Saig_ManCexRemap( Aig_Man_t * p, Aig_Man_t * pAbs, Abc_Cex_t * pCexAbs )
{
    Abc_Cex_t * pCex;
    Aig_Obj_t * pObj;
    int i, f;
    if ( !Saig_ManVerifyCex( pAbs, pCexAbs ) )
        printf( "Saig_ManCexRemap(): The initial counter-example is invalid.\n" );
//    else
//        printf( "Saig_ManCexRemap(): The initial counter-example is correct.\n" );
    // start the counter-example
    pCex = Abc_CexAlloc( Aig_ManRegNum(p), Saig_ManPiNum(p), pCexAbs->iFrame+1 );
    pCex->iFrame = pCexAbs->iFrame;
    pCex->iPo    = pCexAbs->iPo;
    // copy the bit data
    for ( f = 0; f <= pCexAbs->iFrame; f++ )
    {
        Saig_ManForEachPi( pAbs, pObj, i )
        {
            if ( i == Saig_ManPiNum(p) )
                break;
            if ( Abc_InfoHasBit( pCexAbs->pData, pCexAbs->nRegs + pCexAbs->nPis * f + i ) )
                Abc_InfoSetBit( pCex->pData, pCex->nRegs + pCex->nPis * f + i );
        }
    }
    // verify the counter example
    if ( !Saig_ManVerifyCex( p, pCex ) )
    {
        printf( "Saig_ManCexRemap(): Counter-example is invalid.\n" );
        Abc_CexFree( pCex );
        pCex = NULL;
    }
    else
    {
        printf( "Counter-example verification is successful.\n" );
        printf( "Output %d was asserted in frame %d (use \"write_counter\" to dump a witness). \n", pCex->iPo, pCex->iFrame );
    }
    return pCex;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

