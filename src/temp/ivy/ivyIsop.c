/**CFile****************************************************************

  FileName    [ivyIsop.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Computing irredundant SOP using truth table.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyIsop.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ivy_Sop_t_ Ivy_Sop_t;
struct Ivy_Sop_t_
{
    unsigned * pCubes;
    int        nCubes;
};

static Mem_Flex_t * s_Man = NULL;

static unsigned Ivy_TruthIsop5_rec( unsigned uOn, unsigned uOnDc, int nVars, Ivy_Sop_t * pcRes );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_TruthManStart()
{
    s_Man = Mem_FlexStart();
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_TruthManStop()
{
    Mem_FlexStop( s_Man, 0 );
    s_Man = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ivy_TruthIsop( unsigned * uTruth, int nVars )
{
}

/**Function*************************************************************

  Synopsis    [Computes ISOP for 5 variables or less.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Ivy_TruthIsop_rec( unsigned * puOn, unsigned * puOnDc, int nVars, Ivy_Sop_t * pcRes )
{
    Ivy_Sop_t cRes0, cRes1, cRes2;
    Ivy_Sop_t * pcRes0 = &cRes0, * pcRes1 = &cRes1, * pcRes2 = &cRes2;
    unsigned * puRes0, * puRes1, * puRes2;
    unsigned * puOn0, * puOn1, * puOnDc0, * puOnDc1, * pTemp0, * pTemp1;
    int i, k, Var, nWords;
    assert( nVars > 5 );
    assert( Extra_TruthIsImply( puOn, puOnDc, nVars ) );
    if ( Extra_TruthIsConst0( puOn, nVars ) )
    {
        pcRes->nCubes = 0;
        pcRes->pCubes = NULL;
        return puOn;
    }
    if ( Extra_TruthIsConst1( puOnDc, nVars ) )
    {
        pcRes->nCubes = 1;
        pcRes->pCubes = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 );
        pcRes->pCubes[0] = 0;
        return puOnDc;
    }
    // find the topmost var
    for ( Var = nVars-1; Var >= 0; Var-- )
        if ( Extra_TruthVarInSupport( puOn, nVars, Var ) || 
             Extra_TruthVarInSupport( puOnDc, nVars, Var ) )
             break;
    assert( Var >= 0 );
    if ( Var < 5 )
    {
        unsigned * puRes = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 );
        *puRes = Ivy_TruthIsop5_rec( puOn[0], puOnDc[0], Var + 1, pcRes );
        return puRes;
    }
    nWords = Extra_TruthWordNum( Var+1 );
    // cofactor
    puOn0 = puOn;
    puOn1 = puOn + nWords;
    puOnDc0 = puOnDc;
    puOnDc1 = puOnDc + nWords;
    // intermediate copies
    pTemp0 = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 * nWords );
    pTemp1 = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 * nWords );
    // solve for cofactors
    Extra_TruthSharp( pTemp0, puOn0, puOnDc1, Var + 1 );
    puRes0 = Ivy_TruthIsop5_rec( pTemp0, uOnDc0, Var-1, pcRes0 );
    Extra_TruthSharp( pTemp0, puOn1, puOnDc0, Var + 1 );
    puRes1 = Ivy_TruthIsop5_rec( pTemp1, uOnDc1, Var-1, pcRes1 );
    Extra_TruthSharp( pTemp0, puOn0, puRes0, Var + 1 );
    Extra_TruthSharp( pTemp1, puOn1, puRes1, Var + 1 );
    Extra_TruthOr( pTemp0, pTemp0, pTemp1, Var + 1 );
    Extra_TruthAnd( pTemp1, puOnDc0, puOnDc1, Var + 1 );
    puRes2 = Ivy_TruthIsop5_rec( pTemp0, pTemp1, Var-1, pcRes2 );
    // create the resulting cover
    pcRes->nCubes = pcRes0->nCubes + pcRes1->nCubes + pcRes2->nCubes;
    pcRes->pCubes = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 * pcRes->nCubes );
    k = 0;
    for ( i = 0; i < pcRes0->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes0->pCubes[i] | (1 << ((Var<<1)+1));
    for ( i = 0; i < pcRes1->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes1->pCubes[i] | (1 << ((Var<<1)+0));
    for ( i = 0; i < pcRes1->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes2->pCubes[i];
    assert( k == pcRes->nCubes );
    // create the resulting truth table
    Extra_TruthSharp( pTemp0, Var, uRes0, uRes1, Var + 1 );
    Extra_TruthOr( pTemp0, pTemp0, uRes2, Var + 1 );
    return pTemp0;
}

/**Function*************************************************************

  Synopsis    [Computes ISOP for 5 variables or less.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Ivy_TruthIsop5_rec( unsigned uOn, unsigned uOnDc, int nVars, Ivy_Sop_t * pcRes )
{
    unsigned uMasks[5] = { 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 };
    Ivy_Sop_t cRes0, cRes1, cRes2;
    Ivy_Sop_t * pcRes0 = &cRes0, * pcRes1 = &cRes1, * pcRes2 = &cRes2;
    unsigned uRes0, uRes1, uRes2;
    unsigned uOn0, uOn1, uOnDc0, uOnDc1;
    int i, k, Var;
    assert( nVars <= 5 );
    assert( uOn & ~uOnDc == 0 );
    if ( Extra_TruthIsConst0( uOn == 0 )
    {
        pcRes->nCubes = 0;
        pcRes->pCubes = NULL;
        return 0;
    }
    if ( uOnDc == 0xFFFFFFFF )
    {
        pcRes->nCubes = 1;
        pcRes->pCubes = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 );
        pcRes->pCubes[0] = 0;
        return 0xFFFFFFFF;
    }
    // find the topmost var
    for ( Var = nVars-1; Var >= 0; Var-- )
        if ( Extra_TruthVarInSupport( &uOn, 5, Var ) || 
             Extra_TruthVarInSupport( &uOnDc, 5, Var ) )
             break;
    assert( Var >= 0 );
    // cofactor
    uOn0 = uOn1 = uOn;
    uOnDc0 = uOnDc1 = uOnDc;
    Extra_TruthCofactor0( &uOn0, 5, Var );
    Extra_TruthCofactor1( &uOn1, 5, Var );
    Extra_TruthCofactor0( &uOnDc0, 5, Var );
    Extra_TruthCofactor1( &uOnDc1, 5, Var );
    // solve for cofactors
    uRes0 = Ivy_TruthIsop5_rec( uOn0 & ~uOnDc1, uOnDc0, Var-1, pcRes0 );
    uRes1 = Ivy_TruthIsop5_rec( uOn1 & ~uOnDc0, uOnDc1, Var-1, pcRes1 );
    uRes2 = Ivy_TruthIsop5_rec( (uOn0 & ~uRes0) | (uOn1 & ~uRes1), uOnDc0 & uOnDc1, Var-1, pcRes2 );
    // create the resulting cover
    pcRes->nCubes = pcRes0->nCubes + pcRes1->nCubes + pcRes2->nCubes;
    pcRes->pCubes = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 * pcRes->nCubes );
    k = 0;
    for ( i = 0; i < pcRes0->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes0->pCubes[i] | (1 << ((Var<<1)+1));
    for ( i = 0; i < pcRes1->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes1->pCubes[i] | (1 << ((Var<<1)+0));
    for ( i = 0; i < pcRes1->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes2->pCubes[i];
    assert( k == pcRes->nCubes );
    return (uRes0 & ~uMasks[Var]) | (uRes1 & uMasks[Var]) | uRes2;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


