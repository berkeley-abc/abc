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
#include "mem.h"

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

static unsigned * Ivy_TruthIsop_rec( unsigned * puOn, unsigned * puOnDc, int nVars, Ivy_Sop_t * pcRes );
static unsigned   Ivy_TruthIsop5_rec( unsigned uOn, unsigned uOnDc, int nVars, Ivy_Sop_t * pcRes );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Deallocates memory used for computing ISOPs from TTs.]

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

  Synopsis    [Computes ISOP from TT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_TruthIsopOne( unsigned * puTruth, int nVars, Vec_Int_t * vCover )
{
    Ivy_Sop_t cRes, * pcRes = &cRes;
    unsigned * pResult;
    int i;
    assert( nVars >= 0 && nVars < 16 );
    // if nVars < 5, make sure it does not depend on those vars
    for ( i = nVars; i < 5; i++ )
        assert( !Extra_TruthVarInSupport(puTruth, 5, i) );
    // prepare memory manager
    if ( s_Man == NULL )
        s_Man = Mem_FlexStart();
    else
        Mem_FlexRestart( s_Man );
    // compute ISOP
    pResult = Ivy_TruthIsop_rec( puTruth, puTruth, nVars, pcRes );
//    Extra_PrintBinary( stdout, puTruth, 1 << nVars ); printf( "\n" );
//    Extra_PrintBinary( stdout, pResult, 1 << nVars ); printf( "\n" );
    assert( Extra_TruthIsEqual( puTruth, pResult, nVars ) );
//printf( "%d ", Mem_FlexReadMemUsage(s_Man) );
//printf( "%d ", pcRes->nCubes );
    // copy the truth table
    Vec_IntClear( vCover );
    for ( i = 0; i < pcRes->nCubes; i++ )
        Vec_IntPush( vCover, pcRes->pCubes[i] );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Computes ISOP from TT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_TruthIsop( unsigned * puTruth, int nVars, Vec_Int_t * vCover )
{
    Ivy_Sop_t cRes, * pcRes = &cRes;
    unsigned * pResult;
    int i;
    assert( nVars >= 0 && nVars < 16 );
    // if nVars < 5, make sure it does not depend on those vars
    for ( i = nVars; i < 5; i++ )
        assert( !Extra_TruthVarInSupport(puTruth, 5, i) );
    // prepare memory manager
    if ( s_Man == NULL )
        s_Man = Mem_FlexStart();
    else
        Mem_FlexRestart( s_Man );
    // compute ISOP
    pResult = Ivy_TruthIsop_rec( puTruth, puTruth, nVars, pcRes );
//    Extra_PrintBinary( stdout, puTruth, 1 << nVars ); printf( "\n" );
//    Extra_PrintBinary( stdout, pResult, 1 << nVars ); printf( "\n" );
    assert( Extra_TruthIsEqual( puTruth, pResult, nVars ) );
//printf( "%d ", Mem_FlexReadMemUsage(s_Man) );
//printf( "%d ", pcRes->nCubes );
    // copy the truth table
    Vec_IntClear( vCover );
    for ( i = 0; i < pcRes->nCubes; i++ )
        Vec_IntPush( vCover, pcRes->pCubes[i] );

    // try other polarity
    Mem_FlexRestart( s_Man );
    Extra_TruthNot( puTruth, puTruth, nVars );
    pResult = Ivy_TruthIsop_rec( puTruth, puTruth, nVars, pcRes );
    assert( Extra_TruthIsEqual( puTruth, pResult, nVars ) );
    Extra_TruthNot( puTruth, puTruth, nVars );
    if ( Vec_IntSize(vCover) < pcRes->nCubes )
        return 0;

    // copy the truth table
    Vec_IntClear( vCover );
    for ( i = 0; i < pcRes->nCubes; i++ )
        Vec_IntPush( vCover, pcRes->pCubes[i] );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes ISOP 6 variables or more.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Ivy_TruthIsop_rec( unsigned * puOn, unsigned * puOnDc, int nVars, Ivy_Sop_t * pcRes )
{
    Ivy_Sop_t cRes0, cRes1, cRes2;
    Ivy_Sop_t * pcRes0 = &cRes0, * pcRes1 = &cRes1, * pcRes2 = &cRes2;
    unsigned * puRes0, * puRes1, * puRes2;
    unsigned * puOn0, * puOn1, * puOnDc0, * puOnDc1, * pTemp, * pTemp0, * pTemp1;
    int i, k, Var, nWords, nWordsAll;
    assert( Extra_TruthIsImply( puOn, puOnDc, nVars ) );
    // allocate room for the resulting truth table
    nWordsAll = Extra_TruthWordNum( nVars );
    pTemp = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 * nWordsAll );
    // check for constants
    if ( Extra_TruthIsConst0( puOn, nVars ) )
    {
        pcRes->nCubes = 0;
        pcRes->pCubes = NULL;
        Extra_TruthClear( pTemp, nVars );
        return pTemp;
    }
    if ( Extra_TruthIsConst1( puOnDc, nVars ) )
    {
        pcRes->nCubes = 1;
        pcRes->pCubes = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 );
        pcRes->pCubes[0] = 0;
        Extra_TruthFill( pTemp, nVars );
        return pTemp;
    }
    assert( nVars > 0 );
    // find the topmost var
    for ( Var = nVars-1; Var >= 0; Var-- )
        if ( Extra_TruthVarInSupport( puOn, nVars, Var ) || 
             Extra_TruthVarInSupport( puOnDc, nVars, Var ) )
             break;
    assert( Var >= 0 );
    // consider a simple case when one-word computation can be used
    if ( Var < 5 )
    {
        unsigned uRes = Ivy_TruthIsop5_rec( puOn[0], puOnDc[0], Var+1, pcRes );
        for ( i = 0; i < nWordsAll; i++ )
            pTemp[i] = uRes;
        return pTemp;
    }
    assert( Var >= 5 );
    nWords = Extra_TruthWordNum( Var );
    // cofactor
    puOn0   = puOn;    puOn1   = puOn + nWords;
    puOnDc0 = puOnDc;  puOnDc1 = puOnDc + nWords;
    pTemp0  = pTemp;   pTemp1  = pTemp + nWords;
    // solve for cofactors
    Extra_TruthSharp( pTemp0, puOn0, puOnDc1, Var );
    puRes0 = Ivy_TruthIsop_rec( pTemp0, puOnDc0, Var, pcRes0 );
    Extra_TruthSharp( pTemp1, puOn1, puOnDc0, Var );
    puRes1 = Ivy_TruthIsop_rec( pTemp1, puOnDc1, Var, pcRes1 );
    Extra_TruthSharp( pTemp0, puOn0, puRes0, Var );
    Extra_TruthSharp( pTemp1, puOn1, puRes1, Var );
    Extra_TruthOr( pTemp0, pTemp0, pTemp1, Var );
    Extra_TruthAnd( pTemp1, puOnDc0, puOnDc1, Var );
    puRes2 = Ivy_TruthIsop_rec( pTemp0, pTemp1, Var, pcRes2 );
    // create the resulting cover
    pcRes->nCubes = pcRes0->nCubes + pcRes1->nCubes + pcRes2->nCubes;
    pcRes->pCubes = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 * pcRes->nCubes );
    k = 0;
    for ( i = 0; i < pcRes0->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes0->pCubes[i] | (1 << ((Var<<1)+1));
    for ( i = 0; i < pcRes1->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes1->pCubes[i] | (1 << ((Var<<1)+0));
    for ( i = 0; i < pcRes2->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes2->pCubes[i];
    assert( k == pcRes->nCubes );
    // create the resulting truth table
    Extra_TruthOr( pTemp0, puRes0, puRes2, Var );
    Extra_TruthOr( pTemp1, puRes1, puRes2, Var );
    // copy the table if needed
    nWords <<= 1;
    for ( i = 1; i < nWordsAll/nWords; i++ )
        for ( k = 0; k < nWords; k++ )
            pTemp[i*nWords + k] = pTemp[k];
    // verify in the end
//    assert( Extra_TruthIsImply( puOn, pTemp, nVars ) );
//    assert( Extra_TruthIsImply( pTemp, puOnDc, nVars ) );
    return pTemp;
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
    unsigned uOn0, uOn1, uOnDc0, uOnDc1, uRes0, uRes1, uRes2;
    int i, k, Var;
    assert( nVars <= 5 );
    assert( (uOn & ~uOnDc) == 0 );
    if ( uOn == 0 )
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
    assert( nVars > 0 );
    // find the topmost var
    for ( Var = nVars-1; Var >= 0; Var-- )
        if ( Extra_TruthVarInSupport( &uOn, 5, Var ) || 
             Extra_TruthVarInSupport( &uOnDc, 5, Var ) )
             break;
    assert( Var >= 0 );
    // cofactor
    uOn0   = uOn1   = uOn;
    uOnDc0 = uOnDc1 = uOnDc;
    Extra_TruthCofactor0( &uOn0, Var + 1, Var );
    Extra_TruthCofactor1( &uOn1, Var + 1, Var );
    Extra_TruthCofactor0( &uOnDc0, Var + 1, Var );
    Extra_TruthCofactor1( &uOnDc1, Var + 1, Var );
    // solve for cofactors
    uRes0 = Ivy_TruthIsop5_rec( uOn0 & ~uOnDc1, uOnDc0, Var, pcRes0 );
    uRes1 = Ivy_TruthIsop5_rec( uOn1 & ~uOnDc0, uOnDc1, Var, pcRes1 );
    uRes2 = Ivy_TruthIsop5_rec( (uOn0 & ~uRes0) | (uOn1 & ~uRes1), uOnDc0 & uOnDc1, Var, pcRes2 );
    // create the resulting cover
    pcRes->nCubes = pcRes0->nCubes + pcRes1->nCubes + pcRes2->nCubes;
    pcRes->pCubes = (unsigned *)Mem_FlexEntryFetch( s_Man, 4 * pcRes->nCubes );
    k = 0;
    for ( i = 0; i < pcRes0->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes0->pCubes[i] | (1 << ((Var<<1)+1));
    for ( i = 0; i < pcRes1->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes1->pCubes[i] | (1 << ((Var<<1)+0));
    for ( i = 0; i < pcRes2->nCubes; i++ )
        pcRes->pCubes[k++] = pcRes2->pCubes[i];
    assert( k == pcRes->nCubes );
    // derive the final truth table
    uRes2 |= (uRes0 & ~uMasks[Var]) | (uRes1 & uMasks[Var]);
//    assert( (uOn & ~uRes2) == 0 );
//    assert( (uRes2 & ~uOnDc) == 0 );
    return uRes2;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


