/**CFile****************************************************************

  FileName    [simMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Simulation manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: simMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "sim.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the simulatin manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sim_Man_t * Sim_ManStart( Abc_Ntk_t * pNtk )
{
    Sim_Man_t * p;
    int i;
    // start the manager
    p = ALLOC( Sim_Man_t, 1 );
    memset( p, 0, sizeof(Sim_Man_t) );
    p->pNtk = pNtk;
    // internal simulation information
    p->nSimBits   = 2048;
    p->nSimWords  = SIM_NUM_WORDS(p->nSimBits);
    p->vSim0      = Sim_UtilInfoAlloc( Abc_NtkObjNumMax(pNtk), p->nSimWords, 0 );
    p->vSim1      = Sim_UtilInfoAlloc( Abc_NtkObjNumMax(pNtk), p->nSimWords, 0 );
    // support information
    p->nSuppBits  = Abc_NtkCiNum(pNtk);
    p->nSuppWords = SIM_NUM_WORDS(p->nSuppBits);
    p->vSuppStr   = Sim_UtilInfoAlloc( Abc_NtkObjNumMax(pNtk), p->nSuppWords, 1 );
    p->vSuppFun   = Sim_UtilInfoAlloc( Abc_NtkCoNum(p->pNtk),  p->nSuppWords, 1 );
    // other data
    p->pMmPat     = Extra_MmFixedStart( sizeof(Sim_Pat_t) + p->nSuppWords * sizeof(unsigned) ); 
    p->vFifo      = Vec_PtrAlloc( 100 );
    p->vDiffs     = Vec_IntAlloc( 100 );
    // allocate support targets
    p->vSuppTargs = Vec_PtrAlloc( p->nSuppBits );
    p->vSuppTargs->nSize = p->nSuppBits;
    for ( i = 0; i < p->nSuppBits; i++ )
        p->vSuppTargs->pArray[i] = Vec_IntAlloc( 8 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the simulatin manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_ManStop( Sim_Man_t * p )
{
    Sim_ManPrintStats( p );
    if ( p->vSim0 )        Sim_UtilInfoFree( p->vSim0 );       
    if ( p->vSim1 )        Sim_UtilInfoFree( p->vSim1 );       
    if ( p->vSuppStr )     Sim_UtilInfoFree( p->vSuppStr );    
    if ( p->vSuppFun )     Sim_UtilInfoFree( p->vSuppFun );    
    if ( p->vUnateVarsP )  Sim_UtilInfoFree( p->vUnateVarsP ); 
    if ( p->vUnateVarsN )  Sim_UtilInfoFree( p->vUnateVarsN ); 
    if ( p->pMatSym )      Extra_BitMatrixStop( p->pMatSym );
    if ( p->pMatNonSym )   Extra_BitMatrixStop( p->pMatNonSym );
    if ( p->vSuppTargs )   Vec_PtrFreeFree( p->vSuppTargs );
    if ( p->vUnateTargs )  Vec_PtrFree( p->vUnateTargs );
    if ( p->vSymmTargs )   Vec_PtrFree( p->vSymmTargs );
    if ( p->pMmPat )       Extra_MmFixedStop( p->pMmPat, 0 );
    if ( p->vFifo )        Vec_PtrFree( p->vFifo );
    if ( p->vDiffs )       Vec_IntFree( p->vDiffs );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Returns one simulation pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sim_Pat_t * Sim_ManPatAlloc( Sim_Man_t * p )
{
    Sim_Pat_t * pPat;
    pPat = (Sim_Pat_t *)Extra_MmFixedEntryFetch( p->pMmPat );
    pPat->Output = -1;
    pPat->pData  = (unsigned *)((char *)pPat + sizeof(Sim_Pat_t));
    memset( pPat->pData, 0, p->nSuppWords * sizeof(unsigned) );
    return pPat;
}

/**Function*************************************************************

  Synopsis    [Returns one simulation pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_ManPatFree( Sim_Man_t * p, Sim_Pat_t * pPat )
{
    Extra_MmFixedEntryRecycle( p->pMmPat, (char *)pPat );
}

/**Function*************************************************************

  Synopsis    [Prints the manager statisticis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_ManPrintStats( Sim_Man_t * p )
{
    printf( "Inputs = %d. Outputs = %d. Sim words = %d.\n", 
        Abc_NtkCiNum(p->pNtk), Abc_NtkCoNum(p->pNtk), p->nSimWords );
    printf( "Total struct supps = %6d.\n", Sim_UtilCountSuppSizes(p, 1) );
    printf( "Total func supps   = %6d.\n", Sim_UtilCountSuppSizes(p, 0) );
    printf( "Total targets      = %6d.\n", Vec_PtrSizeSize(p->vSuppTargs) );
    printf( "Total sim patterns = %6d.\n", Vec_PtrSize(p->vFifo) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


