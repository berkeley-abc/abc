/**CFile****************************************************************

  FileName    [ntlCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [DFS traversal.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Extracts AIG from the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManPerformSynthesis( Aig_Man_t * pAig )
{
    extern Aig_Man_t * Dar_ManBalance( Aig_Man_t * pAig, int fUpdateLevel );
    extern Aig_Man_t * Dar_ManCompress( Aig_Man_t * pAig, int fBalance, int fUpdateLevel, int fVerbose );
    Aig_Man_t * pTemp;
    // perform synthesis
//printf( "Pre-synthesis AIG:  " );
//Aig_ManPrintStats( pAig );
//    pTemp = Dar_ManBalance( pAig, 1 );
    pTemp = Dar_ManCompress( pAig, 1, 1, 0 );
//printf( "Post-synthesis AIG: " );
//Aig_ManPrintStats( pTemp );
    return pTemp;
}

/**Function*************************************************************

  Synopsis    [Testing procedure for insertion of mapping into the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManInsertTest( Ntl_Man_t * p, Aig_Man_t * pAig )
{
    Vec_Ptr_t * vMapping;
    int RetValue;
    vMapping = Ntl_MappingFromAig( pAig );
    RetValue = Ntl_ManInsert( p, vMapping, pAig );
    Vec_PtrFree( vMapping );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Testing procedure for insertion of mapping into the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManInsertTestIf( Ntl_Man_t * p, Aig_Man_t * pAig )
{
    Vec_Ptr_t * vMapping;
    int RetValue;
    vMapping = Ntl_MappingIf( p, pAig );
    RetValue = Ntl_ManInsert( p, vMapping, pAig );
    Vec_PtrFree( vMapping );
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


