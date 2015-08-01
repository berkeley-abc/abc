/**CFile****************************************************************

  FileName    [cbaBlast.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Collapsing word-level design.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 21, 2015.]

  Revision    [$Id: cbaBlast.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "base/abc/abc.h"
#include "map/mio/mio.h"
#include "bool/dec/dec.h"
#include "base/main/mainInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cba_ManBlast( Cba_Man_t * p, int fBarBufs, int fVerbose )
{
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cba_Man_t * Cba_ManInsertGia( Cba_Man_t * p, Gia_Man_t * pGia )
{
    return NULL;
}
Cba_Man_t * Cba_ManInsertAbc( Cba_Man_t * p, void * pAbc )
{
    Abc_Ntk_t * pNtk = (Abc_Ntk_t *)pAbc;
    return (Cba_Man_t *)pNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

