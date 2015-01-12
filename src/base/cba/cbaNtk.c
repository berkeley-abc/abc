/**CFile****************************************************************

  FileName    [cbaNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaNtk.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"

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
void Cba_ManAssignInternNamesNtk( Cba_Ntk_t * p )
{
    int i, Type, NameId;
    int nDigits = Abc_Base10Log( Cba_NtkObjNum(p) );
    Cba_NtkForEachObjType( p, Type, i )
    {
        if ( Type == CBA_OBJ_NODE || Type == CBA_OBJ_PIN )
        {
            char Buffer[100];
            sprintf( Buffer, "%s%0*d", "_n_", nDigits, i );
            NameId = Abc_NamStrFindOrAdd( p->pDesign->pNames, Buffer, NULL );
            Vec_IntWriteEntry( &p->vNameIds, i, NameId );
        }
    }
}
void Cba_ManAssignInternNames( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManAssignInternNamesNtk( pNtk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

