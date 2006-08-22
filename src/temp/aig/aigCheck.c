/**CFile****************************************************************

  FileName    [aigCheck.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Minimalistic And-Inverter Graph package.]

  Synopsis    [AIG checking procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: aigCheck.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks the consistency of the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManCheck( Aig_Man_t * p )
{
    Aig_Obj_t * pObj, * pObj2;
    int i;
    // check primary inputs
    Aig_ManForEachPi( p, pObj, i )
    {
        if ( Aig_ObjFanin0(pObj) || Aig_ObjFanin1(pObj) )
        {
            printf( "Aig_ManCheck: The PI node \"%p\" has fanins.\n", pObj );
            return 0;
        }
    }
    // check primary outputs
    Aig_ManForEachPo( p, pObj, i )
    {
        if ( !Aig_ObjFanin0(pObj) )
        {
            printf( "Aig_ManCheck: The PO node \"%p\" has NULL fanin.\n", pObj );
            return 0;
        }
        if ( Aig_ObjFanin1(pObj) )
        {
            printf( "Aig_ManCheck: The PO node \"%p\" has second fanin.\n", pObj );
            return 0;
        }
    }
    // check internal nodes
    Aig_ManForEachNode( p, pObj, i )
    {
        if ( !Aig_ObjFanin0(pObj) || !Aig_ObjFanin1(pObj) )
        {
            printf( "Aig_ManCheck: The AIG has internal node \"%p\" with a NULL fanin.\n", pObj );
            return 0;
        }
        if ( Aig_ObjFanin0(pObj) >= Aig_ObjFanin1(pObj) )
        {
            printf( "Aig_ManCheck: The AIG has node \"%p\" with a wrong ordering of fanins.\n", pObj );
            return 0;
        }
        pObj2 = Aig_TableLookup( p, pObj );
        if ( pObj2 != pObj )
        {
            printf( "Aig_ManCheck: Node \"%p\" is not in the structural hashing table.\n", pObj );
            return 0;
        }
    }
    // count the total number of nodes
    if ( Aig_ManObjNum(p) != 1 + Aig_ManPiNum(p) + Aig_ManPoNum(p) + Aig_ManAndNum(p) + Aig_ManExorNum(p) )
    {
        printf( "Aig_ManCheck: The number of created nodes is wrong.\n" );
        return 0;
    }
    // count the number of nodes in the table
    if ( Aig_TableCountEntries(p) != Aig_ManAndNum(p) + Aig_ManExorNum(p) )
    {
        printf( "Aig_ManCheck: The number of nodes in the structural hashing table is wrong.\n" );
        return 0;
    }
//    if ( !Aig_ManIsAcyclic(p) )
//        return 0;
    return 1; 
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


