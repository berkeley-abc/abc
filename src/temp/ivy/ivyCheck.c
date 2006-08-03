/**CFile****************************************************************

  FileName    [ivyCheck.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [AIG checking procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyCheck.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

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
int Ivy_ManCheck( Ivy_Man_t * p )
{
    Ivy_Obj_t * pObj, * pObj2;
    int i;
    Ivy_ManForEachObj( p, pObj, i )
    {
        // skip deleted nodes
        if ( Ivy_ObjId(pObj) != i )
        {
            printf( "Ivy_ManCheck: Node with ID %d is listed as number %d in the array of objects.\n", pObj->Id, i );
            return 0;
        }
        // consider the constant node and PIs
        if ( i == 0 || Ivy_ObjIsPi(pObj) )
        {
            if ( Ivy_ObjFaninId0(pObj) || Ivy_ObjFaninId1(pObj) || Ivy_ObjLevel(pObj) )
            {
                printf( "Ivy_ManCheck: The AIG has non-standard constant or PI node with ID \"%d\".\n", pObj->Id );
                return 0;
            }
            continue;
        }
        if ( Ivy_ObjIsPo(pObj) )
        {
            if ( Ivy_ObjFaninId1(pObj) )
            {
                printf( "Ivy_ManCheck: The AIG has non-standard PO node with ID \"%d\".\n", pObj->Id );
                return 0;
            }
            continue;
        }
        if ( Ivy_ObjIsBuf(pObj) )
        {
            if ( Ivy_ObjFanin1(pObj) )
            {
                printf( "Ivy_ManCheck: The buffer with ID \"%d\" contains second fanin.\n", pObj->Id );
                return 0;
            }
            continue;
        }
        if ( Ivy_ObjIsLatch(pObj) )
        {
            if ( Ivy_ObjFanin1(pObj) )
            {
                printf( "Ivy_ManCheck: The latch with ID \"%d\" contains second fanin.\n", pObj->Id );
                return 0;
            }
            if ( Ivy_ObjInit(pObj) == IVY_INIT_NONE )
            {
                printf( "Ivy_ManCheck: The latch with ID \"%d\" does not have initial state.\n", pObj->Id );
                return 0;
            }
            pObj2 = Ivy_TableLookup( p, pObj );
            if ( pObj2 != pObj )
                printf( "Ivy_ManCheck: Latch with ID \"%d\" is not in the structural hashing table.\n", pObj->Id );
                continue;
        }
        // consider the AND node
        if ( !Ivy_ObjFanin0(pObj) || !Ivy_ObjFanin1(pObj) )
        {
            printf( "Ivy_ManCheck: The AIG has internal node \"%d\" with a NULL fanin.\n", pObj->Id );
            return 0;
        }
        if ( Ivy_ObjFaninId0(pObj) >= Ivy_ObjFaninId1(pObj) )
        {
            printf( "Ivy_ManCheck: The AIG has node \"%d\" with a wrong ordering of fanins.\n", pObj->Id );
            return 0;
        }
        if ( Ivy_ObjLevel(pObj) != Ivy_ObjLevelNew(pObj) )
            printf( "Ivy_ManCheck: Node with ID \"%d\" has level %d but should have level %d.\n", pObj->Id, Ivy_ObjLevel(pObj), Ivy_ObjLevelNew(pObj) );
        pObj2 = Ivy_TableLookup( p, pObj );
        if ( pObj2 != pObj )
            printf( "Ivy_ManCheck: Node with ID \"%d\" is not in the structural hashing table.\n", pObj->Id );
        if ( Ivy_ObjRefs(pObj) == 0 )
            printf( "Ivy_ManCheck: Node with ID \"%d\" has no fanouts.\n", pObj->Id );
        // check fanouts
        if ( p->vFanouts && Ivy_ObjRefs(pObj) != Ivy_ObjFanoutNum(p, pObj) )
            printf( "Ivy_ManCheck: Node with ID \"%d\" has mismatch between the number of fanouts and refs.\n", pObj->Id );
    }
    // count the number of nodes in the table
    if ( Ivy_TableCountEntries(p) != Ivy_ManAndNum(p) + Ivy_ManExorNum(p) + Ivy_ManLatchNum(p) )
    {
        printf( "Ivy_ManCheck: The number of nodes in the structural hashing table is wrong.\n" );
        return 0;
    }
    if ( !Ivy_ManIsAcyclic(p) )
        return 0;
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


