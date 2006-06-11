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
int Ivy_ManCheck( Ivy_Man_t * pMan )
{
    Ivy_Obj_t * pObj, * pObj2;
    int i;
    Ivy_ManForEachObj( pMan, pObj, i )
    {
        // skip deleted nodes
        if ( Ivy_ObjIsNone(pObj) )
            continue;
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
            continue;
        }
        if ( Ivy_ObjIsLatch(pObj) )
        {
            if ( Ivy_ObjFaninId1(pObj) != 0 )
            {
                printf( "Ivy_ManCheck: The latch with ID \"%d\" contains second fanin.\n", pObj->Id );
                return 0;
            }
            if ( Ivy_ObjInit(pObj) == 0 )
            {
                printf( "Ivy_ManCheck: The latch with ID \"%d\" does not have initial state.\n", pObj->Id );
                return 0;
            }
            pObj2 = Ivy_TableLookup( pObj );
            if ( pObj2 != pObj )
                printf( "Ivy_ManCheck: Latch with ID \"%d\" is not in the structural hashing table.\n", pObj->Id );
                continue;
        }
        // consider the AND node
        if ( !Ivy_ObjFaninId0(pObj) || !Ivy_ObjFaninId1(pObj) )
        {
            printf( "Ivy_ManCheck: The AIG has internal node \"%d\" with a constant fanin.\n", pObj->Id );
            return 0;
        }
        if ( Ivy_ObjFaninId0(pObj) <= Ivy_ObjFaninId1(pObj) )
        {
            printf( "Ivy_ManCheck: The AIG has node \"%d\" with a wrong ordering of fanins.\n", pObj->Id );
            return 0;
        }
//        if ( Ivy_ObjLevel(pObj) != Ivy_ObjLevelNew(pObj) )
//            printf( "Ivy_ManCheck: Node with ID \"%d\" has level that does not agree with the fanin levels.\n", pObj->Id );
        pObj2 = Ivy_TableLookup( pObj );
        if ( pObj2 != pObj )
            printf( "Ivy_ManCheck: Node with ID \"%d\" is not in the structural hashing table.\n", pObj->Id );
    }
    // count the number of nodes in the table
    if ( Ivy_TableCountEntries(pMan) != Ivy_ManAndNum(pMan) + Ivy_ManExorNum(pMan) + Ivy_ManLatchNum(pMan) )
    {
        printf( "Ivy_ManCheck: The number of nodes in the structural hashing table is wrong.\n" );
        return 0;
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


