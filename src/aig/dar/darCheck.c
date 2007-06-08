/**CFile****************************************************************

  FileName    [darCheck.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [AIG checking procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darCheck.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

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
int Dar_ManCheck( Dar_Man_t * p )
{
    Dar_Obj_t * pObj, * pObj2;
    int i;
    // check primary inputs
    Dar_ManForEachPi( p, pObj, i )
    {
        if ( Dar_ObjFanin0(pObj) || Dar_ObjFanin1(pObj) )
        {
            printf( "Dar_ManCheck: The PI node \"%p\" has fanins.\n", pObj );
            return 0;
        }
    }
    // check primary outputs
    Dar_ManForEachPo( p, pObj, i )
    {
        if ( !Dar_ObjFanin0(pObj) )
        {
            printf( "Dar_ManCheck: The PO node \"%p\" has NULL fanin.\n", pObj );
            return 0;
        }
        if ( Dar_ObjFanin1(pObj) )
        {
            printf( "Dar_ManCheck: The PO node \"%p\" has second fanin.\n", pObj );
            return 0;
        }
    }
    // check internal nodes
    Dar_ManForEachObj( p, pObj, i )
    {
        if ( !Dar_ObjIsNode(pObj) )
            continue;
        if ( !Dar_ObjFanin0(pObj) || !Dar_ObjFanin1(pObj) )
        {
            printf( "Dar_ManCheck: The AIG has internal node \"%p\" with a NULL fanin.\n", pObj );
            return 0;
        }
        if ( Dar_ObjFanin0(pObj)->Id >= Dar_ObjFanin1(pObj)->Id )
        {
            printf( "Dar_ManCheck: The AIG has node \"%p\" with a wrong ordering of fanins.\n", pObj );
            return 0;
        }
        pObj2 = Dar_TableLookup( p, pObj );
        if ( pObj2 != pObj )
        {
            printf( "Dar_ManCheck: Node \"%p\" is not in the structural hashing table.\n", pObj );
            return 0;
        }
    }
    // count the total number of nodes
    if ( Dar_ManObjNum(p) != 1 + Dar_ManPiNum(p) + Dar_ManPoNum(p) + Dar_ManBufNum(p) + Dar_ManAndNum(p) + Dar_ManExorNum(p) + Dar_ManLatchNum(p) )
    {
        printf( "Dar_ManCheck: The number of created nodes is wrong.\n" );
        printf( "C1 = %d. Pi = %d. Po = %d. Buf = %d. And = %d. Xor = %d. Lat = %d. Total = %d.\n",
            1, Dar_ManPiNum(p), Dar_ManPoNum(p), Dar_ManBufNum(p), Dar_ManAndNum(p), Dar_ManExorNum(p), Dar_ManLatchNum(p), 
            1 + Dar_ManPiNum(p) + Dar_ManPoNum(p) + Dar_ManBufNum(p) + Dar_ManAndNum(p) + Dar_ManExorNum(p) + Dar_ManLatchNum(p) );
        printf( "Created = %d. Deleted = %d. Existing = %d.\n",
            p->nCreated, p->nDeleted, p->nCreated - p->nDeleted );
        return 0;
    }
    // count the number of nodes in the table
    if ( Dar_TableCountEntries(p) != Dar_ManAndNum(p) + Dar_ManExorNum(p) + Dar_ManLatchNum(p) )
    {
        printf( "Dar_ManCheck: The number of nodes in the structural hashing table is wrong.\n" );
        printf( "Entries = %d. And = %d. Xor = %d. Lat = %d. Total = %d.\n", 
            Dar_TableCountEntries(p), Dar_ManAndNum(p), Dar_ManExorNum(p), Dar_ManLatchNum(p),
            Dar_ManAndNum(p) + Dar_ManExorNum(p) + Dar_ManLatchNum(p) );

        return 0;
    }
//    if ( !Dar_ManIsAcyclic(p) )
//        return 0;
    return 1; 
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


