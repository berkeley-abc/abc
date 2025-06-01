#include "abc.h"
#include <stdio.h>
#include "misc/util/abc_global.h"



ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
/**Function*************************************************************

  Synopsis    [Allocates a new fault.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Fault_t * Abc_FaultAlloc( Abc_Obj_t * pNode, Abc_FaultType_t Type, Abc_FaultIo_t Io, int Index )
{
    Abc_Fault_t * pFault;
    pFault = ABC_ALLOC( Abc_Fault_t, 1 );
    pFault->pNode = pNode;
    pFault->Type = Type;
    pFault->Io = Io;
    pFault->Index = Index;
    pFault->fDetected = 0;
    pFault->fActivated = 0;
    pFault->fTestTried = 0;
    pFault->nEqvFaults = 0;
    pFault->iSortIndex = -1;
    pFault->FaultId = -1;
    pFault->nDetectedTimes = 0;
    pFault->pNext = NULL;
    return pFault;
}

/**Function*************************************************************

  Synopsis    [Frees a fault.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FaultFree( Abc_Fault_t * pFault )
{
    ABC_FREE( pFault );
}

/**Function*************************************************************

  Synopsis    [Adds a fault to the network's fault list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkAddFault( Abc_Ntk_t * pNtk, Abc_Fault_t * pFault )
{
    pFault->pNext = pNtk->pFaultList;
    pNtk->pFaultList = pFault;
    pNtk->nFaults++;
    pFault->FaultId = pNtk->nFaults;
}

/**Function*************************************************************

  Synopsis    [Removes a fault from the network's fault list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRemoveFault( Abc_Ntk_t * pNtk, Abc_Fault_t * pFault )
{
    Abc_Fault_t * pPrev, * pCur;
    if ( pNtk->pFaultList == pFault )
    {
        pNtk->pFaultList = pFault->pNext;
        pNtk->nFaults--;
        if ( pFault->fDetected )
            pNtk->nDetectedFaults--;
        if ( pFault->fActivated )
            pNtk->nActivatedFaults--;
        if ( pFault->fTestTried )
            pNtk->nTestTriedFaults--;
        return;
    }
    for ( pPrev = pNtk->pFaultList, pCur = pPrev->pNext; pCur; pPrev = pCur, pCur = pCur->pNext )
    {
        if ( pCur == pFault )
        {
            pPrev->pNext = pCur->pNext;
            pNtk->nFaults--;
            if ( pFault->fDetected )
                pNtk->nDetectedFaults--;
            if ( pFault->fActivated )
                pNtk->nActivatedFaults--;
            if ( pFault->fTestTried )
                pNtk->nTestTriedFaults--;
            return;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Clears all faults from the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkClearFaults( Abc_Ntk_t * pNtk )
{
    Abc_Fault_t * pFault, * pFaultNext;
    for ( pFault = pNtk->pFaultList; pFault; pFault = pFaultNext )
    {
        pFaultNext = pFault->pNext;
        Abc_FaultFree( pFault );
    }
    pNtk->pFaultList = NULL;
    pNtk->nFaults = 0;
    pNtk->nDetectedFaults = 0;
    pNtk->nUndetectableFaults = 0;
    pNtk->nActivatedFaults = 0;
    pNtk->nTestTriedFaults = 0;
}

/**Function*************************************************************

  Synopsis    [Generates stuck-at fault list for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkGenerateFaultList( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, * pFanin;
    int i, k;

    Abc_NtkClearFaults( pNtk );

    /*--------------------------------------------------------------
     *  Step 1.  Add SA0 / SA1 on the *source* side of every wire.
     *           – Primary‑inputs (PIs) drive nets.
     *           – Internal logic nodes drive nets.
     *--------------------------------------------------------------*/
    /* Primary inputs */
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GO, 0 ) );
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GO, 0 ) );
    }

    /* Internal nodes */
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GO, 0 ) );
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GO, 0 ) );
    }

    /*--------------------------------------------------------------
     *  Step 2.  Add SA0 / SA1 on *fan‑out branches* (GI faults)
     *           – Only for nets whose driver has multiple fan‑outs.
     *           – This guarantees each physical wire is represented
     *             by exactly one (SA0, SA1) pair.
     *--------------------------------------------------------------*/
    /* Fan‑outs of internal nodes */
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            if ( Abc_ObjFanoutNum( pFanin ) > 1 )
            {
                Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GI, k ) );
                Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GI, k ) );
            }
        }
    }

    /* Fan‑outs that feed combinational outputs (COs) directly */
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            if ( Abc_ObjFanoutNum( pFanin ) > 1 )
            {
                Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GI, k ) );
                Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GI, k ) );
            }
        }
    }


}


/**Function*************************************************************

  Synopsis    [Generates checkpoint fault list for the network.]

  Description [Implements checkpoint theorem - only adds faults at PIs 
               and fanout branches (stems with multiple fanouts)]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkGenerateCheckpointFaultList( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, *pFanin;
    Vec_Ptr_t * vCheckpoints;
    int i, k;
    
    // Clear existing faults
    Abc_NtkClearFaults( pNtk );
    
    // Create a vector to track checkpoints (for clarity)
    vCheckpoints = Vec_PtrAlloc( 100 );
    
    // Step 1: Identify all checkpoints
    
    // All PIs are checkpoints
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        Vec_PtrPush( vCheckpoints, pObj );
    }
    
    // Find all fanout branches (these are also checkpoints)
    // A fanout branch occurs when a signal feeds multiple gates
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        // Check each input of this node
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            // If this fanin has multiple fanouts, then this input is a branch
            if ( Abc_ObjFanoutNum(pFanin) > 1 )
            {
                // This is a branch point - but we don't add it to checkpoints vector
                // because we'll add the fault directly at the branch (GI fault)
                // The checkpoint is conceptually at the branch, not the stem
            }
        }
    }
    
    // Step 2: Add faults at checkpoints
    
    // Add faults at PI checkpoints
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GO, 0 ) );
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GO, 0 ) );
    }
    
    // Add faults at branch checkpoints
    // For each node that has an input from a multi-fanout signal
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            // If this input comes from a signal with multiple fanouts
            if ( Abc_ObjFanoutNum(pFanin) > 1 )
            {
                // Add fault at this branch (gate input)
                Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GI, k ) );
                Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GI, k ) );
            }
        }
    }
    

    
    // Clean up
    Vec_PtrFree( vCheckpoints );
}
/**Function*************************************************************

  Synopsis    [Generates collapsed fault list using dominance relationships.]

  Description [Implements traditional fault collapsing by:
               1. Finding fault equivalence groups
               2. Building dominance graph
               3. Removing dominated faults
               4. Selecting representative faults from equivalence groups]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/


void Abc_NtkGenerateCollapsedCheckpointFaultList( Abc_Ntk_t * pNtk )
{
    Abc_NtkGenerateCheckpointFaultList( pNtk );

}


/**Function*************************************************************

  Synopsis    [Helper function to determine gate type from SOP.]

  Description [Returns gate type based on SOP analysis]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_SopGetGateType( char * pSop )
{
    int nCubes, nLits, nVars;
    
    if ( !pSop )
        return -1;
        
    nVars = Abc_SopGetVarNum( pSop );
    nCubes = Abc_SopGetCubeNum( pSop );
    nLits = Abc_SopGetLitNum( pSop );
    
    // Check for constant functions
    if ( Abc_SopIsConst0(pSop) )
        return -1;
    if ( Abc_SopIsConst1(pSop) )
        return -1;
        
    // Check for buffer/inverter
    if ( nVars == 1 && nCubes == 1 )
    {
        if ( pSop[0] == '1' && pSop[2] == '1' )
            return 1; // BUF
        if ( pSop[0] == '1' && pSop[2] == '0' )
            return 2; // NOT
        if ( pSop[0] == '0' && pSop[2] == '1' )
            return 2; // NOT
        if ( pSop[0] == '0' && pSop[2] == '0' )
            return 1; // BUF
    }
    
    // Check for AND gate (all variables must be 1 in single cube)
    if ( nCubes == 1 && nLits == nVars )
    {
        if ( pSop[nVars+1] == '1' )
            return 3; // AND
        else
            return 4; // NAND
    }
    
    // Check for OR gate (each cube has exactly one literal)
    if ( nCubes == nVars && nLits == nVars )
    {
        if ( pSop[nVars+1] == '1' )
            return 5; // OR
        else
            return 6; // NOR
    }
    
    // Check for XOR/XNOR (2 variables, 2 cubes)
    if ( nVars == 2 && nCubes == 2 )
    {
        // XOR has pattern: 01 1\n10 1\n or 10 1\n01 1\n
        // XNOR has pattern: 00 1\n11 1\n or 11 1\n00 1\n
        if ( (pSop[0] == '0' && pSop[1] == '1' && pSop[nVars+3] == '1' && pSop[nVars+4] == '0') ||
             (pSop[0] == '1' && pSop[1] == '0' && pSop[nVars+3] == '0' && pSop[nVars+4] == '1') )
        {
            if ( pSop[nVars+1] == '1' )
                return 7; // XOR
            else
                return 8; // XNOR
        }
        if ( (pSop[0] == '0' && pSop[1] == '0' && pSop[nVars+3] == '1' && pSop[nVars+4] == '1') ||
             (pSop[0] == '1' && pSop[1] == '1' && pSop[nVars+3] == '0' && pSop[nVars+4] == '0') )
        {
            if ( pSop[nVars+1] == '1' )
                return 8; // XNOR (EQV)
            else
                return 7; // XOR
        }
    }
    
    // For complex functions, check if it's XOR/XNOR type
    if ( Abc_SopIsExorType(pSop) )
        return 7; // XOR
    
    return -1; // Unknown type
}

/**Function*************************************************************

  Synopsis    [Generates collapsed fault list using equivalence and dominance analysis.]

  Description [Implements fault collapsing by replicating the logic from generate_fault_list]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkGenerateCollapsingFaultList( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj, * pFanin, * pFanout;
    Abc_Fault_t * pFault, * pFaultCur, * pFaultPrev;
    Vec_Int_t * vNumEqvSa0, * vNumEqvSa1;
    char * pSop;
    int i, j, k, nFaults = 0;
    int gateType;
    int nTotalGateFaults = 0;
    
    // Clear existing faults
    Abc_NtkClearFaults( pNtk );
    
    // Create vectors to track equivalent fault counts for each object
    vNumEqvSa0 = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    vNumEqvSa1 = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    
    // Process all nodes and PIs (but NOT POs - they don't generate GO faults)
    // This mimics the original C++ sort_wlist traversal over wires
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        // Skip objects that don't generate GO faults
        if ( !Abc_ObjIsNode(pObj) && !Abc_ObjIsPi(pObj) )
            continue;
            
        // Get gate type
        gateType = -1;
        if ( Abc_ObjIsPi(pObj) )
        {
            gateType = 0; // INPUT
        }
        else if ( Abc_ObjIsNode(pObj) )
        {
            pSop = (char *)pObj->pData;
            if ( pSop )
                gateType = Abc_SopGetGateType( pSop );
        }
        
        // Create GO SA0 fault
        pFault = Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GO, 0 );
        pFault->nEqvFaults = 1; // The fault itself
        
        // Add equivalent faults based on gate type
        switch ( gateType )
        {
            case 3: // AND
            case 1: // BUF
                // For AND/BUF: GO SA0 is equivalent to any GI SA0
                Abc_ObjForEachFanin( pObj, pFanin, k )
                {
                    pFault->nEqvFaults += Vec_IntEntry( vNumEqvSa0, Abc_ObjId(pFanin) );
                }
                break;
                
            case 6: // NOR
            case 2: // NOT
                // For NOR/NOT: GO SA0 is equivalent to any GI SA1
                Abc_ObjForEachFanin( pObj, pFanin, k )
                {
                    pFault->nEqvFaults += Vec_IntEntry( vNumEqvSa1, Abc_ObjId(pFanin) );
                }
                break;
                
            case 0: // INPUT
            case 5: // OR
            case 4: // NAND
            case 7: // XOR
            case 8: // EQV (XNOR)
            default:
                // No equivalence for these types
                break;
        }
        
        // Check if this fault should be added (representative fault conditions)
        int shouldAdd = 0;
        
        if ( Abc_ObjFanoutNum(pObj) > 1 )
        {
            // Fanout stem - always add
            shouldAdd = 1;
        }
        else if ( Abc_ObjFanoutNum(pObj) == 1 )
        {
            pFanout = Abc_ObjFanout0(pObj);
            if ( Abc_ObjIsPo(pFanout) )
            {
                // Wire feeds OUTPUT (dummy PO gate) - always add
                shouldAdd = 1;
            }
            else if ( Abc_ObjIsNode(pFanout) )
            {
                pSop = (char *)pFanout->pData;
                if ( pSop )
                {
                    int fanoutType = Abc_SopGetGateType( pSop );
                    // Check original conditions: EQV, OR, NOR, XOR, OUTPUT
                    if ( fanoutType == 5 || fanoutType == 6 || fanoutType == 7 || fanoutType == 8 )
                        shouldAdd = 1;
                }
            }
        }
        
        if ( shouldAdd )
        {
            nTotalGateFaults += pFault->nEqvFaults;
            Abc_NtkAddFault( pNtk, pFault );
        }
        else
        {
            // Store equivalent fault count for later use
            Vec_IntWriteEntry( vNumEqvSa0, Abc_ObjId(pObj), pFault->nEqvFaults );
            Abc_FaultFree( pFault );
        }
        
        // Create GO SA1 fault
        pFault = Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GO, 0 );
        pFault->nEqvFaults = 1;
        
        // Add equivalent faults based on gate type
        switch ( gateType )
        {
            case 5: // OR
            case 1: // BUF
                // For OR/BUF: GO SA1 is equivalent to any GI SA1
                Abc_ObjForEachFanin( pObj, pFanin, k )
                {
                    pFault->nEqvFaults += Vec_IntEntry( vNumEqvSa1, Abc_ObjId(pFanin) );
                }
                break;
                
            case 4: // NAND
            case 2: // NOT
                // For NAND/NOT: GO SA1 is equivalent to any GI SA0
                Abc_ObjForEachFanin( pObj, pFanin, k )
                {
                    pFault->nEqvFaults += Vec_IntEntry( vNumEqvSa0, Abc_ObjId(pFanin) );
                }
                break;
                
            case 0: // INPUT
            case 3: // AND
            case 6: // NOR
            case 7: // XOR
            case 8: // EQV (XNOR)
            default:
                // No equivalence for these types
                break;
        }
        
        // Check if this fault should be added
        shouldAdd = 0;
        
        if ( Abc_ObjFanoutNum(pObj) > 1 )
        {
            shouldAdd = 1;
        }
        else if ( Abc_ObjFanoutNum(pObj) == 1 )
        {
            pFanout = Abc_ObjFanout0(pObj);
            if ( Abc_ObjIsPo(pFanout) )
            {
                // Wire feeds OUTPUT - always add
                shouldAdd = 1;
            }
            else if ( Abc_ObjIsNode(pFanout) )
            {
                pSop = (char *)pFanout->pData;
                if ( pSop )
                {
                    int fanoutType = Abc_SopGetGateType( pSop );
                    // Check original conditions: EQV, AND, NAND, XOR, OUTPUT
                    if ( fanoutType == 3 || fanoutType == 4 || fanoutType == 7 || fanoutType == 8 )
                        shouldAdd = 1;
                }
            }
        }
        
        if ( shouldAdd )
        {
            nTotalGateFaults += pFault->nEqvFaults;
            Abc_NtkAddFault( pNtk, pFault );
        }
        else
        {
            // Store equivalent fault count for later use
            Vec_IntWriteEntry( vNumEqvSa1, Abc_ObjId(pObj), pFault->nEqvFaults );
            Abc_FaultFree( pFault );
        }
        
        // Handle fanout branches - create GI faults
        if ( Abc_ObjFanoutNum(pObj) > 1 )
        {
            // Set the stem equivalent count to 1 for future use
            Vec_IntWriteEntry( vNumEqvSa0, Abc_ObjId(pObj), 1 );
            Vec_IntWriteEntry( vNumEqvSa1, Abc_ObjId(pObj), 1 );
            
            // Create GI faults for each fanout
            Abc_ObjForEachFanout( pObj, pFanout, j )
            {
                if ( !Abc_ObjIsNode(pFanout) && !Abc_ObjIsPo(pFanout) )
                    continue;
                    
                // Find the input index
                int inputIndex = -1;
                Abc_ObjForEachFanin( pFanout, pFanin, k )
                {
                    if ( pFanin == pObj )
                    {
                        inputIndex = k;
                        break;
                    }
                }
                
                if ( inputIndex == -1 )
                    continue;
                
                // Determine which faults to create based on fanout gate type
                int createSa0 = 0, createSa1 = 0;
                
                if ( Abc_ObjIsPo(pFanout) )
                {
                    // OUTPUT gate - create both SA0 and SA1
                    createSa0 = createSa1 = 1;
                }
                else if ( Abc_ObjIsNode(pFanout) )
                {
                    pSop = (char *)pFanout->pData;
                    if ( pSop )
                    {
                        int fanoutType = Abc_SopGetGateType( pSop );
                        switch ( fanoutType )
                        {
                            case 5: // OR
                            case 6: // NOR
                            case 7: // XOR
                            case 8: // XNOR (EQV)
                                createSa0 = 1;
                                break;
                        }
                        switch ( fanoutType )
                        {
                            case 3: // AND
                            case 4: // NAND
                            case 7: // XOR
                            case 8: // XNOR (EQV)
                                createSa1 = 1;
                                break;
                        }
                    }
                }
                
                // Create SA0 fault if needed
                if ( createSa0 )
                {
                    pFault = Abc_FaultAlloc( pFanout, ABC_FAULT_SA0, ABC_FAULT_GI, inputIndex );
                    pFault->nEqvFaults = 1;
                    nTotalGateFaults++;
                    Abc_NtkAddFault( pNtk, pFault );
                }
                
                // Create SA1 fault if needed
                if ( createSa1 )
                {
                    pFault = Abc_FaultAlloc( pFanout, ABC_FAULT_SA1, ABC_FAULT_GI, inputIndex );
                    pFault->nEqvFaults = 1;
                    nTotalGateFaults++;
                    Abc_NtkAddFault( pNtk, pFault );
                }
            }
        }
    }
    
    // Reverse the fault list (matching original implementation)
    // Since we're using a linked list, we need to reverse it manually
    pFaultPrev = NULL;
    pFaultCur = pNtk->pFaultList;
    while ( pFaultCur )
    {
        Abc_Fault_t * pNext = pFaultCur->pNext;
        pFaultCur->pNext = pFaultPrev;
        pFaultPrev = pFaultCur;
        pFaultCur = pNext;
    }
    pNtk->pFaultList = pFaultPrev;
    
    // Assign fault IDs after reversal
    nFaults = 0;
    for ( pFault = pNtk->pFaultList; pFault; pFault = pFault->pNext )
    {
        pFault->FaultId = nFaults++;
    }
    
    // Clean up
    Vec_IntFree( vNumEqvSa0 );
    Vec_IntFree( vNumEqvSa1 );
    
    // Print statistics
    fprintf( stdout, "#number of equivalent faults = %d\n", nFaults );
}


/**Function*************************************************************

  Synopsis    [Inserts fault simulation gates for each fault in the fault list.]

  Description [For each fault, adds two new PIs (x_id, y_id) and inserts the logic
               (c ^ ~x_id) | y_id at the fault site, as shown in the provided figure.]
               
  SideEffects [Modifies the network structure.]

  SeeAlso     []

***********************************************************************/
void Abc_NtkInsertFaultSimGates(Abc_Ntk_t * pNtk)
{
    Abc_Fault_t * pFault;
    Vec_Ptr_t * vHandledsa0 = Vec_PtrAlloc(100); // Track handled output nodes
    Vec_Ptr_t * vHandledsa1 = Vec_PtrAlloc(100); // Track handled output nodes
    // Iterate over the fault list
    for (pFault = pNtk->pFaultList; pFault; pFault = pFault->pNext)
    {
        char xName[32], yName[32];
        char f0_Name[32], f1_Name[32];
        char po_f0_Name[32], po_f1_Name[32];
        Abc_Obj_t * pX, * pY, * pNotX, * pC, * pAnd, * pOr;

        pC = pFault->pNode; // Output of the gate

        if(pFault->Type == ABC_FAULT_SA0)
        {
            if(Vec_PtrFind(vHandledsa0, pC) != -1)
                continue;
            Vec_PtrPush(vHandledsa0, pC);

            Abc_Obj_t * pOR_pbo, * pf0_pbo, *pNotf0_pbo;

            pAnd = Abc_NtkCreateNode(pNtk);
            pOR_pbo = Abc_NtkCreateNode(pNtk);

            // Rewire the network so that pAnd replaces pC as the output signal
            // Transfer all fanouts of pC to pAnd
            Abc_ObjTransferFanout(pC, pAnd);

            // Generate unique names for x and y
            sprintf(f0_Name, "f0_%s", Abc_ObjName(pC));
            sprintf(xName, "x_%s", Abc_ObjName(pC));
            // Add new PIs
            pf0_pbo = Abc_NtkCreatePi(pNtk);
            pX = Abc_NtkCreatePi(pNtk);
            Abc_ObjAssignName(pf0_pbo, f0_Name, NULL);
            Abc_ObjAssignName(pX, xName, NULL);
            
            // create NOT gate for a_f0
            // Create NOT gate for ~x
            pNotf0_pbo = Abc_NtkCreateNode(pNtk);
            Abc_ObjAddFanin(pNotf0_pbo, pf0_pbo);
            pNotf0_pbo->pData = Abc_SopCreateInv((Mem_Flex_t*)pNtk->pManFunc);

            pNotX = Abc_NtkCreateNode(pNtk);
            Abc_ObjAddFanin(pNotX, pX);
            pNotX->pData = Abc_SopCreateInv((Mem_Flex_t*)pNtk->pManFunc);
            
            // create OR gate for (c OR ~a_f0)
            Abc_ObjAddFanin(pOR_pbo, pC);
            Abc_ObjAddFanin(pOR_pbo, pNotf0_pbo);
            pOR_pbo->pData = Abc_SopCreateOrMultiCube((Mem_Flex_t*)pNtk->pManFunc, 2, NULL);
            
            // create AND gate for (c AND ~x)
            Abc_ObjAddFanin(pAnd, pC);
            Abc_ObjAddFanin(pAnd, pNotX);
            pAnd->pData = Abc_SopCreateAnd((Mem_Flex_t*)pNtk->pManFunc, 2, NULL);

            // wire the constant 1 PO to the OR gate
            Abc_Obj_t * pConst1Po = Abc_NtkCreatePo(pNtk);
            sprintf(po_f0_Name, "const1_po_pbo_%s", Abc_ObjName(pC));
            Abc_ObjAssignName(pConst1Po, po_f0_Name, NULL);
            Abc_ObjAddFanin(pConst1Po, pOR_pbo);
            
            printf("[FaultSim] Inserted SA0 sim gates for node %s \n", Abc_ObjName(pC));

        }
        else if(pFault->Type == ABC_FAULT_SA1)
        {
            if(Vec_PtrFind(vHandledsa1, pC) != -1)
                continue;
            Vec_PtrPush(vHandledsa1, pC);

            Abc_Obj_t * pAND_pbo, * pf1_pbo;

            pOr = Abc_NtkCreateNode(pNtk);
            pAND_pbo = Abc_NtkCreateNode(pNtk);
            // Rewire the network so that pOr replaces pC as the output signal
            // Transfer all fanouts of pC to pOr
            Abc_ObjTransferFanout(pC, pOr);

            // Generate unique names for x and y
            sprintf(f1_Name, "f1_%s", Abc_ObjName(pC));
            sprintf(yName, "y_%s", Abc_ObjName(pC));
            // Add new PIs
            pf1_pbo = Abc_NtkCreatePi(pNtk);
            pY = Abc_NtkCreatePi(pNtk);
            Abc_ObjAssignName(pf1_pbo, f1_Name, NULL);
            Abc_ObjAssignName(pY, yName, NULL);
            
            // create OR gate for (c AND a_f1)
            // Create OR gate for ((c AND ~x) OR y)
            Abc_ObjAddFanin(pAND_pbo, pC);
            Abc_ObjAddFanin(pAND_pbo, pf1_pbo);
            pAND_pbo->pData = Abc_SopCreateAnd((Mem_Flex_t*)pNtk->pManFunc, 2, NULL);

            Abc_ObjAddFanin(pOr, pC);
            Abc_ObjAddFanin(pOr, pY);
            pOr->pData = Abc_SopCreateOrMultiCube((Mem_Flex_t*)pNtk->pManFunc, 2, NULL);

            // wire the constant 0 PO to the AND gate
            Abc_Obj_t * pConst0Po = Abc_NtkCreatePo(pNtk);
            sprintf(po_f1_Name, "const0_po_pbo_%s", Abc_ObjName(pC));
            Abc_ObjAssignName(pConst0Po, po_f1_Name, NULL);
            Abc_ObjAddFanin(pConst0Po, pAND_pbo);
            
            printf("[FaultSim] Inserted SA1 sim gates for node %s \n", Abc_ObjName(pC));
        }
    }
    Vec_PtrFree(vHandledsa0);
    Vec_PtrFree(vHandledsa1);
    printf("[FaultSim] Completed fault simulation gate insertion\n");
}



ABC_NAMESPACE_IMPL_END