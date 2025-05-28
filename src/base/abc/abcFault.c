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
    Abc_Obj_t * pObj;
    int i, k;
    // Clear existing faults
    Abc_NtkClearFaults( pNtk );
    // Add SA0 and SA1 faults for each node
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        // Add gate output faults
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GO, 0 ) );
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GO, 0 ) );
        // Add gate input faults
        for ( k = 0; k < Abc_ObjFaninNum(pObj); k++ )
        {
            Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GI, k ) );
            Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GI, k ) );
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

// Helper structure for fault analysis
typedef struct FaultInfo_t_ {
    Abc_Fault_t * pFault;
    int           nGroupId;      // equivalence group ID
    int           fDominated;    // is this fault dominated?
    int           fRepresentative; // is this the representative of its group?
    Vec_Ptr_t *   vDominates;    // faults that this fault dominates
} FaultInfo_t;

// Check if two faults are equivalent
static int Abc_FaultsAreEquivalent( Abc_Obj_t * pNode, Abc_Fault_t * pFault1, Abc_Fault_t * pFault2 )
{
    char * pSop;
    int nVars;
    
    // Must be on same node
    if ( pFault1->pNode != pFault2->pNode )
        return 0;
        
    // For single-input gates (buffer/inverter)
    if ( Abc_ObjFaninNum(pNode) == 1 && Abc_ObjIsNode(pNode) )
    {
        if ( (pFault1->Io == ABC_FAULT_GI && pFault1->Index == 0 && pFault2->Io == ABC_FAULT_GO) ||
             (pFault1->Io == ABC_FAULT_GO && pFault2->Io == ABC_FAULT_GI && pFault2->Index == 0) )
        {
            pSop = (char *)pNode->pData;
            if ( !pSop )
                return 0;
                
            nVars = Abc_SopGetVarNum(pSop);
            if ( nVars != 1 )
                return 0;
                
            // Check if it's a buffer (F = A) or inverter (F = A')
            if ( pSop[0] == '1' )  // Buffer: positive literal
            {
                return pFault1->Type == pFault2->Type;
            }
            else if ( pSop[0] == '0' )  // Inverter: negative literal
            {
                return pFault1->Type != pFault2->Type;
            }
        }
    }
    
    // For fanout-free gates (single fanout), certain input combinations may be equivalent
    // This requires more complex analysis based on gate function
    // For now, we handle only the simple buffer/inverter case
    
    return 0;
}

// Check if fault1 dominates fault2
static int Abc_FaultDominates( Abc_Obj_t * pNode, Abc_Fault_t * pFault1, Abc_Fault_t * pFault2 )
{
    char * pSop;
    int nCubes, nVars;
    int isComplement;
    
    // Can't dominate if they're on different nodes
    if ( pFault1->pNode != pFault2->pNode )
        return 0;
    
    // Same fault can't dominate itself
    if ( pFault1->Type == pFault2->Type && pFault1->Io == pFault2->Io && pFault1->Index == pFault2->Index )
        return 0;
    
    // Get gate type
    if ( !Abc_ObjIsNode(pNode) )
        return 0;
        
    pSop = (char *)pNode->pData;
    if ( !pSop )
        return 0;
        
    nCubes = Abc_SopGetCubeNum(pSop);
    nVars = Abc_SopGetVarNum(pSop);
    isComplement = Abc_SopIsComplement(pSop);
    
    // Single variable gates (buffer/inverter)
    if ( nVars == 1 )
    {
        // These are handled by equivalence, not dominance
        return 0;
    }
    
    // Two-input gates
    if ( nVars == 2 )
    {
        // AND gate: F = AB (nCubes = 1, all literals positive)
        if ( nCubes == 1 && !isComplement )
        {
            // For AND: output SA0 dominates all input SA0
            if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA0 &&
                 pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA0 )
                return 1;
                
            // For AND: any input SA1 dominates output SA1
            if ( pFault1->Io == ABC_FAULT_GI && pFault1->Type == ABC_FAULT_SA1 &&
                 pFault2->Io == ABC_FAULT_GO && pFault2->Type == ABC_FAULT_SA1 )
                return 1;
        }
        // NAND gate: F = (AB)' (nCubes = 1, complement)
        else if ( nCubes == 1 && isComplement )
        {
            // For NAND: output SA1 dominates all input SA0
            if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA1 &&
                 pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA0 )
                return 1;
                
            // For NAND: any input SA1 dominates output SA0
            if ( pFault1->Io == ABC_FAULT_GI && pFault1->Type == ABC_FAULT_SA1 &&
                 pFault2->Io == ABC_FAULT_GO && pFault2->Type == ABC_FAULT_SA0 )
                return 1;
        }
        // OR gate: F = A + B (nCubes = 2, each with one literal)
        else if ( nCubes == 2 && !isComplement )
        {
            // For OR: output SA1 dominates all input SA1
            if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA1 &&
                 pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA1 )
                return 1;
                
            // For OR: any input SA0 dominates output SA0
            if ( pFault1->Io == ABC_FAULT_GI && pFault1->Type == ABC_FAULT_SA0 &&
                 pFault2->Io == ABC_FAULT_GO && pFault2->Type == ABC_FAULT_SA0 )
                return 1;
        }
        // NOR gate: F = (A + B)' (nCubes = 2, complement)
        else if ( nCubes == 2 && isComplement )
        {
            // For NOR: output SA0 dominates all input SA1
            if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA0 &&
                 pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA1 )
                return 1;
                
            // For NOR: any input SA0 dominates output SA1
            if ( pFault1->Io == ABC_FAULT_GI && pFault1->Type == ABC_FAULT_SA0 &&
                 pFault2->Io == ABC_FAULT_GO && pFault2->Type == ABC_FAULT_SA1 )
                return 1;
        }
    }
    
    // Multi-input AND/NAND gates
    if ( nCubes == 1 )
    {
        if ( !isComplement )  // AND gate
        {
            // Output SA0 dominates all input SA0
            if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA0 &&
                 pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA0 )
                return 1;
            // Any input SA1 dominates output SA1
            if ( pFault1->Io == ABC_FAULT_GI && pFault1->Type == ABC_FAULT_SA1 &&
                 pFault2->Io == ABC_FAULT_GO && pFault2->Type == ABC_FAULT_SA1 )
                return 1;
        }
        else  // NAND gate
        {
            // Output SA1 dominates all input SA0
            if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA1 &&
                 pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA0 )
                return 1;
            // Any input SA1 dominates output SA0
            if ( pFault1->Io == ABC_FAULT_GI && pFault1->Type == ABC_FAULT_SA1 &&
                 pFault2->Io == ABC_FAULT_GO && pFault2->Type == ABC_FAULT_SA0 )
                return 1;
        }
    }
    
    // Multi-input OR/NOR gates (each variable appears in separate cube)
    if ( nCubes == nVars )
    {
        // Check if this is really an OR/NOR structure
        int isOr = 1;
        for ( int i = 0; i < nCubes && isOr; i++ )
        {
            char * pCube = pSop + i * (nVars + 3);
            int litCount = 0;
            for ( int j = 0; j < nVars; j++ )
            {
                if ( pCube[j] != '-' )
                    litCount++;
            }
            if ( litCount != 1 )
                isOr = 0;
        }
        
        if ( isOr )
        {
            if ( !isComplement )  // OR gate
            {
                // Output SA1 dominates all input SA1
                if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA1 &&
                     pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA1 )
                    return 1;
                // Any input SA0 dominates output SA0
                if ( pFault1->Io == ABC_FAULT_GI && pFault1->Type == ABC_FAULT_SA0 &&
                     pFault2->Io == ABC_FAULT_GO && pFault2->Type == ABC_FAULT_SA0 )
                    return 1;
            }
            else  // NOR gate
            {
                // Output SA0 dominates all input SA1
                if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA0 &&
                     pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA1 )
                    return 1;
                // Any input SA0 dominates output SA1
                if ( pFault1->Io == ABC_FAULT_GI && pFault1->Type == ABC_FAULT_SA0 &&
                     pFault2->Io == ABC_FAULT_GO && pFault2->Type == ABC_FAULT_SA1 )
                    return 1;
            }
        }
    }
    
    return 0;
}

void Abc_NtkGenerateCollapsingFaultList( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    Abc_Fault_t * pFault, * pFault2;
    FaultInfo_t * pInfo, * pInfo2;
    Vec_Ptr_t * vAllFaults;
    Vec_Ptr_t * vFaultInfos;
    int i, j, k, nGroups;
    
    // Clear existing faults
    Abc_NtkClearFaults( pNtk );
    
    // Step 1: Generate all possible faults and create fault info structures
    vAllFaults = Vec_PtrAlloc( 1000 );
    vFaultInfos = Vec_PtrAlloc( 1000 );
    
    // Generate all faults
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        // Add gate output faults
        pFault = Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GO, 0 );
        Vec_PtrPush( vAllFaults, pFault );
        pInfo = ABC_ALLOC( FaultInfo_t, 1 );
        pInfo->pFault = pFault;
        pInfo->nGroupId = Vec_PtrSize(vFaultInfos);  // Initially each fault is its own group
        pInfo->fDominated = 0;
        pInfo->fRepresentative = 1;
        pInfo->vDominates = Vec_PtrAlloc( 4 );
        Vec_PtrPush( vFaultInfos, pInfo );
        
        pFault = Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GO, 0 );
        Vec_PtrPush( vAllFaults, pFault );
        pInfo = ABC_ALLOC( FaultInfo_t, 1 );
        pInfo->pFault = pFault;
        pInfo->nGroupId = Vec_PtrSize(vFaultInfos);
        pInfo->fDominated = 0;
        pInfo->fRepresentative = 1;
        pInfo->vDominates = Vec_PtrAlloc( 4 );
        Vec_PtrPush( vFaultInfos, pInfo );
        
        // Add gate input faults
        for ( k = 0; k < Abc_ObjFaninNum(pObj); k++ )
        {
            pFault = Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GI, k );
            Vec_PtrPush( vAllFaults, pFault );
            pInfo = ABC_ALLOC( FaultInfo_t, 1 );
            pInfo->pFault = pFault;
            pInfo->nGroupId = Vec_PtrSize(vFaultInfos);
            pInfo->fDominated = 0;
            pInfo->fRepresentative = 1;
            pInfo->vDominates = Vec_PtrAlloc( 4 );
            Vec_PtrPush( vFaultInfos, pInfo );
            
            pFault = Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GI, k );
            Vec_PtrPush( vAllFaults, pFault );
            pInfo = ABC_ALLOC( FaultInfo_t, 1 );
            pInfo->pFault = pFault;
            pInfo->nGroupId = Vec_PtrSize(vFaultInfos);
            pInfo->fDominated = 0;
            pInfo->fRepresentative = 1;
            pInfo->vDominates = Vec_PtrAlloc( 4 );
            Vec_PtrPush( vFaultInfos, pInfo );
        }
    }
    
    // Add PI faults
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        pFault = Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GO, 0 );
        Vec_PtrPush( vAllFaults, pFault );
        pInfo = ABC_ALLOC( FaultInfo_t, 1 );
        pInfo->pFault = pFault;
        pInfo->nGroupId = Vec_PtrSize(vFaultInfos);
        pInfo->fDominated = 0;
        pInfo->fRepresentative = 1;
        pInfo->vDominates = Vec_PtrAlloc( 4 );
        Vec_PtrPush( vFaultInfos, pInfo );
        
        pFault = Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GO, 0 );
        Vec_PtrPush( vAllFaults, pFault );
        pInfo = ABC_ALLOC( FaultInfo_t, 1 );
        pInfo->pFault = pFault;
        pInfo->nGroupId = Vec_PtrSize(vFaultInfos);
        pInfo->fDominated = 0;
        pInfo->fRepresentative = 1;
        pInfo->vDominates = Vec_PtrAlloc( 4 );
        Vec_PtrPush( vFaultInfos, pInfo );
    }
    
    // Step 2: Find equivalence groups
    nGroups = Vec_PtrSize(vFaultInfos);
    for ( i = 0; i < Vec_PtrSize(vFaultInfos); i++ )
    {
        pInfo = (FaultInfo_t *)Vec_PtrEntry(vFaultInfos, i);
        pFault = pInfo->pFault;
        
        // Check equivalence with remaining faults
        for ( j = i + 1; j < Vec_PtrSize(vFaultInfos); j++ )
        {
            pInfo2 = (FaultInfo_t *)Vec_PtrEntry(vFaultInfos, j);
            pFault2 = pInfo2->pFault;
            
            // Check if faults are on the same node
            if ( pFault->pNode == pFault2->pNode )
            {
                if ( Abc_FaultsAreEquivalent(pFault->pNode, pFault, pFault2) )
                {
                    // Merge groups - use the smaller group ID
                    int minGroupId = Abc_MinInt(pInfo->nGroupId, pInfo2->nGroupId);
                    pInfo->nGroupId = minGroupId;
                    pInfo2->nGroupId = minGroupId;
                    // The one with smaller index becomes representative
                    if ( j < i )
                    {
                        pInfo->fRepresentative = 0;
                        pInfo2->fRepresentative = 1;
                    }
                    else
                    {
                        pInfo2->fRepresentative = 0;
                    }
                }
            }
        }
    }
    
    // Step 3: Build dominance relationships
    for ( i = 0; i < Vec_PtrSize(vFaultInfos); i++ )
    {
        pInfo = (FaultInfo_t *)Vec_PtrEntry(vFaultInfos, i);
        pFault = pInfo->pFault;
        
        for ( j = 0; j < Vec_PtrSize(vFaultInfos); j++ )
        {
            if ( i == j )
                continue;
                
            pInfo2 = (FaultInfo_t *)Vec_PtrEntry(vFaultInfos, j);
            pFault2 = pInfo2->pFault;
            
            // Check if fault i dominates fault j
            if ( Abc_FaultDominates(pFault->pNode, pFault, pFault2) )
            {
                Vec_PtrPush( pInfo->vDominates, pInfo2 );
                pInfo2->fDominated = 1;
            }
        }
    }
    
    // Step 4: Select faults for the collapsed list
    for ( i = 0; i < Vec_PtrSize(vFaultInfos); i++ )
    {
        pInfo = (FaultInfo_t *)Vec_PtrEntry(vFaultInfos, i);
        
        // Add fault if it's:
        // 1. Representative of its equivalence group, AND
        // 2. Not dominated by any other fault
        if ( pInfo->fRepresentative && !pInfo->fDominated )
        {
            Abc_NtkAddFault( pNtk, pInfo->pFault );
        }
        else
        {
            // Free the fault if not added
            Abc_FaultFree( pInfo->pFault );
        }
        
        // Clean up
        Vec_PtrFree( pInfo->vDominates );
        ABC_FREE( pInfo );
    }
    
    // Clean up
    Vec_PtrFree( vAllFaults );
    Vec_PtrFree( vFaultInfos );
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
    int faultId = 0;
    Vec_Ptr_t * vHandled = Vec_PtrAlloc(100); // Track handled output nodes
    // Iterate over the fault list
    for (pFault = pNtk->pFaultList; pFault; pFault = pFault->pNext, ++faultId)
    {
        char xName[32], yName[32];
        Abc_Obj_t * pX, * pY, * pNotX, * pC, * pAnd, * pOut;

        pC = pFault->pNode; // Output of the gate
        // Check if we've already handled this node
        if (Vec_PtrFind(vHandled, pC) != -1)
            continue; // Already handled
        Vec_PtrPush(vHandled, pC);
        
        pOut = Abc_NtkCreateNode(pNtk);
        // Rewire the network so that pOut replaces pC as the output signal
        // Transfer all fanouts of pC to pOut
        Abc_ObjTransferFanout(pC, pOut);

        // Generate unique names for x and y
        sprintf(xName, "x_%d", faultId);
        sprintf(yName, "y_%d", faultId);
        // Add new PIs
        pX = Abc_NtkCreatePi(pNtk);
        Abc_ObjAssignName(pX, xName, NULL);
        pY = Abc_NtkCreatePi(pNtk);
        Abc_ObjAssignName(pY, yName, NULL);
        
        // Create NOT gate for ~x
        pNotX = Abc_NtkCreateNode(pNtk);
        Abc_ObjAddFanin(pNotX, pX);
        pNotX->pData = Abc_SopCreateInv((Mem_Flex_t*)pNtk->pManFunc);
        
        // Create AND gate for (c AND ~x)
        pAnd = Abc_NtkCreateNode(pNtk);
        Abc_ObjAddFanin(pAnd, pC);
        Abc_ObjAddFanin(pAnd, pNotX);
        pAnd->pData = Abc_SopCreateAnd((Mem_Flex_t*)pNtk->pManFunc, 2, NULL);
        
        // Create OR gate for ((c AND ~x) OR y)
        Abc_ObjAddFanin(pOut, pAnd);
        Abc_ObjAddFanin(pOut, pY);
        pOut->pData = Abc_SopCreateOrMultiCube((Mem_Flex_t*)pNtk->pManFunc, 2, NULL);
        
        printf("[FaultSim] Inserted fault sim gates for node %s \n", Abc_ObjName(pC));
    }
    Vec_PtrFree(vHandled);
    printf("[FaultSim] Completed fault simulation gate insertion\n");
}

ABC_NAMESPACE_IMPL_END 