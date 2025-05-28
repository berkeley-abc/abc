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
    Abc_Obj_t * pObj, *pFanout;
    int i, j;
    int inputIndex;
    
    // Clear existing faults
    Abc_NtkClearFaults( pNtk );
    
    // Step 1: Add faults for all primary inputs (these are checkpoints)
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA0, ABC_FAULT_GO, 0 ) );
        Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pObj, ABC_FAULT_SA1, ABC_FAULT_GO, 0 ) );
    }
    
    // Step 2: Find all fanout branches and add faults ONLY at the branches
    // We need to check both internal nodes and PIs for fanouts
    
    // Check internal nodes for fanouts
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        // If this node's output fans out to multiple gates, add faults at the BRANCHES
        if ( Abc_ObjFanoutNum(pObj) > 1 )
        {
            // This is a stem with multiple fanouts
            // Add faults at each fanout branch (the inputs of the fanout gates)
            Abc_ObjForEachFanout( pObj, pFanout, j )
            {
                if ( Abc_ObjIsNode(pFanout) || Abc_ObjIsPo(pFanout) )
                {
                    // Find which input of the fanout node connects to our stem
                    for ( inputIndex = 0; inputIndex < Abc_ObjFaninNum(pFanout); inputIndex++ )
                    {
                        if ( Abc_ObjFanin(pFanout, inputIndex) == pObj )
                        {
                            // Only add faults at gate inputs, not PO inputs
                            if ( Abc_ObjIsNode(pFanout) )
                            {
                                // Add faults at this fanout branch (GI of the fanout gate)
                                Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pFanout, ABC_FAULT_SA0, ABC_FAULT_GI, inputIndex ) );
                                Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pFanout, ABC_FAULT_SA1, ABC_FAULT_GI, inputIndex ) );
                            }
                            break;
                        }
                    }
                }
            }
        }
    }
    
    // Also check if PIs have fanouts (PI outputs may also branch)
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        // If PI has multiple fanouts, add faults at the branches
        // (PI faults were already added, now we add branch faults)
        if ( Abc_ObjFanoutNum(pObj) > 1 )
        {
            Abc_ObjForEachFanout( pObj, pFanout, j )
            {
                if ( Abc_ObjIsNode(pFanout) )
                {
                    // Find which input of the fanout node connects to our PI
                    for ( inputIndex = 0; inputIndex < Abc_ObjFaninNum(pFanout); inputIndex++ )
                    {
                        if ( Abc_ObjFanin(pFanout, inputIndex) == pObj )
                        {
                            // Add faults at this fanout branch
                            Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pFanout, ABC_FAULT_SA0, ABC_FAULT_GI, inputIndex ) );
                            Abc_NtkAddFault( pNtk, Abc_FaultAlloc( pFanout, ABC_FAULT_SA1, ABC_FAULT_GI, inputIndex ) );
                            break;
                        }
                    }
                }
            }
        }
    }
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
    // For single-input gates (buffer/inverter), input and output faults are equivalent
    if ( Abc_ObjFaninNum(pNode) == 1 )
    {
        if ( (pFault1->Io == ABC_FAULT_GI && pFault1->Index == 0 && pFault2->Io == ABC_FAULT_GO) ||
             (pFault1->Io == ABC_FAULT_GO && pFault2->Io == ABC_FAULT_GI && pFault2->Index == 0) )
        {
            // For buffer: sa0-in ≡ sa0-out, sa1-in ≡ sa1-out
            // For inverter: sa0-in ≡ sa1-out, sa1-in ≡ sa0-out
            if ( Abc_NodeIsBuf(pNode) )
                return pFault1->Type == pFault2->Type;
            else if ( Abc_NodeIsInv(pNode) )
                return pFault1->Type != pFault2->Type;
        }
    }
    
    // For fanout-free gates, output faults may be equivalent to some input combinations
    // This is a simplified check - full equivalence checking would require more analysis
    return 0;
}

// Check if fault1 dominates fault2
static int Abc_FaultDominates( Abc_Obj_t * pNode, Abc_Fault_t * pFault1, Abc_Fault_t * pFault2 )
{
    char * pSop;
    int nCubes, nVars;
    
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
    
    // Dominance rules for basic gates
    if ( nVars == 2 && nCubes == 1 )  // AND gate (or NAND)
    {
        // For AND gate: output sa0 dominates all input sa0
        if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA0 &&
             pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA0 )
            return 1;
    }
    else if ( nVars == 2 && nCubes == 2 )  // OR gate (or NOR)
    {
        // For OR gate: output sa1 dominates all input sa1
        if ( pFault1->Io == ABC_FAULT_GO && pFault1->Type == ABC_FAULT_SA1 &&
             pFault2->Io == ABC_FAULT_GI && pFault2->Type == ABC_FAULT_SA1 )
            return 1;
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

ABC_NAMESPACE_IMPL_END 