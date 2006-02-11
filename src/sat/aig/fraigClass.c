/**CFile****************************************************************

  FileName    [fraigClass.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: fraigClass.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"
#include "stmm.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static unsigned Aig_ManHashKey( unsigned * pData, int nWords, bool fPhase );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the equivalence classes of patterns.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * Aig_ManDeriveClassesFirst( Aig_Man_t * p, Aig_SimInfo_t * pInfo )
{
    Vec_Vec_t * vClasses;    // equivalence classes
    stmm_table * tSim2Node;  // temporary hash table hashing key into the class number
    Aig_Node_t * pNode;       
    unsigned uKey;
    int i, * pSpot, Entry, ClassNum;
    assert( pInfo->Type == 1 );
    // fill in the hash table
    tSim2Node = stmm_init_table( stmm_numcmp, stmm_numhash );
    vClasses = Vec_VecAlloc( 100 );
    // enumerate the nodes considered in the equivalence classes
//    Aig_ManForEachNode( p, pNode, i )
    Vec_IntForEachEntry( p->vSat2Var, Entry, i )
    {
        pNode = Aig_ManNode( p, Entry );

        if ( Aig_NodeIsPo(pNode) )
            continue;
        uKey = Aig_ManHashKey( Aig_SimInfoForNode(pInfo, pNode), pInfo->nWords, pNode->fPhase );
        if ( !stmm_find_or_add( tSim2Node, (char *)uKey, (char ***)&pSpot ) ) // does not exist
            *pSpot = (pNode->Id << 1) | 1; // save the node, and do nothing
        else if ( (*pSpot) & 1 ) // this is a node
        {
            // create the class
            ClassNum = Vec_VecSize( vClasses );
            Vec_VecPush( vClasses, ClassNum, (void *)((*pSpot) >> 1) );
            Vec_VecPush( vClasses, ClassNum, (void *)pNode->Id );
            // save the class
            *pSpot = (ClassNum << 1); 
        }
        else // this is a class
        {
            ClassNum = ((*pSpot) >> 1);
            Vec_VecPush( vClasses, ClassNum, (void *)pNode->Id );
        }
    }
    stmm_free_table( tSim2Node );
/*
    // print the classes
    {
        Vec_Ptr_t * vVec;
        printf( "PI/PO = %4d/%4d. Nodes = %7d. SatVars = %7d. Non-trivial classes = %5d: \n", 
            Aig_ManPiNum(p), Aig_ManPoNum(p), 
            Aig_ManNodeNum(p) - Aig_ManPoNum(p), 
            Vec_IntSize(p->vSat2Var), Vec_VecSize(vClasses) );

        Vec_VecForEachLevel( vClasses, vVec, i )
            printf( "%d ", Vec_PtrSize(vVec) );
        printf( "\n" );
    }
*/
    printf( "Classes = %6d. Pairs = %6d.\n", Vec_VecSize(vClasses), Vec_VecSizeSize(vClasses) - Vec_VecSize(vClasses) );
    return vClasses;
}

/**Function*************************************************************

  Synopsis    [Computes the hash key of the simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Aig_ManHashKey( unsigned * pData, int nWords, bool fPhase )
{
    static int Primes[10] = { 1009, 2207, 3779, 4001, 4877, 5381, 6427, 6829, 7213, 7919 };
    unsigned uKey;
    int i;
    uKey = 0;
    if ( fPhase )
        for ( i = 0; i < nWords; i++ )
            uKey ^= i * Primes[i%10] * pData[i];
    else
        for ( i = 0; i < nWords; i++ )
            uKey ^= i * Primes[i%10] * ~pData[i];
    return uKey;
}



/**Function*************************************************************

  Synopsis    [Splits the equivalence class.]

  Description [Given an equivalence class (vClass) and the simulation info, 
  split the class into two based on the info.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManSplitClass( Aig_Man_t * p, Aig_SimInfo_t * pInfo, Vec_Int_t * vClass, Vec_Int_t * vClass2, Aig_Pattern_t * pPat )
{
    int NodeId, i, k, w;
    Aig_Node_t * pRoot, * pTemp;
    unsigned * pRootData, * pTempData;
    assert( Vec_IntSize(vClass) > 1 );
    assert( pInfo->nPatsCur == pPat->nBits );
//    printf( "Class = %5d.  -->  ", Vec_IntSize(vClass) ); 
    // clear storage for the new classes
    Vec_IntClear( vClass2 );
    // get the root member of the class
    pRoot = Aig_ManNode( p, Vec_IntEntry(vClass, 0) );
    pRootData = Aig_SimInfoForNode( pInfo, pRoot );
    // sort the class members:
    // (1) with the same siminfo as pRoot remain in vClass
    // (2) nodes with other siminfo go to vClass2
    k = 1;
    Vec_IntForEachEntryStart( vClass, NodeId, i, 1 )
    {
        NodeId = Vec_IntEntry(vClass, i);
        pTemp  = Aig_ManNode( p, NodeId );
        pTempData = Aig_SimInfoForNode( pInfo, pTemp );
        if ( pRoot->fPhase == pTemp->fPhase )
        {
            for ( w = 0; w < pInfo->nWords; w++ )
                if ( pRootData[w] != pTempData[w] )
                    break;
            if ( w == pInfo->nWords ) // the same info
                Vec_IntWriteEntry( vClass, k++, NodeId );
            else
            {
                Vec_IntPush( vClass2, NodeId );
                // record the diffs if they are not distinguished by the first pattern
                if ( ((pRootData[0] ^ pTempData[0]) & 1) == 0 )
                    for ( w = 0; w < pInfo->nWords; w++ )
                        pPat->pData[w] |= (pRootData[w] ^ pTempData[w]);
            }
        }
        else
        {
            for ( w = 0; w < pInfo->nWords; w++ )
                if ( pRootData[w] != ~pTempData[w] )
                    break;
            if ( w == pInfo->nWords ) // the same info
                Vec_IntWriteEntry( vClass, k++, NodeId );
            else
            {
                Vec_IntPush( vClass2, NodeId );
                // record the diffs if they are not distinguished by the first pattern
                if ( ((pRootData[0] ^ ~pTempData[0]) & 1) == 0 )
                    for ( w = 0; w < pInfo->nWords; w++ )
                        pPat->pData[w] |= (pRootData[w] ^ ~pTempData[w]);
            }
        }
    }
    Vec_IntShrink( vClass, k );
//    printf( "Class1 = %5d. Class2 = %5d.\n", Vec_IntSize(vClass), Vec_IntSize(vClass2) ); 
}

/**Function*************************************************************

  Synopsis    [Updates the equivalence classes using the simulation info.]

  Description [Records successful simulation patterns into the pattern
  storage.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManUpdateClasses( Aig_Man_t * p, Aig_SimInfo_t * pInfo, Vec_Vec_t * vClasses, Aig_Pattern_t * pPatMask )
{
    Vec_Ptr_t * vClass;
    int i, k, fSplit = 0;
    assert( Vec_VecSize(vClasses) > 0 );
    // collect patterns that lead to changes
    Aig_PatternClean( pPatMask );
    // split the classes using the new symmetry info
    Vec_VecForEachLevel( vClasses, vClass, i )
    {
        if ( i == 0 )
            continue;
        // split vClass into two parts (vClass and vClassTemp)
        Aig_ManSplitClass( p, pInfo, (Vec_Int_t *)vClass, p->vClassTemp, pPatMask );
        // check if there is any splitting
        if ( Vec_IntSize(p->vClassTemp) > 0 )
            fSplit = 1;
        // skip the new class if it is empty or trivial
        if ( Vec_IntSize(p->vClassTemp) < 2 )
            continue;
        // consider replacing the current class with the new one
        if ( Vec_PtrSize(vClass) == 1 )
        {
            assert( vClasses->pArray[i] == vClass );
            vClasses->pArray[i] = p->vClassTemp;
            p->vClassTemp = (Vec_Int_t *)vClass;
            i--;
            continue;
        }
        // add the new non-trival class in the end
        Vec_PtrPush( (Vec_Ptr_t *)vClasses, p->vClassTemp );
        p->vClassTemp = Vec_IntAlloc( 10 );
    }
    // free trivial classes
    k = 0;
    Vec_VecForEachLevel( vClasses, vClass, i )
    {
        assert( Vec_PtrSize(vClass) > 0 );
        if ( Vec_PtrSize(vClass) == 1 )
            Vec_PtrFree(vClass);
        else
            vClasses->pArray[k++] = vClass;
    }
    Vec_PtrShrink( (Vec_Ptr_t *)vClasses, k );
    // catch the patterns which led to splitting
    printf( "Classes = %6d. Pairs = %6d.  Patterns = %3d.\n", 
        Vec_VecSize(vClasses), 
        Vec_VecSizeSize(vClasses) - Vec_VecSize(vClasses), 
        Vec_PtrSize(p->vPats) );
    return fSplit;
}

/**Function*************************************************************

  Synopsis    [Collects useful patterns.]

  Description [If the flag fAddToVector is 1, creates and adds new patterns
  to the internal storage of patterns.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManCollectPatterns( Aig_Man_t * p, Aig_SimInfo_t * pInfo, Aig_Pattern_t * pMask, Vec_Ptr_t * vPats )
{
    Aig_SimInfo_t * pInfoRes = p->pInfo;
    Aig_Pattern_t * pPatNew;
    Aig_Node_t * pNode;
    int i, k;

    assert( Aig_InfoHasBit(pMask->pData, 0) == 0 );
    for ( i = 0; i < pMask->nBits; i++ )
    {
        if ( vPats && Vec_PtrSize(vPats) >= p->nPatsMax )
            break;
        if ( i == 0 || Aig_InfoHasBit(pMask->pData, i) )
        {
            // expand storage if needed
            if ( pInfoRes->nPatsCur == pInfoRes->nPatsMax )
                Aig_SimInfoResize( pInfoRes );
            // create a new pattern
            if ( vPats )
            {
                pPatNew = Aig_PatternAlloc( Aig_ManPiNum(p) );
                Aig_PatternClean( pPatNew );
            }
            // go through the PIs
            Aig_ManForEachPi( p, pNode, k )
            {
                if ( Aig_InfoHasBit( Aig_SimInfoForNode(pInfo, pNode), i ) )
                {
                    Aig_InfoSetBit( Aig_SimInfoForPi(pInfoRes, k), pInfoRes->nPatsCur );
                    if ( vPats ) Aig_InfoSetBit( pPatNew->pData, k );
                }
            }
            // store the new pattern
            if ( vPats ) Vec_PtrPush( vPats, pPatNew ); 
            // increment the number of patterns stored
            pInfoRes->nPatsCur++;
        }
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


