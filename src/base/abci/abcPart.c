/**CFile****************************************************************

  FileName    [abcPart.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Output partitioning package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcPart.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "hop.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the number of common entries.]

  Description [Assumes that the vectors are sorted in the increasing order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_IntTwoCountCommon( Vec_Int_t * vArr1, Vec_Int_t * vArr2 )
{
    int i, k, Counter = 0;
    for ( i = k = 0; i < Vec_IntSize(vArr1) && k < Vec_IntSize(vArr2); )
    {
        if ( Vec_IntEntry(vArr1,i) == Vec_IntEntry(vArr2,k) )
            Counter++, i++, k++;
        else if ( Vec_IntEntry(vArr1,i) < Vec_IntEntry(vArr2,k) )
            i++;
        else
            k++;
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Returns the result of merging the two vectors.]

  Description [Assumes that the vectors are sorted in the increasing order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Int_t * Vec_IntTwoMerge( Vec_Int_t * vArr1, Vec_Int_t * vArr2 )
{
    Vec_Int_t * vArr; 
    int i, k;
    vArr = Vec_IntAlloc( Vec_IntSize(vArr1) );
    for ( i = k = 0; i < Vec_IntSize(vArr1) && k < Vec_IntSize(vArr2); )
    {
        if ( Vec_IntEntry(vArr1,i) == Vec_IntEntry(vArr2,k) )
            Vec_IntPush( vArr, Vec_IntEntry(vArr1,i) ), i++, k++;
        else if ( Vec_IntEntry(vArr1,i) < Vec_IntEntry(vArr2,k) )
            Vec_IntPush( vArr, Vec_IntEntry(vArr1,i) ), i++;
        else
            Vec_IntPush( vArr, Vec_IntEntry(vArr2,k) ), k++;
    }
    for ( ; i < Vec_IntSize(vArr1); i++ )
        Vec_IntPush( vArr, Vec_IntEntry(vArr1,i) );
    for ( ; k < Vec_IntSize(vArr2); k++ )
        Vec_IntPush( vArr, Vec_IntEntry(vArr2,k) );
    return vArr;
}

/**Function*************************************************************

  Synopsis    [Comparison procedure for two arrays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_VecSortCompare1( Vec_Ptr_t ** pp1, Vec_Ptr_t ** pp2 )
{
    if ( Vec_PtrSize(*pp1) < Vec_PtrSize(*pp2) )
        return -1;
    if ( Vec_PtrSize(*pp1) > Vec_PtrSize(*pp2) ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Comparison procedure for two integers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_VecSortCompare2( Vec_Ptr_t ** pp1, Vec_Ptr_t ** pp2 )
{
    if ( Vec_PtrSize(*pp1) > Vec_PtrSize(*pp2) )
        return -1;
    if ( Vec_PtrSize(*pp1) < Vec_PtrSize(*pp2) ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Sorting the entries by their integer value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_VecSort( Vec_Vec_t * p, int fReverse )
{
    if ( fReverse ) 
        qsort( (void *)p->pArray, p->nSize, sizeof(void *), 
                (int (*)(const void *, const void *)) Vec_VecSortCompare2 );
    else
        qsort( (void *)p->pArray, p->nSize, sizeof(void *), 
                (int (*)(const void *, const void *)) Vec_VecSortCompare1 );
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkNodeSupport_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanin;
    int i;
    assert( !Abc_ObjIsNet(pNode) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // collect the CI
    if ( Abc_ObjIsCi(pNode) || Abc_ObjFaninNum(pNode) == 0 )
    {
        Vec_PtrPush( vNodes, pNode );
        return;
    }
    assert( Abc_ObjIsNode( pNode ) );
    // visit the transitive fanin of the node
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_NtkNodeSupport_rec( Abc_ObjFanin0Ntk(pFanin), vNodes );
}

/**Function*************************************************************

  Synopsis    [Returns the set of CI nodes in the support of the given nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkNodeSupport( Abc_Ntk_t * pNtk, Abc_Obj_t ** ppNodes, int nNodes )
{
    Vec_Ptr_t * vNodes;
    int i;
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    // go through the PO nodes and call for each of them
    for ( i = 0; i < nNodes; i++ )
        if ( Abc_ObjIsCo(ppNodes[i]) )
            Abc_NtkNodeSupport_rec( Abc_ObjFanin0(ppNodes[i]), vNodes );
        else
            Abc_NtkNodeSupport_rec( ppNodes[i], vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Extra_UtilStrsav()]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Extra_UtilStrsav( char * s )
{
    if ( s == NULL )
       return s;
    return strcpy(ALLOC(char, strlen(s)+1), s);
}

/**Function*************************************************************

  Synopsis    [Creates the network composed of several logic cones.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCreateConeArray( Abc_Ntk_t * pNtk, Vec_Ptr_t * vRoots, int fUseAllCis )
{
    Abc_Ntk_t * pNtkNew; 
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pFanin, * pNodeCoNew;
    char Buffer[1000];
    int i, k;

    assert( Abc_NtkIsLogic(pNtk) || Abc_NtkIsStrash(pNtk) );
    
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc );
    // set the name
    sprintf( Buffer, "%s_part", pNtk->pName );
    pNtkNew->pName = Extra_UtilStrsav(Buffer);

    // establish connection between the constant nodes
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_AigConst1(pNtk->pManFunc)->pCopy = Abc_AigConst1(pNtkNew->pManFunc);

    // collect the nodes in the TFI of the output (mark the TFI)
    vNodes = Abc_NtkDfsNodes( pNtk, (Abc_Obj_t **)Vec_PtrArray(vRoots), Vec_PtrSize(vRoots) );

    // create the PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        if ( fUseAllCis || Abc_NodeIsTravIdCurrent(pObj) ) // TravId is set by DFS
        {
            pObj->pCopy = Abc_NtkCreatePi(pNtkNew);
//          Abc_ObjAssignName( pObj->pCopy, Abc_ObjName(pObj), NULL );
            Abc_NtkLogicStoreName( pObj->pCopy, Abc_ObjName(pObj) );
        }
    }

    // copy the nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        // if it is an AIG, add to the hash table
        if ( Abc_NtkIsStrash(pNtk) )
        {
            pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
        }
        else
        {
            Abc_NtkDupObj( pNtkNew, pObj );
            Abc_ObjForEachFanin( pObj, pFanin, k )
                Abc_ObjAddFanin( pObj->pCopy, pFanin->pCopy );
        }
    }
    Vec_PtrFree( vNodes );

    // add the PO corresponding to the nodes
    Vec_PtrForEachEntry( vRoots, pObj, i )
    {
        // create the PO node
        pNodeCoNew = Abc_NtkCreatePo( pNtkNew );
        // connect the internal nodes to the new CO
        if ( Abc_ObjIsCo(pObj) )
            Abc_ObjAddFanin( pNodeCoNew, Abc_ObjChild0Copy(pObj) );
        else
            Abc_ObjAddFanin( pNodeCoNew, pObj->pCopy );
        // assign the name
//      Abc_ObjAssignName( pNodeCoNew, Abc_ObjName(pObj), NULL );
        Abc_NtkLogicStoreName( pNodeCoNew, Abc_ObjName(pObj) );
    }

    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkCreateConeArray(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Appends the second network to the first.]

  Description [Modifies the first network by adding the logic of the second. 
  Performs structural hashing while appending the networks. Does not change 
  the second network. Returns 0 if the appending failed, 1 otherise.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkAppendNew( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 )
{
    Abc_Obj_t * pObj;
//    char * pName;
    int i, nNewCis;
    // the first network should be an AIG
    assert( Abc_NtkIsStrash(pNtk1) );
    assert( Abc_NtkIsStrash(pNtk2) ); 
    // check that the networks have the same PIs
    // reorder PIs of pNtk2 according to pNtk1
//    if ( !Abc_NtkCompareSignals( pNtk1, pNtk2, 1, 1 ) )
//        printf( "Abc_NtkAppend(): The union of the network PIs is computed (warning).\n" );
    // perform strashing
    nNewCis = 0;
    Abc_NtkCleanCopy( pNtk2 );
    Abc_AigConst1(pNtk2->pManFunc)->pCopy = Abc_AigConst1(pNtk1->pManFunc);
    Abc_NtkForEachCi( pNtk2, pObj, i )
    {
//        pName = Abc_ObjName(pObj);
//        pObj->pCopy = Abc_NtkFindCi(pNtk1, Abc_ObjName(pObj));
        pObj->pCopy = Abc_NtkCi( pNtk1, i );
        if ( pObj->pCopy == NULL )
        {
            pObj->pCopy = Abc_NtkDupObj( pNtk1, pObj );
            nNewCis++;
        }
    }
    if ( nNewCis )
        printf( "Warning: Procedure Abc_NtkAppend() added %d new CIs.\n", nNewCis );
    // add pNtk2 to pNtk1 while strashing
    Abc_NtkForEachNode( pNtk2, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 )
            continue;
        pObj->pCopy = Abc_AigAnd( pNtk1->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
    }
    // add the COs of the second network
    {
        Abc_Obj_t * pObjOld, * pDriverOld, * pDriverNew;
        int fCompl;//, iNodeId;
        // OR the choices
        Abc_NtkForEachCo( pNtk2, pObj, i )
        {
//            iNodeId = Nm_ManFindIdByNameTwoTypes( pNtk1->pManName, Abc_ObjName(pObj), ABC_OBJ_PO, ABC_OBJ_BI );
//            assert( iNodeId >= 0 );
//            pObjOld = Abc_NtkObj( pNtk1, iNodeId );
            pObjOld = Abc_NtkCo( pNtk1, i );

            // derive the new driver
            pDriverOld = Abc_ObjChild0( pObjOld );
            pDriverNew = Abc_ObjChild0Copy( pObj );
            pDriverNew = Abc_AigOr( pNtk1->pManFunc, pDriverOld, pDriverNew );
            if ( Abc_ObjRegular(pDriverOld) == Abc_ObjRegular(pDriverNew) )
                continue;
            // replace the old driver by the new driver
            fCompl = Abc_ObjRegular(pDriverOld)->fPhase ^ Abc_ObjRegular(pDriverNew)->fPhase;
            Abc_ObjPatchFanin( pObjOld, Abc_ObjRegular(pDriverOld), Abc_ObjNotCond(Abc_ObjRegular(pDriverNew), fCompl) );
        }
    }
    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtk1 ) )
    {
        printf( "Abc_NtkAppend: The network check has failed.\n" );
        return 0;
    }
    return 1;
}




/**Function*************************************************************

  Synopsis    [Prepare supports.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkPartitionCollectSupps( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vSupp, * vSupports;
    Vec_Int_t * vSuppI;
    Abc_Obj_t * pObj, * pTemp;
    int i, k;
    vSupports = Vec_PtrAlloc( Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        vSupp = Abc_NtkNodeSupport( pNtk, &pObj, 1 );
        vSuppI = (Vec_Int_t *)vSupp;
        Vec_PtrForEachEntry( vSupp, pTemp, k )
            Vec_IntWriteEntry( vSuppI, k, pTemp->Id );
        Vec_IntSort( vSuppI, 0 );
        // append the number of this output
        Vec_IntPush( vSuppI, i );
        // save the support in the vector
        Vec_PtrPush( vSupports, vSuppI );
    }
    // sort supports by size
    Vec_VecSort( (Vec_Vec_t *)vSupports, 1 );
    return vSupports;
}

/**Function*************************************************************

  Synopsis    [Find the best partition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkPartitionSmartFindPart( Vec_Ptr_t * vPartSuppsAll, Vec_Ptr_t * vPartsAll, int nPartSizeLimit, Vec_Int_t * vOne )
{
    Vec_Int_t * vPartSupp, * vPart;
    double Attract, Repulse, Cost, CostBest;
    int i, nCommon, iBest;
    iBest = -1;
    CostBest = 0.0;
    Vec_PtrForEachEntry( vPartSuppsAll, vPartSupp, i )
    {
        nCommon = Vec_IntTwoCountCommon( vPartSupp, vOne );
        if ( nCommon == 0 )
            continue;
        vPart = Vec_PtrEntry( vPartsAll, i );
        if ( nPartSizeLimit > 0 && Vec_IntSize(vPart) > nPartSizeLimit )
            continue;
        if ( nCommon == Vec_IntSize(vOne) )
            return i;
        Attract = 1.0 * nCommon / Vec_IntSize(vOne);
        if ( Vec_IntSize(vPartSupp) < 100 )
            Repulse = 1.0;
        else
            Repulse = log10( Vec_IntSize(vPartSupp) / 10.0 );
        Cost = pow( Attract, pow(Repulse, 5.0) );
        if ( CostBest < Cost )
        {
            CostBest = Cost;
            iBest = i;
        }
    }
    if ( CostBest < 0.6 )
        return -1;
    return iBest;
}

/**Function*************************************************************

  Synopsis    [Perform the smart partitioning.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPartitionPrint( Abc_Ntk_t * pNtk, Vec_Ptr_t * vPartsAll, Vec_Ptr_t * vPartSuppsAll )
{
    Vec_Int_t * vOne;
    int i, nOutputs, Counter;

    Counter = 0;
    Vec_PtrForEachEntry( vPartSuppsAll, vOne, i )
    {
        nOutputs = Vec_IntSize(Vec_PtrEntry(vPartsAll, i));
        printf( "%d=(%d,%d) ", i, Vec_IntSize(vOne), nOutputs );
        Counter += nOutputs;
        if ( i == Vec_PtrSize(vPartsAll) - 1 )
            break;
    }
    assert( Counter == Abc_NtkCoNum(pNtk) );
    printf( "\nTotal = %d. Outputs = %d.\n", Counter, Abc_NtkCoNum(pNtk) );
}

/**Function*************************************************************

  Synopsis    [Perform the smart partitioning.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPartitionCompact( Vec_Ptr_t * vPartsAll, Vec_Ptr_t * vPartSuppsAll, int nPartSizeLimit )
{
    Vec_Int_t * vOne, * vPart, * vPartSupp, * vTemp;
    int i, iPart;

    if ( nPartSizeLimit == 0 )
        nPartSizeLimit = 200;

    // pack smaller partitions into larger blocks
    iPart = 0;
    vPart = vPartSupp = NULL;
    Vec_PtrForEachEntry( vPartSuppsAll, vOne, i )
    {
        if ( Vec_IntSize(vOne) < nPartSizeLimit )
        {
            if ( vPartSupp == NULL )
            {
                assert( vPart == NULL );
                vPartSupp = Vec_IntDup(vOne);
                vPart = Vec_PtrEntry(vPartsAll, i);
            }
            else
            {
                vPartSupp = Vec_IntTwoMerge( vTemp = vPartSupp, vOne );
                Vec_IntFree( vTemp );
                vPart = Vec_IntTwoMerge( vTemp = vPart, Vec_PtrEntry(vPartsAll, i) );
                Vec_IntFree( vTemp );
                Vec_IntFree( Vec_PtrEntry(vPartsAll, i) );
            }
            if ( Vec_IntSize(vPartSupp) < nPartSizeLimit )
                continue;
        }
        else
            vPart = Vec_PtrEntry(vPartsAll, i);
        // add the partition 
        Vec_PtrWriteEntry( vPartsAll, iPart, vPart );  
        vPart = NULL;
        if ( vPartSupp ) 
        {
            Vec_IntFree( Vec_PtrEntry(vPartSuppsAll, iPart) );
            Vec_PtrWriteEntry( vPartSuppsAll, iPart, vPartSupp );  
            vPartSupp = NULL;
        }
        iPart++;
    }
    // add the last one
    if ( vPart )
    {
        Vec_PtrWriteEntry( vPartsAll, iPart, vPart );  
        vPart = NULL;

        assert( vPartSupp != NULL );
        Vec_IntFree( Vec_PtrEntry(vPartSuppsAll, iPart) );
        Vec_PtrWriteEntry( vPartSuppsAll, iPart, vPartSupp );  
        vPartSupp = NULL;
        iPart++;
    }
    Vec_PtrShrink( vPartsAll, iPart );
    Vec_PtrShrink( vPartsAll, iPart );
}

/**Function*************************************************************

  Synopsis    [Perform the smart partitioning.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * Abc_NtkPartitionSmart( Abc_Ntk_t * pNtk, int nPartSizeLimit, int fVerbose )
{
    Vec_Ptr_t * vSupps, * vPartsAll, * vPartsAll2, * vPartSuppsAll, * vPartPtr;
    Vec_Int_t * vOne, * vPart, * vPartSupp, * vTemp;
    int i, iPart, iOut, clk;

    // compute the supports for all outputs
clk = clock();
    vSupps = Abc_NtkPartitionCollectSupps( pNtk );
if ( fVerbose )
{
PRT( "Supps", clock() - clk );
}

    // create partitions
clk = clock();
    vPartsAll = Vec_PtrAlloc( 256 );
    vPartSuppsAll = Vec_PtrAlloc( 256 );
    Vec_PtrForEachEntry( vSupps, vOne, i )
    {
        // get the output number
        iOut = Vec_IntPop(vOne);
        // find closely matching part
        iPart = Abc_NtkPartitionSmartFindPart( vPartSuppsAll, vPartsAll, nPartSizeLimit, vOne );
        if ( iPart == -1 )
        {
            // create new partition
            vPart = Vec_IntAlloc( 32 );
            Vec_IntPush( vPart, iOut );
            // create new partition support
            vPartSupp = Vec_IntDup( vOne );
            // add this partition and its support
            Vec_PtrPush( vPartsAll, vPart );
            Vec_PtrPush( vPartSuppsAll, vPartSupp );
        }
        else
        {
            // add output to this partition
            vPart = Vec_PtrEntry( vPartsAll, iPart );
            Vec_IntPush( vPart, iOut );
            // merge supports
            vPartSupp = Vec_PtrEntry( vPartSuppsAll, iPart );
            vPartSupp = Vec_IntTwoMerge( vTemp = vPartSupp, vOne );
            Vec_IntFree( vTemp );
            // reinsert new support
            Vec_PtrWriteEntry( vPartSuppsAll, iPart, vPartSupp );
        }
    }
if ( fVerbose )
{
PRT( "Parts", clock() - clk );
}

clk = clock();
    // remember number of supports
    Vec_PtrForEachEntry( vPartSuppsAll, vOne, i )
        Vec_IntPush( vOne, i );
    // sort the supports in the decreasing order
    Vec_VecSort( (Vec_Vec_t *)vPartSuppsAll, 1 );
    // reproduce partitions
    vPartsAll2 = Vec_PtrAlloc( 256 );
    Vec_PtrForEachEntry( vPartSuppsAll, vOne, i )
        Vec_PtrPush( vPartsAll2, Vec_PtrEntry(vPartsAll, Vec_IntPop(vOne)) );
    Vec_PtrFree( vPartsAll );
    vPartsAll = vPartsAll2;

    // compact small partitions
//    Abc_NtkPartitionPrint( pNtk, vPartsAll, vPartSuppsAll );
    Abc_NtkPartitionCompact( vPartsAll, vPartSuppsAll, nPartSizeLimit );
    if ( fVerbose )
    Abc_NtkPartitionPrint( pNtk, vPartsAll, vPartSuppsAll );
if ( fVerbose )
{
PRT( "Comps", clock() - clk );
}

    // cleanup
    Vec_VecFree( (Vec_Vec_t *)vSupps );
    Vec_VecFree( (Vec_Vec_t *)vPartSuppsAll );

    // converts from intergers to nodes
    Vec_PtrForEachEntry( vPartsAll, vPart, iPart )
    {
        vPartPtr = Vec_PtrAlloc( Vec_IntSize(vPart) );
        Vec_IntForEachEntry( vPart, iOut, i )
            Vec_PtrPush( vPartPtr, Abc_NtkCo(pNtk, iOut) );
        Vec_IntFree( vPart );
        Vec_PtrWriteEntry( vPartsAll, iPart, vPartPtr );
    }
    return (Vec_Vec_t *)vPartsAll;
}

/**Function*************************************************************

  Synopsis    [Perform the naive partitioning.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * Abc_NtkPartitionNaive( Abc_Ntk_t * pNtk, int nPartSize )
{
    Vec_Vec_t * vParts;
    Abc_Obj_t * pObj;
    int nParts, i;
    nParts = (Abc_NtkCoNum(pNtk) / nPartSize) + ((Abc_NtkCoNum(pNtk) % nPartSize) > 0);
    vParts = Vec_VecStart( nParts );
    Abc_NtkForEachCo( pNtk, pObj, i )
        Vec_VecPush( vParts, i / nPartSize, pObj );
    return vParts;
}

/**Function*************************************************************

  Synopsis    [Returns representative of the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkPartStitchFindRepr_rec( Vec_Ptr_t * vEquiv, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pRepr;
    pRepr = Vec_PtrEntry( vEquiv, pObj->Id );
    if ( pRepr == NULL || pRepr == pObj )
        return pObj;
    return Abc_NtkPartStitchFindRepr_rec( vEquiv, pRepr );
}

/**Function*************************************************************

  Synopsis    [Returns the representative of the fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_Obj_t * Abc_NtkPartStitchCopy0( Vec_Ptr_t * vEquiv, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFan = Abc_ObjFanin0( pObj );
    Abc_Obj_t * pRepr = Abc_NtkPartStitchFindRepr_rec( vEquiv, pFan );
    return Abc_ObjNotCond( pRepr->pCopy, pRepr->fPhase ^ pFan->fPhase ^ Abc_ObjFaninC1(pObj) );
}
static inline Abc_Obj_t * Abc_NtkPartStitchCopy1( Vec_Ptr_t * vEquiv, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFan = Abc_ObjFanin1( pObj );
    Abc_Obj_t * pRepr = Abc_NtkPartStitchFindRepr_rec( vEquiv, pFan );
    return Abc_ObjNotCond( pRepr->pCopy, pRepr->fPhase ^ pFan->fPhase ^ Abc_ObjFaninC1(pObj) );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Hop_Obj_t * Hop_ObjChild0Next( Abc_Obj_t * pObj ) { return Hop_NotCond( (Hop_Obj_t *)Abc_ObjFanin0(pObj)->pNext, Abc_ObjFaninC0(pObj) ); }
static inline Hop_Obj_t * Hop_ObjChild1Next( Abc_Obj_t * pObj ) { return Hop_NotCond( (Hop_Obj_t *)Abc_ObjFanin1(pObj)->pNext, Abc_ObjFaninC1(pObj) ); }


/**Function*************************************************************

  Synopsis    [Stitches together several networks with choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Man_t * Abc_NtkPartStartHop( Abc_Ntk_t * pNtk )
{
    Hop_Man_t * pMan;
    Abc_Obj_t * pObj;
    int i;
    // start the HOP package
    pMan = Hop_ManStart();
    pMan->vObjs = Vec_PtrAlloc( Abc_NtkObjNumMax(pNtk) + 1  );
    Vec_PtrPush( pMan->vObjs, Hop_ManConst1(pMan) );
    // map constant node and PIs
    Abc_AigConst1(pNtk->pManFunc)->pNext = (Abc_Obj_t *)Hop_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pNext = (Abc_Obj_t *)Hop_ObjCreatePi(pMan);
    // map the internal nodes
//  Abc_AigForEachAnd( pNtk, pObj, i )
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 )
            continue;
        pObj->pNext = (Abc_Obj_t *)Hop_And( pMan, Hop_ObjChild0Next(pObj), Hop_ObjChild1Next(pObj) );
        assert( !Abc_ObjIsComplement(pObj->pNext) );
    }
    // set the choice nodes
//  Abc_AigForEachAnd( pNtk, pObj, i )
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 )
            continue;
        if ( pObj->pCopy )
            ((Hop_Obj_t *)pObj->pNext)->pData = pObj->pCopy->pNext;
    }
    // transfer the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Hop_ObjCreatePo( pMan, Hop_ObjChild0Next(pObj) );
    // check the new manager
    if ( !Hop_ManCheck(pMan) )
        printf( "Abc_NtkPartStartHop: HOP manager check has failed.\n" );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Maps terminals of the old networks into those of the new network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPartMapTerminals( Vec_Ptr_t * vParts, Abc_Ntk_t * pNtkOld )
{
    Abc_Ntk_t * pNtkNew;
    stmm_table * tTablePi, * tTablePo;
    Abc_Obj_t * pObj, * pTemp;
    int i, k;

    // map names into old nodes
    tTablePi = stmm_init_table( strcmp, stmm_strhash );
    tTablePo = stmm_init_table( strcmp, stmm_strhash );
    Abc_NtkForEachPi( pNtkOld, pObj, i )
        stmm_insert( tTablePi, Abc_ObjName(pObj), (char *)pObj );
    Abc_NtkForEachPo( pNtkOld, pObj, i )
        stmm_insert( tTablePo, Abc_ObjName(pObj), (char *)pObj );

    // map new nodes into old nodes
    Vec_PtrForEachEntry( vParts, pNtkNew, k )
    {
        Abc_NtkForEachPi( pNtkNew, pObj, i )
        {
            if ( !stmm_lookup(tTablePi, Abc_ObjName(pObj), (char **)&pTemp) )
            {
                printf( "Cannot find PI node %s in the original network.\n", Abc_ObjName(pObj) );
                return;
            }
            pObj->pCopy = pTemp;
        }
        Abc_NtkForEachPo( pNtkNew, pObj, i )
        {
            if ( !stmm_lookup(tTablePo, Abc_ObjName(pObj), (char **)&pTemp) )
            {
                printf( "Cannot find PO node %s in the original network.\n", Abc_ObjName(pObj) );
                return;
            }
            pObj->pCopy = pTemp;
        }
    }
    stmm_free_table( tTablePi );
    stmm_free_table( tTablePo );
}

/**Function*************************************************************

  Synopsis    [Stitches together several networks with choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkPartStitchChoices( Abc_Ntk_t * pNtk, Vec_Ptr_t * vParts )
{
    extern Abc_Ntk_t * Abc_NtkHopRemoveLoops( Abc_Ntk_t * pNtk, Hop_Man_t * pMan );

    Hop_Man_t * pMan;
    Abc_Ntk_t * pNtkNew, * pNtkTemp;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pFanin;
    int i, k;

    // start a new network similar to the original one
    assert( Abc_NtkIsStrash(pNtk) );
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_STRASH, ABC_FUNC_AIG );


    // annotate parts to point to the new network
    Vec_PtrForEachEntry( vParts, pNtkTemp, i )
    {
        assert( Abc_NtkIsStrash(pNtkTemp) );
        Abc_NtkCleanCopy( pNtkTemp );
    }

    // perform mapping of terminals
    Abc_NtkPartMapTerminals( vParts, pNtkNew );


    // annotate parts to point to the new network
    Vec_PtrForEachEntry( vParts, pNtkTemp, i )
    {
//        assert( Abc_NtkIsStrash(pNtkTemp) );
//        Abc_NtkCleanCopy( pNtkTemp );

        // map the CI nodes
        Abc_AigConst1(pNtkTemp->pManFunc)->pCopy = Abc_AigConst1(pNtkNew->pManFunc);
/*
        Abc_NtkForEachCi( pNtkTemp, pObj, k )
        {
            iNodeId = Nm_ManFindIdByNameTwoTypes( pNtkNew->pManName, Abc_ObjName(pObj), ABC_OBJ_PI, ABC_OBJ_BO );
            if ( iNodeId == -1 )
            {
                printf( "Cannot find CI node %s in the original network.\n", Abc_ObjName(pObj) );
                return NULL;
            }
            pObj->pCopy = Abc_NtkObj( pNtkNew, iNodeId );
        }
*/
        // add the internal nodes while saving representatives
        vNodes = Abc_AigDfs( pNtkTemp, 1, 0 );
        Vec_PtrForEachEntry( vNodes, pObj, k )
        {
            if ( Abc_ObjFaninNum(pObj) == 0 )
                continue;
            pObj->pCopy = Abc_AigAnd( pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
            assert( !Abc_ObjIsComplement(pObj->pCopy) );
            if ( Abc_NodeIsAigChoice(pObj) )
                for ( pFanin = pObj->pData; pFanin; pFanin = pFanin->pData )
                    pFanin->pCopy->pCopy = pObj->pCopy;
        }
        Vec_PtrFree( vNodes );

        // map the CO nodes
        Abc_NtkForEachCo( pNtkTemp, pObj, k )
        {
/*
            iNodeId = Nm_ManFindIdByNameTwoTypes( pNtkNew->pManName, Abc_ObjName(pObj), ABC_OBJ_PO, ABC_OBJ_BI );
            if ( iNodeId == -1 )
            {
                printf( "Cannot find CO node %s in the original network.\n", Abc_ObjName(pObj) );
                return NULL;
            }
            pObj->pCopy = Abc_NtkObj( pNtkNew, iNodeId );
*/
            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjChild0Copy(pObj) );
        }
    }


    // transform into the HOP manager
    pMan = Abc_NtkPartStartHop( pNtkNew );
    pNtkNew = Abc_NtkHopRemoveLoops( pNtkTemp = pNtkNew, pMan );
    Abc_NtkDelete( pNtkTemp );

    // check correctness of the new network
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkPartStitchChoices: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Stitches together several networks with choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFraigPartitioned( Abc_Ntk_t * pNtk, void * pParams )
{
    extern int Cmd_CommandExecute( void * pAbc, char * sCommand );
    extern void * Abc_FrameGetGlobalFrame();

    Vec_Vec_t * vParts;
    Vec_Ptr_t * vFraigs, * vOne;
    Abc_Ntk_t * pNtkAig, * pNtkFraig;
    int i;

    // perform partitioning
    assert( Abc_NtkIsStrash(pNtk) );
//    vParts = Abc_NtkPartitionNaive( pNtk, 20 );
    vParts = Abc_NtkPartitionSmart( pNtk, 0, 0 );

    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "unset progressbar" );

    // fraig each partition
    vFraigs = Vec_PtrAlloc( Vec_VecSize(vParts) );
    Vec_VecForEachLevel( vParts, vOne, i )
    {
        pNtkAig = Abc_NtkCreateConeArray( pNtk, vOne, 0 );
        pNtkFraig = Abc_NtkFraig( pNtkAig, pParams, 0 );
        Vec_PtrPush( vFraigs, pNtkFraig );
        Abc_NtkDelete( pNtkAig );

        printf( "Finished part %d (out of %d)\r", i+1, Vec_VecSize(vParts) );
    }
    Vec_VecFree( vParts );
    printf( "                                              \r" );

    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "set progressbar" );

    // derive the final network
    pNtkFraig = Abc_NtkPartStitchChoices( pNtk, vFraigs );
    Vec_PtrForEachEntry( vFraigs, pNtkAig, i )
    {
//        Abc_NtkPrintStats( stdout, pNtkAig, 0 );
        Abc_NtkDelete( pNtkAig );
    }
    Vec_PtrFree( vFraigs );

    return pNtkFraig;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


