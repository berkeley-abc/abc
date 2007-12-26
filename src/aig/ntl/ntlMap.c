/**CFile****************************************************************

  FileName    [ntlMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Derives mapped network from AIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlMap.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"
#include "kit.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates mapping for the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_MappingAlloc( int nLuts, int nVars )
{
    char * pMemory;
    Ntl_Lut_t ** pArray;
    int nEntrySize, i;
    nEntrySize = sizeof(Ntl_Lut_t) + sizeof(int) * nVars + sizeof(unsigned) * Aig_TruthWordNum(nVars);
    pArray = (Ntl_Lut_t **)malloc( (sizeof(Ntl_Lut_t *) + nEntrySize) * nLuts );
    pMemory = (char *)(pArray + nLuts);
    memset( pMemory, 0, nEntrySize * nLuts );
    for ( i = 0; i < nLuts; i++ )
    {
        pArray[i] = (Ntl_Lut_t *)pMemory;
        pArray[i]->pFanins = (int *)(pMemory + sizeof(Ntl_Lut_t));
        pArray[i]->pTruth = (unsigned *)(pMemory + sizeof(Ntl_Lut_t) + sizeof(int) * nVars);
        pMemory += nEntrySize;
    }
    return Vec_PtrAllocArray( (void **)pArray, nLuts );
}

/**Function*************************************************************

  Synopsis    [Derives trivial mapping from the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_MappingFromAig( Aig_Man_t * p )
{
    Vec_Ptr_t * vMapping;
    Ntl_Lut_t * pLut;
    Aig_Obj_t * pObj;
    int i, k = 0, nBytes = 4;
    vMapping = Ntl_MappingAlloc( Aig_ManAndNum(p) + (int)(Aig_ManConst1(p)->nRefs > 0), 2 );
    if ( Aig_ManConst1(p)->nRefs > 0 )
    {
        pLut = Vec_PtrEntry( vMapping, k++ );
        pLut->Id = 0;
        pLut->nFanins = 0;
        memset( pLut->pTruth, 0xFF, nBytes );
    }
    Aig_ManForEachNode( p, pObj, i )
    {
        pLut = Vec_PtrEntry( vMapping, k++ );
        pLut->Id = pObj->Id;
        pLut->nFanins = 2;
        pLut->pFanins[0] = Aig_ObjFaninId0(pObj);
        pLut->pFanins[1] = Aig_ObjFaninId1(pObj);
        if      (  Aig_ObjFaninC0(pObj) &&  Aig_ObjFaninC1(pObj) ) 
            memset( pLut->pTruth, 0x11, nBytes );
        else if ( !Aig_ObjFaninC0(pObj) &&  Aig_ObjFaninC1(pObj) )
            memset( pLut->pTruth, 0x22, nBytes );
        else if (  Aig_ObjFaninC0(pObj) && !Aig_ObjFaninC1(pObj) )
            memset( pLut->pTruth, 0x44, nBytes );
        else if ( !Aig_ObjFaninC0(pObj) && !Aig_ObjFaninC1(pObj) )
            memset( pLut->pTruth, 0x88, nBytes );
    }
    assert( k == Vec_PtrSize(vMapping) );
    return vMapping;
}


#include "fpgaInt.h"

/**Function*************************************************************

  Synopsis    [Recursively derives the truth table for the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Ntl_FpgaComputeTruth_rec( Fpga_Cut_t * pCut, Vec_Ptr_t * vTruthElem, Vec_Ptr_t * vTruthStore, Vec_Ptr_t * vVisited, int nVars, int * pnCounter )
{
    unsigned * pTruth, * pTruth0, * pTruth1;
    assert( !Fpga_IsComplement(pCut) );
    // if the cut is visited, return the result
    if ( pCut->pRoot )
        return (unsigned *)pCut->pRoot;
    // compute the functions of the children
    pTruth0 = Ntl_FpgaComputeTruth_rec( Fpga_CutRegular(pCut->pOne), vTruthElem, vTruthStore, vVisited, nVars, pnCounter );  
    if ( Fpga_CutIsComplement(pCut->pOne) )
        Kit_TruthNot( pTruth0, pTruth0, nVars );
    pTruth1 = Ntl_FpgaComputeTruth_rec( Fpga_CutRegular(pCut->pTwo), vTruthElem, vTruthStore, vVisited, nVars, pnCounter );   
    if ( Fpga_CutIsComplement(pCut->pTwo) )
        Kit_TruthNot( pTruth1, pTruth1, nVars );
    // get the function of the cut
    pTruth = Vec_PtrEntry( vTruthStore, (*pnCounter)++ );
    Kit_TruthAnd( pTruth, pTruth0, pTruth1, nVars );
    if ( pCut->Phase )
        Kit_TruthNot( pTruth, pTruth, nVars );
    assert( pCut->pRoot == NULL );
    pCut->pRoot = (Fpga_Node_t *)pTruth;
    // add this cut to the visited list
    Vec_PtrPush( vVisited, pCut );
    return pTruth;
}

/**Function*************************************************************

  Synopsis    [Derives the truth table for one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Ntl_FpgaComputeTruth( Fpga_Cut_t * pCut, Vec_Ptr_t * vTruthElem, Vec_Ptr_t * vTruthStore, Vec_Ptr_t * vVisited, int nVars )
{
    unsigned * pTruth;
    int i, nCounter = 0;
    assert( pCut->nLeaves > 1 );
    // set the leaf variables
    for ( i = 0; i < pCut->nLeaves; i++ )
        pCut->ppLeaves[i]->pCuts->pRoot = (Fpga_Node_t *)Vec_PtrEntry( vTruthElem, i );
    // recursively compute the function
    Vec_PtrClear( vVisited );
    pTruth = Ntl_FpgaComputeTruth_rec( pCut, vTruthElem, vTruthStore, vVisited, nVars, &nCounter ); 
    // clean the intermediate BDDs
    for ( i = 0; i < pCut->nLeaves; i++ )
        pCut->ppLeaves[i]->pCuts->pRoot = NULL;
    Vec_PtrForEachEntry( vVisited, pCut, i )
        pCut->pRoot = NULL;
    return pTruth;
}


/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fpga_Man_t * Ntl_ManToFpga( Aig_Man_t * p )
{
    Fpga_Man_t * pMan;
    Aig_Obj_t * pNode;//, * pFanin, * pPrev;
    float * pfArrivals;
    int i;
    // start the mapping manager and set its parameters
    pMan = Fpga_ManCreate( Aig_ManPiNum(p), Aig_ManPoNum(p), 0 );
    if ( pMan == NULL )
        return NULL;
    // set the arrival times
    pfArrivals = ALLOC( float, Aig_ManPiNum(p) );
    memset( pfArrivals, 0, sizeof(float) * Aig_ManPiNum(p) );
    Fpga_ManSetInputArrivals( pMan, pfArrivals );
    // create PIs and remember them in the old nodes
    Aig_ManConst1(p)->pData = Fpga_ManReadConst1(pMan);
    Aig_ManForEachPi( p, pNode, i )
        pNode->pData = Fpga_ManReadInputs(pMan)[i];
    // load the AIG into the mapper
    Aig_ManForEachNode( p, pNode, i )
    {
        pNode->pData = Fpga_NodeAnd( pMan, 
            Fpga_NotCond( Aig_ObjFanin0(pNode)->pData, Aig_ObjFaninC0(pNode) ),
            Fpga_NotCond( Aig_ObjFanin1(pNode)->pData, Aig_ObjFaninC1(pNode) ) );
        // set up the choice node
//        if ( Aig_AigNodeIsChoice( pNode ) )
//            for ( pPrev = pNode, pFanin = pNode->pData; pFanin; pPrev = pFanin, pFanin = pFanin->pData )
//            {
//                Fpga_NodeSetNextE( (If_Obj_t *)pPrev->pData, (If_Obj_t *)pFanin->pData );
//                Fpga_NodeSetRepr( (If_Obj_t *)pFanin->pData, (If_Obj_t *)pNode->pData );
//            }
    }
    // set the primary outputs while copying the phase
    Aig_ManForEachPo( p, pNode, i )
        Fpga_ManReadOutputs(pMan)[i] = Fpga_NotCond( Aig_ObjFanin0(pNode)->pData, Aig_ObjFaninC0(pNode) );
    assert( Fpga_NodeVecReadSize(pMan->vAnds) == Aig_ManNodeNum(p) );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Creates the mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_ManFromFpga( Aig_Man_t * p, Fpga_Man_t * pMan )
{
    Fpga_NodeVec_t * vFpgaMap;
    Fpga_Node_t ** ppLeaves, * pNode; 
    Fpga_Cut_t * pCutBest;
    Vec_Ptr_t * vTruthElem, * vTruthStore, * vVisited, * vMapping;
    Vec_Int_t * vFpgaToAig;
    Aig_Obj_t * pObj;
    Ntl_Lut_t * pLut;
    unsigned * pTruth;
    int i, k, nLuts, nLeaves, nWords, nVarsMax;
    // create mapping of FPGA nodes into AIG nodes
    vFpgaToAig = Vec_IntStart( Aig_ManObjNumMax(p) );
    Vec_IntFill( vFpgaToAig, Aig_ManObjNumMax(p), -1 );
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsPo(pObj) )
            continue;
        if ( Aig_ObjIsConst1(pObj) && pObj->pData == NULL )
            continue;
        pNode = pObj->pData;
        assert( pNode != NULL );
        Vec_IntWriteEntry( vFpgaToAig, Fpga_NodeReadNum(pNode), pObj->Id );
    }
    // create the mapping


    // make sure nodes are in the top order!!!


    nVarsMax = Fpga_ManReadVarMax( pMan );
    nWords   = Aig_TruthWordNum( nVarsMax );
    vFpgaMap = Fpga_ManReadMapping( pMan );
    vMapping = Ntl_MappingAlloc( vFpgaMap->nSize + (int)(Aig_ManConst1(p)->nRefs > 0), nVarsMax );
    nLuts    = 0;
    if ( Aig_ManConst1(p)->nRefs > 0 )
    {
        pLut = Vec_PtrEntry( vMapping, nLuts++ );
        pLut->Id = 0;
        pLut->nFanins = 0;
        memset( pLut->pTruth, 0xFF, 4 * nWords );
    }
    vVisited    = Vec_PtrAlloc( 1000 );
    vTruthElem  = Vec_PtrAllocTruthTables( nVarsMax );
    vTruthStore = Vec_PtrAllocSimInfo( 256, nWords );
    for ( i = 0; i < vFpgaMap->nSize; i++ )
    {
        // get the best cut
        pNode    = vFpgaMap->pArray[i];
        pCutBest = Fpga_NodeReadCutBest( pNode );
        nLeaves  = Fpga_CutReadLeavesNum( pCutBest ); 
        ppLeaves = Fpga_CutReadLeaves( pCutBest );
        // fill the LUT
        pLut = Vec_PtrEntry( vMapping, nLuts++ );
        pLut->Id = Vec_IntEntry( vFpgaToAig, Fpga_NodeReadNum(pNode) );
        pLut->nFanins = nLeaves;
        for ( k = 0; k < nLeaves; k++ )
            pLut->pFanins[k] = Vec_IntEntry( vFpgaToAig, Fpga_NodeReadNum(ppLeaves[k]) );
        // compute the truth table
        pTruth = Ntl_FpgaComputeTruth( pCutBest, vTruthElem, vTruthStore, vVisited, nVarsMax );
        memcpy( pLut->pTruth, pTruth, 4 * nWords );
    }
    assert( nLuts == Vec_PtrSize(vMapping) );
    Vec_IntFree( vFpgaToAig );
    Vec_PtrFree( vVisited );
    Vec_PtrFree( vTruthElem );
    Vec_PtrFree( vTruthStore );
    return vMapping;
}

/**Function*************************************************************

  Synopsis    [Interface with the FPGA mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_MappingFpga( Aig_Man_t * p )
{
    Vec_Ptr_t * vMapping;
    Fpga_Man_t * pMan;
    // print a warning about choice nodes
    if ( p->pEquivs )
        printf( "Ntl_MappingFpga(): Performing FPGA mapping with choices.\n" );
    // perform FPGA mapping
    pMan = Ntl_ManToFpga( p );    
    if ( pMan == NULL )
        return NULL;
    if ( !Fpga_Mapping( pMan ) )
    {
        Fpga_ManFree( pMan );
        return NULL;
    }
    // transform the result of mapping into a BDD network
    vMapping = Ntl_ManFromFpga( p, pMan );
    Fpga_ManFree( pMan );
    if ( vMapping == NULL )
        return NULL;
    return vMapping;
}




#include "if.h"

/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManSetIfParsDefault( If_Par_t * pPars )
{
//    extern void * Abc_FrameReadLibLut();
    // set defaults
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
//    pPars->nLutSize    = -1;
    pPars->nLutSize    =  6;
    pPars->nCutsMax    =  8;
    pPars->nFlowIters  =  1;
    pPars->nAreaIters  =  2;
    pPars->DelayTarget = -1;
    pPars->fPreprocess =  1;
    pPars->fArea       =  0;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  0;
    pPars->fLatchPaths =  0;
    pPars->fEdge       =  1;
    pPars->fCutMin     =  1;
    pPars->fSeqMap     =  0;
    pPars->fVerbose    =  1;
    // internal parameters
    pPars->fTruth      =  1;
    pPars->nLatches    =  0;
    pPars->fLiftLeaves =  0;
//    pPars->pLutLib     =  Abc_FrameReadLibLut();
    pPars->pLutLib     =  NULL;
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->pFuncCost   =  NULL;   
/*
    if ( pPars->nLutSize == -1 )
    {
        if ( pPars->pLutLib == NULL )
        {
            printf( "The LUT library is not given.\n" );
            return;
        }
        // get LUT size from the library
        pPars->nLutSize = pPars->pLutLib->LutMax;
    }
*/
}

/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Man_t * Ntk_ManToIf( Aig_Man_t * p, If_Par_t * pPars )
{
    If_Man_t * pIfMan;
    Aig_Obj_t * pNode;//, * pFanin, * pPrev;
    Vec_Ptr_t * vNodes;
    int i;
    // start the mapping manager and set its parameters
    pIfMan = If_ManStart( pPars );
    // print warning about excessive memory usage
    if ( 1.0 * Aig_ManObjNum(p) * pIfMan->nObjBytes / (1<<30) > 1.0 )
        printf( "Warning: The mapper will allocate %.1f Gb for to represent the subject graph with %d AIG nodes.\n", 
            1.0 * Aig_ManObjNum(p) * pIfMan->nObjBytes / (1<<30), Aig_ManObjNum(p) );
    // load the AIG into the mapper
    vNodes = Aig_ManDfsPio( p );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        if ( Aig_ObjIsAnd(pNode) )
            pNode->pData = (Aig_Obj_t *)If_ManCreateAnd( pIfMan, 
                If_NotCond( (If_Obj_t *)Aig_ObjFanin0(pNode)->pData, Aig_ObjFaninC0(pNode) ), 
                If_NotCond( (If_Obj_t *)Aig_ObjFanin1(pNode)->pData, Aig_ObjFaninC1(pNode) ) );
        else if ( Aig_ObjIsPi(pNode) )
            pNode->pData = If_ManCreateCi( pIfMan );
        else if ( Aig_ObjIsPo(pNode) )
            If_ManCreateCo( pIfMan, If_NotCond( Aig_ObjFanin0(pNode)->pData, Aig_ObjFaninC0(pNode) ) );
        else if ( Aig_ObjIsConst1(pNode) )
            Aig_ManConst1(p)->pData = If_ManConst1( pIfMan );
        else // add the node to the mapper
            assert( 0 );
        // set up the choice node
//        if ( Aig_AigNodeIsChoice( pNode ) )
//        {
//            pIfMan->nChoices++;
//            for ( pPrev = pNode, pFanin = pNode->pData; pFanin; pPrev = pFanin, pFanin = pFanin->pData )
//                If_ObjSetChoice( (If_Obj_t *)pPrev->pData, (If_Obj_t *)pFanin->pData );
//            If_ManCreateChoice( pIfMan, (If_Obj_t *)pNode->pData );
//        }
    }
    Vec_PtrFree( vNodes );
    return pIfMan;
}

/**Function*************************************************************

  Synopsis    [Creates the mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntk_ManFromIf( Aig_Man_t * p, If_Man_t * pMan )
{
    Vec_Ptr_t * vIfMap;
    If_Obj_t * pNode, * pLeaf; 
    If_Cut_t * pCutBest;
    Vec_Ptr_t * vMapping;
    Vec_Int_t * vIfToAig;
    Aig_Obj_t * pObj;
    Ntl_Lut_t * pLut;
    int * ppLeaves;
    int i, k, nLuts, nLeaves, nWords, nVarsMax;
    // create mapping of If nodes into AIG nodes
    vIfToAig = Vec_IntStart( Aig_ManObjNumMax(p) );
    Vec_IntFill( vIfToAig, Aig_ManObjNumMax(p), -1 );
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsPo(pObj) )
            continue;
        if ( Aig_ObjIsConst1(pObj) && pObj->pData == NULL )
            continue;
        if ( Aig_ObjIsPi(pObj) && pObj->pData == NULL )
            continue;
        pNode = pObj->pData;
        assert( pNode != NULL );
        Vec_IntWriteEntry( vIfToAig, pNode->Id, pObj->Id );
    }
    // create the mapping
    If_ManScanMappingDirect( pMan );
    nVarsMax = pMan->pPars->nLutSize;
    nWords   = Aig_TruthWordNum( nVarsMax );
    vIfMap   = pMan->vMapped;
    vMapping = Ntl_MappingAlloc( Vec_PtrSize(vIfMap) + (int)(Aig_ManConst1(p)->nRefs > 0), nVarsMax );
    nLuts    = 0;
    if ( Aig_ManConst1(p)->nRefs > 0 )
    {
        pLut = Vec_PtrEntry( vMapping, nLuts++ );
        pLut->Id = 0;
        pLut->nFanins = 0;
        memset( pLut->pTruth, 0xFF, 4 * nWords );
    }
    Vec_PtrForEachEntry( vIfMap, pNode, i )
    {
        // get the best cut
        pCutBest = If_ObjCutBest(pNode);
        nLeaves  = If_CutLeaveNum( pCutBest ); 
        ppLeaves = If_CutLeaves( pCutBest );
        // fill the LUT
        pLut = Vec_PtrEntry( vMapping, nLuts++ );
        pLut->Id = Vec_IntEntry( vIfToAig, pNode->Id );
        pLut->nFanins = nLeaves;
        If_CutForEachLeaf( pMan, pCutBest, pLeaf, k )
            pLut->pFanins[k] = Vec_IntEntry( vIfToAig, pLeaf->Id );
        // compute the truth table
        memcpy( pLut->pTruth, If_CutTruth(pCutBest), 4 * nWords );
    }
    assert( nLuts == Vec_PtrSize(vMapping) );
    Vec_IntFree( vIfToAig );
    return vMapping;
}

/**Function*************************************************************

  Synopsis    [Interface with the FPGA mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_MappingIf( Aig_Man_t * p )
{
    Vec_Ptr_t * vMapping;
    If_Par_t Pars, * pPars = &Pars;
    If_Man_t * pIfMan;
    // perform FPGA mapping
    Ntk_ManSetIfParsDefault( pPars );
    // set the arrival times
    pPars->pTimesArr = ALLOC( float, Aig_ManPiNum(p) );
    memset( pPars->pTimesArr, 0, sizeof(float) * Aig_ManPiNum(p) );
    // translate into the mapper
    pIfMan = Ntk_ManToIf( p, pPars );    
    if ( pIfMan == NULL )
        return NULL;
    if ( !If_ManPerformMapping( pIfMan ) )
    {
        If_ManStop( pIfMan );
        return NULL;
    }
    // transform the result of mapping into the new network
    vMapping = Ntk_ManFromIf( p, pIfMan );
    If_ManStop( pIfMan );
    if ( vMapping == NULL )
        return NULL;
    return vMapping;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


