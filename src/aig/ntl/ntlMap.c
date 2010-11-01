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
#include "if.h"

ABC_NAMESPACE_IMPL_START


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
    pArray = (Ntl_Lut_t **)ABC_ALLOC( char, (sizeof(Ntl_Lut_t *) + nEntrySize) * nLuts );
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
        pLut = (Ntl_Lut_t *)Vec_PtrEntry( vMapping, k++ );
        pLut->Id = 0;
        pLut->nFanins = 0;
        memset( pLut->pTruth, 0xFF, nBytes );
    }
    Aig_ManForEachNode( p, pObj, i )
    {
        pLut = (Ntl_Lut_t *)Vec_PtrEntry( vMapping, k++ );
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


/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManSetIfParsDefault( If_Par_t * pPars )
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
    pPars->Epsilon     =  (float)0.005;
    pPars->fPreprocess =  1;
    pPars->fArea       =  0;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  0;
    pPars->fLatchPaths =  0;
    pPars->fEdge       =  1;
    pPars->fCutMin     =  0;
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
If_Man_t * Ntl_ManToIf( Aig_Man_t * p, If_Par_t * pPars )
{
    If_Man_t * pIfMan;
    Aig_Obj_t * pNode;//, * pFanin, * pPrev;
    int i;
    // start the mapping manager and set its parameters
    pIfMan = If_ManStart( pPars );
    // print warning about excessive memory usage
    if ( 1.0 * Aig_ManObjNum(p) * pIfMan->nObjBytes / (1<<30) > 1.0 )
        printf( "Warning: The mapper will allocate %.1f Gb for to represent the subject graph with %d AIG nodes.\n", 
            1.0 * Aig_ManObjNum(p) * pIfMan->nObjBytes / (1<<30), Aig_ManObjNum(p) );
    // load the AIG into the mapper
    Aig_ManForEachObj( p, pNode, i )
    {
        if ( Aig_ObjIsAnd(pNode) )
            pNode->pData = (Aig_Obj_t *)If_ManCreateAnd( pIfMan, 
                If_NotCond( (If_Obj_t *)Aig_ObjFanin0(pNode)->pData, Aig_ObjFaninC0(pNode) ), 
                If_NotCond( (If_Obj_t *)Aig_ObjFanin1(pNode)->pData, Aig_ObjFaninC1(pNode) ) );
        else if ( Aig_ObjIsPi(pNode) )
        {
            pNode->pData = If_ManCreateCi( pIfMan );
            ((If_Obj_t *)pNode->pData)->Level = pNode->Level;
            if ( pIfMan->nLevelMax < (int)pNode->Level )
                pIfMan->nLevelMax = (int)pNode->Level;
        }
        else if ( Aig_ObjIsPo(pNode) )
            pNode->pData = If_ManCreateCo( pIfMan, If_NotCond( (If_Obj_t *)Aig_ObjFanin0(pNode)->pData, Aig_ObjFaninC0(pNode) ) );
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
        {
            If_Obj_t * pIfObj = (If_Obj_t *)pNode->pData;
            assert( !If_IsComplement(pIfObj) );
            assert( pIfObj->Id == pNode->Id );
        }
    }
    return pIfMan;
}

/**Function*************************************************************

  Synopsis    [Creates the mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_ManFromIf( Aig_Man_t * p, If_Man_t * pMan )
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
        pNode = (If_Obj_t *)pObj->pData;
        assert( pNode != NULL );
        Vec_IntWriteEntry( vIfToAig, pNode->Id, pObj->Id );
    }
    // create the mapping
    vIfMap   = If_ManCollectMappingDirect( pMan );
    nVarsMax = pMan->pPars->nLutSize;
    nWords   = Aig_TruthWordNum( nVarsMax );
    vMapping = Ntl_MappingAlloc( Vec_PtrSize(vIfMap) + (int)(Aig_ManConst1(p)->nRefs > 0), nVarsMax );
    nLuts    = 0;
    if ( Aig_ManConst1(p)->nRefs > 0 )
    {
        pLut = (Ntl_Lut_t *)Vec_PtrEntry( vMapping, nLuts++ );
        pLut->Id = 0;
        pLut->nFanins = 0;
        memset( pLut->pTruth, 0xFF, 4 * nWords );
    }
    Vec_PtrForEachEntry( If_Obj_t *, vIfMap, pNode, i )
    {
        // get the best cut
        pCutBest = If_ObjCutBest(pNode);
        nLeaves  = If_CutLeaveNum( pCutBest ); 
        ppLeaves = If_CutLeaves( pCutBest );
        // fill the LUT
        pLut = (Ntl_Lut_t *)Vec_PtrEntry( vMapping, nLuts++ );
        pLut->Id = Vec_IntEntry( vIfToAig, pNode->Id );
        pLut->nFanins = nLeaves;
        If_CutForEachLeaf( pMan, pCutBest, pLeaf, k )
            pLut->pFanins[k] = Vec_IntEntry( vIfToAig, pLeaf->Id );
        // compute the truth table
        memcpy( pLut->pTruth, If_CutTruth(pCutBest), 4 * nWords );
    }
    assert( nLuts == Vec_PtrSize(vMapping) );
    Vec_IntFree( vIfToAig );
    Vec_PtrFree( vIfMap );
    return vMapping;
}

/**Function*************************************************************

  Synopsis    [Interface with the FPGA mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_MappingIf( Ntl_Man_t * pMan, Aig_Man_t * p )
{
    Vec_Ptr_t * vMapping;
    If_Par_t Pars, * pPars = &Pars;
    If_Man_t * pIfMan;
    // perform FPGA mapping
    Ntl_ManSetIfParsDefault( pPars );
    // set the arrival times
    pPars->pTimesArr = ABC_ALLOC( float, Aig_ManPiNum(p) );
    memset( pPars->pTimesArr, 0, sizeof(float) * Aig_ManPiNum(p) );
    // translate into the mapper
    pIfMan = Ntl_ManToIf( p, pPars );    
    if ( pIfMan == NULL )
        return NULL;
    pIfMan->pManTim = Tim_ManDup( pMan->pManTime, 0 );
    if ( !If_ManPerformMapping( pIfMan ) )
    {
        If_ManStop( pIfMan );
        return NULL;
    }
    // transform the result of mapping into the new network
    vMapping = Ntl_ManFromIf( p, pIfMan );
    If_ManStop( pIfMan );
    if ( vMapping == NULL )
        return NULL;
    return vMapping;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

