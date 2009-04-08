/**CFile****************************************************************

  FileName    [ntlExtract.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Netlist SOP to AIG conversion.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlExtract.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"
#include "dec.h"
#include "kit.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Ntl_ConvertSopToAigInternal( Aig_Man_t * pMan, Ntl_Obj_t * pNode, char * pSop )
{
    Ntl_Net_t * pNet;
    Aig_Obj_t * pAnd, * pSum;
    int i, Value, nFanins;
    char * pCube;
    // get the number of variables
    nFanins = Kit_PlaGetVarNum(pSop);
    // go through the cubes of the node's SOP
    pSum = Aig_ManConst0(pMan);
    Kit_PlaForEachCube( pSop, nFanins, pCube )
    {
        // create the AND of literals
        pAnd = Aig_ManConst1(pMan);
        Kit_PlaCubeForEachVar( pCube, Value, i )
        {
            pNet = Ntl_ObjFanin( pNode, i );
            if ( Value == '1' )
                pAnd = Aig_And( pMan, pAnd, pNet->pCopy );
            else if ( Value == '0' )
                pAnd = Aig_And( pMan, pAnd, Aig_Not(pNet->pCopy) );
        }
        // add to the sum of cubes
        pSum = Aig_Or( pMan, pSum, pAnd );
    }
    // decide whether to complement the result
    if ( Kit_PlaIsComplement(pSop) )
        pSum = Aig_Not(pSum);
    return pSum;
}

/**Function*************************************************************

  Synopsis    [Transforms the decomposition graph into the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Ntl_GraphToNetworkAig( Aig_Man_t * pMan, Dec_Graph_t * pGraph )
{
    Dec_Node_t * pNode = NULL; // Suppress "might be used uninitialized"
    Aig_Obj_t * pAnd0, * pAnd1;
    int i;
    // check for constant function
    if ( Dec_GraphIsConst(pGraph) )
        return Aig_NotCond( Aig_ManConst1(pMan), Dec_GraphIsComplement(pGraph) );
    // check for a literal
    if ( Dec_GraphIsVar(pGraph) )
        return Aig_NotCond( Dec_GraphVar(pGraph)->pFunc, Dec_GraphIsComplement(pGraph) );
    // build the AIG nodes corresponding to the AND gates of the graph
    Dec_GraphForEachNode( pGraph, pNode, i )
    {
        pAnd0 = Aig_NotCond( Dec_GraphNode(pGraph, pNode->eEdge0.Node)->pFunc, pNode->eEdge0.fCompl ); 
        pAnd1 = Aig_NotCond( Dec_GraphNode(pGraph, pNode->eEdge1.Node)->pFunc, pNode->eEdge1.fCompl ); 
        pNode->pFunc = Aig_And( pMan, pAnd0, pAnd1 );
    }
    // complement the result if necessary
    return Aig_NotCond( pNode->pFunc, Dec_GraphIsComplement(pGraph) );
}

/**Function*************************************************************

  Synopsis    [Converts the network from AIG to BDD representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Ntl_ManBuildNodeAig( Ntl_Obj_t * pNode )
{
    Aig_Man_t * pMan = pNode->pModel->pMan->pAig;
    int fUseFactor = 1;
    // consider the constant node
    if ( Kit_PlaGetVarNum(pNode->pSop) == 0 )
        return Aig_NotCond( Aig_ManConst1(pMan), Kit_PlaIsConst0(pNode->pSop) );
    // decide when to use factoring
    if ( fUseFactor && Kit_PlaGetVarNum(pNode->pSop) > 2 && Kit_PlaGetCubeNum(pNode->pSop) > 1 )
    {
        Dec_Graph_t * pFForm;
        Dec_Node_t * pFFNode;
        Aig_Obj_t * pFunc;
        int i;
        // perform factoring
        pFForm = Dec_Factor( pNode->pSop );
        // collect the fanins
        Dec_GraphForEachLeaf( pFForm, pFFNode, i )
            pFFNode->pFunc = Ntl_ObjFanin(pNode, i)->pCopy;
        // perform strashing
        pFunc = Ntl_GraphToNetworkAig( pMan, pFForm );
        Dec_GraphFree( pFForm );
        return pFunc;
    }
    return Ntl_ConvertSopToAigInternal( pMan, pNode, pNode->pSop );
}

/**Function*************************************************************

  Synopsis    [Collects the nodes in a topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManExtract_rec( Ntl_Man_t * p, Ntl_Net_t * pNet )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNetFanin;
    int i;
    // skip visited
    if ( pNet->nVisits == 2 ) 
        return 1;
    // if the node is on the path, this is a combinational loop
    if ( pNet->nVisits == 1 )
        return 0; 
    // mark the node as the one on the path
    pNet->nVisits = 1;
    // derive the box
    pObj = pNet->pDriver;
    assert( Ntl_ObjIsNode(pObj) || Ntl_ObjIsBox(pObj) );
    // visit the input nets of the box
    Ntl_ObjForEachFanin( pObj, pNetFanin, i )
        if ( !Ntl_ManExtract_rec( p, pNetFanin ) )
            return 0;
    // add box inputs/outputs to COs/CIs
    if ( Ntl_ObjIsBox(pObj) ) 
    {
        int LevelCur, LevelMax = -TIM_ETERNITY;
        assert( Ntl_BoxIsComb(pObj) );
        assert( Ntl_ModelLatchNum(pObj->pImplem) == 0 );
        assert( pObj->pImplem->vDelays != NULL );
        Vec_IntPush( p->vBox1Cios, Aig_ManPoNum(p->pAig) );
        Ntl_ObjForEachFanin( pObj, pNetFanin, i )
        {
            LevelCur = Aig_ObjLevel( Aig_Regular(pNetFanin->pCopy) );
            LevelMax = ABC_MAX( LevelMax, LevelCur );
            Vec_PtrPush( p->vCos, pNetFanin );
            Aig_ObjCreatePo( p->pAig, pNetFanin->pCopy );
        }
        Ntl_ObjForEachFanout( pObj, pNetFanin, i )
        {
            Vec_PtrPush( p->vCis, pNetFanin );
            pNetFanin->pCopy = Aig_ObjCreatePi( p->pAig );
            Aig_ObjSetLevel( pNetFanin->pCopy, LevelMax + 1 );
        }
    }
    Vec_PtrPush( p->vVisNodes, pObj );
    if ( Ntl_ObjIsNode(pObj) )
        pNet->pCopy = Ntl_ManBuildNodeAig( pObj );
    pNet->nVisits = 2;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs DFS.]

  Description [Checks for combinational loops. Collects PI/PO nets.
  Collects nodes in the topological order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManExtract( Ntl_Man_t * p )
{
    Aig_Man_t * pAig;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i, k, nUselessObjects;
    Ntl_ManCleanup( p );
    Vec_PtrClear( p->vCis );
    Vec_PtrClear( p->vCos );
    Vec_PtrClear( p->vVisNodes );
    Vec_IntClear( p->vBox1Cios );
    // start the AIG manager
    assert( p->pAig == NULL );
    p->pAig = Aig_ManStart( 10000 );
    p->pAig->pName = Aig_UtilStrsav( p->pName );
    p->pAig->pSpec = Aig_UtilStrsav( p->pSpec );
    // get the root model
    pRoot = Ntl_ManRootModel( p );
    assert( Ntl_ModelLatchNum(pRoot) == 0 );
    // clear net visited flags
    Ntl_ModelClearNets( pRoot );
    // collect mapping leafs
    Ntl_ModelForEachMapLeaf( pRoot, pObj, i )
    {
        assert( !Ntl_ObjIsBox(pObj) || Ntl_BoxIsBlack(pObj) || Ntl_ModelLatchNum(pObj->pImplem) > 0 );
        Ntl_ObjForEachFanout( pObj, pNet, k )
        {
            Vec_PtrPush( p->vCis, pNet );
            pNet->pCopy = Aig_ObjCreatePi( p->pAig );
            if ( pNet->nVisits )
            {
                printf( "Ntl_ManExtract(): Seq leaf is duplicated or defined as a primary input.\n" );
                return 0;
            }
            pNet->nVisits = 2;
        }
    }
    p->iLastCi = Aig_ManPiNum(p->pAig);
    // collect mapping roots
    Ntl_ModelForEachMapRoot( pRoot, pObj, i )
    {
        Ntl_ObjForEachFanin( pObj, pNet, k )
        {
            if ( !Ntl_ManExtract_rec( p, pNet ) )
            {
                printf( "Ntl_ManExtract(): Error: Combinational loop is detected.\n" );
                return 0;
            }
            Vec_PtrPush( p->vCos, pNet );
            Aig_ObjCreatePo( p->pAig, pNet->pCopy );
        }
    }
    // visit dangling boxes
    Ntl_ModelForEachBox( pRoot, pObj, i )
    {
        pNet = Ntl_ObjFanout0(pObj);
        if ( !Ntl_ManExtract_rec( p, pNet ) )
        {
            printf( "Ntl_ManExtract(): Error: Combinational loop is detected.\n" );
            return 0;
        }
    }
    // report the number of dangling objects
    nUselessObjects = Ntl_ModelNodeNum(pRoot) + Ntl_ModelLut1Num(pRoot) + Ntl_ModelBoxNum(pRoot) - Vec_PtrSize(p->vVisNodes);
//    if ( nUselessObjects )
//        printf( "The number of dangling objects = %d.\n", nUselessObjects );
    // cleanup the AIG
    Aig_ManCleanup( p->pAig );
    // extract the timing manager
    assert( p->pManTime == NULL );
    p->pManTime = Ntl_ManCreateTiming( p );
    // discretize timing info
    p->pAig->pManTime = Tim_ManDup( p->pManTime, 1 );
    pAig = p->pAig; p->pAig = NULL;
    return pAig;    
}




/**Function*************************************************************

  Synopsis    [Collects the nodes in a topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCollapseBoxComb_rec( Ntl_Man_t * p, Ntl_Obj_t * pBox, int fSeq )
{
    extern int Ntl_ManCollapse_rec( Ntl_Man_t * p, Ntl_Net_t * pNet, int fSeq );
    Ntl_Mod_t * pModel = pBox->pImplem;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet, * pNetBox;
    int i;
    assert( Ntl_ObjFaninNum(pBox) == Ntl_ModelPiNum(pModel) );
    assert( Ntl_ObjFanoutNum(pBox) == Ntl_ModelPoNum(pModel) );
    // clear net visited flags
    Ntl_ModelClearNets( pModel );
    // transfer from the box to the PIs of the model
    Ntl_ModelForEachPi( pModel, pObj, i )
    {
        pNet = Ntl_ObjFanout0(pObj);
        pNetBox = Ntl_ObjFanin( pBox, i );
        pNet->pCopy = pNetBox->pCopy;
        pNet->nVisits = 2;
    }
    // compute AIG for the internal nodes
    Ntl_ModelForEachPo( pModel, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
        if ( !Ntl_ManCollapse_rec( p, pNet, fSeq ) )
            return 0;
        pNetBox = Ntl_ObjFanout( pBox, i );
        pNetBox->pCopy = pNet->pCopy;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collects the nodes in a topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCollapseBoxSeq1_rec( Ntl_Man_t * p, Ntl_Obj_t * pBox, int fSeq )
{
    extern int Ntl_ManCollapse_rec( Ntl_Man_t * p, Ntl_Net_t * pNet, int fSeq );
    Ntl_Mod_t * pModel = pBox->pImplem;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet, * pNetBox;
    int i;
    assert( Ntl_ModelLatchNum(pModel) > 0 );
    assert( Ntl_ObjFaninNum(pBox) == Ntl_ModelPiNum(pModel) );
    assert( Ntl_ObjFanoutNum(pBox) == Ntl_ModelPoNum(pModel) );
    // clear net visited flags
    Ntl_ModelClearNets( pModel );
    // initialize the registers
    Ntl_ModelForEachLatch( pModel, pObj, i )
    {
        pNet = Ntl_ObjFanout0(pObj);
        pNet->pCopy = Aig_ObjCreatePi( p->pAig );
        if ( fSeq && Ntl_ObjIsInit1( pObj ) )
            pNet->pCopy = Aig_Not(pNet->pCopy);
        pNet->nVisits = 2;
        // remember the class of this register
        Vec_IntPush( p->vRegClasses, p->pNal ? pBox->iTemp : pObj->LatchId.regClass );
    }
    // compute AIG for the internal nodes
    Ntl_ModelForEachPo( pModel, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
        if ( !Ntl_ManCollapse_rec( p, pNet, fSeq ) )
            return 0;
        pNetBox = Ntl_ObjFanout( pBox, i );
        pNetBox->pCopy = pNet->pCopy;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collects the nodes in a topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCollapseBoxSeq2_rec( Ntl_Man_t * p, Ntl_Obj_t * pBox, int fSeq, int iFirstPi )
{
    extern int Ntl_ManCollapse_rec( Ntl_Man_t * p, Ntl_Net_t * pNet, int fSeq );
    Ntl_Mod_t * pModel = pBox->pImplem;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet, * pNetBox;
    int i;
    assert( Ntl_ModelLatchNum(pModel) > 0 );
    assert( Ntl_ObjFaninNum(pBox) == Ntl_ModelPiNum(pModel) );
    assert( Ntl_ObjFanoutNum(pBox) == Ntl_ModelPoNum(pModel) );
    // clear net visited flags
    Ntl_ModelClearNets( pModel );
    // transfer from the box to the PIs of the model
    Ntl_ModelForEachPi( pModel, pObj, i )
    {
        pNet = Ntl_ObjFanout0(pObj);
        pNetBox = Ntl_ObjFanin( pBox, i );
        pNet->pCopy = pNetBox->pCopy;
        pNet->nVisits = 2;
    }
    // initialize the registers
    Ntl_ModelForEachLatch( pModel, pObj, i )
    {
        pNet = Ntl_ObjFanout0(pObj);
        pNet->pCopy = Aig_ManPi( p->pAig, iFirstPi++ );
        if ( fSeq && Ntl_ObjIsInit1( pObj ) )
            pNet->pCopy = Aig_Not(pNet->pCopy);
        pNet->nVisits = 2;
    }
    // compute AIGs for the registers
    Ntl_ModelForEachLatch( pModel, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
        if ( !Ntl_ManCollapse_rec( p, pNet, fSeq ) )
            return 0;
        if ( fSeq && Ntl_ObjIsInit1( pObj ) )
            Aig_ObjCreatePo( p->pAig, Aig_Not(pNet->pCopy) );
        else
            Aig_ObjCreatePo( p->pAig, pNet->pCopy );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collects the nodes in a topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCollapse_rec( Ntl_Man_t * p, Ntl_Net_t * pNet, int fSeq )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNetFanin;
    int i;
    // skip visited
    if ( pNet->nVisits == 2 ) 
        return 1;
    // if the node is on the path, this is a combinational loop
    if ( pNet->nVisits == 1 )
        return 0; 
    // mark the node as the one on the path
    pNet->nVisits = 1;
    // derive the box
    pObj = pNet->pDriver;
    assert( Ntl_ObjIsNode(pObj) || Ntl_ObjIsBox(pObj) );
    // visit the input nets of the box
    Ntl_ObjForEachFanin( pObj, pNetFanin, i )
        if ( !Ntl_ManCollapse_rec( p, pNetFanin, fSeq ) )
            return 0;
    // add box inputs/outputs to COs/CIs
    if ( Ntl_ObjIsBox(pObj) )
    {
        assert( Ntl_BoxIsWhite(pObj) && Ntl_BoxIsComb(pObj) );
        if ( !Ntl_ManCollapseBoxComb_rec( p, pObj, fSeq ) )
            return 0;
    }
    if ( Ntl_ObjIsNode(pObj) )
        pNet->pCopy = Ntl_ManBuildNodeAig( pObj );
    pNet->nVisits = 2;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs DFS.]

  Description [Checks for combinational loops. Collects PI/PO nets.
  Collects nodes in the topological order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManCollapse( Ntl_Man_t * p, int fSeq )
{
    Aig_Man_t * pAig;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pBox;
    Ntl_Net_t * pNet;
    int i, k, nTruePis, nTruePos, iBox = 0;
    assert( Vec_PtrSize(p->vCis) != 0 );
    assert( Vec_PtrSize(p->vCos) != 0 );
    Vec_IntClear( p->vBox1Cios );
    Vec_IntClear( p->vRegClasses );
    // clear net visited flags
    pRoot = Ntl_ManRootModel(p);
    assert( Ntl_ModelLatchNum(pRoot) == 0 );
    Ntl_ModelClearNets( pRoot );
    // create the manager
    p->pAig = Aig_ManStart( 10000 );
    p->pAig->pName = Aig_UtilStrsav( p->pName );
    p->pAig->pSpec = Aig_UtilStrsav( p->pSpec );
    // set the inputs
    Ntl_ManForEachCiNet( p, pNet, i )
    {
        pNet->pCopy = Aig_ObjCreatePi( p->pAig );
        if ( pNet->nVisits )
        {
            printf( "Ntl_ManCollapse(): Primary input appears twice in the list.\n" );
            return 0;
        }
        pNet->nVisits = 2;
    }
    nTruePis = Aig_ManPiNum(p->pAig);
    // create inputs of seq boxes
    if ( fSeq ) {
      Ntl_ModelForEachBox( pRoot, pBox, i )
      {
          if ( !(Ntl_BoxIsSeq(pBox) && Ntl_BoxIsWhite(pBox)) )
              continue;
          Vec_IntPush( p->vBox1Cios, Aig_ManPiNum(p->pAig) );
          Ntl_ManCollapseBoxSeq1_rec( p, pBox, fSeq );
          Ntl_ObjForEachFanout( pBox, pNet, k )
              pNet->nVisits = 2;
      }
    }
    // derive the outputs
    Ntl_ManForEachCoNet( p, pNet, i )
    {
        if ( !Ntl_ManCollapse_rec( p, pNet, fSeq ) )
        {
            printf( "Ntl_ManCollapse(): Error: Combinational loop is detected.\n" );
            return 0;
        }
        Aig_ObjCreatePo( p->pAig, pNet->pCopy );
    }
    nTruePos = Aig_ManPoNum(p->pAig);
    // create outputs of seq boxes
    if ( fSeq ) {
      Ntl_ModelForEachBox( pRoot, pBox, i )
      {
          if ( !(Ntl_BoxIsSeq(pBox) && Ntl_BoxIsWhite(pBox)) )
              continue;
          Ntl_ObjForEachFanin( pBox, pNet, k )
              if ( !Ntl_ManCollapse_rec( p, pNet, fSeq ) )
              {
                  printf( "Ntl_ManCollapse(): Error: Combinational loop is detected.\n" );
                  return 0;
              }
          Ntl_ManCollapseBoxSeq2_rec( p, pBox, fSeq, Vec_IntEntry(p->vBox1Cios, iBox++) );
      }
    }
    // make sure registers are added correctly
    if ( Aig_ManPiNum(p->pAig) - nTruePis != Aig_ManPoNum(p->pAig) - nTruePos )
    {
        printf( "Ntl_ManCollapse(): Error: Registers are created incorrectly.\n" );
        return 0;
    }
    // cleanup the AIG
    Aig_ManSetRegNum( p->pAig, Aig_ManPiNum(p->pAig) - nTruePis );
    Aig_ManCleanup( p->pAig );
    pAig = p->pAig; p->pAig = NULL;
    return pAig;    
}


/**Function*************************************************************

  Synopsis    [Collapses the netlist combinationally.]

  Description [Checks for combinational loops. Collects PI/PO nets.
  Collects nodes in the topological order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManCollapseComb( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i, k;
    Vec_PtrClear( p->vCis );
    Vec_PtrClear( p->vCos );
    // prepare the model
    pRoot = Ntl_ManRootModel(p);
    // collect the leaves for this traversal
    Ntl_ModelForEachCombLeaf( pRoot, pObj, i )
        Ntl_ObjForEachFanout( pObj, pNet, k )
            Vec_PtrPush( p->vCis, pNet );
    // collect the roots for this traversal
    Ntl_ModelForEachCombRoot( pRoot, pObj, i )
        Ntl_ObjForEachFanin( pObj, pNet, k )
            Vec_PtrPush( p->vCos, pNet );
    // perform the traversal
    return Ntl_ManCollapse( p, 0 );
}

/**Function*************************************************************

  Synopsis    [Collapses the netlist combinationally.]

  Description [Checks for combinational loops. Collects PI/PO nets.
  Collects nodes in the topological order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManCollapseSeq( Ntl_Man_t * p, int nMinDomSize )
{
    Aig_Man_t * pAig;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i, k;
    Vec_PtrClear( p->vCis );
    Vec_PtrClear( p->vCos );
    // prepare the model
    pRoot = Ntl_ManRootModel(p);
    // collect the leaves for this traversal
    Ntl_ModelForEachSeqLeaf( pRoot, pObj, i )
        Ntl_ObjForEachFanout( pObj, pNet, k )
            Vec_PtrPush( p->vCis, pNet );
    // collect the roots for this traversal
    Ntl_ModelForEachSeqRoot( pRoot, pObj, i )
        Ntl_ObjForEachFanin( pObj, pNet, k )
            Vec_PtrPush( p->vCos, pNet );
    // perform the traversal
    pAig = Ntl_ManCollapse( p, 1 );
    // check if there are register classes
    pAig->vClockDoms = Ntl_ManTransformRegClasses( p, nMinDomSize, 1 );
    if ( pAig->vClockDoms )
    {
        if ( Vec_VecSize(pAig->vClockDoms) == 0 )
        {
            printf( "Register classes are below the limit (%d). Seq synthesis is not performed.\n", nMinDomSize );
            Aig_ManStop( pAig );
            pAig = NULL;
        }
        else
            printf( "Performing seq synthesis for %d register classes.\n", Vec_VecSize(pAig->vClockDoms) );
        printf( "\n" );
    }
    return pAig;
}



/**Function*************************************************************

  Synopsis    [Increments reference counter of the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Ntl_NetIncrementRefs( Ntl_Net_t * pNet )
{
    int nRefs = (int)(long)pNet->pCopy;
    pNet->pCopy = (void *)(long)(nRefs + 1);
}

/**Function*************************************************************

  Synopsis    [Extracts logic newtork out of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nwk_Obj_t * Ntl_ManExtractNwk_rec( Ntl_Man_t * p, Ntl_Net_t * pNet, Nwk_Man_t * pNtk, Vec_Int_t * vCover, Vec_Int_t * vMemory )
{
    extern Hop_Obj_t * Kit_CoverToHop( Hop_Man_t * pMan, Vec_Int_t * vCover, int nVars, Vec_Int_t * vMemory );
    Ntl_Net_t * pFaninNet;
    Nwk_Obj_t * pNode;
    int i;
    if ( pNet->fMark )
        return pNet->pCopy2;
    pNet->fMark = 1;
    pNode = Nwk_ManCreateNode( pNtk, Ntl_ObjFaninNum(pNet->pDriver), (int)(long)pNet->pCopy );
    Ntl_ObjForEachFanin( pNet->pDriver, pFaninNet, i )
    {
        Ntl_ManExtractNwk_rec( p, pFaninNet, pNtk, vCover, vMemory );
        Nwk_ObjAddFanin( pNode, pFaninNet->pCopy2 );
    }
    if ( Ntl_ObjFaninNum(pNet->pDriver) == 0 )
        pNode->pFunc = Hop_NotCond( Hop_ManConst1(pNtk->pManHop), Kit_PlaIsConst0(pNet->pDriver->pSop) );
    else
    {
        Kit_PlaToIsop( pNet->pDriver->pSop, vCover );
        pNode->pFunc = Kit_CoverToHop( pNtk->pManHop, vCover, Ntl_ObjFaninNum(pNet->pDriver), vMemory );
        if ( Kit_PlaIsComplement(pNet->pDriver->pSop) )
            pNode->pFunc = Hop_Not(pNode->pFunc);
    }
    return pNet->pCopy2 = pNode;
}

/**Function*************************************************************

  Synopsis    [Extracts logic network out of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nwk_Man_t * Ntl_ManExtractNwk( Ntl_Man_t * p, Aig_Man_t * pAig, Tim_Man_t * pManTime )
{
    Nwk_Man_t * pNtk;
    Nwk_Obj_t * pNode;
    Ntl_Mod_t * pRoot;
    Ntl_Net_t * pNet, * pNetSimple;
    Ntl_Obj_t * pObj;
    Aig_Obj_t * pAnd;
    Vec_Int_t * vCover, * vMemory;
    int i, k;
    pRoot = Ntl_ManRootModel( p );
    if ( Ntl_ModelGetFaninMax(pRoot) > 6 )
    {
        printf( "The network contains logic nodes with more than 6 inputs.\n" );
        return NULL;
    }
    vCover = Vec_IntAlloc( 100 );
    vMemory = Vec_IntAlloc( 1 << 16 );
    // count the number of fanouts of each net
    Ntl_ModelClearNets( pRoot );
    Ntl_ModelForEachObj( pRoot, pObj, i )
        Ntl_ObjForEachFanin( pObj, pNet, k )
            Ntl_NetIncrementRefs( pNet );
    // remember netlist objects int the AIG nodes
    if ( pManTime != NULL ) // logic netlist
    {
        assert( Ntl_ModelPiNum(pRoot) == Aig_ManPiNum(pAig) );
        assert( Ntl_ModelPoNum(pRoot) == Aig_ManPoNum(pAig) );
        Aig_ManForEachPi( pAig, pAnd, i )
            pAnd->pData = Ntl_ObjFanout0( Ntl_ModelPi(pRoot, i) );
        Aig_ManForEachPo( pAig, pAnd, i )
            pAnd->pData = Ntl_ObjFanin0(Ntl_ModelPo(pRoot, i) );
    }
    else // real netlist
    {
        assert( p->vCis && p->vCos );
        Aig_ManForEachPi( pAig, pAnd, i )
            pAnd->pData = Vec_PtrEntry( p->vCis, i );
        Aig_ManForEachPo( pAig, pAnd, i )
            pAnd->pData = Vec_PtrEntry( p->vCos, i );
    }
    // construct the network
    pNtk = Nwk_ManAlloc();
    pNtk->pName = Aig_UtilStrsav( pAig->pName );
    pNtk->pSpec = Aig_UtilStrsav( pAig->pSpec );
    Aig_ManForEachObj( pAig, pAnd, i )
    {
        if ( Aig_ObjIsPi(pAnd) )
        {
            pNet = pAnd->pData;
            pNet->fMark = 1;
            pNet->pCopy2 = Nwk_ManCreateCi( pNtk, (int)(long)pNet->pCopy ); 
        }
        else if ( Aig_ObjIsPo(pAnd) )
        {
            pNet = pAnd->pData;
            pNode = Nwk_ManCreateCo( pNtk );
            if ( (pNetSimple = Ntl_ModelFindSimpleNet( pNet )) )
            {
                pNetSimple->pCopy2 = Ntl_ManExtractNwk_rec( p, pNetSimple, pNtk, vCover, vMemory ); 
                Nwk_ObjAddFanin( pNode, pNetSimple->pCopy2 );
                pNode->fInvert = Kit_PlaIsInv( pNet->pDriver->pSop );
            }
            else
            {
                pNet->pCopy2 = Ntl_ManExtractNwk_rec( p, pNet, pNtk, vCover, vMemory ); 
                Nwk_ObjAddFanin( pNode, pNet->pCopy2 );
            }
        }
    }
    Ntl_ModelClearNets( pRoot );
    Vec_IntFree( vCover );
    Vec_IntFree( vMemory );
    // create timing manager from the current design
    if ( pManTime )
        pNtk->pManTime = Tim_ManDup( pManTime, 0 );
    else
        pNtk->pManTime = Tim_ManDup( p->pManTime, 0 );
    Nwk_ManRemoveDupFanins( pNtk, 0 );
    assert( Nwk_ManCheck( pNtk ) );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Extracts logic newtork out of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nwk_Man_t * Ntl_ManReadNwk( char * pFileName, Aig_Man_t * pAig, Tim_Man_t * pManTime )
{
    Nwk_Man_t * pNtk;
    Ntl_Man_t * pNtl;
    Ntl_Mod_t * pRoot;
    pNtl = Ioa_ReadBlif( pFileName, 1 );
    if ( pNtl == NULL )
    {
        printf( "Ntl_ManReadNwk(): Reading BLIF has failed.\n" );
        return NULL;
    }
    pRoot = Ntl_ManRootModel( pNtl );
    if ( Ntl_ModelLatchNum(pRoot) != 0 )
    {
        printf( "Ntl_ManReadNwk(): The input network has %d registers.\n", Ntl_ModelLatchNum(pRoot) );
        return NULL;
    }
    if ( Ntl_ModelBoxNum(pRoot) != 0 )
    {
        printf( "Ntl_ManReadNwk(): The input network has %d boxes.\n", Ntl_ModelBoxNum(pRoot) );
        return NULL;
    }
    if ( Ntl_ModelPiNum(pRoot) != Aig_ManPiNum(pAig) )
    {
        printf( "Ntl_ManReadNwk(): The number of primary inputs does not match (%d and %d).\n",
            Ntl_ModelPiNum(pRoot), Aig_ManPiNum(pAig) );
        return NULL;
    }
    if ( Ntl_ModelPoNum(pRoot) != Aig_ManPoNum(pAig) )
    {
        printf( "Ntl_ManReadNwk(): The number of primary outputs does not match (%d and %d).\n",
            Ntl_ModelPoNum(pRoot), Aig_ManPoNum(pAig) );
        return NULL;
    }
    pNtk = Ntl_ManExtractNwk( pNtl, pAig, pManTime );
    Ntl_ManFree( pNtl );
    return pNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


