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

#define Ntl_SopForEachCube( pSop, nFanins, pCube )                \
    for ( pCube = (pSop); *pCube; pCube += (nFanins) + 3 )
#define Ntl_CubeForEachVar( pCube, Value, i )                     \
    for ( i = 0; (pCube[i] != ' ') && (Value = pCube[i]); i++ )           

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks if the cover is constant 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_SopIsConst0( char * pSop )
{
    return pSop[0] == ' ' && pSop[1] == '0';
}

/**Function*************************************************************

  Synopsis    [Reads the number of variables in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_SopGetVarNum( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur != '\n'; pCur++ );
    return pCur - pSop - 2;
}

/**Function*************************************************************

  Synopsis    [Reads the number of cubes in the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_SopGetCubeNum( char * pSop )
{
    char * pCur;
    int nCubes = 0;
    if ( pSop == NULL )
        return 0;
    for ( pCur = pSop; *pCur; pCur++ )
        nCubes += (*pCur == '\n');
    return nCubes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_SopIsComplement( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur; pCur++ )
        if ( *pCur == '\n' )
            return (int)(*(pCur - 1) == '0' || *(pCur - 1) == 'n');
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_SopComplement( char * pSop )
{
    char * pCur;
    for ( pCur = pSop; *pCur; pCur++ )
        if ( *pCur == '\n' )
        {
            if ( *(pCur - 1) == '0' )
                *(pCur - 1) = '1';
            else if ( *(pCur - 1) == '1' )
                *(pCur - 1) = '0';
            else if ( *(pCur - 1) == 'x' )
                *(pCur - 1) = 'n';
            else if ( *(pCur - 1) == 'n' )
                *(pCur - 1) = 'x';
            else
                assert( 0 );
        }
}

/**Function*************************************************************

  Synopsis    [Creates the constant 1 cover with the given number of variables and cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ntl_SopStart( Aig_MmFlex_t * pMan, int nCubes, int nVars )
{
    char * pSopCover, * pCube;
    int i, Length;

    Length = nCubes * (nVars + 3);
    pSopCover = Aig_MmFlexEntryFetch( pMan, Length + 1 );
    memset( pSopCover, '-', Length );
    pSopCover[Length] = 0;

    for ( i = 0; i < nCubes; i++ )
    {
        pCube = pSopCover + i * (nVars + 3);
        pCube[nVars + 0] = ' ';
        pCube[nVars + 1] = '1';
        pCube[nVars + 2] = '\n';
    }
    return pSopCover;
}

/**Function*************************************************************

  Synopsis    [Creates the cover from the ISOP computed from TT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ntl_SopCreateFromIsop( Aig_MmFlex_t * pMan, int nVars, Vec_Int_t * vCover )
{
    char * pSop, * pCube;
    int i, k, Entry, Literal;
    assert( Vec_IntSize(vCover) > 0 );
    if ( Vec_IntSize(vCover) == 0 )
        return NULL;
    // start the cover
    pSop = Ntl_SopStart( pMan, Vec_IntSize(vCover), nVars );
    // create cubes
    Vec_IntForEachEntry( vCover, Entry, i )
    {
        pCube = pSop + i * (nVars + 3);
        for ( k = 0; k < nVars; k++ )
        {
            Literal = 3 & (Entry >> (k << 1));
            if ( Literal == 1 )
                pCube[k] = '0';
            else if ( Literal == 2 )
                pCube[k] = '1';
            else if ( Literal != 0 )
                assert( 0 );
        }
    }
    return pSop;
}

/**Function*************************************************************

  Synopsis    [Transforms truth table into the SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ntl_SopFromTruth( Ntl_Man_t * p, unsigned * pTruth, int nVars, Vec_Int_t * vCover )
{
    char * pSop;
    int RetValue;
    if ( Kit_TruthIsConst0(pTruth, nVars) )
        return Ntl_ManStoreSop( p, " 0\n" );
    if ( Kit_TruthIsConst1(pTruth, nVars) )
        return Ntl_ManStoreSop( p, " 1\n" );
    RetValue = Kit_TruthIsop( pTruth, nVars, vCover, 0 ); // 1 );
    assert( RetValue == 0 || RetValue == 1 );
    pSop = Ntl_SopCreateFromIsop( p->pMemSops, nVars, vCover );
    if ( RetValue )
        Ntl_SopComplement( pSop );
    return pSop;
}



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
    nFanins = Ntl_SopGetVarNum(pSop);
    // go through the cubes of the node's SOP
    pSum = Aig_ManConst0(pMan);
    Ntl_SopForEachCube( pSop, nFanins, pCube )
    {
        // create the AND of literals
        pAnd = Aig_ManConst1(pMan);
        Ntl_CubeForEachVar( pCube, Value, i )
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
    if ( Ntl_SopIsComplement(pSop) )
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
    Dec_Node_t * pNode;
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
    int fUseFactor = 0;
    // consider the constant node
    if ( Ntl_SopGetVarNum(pNode->pSop) == 0 )
        return Aig_NotCond( Aig_ManConst1(pMan), Ntl_SopIsConst0(pNode->pSop) );
    // decide when to use factoring
    if ( fUseFactor && Ntl_SopGetVarNum(pNode->pSop) > 2 && Ntl_SopGetCubeNum(pNode->pSop) > 1 )
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
        int LevelCur, LevelMax = -AIG_INFINITY;
        Vec_IntPush( p->vBox1Cos, Aig_ManPoNum(p->pAig) );
        Ntl_ObjForEachFanin( pObj, pNetFanin, i )
        {
            LevelCur = Aig_ObjLevel( Aig_Regular(pNetFanin->pCopy) );
            LevelMax = AIG_MAX( LevelMax, LevelCur );
            Vec_PtrPush( p->vCos, pNetFanin );
            Aig_ObjCreatePo( p->pAig, pNetFanin->pCopy );
        }
        Ntl_ObjForEachFanout( pObj, pNetFanin, i )
        {
            Vec_PtrPush( p->vCis, pNetFanin );
            pNetFanin->pCopy = Aig_ObjCreatePi( p->pAig );
            Aig_ObjSetLevel( pNetFanin->pCopy, LevelMax + 1 );
        }
//printf( "Creating fake PO with ID = %d.\n", Aig_ManPo(p->pAig, Vec_IntEntryLast(p->vBox1Cos))->Id );
    }
    // store the node
    Vec_PtrPush( p->vNodes, pObj );
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
    int i, nUselessObjects;
    assert( Vec_PtrSize(p->vCis) == 0 );
    assert( Vec_PtrSize(p->vCos) == 0 );
    assert( Vec_PtrSize(p->vNodes) == 0 );
    assert( Vec_IntSize(p->vBox1Cos) == 0 );
    // start the AIG manager
    assert( p->pAig == NULL );
    p->pAig = Aig_ManStart( 10000 );
    p->pAig->pName = Aig_UtilStrsav( p->pName );
    p->pAig->pSpec = Aig_UtilStrsav( p->pSpec );
    // get the root model
    pRoot = Ntl_ManRootModel( p );
    // clear net visited flags
    Ntl_ModelForEachNet( pRoot, pNet, i )
        pNet->nVisits = 0;
    // collect primary inputs
    Ntl_ModelForEachPi( pRoot, pObj, i )
    {
        assert( Ntl_ObjFanoutNum(pObj) == 1 );
        pNet = Ntl_ObjFanout0(pObj);
        Vec_PtrPush( p->vCis, pNet );
        pNet->pCopy = Aig_ObjCreatePi( p->pAig );
        if ( pNet->nVisits )
        {
            printf( "Ntl_ManExtract(): Primary input appears twice in the list.\n" );
            return 0;
        }
        pNet->nVisits = 2;
    }
    // collect latch outputs
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        assert( Ntl_ObjFanoutNum(pObj) == 1 );
        pNet = Ntl_ObjFanout0(pObj);
        Vec_PtrPush( p->vCis, pNet );
        pNet->pCopy = Aig_ObjCreatePi( p->pAig );
        if ( pNet->nVisits )
        {
            printf( "Ntl_ManExtract(): Latch output is duplicated or defined as a primary input.\n" );
            return 0;
        }
        pNet->nVisits = 2;
    }
    // visit the nodes starting from primary outputs
    Ntl_ModelForEachPo( pRoot, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
        if ( !Ntl_ManExtract_rec( p, pNet ) )
        {
            printf( "Ntl_ManExtract(): Error: Combinational loop is detected.\n" );
            Vec_PtrClear( p->vCis );
            Vec_PtrClear( p->vCos );
            Vec_PtrClear( p->vNodes );
            return 0;
        }
        Vec_PtrPush( p->vCos, pNet );
        Aig_ObjCreatePo( p->pAig, pNet->pCopy );
    }
    // visit the nodes starting from latch inputs outputs
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
        if ( !Ntl_ManExtract_rec( p, pNet ) )
        {
            printf( "Ntl_ManExtract(): Error: Combinational loop is detected.\n" );
            Vec_PtrClear( p->vCis );
            Vec_PtrClear( p->vCos );
            Vec_PtrClear( p->vNodes );
            return 0;
        }
        Vec_PtrPush( p->vCos, pNet );
        Aig_ObjCreatePo( p->pAig, pNet->pCopy );
    }
    // report the number of dangling objects
    nUselessObjects = Ntl_ModelNodeNum(pRoot) + Ntl_ModelBoxNum(pRoot) - Vec_PtrSize(p->vNodes);
    if ( nUselessObjects )
        printf( "The number of nodes that do not feed into POs = %d.\n", nUselessObjects );
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
int Ntl_ManBuildModelAig( Ntl_Man_t * p, Ntl_Obj_t * pBox )
{
    extern int Ntl_ManCollapse_rec( Ntl_Man_t * p, Ntl_Net_t * pNet );
    Ntl_Mod_t * pModel = pBox->pImplem;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet, * pNetBox;
    int i;
    assert( Ntl_ObjFaninNum(pBox) == Ntl_ModelPiNum(pModel) );
    assert( Ntl_ObjFanoutNum(pBox) == Ntl_ModelPoNum(pModel) );
    // clear net visited flags
    Ntl_ModelForEachNet( pModel, pNet, i )
        pNet->nVisits = 0;
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
        if ( !Ntl_ManCollapse_rec( p, Ntl_ObjFanin0(pObj) ) )
            return 0;
    // transfer from the POs of the model to the box
    Ntl_ModelForEachPo( pModel, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
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
int Ntl_ManCollapse_rec( Ntl_Man_t * p, Ntl_Net_t * pNet )
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
        if ( !Ntl_ManCollapse_rec( p, pNetFanin ) )
            return 0;
    // add box inputs/outputs to COs/CIs
    if ( Ntl_ObjIsBox(pObj) )
    {
        if ( !Ntl_ManBuildModelAig( p, pObj ) )
            return 0;
    }
    // store the node
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
Aig_Man_t * Ntl_ManCollapse( Ntl_Man_t * p )
{
    Aig_Man_t * pAig;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i;
    // start the AIG manager
    assert( p->pAig == NULL );
    p->pAig = Aig_ManStart( 10000 );
    p->pAig->pName = Aig_UtilStrsav( p->pName );
    p->pAig->pSpec = Aig_UtilStrsav( p->pSpec );
    // get the root model
    pRoot = Ntl_ManRootModel( p );
    // clear net visited flags
    Ntl_ModelForEachNet( pRoot, pNet, i )
        pNet->nVisits = 0;
    // collect primary inputs
    Ntl_ModelForEachPi( pRoot, pObj, i )
    {
        assert( Ntl_ObjFanoutNum(pObj) == 1 );
        pNet = Ntl_ObjFanout0(pObj);
        pNet->pCopy = Aig_ObjCreatePi( p->pAig );
        if ( pNet->nVisits )
        {
            printf( "Ntl_ManCollapse(): Primary input appears twice in the list.\n" );
            return 0;
        }
        pNet->nVisits = 2;
    }
    // collect latch outputs
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        assert( Ntl_ObjFanoutNum(pObj) == 1 );
        pNet = Ntl_ObjFanout0(pObj);
        pNet->pCopy = Aig_ObjCreatePi( p->pAig );
        if ( pNet->nVisits )
        {
            printf( "Ntl_ManCollapse(): Latch output is duplicated or defined as a primary input.\n" );
            return 0;
        }
        pNet->nVisits = 2;
    }
    // visit the nodes starting from primary outputs
    Ntl_ModelForEachPo( pRoot, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
        if ( !Ntl_ManCollapse_rec( p, pNet ) )
        {
            printf( "Ntl_ManCollapse(): Error: Combinational loop is detected.\n" );
            return 0;
        }
        Aig_ObjCreatePo( p->pAig, pNet->pCopy );
    }
    // visit the nodes starting from latch inputs outputs
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        pNet = Ntl_ObjFanin0(pObj);
        if ( !Ntl_ManCollapse_rec( p, pNet ) )
        {
            printf( "Ntl_ManCollapse(): Error: Combinational loop is detected.\n" );
            return 0;
        }
        Aig_ObjCreatePo( p->pAig, pNet->pCopy );
    }
    // cleanup the AIG
    Aig_ManCleanup( p->pAig );
    pAig = p->pAig; p->pAig = NULL;
    return pAig;    
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


