/**CFile****************************************************************

  FileName    [ntlAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Netlist SOP to AIG conversion.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlAig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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
                pAnd = Aig_And( pMan, pAnd, pNet->pFunc );
            else if ( Value == '0' )
                pAnd = Aig_And( pMan, pAnd, Aig_Not(pNet->pFunc) );
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
Aig_Obj_t * Ntl_ManExtractAigNode( Ntl_Obj_t * pNode )
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
            pFFNode->pFunc = Ntl_ObjFanin(pNode, i)->pFunc;
        // perform strashing
        pFunc = Ntl_GraphToNetworkAig( pMan, pFForm );
        Dec_GraphFree( pFForm );
        return pFunc;
    }
    return Ntl_ConvertSopToAigInternal( pMan, pNode, pNode->pSop );
}




/**Function*************************************************************

  Synopsis    [Extracts AIG from the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManExtract( Ntl_Man_t * p )
{
    Ntl_Obj_t * pNode;
    Ntl_Net_t * pNet;
    int i;
    // check the DFS traversal
    if ( !Ntl_ManDfs( p ) )
        return 0;
    // start the AIG manager
    assert( p->pAig == NULL );
    p->pAig = Aig_ManStart( 10000 );
    // create the primary inputs
    Ntl_ManForEachCiNet( p, pNet, i )
        pNet->pFunc = Aig_ObjCreatePi( p->pAig );
    // convert internal nodes to AIGs
    Ntl_ManForEachNode( p, pNode, i )
        Ntl_ObjFanout0(pNode)->pFunc = Ntl_ManExtractAigNode( pNode );
    // create the primary outputs
    Ntl_ManForEachCoNet( p, pNet, i )
        Aig_ObjCreatePo( p->pAig, pNet->pFunc );
    // cleanup the AIG
    Aig_ManCleanup( p->pAig );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Inserts the given mapping into the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManInsert( Ntl_Man_t * p, Vec_Ptr_t * vMapping )
{
    char Buffer[100];
    Vec_Ptr_t * vCopies;
    Vec_Int_t * vCover;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pNode;
    Ntl_Net_t * pNet, * pNetCo;
    Ntl_Lut_t * pLut;
    int i, k, nDigits;
    // remove old nodes
    pRoot = Vec_PtrEntry( p->vModels, 0 );
    Ntl_ModelForEachNode( pRoot, pNode, i )
        Vec_PtrWriteEntry( pRoot->vObjs, pNode->Id, NULL );
    // start mapping of AIG nodes into their copies
    vCopies = Vec_PtrStart( Aig_ManObjNumMax(p->pAig) );
    Ntl_ManForEachCiNet( p, pNet, i )
        Vec_PtrWriteEntry( vCopies, pNet->pFunc->Id, pNet );
    // create a new node for each LUT
    vCover = Vec_IntAlloc( 1 << 16 );
    nDigits = Aig_Base10Log( Vec_PtrSize(vMapping) );
    Vec_PtrForEachEntry( vMapping, pLut, i )
    {
        pNode = Ntl_ModelCreateNode( pRoot, pLut->nFanins );
        pNode->pSop = Ntl_SopFromTruth( p, pLut->pTruth, pLut->nFanins, vCover );
        if ( !Kit_TruthIsConst0(pLut->pTruth, pLut->nFanins) && !Kit_TruthIsConst1(pLut->pTruth, pLut->nFanins) )
        {
            for ( k = 0; k < pLut->nFanins; k++ )
            {
                pNet = Vec_PtrEntry( vCopies, pLut->pFanins[k] );
                if ( pNet == NULL )
                {
                    printf( "Ntl_ManInsert(): Internal error: Net not found.\n" );
                    return 0;
                }
                Ntl_ObjSetFanin( pNode, pNet, k );
            }
        }
        sprintf( Buffer, "lut%0*d", nDigits, i );
        if ( (pNet = Ntl_ModelFindNet( pRoot, Buffer )) )
        {
            printf( "Ntl_ManInsert(): Internal error: Intermediate net name is not unique.\n" );
            return 0;
        }
        pNet = Ntl_ModelFindOrCreateNet( pRoot, Buffer );
        if ( !Ntl_ModelSetNetDriver( pNode, pNet ) )
        {
            printf( "Ntl_ManInsert(): Internal error: Net has more than one fanin.\n" );
            return 0;
        }
        Vec_PtrWriteEntry( vCopies, pLut->Id, pNet );
    }
    Vec_IntFree( vCover );
    // mark CIs and outputs of the registers
    Ntl_ManForEachCiNet( p, pNetCo, i )
        pNetCo->nVisits = 101;
    // update the CO pointers
    Ntl_ManForEachCoNet( p, pNetCo, i )
    {
        if ( pNetCo->nVisits == 101 )
            continue;
        pNetCo->nVisits = 101;
        pNet = Vec_PtrEntry( vCopies, Aig_Regular(pNetCo->pFunc)->Id );
        pNode = Ntl_ModelCreateNode( pRoot, 1 );
        pNode->pSop = Aig_IsComplement(pNetCo->pFunc)? Ntl_ManStoreSop( p, "0 1\n" ) : Ntl_ManStoreSop( p, "1 1\n" );
        Ntl_ObjSetFanin( pNode, pNet, 0 );
        // update the CO driver net
        pNetCo->pDriver = NULL;
        if ( !Ntl_ModelSetNetDriver( pNode, pNetCo ) )
        {
            printf( "Ntl_ManInsert(): Internal error: PO net has more than one fanin.\n" );
            return 0;
        }
    }
    Vec_PtrFree( vCopies );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Extracts AIG from the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManPerformSynthesis( Ntl_Man_t * p )
{
    extern Aig_Man_t * Dar_ManBalance( Aig_Man_t * p, int fUpdateLevel );
    extern Aig_Man_t * Dar_ManCompress( Aig_Man_t * pAig, int fBalance, int fUpdateLevel, int fVerbose );
    Aig_Man_t * pTemp;
    Ntl_Net_t * pNet;
    int i;
    // perform synthesis
printf( "Pre-synthesis AIG:  " );
Aig_ManPrintStats( p->pAig );
//    p->pAig = Dar_ManBalance( pTemp = p->pAig, 1 );
    p->pAig = Dar_ManCompress( pTemp = p->pAig, 1, 1, 0 );
    Ntl_ManForEachCiNet( p, pNet, i )
        pNet->pFunc = Aig_ManPi( p->pAig, i );
    Ntl_ManForEachCoNet( p, pNet, i )
        pNet->pFunc = Aig_ObjChild0( Aig_ManPo( p->pAig, i ) );
    Aig_ManStop( pTemp );
printf( "Post-synthesis AIG: " );
Aig_ManPrintStats( p->pAig );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Testing procedure for insertion of mapping into the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManInsertTest( Ntl_Man_t * p )
{
    Vec_Ptr_t * vMapping;
    int RetValue;
    if ( !Ntl_ManExtract( p ) )
        return 0;
    assert( p->pAig != NULL );
    Ntl_ManPerformSynthesis( p );
    vMapping = Ntl_MappingFromAig( p->pAig );
    RetValue = Ntl_ManInsert( p, vMapping );
    Vec_PtrFree( vMapping );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Testing procedure for insertion of mapping into the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManInsertTestIf( Ntl_Man_t * p )
{
    Vec_Ptr_t * vMapping;
    int RetValue;
    if ( !Ntl_ManExtract( p ) )
        return 0;
    assert( p->pAig != NULL );
    Ntl_ManPerformSynthesis( p );
    vMapping = Ntl_MappingIf( p->pAig );
    RetValue = Ntl_ManInsert( p, vMapping );
    Vec_PtrFree( vMapping );
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


