/**CFile****************************************************************

  FileName    [abcUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "main.h"
#include "mio.h"
#include "dec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_NodeRefDeref( Abc_Obj_t * pNode, bool fFanouts, bool fReference );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Increments the current traversal ID of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkIncrementTravId( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;
    if ( pNtk->nTravIds == (1<<12)-1 )
    {
        pNtk->nTravIds = 0;
        Abc_NtkForEachObj( pNtk, pObj, i )
            pObj->TravId = 0;
    }
    pNtk->nTravIds++;
}

/**Function*************************************************************

  Synopsis    [Reads the number of cubes of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetCubeNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, nCubes = 0;
    assert( Abc_NtkHasSop(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        assert( pNode->pData );
        nCubes += Abc_SopGetCubeNum( pNode->pData );
    }
    return nCubes;
}

/**Function*************************************************************

  Synopsis    [Reads the number of cubes of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetLitNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, nLits = 0;
    assert( Abc_NtkHasSop(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        assert( pNode->pData );
        nLits += Abc_SopGetLitNum( pNode->pData );
    }
    return nLits;
}

/**Function*************************************************************

  Synopsis    [Counts the number of literals in the factored forms.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetLitFactNum( Abc_Ntk_t * pNtk )
{
    Dec_Graph_t * pFactor;
    Abc_Obj_t * pNode;
    int nNodes, i;
    assert( Abc_NtkHasSop(pNtk) );
    nNodes = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_NodeIsConst(pNode) )
            continue;
        pFactor = Dec_Factor( pNode->pData );
        nNodes += 1 + Dec_GraphNodeNum(pFactor);
        Dec_GraphFree( pFactor );
    }
    return nNodes;
}

/**Function*************************************************************

  Synopsis    [Reads the number of BDD nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetBddNodeNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, nNodes = 0;
    assert( Abc_NtkIsBddLogic(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        assert( pNode->pData );
        nNodes += pNode->pData? Cudd_DagSize( pNode->pData ) : 0;
    }
    return nNodes;
}

/**Function*************************************************************

  Synopsis    [Reads the number of BDD nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetClauseNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    DdNode * bCover, * zCover, * bFunc;
    DdManager * dd = pNtk->pManFunc;
    int i, nClauses = 0;
    assert( Abc_NtkIsBddLogic(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        assert( pNode->pData );
        bFunc = pNode->pData;

        bCover = Cudd_zddIsop( dd, bFunc, bFunc, &zCover );  
        Cudd_Ref( bCover );
        Cudd_Ref( zCover );
        nClauses += Abc_CountZddCubes( dd, zCover );
        Cudd_RecursiveDeref( dd, bCover );
        Cudd_RecursiveDerefZdd( dd, zCover );

        bCover = Cudd_zddIsop( dd, Cudd_Not(bFunc), Cudd_Not(bFunc), &zCover );  
        Cudd_Ref( bCover );
        Cudd_Ref( zCover );
        nClauses += Abc_CountZddCubes( dd, zCover );
        Cudd_RecursiveDeref( dd, bCover );
        Cudd_RecursiveDerefZdd( dd, zCover );
    }
    return nClauses;
}

/**Function*************************************************************

  Synopsis    [Computes the area of the mapped circuit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
double Abc_NtkGetMappedArea( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    double TotalArea;
    int i;
    assert( Abc_NtkHasMapping(pNtk) );
    TotalArea = 0.0;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        assert( pNode->pData );
        TotalArea += Mio_GateReadArea( pNode->pData );
    }
    return TotalArea;
}

/**Function*************************************************************

  Synopsis    [Counts the number of exors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetExorNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, Counter = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
        Counter += pNode->fExor;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if it is an AIG with choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetChoiceNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, Counter;
    if ( !Abc_NtkIsStrash(pNtk) )
        return 0;
    Counter = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
        Counter += Abc_NodeIsAigChoice( pNode );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Reads the maximum number of fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkGetFaninMax( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, nFaninsMax = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( nFaninsMax < Abc_ObjFaninNum(pNode) )
            nFaninsMax = Abc_ObjFaninNum(pNode);
    }
    return nFaninsMax;
}

/**Function*************************************************************

  Synopsis    [Cleans the copy field of all objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCleanCopy( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;
    i = 0;
    // set the data filed to NULL
    Abc_NtkForEachObj( pNtk, pObj, i )
        pObj->pCopy = NULL;
}

/**Function*************************************************************

  Synopsis    [Checks if the internal node has a unique CO.]

  Description [Checks if the internal node can borrow a name from a CO
  fanout. This is possible if there is only one CO with non-complemented
  fanin edge pointing to this node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeHasUniqueCoFanout( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout, * pFanoutCo;
    int i, Counter;
    if ( !Abc_ObjIsNode(pNode) )
        return NULL;
    Counter = 0;
    Abc_ObjForEachFanout( pNode, pFanout, i )
    {
        if ( Abc_ObjIsCo(pFanout) && !Abc_ObjFaninC0(pFanout) )
        {
            assert( Abc_ObjFaninNum(pFanout) == 1 );
            assert( Abc_ObjFanin0(pFanout) == pNode );
            pFanoutCo = pFanout;
            Counter++;
        }
    }
    if ( Counter == 1 )
        return pFanoutCo;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if COs of a logic network are simple.]

  Description [The COs of a logic network are simple under three conditions:
  (1) The edge from CO to its driver is not complemented.
  (2) No two COs share the same driver. 
  (3) The driver is not a CI unless the CI and the CO have the same name 
  (and so the inv/buf should not be written into a file).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkLogicHasSimpleCos( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode, * pDriver;
    int i;
    assert( !Abc_NtkIsNetlist(pNtk) );
    // check if there are complemented or idential POs
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkForEachCo( pNtk, pNode, i ) 
    {
        pDriver = Abc_ObjFanin0(pNode);
        if ( Abc_ObjFaninC0(pNode) )
            return 0;
        if ( Abc_NodeIsTravIdCurrent(pDriver) )
            return 0;
        if ( Abc_ObjIsCi(pDriver) && strcmp( Abc_ObjName(pDriver), Abc_ObjName(pNode) ) != 0 )
            return 0;
        Abc_NodeSetTravIdCurrent(pDriver);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Transforms the network to have simple COs.]

  Description [The COs of a logic network are simple under three conditions:
  (1) The edge from the CO to its driver is not complemented.
  (2) No two COs share the same driver. 
  (3) The driver is not a CI unless the CI and the CO have the same name 
  (and so the inv/buf should not be written into a file).
  In some cases, such as FPGA mapping, we prevent the increase in delay
  by duplicating the driver nodes, rather than adding invs/bufs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkLogicMakeSimpleCos( Abc_Ntk_t * pNtk, bool fDuplicate )
{
    Abc_Obj_t * pNode, * pDriver, * pDriverNew, * pFanin;
    int i, k, nDupGates = 0;
    assert( Abc_NtkIsLogic(pNtk) );
    // process the COs by adding inverters and buffers when necessary
    Abc_NtkForEachCo( pNtk, pNode, i ) 
    {
        pDriver = Abc_ObjFanin0(pNode);
        if ( Abc_ObjIsCi(pDriver) )
        {
            // skip the case when the driver is a different node with the same name
            if ( pDriver != pNode && strcmp(Abc_ObjName(pDriver), Abc_ObjName(pNode)) == 0 )
            {
                assert( !Abc_ObjFaninC0(pNode) );
                continue;
            }
        }
        else
        {
            // skip the case when the driver's unique CO fanout is this CO
            if ( Abc_NodeHasUniqueCoFanout(pDriver) == pNode )
                continue;
        }
        if ( fDuplicate && !Abc_ObjIsCi(pDriver) )
        {
            pDriverNew = Abc_NtkDupObj( pNtk, pDriver ); 
            Abc_ObjForEachFanin( pDriver, pFanin, k )
                Abc_ObjAddFanin( pDriverNew, pFanin );
            if ( Abc_ObjFaninC0(pNode) )
            {
                // change polarity of the duplicated driver
                if ( Abc_NtkHasSop(pNtk) )
                    Abc_SopComplement( pDriverNew->pData );
                else if ( Abc_NtkHasBdd(pNtk) )
                    pDriverNew->pData = Cudd_Not( pDriverNew->pData );
                else
                    assert( 0 );
                Abc_ObjXorFaninC(pNode, 0);
            }
        }
        else
        {
            // add inverters and buffers when necessary
            if ( Abc_ObjFaninC0(pNode) )
            {
                pDriverNew = Abc_NodeCreateInv( pNtk, pDriver );
                Abc_ObjXorFaninC( pNode, 0 );
            }
            else
                pDriverNew = Abc_NodeCreateBuf( pNtk, pDriver );        
        }
        // update the fanin of the PO node
        Abc_ObjPatchFanin( pNode, pDriver, pDriverNew );
        assert( Abc_ObjFanoutNum(pDriverNew) == 1 );
        nDupGates++;
        // remove the old driver if it dangles
        if ( Abc_ObjFanoutNum(pDriver) == 0 )
            Abc_NtkDeleteObj( pDriver );
    }
    assert( Abc_NtkLogicHasSimpleCos(pNtk) );
    return nDupGates;
}

/**Function*************************************************************

  Synopsis    [Inserts a new node in the order by levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_VecObjPushUniqueOrderByLevel( Vec_Ptr_t * p, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pNode1, * pNode2;
    int i;
    if ( Vec_PtrPushUnique(p, pNode) )
        return;
    // find the p of the node
    for ( i = p->nSize-1; i > 0; i-- )
    {
        pNode1 = p->pArray[i  ];
        pNode2 = p->pArray[i-1];
        if ( Abc_ObjRegular(pNode1)->Level <= Abc_ObjRegular(pNode2)->Level )
            break;
        p->pArray[i  ] = pNode2;
        p->pArray[i-1] = pNode1;
    }
}



/**Function*************************************************************

  Synopsis    [Returns 1 if the node is the root of EXOR/NEXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsExorType( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pNode0, * pNode1;
    // check that the node is regular
    assert( !Abc_ObjIsComplement(pNode) );
    // if the node is not AND, this is not EXOR
    if ( !Abc_NodeIsAigAnd(pNode) )
        return 0;
    // if the children are not complemented, this is not EXOR
    if ( !Abc_ObjFaninC0(pNode) || !Abc_ObjFaninC1(pNode) )
        return 0;
    // get children
    pNode0 = Abc_ObjFanin0(pNode);
    pNode1 = Abc_ObjFanin1(pNode);
    // if the children are not ANDs, this is not EXOR
    if ( Abc_ObjFaninNum(pNode0) != 2 || Abc_ObjFaninNum(pNode1) != 2 )
        return 0;
    // otherwise, the node is EXOR iff its grand-children are the same
    return (Abc_ObjFaninId0(pNode0) == Abc_ObjFaninId0(pNode1) || Abc_ObjFaninId0(pNode0) == Abc_ObjFaninId1(pNode1)) &&
           (Abc_ObjFaninId1(pNode0) == Abc_ObjFaninId0(pNode1) || Abc_ObjFaninId1(pNode0) == Abc_ObjFaninId1(pNode1));
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node is the root of MUX or EXOR/NEXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsMuxType( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pNode0, * pNode1;
    // check that the node is regular
    assert( !Abc_ObjIsComplement(pNode) );
    // if the node is not AND, this is not MUX
    if ( !Abc_NodeIsAigAnd(pNode) )
        return 0;
    // if the children are not complemented, this is not MUX
    if ( !Abc_ObjFaninC0(pNode) || !Abc_ObjFaninC1(pNode) )
        return 0;
    // get children
    pNode0 = Abc_ObjFanin0(pNode);
    pNode1 = Abc_ObjFanin1(pNode);
    // if the children are not ANDs, this is not MUX
    if ( Abc_ObjFaninNum(pNode0) != 2 || Abc_ObjFaninNum(pNode1) != 2 )
        return 0;
    // otherwise the node is MUX iff it has a pair of equal grandchildren
    return (Abc_ObjFaninId0(pNode0) == Abc_ObjFaninId0(pNode1) && (Abc_ObjFaninC0(pNode0) ^ Abc_ObjFaninC0(pNode1))) || 
           (Abc_ObjFaninId0(pNode0) == Abc_ObjFaninId1(pNode1) && (Abc_ObjFaninC0(pNode0) ^ Abc_ObjFaninC1(pNode1))) ||
           (Abc_ObjFaninId1(pNode0) == Abc_ObjFaninId0(pNode1) && (Abc_ObjFaninC1(pNode0) ^ Abc_ObjFaninC0(pNode1))) ||
           (Abc_ObjFaninId1(pNode0) == Abc_ObjFaninId1(pNode1) && (Abc_ObjFaninC1(pNode0) ^ Abc_ObjFaninC1(pNode1)));
}

/**Function*************************************************************

  Synopsis    [Recognizes what nodes are control and data inputs of a MUX.]

  Description [If the node is a MUX, returns the control variable C.
  Assigns nodes T and E to be the then and else variables of the MUX. 
  Node C is never complemented. Nodes T and E can be complemented.
  This function also recognizes EXOR/NEXOR gates as MUXes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeRecognizeMux( Abc_Obj_t * pNode, Abc_Obj_t ** ppNodeT, Abc_Obj_t ** ppNodeE )
{
    Abc_Obj_t * pNode0, * pNode1;
    assert( !Abc_ObjIsComplement(pNode) );
    assert( Abc_NodeIsMuxType(pNode) );
    // get children
    pNode0 = Abc_ObjFanin0(pNode);
    pNode1 = Abc_ObjFanin1(pNode);
    // find the control variable
//    if ( pNode1->p1 == Fraig_Not(pNode2->p1) )
    if ( Abc_ObjFaninId0(pNode0) == Abc_ObjFaninId0(pNode1) && (Abc_ObjFaninC0(pNode0) ^ Abc_ObjFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Abc_ObjFaninC0(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Abc_ObjNot(Abc_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Abc_ObjNot(Abc_ObjChild1(pNode0));//pNode1->p2);
            return Abc_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Abc_ObjNot(Abc_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Abc_ObjNot(Abc_ObjChild1(pNode1));//pNode2->p2);
            return Abc_ObjChild0(pNode0);//pNode1->p1;
        }
    }
//    else if ( pNode1->p1 == Fraig_Not(pNode2->p2) )
    else if ( Abc_ObjFaninId0(pNode0) == Abc_ObjFaninId1(pNode1) && (Abc_ObjFaninC0(pNode0) ^ Abc_ObjFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Abc_ObjFaninC0(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Abc_ObjNot(Abc_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Abc_ObjNot(Abc_ObjChild1(pNode0));//pNode1->p2);
            return Abc_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Abc_ObjNot(Abc_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Abc_ObjNot(Abc_ObjChild0(pNode1));//pNode2->p1);
            return Abc_ObjChild0(pNode0);//pNode1->p1;
        }
    }
//    else if ( pNode1->p2 == Fraig_Not(pNode2->p1) )
    else if ( Abc_ObjFaninId1(pNode0) == Abc_ObjFaninId0(pNode1) && (Abc_ObjFaninC1(pNode0) ^ Abc_ObjFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Abc_ObjFaninC1(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Abc_ObjNot(Abc_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Abc_ObjNot(Abc_ObjChild0(pNode0));//pNode1->p1);
            return Abc_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Abc_ObjNot(Abc_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Abc_ObjNot(Abc_ObjChild1(pNode1));//pNode2->p2);
            return Abc_ObjChild1(pNode0);//pNode1->p2;
        }
    }
//    else if ( pNode1->p2 == Fraig_Not(pNode2->p2) )
    else if ( Abc_ObjFaninId1(pNode0) == Abc_ObjFaninId1(pNode1) && (Abc_ObjFaninC1(pNode0) ^ Abc_ObjFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Abc_ObjFaninC1(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Abc_ObjNot(Abc_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Abc_ObjNot(Abc_ObjChild0(pNode0));//pNode1->p1);
            return Abc_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Abc_ObjNot(Abc_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Abc_ObjNot(Abc_ObjChild0(pNode1));//pNode2->p1);
            return Abc_ObjChild1(pNode0);//pNode1->p2;
        }
    }
    assert( 0 ); // this is not MUX
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Prepares two network for a two-argument command similar to "verify".]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkPrepareTwoNtks( FILE * pErr, Abc_Ntk_t * pNtk, char ** argv, int argc, 
    Abc_Ntk_t ** ppNtk1, Abc_Ntk_t ** ppNtk2, int * pfDelete1, int * pfDelete2 )
{
    int fCheck = 1;
    FILE * pFile;
    Abc_Ntk_t * pNtk1, * pNtk2;
    int util_optind = 0;

    *pfDelete1 = 0;
    *pfDelete2 = 0;
    if ( argc == util_optind ) 
    { // use the spec
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Empty current network.\n" );
            return 0;
        }
        if ( pNtk->pSpec == NULL )
        {
            fprintf( pErr, "The external spec is not given.\n" );
            return 0;
        }
        pFile = fopen( pNtk->pSpec, "r" );
        if ( pFile == NULL )
        {
            fprintf( pErr, "Cannot open the external spec file \"%s\".\n", pNtk->pSpec );
            return 0;
        }
        else
            fclose( pFile );

        if ( Abc_NtkIsSeq(pNtk) )
        {
            pNtk1 = Abc_NtkSeqToLogicSop(pNtk);
            *pfDelete1 = 1;
        }
        else
            pNtk1 = pNtk;
        pNtk2 = Io_Read( pNtk->pSpec, fCheck );
        if ( pNtk2 == NULL )
            return 0;
        *pfDelete2 = 1;
    }
    else if ( argc == util_optind + 1 ) 
    {
        if ( pNtk == NULL )
        {
            fprintf( pErr, "Empty current network.\n" );
            return 0;
        }
        if ( Abc_NtkIsSeq(pNtk) )
        {
            pNtk1 = Abc_NtkSeqToLogicSop(pNtk);
            *pfDelete1 = 1;
        }
        else
            pNtk1 = pNtk;
        pNtk2 = Io_Read( argv[util_optind], fCheck );
        if ( pNtk2 == NULL )
            return 0;
        *pfDelete2 = 1;
    }
    else if ( argc == util_optind + 2 ) 
    {
        pNtk1 = Io_Read(  argv[util_optind], fCheck );
        if ( pNtk1 == NULL )
            return 0;
        pNtk2 = Io_Read( argv[util_optind+1], fCheck );
        if ( pNtk2 == NULL )
        {
            Abc_NtkDelete( pNtk1 );
            return 0;
        }
        *pfDelete1 = 1;
        *pfDelete2 = 1;
    }
    else
    {
        fprintf( pErr, "Wrong number of arguments.\n" );
        return 0;
    }
    *ppNtk1 = pNtk1;
    *ppNtk2 = pNtk2;
    return 1;
}


/**Function*************************************************************

  Synopsis    [Returns 1 if it is an AIG with choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeCollectFanins( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanin;
    int i;
    vNodes->nSize = 0;
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Vec_PtrPush( vNodes, pFanin );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if it is an AIG with choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeCollectFanouts( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanout;
    int i;
    vNodes->nSize = 0;
    Abc_ObjForEachFanout( pNode, pFanout, i )
        Vec_PtrPush( vNodes, pFanout );
}

/**Function*************************************************************

  Synopsis    [Procedure used for sorting the nodes in decreasing order of levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeCompareLevelsIncrease( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 )
{
    int Diff = Abc_ObjRegular(*pp1)->Level - Abc_ObjRegular(*pp2)->Level;
    if ( Diff < 0 )
        return -1;
    if ( Diff > 0 ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Procedure used for sorting the nodes in decreasing order of levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeCompareLevelsDecrease( Abc_Obj_t ** pp1, Abc_Obj_t ** pp2 )
{
    int Diff = Abc_ObjRegular(*pp1)->Level - Abc_ObjRegular(*pp2)->Level;
    if ( Diff > 0 )
        return -1;
    if ( Diff < 0 ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Creates the array of fanout counters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkFanoutCounts( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vFanNums;
    Abc_Obj_t * pObj;
    int i;
    vFanNums = Vec_IntAlloc( 0 );
    Vec_IntFill( vFanNums, Abc_NtkObjNumMax(pNtk), -1 );
    Abc_NtkForEachObj( pNtk, pObj, i )
        if ( Abc_ObjIsCi(pObj) || Abc_ObjIsNode(pObj) )
            Vec_IntWriteEntry( vFanNums, i, Abc_ObjFanoutNum(pObj) );
    return vFanNums;
}

/**Function*************************************************************

  Synopsis    [Collects all objects into one array.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkCollectObjects( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int i;
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkForEachObj( pNtk, pNode, i )
        Vec_PtrPush( vNodes, pNode );
    return vNodes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


