/**CFile****************************************************************

  FileName    [abcUtils.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcUtils.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "main.h"
#include "mio.h"
#include "ft.h"

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
    assert( Abc_NtkIsNetlist(pNtk) || Abc_NtkIsLogicSop(pNtk) );
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
    assert( Abc_NtkIsNetlist(pNtk) || Abc_NtkIsLogicSop(pNtk) );
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
    Vec_Int_t * vFactor;
    Abc_Obj_t * pNode;
    int nNodes, i;
    assert( Abc_NtkIsNetlist(pNtk) || Abc_NtkIsLogicSop(pNtk) );
    nNodes = 0;
//    Ft_FactorStartMan();
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        vFactor = Ft_Factor( pNode->pData );
        nNodes += Ft_FactorGetNumNodes(vFactor);
        Vec_IntFree( vFactor );
    }
//    Ft_FactorStopMan();
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
    assert( Abc_NtkIsLogicBdd(pNtk) );
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
    assert( Abc_NtkIsLogicBdd(pNtk) );
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
    assert( Abc_NtkIsLogicMap(pNtk) );
    TotalArea = 0.0;
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        assert( pNode->pData );
        TotalArea += Mio_GateReadArea( pNode->pData );
    }
    return TotalArea;
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
Abc_Obj_t * Abc_NodeHasUniqueNamedFanout( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanout, * pFanoutNamed;
    int i, Counter;
    if ( !Abc_ObjIsNode(pNode) )
        return NULL;
    Counter = 0;
    Abc_ObjForEachFanout( pNode, pFanout, i )
    {
        if ( (Abc_ObjIsPo(pFanout) || Abc_ObjIsLatch(pFanout)) && !Abc_ObjFaninC0(pFanout) )
        {
            assert( Abc_ObjFaninNum(pFanout) == 1 );
            assert( Abc_ObjFanin0(pFanout) == pNode );
            pFanoutNamed = pFanout;
            Counter++;
        }
    }
    if ( Counter == 1 )
        return pFanoutNamed;
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the PO names can be written directly.]

  Description [This is true if the POs of the logic network are
  not complemented and not duplicated. This condition has to be
  specifically enforced after mapping, to make sure additional 
  INVs/BUFs are not written into the file.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkLogicHasSimplePos( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i;
    assert( !Abc_NtkIsNetlist(pNtk) );
    // check if there are complemented or idential POs
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkForEachPo( pNtk, pNode, i ) 
    {
        pNode = Abc_ObjChild0(pNode);
        if ( Abc_ObjIsComplement(pNode) )
            return 0;
        if ( Abc_NodeIsTravIdCurrent(pNode) )
            return 0;
        Abc_NodeSetTravIdCurrent(pNode);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Transforms the network to have simple POs.]

  Description [The POs are simple if the POs of the logic network are
  not complemented and not duplicated. This condition has to be
  specifically enforced after FPGA mapping, to make sure additional 
  INVs/BUFs are not written into the file.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkLogicMakeSimplePos( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode, * pDriver, * pDriverDup, * pFanin;
    int i, k, nDupGates = 0;
    assert( Abc_NtkIsLogic(pNtk) );
    // if a PO driver has more than one fanout, duplicate it
    Abc_NtkForEachCo( pNtk, pNode, i ) 
    {
        pDriver = Abc_ObjFanin0(pNode);
        if ( Abc_ObjFanoutNum(pDriver) == 1 )
            continue;
        // do not modify CI
        if ( !Abc_ObjIsNode(pDriver) )
            continue;
        pDriverDup = Abc_NtkDupObj( pNtk, pDriver ); 
        Abc_ObjForEachFanin( pDriver, pFanin, k )
            Abc_ObjAddFanin( pDriverDup, pFanin );
        // update the fanin of the PO node
        Abc_ObjPatchFanin( pNode, pDriver, pDriverDup );
        assert( Abc_ObjFanoutNum(pDriverDup) == 1 );
        nDupGates++;
    }
    // if a PO comes complemented change the drivers function
    Abc_NtkForEachCo( pNtk, pNode, i ) 
    {
        pDriver = Abc_ObjFanin0(pNode);
        if ( !Abc_ObjFaninC0(pNode) )
            continue;
        // do not modify PIs and LOs
        if ( !Abc_ObjIsNode(pDriver) )
            continue;
        // the driver is complemented - change polarity
        if ( Abc_NtkIsLogicSop(pNtk) )
            Abc_SopComplement( pDriver->pData );
        else if ( Abc_NtkIsLogicBdd(pNtk) )
            pDriver->pData = Cudd_Not( pDriver->pData );
        else
            assert( 0 );
        // update the complemented edge of the fanin
        Abc_ObjXorFaninC(pNode, 0);
        assert( !Abc_ObjFaninC0(pNode) );
    }
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

  Synopsis    [Returns 1 if the node is the root of MUX or EXOR/NEXOR.]

  Description [The node can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeIsMuxType( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pNode0, * pNode1;
    // check that the node is regular
    assert( !Abc_ObjIsComplement(pNode) );
    // if the node is not AND, this is not MUX
    if ( !Abc_NodeIsAnd(pNode) )
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

  Synopsis    [Returns 1 if it is an AIG with choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCountChoiceNodes( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i, Counter;
    if ( !Abc_NtkIsAig(pNtk) )
        return 0;
    Counter = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
        Counter += Abc_NodeIsChoice( pNode );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Prepares two network for a two-argument command similar to "verify".]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkPrepareCommand( FILE * pErr, Abc_Ntk_t * pNtk, char ** argv, int argc, 
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

  Synopsis    [Collect all nodes by level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_AigCollectAll( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int i;
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
        Vec_PtrPush( vNodes, pNode );
    Vec_PtrSort( vNodes, Abc_NodeCompareLevelsIncrease );
    return vNodes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


