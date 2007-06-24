/**CFile****************************************************************

  FileName    [darLib.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Library of AIG subgraphs used for rewriting.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darLib.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Dar_Lib_t_            Dar_Lib_t;
typedef struct Dar_LibObj_t_         Dar_LibObj_t;
typedef struct Dar_LibDat_t_         Dar_LibDat_t;

struct Dar_LibObj_t_ // library object (2 words)
{
    unsigned         Fan0    : 16;  // the first fanin
    unsigned         Fan1    : 16;  // the second fanin
    unsigned         fCompl0 :  1;  // the first compl attribute
    unsigned         fCompl1 :  1;  // the second compl attribute
    unsigned         fPhase  :  1;  // the phase of the node
    unsigned         fTerm   :  1;  // indicates a PI
    unsigned         Num     : 28;  // internal use
};

struct Dar_LibDat_t_ // library object data
{
    Dar_Obj_t *      pFunc;         // the corresponding AIG node if it exists
    int              Level;         // level of this node after it is constructured
    int              TravId;        // traversal ID of the library object data
    unsigned char    Area;          // area of the node
    unsigned char    nLats[3];      // the number of latches on the input/output stem
};

struct Dar_Lib_t_ // library 
{
    // objects
    Dar_LibObj_t *   pObjs;         // the set of library objects
    int              nObjs;         // the number of objects used
    int              iObj;          // the current object
    // object data
    Dar_LibDat_t *   pDatas;
    int              nDatas;
    // structures by class
    int              nSubgr[222];   // the number of subgraphs by class
    int *            pSubgr[222];   // the subgraphs for each class
    int *            pSubgrMem;     // memory for subgraph pointers
    int              pSubgrTotal;   // the total number of subgraph
    // nodes by class
    int              nNodes[222];   // the number of nodes by class
    int *            pNodes[222];   // the nodes for each class
    int *            pNodesMem;     // memory for nodes pointers
    int              pNodesTotal;   // the total number of nodes
    // information by NPN classes
    char **          pPerms4;
    unsigned short * puCanons; 
    char *           pPhases; 
    char *           pPerms; 
    unsigned char *  pMap;
};

static Dar_Lib_t * s_DarLib = NULL;

static inline Dar_LibObj_t * Dar_LibObj( Dar_Lib_t * p, int Id )    { return p->pObjs + Id; }
static inline int            Dar_LibObjTruth( Dar_LibObj_t * pObj ) { return pObj->Num < (0xFFFF & ~pObj->Num) ? pObj->Num : (0xFFFF & ~pObj->Num); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Lib_t * Dar_LibAlloc( int nObjs, int nDatas )
{
    unsigned uTruths[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    Dar_Lib_t * p;
    int i, clk = clock();
    p = ALLOC( Dar_Lib_t, 1 );
    memset( p, 0, sizeof(Dar_Lib_t) );
    // allocate objects
    p->nObjs = nObjs;
    p->pObjs = ALLOC( Dar_LibObj_t, nObjs );
    memset( p->pObjs, 0, sizeof(Dar_LibObj_t) * nObjs );
    // allocate datas
    p->nDatas = nDatas;
    p->pDatas = ALLOC( Dar_LibDat_t, nDatas );
    memset( p->pObjs, 0, sizeof(Dar_LibDat_t) * nDatas );
    // allocate canonical data
    p->pPerms4 = Extra_Permutations( 4 );
    Extra_Truth4VarNPN( &p->puCanons, &p->pPhases, &p->pPerms, &p->pMap );
    // start the elementary objects
    p->iObj = 4;
    for ( i = 0; i < 4; i++ )
    {
        p->pObjs[i].fTerm = 1;
        p->pObjs[i].Num = uTruths[i];
    }
//    PRT( "Library start", clock() - clk );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibFree( Dar_Lib_t * p )
{
    free( p->pObjs );
    free( p->pDatas );
    free( p->pNodesMem );
    free( p->pSubgrMem );
    free( p->pPerms4 );
    free( p->puCanons );
    free( p->pPhases );
    free( p->pPerms );
    free( p->pMap );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Adds one AND to the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibAddNode( Dar_Lib_t * p, int Id0, int Id1, int fCompl0, int fCompl1 )
{
    Dar_LibObj_t * pFan0 = Dar_LibObj( p, Id0 );
    Dar_LibObj_t * pFan1 = Dar_LibObj( p, Id1 );
    Dar_LibObj_t * pObj  = p->pObjs + p->iObj++;
    pObj->Fan0 = Id0;
    pObj->Fan1 = Id1;
    pObj->fCompl0 = fCompl0;
    pObj->fCompl1 = fCompl1;
    pObj->fPhase = (fCompl0 ^ pFan0->fPhase) & (fCompl1 ^ pFan1->fPhase);
    pObj->Num = 0xFFFF & (fCompl0? ~pFan0->Num : pFan0->Num) & (fCompl1? ~pFan1->Num : pFan1->Num);
}

/**Function*************************************************************

  Synopsis    [Adds one AND to the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibSetup_rec( Dar_Lib_t * p, Dar_LibObj_t * pObj, int Class )
{
    if ( pObj->fTerm || (int)pObj->Num == Class )
        return;
    pObj->Num = Class;
    Dar_LibSetup_rec( p, Dar_LibObj(p, pObj->Fan0), Class );
    Dar_LibSetup_rec( p, Dar_LibObj(p, pObj->Fan1), Class );
    if ( p->pNodesMem )
        p->pNodes[Class][ p->nNodes[Class]++ ] = pObj-p->pObjs;
    else
        p->nNodes[Class]++;
}

/**Function*************************************************************

  Synopsis    [Adds one AND to the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibSetup( Dar_Lib_t * p, Vec_Int_t * vOuts )
{
    Dar_LibObj_t * pObj;
    int nNodesTotal, uTruth, Class, Out, i, k;
    assert( p->iObj == p->nObjs );

    // count the number of representatives of each class
    for ( i = 0; i < 222; i++ )
        p->nSubgr[i] = p->nNodes[i] = 0;
    Vec_IntForEachEntry( vOuts, Out, i )
    {
        pObj = Dar_LibObj( p, Out );
        uTruth = Dar_LibObjTruth( pObj );
        Class = p->pMap[uTruth];
        p->nSubgr[Class]++;
    }
    // allocate memory for the roots of each class
    p->pSubgrMem = ALLOC( int, Vec_IntSize(vOuts) );
    p->pSubgrTotal = 0;
    for ( i = 0; i < 222; i++ )
    {
        p->pSubgr[i] = p->pSubgrMem + p->pSubgrTotal;
        p->pSubgrTotal += p->nSubgr[i];
        p->nSubgr[i] = 0;
    }
    assert( p->pSubgrTotal == Vec_IntSize(vOuts) );
    // add the outputs to storage
    Vec_IntForEachEntry( vOuts, Out, i )
    {
        pObj = Dar_LibObj( p, Out );
        uTruth = Dar_LibObjTruth( pObj );
        Class = p->pMap[uTruth];
        p->pSubgr[Class][ p->nSubgr[Class]++ ] = Out;
    }

    // create traversal IDs
    for ( i = 0; i < p->iObj; i++ )
        Dar_LibObj(p, i)->Num = 0xff;
    // count nodes in each class
    for ( i = 0; i < 222; i++ )
        for ( k = 0; k < p->nSubgr[i]; k++ )
            Dar_LibSetup_rec( p, Dar_LibObj(p, p->pSubgr[i][k]), i );
    // count the total number of nodes
    p->pNodesTotal = 0;
    for ( i = 0; i < 222; i++ )
        p->pNodesTotal += p->nNodes[i];
    // allocate memory for the nodes of each class
    p->pNodesMem = ALLOC( int, p->pNodesTotal );
    p->pNodesTotal = 0;
    for ( i = 0; i < 222; i++ )
    {
        p->pNodes[i] = p->pNodesMem + p->pNodesTotal;
        p->pNodesTotal += p->nNodes[i];
        p->nNodes[i] = 0;
    }
    // create traversal IDs
    for ( i = 0; i < p->iObj; i++ )
        Dar_LibObj(p, i)->Num = 0xff;
    // add the nodes to storage
    nNodesTotal = 0;
    for ( i = 0; i < 222; i++ )
    {
         for ( k = 0; k < p->nSubgr[i]; k++ )
            Dar_LibSetup_rec( p, Dar_LibObj(p, p->pSubgr[i][k]), i );
         nNodesTotal += p->nNodes[i];
    }
    assert( nNodesTotal == p->pNodesTotal );
     // prepare the number of the PI nodes
    for ( i = 0; i < 4; i++ )
        Dar_LibObj(p, i)->Num = i;
}

/**Function*************************************************************

  Synopsis    [Reads library from array.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Lib_t * Dar_LibRead()
{
    Vec_Int_t * vObjs, * vOuts;
    Dar_Lib_t * p;
    int i;
    // read nodes and outputs
    vObjs = Dar_LibReadNodes();
    vOuts = Dar_LibReadOuts();
    // create library
    p = Dar_LibAlloc( Vec_IntSize(vObjs)/2 + 4, 6000 );
    // create nodes
    for ( i = 0; i < vObjs->nSize; i += 2 )
        Dar_LibAddNode( p, vObjs->pArray[i] >> 1, vObjs->pArray[i+1] >> 1,
            vObjs->pArray[i] & 1, vObjs->pArray[i+1] & 1 );
    // create outputs
    Dar_LibSetup( p, vOuts );
    Vec_IntFree( vObjs );
    Vec_IntFree( vOuts );
    return p;
}

/**Function*************************************************************

  Synopsis    [Starts the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibStart()
{
    int clk = clock();
    assert( s_DarLib == NULL );
    s_DarLib = Dar_LibRead();
    printf( "The 4-input library started with %d nodes and %d subgraphs. ", s_DarLib->nObjs - 4, s_DarLib->pSubgrTotal );
    PRT( "Time", clock() - clk );
}

/**Function*************************************************************

  Synopsis    [Stops the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibStop()
{
    assert( s_DarLib != NULL );
    Dar_LibFree( s_DarLib );
    s_DarLib = NULL;
}



/**Function*************************************************************

  Synopsis    [Matches the cut with its canonical form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_LibCutMatch( Dar_Man_t * p, Dar_Cut_t * pCut )
{
    Dar_Obj_t * pFanin;
    unsigned uPhase;
    char * pPerm;
    int i;
    assert( pCut->nLeaves == 4 );
    // get the fanin permutation
    uPhase = s_DarLib->pPhases[pCut->uTruth];
    pPerm = s_DarLib->pPerms4[ s_DarLib->pPerms[pCut->uTruth] ];
    // collect fanins with the corresponding permutation/phase
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
    {
        pFanin = Dar_ManObj( p, pCut->pLeaves[pPerm[i]] );
        if ( pFanin == NULL )
        {
            p->nCutsBad++;
            return 0;
        }
        pFanin = Dar_NotCond(pFanin, ((uPhase >> i) & 1) );
//        Vec_PtrWriteEntry( p->vFaninsCur, i, pFanin );
        s_DarLib->pDatas[i].pFunc = pFanin;
        s_DarLib->pDatas[i].Level = Dar_Regular(pFanin)->Level;
    }
    p->nCutsGood++;
    return 1;
}



/**Function*************************************************************

  Synopsis    [Dereferences the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_NodeDeref_rec( Dar_Man_t * p, Dar_Obj_t * pNode )
{
    Dar_Obj_t * pFanin;
    int Counter = 0;
    if ( Dar_ObjIsPi(pNode) )
        return Counter;
    pFanin = Dar_ObjFanin0( pNode );
    assert( pFanin->nRefs > 0 );
    if ( --pFanin->nRefs == 0 )
        Counter += Dar_NodeDeref_rec( p, pFanin );
    if ( Dar_ObjIsBuf(pNode) )
        return Counter;
    pFanin = Dar_ObjFanin1( pNode );
    assert( pFanin->nRefs > 0 );
    if ( --pFanin->nRefs == 0 )
        Counter += Dar_NodeDeref_rec( p, pFanin );
    return 1 + Counter;
}

/**Function*************************************************************

  Synopsis    [References the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_NodeRef_rec( Dar_Man_t * p, Dar_Obj_t * pNode )
{
    Dar_Obj_t * pFanin;
    int Counter = 0;
    if ( Dar_ObjIsPi(pNode) )
        return Counter;
    Dar_ObjSetTravIdCurrent( p, pNode );
    pFanin = Dar_ObjFanin0( pNode );
    if ( pFanin->nRefs++ == 0 )
        Counter += Dar_NodeRef_rec( p, pFanin );
    if ( Dar_ObjIsBuf(pNode) )
        return Counter;
    pFanin = Dar_ObjFanin1( pNode );
    if ( pFanin->nRefs++ == 0 )
        Counter += Dar_NodeRef_rec( p, pFanin );
    return 1 + Counter;
}

/**Function*************************************************************

  Synopsis    [Marks the MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_LibCutMarkMffc( Dar_Man_t * p, Dar_Obj_t * pRoot )
{
    int i, nNodes1, nNodes2;
    // mark the cut leaves
    for ( i = 0; i < 4; i++ )
        Dar_Regular(s_DarLib->pDatas[i].pFunc)->nRefs++;
    // label MFFC with current ID
    Dar_ManIncrementTravId( p );
    nNodes1 = Dar_NodeDeref_rec( p, pRoot );
    nNodes2 = Dar_NodeRef_rec( p, pRoot );
    assert( nNodes1 == nNodes2 );
    // unmark the cut leaves
    for ( i = 0; i < 4; i++ )
        Dar_Regular(s_DarLib->pDatas[i].pFunc)->nRefs--;
    return nNodes1;
}

/**Function*************************************************************

  Synopsis    [Evaluates one cut.]

  Description [Returns the best gain.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibObjPrint_rec( Dar_LibObj_t * pObj )
{
    if ( pObj->fTerm )
    {
        printf( "%c", 'a' + pObj - s_DarLib->pObjs );
        return;
    }
    printf( "(" );
    Dar_LibObjPrint_rec( Dar_LibObj(s_DarLib, pObj->Fan0) );
    if ( pObj->fCompl0 )
        printf( "\'" );
    Dar_LibObjPrint_rec( Dar_LibObj(s_DarLib, pObj->Fan1) );
    if ( pObj->fCompl0 )
        printf( "\'" );
    printf( ")" );
}


/**Function*************************************************************

  Synopsis    [Assigns numbers to the nodes of one class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibEvalAssignNums( Dar_Man_t * p, int Class )
{
    Dar_LibObj_t * pObj;
    Dar_LibDat_t * pData, * pData0, * pData1;
    Dar_Obj_t * pGhost, * pFanin0, * pFanin1;
    int i;
    for ( i = 0; i < s_DarLib->nNodes[Class]; i++ )
    {
        // get one class node, assign its temporary number and set its data
        pObj = Dar_LibObj(s_DarLib, s_DarLib->pNodes[Class][i]);
        pObj->Num = 4 + i;
        pData = s_DarLib->pDatas + pObj->Num;
        pData->pFunc = NULL;
        pData->TravId = 0xFFFF;
        // explore the fanins
        pData0 = s_DarLib->pDatas + Dar_LibObj(s_DarLib, pObj->Fan0)->Num;
        pData1 = s_DarLib->pDatas + Dar_LibObj(s_DarLib, pObj->Fan1)->Num;
        pData->Level = 1 + DAR_MAX(pData0->Level, pData1->Level);
        if ( pData0->pFunc == NULL || pData1->pFunc == NULL )
            continue;
        pFanin0 = Dar_NotCond( pData0->pFunc, pObj->fCompl0 );
        pFanin1 = Dar_NotCond( pData1->pFunc, pObj->fCompl1 );
        pGhost = Dar_ObjCreateGhost( p, pFanin0, pFanin1, DAR_AIG_AND );
        pData->pFunc = Dar_TableLookup( p, pGhost );
        // clear the node if it is part of MFFC
        if ( pData->pFunc != NULL && Dar_ObjIsTravIdCurrent(p, pData->pFunc) )
            pData->pFunc = NULL;
//if ( Class == 7 )
//printf( "Evaling node %d at data %d\n", pData->pFunc? pData->pFunc->Id : -1, pObj->Num );
    }
}

/**Function*************************************************************

  Synopsis    [Evaluates one cut.]

  Description [Returns the best gain.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_LibEval_rec( Dar_LibObj_t * pObj, int Out, int nNodesSaved, int Required )
{
    Dar_LibDat_t * pData;
    int Area;
    if ( pObj->fTerm )
        return 0;
    assert( pObj->Num > 3 );
    pData = s_DarLib->pDatas + pObj->Num;
    if ( pData->pFunc )
        return 0;
    if ( pData->Level > Required )
        return 0xff;
    if ( pData->TravId == Out )
        return pData->Area;
    pData->TravId = Out;
    Area = 1 + Dar_LibEval_rec( Dar_LibObj(s_DarLib, pObj->Fan0), Out, nNodesSaved, Required );
    if ( Area > nNodesSaved )
        return pData->Area = 0xff;
    Area += Dar_LibEval_rec( Dar_LibObj(s_DarLib, pObj->Fan1), Out, nNodesSaved, Required );
    if ( Area > nNodesSaved )
        return pData->Area = 0xff;
    return pData->Area = Area;
}

/**Function*************************************************************

  Synopsis    [Evaluates one cut.]

  Description [Returns the best gain.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibEval( Dar_Man_t * p, Dar_Obj_t * pRoot, Dar_Cut_t * pCut, int Required )
{
    Dar_LibObj_t * pObj;
    int i, k, Class, nNodesSaved, nNodesAdded, nNodesGained, clk;
    if ( pCut->nLeaves != 4 )
        return;
    clk = clock();
/*
    for ( k = 0; k < 4; k++ )
        if ( pCut->pLeaves[k] > 4 )
            return;
*/    
    // check if the cut exits
    if ( !Dar_LibCutMatch(p, pCut) )
        return;
    // mark MFFC of the node
    nNodesSaved = Dar_LibCutMarkMffc( p, pRoot );
    // evaluate the cut
    Class = s_DarLib->pMap[pCut->uTruth];
    Dar_LibEvalAssignNums( p, Class );

//if ( pRoot->Id == 654 )
//printf( "\n" );
    // profile outputs by their savings
    p->nTotalSubgs += s_DarLib->nSubgr[Class];
    p->ClassSubgs[Class] += s_DarLib->nSubgr[Class];
    for ( i = 0; i < s_DarLib->nSubgr[Class]; i++ )
    {
        pObj = Dar_LibObj(s_DarLib, s_DarLib->pSubgr[Class][i]);
        if ( pRoot->Id == 654 )
        {
//            Dar_LibObjPrint_rec( pObj );
//            printf( "\n" );
        }
        nNodesAdded = Dar_LibEval_rec( pObj, i, nNodesSaved, Required );
        nNodesGained = nNodesSaved - nNodesAdded;
        if ( nNodesGained <= 0 )
            continue;
        if ( nNodesGained < p->GainBest || 
            (nNodesGained == p->GainBest && s_DarLib->pDatas[pObj->Num].Level >= p->GainBest) )
            continue;
        // remember this possibility
        Vec_PtrClear( p->vLeavesBest );
        for ( k = 0; k < 4; k++ )
            Vec_PtrPush( p->vLeavesBest, s_DarLib->pDatas[k].pFunc );
        p->OutBest   = s_DarLib->pSubgr[Class][i];
        p->LevelBest = s_DarLib->pDatas[pObj->Num].Level;
        p->GainBest  = nNodesGained;
        p->ClassBest = Class;
    }
clk = clock() - clk;
p->ClassTimes[Class] += clk;
p->timeEval += clk;
}

/**Function*************************************************************

  Synopsis    [Clears the fields of the nodes used in this cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_LibBuildClear_rec( Dar_LibObj_t * pObj, int * pCounter )
{
    if ( pObj->fTerm )
        return;
    pObj->Num = (*pCounter)++;
    s_DarLib->pDatas[ pObj->Num ].pFunc = NULL;
    Dar_LibBuildClear_rec( Dar_LibObj(s_DarLib, pObj->Fan0), pCounter );
    Dar_LibBuildClear_rec( Dar_LibObj(s_DarLib, pObj->Fan1), pCounter );
}

/**Function*************************************************************

  Synopsis    [Reconstructs the best cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_LibBuildBest_rec( Dar_Man_t * p, Dar_LibObj_t * pObj )
{
    Dar_Obj_t * pFanin0, * pFanin1;
    Dar_LibDat_t * pData = s_DarLib->pDatas + pObj->Num;
    if ( pData->pFunc )
        return pData->pFunc;
    pFanin0 = Dar_LibBuildBest_rec( p, Dar_LibObj(s_DarLib, pObj->Fan0) );
    pFanin1 = Dar_LibBuildBest_rec( p, Dar_LibObj(s_DarLib, pObj->Fan1) );
    pFanin0 = Dar_NotCond( pFanin0, pObj->fCompl0 );
    pFanin1 = Dar_NotCond( pFanin1, pObj->fCompl1 );
    pData->pFunc = Dar_And( p, pFanin0, pFanin1 );
//printf( "Adding node %d for data %d\n", pData->pFunc->Id, pObj->Num );
    return pData->pFunc;
}

/**Function*************************************************************

  Synopsis    [Reconstructs the best cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_LibBuildBest( Dar_Man_t * p )
{
    int i, Counter = 4;
    for ( i = 0; i < 4; i++ )
        s_DarLib->pDatas[i].pFunc = Vec_PtrEntry( p->vLeavesBest, i );
    Dar_LibBuildClear_rec( Dar_LibObj(s_DarLib, p->OutBest), &Counter );
    return Dar_LibBuildBest_rec( p, Dar_LibObj(s_DarLib, p->OutBest) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


