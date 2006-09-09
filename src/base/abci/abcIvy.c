/**CFile****************************************************************

  FileName    [abcIvy.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Strashing of the current network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcIvy.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "dec.h"
#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t *  Abc_NtkFromAig( Abc_Ntk_t * pNtkOld, Ivy_Man_t * pMan );
static Abc_Ntk_t *  Abc_NtkFromAigSeq( Abc_Ntk_t * pNtkOld, Ivy_Man_t * pMan, int fHaig );
static Ivy_Man_t *  Abc_NtkToAig( Abc_Ntk_t * pNtkOld );

static void         Abc_NtkStrashPerformAig( Abc_Ntk_t * pNtk, Ivy_Man_t * pMan );
static Ivy_Obj_t *  Abc_NodeStrashAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode );
static Ivy_Obj_t *  Abc_NodeStrashAigSopAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop );
static Ivy_Obj_t *  Abc_NodeStrashAigExorAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop );
static Ivy_Obj_t *  Abc_NodeStrashAigFactorAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop );
extern char *       Mio_GateReadSop( void * pGate );

typedef int   Abc_Edge_t;
static inline Abc_Edge_t   Abc_EdgeCreate( int Id, int fCompl )                { return (Id << 1) | fCompl;             }
static inline int          Abc_EdgeId( Abc_Edge_t Edge )                       { return Edge >> 1;                      }
static inline int          Abc_EdgeIsComplement( Abc_Edge_t Edge )             { return Edge & 1;                       }
static inline Abc_Edge_t   Abc_EdgeRegular( Abc_Edge_t Edge )                  { return (Edge >> 1) << 1;               }
static inline Abc_Edge_t   Abc_EdgeNot( Abc_Edge_t Edge )                      { return Edge ^ 1;                       }
static inline Abc_Edge_t   Abc_EdgeNotCond( Abc_Edge_t Edge, int fCond )       { return Edge ^ fCond;                   }
static inline Abc_Edge_t   Abc_EdgeFromNode( Abc_Obj_t * pNode )               { return Abc_EdgeCreate( Abc_ObjRegular(pNode)->Id, Abc_ObjIsComplement(pNode) );       }
static inline Abc_Obj_t *  Abc_EdgeToNode( Abc_Ntk_t * p, Abc_Edge_t Edge )    { return Abc_ObjNotCond( Abc_NtkObj(p, Abc_EdgeId(Edge)), Abc_EdgeIsComplement(Edge) ); }

static inline Abc_Obj_t *  Abc_ObjFanin0Ivy( Abc_Ntk_t * p, Ivy_Obj_t * pObj ) { return Abc_ObjNotCond( Abc_EdgeToNode(p, Ivy_ObjFanin0(pObj)->TravId), Ivy_ObjFaninC0(pObj) ); }
static inline Abc_Obj_t *  Abc_ObjFanin1Ivy( Abc_Ntk_t * p, Ivy_Obj_t * pObj ) { return Abc_ObjNotCond( Abc_EdgeToNode(p, Ivy_ObjFanin1(pObj)->TravId), Ivy_ObjFaninC1(pObj) ); }

static int * Abc_NtkCollectLatchValues( Abc_Ntk_t * pNtk, int fUseDcs );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prepares the IVY package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Man_t * Abc_NtkIvyBefore( Abc_Ntk_t * pNtk, int fSeq, int fUseDc )
{
    Ivy_Man_t * pMan;
    int fCleanup = 1;
    assert( !Abc_NtkIsNetlist(pNtk) );
    assert( !Abc_NtkIsSeq(pNtk) );
    if ( Abc_NtkIsBddLogic(pNtk) )
    {
        if ( !Abc_NtkBddToSop(pNtk, 0) )
        {
            printf( "Abc_NtkIvyBefore(): Converting to SOPs has failed.\n" );
            return NULL;
        }
    }
    if ( Abc_NtkCountSelfFeedLatches(pNtk) )
    {
        printf( "Warning: The network has %d self-feeding latches. Quitting.\n", Abc_NtkCountSelfFeedLatches(pNtk) );
        return NULL;
    }
    // print warning about choice nodes
    if ( Abc_NtkGetChoiceNum( pNtk ) )
        printf( "Warning: The choice nodes in the initial AIG are removed by strashing.\n" );
    // convert to the AIG manager
    pMan = Abc_NtkToAig( pNtk );
    if ( !Ivy_ManCheck( pMan ) )
    {
        printf( "AIG check has failed.\n" );
        Ivy_ManStop( pMan );
        return NULL;
    }
//    Ivy_ManPrintStats( pMan );
    if ( fSeq )
    {
        int nLatches = Abc_NtkLatchNum(pNtk);
        int * pInit = Abc_NtkCollectLatchValues( pNtk, fUseDc );
        Ivy_ManMakeSeq( pMan, nLatches, pInit );
        FREE( pInit );
//        Ivy_ManPrintStats( pMan );
    }
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Prepares the IVY package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkIvyAfter( Abc_Ntk_t * pNtk, Ivy_Man_t * pMan, int fSeq, int fHaig )
{
    Abc_Ntk_t * pNtkAig;
    int nNodes, fCleanup = 1;
    // convert from the AIG manager
    if ( fSeq )
        pNtkAig = Abc_NtkFromAigSeq( pNtk, pMan, fHaig );
    else
        pNtkAig = Abc_NtkFromAig( pNtk, pMan );
    // report the cleanup results
    if ( !fHaig && fCleanup && (nNodes = Abc_AigCleanup(pNtkAig->pManFunc)) )
        printf( "Warning: AIG cleanup removed %d nodes (this is not a bug).\n", nNodes );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkAig->pExdc = Abc_NtkDup( pNtk->pExdc );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkStrash: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkIvyStrash( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkAig;
    Ivy_Man_t * pMan;
    pMan = Abc_NtkIvyBefore( pNtk, 1, 0 );
    if ( pMan == NULL )
        return NULL;
    pNtkAig = Abc_NtkIvyAfter( pNtk, pMan, 1, 0 );
    Ivy_ManStop( pMan );
    return pNtkAig;
}
 
/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkIvyHaig( Abc_Ntk_t * pNtk, int nIters, int fUseZeroCost, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Ivy_Man_t * pMan;
    int i;

    pMan = Abc_NtkIvyBefore( pNtk, 1, 1 );
    if ( pMan == NULL )
        return NULL;

    Ivy_ManHaigStart( pMan, fVerbose );
    Ivy_ManRewriteSeq( pMan, 0, 0 );
    for ( i = 1; i < nIters; i++ )
        Ivy_ManRewriteSeq( pMan, fUseZeroCost, 0 );
    Ivy_ManHaigPostprocess( pMan, fVerbose );

    // write working AIG into the current network
//    pNtkAig = Abc_NtkIvyAfter( pNtk, pMan, 1, 0 ); 
    // write HAIG into the current network
    pNtkAig = Abc_NtkIvyAfter( pNtk, pMan->pHaig, 1, 1 );

    Ivy_ManHaigStop( pMan );
    Ivy_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkIvyCuts( Abc_Ntk_t * pNtk, int nInputs )
{
    extern void Ivy_CutComputeAll( Ivy_Man_t * p, int nInputs );
    Ivy_Man_t * pMan;
    pMan = Abc_NtkIvyBefore( pNtk, 1, 0 );
    if ( pMan == NULL )
        return;
    Ivy_CutComputeAll( pMan, nInputs );
    Ivy_ManStop( pMan );
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkIvyRewrite( Abc_Ntk_t * pNtk, int fUpdateLevel, int fUseZeroCost, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Ivy_Man_t * pMan;
    pMan = Abc_NtkIvyBefore( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
    Ivy_ManRewritePre( pMan, fUpdateLevel, fUseZeroCost, fVerbose );
    pNtkAig = Abc_NtkIvyAfter( pNtk, pMan, 0, 0 );
    Ivy_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkIvyRewriteSeq( Abc_Ntk_t * pNtk, int fUseZeroCost, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Ivy_Man_t * pMan;
    pMan = Abc_NtkIvyBefore( pNtk, 1, 1 );
    if ( pMan == NULL )
        return NULL;
    Ivy_ManRewriteSeq( pMan, fUseZeroCost, fVerbose );
//    Ivy_ManRewriteSeq( pMan, 1, 0 );
//    Ivy_ManRewriteSeq( pMan, 1, 0 );
    pNtkAig = Abc_NtkIvyAfter( pNtk, pMan, 1, 0 );
    Ivy_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkIvyResyn( Abc_Ntk_t * pNtk, int fUpdateLevel, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Ivy_Man_t * pMan, * pTemp;
    pMan = Abc_NtkIvyBefore( pNtk, 0, 0 );
    if ( pMan == NULL )
        return NULL;
    pMan = Ivy_ManResyn( pTemp = pMan, fUpdateLevel, fVerbose );
    Ivy_ManStop( pTemp );
    pNtkAig = Abc_NtkIvyAfter( pNtk, pMan, 0, 0 );
    Ivy_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkIvy( Abc_Ntk_t * pNtk )
{
//    Abc_Ntk_t * pNtkAig;
    Ivy_Man_t * pMan;//, * pTemp;
    int fCleanup = 1;
//    int nNodes;
    int nLatches = Abc_NtkLatchNum(pNtk);
    int * pInit = Abc_NtkCollectLatchValues( pNtk, 0 );

    assert( !Abc_NtkIsNetlist(pNtk) );
    assert( !Abc_NtkIsSeq(pNtk) );
    if ( Abc_NtkIsBddLogic(pNtk) )
    {
        if ( !Abc_NtkBddToSop(pNtk, 0) )
        {
            FREE( pInit );
            printf( "Abc_NtkIvy(): Converting to SOPs has failed.\n" );
            return NULL;
        }
    }
    if ( Abc_NtkCountSelfFeedLatches(pNtk) )
    {
        printf( "Warning: The network has %d self-feeding latches. Quitting.\n", Abc_NtkCountSelfFeedLatches(pNtk) );
        return NULL;
    }

    // print warning about choice nodes
    if ( Abc_NtkGetChoiceNum( pNtk ) )
        printf( "Warning: The choice nodes in the initial AIG are removed by strashing.\n" );

    // convert to the AIG manager
    pMan = Abc_NtkToAig( pNtk );
    if ( !Ivy_ManCheck( pMan ) )
    {
        FREE( pInit );
        printf( "AIG check has failed.\n" );
        Ivy_ManStop( pMan );
        return NULL;
    }

//    Ivy_MffcTest( pMan );
//    Ivy_ManPrintStats( pMan );

//    pMan = Ivy_ManBalance( pTemp = pMan, 1 );
//    Ivy_ManStop( pTemp );

//    Ivy_ManSeqRewrite( pMan, 0, 0 );
//    Ivy_ManTestCutsAlg( pMan );
//    Ivy_ManTestCutsBool( pMan );
//    Ivy_ManRewriteAlg( pMan, 1, 1 );

//    pMan = Ivy_ManResyn( pTemp = pMan, 1, 0 );
//    Ivy_ManStop( pTemp );

//    Ivy_ManTestCutsAll( pMan );
//    Ivy_ManTestCutsTravAll( pMan );

//    Ivy_ManPrintStats( pMan );

//    Ivy_ManPrintStats( pMan );
//    Ivy_ManRewritePre( pMan, 1, 0, 0 );
//    Ivy_ManPrintStats( pMan );
//    printf( "\n" );

//    Ivy_ManPrintStats( pMan );
//    Ivy_ManMakeSeq( pMan, nLatches, pInit );
//    Ivy_ManPrintStats( pMan );

//    Ivy_ManRequiredLevels( pMan );

//    Ivy_FastMapPerform( pMan, 8 );
    Ivy_ManStop( pMan );
    return NULL;


/*
    // convert from the AIG manager
    pNtkAig = Abc_NtkFromAig( pNtk, pMan );
//    pNtkAig = Abc_NtkFromAigSeq( pNtk, pMan );
    Ivy_ManStop( pMan );

    // report the cleanup results
    if ( fCleanup && (nNodes = Abc_AigCleanup(pNtkAig->pManFunc)) )
        printf( "Warning: AIG cleanup removed %d nodes (this is not a bug).\n", nNodes );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkAig->pExdc = Abc_NtkDup( pNtk->pExdc );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkAig ) )
    {
        FREE( pInit );
        printf( "Abc_NtkStrash: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }

    FREE( pInit );
    return pNtkAig;
*/
}



/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromAig( Abc_Ntk_t * pNtkOld, Ivy_Man_t * pMan )
{
    Vec_Int_t * vNodes;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj, * pObjNew, * pFaninNew, * pFaninNew0, * pFaninNew1;
    Ivy_Obj_t * pNode;
    int i;
    // perform strashing
    pNtk = Abc_NtkStartFrom( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Ivy_ManConst1(pMan)->TravId = Abc_EdgeFromNode( Abc_AigConst1(pNtk) );
    Abc_NtkForEachCi( pNtkOld, pObj, i )
        Ivy_ManPi(pMan, i)->TravId = Abc_EdgeFromNode( pObj->pCopy );
    // rebuild the AIG
    vNodes = Ivy_ManDfs( pMan );
    Ivy_ManForEachNodeVec( pMan, vNodes, pNode, i )
    {
        // add the first fanins
        pFaninNew0 = Abc_ObjFanin0Ivy( pNtk, pNode );
        if ( Ivy_ObjIsBuf(pNode) )
        {
            pNode->TravId = Abc_EdgeFromNode( pFaninNew0 );
            continue;
        }
        // add the first second
        pFaninNew1 = Abc_ObjFanin1Ivy( pNtk, pNode );
        // create the new node
        if ( Ivy_ObjIsExor(pNode) )
            pObjNew = Abc_AigXor( pNtk->pManFunc, pFaninNew0, pFaninNew1 );
        else
            pObjNew = Abc_AigAnd( pNtk->pManFunc, pFaninNew0, pFaninNew1 );
        pNode->TravId = Abc_EdgeFromNode( pObjNew );
    }
    // connect the PO nodes
    Abc_NtkForEachCo( pNtkOld, pObj, i )
    {
        pFaninNew = Abc_ObjFanin0Ivy( pNtk, Ivy_ManPo(pMan, i) );
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
    }
    Vec_IntFree( vNodes );
    if ( !Abc_NtkCheck( pNtk ) )
        fprintf( stdout, "Abc_NtkFromAig(): Network check has failed.\n" );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromAigSeq( Abc_Ntk_t * pNtkOld, Ivy_Man_t * pMan, int fHaig )
{
    Vec_Int_t * vNodes, * vLatches;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj, * pObjNew, * pFaninNew, * pFaninNew0, * pFaninNew1;
    Ivy_Obj_t * pNode, * pTemp;
    int i;
//    assert( Ivy_ManLatchNum(pMan) > 0 );
    // perform strashing
    pNtk = Abc_NtkStartFromNoLatches( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Ivy_ManConst1(pMan)->TravId = Abc_EdgeFromNode( Abc_AigConst1(pNtk) );
    Abc_NtkForEachPi( pNtkOld, pObj, i )
        Ivy_ManPi(pMan, i)->TravId = Abc_EdgeFromNode( pObj->pCopy );
    // create latches of the new network
    vNodes = Ivy_ManDfsSeq( pMan, &vLatches );
    Ivy_ManForEachNodeVec( pMan, vLatches, pNode, i )
    {
        pObjNew = Abc_NtkCreateLatch( pNtk );
        pFaninNew0 = Abc_NtkCreateBo( pNtk );
        pFaninNew1 = Abc_NtkCreateBi( pNtk );
        Abc_ObjAddFanin( pObjNew, pFaninNew0 );
        Abc_ObjAddFanin( pFaninNew1, pObjNew );
        if ( fHaig || Ivy_ObjInit(pNode) == IVY_INIT_DC )
            Abc_LatchSetInitDc( pObjNew );
        else if ( Ivy_ObjInit(pNode) == IVY_INIT_1 )
            Abc_LatchSetInit1( pObjNew );
        else if ( Ivy_ObjInit(pNode) == IVY_INIT_0 )
            Abc_LatchSetInit0( pObjNew );
        else assert( 0 );
        pNode->TravId = Abc_EdgeFromNode( pFaninNew1 );
    }
    Abc_NtkAddDummyBoxNames( pNtk );
    // rebuild the AIG
    Ivy_ManForEachNodeVec( pMan, vNodes, pNode, i )
    {
        // add the first fanin
        pFaninNew0 = Abc_ObjFanin0Ivy( pNtk, pNode );
        if ( Ivy_ObjIsBuf(pNode) )
        {
            pNode->TravId = Abc_EdgeFromNode( pFaninNew0 );
            continue;
        }
        // add the second fanin
        pFaninNew1 = Abc_ObjFanin1Ivy( pNtk, pNode );
        // create the new node
        if ( Ivy_ObjIsExor(pNode) )
            pObjNew = Abc_AigXor( pNtk->pManFunc, pFaninNew0, pFaninNew1 );
        else
            pObjNew = Abc_AigAnd( pNtk->pManFunc, pFaninNew0, pFaninNew1 );
        pNode->TravId = Abc_EdgeFromNode( pObjNew );
        // process the choice nodes
        if ( fHaig && pNode->pEquiv && Ivy_ObjRefs(pNode) > 0 )
        {
            pFaninNew = Abc_EdgeToNode( pNtk, pNode->TravId );
            pFaninNew->fPhase = 0;
            assert( !Ivy_IsComplement(pNode->pEquiv) );
            for ( pTemp = pNode->pEquiv; pTemp != pNode; pTemp = Ivy_Regular(pTemp->pEquiv) )
            {
                pFaninNew1 = Abc_EdgeToNode( pNtk, pTemp->TravId );
                pFaninNew1->fPhase = Ivy_IsComplement( pTemp->pEquiv );
                pFaninNew->pData = pFaninNew1;
                pFaninNew = pFaninNew1;
            }
            pFaninNew->pData = NULL;
//            printf( "Writing choice node %d.\n", pNode->Id );
        }
    }
    // connect the PO nodes
    Abc_NtkForEachPo( pNtkOld, pObj, i )
    {
        pFaninNew = Abc_ObjFanin0Ivy( pNtk, Ivy_ManPo(pMan, i) );
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
    }
    // connect the latches
    Ivy_ManForEachNodeVec( pMan, vLatches, pNode, i )
    {
        pFaninNew = Abc_ObjFanin0Ivy( pNtk, pNode );
        Abc_ObjAddFanin( Abc_ObjFanin0(Abc_NtkBox(pNtk, i)), pFaninNew );
    }
    Vec_IntFree( vLatches );
    Vec_IntFree( vNodes );
    if ( !Abc_NtkCheck( pNtk ) )
        fprintf( stdout, "Abc_NtkFromAigSeq(): Network check has failed.\n" );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Man_t * Abc_NtkToAig( Abc_Ntk_t * pNtkOld )
{
    Ivy_Man_t * pMan;
    Abc_Obj_t * pObj;
    Ivy_Obj_t * pFanin;
    int i;
    // create the manager
    assert( Abc_NtkHasSop(pNtkOld) || Abc_NtkIsStrash(pNtkOld) );
    pMan = Ivy_ManStart();
    // create the PIs
    if ( Abc_NtkIsStrash(pNtkOld) )
        Abc_AigConst1(pNtkOld)->pCopy = (Abc_Obj_t *)Ivy_ManConst1(pMan);
    Abc_NtkForEachCi( pNtkOld, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Ivy_ObjCreatePi(pMan);
    // perform the conversion of the internal nodes
    Abc_NtkStrashPerformAig( pNtkOld, pMan );
    // create the POs
    Abc_NtkForEachCo( pNtkOld, pObj, i )
    {
        pFanin = (Ivy_Obj_t *)Abc_ObjFanin0(pObj)->pCopy;
        pFanin = Ivy_NotCond( pFanin, Abc_ObjFaninC0(pObj) );
        Ivy_ObjCreatePo( pMan, pFanin );
    }
    Ivy_ManCleanup( pMan );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Prepares the network for strashing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkStrashPerformAig( Abc_Ntk_t * pNtk, Ivy_Man_t * pMan )
{
//    ProgressBar * pProgress;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int i;
    vNodes = Abc_NtkDfs( pNtk, 0 );
//    pProgress = Extra_ProgressBarStart( stdout, vNodes->nSize );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
//        Extra_ProgressBarUpdate( pProgress, i, NULL );
        pNode->pCopy = (Abc_Obj_t *)Abc_NodeStrashAig( pMan, pNode );
    }
//    Extra_ProgressBarStop( pProgress );
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Abc_NodeStrashAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode )
{
    int fUseFactor = 1;
    char * pSop;
    Ivy_Obj_t * pFanin0, * pFanin1;

    assert( Abc_ObjIsNode(pNode) );

    // consider the case when the graph is an AIG
    if ( Abc_NtkIsStrash(pNode->pNtk) )
    {
        if ( Abc_AigNodeIsConst(pNode) )
            return Ivy_ManConst1(pMan);
        pFanin0 = (Ivy_Obj_t *)Abc_ObjFanin0(pNode)->pCopy;
        pFanin0 = Ivy_NotCond( pFanin0, Abc_ObjFaninC0(pNode) );
        pFanin1 = (Ivy_Obj_t *)Abc_ObjFanin1(pNode)->pCopy;
        pFanin1 = Ivy_NotCond( pFanin1, Abc_ObjFaninC1(pNode) );
        return Ivy_And( pMan, pFanin0, pFanin1 );
    }

    // get the SOP of the node
    if ( Abc_NtkHasMapping(pNode->pNtk) )
        pSop = Mio_GateReadSop(pNode->pData);
    else
        pSop = pNode->pData;

    // consider the constant node
    if ( Abc_NodeIsConst(pNode) )
        return Ivy_NotCond( Ivy_ManConst1(pMan), Abc_SopIsConst0(pSop) );

    // consider the special case of EXOR function
    if ( Abc_SopIsExorType(pSop) )
        return Abc_NodeStrashAigExorAig( pMan, pNode, pSop );

    // decide when to use factoring
    if ( fUseFactor && Abc_ObjFaninNum(pNode) > 2 && Abc_SopGetCubeNum(pSop) > 1 )
        return Abc_NodeStrashAigFactorAig( pMan, pNode, pSop );
    return Abc_NodeStrashAigSopAig( pMan, pNode, pSop );
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Abc_NodeStrashAigSopAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop )
{
    Abc_Obj_t * pFanin;
    Ivy_Obj_t * pAnd, * pSum;
    char * pCube;
    int i, nFanins;

    // get the number of node's fanins
    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum(pSop) );
    // go through the cubes of the node's SOP
    pSum = Ivy_Not( Ivy_ManConst1(pMan) );
    Abc_SopForEachCube( pSop, nFanins, pCube )
    {
        // create the AND of literals
        pAnd = Ivy_ManConst1(pMan);
        Abc_ObjForEachFanin( pNode, pFanin, i ) // pFanin can be a net
        {
            if ( pCube[i] == '1' )
                pAnd = Ivy_And( pMan, pAnd, (Ivy_Obj_t *)pFanin->pCopy );
            else if ( pCube[i] == '0' )
                pAnd = Ivy_And( pMan, pAnd, Ivy_Not((Ivy_Obj_t *)pFanin->pCopy) );
        }
        // add to the sum of cubes
        pSum = Ivy_Or( pMan, pSum, pAnd );
    }
    // decide whether to complement the result
    if ( Abc_SopIsComplement(pSop) )
        pSum = Ivy_Not(pSum);
    return pSum;
}

/**Function*************************************************************

  Synopsis    [Strashed n-input XOR function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Abc_NodeStrashAigExorAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop )
{
    Abc_Obj_t * pFanin;
    Ivy_Obj_t * pSum;
    int i, nFanins;
    // get the number of node's fanins
    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum(pSop) );
    // go through the cubes of the node's SOP
    pSum = Ivy_Not( Ivy_ManConst1(pMan) );
    for ( i = 0; i < nFanins; i++ )
    {
        pFanin = Abc_ObjFanin( pNode, i );
        pSum = Ivy_Exor( pMan, pSum, (Ivy_Obj_t *)pFanin->pCopy );
    }
    if ( Abc_SopIsComplement(pSop) )
        pSum = Ivy_Not(pSum);
    return pSum;
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Abc_NodeStrashAigFactorAig( Ivy_Man_t * pMan, Abc_Obj_t * pRoot, char * pSop )
{
    Dec_Graph_t * pFForm;
    Dec_Node_t * pNode;
    Ivy_Obj_t * pAnd;
    int i;

//    extern Ivy_Obj_t * Dec_GraphToNetworkAig( Ivy_Man_t * pMan, Dec_Graph_t * pGraph );
    extern Ivy_Obj_t * Dec_GraphToNetworkIvy( Ivy_Man_t * pMan, Dec_Graph_t * pGraph );

//    assert( 0 );

    // perform factoring
    pFForm = Dec_Factor( pSop );
    // collect the fanins
    Dec_GraphForEachLeaf( pFForm, pNode, i )
        pNode->pFunc = Abc_ObjFanin(pRoot,i)->pCopy;
    // perform strashing
//    pAnd = Dec_GraphToNetworkAig( pMan, pFForm );
    pAnd = Dec_GraphToNetworkIvy( pMan, pFForm );
//    pAnd = NULL;

    Dec_GraphFree( pFForm );
    return pAnd;
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Abc_NtkCollectLatchValues( Abc_Ntk_t * pNtk, int fUseDcs )
{
    Abc_Obj_t * pLatch;
    int * pArray, i;
    pArray = ALLOC( int, Abc_NtkLatchNum(pNtk) );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        if ( fUseDcs || Abc_LatchIsInitDc(pLatch) )
            pArray[i] = IVY_INIT_DC;
        else if ( Abc_LatchIsInit1(pLatch) )
            pArray[i] = IVY_INIT_1;
        else if ( Abc_LatchIsInit0(pLatch) )
            pArray[i] = IVY_INIT_0;
        else assert( 0 );
    }
    return pArray;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


