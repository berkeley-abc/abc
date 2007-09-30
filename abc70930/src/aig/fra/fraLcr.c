/**CFile****************************************************************

  FileName    [fraLcorr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    [Latch correspondence computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraLcorr.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Fra_Lcr_t_    Fra_Lcr_t;
struct Fra_Lcr_t_
{
    // original AIG
    Aig_Man_t *      pAig;
    // equivalence class representation
    Fra_Cla_t *      pCla;       
    // partitioning information
    Vec_Ptr_t *      vParts;        // output partitions
    int *            pInToOutPart;  // mapping of PI num into PO partition num
    int *            pInToOutNum;   // mapping of PI num into the num of this PO in the partition
    // AIGs for the partitions
    Vec_Ptr_t *      vFraigs;
    // other variables
    int              fRefining; 
    // parameters
    int              nFramesP;
    int              fVerbose;
    // statistics
    int              nIters;
    int              nLitsBeg;
    int              nLitsEnd;
    int              nNodesBeg;
    int              nNodesEnd;
    int              nRegsBeg;
    int              nRegsEnd;
    // runtime
    int              timeSim;
    int              timePart;
    int              timeTrav;
    int              timeFraig;
    int              timeUpdate;
    int              timeTotal;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the retiming manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fra_Lcr_t * Lcr_ManAlloc( Aig_Man_t * pAig )
{
    Fra_Lcr_t * p;
    p = ALLOC( Fra_Lcr_t, 1 );
    memset( p, 0, sizeof(Fra_Lcr_t) );
    p->pAig = pAig;
    p->pInToOutPart = ALLOC( int, Aig_ManPiNum(pAig) );
    memset( p->pInToOutPart, 0, sizeof(int) * Aig_ManPiNum(pAig) );
    p->pInToOutNum = ALLOC( int, Aig_ManPiNum(pAig) );
    memset( p->pInToOutNum, 0, sizeof(int) * Aig_ManPiNum(pAig) );
    p->vFraigs = Vec_PtrAlloc( 1000 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Prints stats for the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lcr_ManPrint( Fra_Lcr_t * p )
{
    printf( "Iterations = %d.  LitBeg = %d.  LitEnd = %d. (%6.2f %%).\n", 
        p->nIters, p->nLitsBeg, p->nLitsEnd, 100.0*p->nLitsEnd/p->nLitsBeg );
    printf( "NBeg = %d. NEnd = %d. (Gain = %6.2f %%).  RBeg = %d. REnd = %d. (Gain = %6.2f %%).\n", 
        p->nNodesBeg, p->nNodesEnd, 100.0*(p->nNodesBeg-p->nNodesEnd)/p->nNodesBeg, 
        p->nRegsBeg, p->nRegsEnd, 100.0*(p->nRegsBeg-p->nRegsEnd)/p->nRegsBeg );
    PRT( "AIG simulation  ", p->timeSim  );
    PRT( "AIG partitioning", p->timePart );
    PRT( "AIG rebuiding   ", p->timeTrav );
    PRT( "FRAIGing        ", p->timeFraig );
    PRT( "AIG updating    ", p->timeUpdate );
    PRT( "TOTAL RUNTIME   ", p->timeTotal );
}

/**Function*************************************************************

  Synopsis    [Deallocates the retiming manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lcr_ManFree( Fra_Lcr_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    if ( p->fVerbose )
        Lcr_ManPrint( p );
    Aig_ManForEachPi( p->pAig, pObj, i )
        pObj->pNext = NULL;
    Vec_PtrFree( p->vFraigs );
    if ( p->pCla  )     Fra_ClassesStop( p->pCla );
    if ( p->vParts  )   Vec_VecFree( (Vec_Vec_t *)p->vParts );
    free( p->pInToOutPart );
    free( p->pInToOutNum );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Prepare the AIG for class computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fra_Man_t * Fra_LcrAigPrepare( Aig_Man_t * pAig )
{
    Fra_Man_t * p;
    Aig_Obj_t * pObj;
    int i;
    p = ALLOC( Fra_Man_t, 1 );
    memset( p, 0, sizeof(Fra_Man_t) );
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->pData = p;
    return p;
}

/**Function*************************************************************

  Synopsis    [Prepare the AIG for class computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_LcrAigPrepareTwo( Aig_Man_t * pAig, Fra_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->pData = p;
}

/**Function*************************************************************

  Synopsis    [Compares two nodes for equivalence after partitioned fraiging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_LcrNodesAreEqual( Aig_Obj_t * pObj0, Aig_Obj_t * pObj1 )
{
    Fra_Man_t * pTemp = pObj0->pData;
    Fra_Lcr_t * pLcr = (Fra_Lcr_t *)pTemp->pBmc;
    Aig_Man_t * pFraig;
    Aig_Obj_t * pOut0, * pOut1;
    int nPart0, nPart1;
    assert( Aig_ObjIsPi(pObj0) );
    assert( Aig_ObjIsPi(pObj1) );
    // find the partition to which these nodes belong
    nPart0 = pLcr->pInToOutPart[(int)pObj0->pNext];
    nPart1 = pLcr->pInToOutPart[(int)pObj1->pNext];
    // if this is the result of refinement of the class created const-1 nodes
    // the nodes may end up in different partions - we assume them equivalent
    if ( nPart0 != nPart1 )
    {
        assert( 0 );
        return 1;
    }
    assert( nPart0 == nPart1 );
    pFraig = Vec_PtrEntry( pLcr->vFraigs, nPart0 );
    // get the fraig outputs
    pOut0 = Aig_ManPo( pFraig, pLcr->pInToOutNum[(int)pObj0->pNext] );
    pOut1 = Aig_ManPo( pFraig, pLcr->pInToOutNum[(int)pObj1->pNext] );
    return Aig_ObjFanin0(pOut0) == Aig_ObjFanin0(pOut1);
}

/**Function*************************************************************

  Synopsis    [Compares the node with a constant after partioned fraiging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_LcrNodeIsConst( Aig_Obj_t * pObj )
{
    Fra_Man_t * pTemp = pObj->pData;
    Fra_Lcr_t * pLcr = (Fra_Lcr_t *)pTemp->pBmc;
    Aig_Man_t * pFraig;
    Aig_Obj_t * pOut;
    int nPart;
    assert( Aig_ObjIsPi(pObj) );
    // find the partition to which these nodes belong
    nPart = pLcr->pInToOutPart[(int)pObj->pNext];
    pFraig = Vec_PtrEntry( pLcr->vFraigs, nPart );
    // get the fraig outputs
    pOut = Aig_ManPo( pFraig, pLcr->pInToOutNum[(int)pObj->pNext] );
    return Aig_ObjFanin0(pOut) == Aig_ManConst1(pFraig);
}

/**Function*************************************************************

  Synopsis    [Give the AIG and classes, reduces AIG for partitioning.]

  Description [Ignores registers that are not in the classes. 
  Places candidate equivalent classes of registers into single outputs 
  (for ease of partitioning). The resulting combinational AIG contains 
  outputs in the same order as equivalence classes of registers, 
  followed by constant-1 registers. Preserves the set of all inputs.
  Complemented attributes of the outputs do not matter because we need 
  then only for collecting the structural info.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_LcrDeriveAigForPartitioning( Fra_Lcr_t * pLcr )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjPo, * pObjNew, ** ppClass, * pMiter;
    int i, c, Offset;
    // remember the numbers of the inputs of the original AIG
    Aig_ManForEachPi( pLcr->pAig, pObj, i )
    {
        pObj->pData = pLcr;
        pObj->pNext = (Aig_Obj_t *)i;
    }
    // compute the LO/LI offset
    Offset = Aig_ManPoNum(pLcr->pAig) - Aig_ManPiNum(pLcr->pAig);
    // create the PIs
    Aig_ManCleanData( pLcr->pAig );
    pNew = Aig_ManStartFrom( pLcr->pAig );
    // go over the equivalence classes
    Vec_PtrForEachEntry( pLcr->pCla->vClasses, ppClass, i )
    {
        pMiter = Aig_ManConst0(pNew);
        for ( c = 0; ppClass[c]; c++ )
        {
            assert( Aig_ObjIsPi(ppClass[c]) );
            pObjPo  = Aig_ManPo( pLcr->pAig, Offset+(int)ppClass[c]->pNext );
            pObjNew = Aig_ManDup_rec( pNew, pLcr->pAig, Aig_ObjFanin0(pObjPo) );
            pMiter  = Aig_Exor( pNew, pMiter, pObjNew );
        }
        Aig_ObjCreatePo( pNew, pMiter );
    }
    // go over the constant candidates
    Vec_PtrForEachEntry( pLcr->pCla->vClasses1, pObj, i )
    {
        assert( Aig_ObjIsPi(pObj) );
        pObjPo = Aig_ManPo( pLcr->pAig, Offset+(int)pObj->pNext );
        pMiter = Aig_ManDup_rec( pNew, pLcr->pAig, Aig_ObjFanin0(pObjPo) );
        Aig_ObjCreatePo( pNew, pMiter );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Remaps partitions into the inputs of original AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_LcrRemapPartitions( Vec_Ptr_t * vParts, Fra_Cla_t * pCla, int * pInToOutPart, int * pInToOutNum )
{
    Vec_Int_t * vOne, * vOneNew;
    Aig_Obj_t ** ppClass, * pObjPi;
    int Out, Offset, i, k, c;
    // compute the LO/LI offset
    Offset = Aig_ManPoNum(pCla->pAig) - Aig_ManPiNum(pCla->pAig);
    Vec_PtrForEachEntry( vParts, vOne, i )
    {
        vOneNew = Vec_IntAlloc( Vec_IntSize(vOne) );
        Vec_IntForEachEntry( vOne, Out, k )
        {
            if ( Out < Vec_PtrSize(pCla->vClasses) )
            {
                ppClass = Vec_PtrEntry( pCla->vClasses, Out );
                for ( c = 0; ppClass[c]; c++ )
                {
                    pInToOutPart[(int)ppClass[c]->pNext] = i;
                    pInToOutNum[(int)ppClass[c]->pNext] = Vec_IntSize(vOneNew);
                    Vec_IntPush( vOneNew, Offset+(int)ppClass[c]->pNext );
                }
            }
            else
            {
                pObjPi = Vec_PtrEntry( pCla->vClasses1, Out - Vec_PtrSize(pCla->vClasses) );
                pInToOutPart[(int)pObjPi->pNext] = i;
                pInToOutNum[(int)pObjPi->pNext] = Vec_IntSize(vOneNew);
                Vec_IntPush( vOneNew, Offset+(int)pObjPi->pNext );
            }
        }
        // replace the class
        Vec_PtrWriteEntry( vParts, i, vOneNew );
        Vec_IntFree( vOne );
    }
}

/**Function*************************************************************

  Synopsis    [Creates AIG of one partition with speculative reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Fra_LcrCreatePart_rec( Fra_Cla_t * pCla, Aig_Man_t * pNew, Aig_Man_t * p, Aig_Obj_t * pObj )
{
    assert( !Aig_IsComplement(pObj) );
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return pObj->pData;
    Aig_ObjSetTravIdCurrent(p, pObj);
    if ( Aig_ObjIsPi(pObj) )
    {
//        Aig_Obj_t * pRepr = Fra_ClassObjRepr(pObj);
        Aig_Obj_t * pRepr = pCla->pMemRepr[pObj->Id];
        if ( pRepr == NULL )
            pObj->pData = Aig_ObjCreatePi( pNew );
        else
        {
            pObj->pData = Fra_LcrCreatePart_rec( pCla, pNew, p, pRepr );
            pObj->pData = Aig_NotCond( pObj->pData, pRepr->fPhase ^ pObj->fPhase );
        }
        return pObj->pData;
    }
    Fra_LcrCreatePart_rec( pCla, pNew, p, Aig_ObjFanin0(pObj) );
    Fra_LcrCreatePart_rec( pCla, pNew, p, Aig_ObjFanin1(pObj) );
    return pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Creates AIG of one partition with speculative reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_LcrCreatePart( Fra_Lcr_t * p, Vec_Int_t * vPart )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int Out, i;
    // create new AIG for this partition
    pNew = Aig_ManStartFrom( p->pAig );
    Aig_ManIncrementTravId( p->pAig );
    Aig_ObjSetTravIdCurrent( p->pAig, Aig_ManConst1(p->pAig) );
    Aig_ManConst1(p->pAig)->pData = Aig_ManConst1(pNew);
    Vec_IntForEachEntry( vPart, Out, i )
    {
        pObj = Aig_ManPo( p->pAig, Out );
        if ( pObj->fMarkA )
        {
            pObjNew = Fra_LcrCreatePart_rec( p->pCla, pNew, p->pAig, Aig_ObjFanin0(pObj) );
            pObjNew = Aig_NotCond( pObjNew, Aig_ObjFaninC0(pObj) );
        }
        else
            pObjNew = Aig_ManConst1( pNew );
        Aig_ObjCreatePo( pNew, pObjNew ); 
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Marks the nodes belonging to the equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ClassNodesMark( Fra_Lcr_t * p )
{
    Aig_Obj_t * pObj, ** ppClass;
    int i, c, Offset;
    // compute the LO/LI offset
    Offset = Aig_ManPoNum(p->pCla->pAig) - Aig_ManPiNum(p->pCla->pAig);
    // mark the nodes remaining in the classes
    Vec_PtrForEachEntry( p->pCla->vClasses1, pObj, i )
    {
        pObj = Aig_ManPo( p->pCla->pAig, Offset+(int)pObj->pNext );
        pObj->fMarkA = 1;
    }
    Vec_PtrForEachEntry( p->pCla->vClasses, ppClass, i )
    {
        for ( c = 0; ppClass[c]; c++ )
        {
            pObj = Aig_ManPo( p->pCla->pAig, Offset+(int)ppClass[c]->pNext );
            pObj->fMarkA = 1;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Unmarks the nodes belonging to the equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_ClassNodesUnmark( Fra_Lcr_t * p )
{
    Aig_Obj_t * pObj, ** ppClass;
    int i, c, Offset;
    // compute the LO/LI offset
    Offset = Aig_ManPoNum(p->pCla->pAig) - Aig_ManPiNum(p->pCla->pAig);
    // mark the nodes remaining in the classes
    Vec_PtrForEachEntry( p->pCla->vClasses1, pObj, i )
    {
        pObj = Aig_ManPo( p->pCla->pAig, Offset+(int)pObj->pNext );
        pObj->fMarkA = 0;
    }
    Vec_PtrForEachEntry( p->pCla->vClasses, ppClass, i )
    {
        for ( c = 0; ppClass[c]; c++ )
        {
            pObj = Aig_ManPo( p->pCla->pAig, Offset+(int)ppClass[c]->pNext );
            pObj->fMarkA = 0;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Performs choicing of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_FraigLatchCorrespondence( Aig_Man_t * pAig, int nFramesP, int nConfMax, int fProve, int fVerbose, int * pnIter )
{
    int nPartSize    = 200;
    int fReprSelect  = 0;

    Fra_Lcr_t * p;
    Fra_Sml_t * pSml;
    Fra_Man_t * pTemp;
    Aig_Man_t * pAigPart, * pAigNew = NULL;
    Vec_Int_t * vPart;
//    Aig_Obj_t * pObj = Aig_ManObj(pAig, 2078);
    int i, nIter, timeSim, clk = clock(), clk2, clk3;
    if ( Aig_ManNodeNum(pAig) == 0 )
    {
        if ( pnIter ) *pnIter = 0;
        return Aig_ManDup(pAig, 1);
    }
    assert( Aig_ManLatchNum(pAig) == 0 );
    assert( Aig_ManRegNum(pAig) > 0 );

    // simulate the AIG 
clk2 = clock();
if ( fVerbose )
printf( "Simulating AIG with %d nodes for %d cycles ...  ", Aig_ManNodeNum(pAig), nFramesP + 32 );
    pSml = Fra_SmlSimulateSeq( pAig, nFramesP, 32, 1 ); 
if ( fVerbose ) 
{
PRT( "Time", clock() - clk2 );
timeSim = clock() - clk2;
}
    // check if simulation discovered non-constant-0 POs
    if ( fProve && pSml->fNonConstOut )
    {
        Fra_SmlStop( pSml );
        return NULL;
    }

    // start the manager
    p = Lcr_ManAlloc( pAig );
    p->nFramesP = nFramesP;
    p->fVerbose = fVerbose;
    p->timeSim += timeSim;

    pTemp = Fra_LcrAigPrepare( pAig );
    pTemp->pBmc = (Fra_Bmc_t *)p;
    pTemp->pSml = pSml;

    // get preliminary info about equivalence classes
    pTemp->pCla = p->pCla = Fra_ClassesStart( p->pAig );
    Fra_ClassesPrepare( p->pCla, 1 );
    p->pCla->pFuncNodeIsConst   = Fra_LcrNodeIsConst;
    p->pCla->pFuncNodesAreEqual = Fra_LcrNodesAreEqual;
    Fra_SmlStop( pTemp->pSml );

    // partition the AIG for latch correspondence computation
clk2 = clock();
if ( fVerbose )
printf( "Partitioning AIG ...  " );
    pAigPart = Fra_LcrDeriveAigForPartitioning( p );
    p->vParts = (Vec_Ptr_t *)Aig_ManPartitionSmart( pAigPart, nPartSize, 0, NULL );
    Fra_LcrRemapPartitions( p->vParts, p->pCla, p->pInToOutPart, p->pInToOutNum );
    Aig_ManStop( pAigPart );
if ( fVerbose ) 
{
PRT( "Time", clock() - clk2 );
p->timePart += clock() - clk2;
}

    // get the initial stats
    p->nLitsBeg  = Fra_ClassesCountLits( p->pCla );
    p->nNodesBeg = Aig_ManNodeNum(p->pAig);
    p->nRegsBeg  = Aig_ManRegNum(p->pAig);

    // perforn interative reduction of the partitions
    p->fRefining = 1;
    for ( nIter = 0; p->fRefining; nIter++ )
    {
        p->fRefining = 0;
        clk3 = clock();
        // derive AIGs for each partition
        Fra_ClassNodesMark( p );
        Vec_PtrClear( p->vFraigs );
        Vec_PtrForEachEntry( p->vParts, vPart, i )
        {
clk2 = clock();
            pAigPart = Fra_LcrCreatePart( p, vPart );
p->timeTrav += clock() - clk2;
clk2 = clock();
            pAigNew  = Fra_FraigEquivence( pAigPart, nConfMax );
p->timeFraig += clock() - clk2;
            Vec_PtrPush( p->vFraigs, pAigNew );
            Aig_ManStop( pAigPart );
        }
        Fra_ClassNodesUnmark( p );
        // report the intermediate results
        if ( fVerbose )
        {
            printf( "%3d : Const = %6d. Class = %6d.  L = %6d. Part = %3d.  ", 
                nIter, Vec_PtrSize(p->pCla->vClasses1), Vec_PtrSize(p->pCla->vClasses), 
                Fra_ClassesCountLits(p->pCla), Vec_PtrSize(p->vParts) );
            PRT( "T", clock() - clk3 );
        }
        // refine the classes
        Fra_LcrAigPrepareTwo( p->pAig, pTemp );
        if ( Fra_ClassesRefine( p->pCla ) )
            p->fRefining = 1;
        if ( Fra_ClassesRefine1( p->pCla, 0, NULL ) )
            p->fRefining = 1;
        // clean the fraigs
        Vec_PtrForEachEntry( p->vFraigs, pAigPart, i )
            Aig_ManStop( pAigPart );

        // repartition if needed
        if ( 1 )
        {
clk2 = clock();
            Vec_VecFree( (Vec_Vec_t *)p->vParts );
            pAigPart = Fra_LcrDeriveAigForPartitioning( p );
            p->vParts = (Vec_Ptr_t *)Aig_ManPartitionSmart( pAigPart, nPartSize, 0, NULL );
            Fra_LcrRemapPartitions( p->vParts, p->pCla, p->pInToOutPart, p->pInToOutNum );
            Aig_ManStop( pAigPart );
p->timePart += clock() - clk2;
        }
    }
    free( pTemp );
    p->nIters = nIter;

    // move the classes into representatives and reduce AIG
clk2 = clock();
//    Fra_ClassesPrint( p->pCla, 1 );
    if ( fReprSelect )
        Fra_ClassesSelectRepr( p->pCla );
    Fra_ClassesCopyReprs( p->pCla, NULL );
    pAigNew = Aig_ManDupRepr( p->pAig, 0 );
    Aig_ManSeqCleanup( pAigNew );
//    Aig_ManCountMergeRegs( pAigNew );
p->timeUpdate += clock() - clk2;
p->timeTotal = clock() - clk;
    // get the final stats
    p->nLitsEnd  = Fra_ClassesCountLits( p->pCla );
    p->nNodesEnd = Aig_ManNodeNum(pAigNew);
    p->nRegsEnd  = Aig_ManRegNum(pAigNew);
    Lcr_ManFree( p );
    if ( pnIter ) *pnIter = nIter;
    return pAigNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


