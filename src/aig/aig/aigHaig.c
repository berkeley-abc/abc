/**CFile****************************************************************

  FileName    [aigHaig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigHaig.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"
#include "satSolver.h"
#include "cnf.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Aig_Obj_t *  Aig_HaigObjFrames( Aig_Obj_t ** ppMap, int nFrames, Aig_Obj_t * pObj, int f )                       { return ppMap[nFrames*pObj->Id + f];  }
static inline void         Aig_HaigObjSetFrames( Aig_Obj_t ** ppMap, int nFrames, Aig_Obj_t * pObj, int f, Aig_Obj_t * pNode ) { ppMap[nFrames*pObj->Id + f] = pNode; }
static inline Aig_Obj_t *  Aig_HaigObjChild0Frames( Aig_Obj_t ** ppMap, int nFrames, Aig_Obj_t * pObj, int i )                 { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin0(pObj)? Aig_NotCond(Aig_HaigObjFrames(ppMap,nFrames,Aig_ObjFanin0(pObj),i), Aig_ObjFaninC0(pObj)) : NULL;  }
static inline Aig_Obj_t *  Aig_HaigObjChild1Frames( Aig_Obj_t ** ppMap, int nFrames, Aig_Obj_t * pObj, int i )                 { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin1(pObj)? Aig_NotCond(Aig_HaigObjFrames(ppMap,nFrames,Aig_ObjFanin1(pObj),i), Aig_ObjFaninC1(pObj)) : NULL;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs speculative reduction for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Aig_ManHaigFramesNode( Aig_Obj_t ** ppMap, int nFrames, Aig_Man_t * pFrames, Aig_Obj_t * pObj, int iFrame )
{
    Aig_Obj_t * pObjNew, * pObjNew2, * pObjRepr, * pObjReprNew, * pMiter;
    // skip nodes without representative
    pObjRepr = pObj->pHaig;
    if ( pObjRepr == NULL )
        return;
    assert( !Aig_IsComplement(pObjRepr) );
    assert( pObjRepr->Id < pObj->Id );
    // get the new node 
    pObjNew = Aig_HaigObjFrames( ppMap, nFrames, pObj, iFrame );
    // get the new node of the representative
    pObjReprNew = Aig_HaigObjFrames( ppMap, nFrames, pObjRepr, iFrame );
    // if this is the same node, no need to add constraints
    if ( Aig_Regular(pObjNew) == Aig_Regular(pObjReprNew) )
        return;
    // these are different nodes - perform speculative reduction
    pObjNew2 = Aig_NotCond( pObjReprNew, pObj->fPhase ^ pObjRepr->fPhase );
    // set the new node
    Aig_HaigObjSetFrames( ppMap, nFrames, pObj, iFrame, pObjNew2 );
    // add the constraint
    pMiter = Aig_Exor( pFrames, Aig_Regular(pObjNew), Aig_Regular(pObjReprNew) );
    pMiter = Aig_NotCond( pMiter, Aig_Regular(pMiter)->fPhase ^ Aig_IsComplement(pMiter) );
    pMiter = Aig_Not( pMiter );
    Aig_ObjCreatePo( pFrames, pMiter );
}

/**Function*************************************************************

  Synopsis    [Prepares the inductive case with speculative reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManHaigFrames( Aig_Man_t * pHaig, int nFrames )
{
    Aig_Man_t * pFrames;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo, * pObjNew;
    Aig_Obj_t ** ppMap;
    int i, k, f;
    assert( nFrames >= 2 );
    assert( Aig_ManRegNum(pHaig) > 0 );
    assert( Aig_ManRegNum(pHaig) < Aig_ManPiNum(pHaig) );

    // create node mapping
    ppMap = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pHaig) * nFrames );
    memset( ppMap, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(pHaig) * nFrames );

    // start the frames
    pFrames = Aig_ManStart( Aig_ManObjNumMax(pHaig) * nFrames );
    pFrames->pName = Aig_UtilStrsav( pHaig->pName );
    pFrames->pSpec = Aig_UtilStrsav( pHaig->pSpec );
    pFrames->nRegs = pHaig->nRegs;

    // create PI nodes for the frames
    for ( f = 0; f < nFrames; f++ )
        Aig_HaigObjSetFrames( ppMap, nFrames, Aig_ManConst1(pHaig), f, Aig_ManConst1(pFrames) );
    for ( f = 0; f < nFrames; f++ )
        Aig_ManForEachPiSeq( pHaig, pObj, i )
            Aig_HaigObjSetFrames( ppMap, nFrames, pObj, f, Aig_ObjCreatePi(pFrames) );
    // create latches for the first frame
    Aig_ManForEachLoSeq( pHaig, pObj, i )
        Aig_HaigObjSetFrames( ppMap, nFrames, pObj, 0, Aig_ObjCreatePi(pFrames) );

    // add timeframes
    for ( f = 0; f < nFrames; f++ )
    {
        // mark the asserts
        if ( f == nFrames - 1 )
            pFrames->nAsserts = Aig_ManPoNum(pFrames);
        // constrain latch outputs and internal nodes
        Aig_ManForEachObj( pHaig, pObj, i )
        {
            if ( Aig_ObjIsPi(pObj) && Aig_HaigObjFrames(ppMap, nFrames, pObj, f) == NULL )
            {
                Aig_ManHaigFramesNode( ppMap, nFrames, pFrames, pObj, f );
            }
            else if ( Aig_ObjIsNode(pObj) )
            {
                pObjNew = Aig_And( pFrames, 
                    Aig_HaigObjChild0Frames(ppMap,nFrames,pObj,f), 
                    Aig_HaigObjChild1Frames(ppMap,nFrames,pObj,f) );
                Aig_HaigObjSetFrames( ppMap, nFrames, pObj, f, pObjNew );
                Aig_ManHaigFramesNode( ppMap, nFrames, pFrames, pObj, f );
            }
        }

/*
        // set the constraints on the latch outputs
        Aig_ManForEachLoSeq( pHaig, pObj, i )
            Aig_ManHaigFramesNode( ppMap, nFrames, pFrames, pObj, f );
        // add internal nodes of this frame
        Aig_ManForEachNode( pHaig, pObj, i )
        {
            pObjNew = Aig_And( pFrames, 
                Aig_HaigObjChild0Frames(ppMap,nFrames,pObj,f), 
                Aig_HaigObjChild1Frames(ppMap,nFrames,pObj,f) );
            Aig_HaigObjSetFrames( ppMap, nFrames, pObj, f, pObjNew );
            Aig_ManHaigFramesNode( ppMap, nFrames, pFrames, pObj, f );
        }
*/
        // transfer latch inputs to the latch outputs 
        Aig_ManForEachLiLoSeq( pHaig, pObjLi, pObjLo, k )
        {
            pObjNew = Aig_HaigObjChild0Frames(ppMap,nFrames,pObjLi,f);
            Aig_HaigObjSetFrames( ppMap, nFrames, pObjLo, f+1, pObjNew );
        }
    }

    // remove dangling nodes
    Aig_ManCleanup( pFrames );
    free( ppMap );
    return pFrames;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManHaigVerify( Aig_Man_t * pHaig )
{
    int nBTLimit = 0;
    Aig_Man_t * pFrames;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    Aig_Obj_t * pObj;
    int i, Lit, RetValue, Counter;
    int clk = clock();

    // create time frames with speculative reduction and convert them into CNF
clk = clock();
    pFrames = Aig_ManHaigFrames( pHaig, 2 );
    pCnf = Cnf_DeriveSimple( pFrames, Aig_ManPoNum(pFrames) - pFrames->nAsserts );
//    pCnf = Cnf_Derive( pFrames, Aig_ManPoNum(pFrames) - pFrames->nAsserts );
//Cnf_DataWriteIntoFile( pCnf, "temp.cnf", 1 );
    // create the SAT solver to be used for this problem
    pSat = Cnf_DataWriteIntoSolver( pCnf, 1, 0 );

    printf( "HAIG regs = %d. HAIG nodes = %d. Outputs = %d.\n", 
        Aig_ManRegNum(pHaig), Aig_ManNodeNum(pHaig), Aig_ManPoNum(pHaig) );
    printf( "Frames regs = %d. Frames nodes = %d. Outputs = %d. Assumptions = %d. Asserts = %d.\n", 
        Aig_ManRegNum(pFrames), Aig_ManNodeNum(pFrames), Aig_ManPoNum(pFrames), 
        pFrames->nAsserts, Aig_ManPoNum(pFrames) - pFrames->nAsserts );

PRT( "Preparation", clock() - clk );
    if ( pSat == NULL )
    {
        printf( "Aig_ManHaigVerify(): Computed CNF is not valid.\n" );
        return -1;
    }
    
    // solve each output
clk = clock();
    Counter = 0;
    Aig_ManForEachPo( pFrames, pObj, i )
    {
        if ( i < pFrames->nAsserts )
            continue;
        Lit = toLitCond( pCnf->pVarNums[pObj->Id], pObj->fPhase );
        RetValue = sat_solver_solve( pSat, &Lit, &Lit + 1, (sint64)nBTLimit, (sint64)0, (sint64)0, (sint64)0 );
        if ( RetValue != l_False )
            Counter++;
    }
PRT( "Solving    ", clock() - clk );
    if ( Counter )
        printf( "Verification failed for %d classes.\n", Counter );
    else
        printf( "Verification is successful.\n" );

    // clean up
    Aig_ManStop( pFrames );
    Cnf_DataFree( pCnf );
    sat_solver_delete( pSat );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManHaigRecord( Aig_Man_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // start the HAIG
    p->pManHaig = Aig_ManDup( p, 1 );
    // set the pointers to the HAIG nodes
    Aig_ManForEachObj( p, pObj, i )
        pObj->pHaig = pObj->pData;
    // remove structural hashing table
    Aig_TableClear( p->pManHaig );
    // perform a sequence of synthesis steps
    pNew = Aig_ManRetimeFrontier( p, 10000 );
    // use the haig for verification
    Aig_ManDumpBlif( pNew->pManHaig, "haig_temp.blif" );
    Aig_ManHaigVerify( pNew->pManHaig );
    Aig_ManStop( pNew );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


