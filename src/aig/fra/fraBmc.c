/**CFile****************************************************************

  FileName    [fraBmc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    [Bounded model checking.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraBmc.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// simulation manager
struct Fra_Bmc_t_
{
    // parameters
    int              nPref;             // the size of the prefix
    int              nDepth;            // the depth of the frames
    int              nFramesAll;        // the total number of timeframes
    // AIG managers
    Aig_Man_t *      pAig;              // the original AIG manager
    Aig_Man_t *      pAigFrames;        // initialized timeframes
    Aig_Man_t *      pAigFraig;         // the fraiged initialized timeframes
    // mapping of nodes
    Aig_Obj_t **     pObjToFrames;      // mapping of the original node into frames
    Aig_Obj_t **     pObjToFraig;       // mapping of the frames node into fraig
};

static inline Aig_Obj_t *  Bmc_ObjFrames( Aig_Obj_t * pObj, int i )                       { return ((Fra_Man_t *)pObj->pData)->pBmc->pObjToFrames[((Fra_Man_t *)pObj->pData)->pBmc->nFramesAll*pObj->Id + i];  }
static inline void         Bmc_ObjSetFrames( Aig_Obj_t * pObj, int i, Aig_Obj_t * pNode ) { ((Fra_Man_t *)pObj->pData)->pBmc->pObjToFrames[((Fra_Man_t *)pObj->pData)->pBmc->nFramesAll*pObj->Id + i] = pNode; }

static inline Aig_Obj_t *  Bmc_ObjFraig( Aig_Obj_t * pObj )                               { return ((Fra_Man_t *)pObj->pData)->pBmc->pObjToFraig[pObj->Id];  }
static inline void         Bmc_ObjSetFraig( Aig_Obj_t * pObj, Aig_Obj_t * pNode )         { ((Fra_Man_t *)pObj->pData)->pBmc->pObjToFraig[pObj->Id] = pNode; }

static inline Aig_Obj_t *  Bmc_ObjChild0Frames( Aig_Obj_t * pObj, int i ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin0(pObj)? Aig_NotCond(Bmc_ObjFrames(Aig_ObjFanin0(pObj),i), Aig_ObjFaninC0(pObj)) : NULL;  }
static inline Aig_Obj_t *  Bmc_ObjChild1Frames( Aig_Obj_t * pObj, int i ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin1(pObj)? Aig_NotCond(Bmc_ObjFrames(Aig_ObjFanin1(pObj),i), Aig_ObjFaninC1(pObj)) : NULL;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if the nodes are equivalent.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_BmcNodesAreEqual( Aig_Obj_t * pObj0, Aig_Obj_t * pObj1 )
{
    Fra_Man_t * p = pObj0->pData;
//    Aig_Obj_t ** ppNodes = p->pBmc->pObjToFraig;
    Aig_Obj_t * pObjFrames0, * pObjFrames1;
    Aig_Obj_t * pObjFraig0, * pObjFraig1;
    int i;
    for ( i = p->pBmc->nPref; i < p->pBmc->nFramesAll; i++ )
    {
        pObjFrames0 = Aig_Regular( Bmc_ObjFrames(pObj0, i) );
        pObjFrames1 = Aig_Regular( Bmc_ObjFrames(pObj1, i) );
        if ( pObjFrames0 == pObjFrames1 )
            continue;
        pObjFraig0 = Aig_Regular( Bmc_ObjFraig(pObjFrames0) );
        pObjFraig1 = Aig_Regular( Bmc_ObjFraig(pObjFrames1) );
        if ( pObjFraig0 != pObjFraig1 )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node is costant.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fra_BmcNodeIsConst( Aig_Obj_t * pObj )
{
    Fra_Man_t * p = pObj->pData;
    return Fra_BmcNodesAreEqual( pObj, Aig_ManConst1(p->pManAig) );
}


/**Function*************************************************************

  Synopsis    [Starts the BMC manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fra_Bmc_t * Fra_BmcStart( Aig_Man_t * pAig, int nPref, int nDepth )
{
    Fra_Bmc_t * p;
    p = ALLOC( Fra_Bmc_t, 1 );
    memset( p, 0, sizeof(Fra_Bmc_t) );
    p->pAig = pAig;
    p->nPref = nPref;
    p->nDepth = nDepth;
    p->nFramesAll = nPref + nDepth;
    p->pObjToFrames  = ALLOC( Aig_Obj_t *, p->nFramesAll * (Aig_ManObjIdMax(pAig) + 1) );
    memset( p->pObjToFrames, 0, sizeof(Aig_Obj_t *) * p->nFramesAll * (Aig_ManObjIdMax(pAig) + 1) );
//    p->pObjToFraig  = ALLOC( Aig_Obj_t *, p->nFramesAll * (Aig_ManObjIdMax(pAig) + 1) );
//    memset( p->pObjToFraig, 0, sizeof(Aig_Obj_t *) * p->nFramesAll * (Aig_ManObjIdMax(pAig) + 1) );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the BMC manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_BmcStop( Fra_Bmc_t * p )
{
    Aig_ManStop( p->pAigFrames );
    Aig_ManStop( p->pAigFraig );
    free( p->pObjToFrames );
    free( p->pObjToFraig );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Constructs initialized timeframes of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_BmcFrames( Fra_Bmc_t * p )
{
    Aig_Man_t * pAigFrames;
    Aig_Obj_t * pObj, * pObjNew;
    Aig_Obj_t ** pLatches;
    int i, k, f;

    // start the fraig package
    pAigFrames = Aig_ManStart( (Aig_ManObjIdMax(p->pAig) + 1) * p->nFramesAll );
    // create PI nodes for the frames
    for ( f = 0; f < p->nFramesAll; f++ )
        Bmc_ObjSetFrames( Aig_ManConst1(p->pAig), f, Aig_ManConst1(pAigFrames) );
    for ( f = 0; f < p->nFramesAll; f++ )
        Aig_ManForEachPiSeq( p->pAig, pObj, i )
            Bmc_ObjSetFrames( pObj, f, Aig_ObjCreatePi(pAigFrames) );
    // set initial state for the latches
    Aig_ManForEachLoSeq( p->pAig, pObj, i )
        Bmc_ObjSetFrames( pObj, 0, Aig_ManConst0(pAigFrames) );

    // add timeframes
    pLatches = ALLOC( Aig_Obj_t *, Aig_ManRegNum(p->pAig) );
    for ( f = 0; f < p->nFramesAll; f++ )
    {
        // add internal nodes of this frame
        Aig_ManForEachNode( p->pAig, pObj, i )
        {
            pObjNew = Aig_And( pAigFrames, Bmc_ObjChild0Frames(pObj,f), Bmc_ObjChild1Frames(pObj,f) );
            Bmc_ObjSetFrames( pObj, f, pObjNew );
        }
        if ( f == p->nFramesAll - 1 )
            break;
        // save the latch input values
        k = 0;
        Aig_ManForEachLiSeq( p->pAig, pObj, i )
            pLatches[k++] = Bmc_ObjChild0Frames(pObj,f);
        assert( k == Aig_ManRegNum(p->pAig) );
        // insert them to the latch output values
        k = 0;
        Aig_ManForEachLoSeq( p->pAig, pObj, i )
            Bmc_ObjSetFrames( pObj, f+1, pLatches[k++] );
        assert( k == Aig_ManRegNum(p->pAig) );
    }
    free( pLatches );
    // add POs to all the dangling nodes
    Aig_ManForEachObj( pAigFrames, pObjNew, i )
        if ( Aig_ObjIsNode(pObjNew) && pObjNew->nRefs == 0 )
            Aig_ObjCreatePo( pAigFrames, pObjNew );

    // return the new manager
    return pAigFrames;
}

/**Function*************************************************************

  Synopsis    [Constructs FRAIG manager for the initialized timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_BmcFraig( Fra_Bmc_t * p )
{
    Aig_Man_t * pFraig;
    Fra_Par_t Pars, * pPars = &Pars; 
    Fra_ParamsDefault( pPars );
    pPars->nBTLimitNode = 100000;
    pPars->fVerbose     = 0;
    pPars->fProve       = 0;
    pPars->fDoSparse    = 1;
    pPars->fSpeculate   = 0;
    pPars->fChoicing    = 0;
    pFraig = Fra_FraigPerform( p->pAigFrames, pPars );
    p->pObjToFraig = p->pAigFrames->pObjCopies;
    p->pAigFrames->pObjCopies = NULL;
    return pFraig;
} 

/**Function*************************************************************

  Synopsis    [Performs BMC for the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_BmcPerform( Fra_Man_t * p, int nPref, int nDepth )
{
    Aig_Obj_t * pObj;
    int i, clk = clock();
    assert( p->pBmc == NULL );
    // derive and fraig the frames
    p->pBmc = Fra_BmcStart( p->pManAig, nPref, nDepth );
    p->pBmc->pAigFrames = Fra_BmcFrames( p->pBmc );
    p->pBmc->pAigFraig = Fra_BmcFraig( p->pBmc );
    // annotate frames nodes with pointers to the manager
    Aig_ManForEachObj( p->pBmc->pAigFrames, pObj, i )
        pObj->pData = p;
    // report the results
    if ( p->pPars->fVerbose )
    {
        printf( "Original AIG = %d. Init %d frames = %d. Fraig = %d.  ", 
            Aig_ManNodeNum(p->pBmc->pAig), p->pBmc->nFramesAll, 
            Aig_ManNodeNum(p->pBmc->pAigFrames), Aig_ManNodeNum(p->pBmc->pAigFraig) );
        PRT( "Time", clock() - clk );
        printf( "Before BMC: " );  Fra_ClassesPrint( p->pCla, 0 );
    }
    // refine the classes
    p->pCla->pFuncNodeIsConst   = Fra_BmcNodeIsConst;
    p->pCla->pFuncNodesAreEqual = Fra_BmcNodesAreEqual;
    Fra_ClassesRefine( p->pCla );
    Fra_ClassesRefine1( p->pCla );
    p->pCla->pFuncNodeIsConst   = Fra_SmlNodeIsConst;
    p->pCla->pFuncNodesAreEqual = Fra_SmlNodesAreEqual;
    // report the results
    if ( p->pPars->fVerbose )
    {
        printf( "After  BMC: " );  Fra_ClassesPrint( p->pCla, 0 );
    }
    // free the BMC manager
    Fra_BmcStop( p->pBmc );  
    p->pBmc = NULL;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


