/**CFile****************************************************************

  FileName    [mfxCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Core procedures of this package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfxCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfxInt.h"
#include "bar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void Mfx_ParsDefault( Mfx_Par_t * pPars )
{
    pPars->nWinTfoLevs  =    2;
    pPars->nFanoutsMax  =   10;
    pPars->nDepthMax    =   20;
    pPars->nDivMax      =  250;
    pPars->nWinSizeMax  =  300;
    pPars->nGrowthLevel =    0;
    pPars->nBTLimit     = 5000;
    pPars->fResub       =    1;
    pPars->fArea        =    0;
    pPars->fMoreEffort  =    0;
    pPars->fSwapEdge    =    0;
    pPars->fVerbose     =    0;
    pPars->fVeryVerbose =    0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_Resub( Mfx_Man_t * p, Nwk_Obj_t * pNode )
{
    int clk;
    p->nNodesTried++;
    // prepare data structure for this node
    Mfx_ManClean( p ); 
    // compute window roots, window support, and window nodes
clk = clock();
    p->vRoots = Mfx_ComputeRoots( pNode, p->pPars->nWinTfoLevs, p->pPars->nFanoutsMax );
    p->vSupp  = Nwk_ManSupportNodes( p->pNtk, (Nwk_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
    p->vNodes = Nwk_ManDfsNodes( p->pNtk, (Nwk_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
p->timeWin += clock() - clk;
    if ( p->pPars->nWinSizeMax && Vec_PtrSize(p->vNodes) > p->pPars->nWinSizeMax )
        return 1;
    // compute the divisors of the window
clk = clock();
    p->vDivs  = Mfx_ComputeDivisors( p, pNode, Nwk_ObjRequired(pNode) - If_LutLibSlowestPinDelay(pNode->pMan->pLutLib) );
//    p->vDivs  = Mfx_ComputeDivisors( p, pNode, AIG_INFINITY );
    p->nTotalDivs += Vec_PtrSize(p->vDivs);
p->timeDiv += clock() - clk;
    // construct AIG for the window
clk = clock();
    p->pAigWin = Mfx_ConstructAig( p, pNode );
p->timeAig += clock() - clk;
    // translate it into CNF
clk = clock();
    p->pCnf = Cnf_DeriveSimple( p->pAigWin, 1 + Vec_PtrSize(p->vDivs) );
p->timeCnf += clock() - clk;
    // create the SAT problem
clk = clock();
    p->pSat = Mfx_CreateSolverResub( p, NULL, 0, 0 );
    if ( p->pSat == NULL )
    {
        p->nNodesBad++;
        return 1;
    }
    // solve the SAT problem
    if ( p->pPars->fSwapEdge )
        Mfx_EdgeSwapEval( p, pNode );
    else
    {
        Mfx_ResubNode( p, pNode );
        if ( p->pPars->fMoreEffort )
            Mfx_ResubNode2( p, pNode );
    }
p->timeSat += clock() - clk;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_Node( Mfx_Man_t * p, Nwk_Obj_t * pNode )
{
    Hop_Obj_t * pObj;
    int RetValue;

    int nGain, clk;
    p->nNodesTried++;
    // prepare data structure for this node
    Mfx_ManClean( p );
    // compute window roots, window support, and window nodes
clk = clock();
    p->vRoots = Mfx_ComputeRoots( pNode, p->pPars->nWinTfoLevs, p->pPars->nFanoutsMax );
    p->vSupp  = Nwk_ManSupportNodes( p->pNtk, (Nwk_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
    p->vNodes = Nwk_ManDfsNodes( p->pNtk, (Nwk_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
p->timeWin += clock() - clk;
    // count the number of patterns
//    p->dTotalRatios += Mfx_ConstraintRatio( p, pNode );
    // construct AIG for the window
clk = clock();
    p->pAigWin = Mfx_ConstructAig( p, pNode );
p->timeAig += clock() - clk;
    // translate it into CNF
clk = clock();
    p->pCnf = Cnf_DeriveSimple( p->pAigWin, Nwk_ObjFaninNum(pNode) );
p->timeCnf += clock() - clk;
    // create the SAT problem
clk = clock();
    p->pSat = Cnf_DataWriteIntoSolver( p->pCnf, 1, 0 );
    if ( p->pSat == NULL )
        return 0;
    // solve the SAT problem
    RetValue = Mfx_SolveSat( p, pNode );
    p->nTotConfLevel += p->pSat->stats.conflicts;
p->timeSat += clock() - clk;
    if ( RetValue == 0 )
    {
        p->nTimeOutsLevel++;
        p->nTimeOuts++;
        return 0;
    }
    // minimize the local function of the node using bi-decomposition
    assert( p->nFanins == Nwk_ObjFaninNum(pNode) );
    pObj = Nwk_NodeIfNodeResyn( p->pManDec, pNode->pMan->pManHop, pNode->pFunc, p->nFanins, p->vTruth, p->uCare );
    nGain = Hop_DagSize(pNode->pFunc) - Hop_DagSize(pObj);
    if ( nGain >= 0 )
    {
        p->nNodesDec++;
        p->nNodesGained += nGain;
        p->nNodesGainedLevel += nGain;
        pNode->pFunc = pObj;    
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_Perform( Nwk_Man_t * pNtk, Mfx_Par_t * pPars, If_Lib_t * pLutLib )
{
    Bdc_Par_t Pars = {0}, * pDecPars = &Pars;
    Bar_Progress_t * pProgress;
    Mfx_Man_t * p;
    Tim_Man_t * pManTimeOld = NULL;
    Nwk_Obj_t * pObj;
    Vec_Vec_t * vLevels;
    Vec_Ptr_t * vNodes;
    int i, k, nNodes, nFaninMax, clk = clock(), clk2;
    int nTotalNodesBeg = Nwk_ManNodeNum(pNtk);
    int nTotalEdgesBeg = Nwk_ManGetTotalFanins(pNtk);

    // check limits on the number of fanins
    nFaninMax = Nwk_ManGetFaninMax(pNtk);
    if ( pPars->fResub )
    {
        if ( nFaninMax > 8 )
        {
            printf( "Nodes with more than %d fanins will node be processed.\n", 8 );
            nFaninMax = 8;
        }
    }
    else
    {
        if ( nFaninMax > MFX_FANIN_MAX )
        {
            printf( "Nodes with more than %d fanins will node be processed.\n", MFX_FANIN_MAX );
            nFaninMax = MFX_FANIN_MAX;
        }
    }
    if ( pLutLib && pLutLib->LutMax < nFaninMax )
    {
        printf( "The selected LUT library with max LUT size (%d) cannot be used to compute timing for network with %d-input nodes. Using unit-delay model.\n", pLutLib->LutMax, nFaninMax );
        pLutLib = NULL;
    }
    pNtk->pLutLib = pLutLib;

    // compute levels
    Nwk_ManLevel( pNtk );
    assert( Nwk_ManVerifyLevel( pNtk ) );
    // compute delay trace with white-boxes
    Nwk_ManDelayTraceLut( pNtk );
    assert( Nwk_ManVerifyTiming( pNtk ) );

    // start the manager
    p = Mfx_ManAlloc( pPars );
    p->pNtk = pNtk;
    p->nFaninMax = nFaninMax;
    if ( !pPars->fResub )
    {
        pDecPars->nVarsMax = nFaninMax;
        pDecPars->fVerbose = pPars->fVerbose;
        p->vTruth = Vec_IntAlloc( 0 );
        p->pManDec = Bdc_ManAlloc( pDecPars );
    }

    // compute don't-cares for each node
    nNodes = 0;
    p->nTotalNodesBeg = nTotalNodesBeg;
    p->nTotalEdgesBeg = nTotalEdgesBeg;
    if ( pPars->fResub )
    {
        pProgress = Bar_ProgressStart( stdout, Nwk_ManObjNumMax(pNtk) );
        Nwk_ManForEachNode( pNtk, pObj, i )
        {
            if ( p->pPars->nDepthMax && pObj->Level > p->pPars->nDepthMax )
                continue;
            if ( Nwk_ObjFaninNum(pObj) < 2 || Nwk_ObjFaninNum(pObj) > nFaninMax )
                continue;
            if ( !p->pPars->fVeryVerbose )
                Bar_ProgressUpdate( pProgress, i, NULL );
            Mfx_Resub( p, pObj );
        }
        Bar_ProgressStop( pProgress );
    }
    else
    {
        pProgress = Bar_ProgressStart( stdout, Nwk_ManNodeNum(pNtk) );
        vLevels = Nwk_ManLevelize( pNtk );
        Vec_VecForEachLevelStart( vLevels, vNodes, k, 1 )
        {
            if ( !p->pPars->fVeryVerbose )
                Bar_ProgressUpdate( pProgress, nNodes, NULL );
            p->nNodesGainedLevel = 0;
            p->nTotConfLevel = 0;
            p->nTimeOutsLevel = 0;
            clk2 = clock();
            Vec_PtrForEachEntry( vNodes, pObj, i )
            {
                if ( p->pPars->nDepthMax && pObj->Level > p->pPars->nDepthMax )
                    break;
                if ( Nwk_ObjFaninNum(pObj) < 2 || Nwk_ObjFaninNum(pObj) > nFaninMax )
                    continue;
                Mfx_Node( p, pObj );
            }
            nNodes += Vec_PtrSize(vNodes);
            if ( pPars->fVerbose )
            {
            printf( "Lev = %2d. Node = %5d. Ave gain = %5.2f. Ave conf = %5.2f. T/o = %6.2f %%  ", 
                k, Vec_PtrSize(vNodes),
                1.0*p->nNodesGainedLevel/Vec_PtrSize(vNodes),
                1.0*p->nTotConfLevel/Vec_PtrSize(vNodes),
                100.0*p->nTimeOutsLevel/Vec_PtrSize(vNodes) );
            PRT( "Time", clock() - clk2 );
            }
        }
        Bar_ProgressStop( pProgress );
        Vec_VecFree( vLevels );
    }
    p->nTotalNodesEnd = Nwk_ManNodeNum(pNtk);
    p->nTotalEdgesEnd = Nwk_ManGetTotalFanins(pNtk);

    assert( Nwk_ManVerifyLevel( pNtk ) );
    assert( Nwk_ManVerifyTiming( pNtk ) );

    // free the manager
    p->timeTotal = clock() - clk;
    Mfx_ManStop( p );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


