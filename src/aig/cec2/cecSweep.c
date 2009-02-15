/**CFile****************************************************************

  FileName    [cecSweep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [Pattern accumulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSweep.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"
#include "satSolver.h"
#include "cnf.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Cec_ManCsw_t_ Cec_ManCsw_t;
struct Cec_ManCsw_t_
{
    // parameters
    Cec_ParCsw_t *  pPars;        // parameters   
    Caig_Man_t *    p;            // AIG and simulation manager
    // mapping into copy
    Aig_Obj_t **    pCopy;        // the copy of nodes   
    Vec_Int_t *     vCopies;      // the nodes copied in the last round
    char *          pProved;      // tells if the given node is proved
    char *          pProvedNow;   // tells if the given node is proved
    int *           pLevel;       // level of the nodes
    // collected patterns
    Vec_Ptr_t *     vInfo;        // simulation info accumulated
    Vec_Ptr_t *     vPres;        // simulation presence accumulated
    Vec_Ptr_t *     vInfoAll;     // vector of vectors of simulation info
    // temporaries
    Vec_Int_t *     vPiNums;      // primary input numbers
    Vec_Int_t *     vPoNums;      // primary output numbers
    Vec_Int_t *     vPat;         // one counter-example
    Vec_Ptr_t *     vSupp;        // support of one node
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Adds pattern to storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSavePattern( Cec_ManCsw_t * p, Vec_Int_t * vPat )
{
    unsigned * pInfo, * pPres;
    int nPatsAlloc, iLit, i, c;
    assert( p->p->nWords == Vec_PtrReadWordsSimInfo(p->vInfo) );
    // find next empty place
    nPatsAlloc = 32 * p->p->nWords;
    for ( c = 0; c < nPatsAlloc; c++ )
    {
        Vec_IntForEachEntry( vPat, iLit, i )
        {
            pPres = Vec_PtrEntry( p->vPres, Cec_Lit2Var(iLit) );
            if ( Aig_InfoHasBit( pPres, c ) )
                break;
        }
        if ( i == Vec_IntSize(vPat) )
            break;
    }
    // increase the size if needed
    if ( c == nPatsAlloc )
    {
        p->vInfo = Vec_PtrAllocSimInfo( p->p->nPis, p->p->nWords );
        Vec_PtrCleanSimInfo( p->vInfo, 0, p->p->nWords );
        Vec_PtrCleanSimInfo( p->vPres, 0, p->p->nWords );
        Vec_PtrPush( p->vInfoAll, p->vInfo );
        c = 0;
    }
    // save the pattern
    Vec_IntForEachEntry( vPat, iLit, i )
    {
        pPres = Vec_PtrEntry( p->vPres, Cec_Lit2Var(iLit) );
        pInfo = Vec_PtrEntry( p->vInfo, Cec_Lit2Var(iLit) );
        Aig_InfoSetBit( pPres, c );
        if ( !Cec_LitIsCompl(iLit) )
            Aig_InfoSetBit( pInfo, c );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Cec_ManCswCreatePartition_rec( Aig_Man_t * pAig, Cec_ManCsw_t * p, int i )
{
    Aig_Obj_t * pRes0, * pRes1;
    if ( p->pCopy[i] )
        return p->pCopy[i];
    Vec_IntPush( p->vCopies, i );
    if ( p->p->pFans0[i] == -1 ) // pi
    {
        Vec_IntPush( p->vPiNums, Aig_ObjPioNum( Aig_ManObj(p->p->pAig, i) ) );
        return p->pCopy[i] = Aig_ObjCreatePi( pAig );
    }
    assert( p->p->pFans0[i] && p->p->pFans1[i] );
    pRes0 = Cec_ManCswCreatePartition_rec( pAig, p, Cec_Lit2Var(p->p->pFans0[i]) );
    pRes0 = Aig_NotCond( pRes0, Cec_LitIsCompl(p->p->pFans0[i]) );
    pRes1 = Cec_ManCswCreatePartition_rec( pAig, p, Cec_Lit2Var(p->p->pFans1[i]) );
    pRes1 = Aig_NotCond( pRes1, Cec_LitIsCompl(p->p->pFans1[i]) );
    return p->pCopy[i] = Aig_And( pAig, pRes0, pRes1 );
}

/**Function*************************************************************

  Synopsis    [Creates dynamic partition.]

  Description [PIs point to node IDs. POs point to node IDs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cec_ManCswCreatePartition( Cec_ManCsw_t * p, int * piStart, int nMitersMin, int nNodesMin, int nLevelMax )
{
    Caig_Man_t * pMan = p->p;
    Aig_Man_t * pAig;
    Aig_Obj_t * pRepr, * pNode, * pMiter, * pTerm;
    int i, iNode, Counter = 0;
    assert( p->pCopy && p->vCopies );
    // clear previous marks
    Vec_IntForEachEntry( p->vCopies, iNode, i )
        p->pCopy[iNode] = NULL;
    Vec_IntClear( p->vCopies );
    // iterate through nodes starting from the given one
    pAig = Aig_ManStart( nNodesMin );
    p->pCopy[0] = Aig_ManConst1(pAig);
    Vec_IntPush( p->vCopies, 0 );
    for ( i = *piStart; i < pMan->nObjs; i++ )
    {
        if ( pMan->pFans0[i] == -1 ) // pi always has zero first fanin
            continue;
        if ( pMan->pFans1[i] == -1 ) // po always has non-zero 1st fanin and zero 2nd fanin
            continue;
        if ( pMan->pReprs[i] < 0 )
            continue;
        if ( p->pPars->nLevelMax && (p->pLevel[i] > p->pPars->nLevelMax || p->pLevel[pMan->pReprs[i]] > p->pPars->nLevelMax) )
            continue;
        // create cones
        pRepr = Cec_ManCswCreatePartition_rec( pAig, p, pMan->pReprs[i] );
        pNode = Cec_ManCswCreatePartition_rec( pAig, p, i );
        // skip if they are the same
        if ( Aig_Regular(pRepr) == Aig_Regular(pNode) )
        {
            p->pProvedNow[i] = 1;
            continue;
        }
        // perform speculative reduction
        assert( p->pCopy[i] == pNode );
        p->pCopy[i] = Aig_NotCond( pRepr, Aig_ObjPhaseReal(pRepr) ^ Aig_ObjPhaseReal(pNode) );
        if ( p->pProved[i] )
        {
            p->pProvedNow[i] = 1;
            continue;
        }
        pMiter = Aig_Exor( pAig, pRepr, pNode );
        pTerm = Aig_ObjCreatePo( pAig, Aig_NotCond(pMiter, Aig_ObjPhaseReal(pMiter)) );
        Vec_IntPush( p->vPoNums, i );
        if ( ++Counter > nMitersMin && Aig_ManObjNum(pAig) > nNodesMin )
            break;
    }
    *piStart = i + 1;
    Aig_ManSetRegNum( pAig, 0 );
    Aig_ManCleanup( pAig );
    return pAig;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSatDerivePattern( Cec_ManCsw_t * p, Aig_Man_t * pAig, Aig_Obj_t * pRoot, Cnf_Dat_t * pCnf, sat_solver * pSat )
{
    Aig_Obj_t * pObj;
    int i, Value, iVar;
    assert( Aig_ObjIsPo(pRoot) );
    Aig_SupportNodes( pAig, &pRoot, 1, p->vSupp );
    Vec_IntClear( p->vPat );
    Vec_PtrForEachEntry( p->vSupp, pObj, i )
    {
        assert( Aig_ObjIsPi(pObj) );
        Value = sat_solver_var_value( pSat, pCnf->pVarNums[pObj->Id] );
        iVar = Vec_IntEntry( p->vPiNums, Aig_ObjPioNum(pObj) );
        assert( iVar >= 0 && iVar < p->p->nPis );
        Vec_IntPush( p->vPat, Cec_Var2Lit( iVar, !Value ) );
    }
}

/**Function*************************************************************

  Synopsis    [Creates level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCreateLevel( Cec_ManCsw_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    assert( p->pLevel == NULL );
    p->pLevel = ABC_ALLOC( int, p->p->nObjs );
    Aig_ManForEachObj( p->p->pAig, pObj, i )
        p->pLevel[i] = Aig_ObjLevel(pObj);
}

/**Function*************************************************************

  Synopsis    [Creates the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cec_ManCsw_t * Cec_ManCswCreate( Caig_Man_t * pMan, Cec_ParCsw_t * pPars )
{
    Cec_ManCsw_t * p;
    // create interpolation manager
    p = ABC_ALLOC( Cec_ManCsw_t, 1 );
    memset( p, 0, sizeof(Cec_ManCsw_t) );
    p->pPars      = pPars;
    p->p          = pMan;
    // internal storage
    p->vCopies    = Vec_IntAlloc( 10000 );
    p->pCopy      = ABC_CALLOC( Aig_Obj_t *, pMan->nObjs );
    p->pProved    = ABC_CALLOC( char, pMan->nObjs );
    p->pProvedNow = ABC_CALLOC( char, pMan->nObjs );
    // temporaries
    p->vPat       = Vec_IntAlloc( 1000 );
    p->vSupp      = Vec_PtrAlloc( 1000 );
    p->vPiNums    = Vec_IntAlloc( 1000 );
    p->vPoNums    = Vec_IntAlloc( 1000 );
    if ( pPars->nLevelMax )
        Cec_ManCreateLevel( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswStop( Cec_ManCsw_t * p )
{
    Vec_IntFree( p->vPiNums );
    Vec_IntFree( p->vPoNums );
    Vec_PtrFree( p->vSupp );
    Vec_IntFree( p->vPat );
    Vec_IntFree( p->vCopies );
    Vec_PtrFree( p->vPres );
    Vec_VecFree( (Vec_Vec_t *)p->vInfoAll );
    ABC_FREE( p->pLevel );
    ABC_FREE( p->pCopy );
    ABC_FREE( p->pProved );
    ABC_FREE( p->pProvedNow );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Cleans the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCleanSimInfo( Cec_ManCsw_t * p )
{
    if ( p->vInfoAll )
        Vec_VecFree( (Vec_Vec_t *)p->vInfoAll );
    if ( p->vPres )
        Vec_PtrFree( p->vPres );
    p->vInfoAll = Vec_PtrAlloc( 100 );
    p->vInfo    = Vec_PtrAllocSimInfo( p->p->nPis, p->pPars->nWords );
    p->vPres    = Vec_PtrAllocSimInfo( p->p->nPis, p->pPars->nWords );
    Vec_PtrCleanSimInfo( p->vInfo, 0, p->p->nWords );
    Vec_PtrCleanSimInfo( p->vPres, 0, p->p->nWords );
    Vec_PtrPush( p->vInfoAll, p->vInfo );
}

/**Function*************************************************************

  Synopsis    [Update information about proved nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCountProved( char * pArray, int nSize )
{
    int i, Counter = 0;
    for ( i = 0; i < nSize; i++ )
        Counter += (pArray[i] == 1);
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Update information about proved nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCountDisproved( char * pArray, int nSize )
{
    int i, Counter = 0;
    for ( i = 0; i < nSize; i++ )
        Counter += (pArray[i] == -1);
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Update information about proved nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCountTimedout( char * pArray, int nSize )
{
    int i, Counter = 0;
    for ( i = 0; i < nSize; i++ )
        Counter += (pArray[i] == -2);
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Update information about proved nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManUpdateProved( Cec_ManCsw_t * p )
{
    Caig_Man_t * pMan = p->p;
    int i;
    for ( i = 1; i < pMan->nObjs; i++ )
    {
        if ( pMan->pFans0[i] == -1 ) // pi always has zero first fanin
            continue;
        if ( pMan->pFans1[i] == -1 ) // po always has non-zero 1st fanin and zero 2nd fanin
            continue;
        if ( p->pProvedNow[Cec_Lit2Var(pMan->pFans0[i])] < 0 || 
             p->pProvedNow[Cec_Lit2Var(pMan->pFans1[i])] < 0  )
             p->pProvedNow[i] = -1;
        if ( pMan->pReprs[i] < 0 )
        {
            assert( p->pProvedNow[i] <= 0 );
            continue;
        }
        if ( p->pProved[i] )
        {
            assert( p->pProvedNow[i] == 1 );
            continue;
        }
        if ( p->pProvedNow[i] == 1 )
            p->pProved[i] = 1;
    }
}

/**Function*************************************************************

  Synopsis    [Creates dynamic partition.]

  Description [PIs point to node IDs. POs point to node IDs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSatSweepRound( Cec_ManCsw_t * p )
{
    Bar_Progress_t * pProgress = NULL;
    Vec_Ptr_t * vInfo;
    Aig_Man_t * pAig, * pTemp;
    Aig_Obj_t * pObj;
    Cnf_Dat_t * pCnf;
    sat_solver * pSat;
    int i, Lit, iNode, iStart, status;
    int nProved, nDisproved, nTimedout, nBefore, nAfter, nRecycles = 0;
    int clk = clock();
    Cec_ManCleanSimInfo( p );
    memset( p->pProvedNow, 0, sizeof(char) * p->p->nObjs );
    pProgress = Bar_ProgressStart( stdout, p->p->nObjs );
    for ( iStart = 1; iStart < p->p->nObjs; )
    {
        Bar_ProgressUpdate( pProgress, iStart, "Sweep..." );
        Vec_IntClear( p->vPiNums );
        Vec_IntClear( p->vPoNums );
        // generate AIG, synthesize, convert to CNF, and solve
        pAig = Cec_ManCswCreatePartition( p, &iStart, p->pPars->nCallsRecycle, p->pPars->nSatVarMax, p->pPars->nLevelMax );
        Aig_ManPrintStats( pAig );

        if ( p->pPars->fRewriting )
        {
            pAig = Dar_ManRwsat( pTemp = pAig, 1, 0 );
            Aig_ManStop( pTemp );
        }
        pCnf = Cnf_Derive( pAig, Aig_ManPoNum(pAig) );
        pSat = Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
        Aig_ManForEachPo( pAig, pObj, i )
        {
            iNode = Vec_IntEntry( p->vPoNums, i );
            Lit = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
            status = sat_solver_solve( pSat, &Lit, &Lit + 1, (ABC_INT64_T)p->pPars->nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
            if ( status == l_False )
                p->pProvedNow[iNode] = 1;
            else if ( status == l_Undef ) 
                p->pProvedNow[iNode] = -2;
            else if ( status == l_True ) 
            {
                p->pProvedNow[iNode] = -1;
                Cec_ManSatDerivePattern( p, pAig, pObj, pCnf, pSat );
                Cec_ManSavePattern( p, p->vPat ); 
            }
        }
        // clean up
        Aig_ManStop( pAig );
        Cnf_DataFree( pCnf );
        sat_solver_delete( pSat );
        nRecycles++;
    }
    Bar_ProgressStop( pProgress );
    // collect statistics
    nProved = Cec_ManCountProved( p->pProvedNow, p->p->nObjs );
    nDisproved = Cec_ManCountDisproved( p->pProvedNow, p->p->nObjs );
    nTimedout = Cec_ManCountTimedout( p->pProvedNow, p->p->nObjs );
    nBefore = Cec_ManCountProved( p->pProved, p->p->nObjs );
    Cec_ManUpdateProved( p );
    nAfter = Cec_ManCountProved( p->pProved, p->p->nObjs );
    printf( "Pr =%6d. Cex =%6d. Fail =%6d. Bef =%6d. Aft =%6d.  Rcl =%4d.", 
        nProved, nDisproved, nTimedout, nBefore, nAfter, nRecycles );
    ABC_PRT( "Time", clock() - clk );
    // resimulate with the collected information
    Vec_PtrForEachEntry( p->vInfoAll, vInfo, i )
        Caig_ManSimulateRound( p->p, vInfo, NULL );
Caig_ManPrintClasses( p->p, 0 );
}

/**Function*************************************************************

  Synopsis    [Performs one round of sweeping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSatSweepInt( Caig_Man_t * pMan, Cec_ParCsw_t * pPars )
{
    Cec_ManCsw_t * p;
    p = Cec_ManCswCreate( pMan, pPars );
    Cec_ManSatSweepRound( p );
    Cec_ManCswStop( p );
}


/**Function*************************************************************

  Synopsis    [Performs equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cec_ManTrasferReprs( Aig_Man_t * pAig, Caig_Man_t * pCaig )
{
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Performs equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cec_ManSatSweep( Aig_Man_t * pAig, Cec_ParCsw_t * pPars )
{
/*
    Aig_Man_t * pAigNew, * pAigDfs;
    Caig_Man_t * pCaig;
    Cec_ManCsw_t * p;
    pAigDfs = Cec_Duplicate( pAig );
    pCaig = Caig_ManClassesPrepare( pAigDfs, pPars->nWords, pPars->nRounds );
    p = Cec_ManCswCreate( pCaig, pPars );
    Cec_ManSatSweep( p, pPars );
    Cec_ManCswStop( p );
//    pAigNew = 
    Caig_ManDelete( pCaig );
    Aig_ManStop( pAigDfs );
    return pAigNew;
*/
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


