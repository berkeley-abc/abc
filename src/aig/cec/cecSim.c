/**CFile****************************************************************

  FileName    [cecSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [AIG simulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSim.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Count PIs with fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManCountRelevantPis( Aig_Man_t * pAig )
{
    Aig_Obj_t * pObj;
    int i, Counter = 0;
    Aig_ManForEachPi( pAig, pObj, i )
        if ( Aig_ObjRefs(pObj) )
            Counter++;
        else 
            pObj->iData = -1;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Count PIs with fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManCountRelevantPos( Aig_Man_t * pAig )
{
    Aig_Obj_t * pObj;
    int i, Counter = 0;
    Aig_ManForEachPo( pAig, pObj, i )
        if ( !Aig_ObjIsConst1(Aig_ObjFanin0(pObj)) )
            Counter++;
        else 
            pObj->iData = -1;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Find the PO corresponding to the PO driver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManFindPo( Aig_Man_t * pAig, int iNode )
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManForEachPo( pAig, pObj, i )
        if ( pObj->iData == iNode )
            return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Creates fast simulation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManCreate_rec( Caig_Man_t * p, Aig_Obj_t * pObj )
{
    int iFan0, iFan1;
    assert( !Aig_IsComplement(pObj) );
    assert( !Aig_ObjIsConst1(pObj) );
    if ( pObj->iData )
        return pObj->iData;
    if ( Aig_ObjIsNode(pObj) )
    {
        iFan0 = Caig_ManCreate_rec( p, Aig_ObjFanin0(pObj) );
        iFan0 = (iFan0 << 1) | Aig_ObjFaninC0(pObj);
        iFan1 = Caig_ManCreate_rec( p, Aig_ObjFanin1(pObj) );
        iFan1 = (iFan1 << 1) | Aig_ObjFaninC1(pObj);
    }
    else if ( Aig_ObjIsPo(pObj) )
    {
        iFan0 = Caig_ManCreate_rec( p, Aig_ObjFanin0(pObj) );
        iFan0 = (iFan0 << 1) | Aig_ObjFaninC0(pObj);
        iFan1 = 0;
    }
    else
        iFan0 = iFan1 = 0;
    assert( Aig_ObjRefs(pObj) < (1<<16) );
    p->pFans0[p->nObjs] = iFan0;
    p->pFans1[p->nObjs] = iFan1;
    p->pRefs[p->nObjs]  = (unsigned short)Aig_ObjRefs(pObj);
    return pObj->iData = p->nObjs++;
}

/**Function*************************************************************

  Synopsis    [Creates fast simulation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Caig_Man_t * Caig_ManCreate( Aig_Man_t * pAig )
{
    Caig_Man_t * p;
    Aig_Obj_t * pObj;
    int i, nObjs;
    Aig_ManCleanData( pAig );
    p = (Caig_Man_t *)ALLOC( Caig_Man_t, 1 );
    memset( p, 0, sizeof(Caig_Man_t) );
    p->pAig = pAig;
    p->nPis = Caig_ManCountRelevantPis(pAig);
    p->nPos = Caig_ManCountRelevantPos(pAig);
    p->nNodes = Aig_ManNodeNum(pAig);
    nObjs = p->nPis + p->nPos + p->nNodes + 1;
    p->pFans0 = ALLOC( int, nObjs );
    p->pFans1 = ALLOC( int, nObjs );
    p->pRefs = ALLOC( unsigned short, nObjs );
    p->pSims = CALLOC( unsigned, nObjs );
    // add objects
    p->nObjs = 1;
    Aig_ManForEachPo( pAig, pObj, i )
        if ( !Aig_ObjIsConst1(Aig_ObjFanin0(pObj)) )
            Caig_ManCreate_rec( p, pObj );
    assert( p->nObjs == nObjs );
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates fast simulation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManDelete( Caig_Man_t * p )
{
    if ( p->vSims )     Vec_PtrFree( p->vSims );
    if ( p->vClassOld ) Vec_IntFree( p->vClassOld );
    if ( p->vClassNew ) Vec_IntFree( p->vClassNew );
    FREE( p->pFans0 );
    FREE( p->pFans1 );
    FREE( p->pRefs );
    FREE( p->pSims );
    FREE( p->pMems );
    FREE( p->pReprs );
    FREE( p->pNexts );
    FREE( p );
}

/**Function*************************************************************

  Synopsis    [References simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Caig_ManSimRead( Caig_Man_t * p, int i )
{
    assert( i && p->pSims[i] > 0 );
    return p->pMems + p->pSims[i];
}

/**Function*************************************************************

  Synopsis    [References simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Caig_ManSimRef( Caig_Man_t * p, int i )
{
    unsigned * pSim;
    assert( i );
    assert( p->pSims[i] == 0 );
    if ( p->MemFree == 0 )
    {
        int * pPlace, Ent;
        if ( p->nWordsAlloc == 0 )
        {
            assert( p->pMems == NULL );
            p->nWordsAlloc = (1<<17); // -> 1Mb
            p->nMems = 1;
        }
        p->nWordsAlloc *= 2;
        p->pMems = REALLOC( unsigned, p->pMems, p->nWordsAlloc );
        pPlace = &p->MemFree;
        for ( Ent = p->nMems * (p->nWords + 1); 
              Ent + p->nWords + 1 < p->nWordsAlloc; 
              Ent += p->nWords + 1 )
        {
            *pPlace = Ent;
            pPlace = p->pMems + Ent;
        }
        *pPlace = 0;
    }
    p->pSims[i] = p->MemFree;
    pSim = p->pMems + p->MemFree;
    p->MemFree = pSim[0];
    pSim[0] = p->pRefs[i];
    p->nMems++;
    if ( p->nMemsMax < p->nMems )
        p->nMemsMax = p->nMems;
    return pSim;
}

/**Function*************************************************************

  Synopsis    [Dereference simulaton info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Caig_ManSimDeref( Caig_Man_t * p, int i )
{
    unsigned * pSim;
    assert( i );
    assert( p->pSims[i] > 0 );
    pSim = p->pMems + p->pSims[i];
    if ( --pSim[0] == 0 )
    {
        pSim[0] = p->MemFree;
        p->MemFree = p->pSims[i];
        p->pSims[i] = 0;
        p->nMems--;
    }
    return pSim;
}

/**Function*************************************************************

  Synopsis    [Simulates one round.]

  Description [Returns the number of PO entry if failed; 0 otherwise.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManSimulateRound( Caig_Man_t * p, int fMiter )
{
    Vec_Int_t * vRefined = NULL;
    unsigned * pRes0, * pRes1, * pRes;
    int i, w, iFan0, iFan1;
    if ( p->pReprs )
        vRefined = Vec_IntAlloc( 1000 );
    for ( i = 1; i < p->nObjs; i++ )
    {
        if ( p->pFans0[i] == 0 ) // pi always has zero first fanin
        {
            pRes = Caig_ManSimRef( p, i );
            for ( w = 1; w <= p->nWords; w++ )
                pRes[w] = Aig_ManRandom( 0 );
            goto references;
        }
        if ( p->pFans1[i] == 0 ) // po always has non-zero 1st fanin and zero 2nd fanin
        {
            if ( fMiter )
            {
                unsigned Const = Cec_LitIsCompl(p->pFans0[i])? ~0 : 0;
                pRes0 = Caig_ManSimDeref( p, Cec_Lit2Var(p->pFans0[i]) );
                for ( w = 1; w <= p->nWords; w++ )
                    if ( pRes0[w] != Const )
                        return i;
            }
            continue;
        }
        pRes = Caig_ManSimRef( p, i );
        iFan0 = p->pFans0[i];
        iFan1 = p->pFans1[i];
        pRes0 = Caig_ManSimDeref( p, Cec_Lit2Var(p->pFans0[i]) );
        pRes1 = Caig_ManSimDeref( p, Cec_Lit2Var(p->pFans1[i]) );
        if ( Cec_LitIsCompl(iFan0) && Cec_LitIsCompl(iFan1) )
            for ( w = 1; w <= p->nWords; w++ )
                pRes[w] = ~(pRes0[w] | pRes1[w]);
        else if ( Cec_LitIsCompl(iFan0) && !Cec_LitIsCompl(iFan1) )
            for ( w = 1; w <= p->nWords; w++ )
                pRes[w] = ~pRes0[w] & pRes1[w];
        else if ( !Cec_LitIsCompl(iFan0) && Cec_LitIsCompl(iFan1) )
            for ( w = 1; w <= p->nWords; w++ )
                pRes[w] = pRes0[w] & ~pRes1[w];
        else if ( !Cec_LitIsCompl(iFan0) && !Cec_LitIsCompl(iFan1) )
            for ( w = 1; w <= p->nWords; w++ )
                pRes[w] = pRes0[w] & pRes1[w];
references:
        if ( p->pReprs == NULL )
            continue;
        // if this node is candidate constant, collect it
        if ( p->pReprs[i] == 0 && !Caig_ManCompareConst(pRes + 1, p->nWords) )
        {
            pRes[0]++;
            Vec_IntPush( vRefined, i );
        }
        // if the node belongs to a class, save it
        if ( p->pReprs[i] > 0 || p->pNexts[i] > 0 )
            pRes[0]++;
        // if this is the last node of the class, process it
        if ( p->pReprs[i] > 0 && p->pNexts[i] == 0 )
            Caig_ManProcessClass( p, p->pReprs[i] );
    }
    if ( p->pReprs )
        Caig_ManProcessRefined( p, vRefined );
    if ( p->pReprs )
        Vec_IntFree( vRefined );
    assert( p->nMems == 1 );
/*
    if ( p->nMems > 1 )
    {
        for ( i = 1; i < p->nObjs; i++ )
        if ( p->pSims[i] )
        {
            int x = 0;
        }
    }
*/
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the bug is detected, 0 otherwise.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimulate( Aig_Man_t * pAig, int nWords, int nIters, int TimeLimit, int fMiter, int fVerbose )
{
    Caig_Man_t * p;
    Cec_MtrStatus_t Status;
    int i, RetValue = 0, clk, clkTotal = clock();
/*
    p = Caig_ManClassesPrepare( pAig, nWords, nIters );
//    if ( fVerbose )
    printf( "Maxcut = %6d.  AIG mem = %8.3f Mb.  Sim mem = %8.3f Mb.\n", 
        p->nMemsMax, 
        1.0*(p->nObjs * 14)/(1<<20), 
        1.0*(p->nMemsMax * (nWords+1))/(1<<20) );
    Caig_ManDelete( p );
    return 0;
*/
    Status = Cec_MiterStatus( pAig );
    if ( Status.nSat > 0 )
    {
        printf( "Miter is trivially satisfiable (output %d).\n", Status.iOut );
        return 1;
    }
    if ( Status.nUndec == 0 )
    {
        printf( "Miter is trivially unsatisfiable.\n" );
        return 0;
    }
    Aig_ManRandom( 1 );
    p = Caig_ManCreate( pAig );
    p->nWords = nWords;
    for ( i = 0; i < nIters; i++ )
    {
        clk = clock();
        RetValue = Caig_ManSimulateRound( p, fMiter );
        if ( fVerbose )
        {
            printf( "Iter %3d out of %3d and timeout %3d sec. ", i+1, nIters, TimeLimit );
            printf("Time = %7.2f sec\r", (1.0*clock()-clkTotal)/CLOCKS_PER_SEC);
        }
        if ( RetValue > 0 )
        {
            int iOut = Caig_ManFindPo(p->pAig, RetValue);
            if ( fVerbose )
            printf( "Miter is satisfiable after simulation (output %d).\n", iOut );
            break;
        }
        if ( (clock() - clk)/CLOCKS_PER_SEC >= TimeLimit )
        {
            printf( "No bug detected after %d rounds with time limit %d seconds.\n", i+1, TimeLimit );
            break;
        }
    }
    if ( fVerbose )
    printf( "Maxcut = %6d.  AIG mem = %8.3f Mb.  Sim mem = %8.3f Mb.\n", 
        p->nMemsMax, 
        1.0*(p->nObjs * 14)/(1<<20), 
        1.0*(p->nMemsMax * 4 * (nWords+1))/(1<<20) );
    Caig_ManDelete( p );
    return RetValue > 0;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


