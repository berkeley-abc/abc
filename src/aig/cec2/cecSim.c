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

  Synopsis    [Creates fast simulation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Caig_Man_t * Caig_ManCreate( Aig_Man_t * pAig )
{
    Caig_Man_t * p;
    Aig_Obj_t * pObj;
    int i;
    assert( Aig_ManHasNoGaps(pAig) );
    Aig_ManCleanData( pAig );
    p = (Caig_Man_t *)ABC_ALLOC( Caig_Man_t, 1 );
    memset( p, 0, sizeof(Caig_Man_t) );
    p->pAig = pAig;
    p->nPis = Aig_ManPiNum(pAig);
    p->nPos = Aig_ManPoNum(pAig);
    p->nNodes = Aig_ManNodeNum(pAig);
    p->nObjs  = p->nPis + p->nPos + p->nNodes + 1;
    p->pFans0 = ABC_ALLOC( int, p->nObjs );
    p->pFans1 = ABC_ALLOC( int, p->nObjs );
    p->pRefs  = ABC_ALLOC( int, p->nObjs );
    p->pSims  = ABC_CALLOC( unsigned, p->nObjs );
    // add objects
    Aig_ManForEachObj( pAig, pObj, i )
    {
        p->pRefs[i] = Aig_ObjRefs(pObj);
        if ( Aig_ObjIsNode(pObj) )
        {
            p->pFans0[i] = (Aig_ObjFaninId0(pObj) << 1) | Aig_ObjFaninC0(pObj);
            p->pFans1[i] = (Aig_ObjFaninId1(pObj) << 1) | Aig_ObjFaninC1(pObj);
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            p->pFans0[i] = (Aig_ObjFaninId0(pObj) << 1) | Aig_ObjFaninC0(pObj);
            p->pFans1[i] = -1;
        }
        else 
        {
            assert( Aig_ObjIsPi(pObj) || Aig_ObjIsConst1(pObj) );
            p->pFans0[i] = -1;
            p->pFans1[i] = -1;
        }
    }
    // temporaries
    p->vClassOld = Vec_IntAlloc( 1000 );
    p->vClassNew = Vec_IntAlloc( 1000 );
    p->vRefinedC = Vec_IntAlloc( 10000 );
    p->vSims     = Vec_PtrAlloc( 1000 );
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
    Vec_IntFree( p->vClassOld );
    Vec_IntFree( p->vClassNew );
    Vec_IntFree( p->vRefinedC );
    Vec_PtrFree( p->vSims );
    ABC_FREE( p->pFans0 );
    ABC_FREE( p->pFans1 );
    ABC_FREE( p->pRefs );
    ABC_FREE( p->pSims );
    ABC_FREE( p->pMems );
    ABC_FREE( p->pReprs );
    ABC_FREE( p->pNexts );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [References simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManSimMemRelink( Caig_Man_t * p )
{
    int * pPlace, Ent;
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
    assert( p->pSims[i] == 0 );
    if ( p->MemFree == 0 )
    {
        if ( p->nWordsAlloc == 0 )
        {
            assert( p->pMems == NULL );
            p->nWordsAlloc = (1<<17); // -> 1Mb
            p->nMems = 1;
        }
        p->nWordsAlloc *= 2;
        p->pMems = ABC_REALLOC( unsigned, p->pMems, p->nWordsAlloc );
        Caig_ManSimMemRelink( p );
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
void Caig_ManSimulateRound( Caig_Man_t * p, Vec_Ptr_t * vInfoCis, Vec_Ptr_t * vInfoCos )
{
    unsigned * pRes0, * pRes1, * pRes;
    int i, w, iCiId = 0, iCoId = 0;
    int nWords = Vec_PtrReadWordsSimInfo( vInfoCis );
    assert( vInfoCos == NULL || nWords == Vec_PtrReadWordsSimInfo(vInfoCos) );
    Vec_IntClear( p->vRefinedC );
    if ( p->pRefs[0] )
    {
        pRes = Caig_ManSimRef( p, 0 );
        for ( w = 1; w <= nWords; w++ )
            pRes[w] = ~0;
    }
    for ( i = 1; i < p->nObjs; i++ )
    {
        if ( p->pFans0[i] == -1 ) // ci always has zero first fanin
        {
            if ( p->pRefs[i] == 0 )
            {
                iCiId++;
                continue;
            }
            pRes = Caig_ManSimRef( p, i );
            pRes0 = Vec_PtrEntry( vInfoCis, iCiId++ );
            for ( w = 1; w <= nWords; w++ )
                pRes[w] = pRes0[w-1];
            goto references;
        }
        if ( p->pFans1[i] == -1 ) // co always has non-zero 1st fanin and zero 2nd fanin
        {
            pRes0 = Caig_ManSimDeref( p, Cec_Lit2Var(p->pFans0[i]) );
            if ( vInfoCos )
            {
                pRes = Vec_PtrEntry( vInfoCos, iCoId++ );
                if ( Cec_LitIsCompl(p->pFans0[i]) )
                    for ( w = 1; w <= nWords; w++ )
                        pRes[w-1] = ~pRes0[w];
                else 
                    for ( w = 1; w <= nWords; w++ )
                        pRes[w-1] = pRes0[w];
            }
            continue;
        }
        assert( p->pRefs[i] );
        pRes  = Caig_ManSimRef( p, i );
        pRes0 = Caig_ManSimDeref( p, Cec_Lit2Var(p->pFans0[i]) );
        pRes1 = Caig_ManSimDeref( p, Cec_Lit2Var(p->pFans1[i]) );
        if ( Cec_LitIsCompl(p->pFans0[i]) )
        {
            if ( Cec_LitIsCompl(p->pFans1[i]) )
                for ( w = 1; w <= nWords; w++ )
                    pRes[w] = ~(pRes0[w] | pRes1[w]);
            else
                for ( w = 1; w <= nWords; w++ )
                    pRes[w] = ~pRes0[w] & pRes1[w];
        }
        else
        {
            if ( Cec_LitIsCompl(p->pFans1[i]) )
                for ( w = 1; w <= nWords; w++ )
                    pRes[w] = pRes0[w] & ~pRes1[w];
            else
                for ( w = 1; w <= nWords; w++ )
                    pRes[w] = pRes0[w] & pRes1[w];
        }
references:
        if ( p->pReprs == NULL )
            continue;
        // if this node is candidate constant, collect it
        if ( p->pReprs[i] == 0 && !Caig_ManCompareConst(pRes + 1, nWords) )
        {
            pRes[0]++;
            Vec_IntPush( p->vRefinedC, i );
        }
        // if the node belongs to a class, save it
        if ( p->pReprs[i] > 0 || p->pNexts[i] > 0 )
            pRes[0]++;
        // if this is the last node of the class, process it
        if ( p->pReprs[i] > 0 && p->pNexts[i] == 0 )
        {
            Caig_ManCollectSimsNormal( p, p->pReprs[i] );
            Caig_ManClassRefineOne( p, p->pReprs[i], p->vSims );
        }
    }
    if ( Vec_IntSize(p->vRefinedC) > 0 )
        Caig_ManProcessRefined( p, p->vRefinedC );
    assert( iCiId == p->nPis );
    assert( vInfoCos == NULL || iCoId == p->nPos );
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
}

/**Function*************************************************************

  Synopsis    [Returns the number of PO that failed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManFindPo( Vec_Ptr_t * vInfo, int nWords )
{
    unsigned * pInfo;
    int i, w;
    Vec_PtrForEachEntry( vInfo, pInfo, i )
        for ( w = 0; w < nWords; w++ )
            if ( pInfo[w] != 0 )
                return i;
    return -1;
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
    Vec_Ptr_t * vInfoCis, * vInfoCos = NULL;
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
    if ( fMiter )
    {
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
    }
    Aig_ManRandom( 1 );
    p = Caig_ManCreate( pAig );
    p->nWords = nWords;
    if ( fMiter )
        vInfoCos = Vec_PtrAllocSimInfo( Aig_ManPiNum(pAig), nWords );
    for ( i = 0; i < nIters; i++ )
    {
        clk = clock();
        vInfoCis = Vec_PtrAllocSimInfo( Aig_ManPiNum(pAig), nWords );
        Aig_ManRandomInfo( vInfoCis, 0, nWords );
        Caig_ManSimulateRound( p, vInfoCis, vInfoCos );
        Vec_PtrFree( vInfoCis );
        if ( fVerbose )
        {
            printf( "Iter %3d out of %3d and timeout %3d sec. ", i+1, nIters, TimeLimit );
            printf("Time = %7.2f sec\r", (1.0*clock()-clkTotal)/CLOCKS_PER_SEC);
        }
        if ( fMiter )
        {
            int iOut = Cec_ManFindPo( vInfoCos, nWords );
            if ( iOut >= 0 )
            {
                if ( fVerbose )
                printf( "Miter is satisfiable after simulation (output %d).\n", iOut );
                RetValue = 1;
                break;
            }
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
    if ( vInfoCos )
        Vec_PtrFree( vInfoCos );
    return RetValue > 0;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


