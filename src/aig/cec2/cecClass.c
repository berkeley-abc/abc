/**CFile****************************************************************

  FileName    [cecClass.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [Equivalence class representation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecClass.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

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
Aig_Man_t * Caig_ManSpecReduce( Caig_Man_t * p, int nLevels )
{
    Aig_Man_t * pAig;
    Aig_Obj_t ** pCopy;
    Aig_Obj_t * pRes0, * pRes1, * pRepr, * pNode;
    Aig_Obj_t * pMiter;
    int i;
    pAig = Aig_ManStart( p->nNodes );
    pCopy = ABC_ALLOC( Aig_Obj_t *, p->nObjs );
    pCopy[0] = Aig_ManConst1(pAig);
    for ( i = 1; i < p->nObjs; i++ )
    {
        if ( p->pFans0[i] == -1 ) // pi always has zero first fanin
        {
            pCopy[i] = Aig_ObjCreatePi( pAig );
            continue;
        }
        if ( p->pFans1[i] == -1 ) // po always has non-zero 1st fanin and zero 2nd fanin
            continue;
        pRes0 = Aig_NotCond( pCopy[Cec_Lit2Var(p->pFans0[i])], Cec_LitIsCompl(p->pFans0[i]) );
        pRes1 = Aig_NotCond( pCopy[Cec_Lit2Var(p->pFans1[i])], Cec_LitIsCompl(p->pFans1[i]) );
        pNode = pCopy[i] = Aig_And( pAig, pRes0, pRes1 );
        if ( p->pReprs[i] < 0 )
            continue;
        assert( p->pReprs[i] < i );
        pRepr = pCopy[p->pReprs[i]];
        if ( Aig_Regular(pNode) == Aig_Regular(pRepr) )
            continue;
        pCopy[i] = Aig_NotCond( pRepr, Aig_ObjPhaseReal(pRepr) ^ Aig_ObjPhaseReal(pNode) );
        if ( nLevels && ((int)Aig_Regular(pRepr)->Level > nLevels || (int)Aig_Regular(pNode)->Level > nLevels) )
            continue;
        pMiter = Aig_Exor( pAig, pNode, pRepr );
        Aig_ObjCreatePo( pAig, Aig_NotCond(pMiter, Aig_ObjPhaseReal(pMiter)) );
//        Aig_ObjCreatePo( pAig, Aig_Regular(pRepr) );
//        Aig_ObjCreatePo( pAig, Aig_Regular(pCopy[i]) );
    }
    ABC_FREE( pCopy );
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
int Caig_ManCountOne( Caig_Man_t * p, int i )
{
    int Ent, nLits = 0;
    assert( p->pReprs[i] < 0 && p->pNexts[i] > 0 );
    for ( Ent = p->pNexts[i]; Ent; Ent = p->pNexts[Ent] )
    {
        assert( p->pReprs[Ent] == i );
        nLits++;
    }
    return 1 + nLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManCountLiterals( Caig_Man_t * p )
{
    int i, nLits = 0;
    for ( i = 1; i < p->nObjs; i++ )
        if ( p->pReprs[i] < 0 && p->pNexts[i] > 0 )
            nLits += Caig_ManCountOne(p, i) - 1;
    return nLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManPrintOne( Caig_Man_t * p, int i, int Counter )
{
    int Ent;
    printf( "Class %4d :  Num = %2d  {", Counter, Caig_ManCountOne(p, i) );
    for ( Ent = i; Ent; Ent = p->pNexts[Ent] )
        printf(" %d", Ent );
    printf( " }\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManPrintClasses( Caig_Man_t * p, int fVerbose )
{
    int i, Counter = 0, Counter1 = 0, CounterX = 0, nLits;
    for ( i = 1; i < p->nObjs; i++ )
    {
        if ( p->pReprs[i] < 0 && p->pNexts[i] > 0 )
            Counter++;
        if ( p->pReprs[i] == 0 )
            Counter1++;
        if ( p->pReprs[i] < 0 && p->pNexts[i] == 0 )
            CounterX++;
    }
    nLits = Caig_ManCountLiterals( p );
    printf( "Class = %6d. Const = %6d. Unsed = %6d. Lits = %7d. All = %7d. Mem = %5.2f Mb\n", 
        Counter, Counter1, CounterX, nLits, nLits+Counter1, 1.0*p->nMemsMax/(1<<20) );
    if ( fVerbose )
    for ( i = 1; i < p->nObjs; i++ )
        if ( p->pReprs[i] < 0 && p->pNexts[i] > 0 )
            Caig_ManPrintOne( p, i, ++Counter );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManCollectSimsSimple( Caig_Man_t * p, int i )
{
    int Ent;
    Vec_PtrClear( p->vSims );
    for ( Ent = i; Ent; Ent = p->pNexts[Ent] )
        Vec_PtrPush( p->vSims, p->pSims + Ent );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManCollectSimsNormal( Caig_Man_t * p, int i )
{
    unsigned * pSim;
    int Ent;
    Vec_PtrClear( p->vSims );
    for ( Ent = i; Ent; Ent = p->pNexts[Ent] )
    {
        pSim = Caig_ManSimDeref( p, Ent );
        Vec_PtrPush( p->vSims, pSim + 1 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManCompareEqual( unsigned * p0, unsigned * p1, int nWords )
{
    int w;
    if ( (p0[0] & 1) == (p1[0] & 1) )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != p1[w] )
                return 0;
        return 1;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != ~p1[w] )
                return 0;
        return 1;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManCompareConst( unsigned * p, int nWords )
{
    int w;
    if ( p[0] & 1 )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != ~0 )
                return 0;
        return 1;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != 0 )
                return 0;
        return 1;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManClassCreate( Caig_Man_t * p, Vec_Int_t * vClass )
{
    int * pNext, Repr, Ent, i;
    assert( Vec_IntSize(vClass) > 0 );
    Vec_IntForEachEntry( vClass, Ent, i )
    {
        if ( i == 0 )
        {
            Repr = Ent;
            p->pReprs[Ent] = -1;
            pNext = p->pNexts + Ent;
        }
        else
        {
            p->pReprs[Ent] = Repr;
            *pNext = Ent;
            pNext = p->pNexts + Ent;
        }
    }
    *pNext = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManClassRefineOne( Caig_Man_t * p, int i, Vec_Ptr_t * vSims )
{
    unsigned * pSim0, * pSim1;
    int Ent, c = 0, d = 0;
    Vec_IntClear( p->vClassOld );
    Vec_IntClear( p->vClassNew );
    pSim0 = Vec_PtrEntry( vSims, c++ );
    Vec_IntPush( p->vClassOld, i );
    for ( Ent = p->pNexts[i]; Ent; Ent = p->pNexts[Ent] )
    {
        pSim1 = Vec_PtrEntry( vSims, c++ );
        if ( Caig_ManCompareEqual( pSim0, pSim1, p->nWords ) )
            Vec_IntPush( p->vClassOld, Ent );
        else
        {
            Vec_IntPush( p->vClassNew, Ent );
            Vec_PtrWriteEntry( vSims, d++, pSim1 );
        }
    }
//if ( Vec_PtrSize(vSims) > 100 )
//printf( "%d -> %d %d \n", Vec_PtrSize(vSims), Vec_IntSize(p->vClassOld), Vec_IntSize(p->vClassNew) );
    Vec_PtrShrink( vSims, d );
    if ( Vec_IntSize(p->vClassNew) == 0 )
        return 0;
    Caig_ManClassCreate( p, p->vClassOld );
    Caig_ManClassCreate( p, p->vClassNew );
    if ( Vec_IntSize(p->vClassNew) > 1 )
        return 1 + Caig_ManClassRefineOne( p, Vec_IntEntry(p->vClassNew,0), vSims );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Caig_ManHashKey( unsigned * pSim, int nWords, int nTableSize )
{
    static int s_Primes[16] = { 
        1291, 1699, 1999, 2357, 2953, 3313, 3907, 4177, 
        4831, 5147, 5647, 6343, 6899, 7103, 7873, 8147 };
    unsigned uHash = 0;
    int i;
    if ( pSim[0] & 1 )
        for ( i = 0; i < nWords; i++ )
            uHash ^= ~pSim[i] * s_Primes[i & 0xf];
    else
        for ( i = 0; i < nWords; i++ )
            uHash ^= pSim[i] * s_Primes[i & 0xf];
    return (int)(uHash % nTableSize);

}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManClassesCreate( Caig_Man_t * p )
{
    int * pTable, nTableSize, i, Key;
    nTableSize = Aig_PrimeCudd( 100 + p->nObjs / 10 );
    pTable = ABC_CALLOC( int, nTableSize );
    p->pReprs = ABC_ALLOC( int, p->nObjs );
    p->pNexts = ABC_CALLOC( int, p->nObjs );
    for ( i = 1; i < p->nObjs; i++ )
    {
        if ( p->pFans0[i] > 0 && p->pFans1[i] == -1 ) // po always has non-zero 1st fanin and zero 2nd fanin
            continue;
        if ( Caig_ManCompareConst( p->pSims + i, 1 ) )
        {
            p->pReprs[i] = 0;
            continue;
        }
        Key = Caig_ManHashKey( p->pSims + i, 1, nTableSize );
        if ( pTable[Key] == 0 )
            p->pReprs[i] = -1;
        else
        {
            p->pNexts[ pTable[Key] ] = i;
            p->pReprs[i] = p->pReprs[ pTable[Key] ];
            if ( p->pReprs[i] == -1 )
                p->pReprs[i] = pTable[Key];
        }
        pTable[Key] = i;
    }
    ABC_FREE( pTable );
Caig_ManPrintClasses( p, 0 );
    // refine classes
    for ( i = 1; i < p->nObjs; i++ )
        if ( p->pReprs[i] < 0 && p->pNexts[i] > 0 )
        {
            Caig_ManCollectSimsSimple( p, i );
            Caig_ManClassRefineOne( p, i, p->vSims );
        }
    // clean memory
    memset( p->pSims, 0, sizeof(unsigned) * p->nObjs );
Caig_ManPrintClasses( p, 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManSimulateSimple( Caig_Man_t * p )
{
    unsigned Res0, Res1;
    int i;
    for ( i = 1; i < p->nObjs; i++ )
    {
        if ( p->pFans0[i] == -1 ) // pi
        {
            p->pSims[i] = Aig_ManRandom( 0 );
            continue;
        }
        if ( p->pFans1[i] == -1 ) // po always has non-zero 1st fanin and zero 2nd fanin
            continue;
        Res0 = p->pSims[Cec_Lit2Var(p->pFans0[i])];
        Res1 = p->pSims[Cec_Lit2Var(p->pFans1[i])];
        p->pSims[i] = (Cec_LitIsCompl(p->pFans0[i]) ? ~Res0: Res0) &
                      (Cec_LitIsCompl(p->pFans1[i]) ? ~Res1: Res1);
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Caig_ManProcessRefined( Caig_Man_t * p, Vec_Int_t * vRefined )
{
    Vec_Int_t * vClasses;
    int * pTable, nTableSize, i, Key, iNode;
    unsigned * pSim;
    if ( Vec_IntSize(vRefined) == 0 )
        return;
    nTableSize = Aig_PrimeCudd( 100 + Vec_IntSize(vRefined) / 5 );
    pTable = ABC_CALLOC( int, nTableSize );
    vClasses = Vec_IntAlloc( 100 );
    Vec_IntForEachEntry( vRefined, iNode, i )
    {
        pSim = Caig_ManSimRead( p, iNode );
        assert( !Caig_ManCompareConst( pSim + 1, p->nWords ) );
        Key = Caig_ManHashKey( pSim + 1, p->nWords, nTableSize );
        if ( pTable[Key] == 0 )
        {
            assert( p->pReprs[iNode] == 0 );
            assert( p->pNexts[iNode] == 0 );
            p->pReprs[iNode] = -1;
            Vec_IntPush( vClasses, iNode );
        }
        else
        {
            p->pNexts[ pTable[Key] ] = iNode;
            p->pReprs[iNode] = p->pReprs[ pTable[Key] ];
            if ( p->pReprs[iNode] == -1 )
                p->pReprs[iNode] = pTable[Key];
            assert( p->pReprs[iNode] > 0 );
        }
        pTable[Key] = iNode;
    }
    ABC_FREE( pTable );
    // refine classes
    Vec_IntForEachEntry( vClasses, iNode, i )
    {
        if ( p->pNexts[iNode] == 0 )
        {
            Caig_ManSimDeref( p, iNode );
            continue;
        }
        Caig_ManCollectSimsNormal( p, iNode );
        Caig_ManClassRefineOne( p, iNode, p->vSims );
    }
    Vec_IntFree( vClasses );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Caig_Man_t * Caig_ManClassesPrepare( Aig_Man_t * pAig, int nWords, int nIters )
{
    Vec_Ptr_t * vInfo;
    Caig_Man_t * p;
    int i;
    Aig_ManRandom( 1 );
    p = Caig_ManCreate( pAig );
    p->nWords = 1;
    Caig_ManSimulateSimple( p );
    Caig_ManClassesCreate( p );
    p->nWords = nWords;
    for ( i = 0; i < nIters; i++ )
    {
        p->nWords = i + 1;
        Caig_ManSimMemRelink( p );
        p->nMemsMax = 0;

        vInfo = Vec_PtrAllocSimInfo( p->nPis, p->nWords );
        Aig_ManRandomInfo( vInfo, 0, p->nWords );
        Caig_ManSimulateRound( p, vInfo, NULL );
        Vec_PtrFree( vInfo );
Caig_ManPrintClasses( p, 0 );
    }

    p->nWords = nWords;
    Caig_ManSimMemRelink( p );
    p->nMemsMax = 0;
    return p;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


