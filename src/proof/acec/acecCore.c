/**CFile****************************************************************

  FileName    [acecCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [CEC for arithmetic circuits.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: acecCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acecInt.h"
#include "proof/cec/cec.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec_ManCecSetDefaultParams( Acec_ParCec_t * p )
{
    memset( p, 0, sizeof(Acec_ParCec_t) );
    p->nBTLimit       =    1000;    // conflict limit at a node
    p->TimeLimit      =       0;    // the runtime limit in seconds
    p->fMiter         =       0;    // input circuit is a miter
    p->fDualOutput    =       0;    // dual-output miter
    p->fTwoOutput     =       0;    // two-output miter
    p->fSilent        =       0;    // print no messages
    p->fVeryVerbose   =       0;    // verbose stats
    p->fVerbose       =       0;    // verbose stats
    p->iOutFail       =      -1;    // the number of failed output
}  

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Acec_FindEquivs( Gia_Man_t * pBase, Gia_Man_t * pAdd )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( pAdd );
    Gia_ManConst0(pAdd)->Value = 0;
    if ( pBase == NULL )
    {
        pBase = Gia_ManStart( Gia_ManObjNum(pAdd) );
        pBase->pName = Abc_UtilStrsav( pAdd->pName );
        pBase->pSpec = Abc_UtilStrsav( pAdd->pSpec );
        Gia_ManForEachCi( pAdd, pObj, i )
            pObj->Value = Gia_ManAppendCi(pBase);
        Gia_ManHashAlloc( pBase );
    }
    else
    {
        assert( Gia_ManCiNum(pBase) == Gia_ManCiNum(pAdd) );
        Gia_ManForEachCi( pAdd, pObj, i )
            pObj->Value = Gia_Obj2Lit( pBase, Gia_ManCi(pBase, i) );
    }
    Gia_ManForEachAnd( pAdd, pObj, i )
        pObj->Value = Gia_ManHashAnd( pBase, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    return pBase;
}
Vec_Int_t * Acec_CountRemap( Gia_Man_t * pAdd )
{
    Gia_Obj_t * pObj; int i;
    Vec_Int_t * vMapNew = Vec_IntStartFull( Gia_ManObjNum(pAdd) );
    Gia_ManForEachCand( pAdd, pObj, i )
        Vec_IntWriteEntry( vMapNew, i, Abc_Lit2Var(pObj->Value) );
    return vMapNew;
}
void Acec_ComputeEquivClasses( Gia_Man_t * pOne, Gia_Man_t * pTwo, Vec_Int_t ** pvMap1, Vec_Int_t ** pvMap2 )
{
    Gia_Man_t * pBase;
    pBase = Acec_FindEquivs( NULL, pOne );
    pBase = Acec_FindEquivs( pBase, pTwo );
    *pvMap1 = Acec_CountRemap( pOne );
    *pvMap2 = Acec_CountRemap( pTwo );
    Gia_ManStop( pBase );
}
static inline void Acec_MatchBoxesSort( int * pArray, int nSize, int * pCosts )
{
    int i, j, best_i;
    for ( i = 0; i < nSize-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < nSize; j++ )
            if ( pCosts[Abc_Lit2Var(pArray[j])] > pCosts[Abc_Lit2Var(pArray[best_i])] )
                best_i = j;
        ABC_SWAP( int, pArray[i], pArray[best_i] );
    }
}
int Acec_MatchBoxes( Acec_Box_t * pBox0, Acec_Box_t * pBox1 )
{
    Vec_Int_t * vMap0, * vMap1, * vLevel; 
    int i, nSize, nTotal;
    Acec_ComputeEquivClasses( pBox0->pGia, pBox1->pGia, &vMap0, &vMap1 );
    // sort nodes in the classes by their equivalences
    Vec_WecForEachLevel( pBox0->vLeafLits, vLevel, i )
        Acec_MatchBoxesSort( Vec_IntArray(vLevel), Vec_IntSize(vLevel), Vec_IntArray(vMap0) );
    Vec_WecForEachLevel( pBox1->vLeafLits, vLevel, i )
        Acec_MatchBoxesSort( Vec_IntArray(vLevel), Vec_IntSize(vLevel), Vec_IntArray(vMap1) );
    // reorder nodes to have the same order
    assert( pBox0->vShared == NULL );
    assert( pBox1->vShared == NULL );
    pBox0->vShared = Vec_WecStart( Vec_WecSize(pBox0->vLeafLits) );
    pBox1->vShared = Vec_WecStart( Vec_WecSize(pBox1->vLeafLits) );
    pBox0->vUnique = Vec_WecStart( Vec_WecSize(pBox0->vLeafLits) );
    pBox1->vUnique = Vec_WecStart( Vec_WecSize(pBox1->vLeafLits) );
    nSize = Abc_MinInt( Vec_WecSize(pBox0->vLeafLits), Vec_WecSize(pBox1->vLeafLits) );
    Vec_WecForEachLevelStart( pBox0->vLeafLits, vLevel, i, nSize )
        Vec_IntAppend( Vec_WecEntry(pBox0->vUnique, i), vLevel );
    Vec_WecForEachLevelStart( pBox1->vLeafLits, vLevel, i, nSize )
        Vec_IntAppend( Vec_WecEntry(pBox1->vUnique, i), vLevel );
    for ( i = 0; i < nSize; i++ )
    {
        Vec_Int_t * vShared0 = Vec_WecEntry( pBox0->vShared, i );
        Vec_Int_t * vShared1 = Vec_WecEntry( pBox1->vShared, i );
        Vec_Int_t * vUnique0 = Vec_WecEntry( pBox0->vUnique, i );
        Vec_Int_t * vUnique1 = Vec_WecEntry( pBox1->vUnique, i );

        Vec_Int_t * vLevel0 = Vec_WecEntry( pBox0->vLeafLits, i );
        Vec_Int_t * vLevel1 = Vec_WecEntry( pBox1->vLeafLits, i );
        int * pBeg0 = Vec_IntArray(vLevel0);
        int * pBeg1 = Vec_IntArray(vLevel1);
        int * pEnd0 = Vec_IntLimit(vLevel0);
        int * pEnd1 = Vec_IntLimit(vLevel1);
        while ( pBeg0 < pEnd0 && pBeg1 < pEnd1 )
        {
            int Entry0 = Abc_Lit2LitV( Vec_IntArray(vMap0), *pBeg0 );
            int Entry1 = Abc_Lit2LitV( Vec_IntArray(vMap1), *pBeg1 );
            if ( Entry0 == Entry1 )
            {
                Vec_IntPush( vShared0, *pBeg0++ );
                Vec_IntPush( vShared1, *pBeg1++ );
            }
            else if ( Entry0 > Entry1 )
                Vec_IntPush( vUnique0, *pBeg0++ );
            else 
                Vec_IntPush( vUnique1, *pBeg1++ );
        }
        while ( pBeg0 < pEnd0 )
            Vec_IntPush( vUnique0, *pBeg0++ );
        while ( pBeg1 < pEnd1 )
            Vec_IntPush( vUnique1, *pBeg1++ );
        assert( Vec_IntSize(vShared0) == Vec_IntSize(vShared1) );
        assert( Vec_IntSize(vShared0) + Vec_IntSize(vUnique0) == Vec_IntSize(vLevel0) );
        assert( Vec_IntSize(vShared1) + Vec_IntSize(vUnique1) == Vec_IntSize(vLevel1) );
    }
    Vec_IntFree( vMap0 );
    Vec_IntFree( vMap1 );
    nTotal = Vec_WecSizeSize(pBox0->vShared);
    printf( "Box0: Matched %d entries out of %d.\n", nTotal, Vec_WecSizeSize(pBox0->vLeafLits) );
    printf( "Box1: Matched %d entries out of %d.\n", nTotal, Vec_WecSizeSize(pBox1->vLeafLits) );
    return nTotal;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec_Solve( Gia_Man_t * pGia0, Gia_Man_t * pGia1, Acec_ParCec_t * pPars )
{
    int status = -1;
    Gia_Man_t * pMiter;
    Gia_Man_t * pGia0n = pGia0, * pGia1n = pGia1;
    Cec_ParCec_t ParsCec, * pCecPars = &ParsCec;
    Acec_Box_t * pBox0 = Acec_DeriveBox( pGia0, pPars->fVerbose );
    Acec_Box_t * pBox1 = Acec_DeriveBox( pGia1, pPars->fVerbose );
    if ( pBox0 == NULL || pBox1 == NULL ) // cannot match
        printf( "Cannot find arithmetic boxes in both LHS and RHS. Trying regular CEC.\n" );
    else if ( !Acec_MatchBoxes( pBox0, pBox1 ) ) // cannot find matching
        printf( "Cannot match arithmetic boxes in LHS and RHS. Trying regular CEC.\n" );
    else 
    {
        pGia0n = Acec_InsertBox( pBox0, 1 );
        pGia1n = Acec_InsertBox( pBox1, 1 );
        printf( "Found, matched, and normalized arithmetic boxes in LHS and RHS. Solving resulting CEC.\n" );
    }
    // solve regular CEC problem 
    Cec_ManCecSetDefaultParams( pCecPars );
    pCecPars->nBTLimit = pPars->nBTLimit;
    pMiter = Gia_ManMiter( pGia0n, pGia1n, 0, 1, 0, 0, pPars->fVerbose );
    if ( pMiter )
    {
        int fDumpMiter = 0;
        if ( fDumpMiter )
        {
            Abc_Print( 0, "The verification miter is written into file \"%s\".\n", "acec_miter.aig" );
            Gia_AigerWrite( pMiter, "acec_miter.aig", 0, 0 );
        }
        status = Cec_ManVerify( pMiter, pCecPars );
        ABC_SWAP( Abc_Cex_t *, pGia0->pCexComb, pMiter->pCexComb );
        Gia_ManStop( pMiter );
    }
    else
        printf( "Miter computation has failed.\n" );
    if ( pGia0n != pGia0 )
        Gia_ManStop( pGia0n );
    if ( pGia1n != pGia1 )
        Gia_ManStop( pGia1n );
    Acec_BoxFreeP( &pBox0 );
    Acec_BoxFreeP( &pBox1 );
    return status;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

