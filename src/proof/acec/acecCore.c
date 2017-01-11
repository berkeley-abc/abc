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
void Acec_BoxFree( Acec_Box_t * pBox )
{
    Vec_WecFreeP( &pBox->vAdds );
    Vec_WecFreeP( &pBox->vLeafs );
    Vec_WecFreeP( &pBox->vRoots );
    Vec_WecFreeP( &pBox->vLeafLits );
    Vec_WecFreeP( &pBox->vRootLits );
    Vec_WecFreeP( &pBox->vUnique );
    Vec_WecFreeP( &pBox->vShared );
    Vec_BitFreeP( &pBox->vInvHadds );
    ABC_FREE( pBox );
}
void Acec_BoxFreeP( Acec_Box_t ** ppBox )
{
    if ( *ppBox )
        Acec_BoxFree( *ppBox );
    *ppBox = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec_InsertHadd( Gia_Man_t * pNew, int In[2], int Out[2] )
{
    int And, Or;
    Out[1] = Gia_ManAppendAnd2( pNew, In[0], In[1] );
    And    = Gia_ManAppendAnd2( pNew, Abc_LitNot(In[0]), Abc_LitNot(In[1]) );
    Or     = Gia_ManAppendOr2( pNew, Out[1], And );
    Out[0] = Abc_LitNot( Or );
}
void Acec_InsertFadd( Gia_Man_t * pNew, int In[3], int Out[2] )
{
    int In2[2], Out1[2], Out2[2];
    Acec_InsertHadd( pNew, In, Out1 );
    In2[0] = Out1[0];
    In2[1] = In[2];
    Acec_InsertHadd( pNew, In2, Out2 );
    Out[0] = Out2[0];
    Out[1] = Gia_ManAppendOr2( pNew, Out1[1], Out2[1] );
}
Vec_Int_t * Acec_InsertTree( Gia_Man_t * pNew, Vec_Wec_t * vLeafMap )
{
    Vec_Int_t * vRootRanks = Vec_IntAlloc( Vec_WecSize(vLeafMap) + 5 );
    Vec_Int_t * vLevel;
    int i, In[3], Out[2];
    Vec_WecForEachLevel( vLeafMap, vLevel, i )
    {
        if ( Vec_IntSize(vLevel) == 0 )
        {
            Vec_IntPush( vRootRanks, 0 );
            continue;
        }
        while ( Vec_IntSize(vLevel) > 1 )
        {
            if ( Vec_IntSize(vLevel) == 2 )
                Vec_IntPush( vLevel, 0 );
            In[0] = Vec_IntPop( vLevel );
            In[1] = Vec_IntPop( vLevel );
            In[2] = Vec_IntPop( vLevel );
            Acec_InsertFadd( pNew, In, Out );
            Vec_IntPush( vLevel, Out[0] );
            if ( i-1 < Vec_WecSize(vLeafMap) )
                vLevel = Vec_WecEntry(vLeafMap, i+1);
            else
                vLevel = Vec_WecPushLevel(vLeafMap);
            Vec_IntPush( vLevel, Out[1] );
        }
        assert( Vec_IntSize(vLevel) == 1 );
        Vec_IntPush( vRootRanks, Vec_IntEntry(vLevel, 0) );
    }
    return vRootRanks;
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
            if ( *pBeg0 == *pBeg1 )
            {
                Vec_IntPush( vShared0, *pBeg0++ );
                Vec_IntPush( vShared1, *pBeg1++ );
            }
            else if ( *pBeg0 > *pBeg1 )
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
int Acec_InsertBox_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return pObj->Value;
    assert( Gia_ObjIsAnd(pObj) );
    Acec_InsertBox_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Acec_InsertBox_rec( pNew, p, Gia_ObjFanin1(pObj) );
    return (pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) ));
}
Vec_Int_t * Acec_BuildTree( Gia_Man_t * pNew, Gia_Man_t * p, Vec_Wec_t * vLeafLits )
{
    Vec_Wec_t * vLeafMap = Vec_WecStart( Vec_WecSize(vLeafLits) );
    Vec_Int_t * vLevel, * vRootRanks;  
    int i, k, iLit, iLitNew;
    Vec_WecForEachLevel( vLeafLits, vLevel, i )
        Vec_IntForEachEntry( vLevel, iLit, k )
        {
            Gia_Obj_t * pObj = Gia_ManObj( p, Abc_Lit2Var(iLit) );
            iLitNew = Acec_InsertBox_rec( pNew, p, pObj );
            iLitNew = Abc_LitNotCond( iLitNew, Abc_LitIsCompl(iLit) );
            Vec_WecPush( vLeafMap, i, iLitNew );
        }
    // construct map of root literals
    vRootRanks = Acec_InsertTree( pNew, vLeafMap );
    Vec_WecFree( vLeafMap );
    return vRootRanks;
}

Gia_Man_t * Acec_InsertBox( Acec_Box_t * pBox, int fAll )
{
    Gia_Man_t * p = pBox->pGia;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vRootRanks, * vLevel;
    int i, k, iLit, iLitNew;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    // implement tree
    if ( fAll )
        vRootRanks = Acec_BuildTree( pNew, p, pBox->vLeafLits );
    else
    {
        Vec_Wec_t * vLeafLits;
        assert( pBox->vShared != NULL );
        assert( pBox->vUnique != NULL );
        vRootRanks = Acec_BuildTree( p, p, pBox->vShared );
        // add these roots to the unique ones
        vLeafLits = Vec_WecDup( pBox->vUnique );
        Vec_IntForEachEntry( vRootRanks, iLit, i )
        {
            if ( i < Vec_WecSize(vLeafLits) )
                vLevel = Vec_WecEntry(vLeafLits, i);
            else
                vLevel = Vec_WecPushLevel(vLeafLits);
            Vec_IntPush( vLevel, iLit );
        }
        Vec_IntFree( vRootRanks );
        vRootRanks = Acec_BuildTree( pNew, p, vLeafLits );
        Vec_WecFree( vLeafLits );
    }
    // update polarity of literals
    Vec_WecForEachLevel( pBox->vRootLits, vLevel, i )
        Vec_IntForEachEntry( vLevel, iLit, k )
        {
            pObj = Gia_ManObj( p, Abc_Lit2Var(iLit) );
            iLitNew = k ? 0 : Vec_IntEntry( vRootRanks, k );
            pObj->Value = Abc_LitNotCond( iLitNew, Abc_LitIsCompl(iLit) );
        }
    Vec_IntFree( vRootRanks );
    // construct the outputs
    Gia_ManForEachCo( p, pObj, i )
        Acec_InsertBox_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
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
    Acec_Box_t * pBox0 = Acec_DeriveBox( pGia0 );
    Acec_Box_t * pBox1 = Acec_DeriveBox( pGia1 );
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
        int fDumpMiter = 1;
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

