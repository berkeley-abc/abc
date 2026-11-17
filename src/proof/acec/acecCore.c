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
#include "misc/util/utilTruth.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define TRUTH_UNUSED 0x1234567812345678

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
void Acec_VerifyClasses( Gia_Man_t * p, Vec_Wec_t * vLits, Vec_Wec_t * vReprs )
{
    Vec_Ptr_t * vFunc = Vec_PtrAlloc( Vec_WecSize(vLits) );
    Vec_Int_t * vSupp = Vec_IntAlloc( 100 );
    Vec_Wrd_t * vTemp = Vec_WrdStart( Gia_ManObjNum(p) );
    Vec_Int_t * vLevel;
    int i, j, k, Entry, Entry2, nOvers = 0, nErrors = 0;
    Vec_WecForEachLevel( vLits, vLevel, i )
    {
        Vec_Wrd_t * vTruths = Vec_WrdAlloc( Vec_IntSize(vLevel) );
        Vec_IntForEachEntry( vLevel, Entry, k )
        {
            word Truth = Gia_ObjComputeTruth6Cis( p, Entry, vSupp, vTemp );
            if ( Vec_IntSize(vSupp) > 6  )
            {
                nOvers++;
                Vec_WrdPush( vTruths, TRUTH_UNUSED );
                continue;
            }
            vSupp->nSize = Abc_Tt6MinBase( &Truth, vSupp->pArray, vSupp->nSize );
            if ( Vec_IntSize(vSupp) > 5  )
            {
                nOvers++;
                Vec_WrdPush( vTruths, TRUTH_UNUSED );
                continue;
            }
            Vec_WrdPush( vTruths, Truth );
        }
        Vec_PtrPush( vFunc, vTruths );
    }
    if ( nOvers )
        printf( "Detected %d oversize support nodes.\n", nOvers );
    Vec_IntFree( vSupp );
    Vec_WrdFree( vTemp );
    // verify the classes
    Vec_WecForEachLevel( vReprs, vLevel, i )
    {
        Vec_Wrd_t * vTruths = (Vec_Wrd_t *)Vec_PtrEntry( vFunc, i );
        Vec_IntForEachEntry( vLevel, Entry, k )
        Vec_IntForEachEntryStart( vLevel, Entry2, j, k+1 )
        {
            word Truth = Vec_WrdEntry( vTruths, k );
            word Truth2 = Vec_WrdEntry( vTruths, j );
            if ( Entry == Entry2 )
            {
                nErrors++;
                if ( Truth != Truth2 && Truth != TRUTH_UNUSED && Truth2 != TRUTH_UNUSED )
                    printf( "Rank %d:  Lit %d and %d do not pass verification.\n", i, k, j );
            }
            if ( Entry == Abc_LitNot(Entry2) )
            {
                nErrors++;
                if ( Truth != ~Truth2 && Truth != TRUTH_UNUSED && Truth2 != TRUTH_UNUSED )
                    printf( "Rank %d:  Lit %d and %d do not pass verification.\n", i, k, j );
            }
        }
    }
    if ( nErrors )
        printf( "Total errors in equivalence classes = %d.\n", nErrors );
    Vec_VecFree( (Vec_Vec_t *)vFunc );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Acec_CommonStart( Gia_Man_t * pBase, Gia_Man_t * pAdd )
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
void Acec_CommonFinish( Gia_Man_t * pBase )
{
    int Id;
    Gia_ManCreateRefs( pBase );
    Gia_ManForEachAndId( pBase, Id )
        if ( Gia_ObjRefNumId(pBase, Id) == 0 )
            Gia_ManAppendCo( pBase, Abc_Var2Lit(Id,0) );
}
Vec_Int_t * Acec_CountRemap( Gia_Man_t * pAdd, Gia_Man_t * pBase )
{
    Gia_Obj_t * pObj; int i;
    Vec_Int_t * vMapNew = Vec_IntStartFull( Gia_ManObjNum(pAdd) );
    Gia_ManSetPhase( pAdd );
    Vec_IntWriteEntry( vMapNew, 0, 0 );
    Gia_ManForEachCand( pAdd, pObj, i )
    {
        int iObjBase = Abc_Lit2Var(pObj->Value);
        Gia_Obj_t * pObjBase = Gia_ManObj( pBase, iObjBase );
        int iObjRepr = Abc_Lit2Var(pObjBase->Value);
        Vec_IntWriteEntry( vMapNew, i, Abc_Var2Lit(iObjRepr, Gia_ObjPhase(pObj)) );
    }
    return vMapNew;
}
void Acec_ComputeEquivClasses( Gia_Man_t * pOne, Gia_Man_t * pTwo, Vec_Int_t ** pvMap1, Vec_Int_t ** pvMap2 )
{
    abctime clk = Abc_Clock();
    Gia_Man_t * pBase, * pRepr;
    pBase = Acec_CommonStart( NULL, pOne );
    pBase = Acec_CommonStart( pBase, pTwo );
    Acec_CommonFinish( pBase );
    //Gia_ManShow( pBase, NULL, 0, 0, 0 );
    pRepr = Gia_ManComputeGiaEquivs( pBase, 100, 0 );
    *pvMap1 = Acec_CountRemap( pOne, pBase );
    *pvMap2 = Acec_CountRemap( pTwo, pBase );
    Gia_ManStop( pBase );
    Gia_ManStop( pRepr );
    printf( "Finished computing equivalent nodes.  " );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}
void Acec_MatchBoxesSort( int * pArray, int nSize, int * pCostLits )
{
    int i, j, best_i;
    for ( i = 0; i < nSize-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < nSize; j++ )
            if ( Abc_Lit2LitL(pCostLits, pArray[j]) > Abc_Lit2LitL(pCostLits, pArray[best_i]) )
                best_i = j;
        ABC_SWAP( int, pArray[i], pArray[best_i] );
    }
}
void Acec_MatchPrintEquivLits( Gia_Man_t * p, Vec_Wec_t * vLits, int * pCostLits, int fVerbose )
{
    Vec_Int_t * vSupp;
    Vec_Wrd_t * vTemp;
    Vec_Int_t * vLevel;
    int i, k, Entry;
    printf( "Leaf literals and their classes:\n" );
    Vec_WecForEachLevel( vLits, vLevel, i )
    {
        if ( Vec_IntSize(vLevel) == 0 )
            continue;
        printf( "Rank %2d : %2d  ", i, Vec_IntSize(vLevel) );
        Vec_IntForEachEntry( vLevel, Entry, k )
            printf( "%s%d(%d) ", Abc_LitIsCompl(Entry) ? "-":"+", Abc_Lit2Var(Entry), Abc_Lit2LitL(pCostLits, Entry) );
        printf( "\n" );
    }
    if ( !fVerbose )
        return;
    vSupp = Vec_IntAlloc( 100 );
    vTemp = Vec_WrdStart( Gia_ManObjNum(p) );
    Vec_WecForEachLevel( vLits, vLevel, i )
    {
        //if ( i != 20 )
        //    continue;
        if ( Vec_IntSize(vLevel) == 0 )
            continue;
        Vec_IntForEachEntry( vLevel, Entry, k )
        {
            word Truth = Gia_ObjComputeTruth6Cis( p, Entry, vSupp, vTemp );
/*
            {
                int iObj = Abc_Lit2Var(Entry);
                Gia_Man_t * pGia0 = Gia_ManDupAndCones( p, &iObj, 1, 1 );
                Gia_ManShow( pGia0, NULL, 0, 0, 0 );
                Gia_ManStop( pGia0 );
            }
*/
            printf( "Rank = %4d : ", i );
            printf( "Obj = %4d  ", Abc_Lit2Var(Entry) );
            if ( Vec_IntSize(vSupp) > 6  )
            {
                printf( "Supp = %d.\n", Vec_IntSize(vSupp) );
                continue;
            }
            vSupp->nSize = Abc_Tt6MinBase( &Truth, vSupp->pArray, vSupp->nSize );
            if ( Vec_IntSize(vSupp) > 5  )
            {
                printf( "Supp = %d.\n", Vec_IntSize(vSupp) );
                continue;
            }
            Extra_PrintHex( stdout, (unsigned*)&Truth, Vec_IntSize(vSupp) );
            if ( Vec_IntSize(vSupp) == 4 ) printf( "    " );
            if ( Vec_IntSize(vSupp) == 3 ) printf( "      " );
            if ( Vec_IntSize(vSupp) <= 2 ) printf( "       " );
            printf( "  " );
            Vec_IntPrint( vSupp );
        }
        printf( "\n" );
    }
    Vec_IntFree( vSupp );
    Vec_WrdFree( vTemp );
}
Vec_Wec_t * Acec_MatchCopy( Vec_Wec_t * vLits, Vec_Int_t * vMap )
{
    Vec_Wec_t * vRes = Vec_WecStart( Vec_WecSize(vLits) );
    Vec_Int_t * vLevel; int i, k, iLit;
    Vec_WecForEachLevel( vLits, vLevel, i )
        Vec_IntForEachEntry( vLevel, iLit, k )
            Vec_WecPush( vRes, i, Abc_Lit2LitL(Vec_IntArray(vMap), iLit) );
    return vRes;
}
int Acec_MatchCountCommon( Vec_Wec_t * vLits1, Vec_Wec_t * vLits2, int Shift )
{
    Vec_Int_t * vRes = Vec_IntAlloc( 100 );
    Vec_Int_t * vLevel1, * vLevel2; 
    int i, nCommon = 0;
    Vec_WecForEachLevel( vLits1, vLevel1, i )
    {
        if ( i+Shift < 0 || i+Shift >= Vec_WecSize(vLits2) )
            continue;
        vLevel2 = Vec_WecEntry( vLits2, i+Shift );
        nCommon += Vec_IntTwoFindCommonReverse( vLevel1, vLevel2, vRes );
    }
    Vec_IntFree( vRes );
    return nCommon;
}
void Vec_IntInsertOrder( Vec_Int_t * vLits, Vec_Int_t * vClasses, int Lit, int Class )
{
    int i;
    for ( i = Vec_IntSize(vClasses)-1; i >= 0; i-- )
        if ( Vec_IntEntry(vClasses,i) >= Class )
            break;
    Vec_IntInsert( vLits, i+1, Lit );
    Vec_IntInsert( vClasses, i+1, Class );
}
void Acec_MoveDuplicates( Vec_Wec_t * vLits, Vec_Wec_t * vClasses )
{
    Vec_Int_t * vLevel1, * vLevel2; 
    int i, k, Prev, This, Entry, Counter = 0;
    Vec_WecForEachLevel( vLits, vLevel1, i )
    {
        if ( i == Vec_WecSize(vLits) - 1 )
            break;
        vLevel2 = Vec_WecEntry(vClasses, i);
        assert( Vec_IntSize(vLevel1) == Vec_IntSize(vLevel2) );
        Prev = -1;
        Vec_IntForEachEntry( vLevel2, This, k )
        {
            if ( Prev != This )
            {
                Prev = This;
                continue;
            }
            Prev = -1;
            Entry = Vec_IntEntry( vLevel1, k );

            Vec_IntDrop( vLevel1, k );
            Vec_IntDrop( vLevel2, k-- );

            Vec_IntDrop( vLevel1, k );
            Vec_IntDrop( vLevel2, k-- );

            Vec_IntInsertOrder( Vec_WecEntry(vLits, i+1), Vec_WecEntry(vClasses, i+1), Entry, This );

            assert( Vec_IntSize(vLevel1)                  == Vec_IntSize(vLevel2) );
            assert( Vec_IntSize(Vec_WecEntry(vLits, i+1)) == Vec_IntSize(Vec_WecEntry(vClasses, i+1)) );
            Counter++;
        }
    }
    printf( "Moved %d pairs of PPs to normalize the matrix.\n", Counter );
}

void Acec_MatchCheckShift( Gia_Man_t * pGia0, Gia_Man_t * pGia1, Vec_Wec_t * vLits0, Vec_Wec_t * vLits1, Vec_Int_t * vMap0, Vec_Int_t * vMap1, Vec_Wec_t * vRoots0, Vec_Wec_t * vRoots1 )
{
    Vec_Wec_t * vRes0 = Acec_MatchCopy( vLits0, vMap0 );
    Vec_Wec_t * vRes1 = Acec_MatchCopy( vLits1, vMap1 );
    int nCommon      = Acec_MatchCountCommon( vRes0, vRes1,  0 );
    int nCommonPlus  = Acec_MatchCountCommon( vRes0, vRes1,  1 );
    int nCommonMinus = Acec_MatchCountCommon( vRes0, vRes1, -1 );
    if ( nCommonPlus >= nCommonMinus && nCommonPlus > nCommon )
    {
        Vec_WecInsertLevel( vLits0, 0 );
        Vec_WecInsertLevel( vRoots0, 0 );
        Vec_WecInsertLevel( vRes0, 0 );
        printf( "Shifted one level up.\n" );
    }
    else if ( nCommonMinus > nCommonPlus && nCommonMinus > nCommon )
    {
        Vec_WecInsertLevel( vLits1, 0 );
        Vec_WecInsertLevel( vRoots1, 0 );
        Vec_WecInsertLevel( vRes1, 0 );
        printf( "Shifted one level down.\n" );
    }
    Acec_MoveDuplicates( vLits0, vRes0 );
    Acec_MoveDuplicates( vLits1, vRes1 );

    //Vec_WecPrintLits( vLits1 );
    //printf( "Input literals:\n" );
    //Vec_WecPrintLits( vLits0 );
    //printf( "Equiv classes:\n" );
    //Vec_WecPrintLits( vRes0 );
    //printf( "Input literals:\n" );
    //Vec_WecPrintLits( vLits1 );
    //printf( "Equiv classes:\n" );
    //Vec_WecPrintLits( vRes1 );
    //Acec_VerifyClasses( pGia0, vLits0, vRes0 );
    //Acec_VerifyClasses( pGia1, vLits1, vRes1 );
    Vec_WecFree( vRes0 );
    Vec_WecFree( vRes1 );
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
    Acec_MatchCheckShift( pBox0->pGia, pBox1->pGia, pBox0->vLeafLits, pBox1->vLeafLits, vMap0, vMap1, pBox0->vRootLits, pBox1->vRootLits );
    
    //Acec_MatchPrintEquivLits( pBox0->pGia, pBox0->vLeafLits, Vec_IntArray(vMap0), 0 );
    //Acec_MatchPrintEquivLits( pBox1->pGia, pBox1->vLeafLits, Vec_IntArray(vMap1), 0 );
    //printf( "Outputs:\n" );
    //Vec_WecPrintLits( pBox0->vRootLits );
    //printf( "Outputs:\n" );
    //Vec_WecPrintLits( pBox1->vRootLits );

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
            int Entry0 = Abc_Lit2LitL( Vec_IntArray(vMap0), *pBeg0 );
            int Entry1 = Abc_Lit2LitL( Vec_IntArray(vMap1), *pBeg1 );
            assert( *pBeg0 && *pBeg1 );
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
    nTotal = Vec_WecSizeSize(pBox0->vShared);
    printf( "Box0: Matched %d entries out of %d.\n", nTotal, Vec_WecSizeSize(pBox0->vLeafLits) );
    printf( "Box1: Matched %d entries out of %d.\n", nTotal, Vec_WecSizeSize(pBox1->vLeafLits) );

    //Acec_MatchPrintEquivLits( pBox0->pGia, pBox0->vShared, Vec_IntArray(vMap0), 0 );
    //Acec_MatchPrintEquivLits( pBox1->pGia, pBox1->vShared, Vec_IntArray(vMap1), 0 );
    //printf( "\n" );

    //Acec_MatchPrintEquivLits( pBox0->pGia, pBox0->vUnique, Vec_IntArray(vMap0), 0 );
    //Acec_MatchPrintEquivLits( pBox1->pGia, pBox1->vUnique, Vec_IntArray(vMap1), 0 );

    Vec_IntFree( vMap0 );
    Vec_IntFree( vMap1 );
    return nTotal;
}



/**Function*************************************************************

  Synopsis    [Checks arithmetic CEC and validates counterexamples on the originals.]

  Description [Preserves legacy reconstruction and search policy. A negative
  result is reported only after its witness satisfies the original miter.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec_SolveAig( Gia_Man_t * pGia0, Gia_Man_t * pGia1, Acec_ParCec_t * pPars )
{
    int Status = -1;
    abctime clk = Abc_Clock();
    Gia_Man_t * pMiter = NULL, * pOriginal = NULL;
    Gia_Man_t * pGia0n = pGia0, * pGia1n = pGia1;
    Acec_Box_t * pBox0 = NULL, * pBox1 = NULL;
    Cec_ParCec_t ParsCec;
    pPars->iOutFail = -1;
    if ( pGia0 ) { Abc_CexFree(pGia0->pCexComb); pGia0->pCexComb = NULL; }
    if ( !pGia0 || !pGia1 || Gia_ManCiNum(pGia0) != Gia_ManCiNum(pGia1) ||
         Gia_ManCoNum(pGia0) != Gia_ManCoNum(pGia1) || Gia_ManRegNum(pGia0) != Gia_ManRegNum(pGia1) )
    {
        if ( !pPars->fSilent ) Abc_Print( 1, "Cannot compare networks with different interfaces.\n" );
        goto finish;
    }
    pBox0 = Acec_ProduceBox( pGia0, pPars->fVerbose );
    pBox1 = Acec_ProduceBox( pGia1, pPars->fVerbose );
    if ( pBox0 == NULL || pBox1 == NULL )
    {
        if ( !pPars->fSilent ) Abc_Print( 1, "Cannot find arithmetic boxes in both LHS and RHS. Trying regular CEC.\n" );
    }
    else if ( !Acec_MatchBoxes( pBox0, pBox1 ) )
    {
        if ( !pPars->fSilent ) Abc_Print( 1, "Cannot match arithmetic boxes in LHS and RHS. Trying regular CEC.\n" );
    }
    else
    {
        pGia0n = Acec_InsertBox( pBox0, 0 );
        pGia1n = Acec_InsertBox( pBox1, 0 );
        if ( !pPars->fSilent )
        {
            Abc_Print( 1, "Matching of adder trees in LHS and RHS succeeded.  " );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        }
    }
    Cec_ManCecSetDefaultParams( &ParsCec );
    ParsCec.nBTLimit = pPars->nBTLimit;
    // Do not publish a transformed result before validating its witness.
    ParsCec.fSilent = 1;
    ParsCec.fVerbose = pPars->fVerbose;
    ParsCec.fVeryVerbose = pPars->fVeryVerbose;
    pMiter = Gia_ManMiter( pGia0n, pGia1n, 0, 1, 0, 0, 0 );
    if ( !pMiter ) goto finish;
    Status = Cec_ManVerify( pMiter, &ParsCec );
    if ( Status == 0 )
    {
        Abc_Cex_t * pCex = pMiter->pCexComb;
        pOriginal = Gia_ManMiter( pGia0, pGia1, 0, 1, 0, 0, 0 );
        if ( pOriginal && pCex && pCex->nRegs == 0 && pCex->iFrame == 0 &&
             pCex->nPis == Gia_ManCiNum(pOriginal) && pCex->nBits == pCex->nPis &&
             pCex->iPo >= 0 && pCex->iPo < Gia_ManCoNum(pOriginal)/2 && Gia_ManVerifyCex(pOriginal, pCex, 1) )
        {
            pPars->iOutFail = pCex->iPo;
            pGia0->pCexComb = pCex;
            pMiter->pCexComb = NULL;
        }
        else
        {
            Status = -1;
            if ( !pPars->fSilent ) Abc_Print( 1, "Counterexample failed validation on the original networks.\n" );
        }
    }
finish:
    if ( pOriginal ) Gia_ManStop( pOriginal );
    if ( pMiter ) Gia_ManStop( pMiter );
    if ( pGia0n != pGia0 ) Gia_ManStop( pGia0n );
    if ( pGia1n != pGia1 ) Gia_ManStop( pGia1n );
    Acec_BoxFreeP( &pBox0 );
    Acec_BoxFreeP( &pBox1 );
    if ( !pPars->fSilent )
    {
        Abc_Print( 1, "Networks are %s.  ", Status == 1 ? "equivalent" : Status == 0 ? "NOT EQUIVALENT" : "UNDECIDED" );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        if ( Status == 0 ) Abc_Print( 1, "Original networks differ at output %d (validated counterexample).\n", pPars->iOutFail );
    }
    return Status;
}

/**Function*************************************************************

  Synopsis    [Expands native XOR/MUX nodes before using the legacy detector.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec_Solve( Gia_Man_t * pGia0, Gia_Man_t * pGia1, Acec_ParCec_t * pPars )
{
    Gia_Man_t * pWork0 = pGia0, * pWork1 = pGia1;
    int Status;
    if ( pGia0 && (Gia_ManXorNum(pGia0) || Gia_ManMuxNum(pGia0)) ) pWork0 = Gia_ManDupNoMuxes(pGia0, 1);
    if ( pGia1 && (Gia_ManXorNum(pGia1) || Gia_ManMuxNum(pGia1)) ) pWork1 = Gia_ManDupNoMuxes(pGia1, 1);
    Status = Acec_SolveAig( pWork0, pWork1, pPars );
    if ( pWork0 != pGia0 )
    {
        Abc_CexFree( pGia0->pCexComb );
        pGia0->pCexComb = pWork0->pCexComb; pWork0->pCexComb = NULL;
        Gia_ManStop( pWork0 );
    }
    if ( pWork1 != pGia1 ) Gia_ManStop( pWork1 );
    return Status;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

