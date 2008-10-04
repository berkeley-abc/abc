/**CFile****************************************************************

  FileName    [sswSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [On-demand uniqueness constraints.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswSat.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the result of merging the two vectors.]

  Description [Assumes that the vectors are sorted in the increasing order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrTwoMerge( Vec_Ptr_t * vArr1, Vec_Ptr_t * vArr2, Vec_Ptr_t * vArr )
{
    Aig_Obj_t ** pBeg  = (Aig_Obj_t **)vArr->pArray;
    Aig_Obj_t ** pBeg1 = (Aig_Obj_t **)vArr1->pArray;
    Aig_Obj_t ** pBeg2 = (Aig_Obj_t **)vArr2->pArray;
    Aig_Obj_t ** pEnd1 = (Aig_Obj_t **)vArr1->pArray + vArr1->nSize;
    Aig_Obj_t ** pEnd2 = (Aig_Obj_t **)vArr2->pArray + vArr2->nSize;
    Vec_PtrGrow( vArr, Vec_PtrSize(vArr1) + Vec_PtrSize(vArr2) );
    pBeg  = (Aig_Obj_t **)vArr->pArray;
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        if ( (*pBeg1)->Id == (*pBeg2)->Id )
            *pBeg++ = *pBeg1++, pBeg2++;
        else if ( (*pBeg1)->Id < (*pBeg2)->Id )
            *pBeg++ = *pBeg1++;
        else 
            *pBeg++ = *pBeg2++;
    }
    while ( pBeg1 < pEnd1 )
        *pBeg++ = *pBeg1++;
    while ( pBeg2 < pEnd2 )
        *pBeg++ = *pBeg2++;
    vArr->nSize = pBeg - (Aig_Obj_t **)vArr->pArray;
    assert( vArr->nSize <= vArr->nCap );
    assert( vArr->nSize >= vArr1->nSize );
    assert( vArr->nSize >= vArr2->nSize );
}

/**Function*************************************************************

  Synopsis    [Returns the result of merging the two vectors.]

  Description [Assumes that the vectors are sorted in the increasing order.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_PtrTwoCommon( Vec_Ptr_t * vArr1, Vec_Ptr_t * vArr2, Vec_Ptr_t * vArr )
{
    Aig_Obj_t ** pBeg  = (Aig_Obj_t **)vArr->pArray;
    Aig_Obj_t ** pBeg1 = (Aig_Obj_t **)vArr1->pArray;
    Aig_Obj_t ** pBeg2 = (Aig_Obj_t **)vArr2->pArray;
    Aig_Obj_t ** pEnd1 = (Aig_Obj_t **)vArr1->pArray + vArr1->nSize;
    Aig_Obj_t ** pEnd2 = (Aig_Obj_t **)vArr2->pArray + vArr2->nSize;
    Vec_PtrGrow( vArr, AIG_MIN( Vec_PtrSize(vArr1), Vec_PtrSize(vArr2) ) );
    pBeg  = (Aig_Obj_t **)vArr->pArray;
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        if ( (*pBeg1)->Id == (*pBeg2)->Id )
            *pBeg++ = *pBeg1++, pBeg2++;
        else if ( (*pBeg1)->Id < (*pBeg2)->Id )
//            *pBeg++ = *pBeg1++;
            pBeg1++;
        else 
//            *pBeg++ = *pBeg2++;
            pBeg2++;
    }
//    while ( pBeg1 < pEnd1 )
//        *pBeg++ = *pBeg1++;
//    while ( pBeg2 < pEnd2 )
//        *pBeg++ = *pBeg2++;
    vArr->nSize = pBeg - (Aig_Obj_t **)vArr->pArray;
    assert( vArr->nSize <= vArr->nCap );
    assert( vArr->nSize <= vArr1->nSize );
    assert( vArr->nSize <= vArr2->nSize );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if uniqueness constraints can be added.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ManUniqueOne( Ssw_Man_t * p, Aig_Obj_t * pRepr, Aig_Obj_t * pObj )
{
    int fVerbose = 1;
    Aig_Obj_t * ppObjs[2], * pTemp;
    Vec_Ptr_t * vSupp, * vSupp2;
    int i, k, Value0, Value1, RetValue;
    assert( p->pPars->nFramesK > 1 );

    vSupp  = Vec_PtrAlloc( 100 );
    vSupp2 = Vec_PtrAlloc( 100 );
    Vec_PtrClear( p->vCommon );

    // compute the first support in terms of LOs
    ppObjs[0] = pRepr; 
    ppObjs[1] = pObj;
    Aig_SupportNodes( p->pAig, ppObjs, 2, vSupp );
    // modify support to be in terms of LIs
    k = 0;
    Vec_PtrForEachEntry( vSupp, pTemp, i )
        if ( Saig_ObjIsLo(p->pAig, pTemp) )
            Vec_PtrWriteEntry( vSupp, k++, Saig_ObjLoToLi(p->pAig, pTemp) );
    Vec_PtrShrink( vSupp, k );
    // compute the support of support
    Aig_SupportNodes( p->pAig, (Aig_Obj_t **)Vec_PtrArray(vSupp), Vec_PtrSize(vSupp), vSupp2 );
    // return support to LO
    Vec_PtrForEachEntry( vSupp, pTemp, i )
        Vec_PtrWriteEntry( vSupp, i, Saig_ObjLiToLo(p->pAig, pTemp) );
    // find the number of common vars
    Vec_PtrSort( vSupp, Aig_ObjCompareIdIncrease );
    Vec_PtrSort( vSupp2, Aig_ObjCompareIdIncrease );
    Vec_PtrTwoCommon( vSupp, vSupp2, p->vCommon );
//    Vec_PtrTwoMerge( vSupp, vSupp2, p->vCommon );

/*
    {
        Vec_Ptr_t * vNew = Vec_PtrDup(vSupp);
        Vec_PtrUniqify( vNew, Aig_ObjCompareIdIncrease );
        if ( Vec_PtrSize(vNew) != Vec_PtrSize(vSupp) )
            printf( "Not unique!\n" );
        Vec_PtrFree( vNew );
        Vec_PtrForEachEntry( vSupp, pTemp, i )
            printf( "%d ", pTemp->Id );
        printf( "\n" );
    }
    {
        Vec_Ptr_t * vNew = Vec_PtrDup(vSupp2);
        Vec_PtrUniqify( vNew, Aig_ObjCompareIdIncrease );
        if ( Vec_PtrSize(vNew) != Vec_PtrSize(vSupp2) )
            printf( "Not unique!\n" );
        Vec_PtrFree( vNew );
        Vec_PtrForEachEntry( vSupp2, pTemp, i )
            printf( "%d ", pTemp->Id );
        printf( "\n" );
    }
    {
        Vec_Ptr_t * vNew = Vec_PtrDup(p->vCommon);
        Vec_PtrUniqify( vNew, Aig_ObjCompareIdIncrease );
        if ( Vec_PtrSize(vNew) != Vec_PtrSize(p->vCommon) )
            printf( "Not unique!\n" );
        Vec_PtrFree( vNew );
        Vec_PtrForEachEntry( p->vCommon, pTemp, i )
            printf( "%d ", pTemp->Id );
        printf( "\n" );
    }
*/

    if ( fVerbose )
        printf( "Node = %5d : One = %3d. Two = %3d. Common = %3d.  ",
            Aig_ObjId(pObj), Vec_PtrSize(vSupp), Vec_PtrSize(vSupp2), Vec_PtrSize(p->vCommon) );

//    Vec_PtrClear( vSupp );
//    Vec_PtrForEachEntry( vSupp2, pTemp, i )
//        Vec_PtrPush( vSupp, pTemp );

    // check the current values
    RetValue = 1;
//    Vec_PtrForEachEntry( p->vCommon, pTemp, i )
    Vec_PtrForEachEntry( vSupp, pTemp, i )
    {
        Value0 = Ssw_ManGetSatVarValue( p, pTemp, 0 );
        Value1 = Ssw_ManGetSatVarValue( p, pTemp, 1 );
        if ( Value0 != Value1 )
            RetValue = 0;
        if ( fVerbose )
            printf( "%d", Value0 ^ Value1 );
    }
    if ( Vec_PtrSize(p->vCommon) == 0 )
        RetValue = 0;

    Vec_PtrForEachEntry( vSupp, pTemp, i )
        printf( " %d", pTemp->Id );

    if ( fVerbose )
        printf( "\n" );


    Vec_PtrClear( p->vCommon );
    Vec_PtrForEachEntry( vSupp, pTemp, i )
        Vec_PtrPush( p->vCommon, pTemp );

    Vec_PtrFree( vSupp );
    Vec_PtrFree( vSupp2 );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Returns the output of the uniqueness constraint.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ManUniqueAddConstraint( Ssw_Man_t * p, Vec_Ptr_t * vCommon, int f1, int f2 )
{
    Aig_Obj_t * pObj, * pObj1New, * pObj2New, * pMiter, * pTotal;
    int i, pLits[2];
//    int RetValue;
    assert( Vec_PtrSize(vCommon) > 0 );
    // generate the constraint
    pTotal = Aig_ManConst0(p->pFrames);
    Vec_PtrForEachEntry( vCommon, pObj, i )
    {
        assert( Saig_ObjIsLo(p->pAig, pObj) );
        pObj1New = Ssw_ObjFrame( p, pObj, f1 );
        pObj2New = Ssw_ObjFrame( p, pObj, f2 );
        pMiter = Aig_Exor( p->pFrames, pObj1New, pObj2New );
        pTotal = Aig_Or( p->pFrames, pTotal, pMiter );
    }
/*
    if ( Aig_ObjIsConst1(Aig_Regular(pTotal)) )
    {
//        printf( "Skipped\n" );
        return 0;
    }
*/
    p->nUniques++;
    // create CNF
//    {
//        int Num1 = p->nSatVars;
    Ssw_CnfNodeAddToSolver( p, Aig_Regular(pTotal) );
//    printf( "Created variable %d while vars are %d. (diff = %d)\n", 
//        Ssw_ObjSatNum( p, Aig_Regular(pTotal) ), p->nSatVars, p->nSatVars - Num1 );
//    }
    // add output constraint
    pLits[0] = toLitCond( Ssw_ObjSatNum(p,Aig_Regular(pTotal)), Aig_IsComplement(pTotal) );
/*
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 1 );
    assert( RetValue );
    // simplify the solver
    if ( p->pSat->qtail != p->pSat->qhead )
    {
        RetValue = sat_solver_simplify(p->pSat);
        assert( RetValue != 0 );
    }
*/
    assert( p->iOutputLit == -1 );
    p->iOutputLit = pLits[0];
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


