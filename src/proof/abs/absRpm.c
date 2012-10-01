/**CFile****************************************************************

  FileName    [absRpm.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Abstraction package.]

  Synopsis    [Structural reparameterization.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: absRpm.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#include "abs.h"

ABC_NAMESPACE_IMPL_START 

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
void Gia_ManCountPisNodes_rec( Gia_Man_t * p, Gia_Obj_t * pObj, int * pnPis, int * pnNodes )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( pObj->fMark0 )
    {
        (*pnPis)++;
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManCountPisNodes_rec( p, Gia_ObjFanin0(pObj), pnPis, pnNodes );
    Gia_ManCountPisNodes_rec( p, Gia_ObjFanin1(pObj), pnPis, pnNodes );
    (*pnNodes)++;
}
void Gia_ManCountPisNodes( Gia_Man_t * p, int * pnPis, int * pnNodes )
{
    Gia_Obj_t * pObj;
    int i;
    // mark const0 and flop output
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    Gia_ManForEachRo( p, pObj, i )
        Gia_ObjSetTravIdCurrent( p, pObj );
    // count PIs and internal nodes reachable from COs
    *pnPis = *pnNodes = 0;
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManCountPisNodes_rec( p, Gia_ObjFanin0(pObj), pnPis, pnNodes );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs_ManSupport_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSupp )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( pObj->fMark0 || Gia_ObjIsRo(p, pObj) )
    {
        Vec_IntPush( vSupp, Gia_ObjId(p, pObj) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Abs_ManSupport_rec( p, Gia_ObjFanin0(pObj), vSupp );
    Abs_ManSupport_rec( p, Gia_ObjFanin1(pObj), vSupp );
}
int Abs_ManSupport( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSupp )
{
    assert( Gia_ObjIsAnd(pObj) );
    Vec_IntClear( vSupp );
    Gia_ManIncrementTravId( p );
    Abs_ManSupport_rec( p, pObj, vSupp );
    return Vec_IntSize(vSupp);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs_GiaObjDeref_rec( Gia_Man_t * p, Gia_Obj_t * pNode )
{
    Gia_Obj_t * pFanin;
    int Counter = 0;
    if ( pNode->fMark0 || Gia_ObjIsRo(p, pNode) )
        return 0;
    assert( Gia_ObjIsAnd(pNode) );
    pFanin = Gia_ObjFanin0(pNode);
    assert( Gia_ObjRefs(p, pFanin) > 0 );
    if ( Gia_ObjRefDec(p, pFanin) == 0 )
        Counter += Abs_GiaObjDeref_rec( p, pFanin );
    pFanin = Gia_ObjFanin1(pNode);
    assert( Gia_ObjRefs(p, pFanin) > 0 );
    if ( Gia_ObjRefDec(p, pFanin) == 0 )
        Counter += Abs_GiaObjDeref_rec( p, pFanin );
    return Counter + 1;
}
int Abs_GiaObjRef_rec( Gia_Man_t * p, Gia_Obj_t * pNode )
{
    Gia_Obj_t * pFanin;
    int Counter = 0;
    if ( pNode->fMark0 || Gia_ObjIsRo(p, pNode) )
        return 0;
    assert( Gia_ObjIsAnd(pNode) );
    pFanin = Gia_ObjFanin0(pNode);
    if ( Gia_ObjRefInc(p, pFanin) == 0 )
        Counter += Abs_GiaObjRef_rec( p, pFanin );
    pFanin = Gia_ObjFanin1(pNode);
    if ( Gia_ObjRefInc(p, pFanin) == 0 )
        Counter += Abs_GiaObjRef_rec( p, pFanin );
    return Counter + 1;
}

/**Function*************************************************************

  Synopsis    [Returns the number of nodes with zero refs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs_GiaSortNodes( Gia_Man_t * p, Vec_Int_t * vSupp )
{
    Gia_Obj_t * pObj;
    int nSize = Vec_IntSize(vSupp);
    int i, RetValue;
    Gia_ManForEachObjVec( vSupp, p, pObj, i )
        if ( i < nSize && Gia_ObjRefs(p, pObj) == 0 && !Gia_ObjIsRo(p, pObj) ) // add removable leaves
            Vec_IntPush( vSupp, Gia_ObjId(p, pObj) );
    RetValue = Vec_IntSize(vSupp) - nSize;
    Gia_ManForEachObjVec( vSupp, p, pObj, i )
        if ( i < nSize && !(Gia_ObjRefs(p, pObj) == 0 && !Gia_ObjIsRo(p, pObj)) ) // add non-removable leaves
            Vec_IntPush( vSupp, Gia_ObjId(p, pObj) );
    assert( Vec_IntSize(vSupp) == 2 * nSize );
    memmove( Vec_IntArray(vSupp), Vec_IntArray(vSupp) + nSize, sizeof(int) * nSize );
    Vec_IntShrink( vSupp, nSize );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if truth table has no const cofactors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs_GiaCheckTruth( word * pTruth, int nSize, int nSize0 )
{
    char * pStr = (char *)pTruth;
    int i, k, nSteps, nStr = (nSize >= 3 ? (1 << (nSize - 3)) : 1);
    assert( nSize0 > 0 && nSize0 <= nSize );
    if ( nSize0 == 1 )
    {
        for ( i = 0; i < nStr; i++ )
            if ( (((unsigned)pStr[i] ^ ((unsigned)pStr[i] >> 1)) & 0x55) != 0x55 )
                return 0;
        return 1;
    }
    if ( nSize0 == 2 )
    {
        for ( i = 0; i < nStr; i++ )
            if ( ((unsigned)pStr[i] & 0xF) == 0xF || (((unsigned)pStr[i] >> 4) & 0xF) == 0xF || 
                 ((unsigned)pStr[i] & 0xF) == 0x0 || (((unsigned)pStr[i] >> 4) & 0xF) == 0x0  )
                return 0;
        return 1;
    }
    assert( nSize0 >= 3 );
    nSteps = (1 << (nSize0 - 3));
    for ( i = 0; i < nStr; i += nSteps )
    {
        for ( k = 0; k < nSteps; k++ )
            if ( ((unsigned)pStr[i+k] & 0xFF) != 0x00 )
                break;
        if ( k == nSteps )
            break;
        for ( k = 0; k < nSteps; k++ )
            if ( ((unsigned)pStr[i+k] & 0xFF) != 0xFF )
                break;
        if ( k == nSteps )
            break;
    }
    return (int)( i == nStr );
}

/**Function*************************************************************

  Synopsis    [Computes truth table up to 6 inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs_GiaComputeTruth_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Wrd_t * vTruths )
{
    word uTruth0, uTruth1;
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    assert( !pObj->fMark0 );
    assert( Gia_ObjIsAnd(pObj) );
    Abs_GiaComputeTruth_rec( p, Gia_ObjFanin0(pObj), vTruths );
    Abs_GiaComputeTruth_rec( p, Gia_ObjFanin1(pObj), vTruths );
    uTruth0 = Vec_WrdEntry( vTruths, Gia_ObjFanin0(pObj)->Value );
    uTruth0 = Gia_ObjFaninC0(pObj) ? ~uTruth0 : uTruth0;
    uTruth1 = Vec_WrdEntry( vTruths, Gia_ObjFanin1(pObj)->Value );
    uTruth1 = Gia_ObjFaninC1(pObj) ? ~uTruth1 : uTruth1;
    pObj->Value = Vec_WrdSize(vTruths);
    Vec_WrdPush( vTruths, uTruth0 & uTruth1 );
}
word Abs_GiaComputeTruth( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSupp, Vec_Wrd_t * vTruths )
{
    static word s_Truth6[6] = {
        0xAAAAAAAAAAAAAAAA,
        0xCCCCCCCCCCCCCCCC,
        0xF0F0F0F0F0F0F0F0,
        0xFF00FF00FF00FF00,
        0xFFFF0000FFFF0000,
        0xFFFFFFFF00000000
    };
    Gia_Obj_t * pLeaf;
    int i;
    assert( Vec_IntSize(vSupp) <= 6 );
    assert( Gia_ObjIsAnd(pObj) );
    assert( !pObj->fMark0 );
    Vec_WrdClear( vTruths );
    Gia_ManIncrementTravId( p );
    Gia_ManForEachObjVec( vSupp, p, pLeaf, i )
    {
        assert( pLeaf->fMark0 || Gia_ObjIsRo(p, pLeaf) );
        pLeaf->Value = Vec_WrdSize(vTruths);
        Vec_WrdPush( vTruths, s_Truth6[i] );
        Gia_ObjSetTravIdCurrent(p, pLeaf);
    }
    Abs_GiaComputeTruth_rec( p, pObj, vTruths );
    return Vec_WrdEntryLast( vTruths );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if truth table has const cofactors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs_RpmPerformMark( Gia_Man_t * p, int nCutMax, int fVerbose )
{
    Vec_Int_t * vSupp;
    Vec_Wrd_t * vTruths;
    Gia_Obj_t * pObj;
    word uTruth;
    int Iter, i, nPis, nNodes, nSize0;
    int fChanges = 1;
    Gia_ManCreateRefs( p );
    Gia_ManCleanMark0( p );
    Gia_ManForEachPi( p, pObj, i )
        pObj->fMark0 = 1;
    vSupp = Vec_IntAlloc( 100 );
    vTruths = Vec_WrdAlloc( 100 );
    for ( Iter = 0; fChanges; Iter++ )
    {
        // count the number of PIs and internal nodes
        if ( fVerbose )
        {
            Gia_ManCountPisNodes( p, &nPis, &nNodes );
            printf( "Iter %3d : ", Iter );
            printf( "PI = %5d  ",  nPis );
            printf( "And = %6d  ", nNodes );
            printf( "\n" );
        }

        fChanges = 0;
        Gia_ManCleanMark1( p );
//        pObj = Gia_ObjFanin0( Gia_ManPo(p, 0) );
        Gia_ManForEachAnd( p, pObj, i )
        {
            if ( pObj->fMark0 )
                continue;
            if ( Gia_ObjRefs( p, pObj ) == 0 )
                continue;
            if ( Gia_ObjFanin0(pObj)->fMark1 || Gia_ObjFanin1(pObj)->fMark1 )
            {
                pObj->fMark1 = 1;
                continue;
            }
            if ( Abs_ManSupport(p, pObj, vSupp) > nCutMax )
            {
                pObj->fMark1 = 1;
                continue;
            }

            // pObj has structural support no more than nCutMax
            Abs_GiaObjDeref_rec( p, pObj );
            // sort support nodes by ref count
            nSize0 = Abs_GiaSortNodes( p, vSupp );
            // check how many support nodes have ref count 0
            if ( nSize0 == 0 )
            {
                Abs_GiaObjRef_rec( p, pObj );
                continue;
            }

            // compute truth table
            uTruth = Abs_GiaComputeTruth( p, pObj, vSupp, vTruths );

            // check if truth table has const cofs
            if ( !Abs_GiaCheckTruth( &uTruth, Vec_IntSize(vSupp), nSize0 ) ) // has const
            {
                Abs_GiaObjRef_rec( p, pObj );
//            printf( "  no\n" );
                continue;
            }
            printf( "Node = %8d   Supp = %2d   Supp0 = %2d   ", Gia_ObjId(p, pObj), Vec_IntSize(vSupp), nSize0 );
            Extra_PrintHex( stdout, &uTruth, Vec_IntSize(vSupp) );
            printf( "  yes\n" );

            // pObj can be reparamed
            pObj->fMark0 = 1;
            fChanges = 1;
        }
    }
    Vec_IntFree( vSupp );
    Vec_WrdFree( vTruths );
    ABC_FREE( p->pRefs );
    Gia_ManCleanMark0( p ); // temp
    Gia_ManCleanMark1( p );
}

Gia_Man_t * Abs_RpmPerform( Gia_Man_t * p, int nCutMax, int fVerbose )
{
//    Abs_GiaTest( p, nCutMax, fVerbose );
    Abs_RpmPerformMark( p, nCutMax, 1 );
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

