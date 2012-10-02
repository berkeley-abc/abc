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

static inline int   Gia_ObjDom( Gia_Man_t * p, Gia_Obj_t * pObj )            { return Vec_IntEntry(p->vDoms, Gia_ObjId(p, pObj));   }
static inline void  Gia_ObjSetDom( Gia_Man_t * p, Gia_Obj_t * pObj, int d )  { Vec_IntWriteEntry(p->vDoms, Gia_ObjId(p, pObj), d);  }

static int Abs_ManSupport( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSupp );
static int Abs_GiaObjDeref_rec( Gia_Man_t * p, Gia_Obj_t * pNode );
static int Abs_GiaObjRef_rec( Gia_Man_t * p, Gia_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collects non-trivial internal dominators of the PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManCollectDoms( Gia_Man_t * p )
{
    Vec_Int_t * vNodes;
    Gia_Obj_t * pObj;
    int Lev, LevMax = 2;
    int i, iDom, iDomNext;
    vNodes = Vec_IntAlloc( 100 );
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( !pObj->fMark0 )
            continue;
        iDom = Gia_ObjDom(p, pObj);
        if ( iDom == i )
            continue;
        for ( Lev = 0; Lev < LevMax && Gia_ObjIsAnd( Gia_ManObj(p, iDom) ); Lev++ )
        {
            Vec_IntPush( vNodes, iDom );
            iDomNext = Gia_ObjDom( p, Gia_ManObj(p, iDom) );
            if ( iDomNext == iDom )
                break;
            iDom = iDomNext;
        }
    }
    Vec_IntUniqify( vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Computes one-node dominators.]

  Description [For each node, computes the closest one-node dominator,
  which can be the node itself if the node has no other dominators.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManAddDom( Gia_Man_t * p, Gia_Obj_t * pObj, int iDom0 )
{
    int iDom1, iDomNext;
    if ( Gia_ObjDom(p, pObj) == -1 )
    {
        Gia_ObjSetDom( p, pObj, iDom0 );
        return;
    }
    iDom1 = Gia_ObjDom( p, pObj );
    while ( 1 )
    {
        if ( iDom0 > iDom1 )
        {
            iDomNext = Gia_ObjDom( p, Gia_ManObj(p, iDom1) );
            if ( iDomNext == iDom1 )
                break;
            iDom1 = iDomNext;
            continue;
        }
        if ( iDom1 > iDom0 )
        {
            iDomNext = Gia_ObjDom( p, Gia_ManObj(p, iDom0) );
            if ( iDomNext == iDom0 )
                break;
            iDom0 = iDomNext;
            continue;
        }
        assert( iDom0 == iDom1 );
        Gia_ObjSetDom( p, pObj, iDom0 );
        return;
    }
    Gia_ObjSetDom( p, pObj, Gia_ObjId(p, pObj) );
}
void Gia_ManComputeDoms( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    if ( p->vDoms == NULL )
        p->vDoms = Vec_IntAlloc( 0 );
    Vec_IntFill( p->vDoms, Gia_ManObjNum(p), -1 );
    Gia_ManForEachObjReverse( p, pObj, i )
    {
        if ( i == 0 || Gia_ObjIsCi(pObj) )
            continue;
        if ( pObj->fMark0 || (p->pRefs && Gia_ObjRefs(p, pObj) == 0) )
            continue;
        if ( Gia_ObjIsCo(pObj) )
        {
            Gia_ObjSetDom( p, pObj, i );
            Gia_ManAddDom( p, Gia_ObjFanin0(pObj), i );
            continue;
        }
        assert( Gia_ObjIsAnd(pObj) );
        Gia_ManAddDom( p, Gia_ObjFanin0(pObj), i );
        Gia_ManAddDom( p, Gia_ObjFanin1(pObj), i );
    }
}
void Gia_ManTestDoms2( Gia_Man_t * p )
{
    Vec_Int_t * vNodes;
    Gia_Obj_t * pObj, * pDom;
    clock_t clk = clock();
    int i;
    assert( p->vDoms == NULL );
    Gia_ManComputeDoms( p );
/*
    Gia_ManForEachPi( p, pObj, i )
        if ( Gia_ObjId(p, pObj) != Gia_ObjDom(p, pObj) )
            printf( "PI =%6d  Id =%8d. Dom =%8d.\n", i, Gia_ObjId(p, pObj), Gia_ObjDom(p, pObj) );
*/
    Abc_PrintTime( 1, "Time", clock() - clk );
    // for each dominated PI, when if the PIs is in a leaf of the MFFC of the dominator
    Gia_ManCleanMark0( p );
    Gia_ManForEachPi( p, pObj, i )
        pObj->fMark0 = 1;
    vNodes = Vec_IntAlloc( 100 );
    Gia_ManCreateRefs( p );
    Gia_ManForEachPi( p, pObj, i )
    {
        if ( Gia_ObjId(p, pObj) == Gia_ObjDom(p, pObj) )
            continue;

        pDom = Gia_ManObj(p, Gia_ObjDom(p, pObj));
        if ( Gia_ObjIsCo(pDom) )
        {
            assert( Gia_ObjFanin0(pDom) == pObj );
            continue;
        }
        assert( Gia_ObjIsAnd(pDom) );
        Abs_GiaObjDeref_rec( p, pDom );
        Abs_ManSupport( p, pDom, vNodes );
        Abs_GiaObjRef_rec( p, pDom );

        if ( Vec_IntFind(vNodes, Gia_ObjId(p, pObj)) == -1 )
            printf( "FAILURE.\n" );
//        else
//            printf( "Success.\n" );
    }
    Vec_IntFree( vNodes );
    Gia_ManCleanMark0( p );
}

/**Function*************************************************************

  Synopsis    [Collect PI doms.]

  Description [Assumes that some PIs and ANDs are marked with fMark0.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManComputePiDoms( Gia_Man_t * p )
{
    Vec_Int_t * vNodes;
    Gia_ManComputeDoms( p );
    vNodes = Gia_ManCollectDoms( p );
//    Vec_IntPrint( vNodes );
    printf( "Nodes = %d. Doms = %d.\n", Gia_ManAndNum(p), Vec_IntSize(vNodes) );
    return vNodes;
}

void Gia_ManTestDoms( Gia_Man_t * p )
{
    Vec_Int_t * vNodes;
    Gia_Obj_t * pObj;
    int i;
    assert( p->vDoms == NULL );
    // mark PIs
    Gia_ManCleanMark0( p );
    Gia_ManForEachPi( p, pObj, i )
        pObj->fMark0 = 1;
    // compute dominators
    vNodes = Gia_ManComputePiDoms( p );
    Vec_IntFree( vNodes );
    // unmark PIs
    Gia_ManCleanMark0( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCountPisNodes_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vPis, Vec_Int_t * vAnds )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( pObj->fMark0 )
    {
        Vec_IntPush( vPis, Gia_ObjId(p, pObj) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManCountPisNodes_rec( p, Gia_ObjFanin0(pObj), vPis, vAnds );
    Gia_ManCountPisNodes_rec( p, Gia_ObjFanin1(pObj), vPis, vAnds );
    Vec_IntPush( vAnds, Gia_ObjId(p, pObj) );
}
void Gia_ManCountPisNodes( Gia_Man_t * p, Vec_Int_t * vPis, Vec_Int_t * vAnds )
{
    Gia_Obj_t * pObj;
    int i;
    // mark const0 and flop output
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    Gia_ManForEachRo( p, pObj, i )
        Gia_ObjSetTravIdCurrent( p, pObj );
    // count PIs and internal nodes reachable from COs
    Vec_IntClear( vPis );
    Vec_IntClear( vAnds );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManCountPisNodes_rec( p, Gia_ObjFanin0(pObj), vPis, vAnds );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs_ManSupport2_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSupp )
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
    Abs_ManSupport2_rec( p, Gia_ObjFanin0(pObj), vSupp );
    Abs_ManSupport2_rec( p, Gia_ObjFanin1(pObj), vSupp );
}
int Abs_ManSupport2( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSupp )
{
    assert( Gia_ObjIsAnd(pObj) );
    Vec_IntClear( vSupp );
    Gia_ManIncrementTravId( p );
    Abs_ManSupport2_rec( p, pObj, vSupp );
    return Vec_IntSize(vSupp);
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
    if ( pObj->fMark0 || Gia_ObjIsRo(p, pObj) || Gia_ObjRefs(p, pObj) > 0 )
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
    Abs_ManSupport_rec( p, Gia_ObjFanin0(pObj), vSupp );
    Abs_ManSupport_rec( p, Gia_ObjFanin1(pObj), vSupp );
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
        {
            assert( pObj->fMark0 );
            Vec_IntPush( vSupp, Gia_ObjId(p, pObj) );
        }
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

  Synopsis    [Returns 1 if truth table has const cofactors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs_RpmPerformMark( Gia_Man_t * p, int nCutMax, int fVerbose )
{
    Vec_Int_t * vSupp, * vPis, * vAnds;
    Vec_Wrd_t * vTruths;
    Gia_Obj_t * pObj;
    word uTruth;
    int Iter, i, nSize0;
    int fChanges = 1;
    Gia_ManCreateRefs( p );
    Gia_ManCleanMark0( p );
    Gia_ManForEachPi( p, pObj, i )
        pObj->fMark0 = 1;
    vPis = Vec_IntAlloc( 100 );
    vAnds = Vec_IntAlloc( 100 );
    vSupp = Vec_IntAlloc( 100 );
    vTruths = Vec_WrdAlloc( 100 );
    for ( Iter = 0; fChanges; Iter++ )
    {
        // count the number of PIs and internal nodes
        if ( fVerbose )
        {
            Gia_ManCountPisNodes( p, vPis, vAnds );
            printf( "Iter %3d : ", Iter );
            printf( "PI = %5d  ",  Vec_IntSize(vPis) );
            printf( "And = %6d  ", Vec_IntSize(vAnds) );
            printf( "\n" );
        }

        fChanges = 0;
        Gia_ManCleanMark1( p );
//        pObj = Gia_ObjFanin0( Gia_ManPo(p, 1) );
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

            // dereference nodes
            Abs_GiaObjDeref_rec( p, pObj );
            // compute support
            Abs_ManSupport( p, pObj, vSupp );
            // check support size
            if ( Vec_IntSize(vSupp) > nCutMax )
            {
                Abs_GiaObjRef_rec( p, pObj );
                pObj->fMark1 = 1;
                continue;
            }
            // order nodes by their ref counts
            nSize0 = Abs_GiaSortNodes( p, vSupp );
            // quit if there is no removable or too many
            if ( nSize0 == 0 || nSize0 > nCutMax )
            {
                Abs_GiaObjRef_rec( p, pObj );
                continue;
            }

            // compute truth table
            uTruth = Gia_ObjComputeTruthTable6( p, pObj, vSupp, vTruths );

            // check if truth table has const cofs
            if ( !Abs_GiaCheckTruth( &uTruth, Vec_IntSize(vSupp), nSize0 ) ) // has const
            {
                Abs_GiaObjRef_rec( p, pObj );
/*
                if ( Iter == 1 )
                {
                    printf( "Node = %8d   Supp = %2d   Supp0 = %2d   ", Gia_ObjId(p, pObj), Vec_IntSize(vSupp), nSize0 );
                    Extra_PrintHex( stdout, &uTruth, Vec_IntSize(vSupp) );
                    printf( "  no\n" );
                }
*/
                continue;
            }
/*
            printf( "Node = %8d   Supp = %2d   Supp0 = %2d   ", Gia_ObjId(p, pObj), Vec_IntSize(vSupp), nSize0 );
            Extra_PrintHex( stdout, &uTruth, Vec_IntSize(vSupp) );
            printf( "  yes\n" );
*/
            // pObj can be reparamed
            pObj->fMark0 = 1;
            fChanges = 1;
        }
    }
    Vec_IntFree( vPis );
    Vec_IntFree( vAnds );
    Vec_IntFree( vSupp );
    Vec_WrdFree( vTruths );
    ABC_FREE( p->pRefs );
//    Gia_ManCleanMark0( p ); // temp
    Gia_ManCleanMark1( p );
}

/**Function*************************************************************

  Synopsis    [Assumed that fMark0 marks the internal PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupRpm( Gia_Man_t * p )
{
    Vec_Int_t * vPis, * vAnds;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    vPis = Vec_IntAlloc( 100 );
    vAnds = Vec_IntAlloc( 100 );
    Gia_ManCountPisNodes( p, vPis, vAnds );

    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    // create PIs
    Gia_ManForEachObjVec( vPis, p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    // create flops
    Gia_ManForEachRo( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    // create internal nodes
    Gia_ManForEachObjVec( vAnds, p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    // create COs
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );

    Vec_IntFree( vPis );
    Vec_IntFree( vAnds );
    return pNew;
}

Gia_Man_t * Abs_RpmPerform( Gia_Man_t * p, int nCutMax, int fVerbose )
{
    Gia_Man_t * pNew;
    Gia_ObjComputeTruthTableStart( p, nCutMax );
//    Gia_ManTestDoms( p );
//    return NULL;
    Abs_RpmPerformMark( p, nCutMax, 1 );
    pNew = Gia_ManDupRpm( p );
    Gia_ManCleanMark0( p );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

