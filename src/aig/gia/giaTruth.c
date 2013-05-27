/**CFile****************************************************************

  FileName    [giaTruth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Truth table computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaTruth.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline word * Gla_ObjTruthElem( Gia_Man_t * p, int i )            { return (word *)Vec_PtrEntry( p->vTtInputs, i );                                           }
static inline word * Gla_ObjTruthNode( Gia_Man_t * p, Gia_Obj_t * pObj ) { return Vec_WrdArray(p->vTtMemory) + p->nTtWords * Gia_ObjNum(p, pObj);                    }
static inline word * Gla_ObjTruthFree1( Gia_Man_t * p )                  { return Vec_WrdArray(p->vTtMemory) + p->nTtWords * 254;                                    }
static inline word * Gla_ObjTruthFree2( Gia_Man_t * p )                  { return Vec_WrdArray(p->vTtMemory) + p->nTtWords * 255;                                    }
static inline word * Gla_ObjTruthConst0( Gia_Man_t * p, word * pDst )                   { int w; for ( w = 0; w < p->nTtWords; w++ ) pDst[w] = 0; return pDst;                      }
static inline word * Gla_ObjTruthDup( Gia_Man_t * p, word * pDst, word * pSrc, int c )  { int w; for ( w = 0; w < p->nTtWords; w++ ) pDst[w] = c ? ~pSrc[w] : pSrc[w]; return pDst; }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes truth table up to 6 inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjComputeTruthTable6_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Wrd_t * vTruths )
{
    word uTruth0, uTruth1;
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    assert( !pObj->fMark0 );
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ObjComputeTruthTable6_rec( p, Gia_ObjFanin0(pObj), vTruths );
    Gia_ObjComputeTruthTable6_rec( p, Gia_ObjFanin1(pObj), vTruths );
    uTruth0 = Vec_WrdEntry( vTruths, Gia_ObjFanin0(pObj)->Value );
    uTruth0 = Gia_ObjFaninC0(pObj) ? ~uTruth0 : uTruth0;
    uTruth1 = Vec_WrdEntry( vTruths, Gia_ObjFanin1(pObj)->Value );
    uTruth1 = Gia_ObjFaninC1(pObj) ? ~uTruth1 : uTruth1;
    pObj->Value = Vec_WrdSize(vTruths);
    Vec_WrdPush( vTruths, uTruth0 & uTruth1 );
}
word Gia_ObjComputeTruthTable6( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vSupp, Vec_Wrd_t * vTruths )
{
    static word s_Truth6[6] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
        ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000),
        ABC_CONST(0xFFFFFFFF00000000)
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
    Gia_ObjComputeTruthTable6_rec( p, pObj, vTruths );
    return Vec_WrdEntryLast( vTruths );
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes reachable from the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjCollectInternal_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( !Gia_ObjIsAnd(pObj) )
        return 0;
    if ( pObj->fMark0 )
        return 0;
    pObj->fMark0 = 1;
    Gia_ObjCollectInternal_rec( p, Gia_ObjFanin0(pObj) );
    Gia_ObjCollectInternal_rec( p, Gia_ObjFanin1(pObj) );
    if ( Vec_IntSize(p->vTtNodes) > 253 )
        return 1;
    Gia_ObjSetNum( p, pObj, Vec_IntSize(p->vTtNodes) );
    Vec_IntPush( p->vTtNodes, Gia_ObjId(p, pObj) );
    return 0;
}
int Gia_ObjCollectInternal( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    int RetValue;
    Vec_IntClear( p->vTtNodes );
    RetValue = Gia_ObjCollectInternal_rec( p, pObj );
    assert( Vec_IntSize(p->vTtNodes) < 254 );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Computing the truth table for GIA object.]

  Description [The truth table should be used by the calling application
  (or saved into the user's storage) before this procedure is called again.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word * Gia_ObjComputeTruthTable( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Gia_Obj_t * pTemp, * pRoot;
    word * pTruth, * pTruthL, * pTruth0, * pTruth1;
    int i;
    if ( p->vTtMemory == NULL )
    {
        p->nTtVars   = Gia_ManPiNum( p );
        p->nTtWords  = (p->nTtVars <= 6 ? 1 : (1 << (p->nTtVars - 6)));
        p->vTtNums   = Vec_StrAlloc( Gia_ManObjNum(p) + 1000 );
        p->vTtNodes  = Vec_IntAlloc( 256 );
        p->vTtInputs = Vec_PtrAllocTruthTables( p->nTtVars );
        p->vTtMemory = Vec_WrdStart( p->nTtWords * 256 );
    }
    else
    {
        // make sure the number of primary inputs did not change 
        // since the truth table computation storage was prepared
        assert( p->nTtVars == Gia_ManPiNum(p) );
    }
    // collect internal nodes
    pRoot = Gia_ObjIsCo(pObj) ? Gia_ObjFanin0(pObj) : pObj;
    if ( Gia_ObjCollectInternal( p, pRoot ) )
    {
        Gia_ManForEachObjVec( p->vTtNodes, p, pTemp, i )
            pTemp->fMark0 = 0;
        return NULL;
    }
    // compute the truth table for internal nodes
    Gia_ManForEachObjVec( p->vTtNodes, p, pTemp, i )
    {
        pTemp->fMark0 = 0; // unmark nodes marked by Gia_ObjCollectInternal()
        pTruth  = Gla_ObjTruthNode(p, pTemp);
        pTruthL = pTruth + p->nTtWords;
        pTruth0 = Gia_ObjIsAnd(Gia_ObjFanin0(pTemp)) ? Gla_ObjTruthNode(p, Gia_ObjFanin0(pTemp)) : Gla_ObjTruthElem(p, Gia_ObjCioId(Gia_ObjFanin0(pTemp)) );
        pTruth1 = Gia_ObjIsAnd(Gia_ObjFanin1(pTemp)) ? Gla_ObjTruthNode(p, Gia_ObjFanin1(pTemp)) : Gla_ObjTruthElem(p, Gia_ObjCioId(Gia_ObjFanin1(pTemp)) );
        if ( Gia_ObjFaninC0(pTemp) )
        {
            if ( Gia_ObjFaninC1(pTemp) )
                while ( pTruth < pTruthL )
                    *pTruth++ = ~*pTruth0++ & ~*pTruth1++;
            else
                while ( pTruth < pTruthL )
                    *pTruth++ = ~*pTruth0++ &  *pTruth1++;
        }
        else
        {
            if ( Gia_ObjFaninC1(pTemp) )
                while ( pTruth < pTruthL )
                    *pTruth++ =  *pTruth0++ & ~*pTruth1++;
            else
                while ( pTruth < pTruthL )
                    *pTruth++ =  *pTruth0++ &  *pTruth1++;
        }
    }
    // compute the final table
    if ( Gia_ObjIsConst0(pRoot) )
        pTruth = Gla_ObjTruthConst0( p, Gla_ObjTruthFree1(p) );
    else if ( Gia_ObjIsPi(p, pRoot) )
        pTruth = Gla_ObjTruthElem( p, Gia_ObjCioId(pRoot) );
    else if ( Gia_ObjIsAnd(pRoot) )
        pTruth = Gla_ObjTruthNode( p, pRoot );
    else
        pTruth = NULL;
    return Gla_ObjTruthDup( p, Gla_ObjTruthFree2(p), pTruth, Gia_ObjIsCo(pObj) && Gia_ObjFaninC0(pObj) );
}

/**Function*************************************************************

  Synopsis    [Testing truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjComputeTruthTableTest( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    unsigned * pTruth;
    abctime clk = Abc_Clock();
    int i;
    Gia_ManForEachPo( p, pObj, i )
    {
        pTruth = (unsigned *)Gia_ObjComputeTruthTable( p, pObj );
//        Extra_PrintHex( stdout, pTruth, Gia_ManPiNum(p) ); printf( "\n" );
    }
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}


/**Function*************************************************************

  Synopsis    [Collects internal nodes reachable from the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjCollectInternalCut_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( pObj->fMark0 )
        return 0;
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjCollectInternalCut_rec( p, Gia_ObjFanin0(pObj) ) )
        return 1;
    if ( Gia_ObjCollectInternalCut_rec( p, Gia_ObjFanin1(pObj) ) )
        return 1;
    pObj->fMark0 = 1;
    Gia_ObjSetNum( p, pObj, Vec_IntSize(p->vTtNodes) );
    Vec_IntPush( p->vTtNodes, Gia_ObjId(p, pObj) );
    return (Vec_IntSize(p->vTtNodes) >= 254);
}
int Gia_ObjCollectInternalCut( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vLeaves )
{
    Gia_Obj_t * pObj;
    int i;
    assert( Gia_ObjIsAnd(pRoot) );
    assert( pRoot->fMark0 == 0 );
    Gia_ManForEachObjVec( vLeaves, p, pObj, i )
    {
        assert( pObj->fMark0 == 0 );
        pObj->fMark0 = 1;
        Gia_ObjSetNum( p, pObj, i );
    }
    assert( pRoot->fMark0 == 0 ); // the root cannot be one of the leaves
    Vec_IntClear( p->vTtNodes );
    return Gia_ObjCollectInternalCut_rec( p, pRoot );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjComputeTruthTableStart( Gia_Man_t * p, int nVarsMax )
{
    assert( p->vTtMemory == NULL );
    p->nTtVars   = nVarsMax;
    p->nTtWords  = (p->nTtVars <= 6 ? 1 : (1 << (p->nTtVars - 6)));
    p->vTtNums   = Vec_StrAlloc( Gia_ManObjNum(p) + 1000 );
    p->vTtNodes  = Vec_IntAlloc( 256 );
    p->vTtInputs = Vec_PtrAllocTruthTables( p->nTtVars );
    p->vTtMemory = Vec_WrdStart( p->nTtWords * 256 );
}
void Gia_ObjComputeTruthTableStop( Gia_Man_t * p )
{
    p->nTtVars   = 0;
    p->nTtWords  = 0;
    Vec_StrFreeP( &p->vTtNums );
    Vec_IntFreeP( &p->vTtNodes );
    Vec_PtrFreeP( &p->vTtInputs );
    Vec_WrdFreeP( &p->vTtMemory );
}

/**Function*************************************************************

  Synopsis    [Computes the truth table of pRoot in terms of leaves.]

  Description [The root cannot be one of the leaves.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word * Gia_ObjComputeTruthTableCut( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vLeaves )
{
    Gia_Obj_t * pTemp;
    word * pTruth, * pTruthL, * pTruth0, * pTruth1;
    int i;
    assert( p->vTtMemory != NULL );
    assert( Vec_IntSize(vLeaves) <= p->nTtVars );
    // collect internal nodes
    if ( Gia_ObjCollectInternalCut( p, pRoot, vLeaves ) )
    {
        // unmark nodes makred by Gia_ObjCollectInternal()
        Gia_ManForEachObjVec( p->vTtNodes, p, pTemp, i )
            pTemp->fMark0 = 0; 
        // unmark leaves marked by Gia_ObjCollectInternal()
        Gia_ManForEachObjVec( vLeaves, p, pTemp, i )
        {
            assert( pTemp->fMark0 == 1 );
            pTemp->fMark0 = 0; 
        }
        return NULL;
    }
    // compute the truth table for internal nodes
    assert( Vec_IntSize(p->vTtNodes) < 254 );
    Gia_ManForEachObjVec( p->vTtNodes, p, pTemp, i )
    {
        pTemp->fMark0 = 0; // unmark nodes marked by Gia_ObjCollectInternal()
        pTruth  = Gla_ObjTruthNode(p, pTemp);
        pTruthL = pTruth + p->nTtWords;
        pTruth0 = !Gia_ObjFanin0(pTemp)->fMark0 ? Gla_ObjTruthNode(p, Gia_ObjFanin0(pTemp)) : Gla_ObjTruthElem(p, Gia_ObjNum(p, Gia_ObjFanin0(pTemp)) );
        pTruth1 = !Gia_ObjFanin1(pTemp)->fMark0 ? Gla_ObjTruthNode(p, Gia_ObjFanin1(pTemp)) : Gla_ObjTruthElem(p, Gia_ObjNum(p, Gia_ObjFanin1(pTemp)) );
        if ( Gia_ObjFaninC0(pTemp) )
        {
            if ( Gia_ObjFaninC1(pTemp) )
                while ( pTruth < pTruthL )
                    *pTruth++ = ~*pTruth0++ & ~*pTruth1++;
            else
                while ( pTruth < pTruthL )
                    *pTruth++ = ~*pTruth0++ &  *pTruth1++;
        }
        else
        {
            if ( Gia_ObjFaninC1(pTemp) )
                while ( pTruth < pTruthL )
                    *pTruth++ =  *pTruth0++ & ~*pTruth1++;
            else
                while ( pTruth < pTruthL )
                    *pTruth++ =  *pTruth0++ &  *pTruth1++;
        }
    }
    // unmark leaves marked by Gia_ObjCollectInternal()
    Gia_ManForEachObjVec( vLeaves, p, pTemp, i )
    {
        assert( pTemp->fMark0 == 1 );
        pTemp->fMark0 = 0; 
    }
    return Gla_ObjTruthNode( p, pRoot );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

