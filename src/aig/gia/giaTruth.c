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

static word s_Truth6[6] = {
    ABC_CONST(0xAAAAAAAAAAAAAAAA),
    ABC_CONST(0xCCCCCCCCCCCCCCCC),
    ABC_CONST(0xF0F0F0F0F0F0F0F0),
    ABC_CONST(0xFF00FF00FF00FF00),
    ABC_CONST(0xFFFF0000FFFF0000),
    ABC_CONST(0xFFFFFFFF00000000)
};

static inline word * Gla_ObjTruthElem( Gia_Man_t * p, int i )            { return (word *)Vec_PtrEntry( p->vTtInputs, i );                                           }
static inline word * Gla_ObjTruthNodeId( Gia_Man_t * p, int Id )         { return Vec_WrdArray(p->vTtMemory) + p->nTtWords * Id;                                     }
static inline word * Gla_ObjTruthNode( Gia_Man_t * p, Gia_Obj_t * pObj ) { return Vec_WrdArray(p->vTtMemory) + p->nTtWords * Gia_ObjNum(p, pObj);                    }
static inline word * Gla_ObjTruthFree1( Gia_Man_t * p )                  { return Vec_WrdArray(p->vTtMemory) + Vec_WrdSize(p->vTtMemory) - p->nTtWords * 1;          }
static inline word * Gla_ObjTruthFree2( Gia_Man_t * p )                  { return Vec_WrdArray(p->vTtMemory) + Vec_WrdSize(p->vTtMemory) - p->nTtWords * 2;          }
static inline word * Gla_ObjTruthConst0( Gia_Man_t * p, word * pDst )                   { int w; for ( w = 0; w < p->nTtWords; w++ ) pDst[w] = 0; return pDst;                      }
static inline word * Gla_ObjTruthDup( Gia_Man_t * p, word * pDst, word * pSrc, int c )  { int w; for ( w = 0; w < p->nTtWords; w++ ) pDst[w] = c ? ~pSrc[w] : pSrc[w]; return pDst; }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes truth table of a 6-LUT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjComputeTruthTable6Lut_rec( Gia_Man_t * p, int iObj, Vec_Wrd_t * vTemp )
{
    word uTruth0, uTruth1;
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    if ( !Gia_ObjIsAnd(pObj) )
        return;
    Gia_ObjComputeTruthTable6Lut_rec( p, Gia_ObjFaninId0p(p, pObj), vTemp );
    Gia_ObjComputeTruthTable6Lut_rec( p, Gia_ObjFaninId1p(p, pObj), vTemp );
    uTruth0 = Vec_WrdEntry( vTemp, Gia_ObjFanin0(pObj)->Value );
    uTruth0 = Gia_ObjFaninC0(pObj) ? ~uTruth0 : uTruth0;
    uTruth1 = Vec_WrdEntry( vTemp, Gia_ObjFanin1(pObj)->Value );
    uTruth1 = Gia_ObjFaninC1(pObj) ? ~uTruth1 : uTruth1;
    Vec_WrdWriteEntry( vTemp, iObj, uTruth0 & uTruth1 );
}
word Gia_ObjComputeTruthTable6Lut( Gia_Man_t * p, int iObj, Vec_Wrd_t * vTemp )
{
    int i, Fanin;
    assert( Vec_WrdSize(vTemp) == Gia_ManObjNum(p) );
    assert( Gia_ObjIsLut(p, iObj) );
    Gia_LutForEachFanin( p, iObj, Fanin, i )
        Vec_WrdWriteEntry( vTemp, Fanin, s_Truth6[i] );
    assert( i <= 6 );
    Gia_ObjComputeTruthTable6Lut_rec( p, iObj, vTemp );
    return Vec_WrdEntry( vTemp, iObj );
}

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
void Gia_ObjCollectInternal_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( !Gia_ObjIsAnd(pObj) )
        return;
    if ( pObj->fMark0 )
        return;
    pObj->fMark0 = 1;
    Gia_ObjCollectInternal_rec( p, Gia_ObjFanin0(pObj) );
    Gia_ObjCollectInternal_rec( p, Gia_ObjFanin1(pObj) );
    Gia_ObjSetNum( p, pObj, Vec_IntSize(p->vTtNodes) );
    Vec_IntPush( p->vTtNodes, Gia_ObjId(p, pObj) );
}
void Gia_ObjCollectInternal( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Vec_IntClear( p->vTtNodes );
    Gia_ObjCollectInternal_rec( p, pObj );
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
        p->nTtWords  = Abc_Truth6WordNum( p->nTtVars );
        p->vTtNums   = Vec_IntStart( Gia_ManObjNum(p) + 1000 );
        p->vTtNodes  = Vec_IntAlloc( 256 );
        p->vTtInputs = Vec_PtrAllocTruthTables( Abc_MaxInt(6, p->nTtVars) );
        p->vTtMemory = Vec_WrdStart( p->nTtWords * 256 );
    }
    else
    {
        // make sure the number of primary inputs did not change 
        // since the truth table computation storage was prepared
        assert( p->nTtVars == Gia_ManPiNum(p) );
    }
    // extend ID numbers
    if ( Vec_IntSize(p->vTtNums) < Gia_ManObjNum(p) )
        Vec_IntFillExtra( p->vTtNums, Gia_ManObjNum(p), 0 );
    // collect internal nodes
    pRoot = Gia_ObjIsCo(pObj) ? Gia_ObjFanin0(pObj) : pObj;
    Gia_ObjCollectInternal( p, pRoot );
    // extend TT storage
    if ( Vec_WrdSize(p->vTtMemory) < p->nTtWords * (Vec_IntSize(p->vTtNodes) + 2) )
        Vec_WrdFillExtra( p->vTtMemory, p->nTtWords * (Vec_IntSize(p->vTtNodes) + 2), 0 );
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

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjComputeTruthTableStart( Gia_Man_t * p, int nVarsMax )
{
    assert( p->vTtMemory == NULL );
    p->nTtVars   = nVarsMax;
    p->nTtWords  = Abc_Truth6WordNum( p->nTtVars );
    p->vTtNodes  = Vec_IntAlloc( 256 );
    p->vTtInputs = Vec_PtrAllocTruthTables( Abc_MaxInt(6, p->nTtVars) );
    p->vTtMemory = Vec_WrdStart( p->nTtWords * 64 );
    p->vTtNums   = Vec_IntAlloc( Gia_ManObjNum(p) + 1000 );
    Vec_IntFill( p->vTtNums, Vec_IntCap(p->vTtNums), -ABC_INFINITY );
}
void Gia_ObjComputeTruthTableStop( Gia_Man_t * p )
{
    p->nTtVars   = 0;
    p->nTtWords  = 0;
    Vec_IntFreeP( &p->vTtNums );
    Vec_IntFreeP( &p->vTtNodes );
    Vec_PtrFreeP( &p->vTtInputs );
    Vec_WrdFreeP( &p->vTtMemory );
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes reachable from the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjCollectInternalCut_rec( Gia_Man_t * p, int iObj )
{
    if ( Gia_ObjHasNumId(p, iObj) )
        return;
    assert( Gia_ObjIsAnd(Gia_ManObj(p, iObj)) );
    Gia_ObjCollectInternalCut_rec( p, Gia_ObjFaninId0(Gia_ManObj(p, iObj), iObj) );
    Gia_ObjCollectInternalCut_rec( p, Gia_ObjFaninId1(Gia_ManObj(p, iObj), iObj) );
    Gia_ObjSetNumId( p, iObj, Vec_IntSize(p->vTtNodes) );
    Vec_IntPush( p->vTtNodes, iObj );
}
void Gia_ObjCollectInternalCut( Gia_Man_t * p, int iRoot, Vec_Int_t * vLeaves )
{
    int i, iObj;
    assert( !Gia_ObjHasNumId(p, iRoot) );
    assert( Gia_ObjIsAnd(Gia_ManObj(p, iRoot)) );
    Vec_IntForEachEntry( vLeaves, iObj, i )
    {
        assert( !Gia_ObjHasNumId(p, iObj) );
        Gia_ObjSetNumId( p, iObj, -i );
    }
    assert( !Gia_ObjHasNumId(p, iRoot) ); // the root cannot be one of the leaves
    Vec_IntClear( p->vTtNodes );
    Vec_IntPush( p->vTtNodes, -1 );
    Gia_ObjCollectInternalCut_rec( p, iRoot );
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
    int i, iObj, Id0, Id1;
    assert( p->vTtMemory != NULL );
    assert( Vec_IntSize(vLeaves) <= p->nTtVars );
    // extend ID numbers
    if ( Vec_IntSize(p->vTtNums) < Gia_ManObjNum(p) )
        Vec_IntFillExtra( p->vTtNums, Gia_ManObjNum(p), -ABC_INFINITY );
    // collect internal nodes
    Gia_ObjCollectInternalCut( p, Gia_ObjId(p, pRoot), vLeaves );
    // extend TT storage
    if ( Vec_WrdSize(p->vTtMemory) < p->nTtWords * (Vec_IntSize(p->vTtNodes) + 2) )
        Vec_WrdFillExtra( p->vTtMemory, p->nTtWords * (Vec_IntSize(p->vTtNodes) + 2), 0 );
    // compute the truth table for internal nodes
    Vec_IntForEachEntryStart( p->vTtNodes, iObj, i, 1 )
    {
        assert( i == Gia_ObjNumId(p, iObj) );
        pTemp   = Gia_ManObj( p, iObj );
        pTruth  = Gla_ObjTruthNodeId( p, i );  
        pTruthL = pTruth + p->nTtWords;
        Id0 = Gia_ObjNumId( p, Gia_ObjFaninId0(pTemp, iObj) );
        Id1 = Gia_ObjNumId( p, Gia_ObjFaninId1(pTemp, iObj) );
        pTruth0 = (Id0 > 0) ? Gla_ObjTruthNodeId(p, Id0) : Gla_ObjTruthElem(p, -Id0);
        pTruth1 = (Id1 > 0) ? Gla_ObjTruthNodeId(p, Id1) : Gla_ObjTruthElem(p, -Id1);
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
    pTruth = Gla_ObjTruthNode( p, pRoot );
    // unmark leaves marked by Gia_ObjCollectInternal()
    Vec_IntForEachEntry( vLeaves, iObj, i )
        Gia_ObjResetNumId( p, iObj );
    Vec_IntForEachEntryStart( p->vTtNodes, iObj, i, 1 )
        Gia_ObjResetNumId( p, iObj );
    return pTruth;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

