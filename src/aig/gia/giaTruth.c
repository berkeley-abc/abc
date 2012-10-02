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
    assert( Vec_IntSize(p->vTtNodes) < 254 );
}

/**Function*************************************************************

  Synopsis    [Computing the truth table for GIA object.]

  Description [The truth table should be used by the calling application
  (or saved into the user's storage) before this procedure is called again.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Gia_ObjComputeTruthTable( Gia_Man_t * p, Gia_Obj_t * pObj )
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
    Gia_ObjCollectInternal( p, pRoot );
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
    return (unsigned *)Gla_ObjTruthDup( p, Gla_ObjTruthFree2(p), pTruth, Gia_ObjIsCo(pObj) && Gia_ObjFaninC0(pObj) );
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
    clock_t clk = clock();
    int i;
    Gia_ManForEachPo( p, pObj, i )
    {
        pTruth = Gia_ObjComputeTruthTable( p, pObj );
//        Extra_PrintHex( stdout, pTruth, Gia_ManPiNum(p) ); printf( "\n" );
    }
    Abc_PrintTime( 1, "Time", clock() - clk );
}


/**Function*************************************************************

  Synopsis    [Collects internal nodes reachable from the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjCollectInternalCut_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( pObj->fMark0 )
        return;
    pObj->fMark0 = 1;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ObjCollectInternalCut_rec( p, Gia_ObjFanin0(pObj) );
    Gia_ObjCollectInternalCut_rec( p, Gia_ObjFanin1(pObj) );
    Gia_ObjSetNum( p, pObj, Vec_IntSize(p->vTtNodes) );
    Vec_IntPush( p->vTtNodes, Gia_ObjId(p, pObj) );
}
void Gia_ObjCollectInternalCut( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vLeaves )
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
    Gia_ObjCollectInternalCut_rec( p, pRoot );
    assert( Vec_IntSize(p->vTtNodes) < 254 );
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

/**Function*************************************************************

  Synopsis    [Computes the truth table of pRoot in terms of leaves.]

  Description [The root cannot be one of the leaves.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Gia_ObjComputeTruthTableCut( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vLeaves )
{
    Gia_Obj_t * pTemp;
    word * pTruth, * pTruthL, * pTruth0, * pTruth1;
    int i;
    assert( p->vTtMemory != NULL );
    assert( p->nTtVars <= Vec_IntSize(vLeaves) );
    // collect internal nodes
    Gia_ObjCollectInternalCut( p, pRoot, vLeaves );
    // compute the truth table for internal nodes
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
    return (unsigned *)Gla_ObjTruthNode( p, pRoot );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

