/**CFile****************************************************************

  FileName    [giaResub2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaResub2.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
typedef struct Gia_Rsb2Man_t_ Gia_Rsb2Man_t;
struct Gia_Rsb2Man_t_
{
    // hyper-parameters
    int            nDivsMax;
    int            nLevelIncrease;
    int            fUseXor;
    int            fUseZeroCost;
    int            fDebug;
    int            fVerbose;
    // input AIG
    int            nObjs;
    int            nPis;
    int            nNodes;
    int            nPos;
    int            iFirstPo;
    int            Level;
    int            nMffc;
    // intermediate data
    Vec_Int_t      vObjs;
    Vec_Wrd_t      vSims;
    Vec_Ptr_t      vpDivs;
    Vec_Int_t      vDivs;
    Vec_Int_t      vLevels;
    Vec_Int_t      vRefs;
    Vec_Int_t      vCopies;
    word           Truth0;
    word           Truth1;
    word           CareSet;
};

extern int Abc_ResubComputeFunction( void ** ppDivs, int nDivs, int nWords, int nLimit, int nDivsMax, int iChoice, int fUseXor, int fDebug, int fVerbose, int ** ppArray );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ResubComputeWindow( int * pObjs, int nObjs, int nDivsMax, int nLevelIncrease, int fUseXor, int fUseZeroCost, int fDebug, int fVerbose, int ** ppArray )
{
    *ppArray = NULL;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Gia_ManToResub( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int * pObjs = ABC_CALLOC( int, 2*Gia_ManObjNum(p) );
    int i, iFirstPo = 1 + Gia_ManCiNum(p) + Gia_ManAndNum(p);
    assert( Gia_ManIsNormalized(p) );
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
            continue;
        pObjs[2*i+0] = Gia_ObjFaninLit0(Gia_ManObj(p, i), i);
        if ( Gia_ObjIsCo(pObj) )
            pObjs[2*i+1] = pObjs[2*i+0];
        else if ( Gia_ObjIsAnd(pObj) )
            pObjs[2*i+1] = Gia_ObjFaninLit1(Gia_ManObj(p, i), i);
        else assert( 0 );
    }
    return pObjs;
}
Gia_Man_t * Gia_ManFromResub( int * pObjs, int nObjs )
{
    int i;
    Gia_Man_t * pNew = Gia_ManStart( nObjs );
    for ( i = 1; i < nObjs; i++ )
    {
        if ( pObjs[2*i] == 0 ) // pi
            Gia_ManAppendCi( pNew );
        else if ( pObjs[2*i] == pObjs[2*i+1] ) // po
            Gia_ManAppendCo( pNew, pObjs[2*i] );
        else if ( pObjs[2*i] < pObjs[2*i+1] )
            Gia_ManAppendAnd( pNew, pObjs[2*i], pObjs[2*i+1] );
        else if ( pObjs[2*i] > pObjs[2*i+1] )
            Gia_ManAppendXor( pNew, pObjs[2*i], pObjs[2*i+1] );
        else assert( 0 );
    }
    return pNew;
}
Gia_Man_t * Gia_ManResub2Test( Gia_Man_t * p )
{
    int * pObjsNew, * pObjs = Gia_ManToResub( p );
    int nObjsNew = Abc_ResubComputeWindow( pObjs, Gia_ManObjNum(p), 1000, 0, 0, 0, 0, 0, &pObjsNew );
    Gia_Man_t * pNew = Gia_ManFromResub( pObjsNew, nObjsNew );
    ABC_FREE( pObjs );
    ABC_FREE( pObjsNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Rsb2Man_t * Gia_Rsb2ManAlloc()
{
    Gia_Rsb2Man_t * p = ABC_CALLOC( Gia_Rsb2Man_t, 1 );
    return p;
}
void Gia_Rsb2ManFree( Gia_Rsb2Man_t * p )
{
    Vec_IntErase( &p->vObjs   );
    Vec_WrdErase( &p->vSims   );
    Vec_PtrErase( &p->vpDivs  );
    Vec_IntErase( &p->vDivs   );
    Vec_IntErase( &p->vLevels );
    Vec_IntErase( &p->vRefs   );
    Vec_IntErase( &p->vCopies );
    ABC_FREE( p );
}
int Gia_Rsb2ManLevel( Gia_Rsb2Man_t * p )
{
    int i, * pLevs, Level = 0;
    Vec_IntClear( &p->vLevels );
    Vec_IntGrow( &p->vLevels, p->nObjs );
    pLevs = Vec_IntArray( &p->vLevels );
    for ( i = p->nPis + 1; i < p->iFirstPo; i++ )
        pLevs[i] = 1 + Abc_MaxInt( pLevs[2*i+0]/2, pLevs[2*i+1]/2 );
    for ( i = p->iFirstPo; i < p->nObjs; i++ )
        Level = Abc_MaxInt( Level, pLevs[i] = pLevs[2*i+0]/2 );
    return Level;
}
void Gia_Rsb2ManStart( Gia_Rsb2Man_t * p, int * pObjs, int nObjs, int nDivsMax, int nLevelIncrease, int fUseXor, int fUseZeroCost, int fDebug, int fVerbose )
{
    int i;
    // hyper-parameters
    p->nDivsMax       = nDivsMax; 
    p->nLevelIncrease = nLevelIncrease; 
    p->fUseXor        = fUseXor; 
    p->fUseZeroCost   = fUseZeroCost; 
    p->fDebug         = fDebug; 
    p->fVerbose       = fVerbose; 
    // user data
    Vec_IntClear( &p->vObjs );
    Vec_IntPushArray( &p->vObjs, pObjs, nObjs );
    assert( pObjs[0] == 0 );
    assert( pObjs[1] == 0 );
    p->nObjs    = nObjs;
    p->nPis     = 0;
    p->nNodes   = 0;
    p->nPos     = 0;
    p->iFirstPo = 0;
    for ( i = 1; i < nObjs; i++ )
    {
        if ( pObjs[0] == 0 && pObjs[1] == 0 )
            p->nPis++;
        else if ( pObjs[0] == pObjs[1] )
            p->nPos++;
        else
            p->nNodes++;
    }
    assert( nObjs == 1 + p->nPis + p->nNodes + p->nPos );
    p->iFirstPo = nObjs - p->nPos;
    p->Level = Gia_Rsb2ManLevel(p);
    Vec_WrdClear( &p->vSims );
    Vec_WrdGrow( &p->vSims, 2*nObjs );
    Vec_WrdPush( &p->vSims, 0 );
    Vec_WrdPush( &p->vSims, 0 );
    for ( i = 0; i < p->nPis; i++ )
    {
        Vec_WrdPush( &p->vSims, s_Truths6[i] );
        Vec_WrdPush( &p->vSims, ~s_Truths6[i] );
    }
    Vec_IntClear( &p->vDivs   );
    Vec_IntClear( &p->vLevels );
    Vec_IntClear( &p->vRefs   );
    Vec_IntClear( &p->vCopies );
    Vec_PtrClear( &p->vpDivs  );
    Vec_IntGrow( &p->vDivs,   nObjs );
    Vec_IntGrow( &p->vLevels, nObjs );
    Vec_IntGrow( &p->vRefs,   nObjs );
    Vec_IntGrow( &p->vCopies, nObjs );
    Vec_PtrGrow( &p->vpDivs,  nObjs );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Gia_Rsb2ManOdcs( Gia_Rsb2Man_t * p, int iNode )
{
    int i; word Res = 0;
    int  * pObjs = Vec_IntArray( &p->vObjs );
    word * pSims = Vec_WrdArray( &p->vSims );
    for ( i = p->nPis + 1; i < p->iFirstPo; i++ )
    {
        if ( pObjs[2*i+0] < pObjs[2*i+1] )
            pSims[2*i+0] = pSims[pObjs[2*i+0]] & pSims[pObjs[2*i+1]];
        else
            pSims[2*i+0] = pSims[pObjs[2*i+0]] ^ pSims[pObjs[2*i+1]];
        pSims[2*i+1] = ~pSims[2*i+0];        
    }
    for ( i = p->iFirstPo; i < p->nObjs; i++ )
        pSims[2*i+0] = pSims[pObjs[2*i+0]];
    ABC_SWAP( word, pSims[2*iNode+0], pSims[2*iNode+1] );
    for ( i = iNode + 1; i < p->iFirstPo; i++ )
    {
        if ( pObjs[2*i+0] < pObjs[2*i+1] )
            pSims[2*i+0] = pSims[pObjs[2*i+0]] & pSims[pObjs[2*i+1]];
        else
            pSims[2*i+0] = pSims[pObjs[2*i+0]] ^ pSims[pObjs[2*i+1]];
        pSims[2*i+1] = ~pSims[2*i+0];        
    }
    for ( i = p->iFirstPo; i < p->nObjs; i++ )
        Res |= pSims[2*i+0] ^ pSims[pObjs[2*i+0]];
    return Res;
}
// marks MFFC and returns its size
int Gia_Rsb2ManMffc( Gia_Rsb2Man_t * p, int iNode )
{
    int i, * pRefs, * pObjs, nMffc = 0;
    Vec_IntFill( &p->vRefs, p->nObjs, 0 );
    pRefs = Vec_IntArray( &p->vRefs );
    pObjs = Vec_IntArray( &p->vObjs );
    for ( i = p->nObjs - 1; i >= p->iFirstPo; i-- )
        pRefs[pObjs[2*i+0]] = 1;
    for ( i = p->iFirstPo - 1; i > p->nPis; i-- )
        if ( i != iNode && pRefs[i] )
            pRefs[pObjs[2*i+0]] = pRefs[pObjs[2*i+1]] = 1;
    for ( i = p->nPis + 1; i < p->iFirstPo; i++ )
        nMffc += !pRefs[i];
    return nMffc;
}
// collects divisors and maps them into nodes
// assumes MFFC is already marked
int Gia_Rsb2ManDivs( Gia_Rsb2Man_t * p, int iNode )
{
    int i;
    int * pRefs = Vec_IntArray( &p->vRefs );
    int * pObjs = Vec_IntArray( &p->vObjs );
    p->CareSet = Gia_Rsb2ManOdcs( p, iNode );
    p->Truth1 = p->CareSet & Vec_WrdEntry(&p->vSims, iNode);
    p->Truth0 = p->CareSet & ~p->Truth1;
    Vec_PtrClear( &p->vpDivs );
    Vec_PtrPush( &p->vpDivs, &p->Truth0 );
    Vec_PtrPush( &p->vpDivs, &p->Truth1 );
    Vec_IntClear( &p->vDivs );
    Vec_IntPushTwo( &p->vDivs, -1, -1 );
    for ( i = 1; i <= p->nPis; i++ )
    {
        Vec_PtrPush( &p->vpDivs, Vec_WrdEntryP(&p->vSims, i) );
        Vec_IntPush( &p->vDivs, i );
    }
    p->nMffc = Gia_Rsb2ManMffc( p, iNode );
    assert( pRefs[iNode] == 1 );
    pRefs[iNode] = 0;
    for ( i = p->nPis + 1; i < p->iFirstPo; i++ )
    {
        if ( i > iNode )
            pRefs[i] = pRefs[pObjs[2*i+0]] && pRefs[pObjs[2*i+1]];
        if ( !pRefs[i] )
            continue;
        Vec_PtrPush( &p->vpDivs, Vec_WrdEntryP(&p->vSims, i) );
        Vec_IntPush( &p->vDivs, i );
    }
    assert( Vec_IntSize(&p->vDivs) == Vec_PtrSize(&p->vpDivs) );
    return Vec_IntSize(&p->vDivs);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_Rsb2AddNode( Vec_Int_t * vRes, int iLit0, int iLit1, int iRes0, int iRes1 )
{
    int iLitMin = iRes0 < iRes1 ? Abc_LitNotCond(iRes0, Abc_LitIsCompl(iLit0)) : Abc_LitNotCond(iRes1, Abc_LitIsCompl(iLit1));
    int iLitMax = iRes0 < iRes1 ? Abc_LitNotCond(iRes1, Abc_LitIsCompl(iLit1)) : Abc_LitNotCond(iRes0, Abc_LitIsCompl(iLit0));
    int iLitRes = Vec_IntSize(vRes);
    if ( iLit0 < iLit1 ) // and
        Vec_IntPushTwo( vRes, iLitMin, iLitMax );
    else if ( iLit0 > iLit1 ) // xor
    {
        assert( !Abc_LitIsCompl(iLit0) );
        assert( !Abc_LitIsCompl(iLit1) );
        Vec_IntPushTwo( vRes, iLitMax, iLitMin );
    }
    else assert( 0 );
    return iLitRes;
}
int Gia_Rsb2ManInsert_rec( Vec_Int_t * vRes, int nPis, Vec_Int_t * vObjs, int iNode, Vec_Int_t * vResub, Vec_Int_t * vDivs, Vec_Int_t * vCopies, int iObj )
{
    if ( Vec_IntEntry(vCopies, iObj) >= 0 )
        return Vec_IntEntry(vCopies, iObj);
    assert( iObj > nPis );
    if ( iObj == iNode )
    {
        int nVars = Vec_IntSize(vDivs);
        int iLitRes, iTopLit = Vec_IntEntryLast( vResub );
        if ( Abc_Lit2Var(iTopLit) == 0 )
            iLitRes = 0;
        else if ( Abc_Lit2Var(iTopLit) < nVars )
            iLitRes = Gia_Rsb2ManInsert_rec( vRes, nPis, vObjs, -1, vResub, vDivs, vCopies, Vec_IntEntry(vDivs, Abc_Lit2Var(iTopLit)) );
        else
        {
            Vec_Int_t * vCopy = Vec_IntAlloc( 10 );
            int k, iLit, iLit0, iLit1;
            Vec_IntForEachEntryStop( vResub, iLit, k, Vec_IntSize(vResub)-1 )
                if ( Abc_Lit2Var(iLit) < nVars )
                    Gia_Rsb2ManInsert_rec( vRes, nPis, vObjs, -1, vResub, vDivs, vCopies, Vec_IntEntry(vDivs, Abc_Lit2Var(iLit)) );
            Vec_IntForEachEntryDouble( vResub, iLit0, iLit1, k )
            {
                int iVar0 = Abc_Lit2Var(iLit0);
                int iVar1 = Abc_Lit2Var(iLit1);
                int iRes0 = iVar0 < nVars ? Vec_IntEntry(vCopies, Vec_IntEntry(vDivs, iVar0)) : Vec_IntEntry(vCopy, iVar0 - nVars);
                int iRes1 = iVar1 < nVars ? Vec_IntEntry(vCopies, Vec_IntEntry(vDivs, iVar1)) : Vec_IntEntry(vCopy, iVar1 - nVars);
                iLitRes = Gia_Rsb2AddNode( vRes, iLit0, iLit1, iRes0, iRes1 );
                Vec_IntPush( vCopy, iLitRes );
            }
            Vec_IntFree( vCopy );
        }
        iLitRes = Abc_LitNotCond( iLitRes, Abc_LitIsCompl(iTopLit) );
        Vec_IntWriteEntry( vCopies, iObj, iLitRes );
        return iLitRes;
    }
    else
    {
        int iLit0 = Vec_IntEntry( vObjs, 2*iObj+0 );
        int iLit1 = Vec_IntEntry( vObjs, 2*iObj+1 );
        int iRes0 = Gia_Rsb2ManInsert_rec( vRes, nPis, vObjs, iNode, vResub, vDivs, vCopies, Abc_Lit2Var(iLit0) );
        int iRes1 = Gia_Rsb2ManInsert_rec( vRes, nPis, vObjs, iNode, vResub, vDivs, vCopies, Abc_Lit2Var(iLit1) );
        int iLitRes = Gia_Rsb2AddNode( vRes, iLit0, iLit1, iRes0, iRes1 );
        Vec_IntWriteEntry( vCopies, iObj, iLitRes );
        return iLitRes;
    }
}
Vec_Int_t * Gia_Rsb2ManInsert( int nPis, int nPos, Vec_Int_t * vObjs, int iNode, Vec_Int_t * vResub, Vec_Int_t * vDivs, Vec_Int_t * vCopies )
{
    int i, iFirstPo = Vec_IntSize(vObjs) - nPos;
    Vec_Int_t * vRes = Vec_IntAlloc( 2*Vec_IntSize(vObjs) );
    Vec_IntFill( vCopies, Vec_IntSize(vObjs), -1 );
    Vec_IntFill( vRes, 2*(nPis + 1), 0 );
    for ( i = 0; i <= nPis; i++ )
        Vec_IntPush( vCopies, 2*i );
    for ( i = 0; i < nPos; i++ )
        Gia_Rsb2ManInsert_rec( vRes, nPis, vObjs, iNode, vResub, vDivs, vCopies, Abc_Lit2Var(Vec_IntEntry(vObjs, 2*(iFirstPo+1))) );
    for ( i = 0; i < nPos; i++ )
    {
        int iLitNew = Abc_Lit2LitL( Vec_IntArray(vCopies), Vec_IntEntry(vObjs, 2*(iFirstPo+1)) );
        Vec_IntPushTwo( vRes, iLitNew, iLitNew );
    }
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Creating a window with support composed of primary inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// returns the number of nodes added to the window when is iPivot is added
// the window nodes in vNodes are labeled with the current traversal ID
// the new node iPivot and its fanout are temporarily labeled and then unlabeled
int Gia_WinTryAddingNode( Gia_Man_t * p, int iPivot, Vec_Wec_t * vLevels, Vec_Int_t * vNodes )
{
    Vec_Int_t * vLevel; 
    Gia_Obj_t * pObj, * pFanout;
    int k, i, f, Count = 0;
    // precondition:  the levelized structure is empty
    assert( Vec_WecSizeSize(vLevels) == 0 );
    // precondition:  the new object to be added (iPivot) is not in the window
    assert( !Gia_ObjIsTravIdCurrentId(p, iPivot) );
    // add the object to the window and to the levelized structure
    Gia_ObjSetTravIdCurrentId( p, iPivot );
    Vec_WecPush( vLevels, Gia_ObjLevelId(p, iPivot), iPivot );
    // iterate through all objects and explore their fanouts
    Vec_WecForEachLevel( vLevels, vLevel, k )
        Gia_ManForEachObjVec( vLevel, p, pObj, i )
            if ( Gia_ObjFanoutNum(p, pObj) > 10 ) // do not explore objects with high fanout
                Gia_ObjForEachFanoutStatic( p, pObj, pFanout, f )
                    if ( Gia_ObjIsAnd(pFanout) && // internal node
                        !Gia_ObjIsTravIdCurrent(p, pFanout) && // not in the window
                         Gia_ObjIsTravIdCurrent(p, Gia_ObjFanin0(pFanout)) && // but fanins are
                         Gia_ObjIsTravIdCurrent(p, Gia_ObjFanin1(pFanout)) )  // in the window
                    {
                        // add fanout to the window and to the levelized structure
                        Gia_ObjSetTravIdCurrent( p, pFanout );
                        Vec_WecPush( vLevels, Gia_ObjLevel(p, pFanout), Gia_ObjId(p, pFanout) );
                        // count the number of nodes in the structure
                        Count++;
                    }
    // iterate through the nodes in the levelized structure
    Vec_WecForEachLevel( vLevels, vLevel, k )
    {
        Gia_ManForEachObjVec( vLevel, p, pObj, i )
            if ( vNodes == NULL ) // it was a test run - unmark the node
                Gia_ObjSetTravIdPrevious( p, pObj );
            else // it was a real run - permanently add to the node to the window
                Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
        // clean the levelized structure
        Vec_IntClear( vLevel );
    }
    // return the number of nodes to be added
    return Count;
}
// find the first PI to add based on the fanout count
int Gia_WinAddCiWithMaxFanouts( Gia_Man_t * p )
{
    int i, Id, nMaxFan = -1, iMaxFan = -1;
    Gia_ManForEachCiId( p, Id, i )
        if ( nMaxFan < Gia_ObjFanoutNumId(p, Id) )
        {
            nMaxFan = Gia_ObjFanoutNumId(p, Id);
            iMaxFan = Id;
        }
    assert( iMaxFan >= 0 );
    return iMaxFan;
}
// find the next PI to add based on how many nodes will be added to the window
int Gia_WinAddCiWithMaxDivisors( Gia_Man_t * p, Vec_Wec_t * vLevels )
{
    int i, Id, nCurFan, nMaxFan = -1, iMaxFan = -1;
    Gia_ManForEachCiId( p, Id, i )
    {
        if ( Gia_ObjIsTravIdCurrentId( p, Id ) )
            continue;
        nCurFan = Gia_WinTryAddingNode( p, Id, vLevels, NULL );
        if ( nMaxFan < nCurFan )
        {
            nMaxFan = nCurFan;
            iMaxFan = Id;
        }
    }
    assert( iMaxFan >= 0 );
    return iMaxFan;
}
// check if the node has unmarked fanouts
int Gia_WinNodeHasUnmarkedFanouts( Gia_Man_t * p, int iPivot )
{
    int f, iFan;
    Gia_ObjForEachFanoutStaticId( p, iPivot, iFan, f )
        if ( !Gia_ObjIsTravIdCurrentId(p, iFan) )
            return 1;
    return 0;
}
// this is a translation procedure, which converts the array of node IDs (vObjs) 
// into the internal represnetation for the resub engine, which is returned
// (this procedure is not needed when we simply construct a window)
Vec_Int_t * Gia_RsbCiTranslate( Gia_Man_t * p, Vec_Int_t * vObjs, Vec_Int_t * vMap )
{
    int i, iObj, Lit0, Lit1, Fan0, Fan1;
    Vec_Int_t * vNodes = Vec_IntAlloc( 100 );
    assert( Vec_IntSize(vMap) == Gia_ManObjNum(p) );
    Vec_IntPushTwo( vNodes, 0, 0 ); // const0 node
    Vec_IntForEachEntry( vObjs, iObj, i )
    {
        Gia_Obj_t * pObj = Gia_ManObj(p, iObj);
        assert( Gia_ObjIsTravIdCurrentId(p, iObj) );
        Fan0 = Gia_ObjIsCi(pObj) ? 0 : Vec_IntEntry(vMap, Gia_ObjFaninId0(pObj, iObj));
        Fan1 = Gia_ObjIsCi(pObj) ? 0 : Vec_IntEntry(vMap, Gia_ObjFaninId1(pObj, iObj));
        Lit0 = Gia_ObjIsCi(pObj) ? 0 : Abc_LitNotCond( Fan0, Gia_ObjFaninC0(pObj) );
        Lit1 = Gia_ObjIsCi(pObj) ? 0 : Abc_LitNotCond( Fan1, Gia_ObjFaninC1(pObj) );
        Vec_IntWriteEntry( vMap, iObj, Vec_IntSize(vNodes) );
        Vec_IntPushTwo( vNodes, Lit0, Lit1 );
    }
    Vec_IntForEachEntry( vObjs, iObj, i )
        if ( Gia_WinNodeHasUnmarkedFanouts( p, iObj ) )
            Vec_IntPushTwo( vNodes, Vec_IntEntry(vMap, iObj), Vec_IntEntry(vMap, iObj) );
    return vNodes;
}
// construct a high-volume window support by the given number (nPis) of primary inputs
Vec_Int_t * Gia_RsbCiWindow( Gia_Man_t * p, int nPis )
{
    Vec_Int_t * vRes;  int i, iMaxFan;
    Vec_Int_t * vNodes  = Vec_IntAlloc( 100 );
    Vec_Int_t * vMap    = Vec_IntStartFull( Gia_ManObjNum(p) );
    Vec_Wec_t * vLevels = Vec_WecStart( Gia_ManLevelNum(p)+1 );
    Gia_ManStaticFanoutStart( p );
    Gia_ManIncrementTravId(p);
    // add the first one
    iMaxFan = Gia_WinAddCiWithMaxFanouts( p );
    Gia_ObjSetTravIdCurrentId( p, iMaxFan );
    Vec_IntPush( vNodes, iMaxFan );
    // add remaining ones
    for ( i = 1; i < nPis; i++ )
    {
        iMaxFan = Gia_WinAddCiWithMaxDivisors( p, vLevels );
        Gia_WinTryAddingNode( p, iMaxFan, vLevels, vNodes );
    }
    Vec_IntSort( vNodes, 0 );
    vRes = Gia_RsbCiTranslate( p, vNodes, vMap );
    Gia_ManStaticFanoutStop( p );
    Vec_WecFree( vLevels );
    Vec_IntFree( vMap );
Vec_IntPrint( vNodes );
    Vec_IntFree( vNodes );
    return vRes;
}
void Gia_RsbCiWindowTest( Gia_Man_t * p )
{
    Vec_Int_t * vWin = Gia_RsbCiWindow( p, 6 );
    //Vec_IntPrint( vWin );
    Vec_IntFree( vWin );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

