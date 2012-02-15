/**CFile****************************************************************

  FileName    [giaIso.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Graph isomorphism.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaIso.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Gia_IsoLnk_t_       Gia_IsoLnk_t;
struct Gia_IsoLnk_t_ 
{
    int              iBeg;
    int              nSize;
    int              iPrev;
    int              iNext;
};

typedef struct Gia_IsoLst_t_       Gia_IsoLst_t;
struct Gia_IsoLst_t_ 
{
    int              iHead;
    int              iTail;
};

typedef struct Gia_IsoMan_t_       Gia_IsoMan_t;
struct Gia_IsoMan_t_ 
{
    Gia_Man_t *      pGia;
    int              nObjs;
    // collected info
    Vec_Int_t *      vLevels;
    Vec_Int_t *      vFin0Levs;
    Vec_Int_t *      vFin1Levs;
    Vec_Int_t *      vFoutPos;
    Vec_Int_t *      vFoutNeg;
    Vec_Int_t *      vFinSig;
    // sorting structures
    Vec_Int_t *      vMap;
    Vec_Int_t *      vSeens;
    Vec_Int_t *      vCounts;
    Vec_Int_t *      vResult;
    // fanout representation
    Vec_Int_t *      vFanouts;
    // class representation
    Vec_Int_t *      vItems;
    Gia_IsoLst_t     List;
    Gia_IsoLnk_t *   pLinks;
    Gia_IsoLnk_t *   pLinksFree;
    int              nLinksUsed;
    int              nLinksAlloc;
    // temporary storage
    Vec_Ptr_t *      vRoots;
    Vec_Int_t *      vUsed;
    Vec_Int_t *      vRefs;
    // results
    Vec_Ptr_t *      vResults;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_IsoMan_t * Gia_IsoManStart( Gia_Man_t * pGia )
{
    Gia_IsoMan_t * p;
    p = ABC_CALLOC( Gia_IsoMan_t, 1 );
    p->pGia      = pGia;
    p->nObjs     = Gia_ManObjNum( pGia );
    // collected info
    p->vLevels   = Vec_IntAlloc( p->nObjs );
    p->vFin0Levs = Vec_IntAlloc( p->nObjs );
    p->vFin1Levs = Vec_IntAlloc( p->nObjs );
    p->vFoutPos  = Vec_IntAlloc( p->nObjs );
    p->vFoutNeg  = Vec_IntAlloc( p->nObjs );
    p->vFinSig   = Vec_IntAlloc( p->nObjs );
    // sorting structures
    p->vMap      = Vec_IntStartFull( 2*p->nObjs );
    p->vSeens    = Vec_IntAlloc( p->nObjs );
    p->vCounts   = Vec_IntAlloc( p->nObjs );
    p->vResult   = Vec_IntAlloc( p->nObjs );
    // class representation
    p->vItems    = Vec_IntAlloc( p->nObjs );
    // fanout representation
    p->vFanouts  = Vec_IntAlloc( 6 * p->nObjs );
    // temporary storage
    p->vRoots    = Vec_PtrAlloc( 1000 );
    p->vUsed     = Vec_IntAlloc( p->nObjs );
    p->vRefs     = Vec_IntAlloc( p->nObjs );
    // results
    p->vResults  = Vec_PtrAlloc( Gia_ManPoNum(pGia) );
    return p;
}
void Gia_IsoManStop( Gia_IsoMan_t * p )
{
    // collected info
    Vec_IntFree( p->vLevels );
    Vec_IntFree( p->vFin0Levs );
    Vec_IntFree( p->vFin1Levs );
    Vec_IntFree( p->vFoutPos );
    Vec_IntFree( p->vFoutNeg );
    Vec_IntFree( p->vFinSig );
    // sorting structures
    Vec_IntFree( p->vMap );
    Vec_IntFree( p->vSeens );
    Vec_IntFree( p->vCounts );
    Vec_IntFree( p->vResult );
    // class representation
    Vec_IntFree( p->vItems );
    // fanout representation
    Vec_IntFree( p->vFanouts );
    // temporary storage
    Vec_IntFree( p->vRefs );
    Vec_IntFree( p->vUsed );
    Vec_PtrFree( p->vRoots );
//    Vec_PtrFree( p->vResults );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Collect the nodes used for the given PO.]

  Description [Includes Const0, CI and AND nodes, no COs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoCleanUsed( Gia_Man_t * p, Vec_Int_t * vUsed )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObjVec( vUsed, p, pObj, i )
        pObj->Value = 0;
}
void Gia_IsoCollectUsed_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vUsed, Vec_Ptr_t * vRoots )
{
    if ( pObj->Value )
        return;
    if ( Gia_ObjIsAnd(pObj) )
    {
        Gia_IsoCollectUsed_rec( p, Gia_ObjFanin0(pObj), vUsed, vRoots );
        Gia_IsoCollectUsed_rec( p, Gia_ObjFanin1(pObj), vUsed, vRoots );
    }
    else if ( Gia_ObjIsRo(p, pObj) )
        Vec_PtrPush( vRoots, Gia_ObjRoToRi(p, pObj) );
    else if ( !Gia_ObjIsPi(p, pObj) )
        assert( 0 );
    pObj->Value = Vec_IntSize( vUsed );
    Vec_IntPush( vUsed, Gia_ObjId(p, pObj) );
}
void Gia_IsoCollectUsed( Gia_Man_t * p, int iPo, Vec_Int_t * vUsed, Vec_Ptr_t * vRoots )
{
    Gia_Obj_t * pObj;
    int i;
    assert( iPo >= 0 && iPo < Gia_ManPoNum(p) );
    Vec_PtrClear( vRoots );
    Vec_PtrPush( vRoots, Gia_ManPo(p, iPo) );
    // collect used nodes
    Vec_IntClear( vUsed );
    Vec_IntPush( vUsed, 0 );
    Vec_PtrForEachEntry( Gia_Obj_t *, vRoots, pObj, i )
        if ( !Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) )
            Gia_IsoCollectUsed_rec( p, Gia_ObjFanin0(pObj), vUsed, vRoots );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoCreateFanout( Gia_Man_t * p, Vec_Int_t * vUsed, Vec_Int_t * vRefs, Vec_Int_t * vFanout )
{
    // Value of GIA objects points to the index in Used
    // vUsed includes only CIs and ANDs
    Gia_Obj_t * pObj, * pObjRi;
    int * pOff, * pOff0, * pOff1;
    int i, nOffset, Counter = 0;

    // count references
    Vec_IntFill( vRefs, Vec_IntSize(vUsed), 0 );
    Gia_ManForEachObjVec( vUsed, p, pObj, i )
    {
        if ( !i ) continue;
        if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntAddToEntry( vRefs, Gia_ObjFanin0(pObj)->Value, 1 );
            Vec_IntAddToEntry( vRefs, Gia_ObjFanin1(pObj)->Value, 1 );
            Counter += 2;
        }
        else if ( Gia_ObjIsRo(p, pObj) )
        {
            pObj = Gia_ObjRoToRi(p, pObj);
            Vec_IntAddToEntry( vRefs, Gia_ObjFanin0(pObj)->Value, 1 );
            Counter += 1;
        }
        else if ( !Gia_ObjIsPi(p, pObj) )
            assert( 0 );
    }

    // create fanout
    nOffset = Vec_IntSize(vUsed);
    Vec_IntGrowResize( vFanout, 2 * Vec_IntSize(vUsed) + 2 * Counter );
    Gia_ManForEachObjVec( vUsed, p, pObj, i )
    {
        Vec_IntWriteEntry( vFanout, i, nOffset );
        Vec_IntWriteEntry( vFanout, nOffset, 0 );
        nOffset += 1 + Vec_IntEntry(vRefs, pObj->Value);
        if ( Gia_ObjIsAnd(pObj) )
            nOffset += 2;
        else if ( Gia_ObjIsRo(p, pObj) )
            nOffset += 1;
    }
    assert( nOffset == 2 * Vec_IntSize(vUsed) + 2 * Counter );
 
    // load fanout
    Gia_ManForEachObjVec( vUsed, p, pObj, i )
    {
        pOff = Vec_IntEntryP( vFanout, Vec_IntEntry(vFanout, pObj->Value) );
        if ( Gia_ObjIsAnd(pObj) )
        {
            pOff0 = Vec_IntEntryP( vFanout, Vec_IntEntry(vFanout, Gia_ObjFanin0(pObj)->Value) );
            pOff1 = Vec_IntEntryP( vFanout, Vec_IntEntry(vFanout, Gia_ObjFanin1(pObj)->Value) );
            pOff[1+(*pOff)++] = Abc_Var2Lit( Gia_ObjFanin0(pObj)->Value, Gia_ObjFaninC0(pObj) );
            pOff[1+(*pOff)++] = Abc_Var2Lit( Gia_ObjFanin1(pObj)->Value, Gia_ObjFaninC1(pObj) );
            pOff0[1+(*pOff0)++] = Abc_Var2Lit( pObj->Value, Gia_ObjFaninC0(pObj) );
            pOff1[1+(*pOff1)++] = Abc_Var2Lit( pObj->Value, Gia_ObjFaninC1(pObj) );

        }
        else if ( Gia_ObjIsRo(p, pObj) )
        {
            pObjRi = Gia_ObjRoToRi(p, pObj);
            pOff0  = Vec_IntEntryP( vFanout, Vec_IntEntry(vFanout, Gia_ObjFanin0(pObjRi)->Value) );
            pOff[1+(*pOff)++] = Abc_Var2Lit( Gia_ObjFanin0(pObj)->Value, Gia_ObjFaninC0(pObj) );
            pOff0[1+(*pOff0)++] = Abc_Var2Lit( pObj->Value, Gia_ObjFaninC0(pObj) );
        }
    }
    // verify
    Gia_ManForEachObjVec( vUsed, p, pObj, i )
    {
        nOffset = Vec_IntEntry( vFanout, Vec_IntEntry(vFanout, pObj->Value) );
        if ( Gia_ObjIsAnd(pObj) )
            nOffset -= 2;
        else if ( Gia_ObjIsRo(p, pObj) )
            nOffset -= 1;
        assert( nOffset == Vec_IntEntry(vRefs, pObj->Value) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoCreateSigs( Gia_IsoMan_t * p )
{
    Gia_Obj_t * pObj, * pObjRi;
    int i, Lev0, Lev1, Lev;
    Vec_IntClear( p->vLevels );
    Vec_IntClear( p->vFin0Levs );
    Vec_IntClear( p->vFin1Levs );
    Vec_IntClear( p->vFinSig );
    Vec_IntFill( p->vFoutPos, p->nObjs, 0 );
    Vec_IntFill( p->vFoutNeg, p->nObjs, 0 );
    Gia_ManForEachObjVec( p->vUsed, p->pGia, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            Lev0 = Vec_IntEntry( p->vLevels, Gia_ObjFanin0(pObj)->Value );
            Lev1 = Vec_IntEntry( p->vLevels, Gia_ObjFanin1(pObj)->Value );
            Lev  = 1 + Abc_MaxInt( Lev0, Lev1 );

            Vec_IntPush( p->vLevels, Lev );
            if ( Gia_ObjFaninC0(pObj) < Gia_ObjFaninC1(pObj) || (Gia_ObjFaninC0(pObj) == Gia_ObjFaninC1(pObj) && Lev0 < Lev1) )
            {
                Vec_IntPush( p->vFin0Levs, Lev-Lev0 );
                Vec_IntPush( p->vFin1Levs, Lev-Lev1 );
            }
            else
            {
                Vec_IntPush( p->vFin0Levs, Lev-Lev1 );
                Vec_IntPush( p->vFin1Levs, Lev-Lev0 );
            }
            if ( Gia_ObjIsMuxType(pObj) ) // uniqify MUX/XOR
                Vec_IntPush( p->vFinSig, 3 );
            else
                Vec_IntPush( p->vFinSig, Gia_ObjFaninC0(pObj) + Gia_ObjFaninC1(pObj) );
            Vec_IntAddToEntry( Gia_ObjFaninC0(pObj) ? p->vFoutNeg : p->vFoutPos, Gia_ObjFanin0(pObj)->Value, 1 );
            Vec_IntAddToEntry( Gia_ObjFaninC1(pObj) ? p->vFoutNeg : p->vFoutPos, Gia_ObjFanin1(pObj)->Value, 1 );
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            pObjRi = Gia_ObjRoToRi(p->pGia, pObj);
            Vec_IntPush( p->vLevels, 0 );
            Vec_IntPush( p->vFin0Levs, 1 );
            Vec_IntPush( p->vFin1Levs, 0 );
            Vec_IntPush( p->vFinSig, Gia_ObjFaninC0(pObjRi) );
            Vec_IntAddToEntry( Gia_ObjFaninC0(pObjRi) ? p->vFoutNeg : p->vFoutPos, Gia_ObjFanin0(pObjRi)->Value, 1 );
        }
        else if ( Gia_ObjIsPi(p->pGia, pObj) )
        {
            Vec_IntPush( p->vLevels, 0 );
            Vec_IntPush( p->vFin0Levs, 0 );
            Vec_IntPush( p->vFin1Levs, 0 );
            Vec_IntPush( p->vFinSig, 4 );
        }
        else if ( Gia_ObjIsConst0(pObj) )
        {
            Vec_IntPush( p->vLevels, 0 );
            Vec_IntPush( p->vFin0Levs, 0 );
            Vec_IntPush( p->vFin1Levs, 0 );
            Vec_IntPush( p->vFinSig, 5 );
        }
        else assert( 0 );
    }
    // create items
    Vec_IntClear( p->vItems );
    for ( i = 0; i < Vec_IntSize(p->vUsed); i++ )
        Vec_IntPush( p->vItems, i );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoSortStats( Vec_Int_t * vItems, Vec_Int_t * vCosts, Vec_Int_t * vMap, Vec_Int_t * vSeens, Vec_Int_t * vCounts, Vec_Int_t * vResult )
{
    int i, Entry, Place;
    // assumes vCosts are between 0 and Vec_IntSize(vMap)
    // assumes vMap is clean and leaves it clean
//    Vec_IntForEachEntry( vMap, Entry, i )
//        assert( Entry == -1 );

//    printf( "vItems: " );
//    Vec_IntPrint( vItems );
//    printf( "vCosts: " );
//    Vec_IntPrint( vCosts );

    // collect places
    Vec_IntClear( vSeens );
    Vec_IntClear( vCounts );
    Vec_IntForEachEntry( vCosts, Entry, i )
    {
        Place = Vec_IntEntry(vMap, Entry);
        if ( Place == -1 )
        {
            Vec_IntWriteEntry( vMap, Entry, Vec_IntSize(vSeens) );
            Vec_IntPush( vSeens, Entry );
            Vec_IntPush( vCounts, 1 );
        }
        else
            Vec_IntAddToEntry( vCounts, Place, 1 );
    }

    // sort places
    Vec_IntSort( vSeens, 0 );

//    printf( "vCounts: " );
//    Vec_IntPrint( vCounts );
//    printf( "vSeens: " );
//    Vec_IntPrint( vSeens );

    // create the final array
    Vec_IntClear( vResult );
    Vec_IntForEachEntry( vSeens, Entry, i )
    {
        Place = Vec_IntEntry( vMap, Entry );
        Vec_IntPush( vResult, Entry );
        Vec_IntPush( vResult, Vec_IntEntry(vCounts, Place) );
    }

    // clean map
    Vec_IntForEachEntry( vSeens, Entry, i )
        Vec_IntWriteEntry( vMap, Entry, -1 );

//    printf( "vResult: " );
//    Vec_IntPrint( vResult );

//    printf( "(%d)", Vec_IntSize(vResult)/2 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoSortVec( Vec_Int_t * vItems, Vec_Int_t * vCosts, Vec_Int_t * vMap, Vec_Int_t * vSeens, Vec_Int_t * vCounts, Vec_Int_t * vResult )
{
    int i, Entry, Place, Counter;
    // assumes vCosts are between 0 and Vec_IntSize(vMap)
    // assumes vMap is clean and leaves it clean
    assert( Vec_IntSize(vItems) > 1 );
    if ( Vec_IntSize(vItems) < 15 )
    {
        Vec_IntGrowResize( vResult, Vec_IntSize(vItems) );
        memmove( Vec_IntArray(vResult),  Vec_IntArray(vItems), sizeof(int) * Vec_IntSize(vItems) );
        Vec_IntSelectSortCost( Vec_IntArray(vResult), Vec_IntSize(vItems), vCosts );
        return;
    }

    // collect places
    Vec_IntClear( vSeens );
    Vec_IntClear( vCounts );
    Vec_IntForEachEntry( vCosts, Entry, i )
    {
        Place = Vec_IntEntry(vMap, Entry);
        if ( Place == -1 )
        {
            Vec_IntWriteEntry( vMap, Entry, Vec_IntSize(vSeens) );
            Vec_IntPush( vSeens, Entry );
            Vec_IntPush( vCounts, 1 );
        }
        else
            Vec_IntAddToEntry( vCounts, Place, 1 );
    }

    // sort places
    Vec_IntSort( vSeens, 0 );

    // set the map to point to the place in the final array
    Counter = 0;
    Vec_IntForEachEntry( vSeens, Entry, i )
    {
        Place = Vec_IntEntry( vMap, Entry ); 
        Vec_IntWriteEntry( vMap, Entry, Counter );
        Counter += Vec_IntEntry( vCounts, Place );
    }
    assert( Counter == Vec_IntSize(vItems) );

    // fill the result
    Vec_IntGrowResize( vResult, Vec_IntSize(vItems) );
    Vec_IntFill( vResult, Vec_IntSize(vItems), -1 ); // verify
    Vec_IntForEachEntry( vItems, Entry, i )
    {
        Place = Vec_IntAddToEntry( vMap, Entry, 1 ) - 1;
        Vec_IntWriteEntry( vResult, Place, Entry );
    }
    Vec_IntForEachEntry( vResult, Entry, i ) // verify
        assert( Entry >= 0 );

    // clean map
    Vec_IntForEachEntry( vSeens, Entry, i )
        Vec_IntWriteEntry( vMap, Entry, -1 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_IsoCreateStats( Gia_IsoMan_t * p )
{
    Vec_Int_t * vRes;
    vRes = Vec_IntAlloc( 1000 );
    Gia_IsoSortStats( p->vItems, p->vLevels,   p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vRes, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFin0Levs, p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vRes, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFin1Levs, p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vRes, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFoutPos,  p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vRes, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFoutNeg,  p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vRes, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFinSig,   p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vRes, p->vResult );
    return vRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_IsoOne( Gia_IsoMan_t * p, int iPo )
{
    Vec_Int_t * vStats = NULL;
    Gia_IsoCollectUsed( p->pGia, iPo, p->vUsed, p->vRoots );
//    Gia_IsoCreateFanout( p->pGia, p->vUsed, p->vRefs, p->vFanouts );
    Gia_IsoCreateSigs( p );
    vStats = Gia_IsoCreateStats( p );
    Gia_IsoCleanUsed( p->pGia, p->vUsed );
    return vStats;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoTest( Gia_Man_t * pGia )
{
    int fVerbose = 0;
    Vec_Ptr_t * vResults;
    Vec_Int_t * vStats;
    Gia_IsoMan_t * p;
    int i, clk = clock();
    Gia_ManCleanValue( pGia );
    p = Gia_IsoManStart( pGia );
    for ( i = 0; i < Gia_ManPoNum(pGia); i++ )
    {
        if ( i % 1000 == 0 )
            printf( "Finished %5d\r", i );
        vStats = Gia_IsoOne( p, i );
        Vec_PtrPush( p->vResults, vStats );
        if ( fVerbose )
        printf( "%d ", Vec_IntSize(vStats)/2 );
    }
    if ( fVerbose )
    printf( "               \n" );

    vResults = p->vResults;
    p->vResults = NULL;
    Gia_IsoManStop( p );
//    return vResults;
    Vec_VecFree( (Vec_Vec_t *)vResults );
    Abc_PrintTime( 1, "Time", clock() - clk );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

