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

typedef struct Gia_IsoMan_t_       Gia_IsoMan_t;
struct Gia_IsoMan_t_ 
{
    Gia_Man_t *      pGia;
    int              nObjs;
    int              nUniques;
    // collected info
    Vec_Int_t *      vLevels;
    Vec_Int_t *      vFin0Levs;
    Vec_Int_t *      vFin1Levs;
    Vec_Int_t *      vFinSig;
    Vec_Int_t *      vFoutPos;
    Vec_Int_t *      vFoutNeg;
    // sorting structures
    Vec_Int_t *      vMap;
    Vec_Int_t *      vSeens;
    Vec_Int_t *      vCounts;
    Vec_Int_t *      vResult;
    // fanout representation
    Vec_Int_t *      vFanout;
    Vec_Int_t *      vFanout2;
    // class representation
    Vec_Int_t *      vItems;
    Vec_Int_t *      vUniques;
    Vec_Int_t *      vClass;
    Vec_Int_t *      vClass2;
    Vec_Int_t *      vClassNew;
    Vec_Int_t *      vLevelLim;
    // temporary storage
    Vec_Ptr_t *      vRoots;
    Vec_Int_t *      vUsed;
    Vec_Int_t *      vRefs;
    // results
    Vec_Ptr_t *      vResults;
    Vec_Int_t *      vPermCis;
    Vec_Int_t *      vPermCos;
};

static inline int *  Gia_IsoFanoutVec( Vec_Int_t * p, int Id )  { return Vec_IntEntryP( p, Vec_IntEntry(p, Id) );       }


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
    p->vFinSig   = Vec_IntAlloc( p->nObjs );
    p->vFoutPos  = Vec_IntAlloc( p->nObjs );
    p->vFoutNeg  = Vec_IntAlloc( p->nObjs );
    // sorting structures
    p->vMap      = Vec_IntStartFull( 2*p->nObjs );
    p->vSeens    = Vec_IntAlloc( p->nObjs );
    p->vCounts   = Vec_IntAlloc( p->nObjs );
    p->vResult   = Vec_IntAlloc( p->nObjs );
    // class representation
    p->vItems    = Vec_IntAlloc( p->nObjs );
    p->vUniques  = Vec_IntAlloc( p->nObjs );
    p->vClass    = Vec_IntAlloc( p->nObjs/2 );
    p->vClass2   = Vec_IntAlloc( p->nObjs/2 );
    p->vClassNew = Vec_IntAlloc( p->nObjs/2 );
    p->vLevelLim = Vec_IntAlloc( 1000 );
    // fanout representation
    p->vFanout   = Vec_IntAlloc( 6 * p->nObjs );
    p->vFanout2  = Vec_IntAlloc( 0 );
    // temporary storage
    p->vRoots    = Vec_PtrAlloc( 1000 );
    p->vUsed     = Vec_IntAlloc( p->nObjs );
    p->vRefs     = Vec_IntAlloc( p->nObjs );
    // results
    p->vResults  = Vec_PtrAlloc( Gia_ManPoNum(pGia) );
    p->vPermCis  = Vec_IntAlloc( Gia_ManCiNum(pGia) );
    p->vPermCos  = Vec_IntAlloc( Gia_ManCoNum(pGia) );
    return p;
}
void Gia_IsoManStop( Gia_IsoMan_t * p )
{
    // collected info
    Vec_IntFree( p->vLevels );
    Vec_IntFree( p->vFin0Levs );
    Vec_IntFree( p->vFin1Levs );
    Vec_IntFree( p->vFinSig );
    Vec_IntFree( p->vFoutPos );
    Vec_IntFree( p->vFoutNeg );
    // sorting structures
    Vec_IntFree( p->vMap );
    Vec_IntFree( p->vSeens );
    Vec_IntFree( p->vCounts );
    Vec_IntFree( p->vResult );
    // class representation
    Vec_IntFree( p->vItems );
    Vec_IntFree( p->vUniques );
    Vec_IntFree( p->vClass );
    Vec_IntFree( p->vClass2 );
    Vec_IntFree( p->vClassNew );
    Vec_IntFree( p->vLevelLim );
    // fanout representation
    Vec_IntFree( p->vFanout );
    Vec_IntFree( p->vFanout2 );
    // temporary storage
    Vec_IntFree( p->vRefs );
    Vec_IntFree( p->vUsed );
    Vec_PtrFree( p->vRoots );
    // results
//    Vec_PtrFree( p->vResults );
    Vec_IntFree( p->vPermCis );
    Vec_IntFree( p->vPermCos );
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
            pOff0 = Gia_IsoFanoutVec( vFanout, Gia_ObjFanin0(pObj)->Value );
            pOff1 = Gia_IsoFanoutVec( vFanout, Gia_ObjFanin1(pObj)->Value );
            pOff[1+(*pOff)++] = Abc_Var2Lit( Gia_ObjFanin0(pObj)->Value, Gia_ObjFaninC0(pObj) );
            pOff[1+(*pOff)++] = Abc_Var2Lit( Gia_ObjFanin1(pObj)->Value, Gia_ObjFaninC1(pObj) );
            pOff0[1+(*pOff0)++] = Abc_Var2Lit( pObj->Value, Gia_ObjFaninC0(pObj) );
            pOff1[1+(*pOff1)++] = Abc_Var2Lit( pObj->Value, Gia_ObjFaninC1(pObj) );

        }
        else if ( Gia_ObjIsRo(p, pObj) )
        {
            pObjRi = Gia_ObjRoToRi(p, pObj);
            pOff0  = Gia_IsoFanoutVec( vFanout, Gia_ObjFanin0(pObjRi)->Value );
            pOff[1+(*pOff)++] = Abc_Var2Lit( Gia_ObjFanin0(pObjRi)->Value, Gia_ObjFaninC0(pObjRi) );
            pOff0[1+(*pOff0)++] = Abc_Var2Lit( pObj->Value, Gia_ObjFaninC0(pObjRi) );
        }
    }
    // verify
    Gia_ManForEachObjVec( vUsed, p, pObj, i )
    {
        nOffset = *Gia_IsoFanoutVec( vFanout, pObj->Value );
        if ( Gia_ObjIsAnd(pObj) )
            nOffset -= 2;
        else if ( Gia_ObjIsRo(p, pObj) )
            nOffset -= 1;
        assert( nOffset == Vec_IntEntry(vRefs, pObj->Value) );
    }
}

/**Function*************************************************************

  Synopsis    [Add fanouts of a new singleton object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_IsoAddSingletonFanouts( Gia_IsoMan_t * p, int Item, int Unique )
{
    int i, * pFan, * pFan2;
    pFan = Gia_IsoFanoutVec( p->vFanout, Item );
    for ( i = 0; i < pFan[0]; i++ )
    {
        if ( Vec_IntEntry( p->vUniques, Abc_Lit2Var(pFan[1+i]) ) >= 0 )
            continue;
        pFan2 = Gia_IsoFanoutVec( p->vFanout2, Abc_Lit2Var(pFan[1+i]) );
        pFan2[1+(*pFan2)++] = Abc_Var2Lit( Unique, Abc_LitIsCompl(pFan[1+i]) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoCreateFanout2( Gia_IsoMan_t * p )
{
    int i, Entry, nOffset, nFanouts = 0, nLeftover = 0;
    assert( Vec_IntSize(p->vFanout2) == 0 );
    // count the number of fanouts and objects remaining
    Vec_IntForEachEntry( p->vUniques, Entry, i )
    {
        if ( Entry >= 0 )
            continue;
        nLeftover++;
        nFanouts += *Gia_IsoFanoutVec(p->vFanout, i);
    }
    assert( nLeftover + p->nUniques == Vec_IntSize(p->vUsed) );
    // assign the fanouts
    nOffset = Vec_IntSize(p->vUsed);
    Vec_IntGrowResize( p->vFanout2, Vec_IntSize(p->vUsed) + 2 * nLeftover + nFanouts );
    Vec_IntForEachEntry( p->vUniques, Entry, i )
    {
        if ( Entry >= 0 )
            continue;
        Vec_IntWriteEntry( p->vFanout2, i, nOffset );
        Vec_IntWriteEntry( p->vFanout2, nOffset, 0 );
        nOffset += 2 + *Gia_IsoFanoutVec(p->vFanout, i);
    }
    assert( nOffset == Vec_IntSize(p->vUsed) + 2 * nLeftover + nFanouts );
    // add currently available items
    Vec_IntForEachEntry( p->vUniques, Entry, i )
    {
        if ( Entry == -1 )
            continue;
        Gia_IsoAddSingletonFanouts( p, i, Entry );
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
    Vec_IntFill( p->vFoutPos, Vec_IntSize(p->vUsed), 0 );
    Vec_IntFill( p->vFoutNeg, Vec_IntSize(p->vUsed), 0 );
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
            Vec_IntPush( p->vFin0Levs, 1 ); // not ready yet!
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
    assert( Vec_IntSize( p->vLevels ) == Vec_IntSize(p->vUsed) );
    assert( Vec_IntSize( p->vFin0Levs ) == Vec_IntSize(p->vUsed) );
    assert( Vec_IntSize( p->vFin1Levs ) == Vec_IntSize(p->vUsed) );
    assert( Vec_IntSize( p->vFinSig ) == Vec_IntSize(p->vUsed) );
    // prepare items
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
    Vec_IntForEachEntry( vItems, Entry, i )
    {
        Entry = Vec_IntEntry(vCosts, Entry);
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
Vec_Int_t * Gia_IsoCreateStats( Gia_IsoMan_t * p, int iPo )
{
    Vec_Int_t * vStats = Vec_IntAlloc( 1000 );
    Gia_IsoCollectUsed( p->pGia, iPo, p->vUsed, p->vRoots );
    Gia_IsoSortStats( p->vItems, p->vLevels,   p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vStats, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFin0Levs, p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vStats, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFin1Levs, p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vStats, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFoutPos,  p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vStats, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFoutNeg,  p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vStats, p->vResult );
    Gia_IsoSortStats( p->vItems, p->vFinSig,   p->vMap, p->vSeens, p->vCounts, p->vResult );   Vec_IntAppend( vStats, p->vResult );
    Gia_IsoCleanUsed( p->pGia, p->vUsed );
    return vStats;
}




/**Function*************************************************************

  Synopsis    [Sorting an array of entries.]

  Description [This procedure can have the following outcomes:
  - There is no refinement (the class remains unchanged).
  - There is complete refinement (all elements became singletons)
  - There is partial refinement (some new classes and some singletons)
  The permutes set of items if returned in vItems.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoSortVec( Vec_Int_t * vItems, Vec_Int_t * vCosts, Vec_Int_t * vMap, 
                     Vec_Int_t * vSeens, Vec_Int_t * vCounts, Vec_Int_t * vResult,
                     Vec_Int_t * vClassNew )
{
    int i, Entry, Entry0, Place, Counter;
    // assumes vCosts are between 0 and Vec_IntSize(vMap)
    // assumes vMap is clean and leaves it clean
    assert( Vec_IntSize(vItems) > 1 );

    // prepare return values
    Vec_IntClear( vClassNew );

    // collect places
    Vec_IntClear( vSeens );
    Vec_IntClear( vCounts );
    Vec_IntForEachEntry( vItems, Entry0, i )
    {
        Entry = Vec_IntEntry(vCosts, Entry0);
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

    // check if refinement is happening
    if ( Vec_IntSize(vSeens) == 1 ) // there is no refinement
    {
        Vec_IntPush( vClassNew, 0 );
        Vec_IntPush( vClassNew, Vec_IntSize(vItems) );
        // no need to change vItems
    }
    else // complete or partial refinement
    {
        // sort places
        Vec_IntSort( vSeens, 0 );

        // set the map to point to the place in the final array
        Counter = 0;
        Vec_IntForEachEntry( vSeens, Entry, i )
        {
            Place = Vec_IntEntry( vMap, Entry ); 
            Vec_IntWriteEntry( vMap, Entry, Counter );
            Vec_IntPush( vClassNew, Counter );
            Vec_IntPush( vClassNew, Vec_IntEntry( vCounts, Place ) );
            assert( Vec_IntEntry( vCounts, Place ) > 0 );
            Counter += Vec_IntEntry( vCounts, Place );
        }
        assert( Counter == Vec_IntSize(vItems) );

        // fill the result
        Vec_IntGrowResize( vResult, Vec_IntSize(vItems) );
        Vec_IntFill( vResult, Vec_IntSize(vItems), -1 ); // verify
        Vec_IntForEachEntry( vItems, Entry0, i )
        {
            Entry = Vec_IntEntry(vCosts, Entry0);
            Place = Vec_IntAddToEntry( vMap, Entry, 1 ) - 1;
            Vec_IntWriteEntry( vResult, Place, Entry0 );
        }
        Vec_IntForEachEntry( vResult, Entry, i ) // verify
            assert( Entry >= 0 );
        assert( Vec_IntSize(vItems) == Vec_IntSize(vResult) );
        memmove( Vec_IntArray(vItems), Vec_IntArray(vResult), sizeof(int) * Vec_IntSize(vResult) );
    }

    // clean map
    Vec_IntForEachEntry( vSeens, Entry, i )
        Vec_IntWriteEntry( vMap, Entry, -1 );
}

/**Function*************************************************************

  Synopsis    [Introduces a new singleton object.]

  Description [Updates current equivalence classes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoAddSingleton( Gia_IsoMan_t * p, int Item )
{
    // assign unique number
    assert( Vec_IntEntry( p->vUniques, Item ) == -1 );
    Vec_IntWriteEntry( p->vUniques, Item, p->nUniques++ );
    if ( Vec_IntSize(p->vFanout2) == 0 )
        return;
    // create fanouts 
    Gia_IsoAddSingletonFanouts( p, Item, p->nUniques-1 );
}

/**Function*************************************************************

  Synopsis    [Updates current equivalence classes.]]

  Description [
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_IsoRefine( Gia_IsoMan_t * p, Vec_Int_t * vParam )
{
    Vec_Int_t vThis, * pTemp;
    int i, k, Begin, nSize, Begin2, nSize2, Counter = 0;
    assert( Vec_IntSize(p->vClass) > 0 );
    assert( Vec_IntSize(p->vClass) % 2 == 0 );
    Vec_IntClear( p->vClass2 );
    Vec_IntForEachEntryDouble( p->vClass, Begin, nSize, i )
    {
        vThis.nSize  = vThis.nCap = nSize;
        vThis.pArray = Vec_IntArray(p->vItems) + Begin;
        Gia_IsoSortVec( &vThis, vParam, p->vMap, p->vSeens, p->vCounts, p->vResult, p->vClassNew );
        Vec_IntForEachEntryDouble( p->vClassNew, Begin2, nSize2, k )
        {
            if ( nSize2 == 1 )
            {
                Gia_IsoAddSingleton( p, Vec_IntEntry(p->vItems, Begin+Begin2) );
                Counter++;
                continue;
            }
            Vec_IntPush( p->vClass2, Begin+Begin2 );
            Vec_IntPush( p->vClass2, nSize2 );
        }
    }
    // update classes
    pTemp = p->vClass2; p->vClass2 = p->vClass; p->vClass = pTemp;
    // remember beginning of each level
    if ( vParam == p->vLevels )
    {
        Vec_IntClear( p->vLevelLim );
        Vec_IntForEachEntryDouble( p->vClass, Begin, nSize, i )
        {
            assert( nSize > 0 );
            assert( Vec_IntEntry(p->vLevels, Vec_IntEntry(p->vItems, Begin)) == i );
            Vec_IntPush( p->vLevelLim, Begin );
        }
        Vec_IntPush( p->vLevelLim, Vec_IntSize(p->vItems) );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_IsoAssignUniqueToLastLevel( Gia_IsoMan_t * p )
{
    int i, Begin, End, Item, Level, Counter = 0;
    assert( Vec_IntSize( p->vClass ) > 0 );
    // get the last unrefined class
    Begin = Vec_IntEntry( p->vClass, Vec_IntSize(p->vClass)-2 );
    // get the last unrefined class
    Item  = Vec_IntEntry( p->vItems, Begin );
    // get the level of this class
    Level = Vec_IntEntry( p->vLevels, Item );
    // get the first entry on this level
    Begin = Vec_IntEntry( p->vLevelLim, Level );
    End   = Vec_IntEntry( p->vLevelLim, Level+1 );
    // assign all unassigned items on this level
    Vec_IntForEachEntryStartStop( p->vItems, Item, i, Begin, End )
        if ( Vec_IntEntry( p->vUniques, Item ) == -1 )
        {
            Gia_IsoAddSingleton( p, Item );
            Counter++;
        }
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoPrint( Gia_IsoMan_t * p, int Iter, int nSingles, int Time )
{
    printf( "Iter %3d : ", Iter );
    printf( "Classes =%7d. ", Vec_IntSize(p->vClass)/2 );
    printf( "Uniques =%7d. ", p->nUniques );
    printf( "Singles =%7d. ", nSingles );
    Abc_PrintTime( 1, "Time", Time );
}

/**Function*************************************************************

  Synopsis    [Compares two objects by their ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjCompareByValue( Gia_Obj_t ** pp1, Gia_Obj_t ** pp2 )
{
    Gia_Obj_t * pObj1 = *pp1;
    Gia_Obj_t * pObj2 = *pp2;
    assert( Gia_ObjIsTerm(pObj1) && Gia_ObjIsTerm(pObj2) );
    return pObj1->Value - pObj2->Value;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoCreateUniques( Gia_IsoMan_t * p, int iPo )
{
    Vec_Int_t * vArray[6] = { p->vLevels, p->vFin0Levs, p->vFin1Levs, p->vFoutPos, p->vFoutNeg, p->vFinSig };
    int i, nSingles, clk = clock();
    Gia_IsoCollectUsed( p->pGia, iPo, p->vUsed, p->vRoots );
    Vec_IntClear( p->vFanout2 );
    // prepare uniques
    p->nUniques = 0;
    Vec_IntFill( p->vUniques, Vec_IntSize(p->vUsed), -1 );
    Gia_IsoAddSingleton( p, 0 );
    // prepare classes
    Vec_IntClear( p->vClass );
    Vec_IntPush( p->vClass, 1 );
    Vec_IntPush( p->vClass, Vec_IntSize(p->vUsed) );
    // perform refinement
    Gia_IsoPrint( p, 0, 0, clock() - clk );
    for ( i = 0; i < 6; i++ )
    {
        nSingles = Gia_IsoRefine( p, vArray[i] );
        Gia_IsoPrint( p, i+1, nSingles, clock() - clk );
    }
    // derive fanouts
    Gia_IsoCreateFanout( p->pGia, p->vUsed, p->vRefs, p->vFanout );
    Gia_IsoCreateFanout2( p );
    // perform refinement
    for ( i = 6; p->nUniques < Vec_IntSize(p->vUsed); i++ )
    {
        nSingles = Gia_IsoRefine( p, NULL );
        Gia_IsoPrint( p, i+1, nSingles, clock() - clk );
        if ( nSingles == 0 )
        {
            nSingles = Gia_IsoAssignUniqueToLastLevel( p );
            Gia_IsoPrint( p, i+1, nSingles, clock() - clk );
        }
    }
    // finished refinement
    Gia_IsoCleanUsed( p->pGia, p->vUsed );
}

/**Function*************************************************************

  Synopsis    [Returns canonical permutation of the inputs.]

  Description [Assumes that each CI/AND object has its unique number set.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFindIsoPermCis( Gia_Man_t * p, Vec_Ptr_t * vTemp, Vec_Int_t * vRes )
{
    Gia_Obj_t * pObj;
    int i;
    Vec_IntClear( vRes );
    // assign unique IDs to PIs
    Vec_PtrClear( vTemp );
    Gia_ManForEachPi( p, pObj, i )
        Vec_PtrPush( vTemp, pObj );
    Vec_PtrSort( vTemp, (int (*)(void))Gia_ObjCompareByValue );
    // create the result
    Vec_PtrForEachEntry( Gia_Obj_t *, vTemp, pObj, i )
        Vec_IntPush( vRes, Gia_ObjCioId(pObj) );
    // assign unique IDs to ROs
    Vec_PtrClear( vTemp );
    Gia_ManForEachRo( p, pObj, i )
        Vec_PtrPush( vTemp, pObj );
    Vec_PtrSort( vTemp, (int (*)(void))Gia_ObjCompareByValue );
    // create the result
    Vec_PtrForEachEntry( Gia_Obj_t *, vTemp, pObj, i )
        Vec_IntPush( vRes, Gia_ObjCioId(pObj) );
}

/**Function*************************************************************

  Synopsis    [Find the canonical permutation of the COs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFindIsoPermCos( Gia_Man_t * p, Vec_Int_t * vPermCis, Vec_Ptr_t * vTemp, Vec_Int_t * vRes )
{
    Gia_Obj_t * pObj;
    int i, Entry, Diff;
    assert( Vec_IntSize(vPermCis) == Gia_ManCiNum(p) );
    Vec_IntClear( vRes );
    if ( Gia_ManPoNum(p) == 1 )
        Vec_IntPush( vRes, 0 );
    else
    {
        Vec_PtrClear( vTemp );
        Gia_ManForEachPo( p, pObj, i )
        {
            pObj->Value = Abc_Var2Lit( Gia_ObjFanin0(pObj)->Value, Gia_ObjFaninC0(pObj) );
            Vec_PtrPush( vTemp, pObj );
        }
        Vec_PtrSort( vTemp, (int (*)(void))Gia_ObjCompareByValue );
        Vec_PtrForEachEntry( Gia_Obj_t *, vTemp, pObj, i )
            Vec_IntPush( vRes, Gia_ObjCioId(pObj) );
    }
    // add flop outputs
    Diff = Gia_ManPoNum(p) - Gia_ManPiNum(p);
    Vec_IntForEachEntryStart( vPermCis, Entry, i, Gia_ManPiNum(p) )
        Vec_IntPush( vRes, Entry + Diff );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDupCanonical( Gia_Man_t * p, Vec_Int_t * vUsed, Vec_Int_t * vUniques )
{
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_IsoCompareVecStr( Vec_Str_t ** p1, Vec_Str_t ** p2 )
{
    return Vec_StrCompareVec( *p1, *p2 );
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
        if ( i % 100 == 0 )
            printf( "Finished %5d\r", i );
        vStats = Gia_IsoCreateStats( p, i );
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


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_IsoFilterPos( Gia_Man_t * pGia, int fVerbose )
{
//    int fVeryVerbose = 0;
    Gia_IsoMan_t * p;
    Gia_Man_t * pTemp;
    Vec_Ptr_t * vBuffers, * vClasses;
    Vec_Int_t * vLevel, * vRemain;
    Vec_Str_t * vStr, * vPrev;
    int i, nUnique = 0, clk = clock();
    int clkAig = 0, clkIso = 0, clk2;

    // start the manager
    Gia_ManCleanValue( pGia );
    p = Gia_IsoManStart( pGia );
    // derive AIG for each PO
    vBuffers = Vec_PtrAlloc( Gia_ManPoNum(pGia) );
    for ( i = 0; i < Gia_ManPoNum(pGia); i++ )
    {
        if ( i % 100 == 0 )
            printf( "%6d finished...\r", i );

        clk2 = clock();
        pTemp = Gia_ManDupCanonical( pGia, p->vUsed, p->vUniques );
        clkIso += clock() - clk2;

        clk2 = clock();
        vStr  = Gia_WriteAigerIntoMemoryStr( pTemp );
        clkAig += clock() - clk2;

        Vec_PtrPush( vBuffers, vStr );
        Gia_ManStop( pTemp );
        // remember the output number in nCap (attention: hack!)
        vStr->nCap = i;
    }
    // stop the manager
    Gia_IsoManStop( p );

//    s_Counter = 0;
    if ( fVerbose )
    {
    Abc_PrintTime( 1, "Isomorph  time", clkIso );
    Abc_PrintTime( 1, "AIGER     time", clkAig );
    }

    // sort the infos
    clk = clock();
    Vec_PtrSort( vBuffers, (int (*)(void))Gia_IsoCompareVecStr );

    // create classes
    clk = clock();
    vClasses = Vec_PtrAlloc( Gia_ManPoNum(pGia) );
    // start the first class
    Vec_PtrPush( vClasses, (vLevel = Vec_IntAlloc(4)) );
    vPrev = (Vec_Str_t *)Vec_PtrEntry( vBuffers, 0 );
    Vec_IntPush( vLevel, vPrev->nCap );
    // consider other classes
    Vec_PtrForEachEntryStart( Vec_Str_t *, vBuffers, vStr, i, 1 )
    {
        if ( Vec_StrCompareVec(vPrev, vStr) )
            Vec_PtrPush( vClasses, Vec_IntAlloc(4) );
        vLevel = (Vec_Int_t *)Vec_PtrEntryLast( vClasses );
        Vec_IntPush( vLevel, vStr->nCap );
        vPrev = vStr;
    }
    Vec_VecFree( (Vec_Vec_t *)vBuffers );

    if ( fVerbose )
    Abc_PrintTime( 1, "Sorting   time", clock() - clk );
//    Abc_PrintTime( 1, "Traversal time", time_Trav );

    // report the results
//    Vec_VecPrintInt( (Vec_Vec_t *)vClasses );
//    printf( "Devided %d outputs into %d cand equiv classes.\n", Gia_ManPoNum(pGia), Vec_PtrSize(vClasses) );
    if ( fVerbose )
    {
        Vec_PtrForEachEntry( Vec_Int_t *, vClasses, vLevel, i )
            if ( Vec_IntSize(vLevel) > 1 )
                printf( "%d ", Vec_IntSize(vLevel) );
            else
                nUnique++;
        printf( " Unique = %d\n", nUnique );
    }

    // collect the first ones
    vRemain = Vec_IntAlloc( 100 );
    Vec_PtrForEachEntry( Vec_Int_t *, vClasses, vLevel, i )
        Vec_IntPush( vRemain, Vec_IntEntry(vLevel, 0) );

    // derive the resulting AIG
    pTemp = Gia_ManDupCones( pGia, Vec_IntArray(vRemain), Vec_IntSize(vRemain) );
    Vec_IntFree( vRemain );

//    return (Vec_Vec_t *)vClasses;
    Vec_VecFree( (Vec_Vec_t *)vClasses );

//    printf( "The number of all checks %d.  Complex checks %d.\n", nPos*(nPos-1)/2, s_Counter );
    return pTemp;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

