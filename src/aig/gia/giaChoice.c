/**CFile****************************************************************

  FileName    [giaChoice.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Normalization of structural choices.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaChoice.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "giaAig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reverse the order of nodes in equiv classes.]

  Description [If the flag is 1, assumed current increasing order ]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManReverseClasses( Gia_Man_t * p, int fNowIncreasing )
{
    Vec_Int_t * vCollected;
    Vec_Int_t * vClass;
    int i, k, iRepr, iNode, iPrev;
    // collect classes
    vCollected = Vec_IntAlloc( 100 );
    Gia_ManForEachClass( p, iRepr )
    {
        Vec_IntPush( vCollected, iRepr );
/*
        // check classes
        if ( !fNowIncreasing )
        {
            iPrev = iRepr;
            Gia_ClassForEachObj1( p, iRepr, iNode )
            {
                if ( iPrev < iNode )
                {
                    printf( "Class %d : ", iRepr );
                    Gia_ClassForEachObj( p, iRepr, iNode )
                        printf( " %d", iNode );
                    printf( "\n" );
                    break;
                }
                iPrev = iNode;
            }
        }
*/
    }
    // correct each class
    vClass = Vec_IntAlloc( 100 );
    Vec_IntForEachEntry( vCollected, iRepr, i )
    {
        Vec_IntClear( vClass );
        Vec_IntPush( vClass, iRepr );
        Gia_ClassForEachObj1( p, iRepr, iNode )
        {
            if ( fNowIncreasing )
                assert( iRepr < iNode );
//            else
//                assert( iRepr > iNode );
            Vec_IntPush( vClass, iNode );
        }
        if ( !fNowIncreasing )
            Vec_IntSort( vClass, 1 );
//        if ( iRepr == 129720 || iRepr == 129737 )
//            Vec_IntPrint( vClass );
        // reverse the class
        iPrev = 0;
        iRepr = Vec_IntEntryLast( vClass );
        Vec_IntForEachEntry( vClass, iNode, k )
        {
            if ( fNowIncreasing )
                Gia_ObjSetReprRev( p, iNode, iNode == iRepr ? GIA_VOID : iRepr );
            else
                Gia_ObjSetRepr( p, iNode, iNode == iRepr ? GIA_VOID : iRepr );
            Gia_ObjSetNext( p, iNode, iPrev );
            iPrev = iNode;
        }
    }
    Vec_IntFree( vCollected );
    Vec_IntFree( vClass );
    // verify
    Gia_ManForEachClass( p, iRepr )
        Gia_ClassForEachObj1( p, iRepr, iNode )
            if ( fNowIncreasing )
                assert( Gia_ObjRepr(p, iNode) == iRepr && iRepr > iNode );
            else
                assert( Gia_ObjRepr(p, iNode) == iRepr && iRepr < iNode );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManVerifyChoices( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, iRepr, iNode, fProb = 0;
    assert( p->pReprs );

    // mark nodes 
    Gia_ManCleanMark0(p);
    Gia_ManForEachClass( p, iRepr )
        Gia_ClassForEachObj1( p, iRepr, iNode )
        {
            if ( Gia_ObjIsHead(p, iNode) )
                printf( "Member %d of choice class %d is a representative.\n", iNode, iRepr ), fProb = 1;
            if ( Gia_ManObj( p, iNode )->fMark0 == 1 )
                printf( "Node %d participates in more than one choice node.\n", iNode ), fProb = 1;
            Gia_ManObj( p, iNode )->fMark0 = 1;
        }
    Gia_ManCleanMark0(p);

    Gia_ManForEachObj( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            if ( Gia_ObjHasRepr(p, Gia_ObjFaninId0(pObj, i)) )
                printf( "Fanin 0 of AND node %d has a repr.\n", i ), fProb = 1;
            if ( Gia_ObjHasRepr(p, Gia_ObjFaninId1(pObj, i)) )
                printf( "Fanin 1 of AND node %d has a repr.\n", i ), fProb = 1;
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            if ( Gia_ObjHasRepr(p, Gia_ObjFaninId0(pObj, i)) )
                printf( "Fanin 0 of CO node %d has a repr.\n", i ), fProb = 1;
        }
    }
    if ( !fProb )
        printf( "GIA with choices is correct.\n" );
}

/**Function*************************************************************

  Synopsis    [Make sure reprsentative nodes do not have representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCheckReprs( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, fProb = 0;
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( !Gia_ObjHasRepr(p, i) )
            continue;
        if ( !Gia_ObjIsAnd(pObj) )
            printf( "Obj %d is not an AND but it has a repr %d.\n", i, Gia_ObjRepr(p, i) ), fProb = 1;
        else if ( Gia_ObjHasRepr( p, Gia_ObjRepr(p, i) ) )
            printf( "Obj %d has repr %d with a repr %d.\n", i, Gia_ObjRepr(p, i), Gia_ObjRepr(p, Gia_ObjRepr(p, i)) ), fProb = 1;
    }
    if ( !fProb )
        printf( "GIA \"%s\": Representive verification successful.\n", Gia_ManName(p) );
}

/**Function*************************************************************

  Synopsis    [Find minimum level of each node using representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManMinLevelRepr_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    int levMin, levCur, objId, reprId;
    // skip visited nodes
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return Gia_ObjLevel(p, pObj);
    Gia_ObjSetTravIdCurrent(p, pObj);
    // skip CI nodes
    if ( Gia_ObjIsCi(pObj) )
        return Gia_ObjLevel(p, pObj);
    assert( Gia_ObjIsAnd(pObj) );
    objId = Gia_ObjId(p, pObj);
    if ( Gia_ObjIsNone(p, objId) )
    {
        // not part of the equivalence class
        Gia_ManMinLevelRepr_rec( p, Gia_ObjFanin0(pObj) );
        Gia_ManMinLevelRepr_rec( p, Gia_ObjFanin1(pObj) );
        Gia_ObjSetAndLevel( p, pObj );
        return Gia_ObjLevel(p, pObj);
    }
    // has equivalences defined
    assert( Gia_ObjHasRepr(p, objId) || Gia_ObjIsHead(p, objId) );
    reprId = Gia_ObjHasRepr(p, objId) ? Gia_ObjRepr(p, objId) : objId;
    // iterate through objects
    levMin = ABC_INFINITY;
    Gia_ClassForEachObj( p, reprId, objId )
    {
        levCur = Gia_ManMinLevelRepr_rec( p, Gia_ManObj(p, objId) );
        levMin = Abc_MinInt( levMin, levCur );
    }
    assert( levMin < ABC_INFINITY );
    // assign minimum level to all
    Gia_ClassForEachObj( p, reprId, objId )
        Gia_ObjSetLevelId( p, objId, levMin );
    return levMin;
}
int Gia_ManMinLevelRepr( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, LevelCur, LevelMax = 0;
    assert( Gia_ManRegNum(p) == 0 );
    Gia_ManCleanLevels( p, Gia_ManObjNum(p) );
    Gia_ManIncrementTravId( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        assert( !Gia_ObjIsConst(p, i) );
        LevelCur = Gia_ManMinLevelRepr_rec( p, pObj );
        LevelMax = Abc_MaxInt( LevelMax, LevelCur );
    }
    printf( "Max level %d\n", LevelMax );
    return LevelMax;
} 

/**Function*************************************************************

  Synopsis    [Returns mapping of each old repr into new repr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Gia_ManFindMinLevelMap( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int reprId, objId, levFan0, levFan1;
    int levMin, levMinOld, levMax, reprBest;
    int * pReprMap, * pMinLevels, iFanin;
    int i, fChange = 1;

    Gia_ManLevelNum( p );
    pMinLevels = ABC_ALLOC( int, Gia_ManObjNum(p) );
    while ( fChange )
    {
        fChange = 0;
        // clean min-levels
        memset( pMinLevels, 0xFF, sizeof(int) * Gia_ManObjNum(p) );        
        // for each class find min level
        Gia_ManForEachClass( p, reprId )
        {
            levMin = ABC_INFINITY;
            Gia_ClassForEachObj( p, reprId, objId )
                levMin = Abc_MinInt( levMin, Gia_ObjLevelId(p, objId) );
            assert( levMin >= 0 && levMin < ABC_INFINITY );
            Gia_ClassForEachObj( p, reprId, objId )
            {
                assert( pMinLevels[objId] == -1 );
                pMinLevels[objId] = levMin;
            }
        }
        // recompute levels
        levMax = 0;
        Gia_ManForEachAnd( p, pObj, i )
        {
            iFanin = Gia_ObjFaninId0(pObj, i);
            if ( Gia_ObjIsNone(p, iFanin) )
                levFan0 = Gia_ObjLevelId(p, iFanin);
            else if ( Gia_ObjIsConst(p, iFanin) )
                levFan0 = 0;
            else
            {
                assert( Gia_ObjIsClass( p, iFanin ) );
                assert( pMinLevels[iFanin] >= 0 );
                levFan0 = pMinLevels[iFanin];
            }

            iFanin = Gia_ObjFaninId1(pObj, i);
            if ( Gia_ObjIsNone(p, iFanin) )
                levFan1 = Gia_ObjLevelId(p, iFanin);
            else if ( Gia_ObjIsConst(p, iFanin) )
                levFan1 = 0;
            else
            {
                assert( Gia_ObjIsClass( p, iFanin ) );
                assert( pMinLevels[iFanin] >= 0 );
                levFan1 = pMinLevels[iFanin];
            }
            levMinOld = Gia_ObjLevelId(p, i);
            levMin = 1 + Abc_MaxInt( levFan0, levFan1 );
            Gia_ObjSetLevelId( p, i, levMin );
            assert( levMin <= levMinOld );
            if ( levMin < levMinOld )
                fChange = 1;
            levMax = Abc_MaxInt( levMax, levMin );
        }
        printf( "%d ", levMax );
    }
    ABC_FREE( pMinLevels );
    printf( "\n" );

    // create repr map
    pReprMap = ABC_FALLOC( int, Gia_ManObjNum(p) );
    Gia_ManForEachAnd( p, pObj, i )
        if ( Gia_ObjIsConst(p, i) )
            pReprMap[i] = 0;
    Gia_ManForEachClass( p, reprId )
    {
        // find min-level repr
        reprBest = -1;
        levMin = ABC_INFINITY;
        Gia_ClassForEachObj( p, reprId, objId )
            if ( levMin > Gia_ObjLevelId(p, objId) )
            {
                levMin = Gia_ObjLevelId(p, objId);
                reprBest = objId;
            }
        assert( reprBest > 0 );
        Gia_ClassForEachObj( p, reprId, objId )
            pReprMap[objId] = reprBest;
    }
    return pReprMap;
}



/**Function*************************************************************

  Synopsis    [Find terminal AND nodes]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManDanglingAndNodes( Gia_Man_t * p )
{
    Vec_Int_t * vTerms;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManCleanMark0( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        Gia_ObjFanin0(pObj)->fMark0 = 1;
        Gia_ObjFanin1(pObj)->fMark1 = 1;
    }
    vTerms = Vec_IntAlloc( 1000 );
    Gia_ManForEachAnd( p, pObj, i )
        if ( !pObj->fMark0 )
            Vec_IntPush( vTerms, i );
    Gia_ManCleanMark0( p );
    return vTerms;
}

/**Function*************************************************************

  Synopsis    [Reconstruct AIG starting with terminals.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManRebuidRepr_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int * pReprMap )
{
    int objId, reprLit = -1;
    if ( ~pObj->Value )
        return pObj->Value;
    assert( Gia_ObjIsAnd(pObj) );
    objId = Gia_ObjId( p, pObj );
    if ( Gia_ObjIsClass(p, objId) )
    {
        assert( pReprMap[objId] > 0 );
        reprLit = Gia_ManRebuidRepr_rec( pNew, p, Gia_ManObj(p, pReprMap[objId]), pReprMap );
        assert( reprLit > 1 );
    }
    else
        assert( Gia_ObjIsNone(p, objId) );
    Gia_ManRebuidRepr_rec( pNew, p, Gia_ObjFanin0(pObj), pReprMap );
    Gia_ManRebuidRepr_rec( pNew, p, Gia_ObjFanin1(pObj), pReprMap );
    pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    assert( reprLit != (int)pObj->Value );
    if ( reprLit > 1 )
        pNew->pReprs[ Abc_Lit2Var(pObj->Value) ].iRepr = Abc_Lit2Var(reprLit);
    return pObj->Value;
}
Gia_Man_t * Gia_ManRebuidRepr( Gia_Man_t * p, int * pReprMap )
{
    Vec_Int_t * vTerms;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    vTerms = Gia_ManDanglingAndNodes( p );
    Gia_ManForEachObjVec( vTerms, p, pObj, i )
        Gia_ManRebuidRepr_rec( pNew, p, pObj, pReprMap );
    Vec_IntFree( vTerms );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Gia_ManNormalizeChoices( Aig_Man_t * pAig )
{
    int * pReprMap;
    Aig_Man_t * pNew;
    Gia_Man_t * pGia, * pTemp;
    // create GIA with representatives
    assert( Aig_ManRegNum(pAig) == 0 );
    assert( pAig->pReprs != NULL );
    pGia = Gia_ManFromAigSimple( pAig );
    Gia_ManReprFromAigRepr2( pAig, pGia );
    // verify that representatives are correct
    Gia_ManCheckReprs( pGia );
    // find min-level repr for each class
    pReprMap = Gia_ManFindMinLevelMap( pGia );
    // reconstruct using correct order
    pGia = Gia_ManRebuidRepr( pTemp = pGia, pReprMap );
    Gia_ManStop( pTemp );
    ABC_FREE( pReprMap );
    // create choices

    // verify that choices are correct
//    Gia_ManVerifyChoices( pGia );
    // copy the result back into AIG
    pNew = Gia_ManToAigSimple( pGia );
    Gia_ManReprToAigRepr( pNew, pGia );
    return pNew;
}
void Gia_ManNormalizeChoicesTest( Aig_Man_t * pAig )
{
    Aig_Man_t * pNew = Gia_ManNormalizeChoices( pAig );
    Aig_ManStop( pNew );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

