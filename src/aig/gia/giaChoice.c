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
#include "misc/tim/tim.h"

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
        Vec_IntPush( vCollected, iRepr );
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
            else
                assert( iRepr > iNode );
            Vec_IntPush( vClass, iNode );
        }
//        if ( !fNowIncreasing )
//            Vec_IntSort( vClass, 1 );
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
//    if ( !fProb )
//        printf( "GIA with choices is correct.\n" );
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

  Synopsis    [Returns 1 if AIG has choices.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManHasChoices( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, Counter1 = 0, Counter2 = 0;
    int nFailNoRepr = 0;
    int nFailHaveRepr = 0;
    int nChoiceNodes = 0;
    int nChoices = 0;
    if ( p->pReprs == NULL || p->pNexts == NULL )
        return 0;
    // check if there are any representatives
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( Gia_ObjReprObj( p, Gia_ObjId(p, pObj) ) )
        {
//            printf( "%d ", i );
            Counter1++;
        }
//        if ( Gia_ObjNext( p, Gia_ObjId(p, pObj) ) )
//            Counter2++;
    }
//    printf( "\n" );
    Gia_ManForEachObj( p, pObj, i )
    {
//        if ( Gia_ObjReprObj( p, Gia_ObjId(p, pObj) ) )
//            Counter1++;
        if ( Gia_ObjNext( p, Gia_ObjId(p, pObj) ) )
        {
//            printf( "%d ", i );
            Counter2++;
        }
    }
//    printf( "\n" );
    if ( Counter1 == 0 )
    {
        printf( "Warning: AIG has repr data-strucure but not reprs.\n" );
        return 0;
    }
    printf( "%d nodes have reprs.\n", Counter1 );
    printf( "%d nodes have nexts.\n", Counter2 );
    // check if there are any internal nodes without fanout
    // make sure all nodes without fanout have representatives
    // make sure all nodes with fanout have no representatives
    ABC_FREE( p->pRefs );
    Gia_ManCreateRefs( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( Gia_ObjRefNum(p, pObj) == 0 )
        {
            if ( Gia_ObjReprObj( p, Gia_ObjId(p, pObj) ) == NULL )
                nFailNoRepr++;
            else
                nChoices++;
        }
        else
        {
            if ( Gia_ObjReprObj( p, Gia_ObjId(p, pObj) ) != NULL )
                nFailHaveRepr++;
            if ( Gia_ObjNextObj( p, Gia_ObjId(p, pObj) ) != NULL )
                nChoiceNodes++;
        }
        if ( Gia_ObjReprObj( p, i ) )
            assert( Gia_ObjRepr(p, i) < i );
    }
    if ( nChoices == 0 )
        return 0;
    if ( nFailNoRepr )
    {
        printf( "Gia_ManHasChoices(): Error: %d internal nodes have no fanout and no repr.\n", nFailNoRepr );
//        return 0;
    }
    if ( nFailHaveRepr )
    {
        printf( "Gia_ManHasChoices(): Error: %d internal nodes have both fanout and repr.\n", nFailHaveRepr );
//        return 0;
    }
//    printf( "Gia_ManHasChoices(): AIG has %d choice nodes with %d choices.\n", nChoiceNodes, nChoices );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Computes levels for AIG with choices and white boxes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManChoiceLevel_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Tim_Man_t * pManTime = (Tim_Man_t *)p->pManTime;
    Gia_Obj_t * pNext;
    int i, iBox, iTerm1, nTerms, LevelMax = 0;
    if ( Gia_ObjIsTravIdCurrent( p, pObj ) )
        return;
    Gia_ObjSetTravIdCurrent( p, pObj );
    if ( Gia_ObjIsCi(pObj) )
    {
        if ( pManTime )
        {
            iBox = Tim_ManBoxForCi( pManTime, Gia_ObjCioId(pObj) );
            if ( iBox >= 0 ) // this is not a true PI
            {
                iTerm1 = Tim_ManBoxInputFirst( pManTime, iBox );
                nTerms = Tim_ManBoxInputNum( pManTime, iBox );
                for ( i = 0; i < nTerms; i++ )
                {
                    pNext = Gia_ManCo( p, iTerm1 + i );
                    Gia_ManChoiceLevel_rec( p, pNext );
                    if ( LevelMax < Gia_ObjLevel(p, pNext) )
                        LevelMax = Gia_ObjLevel(p, pNext);
                }
                LevelMax++;
            }
        }
//        Abc_Print( 1, "%d ", pObj->Level );
    }
    else if ( Gia_ObjIsCo(pObj) )
    {
        pNext = Gia_ObjFanin0(pObj);
        Gia_ManChoiceLevel_rec( p, pNext );
        if ( LevelMax < Gia_ObjLevel(p, pNext) )
            LevelMax = Gia_ObjLevel(p, pNext);
    }
    else if ( Gia_ObjIsAnd(pObj) )
    { 
        // get the maximum level of the two fanins
        pNext = Gia_ObjFanin0(pObj);
        Gia_ManChoiceLevel_rec( p, pNext );
        if ( LevelMax < Gia_ObjLevel(p, pNext) )
            LevelMax = Gia_ObjLevel(p, pNext);
        pNext = Gia_ObjFanin1(pObj);
        Gia_ManChoiceLevel_rec( p, pNext );
        if ( LevelMax < Gia_ObjLevel(p, pNext) )
            LevelMax = Gia_ObjLevel(p, pNext);
        LevelMax++;

        // get the level of the nodes in the choice node
        if ( p->pSibls && (pNext = Gia_ObjSiblObj(p, Gia_ObjId(p, pObj))) )
        {
            Gia_ManChoiceLevel_rec( p, pNext );
            if ( LevelMax < Gia_ObjLevel(p, pNext) )
                LevelMax = Gia_ObjLevel(p, pNext);
        }
    }
    else if ( !Gia_ObjIsConst0(pObj) )
        assert( 0 );
    Gia_ObjSetLevel( p, pObj, LevelMax );
}
int Gia_ManChoiceLevel( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, LevelMax = 0;
//    assert( Gia_ManRegNum(p) == 0 );
    Gia_ManCleanLevels( p, Gia_ManObjNum(p) );
    Gia_ManIncrementTravId( p );
    Gia_ManForEachCo( p, pObj, i )
    {
        Gia_ManChoiceLevel_rec( p, pObj );
        if ( LevelMax < Gia_ObjLevel(p, pObj) )
            LevelMax = Gia_ObjLevel(p, pObj);
    }
    // account for dangling boxes
    Gia_ManForEachCi( p, pObj, i )
    {
        Gia_ManChoiceLevel_rec( p, pObj );
        if ( LevelMax < Gia_ObjLevel(p, pObj) )
            LevelMax = Gia_ObjLevel(p, pObj);
//        Abc_Print( 1, "%d ", Gia_ObjLevel(p, pObj) );
    }
//    Abc_Print( 1, "\n" );
    Gia_ManForEachAnd( p, pObj, i )
        assert( Gia_ObjLevel(p, pObj) > 0 );
//    printf( "Max level %d\n", LevelMax );
    return LevelMax;
} 


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

