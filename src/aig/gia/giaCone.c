/**CFile****************************************************************

  FileName    [giaCone.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCone.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Opa_Man_t_ Opa_Man_t;
struct Opa_Man_t_
{
    Gia_Man_t *    pGia;
    Vec_Int_t *    vFront;
    Vec_Int_t *    pvParts;
    int *          pId2Part; 
    int            nParts;
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
static inline Opa_Man_t * Opa_ManStart( Gia_Man_t * pGia)
{
    Opa_Man_t * p;
    Gia_Obj_t * pObj;
    int i;
    p = ABC_CALLOC( Opa_Man_t, 1 );
    p->pGia = pGia;
    p->pvParts  = ABC_CALLOC( Vec_Int_t, Gia_ManPoNum(pGia) );
    p->pId2Part = ABC_FALLOC( int, Gia_ManObjNum(pGia) );
    p->vFront   = Vec_IntAlloc( 100 );
    Gia_ManForEachPo( pGia, pObj, i )
    {
        Vec_IntPush( p->pvParts + i, Gia_ObjId(pGia, pObj) );
        p->pId2Part[Gia_ObjId(pGia, pObj)] = i;
        Vec_IntPush( p->vFront, Gia_ObjId(pGia, pObj) );
    }
    p->nParts = Gia_ManPoNum(pGia);
    return p;
}
static inline void Opa_ManStop( Opa_Man_t * p )
{
    int i;
    Vec_IntFree( p->vFront );
    for ( i = 0; i < Gia_ManPoNum(p->pGia); i++ )
        ABC_FREE( p->pvParts[i].pArray );
    ABC_FREE( p->pvParts );
    ABC_FREE( p->pId2Part );
    ABC_FREE( p );
}
static inline void Opa_ManPrint( Opa_Man_t * p )
{
    int i, k;
    printf( "Groups:\n" );
    for ( i = 0; i < Gia_ManPoNum(p->pGia); i++ )
    {
        if ( p->pvParts[i].nSize == 0 )
            continue;
        printf( "%3d : ", i );
        for ( k = 0; k < p->pvParts[i].nSize; k++ )
            printf( "%d ", p->pvParts[i].pArray[k] );
        printf( "\n" );
    }
}
static inline void Opa_ManPrint2( Opa_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, k, Count;
    printf( "Groups %d: ", p->nParts );
    for ( i = 0; i < Gia_ManPoNum(p->pGia); i++ )
    {
        if ( p->pvParts[i].nSize == 0 )
            continue;
        // count POs in this group
        Count = 0;
        Gia_ManForEachObjVec( p->pvParts + i, p->pGia, pObj, k )
            Count += Gia_ObjIsPo(p->pGia, pObj);
        printf( "%d ", Count );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Opa_ManMoveOne( Opa_Man_t * p, Gia_Obj_t * pObj, Gia_Obj_t * pFanin )
{
    int iObj   = Gia_ObjId(p->pGia, pObj);
    int iFanin = Gia_ObjId(p->pGia, pFanin);
    if ( iFanin == 0 )
        return;
    assert( p->pId2Part[ iObj ] >= 0 );
    if ( p->pId2Part[ iFanin ] == -1 )
    {
        p->pId2Part[ iFanin ] = p->pId2Part[ iObj ];
        Vec_IntPush( p->pvParts + p->pId2Part[ iObj ], iFanin );
        assert( Gia_ObjIsCi(pFanin) || Gia_ObjIsAnd(pFanin) );
        if ( Gia_ObjIsAnd(pFanin) )
            Vec_IntPush( p->vFront, iFanin );
        else if ( Gia_ObjIsRo(p->pGia, pFanin) )
        {
            pFanin = Gia_ObjRoToRi(p->pGia, pFanin);
            iFanin = Gia_ObjId(p->pGia, pFanin);
            assert( p->pId2Part[ iFanin ] == -1 );
            p->pId2Part[ iFanin ] = p->pId2Part[ iObj ];
            Vec_IntPush( p->pvParts + p->pId2Part[ iObj ], iFanin );
            Vec_IntPush( p->vFront, iFanin );
        }
    }
    else if ( p->pId2Part[ iObj ] != p->pId2Part[ iFanin ] )
    {
        Vec_Int_t * vPartObj = p->pvParts + p->pId2Part[ iObj ];
        Vec_Int_t * vPartFan = p->pvParts + p->pId2Part[ iFanin ];
        int iTemp, i;
//        printf( "Moving %d to %d (%d -> %d)\n", iObj, iFanin, Vec_IntSize(vPartObj), Vec_IntSize(vPartFan) );
        // add group of iObj to group of iFanin
        assert( Vec_IntSize(vPartObj) > 0 );
        Vec_IntForEachEntry( vPartObj, iTemp, i )
        {
            Vec_IntPush( vPartFan, iTemp );
            p->pId2Part[ iTemp ] = p->pId2Part[ iFanin ];
        }
        Vec_IntShrink( vPartObj, 0 );
        p->nParts--;
    }
}
void Opa_ManPerform( Gia_Man_t * pGia )
{
    Opa_Man_t * p;
    Gia_Obj_t * pObj;
    int i, Limit, Count = 0;
 
    p = Opa_ManStart( pGia );
    Limit = Vec_IntSize(p->vFront);
//Opa_ManPrint2( p );
    Gia_ManForEachObjVec( p->vFront, pGia, pObj, i )
    {
        if ( i == Limit )
        {
            printf( "%6d : %6d -> %6d\n", ++Count, i, p->nParts );
            Limit = Vec_IntSize(p->vFront);
            if ( Count > 1 )
                Opa_ManPrint2( p );
        }
//        printf( "*** Object %d  ", Gia_ObjId(pGia, pObj) );
        if ( Gia_ObjIsAnd(pObj) )
        {
            Opa_ManMoveOne( p, pObj, Gia_ObjFanin0(pObj) );
            Opa_ManMoveOne( p, pObj, Gia_ObjFanin1(pObj) );
        }
        else if ( Gia_ObjIsCo(pObj) )
            Opa_ManMoveOne( p, pObj, Gia_ObjFanin0(pObj) );
        else assert( 0 );
//        if ( i % 10 == 0 )
//            printf( "%d   ", p->nParts );
        if ( p->nParts == 1 )
            break;
        if ( Count == 5 )
            break;
    }
    printf( "\n" );
    Opa_ManStop( p );
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManConeMark_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vRoots, int nLimit )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 0;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsAnd(pObj) )
    {
        if ( Gia_ManConeMark_rec( p, Gia_ObjFanin0(pObj), vRoots, nLimit ) )
            return 1;
        if ( Gia_ManConeMark_rec( p, Gia_ObjFanin1(pObj), vRoots, nLimit ) )
            return 1;
    }
    else if ( Gia_ObjIsCo(pObj) )
    {
        if ( Gia_ManConeMark_rec( p, Gia_ObjFanin0(pObj), vRoots, nLimit ) )
            return 1;
    }
    else if ( Gia_ObjIsRo(p, pObj) )
        Vec_IntPush( vRoots, Gia_ObjId(p, Gia_ObjRoToRi(p, pObj)) );
    else if ( Gia_ObjIsPi(p, pObj) )
    {}
    else assert( 0 );
    return (int)(Vec_IntSize(vRoots) > nLimit);
}
int Gia_ManConeMark( Gia_Man_t * p, int iOut, int Limit )
{
    Vec_Int_t * vRoots;
    Gia_Obj_t * pObj;
    int i, RetValue;
    // start the outputs
    pObj = Gia_ManPo( p, iOut );
    vRoots = Vec_IntAlloc( 100 );
    Vec_IntPush( vRoots, Gia_ObjId(p, pObj) );
    // mark internal nodes
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    Gia_ManForEachObjVec( vRoots, p, pObj, i )
        if ( Gia_ManConeMark_rec( p, pObj, vRoots, Limit ) )
            break;
    RetValue = Vec_IntSize( vRoots ) - 1;
    Vec_IntFree( vRoots );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManConeExtract( Gia_Man_t * p, int iOut, int nDelta, int nOutsMin, int nOutsMax )
{
/*
    int i, Count = 0;
    // mark nodes belonging to output 'iOut'
    for ( i = 0; i < Gia_ManPoNum(p); i++ )
        Count += (Gia_ManConeMark(p, i, 10000) < 10000);
     //   printf( "%d ", Gia_ManConeMark(p, i, 1000) );
    printf( "%d out of %d\n", Count, Gia_ManPoNum(p) );

    // add other outputs as long as they are nDelta away
*/
    Opa_ManPerform( p );

    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

