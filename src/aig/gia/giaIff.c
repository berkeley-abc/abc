/**CFile****************************************************************

  FileName    [giaIff.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Hierarchical mapping of AIG with white boxes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaIff.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "map/if/if.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Iff_Man_t_ Iff_Man_t;
struct Iff_Man_t_
{
    Gia_Man_t *   pGia;          // mapped GIA
    If_LibLut_t * pLib;          // LUT library
    int           nLutSize;      // LUT size
    int           nDegree;       // degree 
    Vec_Flt_t *   vTimes;        // arrival times
    Vec_Int_t *   vMatch[4];     // matches
};

static inline float Iff_ObjTimeId( Iff_Man_t * p, int iObj, int Type )                      { return Vec_FltEntry( p->vTimes, iObj );                      }
static inline float Iff_ObjTime( Iff_Man_t * p, Gia_Obj_t * pObj, int Type )                { return Iff_ObjTimeId( p, Gia_ObjId(p->pGia, pObj), Type );   }
static inline void  Iff_ObjSetTimeId( Iff_Man_t * p, int iObj, int Type, float Time )       { Vec_FltWriteEntry( p->vTimes, iObj, Time );                  }
static inline void  Iff_ObjSetTime( Iff_Man_t * p, Gia_Obj_t * pObj, int Type, float Time ) { Iff_ObjSetTimeId( p, Gia_ObjId(p->pGia, pObj), Type, Time ); }

static inline int   Iff_ObjMatchId( Iff_Man_t * p, int iObj, int Type )                     { return Vec_IntEntry( p->vMatch[Type], iObj );                }
static inline int   Iff_ObjMatch( Iff_Man_t * p, Gia_Obj_t * pObj, int Type )               { return Iff_ObjTimeId( p, Gia_ObjId(p->pGia, pObj), Type );   }
static inline void  Iff_ObjSetMatchId( Iff_Man_t * p, int iObj, int Type, int Match )       { Vec_IntWriteEntry( p->vMatch[Type], iObj, Match );           }
static inline void  Iff_ObjSetMatch( Iff_Man_t * p, Gia_Obj_t * pObj, int Type, int Match ) { Iff_ObjSetTimeId( p, Gia_ObjId(p->pGia, pObj), Type, Match );}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Iff_Man_t * Gia_ManIffStart( Gia_Man_t * pGia )
{
    Iff_Man_t * p = ABC_CALLOC( Iff_Man_t, 1 );
    p->vTimes    = Vec_FltStartFull( Gia_ManObjNum(pGia) );
    p->vMatch[2] = Vec_IntStartFull( Gia_ManObjNum(pGia) );
    p->vMatch[3] = Vec_IntStartFull( Gia_ManObjNum(pGia) );
    return p;
}
void Gia_ManIffStop( Iff_Man_t * p )
{
    Vec_FltFree( p->vTimes );
    Vec_IntFree( p->vMatch[2] );
    Vec_IntFree( p->vMatch[3] );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Gia_IffObjTimeBest( Iff_Man_t * p, int iObj )
{
    return Abc_MinFloat( Iff_ObjTimeId(p, iObj, 1), Iff_ObjTimeId(p, iObj, 2) );
}

/**Function*************************************************************

  Synopsis    [Count the number of unique fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_IffObjCount( Gia_Man_t * pGia, int iObj, int iFaninSkip, int iFaninSkip2 )
{
    int i, iFanin, Count = 0;
    Gia_ManIncrementTravId( pGia );
    Gia_LutForEachFanin( pGia, iObj, iFanin, i )
    {
        if ( iFanin == iFaninSkip || iFanin == iFaninSkip2 )
            continue;
        if ( Gia_ObjIsTravIdCurrentId( pGia, iFanin ) )
            continue;
        Gia_ObjSetTravIdCurrentId( pGia, iFanin );
        Count++;
    }
    if ( iFaninSkip >= 0 )
    {
        Gia_LutForEachFanin( pGia, iFaninSkip, iFanin, i )
        {
            if ( iFanin == iFaninSkip2 )
                continue;
            if ( Gia_ObjIsTravIdCurrentId( pGia, iFanin ) )
                continue;
            Gia_ObjSetTravIdCurrentId( pGia, iFanin );
            Count++;
        }
    }
    if ( iFaninSkip2 >= 0 )
    {
        Gia_LutForEachFanin( pGia, iFaninSkip2, iFanin, i )
        {
            if ( Gia_ObjIsTravIdCurrentId( pGia, iFanin ) )
                continue;
            Gia_ObjSetTravIdCurrentId( pGia, iFanin );
            Count++;
        }
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Gia_IffObjTimeOne( Iff_Man_t * p, int iObj, int iFaninSkip, int iFaninSkip2 )
{
    int i, iFanin;
    float Best = -ABC_INFINITY;
    Gia_LutForEachFanin( p->pGia, iObj, iFanin, i )
        if ( iFanin != iFaninSkip && iFanin != iFaninSkip2 && Best < Iff_ObjTimeId(p, iFanin, 1) )
            Best = Iff_ObjTimeId(p, iFanin, 1);
    assert( i == Gia_ObjLutSize(p->pGia, iObj) );
    if ( iFaninSkip == -1 )
        return Best + p->pLib->pLutDelays[i][0];
    Gia_LutForEachFanin( p->pGia, iFaninSkip, iFanin, i )
        if ( Best < Iff_ObjTimeId(p, iFanin, 1) )
            Best = Iff_ObjTimeId(p, iFanin, 1);
    if ( iFaninSkip2 == -1 )
        return Best;
    Gia_LutForEachFanin( p->pGia, iFaninSkip2, iFanin, i )
        if ( Best < Iff_ObjTimeId(p, iFanin, 1) )
            Best = Iff_ObjTimeId(p, iFanin, 1);
    assert( Best >= 0 );
    return Best;
}
float Gia_IffObjTimeTwo( Iff_Man_t * p, int iObj, int * piFanin )
{
    int i, iFanin, nSize;
    float This, Best = -ABC_INFINITY;
    *piFanin = -1;
    Gia_LutForEachFanin( p->pGia, iObj, iFanin, i )
    {
        This = Gia_IffObjTimeOne( p, iObj, iFanin, -1 );
        nSize = Abc_MinInt( Gia_ObjLutSize(p->pGia, iObj) + Gia_ObjLutSize(p->pGia, iFanin) - 1, p->pLib->LutMax );
        This += p->pLib->pLutDelays[nSize][0];
        if ( Best < This )
        {
            Best = This;
            *piFanin = iFanin;
        }
    }
    return Best;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Iff_Man_t * Gia_ManIffPerform( Gia_Man_t * pGia, If_LibLut_t * pLib, Tim_Man_t * pTime, int nLutSize, int nDegree )
{
    Iff_Man_t * p;
    Gia_Obj_t * pObj;
    float arrTime1, arrTime2; 
    int iObj, iFanin;
    assert( nDegree == 2 );//|| nDegree == 3 );
    // start the mapping manager and set its parameters
    p = Gia_ManIffStart( pGia );
    p->pGia     = pGia;
    p->pLib     = pLib;
    p->nLutSize = nLutSize;
    p->nDegree  = nDegree;
    // compute arrival times of each node
    Iff_ObjSetTimeId( p, 0, 1, 0 );
    Iff_ObjSetTimeId( p, 0, 2, 0 );
    Iff_ObjSetTimeId( p, 0, 3, 0 );
    Tim_ManIncrementTravId( pTime );
    Gia_ManForEachObj1( pGia, pObj, iObj )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            if ( !Gia_ObjIsLut(pGia, iObj) )
                continue;
            // compute arrival times of LUT inputs
            arrTime1 = Gia_IffObjTimeOne( p, iObj, -1, -1 );
            // compute arrival times of LUT pairs
            arrTime2 = Gia_IffObjTimeTwo( p, iObj, &iFanin );
            // check arrival times
            Iff_ObjSetTimeId( p, iObj, 1, arrTime2 );
            if ( arrTime2 < arrTime1 )
                Iff_ObjSetMatchId( p, iObj, 2, iFanin );
            // compute arrival times of LUT triples
        }
        else if ( Gia_ObjIsCi(pObj) )
        {
            arrTime1 = Tim_ManGetCiArrival( pTime, Gia_ObjCioId(pObj) );
            Iff_ObjSetTime( p, pObj, 1, arrTime1 );
            Iff_ObjSetTime( p, pObj, 2, arrTime1 );
            Iff_ObjSetTime( p, pObj, 3, arrTime1 );
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            arrTime1 = Gia_IffObjTimeBest( p, Gia_ObjFaninId0p(pGia, pObj) );
            Tim_ManSetCoArrival( pTime, Gia_ObjCioId(pObj), arrTime1 );
            Iff_ObjSetTime( p, pObj, 1, arrTime1 );
            Iff_ObjSetTime( p, pObj, 2, arrTime1 );
            Iff_ObjSetTime( p, pObj, 3, arrTime1 );
        }
        else assert( 0 );
    }
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     [] 

***********************************************************************/
void Gia_ManIffSelect_rec( Iff_Man_t * p, int iObj, Vec_Int_t * vPacking )
{
    int i, iFanin, iFaninSkip;
    if ( Gia_ObjIsTravIdCurrentId( p->pGia, iObj ) )
        return;
    Gia_ObjSetTravIdCurrentId( p->pGia, iObj );
    assert( Gia_ObjIsLut(p->pGia, iObj) );
    iFaninSkip = Iff_ObjMatchId(p, iObj, 2);
    if ( iFaninSkip == -1 )
    {
        Gia_LutForEachFanin( p->pGia, iObj, iFanin, i )
            Gia_ManIffSelect_rec( p, iFanin, vPacking );
        Vec_IntPush( vPacking, 1 );
        Vec_IntPush( vPacking, iObj );
    }
    else
    {
        Gia_LutForEachFanin( p->pGia, iFaninSkip, iFanin, i )
                Gia_ManIffSelect_rec( p, iFanin, vPacking );
        Gia_LutForEachFanin( p->pGia, iObj, iFanin, i )
            if ( iFanin != iFaninSkip )
                Gia_ManIffSelect_rec( p, iFanin, vPacking );
        Vec_IntPush( vPacking, 2 );
        Vec_IntPush( vPacking, iFaninSkip );
        Vec_IntPush( vPacking, iObj );
    }
    Vec_IntAddToEntry( vPacking, 0, 1 );
}
Vec_Int_t * Gia_ManIffSelect( Iff_Man_t * p )
{
    Vec_Int_t * vPacking;
    Gia_Obj_t * pObj; int i;
    vPacking = Vec_IntAlloc( Gia_ManObjNum(p->pGia) );
    Vec_IntPush( vPacking, 0 );
    // mark const0 and PIs
    Gia_ManIncrementTravId( p->pGia );
    Gia_ObjSetTravIdCurrent( p->pGia, Gia_ManConst0(p->pGia) );
    Gia_ManForEachCi( p->pGia, pObj, i )
        Gia_ObjSetTravIdCurrent( p->pGia, pObj );
    // recursively collect internal nodes
    Gia_ManForEachCo( p->pGia, pObj, i )
        Gia_ManIffSelect_rec( p, Gia_ObjFaninId0p(p->pGia, pObj), vPacking );
    return vPacking;
}

/**Function*************************************************************

  Synopsis    [This command performs hierarhical mapping.]

  Description []
               
  SideEffects []

  SeeAlso     [] 

***********************************************************************/
void Gia_ManIffTest( Gia_Man_t * pGia, If_LibLut_t * pLib, int fVerbose )
{
    Iff_Man_t * p;
    int nDegree = -1;
    int nLutSize = Gia_ManLutSizeMax( pGia );
    if ( nLutSize <= 4 )
    {
        nLutSize = 4;
        if ( pLib->LutMax <= 7 )
            nDegree = 2;
        else if ( pLib->LutMax <= 10 )
            nDegree = 3;
        else
            { printf( "Degree is more than 3.\n" ); return; }
    }
    else if ( nLutSize <= 6 )
    {
        nLutSize = 6;
        if ( pLib->LutMax <= 11 )
            nDegree = 2;
        else if ( pLib->LutMax <= 16 )
            nDegree = 3;
        else
            { printf( "Degree is more than 3.\n" ); return; }
    }
    else
    {
        printf( "The LUT size is more than 6.\n" );
        return;
    }
    if ( fVerbose )
        printf( "Performing %d-clustering with %d-LUTs:\n", nDegree, nLutSize );
    // create timing manager
    if ( pGia->pManTime == NULL )
        pGia->pManTime = Tim_ManStart( Gia_ManCiNum(pGia), Gia_ManCoNum(pGia) );
    // perform timing computation
    p = Gia_ManIffPerform( pGia, pLib, pGia->pManTime, nLutSize, nDegree );
    // derive clustering
    Vec_IntFreeP( &pGia->vPacking );
    pGia->vPacking = Gia_ManIffSelect( p );
    Gia_ManIffStop( p );
    // print statistics
    if ( fVerbose )
        Gia_ManPrintPackingStats( pGia );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

