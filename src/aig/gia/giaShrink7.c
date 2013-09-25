/**CFile****************************************************************

  FileName    [giaShrink7.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Implementation of DAG-aware unmapping for 6-input cuts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaShrink6.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/vec/vecHsh4.h"
#include "misc/util/utilTruth.h"


ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// operation manager
typedef struct Unm_Man_t_ Unm_Man_t;
struct Unm_Man_t_
{
    Gia_Man_t *        pGia;           // user's AIG
    Gia_Man_t *        pNew;           // constructed AIG
    Hsh_Int4Man_t *    pHash;          // hash table
    int                nNewSize;       // expected size of new manager
    Vec_Wrd_t *        vTruths;        // truth tables
    Vec_Int_t *        vLeaves;        // temporary storage for leaves
    abctime            clkStart;       // starting the clock
};

extern word Shr_ManComputeTruth6( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vLeaves, Vec_Wrd_t * vTruths );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Unm_Man_t * Unm_ManAlloc( Gia_Man_t * pGia )
{
    Unm_Man_t * p;
    p = ABC_CALLOC( Unm_Man_t, 1 );
    p->clkStart    = Abc_Clock();
    p->nNewSize    = 3 * Gia_ManObjNum(pGia) / 2;
    p->pGia        = pGia;
    p->pNew        = Gia_ManStart( p->nNewSize );
    p->pNew->pName = Abc_UtilStrsav( pGia->pName );
    p->pNew->pSpec = Abc_UtilStrsav( pGia->pSpec );
    Gia_ManHashAlloc( p->pNew );
    Gia_ManCleanLevels( p->pNew, p->nNewSize );
    // allocate traversal IDs
    p->pNew->nObjs = p->nNewSize;
    Gia_ManIncrementTravId( p->pNew );
    p->pNew->nObjs = 1;
    // start hashing
    p->pHash = Hsh_Int4ManStart( 1000 );
    // truth tables
    p->vTruths = Vec_WrdStart( Gia_ManObjNum(pGia) );
    p->vLeaves = Vec_IntStart( 10 );
    return p;
}
Gia_Man_t * Unm_ManFree( Unm_Man_t * p )
{
    Gia_Man_t * pTemp = p->pNew; p->pNew = NULL;
    Gia_ManHashStop( pTemp );
    Vec_IntFreeP( &pTemp->vLevels );
    Gia_ManSetRegNum( pTemp, Gia_ManRegNum(p->pGia) );
    // truth tables
    Vec_WrdFreeP( &p->vTruths );
    Vec_IntFreeP( &p->vLeaves );
    // free data structures
    Hsh_Int4ManStop( p->pHash );
    ABC_FREE( p );

    Gia_ManStop( pTemp );
    pTemp = NULL;

    return pTemp;
}

/**Function*************************************************************

  Synopsis    [Computes truth tables for all LUTs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Unm_ManComputeTruths( Unm_Man_t * p )
{
    Vec_Wrd_t * vTruths2;
    Gia_Obj_t * pObj;
    int i, k, iNode;
    word uTruth;
    vTruths2 = Vec_WrdStart( Gia_ManObjNum(p->pGia) );
    Gia_ManForEachLut( p->pGia, i )
    {
        pObj = Gia_ManObj( p->pGia, i );
        // collect leaves of this gate  
        Vec_IntClear( p->vLeaves );
        Gia_LutForEachFanin( p->pGia, i, iNode, k )
            Vec_IntPush( p->vLeaves, iNode );
        assert( Vec_IntSize(p->vLeaves) <= 6 );
        // compute truth table 
        uTruth = Shr_ManComputeTruth6( p->pGia, pObj, p->vLeaves, vTruths2 );
        Vec_WrdWriteEntry( p->vTruths, i, uTruth );
//        if ( i % 100 == 0 )
//            Kit_DsdPrintFromTruth( (unsigned *)&uTruth, 6 ), printf( "\n" );
    }
    Vec_WrdFreeP( &vTruths2 );
}

/**Function*************************************************************

  Synopsis    [Computes information about node pairs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Unm_ManPrintPairStats( Unm_Man_t * p )
{
    int i, Num, nRefs, nPairs = 0, nTotal = 0, Counter[51] = {0};
    Num = Hsh_Int4ManEntryNum( p->pHash );
    for ( i = 1; i <= Num; i++ )
    {
        nRefs = Abc_MinInt( 50, Hsh_Int4ObjRes(p->pHash, i) );
        nTotal += nRefs;
        Counter[nRefs]++;
        nPairs += (nRefs > 1);
//        printf( "(%c, %c) %d\n", 'a' + Hsh_Int4ObjData0(p->pHash, i)-1, 'a' + Hsh_Int4ObjData1(p->pHash, i)-1, nRefs );
//        printf( "(%4d, %4d) %d\n", Hsh_Int4ObjData0(p->pHash, i), Hsh_Int4ObjData1(p->pHash, i), nRefs );
    }
    for ( i = 0; i < 51; i++ )
        if ( Counter[i] > 0 )
            printf( "%3d : %7d  %7.2f %%\n", i, Counter[i], 100.0 * Counter[i] * i / nTotal );
    return nPairs;
}
void Unm_ManComputePairs( Unm_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, k, j, FanK, FanJ, Num;
    word Total = 0, Pairs = 0, Pairs2 = 0;
    Gia_ManSetRefsMapped( p->pGia );
    Gia_ManForEachLut( p->pGia, i )
    {
        Total += Gia_ObjLutSize(p->pGia, i) * (Gia_ObjLutSize(p->pGia, i) - 1) / 2;
        pObj = Gia_ManObj( p->pGia, i );
        // collect leaves of this gate  
        Vec_IntClear( p->vLeaves );
        Gia_LutForEachFanin( p->pGia, i, Num, k )
            if ( Gia_ObjRefNumId(p->pGia, Num) > 1 )
                Vec_IntPush( p->vLeaves, Num );
        if ( Vec_IntSize(p->vLeaves) < 2 )
            continue;
        Pairs += Vec_IntSize(p->vLeaves) * (Vec_IntSize(p->vLeaves) - 1) / 2;
        // enumerate pairs
        Vec_IntForEachEntry( p->vLeaves, FanK, k )
        Vec_IntForEachEntryStart( p->vLeaves, FanJ, j, k+1 )
        {
            if ( FanK > FanJ )
                ABC_SWAP( int, FanK, FanJ );
            Num = Hsh_Int4ManInsert( p->pHash, FanK, FanJ, 0 );
            Hsh_Int4ObjInc( p->pHash, Num );
        }
    }
    Total = Abc_MaxWord( Total, 1 );
    Pairs2 = Unm_ManPrintPairStats( p );
    printf( "Total = %8d    Pairs = %8d %7.2f %%    Pairs2 = %8d %7.2f %%\n", (int)Total, 
        (int)Pairs,  100.0 * (int)Pairs / (int)Total, 
        (int)Pairs2, 100.0 * (int)Pairs2 / (int)Total );
    // print statistics
    
}


/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Unm_ManTest( Gia_Man_t * pGia )
{
    Unm_Man_t * p;
    p = Unm_ManAlloc( pGia );
//    Unm_ManComputeTruths( p );
    Unm_ManComputePairs( p );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
    return Unm_ManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

