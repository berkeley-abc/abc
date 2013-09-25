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
    p->pHash = Hsh_Int4ManStart( 10 );
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

  Synopsis    []

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
        if ( i % 100 == 0 )
            Kit_DsdPrintFromTruth( (unsigned *)&uTruth, 6 ), printf( "\n" );
    }
    Vec_WrdFreeP( &vTruths2 );
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
    Unm_ManComputeTruths( p );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
    return Unm_ManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

