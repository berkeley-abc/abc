/**CFile****************************************************************

  FileName    [wlcAbs2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Abstraction for word-level networks.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcAbs2.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Wabs_Par_t_ Wabs_Par_t;
struct Wabs_Par_t_
{
    Wlc_Ntk_t *            pNtk;
    Wlc_Par_t *            pPars;
    Vec_Bit_t *            vLeaves;
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
void Wlc_ManSetDefaultParams( Wlc_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Wlc_Par_t) );
    pPars->nBitsAdd    = ABC_INFINITY;   // adder bit-width
    pPars->nBitsMul    = ABC_INFINITY;   // multiplier bit-widht 
    pPars->nBitsMux    = ABC_INFINITY;   // MUX bit-width
    pPars->nBitsFlop   = ABC_INFINITY;   // flop bit-width
    pPars->fVerbose    =             0;  // verbose output`
}

/**Function*************************************************************

  Synopsis    [Mark operators that meet the criteria.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Bit_t * Wlc_NtkAbsMarkOpers( Wlc_Ntk_t * p, Wlc_Par_t * pPars )
{
    Vec_Bit_t * vLeaves = Vec_BitStart( Wlc_NtkObjNumMax(p) );
    Wlc_Obj_t * pObj; int i, Count[4] = {0};
    Wlc_NtkForEachObj( p, pObj, i )
    {
        if ( pObj->Type == WLC_OBJ_ARI_ADD || pObj->Type == WLC_OBJ_ARI_SUB || pObj->Type == WLC_OBJ_ARI_MINUS )
        {
            if ( Wlc_ObjRange(pObj) >= pPars->nBitsAdd )
                Vec_BitWriteEntry( vLeaves, Wlc_ObjId(p, pObj), 1 ), Count[0]++;
            continue;
        }
        if ( pObj->Type == WLC_OBJ_ARI_MULTI || pObj->Type == WLC_OBJ_ARI_DIVIDE || pObj->Type == WLC_OBJ_ARI_REM || pObj->Type == WLC_OBJ_ARI_MODULUS )
        {
            if ( Wlc_ObjRange(pObj) >= pPars->nBitsMul )
                Vec_BitWriteEntry( vLeaves, Wlc_ObjId(p, pObj), 1 ), Count[1]++;
            continue;
        }
        if ( pObj->Type == WLC_OBJ_MUX )
        {
            if ( Wlc_ObjRange(pObj) >= pPars->nBitsMux )
                Vec_BitWriteEntry( vLeaves, Wlc_ObjId(p, pObj), 1 ), Count[2]++;
            continue;
        }
        if ( Wlc_ObjIsCi(pObj) && !Wlc_ObjIsPi(pObj) )
        {
            if ( Wlc_ObjRange(pObj) >= pPars->nBitsFlop )
                Vec_BitWriteEntry( vLeaves, Wlc_ObjId(p, pObj), 1 ), Count[3]++;
            continue;
        }
    }
    printf( "Abstraction engine marked %d adds/subs, %d muls/divs, %d muxes, and %d flops to be abstracted away.\n", Count[0], Count[1], Count[2], Count[3] );
    return vLeaves;
}

/**Function*************************************************************

  Synopsis    [Marks nodes to be included in the abstracted network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_NtkAbsMarkNodes_rec( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, Vec_Bit_t * vLeaves, Vec_Int_t * vPisOld, Vec_Int_t * vPisNew, Vec_Int_t * vFlops )
{
    int i, iFanin;
    if ( pObj->Mark )
        return;
    pObj->Mark = 1;
    if ( Vec_BitEntry(vLeaves, Wlc_ObjId(p, pObj)) )
    {
        assert( !Wlc_ObjIsPi(pObj) );
        Vec_IntPush( vPisNew, Wlc_ObjId(p, pObj) );
        return;
    }
    if ( Wlc_ObjIsCi(pObj) )
    {
        if ( Wlc_ObjIsPi(pObj) )
            Vec_IntPush( vPisOld, Wlc_ObjId(p, pObj) );
        else
            Vec_IntPush( vFlops, Wlc_ObjId(p, pObj) );
        return;
    }
    Wlc_ObjForEachFanin( pObj, iFanin, i )
        Wlc_NtkAbsMarkNodes_rec( p, Wlc_NtkObj(p, iFanin), vLeaves, vPisOld, vPisNew, vFlops );
}

void Wlc_NtkAbsMarkNodes( Wlc_Ntk_t * p, Vec_Bit_t * vLeaves, Vec_Int_t * vPisOld, Vec_Int_t * vPisNew, Vec_Int_t * vFlops )
{
    Wlc_Obj_t * pObj;
    int i, Count = 0;
    Wlc_NtkCleanMarks( p );
    Wlc_NtkForEachCo( p, pObj, i )
        Wlc_NtkAbsMarkNodes_rec( p, pObj, vLeaves, vPisOld, vPisNew, vFlops );
    Wlc_NtkForEachObjVec( vFlops, p, pObj, i )
        Wlc_NtkAbsMarkNodes_rec( p, Wlc_ObjFo2Fi(p, pObj), vLeaves, vPisOld, vPisNew, vFlops );
    Wlc_NtkForEachObj( p, pObj, i )
        Count += pObj->Mark;
//    printf( "Collected %d old PIs, %d new PIs, %d flops, and %d other objects.\n", 
//        Vec_IntSize(vPisOld), Vec_IntSize(vPisNew), Vec_IntSize(vFlops), 
//        Count - Vec_IntSize(vPisOld) - Vec_IntSize(vPisNew) - Vec_IntSize(vFlops) );
    Vec_IntSort( vPisOld, 0 );
    Vec_IntSort( vPisNew, 0 );
    Vec_IntSort( vFlops, 0 );
    Wlc_NtkCleanMarks( p );
}

/**Function*************************************************************

  Synopsis    [Derive abstraction based on the parameter values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Wlc_Ntk_t * Wlc_NtkAbs( Wlc_Ntk_t * p, Wlc_Par_t * pPars )
{
    Wlc_Ntk_t * pNtkNew = NULL;
    Vec_Int_t * vPisOld = Vec_IntAlloc( 100 );
    Vec_Int_t * vPisNew = Vec_IntAlloc( 100 );
    Vec_Int_t * vFlops  = Vec_IntAlloc( 100 );
    Vec_Bit_t * vLeaves = Wlc_NtkAbsMarkOpers( p, pPars );
    Wlc_NtkAbsMarkNodes( p, vLeaves, vPisOld, vPisNew, vFlops );
    Vec_BitFree( vLeaves );
    pNtkNew = Wlc_NtkDupDfsAbs( p, vPisOld, vPisNew, vFlops );
    Vec_IntFree( vPisOld );
    Vec_IntFree( vPisNew );
    Vec_IntFree( vFlops );
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

