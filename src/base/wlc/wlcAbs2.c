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
    pPars->nBitsAdd       =      16;  // adder bit-width
    pPars->nBitsMul       =       8;  // multiplier bit-widht 
    pPars->nBitsMux       =      32;  // MUX bit-width
    pPars->nBitsFlop      =      32;  // flop bit-width
    pPars->fVerbose       =       0;  // verbose output`
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
    Wlc_Obj_t * pObj; int i;
    Wlc_NtkForEachObj( p, pObj, i )
    {
        if ( pObj->Type == WLC_OBJ_ARI_ADD || pObj->Type == WLC_OBJ_ARI_SUB || pObj->Type == WLC_OBJ_ARI_MINUS )
        {
            if ( Wlc_ObjRange(pObj) >= pPars->nBitsAdd )
                Vec_BitWriteEntry( vLeaves, Wlc_ObjId(p, pObj), 1 );
            continue;
        }
        if ( pObj->Type == WLC_OBJ_ARI_MULTI || pObj->Type == WLC_OBJ_ARI_DIVIDE || pObj->Type == WLC_OBJ_ARI_REM || pObj->Type == WLC_OBJ_ARI_MODULUS )
        {
            if ( Wlc_ObjRange(pObj) >= pPars->nBitsMul )
                Vec_BitWriteEntry( vLeaves, Wlc_ObjId(p, pObj), 1 );
            continue;
        }
        if ( pObj->Type == WLC_OBJ_MUX )
        {
            if ( Wlc_ObjRange(pObj) >= pPars->nBitsMux )
                Vec_BitWriteEntry( vLeaves, Wlc_ObjId(p, pObj), 1 );
            continue;
        }
        if ( Wlc_ObjIsCi(pObj) && !Wlc_ObjIsPi(pObj) )
        {
            if ( Wlc_ObjRange(pObj) >= pPars->nBitsFlop )
                Vec_BitWriteEntry( vLeaves, Wlc_ObjId(p, pObj), 1 );
            continue;
        }
    }
    return vLeaves;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_NtkAbsMarkNodes_rec( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, Vec_Bit_t * vLeaves, Vec_Int_t * vFlops, Vec_Int_t * vPisNew )
{
    int i, iFanin;
    if ( pObj->Mark )
        return;
    pObj->Mark = 1;
    if ( Vec_BitEntry(vLeaves, Wlc_ObjId(p, pObj)) )
    {
        Vec_IntPush( vPisNew, Wlc_ObjId(p, pObj) );
        return;
    }
    if ( Wlc_ObjIsCi(pObj) )
    {
        if ( !Wlc_ObjIsPi(pObj) )
            Vec_IntPush( vFlops, Wlc_ObjCiId(pObj) );
        return;
    }
    Wlc_ObjForEachFanin( pObj, iFanin, i )
        Wlc_NtkAbsMarkNodes_rec( p, Wlc_NtkObj(p, iFanin), vLeaves, vFlops, vPisNew );
}

Vec_Int_t * Wlc_NtkAbsMarkNodes( Wlc_Ntk_t * p, Vec_Bit_t * vLeaves )
{
    Vec_Int_t * vFlops;
    Vec_Int_t * vPisNew;
    Wlc_Obj_t * pObj;
    int i, CiId, CoId;
    Wlc_NtkCleanMarks( p );
    vFlops = Vec_IntAlloc( 100 );
    vPisNew = Vec_IntAlloc( 100 );
    Wlc_NtkForEachCo( p, pObj, i )
        Wlc_NtkAbsMarkNodes_rec( p, pObj, vLeaves, vFlops, vPisNew );
    Vec_IntForEachEntry( vFlops, CiId, i )
    {
        CoId = Wlc_NtkPoNum(p) + CiId - Wlc_NtkPiNum(p);
        Wlc_NtkAbsMarkNodes_rec( p, Wlc_NtkCo(p, CoId), vLeaves, vFlops, vPisNew );
    }
    Vec_IntFree( vFlops );
    return vPisNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Wlc_Ntk_t * Wlc_NtkAbs( Wlc_Ntk_t * p, Wlc_Par_t * pPars )
{
    Vec_Bit_t * vLeaves = Wlc_NtkAbsMarkOpers( p, pPars );
    Vec_Int_t * vPisNew = Wlc_NtkAbsMarkNodes( p, vLeaves );
    Wlc_Ntk_t * pNtkNew = Wlc_NtkDupDfs( p, 1, 1, vPisNew );
    Vec_IntFree( vPisNew );
    Vec_BitFree( vLeaves );
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

