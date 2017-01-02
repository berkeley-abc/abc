/**CFile****************************************************************

  FileName    [sbdPath.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Critical path.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sbdPath.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sbdInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sbc_ManAddInternalToPath_rec( Gia_Man_t * p, int iObj, Vec_Bit_t * vPath )
{
    Gia_Obj_t * pObj; 
    int k, iFan, Value = 0;
    if ( Gia_ObjIsTravIdCurrentId(p, iObj) )
        return Vec_BitEntry(vPath, iObj);
    Gia_ObjSetTravIdCurrentId(p, iObj);
    pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjIsCi(pObj) )
        return 0;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_LutForEachFanin( p, iObj, iFan, k )
        Value |= Sbc_ManAddInternalToPath_rec( p, iFan, vPath );
    if ( Value )
        Vec_BitWriteEntry( vPath, iObj, 1 );
    return Value;
}
void Sbc_ManAddInternalToPath( Gia_Man_t * p, Vec_Bit_t * vPath )
{
    int iObj;
    Gia_ManForEachLut( p, iObj )
    {
        if ( !Vec_BitEntry(vPath, iObj) )
            continue;
        Gia_ManIncrementTravId( p );
        Sbc_ManAddInternalToPath_rec( p, iObj, vPath );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sbc_ManCriticalPath_rec( Gia_Man_t * p, int * pLevels, int iObj, int LevelFan, Vec_Bit_t * vPath )
{
    Gia_Obj_t * pObj; int k, iFan;
    if ( Gia_ObjIsTravIdCurrentId(p, iObj) )
        return;
    Gia_ObjSetTravIdCurrentId(p, iObj);
    pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjIsCi(pObj) )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Vec_BitWriteEntry( vPath, iObj, 1 );
    Gia_LutForEachFanin( p, iObj, iFan, k )
        if ( pLevels[iFan] == LevelFan )
            Sbc_ManCriticalPath_rec( p, pLevels, iFan, LevelFan-1, vPath );
}
Vec_Bit_t * Sbc_ManCriticalPath( Gia_Man_t * p )
{
    int * pLevels = NULL, k, iDriver;
    int nLevels = p->pManTime ? Gia_ManLutLevelWithBoxes(p) : Gia_ManLutLevel(p, &pLevels);
    Vec_Bit_t * vPath = Vec_BitStart( Gia_ManObjNum(p) );
    if ( p->pManTime )
        pLevels = Vec_IntArray( p->vLevels );
    Gia_ManIncrementTravId( p );
    Gia_ManForEachCoDriverId( p, iDriver, k )
        if ( pLevels[iDriver] == nLevels && iDriver )
            Sbc_ManCriticalPath_rec( p, pLevels, iDriver, nLevels-1, vPath );
    if ( !p->pManTime )
        ABC_FREE( pLevels );
    Sbc_ManAddInternalToPath( p, vPath );
    return vPath;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

