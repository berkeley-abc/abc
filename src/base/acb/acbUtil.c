/**CFile****************************************************************

  FileName    [acbUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 21, 2015.]

  Revision    [$Id: acbUtil.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acb.h"
#include "base/abc/abc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collecting TFI and TFO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_ObjCollectTfi_rec( Acb_Ntk_t * p, int iObj, int fTerm )
{
    int * pFanin, iFanin, i;
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    if ( !fTerm && Acb_ObjIsCi(p, iObj) )
        return;
    Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, i )
        Acb_ObjCollectTfi_rec( p, iFanin, fTerm );
    Vec_IntPush( &p->vArray0, iObj );
}
Vec_Int_t * Acb_ObjCollectTfi( Acb_Ntk_t * p, int iObj, int fTerm )
{
    int i;
    Vec_IntClear( &p->vArray0 );
    Acb_NtkIncTravId( p );
    if ( iObj > 0 )
        Acb_ObjCollectTfi_rec( p, iObj, fTerm );
    else
        Acb_NtkForEachCo( p, iObj, i )
            Acb_ObjCollectTfi_rec( p, iObj, fTerm );
    return &p->vArray0;
}

void Acb_ObjCollectTfo_rec( Acb_Ntk_t * p, int iObj, int fTerm )
{
    int iFanout, i;
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    if ( !fTerm && Acb_ObjIsCo(p, iObj) )
        return;
    Acb_ObjForEachFanout( p, iObj, iFanout, i )
        Acb_ObjCollectTfo_rec( p, iFanout, fTerm );
    Vec_IntPush( &p->vArray1, iObj );
}
Vec_Int_t * Acb_ObjCollectTfo( Acb_Ntk_t * p, int iObj, int fTerm )
{
    int i;
    Vec_IntClear( &p->vArray1 );
    Acb_NtkIncTravId( p );
    if ( iObj > 0 )
        Acb_ObjCollectTfo_rec( p, iObj, fTerm );
    else
        Acb_NtkForEachCi( p, iObj, i )
            Acb_ObjCollectTfo_rec( p, iObj, fTerm );
    return &p->vArray1;
}

/**Function*************************************************************

  Synopsis    [Computing and updating direct and reverse logic level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_ObjComputeLevelD( Acb_Ntk_t * p, int iObj )
{
    int * pFanins, iFanin, k, Level = 0;
    Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
        Level = Abc_MaxInt( Level, Acb_ObjLevelD(p, iFanin) );
    return Acb_ObjSetLevelD( p, iObj, Level + !Acb_ObjIsCio(p, iObj) );
}
int Acb_NtkComputeLevelD( Acb_Ntk_t * p, Vec_Int_t * vTfo )
{
    // it is assumed that vTfo contains CO nodes and level of new nodes was already updated
    int i, iObj, Level = 0;
    if ( !Acb_NtkHasObjLevelD( p ) )
        Acb_NtkCleanObjLevelD( p );
    Vec_IntForEachEntryReverse( vTfo, iObj, i )
        Acb_ObjComputeLevelD( p, iObj );
    Acb_NtkForEachCo( p, iObj, i )
        Level = Abc_MaxInt( Level, Acb_ObjLevelD(p, iObj) );
    p->LevelMax = Level;
    return Level;
}

int Acb_ObjComputeLevelR( Acb_Ntk_t * p, int iObj )
{
    int iFanout, k, Level = 0;
    Acb_ObjForEachFanout( p, iObj, iFanout, k )
        Level = Abc_MaxInt( Level, Acb_ObjLevelR(p, iFanout) );
    return Acb_ObjSetLevelR( p, iObj, Level + !Acb_ObjIsCio(p, iObj) );
}
int Acb_NtkComputeLevelR( Acb_Ntk_t * p, Vec_Int_t * vTfi )
{
    // it is assumed that vTfi contains CI nodes
    int i, iObj, Level = 0;
    if ( !Acb_NtkHasObjLevelD( p ) )
        Acb_NtkCleanObjLevelD( p );
    Vec_IntForEachEntryReverse( vTfi, iObj, i )
        Acb_ObjComputeLevelR( p, iObj );
    Acb_NtkForEachCi( p, iObj, i )
        Level = Abc_MaxInt( Level, Acb_ObjLevelR(p, iObj) );
    assert( p->LevelMax == Level );
    return Level;
}

void Acb_NtkUpdateLevelD( Acb_Ntk_t * p, int Pivot )
{
    Vec_Int_t * vTfo = Acb_ObjCollectTfo( p, Pivot, 1 );
    Acb_NtkComputeLevelD( p, vTfo );
}

/**Function*************************************************************

  Synopsis    [Computing and updating direct and reverse path count.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_ObjSlack( Acb_Ntk_t * p, int iObj )
{
    int LevelSum = Acb_ObjLevelD(p, iObj) + Acb_ObjLevelR(p, iObj);
    assert( !Acb_ObjIsCio(p, iObj) + p->LevelMax >= LevelSum );
    return !Acb_ObjIsCio(p, iObj) + p->LevelMax - LevelSum;
}

int Acb_ObjComputePathD( Acb_Ntk_t * p, int iObj )
{
    int * pFanins, iFanin, k, Path = 0;
    assert( !Acb_ObjIsCi(p, iObj) );
    Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
        if ( !Acb_ObjSlack(p, iFanin) )
            Path += Acb_ObjPathD(p, iFanin);
    return Acb_ObjSetPathD( p, iObj, Path );
}
int Acb_NtkComputePathsD( Acb_Ntk_t * p, Vec_Int_t * vTfo )
{
    int i, iObj, Path = 0;
    // it is assumed that vTfo contains CO nodes
    //assert( Acb_ObjSlack(p, Vec_IntEntry(vTfo, 0)) );
    Vec_IntForEachEntryReverse( vTfo, iObj, i )
        if ( !Acb_ObjSlack(p, iObj) )
            Acb_ObjComputePathD( p, iObj );
        else
            Acb_ObjSetPathD( p, iObj, 0 );
    Acb_NtkForEachCo( p, iObj, i )
        Path += Acb_ObjPathD(p, iObj);
    p->nPaths = Path;
    return Path;
}

int Acb_ObjComputePathR( Acb_Ntk_t * p, int iObj )
{
    int iFanout, k, Path = 0;
    assert( !Acb_ObjIsCo(p, iObj) );
    Acb_ObjForEachFanout( p, iObj, iFanout, k )
        if ( !Acb_ObjSlack(p, iFanout) )
            Path += Acb_ObjPathR(p, iFanout);
    return Acb_ObjSetPathR( p, iObj, Path );
}
int Acb_NtkComputePathsR( Acb_Ntk_t * p, Vec_Int_t * vTfi )
{
    int i, iObj, Path = 0;
    // it is assumed that vTfi contains CI nodes
    //assert( Acb_ObjSlack(p, Vec_IntEntry(vTfi, 0)) );
    Vec_IntForEachEntryReverse( vTfi, iObj, i )
        if ( !Acb_ObjSlack(p, iObj) )
            Acb_ObjComputePathR( p, iObj );
        else
            Acb_ObjSetPathR( p, iObj, 0 );
    Acb_NtkForEachCi( p, iObj, i )
        Path += Acb_ObjPathR(p, iObj);
    assert( p->nPaths == Path );
    return Path;
}

int Acb_NtkComputePaths( Acb_Ntk_t * p )
{
    Vec_Int_t * vTfi = Acb_ObjCollectTfi( p, -1, 1 );
    Vec_Int_t * vTfo = Acb_ObjCollectTfo( p, -1, 1 );
    Acb_NtkComputeLevelD( p, vTfi );
    Acb_NtkComputeLevelR( p, vTfo );
    Acb_NtkComputePathsD( p, vTfi );
    Acb_NtkComputePathsR( p, vTfo );
    return p->nPaths;
}
void Abc_NtkComputePaths( Abc_Ntk_t * p )
{
    extern Acb_Ntk_t * Acb_NtkFromAbc( Abc_Ntk_t * p );
    Acb_Ntk_t * pNtk = Acb_NtkFromAbc( p );
    Acb_NtkCreateFanout( pNtk );
    printf( "Computed %d paths.\n", Acb_NtkComputePaths(pNtk) );
    Acb_ManFree( pNtk->pDesign );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_ObjUpdatePriority( Acb_Ntk_t * p, int iObj )
{
    int nPaths;
    if ( p->vQue == NULL )
    {
        Acb_NtkCleanObjCounts( p );
        p->vQue = Vec_QueAlloc( 1000 );
        Vec_QueSetPriority( p->vQue, Vec_FltArrayP(&p->vCounts) );
    }
    nPaths = Acb_ObjPathD(p, iObj) + Acb_ObjPathR(p, iObj);
    if ( nPaths == 0 )
        return;
    Acb_ObjSetCounts( p, iObj, (float)nPaths );
    if ( Vec_QueIsMember( p->vQue, iObj ) )
        Vec_QueUpdate( p->vQue, iObj );
    else
        Vec_QuePush( p->vQue, iObj );
}
void Acb_NtkUpdateTiming( Acb_Ntk_t * p, int iObj )
{
    int i, Entry, LevelMax = p->LevelMax;
    // assuming that level of the new nodes is up to date
    Vec_Int_t * vTfi = Acb_ObjCollectTfi( p, iObj, 1 );
    Vec_Int_t * vTfo = Acb_ObjCollectTfo( p, iObj, 1 );
    Acb_NtkComputeLevelD( p, vTfo );
    Acb_NtkComputeLevelR( p, vTfi );
    if ( iObj > 0 && LevelMax > p->LevelMax ) // reduced level
    {
        vTfi = Acb_ObjCollectTfi( p, -1, 1 );
        vTfo = Acb_ObjCollectTfo( p, -1, 1 );   
        Vec_QueClear( p->vQue );
        // add backup here
    }
    Acb_NtkComputePathsD( p, vTfo );
    Acb_NtkComputePathsR( p, vTfi );
    Vec_IntForEachEntry( vTfi, Entry, i )
        Acb_ObjUpdatePriority( p, Entry );
    Vec_IntForEachEntry( vTfo, Entry, i )
        Acb_ObjUpdatePriority( p, Entry );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkCreateNode( Acb_Ntk_t * p, word uTruth, Vec_Int_t * vSupp )
{
    int Pivot = Acb_ObjAlloc( p, ABC_OPER_LUT, Vec_IntSize(vSupp), 0 );
    Acb_ObjSetTruth( p, Pivot, uTruth );
    Acb_ObjAddFanins( p, Pivot, vSupp );
    Acb_ObjAddFaninFanout( p, Pivot );
    Acb_ObjComputeLevelD( p, Pivot );
}
void Acb_NtkUpdateNode( Acb_Ntk_t * p, int Pivot, word uTruth, Vec_Int_t * vSupp )
{
    Vec_WrdSetEntry( &p->vObjTruth, Pivot, uTruth );
    Vec_IntErase( Vec_WecEntry(&p->vCnfs, Pivot) );
    Acb_ObjRemoveFaninFanout( p, Pivot );
    Acb_ObjRemoveFanins( p, Pivot );
    Acb_ObjAddFanins( p, Pivot, vSupp );
    Acb_ObjAddFaninFanout( p, Pivot );
    if ( p->vQue == NULL )
        Acb_NtkUpdateLevelD( p, Pivot );
    else
        Acb_NtkUpdateTiming( p, Pivot );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

