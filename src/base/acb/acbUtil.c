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

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkCreateFanout( Acb_Ntk_t * p )
{
    int k, iObj, iFanin, * pFanins; 
    Vec_WecInit( &p->vFanouts, Acb_NtkObjNumMax(p) );
    Acb_NtkForEachObj( p, iObj )
        Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
            Vec_IntPush( Vec_WecEntry(&p->vFanouts, iFanin), iObj );
}

/**Function*************************************************************

  Synopsis    []

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
    Vec_IntClear( &p->vArray0 );
    Acb_NtkIncTravId( p );
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
    Vec_IntClear( &p->vArray1 );
    Acb_NtkIncTravId( p );
    Acb_ObjCollectTfo_rec( p, iObj, fTerm );
    return &p->vArray1;
}


/**Function*************************************************************

  Synopsis    []

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
    int i, iObj, Level = 0;
    if ( vTfo == NULL )
    {
        Acb_NtkCleanObjLevelD( p );
        Acb_NtkForEachObj( p, iObj )
            Acb_ObjComputeLevelD( p, iObj );
    }
    else
    {
        // it is assumed that vTfo contains CO nodes and level of new nodes was already updated
        Vec_IntForEachEntry( vTfo, iObj, i )
            Acb_ObjComputeLevelD( p, iObj );
    }
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
    int i, iObj, Level = 0;
    if ( vTfi == NULL )
    {
        Acb_NtkCleanObjLevelR( p );
        Acb_NtkForEachObjReverse( p, iObj )
            Acb_ObjComputeLevelR( p, iObj );
    }
    else
    {
        // it is assumed that vTfi contains CI nodes
        Vec_IntForEachEntryReverse( vTfi, iObj, i )
            Acb_ObjComputeLevelR( p, iObj );
    }
    Acb_NtkForEachCi( p, iObj, i )
        Level = Abc_MaxInt( Level, Acb_ObjLevelR(p, iObj) );
    assert( p->LevelMax == Level );
    return Level;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_ObjSlack( Acb_Ntk_t * p, int iObj )
{
    assert( !Acb_ObjIsCio(p, iObj) + p->LevelMax >= Acb_ObjLevelD(p, iObj) + Acb_ObjLevelR(p, iObj) );
    return !Acb_ObjIsCio(p, iObj) + p->LevelMax - Acb_ObjLevelD(p, iObj) - Acb_ObjLevelR(p, iObj);
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
    if ( vTfo == NULL )
    {
        Acb_NtkCleanObjPathD( p );
        Acb_NtkForEachCi( p, iObj, i )
            if ( Acb_ObjLevelR(p, iObj) == p->LevelMax )
                Acb_ObjSetPathD( p, iObj, 1 );
        Acb_NtkForEachObj( p, iObj )
            if ( !Acb_ObjIsCi(p, iObj) && !Acb_ObjSlack(p, iObj) )
                Acb_ObjComputePathD( p, iObj );
    }
    else
    {
        // it is assumed that vTfo contains CO nodes
        assert( Acb_ObjSlack(p, Vec_IntEntry(vTfo, 0)) );
        Vec_IntForEachEntry( vTfo, iObj, i )
            if ( !Acb_ObjSlack(p, iObj) )
                Acb_ObjComputePathD( p, iObj );
            else
                Acb_ObjSetPathD( p, iObj, 0 );
    }
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
    int i, iObj, Level = p->LevelMax, Path = 0;
    if ( vTfi == NULL )
    {
        Acb_NtkCleanObjPathR( p );
        Acb_NtkForEachCo( p, iObj, i )
            if ( Acb_ObjLevelD(p, iObj) == p->LevelMax )
                Acb_ObjSetPathR( p, iObj, 1 );
        Acb_NtkForEachObjReverse( p, iObj )
            if ( !Acb_ObjIsCo(p, iObj) && !Acb_ObjSlack(p, iObj) )
                Acb_ObjComputePathR( p, iObj );
    }
    else
    {
        // it is assumed that vTfi contains CI nodes
        assert( Acb_ObjSlack(p, Vec_IntEntry(vTfi, 0)) );
        Vec_IntForEachEntryReverse( vTfi, iObj, i )
            if ( !Acb_ObjSlack(p, iObj) )
                Acb_ObjComputePathR( p, iObj );
            else
                Acb_ObjSetPathR( p, iObj, 0 );
    }
    Acb_NtkForEachCi( p, iObj, i )
        Path += Acb_ObjPathR(p, iObj);
    assert( p->nPaths == Path );
    return Path;
}


int Acb_NtkComputePaths( Acb_Ntk_t * p )
{
    int LevelD = Acb_NtkComputeLevelD( p, NULL );
    int LevelR = Acb_NtkComputeLevelR( p, NULL );
    int PathD  = Acb_NtkComputePathsD( p, NULL );
    int PathR  = Acb_NtkComputePathsR( p, NULL );
    assert( PathD  == PathR );
    return PathR;
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
int Acb_ObjPath( Acb_Ntk_t * p, int iObj )
{
    return Acb_ObjPathD(p, iObj) + Acb_ObjPathR(p, iObj);
}
void Acb_ObjUpdateTiming( Acb_Ntk_t * p, int iObj )
{
}
void Acb_NtkUpdateTiming( Acb_Ntk_t * p, int iObj )
{
    int i, Entry;
    if ( iObj > 0 )
    {
        // assuming that level of the new nodes is up to date
        Vec_Int_t * vTfi = Acb_ObjCollectTfi( p, iObj, 1 );
        Vec_Int_t * vTfo = Acb_ObjCollectTfo( p, iObj, 1 );
        int nLevelD = Acb_NtkComputeLevelD( p, vTfo );
        int nLevelR = Acb_NtkComputeLevelR( p, vTfi );
        int nPathD = Acb_NtkComputePathsD( p, vTfo );
        int nPathR = Acb_NtkComputePathsR( p, vTfi );
        Vec_IntForEachEntry( vTfi, Entry, i )
            Acb_ObjUpdateTiming( p, Entry );
        Vec_IntForEachEntry( vTfo, Entry, i )
            Acb_ObjUpdateTiming( p, Entry );
    }
    else
    {
        int LevelD = Acb_NtkComputeLevelD( p, NULL );
        int LevelR = Acb_NtkComputeLevelR( p, NULL );
        int PathD  = Acb_NtkComputePathsD( p, NULL );
        int PathR  = Acb_NtkComputePathsR( p, NULL );
        Acb_NtkForEachNode( p, Entry )
            Acb_ObjUpdateTiming( p, Entry );
    }
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

