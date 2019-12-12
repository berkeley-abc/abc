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
    int i, Node;
    Vec_IntClear( &p->vArray0 );
    Acb_NtkIncTravId( p );
    if ( iObj > 0 )
    {
        Vec_IntForEachEntry( &p->vSuppOld, Node, i )
            Acb_ObjCollectTfi_rec( p, Node, fTerm );
        Acb_ObjCollectTfi_rec( p, iObj, fTerm );
    }
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
    if ( !Acb_NtkHasObjLevelR( p ) )
        Acb_NtkCleanObjLevelR( p );
    Vec_IntForEachEntryReverse( vTfi, iObj, i )
        Acb_ObjComputeLevelR( p, iObj );
    Acb_NtkForEachCi( p, iObj, i )
        Level = Abc_MaxInt( Level, Acb_ObjLevelR(p, iObj) );
//    assert( p->LevelMax == Level );
    p->LevelMax = Level;
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
int Acb_NtkComputePathsD( Acb_Ntk_t * p, Vec_Int_t * vTfo, int fReverse )
{
    int i, iObj, Path = 0;
    //Vec_IntPrint( vTfo );
    if ( !Acb_NtkHasObjPathD( p ) )
        Acb_NtkCleanObjPathD( p );
    // it is assumed that vTfo contains CI nodes
    //assert( Acb_ObjSlack(p, Vec_IntEntry(vTfo, 0)) );
    if ( fReverse )
    {
        Vec_IntForEachEntryReverse( vTfo, iObj, i )
        {
            if ( Acb_ObjIsCi(p, iObj) )
                Acb_ObjSetPathD( p, iObj, Acb_ObjSlack(p, iObj) == 0 );
            else if ( Acb_ObjSlack(p, iObj) )
                Acb_ObjSetPathD( p, iObj, 0 );
            else
                Acb_ObjComputePathD( p, iObj );
        }
    }
    else
    {
        Vec_IntForEachEntry( vTfo, iObj, i )
        {
            if ( Acb_ObjIsCi(p, iObj) )
                Acb_ObjSetPathD( p, iObj, Acb_ObjSlack(p, iObj) == 0 );
            else if ( Acb_ObjSlack(p, iObj) )
                Acb_ObjSetPathD( p, iObj, 0 );
            else
                Acb_ObjComputePathD( p, iObj );
        }
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
int Acb_NtkComputePathsR( Acb_Ntk_t * p, Vec_Int_t * vTfi, int fReverse )
{
    int i, iObj, Path = 0;
    if ( !Acb_NtkHasObjPathR( p ) )
        Acb_NtkCleanObjPathR( p );
    // it is assumed that vTfi contains CO nodes
    //assert( Acb_ObjSlack(p, Vec_IntEntry(vTfi, 0)) );
    if ( fReverse )
    {
        Vec_IntForEachEntryReverse( vTfi, iObj, i )
        {
            if ( Acb_ObjIsCo(p, iObj) )
                Acb_ObjSetPathR( p, iObj, Acb_ObjSlack(p, iObj) == 0 );
            else if ( Acb_ObjSlack(p, iObj) )
                Acb_ObjSetPathR( p, iObj, 0 );
            else
                Acb_ObjComputePathR( p, iObj );
        }
    }
    else
    {
        Vec_IntForEachEntry( vTfi, iObj, i )
        {
            if ( Acb_ObjIsCo(p, iObj) )
                Acb_ObjSetPathR( p, iObj, Acb_ObjSlack(p, iObj) == 0 );
            else if ( Acb_ObjSlack(p, iObj) )
                Acb_ObjSetPathR( p, iObj, 0 );
            else
                Acb_ObjComputePathR( p, iObj );
        }
    }
    Acb_NtkForEachCi( p, iObj, i )
        Path += Acb_ObjPathR(p, iObj);
//    assert( p->nPaths == Path );
    p->nPaths = Path;
    return Path;
}

void Acb_NtkPrintPaths( Acb_Ntk_t * p )
{
    int iObj;
    Acb_NtkForEachObj( p, iObj )
    {
        printf( "Obj = %5d :   ",   iObj );
        printf( "LevelD = %5d  ",   Acb_ObjLevelD(p, iObj) );
        printf( "LevelR = %5d    ", Acb_ObjLevelR(p, iObj) );
        printf( "PathD = %5d  ",    Acb_ObjPathD(p, iObj) );
        printf( "PathR = %5d    ",  Acb_ObjPathR(p, iObj) );
        printf( "Paths = %5d  ",    Acb_ObjPathD(p, iObj) * Acb_ObjPathR(p, iObj) );
        printf( "\n" );
    }
}

int Acb_NtkComputePaths( Acb_Ntk_t * p )
{
    int LevelD, LevelR;
    Vec_Int_t * vTfi = Acb_ObjCollectTfi( p, -1, 1 );
    Vec_Int_t * vTfo = Acb_ObjCollectTfo( p, -1, 1 );
    Acb_NtkComputeLevelD( p, vTfo );
    LevelD = p->LevelMax;
    Acb_NtkComputeLevelR( p, vTfi );
    LevelR = p->LevelMax;
    assert( LevelD == LevelR );
    Acb_NtkComputePathsD( p, vTfo, 1 );
    Acb_NtkComputePathsR( p, vTfi, 1 );
    return p->nPaths;
}
void Abc_NtkComputePaths( Abc_Ntk_t * p )
{
    extern Acb_Ntk_t * Acb_NtkFromAbc( Abc_Ntk_t * p );
    Acb_Ntk_t * pNtk = Acb_NtkFromAbc( p );
    Acb_NtkCreateFanout( pNtk );
    Acb_NtkCleanObjCounts( pNtk );
    printf( "Computed %d paths.\n", Acb_NtkComputePaths(pNtk) );
    Acb_NtkPrintPaths( pNtk );
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
    if ( Acb_ObjIsCio(p, iObj) || Acb_ObjLevelD(p, iObj) == 1 )
        return;
    if ( p->vQue == NULL )
    {
        Acb_NtkCleanObjCounts( p );
        p->vQue = Vec_QueAlloc( 1000 );
        Vec_QueSetPriority( p->vQue, Vec_FltArrayP(&p->vCounts) );
    }
    nPaths = Acb_ObjPathD(p, iObj) * Acb_ObjPathR(p, iObj);
    Acb_ObjSetCounts( p, iObj, (float)nPaths );
    if ( Vec_QueIsMember( p->vQue, iObj ) )
    {
//printf( "Updating object %d with count %d\n", iObj, nPaths );
        Vec_QueUpdate( p->vQue, iObj );
    }
    else if ( nPaths )
    {
//printf( "Adding object %d with count %d\n", iObj, nPaths );
        Vec_QuePush( p->vQue, iObj );
    }
}
void Acb_NtkUpdateTiming( Acb_Ntk_t * p, int iObj )
{
    int i, Entry, LevelMax = p->LevelMax;
    int LevelD, LevelR, nPaths1, nPaths2;
    // assuming that direct level of the new nodes (including iObj) is up to date
    Vec_Int_t * vTfi = Acb_ObjCollectTfi( p, iObj, 1 );
    Vec_Int_t * vTfo = Acb_ObjCollectTfo( p, iObj, 1 );
    if ( iObj > 0 )
    {
        assert( Vec_IntEntryLast(vTfi) == iObj );
        assert( Vec_IntEntryLast(vTfo) == iObj );
        Vec_IntPop( vTfo );
    }
    Acb_NtkComputeLevelD( p, vTfo );
    LevelD = p->LevelMax;
    Acb_NtkComputeLevelR( p, vTfi );
    LevelR = p->LevelMax;
    assert( LevelD == LevelR );
    if ( iObj > 0 && LevelMax > p->LevelMax ) // reduced level
    {
        iObj = -1;
        vTfi = Acb_ObjCollectTfi( p, -1, 1 );
        vTfo = Acb_ObjCollectTfo( p, -1, 1 );   
        Vec_QueClear( p->vQue );
        // add backup here
    }
    if ( iObj > 0 )
    Acb_NtkComputePathsD( p, vTfi, 0 );
    Acb_NtkComputePathsD( p, vTfo, 1 );
    nPaths1 = p->nPaths;
    if ( iObj > 0 )
    Acb_NtkComputePathsR( p, vTfo, 0 );
    Acb_NtkComputePathsR( p, vTfi, 1 );
    nPaths2 = p->nPaths;
    assert( nPaths1 == nPaths2 );
    Vec_IntForEachEntry( vTfi, Entry, i )
        Acb_ObjUpdatePriority( p, Entry );
    if ( iObj > 0 )
    Vec_IntForEachEntry( vTfo, Entry, i )
        Acb_ObjUpdatePriority( p, Entry );

//    printf( "Updating timing for object %d.\n", iObj );
//    Acb_NtkPrintPaths( p );
//    while ( (Entry = (int)Vec_QueTopPriority(p->vQue)) > 0 )
//        printf( "Obj = %5d : Prio = %d.\n", Vec_QuePop(p->vQue), Entry );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkPrintNode( Acb_Ntk_t * p, int iObj )
{
    int k, iFanin, * pFanins; 
    printf( "Node %5d : ", iObj );
    Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
        printf( "%d ", iFanin );
    printf( "LevelD = %d. LevelR = %d.\n", Acb_ObjLevelD(p, iObj), Acb_ObjLevelR(p, iObj) );
}
int Acb_NtkCreateNode( Acb_Ntk_t * p, word uTruth, Vec_Int_t * vSupp )
{
    int Pivot = Acb_ObjAlloc( p, ABC_OPER_LUT, Vec_IntSize(vSupp), 0 );
    Acb_ObjSetTruth( p, Pivot, uTruth );
    Acb_ObjAddFanins( p, Pivot, vSupp );
    Acb_ObjAddFaninFanout( p, Pivot );
    Acb_ObjComputeLevelD( p, Pivot );
    return Pivot;
}
void Acb_NtkResetNode( Acb_Ntk_t * p, int Pivot, word uTruth, Vec_Int_t * vSupp )
{
    // remember old fanins
    int k, iFanin, * pFanins; 
    Vec_Int_t * vFanins = Vec_IntAlloc( 6 );
    assert( !Acb_ObjIsCio(p, Pivot) );
    Acb_ObjForEachFaninFast( p, Pivot, pFanins, iFanin, k )
        Vec_IntPush( vFanins, iFanin );
    // update function
    Vec_WrdSetEntry( &p->vObjTruth, Pivot, uTruth );
    Vec_IntErase( Vec_WecEntry(&p->vCnfs, Pivot) );
    // remove old fanins
    Acb_ObjRemoveFaninFanout( p, Pivot );
    Acb_ObjRemoveFanins( p, Pivot );
    // add new fanins
    if ( vSupp != NULL )
    {
        assert( Acb_ObjFanoutNum(p, Pivot) > 0 );
        Acb_ObjAddFanins( p, Pivot, vSupp );
        Acb_ObjAddFaninFanout( p, Pivot );
    }
    else if ( Acb_ObjFanoutNum(p, Pivot) == 0 )
        Acb_ObjCleanType( p, Pivot );
    // delete dangling fanins
    Vec_IntForEachEntry( vFanins, iFanin, k )
        if ( !Acb_ObjIsCio(p, iFanin) && Acb_ObjFanoutNum(p, iFanin) == 0 )
            Acb_NtkResetNode( p, iFanin, 0, NULL );
    Vec_IntFree( vFanins );
}
void Acb_NtkSaveSupport( Acb_Ntk_t * p, int iObj )
{
    int k, iFanin, * pFanins; 
    Vec_IntClear( &p->vSuppOld );
    Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
        Vec_IntPush( &p->vSuppOld, iFanin );
}
void Acb_NtkUpdateNode( Acb_Ntk_t * p, int Pivot, word uTruth, Vec_Int_t * vSupp )
{
    //int Level = Acb_ObjLevelD(p, Pivot);
    Acb_NtkSaveSupport( p, Pivot );
    //Acb_NtkPrintNode( p, Pivot );
    Acb_NtkResetNode( p, Pivot, uTruth, vSupp );
    Acb_ObjComputeLevelD( p, Pivot );
    //assert( Level > Acb_ObjLevelD(p, Pivot) );
    //Acb_NtkPrintNode( p, Pivot );
    if ( p->vQue == NULL )
        Acb_NtkUpdateLevelD( p, Pivot );
    else
//        Acb_NtkUpdateTiming( p, Pivot );
        Acb_NtkUpdateTiming( p, -1 );
    Vec_IntClear( &p->vSuppOld );
}

/**Function*************************************************************

  Synopsis    [Derive AIG for one network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkFindNodes2_rec( Acb_Ntk_t * p, int iObj, Vec_Int_t * vNodes )
{
    int * pFanin, iFanin, i;
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    if ( Acb_ObjIsCi(p, iObj) )
        return;
    Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, i )
        Acb_NtkFindNodes2_rec( p, iFanin, vNodes );
    assert( !Acb_ObjIsCo(p, iObj) );
    Vec_IntPush( vNodes, iObj );
}
Vec_Int_t * Acb_NtkFindNodes2( Acb_Ntk_t * p )
{
    int i, iObj;
    Vec_Int_t * vNodes = Vec_IntAlloc( 1000 );
    Acb_NtkIncTravId( p );
    Acb_NtkForEachCo( p, iObj, i )
        Acb_NtkFindNodes2_rec( p, Acb_ObjFanin(p, iObj, 0), vNodes );
    return vNodes;
}
int Acb_ObjToGia2( Gia_Man_t * pNew, Acb_Ntk_t * p, int iObj, Vec_Int_t * vTemp )
{
    //char * pName = Abc_NamStr( p->pDesign->pStrs, Acb_ObjName(p, iObj) );
    int * pFanin, iFanin, k, Type, Res;
    assert( !Acb_ObjIsCio(p, iObj) );
    Vec_IntClear( vTemp );
    Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, k )
    {
        assert( Acb_ObjCopy(p, iFanin) >= 0 );
        Vec_IntPush( vTemp, Acb_ObjCopy(p, iFanin) );
    }
    Type = Acb_ObjType( p, iObj );
    if ( Type == ABC_OPER_CONST_F ) 
        return 0;
    if ( Type == ABC_OPER_CONST_T ) 
        return 1;
    if ( Type == ABC_OPER_BIT_BUF ) 
        return Vec_IntEntry(vTemp, 0);
    if ( Type == ABC_OPER_BIT_INV ) 
        return Abc_LitNot( Vec_IntEntry(vTemp, 0) );
    if ( Type == ABC_OPER_BIT_AND || Type == ABC_OPER_BIT_NAND )
    {
        Res = 1;
        Vec_IntForEachEntry( vTemp, iFanin, k )
            Res = Gia_ManAppendAnd2( pNew, Res, iFanin );
        return Abc_LitNotCond( Res, Type == ABC_OPER_BIT_NAND );
    }
    if ( Type == ABC_OPER_BIT_OR || Type == ABC_OPER_BIT_NOR )
    {
        Res = 0;
        Vec_IntForEachEntry( vTemp, iFanin, k )
            Res = Gia_ManAppendOr2( pNew, Res, iFanin );
        return Abc_LitNotCond( Res, Type == ABC_OPER_BIT_NOR );
    }
    if ( Type == ABC_OPER_BIT_XOR || Type == ABC_OPER_BIT_NXOR )
    {
        Res = 0;
        Vec_IntForEachEntry( vTemp, iFanin, k )
            Res = Gia_ManAppendXor2( pNew, Res, iFanin );
        return Abc_LitNotCond( Res, Type == ABC_OPER_BIT_NXOR );
    }
    assert( 0 );
    return -1;
}
Gia_Man_t * Acb_NtkToGia2( Acb_Ntk_t * p )
{
    Gia_Man_t * pNew, * pOne;
    Vec_Int_t * vFanins, * vNodes;
    int i, iObj;
    pNew = Gia_ManStart( 2 * Acb_NtkObjNum(p) + 1000 );
    pNew->pName = Abc_UtilStrsav(Acb_NtkName(p));
    Acb_NtkCleanObjCopies( p );
    Acb_NtkForEachCi( p, iObj, i )
        Acb_ObjSetCopy( p, iObj, Gia_ManAppendCi(pNew) );
    vFanins = Vec_IntAlloc( 4 );
    vNodes  = Acb_NtkFindNodes2( p );
    Vec_IntForEachEntry( vNodes, iObj, i )
        Acb_ObjSetCopy( p, iObj, Acb_ObjToGia2(pNew, p, iObj, vFanins) );
    Vec_IntFree( vNodes );
    Vec_IntFree( vFanins );
    Acb_NtkForEachCo( p, iObj, i )
        Gia_ManAppendCo( pNew, Acb_ObjCopy(p, Acb_ObjFanin(p, iObj, 0)) );
    pNew = Gia_ManCleanup( pOne = pNew );
    Gia_ManUpdateCopy( &p->vObjCopy, pOne );
    Gia_ManStop( pOne );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acb_NtkCollectCopies( Acb_Ntk_t * p, Gia_Man_t * pGia, Vec_Ptr_t ** pvNodesR )
{
    int i, iObj, iLit;
    Vec_Int_t * vObjs   = Acb_NtkFindNodes2( p );
    Vec_Int_t * vNodes  = Vec_IntAlloc( Acb_NtkObjNum(p) );
    Vec_Ptr_t * vNodesR = Vec_PtrStart( Gia_ManObjNum(pGia) );
    Vec_Bit_t * vDriver = Vec_BitStart( Gia_ManObjNum(pGia) );
    Gia_ManForEachCoId( pGia, iObj, i )
    {
        Vec_BitWriteEntry( vDriver, Gia_ObjFaninId0(Gia_ManObj(pGia, iObj), iObj), 1 );
        Vec_PtrWriteEntry( vNodesR, iObj, Abc_UtilStrsav(Acb_ObjNameStr(p, Acb_NtkCo(p, i))) );
        Vec_IntPush( vNodes, iObj );
    }
    Vec_IntForEachEntry( vObjs, iObj, i )
        if ( (iLit = Acb_ObjCopy(p, iObj)) >= 0 && Gia_ObjIsAnd(Gia_ManObj(pGia, Abc_Lit2Var(iLit))) )
        {
            if ( !Vec_BitEntry(vDriver, Abc_Lit2Var(iLit)) && Vec_PtrEntry(vNodesR, Abc_Lit2Var(iLit)) == NULL )
            {
                Vec_PtrWriteEntry( vNodesR, Abc_Lit2Var(iLit), Abc_UtilStrsav(Acb_ObjNameStr(p, iObj)) );
                Vec_IntPush( vNodes, Abc_Lit2Var(iLit) );
            }
        }
    Vec_BitFree( vDriver );
    Vec_IntFree( vObjs );
    Vec_IntSort( vNodes, 0 );
    *pvNodesR = vNodesR;
    return vNodes;
}
Vec_Int_t * Acb_NtkCollectUser( Acb_Ntk_t * p, Vec_Ptr_t * vUser )
{
    char * pTemp; int i;
    Vec_Int_t * vRes = Vec_IntAlloc( Vec_PtrSize(vUser) );
    Vec_Int_t * vMap = Vec_IntStart( Abc_NamObjNumMax(Acb_NtkNam(p)) );
    Acb_NtkForEachNode( p, i )
        if ( Acb_ObjName(p, i) > 0 )
            Vec_IntWriteEntry( vMap, Acb_ObjName(p, i), Acb_ObjCopy(p, i) );
    Vec_PtrForEachEntry( char *, vUser, pTemp, i )
        if ( Acb_NtkStrId(p, pTemp) < Vec_IntSize(vMap) )
        {
            int iLit = Vec_IntEntry( vMap, Acb_NtkStrId(p, pTemp) );
            assert( iLit > 0 );
            //printf( "Obj = %3d  Name = %3d  Copy = %3d\n", i, Acb_NtkStrId(p, pTemp), iLit );
            Vec_IntPush( vRes, Abc_Lit2Var(iLit) );
        }
    assert( Vec_IntSize(vRes) == Vec_PtrSize(vUser) );
    Vec_IntFree( vMap );
    Vec_IntUniqify( vRes );
    return vRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_NtkExtract( char * pFileName0, char * pFileName1, int fVerbose, 
                    Gia_Man_t ** ppGiaF, Gia_Man_t ** ppGiaG, Vec_Int_t ** pvNodes, Vec_Ptr_t ** pvNodesR )
{
    extern Acb_Ntk_t * Acb_VerilogSimpleRead( char * pFileName, char * pFileNameW );
    Acb_Ntk_t * pNtkF = Acb_VerilogSimpleRead( pFileName0, NULL );
    Acb_Ntk_t * pNtkG = Acb_VerilogSimpleRead( pFileName1, NULL );
    int RetValue = 0;
    if ( pNtkF && pNtkG )
    {
        Gia_Man_t * pGiaF = Acb_NtkToGia2( pNtkF );
        Gia_Man_t * pGiaG = Acb_NtkToGia2( pNtkG );
        assert( Acb_NtkCiNum(pNtkF) == Acb_NtkCiNum(pNtkG) );
        assert( Acb_NtkCoNum(pNtkF) == Acb_NtkCoNum(pNtkG) );
        *ppGiaF  = pGiaF;
        *ppGiaG  = pGiaG;
        *pvNodes = Acb_NtkCollectCopies( pNtkF, pGiaF, pvNodesR );
        RetValue = 1;
    }
    if ( pNtkF ) Acb_ManFree( pNtkF->pDesign );
    if ( pNtkG ) Acb_ManFree( pNtkG->pDesign );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acb_NtkPlaces( char * pFileName, Vec_Ptr_t * vNames )
{
    Vec_Int_t * vPlaces; int First = 1, Pos = -1;
    char * pTemp, * pBuffer = Extra_FileReadContents( pFileName );
    char * pLimit = pBuffer + strlen(pBuffer);
    if ( pBuffer == NULL )
        return NULL;
    vPlaces = Vec_IntAlloc( Vec_PtrSize(vNames) );
    for ( pTemp = pBuffer; *pTemp; pTemp++ )
    {
        if ( *pTemp == '\n' )
            Pos = pTemp - pBuffer + 1;
        else if ( *pTemp == '(' )
        {
            if ( First )
                First = 0;
            else
            {
                char * pToken = strtok( pTemp+1, "  \n\r\t," );
                char * pName; int i;
                Vec_PtrForEachEntry( char *, vNames, pName, i )
                    if ( !strcmp(pName, pToken) )
                        Vec_IntPushTwo( vPlaces, Pos, i );
                pTemp = pToken + strlen(pToken);
                while ( *pTemp == 0 )
                    pTemp++;
                assert( pTemp < pLimit );
            }
        }
    }
    assert( Vec_IntSize(vPlaces) == 2*Vec_PtrSize(vNames) );
    ABC_FREE( pBuffer );
    return vPlaces;
}
void Acb_NtkInsert( char * pFileNameIn, char * pFileNameOut, Vec_Ptr_t * vNames )
{
    int i, k, Prev = 0, Pos, Pos2, iObj;
    Vec_Int_t * vPlaces;
    char * pName, * pBuffer;
    FILE * pFile = fopen( pFileNameOut, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileNameOut );
        return;
    }
    pBuffer = Extra_FileReadContents( pFileNameIn );
    if ( pBuffer == NULL )
    {
        fclose( pFile );
        printf( "Cannot open input file \"%s\".\n", pFileNameIn );
        return;
    }
    vPlaces = Acb_NtkPlaces( pFileNameIn, vNames );
    Vec_IntForEachEntryDouble( vPlaces, Pos, iObj, i )
    {
        for ( k = Prev; k < Pos; k++ )
            fputc( pBuffer[k], pFile );
        fprintf( pFile, "// [t_%d = %s] //", iObj, (char *)Vec_PtrEntry(vNames, iObj) );
        Prev = Pos;
    }
    Vec_IntFree( vPlaces );
    pName = strstr(pBuffer, "endmodule");
    Pos2 = pName - pBuffer;
    for ( k = Prev; k < Pos2; k++ )
        fputc( pBuffer[k], pFile );
    fprintf( pFile, "\n\n" );
    fprintf( pFile, "  wire " );
    Vec_PtrForEachEntry( char *, vNames, pName, i )
        fprintf( pFile, " t_%d%s", i, i==Vec_PtrSize(vNames)-1 ? ";" : "," );
    fprintf( pFile, "\n\n" );
    Vec_PtrForEachEntry( char *, vNames, pName, i )
        fprintf( pFile, "  buf( %s, t_%d );\n", pName, i );
    fprintf( pFile, "\n" );
    for ( k = Pos2; pBuffer[k]; k++ )
        fputc( pBuffer[k], pFile );
    ABC_FREE( pBuffer );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkRunSim( char * pFileName[4], int nWords, int nBeam, int LevL, int LevU, int fOrder, int fFancy, int fVerbose )
{
    extern int Gia_Sim4Try( char * pFileName0, char * pFileName1, char * pFileName2, int nWords, int nBeam, int LevL, int LevU, int fOrder, int fFancy, int fVerbose );
    extern void Acb_NtkRunEco( char * pFileNames[4], int fCheck, int fVerbose );
    char * pFileNames[4] = { pFileName[2], pFileName[1], NULL, pFileName[2] };
    if ( Gia_Sim4Try( pFileName[0], pFileName[1], pFileName[2], nWords, nBeam, LevL, LevU, fOrder, fFancy, fVerbose ) )
        Acb_NtkRunEco( pFileNames, 1, fVerbose );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

