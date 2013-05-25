/**CFile****************************************************************

  FileName    [sfmNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Logic network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmNtk.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"

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
void Sfm_CheckConsistency( Vec_Wec_t * vFanins, int nPis, int nPos, Vec_Str_t * vFixed )
{
    Vec_Int_t * vArray;
    int i, k, Fanin;
    // check entries
    Vec_WecForEachLevel( vFanins, vArray, i )
    {
        // PIs have no fanins
        if ( i < nPis )
            assert( Vec_IntSize(vArray) == 0 && Vec_StrEntry(vFixed, i) == (char)0 );
        // nodes are in a topo order; POs cannot be fanins
        Vec_IntForEachEntry( vArray, Fanin, k )
            assert( Fanin < i && Fanin + nPos < Vec_WecSize(vFanins) );
        // POs have one fanout
        if ( i + nPos >= Vec_WecSize(vFanins) )
            assert( Vec_IntSize(vArray) == 1 && Vec_StrEntry(vFixed, i) == (char)0 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_CreateFanout( Vec_Wec_t * vFanins, Vec_Wec_t * vFanouts )
{
    Vec_Int_t * vArray;
    int i, k, Fanin;
    // count fanouts
    Vec_WecInit( vFanouts, Vec_WecSize(vFanins) );
    Vec_WecForEachLevel( vFanins, vArray, i )
        Vec_IntForEachEntry( vArray, Fanin, k )
            Vec_WecEntry( vFanouts, Fanin )->nSize++;
    // allocate fanins
    Vec_WecForEachLevel( vFanouts, vArray, i )
    {
        k = vArray->nSize; vArray->nSize = 0;
        Vec_IntGrow( vArray, k );
    }
    // add fanouts
    Vec_WecForEachLevel( vFanins, vArray, i )
        Vec_IntForEachEntry( vArray, Fanin, k )
            Vec_IntPush( Vec_WecEntry( vFanouts, Fanin ), i );
    // verify
    Vec_WecForEachLevel( vFanouts, vArray, i )
        assert( Vec_IntSize(vArray) == Vec_IntCap(vArray) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sfm_ObjCreateLevel( Vec_Int_t * vArray, Vec_Int_t * vLevels )
{
    int k, Fanin, Level = 0;
    Vec_IntForEachEntry( vArray, Fanin, k )
        Level = Abc_MaxInt( Level, Vec_IntEntry(vLevels, Fanin) + 1 );
    return Level;
}
void Sfm_CreateLevel( Vec_Wec_t * vFanins, Vec_Int_t * vLevels )
{
    Vec_Int_t * vArray;
    int i;
    assert( Vec_IntSize(vLevels) == 0 );
    Vec_IntGrow( vLevels, Vec_WecSize(vFanins) );
    Vec_WecForEachLevel( vFanins, vArray, i )
        Vec_IntPush( vLevels, Sfm_ObjCreateLevel(vArray, vLevels) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sfm_Ntk_t * Sfm_NtkConstruct( Vec_Wec_t * vFanins, int nPis, int nPos, Vec_Str_t * vFixed, Vec_Wrd_t * vTruths )
{
    Sfm_Ntk_t * p;
    Sfm_CheckConsistency( vFanins, nPis, nPos, vFixed );
    p = ABC_CALLOC( Sfm_Ntk_t, 1 );
    p->nObjs    = Vec_WecSize( vFanins );
    p->nPis     = nPis;
    p->nPos     = nPos;
    p->nNodes   = p->nObjs - p->nPis - p->nPos;
    // user data
    p->vFixed   = vFixed;
    p->vTruths  = vTruths;
    p->vFanins  = *vFanins;
    ABC_FREE( vFanins );
    // attributes
    Sfm_CreateFanout( &p->vFanins, &p->vFanouts );
    Sfm_CreateLevel( &p->vFanins, &p->vLevels );
    Vec_IntFill( &p->vCounts,   p->nObjs,  0 );
    Vec_IntFill( &p->vTravIds,  p->nObjs,  0 );
    Vec_IntFill( &p->vTravIds2, p->nObjs,  0 );
    Vec_IntFill( &p->vId2Var,   p->nObjs, -1 );
    Vec_IntFill( &p->vVar2Id,   p->nObjs, -1 );
    p->vCover   = Vec_IntAlloc( 1 << 16 );
    p->vCnfs    = Sfm_CreateCnf( p );
    return p;
}
void Sfm_NtkPrepare( Sfm_Ntk_t * p )
{
    p->vLeaves   = Vec_IntAlloc( 1000 );
    p->vNodes    = Vec_IntAlloc( 1000 );
    p->vDivs     = Vec_IntAlloc( 100 );
    p->vRoots    = Vec_IntAlloc( 1000 );
    p->vTfo      = Vec_IntAlloc( 1000 );
    p->vDivCexes = Vec_WrdStart( p->pPars->nDivNumMax );
//    p->vFans     = Vec_IntAlloc( 100 );
    p->vOrder    = Vec_IntAlloc( 100 );
    p->vDivVars  = Vec_IntAlloc( 100 );
    p->vDivIds   = Vec_IntAlloc( 1000 );
    p->vLits     = Vec_IntAlloc( 100 );
    p->vClauses  = Vec_WecAlloc( 100 );
    p->vFaninMap = Vec_IntAlloc( 10 );
}
void Sfm_NtkFree( Sfm_Ntk_t * p )
{
    // user data
    Vec_StrFree( p->vFixed );
    Vec_WrdFree( p->vTruths );
    Vec_WecErase( &p->vFanins );
    // attributes
    Vec_WecErase( &p->vFanouts );
    ABC_FREE( p->vLevels.pArray );
    ABC_FREE( p->vCounts.pArray );
    ABC_FREE( p->vTravIds.pArray );
    ABC_FREE( p->vTravIds2.pArray );
    ABC_FREE( p->vId2Var.pArray );
    ABC_FREE( p->vVar2Id.pArray );
    Vec_WecFree( p->vCnfs );
    Vec_IntFree( p->vCover );
    // other data
    Vec_IntFreeP( &p->vLeaves );
    Vec_IntFreeP( &p->vNodes );
    Vec_IntFreeP( &p->vDivs  );
    Vec_IntFreeP( &p->vRoots );
    Vec_IntFreeP( &p->vTfo   );
    Vec_WrdFreeP( &p->vDivCexes );
//    Vec_IntFreeP( &p->vFans );
    Vec_IntFreeP( &p->vOrder );
    Vec_IntFreeP( &p->vDivVars );
    Vec_IntFreeP( &p->vDivIds );
    Vec_IntFreeP( &p->vLits  );
    Vec_WecFreeP( &p->vClauses );
    Vec_IntFreeP( &p->vFaninMap );
    if ( p->pSat0 ) sat_solver_delete( p->pSat0 );
    if ( p->pSat1 ) sat_solver_delete( p->pSat1 );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Performs resubstitution for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkRemoveFanin( Sfm_Ntk_t * p, int iNode, int iFanin )
{
    int RetValue;
    RetValue = Vec_IntRemove( Sfm_ObjFiArray(p, iNode), iFanin );
    assert( RetValue );
    RetValue = Vec_IntRemove( Sfm_ObjFoArray(p, iFanin), iNode );
    assert( RetValue );
}
void Sfm_NtkAddFanin( Sfm_Ntk_t * p, int iNode, int iFanin )
{
    if ( iFanin < 0 )
        return;
    assert( Vec_IntFind( Sfm_ObjFiArray(p, iNode), iFanin ) == -1 );
    assert( Vec_IntFind( Sfm_ObjFoArray(p, iFanin), iNode ) == -1 );
    Vec_IntPush( Sfm_ObjFiArray(p, iNode), iFanin );
    Vec_IntPush( Sfm_ObjFoArray(p, iFanin), iNode );
}
void Sfm_NtkDeleteObj_rec( Sfm_Ntk_t * p, int iNode )
{
    int i, iFanin;
    if ( iNode == 202 )
    {
        int s = 0;
    }
    if ( Sfm_ObjFanoutNum(p, iNode) > 0 || Sfm_ObjIsPi(p, iNode) )
        return;
    assert( Sfm_ObjIsNode(p, iNode) );
    Sfm_ObjForEachFanin( p, iNode, iFanin, i )
    {
        int RetValue = Vec_IntRemove( Sfm_ObjFoArray(p, iFanin), iNode );  assert( RetValue );
        if ( Sfm_ObjFanoutNum(p, iFanin) == 0 )
            Sfm_NtkDeleteObj_rec( p, iFanin );
    }
    Vec_IntClear( Sfm_ObjFiArray(p, iNode) );
}
void Sfm_NtkUpdateLevel_rec( Sfm_Ntk_t * p, int iNode )
{
    int i, iFanout;
    int LevelNew = Sfm_ObjCreateLevel( Sfm_ObjFiArray(p, iNode), &p->vLevels );
    if ( LevelNew == Sfm_ObjLevel(p, iNode) )
        return;
    Sfm_ObjSetLevel( p, iNode, LevelNew );
    if ( Sfm_ObjIsNode(p, iNode) )
        Sfm_ObjForEachFanout( p, iNode, iFanout, i )
            Sfm_NtkUpdateLevel_rec( p, iFanout );
}
void Sfm_NtkUpdate( Sfm_Ntk_t * p, int iNode, int f, int iFaninNew, word uTruth )
{
    int iFanin = Sfm_ObjFanin( p, iNode, f );
    // replace old fanin by new fanin
    assert( Sfm_ObjIsNode(p, iNode) );
    Sfm_NtkRemoveFanin( p, iNode, iFanin );
    Sfm_NtkAddFanin( p, iNode, iFaninNew );
    // recursively remove MFFC
    Sfm_NtkDeleteObj_rec( p, iFanin );
    // update logic level
    Sfm_NtkUpdateLevel_rec( p, iNode );
    // update truth table
    Vec_WrdWriteEntry( p->vTruths, iNode, uTruth );
    Sfm_TruthToCnf( uTruth, Sfm_ObjFaninNum(p, iNode), p->vCover, (Vec_Str_t *)Vec_WecEntry(p->vCnfs, iNode) );
}

/**Function*************************************************************

  Synopsis    [Public APIs of this network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t *  Sfm_NodeReadFanins( Sfm_Ntk_t * p, int i )
{
    return Vec_WecEntry( &p->vFanins, i );
}
word * Sfm_NodeReadTruth( Sfm_Ntk_t * p, int i )
{
    return Vec_WrdEntryP( p->vTruths, i );
}
int Sfm_NodeReadFixed( Sfm_Ntk_t * p, int i )
{
    return (int)Vec_StrEntry( p->vFixed, i );
}
int Sfm_NodeReadUsed( Sfm_Ntk_t * p, int i )
{
    return (Sfm_ObjFaninNum(p, i) > 0) || (Sfm_ObjFanoutNum(p, i) > 0);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

