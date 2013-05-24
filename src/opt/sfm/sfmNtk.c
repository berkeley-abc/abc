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
void Sfm_CreateLevel( Vec_Wec_t * vFanins, Vec_Int_t * vLevels )
{
    Vec_Int_t * vArray;
    int i, k, Fanin, * pLevels;
    Vec_IntFill( vLevels, Vec_WecSize(vFanins), 0 );
    pLevels = Vec_IntArray( vLevels );
    Vec_WecForEachLevel( vFanins, vArray, i )
        Vec_IntForEachEntry( vArray, Fanin, k )
            pLevels[i] = Abc_MaxInt( pLevels[i], pLevels[Fanin] + 1 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Sfm_CreateCnf( Sfm_Ntk_t * p )
{
    Vec_Wec_t * vCnfs;
    Vec_Str_t * vCnf, * vCnfBase;
    word uTruth;
    int i;
    vCnf = Vec_StrAlloc( 100 );
    vCnfs = Vec_WecStart( p->nObjs );
    Vec_WrdForEachEntryStartStop( p->vTruths, uTruth, i, p->nPis, Vec_WrdSize(p->vTruths)-p->nPos )
    {
        Sfm_TruthToCnf( uTruth, Sfm_ObjFaninNum(p, i), p->vCover, vCnf );
        vCnfBase = (Vec_Str_t *)Vec_WecEntry( vCnfs, i );
        Vec_StrGrow( vCnfBase, Vec_StrSize(vCnf) );
        memcpy( Vec_StrArray(vCnfBase), Vec_StrArray(vCnf), Vec_StrSize(vCnf) );
        vCnfBase->nSize = Vec_StrSize(vCnf);
    }
    Vec_StrFree( vCnf );
    return vCnfs;
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
    Vec_IntFill( &p->vCounts, p->nObjs, 0 );
    Vec_IntFill( &p->vTravIds, p->nObjs, 0 );
    Vec_IntFill( &p->vTravIds2, p->nObjs, 0 );
    Vec_IntFill( &p->vId2Var, p->nObjs, -1 );
    Vec_IntFill( &p->vVar2Id, p->nObjs, -1 );
    p->vCover   = Vec_IntAlloc( 1 << 16 );
    p->vCnfs    = Sfm_CreateCnf( p );
    return p;
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
    Vec_IntFreeP( &p->vRoots );
    Vec_IntFreeP( &p->vNodes );
    Vec_IntFreeP( &p->vTfo   );
    Vec_IntFreeP( &p->vDivs  );
    Vec_IntFreeP( &p->vDivIds );
    Vec_IntFreeP( &p->vLits  );
    Vec_IntFreeP( &p->vDiffs  );
    Vec_WecFreeP( &p->vClauses );
    Vec_IntFreeP( &p->vFaninMap );
    if ( p->pSat0 ) sat_solver_delete( p->pSat0 );
    if ( p->pSat1 ) sat_solver_delete( p->pSat1 );
    ABC_FREE( p );
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
word Sfm_NodeReadTruth( Sfm_Ntk_t * p, int i )
{
    return Vec_WrdEntry( p->vTruths, i );
}
int Sfm_NodeReadFixed( Sfm_Ntk_t * p, int i )
{
    return (int)Vec_StrEntry( p->vFixed, i );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

