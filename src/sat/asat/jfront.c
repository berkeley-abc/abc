/**CFile****************************************************************

  FileName    [jfront.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [C-language MiniSat solver.]

  Synopsis    [Implementation of J-frontier.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: jfront.c,v 1.4 2005/09/16 22:55:03 casem Exp $]

***********************************************************************/

#include <stdio.h>
#include <assert.h>
#include "solver.h"
#include "extra.h"
#include "vec.h"

/*
    At any time during the solving process, the J-frontier is the set of currently 
    unassigned variables, each of which has at least one fanin/fanout variable that 
    is currently assigned. In the context of a CNF-based solver, default decisions 
    based on variable activity are modified to choose the most active variable among 
    those currently on the J-frontier.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// variable on the J-frontier
typedef struct Asat_JVar_t_  Asat_JVar_t;
struct Asat_JVar_t_
{
    unsigned int       Num;      // variable number
    unsigned int       nRefs;    // the number of adjacent assigned vars
    unsigned int       Prev;     // the previous variable
    unsigned int       Next;     // the next variable
    unsigned int       nFans;    // the number of fanins/fanouts
    unsigned int       Fans[0];  // the fanin/fanout variables
};

// the J-frontier as a ring of variables
// (ring is used instead of list because it allows to control the insertion point)
typedef struct Asat_JRing_t_ Asat_JRing_t;
struct Asat_JRing_t_
{
    Asat_JVar_t *        pRoot;    // the pointer to the root
    int                  nItems;   // the number of variables in the ring
};

// the J-frontier manager
struct Asat_JMan_t_
{
    solver *             pSat;     // the SAT solver
    Asat_JRing_t         rVars;    // the ring of variables
    Vec_Ptr_t *          vVars;    // the pointers to variables
    Extra_MmFlex_t *     pMem;     // the memory manager for variables
};

// getting hold of the given variable
static inline Asat_JVar_t * Asat_JManVar( Asat_JMan_t * p, int Num )              { return !Num? NULL : Vec_PtrEntry(p->vVars, Num); }
static inline Asat_JVar_t * Asat_JVarPrev( Asat_JMan_t * p, Asat_JVar_t * pVar )  { return Asat_JManVar(p, pVar->Prev); }
static inline Asat_JVar_t * Asat_JVarNext( Asat_JMan_t * p, Asat_JVar_t * pVar )  { return Asat_JManVar(p, pVar->Next); }

//The solver can communicate to the variable order the following parts:
//- the array of current assignments (pSat->pAssigns)
//- the array of variable activities (pSat->pdActivity)
//- the array of variables currently in the cone 
//- the array of arrays of variables adjacent to each other

static inline int Asat_JVarIsInBoundary( Asat_JMan_t * p, Asat_JVar_t * pVar )  { return pVar->Next > 0;                         }
static inline int Asat_JVarIsAssigned( Asat_JMan_t * p, Asat_JVar_t * pVar )    { return p->pSat->assigns[pVar->Num] != l_Undef; }
//static inline int Asat_JVarIsUsedInCone( Asat_JMan_t * p, int Var )  { return p->pSat->vVarsUsed->pArray[i];    }

// manipulating the ring of variables
static void Asat_JRingAddLast( Asat_JMan_t * p, Asat_JVar_t * pVar );
static void Asat_JRingRemove( Asat_JMan_t * p, Asat_JVar_t * pVar );

// iterator through the entries in J-boundary
#define Asat_JRingForEachEntry( p, pVar, pNext )                \
    for ( pVar = p->rVars.pRoot,                                \
          pNext = pVar? Asat_JVarNext(p, pVar) : NULL;          \
          pVar;                                                 \
          pVar = (pNext != p->rVars.pRoot)? pNext : NULL,       \
          pNext = pVar? Asat_JVarNext(p, pVar) : NULL )

// iterator through the adjacent variables
#define Asat_JVarForEachFanio( p, pVar, pFan, i )               \
    for ( i = 0; (i < (int)pVar->nFans) && (((pFan) = Asat_JManVar(p, pVar->Fans[i])), 1); i++ )

extern void Asat_JManAssign( Asat_JMan_t * p, int Var );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Start the J-frontier.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Asat_JMan_t * Asat_JManStart( solver * pSat, void * pCircuit )
{
    Vec_Vec_t * vCircuit = pCircuit;
    Asat_JMan_t * p;
    Asat_JVar_t * pVar;
    Vec_Int_t * vConnect;
    int i, nBytes, Entry, k;
    // make sure the number of variables is less than sizeof(unsigned int)
    assert( Vec_VecSize(vCircuit) < (1 << 16) );
    assert( Vec_VecSize(vCircuit) == pSat->size );
    // allocate the manager
    p = ALLOC( Asat_JMan_t, 1 );
    memset( p, 0, sizeof(Asat_JMan_t) );
    p->pSat = pSat;
    p->pMem = Extra_MmFlexStart();
    // fill in the variables
    p->vVars = Vec_PtrAlloc( Vec_VecSize(vCircuit) );
    for ( i = 0; i < Vec_VecSize(vCircuit); i++ )
    {
        vConnect = Vec_VecEntry( vCircuit, i );
        nBytes = sizeof(Asat_JVar_t) + sizeof(int) * Vec_IntSize(vConnect);
        nBytes = sizeof(void *) * (nBytes / sizeof(void *) + ((nBytes % sizeof(void *)) != 0));
        pVar = (Asat_JVar_t *)Extra_MmFlexEntryFetch( p->pMem, nBytes );
        memset( pVar, 0, nBytes );
        pVar->Num = i;
        // add fanins/fanouts
        pVar->nFans = Vec_IntSize( vConnect );
        Vec_IntForEachEntry( vConnect, Entry, k )
            pVar->Fans[k] = Entry;
        // add the variable
        Vec_PtrPush( p->vVars, pVar );
    }
    // set the current assignments
    Vec_PtrForEachEntryStart( p->vVars, pVar, i, 1 )
    {
//      if ( !Asat_JVarIsUsedInCone(p, pVar) )
//          continue;
        // skip assigned vars, vars in the boundary, and vars not used in the cone
        if ( Asat_JVarIsAssigned(p, pVar) )
            Asat_JManAssign( p, pVar->Num );
    }

    pSat->pJMan = p;
    return p;
}   

/**Function*************************************************************

  Synopsis    [Stops the J-frontier.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Asat_JManStop( solver * pSat )
{
    Asat_JMan_t * p = pSat->pJMan;
    if ( p == NULL )
        return;
    pSat->pJMan = NULL;
    Extra_MmFlexStop( p->pMem, 0 );
    Vec_PtrFree( p->vVars );
    free( p );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Asat_JManCheck( Asat_JMan_t * p )
{
    Asat_JVar_t * pVar, * pNext, * pFan;
//    Msat_IntVec_t * vRound;
//    int * pRound, nRound;
//    int * pVars, nVars, i, k;
    int i, k;
    int Counter = 0;

    // go through all the variables in the boundary
    Asat_JRingForEachEntry( p, pVar, pNext )
    {
        assert( !Asat_JVarIsAssigned(p, pVar) );
        // go though all the variables in the neighborhood
        // and check that it is true that there is least one assigned
//        vRound = (Msat_IntVec_t *)Msat_ClauseVecReadEntry( p->pSat->vAdjacents, pVar->Num );
//        nRound = Msat_IntVecReadSize( vRound );
//        pRound = Msat_IntVecReadArray( vRound );
//        for ( i = 0; i < nRound; i++ )
        Asat_JVarForEachFanio( p, pVar, pFan, i )
        {
//            if ( !Asat_JVarIsUsedInCone(p, pFan) )
//                continue;
            if ( Asat_JVarIsAssigned(p, pFan) )
                break;
        }
//        assert( i != pVar->nFans );
//        if ( i == pVar->nFans )
//            return 0;
        if ( i == (int)pVar->nFans )
            Counter++;
    }
    if ( Counter > 0 )
        printf( "%d(%d) ", Counter, p->rVars.nItems );

    // we may also check other unassigned variables in the cone
    // to make sure that if they are not in J-boundary, 
    // then they do not have an assigned neighbor
//    nVars = Msat_IntVecReadSize( p->pSat->vConeVars );
//    pVars = Msat_IntVecReadArray( p->pSat->vConeVars );
//    for ( i = 0; i < nVars; i++ )
    Vec_PtrForEachEntry( p->vVars, pVar, i )
    {
//        assert( Asat_JVarIsUsedInCone(p, pVar) );
        // skip assigned vars, vars in the boundary, and vars not used in the cone
        if ( Asat_JVarIsAssigned(p, pVar) || Asat_JVarIsInBoundary(p, pVar) )
            continue;
        // make sure, it does not have assigned neighbors
//        vRound = (Msat_IntVec_t *)Msat_ClauseVecReadEntry( p->pSat->vAdjacents, pVars[i] );
//        nRound = Msat_IntVecReadSize( vRound );
//        pRound = Msat_IntVecReadArray( vRound );
//        for ( i = 0; i < nRound; i++ )
        Asat_JVarForEachFanio( p, pVar, pFan, k )
        {
//            if ( !Asat_JVarIsUsedInCone(p, pFan) )
//                continue;
            if ( Asat_JVarIsAssigned(p, pFan) )
                break;
        }
//        assert( k == pVar->nFans );
//        if ( k != pVar->nFans )
//            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Asat_JManAssign( Asat_JMan_t * p, int Var )
{
//    Msat_IntVec_t * vRound;
    Asat_JVar_t * pVar, * pFan;
    int i, clk = clock();

    // make sure the variable is in the boundary
    assert( Var < Vec_PtrSize(p->vVars) );
    // if it is not in the boundary (initial decision, random decision), do not remove
    pVar = Asat_JManVar( p, Var );
    if ( Asat_JVarIsInBoundary( p, pVar ) )
        Asat_JRingRemove( p, pVar );
    // add to the boundary those neighbors that are (1) unassigned, (2) not in boundary
    // because for them we know that there is a variable (Var) which is assigned
//    vRound = (Msat_IntVec_t *)p->pSat->vAdjacents->pArray[Var];
//    for ( i = 0; i < vRound->nSize; i++ )
    Asat_JVarForEachFanio( p, pVar, pFan, i )
    {
//        if ( !Asat_JVarIsUsedInCone(p, pFan) )
//            continue;
        pFan->nRefs++;
        if ( Asat_JVarIsAssigned(p, pFan) || Asat_JVarIsInBoundary(p, pFan) )
            continue;
        Asat_JRingAddLast( p, pFan );
    }
//timeSelect += clock() - clk;
//    Asat_JManCheck( p );
    p->pSat->timeUpdate += clock() - clk;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Asat_JManUnassign( Asat_JMan_t * p, int Var )
{
//    Msat_IntVec_t * vRound, * vRound2;
    Asat_JVar_t * pVar, * pFan;
    int i, clk = clock();//, k

    // make sure the variable is not in the boundary
    assert( Var < Vec_PtrSize(p->vVars) );
    pVar = Asat_JManVar( p, Var );
    assert( !Asat_JVarIsInBoundary( p, pVar ) );
    // go through its neigbors - if one of them is assigned add this var
    // add to the boundary those neighbors that are not there already
    // this will also get rid of variable outside of the current cone
    // because they are unassigned in Msat_SolverPrepare()
//    vRound = (Msat_IntVec_t *)p->pSat->vAdjacents->pArray[Var];
//    for ( i = 0; i < vRound->nSize; i++ )
//        if ( Asat_JVarIsAssigned(p, vRound->pArray[i]) ) 
//            break;
//    if ( i != vRound->nSize )
//        Asat_JRingAddLast( &p->rVars, &p->pVars[Var] );
    if ( pVar->nRefs != 0 )
        Asat_JRingAddLast( p, pVar );

/*
    // unassigning a variable may lead to its adjacents dropping from the boundary
    for ( i = 0; i < vRound->nSize; i++ )
        if ( Asat_JVarIsInBoundary(p, vRound->pArray[i]) )
        { // the neighbor is in the J-boundary (and unassigned)
            assert( !Asat_JVarIsAssigned(p, vRound->pArray[i]) );
            vRound2 = (Msat_IntVec_t *)p->pSat->vAdjacents->pArray[vRound->pArray[i]];
            // go through its neighbors and determine if there is at least one assigned
            for ( k = 0; k < vRound2->nSize; k++ )
                if ( Asat_JVarIsAssigned(p, vRound2->pArray[k]) ) 
                    break;
            if ( k == vRound2->nSize ) // there is no assigned vars, delete this one
                Asat_JRingRemove( &p->rVars, &p->pVars[vRound->pArray[i]] );
        }
*/
    Asat_JVarForEachFanio( p, pVar, pFan, i )
    {
//        if ( !Asat_JVarIsUsedInCone(p, pFan) )
//            continue;
        assert( pFan->nRefs > 0 );
        pFan->nRefs--;
        if ( !Asat_JVarIsInBoundary(p, pFan) )
            continue;
        // the neighbor is in the J-boundary (and unassigned)
        assert( !Asat_JVarIsAssigned(p, pFan) );
        // if there is no assigned vars, delete this one
        if ( pFan->nRefs == 0 )
            Asat_JRingRemove( p, pFan );
    }

//timeSelect += clock() - clk;
//    Asat_JManCheck( p );
    p->pSat->timeUpdate += clock() - clk;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Asat_JManSelect( Asat_JMan_t * p )
{
    Asat_JVar_t * pVar, * pNext, * pVarBest;
    double * pdActs = p->pSat->activity;
    double dfActBest;
    int clk = clock();

    pVarBest = NULL;
    dfActBest = -1.0;
    Asat_JRingForEachEntry( p, pVar, pNext )
    {
        if ( dfActBest <= pdActs[pVar->Num] )//+ 0.00001 )
        {
            dfActBest = pdActs[pVar->Num];
            pVarBest  = pVar;
        }
    }
//timeSelect += clock() - clk;
//timeAssign += clock() - clk;
//if ( pVarBest && pVarBest->Num % 1000 == 0 )
//printf( "%d ", p->rVars.nItems );

//    Asat_JManCheck( p );
    p->pSat->timeSelect += clock() - clk;
    if ( pVarBest )
    {
//        assert( Asat_JVarIsUsedInCone(p, pVarBest) );
        return pVarBest->Num;
    }
    return var_Undef;
}



/**Function*************************************************************

  Synopsis    [Adds node to the end of the ring.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Asat_JRingAddLast( Asat_JMan_t * p, Asat_JVar_t * pVar )
{
    Asat_JRing_t * pRing = &p->rVars;
//printf( "adding %d\n", pVar->Num );
    // check that the node is not in a ring
    assert( pVar->Prev == 0 );
    assert( pVar->Next == 0 );
    // if the ring is empty, make the node point to itself
    pRing->nItems++;
    if ( pRing->pRoot == NULL )
    {
        pRing->pRoot = pVar;
//        pVar->pPrev  = pVar;
        pVar->Prev   = pVar->Num;
//        pVar->pNext  = pVar;
        pVar->Next   = pVar->Num;
        return;
    }
    // if the ring is not empty, add it as the last entry
//    pVar->pPrev = pRing->pRoot->pPrev;
    pVar->Prev = pRing->pRoot->Prev;
//    pVar->pNext = pRing->pRoot;
    pVar->Next = pRing->pRoot->Num;
//    pVar->pPrev->pNext = pVar;
    Asat_JVarPrev(p, pVar)->Next = pVar->Num;
//    pVar->pNext->pPrev = pVar;
    Asat_JVarNext(p, pVar)->Prev = pVar->Num;

    // move the root so that it points to the new entry
//    pRing->pRoot = pRing->pRoot->pPrev;
    pRing->pRoot = Asat_JVarPrev(p, pRing->pRoot);
}

/**Function*************************************************************

  Synopsis    [Removes the node from the ring.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Asat_JRingRemove( Asat_JMan_t * p, Asat_JVar_t * pVar )
{
    Asat_JRing_t * pRing = &p->rVars;
//printf( "removing %d\n", pVar->Num );
    // check that the var is in a ring
    assert( pVar->Prev );
    assert( pVar->Next );
    pRing->nItems--;
    if ( pRing->nItems == 0 )
    {
        assert( pRing->pRoot == pVar );
//        pVar->pPrev = NULL;
        pVar->Prev = 0;
//        pVar->pNext = NULL;
        pVar->Next = 0;
        pRing->pRoot = NULL;
        return;
    }
    // move the root if needed
    if ( pRing->pRoot == pVar )
//        pRing->pRoot = pVar->pNext;
        pRing->pRoot = Asat_JVarNext(p, pVar);
    // move the root to the next entry after pVar
    // this way all the additions to the list will be traversed first
//    pRing->pRoot = pVar->pNext;
    pRing->pRoot = Asat_JVarPrev(p, pVar);
    // delete the node
//    pVar->pPrev->pNext = pVar->pNext;
    Asat_JVarPrev(p, pVar)->Next = Asat_JVarNext(p, pVar)->Num;
//    pVar->pNext->pPrev = pVar->pPrev;
    Asat_JVarNext(p, pVar)->Prev = Asat_JVarPrev(p, pVar)->Num;
//    pVar->pPrev = NULL;
    pVar->Prev = 0;
//    pVar->pNext = NULL;
    pVar->Next = 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


