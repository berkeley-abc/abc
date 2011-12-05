/**CFile****************************************************************

  FileName    [satProof.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT solver.]

  Synopsis    [Proof manipulation procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: satProof.c,v 1.4 2005/09/16 22:55:03 casem Exp $]

***********************************************************************/

#include "satSolver.h"
#include "vec.h"
#include "aig.h"

ABC_NAMESPACE_IMPL_START


/*
    Proof is represented as a vector of integers.
    The first entry is -1.
    The clause is represented as an offset in this array.
    One clause's entry is <size><label><ant1><ant2>...<antN>
    Label is initialized to 0.
    Root clauses are 1-based. They are marked by prepending bit 1;
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sat_Set_t_ Sat_Set_t;
struct Sat_Set_t_
{
    int nEnts;
    int Label;
    int pEnts[0];
};

static inline int          Sat_SetCheck( Vec_Int_t * p, Sat_Set_t * pNode ) { return (int *)pNode > Vec_IntArray(p) && (int *)pNode < Vec_IntLimit(p); }
static inline int          Sat_SetId( Vec_Int_t * p, Sat_Set_t * pNode )    { return (int *)pNode - Vec_IntArray(p);                                   }
static inline Sat_Set_t *  Sat_SetFromId( Vec_Int_t * p, int i )            { return (Sat_Set_t *)(Vec_IntArray(p) + i);                              }
static inline int          Sat_SetSize( Sat_Set_t * pNode )                 { return pNode->nEnts + 2;          }

#define Sat_PoolForEachSet( p, pNode, i )  \
    for ( i = 1; (i < Vec_IntSize(p)) && ((pNode) = Sat_SetFromId(p, Vec_IntEntry(p,i))); i += Sat_SetSize(pNode) )
#define Sat_SetForEachSet( p, pSet, pNode, i )  \
    for ( i = 0; (i < pSet->nEnts) && (((pNode) = ((pSet->pEnts[i] & 1) ? NULL : Sat_SetFromId(p, pSet->pEnts[i]))), 1); i++ )
#define Sat_VecForEachSet( pVec, p, pNode, i )  \
    for ( i = 0; (i < Vec_IntSize(pVec)) && ((pNode) = Sat_SetFromId(p, Vec_IntEntry(pVec,i))); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sat_ProofReduceOne( Vec_Int_t * p, Sat_Set_t * pNode, int * pnSize, Vec_Int_t * vStack )
{
    Sat_Set_t * pNext;
    int i, NodeId;
    if ( pNode->Label )
        return pNode->Label;
    // start with node
    pNode->Label = 1;
    Vec_IntPush( vStack, Sat_SetId(p, pNode) );
    // perform DFS search
    while ( Vec_IntSize(vStack) )
    {
        NodeId = Vec_IntPop( vStack );
        if ( NodeId & 1 ) // extrated second time
        {
            pNode = Sat_SetFromId( p, NodeId ^ 1 );
            pNode->Label = *pnSize;
            *pnSize += Sat_SetSize(pNode);
            // update fanins
            Sat_SetForEachSet( p, pNode, pNext, i )
                if ( pNext )
                    pNode->pEnts[i] = pNext->Label;
            continue;
        }
        // extracted first time
        // add second time
        Vec_IntPush( vStack, NodeId ^ 1 );
        // add its anticedents
        pNode = Sat_SetFromId( p, NodeId );
        Sat_SetForEachSet( p, pNode, pNext, i )
            if ( pNext && !pNext->Label )
            {
                pNext->Label = 1;
                Vec_IntPush( vStack, Sat_SetId(p, pNode) ); // add first time
            }
    }
    return pNode->Label;
}

/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*
int Sat_ProofReduce_rec( Vec_Int_t * p, Sat_Set_t * pNode, int * pnSize )
{
    int * pBeg;
    assert( Sat_SetCheck(p, pNode) );
    if ( pNode->Label )
        return pNode->Label;
    for ( pBeg = pNode->pEnts; pBeg < pNode->pEnts + pNode->nEnts; pBeg++ )
        if ( !(*pBeg & 1) )
            *pBeg = Sat_ProofReduce_rec( p, Sat_SetFromId(p, *pBeg), pnSize );
    pNode->Label = *pnSize;
    *pnSize += Sat_SetSize(pNode);
    return pNode->Label;
}
*/

/**Function*************************************************************

  Synopsis    [Reduces the proof to contain only roots and their children.]

  Description [The result is updated proof and updated roots.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_ProofReduce( Vec_Int_t * p, Vec_Int_t * vRoots )
{
    int i, nSize = 1;
    int * pBeg, * pEnd, * pNew;
    Vec_Int_t * vStack;
    Sat_Set_t * pNode;
    // mark used nodes
    vStack = Vec_IntAlloc( 1000 );
    Sat_VecForEachSet( vRoots, p, pNode, i )
        vRoots->pArray[i] = Sat_ProofReduceOne( p, pNode, &nSize, vStack );
    Vec_IntFree( vStack );
    // compact proof
    pNew = Vec_IntArray(p) + 1;
    Sat_PoolForEachSet( p, pNode, i )
    {
        if ( !pNode->Label )
            continue;
        assert( pNew - Vec_IntArray(p) == pNode->Label );
        pNode->Label = 0;
        pBeg = (int *)pNode;
        pEnd = pBeg + Sat_SetSize(pNode);
        while ( pBeg < pEnd )
            *pNew++ = *pBeg++;
    }
    // report the result
    printf( "The proof was reduced from %d to %d (by %6.2f %%)\n", 
        Vec_IntSize(p), nSize, 100.0 * (Vec_IntSize(p) - nSize) / Vec_IntSize(p) );
    assert( pNew - Vec_IntArray(p) == nSize );
    Vec_IntShrink( p, nSize );
}   

/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_ProofLabel( Vec_Int_t * p, Sat_Set_t * pNode, Vec_Int_t * vUsed, Vec_Int_t * vStack )
{
    Sat_Set_t * pNext;
    int i, NodeId;
    if ( pNode->Label )
        return;
    // start with node
    pNode->Label = 1;
    Vec_IntPush( vStack, Sat_SetId(p, pNode) );
    // perform DFS search
    while ( Vec_IntSize(vStack) )
    {
        NodeId = Vec_IntPop( vStack );
        if ( NodeId & 1 ) // extrated second time
        {
            Vec_IntPush( vUsed, NodeId ^ 1 );
            continue;
        }
        // extracted first time
        // add second time
        Vec_IntPush( vStack, NodeId ^ 1 );
        // add its anticedents
        pNode = Sat_SetFromId( p, NodeId );
        Sat_SetForEachSet( p, pNode, pNext, i )
            if ( pNext && !pNext->Label )
            {
                pNext->Label = 1;
                Vec_IntPush( vStack, Sat_SetId(p, pNode) ); // add first time
            }
    }
}

/**Function*************************************************************

  Synopsis    [Computes UNSAT core.]

  Description [The result is the array of root clause indexes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Sat_ProofCore( Vec_Int_t * p, int nRoots, int * pBeg, int * pEnd )
{
    unsigned * pSeen;
    Vec_Int_t * vCore, * vUsed, * vStack;
    Sat_Set_t * pNode;
    int i;
    // collect visited clauses
    vUsed = Vec_IntAlloc( 1000 );
    vStack = Vec_IntAlloc( 1000 );
    while ( pBeg < pEnd )
        Sat_ProofLabel( p, Sat_SetFromId(p, *pBeg++), vUsed, vStack );
    Vec_IntFree( vStack );
    // find the core
    vCore = Vec_IntAlloc( 1000 );
    pSeen = ABC_CALLOC( unsigned, Aig_BitWordNum(nRoots) );
    Sat_VecForEachSet( vUsed, p, pNode, i )
    {
        pNode->Label = 0;
        for ( pBeg = pNode->pEnts; pBeg < pNode->pEnts + pNode->nEnts; pBeg++ )
            if ( (*pBeg & 1) && !Aig_InfoHasBit(pBeg, *pBeg>>1) )
            {
                Aig_InfoSetBit( pBeg, *pBeg>>1 );
                Vec_IntPush( vCore, (*pBeg>>1)-1 );
            }
    }
    Vec_IntFree( vUsed );
    ABC_FREE( pSeen );
    return vCore;
}


/**Function*************************************************************

  Synopsis    [Performs one resultion step.]

  Description [Returns ID of the resolvent if success, and -1 if failure.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sat_Set_t * Sat_ProofResolve( Vec_Int_t * p, Sat_Set_t * c1, Sat_Set_t * c2 )
{
    int i, k, Id, Var = -1, Count = 0;
    // find resolution variable
    for ( i = 0; i < c1->nEnts; i++ )
    for ( k = 0; k < c2->nEnts; k++ )
        if ( (c1->pEnts[i] ^ c2->pEnts[k]) == 1 )
        {
            Var = (c1->pEnts[i] >> 1);
            Count++;
        }
    if ( Count == 0 )
    {
        printf( "Cannot find resolution variable\n" );
        return NULL;
    }
    if ( Count > 1 )
    {
        printf( "Found more than 1 resolution variables\n" );
        return NULL;
    }
    // perform resolution
    Id = Vec_IntSize( p );
    Vec_IntPush( p, 0 ); // placeholder
    Vec_IntPush( p, 0 );
    for ( i = 0; i < c1->nEnts; i++ )
    {
        if ( (c1->pEnts[i] >> 1) == Var )
            continue;
        for ( k = Id + 2; k < Vec_IntSize(p); k++ )
            if ( p->pArray[k] == c1->pEnts[i] )
                break;
        if ( k == Vec_IntSize(p) )
            Vec_IntPush( p, c1->pEnts[i] );
    }
    for ( i = 0; i < c2->nEnts; i++ )
    {
        if ( (c2->pEnts[i] >> 1) == Var )
            continue;
        for ( k = Id + 2; k < Vec_IntSize(p); k++ )
            if ( p->pArray[k] == c2->pEnts[i] )
                break;
        if ( k == Vec_IntSize(p) )
            Vec_IntPush( p, c2->pEnts[i] );
    }
    Vec_IntWriteEntry( p, Id, Vec_IntSize(p) - Id - 2 );
    return Sat_SetFromId( p, Id );
}

/**Function*************************************************************

  Synopsis    [Checks the proof for consitency.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sat_Set_t * Sat_ProofCheckGetOne( Vec_Int_t * vClauses, Vec_Int_t * vProof, Vec_Int_t * vResolves, int iAnt )
{
    Sat_Set_t * pAnt;
    if ( iAnt & 1 )
        return Sat_SetFromId( vClauses, iAnt >> 1 );
    pAnt = Sat_SetFromId( vProof, iAnt );
    return Sat_SetFromId( vResolves, pAnt->Label );
}

/**Function*************************************************************

  Synopsis    [Checks the proof for consitency.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_ProofCheck( Vec_Int_t * vClauses, Vec_Int_t * vProof, int iRoot )
{
    Vec_Int_t * vOrigs, * vStack, * vUsed, * vResolves;
    Sat_Set_t * pSet, * pSet0, * pSet1;
    int i, k;
    // collect original clauses
    vOrigs = Vec_IntAlloc( 1000 );
    Vec_IntPush( vOrigs, -1 );
    Sat_PoolForEachSet( vClauses, pSet, i )
        Vec_IntPush( vOrigs, Sat_SetId(vClauses, pSet) );
    // collect visited clauses
    vUsed = Vec_IntAlloc( 1000 );
    vStack = Vec_IntAlloc( 1000 );
    Sat_ProofLabel( vProof, Sat_SetFromId(vProof, iRoot), vUsed, vStack );
    Vec_IntFree( vStack );
    // perform resolution steps
    vResolves = Vec_IntAlloc( 1000 );
    Vec_IntPush( vResolves, -1 );
    Sat_VecForEachSet( vUsed, vProof, pSet, i )
    {
        pSet0 = Sat_ProofCheckGetOne( vOrigs, vProof, vResolves, pSet->pEnts[0] );
        for ( k = 1; k < pSet->nEnts; k++ )
        {
            pSet1 = Sat_ProofCheckGetOne( vOrigs, vProof, vResolves, pSet->pEnts[k] );
            pSet0 = Sat_ProofResolve( vResolves, pSet0, pSet1 );
        }
        pSet->Label = Sat_SetId( vResolves, pSet0 );
    }
    // clean the proof
    Sat_VecForEachSet( vUsed, vProof, pSet, i )
        pSet->Label = 0;
    // compare the final clause
    if ( pSet0->nEnts > 0 )
        printf( "Cound not derive the empty clause\n" );
    Vec_IntFree( vResolves );
    Vec_IntFree( vUsed );
    Vec_IntFree( vOrigs );
}


/**Function*************************************************************

  Synopsis    [Creates variable map.]

  Description [1=A, 2=B, neg=global]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_ProofVarMapCheck( Vec_Int_t * vClauses, Vec_Int_t * vVarMap )
{
    Sat_Set_t * pSet;
    int i, k, fSeeA, fSeeB;
    // make sure all clauses are either A or B
    Sat_PoolForEachSet( vClauses, pSet, i )
    {
        fSeeA = fSeeB = 0;
        for ( k = 0; k < pSet->nEnts; k++ )
        {
            fSeeA += (Vec_IntEntry(vVarMap, pSet->pEnts[k]) == 1);
            fSeeB += (Vec_IntEntry(vVarMap, pSet->pEnts[k]) == 2);
        }
        if ( fSeeA && fSeeB )
            printf( "VarMap error!\n" );
    }
}

/**Function*************************************************************

  Synopsis    [Computes interpolant of the proof.]

  Description [Assuming that res vars are recorded, too...]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Sat_ProofInterpolant( Vec_Int_t * vProof, int iRoot, Vec_Int_t * vClauses, Vec_Int_t * vVarMap )
{
    Vec_Int_t * vOrigs, * vUsed, * vStack;
    Aig_Man_t * pAig;
    Sat_Set_t * pSet;
    int i;

    Sat_ProofVarMapCheck( vClauses, vVarMap );

    // collect original clauses
    vOrigs = Vec_IntAlloc( 1000 );
    Vec_IntPush( vOrigs, -1 );
    Sat_PoolForEachSet( vClauses, pSet, i )
        Vec_IntPush( vOrigs, Sat_SetId(vClauses, pSet) );

    // collect visited clauses
    vUsed = Vec_IntAlloc( 1000 );
    vStack = Vec_IntAlloc( 1000 );
    Sat_ProofLabel( vProof, Sat_SetFromId(vProof, iRoot), vUsed, vStack );
    Vec_IntFree( vStack );

    // start the AIG
    pAig = Aig_ManStart( 10000 );
    pAig->pName = Aig_UtilStrsav( "interpol" );
    for ( i = 0; i < Vec_IntSize(vVarMap); i++ )
        if ( Vec_IntEntry(vVarMap, i) < 0 )
            Aig_ObjCreatePi( pAig );
 
    return pAig;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

