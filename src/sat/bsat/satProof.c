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

#include "satSolver2.h"
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
/*

typedef struct satset_t satset;
struct satset_t 
{
    unsigned learnt :  1;
    unsigned mark   :  1;
    unsigned partA  :  1;
    unsigned nEnts  : 29;
    int      Id;
    lit      pEnts[0];
};

#define satset_foreach_entry( p, c, h, s )  \
    for ( h = s; (h < veci_size(p)) && (((c) = satset_read(p, h)), 1); h += satset_size(c->nEnts) )
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline satset* Proof_NodeRead   (Vec_Int_t* p, cla h )     { return satset_read( (veci*)p, h );   }
static inline cla     Proof_NodeHandle (Vec_Int_t* p, satset* c)  { return satset_handle( (veci*)p, c ); }
static inline int     Proof_NodeCheck  (Vec_Int_t* p, satset* c)  { return satset_check( (veci*)p, c );  }
static inline int     Proof_NodeSize   (int nEnts)                { return sizeof(satset)/4 + nEnts;     }

#define Proof_ForeachNode( p, pNode, hNode )             \
    satset_foreach_entry( ((veci*)p), pNode, hNode, 1 )
#define Proof_ForeachNodeVec( pVec, p, pNode, i )        \
    for ( i = 0; (i < Vec_IntSize(pVec)) && ((pNode) = Proof_NodeRead(p, Vec_IntEntry(pVec,i))); i++ )
#define Proof_NodeForeachFanin( p, pNode, pFanin, i )    \
    for ( i = 0; (i < (int)pNode->nEnts) && (((pFanin) = (pNode->pEnts[i] & 1) ? NULL : Proof_NodeRead(p, pNode->pEnts[i] >> 2)), 1); i++ )
#define Proof_NodeForeachLeaf( pLeaves, pNode, pLeaf, i )    \
    for ( i = 0; (i < (int)pNode->nEnts) && (((pLeaf) = (pNode->pEnts[i] & 1) ? Proof_NodeRead(pLeaves, pNode->pEnts[i] >> 2) : NULL), 1); i++ )
#define Proof_NodeForeachFaninRoot( p, pLeaves, pNode, pFanin, i )    \
    for ( i = 0; (i < (int)pNode->nEnts) && ((pFanin) = (pNode->pEnts[i] & 1) ? Proof_NodeRead(pLeaves, pNode->pEnts[i] >> 2) : Proof_NodeRead(p, pNode->pEnts[i] >> 2)); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collects all resolution nodes belonging to the proof.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Proof_CollectAll( Vec_Int_t * p )
{
    Vec_Int_t * vUsed;
    satset * pNode;
    int hNode;
    vUsed = Vec_IntAlloc( 1000 );
    Proof_ForeachNode( p, pNode, hNode )
        Vec_IntPush( vUsed, hNode );
    return vUsed;
}

/**Function*************************************************************

  Synopsis    [Cleans collected resultion nodes belonging to the proof.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Proof_CleanCollected( Vec_Int_t * vProof, Vec_Int_t * vUsed )
{
    satset * pNode;
    int hNode;
    Proof_ForeachNodeVec( vUsed, vProof, pNode, hNode )
        pNode->Id = 0;
}

/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Proof_CollectUsed_iter( Vec_Int_t * p, satset * pNode, Vec_Int_t * vUsed, Vec_Int_t * vStack )
{
    satset * pNext;
    int i, hNode;
    if ( pNode->Id )
        return;
    // start with node
    pNode->Id = 1;
    Vec_IntPush( vStack, Proof_NodeHandle(p, pNode) << 1 );
    // perform DFS search
    while ( Vec_IntSize(vStack) )
    {
        hNode = Vec_IntPop( vStack );
        if ( hNode & 1 ) // extrated second time
        {
            Vec_IntPush( vUsed, hNode >> 1 );
            continue;
        }
        // extracted first time        
        Vec_IntPush( vStack, hNode ^ 1 ); // add second time
        // add its anticedents        ;
        pNode = Proof_NodeRead( p, hNode >> 1 );
        Proof_NodeForeachFanin( p, pNode, pNext, i )
            if ( pNext && !pNext->Id )
            {
                pNext->Id = 1;
                Vec_IntPush( vStack, Proof_NodeHandle(p, pNext) << 1 ); // add first time
            }
    }
}

/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Proof_CollectUsedIter( Vec_Int_t * vProof, Vec_Int_t * vRoots, int hRoot )
{
    Vec_Int_t * vUsed, * vStack;
    assert( (hRoot > 0) ^ (vRoots != NULL) );
    vUsed = Vec_IntAlloc( 1000 );
    vStack = Vec_IntAlloc( 1000 );
    if ( hRoot )
        Proof_CollectUsed_iter( vProof, Proof_NodeRead(vProof, hRoot), vUsed, vStack );
    else
    {
        satset * pNode;
        int i;
        Proof_ForeachNodeVec( vRoots, vProof, pNode, i )
            Proof_CollectUsed_iter( vProof, pNode, vUsed, vStack );
    }
    Vec_IntFree( vStack );
    return vUsed;
}

/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Proof_CollectUsed_rec( Vec_Int_t * p, satset * pNode, Vec_Int_t * vUsed )
{
    satset * pNext;
    int i;
    if ( pNode->Id )
        return;
    pNode->Id = 1;
    Proof_NodeForeachFanin( p, pNode, pNext, i )
        if ( pNext && !pNext->Id )
            Proof_CollectUsed_rec( p, pNext, vUsed );
    Vec_IntPush( vUsed, Proof_NodeHandle(p, pNode) );
}

/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Proof_CollectUsedRec( Vec_Int_t * vProof, Vec_Int_t * vRoots, int hRoot )
{
    Vec_Int_t * vUsed, * vStack;
    assert( (hRoot > 0) ^ (vRoots != NULL) );
    vUsed = Vec_IntAlloc( 1000 );
    vStack = Vec_IntAlloc( 1000 );
    if ( hRoot )
        Proof_CollectUsed_rec( vProof, Proof_NodeRead(vProof, hRoot), vUsed );
    else
    {
        satset * pNode;
        int i;
        Proof_ForeachNodeVec( vRoots, vProof, pNode, i )
            Proof_CollectUsed_rec( vProof, pNode, vUsed );
    }
    Vec_IntFree( vStack );
    return vUsed;
}
 
/**Function*************************************************************

  Synopsis    [Performs one resultion step.]

  Description [Returns ID of the resolvent if success, and -1 if failure.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
satset * Proof_ResolveOne( Vec_Int_t * p, satset * c1, satset * c2, Vec_Int_t * vTemp )
{
    satset * c;
    int i, k, hNode, Var = -1, Count = 0;
    // find resolution variable
    for ( i = 0; i < (int)c1->nEnts; i++ )
    for ( k = 0; k < (int)c2->nEnts; k++ )
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
    Vec_IntClear( vTemp );
    for ( i = 0; i < (int)c1->nEnts; i++ )
        if ( (c1->pEnts[i] >> 1) != Var )
            Vec_IntPush( vTemp, c1->pEnts[i] );
    for ( i = 0; i < (int)c2->nEnts; i++ )
        if ( (c2->pEnts[i] >> 1) != Var )
            Vec_IntPushUnique( vTemp, c2->pEnts[i] );
    // move to the new one
    hNode = Vec_IntSize( p );
    Vec_IntPush( p, 0 ); // placeholder
    Vec_IntPush( p, 0 );
    Vec_IntForEachEntry( vTemp, Var, i )
        Vec_IntPush( p, Var );
    c = Proof_NodeRead( p, hNode );
    c->nEnts = Vec_IntSize(vTemp);
    return c;
}

/**Function*************************************************************

  Synopsis    [Checks the proof for consitency.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
satset * Proof_CheckReadOne( Vec_Int_t * vClauses, Vec_Int_t * vProof, Vec_Int_t * vResolves, int iAnt )
{
    satset * pAnt;
    if ( iAnt & 1 )
        return Proof_NodeRead( vClauses, iAnt >> 2 );
    assert( iAnt > 0 );
    pAnt = Proof_NodeRead( vProof, iAnt >> 2 );
    assert( pAnt->Id > 0 );
    return Proof_NodeRead( vResolves, pAnt->Id );
}

/**Function*************************************************************

  Synopsis    [Checks the proof for consitency.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Proof_Check( Vec_Int_t * vClauses, Vec_Int_t * vProof, int hRoot )
{
    Vec_Int_t * vUsed, * vResolves, * vTemp;
    satset * pSet, * pSet0, * pSet1;
    int i, k, Counter = 0, clk = clock(); 
    // collect visited clauses
    vUsed = Proof_CollectUsedRec( vProof, NULL, hRoot );
    Proof_CleanCollected( vProof, vUsed );
    // perform resolution steps
    vTemp = Vec_IntAlloc( 1000 );
    vResolves = Vec_IntAlloc( 1000 );
    Vec_IntPush( vResolves, -1 );
    Proof_ForeachNodeVec( vUsed, vProof, pSet, i )
    {
        pSet0 = Proof_CheckReadOne( vClauses, vProof, vResolves, pSet->pEnts[0] );
        for ( k = 1; k < (int)pSet->nEnts; k++ )
        {
            pSet1 = Proof_CheckReadOne( vClauses, vProof, vResolves, pSet->pEnts[k] );
            pSet0 = Proof_ResolveOne( vResolves, pSet0, pSet1, vTemp );
        }
        pSet->Id = Proof_NodeHandle( vResolves, pSet0 );
//printf( "Clause for proof %d: ", Vec_IntEntry(vUsed, i) );
//satset_print( pSet0 );
        Counter++;
    }
    Vec_IntFree( vTemp );
    // clean the proof
    Proof_CleanCollected( vProof, vUsed );
    // compare the final clause
    printf( "Used %6.2f Mb for resolvents.\n", 4.0 * Vec_IntSize(vResolves) / (1<<20) );
    if ( pSet0->nEnts > 0 )
        printf( "Cound not derive the empty clause.  " );
    else
        printf( "Proof verification successful.  " );
    Abc_PrintTime( 1, "Time", clock() - clk );
    // cleanup
    Vec_IntFree( vResolves );
    Vec_IntFree( vUsed );
}





/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sat_ProofReduceOne( Vec_Int_t * p, satset * pNode, int * pnSize, Vec_Int_t * vStack )
{
    satset * pNext;
    int i, NodeId;
    if ( pNode->Id )
        return pNode->Id;
    // start with node
    pNode->Id = 1;
    Vec_IntPush( vStack, Proof_NodeHandle(p, pNode) );
    // perform DFS search
    while ( Vec_IntSize(vStack) )
    {
        NodeId = Vec_IntPop( vStack );
        if ( NodeId & 1 ) // extrated second time
        {
            pNode = Proof_NodeRead( p, NodeId ^ 1 );
            pNode->Id = *pnSize;
            *pnSize += Proof_NodeSize(pNode->nEnts);
            // update fanins
            Proof_NodeForeachFanin( p, pNode, pNext, i )
                if ( pNext )
                    pNode->pEnts[i] = pNext->Id;
            continue;
        }
        // extracted first time
        // add second time
        Vec_IntPush( vStack, NodeId ^ 1 );
        // add its anticedents
        pNode = Proof_NodeRead( p, NodeId );
        Proof_NodeForeachFanin( p, pNode, pNext, i )
            if ( pNext && !pNext->Id )
            {
                pNext->Id = 1;
                Vec_IntPush( vStack, Proof_NodeHandle(p, pNode) ); // add first time
            }
    }
    return pNode->Id;
}

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
    satset * pNode;
    // mark used nodes
    vStack = Vec_IntAlloc( 1000 );
    Proof_ForeachNodeVec( vRoots, p, pNode, i )
        vRoots->pArray[i] = Sat_ProofReduceOne( p, pNode, &nSize, vStack );
    Vec_IntFree( vStack );
    // compact proof
    pNew = Vec_IntArray(p) + 1;
    Proof_ForeachNode( p, pNode, i )
    {
        if ( !pNode->Id )
            continue;
        assert( pNew - Vec_IntArray(p) == pNode->Id );
        pNode->Id = 0;
        pBeg = (int *)pNode;
        pEnd = pBeg + Proof_NodeSize(pNode->nEnts);
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

  Synopsis    [Computes UNSAT core.]

  Description [The result is the array of root clause indexes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Sat_ProofCore( Vec_Int_t * vProof, Vec_Int_t * vRoots )
{
    Vec_Int_t * vCore, * vUsed;
    satset * pNode, * pFanin;
    int i, k, clk = clock();;
    // collect visited clauses
    vUsed = Proof_CollectUsedIter( vProof, vRoots, 0 );
    // collect core clauses 
    vCore = Vec_IntAlloc( 1000 );
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
    {
        pNode->Id = 0;
        Proof_NodeForeachLeaf( vRoots, pNode, pFanin, k )
            if ( pFanin && !pFanin->mark )
            {
                pFanin->mark = 1;
                Vec_IntPush( vCore, Proof_NodeHandle(vRoots, pFanin) );
            }
    }
    // clean core clauses
    Proof_ForeachNodeVec( vCore, vRoots, pNode, i )
        pNode->mark = 0;
    Vec_IntFree( vUsed );
    printf( "Collected %d core clauses.  ", Vec_IntSize(vCore) );
    Abc_PrintTime( 1, "Time", clock() - clk );
    return vCore;
}

/**Function*************************************************************

  Synopsis    [Computes interpolant of the proof.]

  Description [Aassuming that vars/clause of partA are marked.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Sat_ProofInterpolant( Vec_Int_t * vClauses, Vec_Int_t * vProof, int hRoot, Vec_Int_t * vGlobVars )
{
    Vec_Int_t * vUsed, * vCore, * vVarMap;
    Vec_Int_t * vUsedNums, * vCoreNums;
    satset * pNode, * pFanin;
    Aig_Man_t * pAig;
    Aig_Obj_t * pObj;
    int i, k, iVar, Entry;

    // collect core clauses
    vCore = Sat_ProofCore( vProof, vClauses );
    // collect visited clauses
    vUsed = Proof_CollectUsedRec( vProof, NULL, hRoot );
    Proof_CleanCollected( vProof, vUsed );

    // start the AIG
    pAig = Aig_ManStart( 10000 );
    pAig->pName = Aig_UtilStrsav( "interpol" );
    for ( i = 0; i < Vec_IntSize(vGlobVars); i++ )
        Aig_ObjCreatePi( pAig );

    // map variables into their global numbers
    vVarMap = Vec_IntStartFull( Vec_IntFindMax(vGlobVars) + 1 );
    Vec_IntForEachEntry( vGlobVars, Entry, i )
        Vec_IntWriteEntry( vVarMap, Entry, i );

    // copy the numbers out and derive interpol for clause
    vCoreNums = Vec_IntAlloc( Vec_IntSize(vCore) );
    Proof_ForeachNodeVec( vCore, vClauses, pNode, i )
    {
        if ( pNode->partA )
        {
            pObj = Aig_ManConst0( pAig );
            satset_foreach_var( pNode, iVar, k )
                if ( iVar < Vec_IntSize(vVarMap) && Vec_IntEntry(vVarMap, iVar) >= 0 )
                    pObj = Aig_Or( pAig, pObj, Aig_IthVar(pAig, iVar) );
        }
        else
            pObj = Aig_ManConst1( pAig );
        // remember the interpolant
        Vec_IntPush( vCoreNums, pNode->Id );
        pNode->Id = Aig_ObjToLit(pObj);
    }
    Vec_IntFree( vVarMap );

    // copy the numbers out and derive interpol for resolvents
    vUsedNums = Vec_IntAlloc( Vec_IntSize(vUsed) );
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
    {
        assert( pNode->nEnts > 1 );
        Proof_NodeForeachFaninRoot( vProof, vClauses, pNode, pFanin, k )
        {
            if ( k == 0 )
                pObj = Aig_ObjFromLit(pAig, pFanin->Id);
            else if ( pNode->pEnts[k] & 2 ) // variable of A
                pObj = Aig_Or( pAig, pObj, Aig_ObjFromLit(pAig, pFanin->Id) );
            else
                pObj = Aig_And( pAig, pObj, Aig_ObjFromLit(pAig, pFanin->Id) );
        }
        // remember the interpolant
        Vec_IntPush( vUsedNums, pNode->Id );
        pNode->Id = Aig_ObjToLit(pObj);
    }
    // save the result
    Aig_ObjCreatePo( pAig, pObj );
    Aig_ManCleanup( pAig );

    // move the results back
    Proof_ForeachNodeVec( vCore, vClauses, pNode, i )
        pNode->Id = Vec_IntEntry( vCoreNums, i );
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
        pNode->Id = Vec_IntEntry( vUsedNums, i );
    // cleanup
    Vec_IntFree( vCore );
    Vec_IntFree( vUsed );
    Vec_IntFree( vCoreNums );
    Vec_IntFree( vUsedNums );
    return pAig;
}

/*
    Sat_ProofTest( 
        &s->clauses,      // clauses
        &s->proof_clas,   // proof clauses
        NULL,             // proof roots
        veci_begin(&s->claProofs)[clause_read(s, s->iLearntLast)->Id)],  // one root
        &s->glob_vars );  // global variables (for interpolation)
*/

/**Function*************************************************************

  Synopsis    [Computes interpolant of the proof.]

  Description [Aassuming that global vars and A-clauses are marked.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_ProofTest( veci * pClauses, veci * pProof, veci * pRoots, int hRoot )
{
    Vec_Int_t * vClauses  = (Vec_Int_t *)pClauses;
    Vec_Int_t * vProof    = (Vec_Int_t *)pProof;
    Vec_Int_t * vRoots    = (Vec_Int_t *)pRoots;
    Vec_Int_t * vUsed, * vCore;
//    int i, Entry;

    // collect visited clauses
    vUsed = Proof_CollectUsedRec( vProof, NULL, hRoot );
    Proof_CleanCollected( vProof, vUsed );
    printf( "Found %d useful resolution nodes.\n", Vec_IntSize(vUsed) );
    Vec_IntFree( vUsed );

    // collect visited clauses
    vUsed = Proof_CollectUsedIter( vProof, NULL, hRoot );
    Proof_CleanCollected( vProof, vUsed );
    printf( "Found %d useful resolution nodes.\n", Vec_IntSize(vUsed) );
    Vec_IntFree( vUsed );

    vCore = Sat_ProofCore( vProof, vClauses );
    Vec_IntFree( vCore );



//    Vec_IntForEachEntry( vUsed, Entry, i )
//        printf( "%d ", Entry );
//    printf( "\n" );
/*
    printf( "Found %d useful resolution nodes.\n", Vec_IntSize(vUsed) );
    Vec_IntFree( vUsed );
    vUsed = Proof_CollectAll( vProof );
    printf( "Found %d total  resolution nodes.\n", Vec_IntSize(vUsed) );
    Vec_IntFree( vUsed );

    Proof_Check( vClauses, vProof, hRoot );
*/
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

