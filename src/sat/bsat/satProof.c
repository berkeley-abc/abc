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
#include "src/misc/vec/vec.h"
#include "src/aig/aig/aig.h"
#include "satTruth.h"
#include "vecRec.h"

ABC_NAMESPACE_IMPL_START


/*
    Proof is represented as a vector of integers.
    The first entry is -1.
    A resolution record is represented by a handle (an offset in this array).
    A resolution record entry is <size><label><ant1><ant2>...<antN>
    Label is initialized to 0.
    Root clauses are given by their handles.
    They are marked by bitshifting by 2 bits up and setting the LSB to 1
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

static inline satset* Proof_NodeRead    (Vec_Int_t* p, cla h)     { return satset_read( (veci*)p, h );   }
//static inline cla     Proof_NodeHandle  (Vec_Int_t* p, satset* c) { return satset_handle( (veci*)p, c ); }
//static inline int     Proof_NodeCheck   (Vec_Int_t* p, satset* c) { return satset_check( (veci*)p, c );  }
static inline int     Proof_NodeSize    (int nEnts)               { return sizeof(satset)/4 + nEnts;     }

static inline satset* Proof_ResolveRead (Vec_Rec_t* p, cla h)     { return (satset*)Vec_RecEntryP(p, h); }

// iterating through nodes in the proof
#define Proof_ForeachNode( p, pNode, h )                         \
    for ( h = 1; (h < Vec_IntSize(p)) && ((pNode) = Proof_NodeRead(p, h)); h += Proof_NodeSize(pNode->nEnts) )
#define Proof_ForeachNodeVec( pVec, p, pNode, i )            \
    for ( i = 0; (i < Vec_IntSize(pVec)) && ((pNode) = Proof_NodeRead(p, Vec_IntEntry(pVec,i))); i++ )

// iterating through fanins of a proof node
#define Proof_NodeForeachFanin( p, pNode, pFanin, i )        \
    for ( i = 0; (i < (int)pNode->nEnts) && (((pFanin) = (pNode->pEnts[i] & 1) ? NULL : Proof_NodeRead(p, pNode->pEnts[i] >> 2)), 1); i++ )
#define Proof_NodeForeachLeaf( pClauses, pNode, pLeaf, i )   \
    for ( i = 0; (i < (int)pNode->nEnts) && (((pLeaf) = (pNode->pEnts[i] & 1) ? Proof_NodeRead(pClauses, pNode->pEnts[i] >> 2) : NULL), 1); i++ )
#define Proof_NodeForeachFaninLeaf( p, pClauses, pNode, pFanin, i )    \
    for ( i = 0; (i < (int)pNode->nEnts) && ((pFanin) = (pNode->pEnts[i] & 1) ? Proof_NodeRead(pClauses, pNode->pEnts[i] >> 2) : Proof_NodeRead(p, pNode->pEnts[i] >> 2)); i++ )


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the number of proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Proof_CountAll( Vec_Int_t * p )
{
    satset * pNode;
    int hNode, Counter = 0;
    Proof_ForeachNode( p, pNode, hNode )
        Counter++;
    return Counter;
}

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
void Proof_CollectUsed_iter( Vec_Int_t * vProof, int hNode, Vec_Int_t * vUsed, Vec_Int_t * vStack )
{
    satset * pNext, * pNode = Proof_NodeRead( vProof, hNode );
    int i;
    if ( pNode->Id )
        return;
    // start with node
    pNode->Id = 1;
    Vec_IntPush( vStack, hNode << 1 );
    // perform DFS search
    while ( Vec_IntSize(vStack) )
    {
        hNode = Vec_IntPop( vStack );
        if ( hNode & 1 ) // extracted second time
        {
            Vec_IntPush( vUsed, hNode >> 1 );
            continue;
        }
        // extracted first time        
        Vec_IntPush( vStack, hNode ^ 1 ); // add second time
        // add its anticedents        ;
        pNode = Proof_NodeRead( vProof, hNode >> 1 );
        Proof_NodeForeachFanin( vProof, pNode, pNext, i )
            if ( pNext && !pNext->Id )
            {
                pNext->Id = 1;
                Vec_IntPush( vStack, (pNode->pEnts[i] >> 2) << 1 ); // add first time
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
    int clk = clock();
    int i, Entry, iPrev = 0;
    assert( (hRoot > 0) ^ (vRoots != NULL) );
    vUsed = Vec_IntAlloc( 1000 );
    vStack = Vec_IntAlloc( 1000 );
    if ( hRoot )
        Proof_CollectUsed_iter( vProof, hRoot, vUsed, vStack );
    else
    {
        Vec_IntForEachEntry( vRoots, Entry, i )
            Proof_CollectUsed_iter( vProof, Entry, vUsed, vStack );
    }
    Vec_IntFree( vStack );
//    Abc_PrintTime( 1, "Iterative clause collection time", clock() - clk );

/*
    // verify topological order
    iPrev = 0;
    Vec_IntForEachEntry( vUsed, Entry, i )
    {
        printf( "%d ", Entry - iPrev );
        iPrev = Entry;
    }
*/
    clk = clock();
//    Vec_IntSort( vUsed, 0 );
    Abc_Sort( Vec_IntArray(vUsed), Vec_IntSize(vUsed) );
//    Abc_PrintTime( 1, "Postprocessing with sorting time", clock() - clk );

    // verify topological order
    iPrev = 0;
    Vec_IntForEachEntry( vUsed, Entry, i )
    {
        if ( iPrev >= Entry )
            printf( "Out of topological order!!!\n" );
        assert( iPrev < Entry );
        iPrev = Entry;
    }
    return vUsed;
}

/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Proof_CollectUsed_rec( Vec_Int_t * vProof, int hNode, Vec_Int_t * vUsed )
{
    satset * pNext, * pNode = Proof_NodeRead( vProof, hNode );
    int i;
    if ( pNode->Id )
        return;
    pNode->Id = 1;
    Proof_NodeForeachFanin( vProof, pNode, pNext, i )
        if ( pNext && !pNext->Id )
            Proof_CollectUsed_rec( vProof, pNode->pEnts[i] >> 2, vUsed );
    Vec_IntPush( vUsed, hNode );
}

/**Function*************************************************************

  Synopsis    [Recursively visits useful proof nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Proof_CollectUsedRec( Vec_Int_t * vProof, Vec_Int_t * vRoots, int hRoot )
{
    Vec_Int_t * vUsed;
    assert( (hRoot > 0) ^ (vRoots != NULL) );
    vUsed = Vec_IntAlloc( 1000 );
    if ( hRoot )
        Proof_CollectUsed_rec( vProof, hRoot, vUsed );
    else
    {
        int i, Entry;
        Vec_IntForEachEntry( vRoots, Entry, i )
            Proof_CollectUsed_rec( vProof, Entry, vUsed );
    }
    return vUsed;
}



 
/**Function*************************************************************

  Synopsis    [Reduces the proof to contain only roots and their children.]

  Description [The result is updated proof and updated roots.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_ProofReduce( sat_solver2 * s )
{
    Vec_Int_t * vProof   = (Vec_Int_t *)&s->proofs;
    Vec_Int_t * vRoots   = (Vec_Int_t *)&s->claProofs;

    int fVerbose = 0;
    Vec_Int_t * vUsed;
    satset * pNode, * pFanin;
    int i, k, hTemp, hNewHandle = 1, clk = clock();
    static int TimeTotal = 0;

    // collect visited nodes
    vUsed = Proof_CollectUsedIter( vProof, vRoots, 0 );
//    printf( "The proof uses %d out of %d proof nodes (%.2f %%)\n", 
//        Vec_IntSize(vUsed), Proof_CountAll(vProof), 
//        100.0 * Vec_IntSize(vUsed) / Proof_CountAll(vProof) );

    // relabel nodes to use smaller space
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
    {
        pNode->Id = hNewHandle; hNewHandle += Proof_NodeSize(pNode->nEnts);
        Proof_NodeForeachFanin( vProof, pNode, pFanin, k )
            if ( pFanin )
                pNode->pEnts[k] = (pFanin->Id << 2) | (pNode->pEnts[k] & 2);
    }
    // update roots
    Proof_ForeachNodeVec( vRoots, vProof, pNode, i )
        Vec_IntWriteEntry( vRoots, i, pNode->Id );
    // compact the nodes
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
    {
        hTemp = pNode->Id; pNode->Id = 0;
        memmove( Vec_IntArray(vProof) + hTemp, pNode, sizeof(int)*Proof_NodeSize(pNode->nEnts) );
    }
    Vec_IntFree( vUsed );

    // report the result
    if ( fVerbose )
    {
        printf( "The proof was reduced from %10d to %10d integers (by %6.2f %%)  ", 
            Vec_IntSize(vProof), hNewHandle, 100.0 * (Vec_IntSize(vProof) - hNewHandle) / Vec_IntSize(vProof) );
        TimeTotal += clock() - clk;
        Abc_PrintTime( 1, "Time", TimeTotal );
    }
    Vec_IntShrink( vProof, hNewHandle );
}


/**Function*************************************************************

  Synopsis    [Performs one resultion step.]

  Description [Returns ID of the resolvent if success, and -1 if failure.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sat_ProofCheckResolveOne( Vec_Rec_t * p, satset * c1, satset * c2, Vec_Int_t * vTemp )
{
    satset * c;
    int h, i, k, Var = -1, Count = 0;
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
        return 0;
    }
    if ( Count > 1 )
    {
        printf( "Found more than 1 resolution variables\n" );
        return 0;
    }
    // perform resolution
    Vec_IntClear( vTemp );
    Vec_IntPush( vTemp, 0 ); // placeholder
    Vec_IntPush( vTemp, 0 );
    for ( i = 0; i < (int)c1->nEnts; i++ )
        if ( (c1->pEnts[i] >> 1) != Var )
            Vec_IntPush( vTemp, c1->pEnts[i] );
    for ( i = 0; i < (int)c2->nEnts; i++ )
        if ( (c2->pEnts[i] >> 1) != Var )
            Vec_IntPushUnique( vTemp, c2->pEnts[i] );
    // create new resolution entry
    h = Vec_RecPush( p, Vec_IntArray(vTemp), Vec_IntSize(vTemp) );
    // return the new entry
    c = Proof_ResolveRead( p, h );
    c->nEnts = Vec_IntSize(vTemp)-2;
    return h;
}

/**Function*************************************************************

  Synopsis    [Checks the proof for consitency.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
satset * Sat_ProofCheckReadOne( Vec_Int_t * vClauses, Vec_Int_t * vProof, Vec_Rec_t * vResolves, int iAnt )
{
    satset * pAnt;
    if ( iAnt & 1 )
        return Proof_NodeRead( vClauses, iAnt >> 2 );
    assert( iAnt > 0 );
    pAnt = Proof_NodeRead( vProof, iAnt >> 2 );
    assert( pAnt->Id > 0 );
    return Proof_ResolveRead( vResolves, pAnt->Id );
}

/**Function*************************************************************

  Synopsis    [Checks the proof for consitency.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_ProofCheck( sat_solver2 * s )
{
    Vec_Int_t * vClauses = (Vec_Int_t *)&s->clauses;
    Vec_Int_t * vProof   = (Vec_Int_t *)&s->proofs;
    Vec_Rec_t * vResolves;
    Vec_Int_t * vUsed, * vTemp;
    satset * pSet, * pSet0, * pSet1;
    int i, k, hRoot, Handle, Counter = 0, clk = clock(); 
//    if ( s->hLearntLast < 0 )
//        return;
//    hRoot = veci_begin(&s->claProofs)[satset_read(&s->learnts, s->hLearntLast>>1)->Id];
    hRoot = s->hProofLast;
    if ( hRoot == -1 )
        return;

    // collect visited clauses
    vUsed = Proof_CollectUsedIter( vProof, NULL, hRoot );
    Proof_CleanCollected( vProof, vUsed );
    // perform resolution steps
    vTemp = Vec_IntAlloc( 1000 );
    vResolves = Vec_RecAlloc();
    Proof_ForeachNodeVec( vUsed, vProof, pSet, i )
    {
        pSet0 = Sat_ProofCheckReadOne( vClauses, vProof, vResolves, pSet->pEnts[0] );
        for ( k = 1; k < (int)pSet->nEnts; k++ )
        {
            pSet1  = Sat_ProofCheckReadOne( vClauses, vProof, vResolves, pSet->pEnts[k] );
            Handle = Sat_ProofCheckResolveOne( vResolves, pSet0, pSet1, vTemp );
            pSet0  = Proof_ResolveRead( vResolves, Handle );
        }
        pSet->Id = Handle;
//printf( "Clause for proof %d: ", Vec_IntEntry(vUsed, i) );
//satset_print( pSet0 );
        Counter++;
    }
    Vec_IntFree( vTemp );
    // clean the proof
    Proof_CleanCollected( vProof, vUsed );
    // compare the final clause
    printf( "Used %6.2f Mb for resolvents.\n", 4.0 * Vec_RecSize(vResolves) / (1<<20) );
    if ( pSet0->nEnts > 0 )
        printf( "Derived clause with %d lits instead of the empty clause.  ", pSet0->nEnts );
    else
        printf( "Proof verification successful.  " );
    Abc_PrintTime( 1, "Time", clock() - clk );
    // cleanup
    Vec_RecFree( vResolves );
    Vec_IntFree( vUsed );
}


/**Function*************************************************************

  Synopsis    [Collects nodes belonging to the UNSAT core.]

  Description [The resulting array contains 1-based IDs of root clauses.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Sat_ProofCollectCore( Vec_Int_t * vClauses, Vec_Int_t * vProof, Vec_Int_t * vUsed, int fUseIds )
{
    Vec_Int_t * vCore;
    satset * pNode, * pFanin;
    int i, k, clk = clock();
    vCore = Vec_IntAlloc( 1000 );
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
    {
        pNode->Id = 0;
        Proof_NodeForeachLeaf( vClauses, pNode, pFanin, k )
            if ( pFanin && !pFanin->mark )
            {
                pFanin->mark = 1;
                Vec_IntPush( vCore, pNode->pEnts[k] >> 2 );
            }
    }
    // clean core clauses and reexpress core in terms of clause IDs
    Proof_ForeachNodeVec( vCore, vClauses, pNode, i )
    {
        pNode->mark = 0;
        if ( fUseIds )
//            Vec_IntWriteEntry( vCore, i, pNode->Id - 1 );
            Vec_IntWriteEntry( vCore, i, pNode->Id );
    }
    return vCore;
}

/**Function*************************************************************

  Synopsis    [Verifies that variables are labeled correctly.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_ProofInterpolantCheckVars( sat_solver2 * s, Vec_Int_t * vGloVars )
{
    satset* c; 
    Vec_Int_t * vVarMap;
    int i, k, Entry, * pMask;
    int Counts[5] = {0};
    // map variables into their type (A, B, or AB)
    vVarMap = Vec_IntStart( s->size );
    sat_solver_foreach_clause( s, c, i )
        for ( k = 0; k < (int)c->nEnts; k++ )
            *Vec_IntEntryP(vVarMap, lit_var(c->pEnts[k])) |= 2 - c->partA;
    // analyze variables
    Vec_IntForEachEntry( vGloVars, Entry, i )
    {
        pMask = Vec_IntEntryP(vVarMap, Entry);
        assert( *pMask >= 0 && *pMask <= 3 );
        Counts[(*pMask & 3)]++;
        *pMask = 0;
    }
    // count the number of global variables not listed
    Vec_IntForEachEntry( vVarMap, Entry, i )
        if ( Entry == 3 )
            Counts[4]++;
    Vec_IntFree( vVarMap );
    // report
    if ( Counts[0] )
        printf( "Warning: %6d variables listed as global do not appear in clauses (this is normal)\n", Counts[0] );
    if ( Counts[1] )
        printf( "Warning: %6d variables listed as global appear only in A-clauses (this is a BUG)\n", Counts[1] );
    if ( Counts[2] )
        printf( "Warning: %6d variables listed as global appear only in B-clauses (this is a BUG)\n", Counts[2] );
    if ( Counts[3] )
        printf( "Warning: %6d (out of %d) variables listed as global appear in both A- and B-clauses (this is normal)\n", Counts[3], Vec_IntSize(vGloVars) );
    if ( Counts[4] )
        printf( "Warning: %6d variables not listed as global appear in both A- and B-clauses (this is a BUG)\n", Counts[4] );
}

/**Function*************************************************************

  Synopsis    [Computes interpolant of the proof.]

  Description [Aassuming that vars/clause of partA are marked.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Sat_ProofInterpolant( sat_solver2 * s, void * pGloVars )
{
    Vec_Int_t * vClauses  = (Vec_Int_t *)&s->clauses;
    Vec_Int_t * vProof    = (Vec_Int_t *)&s->proofs;
    Vec_Int_t * vGlobVars = (Vec_Int_t *)pGloVars;
    Vec_Int_t * vUsed, * vCore, * vCoreNums, * vVarMap;
    satset * pNode, * pFanin;
    Aig_Man_t * pAig;
    Aig_Obj_t * pObj;
    int i, k, iVar, Lit, Entry, hRoot;
//    if ( s->hLearntLast < 0 )
//        return NULL;
//    hRoot = veci_begin(&s->claProofs)[satset_read(&s->learnts, s->hLearntLast>>1)->Id];
    hRoot = s->hProofLast;
    if ( hRoot == -1 )
        return NULL;

    Sat_ProofInterpolantCheckVars( s, vGlobVars );

    // collect visited nodes
    vUsed = Proof_CollectUsedIter( vProof, NULL, hRoot );
    // collect core clauses (cleans vUsed and vCore)
    vCore = Sat_ProofCollectCore( vClauses, vProof, vUsed, 0 );

    // map variables into their global numbers
    vVarMap = Vec_IntStartFull( s->size );
    Vec_IntForEachEntry( vGlobVars, Entry, i )
        Vec_IntWriteEntry( vVarMap, Entry, i );

    // start the AIG
    pAig = Aig_ManStart( 10000 );
    pAig->pName = Abc_UtilStrsav( "interpol" );
    for ( i = 0; i < Vec_IntSize(vGlobVars); i++ )
        Aig_ObjCreatePi( pAig );

    // copy the numbers out and derive interpol for clause
    vCoreNums = Vec_IntAlloc( Vec_IntSize(vCore) );
    Proof_ForeachNodeVec( vCore, vClauses, pNode, i )
    {
        if ( pNode->partA )
        {
            pObj = Aig_ManConst0( pAig );
            satset_foreach_lit( pNode, Lit, k, 0 )
                if ( (iVar = Vec_IntEntry(vVarMap, lit_var(Lit))) >= 0 )
                    pObj = Aig_Or( pAig, pObj, Aig_NotCond(Aig_IthVar(pAig, iVar), lit_sign(Lit)) );
        }
        else
            pObj = Aig_ManConst1( pAig );
        // remember the interpolant
        Vec_IntPush( vCoreNums, pNode->Id );
        pNode->Id = Aig_ObjToLit(pObj);
    }
    Vec_IntFree( vVarMap );

    // copy the numbers out and derive interpol for resolvents
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
    {
//        satset_print( pNode );
        assert( pNode->nEnts > 1 );
        Proof_NodeForeachFaninLeaf( vProof, vClauses, pNode, pFanin, k )
        {
            assert( pFanin->Id < 2*Aig_ManObjNumMax(pAig) );
            if ( k == 0 )
                pObj = Aig_ObjFromLit( pAig, pFanin->Id );
            else if ( pNode->pEnts[k] & 2 ) // variable of A
                pObj = Aig_Or( pAig, pObj, Aig_ObjFromLit(pAig, pFanin->Id) );
            else
                pObj = Aig_And( pAig, pObj, Aig_ObjFromLit(pAig, pFanin->Id) );
        }
        // remember the interpolant
        pNode->Id = Aig_ObjToLit(pObj);
    }
    // save the result
//    assert( Proof_NodeHandle(vProof, pNode) == hRoot );
    Aig_ObjCreatePo( pAig, pObj );
    Aig_ManCleanup( pAig );

    // move the results back
    Proof_ForeachNodeVec( vCore, vClauses, pNode, i )
        pNode->Id = Vec_IntEntry( vCoreNums, i );
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
        pNode->Id = 0;
    // cleanup
    Vec_IntFree( vCore );
    Vec_IntFree( vUsed );
    Vec_IntFree( vCoreNums );
    return pAig;
}


/**Function*************************************************************

  Synopsis    [Computes interpolant of the proof.]

  Description [Aassuming that vars/clause of partA are marked.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word * Sat_ProofInterpolantTruth( sat_solver2 * s, void * pGloVars )
{
    Vec_Int_t * vClauses  = (Vec_Int_t *)&s->clauses;
    Vec_Int_t * vProof    = (Vec_Int_t *)&s->proofs;
    Vec_Int_t * vGlobVars = (Vec_Int_t *)pGloVars;
    Vec_Int_t * vUsed, * vCore, * vCoreNums, * vVarMap;
    satset * pNode, * pFanin;
    Tru_Man_t * pTru;
    int nVars = Vec_IntSize(vGlobVars);
    int nWords = (nVars < 6) ? 1 : (1 << (nVars-6));
    word * pRes = ABC_ALLOC( word, nWords );
    int i, k, iVar, Lit, Entry, hRoot;
    assert( nVars > 0 && nVars <= 16 );
//    if ( s->hLearntLast < 0 )
//        return NULL;
//    hRoot = veci_begin(&s->claProofs)[satset_read(&s->learnts, s->hLearntLast>>1)->Id];
    hRoot = s->hProofLast;
    if ( hRoot == -1 )
        return NULL;

    Sat_ProofInterpolantCheckVars( s, vGlobVars );

    // collect visited nodes
    vUsed = Proof_CollectUsedIter( vProof, NULL, hRoot );
    // collect core clauses (cleans vUsed and vCore)
    vCore = Sat_ProofCollectCore( vClauses, vProof, vUsed, 0 );

    // map variables into their global numbers
    vVarMap = Vec_IntStartFull( s->size );
    Vec_IntForEachEntry( vGlobVars, Entry, i )
        Vec_IntWriteEntry( vVarMap, Entry, i );

    // start the AIG
    pTru = Tru_ManAlloc( nVars );

    // copy the numbers out and derive interpol for clause
    vCoreNums = Vec_IntAlloc( Vec_IntSize(vCore) );
    Proof_ForeachNodeVec( vCore, vClauses, pNode, i )
    {
        if ( pNode->partA )
        {
//            pObj = Aig_ManConst0( pAig );
            Tru_ManClear( pRes, nWords );
            satset_foreach_lit( pNode, Lit, k, 0 )
                if ( (iVar = Vec_IntEntry(vVarMap, lit_var(Lit))) >= 0 )
//                    pObj = Aig_Or( pAig, pObj, Aig_NotCond(Aig_IthVar(pAig, iVar), lit_sign(Lit)) );
                    pRes = Tru_ManOrNotCond( pRes, Tru_ManVar(pTru, iVar), nWords, lit_sign(Lit) );
        }
        else
//            pObj = Aig_ManConst1( pAig );
            Tru_ManFill( pRes, nWords );
        // remember the interpolant
        Vec_IntPush( vCoreNums, pNode->Id );
//        pNode->Id = Aig_ObjToLit(pObj);
        pNode->Id = Tru_ManInsert( pTru, pRes );
    }
    Vec_IntFree( vVarMap );

    // copy the numbers out and derive interpol for resolvents
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
    {
//        satset_print( pNode );
        assert( pNode->nEnts > 1 );
        Proof_NodeForeachFaninLeaf( vProof, vClauses, pNode, pFanin, k )
        {
//            assert( pFanin->Id < 2*Aig_ManObjNumMax(pAig) );
            assert( pFanin->Id <= Tru_ManHandleMax(pTru) );
            if ( k == 0 )
//                pObj = Aig_ObjFromLit( pAig, pFanin->Id );
                pRes = Tru_ManCopyNotCond( pRes, Tru_ManFunc(pTru, pFanin->Id & ~1), nWords, pFanin->Id & 1 );
            else if ( pNode->pEnts[k] & 2 ) // variable of A
//                pObj = Aig_Or( pAig, pObj, Aig_ObjFromLit(pAig, pFanin->Id) );
                pRes = Tru_ManOrNotCond( pRes, Tru_ManFunc(pTru, pFanin->Id & ~1), nWords, pFanin->Id & 1 );
            else
//                pObj = Aig_And( pAig, pObj, Aig_ObjFromLit(pAig, pFanin->Id) );
                pRes = Tru_ManAndNotCond( pRes, Tru_ManFunc(pTru, pFanin->Id & ~1), nWords, pFanin->Id & 1 );
        }
        // remember the interpolant
//        pNode->Id = Aig_ObjToLit(pObj);
        pNode->Id = Tru_ManInsert( pTru, pRes );
    }
    // save the result
//    assert( Proof_NodeHandle(vProof, pNode) == hRoot );
//    Aig_ObjCreatePo( pAig, pObj );
//    Aig_ManCleanup( pAig );

    // move the results back
    Proof_ForeachNodeVec( vCore, vClauses, pNode, i )
        pNode->Id = Vec_IntEntry( vCoreNums, i );
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
        pNode->Id = 0;
    // cleanup
    Vec_IntFree( vCore );
    Vec_IntFree( vUsed );
    Vec_IntFree( vCoreNums );
    Tru_ManFree( pTru );
//    ABC_FREE( pRes );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Computes UNSAT core.]

  Description [The result is the array of root clause indexes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Sat_ProofCore( sat_solver2 * s )
{
    Vec_Int_t * vClauses  = (Vec_Int_t *)&s->clauses;
    Vec_Int_t * vProof    = (Vec_Int_t *)&s->proofs;
    Vec_Int_t * vCore, * vUsed;
    int hRoot;
//    if ( s->hLearntLast < 0 )
//        return NULL;
//    hRoot = veci_begin(&s->claProofs)[satset_read(&s->learnts, s->hLearntLast>>1)->Id];
    hRoot = s->hProofLast;
    if ( hRoot == -1 )
        return NULL;

    // collect visited clauses
    vUsed = Proof_CollectUsedIter( vProof, NULL, hRoot );
    // collect core clauses 
    vCore = Sat_ProofCollectCore( vClauses, vProof, vUsed, 1 );
    Vec_IntFree( vUsed );
    return vCore;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

