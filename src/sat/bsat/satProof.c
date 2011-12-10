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
    A resolution record is represented by a handle (an offset in this array).
    A resolution record entry is <size><label><ant1><ant2>...<antN>
    Label is initialized to 0.
    Root clauses are given by their handles.
    They are marked by bitshifting by 2 bits up and setting the LSB to 1
*/

// data-structure to record resolvents of the proof
typedef struct Rec_Int_t_ Rec_Int_t;
struct Rec_Int_t_ 
{
    int          nShift;  // log number of entries on a page
    int          Mask;    // mask for entry number on a page
    int          nSize;   // the total number of entries
    int          nLast;   // the total number of entries before last append
    Vec_Ptr_t *  vPages;  // memory pages
};
static inline Rec_Int_t * Rec_IntAlloc( int nShift )
{
    Rec_Int_t * p;
    p = ABC_CALLOC( Rec_Int_t, 1 );
    p->nShift  = nShift;
    p->Mask    = (1<<nShift)-1;
    p->vPages  = Vec_PtrAlloc( 50 );
    return p;
}
static inline int Rec_IntSize( Rec_Int_t * p )
{
    return p->nSize;
}
static inline int Rec_IntSizeLast( Rec_Int_t * p )
{
    return p->nLast;
}
static inline void Rec_IntPush( Rec_Int_t * p, int Entry )
{
    if ( (p->nSize >> p->nShift) == Vec_PtrSize(p->vPages) )
        Vec_PtrPush( p->vPages, ABC_ALLOC(int, p->Mask+1) );
    ((int*)Vec_PtrEntry(p->vPages, p->nSize >> p->nShift))[p->nSize++ & p->Mask] = Entry;
}
static inline void Rec_IntAppend( Rec_Int_t * p, int * pArray, int nSize )
{
    assert( nSize <= p->Mask );
    if ( (p->nSize & p->Mask) + nSize >= p->Mask )
    {
        Rec_IntPush( p, 0 );
        p->nSize = ((p->nSize >> p->nShift) + 1) * (p->Mask + 1);
    }
    if ( (p->nSize >> p->nShift) == Vec_PtrSize(p->vPages) )
        Vec_PtrPush( p->vPages, ABC_ALLOC(int, p->Mask+1) );
//    assert( (p->nSize >> p->nShift) + 1 == Vec_PtrSize(p->vPages) );
    memmove( (int*)Vec_PtrEntry(p->vPages, p->nSize >> p->nShift) + (p->nSize & p->Mask), pArray, sizeof(int) * nSize );
    p->nLast = p->nSize;
    p->nSize += nSize;
}
static inline int Rec_IntEntry( Rec_Int_t * p, int i )
{
    return ((int*)p->vPages->pArray[i >> p->nShift])[i & p->Mask];
}
static inline int * Rec_IntEntryP( Rec_Int_t * p, int i )
{
    return (int*)p->vPages->pArray[i >> p->nShift] + (i & p->Mask);
}
static inline void Rec_IntFree( Rec_Int_t * p )
{
    Vec_PtrFreeFree( p->vPages );
    ABC_FREE( p );
}

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

static inline satset* Proof_NodeRead    (Vec_Int_t* p, cla h )    { return satset_read( (veci*)p, h );   }
static inline cla     Proof_NodeHandle  (Vec_Int_t* p, satset* c) { return satset_handle( (veci*)p, c ); }
static inline int     Proof_NodeCheck   (Vec_Int_t* p, satset* c) { return satset_check( (veci*)p, c );  }
static inline int     Proof_NodeSize    (int nEnts)               { return sizeof(satset)/4 + nEnts;     }

static inline satset* Proof_ResolveRead (Rec_Int_t* p, cla h )    { return (satset*)Rec_IntEntryP(p, h); }

// iterating through nodes in the proof
#define Proof_ForeachNode( p, pNode, h )                         \
    for ( h = 1; (h < Vec_IntSize(p)) && ((pNode) = Proof_NodeRead(p, h)); h += Proof_NodeSize(pNode->nEnts) )
#define Proof_ForeachNodeVec( pVec, p, pNode, i )            \
    for ( i = 0; (i < Vec_IntSize(pVec)) && ((pNode) = Proof_NodeRead(p, Vec_IntEntry(pVec,i))); i++ )

// iterating through fanins of a proof node
#define Proof_NodeForeachFanin( p, pNode, pFanin, i )        \
    for ( i = 0; (i < (int)pNode->nEnts) && (((pFanin) = (pNode->pEnts[i] & 1) ? NULL : Proof_NodeRead(p, pNode->pEnts[i] >> 2)), 1); i++ )
#define Proof_NodeForeachLeaf( pLeaves, pNode, pLeaf, i )    \
    for ( i = 0; (i < (int)pNode->nEnts) && (((pLeaf) = (pNode->pEnts[i] & 1) ? Proof_NodeRead(pLeaves, pNode->pEnts[i] >> 2) : NULL), 1); i++ )
#define Proof_NodeForeachFaninLeaf( p, pLeaves, pNode, pFanin, i )    \
    for ( i = 0; (i < (int)pNode->nEnts) && ((pFanin) = (pNode->pEnts[i] & 1) ? Proof_NodeRead(pLeaves, pNode->pEnts[i] >> 2) : Proof_NodeRead(p, pNode->pEnts[i] >> 2)); i++ )


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
void Proof_CollectUsed_iter( Vec_Int_t * vProof, satset * pNode, Vec_Int_t * vUsed, Vec_Int_t * vStack )
{
    satset * pNext;
    int i, hNode;
    if ( pNode->Id )
        return;
    // start with node
    pNode->Id = 1;
    Vec_IntPush( vStack, Proof_NodeHandle(vProof, pNode) << 1 );
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
                Vec_IntPush( vStack, Proof_NodeHandle(vProof, pNext) << 1 ); // add first time
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
        Proof_CollectUsed_iter( vProof, Proof_NodeRead(vProof, hRoot), vUsed, vStack );
    else
    {
        satset * pNode;
        int i;
        Proof_ForeachNodeVec( vRoots, vProof, pNode, i )
            Proof_CollectUsed_iter( vProof, pNode, vUsed, vStack );
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
void Proof_CollectUsed_rec( Vec_Int_t * vProof, satset * pNode, Vec_Int_t * vUsed )
{
    satset * pNext;
    int i;
    if ( pNode->Id )
        return;
    pNode->Id = 1;
    Proof_NodeForeachFanin( vProof, pNode, pNext, i )
        if ( pNext && !pNext->Id )
            Proof_CollectUsed_rec( vProof, pNext, vUsed );
    Vec_IntPush( vUsed, Proof_NodeHandle(vProof, pNode) );
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
        Proof_CollectUsed_rec( vProof, Proof_NodeRead(vProof, hRoot), vUsed );
    else
    {
        satset * pNode;
        int i;
        Proof_ForeachNodeVec( vRoots, vProof, pNode, i )
            Proof_CollectUsed_rec( vProof, pNode, vUsed );
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





#if 0
 
/**Function*************************************************************

  Synopsis    [Performs one resultion step.]

  Description [Returns ID of the resolvent if success, and -1 if failure.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
satset * Sat_ProofCheckResolveOne( Vec_Int_t * p, satset * c1, satset * c2, Vec_Int_t * vTemp )
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
satset * Sat_ProofCheckReadOne( Vec_Int_t * vClauses, Vec_Int_t * vProof, Vec_Int_t * vResolves, int iAnt )
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
void Sat_ProofCheck( Vec_Int_t * vClauses, Vec_Int_t * vProof, int hRoot )
{
    Vec_Int_t * vUsed, * vResolves, * vTemp;
    satset * pSet, * pSet0, * pSet1;
    int i, k, Counter = 0, clk = clock(); 
    // collect visited clauses
    vUsed = Proof_CollectUsedIter( vProof, NULL, hRoot );
    Proof_CleanCollected( vProof, vUsed );
    // perform resolution steps
    vTemp = Vec_IntAlloc( 1000 );
    vResolves = Vec_IntAlloc( 1000 );
    Vec_IntPush( vResolves, -1 );
    Proof_ForeachNodeVec( vUsed, vProof, pSet, i )
    {
        pSet0 = Sat_ProofCheckReadOne( vClauses, vProof, vResolves, pSet->pEnts[0] );
        for ( k = 1; k < (int)pSet->nEnts; k++ )
        {
            pSet1 = Sat_ProofCheckReadOne( vClauses, vProof, vResolves, pSet->pEnts[k] );
            pSet0 = Sat_ProofCheckResolveOne( vResolves, pSet0, pSet1, vTemp );
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

#endif

/**Function*************************************************************

  Synopsis    [Performs one resultion step.]

  Description [Returns ID of the resolvent if success, and -1 if failure.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
satset * Sat_ProofCheckResolveOne( Rec_Int_t * p, satset * c1, satset * c2, Vec_Int_t * vTemp )
{
    satset * c;
    int i, k, Var = -1, Count = 0;
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
    Vec_IntPush( vTemp, 0 ); // placeholder
    Vec_IntPush( vTemp, 0 );
    for ( i = 0; i < (int)c1->nEnts; i++ )
        if ( (c1->pEnts[i] >> 1) != Var )
            Vec_IntPush( vTemp, c1->pEnts[i] );
    for ( i = 0; i < (int)c2->nEnts; i++ )
        if ( (c2->pEnts[i] >> 1) != Var )
            Vec_IntPushUnique( vTemp, c2->pEnts[i] );
    // create new resolution entry
    Rec_IntAppend( p, Vec_IntArray(vTemp), Vec_IntSize(vTemp) );
    // return the new entry
    c = Proof_ResolveRead( p, Rec_IntSizeLast(p) );
    c->nEnts = Vec_IntSize(vTemp)-2;
    return c;
}

/**Function*************************************************************

  Synopsis    [Checks the proof for consitency.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
satset * Sat_ProofCheckReadOne( Vec_Int_t * vClauses, Vec_Int_t * vProof, Rec_Int_t * vResolves, int iAnt )
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
    int hRoot = veci_begin(&s->claProofs)[satset_read(&s->learnts, s->hLearntLast>>1)->Id];

    Rec_Int_t * vResolves;
    Vec_Int_t * vUsed, * vTemp;
    satset * pSet, * pSet0, * pSet1;
    int i, k, Counter = 0, clk = clock(); 
    // collect visited clauses
    vUsed = Proof_CollectUsedIter( vProof, NULL, hRoot );
    Proof_CleanCollected( vProof, vUsed );
    // perform resolution steps
    vTemp = Vec_IntAlloc( 1000 );
    vResolves = Rec_IntAlloc( 20 );
    Rec_IntPush( vResolves, -1 );
    Proof_ForeachNodeVec( vUsed, vProof, pSet, i )
    {
        pSet0 = Sat_ProofCheckReadOne( vClauses, vProof, vResolves, pSet->pEnts[0] );
        for ( k = 1; k < (int)pSet->nEnts; k++ )
        {
            pSet1 = Sat_ProofCheckReadOne( vClauses, vProof, vResolves, pSet->pEnts[k] );
            pSet0 = Sat_ProofCheckResolveOne( vResolves, pSet0, pSet1, vTemp );
        }
        pSet->Id = Rec_IntSizeLast( vResolves );
//printf( "Clause for proof %d: ", Vec_IntEntry(vUsed, i) );
//satset_print( pSet0 );
        Counter++;
    }
    Vec_IntFree( vTemp );
    // clean the proof
    Proof_CleanCollected( vProof, vUsed );
    // compare the final clause
    printf( "Used %6.2f Mb for resolvents.\n", 4.0 * Rec_IntSize(vResolves) / (1<<20) );
    if ( pSet0->nEnts > 0 )
        printf( "Cound not derive the empty clause.  " );
    else
        printf( "Proof verification successful.  " );
    Abc_PrintTime( 1, "Time", clock() - clk );
    // cleanup
    Rec_IntFree( vResolves );
    Vec_IntFree( vUsed );
}

/**Function*************************************************************

  Synopsis    [Collects nodes belonging to the UNSAT core.]

  Description [The resulting array contains 0-based IDs of root clauses.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Sat_ProofCollectCore( Vec_Int_t * vClauses, Vec_Int_t * vProof, Vec_Int_t * vUsed )
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
                Vec_IntPush( vCore, Proof_NodeHandle(vClauses, pFanin) );
            }
    }
    // clean core clauses and reexpress core in terms of clause IDs
    Proof_ForeachNodeVec( vCore, vClauses, pNode, i )
    {
        pNode->mark = 0;
        Vec_IntWriteEntry( vCore, i, pNode->Id - 1 );
    }
    return vCore;
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
    int hRoot = veci_begin(&s->claProofs)[satset_read(&s->learnts, s->hLearntLast>>1)->Id];

    Vec_Int_t * vUsed, * vCore, * vCoreNums, * vVarMap;
    satset * pNode, * pFanin;
    Aig_Man_t * pAig;
    Aig_Obj_t * pObj;
    int i, k, iVar, Entry;

    // collect visited nodes
    vUsed = Proof_CollectUsedIter( vProof, NULL, hRoot );
    // collect core clauses (cleans vUsed and vCore)
    vCore = Sat_ProofCollectCore( vClauses, vProof, vUsed );

    // map variables into their global numbers
    vVarMap = Vec_IntStartFull( Vec_IntFindMax(vGlobVars) + 1 );
    Vec_IntForEachEntry( vGlobVars, Entry, i )
        Vec_IntWriteEntry( vVarMap, Entry, i );

    // start the AIG
    pAig = Aig_ManStart( 10000 );
    pAig->pName = Aig_UtilStrsav( "interpol" );
    for ( i = 0; i < Vec_IntSize(vGlobVars); i++ )
        Aig_ObjCreatePi( pAig );

    // copy the numbers out and derive interpol for clause
    vCoreNums = Vec_IntAlloc( Vec_IntSize(vCore) );
    Proof_ForeachNodeVec( vCore, vClauses, pNode, i )
    {
        if ( pNode->partA )
        {
            pObj = Aig_ManConst0( pAig );
            satset_foreach_var( pNode, iVar, k, 0 )
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
    Proof_ForeachNodeVec( vUsed, vProof, pNode, i )
    {
        assert( pNode->nEnts > 1 );
        Proof_NodeForeachFaninLeaf( vProof, vClauses, pNode, pFanin, k )
        {
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
    assert( Proof_NodeHandle(vProof, pNode) == hRoot );
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

  Synopsis    [Computes UNSAT core.]

  Description [The result is the array of root clause indexes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Sat_ProofCore( sat_solver2 * s )
{
    Vec_Int_t * vClauses  = (Vec_Int_t *)&s->clauses;
    Vec_Int_t * vProof    = (Vec_Int_t *)&s->proofs;
    int hRoot = veci_begin(&s->claProofs)[satset_read(&s->learnts, s->hLearntLast>>1)->Id];

    Vec_Int_t * vCore, * vUsed;
    // collect visited clauses
    vUsed = Proof_CollectUsedIter( vProof, NULL, hRoot );
    // collect core clauses 
    vCore = Sat_ProofCollectCore( vClauses, vProof, vUsed );
    Vec_IntFree( vUsed );
    return vCore;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

