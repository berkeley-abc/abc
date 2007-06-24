/**CFile****************************************************************

  FileName    [darCnf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darCnf.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Dereferences the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Dar_CurDeref2( Dar_Man_t * p, Dar_Cut_t * pCut )
{
    Dar_Obj_t * pLeaf;
    int i;
    Dar_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        assert( pLeaf->nRefs > 0 );
        pLeaf->nRefs--;
    }
}

/**Function*************************************************************

  Synopsis    [References the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Dar_CurRef2( Dar_Man_t * p, Dar_Cut_t * pCut )
{
    Dar_Obj_t * pLeaf;
    int i;
    Dar_CutForEachLeaf( p, pCut, pLeaf, i )
        pLeaf->nRefs++;
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void Dar_CutDeref( Dar_Man_t * p, Dar_Cut_t * pCut )
{ 
    Dar_Obj_t * pLeaf;
    int i;
    Dar_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        assert( pLeaf->nRefs > 0 );
        if ( --pLeaf->nRefs > 0 || !Dar_ObjIsAnd(pLeaf) )
            continue;
        Dar_CutDeref( p, Dar_ObjBestCut(pLeaf) );
    }
}

/**Function*************************************************************

  Synopsis    [Computes area of the first level.]

  Description [The cut need to be derefed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_CutRef( Dar_Man_t * p, Dar_Cut_t * pCut )
{
    Dar_Obj_t * pLeaf;
    int i, Area = pCut->Cost;
    Dar_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        assert( pLeaf->nRefs >= 0 );
        if ( pLeaf->nRefs++ > 0 || !Dar_ObjIsAnd(pLeaf) )
            continue;
        Area += Dar_CutRef( p, Dar_ObjBestCut(pLeaf) );
    }
    return Area;
}

/**Function*************************************************************

  Synopsis    [Computes exact area of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_CutArea( Dar_Man_t * p, Dar_Cut_t * pCut )
{
    int Area = Dar_CutRef( p, pCut );
    Dar_CutDeref( p, pCut );
    return Area;
}


/**Function*************************************************************

  Synopsis    [Returns 1 if the second cut is better.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Dar_CutCompare( Dar_Cut_t * pC0, Dar_Cut_t * pC1 )
{
    if ( pC0->Area < pC1->Area - 0.0001 )
        return -1;
    if ( pC0->Area > pC1->Area + 0.0001 ) // smaller area flow is better
        return 1;
/*
    if ( pC0->NoRefs < pC1->NoRefs )
        return -1;
    if ( pC0->NoRefs > pC1->NoRefs ) // fewer non-referenced fanins is better
        return 1;
*/
//    if ( pC0->FanRefs / pC0->nLeaves > pC1->FanRefs / pC1->nLeaves )
//        return -1;

//    if ( pC0->FanRefs / pC0->nLeaves < pC1->FanRefs / pC1->nLeaves )
        return 1; // larger average fanin ref-counter is better
//    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns the cut with the smallest area flow.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Cut_t * Dar_ObjFindBestCut( Dar_Obj_t * pObj )
{
    Dar_Cut_t * pCut, * pCutBest;
    int i;
    pCutBest = NULL;
    Dar_ObjForEachCut( pObj, pCut, i )
        if ( pCutBest == NULL || Dar_CutCompare(pCutBest, pCut) == 1 )
            pCutBest = pCut;
    return pCutBest;
}

/**Function*************************************************************

  Synopsis    [Computes area flow of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_CutAssignAreaFlow( Dar_Man_t * p, Dar_Cut_t * pCut )
{
    Dar_Obj_t * pLeaf;
    int i;
    pCut->Area    = (float)pCut->Cost;
    pCut->NoRefs  = 0;
    pCut->FanRefs = 0;
    Dar_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        if ( !Dar_ObjIsNode(pLeaf) )
            continue;
        if ( pLeaf->nRefs == 0 )
        {
            pCut->Area += Dar_ObjBestCut(pLeaf)->Area;
//            pCut->NoRefs++;
        }
        else
        {
            pCut->Area += Dar_ObjBestCut(pLeaf)->Area / pLeaf->nRefs;
//            if ( pCut->FanRefs + pLeaf->nRefs > 15 )
//                pCut->FanRefs = 15;
//            else
//                pCut->FanRefs += pLeaf->nRefs;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Computes area flow of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_CutAssignArea( Dar_Man_t * p, Dar_Cut_t * pCut )
{
    Dar_Obj_t * pLeaf;
    int i;
    pCut->Area    = (float)pCut->Cost;
    pCut->NoRefs  = 0;
    pCut->FanRefs = 0;
    Dar_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        if ( !Dar_ObjIsNode(pLeaf) )
            continue;
        if ( pLeaf->nRefs == 0 )
        {
            pCut->Area += Dar_ObjBestCut(pLeaf)->Cost;
            pCut->NoRefs++;
        }
        else
        {
            if ( pCut->FanRefs + pLeaf->nRefs > 15 )
                pCut->FanRefs = 15;
            else
                pCut->FanRefs += pLeaf->nRefs;
        }
    }
}


/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManScanMapping_rec( Dar_Man_t * p, Dar_Obj_t * pObj, Vec_Ptr_t * vMapped )
{
    Dar_Obj_t * pLeaf;
    Dar_Cut_t * pCutBest;
    int aArea, i;
    if ( pObj->nRefs++ || Dar_ObjIsPi(pObj) || Dar_ObjIsConst1(pObj) )
        return 0;
    assert( Dar_ObjIsAnd(pObj) );
    // collect the node first to derive pre-order
    if ( vMapped )
    {
//        printf( "%d ", Dar_ObjBestCut(pObj)->Cost );
        Vec_PtrPush( vMapped, pObj );
    }
    // visit the transitive fanin of the selected cut
    pCutBest = Dar_ObjBestCut(pObj);
    aArea = pCutBest->Cost;
    Dar_CutForEachLeaf( p, pCutBest, pLeaf, i )
        aArea += Dar_ManScanMapping_rec( p, pLeaf, vMapped );
    return aArea;
}

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description [Collects the nodes in reverse topological order in array 
  p->vMapping.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Dar_ManScanMapping( Dar_Man_t * p, int fCollect )
{
    Vec_Ptr_t * vMapped = NULL;
    Dar_Obj_t * pObj;
    int i;
    // clean all references
    Dar_ManForEachObj( p, pObj, i )
        pObj->nRefs = 0;
    // allocate the array
    if ( fCollect )
        vMapped = Vec_PtrAlloc( 1000 );
    // collect nodes reachable from POs in the DFS order through the best cuts
    p->aArea = 0;
    Dar_ManForEachPo( p, pObj, i )
        p->aArea += Dar_ManScanMapping_rec( p, Dar_ObjFanin0(pObj), vMapped );
    printf( "Variables = %d. Clauses = %6d.\n", vMapped? Vec_PtrSize(vMapped) : 0, p->aArea );
    return vMapped;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManMapForCnf( Dar_Man_t * p )
{
    Dar_Obj_t * pObj;
    Dar_Cut_t * pCut;
    int i, k;
    // visit the nodes in the topological order and update their best cuts
    Dar_ManForEachObj( p, pObj, i )
    {
        if ( !Dar_ObjIsNode(pObj) )
            continue;
//        if ( pObj->nRefs )
//            continue;

        // if the node is used, dereference its cut
        if ( pObj->nRefs )
            Dar_CutDeref( p, Dar_ObjBestCut(pObj) );
        // evaluate the cuts of this node
        Dar_ObjForEachCut( pObj, pCut, k )
//            Dar_CutAssignArea( p, pCut );
//            Dar_CutAssignAreaFlow( p, pCut );
            pCut->Area = (float)Dar_CutArea( p, pCut );
        // find a new good cut
        Dar_ObjSetBestCut( pObj, Dar_ObjFindBestCut(pObj) );
        // if the node is used, reference its cut
        if ( pObj->nRefs )
            Dar_CutRef( p, Dar_ObjBestCut(pObj) );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the number of literals in the SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_SopCountLiterals( char * pSop, int nCubes )
{
    int nLits = 0, Cube, i, b;
    for ( i = 0; i < nCubes; i++ )
    {
        Cube = pSop[i];
        for ( b = 3; b >= 0; b-- )
        {
            if ( Cube % 3 != 2 )
                nLits++;
            Cube = Cube / 3;
        }
    }
    return nLits;
}

/**Function*************************************************************

  Synopsis    [Writes the cube and returns the number of literals in it.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_SopWriteCube( char Cube, int * pVars, int fCompl, int * pLiterals )
{
    int nLits = 4, b;
    for ( b = 3; b >= 0; b-- )
    {
        if ( Cube % 3 == 0 )
            *pLiterals++ = 2 * pVars[b] + 1 ^ fCompl;
        else if ( Cube % 3 == 1 )
            *pLiterals++ = 2 * pVars[b] + fCompl;
        else
            nLits--;
        Cube = Cube / 3;
    }
    return nLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Cnf_t * Dar_ManWriteCnf( Dar_Man_t * p, Vec_Ptr_t * vMapped )
{
    Dar_Cnf_t * pCnf;
    Dar_Obj_t * pObj;
    Dar_Cut_t * pCut;
    int OutVar, pVars[4], * pLits, ** pClas;
    unsigned uTruth;
    int i, k, nLiterals, nClauses, nCubes, Number;

    // count the number of literals and clauses
    nLiterals = 1 + Dar_ManPoNum( p );
    nClauses = 1 + Dar_ManPoNum( p );
    Vec_PtrForEachEntry( vMapped, pObj, i )
    {
        assert( Dar_ObjIsNode(pObj) );
        pCut = Dar_ObjBestCut( pObj );
        // positive polarity of the cut
        uTruth = pCut->uTruth;
        nLiterals += Dar_SopCountLiterals( p->pSops[uTruth], p->pSopSizes[uTruth] ) + p->pSopSizes[uTruth];
        nClauses += p->pSopSizes[uTruth];
        // negative polarity of the cut
        uTruth = 0xFFFF & ~pCut->uTruth;
        nLiterals += Dar_SopCountLiterals( p->pSops[uTruth], p->pSopSizes[uTruth] ) + p->pSopSizes[uTruth];
        nClauses += p->pSopSizes[uTruth];
    }

    // allocate CNF
    pCnf = ALLOC( Dar_Cnf_t, 1 );
    memset( pCnf, 0, sizeof(Dar_Cnf_t) );
    pCnf->nLiterals = nLiterals;
    pCnf->nClauses = nClauses;
    pCnf->pClauses = ALLOC( int *, nClauses );
    pCnf->pClauses[0] = ALLOC( int, nLiterals );
    pCnf->pVarNums = ALLOC( int, 1+Dar_ManObjIdMax(p) );

    // set variable numbers
    Number = 0;
    memset( pCnf->pVarNums, 0xff, sizeof(int) * (1+Dar_ManObjIdMax(p)) );
    Vec_PtrForEachEntry( vMapped, pObj, i )
        pCnf->pVarNums[pObj->Id] = Number++;
    Dar_ManForEachPi( p, pObj, i )
        pCnf->pVarNums[pObj->Id] = Number++;
    pCnf->pVarNums[Dar_ManConst1(p)->Id] = Number++;

    // assign the clauses
    pLits = pCnf->pClauses[0];
    pClas = pCnf->pClauses;
    Vec_PtrForEachEntry( vMapped, pObj, i )
    {
        pCut = Dar_ObjBestCut( pObj );
        // write variables of this cut
        OutVar = pCnf->pVarNums[ pObj->Id ];
        for ( k = 0; k < (int)pCut->nLeaves; k++ )
        {
            pVars[k] = pCnf->pVarNums[ pCut->pLeaves[k] ];
            assert( pVars[k] <= Dar_ManObjIdMax(p) );
        }

        // positive polarity of the cut
        uTruth = pCut->uTruth;
        nCubes = p->pSopSizes[uTruth];
        // write the cubes
        for ( k = 0; k < nCubes; k++ )
        {
            *pClas++ = pLits;
            *pLits++ = 2 * pVars[OutVar] + 1; 
            pLits += Dar_SopWriteCube( p->pSops[uTruth][k], pVars, 0, pLits );
        }

        // negative polarity of the cut
        uTruth = 0xFFFF & ~pCut->uTruth;
        nCubes = p->pSopSizes[uTruth];
        // write the cubes
        for ( k = 0; k < nCubes; k++ )
        {
            *pClas++ = pLits;
            *pLits++ = 2 * pVars[OutVar]; 
            pLits += Dar_SopWriteCube( p->pSops[uTruth][k], pVars, 1, pLits );
        }
    }

    // write the output literals
    Dar_ManForEachPo( p, pObj, i )
    {
        OutVar = pCnf->pVarNums[ Dar_ObjFanin0(pObj)->Id ];
        *pClas++ = pLits;
        *pLits++ = 2 * pVars[OutVar] + Dar_ObjFaninC0(pObj); 
    }
    // write the constant literal
    OutVar = pCnf->pVarNums[ Dar_ManConst1(p)->Id ];
    assert( OutVar <= Dar_ManObjIdMax(p) );
    *pClas++ = pLits;
    *pLits++ = 2 * pVars[OutVar]; 

    // verify that the correct number of literals and clauses was written
    assert( pLits - pCnf->pClauses[0] == nLiterals );
    assert( pClas - pCnf->pClauses == nClauses );
    return pCnf;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_CnfFree( Dar_Cnf_t * pCnf )
{
    if ( pCnf == NULL )
        return;
    free( pCnf->pClauses[0] );
    free( pCnf->pClauses );
    free( pCnf->pVarNums );
    free( pCnf );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManExploreMapping( Dar_Man_t * p )
{
    extern int Dar_ManLargeCutEval( Dar_Man_t * p, Dar_Obj_t * pRoot, Dar_Cut_t * pCutR, Dar_Cut_t * pCutL, int Leaf );
    int nNew, Gain, nGain = 0, nVars = 0;

    Dar_Obj_t * pObj, * pLeaf;
    Dar_Cut_t * pCutBest, * pCut;
    int i, k, a, b, Counter;
    Dar_ManForEachObj( p, pObj, i )
    {
        if ( !Dar_ObjIsNode(pObj) )
            continue;
        if ( pObj->nRefs == 0 )
            continue;
        pCutBest = Dar_ObjBestCut(pObj);
        Dar_CutForEachLeaf( p, pCutBest, pLeaf, k )
        {
            if ( !Dar_ObjIsNode(pLeaf) )
                continue;
            assert( pLeaf->nRefs != 0 );
            if ( pLeaf->nRefs != 1 )
                continue;
            pCut = Dar_ObjBestCut(pLeaf);
/*
            // find how many common variable they have
            Counter = 0;
            for ( a = 0; a < (int)pCut->nLeaves; a++ )
            {
                for ( b = 0; b < (int)pCutBest->nLeaves; b++ )
                    if ( pCut->pLeaves[a] == pCutBest->pLeaves[b] )
                        break;
                if ( b == (int)pCutBest->nLeaves )
                    continue;
                Counter++;
            }
            printf( "%d ", Counter );
*/
            // find the new truth table after collapsing these two cuts
            nNew = Dar_ManLargeCutEval( p, pObj, pCutBest, pCut, pLeaf->Id );
//            printf( "%d+%d=%d:%d(%d) ", pCutBest->Cost, pCut->Cost, 
//                pCutBest->Cost+pCut->Cost, nNew, pCutBest->Cost+pCut->Cost-nNew );

            Gain = pCutBest->Cost+pCut->Cost-nNew;
            if ( Gain > 0 )
            {
                nGain += Gain;
                nVars++;
            }
        }
    }
    printf( "Total gain = %d.  Vars = %d.\n", nGain, nVars );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Cnf_t * Dar_ManDeriveCnf( Dar_Man_t * p )
{
    Dar_Cnf_t * pCnf = NULL;
    Vec_Ptr_t * vMapped;
    int i, nIters = 2;
    int clk;

    // derive SOPs for all 4-variable functions
clk = clock();
    Dar_LibReadMsops( &p->pSopSizes, &p->pSops );
PRT( "setup", clock() - clk );

    // generate cuts for all nodes, assign cost, and find best cuts
    // (used pObj->pNext for storing the best cut of the node!)
clk = clock();
    Dar_ManComputeCuts( p );
PRT( "cuts ", clock() - clk );

    // iteratively improve area flow
    for ( i = 0; i < nIters; i++ )
    {
clk = clock();
        Dar_ManScanMapping( p, 0 );
        Dar_ManMapForCnf( p );
PRT( "iter ", clock() - clk );
    }

    // write the file
    vMapped = Dar_ManScanMapping( p, 1 );
clk = clock();
    Dar_ManExploreMapping( p );
PRT( "exten", clock() - clk );
//    pCnf = Dar_ManWriteCnf( p, vMapped );
    Vec_PtrFree( vMapped );

    // clean up
    Dar_ManCutsFree( p );
    return pCnf;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


