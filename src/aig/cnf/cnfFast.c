/**CFile****************************************************************

  FileName    [cnfFast.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG-to-CNF conversion.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: cnfFast.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cnf.h"
#include "kit.h"
#include "satSolver.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Detects multi-input gate rooted at this node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_CollectSuper_rec( Aig_Obj_t * pRoot, Aig_Obj_t * pObj, Vec_Ptr_t * vSuper, int fStopCompl )
{
    if ( pRoot != pObj && (pObj->fMarkA || (fStopCompl && Aig_IsComplement(pObj))) )
    {
        Vec_PtrPushUnique( vSuper, fStopCompl ? pObj : Aig_Regular(pObj) );
        return;
    }
    assert( Aig_ObjIsNode(pObj) );
    if ( fStopCompl )
    {
        Cnf_CollectSuper_rec( pRoot, Aig_ObjChild0(pObj), vSuper, 1 );
        Cnf_CollectSuper_rec( pRoot, Aig_ObjChild1(pObj), vSuper, 1 );
    }
    else
    {
        Cnf_CollectSuper_rec( pRoot, Aig_ObjFanin0(pObj), vSuper, 0 );
        Cnf_CollectSuper_rec( pRoot, Aig_ObjFanin1(pObj), vSuper, 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Detects multi-input gate rooted at this node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_CollectSuper( Aig_Obj_t * pRoot, Vec_Ptr_t * vSuper, int fStopCompl )
{
    assert( !Aig_IsComplement(pRoot) );
    Vec_PtrClear( vSuper );
    Cnf_CollectSuper_rec( pRoot, pRoot, vSuper, fStopCompl );
}

/**Function*************************************************************

  Synopsis    [Collects nodes inside the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_CollectVolume_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    if ( Aig_ObjIsTravIdCurrent( p, pObj ) )
        return;
    Aig_ObjSetTravIdCurrent( p, pObj );
    assert( Aig_ObjIsNode(pObj) );
    Cnf_CollectVolume_rec( p, Aig_ObjFanin0(pObj), vNodes );
    Cnf_CollectVolume_rec( p, Aig_ObjFanin1(pObj), vNodes );
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Collects nodes inside the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_CollectVolume( Aig_Man_t * p, Aig_Obj_t * pRoot, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vNodes )
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManIncrementTravId( p );
    Vec_PtrForEachEntry( Aig_Obj_t *, vLeaves, pObj, i )
        Aig_ObjSetTravIdCurrent( p, pObj );
    Vec_PtrClear( vNodes );
    Cnf_CollectVolume_rec( p, pRoot, vNodes );
}

/**Function*************************************************************

  Synopsis    [Derive truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Cnf_CutDeriveTruth( Aig_Man_t * p, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vNodes )
{
    static word Truth6[6] = {
        0xAAAAAAAAAAAAAAAA,
        0xCCCCCCCCCCCCCCCC,
        0xF0F0F0F0F0F0F0F0,
        0xFF00FF00FF00FF00,
        0xFFFF0000FFFF0000,
        0xFFFFFFFF00000000
    };
    static word C[2] = { 0, ~0 };
    static word S[256];
    Aig_Obj_t * pObj;
    int i;
    assert( Vec_PtrSize(vLeaves) <= 6 && Vec_PtrSize(vNodes) > 0 );
    assert( Vec_PtrSize(vLeaves) + Vec_PtrSize(vNodes) <= 256 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vLeaves, pObj, i )
    {
        pObj->iData    = i;
        S[pObj->iData] = Truth6[i];
    }
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
    {
        pObj->iData    = Vec_PtrSize(vLeaves) + i;
        S[pObj->iData] = (S[Aig_ObjFanin0(pObj)->iData] ^ C[Aig_ObjFaninC0(pObj)]) & 
                         (S[Aig_ObjFanin1(pObj)->iData] ^ C[Aig_ObjFaninC1(pObj)]);
    }
    return S[pObj->iData];
}


/**Function*************************************************************

  Synopsis    [Marks AIG for CNF computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_DeriveFastMark_( Aig_Man_t * p )
{
    Vec_Ptr_t * vLeaves, * vNodes;
    Aig_Obj_t * pObj, * pObjC, * pObj0, * pObj1;
    int i, k;
    // mark CIs
    Aig_ManForEachPi( p, pObj, i )
        pObj->fMarkA = 1;
    // mark CO drivers
    Aig_ManForEachPo( p, pObj, i )
        Aig_ObjFanin0(pObj)->fMarkA = 1;


    // mark roots/leaves of MUX/XOR with MarkA
    // mark internal nodes of MUX/XOR with MarkB
    Aig_ManForEachNode( p, pObj, i )
    {
        if ( !Aig_ObjIsMuxType(pObj) )
            continue;
        pObjC = Aig_ObjRecognizeMux( pObj, &pObj1, &pObj0 );
        Aig_Regular(pObjC)->fMarkA = 1;
        Aig_Regular(pObj1)->fMarkA = 1;
        Aig_Regular(pObj0)->fMarkA = 1;

        Aig_ObjFanin0(pObj)->fMarkB = 1;
        Aig_ObjFanin1(pObj)->fMarkB = 1;
    }

    // mark nodes with many fanouts or pointed to by a complemented edge
    Aig_ManForEachNode( p, pObj, i )
    {
        if ( Aig_ObjRefs(pObj) > 1 )
            pObj->fMarkA = 1;
        if ( Aig_ObjFaninC0(pObj) )
            Aig_ObjFanin0(pObj)->fMarkA = 1;
        if ( Aig_ObjFaninC1(pObj) )
            Aig_ObjFanin1(pObj)->fMarkA = 1;
    }

    // clean internal nodes of MUX/XOR
    Aig_ManForEachNode( p, pObj, i )
    {
        if ( pObj->fMarkB )
            pObj->fMarkB = pObj->fMarkA = 0;
//            pObj->fMarkB = 0;
    }
    // remove nodes those fanins are used
    Aig_ManForEachNode( p, pObj, i )
        if ( pObj->fMarkA && Aig_ObjFanin0(pObj)->fMarkA && Aig_ObjFanin1(pObj)->fMarkA )
            pObj->fMarkA = 0;

    // mark CO drivers
    Aig_ManForEachPo( p, pObj, i )
        Aig_ObjFanin0(pObj)->fMarkA = 1;
/*
    // if node has multiple fanout
    Aig_ManForEachNode( p, pObj, i )
    {
        if ( Aig_ObjRefs(pObj) == 1 )
            continue;
        if ( Aig_ObjRefs(pObj) == 2 && Aig_ObjFanin0(pObj)->fMarkA && Aig_ObjFanin1(pObj)->fMarkA )
            continue;
        pObj->fMarkA = 1;
    }
*/
    // consider large cuts and mark inputs that are
    vLeaves = Vec_PtrAlloc( 100 );
    vNodes  = Vec_PtrAlloc( 100 );
/*
    while ( 1 )
    {
        int fChanges = 0;
        Aig_ManForEachNode( p, pObj, i )
        {
            if ( !pObj->fMarkA )
                continue;
            if ( Aig_ObjRefs(pObj) == 1 )
                continue;

            Cnf_CollectSuper( pObj, vLeaves, 1 );
            if ( Vec_PtrSize(vLeaves) <= 6 )
                continue;
            Vec_PtrForEachEntry( Aig_Obj_t *, vLeaves, pObjC, k )
            {
                if ( Aig_Regular(pObjC)->fMarkA == 0 )
                    fChanges = 1;
                Aig_Regular(pObjC)->fMarkA = 1;
            }
        }
        printf( "Round 1 \n" );
        if ( !fChanges )
            break;
    }
*/
    while ( 1 )
    {
        int fChanges = 0;
        Aig_ManForEachNode( p, pObj, i )
        {
            if ( !pObj->fMarkA )
                continue;
            Cnf_CollectSuper( pObj, vLeaves, 0 );
            if ( Vec_PtrSize(vLeaves) <= 6 )
                continue;
            Cnf_CollectVolume( p, pObj, vLeaves, vNodes );
            Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObjC, k )
            {
                if ( Aig_ObjFaninC0(pObjC) && !Aig_ObjFanin0(pObjC)->fMarkA )
                {
                    Aig_ObjFanin0(pObjC)->fMarkA = 1;
//                    printf( "%d ", Aig_ObjFaninId0(pObjC) );
                    fChanges = 1;
                }
                if ( Aig_ObjFaninC1(pObjC) && !Aig_ObjFanin1(pObjC)->fMarkA )
                {
                    Aig_ObjFanin1(pObjC)->fMarkA = 1;
//                    printf( "%d ", Aig_ObjFaninId1(pObjC) );
                    fChanges = 1;
                }
            }
        }
        printf( "Round 2\n" );
        if ( !fChanges )
            break;
    }


    Vec_PtrFree( vLeaves );
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    [Marks AIG for CNF computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_DeriveFastMark( Aig_Man_t * p )
{
    Vec_Ptr_t * vLeaves, * vNodes;
    Aig_Obj_t * pObj, * pObjC, * pObj0, * pObj1;
    int i, k, Counter;
    Aig_ManCleanMarkAB( p );

    // mark CIs
    Aig_ManForEachPi( p, pObj, i )
        pObj->fMarkA = 1;

    // mark CO drivers
    Aig_ManForEachPo( p, pObj, i )
        Aig_ObjFanin0(pObj)->fMarkA = 1;

    Aig_ManForEachNode( p, pObj, i )
    {
        // mark nodes with many fanouts
        if ( Aig_ObjRefs(pObj) > 1 )
            pObj->fMarkA = 1;
        // mark nodes pointed to by a complemented edge
        if ( Aig_ObjFaninC0(pObj) )
            Aig_ObjFanin0(pObj)->fMarkA = 1;
        if ( Aig_ObjFaninC1(pObj) )
            Aig_ObjFanin1(pObj)->fMarkA = 1;

        // mark roots/leaves of MUX/XOR with MarkA
        // mark internal nodes of MUX/XOR with MarkB
        if ( !Aig_ObjIsMuxType(pObj) )
            continue;

        pObjC = Aig_ObjRecognizeMux( pObj, &pObj1, &pObj0 );
        Aig_Regular(pObjC)->fMarkA = 1;
        Aig_Regular(pObj1)->fMarkA = 1;
        Aig_Regular(pObj0)->fMarkA = 1;

        Aig_ObjFanin0(pObj)->fMarkB = 1;
        Aig_ObjFanin1(pObj)->fMarkB = 1;
    }

    // clean internal nodes of MUX/XOR
    Aig_ManForEachNode( p, pObj, i )
    {
        if ( !pObj->fMarkB )
            continue;
        pObj->fMarkB = 0;
        if ( Aig_ObjRefs(pObj) == 1 )
            pObj->fMarkA = 0;
    }

    // remove nodes those fanins are used
    Aig_ManForEachNode( p, pObj, i )
        if ( pObj->fMarkA && Aig_ObjFanin0(pObj)->fMarkA && Aig_ObjFanin1(pObj)->fMarkA )
            pObj->fMarkA = 0;

    // mark CO drivers
    Aig_ManForEachPo( p, pObj, i )
        Aig_ObjFanin0(pObj)->fMarkA = 1;


    vLeaves = Vec_PtrAlloc( 100 );
    vNodes  = Vec_PtrAlloc( 100 );

    while ( 1 )
    {
        int nChanges = 0;
        Aig_ManForEachNode( p, pObj, i )
        {
            if ( !pObj->fMarkA )
                continue;
            Cnf_CollectSuper( pObj, vLeaves, 0 );
            if ( Vec_PtrSize(vLeaves) <= 6 )
                continue;
            Cnf_CollectVolume( p, pObj, vLeaves, vNodes );
            Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObjC, k )
            {
                if ( Aig_ObjFaninC0(pObjC) && !Aig_ObjFanin0(pObjC)->fMarkA )
                {
                    Aig_ObjFanin0(pObjC)->fMarkA = 1;
//                    printf( "%d ", Aig_ObjFaninId0(pObjC) );
                    nChanges++;
                }
                if ( Aig_ObjFaninC1(pObjC) && !Aig_ObjFanin1(pObjC)->fMarkA )
                {
                    Aig_ObjFanin1(pObjC)->fMarkA = 1;
//                    printf( "%d ", Aig_ObjFaninId1(pObjC) );
                    nChanges++;
                }
            }
        }
        printf( "Made %d gate changes\n", nChanges );
        if ( !nChanges )
            break;
    }

    // check CO drivers
    Counter = 0;
    Aig_ManForEachPo( p, pObj, i )
        Counter += !Aig_ObjFanin0(pObj)->fMarkA;
    printf( "PO-driver rule is violated %d times.\n", Counter );

    // check that the AND-gates are fine
    Counter = 0;
    Aig_ManForEachNode( p, pObj, i )
    {
        assert( pObj->fMarkB == 0 );
        if ( !pObj->fMarkA )
            continue;
        Cnf_CollectSuper( pObj, vLeaves, 0 );
        if ( Vec_PtrSize(vLeaves) <= 6 )
            continue;
        Cnf_CollectVolume( p, pObj, vLeaves, vNodes );
        Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj1, k )
        {
            if ( Aig_ObjFaninC0(pObj1) && !Aig_ObjFanin0(pObj1)->fMarkA )
                Counter++;
            if ( Aig_ObjFaninC1(pObj1) && !Aig_ObjFanin1(pObj1)->fMarkA )
                Counter++;
        }
    }
    Vec_PtrFree( vLeaves );
    Vec_PtrFree( vNodes );

    printf( "AND-gate rule is violated %d times.\n", Counter );
}


/**Function*************************************************************

  Synopsis    [Counts the number of clauses.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_CutCountClauses( Aig_Man_t * p, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vNodes, Vec_Int_t * vCover )
{
    word Truth;
    Aig_Obj_t * pObj;
    int i, RetValue, nSize = 0;
    if ( Vec_PtrSize(vLeaves) > 6 )
    {
        // make sure this is an AND gate
        Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        {
            if ( Aig_ObjFaninC0(pObj) && !Aig_ObjFanin0(pObj)->fMarkA )
                printf( "Unusual 1!\n" );
            if ( Aig_ObjFaninC1(pObj) && !Aig_ObjFanin1(pObj)->fMarkA )
                printf( "Unusual 2!\n" );
            continue;

            assert( !Aig_ObjFaninC0(pObj) || Aig_ObjFanin0(pObj)->fMarkA );
            assert( !Aig_ObjFaninC1(pObj) || Aig_ObjFanin1(pObj)->fMarkA );
        }
        return Vec_PtrSize(vLeaves) + 1;
    }
    Truth = Cnf_CutDeriveTruth( p, vLeaves, vNodes );

    RetValue = Kit_TruthIsop( (unsigned *)&Truth, Vec_PtrSize(vLeaves), vCover, 0 );
    assert( RetValue >= 0 );
    nSize += Vec_IntSize(vCover);

    Truth = ~Truth;

    RetValue = Kit_TruthIsop( (unsigned *)&Truth, Vec_PtrSize(vLeaves), vCover, 0 );
    assert( RetValue >= 0 );
    nSize += Vec_IntSize(vCover);
    return nSize;
}

/**Function*************************************************************

  Synopsis    [Counts the size of the CNF, assuming marks are set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_CountCnfSize( Aig_Man_t * p )
{
    Vec_Ptr_t * vLeaves, * vNodes;
    Vec_Int_t * vCover;
    Aig_Obj_t * pObj;
    int nVars = 0, nClauses = 0;
    int i, nSize;

    vLeaves = Vec_PtrAlloc( 100 );
    vNodes  = Vec_PtrAlloc( 100 );
    vCover  = Vec_IntAlloc( 1 << 16 );

    Aig_ManForEachObj( p, pObj, i )
        nVars += pObj->fMarkA;

    Aig_ManForEachNode( p, pObj, i )
    {
        if ( !pObj->fMarkA )
            continue;
        Cnf_CollectSuper( pObj, vLeaves, 0 );
        Cnf_CollectVolume( p, pObj, vLeaves, vNodes );
        assert( pObj == Vec_PtrEntryLast(vNodes) );

        nSize = Cnf_CutCountClauses( p, vLeaves, vNodes, vCover );
//        printf( "%d(%d) ", Vec_PtrSize(vLeaves), nSize );

        nClauses += nSize;
    }
//    printf( "\n" );
    printf( "Vars = %d  Clauses = %d\n", nVars, nClauses );

    Vec_PtrFree( vLeaves );
    Vec_PtrFree( vNodes );
    Vec_IntFree( vCover );
    return nClauses;
}

/**Function*************************************************************

  Synopsis    [Derives CNF from the marked AIG.]

  Description [Assumes that marking is such that when we traverse from each
  marked node, the logic cone has 6 inputs or less, or it is a multi-input AND.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cnf_Dat_t * Cnf_DeriveFastClauses( Aig_Man_t * p, int nOutputs )
{
    Cnf_Dat_t * pCnf;
    Vec_Int_t * vLits, * vClas, * vMap;
    Vec_Ptr_t * vLeaves, * vNodes;
    Vec_Int_t * vCover;
    Aig_Obj_t * pObj, * pLeaf;
    int i, c, k, nVars, Cube, Entry, OutLit, DriLit, RetValue;
    word Truth;

    vLits = Vec_IntAlloc( 1 << 16 );
    vClas = Vec_IntAlloc( 1 << 12 );
    vMap  = Vec_IntStartFull( Aig_ManObjNumMax(p) );

    // assign variables for the outputs
    nVars = 1;
    if ( nOutputs )
    {
        if ( Aig_ManRegNum(p) == 0 )
        {
            assert( nOutputs == Aig_ManPoNum(p) );
            Aig_ManForEachPo( p, pObj, i )
                Vec_IntWriteEntry( vMap, Aig_ObjId(pObj), nVars++ );
        }
        else
        {
            assert( nOutputs == Aig_ManRegNum(p) );
            Aig_ManForEachLiSeq( p, pObj, i )
                Vec_IntWriteEntry( vMap, Aig_ObjId(pObj), nVars++ );
        }
    }
    // assign variables to the internal nodes
    Aig_ManForEachNodeReverse( p, pObj, i )
        if ( pObj->fMarkA )
            Vec_IntWriteEntry( vMap, Aig_ObjId(pObj), nVars++ );
    // assign variables to the PIs and constant node
    Aig_ManForEachPi( p, pObj, i )
        Vec_IntWriteEntry( vMap, Aig_ObjId(pObj), nVars++ );
    Vec_IntWriteEntry( vMap, Aig_ObjId(Aig_ManConst1(p)), nVars++ );

    // create clauses
    vLeaves = Vec_PtrAlloc( 100 );
    vNodes  = Vec_PtrAlloc( 100 );
    vCover  = Vec_IntAlloc( 1 << 16 );
    Aig_ManForEachNodeReverse( p, pObj, i )
    {
        if ( !pObj->fMarkA )
            continue;
        OutLit = toLit( Vec_IntEntry(vMap, Aig_ObjId(pObj)) );
        // detect cone
        Cnf_CollectSuper( pObj, vLeaves, 0 );
        Cnf_CollectVolume( p, pObj, vLeaves, vNodes );
        assert( pObj == Vec_PtrEntryLast(vNodes) );
        // check if this is an AND-gate
        Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pLeaf, k )
        {
            if ( Aig_ObjFaninC0(pLeaf) && !Aig_ObjFanin0(pLeaf)->fMarkA )
                break;
            if ( Aig_ObjFaninC1(pLeaf) && !Aig_ObjFanin1(pLeaf)->fMarkA )
                break;
        }
        if ( k == Vec_PtrSize(vNodes) )
        {
            Cnf_CollectSuper( pObj, vLeaves, 1 );
            // write big clause
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPush( vLits, OutLit );
            Vec_PtrForEachEntry( Aig_Obj_t *, vLeaves, pLeaf, k )
                Vec_IntPush( vLits, toLitCond(Vec_IntEntry(vMap, Aig_ObjId(Aig_Regular(pLeaf))), !Aig_IsComplement(pLeaf)) );
            // write small clauses
            Vec_PtrForEachEntry( Aig_Obj_t *, vLeaves, pLeaf, k )
            {
                Vec_IntPush( vClas, Vec_IntSize(vLits) );
                Vec_IntPush( vLits, lit_neg(OutLit) );
                Vec_IntPush( vLits, toLitCond(Vec_IntEntry(vMap, Aig_ObjId(Aig_Regular(pLeaf))), Aig_IsComplement(pLeaf)) );
            }
            continue;
        }
        assert( Vec_PtrSize(vLeaves) <= 6 );

        Truth = Cnf_CutDeriveTruth( p, vLeaves, vNodes );
        if ( Truth == 0 || Truth == ~0 )
        {
            assert( RetValue == 0 );
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPush( vLits, (Truth == 0) ? lit_neg(OutLit) : OutLit );
            continue;
        }

        RetValue = Kit_TruthIsop( (unsigned *)&Truth, Vec_PtrSize(vLeaves), vCover, 0 );
        assert( RetValue >= 0 );

        Vec_IntForEachEntry( vCover, Cube, c )
        {
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPush( vLits, OutLit );
            for ( k = 0; k < Vec_PtrSize(vLeaves); k++, Cube >>= 2 )
            {
                if ( (Cube & 3) == 0 )
                    continue;
                assert( (Cube & 3) != 3 );
                Vec_IntPush( vLits, toLitCond( Vec_IntEntry(vMap, Aig_ObjId(Vec_PtrEntry(vLeaves,k))), (Cube&3)!=1 ) );
            }
        }

        Truth = ~Truth;

        RetValue = Kit_TruthIsop( (unsigned *)&Truth, Vec_PtrSize(vLeaves), vCover, 0 );
        assert( RetValue >= 0 );
        Vec_IntForEachEntry( vCover, Cube, c )
        {
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPush( vLits, lit_neg(OutLit) );
            for ( k = 0; k < Vec_PtrSize(vLeaves); k++, Cube >>= 2 )
            {
                if ( (Cube & 3) == 0 )
                    continue;
                assert( (Cube & 3) != 3 );
                Vec_IntPush( vLits, toLitCond( Vec_IntEntry(vMap, Aig_ObjId(Vec_PtrEntry(vLeaves,k))), (Cube&3)==1 ) );
            }
        }
    }
    Vec_PtrFree( vLeaves );
    Vec_PtrFree( vNodes );
    Vec_IntFree( vCover );

    // create clauses for the outputs
    Aig_ManForEachPo( p, pObj, i )
    {
        DriLit = toLitCond( Vec_IntEntry(vMap, Aig_ObjFaninId0(pObj)), Aig_ObjFaninC0(pObj) );
        if ( i < Aig_ManPoNum(p) - nOutputs )
        {
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPush( vLits, DriLit );
        }
        else
        {
            OutLit = toLit( Vec_IntEntry(vMap, Aig_ObjId(pObj)) );
            // first clause
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPush( vLits, OutLit );
            Vec_IntPush( vLits, lit_neg(DriLit) );
            // second clause
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPush( vLits, lit_neg(OutLit) );
            Vec_IntPush( vLits, DriLit );
        }
    }
 
    // write the constant literal
    OutLit = toLit( Vec_IntEntry(vMap, Aig_ObjId(Aig_ManConst1(p))) );
    Vec_IntPush( vClas, Vec_IntSize(vLits) );
    Vec_IntPush( vLits, OutLit );

    // create structure
    pCnf = ABC_CALLOC( Cnf_Dat_t, 1 );
    pCnf->pMan = p;
    pCnf->nVars = nVars;
    pCnf->nLiterals = Vec_IntSize( vLits );
    pCnf->nClauses  = Vec_IntSize( vClas );
    pCnf->pClauses  = ABC_ALLOC( int *, pCnf->nClauses + 1 );
    pCnf->pClauses[0] = Vec_IntReleaseArray( vLits );
    Vec_IntForEachEntry( vClas, Entry, i )
        pCnf->pClauses[i] = pCnf->pClauses[0] + Entry;
    pCnf->pClauses[pCnf->nClauses] = pCnf->pClauses[0] + pCnf->nLiterals;
    pCnf->pVarNums  = Vec_IntReleaseArray( vMap );

    // cleanup
    Vec_IntFree( vLits );
    Vec_IntFree( vClas );
    Vec_IntFree( vMap );
    return pCnf;
}

/**Function*************************************************************

  Synopsis    [Fast CNF computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cnf_Dat_t * Cnf_DeriveFast( Aig_Man_t * p, int nOutputs )
{
    Cnf_Dat_t * pCnf = NULL;
    int clk, clkTotal = clock();
    printf( "\n" );
    Aig_ManCleanMarkAB( p );
    // create initial marking
    clk = clock();
    Cnf_DeriveFastMark( p );
    Abc_PrintTime( 1, "Marking", clock() - clk );
    // compute CNF size
    clk = clock();
    pCnf = Cnf_DeriveFastClauses( p, nOutputs );
    Abc_PrintTime( 1, "Clauses", clock() - clk );
    // derive the resulting CNF
    Aig_ManCleanMarkA( p );
    Abc_PrintTime( 1, "TOTAL  ", clock() - clkTotal );

    printf( "Vars = %6d. Clauses = %7d. Literals = %8d.   \n", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );

//    Cnf_DataFree( pCnf );
//    pCnf = NULL;
    return pCnf;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

