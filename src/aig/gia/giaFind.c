/**CFile****************************************************************

  FileName    [giaFind.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Multiplier detection.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaMulFind.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "gia.h"
#include "misc/util/abc_global.h"
#include "misc/vec/vecInt.h"
#include "misc/vec/vecMem.h"
#include "misc/vec/vecVec.h"
#include "misc/vec/vecWec.h"
#include "misc/util/utilTruth.h"
#include "misc/vec/vecWrd.h"
#include "sat/satoko/solver.h"
#include "misc/vec/vecHsh.h"
#include <complex.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////


Gia_Far_t * Gia_FarAlloc( Gia_Man_t * pGia, int fVerbose );
void Gia_FarFree( Gia_Far_t * p );
Vec_Int_t * Gia_FarFindInputA( Gia_Far_t * p );
Vec_Int_t * Gia_FarFindInputB( Gia_Far_t * p );
int Gia_FarFindInputs( Gia_Far_t * pMan );
int Gia_FarFindInputAB( Gia_Far_t * pMan );

int Gia_FarGetFlag( Gia_Far_t * p, int id );
void Gia_FarSetFlag( Gia_Far_t * p, int id, int flag );
void Gia_FarResetFlag( Gia_Far_t * p );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Returns coupled nodes whose coupled fanout count is >= than the limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManMark0Nodes( Gia_Man_t * p, Vec_Int_t * vNodes, int Value )
{
    Gia_Obj_t * pObj; int i;
    Gia_ManForEachObjVec( vNodes, p, pObj, i )
        pObj->fMark0 = Value;
}
void Gia_ManMark1Nodes( Gia_Man_t * p, Vec_Int_t * vNodes, int Value )
{
    Gia_Obj_t * pObj; int i;
    Gia_ManForEachObjVec( vNodes, p, pObj, i )
        pObj->fMark1 = Value;
}
Vec_Int_t * Gia_MulFindGetCoupledNodes( Gia_Man_t * p, int nFanoutMax, Vec_Int_t * vDetected )
{
    Vec_Int_t * vCoupled = Vec_IntAlloc( 100 );
    Vec_Int_t * vFanCounts = Vec_IntAlloc(0);
    Gia_ManCleanMark01(p);
    // mark detected coupling nodes
    Gia_ManMark1Nodes( p, vDetected, 1 );
    // count the fanouts of each node
    Gia_ManCreateRefs(p);
    // subtract fanouts due to detected partial produces
    Gia_Obj_t * pObj; int i;
    Gia_ManForEachObjVec( vDetected, p, pObj, i ) {
        Gia_ObjRefDec( p, Gia_ObjFanin0(pObj) );
        Gia_ObjRefDec( p, Gia_ObjFanin1(pObj) );
    }
    // mark the nodes whose fanout count >= the limit 
    Gia_ManForEachCand( p, pObj, i )
        if ( Gia_ObjRefNum(p, pObj) >= nFanoutMax )
        {
            pObj->fMark0 = 1;
        }
    // use fixed-point computation to compute the set of coupled nodes
    // (coupled nodes have coupling fanout count that is >= than the limit;
    // coupling nodes have both fanins in the set of coupled nodes)
    int fChanges = 1;
    while ( fChanges ) {
        fChanges = 0;
        // count the number of coupling fanouts
        Vec_IntFill( vFanCounts, Gia_ManObjNum(p), 0 );
        Gia_ManForEachAnd( p, pObj, i )
            if ( !pObj->fMark1 && Gia_ObjFanin0(pObj)->fMark0 && Gia_ObjFanin1(pObj)->fMark0 ) { 
                // pObj is an unused coupling node
                Vec_IntAddToEntry( vFanCounts, Gia_ObjFaninId0(pObj, i), 1 );
                Vec_IntAddToEntry( vFanCounts, Gia_ObjFaninId1(pObj, i), 1 );
            }
        // remove those coupled nodes whose coupling fanout count is under the limit
        Gia_ManForEachCand( p, pObj, i )
            if ( pObj->fMark0 && Vec_IntEntry(vFanCounts, i) < nFanoutMax )
                pObj->fMark0 = 0, fChanges = 1;
    }
    Vec_IntFree( vFanCounts );
    // collect remaining coupled nodes
    Gia_ManForEachCand( p, pObj, i ) 
        if ( pObj->fMark0 ) {
            pObj->fMark0 = 0;
            Vec_IntPush( vCoupled, i );
        }
    // unmark detected coupling nodes
    Gia_ManMark1Nodes( p, vDetected, 0 );

    // remove ref
    ABC_FREE(p->pRefs);
    return vCoupled;
}

/**Function*************************************************************

  Synopsis    [Returns the set of coupling nodes.]

  Description [For the given set of coupled nodes, computes coupling nodes
  (coupling nodes are those and-nodes whose both fanins are coupled nodes).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Gia_MulFindGetCouplingNodes( Gia_Man_t * p, Vec_Int_t * vCoupled, Vec_Int_t * vObj2Index, Vec_Int_t * vDetected )
{
    Gia_Obj_t * pObj; int i;
    Vec_Wec_t * vCoupling = Vec_WecStart( Vec_IntSize(vCoupled) );
    Gia_ManMark0Nodes( p, vCoupled, 1 );
    Gia_ManMark1Nodes( p, vDetected, 1 );
    Gia_ManForEachAnd( p, pObj, i )
        if ( !pObj->fMark1 && Gia_ObjFanin0(pObj)->fMark0 && Gia_ObjFanin1(pObj)->fMark0 )  { // pObj is an unused coupling node
            Vec_WecPush( vCoupling, Vec_IntEntry(vObj2Index, Gia_ObjFaninId0(pObj, i)), i );
            Vec_WecPush( vCoupling, Vec_IntEntry(vObj2Index, Gia_ObjFaninId1(pObj, i)), i );
        }
    Gia_ManMark0Nodes( p, vCoupled, 0 );
    Gia_ManMark1Nodes( p, vDetected, 0 );
    return vCoupling;
}

/**Function*************************************************************

  Synopsis    [Returns the set of unique supports in terms of coupled nodes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Hsh_VecMan_t * Gia_MulFindGetSupportsVec( Gia_Man_t * p, Vec_Int_t * vCoupled, Vec_Int_t * vTopo, Vec_Int_t * vSuppIds )
{    
    // TODO
    Gia_Obj_t * pObj; int i;
    Hsh_VecMan_t * pHash = Hsh_VecManStart( 1000 );
    Vec_Int_t * vSupp = Vec_IntAlloc( 100 );
    int iSet = Hsh_VecManAdd( pHash, vSupp ); // add empty set
    assert( iSet == 0 );    
    // initialize input supports with empty sets
    Gia_ManForEachCi( p, pObj, i )
        Vec_IntWriteEntry( vSuppIds, Gia_ObjId(p, pObj), 0 );
    // compute supports of internal nodes
    Gia_ManMark0Nodes( p, vCoupled, 1 );
    Gia_ManForEachAnd( p, pObj, i )
    {
        Vec_Int_t * vSupp0 = Hsh_VecReadEntry(pHash, Vec_IntEntry(vSuppIds, Gia_ObjFaninId0(pObj, i)));
        Vec_Int_t * vSupp1 = Hsh_VecReadEntry1(pHash, Vec_IntEntry(vSuppIds, Gia_ObjFaninId1(pObj, i)));

        Vec_IntTwoMerge2( vSupp0, vSupp1, vSupp );
        // add unit nodes for the fanins if they are coupled
        if ( Gia_ObjFanin0(pObj)->fMark0 )
            Vec_IntPushOrder( vSupp, Gia_ObjFaninId0(pObj, i) );
        if ( Gia_ObjFanin1(pObj)->fMark0 )
            Vec_IntPushOrder( vSupp, Gia_ObjFaninId1(pObj, i) );
        int iSupp = Hsh_VecManAdd( pHash, vSupp );
        Vec_IntWriteEntry( vSuppIds, i, iSupp );
    }
    Gia_ManMark0Nodes( p, vCoupled, 0 );
    Vec_IntFree( vSupp );
    return pHash;
}

/**Function*************************************************************

  Synopsis    [Returns the set of unique supports in terms of coupled nodes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Hsh_VecMan_t * Gia_MulFindGetSupports( Gia_Man_t * p, Vec_Int_t * vCoupled, Vec_Int_t * vSuppIds )
{    
    Gia_Obj_t * pObj; int i;
    Hsh_VecMan_t * pHash = Hsh_VecManStart( 1000 );
    Vec_Int_t * vSupp = Vec_IntAlloc( 100 );
    int iSet = Hsh_VecManAdd( pHash, vSupp ); // add empty set
    assert( iSet == 0 );    
    // initialize input supports with empty sets
    Gia_ManForEachCi( p, pObj, i )
        Vec_IntWriteEntry( vSuppIds, Gia_ObjId(p, pObj), 0 );
    // compute supports of internal nodes
    Gia_ManMark0Nodes( p, vCoupled, 1 );
    Gia_ManForEachAnd( p, pObj, i )
    {
        Vec_Int_t * vSupp0 = Hsh_VecReadEntry(pHash, Vec_IntEntry(vSuppIds, Gia_ObjFaninId0(pObj, i)));
        Vec_Int_t * vSupp1 = Hsh_VecReadEntry1(pHash, Vec_IntEntry(vSuppIds, Gia_ObjFaninId1(pObj, i)));

        Vec_IntTwoMerge2( vSupp0, vSupp1, vSupp );
        // add unit nodes for the fanins if they are coupled
        if ( Gia_ObjFanin0(pObj)->fMark0 )
            Vec_IntPushOrder( vSupp, Gia_ObjFaninId0(pObj, i) );
        if ( Gia_ObjFanin1(pObj)->fMark0 )
            Vec_IntPushOrder( vSupp, Gia_ObjFaninId1(pObj, i) );
        int iSupp = Hsh_VecManAdd( pHash, vSupp );
        Vec_IntWriteEntry( vSuppIds, i, iSupp );
    }
    Gia_ManMark0Nodes( p, vCoupled, 0 );
    Vec_IntFree( vSupp );
    return pHash;
}

/**Function**********

  Synopsis    [Computes the union of coupling nodes for the coupled nodes in the set.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_MulFindSuppCouplingNodes( Gia_Man_t * p, Vec_Int_t * vCoupled, Vec_Int_t * vObj2Index, Vec_Wec_t * vCoupling, Vec_Int_t * vUnion )
{
    Gia_Obj_t * pObj; 
    int iObj, i, k = 0;
    Vec_IntClear( vUnion );
    Vec_IntForEachEntry( vCoupled, iObj, i )
        Vec_IntAppend( vUnion, Vec_WecEntry(vCoupling, Vec_IntEntry(vObj2Index, iObj)) );
    Vec_IntUniqify( vUnion );
    // keep only those coupling nodes whose both fanins are in the set of coupled nodes
    Gia_ManMark0Nodes( p, vCoupled, 1 );
    Gia_ManForEachObjVec( vUnion, p, pObj, i )
        if ( Gia_ObjFanin0(pObj)->fMark0 && Gia_ObjFanin1(pObj)->fMark0 ) // pObj is a coupling node with fanins in vCoupled
            Vec_IntWriteEntry( vUnion, k++, Gia_ObjId(p, pObj) );
    Vec_IntShrink( vUnion, k );
    Gia_ManMark0Nodes( p, vCoupled, 0 );

}

/**Function*************************************************************

  Synopsis    [Checks if the given set of coupled nodes is bi-partite.]

  Description [If it is bi-partite, adds two arrays of AIG literals to vRes
  and adds non-booth partial products pointing to these literals to vDetected.
  Currently too strict.
  ]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_MulFindCheckBipartiteSet( Gia_Man_t * p, Vec_Int_t * vCoupled, Vec_Int_t * vCoupling, Vec_Int_t * vLitCount, Vec_Int_t * vPart[3] )
{
    Gia_Obj_t * pObj; int i, k = 0;
    assert( Vec_IntSum(vLitCount) == 0 );

    // count how many times each literal of coupled nodes appears as a fanin of the coupling nodes
    Gia_ManForEachObjVec( vCoupling, p, pObj, i ) {
        Vec_IntAddToEntry( vLitCount, Gia_ObjFaninLit0p(p, pObj), 1 );
        Vec_IntAddToEntry( vLitCount, Gia_ObjFaninLit1p(p, pObj), 1 );
    }
    // find predominant polarity of each coupled node
    Gia_ManForEachObjVec( vCoupling, p, pObj, i )
    {
        if ( Vec_IntEntry(vLitCount, Gia_ObjFaninLit0p(p, pObj)) < Vec_IntEntry(vLitCount, Abc_LitNot(Gia_ObjFaninLit0p(p, pObj))) )
            Vec_IntWriteEntry( vLitCount, Gia_ObjFaninLit0p(p, pObj), 0 );
        else
            Vec_IntWriteEntry( vLitCount, Abc_LitNot(Gia_ObjFaninLit0p(p, pObj)), 0 );
        if ( Vec_IntEntry(vLitCount, Gia_ObjFaninLit1p(p, pObj)) < Vec_IntEntry(vLitCount, Abc_LitNot(Gia_ObjFaninLit1p(p, pObj))) )
            Vec_IntWriteEntry( vLitCount, Gia_ObjFaninLit1p(p, pObj), 0 );
        else
            Vec_IntWriteEntry( vLitCount, Abc_LitNot(Gia_ObjFaninLit1p(p, pObj)), 0 );
    }
    // remove those coupling nodes that have a wrong polarity
    Gia_ManForEachObjVec( vCoupling, p, pObj, i )
        if ( Vec_IntEntry(vLitCount, Gia_ObjFaninLit0p(p, pObj)) > 0 && 
             Vec_IntEntry(vLitCount, Gia_ObjFaninLit1p(p, pObj)) > 0 ) // pObj is a coupling node with correct polarity of fanins
            Vec_IntWriteEntry( vCoupling, k++, Gia_ObjId(p, pObj) );
    Vec_IntShrink( vCoupling, k );

    // cleanup the array
    // Gia_ManForEachObjVec( vCoupling, p, pObj, i ) {
    //     Vec_IntWriteEntry( vLitCount, Gia_ObjFaninLit0p(p, pObj), 0 );
    //     Vec_IntWriteEntry( vLitCount, Gia_ObjFaninLit1p(p, pObj), 0 );
    // }

    // check if the set is bi-partite -- start with any node
    pObj = Gia_ManObj( p, Vec_IntPop(vCoupling) );
    Vec_IntFill( vPart[0], 1, Gia_ObjFaninLit0p(p, pObj) );
    Vec_IntFill( vPart[1], 1, Gia_ObjFaninLit1p(p, pObj) );
    Vec_IntFill( vPart[2], 1, Gia_ObjId(p, pObj) );


    // 5 5 5 6 5 6 5
    // 7 7 7 7 7

    // iterate through the remaining nodes
    int fChanges = 1;
    int iLit0, iLit1, f00, f01, f10, f11;
    while ( fChanges && (Vec_IntSize(vCoupling) + Vec_IntSize(vPart[2])) >= (Vec_IntSize(vPart[0])*Vec_IntSize(vPart[1])) )
    {
        fChanges = 0;

        // Vec_IntPrint(vPart[0]);
        // Vec_IntPrint(vPart[1]);
        // Vec_IntPrint(vPart[2]);
        // printf("\n");

        Gia_ManForEachObjVec( vCoupling, p, pObj, i ) {
            iLit0 = Gia_ObjFaninLit0p(p, pObj);
            iLit1 = Gia_ObjFaninLit1p(p, pObj);
            f00 = Vec_IntFind(vPart[0], iLit0);
            f01 = Vec_IntFind(vPart[0], iLit1);
            f10 = Vec_IntFind(vPart[1], iLit0);
            f11 = Vec_IntFind(vPart[1], iLit1);
            if ( f00 < 0 && f01 < 0 && f10 < 0 && f11 < 0 ) 
                continue;
            else if ( f00 < 0 && f10 < 0 )  // lit 0 not found, update and drop it
            {
                Vec_IntPush( vPart[2], Gia_ObjId(p, pObj) );
                fChanges = 1;
                if ( f01 < 0 ) Vec_IntPush(vPart[0], iLit0);
                else Vec_IntPush(vPart[1], iLit0);
            }
            else if ( f01 < 0 && f11 < 0 )  // lit 1 not found, update and drop it
            {
                Vec_IntPush( vPart[2], Gia_ObjId(p, pObj) );
                fChanges = 1;
                if ( f00 < 0 ) Vec_IntPush(vPart[0], iLit1);
                else Vec_IntPush(vPart[1], iLit1);
            }
            else if ( (f00 >= 0 && f01 >= 0 ) || (f10 >= 0 && f11 >= 0) ) // both found but in the same set, drop it
            {

            }
            else // both found and consistent, drop and save it
            {
                Vec_IntPush( vPart[2], Gia_ObjId(p, pObj) );
            }

            
            /*
            // if one lit belongs to one part and the other does not belong to any part, add the other one
            // if two lit belongs to the same part, not bipartite
            if ( Vec_IntFind(vPart[0], iLit0) >= 0 && Vec_IntFind(vPart[1], iLit1) < 0 && Vec_IntFind(vPart[0], iLit1) < 0 )
                Vec_IntPush(vPart[1], iLit1);
            else if ( Vec_IntFind(vPart[0], iLit1) >= 0 && Vec_IntFind(vPart[1], iLit0) < 0 && Vec_IntFind(vPart[0], iLit0) < 0 )
                Vec_IntPush(vPart[1], iLit0);
            else if ( Vec_IntFind(vPart[1], iLit0) >= 0 && Vec_IntFind(vPart[0], iLit1) < 0 && Vec_IntFind(vPart[1], iLit1) < 0 )
                Vec_IntPush(vPart[0], iLit1);
            else if ( Vec_IntFind(vPart[1], iLit1) >= 0 && Vec_IntFind(vPart[0], iLit0) < 0 && Vec_IntFind(vPart[1], iLit0) < 0 )
                Vec_IntPush(vPart[0], iLit0);
            else continue;
            */

            Vec_IntDrop( vCoupling, i );
            i--;
            if ( fChanges ) break;
        }
    }

    Vec_IntFill( vLitCount, 2*Gia_ManObjNum(p), 0 );

    // add this set if it is bi-partite 
    // printf("final\n");
    // Vec_IntPrint(vPart[0]);
    // Vec_IntPrint(vPart[1]);
    // Vec_IntPrint(vPart[2]);
    // printf("\n");

    if ( Vec_IntSize(vPart[0]) * Vec_IntSize(vPart[1]) == Vec_IntSize(vPart[2]) ) {
        for ( i = 0; i < 3; i++ )
            Vec_IntSort( vPart[i], 0 );
        return 1;
    }
    else 
    {
        // printf( "fail: only %d coupling nodes\n", Vec_IntSize(vPart[2]) );
        return 0;
    }
}


Vec_Int_t * Gia_MulFindGetTfo( Gia_Man_t * p, Vec_Int_t * vIn0, Vec_Int_t * vIn1  )
{
    int i;
    Gia_Obj_t * pObj;
    Vec_Int_t * vTfo = Vec_IntAlloc(128);
    Gia_ManMark0Nodes(p, vIn0, 1);
    Gia_ManMark0Nodes(p, vIn1, 1);
    Gia_ManForEachAnd(p, pObj, i)
    {
        if ( Gia_ObjFanin0(pObj)->fMark0 && Gia_ObjFanin1(pObj)->fMark0 )
        {
            pObj->fMark0 = 1;
            Vec_IntPush(vTfo, Gia_ObjId(p, pObj) );
        }
    }
    Gia_ManCleanMark01(p);
    return vTfo;
}

/**Function*************************************************************

  Synopsis    [sort the input nodes of the given set of bi-partite supports.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
extern Vec_Wrd_t * Gia_ManMulFindSim( Vec_Wrd_t * vSim0, Vec_Wrd_t * vSim1, int fSigned );
extern Vec_Wrd_t * Gia_ManMulFindSimCone( Gia_Man_t * p, Vec_Int_t * vIn0, Vec_Int_t * vIn1, Vec_Wrd_t * vSim0, Vec_Wrd_t * vSim1, Vec_Int_t * vTfo );
Vec_Int_t * Gia_ManMulCheckOutputs( Gia_Man_t * p, Vec_Int_t * vIn0Lit, Vec_Int_t * vIn1Lit, int fVerbose )
{
    Abc_Random(537);
    int i, lit;
    word Word; int w, iPlace;

    if ( fVerbose )
    {
        printf("Checking outputs with the following inputs:\n");
        printf("Input lit A: ");
        Vec_IntPrint(vIn0Lit);
        printf("Input lit B: ");
        Vec_IntPrint(vIn1Lit);
    }


    int nIn0 = Vec_IntSize(vIn0Lit);
    int nIn1 = Vec_IntSize(vIn1Lit);
    Vec_Int_t * vIn0 = Vec_IntAlloc(nIn0);
    Vec_Int_t * vIn0Phase = Vec_IntAlloc(nIn0);
    Vec_IntForEachEntry(vIn0Lit, lit, i) 
    {
        Vec_IntPush(vIn0, Abc_Lit2Var(lit) );
        Vec_IntPush(vIn0Phase, Abc_LitIsCompl(lit) );
    }
    Vec_Int_t * vIn1 = Vec_IntAlloc(nIn1);
    Vec_Int_t * vIn1Phase = Vec_IntAlloc(nIn1);
    Vec_IntForEachEntry(vIn1Lit, lit, i) 
    {
        Vec_IntPush(vIn1, Abc_Lit2Var(lit) );
        Vec_IntPush(vIn1Phase, Abc_LitIsCompl(lit) );
    }
    Vec_Int_t * vOut = Vec_IntAlloc(Vec_IntSize(vIn0Lit) + Vec_IntSize(vIn1Lit));
    Vec_Wrd_t * vSim0 = Vec_WrdStartRandom( Vec_IntSize(vIn0) );
    Vec_Wrd_t * vSim1 = Vec_WrdStartRandom( Vec_IntSize(vIn1) );
    Vec_WrdForEachEntry(vSim0, Word, i)
        if ( Vec_IntEntry(vIn0Phase, i) ) Vec_WrdSetEntry(vSim0, i, ~Word);
    Vec_WrdForEachEntry(vSim1, Word, i)
        if ( Vec_IntEntry(vIn1Phase, i) ) Vec_WrdSetEntry(vSim1, i, ~Word);
    Vec_Wrd_t * vSimU = Gia_ManMulFindSim( vSim0, vSim1, 0 );
    Vec_Wrd_t * vSimS = Gia_ManMulFindSim( vSim0, vSim1, 1 );
    Vec_WrdForEachEntry(vSim0, Word, i)
        if ( Vec_IntEntry(vIn0Phase, i) ) Vec_WrdSetEntry(vSim0, i, ~Word);
    Vec_WrdForEachEntry(vSim1, Word, i)
        if ( Vec_IntEntry(vIn1Phase, i) ) Vec_WrdSetEntry(vSim1, i, ~Word);
    Vec_Int_t * vTfo  = Gia_MulFindGetTfo( p, vIn0, vIn1 );
    Vec_Wrd_t * vSims = Gia_ManMulFindSimCone( p, vIn0, vIn1, vSim0, vSim1, vTfo );
    Vec_Int_t * vOutU = Vec_IntAlloc( 100 );
    Vec_Int_t * vOutS = Vec_IntAlloc( 100 );

    Vec_WrdForEachEntry( vSimU, Word, w ) {
        if ( (iPlace = Vec_WrdFind(vSims, Word)) >= 0 )
            Vec_IntPush( vOutU, Abc_Var2Lit(Vec_IntEntry(vTfo, iPlace), 0) );
        else if ( (iPlace = Vec_WrdFind(vSims, ~Word)) >= 0 )
            Vec_IntPush( vOutU, Abc_Var2Lit(Vec_IntEntry(vTfo, iPlace), 1) );
        else
            Vec_IntPush( vOutU, -1 );                  
    }
    Vec_WrdForEachEntry( vSimS, Word, w ) {
        if ( (iPlace = Vec_WrdFind(vSims, Word)) >= 0 )
            Vec_IntPush( vOutS, Abc_Var2Lit(Vec_IntEntry(vTfo, iPlace), 0) );
        else if ( (iPlace = Vec_WrdFind(vSims, ~Word)) >= 0 )
            Vec_IntPush( vOutS, Abc_Var2Lit(Vec_IntEntry(vTfo, iPlace), 1) );
        else
            Vec_IntPush( vOutS, -1 );
    }
    assert( Vec_IntSize(vOut) == 0 );
    if ( Vec_IntCountEntry(vOutU, -1) < Vec_IntSize(vOutU) ||
            Vec_IntCountEntry(vOutS, -1) < Vec_IntSize(vOutS) )
    {
        if ( Vec_IntCountEntry(vOutU, -1) < Vec_IntCountEntry(vOutS, -1) )
            Vec_IntAppend( vOut, vOutU ), Vec_IntPush(vOut, 0);
        else
            Vec_IntAppend( vOut, vOutS ), Vec_IntPush(vOut, 1);
    }


    Vec_IntClear(vIn0);
    Vec_IntClear(vIn1);
    Vec_IntClear(vIn0Phase);
    Vec_IntClear(vIn1Phase);
    Vec_WrdFree( vSim0 );
    Vec_WrdFree( vSim1 );
    Vec_WrdFree( vSimU );
    Vec_WrdFree( vSimS );
    Vec_WrdFree( vSims );
    Vec_IntFree( vTfo );
    Vec_IntFree( vOutU );
    Vec_IntFree( vOutS );
    return vOut;
}

/**Function*************************************************************

  Synopsis    [sort the input nodes of the given set of bi-partite supports.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_MulFindSortLitByObjValue( Gia_Man_t * p, Vec_Int_t * vId )
{

    int * v = Vec_IntEntryP(vId, 0);

    for( int i = 0; i < Vec_IntSize(vId); i++ )
    {
        for ( int j = 0; j < Vec_IntSize(vId)-1; j++ )
        {
            if ( Gia_ManObj(p, Abc_Lit2Var(v[j]) ) -> Value < Gia_ManObj(p, Abc_Lit2Var(v[j+1]) ) -> Value ) ABC_SWAP( int, v[j], v[j+1] );
        }
    }
}



/**Function*************************************************************

  Synopsis    [sort the input nodes of the given set of bi-partite supports.]

  Description [Each bi-partite support is composed of two arrays of
  AIG literals in terms of coupled nodes whose sizes are N and M, such that 
  there are N * M coupling nodes having these literal pairs as their fanins.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_MulFindGetInputOrder( Gia_Man_t * p, Vec_Int_t * vPart[3] )
{
    int i, j, lit;
    int nSup = Vec_IntSize(vPart[0]) + Vec_IntSize(vPart[1]);
    Gia_Obj_t * pObj, * pFanout;
    Vec_Int_t * vOutputIds = Vec_IntAlloc(Vec_IntSize(vPart[0])+Vec_IntSize(vPart[1]));

    // compute support set
    Vec_Int_t * vSet = Vec_IntAlloc(nSup);
    Vec_IntForEachEntry(vPart[0], lit, i)
        Vec_IntPush(vSet, Abc_Lit2Var(lit));
    Vec_IntForEachEntry(vPart[1], lit, i)
        Vec_IntPush(vSet, Abc_Lit2Var(lit));

    // compute supports
    Vec_Int_t * vSuppIds = Vec_IntStartFull( Gia_ManObjNum(p) );
    Hsh_VecMan_t * pHash   = Gia_MulFindGetSupports( p, vSet, vSuppIds );


    // find TFO
    Gia_ManMark0Nodes(p, vPart[2], 1);
    Gia_ManForEachAnd(p, pObj, i)
        if ( Gia_ObjFanin0(pObj)->fMark0 && Gia_ObjFanin1(pObj)->fMark0 )
            pObj->fMark0 = 1;
    Gia_ManForEachAnd(p, pObj, i)
        if ( pObj->fMark0 )
        {
            Gia_ObjFanin0(pObj)->fMark0 = 0;
            Gia_ObjFanin1(pObj)->fMark0 = 0;
        }


    // find those with smaller support size
    Vec_Int_t * vSupp;
    Gia_Obj_t * pSupp;
    Gia_ManForEachObjVec(vSet, p, pObj, i)
        pObj->Value = 0;
    Gia_ManForEachAnd(p, pObj, i)
    {
        if ( pObj->fMark0 ) 
        {
            vSupp = Hsh_VecReadEntry(pHash, Vec_IntEntry(vSuppIds, Gia_ObjId(p, pObj)));
            if ( Vec_IntSize(vSupp) < nSup )
            {
                Vec_IntPush(vOutputIds, Gia_ObjId(p, pObj) );
                Gia_ManForEachObjVec(vSupp, p, pSupp, j )
                    pSupp -> Value ++;
            }
            pObj->fMark0 = 0;
        }
    }

    // sort lit by obj value
    // Vec_IntPrint(vPart[0]);
    // Vec_IntPrint(vPart[1]);
    Gia_MulFindSortLitByObjValue(p, vPart[0]);
    Gia_MulFindSortLitByObjValue(p, vPart[1]);

    /*
    Vec_IntPrint(vPart[0]);
    Vec_IntPrint(vPart[1]);
    printf("Outputs: ");
    Vec_IntPrint(vOutputIds);
    printf("\n");
    printf("%d, %d, %d\n\n", Vec_IntSize(vPart[0]), Vec_IntSize(vPart[1]), Vec_IntSize(vOutputIds) );
    Gia_ManForEachObjVec(vSet, p, pObj, i)
    {
        printf("%d: %d\n", Gia_ObjId(p, pObj), pObj->Value);
    }
    printf("\n");
    */

    

    Vec_IntFree(vOutputIds);

    Hsh_VecManStop(pHash);
    Vec_IntFree(vSuppIds);
    Vec_IntFree(vSet);
}


/**Function*************************************************************

  Synopsis    [Find the largest bi-partite supports.]


  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_MulFindDetectOne( Gia_Man_t * p, Vec_Int_t * vCoupled, Vec_Wec_t * vRes, Vec_Int_t * vDetected, int fVerbose )
{

    Vec_Int_t * vObj2Index = Vec_IntInvert( vCoupled, -1 );
    Vec_Wec_t * vCoupling  = Gia_MulFindGetCouplingNodes( p, vCoupled, vObj2Index, vDetected );
    Vec_Int_t * vUnion     = Vec_IntAlloc( 100 );
    Vec_Int_t * vLitCount  = Vec_IntStart( 2 * Gia_ManObjNum(p) );
    Vec_Int_t * vPart[3]   = {Vec_IntAlloc(16), Vec_IntAlloc(16), Vec_IntAlloc(64)};

    int found = 0;

    // TODO: find the largest BS
    // TODO: remove the coupled nodes that are not Mul

    if ( Vec_IntSize(vCoupled) >= 8 )
    {
        Gia_MulFindSuppCouplingNodes( p, vCoupled, vObj2Index, vCoupling, vUnion );
        if ( Gia_MulFindCheckBipartiteSet( p, vCoupled, vUnion, vLitCount, vPart ) )
        {
            // TODO: try different orders
            // find output boundary and sort by support size
            Gia_MulFindGetInputOrder( p, vPart );

            Vec_Int_t * vOut = Gia_ManMulCheckOutputs(p, vPart[0], vPart[1], fVerbose);
            if ( Vec_IntSize(vOut) > 1 && Vec_IntCountEntry(vOut, -1) <= Vec_IntSize(vOut) / 2  )
            {
                found = 1;
                int id, i;
                // Vec_IntForEachEntry( vPart[2], id, i )
                //     Vec_IntPush( vDetected, id );
                Vec_IntAppend(vDetected, vPart[2]);

                // store result
                Vec_Int_t * vTmp;
                vTmp = Vec_WecPushLevel(vRes); Vec_IntAppend(vTmp, vPart[0]);
                vTmp = Vec_WecPushLevel(vRes); Vec_IntAppend(vTmp, vPart[1]);
                vTmp = Vec_WecPushLevel(vRes); Vec_IntAppend(vTmp, vOut); 

            }
            else
            {
                printf("No multiplier found with the given input & input order.");
            }
            Vec_IntFree( vOut );
        }
    }

    Vec_IntFree( vObj2Index );
    Vec_WecFree( vCoupling );
    Vec_IntFree( vUnion );
    Vec_IntFree( vLitCount );
    Vec_IntFree( vPart[0] );
    Vec_IntFree( vPart[1] );
    Vec_IntFree( vPart[2] );

    return found;
}

/**Function*************************************************************

  Synopsis    [Returns the set of bi-partite supports.]

  Description [Each bi-partite support is composed of two arrays of
  AIG literals in terms of coupled nodes whose sizes are N and M, such that 
  there are N * M coupling nodes having these literal pairs as their fanins.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_MulFindGetBipartiteSupps( Gia_Man_t * p, Vec_Int_t * vCoupled, Vec_Wec_t * vRes, Vec_Int_t * vDetected )
{

    Vec_Int_t * vSuppIds = Vec_IntStartFull( Gia_ManObjNum(p) );
    Hsh_VecMan_t * pHash   = Gia_MulFindGetSupports( p, vCoupled, vSuppIds );
    Vec_Int_t * vObj2Index = Vec_IntInvert( vCoupled, -1 );
    Vec_Wec_t * vCoupling  = Gia_MulFindGetCouplingNodes( p, vCoupled, vObj2Index, vDetected );
    Vec_Int_t * vUnion     = Vec_IntAlloc( 100 );
    Vec_Int_t * vLitCount  = Vec_IntStart( 2 * Gia_ManObjNum(p) );
    Vec_Int_t * vPart[3]   = {Vec_IntAlloc(10), Vec_IntAlloc(10), Vec_IntAlloc(10)};
    for ( int i = 1; i < Hsh_VecSize(pHash); i++ ) {
        Vec_Int_t * vSet = Hsh_VecReadEntry(pHash, i);
        if ( Vec_IntSize(vSet) < 8 )
        // if ( Vec_IntSize(vSet) < 16 )
        {
            continue;
        }
        // printf("\nvSet: ");
        // Vec_IntPrint(vSet);
        Gia_MulFindSuppCouplingNodes( p, vSet, vObj2Index, vCoupling, vUnion );
        if ( Gia_MulFindCheckBipartiteSet( p, vSet, vUnion, vLitCount, vPart ) )
        {
            // find output boundary and sort by support size
            Gia_MulFindGetInputOrder( p, vPart );
        }
    }
    Hsh_VecManStop( pHash );
    Vec_IntFree( vObj2Index );
    Vec_WecFree( vCoupling );
    Vec_IntFree( vUnion );
    Vec_IntFree( vLitCount );
    Vec_IntFree( vPart[0] );
    Vec_IntFree( vPart[1] );
    Vec_IntFree( vPart[2] );
    Vec_IntFree( vSuppIds );
}

/**Function*************************************************************

  Synopsis    [Detects non-booth multipliers.]

  Description [Each multiplier A*B is a pair of arrays containing unordered 
  input literals of A and B.]

  SideEffects []

  SeeAlso     []

***********************************************************************/


Vec_Wec_t * Gia_ManFunTraceTruth( Gia_Man_t * p, word* pTruth, int nVars, int nCutNum, int fVerbose );
int Gia_ManFindCompl( Gia_Man_t * p, int id0, int id1 )
{
    int iLit0 = Abc_Var2Lit(id0, 0);
    int iLit1 = Abc_Var2Lit(id1, 0);

    
    if ( Gia_ManHashLookupInt(p, iLit0, iLit1) || Gia_ManHashLookupInt(p, iLit0, iLit1 ^ 1) ) return 0;
    else if ( Gia_ManHashLookupInt(p, iLit0 ^ 1, iLit1) || Gia_ManHashLookupInt(p, iLit0 ^ 1, iLit1 ^ 1) ) return 1;
    else return -1;
}


/**Function*************************************************************

  Synopsis    [Detects non-booth multipliers.]

  Description [find the lit of the given var in a vector of lit]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Vec_IntFindVar(Vec_Int_t *p, int var)
{
    int res = Vec_IntFind(p, Abc_Var2Lit(var, 0));
    if ( res != -1 ) return res;
    return  Vec_IntFind(p, Abc_Var2Lit(var, 0));
}

void Gia_FarComputeCoupledNodes( Gia_Far_t * p )
{
    Gia_Obj_t * pObj;
    int i;

    p->vCoupling = Vec_IntAlloc(  Gia_ManObjNum(p->pGia) );
    Vec_IntFill( p->vCoupling, Gia_ManObjNum(p->pGia), 0 );
    Gia_ManCreateRefs(p->pGia);
    
    Gia_ManForEachObj( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntSetEntry( p->vCoupling, i, 1 );
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            Gia_ObjRefDec(p->pGia, Gia_ObjFaninId0(p->pGia, pObj) );
        }
    }

    int change = 1;
    while ( change )
    {
    }
    
}


Gia_Far_t * Gia_FarAlloc( Gia_Man_t * pGia, int fVerbose ) 
{
    int i, j, k, id, id0, id1;
    Vec_Wec_t * vCuts_tmp;
    Vec_Int_t * cut, * cut2;
    Vec_Wec_t * vCuts = Vec_WecAlloc(64);
    Gia_Obj_t * pObj;

    Gia_Far_t * p = ABC_CALLOC( Gia_Far_t, 1 );

    // save gia
    p->pGia = pGia;
    Gia_ManHashStart(p->pGia);

    // build neighbors
    Vec_Wec_t * vNeighbor = Vec_WecStart( Gia_ManObjNum(pGia) );
    Gia_ManForEachAnd(pGia, pObj, i)
    {
        id = Gia_ObjId(pGia, pObj);
        id0 = Gia_ObjFaninId0(pObj, id);
        id1 = Gia_ObjFaninId1(pObj, id);
        Vec_WecPush(vNeighbor, id0, id1);
        Vec_WecPush(vNeighbor, id1, id0);
    }

    // find cuts

    // word pTruths[3] = { 
    //     ABC_CONST(0x000100010001111f),
    //     ABC_CONST(0x01010157), 
    //     ABC_CONST(0x0001) 
    // };   // output bit 1 (maj)
    word pTruths[3] = { 
        ABC_CONST(0x111e111e111eeee1),
        ABC_CONST(0x565656a9565656a9), 
        ABC_CONST(0x111e111e111e111e)
    };  // output bit 0 (xor)

    for ( i = 0; i < 3; i++ )
    {
        vCuts_tmp = Gia_ManFunTraceTruth( p->pGia, pTruths+i, 6-i, 64, 0 );
        // vCuts_tmp = Gia_ManFunTraceTruth( p->pGia, pTruths+i, 4+i, 64, 0 );
        Vec_WecForEachLevel( vCuts_tmp, cut, j)
        {
            cut2 = Vec_WecPushLevel(vCuts);
            Vec_IntForEachEntry(cut, id, k)
            {
                if ( k == 0 ) continue;
                Vec_IntPush(cut2, id);
            }
        }
        // vCuts = Gia_ManFunTraceTruth( pMan->pGia, pTruths+i, 4+i, 64, 1 );
        Vec_WecFree(vCuts_tmp);
    }

    printf("Cuts found: ");
    Vec_WecPrint(vCuts, 0);

    // init
    p->vCuts = vCuts;
    p->vNeighbor = vNeighbor;
    p->vInA = 0;
    p->vInB = 0;
    p->fVerbose = fVerbose;

    // init flag
    p->vFlag = Vec_IntAlloc( Gia_ManObjNum(pGia) );
    Vec_IntFill(p->vFlag, Gia_ManObjNum(pGia), 0);
    p->gFlag = 0;
    p->mFlag = 0;

    Gia_ManStaticFanoutStart(pGia);

    return p;
}
void Gia_FarFree( Gia_Far_t * p )
{
    if ( p )
    {
        Gia_ManStaticFanoutStop(p->pGia);
        Gia_ManHashStop(p->pGia);
        if ( p->vInA ) Vec_IntFree(p->vInA);
        if ( p->vInB ) Vec_IntFree(p->vInB);
        if ( p->vCoupling ) Vec_IntFree(p->vCoupling);
        ABC_FREE(p);
    }
}

int Gia_FarFindInputs( Gia_Far_t * p ) 
{
    Vec_Wec_t * vCuts = p -> vCuts;
    if ( p -> vInA ) Vec_IntFree(p -> vInA);
    if ( p -> vInB ) Vec_IntFree(p -> vInB);
    p -> vInA = Vec_IntAlloc(64);
    p -> vInB = Vec_IntAlloc(64);

    // p -> vInA = Gia_FarFindInputA(p);
    // p -> vInB = Gia_FarFindInputB(p);

    int res = Gia_FarFindInputAB(p);

    Vec_WecFree(vCuts);

    return res;
}

int Gia_FarFindInputAB( Gia_Far_t * p )
{
    Gia_Man_t * pGia = p -> pGia;
    Vec_Wec_t * vN = p -> vNeighbor;
    Vec_Int_t * cut, *neighbor;
    int i, j, k, id, lit, id2, a = -1, b = -1, max;
    Gia_Obj_t * pObj;

    // select a signal A0 B0
    // where A0 & B0 exist and they have the most #fanout
    max = 0;
    Vec_WecForEachLevel(vN, neighbor, i)
    {
        if ( Vec_IntSize(neighbor) > max )
        {
            a = i;
            max = Vec_IntSize(neighbor);
        }
    }

    // select B0
    max = 0; 
    Vec_IntForEachEntry( Vec_WecEntry(vN, a), id, i)
    {
        if ( Vec_IntSize(Vec_WecEntry(vN, id)) >= max )
        {
            if ( Vec_IntSize(Vec_WecEntry(vN, id)) == max && id > b )
            {
                continue;
            }
            max = Vec_IntSize(Vec_WecEntry(vN, id));
            b = id;
        }
    }


    printf("Node %d (A) has maximum number of fanouts (%d).\n", a, max );
    printf("Node %d (B) has maximum number of fanouts (%d).\n", b, max );



    // set A B
    Gia_FarResetFlag(p);
    Gia_FarSetFlag(p, a, 1);
    Vec_IntPush(p->vInA, Abc_Var2Lit(a, Gia_ManFindCompl(pGia, a, b)) );
    Gia_FarSetFlag(p, b, 2);
    Vec_IntPush(p->vInB, Abc_Var2Lit(b, Gia_ManFindCompl(pGia, b, a)) );

    // repeat until no more nodes can be added
    Vec_Int_t * vA = Vec_IntAlloc(8);
    Vec_Int_t * vB = Vec_IntAlloc(8);

    int new = 1;
    while( new )
    {
        new = 0;
        Vec_WecForEachLevel(p->vCuts, cut, i)
        {
            // for each cut, include Ai if Ai and Aj and Bk are in the same cut
            // for each cut, include Bi if Bi and Bj and Ak are in the same cut
            Vec_IntForEachEntry(cut, id, j)
            {
                if ( Gia_FarGetFlag(p, id) == 1 )
                    Vec_IntPush(vA, id);
                else if ( Gia_FarGetFlag(p, id) == 2 )
                    Vec_IntPush(vB, id);
            }

            if ( Vec_IntSize(vA) > 0 && Vec_IntSize(vB) > 0 )
            {

                Vec_IntForEachEntry(cut, id, j)
                {
                    if ( Gia_FarGetFlag(p, id) > 0 ) continue;

                    // check if its neighbor in this cuts belongs to A or B
                    neighbor = Vec_WecEntry(p->vNeighbor, id);

                    Vec_IntForEachEntry(vA, id2, k)
                    {
                        if ( Vec_IntFind(neighbor, id2) != -1 )
                        {
                            // neighbor in A
                            new = 1;
                            Gia_FarSetFlag(p, id, 2);
                            Vec_IntPush(p->vInB, Abc_Var2Lit(id, Gia_ManFindCompl(pGia, id, id2)));
                            break;
                        }
                    }
                    Vec_IntForEachEntry(vB, id2, k)
                    {
                        if ( Vec_IntFind(neighbor, id2) != -1 )
                        {
                            // neighbor in B
                            new = 1;
                            Gia_FarSetFlag(p, id, 1);
                            // Vec_IntPush(p->vInA, id);
                            Vec_IntPush(p->vInA, Abc_Var2Lit(id, Gia_ManFindCompl(pGia, id, id2)));
                            break;
                        }
                    }
                }
            }

            Vec_IntClear(vA);
            Vec_IntClear(vB);
        }
    }

    Vec_IntFree(vA);
    Vec_IntFree(vB);

    // print result
    printf("Input A: ");
    Vec_IntPrint(p->vInA);
    printf("Input B: ");
    Vec_IntPrint(p->vInB);

    if ( Vec_IntSize(p->vInA) > 2 && Vec_IntSize(p->vInB) > 2 ) return 1;
    else return 0;

}

Vec_Int_t * Gia_FarFindInputA( Gia_Far_t * p ) 
{

    Gia_Man_t * pGia = p -> pGia; 
    Gia_Obj_t *pObj, *pFanout;
    int i, j, id, fanin;

    Vec_Int_t * vFlag = Vec_IntAlloc( Gia_ManObjNum(pGia) );
    Vec_Int_t * vN = Vec_IntAlloc(64);
    Vec_Int_t * vRes = Vec_IntAlloc(64);


    // find the node with max number of inputs
    int max = 0, maxId = -1;
    Gia_ManForEachObj(pGia, pObj, i)
    {
        if ( Gia_ObjFanoutNum(pGia, pObj) > max )
        {
            maxId = Gia_ObjId(pGia, pObj);
            max = Gia_ObjFanoutNum(pGia, pObj);
        }
    }
    printf("Node %d has maximum number of fanouts (%d).\n", maxId, max );

    // test: number of nodes with at least 4 outputs
    int count = 0;
    Gia_ManForEachObj(pGia, pObj, i)
    {
        if ( Gia_ObjFanoutNum(pGia, pObj) >= 4 ) count ++; 
    }
    printf("#node with at least 4 fanouts: %d\n", count);


    // neighbor of n
    Vec_IntFill( vFlag, Gia_ManObjNum(pGia), 0 );
    pObj = Gia_ManObj(pGia, maxId);
    Gia_ObjForEachFanoutStatic(pGia, pObj, pFanout, i)
    {
        fanin = Gia_ObjFanin0(pFanout) == pObj ? 1 : 0;
        Vec_IntPush(vN, Gia_ObjFaninId(pFanout, Gia_ObjId(pGia, pFanout), fanin) );
    }

    // Vec_IntPrint(vN);
    Vec_IntForEachEntry(vN, id, i)
    {
        pObj = Gia_ManObj(pGia, id);
        Gia_ObjForEachFanoutStatic(pGia, pObj, pFanout, j)
        {
            fanin = Gia_ObjFanin0(pFanout) == pObj ? 1 : 0;
            fanin = Gia_ObjFaninId(pFanout, Gia_ObjId(pGia, pFanout), fanin );
            Vec_IntSetEntry(vFlag, fanin, Vec_IntEntry(vFlag, fanin)+1 );
        }
    }

    // Vec_IntPrint(vFlag);

    int flag;
    int t = max/2;
    Vec_IntForEachEntry(vFlag, flag, i)
    {
        if ( flag >= t ) 
        // TODO: use threshold instead of 0
        {
            Vec_IntPush(vRes, 2*i);
        }
    }

    printf("Input A:");
    Vec_IntPrint(vRes);

    Vec_IntFree( vFlag );
    Vec_IntFree( vN );

    return vRes;

}

Vec_Int_t * Gia_FarFindInputB( Gia_Far_t * p ) 
{

    Gia_Man_t * pGia = p -> pGia; 
    int lit, id, i, j, fanin;
    Gia_Obj_t * pObj, * pFanout;
    Vec_Int_t *inA = p -> vInA;
    Vec_Wec_t *vCuts = p -> vCuts;


    Vec_Int_t * vRes = Vec_IntAlloc(64); 
    Vec_Int_t * vFlag = Vec_IntAlloc( Gia_ManObjNum(pGia) );

    Vec_IntFill( vFlag, Gia_ManObjNum(pGia), 0 );

    // increase flag
    Vec_IntForEachEntry(inA, lit, i)
    {
        id = Abc_Lit2Var(lit);
        pObj = Gia_ManObj(pGia, id);
        Gia_ObjForEachFanoutStatic(pGia, pObj, pFanout, j)
        {
            fanin = Gia_ObjFanin0(pFanout) == pObj ? 1 : 0;
            fanin = Gia_ObjFaninId(pFanout, Gia_ObjId(pGia, pFanout), fanin );
            Vec_IntSetEntry(vFlag, fanin, Vec_IntEntry(vFlag, fanin)+1 );
        }
    }
    // select one
    int max = 0, maxId = -1;
    int flag;

    Vec_IntForEachEntry(vFlag, flag, i)
    {
        if ( flag > max )
        {
            maxId = i;
            max = flag;
        }
    }
    printf("Node %d has maximum flag (%d).\n", maxId, max );

    // select other if only they are in the same cuts
    int t = max/2;
    Vec_IntForEachEntry(vFlag, flag, i)
    {
        if ( flag >= t ) Vec_IntSetEntry(vFlag, i, 1);
        else Vec_IntSetEntry(vFlag, i, 0);
    }
    Vec_IntSetEntry(vFlag, maxId, 2);

    int new = 1;
    Vec_Int_t * cut;
    while( new )
    {
        new = 0;
        Vec_WecForEachLevel(vCuts, cut, i)
        {
            // if some flagged node is selected
            int add = 0;
            Vec_IntForEachEntry(cut, id, j)
            {
                if ( Vec_IntEntry(vFlag, id) == 2 )
                {
                    add = 1;
                    break;
                }
            }
            
            // add other flagged node and set new to 1
            if ( add )
            {
                Vec_IntForEachEntry(cut, id, j)
                {
                    if ( Vec_IntEntry(vFlag, id) == 1 )
                    {
                        Vec_IntSetEntry(vFlag, id, 2);
                        new = 1;
                    }
                }
            }
        }
    }

    Vec_IntForEachEntry(vFlag, flag, i)
    {
        if ( flag == 2 ) Vec_IntPush(vRes, 2*i);
    }

    printf( "Input B: " );
    Vec_IntPrint(vRes);

    Vec_IntFree(vFlag);

    return vRes;

}

Vec_Wec_t * Gia_ManFunTraceStr( Gia_Man_t * p, char* pStr, int nCutNum, int fVerbose )
{
    extern Vec_Mem_t * Dau_CollectNpnFunctions( word * p, int nVars, int fVerbose );
    extern Vec_Wec_t * Gia_ManMatchCutsRet( Vec_Mem_t * vTtMem, Gia_Man_t * pGia, int nCutSize, int nCutNum, Vec_Int_t * vSpot, int fVerbose );

    int nVars, nVars2;
    word * pTruth;
    Vec_Wec_t * vCuts;
    Vec_Int_t * vSpot;
    Vec_Mem_t * vTtMem;

    nVars = Abc_Base2Log(strlen(pStr)*4);
    if ( (1 << nVars) != strlen(pStr)*4 )
    {
        Abc_Print( -1, "Abc_CommandAbc9FunTrace(): String \"%s\" does not look like a truth table of a %d-var function.\n", pStr, nVars );
        return 0;
    }
    pTruth = ABC_CALLOC( word, Abc_Truth6WordNum(nVars+1) );
    nVars2 = Abc_TtReadHex( pTruth, pStr );
    if ( nVars != nVars2 )
    {
        ABC_FREE( pTruth );
        Abc_Print( -1, "Abc_CommandAbc9FunTrace(): String \"%s\" does not look like a truth table of a %d-var function.\n", pStr, nVars );
        return 0;
    }

    vSpot = Vec_IntAlloc(8);
    vTtMem = Dau_CollectNpnFunctions( pTruth, nVars, fVerbose );
    vCuts = Gia_ManMatchCutsRet( vTtMem, p, nVars, nCutNum, vSpot, fVerbose );

    Vec_IntFree(vSpot);
    return vCuts;
}

Vec_Wec_t * Gia_ManFunTraceTruth( Gia_Man_t * p, word* pTruth, int nVars, int nCutNum, int fVerbose )
{
    extern Vec_Mem_t * Dau_CollectNpnFunctions( word * p, int nVars, int fVerbose );
    extern Vec_Wec_t * Gia_ManMatchCutsRet( Vec_Mem_t * vTtMem, Gia_Man_t * pGia, int nCutSize, int nCutNum, Vec_Int_t * vSpot, int fVerbose );

    Vec_Wec_t * vCuts;
    Vec_Int_t * vSpot;
    Vec_Mem_t * vTtMem;

    vSpot = Vec_IntAlloc(8);
    vTtMem = Dau_CollectNpnFunctions( pTruth, nVars, fVerbose );
    vCuts = Gia_ManMatchCutsRet( vTtMem, p, nVars, nCutNum, vSpot, fVerbose );

    Vec_IntFree(vSpot);
    Vec_MemHashFree( vTtMem );
    Vec_MemFree( vTtMem );
    return vCuts;
}


int Gia_FarGetFlag( Gia_Far_t * p, int id )
{
    int r = Vec_IntEntry(p->vFlag, id) - p->gFlag;
    return r > 0 ? r : 0;
}
void Gia_FarSetFlag( Gia_Far_t * p, int id, int flag )
{
    Vec_IntSetEntry(p->vFlag, id, p->gFlag + flag);
    p->mFlag = p->mFlag > flag ? p->mFlag : flag;
}
void Gia_FarResetFlag( Gia_Far_t * p )
{
    p->gFlag += p->mFlag;
}

void Gia_FarRemoveInputs( Gia_Far_t * p )
{
    int i, j, lit;
    Vec_Int_t * vN;

    Gia_FarResetFlag(p);
    Vec_IntForEachEntry(p->vInA, lit, i) Gia_FarSetFlag(p, lit2var(lit), 1);
    Vec_IntForEachEntry(p->vInB, lit, i) Gia_FarSetFlag(p, lit2var(lit), 1);


    Vec_IntForEachEntry(p->vInA, lit, i)
    {
        vN = Vec_WecEntry(p->vNeighbor, lit2var(lit));
        for( j = 0; j < Vec_IntSize(vN); j++ )
        {
            if ( Gia_FarGetFlag(p, Vec_IntEntry(vN, j)) )
            {
                if ( Vec_IntSize(vN) == 1 ) 
                {
                    Vec_IntClear(vN);
                    break;
                }
                // printf("remove %d from %d\n", Vec_IntEntry(vN, j), lit2var(lit));
                Vec_IntSetEntry(vN, j, Vec_IntEntryLast(vN));
                Vec_IntShrink(vN, Vec_IntSize(vN)-1);
                j--;
            }
        }
    }
    Vec_IntForEachEntry(p->vInB, lit, i)
    {
        vN = Vec_WecEntry(p->vNeighbor, lit2var(lit));
        for( j = 0; j < Vec_IntSize(vN); j++ )
        {
            if ( Gia_FarGetFlag(p, Vec_IntEntry(vN, j)) )
            {
                if ( Vec_IntSize(vN) == 1 ) 
                {
                    Vec_IntClear(vN);
                    break;
                }

                // printf("remove %d from %d\n", Vec_IntEntry(vN, j), lit2var(lit));
                Vec_IntSetEntry(vN, j, Vec_IntEntryLast(vN));
                Vec_IntShrink(vN, Vec_IntSize(vN)-1);
                j--;
            }
        }
    }

}

int Gia_FarFindOne( Gia_Far_t * p )
{
    if ( ! Gia_FarFindInputs(p) )
    {
        return 0;
    }
    Gia_FarRemoveInputs(p);
    return 1;
}

Vec_Wec_t * Gia_MulFindNonBooth( Gia_Man_t * p )
{
    Vec_Wec_t * vRes = Vec_WecAlloc( 100 );
    Vec_Int_t * vDetected = Vec_IntAlloc( 100 ); // partial products of detected multipliers
    while ( 1 )
    {
        int nMultBefore = Vec_WecSize(vRes);
        Vec_Int_t * vCoupled = Gia_MulFindGetCoupledNodes( p, 4, vDetected );
        if ( Vec_IntSize(vCoupled) > 0 )
            Gia_MulFindGetBipartiteSupps( p, vCoupled, vRes, vDetected );
        Vec_IntFree( vCoupled );
        if ( nMultBefore == Vec_WecSize(vRes) )
            break;
    }
    Vec_IntFree( vDetected );
    return vRes;
}

void Gia_ManMulFind2( Gia_Man_t * p, int nCutNum, int fVerbose )
{

    Gia_ManStaticFanoutStart(p);
    Vec_Wec_t * vRes = Vec_WecAlloc( 100 );
    Vec_Int_t * vDetected = Vec_IntAlloc( 100 ); // partial products of detected multipliers
    int found = 1;

    // if ( fVerbose )
    //     Gia_ManForEachAnd(p, pObj, i)
    //         printf("%5d = %c %5d & %c %5d\n", i, Gia_ObjFaninC0(pObj)?' ':'!', Gia_ObjFaninId0(pObj, i),  Gia_ObjFaninC1(pObj)?' ':'!', Gia_ObjFaninId1(pObj, i)); 

    while ( found )
    {
        found = 0;
        Vec_Int_t * vCoupled = Gia_MulFindGetCoupledNodes( p, 4, vDetected );
        if ( fVerbose )
        {
            printf("Coupled Nodes: ");
            Vec_IntPrint(vCoupled);
        }
        if ( Vec_IntSize(vCoupled) > 0 )
            found = Gia_MulFindDetectOne( p, vCoupled, vRes, vDetected, fVerbose );
        Vec_IntFree( vCoupled );
    }
    printf("res:\n");
    Vec_WecPrint( vRes, 0 );
    Vec_IntFree( vDetected );
    Vec_WecFree( vRes );

    Gia_ManStaticFanoutStop(p);


}

void Gia_ManMulFind3( Gia_Man_t * p, int nCutNum, int fVerbose )
{
    Gia_Far_t *pMan = Gia_FarAlloc(p, fVerbose);
    Gia_FarFindInputs(pMan);
    Gia_FarFree(pMan);
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END