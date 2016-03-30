/**CFile****************************************************************

  FileName    [giaSplit.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Structural AIG splitting.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSplit.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Spl_Man_t_ Spl_Man_t;
struct Spl_Man_t_
{
    // input data
    Gia_Man_t *      pGia;       // user AIG with nodes marked
    int              iObj;       // object ID
    int              Limit;      // limit on AIG nodes
    int              Count;      // count of AIG nodes
    // intermediate
    Vec_Bit_t *      vMarksCIO;  // CI/CO marks
    Vec_Bit_t *      vMarksIn;   // input marks
    Vec_Bit_t *      vMarksNo;   // node marks
    Vec_Int_t *      vNodes;     // nodes used in the window
    Vec_Int_t *      vRoots;     // nodes pointing to Nodes
    Vec_Int_t *      vLeaves;    // nodes pointed by Nodes
    // temporary 
    Vec_Int_t *      vFanouts;   // fanouts of the node
    Vec_Int_t *      vCands;     // candidate nodes
    Vec_Int_t *      vInputs;    // non-trivial inputs
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Spl_Man_t * Spl_ManAlloc( Gia_Man_t * pGia, int Limit )
{
    int i, iObj;
    Spl_Man_t * p = ABC_CALLOC( Spl_Man_t, 1 );
    assert( Gia_ManHasMapping(pGia) );
    p->pGia       = pGia;
    p->Limit      = Limit;
    // intermediate
    p->vMarksCIO  = Vec_BitStart( Gia_ManObjNum(pGia) );
    p->vMarksIn   = Vec_BitStart( Gia_ManObjNum(pGia) );
    p->vMarksNo   = Vec_BitStart( Gia_ManObjNum(pGia) );
    p->vRoots     = Vec_IntAlloc( 100 );
    p->vNodes     = Vec_IntAlloc( 100 );
    p->vLeaves    = Vec_IntAlloc( 100 );
    // temporary 
    p->vFanouts   = Vec_IntAlloc( 100 );
    p->vCands     = Vec_IntAlloc( 100 );
    p->vInputs    = Vec_IntAlloc( 100 );
    // mark CIs/COs
    Gia_ManForEachCiId( pGia, iObj, i )
        Vec_BitWriteEntry( p->vMarksCIO, iObj, 1 );
    Gia_ManForEachCoId( pGia, iObj, i )
        Vec_BitWriteEntry( p->vMarksCIO, iObj, 1 );
    // prepare AIG
    Gia_ManStaticFanoutStart( pGia );
    Gia_ManSetLutRefs( pGia );
    Gia_ManCreateRefs( pGia );
    return p;
}
void Spl_ManStop( Spl_Man_t * p )
{
    Gia_ManStaticFanoutStop( p->pGia );
    // intermediate
    Vec_BitFree( p->vMarksCIO );
    Vec_BitFree( p->vMarksIn );
    Vec_BitFree( p->vMarksNo );
    Vec_IntFree( p->vRoots );
    Vec_IntFree( p->vNodes );
    Vec_IntFree( p->vLeaves );
    // temporary 
    Vec_IntFree( p->vFanouts );
    Vec_IntFree( p->vCands );
    Vec_IntFree( p->vInputs );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Takes Nodes and Marks. Returns Leaves and Roots.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Spl_ManWinFindLeavesRoots( Spl_Man_t * p )
{
    int iObj, iFan, i, k;
    // collect leaves
    Vec_IntClear( p->vLeaves );
    Vec_IntForEachEntry( p->vNodes, iObj, i )
    {
        assert( Vec_BitEntry(p->vMarksNo, iObj) );
        Gia_LutForEachFanin( p->pGia, iObj, iFan, k )
            if ( !Vec_BitEntry(p->vMarksNo, iFan) )
            {
                Vec_BitWriteEntry(p->vMarksNo, iFan, 1);
                Vec_IntPush( p->vLeaves, iFan );
            }
    }
    Vec_IntForEachEntry( p->vLeaves, iObj, i )
        Vec_BitWriteEntry(p->vMarksNo, iObj, 0);
    // collect roots
    Vec_IntClear( p->vRoots );
    Vec_IntForEachEntry( p->vNodes, iObj, i )
        Gia_LutForEachFanin( p->pGia, iObj, iFan, k )
            Gia_ObjLutRefDecId( p->pGia, iFan );
    Vec_IntForEachEntry( p->vNodes, iObj, i )
        if ( Gia_ObjLutRefNumId(p->pGia, iObj) )
            Vec_IntPush( p->vRoots, iObj );
    Vec_IntForEachEntry( p->vNodes, iObj, i )
        Gia_LutForEachFanin( p->pGia, iObj, iFan, k )
            Gia_ObjLutRefIncId( p->pGia, iFan );
}




/**Function*************************************************************

  Synopsis    [Computes LUTs that are fanouts of the node outside of the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Spl_ManLutFanouts_rec( Gia_Man_t * p, int iObj, Vec_Int_t * vFanouts, Vec_Bit_t * vMarksNo, Vec_Bit_t * vMarksCIO )
{
    int iFanout, i;
    if ( Vec_BitEntry(vMarksNo, iObj) || Vec_BitEntry(vMarksCIO, iObj) )
        return;
    if ( Gia_ObjIsLut(p, iObj) )
    {
        Vec_BitWriteEntry( vMarksCIO, iObj, 1 );
        Vec_IntPush( vFanouts, iObj );
        return;
    }
    Gia_ObjForEachFanoutStaticId( p, iObj, iFanout, i )
        Spl_ManLutFanouts_rec( p, iFanout, vFanouts, vMarksNo, vMarksCIO );
}
int Spl_ManLutFanouts( Gia_Man_t * p, int iObj, Vec_Int_t * vFanouts, Vec_Bit_t * vMarksNo, Vec_Bit_t * vMarksCIO )
{
    int i, iFanout;
    assert( Gia_ObjIsLut(p, iObj) );
    Vec_IntClear( vFanouts );
    Gia_ObjForEachFanoutStaticId( p, iObj, iFanout, i )
        Spl_ManLutFanouts_rec( p, iFanout, vFanouts, vMarksNo, vMarksCIO );
    // clean up
    Vec_IntForEachEntry( vFanouts, iFanout, i )
        Vec_BitWriteEntry( vMarksCIO, iFanout, 0 );
    return Vec_IntSize(vFanouts);
}


/**Function*************************************************************

  Synopsis    [Compute MFFC size of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Spl_ManLutMffcSize( Gia_Man_t * p, int iObj )
{
    int Res, iFan, i;
    assert( Gia_ObjIsLut(p, iObj) );
    Gia_LutForEachFanin( p, iObj, iFan, i )
        Gia_ObjRefIncId( p, iFan );
    Res = Gia_NodeMffcSize( p, Gia_ManObj(p, iObj) );
    Gia_LutForEachFanin( p, iObj, iFan, i )
        Gia_ObjRefDecId( p, iFan );
    return Res;
}

/**Function*************************************************************

  Synopsis    [Returns the number of fanins not beloning to the set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Spl_ManCountMarkedFanins( Gia_Man_t * p, int iObj, Vec_Bit_t * vMarks )
{
    int k, iFan, Count = 0;
    Gia_LutForEachFanin( p, iObj, iFan, k )
        if ( Vec_BitEntry(vMarks, iFan) )
            Count++;
    return Count;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Spl_ManFindOne( Spl_Man_t * p )
{
    int nFanouts, iObj, iFan, i, k;
    int Res = 0, InCount, InCountMax = -1; 
    Vec_IntClear( p->vCands );
    Vec_IntClear( p->vInputs );
    // deref
    Vec_IntForEachEntry( p->vNodes, iObj, i )
        Gia_LutForEachFanin( p->pGia, iObj, iFan, k )
            Gia_ObjLutRefDecId( p->pGia, iFan );
    // consider LUT inputs - get one that has no refs
    Vec_IntForEachEntry( p->vNodes, iObj, i )
        Gia_LutForEachFanin( p->pGia, iObj, iFan, k )
            if ( !Vec_BitEntry(p->vMarksNo, iFan) && !Vec_BitEntry(p->vMarksCIO, iFan) )
            {
                if ( !Gia_ObjLutRefNumId(p->pGia, iFan) )
                {
                    Res = iFan;
                    goto finish;
                }
                Vec_IntPush( p->vCands, iFan );
                Vec_IntPush( p->vInputs, iFan );
            }

    // all inputs have refs - collect external nodes
    Vec_IntForEachEntry( p->vNodes, iObj, i )
    {
        if ( Gia_ObjLutRefNumId(p->pGia, iObj) == 0 )
            continue;
        assert( Gia_ObjLutRefNumId(p->pGia, iObj) > 0 );
        if ( Gia_ObjLutRefNumId(p->pGia, iObj) >= 5 )
            continue;
        nFanouts = Spl_ManLutFanouts( p->pGia, iObj, p->vFanouts, p->vMarksNo, p->vMarksCIO );
        if ( Gia_ObjLutRefNumId(p->pGia, iObj) == 1 && nFanouts == 1 )
        {
            Res = Vec_IntEntry(p->vFanouts, 0);
            goto finish;
        }
        Vec_IntAppend( p->vCands, p->vFanouts );
    }

    // mark leaves
    Vec_IntForEachEntry( p->vInputs, iObj, i )
        Vec_BitWriteEntry( p->vMarksIn, iObj, 1 );
    // find candidate with maximum input overlap
    Vec_IntForEachEntry( p->vCands, iObj, i )
    {
        InCount = Spl_ManCountMarkedFanins( p->pGia, iObj, p->vMarksIn );
        if ( InCountMax < InCount )
        {
            InCountMax = InCount;
            Res = iObj;
        }
    }
    // unmark leaves
    Vec_IntForEachEntry( p->vInputs, iObj, i )
        Vec_BitWriteEntry( p->vMarksIn, iObj, 0 );

    // get the first candidate
    if ( Res == 0 && Vec_IntSize(p->vCands) > 0 )
        Res = Vec_IntEntry( p->vCands, 0 );

finish:
    // deref
    Vec_IntForEachEntry( p->vNodes, iObj, i )
        Gia_LutForEachFanin( p->pGia, iObj, iFan, k )
            Gia_ObjLutRefIncId( p->pGia, iFan );
    return Res;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Spl_ManComputeOne( Spl_Man_t * p, int iPivot )
{
    int CountAdd, iObj, i;
    assert( Gia_ObjIsLut(p->pGia, iPivot) );
    // assume it was previously filled in
    Vec_IntForEachEntry( p->vNodes, iObj, i )
        Vec_BitWriteEntry( p->vMarksNo, iObj, 0 );
    // double check that it is empty
    //Gia_ManForEachLut( p->pGia, iObj )
    //    assert( !Vec_BitEntry(p->vMarksNo, iObj) );
    // add root node
    Vec_IntFill( p->vNodes, 1, iPivot );
    Vec_BitWriteEntry( p->vMarksNo, iPivot, 1 );
    //printf( "%d ", iPivot );
    // add one node at a time
    p->Count = Spl_ManLutMffcSize( p->pGia, iPivot );
    while ( (iObj = Spl_ManFindOne(p)) )
    {
        assert( Gia_ObjIsLut(p->pGia, iObj) );
        CountAdd = Spl_ManLutMffcSize( p->pGia, iObj );
        if ( p->Count + CountAdd > p->Limit )
            break;
        p->Count += CountAdd;
        Vec_IntPush( p->vNodes, iObj );
        Vec_BitWriteEntry( p->vMarksNo, iObj, 1 );
        //printf( "+%d ", iObj );
    }
    //printf( "\n" );
    Vec_IntSort( p->vNodes, 0 );
}

void Spl_ManComputeOneTest( Gia_Man_t * pGia )
{
    int iLut;
    Spl_Man_t * p = Spl_ManAlloc( pGia, 64 );
    Gia_ManForEachLut( pGia, iLut )
    {
        Spl_ManComputeOne( p, iLut );
        Spl_ManWinFindLeavesRoots( p );
        // Vec_IntPrint( p->vNodes );
        printf( "Obj = %6d : Leaf = %2d.  Node = %2d.  Root = %2d.    AND = %3d.\n", 
            iLut, Vec_IntSize(p->vLeaves), Vec_IntSize(p->vNodes), Vec_IntSize(p->vRoots), p->Count ); 
    }
    Spl_ManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

