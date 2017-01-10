/**CFile****************************************************************

  FileName    [acecTree.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [CEC for arithmetic circuits.]

  Synopsis    [Adder tree construction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: acecTree.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acecInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Find internal cut points with exactly one adder fanin/fanout.]

  Description [Returns a map of point into its input/output adder.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec_TreeAddInOutPoint( Vec_Int_t * vMap, int iObj, int iAdd, int fOut )
{
    int * pPlace = Vec_IntEntryP( vMap, Abc_Var2Lit(iObj, fOut) );
    if ( *pPlace == -1 )
        *pPlace = iAdd;
    else if ( *pPlace >= 0 )
        *pPlace = -2;
}
Vec_Int_t * Acec_TreeFindPoints( Gia_Man_t * p, Vec_Int_t * vAdds )
{
    Vec_Int_t * vMap = Vec_IntStartFull( 2*Gia_ManObjNum(p) );
    int i;
    for ( i = 0; 6*i < Vec_IntSize(vAdds); i++ )
    {
        Acec_TreeAddInOutPoint( vMap, Vec_IntEntry(vAdds, 6*i+0), i, 0 );
        Acec_TreeAddInOutPoint( vMap, Vec_IntEntry(vAdds, 6*i+1), i, 0 );
        Acec_TreeAddInOutPoint( vMap, Vec_IntEntry(vAdds, 6*i+2), i, 0 );
        Acec_TreeAddInOutPoint( vMap, Vec_IntEntry(vAdds, 6*i+3), i, 1 );
        Acec_TreeAddInOutPoint( vMap, Vec_IntEntry(vAdds, 6*i+4), i, 1 );
    }
    return vMap;
}

/**Function*************************************************************

  Synopsis    [Find adder trees as groups of adders connected vis cut-points.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec_TreeWhichPoint( Vec_Int_t * vAdds, int iAdd, int iObj )
{
    int k;
    for ( k = 0; k < 5; k++ )
        if ( Vec_IntEntry(vAdds, 6*iAdd+k) == iObj )
            return k;
    assert( 0 );
    return -1;
}
void Acec_TreeFindTrees2_rec( Vec_Int_t * vAdds, Vec_Int_t * vMap, int iAdd, int Rank, Vec_Int_t * vTree, Vec_Bit_t * vFound )
{
    extern void Acec_TreeFindTrees_rec( Vec_Int_t * vAdds, Vec_Int_t * vMap, int iObj, int Rank, Vec_Int_t * vTree, Vec_Bit_t * vFound );
    int k;
    if ( Vec_BitEntry(vFound, iAdd) )
        return;
    Vec_BitWriteEntry( vFound, iAdd, 1 );
    Vec_IntPush( vTree, iAdd );
    Vec_IntPush( vTree, Rank );
    //printf( "Assigning rank %d to (%d:%d).\n", Rank, Vec_IntEntry(vAdds, 6*iAdd+3), Vec_IntEntry(vAdds, 6*iAdd+4) );
    for ( k = 0; k < 5; k++ )
        Acec_TreeFindTrees_rec( vAdds, vMap, Vec_IntEntry(vAdds, 6*iAdd+k), k == 4 ? Rank + 1 : Rank, vTree, vFound );
}
void Acec_TreeFindTrees_rec( Vec_Int_t * vAdds, Vec_Int_t * vMap, int iObj, int Rank, Vec_Int_t * vTree, Vec_Bit_t * vFound )
{
    int In  = Vec_IntEntry( vMap, Abc_Var2Lit(iObj, 1) );
    int Out = Vec_IntEntry( vMap, Abc_Var2Lit(iObj, 0) );
    if ( In < 0 || Out < 0 )
        return;
    Acec_TreeFindTrees2_rec( vAdds, vMap, In,  Acec_TreeWhichPoint(vAdds, In, iObj) == 4 ? Rank-1 : Rank, vTree, vFound );
    Acec_TreeFindTrees2_rec( vAdds, vMap, Out, Rank, vTree, vFound );
}
Vec_Wec_t * Acec_TreeFindTrees( Gia_Man_t * p, Vec_Int_t * vAdds )
{
    Vec_Wec_t * vTrees = Vec_WecAlloc( 10 );
    Vec_Int_t * vMap   = Acec_TreeFindPoints( p, vAdds );
    Vec_Bit_t * vFound = Vec_BitStart( Vec_IntSize(vAdds)/6 );
    Vec_Int_t * vTree;
    int i, k, In, Out, Box, Rank, MinRank;
    // go through the cut-points
    Vec_IntForEachEntryDouble( vMap, In, Out, i )
    {
        if ( In < 0 || Out < 0 )
            continue;
        assert( Vec_BitEntry(vFound, In) == Vec_BitEntry(vFound, Out) );
        if ( Vec_BitEntry(vFound, In) )
            continue;
        vTree = Vec_WecPushLevel( vTrees );
        Acec_TreeFindTrees_rec( vAdds, vMap, i/2, 0, vTree, vFound );
        // normalize rank
        MinRank = ABC_INFINITY;
        Vec_IntForEachEntryDouble( vTree, Box, Rank, k )
            MinRank = Abc_MinInt( MinRank, Rank );
        Vec_IntForEachEntryDouble( vTree, Box, Rank, k )
            Vec_IntWriteEntry( vTree, k+1, Rank - MinRank );
    }
    Vec_BitFree( vFound );
    Vec_IntFree( vMap );
    // sort by size
    Vec_WecSort( vTrees, 1 );
    return vTrees;
}
void Acec_TreeFindTreesTest( Gia_Man_t * p )
{
    Vec_Wec_t * vTrees;

    abctime clk = Abc_Clock();
    Vec_Int_t * vAdds = Ree_ManComputeCuts( p, NULL, 1 );
    int nFadds = Ree_ManCountFadds( vAdds );
    printf( "Detected %d adders (%d FAs and %d HAs).  ", Vec_IntSize(vAdds)/6, nFadds, Vec_IntSize(vAdds)/6-nFadds );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

    clk = Abc_Clock();
    vTrees = Acec_TreeFindTrees( p, vAdds );
    printf( "Collected %d trees with %d adders in them.  ", Vec_WecSize(vTrees), Vec_WecSizeSize(vTrees)/2 );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Vec_WecPrint( vTrees, 0 );

    Vec_WecFree( vTrees );
    Vec_IntFree( vAdds );
}


/**Function*************************************************************

  Synopsis    [Creates leaves and roots.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec_PrintRootLits( Vec_Wec_t * vRoots )
{
    Vec_Int_t * vLevel;
    int i, k, iObj;
    Vec_WecForEachLevel( vRoots, vLevel, i )
    {
        printf( "Rank %d : ", i );
        Vec_IntForEachEntry( vLevel, iObj, k )
        {
            int fFadd = Abc_LitIsCompl(iObj);
            int fCout = Abc_LitIsCompl(Abc_Lit2Var(iObj));
            int Node  = Abc_Lit2Var(Abc_Lit2Var(iObj));
            printf( "%d%s%s ", Node, fCout ? "*" : "", (fCout && fFadd) ? "*" : "" );
        }
        printf( "\n" );
    }
}
int Acec_CreateBoxMaxRank( Vec_Int_t * vTree )
{
    int k, Box, Rank, MaxRank = 0;
    Vec_IntForEachEntryDouble( vTree, Box, Rank, k )
        MaxRank = Abc_MaxInt( MaxRank, Rank );
    return MaxRank;
}
void Acec_BoxInsOuts( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Int_t * vTree, Vec_Wec_t * vLeaves, Vec_Wec_t * vRoots )
{
    Vec_Bit_t * vIsLeaf = Vec_BitStart( Gia_ManObjNum(p) );
    Vec_Bit_t * vIsRoot = Vec_BitStart( Gia_ManObjNum(p) );
    Vec_Int_t * vLevel;
    int i, k, Box, Rank;
    Vec_BitWriteEntry( vIsLeaf, 0, 1 );
    Vec_BitWriteEntry( vIsRoot, 0, 1 );
    Vec_IntForEachEntryDouble( vTree, Box, Rank, i )
    {
        Vec_BitWriteEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+0), 1 );
        Vec_BitWriteEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+1), 1 );
        Vec_BitWriteEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+2), 1 );
        Vec_BitWriteEntry( vIsRoot, Vec_IntEntry(vAdds, 6*Box+3), 1 );
        Vec_BitWriteEntry( vIsRoot, Vec_IntEntry(vAdds, 6*Box+4), 1 );
    }
    Vec_IntForEachEntryDouble( vTree, Box, Rank, i )
    {
        for ( k = 0; k < 3; k++ )
        {
            if ( Vec_BitEntry( vIsRoot, Vec_IntEntry(vAdds, 6*Box+k) ) )
                continue;
            Vec_BitWriteEntry( vIsRoot, Vec_IntEntry(vAdds, 6*Box+k), 1 );
            Vec_WecPush( vLeaves, Rank, Vec_IntEntry(vAdds, 6*Box+k) );
        }
        for ( k = 3; k < 5; k++ )
        {
            if ( Vec_BitEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+k) ) )
                continue;
            Vec_BitWriteEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+k), 1 );
            Vec_WecPush( vRoots, k == 4 ? Rank + 1 : Rank, Abc_Var2Lit(Abc_Var2Lit(Vec_IntEntry(vAdds, 6*Box+k), k==4), Vec_IntEntry(vAdds, 6*Box+2)!=0)  );
        }
    }
    Vec_BitFree( vIsLeaf );
    Vec_BitFree( vIsRoot );
    // sort each level
    Vec_WecForEachLevel( vLeaves, vLevel, i )
        Vec_IntSort( vLevel, 0 );
    Vec_WecForEachLevel( vRoots, vLevel, i )
        Vec_IntSort( vLevel, 0 );
}

/**Function*************************************************************

  Synopsis    [Creates polarity.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec_BoxPhases( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Int_t * vTree, Vec_Wec_t * vLeaves, Vec_Wec_t * vRoots, Vec_Wec_t * vLeafLits, Vec_Wec_t * vRootLits )
{
}

/**Function*************************************************************

  Synopsis    [Derives one adder tree.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec_Box_t * Acec_CreateBox( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Int_t * vTree )
{
    Acec_Box_t * pBox = ABC_CALLOC( Acec_Box_t, 1 );
    pBox->pGia      = p;

    pBox->vLeafs    = Vec_WecStart( Acec_CreateBoxMaxRank(vTree) + 1 );
    pBox->vRoots    = Vec_WecStart( Vec_WecSize(pBox->vLeafs)    + 1 );

    Acec_BoxInsOuts( p, vAdds, vTree, pBox->vLeafs, pBox->vRoots );

    pBox->vLeafLits = Vec_WecStart( Vec_WecSize(pBox->vLeafs) );
    pBox->vRootLits = Vec_WecStart( Vec_WecSize(pBox->vRoots) );

    Acec_BoxPhases( p, vAdds, vTree, pBox->vLeafs, pBox->vRoots, pBox->vLeafLits, pBox->vRootLits );

    return pBox;
}
void Acec_CreateBoxTest( Gia_Man_t * p )
{
    extern void Acec_BoxFree( Acec_Box_t * pBox );
    Acec_Box_t * pBox;
    Vec_Wec_t * vTrees;

    abctime clk = Abc_Clock();
    Vec_Int_t * vAdds = Ree_ManComputeCuts( p, NULL, 1 );
    int nFadds = Ree_ManCountFadds( vAdds );
    printf( "Detected %d adders (%d FAs and %d HAs).  ", Vec_IntSize(vAdds)/6, nFadds, Vec_IntSize(vAdds)/6-nFadds );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

    clk = Abc_Clock();
    vTrees = Acec_TreeFindTrees( p, vAdds );
    printf( "Collected %d trees with %d adders in them.  ", Vec_WecSize(vTrees), Vec_WecSizeSize(vTrees)/2 );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Vec_WecPrint( vTrees, 0 );

    pBox = Acec_CreateBox( p, vAdds, Vec_WecEntry(vTrees, 0) );
    Vec_WecPrint( pBox->vLeafs, 0 );
    Vec_WecPrint( pBox->vRoots, 0 );
    Acec_PrintRootLits( pBox->vRoots );
    Acec_BoxFree( pBox );

    Vec_WecFree( vTrees );
    Vec_IntFree( vAdds );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec_Box_t * Acec_DeriveBox( Gia_Man_t * p )
{
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

