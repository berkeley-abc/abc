/**CFile****************************************************************

  FileName    [acecPool.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [CEC for arithmetic circuits.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: acecPool.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acecInt.h"
#include "misc/vec/vecWec.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Bit_t * Acec_ManPoolGetPointed( Gia_Man_t * p, Vec_Int_t * vAdds )
{
    Vec_Bit_t * vMarks = Vec_BitStart( Gia_ManObjNum(p) );
    int i, k;
    for ( i = 0; 6*i < Vec_IntSize(vAdds); i++ )
        for ( k = 0; k < 3; k++ )
            Vec_BitWriteEntry( vMarks, Vec_IntEntry(vAdds, 6*i+k), 1 );
    return vMarks;
}

Vec_Int_t * Acec_ManPoolTopMost( Gia_Man_t * p, Vec_Int_t * vAdds )
{
    int i, k, iTop, fVerbose = 0;
    Vec_Int_t * vTops = Vec_IntAlloc( 1000 );
    Vec_Bit_t * vMarks = Acec_ManPoolGetPointed( p, vAdds );

    for ( i = 0; 6*i < Vec_IntSize(vAdds); i++ )
        if ( !Vec_BitEntry(vMarks, Vec_IntEntry(vAdds, 6*i+3)) && 
             !Vec_BitEntry(vMarks, Vec_IntEntry(vAdds, 6*i+4)) )
            Vec_IntPush( vTops, i );

    if ( fVerbose )
    Vec_IntForEachEntry( vTops, iTop, i )
    {
        printf( "%4d : ", iTop );
        for ( k = 0; k < 3; k++ )
            printf( "%4d ", Vec_IntEntry(vAdds, 6*iTop+k) );
        printf( " -> " );
        for ( k = 3; k < 5; k++ )
            printf( "%4d ", Vec_IntEntry(vAdds, 6*iTop+k) );
        printf( "\n" );
    }

    Vec_BitFree( vMarks );
    return vTops;
}
void Acec_ManPool( Gia_Man_t * p )
{
    extern Vec_Int_t * Ree_ManComputeCuts( Gia_Man_t * p, int fVerbose );
    extern Vec_Wec_t * Gia_PolynCoreOrderArray( Gia_Man_t * pGia, Vec_Int_t * vAdds, Vec_Int_t * vRootBoxes );

    extern int Ree_ManCountFadds( Vec_Int_t * vAdds );
    extern void Ree_ManPrintAdders( Vec_Int_t * vAdds, int fVerbose );
    extern void Ree_ManRemoveTrivial( Gia_Man_t * p, Vec_Int_t * vAdds );
    extern void Ree_ManRemoveContained( Gia_Man_t * p, Vec_Int_t * vAdds );
    Vec_Int_t * vTops, * vTree;
    Vec_Wec_t * vTrees;

    abctime clk = Abc_Clock();
    Vec_Int_t * vAdds = Ree_ManComputeCuts( p, 1 );
    int i, nFadds = Ree_ManCountFadds( vAdds );
    printf( "Detected %d FAs and %d HAs.  ", nFadds, Vec_IntSize(vAdds)/6-nFadds );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

    clk = Abc_Clock();
    Ree_ManRemoveTrivial( p, vAdds );
    Ree_ManRemoveContained( p, vAdds );
    nFadds = Ree_ManCountFadds( vAdds );
    printf( "Detected %d FAs and %d HAs.  ", nFadds, Vec_IntSize(vAdds)/6-nFadds );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

    //Ree_ManPrintAdders( vAdds, 1 );

    // detect topmost nodes
    vTops = Acec_ManPoolTopMost( p, vAdds );
    printf( "Detected %d topmost adder%s.\n", Vec_IntSize(vTops), Vec_IntSize(vTops) > 1 ? "s":"" );

    // collect adder trees
    vTrees = Gia_PolynCoreOrderArray( p, vAdds, vTops );
    Vec_WecForEachLevel( vTrees, vTree, i )
        printf( "Adder %5d : Tree with %5d nodes.\n", Vec_IntEntry(vTops, i), Vec_IntSize(vTree) );

    Vec_WecFree( vTrees );
    Vec_IntFree( vAdds );
    Vec_IntFree( vTops );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

