/**CFile****************************************************************

  FileName    [acecXor.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [CEC for arithmetic circuits.]

  Synopsis    [Detection of XOR trees.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: acecXor.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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
Vec_Int_t * Acec_OrderXorRoots( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Int_t * vXorRoots, Vec_Wec_t * vXorTrees, Vec_Int_t * vMap )
{
    Vec_Int_t * vOrder = Vec_IntAlloc( Vec_WecSize(vXorTrees) );
    Vec_Int_t * vReMap = Vec_IntStartFull( Vec_WecSize(vXorTrees) );
    int i, k, Entry, This;
    // iterate through adders and for each try mark the next one
    for ( i = 0; 6*i < Vec_IntSize(vAdds); i++ )
    {
        int Node = Vec_IntEntry(vAdds, 6*i+4);
        if ( Vec_IntEntry(vMap, Node) == -1 )
            continue;
        for ( k = 0; k < 3; k++ )
        {
            int Fanin = Vec_IntEntry(vAdds, 6*i+k);
            if ( Vec_IntEntry(vMap, Fanin) == -1 )
                continue;
            //printf( "%4d:  %2d -> %2d\n", Node, Vec_IntEntry(vMap, Node), Vec_IntEntry(vMap, Fanin) );
            Vec_IntWriteEntry( vReMap, Vec_IntEntry(vMap, Node), Vec_IntEntry(vMap, Fanin) );
        }
    }
//Vec_IntPrint( vReMap );
    // find reodering
    Vec_IntForEachEntry( vReMap, Entry, i )
        if ( Entry == -1 && Vec_IntFind(vReMap, i) >= 0 )
            break;
    assert( i < Vec_IntSize(vReMap) );
    while ( 1 )
    {
        Vec_IntPush( vOrder, Vec_IntEntry(vXorRoots, i) );
        Entry = i;
        Vec_IntForEachEntry( vReMap, This, i )
            if ( This == Entry )
                break;
        if ( i == Vec_IntSize(vReMap) )
            break;
    }
    Vec_IntFree( vReMap );
//Vec_IntPrint( vOrder );
    return vOrder;
}
                       
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// marks nodes appearing as fanins to XORs
Vec_Bit_t * Acec_MapXorIns( Gia_Man_t * p, Vec_Int_t * vXors )
{
    Vec_Bit_t * vMap = Vec_BitStart( Gia_ManObjNum(p) ); int i;
    for ( i = 0; 4*i < Vec_IntSize(vXors); i++ )
    {
        Vec_BitWriteEntry( vMap, Vec_IntEntry(vXors, 4*i+1), 1 );
        Vec_BitWriteEntry( vMap, Vec_IntEntry(vXors, 4*i+2), 1 );
        Vec_BitWriteEntry( vMap, Vec_IntEntry(vXors, 4*i+3), 1 );
    }
    return vMap;
}
// marks nodes having XOR cuts
Vec_Bit_t * Acec_MapXorOuts( Gia_Man_t * p, Vec_Int_t * vXors )
{
    Vec_Bit_t * vMap = Vec_BitStart( Gia_ManObjNum(p) ); int i;
    for ( i = 0; 4*i < Vec_IntSize(vXors); i++ )
        Vec_BitWriteEntry( vMap, Vec_IntEntry(vXors, 4*i), 1 );
    return vMap;
}
// marks nodes appearing as outputs of MAJs
Vec_Bit_t * Acec_MapMajOuts( Gia_Man_t * p, Vec_Int_t * vAdds )
{
    Vec_Bit_t * vMap = Vec_BitStart( Gia_ManObjNum(p) ); int i;
    for ( i = 0; 6*i < Vec_IntSize(vAdds); i++ )
        Vec_BitWriteEntry( vMap, Vec_IntEntry(vAdds, 6*i+4), 1 );
    return vMap;
}
// maps MAJ outputs into their FAs and HAs
Vec_Int_t * Acec_MapMajOutsToAdds( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Bit_t * vXorOuts, Vec_Int_t * vMapRank )
{
    Vec_Int_t * vMap = Vec_IntStartFull( Gia_ManObjNum(p) ); int i;
    for ( i = 0; 6*i < Vec_IntSize(vAdds); i++ )
    {
        int Xor = Vec_IntEntry(vAdds, 6*i+3);
        int Maj = Vec_IntEntry(vAdds, 6*i+4);
        if ( Vec_IntEntry(vMap, Maj) >= 0 )
        {
            int i2 = Vec_IntEntry(vMap, Maj);
            int Xor2 = Vec_IntEntry(vAdds, 6*i2+3);
            int Maj2 = Vec_IntEntry(vAdds, 6*i2+4);
            printf( "*** Node %d has two MAJ adder drivers: %d%s (%d  rank %d) and %d%s (%d  rank %d).\n", 
                Maj, 
                i, Vec_IntEntry(vAdds, 6*i+2) ? "":"*", Vec_BitEntry(vXorOuts, Xor), Vec_IntEntry(vMapRank, Xor),
                i2, Vec_IntEntry(vAdds, 6*i2+2) ? "":"*", Vec_BitEntry(vXorOuts, Xor2), Vec_IntEntry(vMapRank, Xor2) );
        }
        Vec_IntWriteEntry( vMap, Vec_IntEntry(vAdds, 6*i+4), i );
    }
    return vMap;
}
// collects XOR roots (XOR nodes not appearing as fanins of other XORs)
Vec_Int_t * Acec_FindXorRoots( Gia_Man_t * p, Vec_Int_t * vXors )
{
    Vec_Bit_t * vMapXorIns = Acec_MapXorIns( p, vXors );
    Vec_Int_t * vXorRoots = Vec_IntAlloc( 100 );  int i;
    for ( i = 0; 4*i < Vec_IntSize(vXors); i++ )
        if ( !Vec_BitEntry(vMapXorIns, Vec_IntEntry(vXors, 4*i)) )
            Vec_IntPushUniqueOrder( vXorRoots, Vec_IntEntry(vXors, 4*i) );
    Vec_BitFree( vMapXorIns );
//Vec_IntRemove( vXorRoots, 54 );
    return vXorRoots;
}
// collects XOR trees belonging to each of XOR roots
Vec_Wec_t * Acec_FindXorTrees( Gia_Man_t * p, Vec_Int_t * vXors, Vec_Int_t * vXorRoots, Vec_Int_t ** pvMap )
{
    Vec_Int_t * vDoubles = Vec_IntAlloc( 100 );
    Vec_Wec_t * vXorTrees = Vec_WecStart( Vec_IntSize(vXorRoots) );
    Vec_Int_t * vLevel;
    int i, k, Entry;
    // map roots into their classes
    Vec_Int_t * vMap = Vec_IntStartFull( Gia_ManObjNum(p) ); 
    Vec_IntForEachEntry( vXorRoots, Entry, i )
    {
        Vec_IntWriteEntry( vMap, Entry, i );
        Vec_WecPush( vXorTrees, i, Entry );
    }
    // map nodes into their classes
    for ( i = Vec_IntSize(vXors)/4 - 1; i >= 0; i-- )
    {
        int Root = Vec_IntEntry( vXors, 4*i );
        int Repr = Vec_IntEntry( vMap, Root );
        //assert( Repr != -1 );
        if ( Repr == -1 )
            continue;
        for ( k = 1; k < 4; k++ )
        {
            int Node = Vec_IntEntry( vXors, 4*i+k );
            if ( Node == 0 )
                continue;
            Entry = Vec_IntEntry( vMap, Node );
            if ( Entry == Repr )
                continue;
            if ( Entry == -1 )
            {
                Vec_IntWriteEntry( vMap, Node, Repr );
                Vec_WecPush( vXorTrees, Repr, Node );
                continue;
            }
            //printf( "Node %d belongs to Tree %d and Tree %d.\n", Node, Entry, Repr );
            Vec_IntPushUnique( Vec_WecEntry(vXorTrees, Entry), Node );
            Vec_IntPush( vDoubles, Node );
        }
    }
    // clean map 
    Vec_IntForEachEntry( vDoubles, Entry, i )
        Vec_IntWriteEntry( vMap, Entry, -1 );
    Vec_IntFree( vDoubles );
    // sort nodes
    Vec_WecForEachLevel( vXorTrees, vLevel, i )
        Vec_IntSort( vLevel, 0 );
    if ( pvMap )
        *pvMap = vMap;
    else
        Vec_IntFree( vMap );
    return vXorTrees;
}
// collects leaves of each XOR tree
Vec_Wec_t * Acec_FindXorLeaves( Gia_Man_t * p, Vec_Int_t * vXors, Vec_Int_t * vAdds, Vec_Wec_t * vXorTrees, Vec_Int_t * vMap, Vec_Wec_t ** pvAddBoxes )
{
    Vec_Bit_t * vMapXorOuts = Acec_MapXorOuts( p, vXors );
    Vec_Int_t * vMapMajOuts = Acec_MapMajOutsToAdds( p, vAdds, vMapXorOuts, vMap );
    Vec_Wec_t * vXorLeaves = Vec_WecStart( Vec_WecSize(vXorTrees) );
    int i, k;
    if ( pvAddBoxes )
        *pvAddBoxes = Vec_WecStart( Vec_WecSize(vXorTrees) );
    // collect leaves
    for ( i = 0; 4*i < Vec_IntSize(vXors); i++ )
    {
        int Xor = Vec_IntEntry(vXors, 4*i);
        for ( k = 1; k < 4; k++ )
        {
            int Node = Vec_IntEntry(vXors, 4*i+k);
            if ( Node == 0 )
                continue;
            if ( Vec_BitEntry(vMapXorOuts, Node) || Vec_IntEntry(vMap, Xor) == -1 )
                continue;
            if ( Vec_IntEntry(vMapMajOuts, Node) == -1 ) // no maj driver
                Vec_WecPush( vXorLeaves, Vec_IntEntry(vMap, Xor), Node );
            else if ( pvAddBoxes && Vec_IntEntry(vMap, Xor) > 0 ) // save adder box
                Vec_WecPush( *pvAddBoxes, Vec_IntEntry(vMap, Xor)-1, Vec_IntEntry(vMapMajOuts, Node) );
        }
    }
/*
    if ( pvAddBoxes )
    {
        Vec_Int_t * vLevel;
        //Vec_WecPrint( *pvAddBoxes, 0 );
        Vec_WecForEachLevelReverse( *pvAddBoxes, vLevel, i )
            if ( Vec_IntSize(vLevel) > 0 )
                break;
        Vec_WecShrink( *pvAddBoxes, i+1 );
        //Vec_WecPrint( *pvAddBoxes, 0 );
    }
*/
    Vec_BitFree( vMapXorOuts );
    Vec_IntFree( vMapMajOuts );
    return vXorLeaves;
}

Acec_Box_t * Acec_FindBox( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Wec_t * vAddBoxes, Vec_Wec_t * vXorTrees, Vec_Wec_t * vXorLeaves )
{
    extern Vec_Int_t * Acec_TreeCarryMap( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Wec_t * vBoxes );
    extern void Acec_TreePhases_rec( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Int_t * vMap, int Node, int fPhase, Vec_Bit_t * vVisit );
    extern void Acec_TreeVerifyPhases( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Wec_t * vBoxes );
    extern void Acec_TreeVerifyPhases2( Gia_Man_t * p, Vec_Int_t * vAdds, Vec_Wec_t * vBoxes );

    int MaxRank = Vec_WecSize( vAddBoxes );
    Vec_Bit_t * vVisit  = Vec_BitStart( Vec_IntSize(vAdds)/6 );
    Vec_Bit_t * vIsLeaf = Vec_BitStart( Gia_ManObjNum(p) );
    Vec_Bit_t * vIsRoot = Vec_BitStart( Gia_ManObjNum(p) );
    Vec_Int_t * vLevel, * vLevel2, * vMap;
    int i, j, k, Box, Node;

    Acec_Box_t * pBox = ABC_CALLOC( Acec_Box_t, 1 );
    pBox->pGia        = p;
    pBox->vAdds       = vAddBoxes; // Vec_WecDup( vAddBoxes );
    pBox->vLeafLits   = Vec_WecStart( MaxRank + 0 );
    pBox->vRootLits   = Vec_WecStart( MaxRank + 0 );

    assert( Vec_WecSize(vAddBoxes) == Vec_WecSize(vXorTrees) );
    assert( Vec_WecSize(vAddBoxes) == Vec_WecSize(vXorLeaves) );

    // collect boxes; mark inputs/outputs
    Vec_WecForEachLevel( pBox->vAdds, vLevel, i )
    Vec_IntForEachEntry( vLevel, Box, k )
    {
        Vec_BitWriteEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+0), 1 );
        Vec_BitWriteEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+1), 1 );
        Vec_BitWriteEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+2), 1 );
        Vec_BitWriteEntry( vIsRoot, Vec_IntEntry(vAdds, 6*Box+3), 1 );
        Vec_BitWriteEntry( vIsRoot, Vec_IntEntry(vAdds, 6*Box+4), 1 );
    }
    // sort each level
    Vec_WecForEachLevel( pBox->vAdds, vLevel, i )
        Vec_IntSort( vLevel, 0 );

    // set phases starting from roots
    vMap = Acec_TreeCarryMap( p, vAdds, pBox->vAdds );
    Vec_WecForEachLevelReverse( pBox->vAdds, vLevel, i )
        Vec_IntForEachEntry( vLevel, Box, k )
            if ( !Vec_BitEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+4) ) )
            {
                //printf( "Pushing phase of output %d of box %d\n", Vec_IntEntry(vAdds, 6*Box+4), Box );
                Acec_TreePhases_rec( p, vAdds, vMap, Vec_IntEntry(vAdds, 6*Box+4), Vec_IntEntry(vAdds, 6*Box+2) != 0, vVisit );
            }
    Acec_TreeVerifyPhases( p, vAdds, pBox->vAdds );
    Acec_TreeVerifyPhases2( p, vAdds, pBox->vAdds );
    Vec_BitFree( vVisit );
    Vec_IntFree( vMap );

    // collect inputs/outputs
    Vec_BitWriteEntry( vIsRoot, 0, 1 );
    Vec_WecForEachLevel( pBox->vAdds, vLevel, i )
        Vec_IntForEachEntry( vLevel, Box, j )
        {
            for ( k = 0; k < 3; k++ )
                if ( !Vec_BitEntry( vIsRoot, Vec_IntEntry(vAdds, 6*Box+k) ) )
                    Vec_WecPush( pBox->vLeafLits, i, Abc_Var2Lit(Vec_IntEntry(vAdds, 6*Box+k), Acec_SignBit2(vAdds, Box, k)) );
            for ( k = 3; k < 5; k++ )
                if ( !Vec_BitEntry( vIsLeaf, Vec_IntEntry(vAdds, 6*Box+k) ) )
                    Vec_WecPush( pBox->vRootLits, k == 4 ? i + 1 : i, Abc_Var2Lit(Vec_IntEntry(vAdds, 6*Box+k), Acec_SignBit2(vAdds, Box, k)) );
            if ( Vec_IntEntry(vAdds, 6*Box+2) == 0 && Acec_SignBit2(vAdds, Box, 2) )
                Vec_WecPush( pBox->vLeafLits, i, 1 );
        }
    Vec_BitFree( vIsLeaf );
    Vec_BitFree( vIsRoot );

    // collect last bit
    vLevel  = Vec_WecEntry( pBox->vLeafLits, Vec_WecSize(pBox->vLeafLits)-1 );
    vLevel2 = Vec_WecEntry( vXorLeaves, Vec_WecSize(vXorLeaves)-1 );
    if ( Vec_IntSize(vLevel) == 0 && Vec_IntSize(vLevel2) > 0 )
    {
        Vec_IntForEachEntry( vLevel2, Node, k )
            Vec_IntPush( vLevel, Abc_Var2Lit(Node, 0) );
    }
    vLevel  = Vec_WecEntry( pBox->vRootLits, Vec_WecSize(pBox->vRootLits)-1 );
    vLevel2 = Vec_WecEntry( vXorTrees, Vec_WecSize(vXorTrees)-1 );
    Vec_IntClear( vLevel );
    if ( Vec_IntSize(vLevel) == 0 && Vec_IntSize(vLevel2) > 0 )
    {
        Vec_IntPush( vLevel, Abc_Var2Lit(Vec_IntEntryLast(vLevel2), 0) );
    }

    // sort each level
    Vec_WecForEachLevel( pBox->vLeafLits, vLevel, i )
        Vec_IntSort( vLevel, 0 );
    Vec_WecForEachLevel( pBox->vRootLits, vLevel, i )
        Vec_IntSort( vLevel, 1 );
    return pBox;
}

Acec_Box_t * Acec_DetectXorTrees( Gia_Man_t * p, int fVerbose )
{
    abctime clk = Abc_Clock();
    Acec_Box_t * pBox = NULL;
    Vec_Int_t * vXors, * vAdds = Ree_ManComputeCuts( p, &vXors, 0 );
    Vec_Int_t * vMap, * vXorRootsNew;
    Vec_Int_t * vXorRoots = Acec_FindXorRoots( p, vXors ); 
    Vec_Wec_t * vXorTrees = Acec_FindXorTrees( p, vXors, vXorRoots, &vMap ); 
    Vec_Wec_t * vXorLeaves, * vAddBoxes = NULL; 

    //Ree_ManPrintAdders( vAdds, 1 );
    printf( "Detected %d full-adders and %d half-adders.  Found %d XOR-cuts.  ", Ree_ManCountFadds(vAdds), Vec_IntSize(vAdds)/6-Ree_ManCountFadds(vAdds), Vec_IntSize(vXors)/4 );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

//    printf( "XOR roots: \n" );
//    Vec_IntPrint( vXorRoots );
//    Vec_WecPrint( vXorTrees, 0 );

    vXorRootsNew = Acec_OrderXorRoots( p, vAdds, vXorRoots, vXorTrees, vMap );
    Vec_IntFree( vXorRoots );
    Vec_WecFree( vXorTrees );
    Vec_IntFree( vMap );

    vXorRoots = vXorRootsNew; vXorRootsNew = NULL;
    vXorTrees = Acec_FindXorTrees( p, vXors, vXorRoots, &vMap ); 
    vXorLeaves = Acec_FindXorLeaves( p, vXors, vAdds, vXorTrees, vMap, &vAddBoxes ); 

    printf( "XOR roots: \n" );
    Vec_IntPrint( vXorRoots );
    printf( "XOR leaves: \n" );
    Vec_WecPrint( vXorLeaves, 0 );
    printf( "Adder boxes: \n" );
    Vec_WecPrint( vAddBoxes, 0 );

    pBox = Acec_FindBox( p, vAdds, vAddBoxes, vXorTrees, vXorLeaves );

    Acec_TreePrintBox( pBox, vAdds );

    Vec_IntFree( vXorRoots );
    Vec_WecFree( vXorTrees );
    Vec_WecFree( vXorLeaves );
    //Vec_WecFree( vAddBoxes );

    Vec_IntFree( vMap );
    Vec_IntFree( vXors );
    Vec_IntFree( vAdds );

    return pBox;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

