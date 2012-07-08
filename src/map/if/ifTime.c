/**CFile****************************************************************

  FileName    [ifTime.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Computation of delay paramters depending on the library.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifTime.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "bool/kit/kit.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define IF_BIG_CHAR 120

static float s_ExtraDel[2][3] = { {1.0, 1.0, (float)0.1}, {1.0, 1.0, (float)0.1} };

static void If_CutSortInputPins( If_Man_t * p, If_Cut_t * pCut, int * pPinPerm, float * pPinDelays );

int s_timeNew;
int s_timeOld;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Inserts the entry while sorting them by delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word If_AndVerifyArray( Vec_Wrd_t * vAnds, int nVars )
{
    Vec_Wrd_t * vTruths;
    If_And_t This;
    word Entry, Truth0, Truth1, TruthR = 0;
    int i;
    static word Truth[8] = {
        0xAAAAAAAAAAAAAAAA,
        0xCCCCCCCCCCCCCCCC,
        0xF0F0F0F0F0F0F0F0,
        0xFF00FF00FF00FF00,
        0xFFFF0000FFFF0000,
        0xFFFFFFFF00000000,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF
    };
    if ( Vec_WrdSize(vAnds) == 0 )
        return Truth[6];
    if ( Vec_WrdSize(vAnds) == 1 && Vec_WrdEntry(vAnds,0) == 0 )
        return Truth[7];
    vTruths = Vec_WrdAlloc( Vec_WrdSize(vAnds) );
    for ( i = 0; i < nVars; i++ )
        Vec_WrdPush( vTruths, Truth[i] );
    Vec_WrdForEachEntryStart( vAnds, Entry, i, nVars )
    {
        This   = If_WrdToAnd(Entry);
        Truth0 = Vec_WrdEntry( vTruths, This.iFan0 );
        Truth0 = This.fCompl0 ? ~Truth0 : Truth0;
        Truth1 = Vec_WrdEntry( vTruths, This.iFan1 );
        Truth1 = This.fCompl1 ? ~Truth1 : Truth1;
        TruthR = Truth0 & Truth1;
        Vec_WrdPush( vTruths, TruthR );
    }
    Vec_WrdFree( vTruths );
    TruthR = This.fCompl ? ~TruthR : TruthR;
    return TruthR;
}

/**Function*************************************************************

  Synopsis    [Inserts the entry while sorting them by delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_AndInsertSorted( Vec_Wrd_t * vAnds, If_And_t And )
{
    If_And_t This, Prev;
    int i;
    Vec_WrdPush( vAnds, If_AndToWrd(And) );
    for ( i = Vec_WrdSize(vAnds) - 1; i > 0; i-- )
    {
        This = If_WrdToAnd( Vec_WrdEntry(vAnds, i) );
        Prev = If_WrdToAnd( Vec_WrdEntry(vAnds, i-1) );
        if ( This.Delay <= Prev.Delay )
            break;
        Vec_WrdWriteEntry( vAnds, i,   If_AndToWrd(Prev) );
        Vec_WrdWriteEntry( vAnds, i-1, If_AndToWrd(This) );
    }
}

/**Function*************************************************************

  Synopsis    [Decomposes the cube into a bunch of AND gates.]

  Description [Records the result of decomposition into vLits. Returns
  the last AND gate of the decomposition.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_And_t If_CutDelaySopCube( Vec_Wrd_t * vCube, Vec_Wrd_t * vAnds, int fOrGate )
{
    If_And_t This, Prev, Next;
    assert( Vec_WrdSize(vCube) > 0 );
    while ( Vec_WrdSize(vCube) > 1 )
    {
        // get last
        This = If_WrdToAnd( Vec_WrdPop(vCube) );
        Prev = If_WrdToAnd( Vec_WrdPop(vCube) );
        // create new
        If_AndClear( &Next );
        Next.iFan0   = Prev.Id;
        Next.fCompl0 = Prev.fCompl ^ fOrGate;
        Next.iFan1   = This.Id;
        Next.fCompl1 = This.fCompl ^ fOrGate;
        Next.Id      = Vec_WrdSize(vAnds);
        Next.fCompl  = fOrGate;
        Next.Delay   = 1 + Abc_MaxInt( This.Delay, Prev.Delay );
        // add new
        If_AndInsertSorted( vCube, Next );
        Vec_WrdPush( vAnds, If_AndToWrd(Next) );
    }
    return If_WrdToAnd( Vec_WrdPop(vCube) );
}



/**Function*************************************************************

  Synopsis    [Returns the well-balanced structure of AIG nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wrd_t * If_CutDelaySopAnds( If_Man_t * p, If_Cut_t * pCut, Vec_Int_t * vCover, int fCompl )
{
    If_Obj_t * pLeaf;
    If_And_t Leaf;
    int i, k, Entry, Literal;
    Vec_WrdClear( p->vAnds );
    if ( Vec_IntSize(vCover) == 0 ) // const 0
    {
        assert( fCompl == 0 );
        return p->vAnds; 
    }
    if ( Vec_IntSize(vCover) == 1 && Vec_IntEntry(vCover, 0) == 0 ) // const 1
    {
        assert( fCompl == 0 );
        Vec_WrdPush( p->vAnds, 0 );
        return p->vAnds;
    }
    If_CutForEachLeaf( p, pCut, pLeaf, k )
    {
        If_AndClear( &Leaf );
        Leaf.Id     = k;
        Leaf.Delay  = (int)If_ObjCutBest(pLeaf)->Delay; 
        Vec_WrdPush( p->vAnds, If_AndToWrd(Leaf) );
    }
    // iterate through the cubes
    Vec_WrdClear( p->vOrGate );
    Vec_WrdClear( p->vAndGate );
    Vec_IntForEachEntry( vCover, Entry, i )
    { 
        Vec_WrdClear( p->vAndGate );
        If_CutForEachLeaf( p, pCut, pLeaf, k )
        {
            Literal = 3 & (Entry >> (k << 1));
            if ( Literal == 1 ) // neg literal
            {
                If_AndClear( &Leaf );
                Leaf.fCompl = 1;
                Leaf.Id     = k;
                Leaf.Delay  = (int)If_ObjCutBest(pLeaf)->Delay; 
                If_AndInsertSorted( p->vAndGate, Leaf );
            }
            else if ( Literal == 2 ) // pos literal
            {
                If_AndClear( &Leaf );
                Leaf.Id     = k;
                Leaf.Delay  = (int)If_ObjCutBest(pLeaf)->Delay; 
                If_AndInsertSorted( p->vAndGate, Leaf );
            }
            else if ( Literal != 0 ) 
                assert( 0 );
        }
        Leaf = If_CutDelaySopCube( p->vAndGate, p->vAnds, 0 );
        If_AndInsertSorted( p->vOrGate, Leaf );
    }
    Leaf = If_CutDelaySopCube( p->vOrGate, p->vAnds, 1 );
    if ( Vec_WrdSize(p->vAnds) == (int)pCut->nLeaves )
    {
//        Extra_PrintBinary( stdout, If_CutTruth(pCut), 32 ); printf( "\n" );
        assert( Leaf.Id < pCut->nLeaves );
        Leaf.iFan0 = Leaf.iFan1 = Leaf.Id;
        Leaf.Id    = Vec_WrdSize(p->vAnds);
        Vec_WrdPush( p->vAnds, If_AndToWrd(Leaf) );
    }
    if ( fCompl )
    {
        Leaf = If_WrdToAnd( Vec_WrdPop(p->vAnds) );
        Leaf.fCompl ^= 1;
        Vec_WrdPush( p->vAnds, If_AndToWrd(Leaf) );
    }
    return p->vAnds;
}

/**Function*************************************************************

  Synopsis    [Computes balanced AND decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wrd_t * If_CutDelaySopArray( If_Man_t * p, If_Cut_t * pCut )
{
    clock_t clk;
    Vec_Wrd_t * vAnds;
    int RetValue;
    if ( p->vCover == NULL )
        p->vCover   = Vec_IntAlloc(0);
    if ( p->vAnds == NULL )
        p->vAnds    = Vec_WrdAlloc(100);
    if ( p->vAndGate == NULL )
        p->vAndGate = Vec_WrdAlloc(100);
    if ( p->vOrGate == NULL )
        p->vOrGate  = Vec_WrdAlloc(100);
    RetValue = Kit_TruthIsop( If_CutTruth(pCut), If_CutLeaveNum(pCut), p->vCover, 1 );
    if ( RetValue == -1 )
        return NULL;
    assert( RetValue == 0 || RetValue == 1 );

    clk = clock();
    vAnds = If_CutDelaySopAnds( p, pCut, p->vCover, RetValue ^ pCut->fCompl );
    s_timeOld += clock() - clk;
/*
    if ( pCut->nLeaves <= 5 )
    {
        if ( *If_CutTruth(pCut) != (unsigned)If_AndVerifyArray(vAnds, pCut->nLeaves) )
        {
            unsigned Truth0 = *If_CutTruth(pCut);
            unsigned Truth1 = (unsigned)If_AndVerifyArray(vAnds, pCut->nLeaves);

            printf( "\n" );
            Extra_PrintBinary( stdout, &Truth0, 32 ); printf( "\n" );
            Extra_PrintBinary( stdout, &Truth1, 32 ); printf( "\n" );

            printf( "Verification failed for %d vars.\n", pCut->nLeaves );
        }
//        else
//            printf( "Verification passed for %d vars.\n", pCut->nLeaves );
    }
    else if ( pCut->nLeaves == 6 )
    {
        if ( *((word *)If_CutTruth(pCut)) != If_AndVerifyArray(vAnds, pCut->nLeaves) )
            printf( "Verification failed for %d vars.\n", pCut->nLeaves );
//        else
//            printf( "Verification passed for %d vars.\n", pCut->nLeaves );
    }
*/
    return vAnds;
}


/**Function*************************************************************

  Synopsis    [Derives the maximum depth from the leaf to the root.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutDelayLeafDepth_rec( Vec_Wrd_t * vAnds, If_And_t And, int iLeaf )
{
    int Depth0, Depth1, Depth;
    if ( (int)And.Id == iLeaf )
        return 0;
    if ( And.iFan0 == And.iFan1 )
        return -IF_BIG_CHAR;
    Depth0 = If_CutDelayLeafDepth_rec( vAnds, If_WrdToAnd(Vec_WrdEntry(vAnds, And.iFan0)), iLeaf );
    Depth1 = If_CutDelayLeafDepth_rec( vAnds, If_WrdToAnd(Vec_WrdEntry(vAnds, And.iFan1)), iLeaf );
    Depth  = Abc_MaxInt( Depth0, Depth1 );
    Depth  = (Depth == -IF_BIG_CHAR) ? -IF_BIG_CHAR : Depth + 1;
    return Depth;
}

/**Function*************************************************************

  Synopsis    [Derives the maximum depth from the leaf to the root.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutDelayLeafDepth( Vec_Wrd_t * vAnds, int iLeaf )
{
    If_And_t Leaf;
    if ( Vec_WrdSize(vAnds) == 0 ) // const 0
        return -IF_BIG_CHAR;
    if ( Vec_WrdSize(vAnds) == 1 && Vec_WrdEntry(vAnds, 0) == 0 ) // const 1
        return -IF_BIG_CHAR;
    Leaf = If_WrdToAnd(Vec_WrdEntryLast(vAnds));
    if ( Leaf.iFan0 == Leaf.iFan1 )
    {
        if ( (int)Leaf.iFan0 == iLeaf )
            return 0;
        return -IF_BIG_CHAR;
    }
    return If_CutDelayLeafDepth_rec( vAnds, Leaf, iLeaf );
}


/**Function*************************************************************

  Synopsis    [Computes the SOP delay using balanced AND decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutDelaySopCost( If_Man_t * p, If_Cut_t * pCut )
{
    If_And_t Leaf;
    Vec_Wrd_t * vAnds;
    int i, Delay;
    // mark cut as a user cut
    pCut->fUser = 1;
    vAnds = If_CutDelaySopArray( p, pCut );
    if ( vAnds == NULL )
    {
        assert( 0 );
        return ABC_INFINITY;
    }
    // get the cost
    If_AndClear( &Leaf );
    if ( Vec_WrdSize(vAnds) )
        Leaf = If_WrdToAnd( Vec_WrdEntryLast(vAnds) );
    if ( pCut->nLeaves > 2 && Vec_WrdSize(vAnds) > (int)pCut->nLeaves )
        pCut->Cost = Vec_WrdSize(vAnds) - pCut->nLeaves;
    else
        pCut->Cost = 1;
    // get the permutation
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
    {
        Delay = If_CutDelayLeafDepth( vAnds, i );
        pCut->pPerm[i] = (char)(Delay == -IF_BIG_CHAR ? IF_BIG_CHAR : Delay);
//printf( "%d ", pCut->pPerm[i] );
    }
//printf( " (%d)\n", Leaf.Delay );
    // verify the delay
//    Delay = If_CutDelay( p, pObj, pCut );
//    assert( (int)Leaf.Delay == Delay );
    return Leaf.Delay;
}


/**Function*************************************************************

  Synopsis    [Alternative computation of delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word If_CutDelayCountFormula( Vec_Int_t * vNums )
{
    word Count = 0;
    int i, Entry;
    Vec_IntForEachEntry( vNums, Entry, i )
    {
        if ( Entry < 0 )
            continue;
        assert( Entry < 60 );
        Count += ((word)1) << Entry;
    }
    return Count;
}
int If_CutDelayUseFormula( Vec_Int_t * vNums )
{
    int i, k, fChanges = 1;
//    word Count = If_CutDelayCountFormula( vNums );
//    Vec_IntPrint( vNums );
    while ( fChanges )
    {
        fChanges = 0;
        for ( i = Vec_IntSize(vNums) - 1; i > 0; i-- )
            if ( vNums->pArray[i] == vNums->pArray[i-1] )
            {
                vNums->pArray[i-1]++;
                for ( k = i; k < Vec_IntSize(vNums) - 1; k++ )
                    vNums->pArray[k] = vNums->pArray[k+1];
                Vec_IntShrink( vNums, Vec_IntSize(vNums)-1 );
                fChanges = 1;
            }
    }
//    assert( Count == If_CutDelayCountFormula(vNums) );
//    Vec_IntPrint( vNums );
//    printf( "\n" );
    if ( Vec_IntSize(vNums) == 1 )
        return vNums->pArray[0];
    return Vec_IntEntryLast(vNums) + 1;
}
int If_CutDelaySopAnds2( If_Man_t * p, If_Cut_t * pCut, Vec_Int_t * vCover, int fCompl, int * pArea )
{
    Vec_Int_t * vOrGate2  = (Vec_Int_t *)p->vOrGate;
    Vec_Int_t * vAndGate2 = (Vec_Int_t *)p->vAndGate;
    int Arrivals[16];
    If_Obj_t * pLeaf;
    int i, k, Entry, Literal;
    *pArea = 0;
    if ( Vec_IntSize(vCover) == 0 ) // const 0
    {
        assert( fCompl == 0 );
        return 0; 
    }
    if ( Vec_IntSize(vCover) == 1 && Vec_IntEntry(vCover, 0) == 0 ) // const 1
    {
        assert( fCompl == 0 );
        return 0; 
    }
    If_CutForEachLeaf( p, pCut, pLeaf, k )
        Arrivals[k] = (int)If_ObjCutBest(pLeaf)->Delay;
    // iterate through the cubes
    Vec_IntClear( vOrGate2 );
    Vec_IntForEachEntry( vCover, Entry, i )
    { 
        Vec_IntClear( vAndGate2 );
        for ( k = 0; k < (int)pCut->nLeaves; k++ )
        {
            Literal = 3 & (Entry >> (k << 1));
            if ( Literal == 1 ) // neg literal
                Vec_IntPushOrder( vAndGate2, Arrivals[k] );
            else if ( Literal == 2 ) // pos literal
                Vec_IntPushOrder( vAndGate2, Arrivals[k] );
            else if ( Literal != 0 ) 
                assert( 0 );
        }
        *pArea += Vec_IntSize(vAndGate2) - 1;
        Vec_IntPushOrder( vOrGate2, If_CutDelayUseFormula(vAndGate2) );
    }
    *pArea += Vec_IntSize(vOrGate2) - 1;
    return If_CutDelayUseFormula(vOrGate2);
}
int If_CutDelaySopArray2( If_Man_t * p, If_Cut_t * pCut, int * pArea )
{
    clock_t clk;
    int RetValue;
    if ( p->vCover == NULL )
        p->vCover = Vec_IntAlloc(0);
    if ( p->vAndGate == NULL )
        p->vAndGate = Vec_WrdAlloc(100);
    if ( p->vOrGate == NULL )
        p->vOrGate = Vec_WrdAlloc(100);
    RetValue = Kit_TruthIsop( If_CutTruth(pCut), If_CutLeaveNum(pCut), p->vCover, 1 );
    if ( RetValue == -1 )
        return -1;
    assert( RetValue == 0 || RetValue == 1 );

    clk = clock();
    RetValue = If_CutDelaySopAnds2( p, pCut, p->vCover, RetValue ^ pCut->fCompl, pArea );
//    RetValue = If_CutDelaySopAnds2_( p, pCut, p->vCover, RetValue ^ pCut->fCompl, pArea );
    s_timeNew += clock() - clk;
    return RetValue;
}
int If_CutDelaySopCost2( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    int i, DelayMax, Area;
    // mark cut as a user cut
    pCut->fUser = 1;
    DelayMax = If_CutDelaySopArray2( p, pCut, &Area );
    if ( DelayMax == -1 )
    {
        assert( 0 );
        return ABC_INFINITY;
    }
    // get the cost
    if ( pCut->nLeaves > 2 )
        pCut->Cost = Area;
    else
        pCut->Cost = 1;
    // get the permutation
    If_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        assert( DelayMax == 0 || DelayMax >= (int)If_ObjCutBest(pLeaf)->Delay );
        pCut->pPerm[i] = (char)(DelayMax - (int)If_ObjCutBest(pLeaf)->Delay);
//        printf( "%d ", pCut->pPerm[i] );
    }
//    printf( "(%d)     ", DelayMax );
    // verify the delay
//    Delay = If_CutDelay( p, pObj, pCut );
//    assert( (int)Leaf.Delay == Delay );
    return DelayMax;
}



/**Function*************************************************************

  Synopsis    [Computes the SOP delay using balanced AND decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_CutMaxCubeSize( Vec_Int_t * vCover, int nVars )
{
    int i, k, Entry, Literal, Count, CountMax = 0;
    Vec_IntForEachEntry( vCover, Entry, i )
    {
        Count = 0;
        for ( k = 0; k < nVars; k++ )
        {
            Literal = (3 & (Entry >> (k << 1)));
            if ( Literal == 1 || Literal == 2 )
                Count++;
        }
        CountMax = Abc_MaxInt( CountMax, Count );
    }
    return CountMax;
}
int If_CutDelaySop( If_Man_t * p, If_Cut_t * pCut )
{
    // delay is calculated using 1+log2(NumFanins)
    static double GateDelays[20] = { 1.00, 1.00, 2.00, 2.58, 3.00, 3.32, 3.58, 3.81, 4.00, 4.17, 4.32, 4.46, 4.58, 4.70, 4.81, 4.91, 5.00, 5.09, 5.17, 5.25 };
    If_Obj_t * pLeaf;
    int Delay, DelayMax;
    int i, nLitMax, RetValue;
    // mark cut as a user cut
    pCut->fUser = 1;
    if ( p->vCover == NULL )
        p->vCover = Vec_IntAlloc(0);
    RetValue = Kit_TruthIsop( If_CutTruth(pCut), If_CutLeaveNum(pCut), p->vCover, 1 );
    if ( RetValue == -1 )
        return ABC_INFINITY;
    assert( RetValue == 0 || RetValue == 1 );
    // mark the output as complemented
//    vAnds = If_CutDelaySopAnds( p, pCut, p->vCover, RetValue ^ pCut->fCompl );
    if ( Vec_IntSize(p->vCover) > p->pPars->nGateSize )
        return ABC_INFINITY;
    // set the area cost
    assert( If_CutLeaveNum(pCut) >= 0 && If_CutLeaveNum(pCut) <= 16 );
    // compute the gate delay
    nLitMax = If_CutMaxCubeSize( p->vCover, If_CutLeaveNum(pCut) );
    if ( Vec_IntSize(p->vCover) < 2 )
    {
        pCut->Cost = Vec_IntSize(p->vCover);
        Delay = (int)(GateDelays[If_CutLeaveNum(pCut)] + 0.5);
        DelayMax = 0;
        If_CutForEachLeaf( p, pCut, pLeaf, i )
            DelayMax = Abc_MaxInt( DelayMax, If_ObjCutBest(pLeaf)->Delay + (pCut->pPerm[i] = (char)Delay) );
    }
    else
    {
        pCut->Cost = Vec_IntSize(p->vCover) + 1;
        Delay = (int)(GateDelays[If_CutLeaveNum(pCut)] + GateDelays[nLitMax] + 0.5);
        DelayMax = 0;
        If_CutForEachLeaf( p, pCut, pLeaf, i )
            DelayMax = Abc_MaxInt( DelayMax, If_ObjCutBest(pLeaf)->Delay + (pCut->pPerm[i] = (char)Delay) );
    }
    return DelayMax;
}

/**Function*************************************************************

  Synopsis    [Computes delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutDelay( If_Man_t * p, If_Obj_t * pObj, If_Cut_t * pCut )
{
    static int pPinPerm[IF_MAX_LUTSIZE];
    static float pPinDelays[IF_MAX_LUTSIZE];
    If_Obj_t * pLeaf;
    float Delay, DelayCur;
    float * pLutDelays;
    int i, Shift, Pin2PinDelay, iLeaf;
    assert( p->pPars->fSeqMap || pCut->nLeaves > 1 );
    Delay = -IF_FLOAT_LARGE;
    if ( p->pPars->pLutLib )
    {
        assert( !p->pPars->fLiftLeaves );
        pLutDelays = p->pPars->pLutLib->pLutDelays[pCut->nLeaves];
        if ( p->pPars->pLutLib->fVarPinDelays )
        {
            // compute the delay using sorted pins
            If_CutSortInputPins( p, pCut, pPinPerm, pPinDelays );
            for ( i = 0; i < (int)pCut->nLeaves; i++ )
            {
                DelayCur = pPinDelays[pPinPerm[i]] + pLutDelays[i];
                Delay = IF_MAX( Delay, DelayCur );
            }
        }
        else
        {
            If_CutForEachLeaf( p, pCut, pLeaf, i )
            {
                if ( p->pDriverCuts && p->pDriverCuts[pObj->Id] && (iLeaf = Vec_IntFind(p->pDriverCuts[pObj->Id], pLeaf->Id)) >= 0 )
                    DelayCur = If_ObjCutBest(pLeaf)->Delay + s_ExtraDel[pObj->fDriver][iLeaf];
                else
                    DelayCur = If_ObjCutBest(pLeaf)->Delay + pLutDelays[0];
                Delay = IF_MAX( Delay, DelayCur );
            }
        }
    }
    else
    {
        if ( pCut->fUser )
        {
            assert( !p->pPars->fLiftLeaves );
            If_CutForEachLeaf( p, pCut, pLeaf, i )
            {
                Pin2PinDelay = pCut->pPerm ? (pCut->pPerm[i] == IF_BIG_CHAR ? -IF_BIG_CHAR : pCut->pPerm[i]) : 1;
                DelayCur = If_ObjCutBest(pLeaf)->Delay + (float)Pin2PinDelay;
                Delay = IF_MAX( Delay, DelayCur );
            }
        }
        else
        {
            if ( p->pPars->fLiftLeaves )
            {
                If_CutForEachLeafSeq( p, pCut, pLeaf, Shift, i )
                {
                    DelayCur = If_ObjCutBest(pLeaf)->Delay - Shift * p->Period;
                    Delay = IF_MAX( Delay, DelayCur + 1.0 );
                }
            }
            else
            {
                If_CutForEachLeaf( p, pCut, pLeaf, i )
                {
                    if ( p->pDriverCuts && p->pDriverCuts[pObj->Id] && (iLeaf = Vec_IntFind(p->pDriverCuts[pObj->Id], pLeaf->Id)) >= 0 )
                        DelayCur = If_ObjCutBest(pLeaf)->Delay + ((pObj->fDriver && iLeaf == 2) ? 0.0 : 1.0);
                    else
                        DelayCur = If_ObjCutBest(pLeaf)->Delay + 1.0;
                    Delay = IF_MAX( Delay, DelayCur );
                }
            }
        }
    }
    return Delay;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutPropagateRequired( If_Man_t * p, If_Obj_t * pObj, If_Cut_t * pCut, float ObjRequired )
{
    static int pPinPerm[IF_MAX_LUTSIZE];
    static float pPinDelays[IF_MAX_LUTSIZE];
    If_Obj_t * pLeaf;
    float * pLutDelays;
    float Required;
    int i, Pin2PinDelay, iLeaf;
    assert( !p->pPars->fLiftLeaves );
    // compute the pins
    if ( p->pPars->pLutLib )
    {
        pLutDelays = p->pPars->pLutLib->pLutDelays[pCut->nLeaves];
        if ( p->pPars->pLutLib->fVarPinDelays )
        {
            // compute the delay using sorted pins
            If_CutSortInputPins( p, pCut, pPinPerm, pPinDelays );
            for ( i = 0; i < (int)pCut->nLeaves; i++ )
            {
                Required = ObjRequired - pLutDelays[i];
                pLeaf = If_ManObj( p, pCut->pLeaves[pPinPerm[i]] );
                pLeaf->Required = IF_MIN( pLeaf->Required, Required );
            }
        }
        else
        {
            Required = ObjRequired;
            If_CutForEachLeaf( p, pCut, pLeaf, i )
            {
                if ( p->pDriverCuts && p->pDriverCuts[pObj->Id] && (iLeaf = Vec_IntFind(p->pDriverCuts[pObj->Id], pLeaf->Id)) >= 0 )
                    pLeaf->Required = IF_MIN( pLeaf->Required, Required - s_ExtraDel[pObj->fDriver][iLeaf] );
                else
                    pLeaf->Required = IF_MIN( pLeaf->Required, Required - pLutDelays[0] );
            }
        }
    }
    else
    {
        if ( pCut->fUser )
        {
            If_CutForEachLeaf( p, pCut, pLeaf, i )
            {
                Pin2PinDelay = pCut->pPerm ? (pCut->pPerm[i] == IF_BIG_CHAR ? -IF_BIG_CHAR : pCut->pPerm[i]) : 1;
                Required = ObjRequired - (float)Pin2PinDelay;
                pLeaf->Required = IF_MIN( pLeaf->Required, Required );
            }
        }
        else
        {
            Required = ObjRequired;
            If_CutForEachLeaf( p, pCut, pLeaf, i )
            {
                if ( p->pDriverCuts && p->pDriverCuts[pObj->Id] && (iLeaf = Vec_IntFind(p->pDriverCuts[pObj->Id], pLeaf->Id)) >= 0 )
                    pLeaf->Required = IF_MIN( pLeaf->Required, Required - (float)((pObj->fDriver && iLeaf == 2) ? 0.0 : 1.0) );
                else
                    pLeaf->Required = IF_MIN( pLeaf->Required, Required - (float)1.0 );
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    [Sorts the pins in the decreasing order of delays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutSortInputPins( If_Man_t * p, If_Cut_t * pCut, int * pPinPerm, float * pPinDelays )
{
    If_Obj_t * pLeaf;
    int i, j, best_i, temp;
    // start the trivial permutation and collect pin delays
    If_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        pPinPerm[i] = i;
        pPinDelays[i] = If_ObjCutBest(pLeaf)->Delay;
    }
    // selection sort the pins in the decreasible order of delays
    // this order will match the increasing order of LUT input pins
    for ( i = 0; i < (int)pCut->nLeaves-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < (int)pCut->nLeaves; j++ )
            if ( pPinDelays[pPinPerm[j]] > pPinDelays[pPinPerm[best_i]] )
                best_i = j;
        if ( best_i == i )
            continue;
        temp = pPinPerm[i]; 
        pPinPerm[i] = pPinPerm[best_i]; 
        pPinPerm[best_i] = temp;
    }
/*
    // verify
    assert( pPinPerm[0] < (int)pCut->nLeaves );
    for ( i = 1; i < (int)pCut->nLeaves; i++ )
    {
        assert( pPinPerm[i] < (int)pCut->nLeaves );
        assert( pPinDelays[pPinPerm[i-1]] >= pPinDelays[pPinPerm[i]] );
    }
*/
}

/**Function*************************************************************

  Synopsis    [Sorts the pins in the decreasing order of delays.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutRotatePins( If_Man_t * p, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    float PinDelays[32];
//    int PinPerm[32];
    int i;
//    assert( p->pPars->pLutLib && p->pPars->pLutLib->fVarPinDelays && p->pPars->fTruth ); 
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        PinDelays[i] = If_ObjCutBest(pLeaf)->Delay;
    If_CutTruthPermute( p->puTemp[0], If_CutTruth(pCut), If_CutLeaveNum(pCut), PinDelays, If_CutLeaves(pCut) );
//    If_CutSortInputPins( p, pCut, PinPerm, PinDelays );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

