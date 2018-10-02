/**CFile****************************************************************

  FileName    [dau.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware unmapping.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: dau.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dauInt.h"
#include "misc/util/utilTruth.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Dtt_Man_t_ Dtt_Man_t;
struct Dtt_Man_t_
{
    int            nVars;          // variable number
    int            nPerms;         // number of permutations
    int            nComps;         // number of complementations
    int *          pPerms;         // permutations
    int *          pComps;         // complementations
    word *         pPres;          // function marks
    Vec_Int_t *    vFanins;        // node fanins
    Vec_Int_t *    vTruths;        // node truth tables
    Vec_Int_t *    vConfigs;       // configurations
    Vec_Int_t *    vClasses;       // node NPN classes
    Vec_Int_t *    vTruthNpns;     // truth tables of the classes
    Vec_Wec_t *    vFunNodes;      // nodes by NPN class
    Vec_Int_t *    vTemp;          // temporary
    Vec_Int_t *    vTemp2;         // temporary
    unsigned       FunMask;        // function mask
    unsigned       CmpMask;        // function mask
    unsigned       BinMask;        // hash mask
    unsigned *     pBins;          // hash bins
    Vec_Int_t *    vUsedBins;      // used bins
    int            Counts[32];     // node counts
    int            nClasses;       // count of classes
    unsigned *     pTable;         // mapping of funcs into their classes
    int *          pNodes;         // the number of nodes in min-node network
    int *          pTimes;         // the number of different min-node networks
    char *         pVisited;       // visited classes
    Vec_Int_t *    vVisited;       // the number of visited classes
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
unsigned * Dau_ReadFile2( char * pFileName, int nSizeW )
{
    abctime clk = Abc_Clock();
    FILE * pFile = fopen( pFileName, "rb" );
    unsigned * p = (unsigned *)ABC_CALLOC(word, nSizeW);
    int RetValue = pFile ? fread( p, sizeof(word), nSizeW, pFile ) : 0;
    RetValue = 0;
    if ( pFile )
    {
        printf( "Finished reading file \"%s\".\n", pFileName );
        fclose( pFile );
    }
    else
        printf( "Cannot open input file \"%s\".\n", pFileName );
    Abc_PrintTime( 1, "File reading", Abc_Clock() - clk );
    return p;
}
void Dtt_ManRenum( int nVars, unsigned * pTable, int * pnClasses )
{
    unsigned i, Limit = 1 << ((1 << nVars)-1), Count = 0;
    for ( i = 0; i < Limit; i++ )
        if ( pTable[i] == i )
            pTable[i] = Count++;
        else 
        {
            assert( pTable[i] < i );
            pTable[i] = pTable[pTable[i]];
        }
    printf( "The total number of NPN classes = %d.\n", Count );
    *pnClasses = Count;
}
unsigned * Dtt_ManLoadClasses( int nVars, int * pnClasses )
{
    unsigned * pTable = NULL;
    if ( nVars == 4 )
        pTable = Dau_ReadFile2( "tableW14.data", 1 << 14 );
    else if ( nVars == 5 )
        pTable = Dau_ReadFile2( "tableW30.data", 1 << 30 );
    else assert( 0 );
    Dtt_ManRenum( nVars, pTable, pnClasses );
    return pTable;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dtt_ManAddVisited( Dtt_Man_t * p, unsigned Truth2, int n )
{
    unsigned Truth = Truth2 & p->CmpMask ? ~Truth2 : Truth2;
    unsigned Class = p->pTable[Truth & p->FunMask];
    assert( Class < (unsigned)p->nClasses );
    if ( p->pNodes[Class] < n )
        return;
    assert( p->pNodes[Class] == n );
    if ( p->pVisited[Class] )
        return;
    p->pVisited[Class] = 1;
    Vec_IntPush( p->vVisited, Class );
}
void Dtt_ManProcessVisited( Dtt_Man_t * p )
{
    int i, Class;
    Vec_IntForEachEntry( p->vVisited, Class, i )
    {
        assert( p->pVisited[Class] );
        p->pVisited[Class] = 0;
        p->pTimes[Class]++;
    }
    Vec_IntClear( p->vVisited );
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dtt_Man_t * Dtt_ManAlloc( int nVars, int fMulti )
{
    Dtt_Man_t * p = ABC_CALLOC( Dtt_Man_t, 1 );
    p->nVars      = nVars;
    p->nPerms     = Extra_Factorial( nVars );
    p->nComps     = 1 << nVars;
    p->pPerms     = Extra_PermSchedule( nVars );
    p->pComps     = Extra_GreyCodeSchedule( nVars );
    p->pPres      = ABC_CALLOC( word, 1 << (p->nComps - 7) );
    p->vFanins    = Vec_IntAlloc( 2*617000 );
    p->vTruths    = Vec_IntAlloc( 617000 );
    p->vConfigs   = Vec_IntAlloc( 617000 );
    p->vClasses   = Vec_IntAlloc( 617000 );
    p->vTruthNpns = Vec_IntAlloc( 617000 );
    p->vFunNodes  = Vec_WecStart( 16 );
    p->vTemp      = Vec_IntAlloc( 4000 );
    p->vTemp2     = Vec_IntAlloc( 4000 );
    p->FunMask    = nVars == 5 ?      ~0 : (nVars == 4 ?  0xFFFF :   0xFF);
    p->CmpMask    = nVars == 5 ? 1 << 31 : (nVars == 4 ? 1 << 15 : 1 << 7);
    p->BinMask    = 0x3FFF;
    p->pBins      = ABC_FALLOC( unsigned, p->BinMask + 1 );
    p->vUsedBins  = Vec_IntAlloc( 4000 );
    if ( !fMulti ) return p;
    p->pTable     = Dtt_ManLoadClasses( p->nVars, &p->nClasses );
    p->pNodes     = ABC_CALLOC( int, p->nClasses );
    p->pTimes     = ABC_CALLOC( int, p->nClasses );
    p->pVisited   = ABC_CALLOC( char, p->nClasses );
    p->vVisited   = Vec_IntAlloc( 1000 );
    return p;
}
void Dtt_ManFree( Dtt_Man_t * p )
{
    Vec_IntFreeP( &p->vVisited );
    ABC_FREE( p->pTable );
    ABC_FREE( p->pNodes );
    ABC_FREE( p->pTimes );
    ABC_FREE( p->pVisited );
    Vec_IntFreeP( &p->vFanins );
    Vec_IntFreeP( &p->vTruths );
    Vec_IntFreeP( &p->vConfigs );
    Vec_IntFreeP( &p->vClasses );
    Vec_IntFreeP( &p->vTruthNpns );
    Vec_WecFreeP( &p->vFunNodes );
    Vec_IntFreeP( &p->vTemp );
    Vec_IntFreeP( &p->vTemp2 );
    Vec_IntFreeP( &p->vUsedBins );
    ABC_FREE( p->pPerms );
    ABC_FREE( p->pComps );
    ABC_FREE( p->pPres );
    ABC_FREE( p->pBins );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Collect representatives of the same class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Dtt_ManHashKey( Dtt_Man_t * p, unsigned Truth )
{
    static unsigned s_P[4] = { 1699, 5147, 7103, 8147 };
    unsigned char * pD = (unsigned char*)&Truth;
    return pD[0] * s_P[0] + pD[1] * s_P[1] + pD[2] * s_P[2] + pD[3] * s_P[3];
}
int Dtt_ManCheckHash( Dtt_Man_t * p, unsigned Truth )
{
    unsigned Hash = Dtt_ManHashKey(p, Truth);
    unsigned * pSpot = p->pBins + (Hash & p->BinMask);
    for ( ; ~*pSpot; Hash++, pSpot = p->pBins + (Hash & p->BinMask) )
        if ( *pSpot == Truth ) // equal
            return 0;
    Vec_IntPush( p->vUsedBins, pSpot - p->pBins );
    *pSpot = Truth;
    return 1;
}
Vec_Int_t * Dtt_ManCollect( Dtt_Man_t * p, unsigned Truth, Vec_Int_t * vFuns )
{
    int i, k, Entry, Shift = (1 << p->nVars) - 1;
    word tCur = ((word)Truth << 32) | (word)Truth;
    Vec_IntClear( vFuns );
    for ( i = 0; i < p->nPerms; i++ )
    {
        for ( k = 0; k < p->nComps; k++ )
        {
//            unsigned tTemp = (unsigned)(tCur & 1 ? ~tCur : tCur);
            unsigned tTemp = (unsigned)(tCur & p->CmpMask ? ~tCur : tCur);
            if ( Dtt_ManCheckHash( p, tTemp ) )
                Vec_IntPush( vFuns, tTemp );
            tCur = Abc_Tt6Flip( tCur, p->pComps[k] );
        }
        tCur = Abc_Tt6SwapAdjacent( tCur, p->pPerms[i] );
    }
    assert( tCur == (((word)Truth << 32) | (word)Truth) );
    // clean hash table
    Vec_IntForEachEntry( p->vUsedBins, Entry, i )
        p->pBins[Entry] = ~0;
    Vec_IntClear( p->vUsedBins );
    //printf( "%d ", Vec_IntSize(vFuns) );
    return vFuns;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Dtt_ManGetFun( Dtt_Man_t * p, unsigned tFun )
{
    tFun = tFun & p->CmpMask ? ~tFun : tFun;
    return Abc_TtGetBit( p->pPres, tFun & p->FunMask );
}
static inline void Dtt_ManSetFun( Dtt_Man_t * p, unsigned tFun )
{
    tFun = tFun & p->CmpMask ? ~tFun : tFun;
    //assert( !Dtt_ManGetFun(p, fFun & p->FunMask );
    Abc_TtSetBit( p->pPres, tFun & p->FunMask );
}
void Dtt_ManAddFunction( Dtt_Man_t * p, int n, int FanI, int FanJ, int Type, unsigned Truth )
{
    Vec_Int_t * vFuncs = Dtt_ManCollect( p, Truth, p->vTemp2 );
    unsigned Min = Vec_IntFindMin( vFuncs ); 
    int i, nObjs = Vec_IntSize(p->vFanins)/2;
    int nNodesI = 0xF & (Vec_IntEntry(p->vConfigs, FanI) >> 3);
    int nNodesJ = 0xF & (Vec_IntEntry(p->vConfigs, FanJ) >> 3);
    int nNodes  = nNodesI + nNodesJ + 1;
    assert( nObjs == Vec_IntSize(p->vTruths) );
    assert( nObjs == Vec_IntSize(p->vConfigs) );
    assert( nObjs == Vec_IntSize(p->vClasses) );
    Vec_WecPush( p->vFunNodes, n, nObjs );
    Vec_IntPushTwo( p->vFanins, FanI, FanJ );
    Vec_IntPush( p->vTruths, Truth );
    Vec_IntPush( p->vConfigs, (nNodes << 3) | Type );
    Vec_IntPush( p->vClasses, Vec_IntSize(p->vTruthNpns) );
    Vec_IntPush( p->vTruthNpns, Min );
    Vec_IntForEachEntry( vFuncs, Min, i )
        Dtt_ManSetFun( p, Min );
    assert( nNodes < 32 );
    p->Counts[nNodes]++;

    if ( p->pTable == NULL )
        return;
    Truth = Truth & p->CmpMask ? ~Truth : Truth;
    Truth &= p->FunMask;
    assert( p->pNodes[p->pTable[Truth]] == 0 );
    p->pNodes[p->pTable[Truth]] = n;
}

int Dtt_PrintStats( int nNodes, int nVars, Vec_Wec_t * vFunNodes, word nSteps, abctime clk, int fDelay, word nMultis )
{
    int nNew = Vec_IntSize(Vec_WecEntry(vFunNodes, nNodes));
    printf("%c =%2d  |  ",     fDelay ? 'D':'N', nNodes );
    printf("C =%12.0f  |  ",   (double)(iword)nSteps );
    printf("New%d =%10d   ",   nVars, nNew + (int)(nNodes==0) );
    printf("All%d =%10d  |  ", nVars, Vec_WecSizeSize(vFunNodes)+1 );
    printf("Multi =%10d  |  ", (int)nMultis );
    Abc_PrintTime( 1, "Time",  Abc_Clock() - clk );
    //Abc_Print(1, "%9.2f sec\n", 1.0*(Abc_Clock() - clk)/(CLOCKS_PER_SEC));
    fflush(stdout);
    return nNew;
}
void Dtt_PrintDistrib( Dtt_Man_t * p )
{
    int i;
    printf( "NPN classes for each node count (N):\n" );
    for ( i = 0; i < 32; i++ )
        if ( p->Counts[i] )
            printf( "N = %2d : NPN = %6d\n", i, p->Counts[i] );
}
void Dtt_PrintMulti2( Dtt_Man_t * p )
{
    int i, n;
    for ( n = 0; n <= 7; n++ )
    {
        printf( "n=%d : ", n);
        for ( i = 0; i < p->nClasses; i++ )
            if ( p->pNodes[i] == n )
                printf( "%d ", p->pTimes[i] );
        printf( "\n" );
    }
}
void Dtt_PrintMulti( Dtt_Man_t * p )
{
    int i, n, Entry, Count, Prev;
    for ( n = 0; n < 16; n++ )
    {
        Vec_Int_t * vTimes = Vec_IntAlloc( 100 );
        Vec_Int_t * vUsed  = Vec_IntAlloc( 100 );
        for ( i = 0; i < p->nClasses; i++ )
            if ( p->pNodes[i] == n )
                Vec_IntPush( vTimes, p->pTimes[i] );
        if ( Vec_IntSize(vTimes) == 0 )
        {
            Vec_IntFree(vTimes);
            Vec_IntFree(vUsed);
            break;
        }
        Vec_IntSort( vTimes, 0 );
        Count = 1;
        Prev = Vec_IntEntry( vTimes, 0 );
        Vec_IntForEachEntryStart( vTimes, Entry, i, 1 )
            if ( Prev == Entry )
                Count++;
            else
            {
                assert( Prev < Entry );
                Vec_IntPushTwo( vUsed, Prev, Count );
                Count = 1;
                Prev = Entry;
            }
        if ( Count > 0 )
            Vec_IntPushTwo( vUsed, Prev, Count );
        printf( "n=%d : ", n);
        Vec_IntForEachEntryDouble( vUsed, Prev, Entry, i )
            printf( "%d=%d ", Prev, Entry );
        printf( "\n" );
        Vec_IntFree( vTimes );
        Vec_IntFree( vUsed );
    }
}
void Dtt_EnumerateLf( int nVars, int nNodeMax, int fDelay, int fMulti, int fVerbose )
{
    abctime clk = Abc_Clock(); word nSteps = 0, nMultis = 0;
    Dtt_Man_t * p = Dtt_ManAlloc( nVars, fMulti ); int n, i, j;
    // constant zero class
    Vec_IntPushTwo( p->vFanins, 0, 0 );
    Vec_IntPush( p->vTruths, 0 );
    Vec_IntPush( p->vConfigs, 0 );
    Vec_IntPush( p->vClasses, Vec_IntSize(p->vTruthNpns) );
    Vec_IntPush( p->vTruthNpns, 0 );
    Dtt_ManSetFun( p, 0 );
    // buffer class
    Vec_WecPush( p->vFunNodes, 0, Vec_IntSize(p->vFanins)/2 );
    Vec_IntPushTwo( p->vFanins, 0, 0 );
    Vec_IntPush( p->vTruths, (unsigned)s_Truths6[0] );
    Vec_IntPush( p->vConfigs, 0 );
    Vec_IntPush( p->vClasses, Vec_IntSize(p->vTruthNpns) );
    Vec_IntPush( p->vTruthNpns, (unsigned)s_Truths6[0] );
    for ( i = 0; i < nVars; i++ )
        Dtt_ManSetFun( p, (unsigned)s_Truths6[i] );
    p->Counts[0] = 2;
    // enumerate
    Dtt_PrintStats(0, nVars, p->vFunNodes, nSteps, clk, fDelay, 0);
    for ( n = 1; n <= nNodeMax; n++ )
    {
        for ( i = 0, j = n - 1; i < n; i++, j = j - 1 + fDelay ) if ( i <= j )
        {
            Vec_Int_t * vFaninI = Vec_WecEntry( p->vFunNodes, i );
            Vec_Int_t * vFaninJ = Vec_WecEntry( p->vFunNodes, j );
            int k, i0, j0, EntryI, EntryJ;
            Vec_IntForEachEntry( vFaninI, EntryI, i0 )
            {
                unsigned TruthI = Vec_IntEntry(p->vTruths, EntryI);
                Vec_Int_t * vFuns = Dtt_ManCollect( p, TruthI, p->vTemp );
                int Start = i == j ? i0 : 0;
                Vec_IntForEachEntryStart( vFaninJ, EntryJ, j0, Start )
                {
                    unsigned Truth, TruthJ = Vec_IntEntry(p->vTruths, EntryJ);
                    Vec_IntForEachEntry( vFuns, Truth, k )
                    {
                        if ( !Dtt_ManGetFun(p,  TruthJ &  Truth) )
                            Dtt_ManAddFunction( p, n, EntryI, EntryJ, 0,  TruthJ &  Truth );
                        if ( !Dtt_ManGetFun(p,  TruthJ & ~Truth) )
                            Dtt_ManAddFunction( p, n, EntryI, EntryJ, 1,  TruthJ & ~Truth );
                        if ( !Dtt_ManGetFun(p, ~TruthJ &  Truth) )
                            Dtt_ManAddFunction( p, n, EntryI, EntryJ, 2, ~TruthJ &  Truth );
                        if ( !Dtt_ManGetFun(p,  TruthJ |  Truth) )
                            Dtt_ManAddFunction( p, n, EntryI, EntryJ, 3,  TruthJ |  Truth );
                        if ( !Dtt_ManGetFun(p,  TruthJ ^  Truth) )
                            Dtt_ManAddFunction( p, n, EntryI, EntryJ, 4,  TruthJ ^  Truth );
                        nSteps += 5;

                        if ( p->pTable ) Dtt_ManAddVisited( p,  TruthJ &  Truth, n );
                        if ( p->pTable ) Dtt_ManAddVisited( p,  TruthJ & ~Truth, n );
                        if ( p->pTable ) Dtt_ManAddVisited( p, ~TruthJ &  Truth, n );
                        if ( p->pTable ) Dtt_ManAddVisited( p,  TruthJ |  Truth, n );
                        if ( p->pTable ) Dtt_ManAddVisited( p,  TruthJ ^  Truth, n );
                    }
                    nMultis++;
                    if ( p->pTable ) Dtt_ManProcessVisited( p );
                }
            }
        }
        if ( Dtt_PrintStats(n, nVars, p->vFunNodes, nSteps, clk, fDelay, nMultis) == 0 )
            break;
    }
    if ( fDelay )
        Dtt_PrintDistrib( p );
    if ( p->pTable ) 
        Dtt_PrintMulti( p );
    Dtt_ManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

