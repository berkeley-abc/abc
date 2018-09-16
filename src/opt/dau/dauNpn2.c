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
    unsigned       BinMask;        // hash mask
    unsigned *     pBins;          // hash bins
    Vec_Int_t *    vUsedBins;      // used bins
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
Dtt_Man_t * Dtt_ManAlloc( int nVars )
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
    p->BinMask    = 0x3FFF;
    p->pBins      = ABC_FALLOC( unsigned, p->BinMask + 1 );
    p->vUsedBins  = Vec_IntAlloc( 4000 );
    return p;
}
void Dtt_ManFree( Dtt_Man_t * p )
{
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
    int i, k, Entry;
    word tCur = ((word)Truth << 32) | (word)Truth;
    Vec_IntClear( vFuns );
    for ( i = 0; i < p->nPerms; i++ )
    {
        for ( k = 0; k < p->nComps; k++ )
        {
            unsigned tTemp = (unsigned)(tCur & 1 ? ~tCur : tCur);
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
    unsigned ttFun = p->nVars == 4 ? 0xFFFF & tFun : tFun;
    return Abc_TtGetBit( p->pPres, ttFun >> 1 );
}
static inline void Dtt_ManSetFun( Dtt_Man_t * p, unsigned tFun )
{
    unsigned ttFun = p->nVars == 4 ? 0xFFFF & tFun : tFun;
    //assert( !Dtt_ManGetFun(p, ttFun) );
    Abc_TtSetBit( p->pPres, ttFun >> 1 );
}
void Dtt_ManAddFunction( Dtt_Man_t * p, int n, int FanI, int FanJ, int Type, unsigned Truth )
{
    Vec_Int_t * vFuncs = Dtt_ManCollect( p, Truth, p->vTemp2 );
    unsigned Min = Vec_IntFindMin( vFuncs ); 
    int i, nObjs = Vec_IntSize(p->vFanins)/2;
    assert( nObjs == Vec_IntSize(p->vTruths) );
    assert( nObjs == Vec_IntSize(p->vConfigs) );
    assert( nObjs == Vec_IntSize(p->vClasses) );
    Vec_WecPush( p->vFunNodes, n, nObjs );
    Vec_IntPushTwo( p->vFanins, FanI, FanJ );
    Vec_IntPush( p->vTruths, Truth );
    Vec_IntPush( p->vConfigs, Type );
    Vec_IntPush( p->vClasses, Vec_IntSize(p->vTruthNpns) );
    Vec_IntPush( p->vTruthNpns, Min );
    Vec_IntForEachEntry( vFuncs, Min, i )
        Dtt_ManSetFun( p, Min );
}
int Dtt_PrintStats( int nNodes, int nVars, Vec_Wec_t * vFunNodes, word nSteps, abctime clk )
{
    int nNew = Vec_IntSize(Vec_WecEntry(vFunNodes, nNodes));
    printf("N =%2d  | ",       nNodes );
    printf("C =%12.0f  |  ",   (double)(iword)nSteps );
    printf("New%d =%10d  ",    nVars, nNew + (int)(nNodes==0) );
    printf("All%d =%10d  |  ", nVars, Vec_WecSizeSize(vFunNodes)+1 );
    Abc_PrintTime( 1, "Time",  Abc_Clock() - clk );
    //Abc_Print(1, "%9.2f sec\n", 1.0*(Abc_Clock() - clk)/(CLOCKS_PER_SEC));
    fflush(stdout);
    return nNew;
}
void Dtt_EnumerateLf( int nVars, int nNodeMax, int fVerbose )
{
    abctime clk = Abc_Clock(); word nSteps = 0;
    Dtt_Man_t * p = Dtt_ManAlloc( nVars ); int n, i, j;
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
    Vec_IntPush( p->vConfigs, -1 );
    Vec_IntPush( p->vClasses, Vec_IntSize(p->vTruthNpns) );
    Vec_IntPush( p->vTruthNpns, (unsigned)s_Truths6[0] );
    for ( i = 0; i < nVars; i++ )
        Dtt_ManSetFun( p, (unsigned)s_Truths6[i] );
    // enumerate
    Dtt_PrintStats(0, nVars, p->vFunNodes, nSteps, clk);
    for ( n = 1; n < nNodeMax; n++ )
    {
        for ( i = 0, j = n - 1; i < n; i++, j-- ) if ( i <= j )
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
                    }
                }
            }
        }
        if ( Dtt_PrintStats(n, nVars, p->vFunNodes, nSteps, clk) == 0 )
            break;
    }
    Dtt_ManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

