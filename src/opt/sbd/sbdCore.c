/**CFile****************************************************************

  FileName    [sbdCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sbdCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sbdInt.h"
#include "opt/dau/dau.h"
#include "misc/tim/tim.h"
#include "map/if/if.h"
#include "opt/sfm/sfm.h"
#include "aig/gia/giaAig.h"
#include "proof/dch/dch.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define SBD_MAX_LUTSIZE 6

typedef struct Sbd_Man_t_ Sbd_Man_t;
struct Sbd_Man_t_
{
    Sbd_Par_t *     pPars;       // user's parameters
    Gia_Man_t *     pGia;        // user's AIG manager (will be modified by adding nodes)
    Vec_Wec_t *     vTfos;       // TFO for each node (roots are marked) (windowing)
    Vec_Int_t *     vLutLevs;    // LUT level for each node after resynthesis
    Vec_Int_t *     vLutCuts;    // LUT cut for each nodes after resynthesis
    Vec_Int_t *     vLutCuts2;   // LUT cut for each nodes after resynthesis
    Vec_Int_t *     vMirrors;    // alternative node
    Vec_Wrd_t *     vSims[4];    // simulation information (main, backup, controlability)
    Vec_Int_t *     vCover;      // temporary
    Vec_Int_t *     vLits;       // temporary
    Vec_Int_t *     vLits2;      // temporary
    Vec_Int_t *     vAcdMap;     // object-to-truth literals for the current cut
    Vec_Int_t *     vAcdNodes;   // objects whose truth literals need clearing
    Vec_Wrd_t *     vAcdTruth;   // truth tables computed by structural simulation
    int             nAcdTried;
    int             nAcdTruths;
    int             nAcdFound;
    int             nAcdUsed;
    int             nQbfCalls;
    int             fAcdFound;
    int             fRevisit;   // use structural synthesis in the extra pass
    int             nLuts[6];    // 0=const, 1=1lut, 2=2lut, 3=3lut
    int             nTried;  
    int             nUsed;  
    abctime         timeWin;
    abctime         timeCut;
    abctime         timeCov;
    abctime         timeCnf;
    abctime         timeSat;
    abctime         timeQbf;
    abctime         timeAcd;
    abctime         timeNew;
    abctime         timeOther;
    abctime         timeTotal;
    Sbd_Sto_t *     pSto;
    Sbd_Srv_t *     pSrv;
    // target node
    int             Pivot;       // target node
    int             DivCutoff;   // the place where D-2 divisors begin
    Vec_Int_t *     vTfo;        // TFO (excludes node, includes roots) - precomputed
    Vec_Int_t *     vRoots;      // TFO root nodes
    Vec_Int_t *     vWinObjs;    // TFI + Pivot + sideTFI + TFO (including roots)
    Vec_Int_t *     vObj2Var;    // SAT variables for the window (indexes of objects in vWinObjs)
    Vec_Int_t *     vDivSet;     // divisor variables
    Vec_Int_t *     vDivVars;    // divisor variables
    Vec_Int_t *     vDivValues;  // SAT variables values for the divisor variables
    Vec_Wec_t *     vDivLevels;  // divisors collected by levels
    Vec_Int_t *     vCounts[2];  // counters of zeros and ones
    Vec_Wrd_t *     vMatrix;     // covering matrix
    sat_solver *    pSat;        // SAT solver
    sat_solver *    pSatCec;     // reusable QBF verification solver
    sat_solver *    pSatQbf;     // reusable QBF parameter solver
};

static inline int *  Sbd_ObjCut( Sbd_Man_t * p, int i )  { return Vec_IntEntryP( p->vLutCuts,  (p->pPars->nLutSize + 1) * i ); }
static inline int *  Sbd_ObjCut2( Sbd_Man_t * p, int i ) { return Vec_IntEntryP( p->vLutCuts2, (p->pPars->nLutSize + 1) * i ); }

static inline word * Sbd_ObjSim0( Sbd_Man_t * p, int i ) { return Vec_WrdEntryP( p->vSims[0], p->pPars->nWords * i );         }
static inline word * Sbd_ObjSim1( Sbd_Man_t * p, int i ) { return Vec_WrdEntryP( p->vSims[1], p->pPars->nWords * i );         }
static inline word * Sbd_ObjSim2( Sbd_Man_t * p, int i ) { return Vec_WrdEntryP( p->vSims[2], p->pPars->nWords * i );         }
static inline word * Sbd_ObjSim3( Sbd_Man_t * p, int i ) { return Vec_WrdEntryP( p->vSims[3], p->pPars->nWords * i );         }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sbd_ParSetDefault( Sbd_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Sbd_Par_t) );
    pPars->nLutSize     = 4;    // target LUT size
    pPars->nLutNum      = 3;    // target LUT count
    pPars->nCutSize     = (pPars->nLutSize - 1) * pPars->nLutNum + 1;  // target cut size
    pPars->nCutNum      = 128;  // target cut count
    pPars->nIters       = 1;    // complete delay optimization rounds
    pPars->nTfoLevels   = -1;   // use the objective's window defaults
    pPars->nTfoFanMax   = -1;
    pPars->nWinSizeMax  = -1;
    pPars->nBTLimit     = -1;
    pPars->nBTLimitDch  = -1;   // use the default choice budget
    pPars->nWords       = 1;    // simulation word count
    pPars->fMapping     = 1;    // generate mapping
    pPars->fMoreCuts    = 0;    // use several cuts
    pPars->fFindDivs    = 0;    // perform divisor search
    pPars->fUsePath     = -1;   // use critical paths when the input mapping fits
    pPars->fArea        = 0;    // area optimization preserves the input LUT depth
    pPars->fDelay       = 0;    // delay optimization is optional
    pPars->fCover       = 0;    // use complete cover procedure
    pPars->fVerbose     = 0;    // verbose flag
    pPars->fVeryVerbose = 0;    // verbose flag
}

/**Function*************************************************************

  Synopsis    [Resolves objective defaults without overriding explicit limits.]

  Description [Area recovery uses SFM's defaults. Delay search keeps its
  own window profile. A zero limit is explicit and remains unchanged.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sbd_ParResolve( Sbd_Par_t * pPars )
{
    Sfm_Par_t AreaPars;
    Sfm_ParSetDefault( &AreaPars );
    if ( pPars->nTfoLevels < 0 )  pPars->nTfoLevels  = pPars->fDelay ? 5 : AreaPars.nTfoLevMax;
    if ( pPars->nTfoFanMax < 0 )  pPars->nTfoFanMax  = pPars->fDelay ? 4 : AreaPars.nFanoutMax;
    if ( pPars->nWinSizeMax < 0 ) pPars->nWinSizeMax = pPars->fDelay ? 2000 : AreaPars.nWinSizeMax;
    if ( pPars->nBTLimit < 0 )    pPars->nBTLimit    = pPars->fDelay ? 0 : AreaPars.nBTLimit;
    if ( pPars->nBTLimitDch < 0 ) pPars->nBTLimitDch = 100;
}

/**Function*************************************************************

  Synopsis    [Computes TFO and window roots for all nodes.]

  Description [TFO does not include the node itself. If TFO is empty,
  it means that the node itself is its own root, which may happen if
  the node is pointed by a PO or if it has too many fanouts.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Sbd_ManWindowRoots( Gia_Man_t * p, int nTfoLevels, int nTfoFanMax )
{
    Vec_Wec_t * vTfos = Vec_WecStart( Gia_ManObjNum(p) ); // TFO nodes with roots marked
    Vec_Wec_t * vTemp = Vec_WecStart( Gia_ManObjNum(p) ); // storage
    Vec_Int_t * vNodes, * vNodes0, * vNodes1;
    Vec_Bit_t * vPoDrivers = Vec_BitStart( Gia_ManObjNum(p) );
    int i, k, k2, Id, Fan;
    Gia_ManLevelNum( p );
    Gia_ManCreateRefs( p );
    Gia_ManCleanMark0( p );
    Gia_ManForEachCiId( p, Id, i )
    {
        vNodes = Vec_WecEntry( vTemp, Id );
        Vec_IntGrow( vNodes, 1 );
        Vec_IntPush( vNodes, Id );
    }
    Gia_ManForEachCoDriverId( p, Id, i )
        Vec_BitWriteEntry( vPoDrivers, Id, 1 );
    Gia_ManForEachAndId( p, Id )
    {
        int fAlwaysRoot = Vec_BitEntry(vPoDrivers, Id) || (Gia_ObjRefNumId(p, Id) >= nTfoFanMax);
        vNodes0 = Vec_WecEntry( vTemp, Gia_ObjFaninId0(Gia_ManObj(p, Id), Id) );
        vNodes1 = Vec_WecEntry( vTemp, Gia_ObjFaninId1(Gia_ManObj(p, Id), Id) );
        vNodes = Vec_WecEntry( vTemp, Id );
        Vec_IntTwoMerge2( vNodes0, vNodes1, vNodes );
        k2 = 0;
        Vec_IntForEachEntry( vNodes, Fan, k )
        {
            int fRoot = fAlwaysRoot || (Gia_ObjLevelId(p, Id) - Gia_ObjLevelId(p, Fan) >= nTfoLevels);
            Vec_WecPush( vTfos, Fan, Abc_Var2Lit(Id, fRoot) );
            if ( !fRoot ) Vec_IntWriteEntry( vNodes, k2++, Fan );
        }
        Vec_IntShrink( vNodes, k2 );
        if ( !fAlwaysRoot )
            Vec_IntPush( vNodes, Id );
    }
    Vec_WecFree( vTemp );
    Vec_BitFree( vPoDrivers );

    // print the results
    if ( 0 )
    Vec_WecForEachLevel( vTfos, vNodes, i )
    {
        if ( !Gia_ObjIsAnd(Gia_ManObj(p, i)) )
            continue;
        printf( "Node %3d : ", i );
        Vec_IntForEachEntry( vNodes, Fan, k )
            printf( "%d%s ", Abc_Lit2Var(Fan), Abc_LitIsCompl(Fan)? "*":"" );
        printf( "\n" );
    }

    return vTfos;
}

/**Function*************************************************************

  Synopsis    [Manager manipulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sbd_Man_t * Sbd_ManStart( Gia_Man_t * pGia, Sbd_Par_t * pPars )
{
    int i, w, Id;
    Sbd_Man_t * p = ABC_CALLOC( Sbd_Man_t, 1 );  
    p->timeTotal  = Abc_Clock();
    p->pPars      = pPars;
    p->pGia       = pGia;
    p->vTfos      = Sbd_ManWindowRoots( pGia, pPars->nTfoLevels, pPars->nTfoFanMax );
    p->vLutLevs   = Vec_IntStart( Gia_ManObjNum(pGia) );
    p->vLutCuts   = Vec_IntStart( Gia_ManObjNum(pGia) * (p->pPars->nLutSize + 1) );
    p->vMirrors   = Vec_IntStartFull( Gia_ManObjNum(pGia) );
    for ( i = 0; i < 4; i++ )
        p->vSims[i] = Vec_WrdStart( Gia_ManObjNum(pGia) * p->pPars->nWords );
    // target node
    p->vCover     = Vec_IntAlloc( 100 );
    p->vLits      = Vec_IntAlloc( 100 );
    p->vLits2     = Vec_IntAlloc( 100 );
    p->vAcdMap    = Vec_IntStartFull( Gia_ManObjNum(pGia) );
    p->vAcdNodes  = Vec_IntAlloc( 100 );
    p->vAcdTruth  = Vec_WrdAlloc( 1000 );
    p->vRoots     = Vec_IntAlloc( 100 );
    p->vWinObjs   = Vec_IntAlloc( Gia_ManObjNum(pGia) );
    p->vObj2Var   = Vec_IntStart( Gia_ManObjNum(pGia) );
    p->vDivSet    = Vec_IntAlloc( 100 );
    p->vDivVars   = Vec_IntAlloc( 100 );
    p->vDivValues = Vec_IntAlloc( 100 );
    p->vDivLevels = Vec_WecAlloc( 100 );
    p->vCounts[0] = Vec_IntAlloc( 100 );
    p->vCounts[1] = Vec_IntAlloc( 100 );
    p->vMatrix    = Vec_WrdAlloc( 100 );
    // start input cuts
    Gia_ManForEachCiId( pGia, Id, i )
    {
        int * pCut = Sbd_ObjCut( p, Id );
        pCut[0] = 1;
        pCut[1] = Id;
    }
    // generate random input
    Gia_ManRandom( 1 );
    Gia_ManForEachCiId( pGia, Id, i )
        for ( w = 0; w < p->pPars->nWords; w++ )
            Sbd_ObjSim0(p, Id)[w] = Gia_ManRandomW( 0 );     
    // cut enumeration
    if ( pPars->fMoreCuts )
        p->pSto = Sbd_StoAlloc( pGia, p->vMirrors, pPars->nLutSize, pPars->nCutSize, pPars->nCutNum, !pPars->fMapping, 1 );
    else
    {
        p->pSto = Sbd_StoAlloc( pGia, p->vMirrors, pPars->nLutSize, pPars->nLutSize, pPars->nCutNum, !pPars->fMapping, 1 );
        p->pSrv = Sbd_ManCutServerStart( pGia, p->vMirrors, p->vLutLevs, NULL, NULL, pPars->nLutSize, pPars->nCutSize, pPars->nCutNum, 0 );
    }
    return p;
}
void Sbd_ManStop( Sbd_Man_t * p )
{
    int i;
    Vec_WecFree( p->vTfos );
    Vec_IntFree( p->vLutLevs );
    Vec_IntFree( p->vLutCuts );
    Vec_IntFree( p->vMirrors );
    for ( i = 0; i < 4; i++ )
        Vec_WrdFree( p->vSims[i] );
    Vec_IntFree( p->vCover );
    Vec_IntFree( p->vLits );
    Vec_IntFree( p->vLits2 );
    Vec_IntFree( p->vAcdMap );
    Vec_IntFree( p->vAcdNodes );
    Vec_WrdFree( p->vAcdTruth );
    Vec_IntFree( p->vRoots );
    Vec_IntFree( p->vWinObjs );
    Vec_IntFree( p->vObj2Var );
    Vec_IntFree( p->vDivSet );
    Vec_IntFree( p->vDivVars );
    Vec_IntFree( p->vDivValues );
    Vec_WecFree( p->vDivLevels );
    Vec_IntFree( p->vCounts[0] );
    Vec_IntFree( p->vCounts[1] );
    Vec_WrdFree( p->vMatrix );
    sat_solver_delete_p( &p->pSat );
    sat_solver_delete_p( &p->pSatCec );
    sat_solver_delete_p( &p->pSatQbf );
    if ( p->pSto ) Sbd_StoFree( p->pSto );
    if ( p->pSrv ) Sbd_ManCutServerStop( p->pSrv );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Constructing window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sbd_ManPropagateControlOne( Sbd_Man_t * p, int Node )
{
    Gia_Obj_t * pNode = Gia_ManObj(p->pGia, Node);  int w;
    int iObj0 = Gia_ObjFaninId0(pNode, Node);
    int iObj1 = Gia_ObjFaninId1(pNode, Node);

//    word * pSims  = Sbd_ObjSim0(p, Node);
//    word * pSims0 = Sbd_ObjSim0(p, iObj0);
//    word * pSims1 = Sbd_ObjSim0(p, iObj1);

    word * pCtrl  = Sbd_ObjSim2(p, Node);
    word * pCtrl0 = Sbd_ObjSim2(p, iObj0);
    word * pCtrl1 = Sbd_ObjSim2(p, iObj1);

    word * pDtrl  = Sbd_ObjSim3(p, Node);
    word * pDtrl0 = Sbd_ObjSim3(p, iObj0);
    word * pDtrl1 = Sbd_ObjSim3(p, iObj1);

//    Gia_ObjPrint( p->pGia, pNode );
//    printf( "Node %2d : %d %d\n\n", Node, (int)(pSims[0] & 1), (int)(pCtrl[0] & 1) );

    for ( w = 0; w < p->pPars->nWords; w++ )
    {
//        word Sim0 = Gia_ObjFaninC0(pNode) ? ~pSims0[w] : pSims0[w];
//        word Sim1 = Gia_ObjFaninC1(pNode) ? ~pSims1[w] : pSims1[w];

        pCtrl0[w] |= pCtrl[w];// & (pSims[w] | Sim1 | (~Sim0 & ~Sim1));
        pCtrl1[w] |= pCtrl[w];// & (pSims[w] | Sim0 | (~Sim0 & ~Sim1));

        pDtrl0[w] |= pDtrl[w];// & (pSims[w] | Sim1 | (~Sim0 & ~Sim1));
        pDtrl1[w] |= pDtrl[w];// & (pSims[w] | Sim0 | (~Sim0 & ~Sim1));
    }
}
void Sbd_ManPropagateControl( Sbd_Man_t * p, int Pivot )
{
    abctime clk = Abc_Clock();
    int i, Node;
    Abc_TtCopy( Sbd_ObjSim3(p, Pivot), Sbd_ObjSim2(p, Pivot), p->pPars->nWords, 0 );
    // clean controlability
    for ( i = 0; i < Vec_IntEntry(p->vObj2Var, Pivot) && ((Node = Vec_IntEntry(p->vWinObjs, i)), 1); i++ )
    {
        Abc_TtClear( Sbd_ObjSim2(p, Node), p->pPars->nWords );
        Abc_TtClear( Sbd_ObjSim3(p, Node), p->pPars->nWords );
        //printf( "Clearing node %d.\n", Node );
    }
    // propagate controlability to fanins for the TFI nodes starting from the pivot
    for ( i = Vec_IntEntry(p->vObj2Var, Pivot); i >= 0 && ((Node = Vec_IntEntry(p->vWinObjs, i)), 1); i-- )
        if ( Gia_ObjIsAnd(Gia_ManObj(p->pGia, Node)) )
            Sbd_ManPropagateControlOne( p, Node );
    p->timeWin += Abc_Clock() - clk;
}
void Sbd_ManUpdateOrder( Sbd_Man_t * p, int Pivot )
{
    int i, k, Node;
    Vec_Int_t * vLevel;
    int nTimeValidDivs = 0;
    // collect divisors by logic level
    int LevelMax = Vec_IntEntry(p->vLutLevs, Pivot);
    Vec_WecClear( p->vDivLevels );
    Vec_WecInit( p->vDivLevels, LevelMax + 1 );
    Vec_IntForEachEntry( p->vWinObjs, Node, i )
        Vec_WecPush( p->vDivLevels, Vec_IntEntry(p->vLutLevs, Node), Node );
    // reload divisors
    Vec_IntClear( p->vWinObjs );
    Vec_WecForEachLevel( p->vDivLevels, vLevel, i )
    {
        if ( Vec_IntSize(vLevel) > 1 )
            Vec_IntSort( vLevel, 0 );
        Vec_IntForEachEntry( vLevel, Node, k )
        {
            Vec_IntWriteEntry( p->vObj2Var, Node, Vec_IntSize(p->vWinObjs) );
            Vec_IntPush( p->vWinObjs, Node );
        }
        // remember divisor cutoff
        if ( i == LevelMax - 2 )
            nTimeValidDivs = Vec_IntSize(p->vWinObjs);
    }
    assert( nTimeValidDivs > 0 );
    Vec_IntClear( p->vDivVars );
    p->DivCutoff = -1;
    Vec_IntForEachEntryStartStop( p->vWinObjs, Node, i, Abc_MaxInt(0, nTimeValidDivs-63), nTimeValidDivs )
    {
        if ( p->DivCutoff == -1 && Vec_IntEntry(p->vLutLevs, Node) == LevelMax - 2 )
            p->DivCutoff = Vec_IntSize(p->vDivVars);
        Vec_IntPush( p->vDivVars, i );
    }
    if ( p->DivCutoff == -1 )
        p->DivCutoff = 0;
    // verify
//
//     assert( Vec_IntSize(p->vDivVars) < 64 );
//     Vec_IntForEachEntryStart( p->vDivVars, Node, i, p->DivCutoff )
//         assert( Vec_IntEntry(p->vLutLevs, Vec_IntEntry(p->vWinObjs, Node)) == LevelMax - 2 );
//     Vec_IntForEachEntryStop( p->vDivVars, Node, i, p->DivCutoff )
//         assert( Vec_IntEntry(p->vLutLevs, Vec_IntEntry(p->vWinObjs, Node)) < LevelMax - 2 );
//
    Vec_IntFill( p->vDivValues, Vec_IntSize(p->vDivVars), 0 );
    //printf( "%d ", Vec_IntSize(p->vDivVars) );
//    printf( "Node %4d :  Win = %5d.   Divs = %5d.    D1 = %5d.  D2 = %5d.\n",
//        Pivot, Vec_IntSize(p->vWinObjs), Vec_IntSize(p->vDivVars), Vec_IntSize(p->vDivVars)-p->DivCutoff, p->DivCutoff );
}
void Sbd_ManWindowSim_rec( Sbd_Man_t * p, int NodeInit )
{
    Gia_Obj_t * pObj;
    int Node = NodeInit;
    if ( Vec_IntEntry(p->vMirrors, Node) >= 0 )
        Node = Abc_Lit2Var( Vec_IntEntry(p->vMirrors, Node) );
    if ( Gia_ObjIsTravIdCurrentId(p->pGia, Node) )
        return;
    Gia_ObjSetTravIdCurrentId(p->pGia, Node);
    pObj = Gia_ManObj( p->pGia, Node );
    if ( Gia_ObjIsAnd(pObj) )
    {
        Sbd_ManWindowSim_rec( p, Gia_ObjFaninId0(pObj, Node) );
        Sbd_ManWindowSim_rec( p, Gia_ObjFaninId1(pObj, Node) );
    }
    if ( !pObj->fMark0 )
    {
        Vec_IntWriteEntry( p->vObj2Var, Node, Vec_IntSize(p->vWinObjs) );
        Vec_IntPush( p->vWinObjs, Node );
    }
    if ( Gia_ObjIsCi(pObj) )
        return;
    // simulate
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjIsXor(pObj) )
    {
        Abc_TtXor( Sbd_ObjSim0(p, Node), 
            Sbd_ObjSim0(p, Gia_ObjFaninId0(pObj, Node)), 
            Sbd_ObjSim0(p, Gia_ObjFaninId1(pObj, Node)), 
            p->pPars->nWords, 
            Gia_ObjFaninC0(pObj) ^ Gia_ObjFaninC1(pObj) );

        if ( pObj->fMark0 )
            Abc_TtXor( Sbd_ObjSim1(p, Node), 
                Gia_ObjFanin0(pObj)->fMark0 ? Sbd_ObjSim1(p, Gia_ObjFaninId0(pObj, Node)) : Sbd_ObjSim0(p, Gia_ObjFaninId0(pObj, Node)), 
                Gia_ObjFanin1(pObj)->fMark0 ? Sbd_ObjSim1(p, Gia_ObjFaninId1(pObj, Node)) : Sbd_ObjSim0(p, Gia_ObjFaninId1(pObj, Node)), 
                p->pPars->nWords, 
                Gia_ObjFaninC0(pObj) ^ Gia_ObjFaninC1(pObj) );
    }
    else
    {
        Abc_TtAndCompl( Sbd_ObjSim0(p, Node), 
            Sbd_ObjSim0(p, Gia_ObjFaninId0(pObj, Node)), Gia_ObjFaninC0(pObj), 
            Sbd_ObjSim0(p, Gia_ObjFaninId1(pObj, Node)), Gia_ObjFaninC1(pObj), 
            p->pPars->nWords );

        if ( pObj->fMark0 )
            Abc_TtAndCompl( Sbd_ObjSim1(p, Node), 
                Gia_ObjFanin0(pObj)->fMark0 ? Sbd_ObjSim1(p, Gia_ObjFaninId0(pObj, Node)) : Sbd_ObjSim0(p, Gia_ObjFaninId0(pObj, Node)), Gia_ObjFaninC0(pObj), 
                Gia_ObjFanin1(pObj)->fMark0 ? Sbd_ObjSim1(p, Gia_ObjFaninId1(pObj, Node)) : Sbd_ObjSim0(p, Gia_ObjFaninId1(pObj, Node)), Gia_ObjFaninC1(pObj), 
                p->pPars->nWords );
    }
    if ( Node != NodeInit )
        Abc_TtCopy( Sbd_ObjSim0(p, NodeInit), Sbd_ObjSim0(p, Node), p->pPars->nWords, Abc_LitIsCompl(Vec_IntEntry(p->vMirrors, NodeInit)) );
}
int Sbd_ManWindow( Sbd_Man_t * p, int Pivot )
{
    abctime clk = Abc_Clock();
    int i, Node;
    // assign pivot and TFO (assume siminfo is assigned at the PIs)
    p->Pivot = Pivot;
    p->vTfo = Vec_WecEntry( p->vTfos, Pivot );
    // add constant node
    Vec_IntClear( p->vWinObjs );
    Vec_IntWriteEntry( p->vObj2Var, 0, Vec_IntSize(p->vWinObjs) );
    Vec_IntPush( p->vWinObjs, 0 );
    // simulate TFI cone
    Gia_ManIncrementTravId( p->pGia );
    Gia_ObjSetTravIdCurrentId(p->pGia, 0);
    Sbd_ManWindowSim_rec( p, Pivot );
    if ( p->pPars->nWinSizeMax && Vec_IntSize(p->vWinObjs) > p->pPars->nWinSizeMax )
    {
        p->timeWin += Abc_Clock() - clk;
        return 0;
    }
    Sbd_ManUpdateOrder( p, Pivot );
    assert( Vec_IntSize(p->vDivVars) == Vec_IntSize(p->vDivValues) );
    assert( Vec_IntSize(p->vDivVars) < Vec_IntSize(p->vWinObjs) );
    // simulate node
    Gia_ManObj(p->pGia, Pivot)->fMark0 = 1;
    Abc_TtCopy( Sbd_ObjSim1(p, Pivot), Sbd_ObjSim0(p, Pivot), p->pPars->nWords, 1 );
    // mark TFO and simulate extended TFI without adding TFO nodes
    Vec_IntClear( p->vRoots );
    Vec_IntForEachEntry( p->vTfo, Node, i )
    {
        Gia_ManObj(p->pGia, Abc_Lit2Var(Node))->fMark0 = 1;
        if ( !Abc_LitIsCompl(Node) ) 
            continue;
        Sbd_ManWindowSim_rec( p, Abc_Lit2Var(Node) );
        Vec_IntPush( p->vRoots, Abc_Lit2Var(Node) );
    }
    // add TFO nodes and remove marks
    Gia_ManObj(p->pGia, Pivot)->fMark0 = 0;
    Vec_IntForEachEntry( p->vTfo, Node, i )
    {
        Gia_ManObj(p->pGia, Abc_Lit2Var(Node))->fMark0 = 0;
        Vec_IntWriteEntry( p->vObj2Var, Abc_Lit2Var(Node), Vec_IntSize(p->vWinObjs) );
        Vec_IntPush( p->vWinObjs, Abc_Lit2Var(Node) );
    }
    if ( p->pPars->nWinSizeMax && Vec_IntSize(p->vWinObjs) > p->pPars->nWinSizeMax )
    {
        p->timeWin += Abc_Clock() - clk;
        return 0;
    }
    // compute controlability for node
    if ( Vec_IntSize(p->vTfo) == 0 )
        Abc_TtFill( Sbd_ObjSim2(p, Pivot), p->pPars->nWords );
    else
        Abc_TtClear( Sbd_ObjSim2(p, Pivot), p->pPars->nWords );
    Vec_IntForEachEntry( p->vTfo, Node, i )
        if ( Abc_LitIsCompl(Node) ) // root
            Abc_TtOrXor( Sbd_ObjSim2(p, Pivot), Sbd_ObjSim0(p, Abc_Lit2Var(Node)), Sbd_ObjSim1(p, Abc_Lit2Var(Node)), p->pPars->nWords );
    p->timeWin += Abc_Clock() - clk;
    // propagate controlability to fanins for the TFI nodes starting from the pivot
    Sbd_ManPropagateControl( p, Pivot );
    assert( Vec_IntSize(p->vDivValues) <= 64 );
    return (int)(Vec_IntSize(p->vDivValues) <= 64);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sbd_ManCheckConst( Sbd_Man_t * p, int Pivot )
{
    int nMintCount = 1;
    Vec_Ptr_t * vSims;
    word * pSims = Sbd_ObjSim0( p, Pivot );
    word * pCtrl = Sbd_ObjSim2( p, Pivot );
    int PivotVar = Vec_IntEntry(p->vObj2Var, Pivot);
    int RetValue, i, iObj, Ind, fFindOnset, nCares[2] = {0};

    abctime clk;
    //return -1;
    //Sbd_ManPrintObj( p, Pivot );

    // count the number of on-set and off-set care-set minterms
    Vec_IntClear( p->vLits );
    for ( i = 0; i < 64; i++ )
        if ( Abc_TtGetBit(pCtrl, i) )
            nCares[Abc_TtGetBit(pSims, i)]++;
        else
            Vec_IntPush( p->vLits, i );
    fFindOnset = (int)(nCares[0] < nCares[1]);
    if ( nCares[0] >= nMintCount && nCares[1] >= nMintCount )
        return -1;
    // Build the solver only when simulation has not proved nonconstancy.
    clk = Abc_Clock();
    p->pSat = Sbd_ManSatSolver( p->pSat, p->pGia, p->vMirrors, Pivot, p->vWinObjs, p->vObj2Var, p->vTfo, p->vRoots, 0 );
    p->timeCnf += Abc_Clock() - clk;
    if ( p->pSat == NULL )
    {
        //if ( p->pPars->fVerbose )
        //    printf( "Found stuck-at-%d node %d.\n", 0, Pivot );
        Vec_IntWriteEntry( p->vLutLevs, Pivot, 0 );
        p->nLuts[0]++;
        return 0;
    }
    // find how many do we need
    nCares[0] = nCares[0] < nMintCount ? nMintCount - nCares[0] : 0;
    nCares[1] = nCares[1] < nMintCount ? nMintCount - nCares[1] : 0;

    if ( p->pPars->fVeryVerbose )
        printf( "Computing %d offset and %d onset minterms for node %d.\n", nCares[0], nCares[1], Pivot );

    if ( Vec_IntSize(p->vLits) >= nCares[0] + nCares[1] )
        Vec_IntShrink( p->vLits, nCares[0] + nCares[1] );
    else
    {
        // collect places to insert new minterms
        for ( i = 0; i < 64 && Vec_IntSize(p->vLits) < nCares[0] + nCares[1]; i++ )
            if ( fFindOnset == Abc_TtGetBit(pSims, i) )
                Vec_IntPush( p->vLits, i );
    }
    // collect simulation pointers
    vSims = Vec_PtrAlloc( PivotVar + 1 );
    Vec_IntForEachEntry( p->vWinObjs, iObj, i )
    {
        Vec_PtrPush( vSims, Sbd_ObjSim0(p, iObj) );
        if ( iObj == Pivot )
            break;
    }
    assert( i == PivotVar );
    // compute patterns
    RetValue = Sbd_ManCollectConstants( p->pSat, nCares, PivotVar, (word **)Vec_PtrArray(vSims), p->vLits, p->pPars->nBTLimit );
    // print computed miterms
    if ( 0 && RetValue < 0 )
    {
        Vec_Int_t * vPis = Vec_WecEntry(p->vDivLevels, 0);
        int i, k, Ind;
        printf( "Additional minterms:\n" );
        Vec_IntForEachEntry( p->vLits, Ind, k )
        {
            for ( i = 0; i < Vec_IntSize(vPis); i++ )
                printf( "%d", Abc_TtGetBit( (word *)Vec_PtrEntry(vSims, Vec_IntEntry(p->vWinObjs, i)), Ind ) );
            printf( "\n" );
        }
    }
    Vec_PtrFree( vSims );
    if ( RetValue == -2 )
        return RetValue;
    if ( RetValue >= 0 )
    {
        if ( p->pPars->fVeryVerbose )
            printf( "Found stuck-at-%d node %d.\n", RetValue, Pivot );
        Vec_IntWriteEntry( p->vLutLevs, Pivot, 0 );
        p->nLuts[0]++;
        return RetValue;
    }
    // set controlability of these minterms
    Vec_IntForEachEntry( p->vLits, Ind, i )
        Abc_TtSetBit( pCtrl, Ind );
    // propagate controlability to fanins for the TFI nodes starting from the pivot
    Sbd_ManPropagateControl( p, Pivot );
    // double check that we now have enough minterms
    for ( i = 0; i < 64; i++ )
        if ( Abc_TtGetBit(pCtrl, i) )
            nCares[Abc_TtGetBit(pSims, i)]++;
    assert( nCares[0] >= nMintCount && nCares[1] >= nMintCount );
    return -1;
}

/**Function*************************************************************

  Synopsis    [Transposing 64-bit matrix.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Sbd_TransposeMatrix64( word A[64] )
{
    int j, k;
    word t, m = 0x00000000FFFFFFFF;
    for ( j = 32; j != 0; j = j >> 1, m = m ^ (m << j) )
    {
        for ( k = 0; k < 64; k = (k + j + 1) & ~j )
        {
            t = (A[k] ^ (A[k+j] >> j)) & m;
            A[k] = A[k] ^ t;
            A[k+j] = A[k+j] ^ (t << j);
        }
    }
}
static inline void Sbd_PrintMatrix64( word A[64] )
{
    int j, k;
    for ( j = 0; j < 64; j++, printf("\n") )
    for ( k = 0; k < 64; k++ )
        printf( "%d", (int)((A[j] >> k) & 1) );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Profiling divisor candidates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sbd_ManPrintObj( Sbd_Man_t * p, int Pivot )
{
    int nDivs = Vec_IntEntry(p->vObj2Var, Pivot) + 1;
    int i, k, k0, k1, Id, Bit0, Bit1;

    Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
        printf( "%3d : ", Id ), Extra_PrintBinary( stdout, (unsigned *)Sbd_ObjSim0(p, Id), 64 ), printf( "\n" );

    assert( p->Pivot == Pivot );
    Vec_IntClear( p->vCounts[0] );
    Vec_IntClear( p->vCounts[1] );

    printf( "Node %d.  Useful divisors = %d.\n", Pivot, Vec_IntSize(p->vDivValues) );
    printf( "Lev : " );
    Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
    {
        if ( i == nDivs-1 )
            printf( " " );
        printf( "%d", Vec_IntEntry(p->vLutLevs, Id) );
    }
    printf( "\n" );
    printf( "\n" );

    if ( nDivs > 99 )
    {
        printf( "    : " );
        Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
        {
            if ( i == nDivs-1 )
                printf( " " );
            printf( "%d", Id / 100 );
        }
        printf( "\n" );
    }
    if ( nDivs > 9 )
    {
        printf( "    : " );
        Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
        {
            if ( i == nDivs-1 )
                printf( " " );
            printf( "%d", (Id % 100) / 10 );
        }
        printf( "\n" );
    }
    if ( nDivs > 0 )
    {
        printf( "    : " );
        Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
        {
            if ( i == nDivs-1 )
                printf( " " );
            printf( "%d", Id % 10 );
        }
        printf( "\n" );
        printf( "\n" );
    }

    // sampling matrix
    for ( k = 0; k < p->pPars->nWords * 64; k++ )
    {
        if ( !Abc_TtGetBit(Sbd_ObjSim2(p, Pivot), k) )
            continue;

        printf( "%3d : ", k );
        Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
        {
            word * pSims = Sbd_ObjSim0( p, Id );
            word * pCtrl = Sbd_ObjSim2( p, Id );
            if ( i == nDivs-1 )
            {
                if ( Abc_TtGetBit(pCtrl, k) )
                    Vec_IntPush( p->vCounts[Abc_TtGetBit(pSims, k)], k );
                printf( " " );
            }
            printf( "%c", Abc_TtGetBit(pCtrl, k) ? '0' + Abc_TtGetBit(pSims, k) : '.' );
        }
        printf( "\n" );

        printf( "%3d : ", k );
        Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
        {
            word * pSims = Sbd_ObjSim0( p, Id );
            word * pCtrl = Sbd_ObjSim3( p, Id );
            if ( i == nDivs-1 )
            {
                if ( Abc_TtGetBit(pCtrl, k) )
                    Vec_IntPush( p->vCounts[Abc_TtGetBit(pSims, k)], k );
                printf( " " );
            }
            printf( "%c", Abc_TtGetBit(pCtrl, k) ? '0' + Abc_TtGetBit(pSims, k) : '.' );
        }
        printf( "\n" );

        printf( "Sims: " );
        Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
        {
            word * pSims = Sbd_ObjSim0( p, Id );
            //word * pCtrl = Sbd_ObjSim2( p, Id );
            if ( i == nDivs-1 )
                printf( " " );
            printf( "%c", '0' + Abc_TtGetBit(pSims, k) );
        }
        printf( "\n" );

        printf( "Ctrl: " );
        Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
        {
            //word * pSims = Sbd_ObjSim0( p, Id );
            word * pCtrl = Sbd_ObjSim2( p, Id );
            if ( i == nDivs-1 )
                printf( " " );
            printf( "%c", '0' + Abc_TtGetBit(pCtrl, k) );
        }
        printf( "\n" );


        printf( "\n" );
    }
    // covering table
    printf( "Exploring %d x %d covering table.\n", Vec_IntSize(p->vCounts[0]), Vec_IntSize(p->vCounts[1]) );
//
//     Vec_IntForEachEntryStop( p->vCounts[0], Bit0, k0, Abc_MinInt(Vec_IntSize(p->vCounts[0]), 8) )
//     Vec_IntForEachEntryStop( p->vCounts[1], Bit1, k1, Abc_MinInt(Vec_IntSize(p->vCounts[1]), 8) )
//     {
//         printf( "%3d %3d : ", Bit0, Bit1 );
//         Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
//         {
//             word * pSims = Sbd_ObjSim0( p, Id );
//             word * pCtrl = Sbd_ObjSim2( p, Id );
//             if ( i == nDivs-1 )
//                 printf( " " );
//             printf( "%c", (Abc_TtGetBit(pCtrl, Bit0) && Abc_TtGetBit(pCtrl, Bit1) && Abc_TtGetBit(pSims, Bit0) != Abc_TtGetBit(pSims, Bit1)) ? '1' : '.' );
//         }
//         printf( "\n" );
//     }
//
    Vec_WrdClear( p->vMatrix );
    Vec_IntForEachEntryStop( p->vCounts[0], Bit0, k0, Abc_MinInt(Vec_IntSize(p->vCounts[0]), 64) )
    Vec_IntForEachEntryStop( p->vCounts[1], Bit1, k1, Abc_MinInt(Vec_IntSize(p->vCounts[1]), 64) )
    {
        word Row = 0;
        Vec_IntForEachEntryStop( p->vWinObjs, Id, i, nDivs )
        {
            word * pSims = Sbd_ObjSim0( p, Id );
            word * pCtrl = Sbd_ObjSim2( p, Id );
            if ( Abc_TtGetBit(pCtrl, Bit0) && Abc_TtGetBit(pCtrl, Bit1) && Abc_TtGetBit(pSims, Bit0) != Abc_TtGetBit(pSims, Bit1) )
                Abc_TtXorBit( &Row, i );
        }
        if ( Vec_WrdPushUnique( p->vMatrix, Row ) )
            continue;
        for ( i = 0; i < nDivs; i++ )
            printf( "%d", (int)((Row >> i) & 1) );
        printf( "\n" );
    }
}

void Sbd_ManMatrPrint( Sbd_Man_t * p, word Cover[], int nCol, int nRows )
{
    int i, k;
    for ( i = 0; i <= nCol; i++ )
    {
        printf( "%2d : ", i );
        printf( "%d ", i == nCol ? Vec_IntEntry(p->vLutLevs, p->Pivot) : Vec_IntEntry(p->vLutLevs, Vec_IntEntry(p->vWinObjs, Vec_IntEntry(p->vDivVars, i))) );
        for ( k = 0; k < nRows; k++ )
            printf( "%d", (int)((Cover[i] >> k) & 1) );
        printf( "\n"); 
    }
    printf( "\n");
}
static inline void Sbd_ManCoverReverseOrder( word Cover[64] )
{
    int i;
    for ( i = 0; i < 32; i++ )
    {
        word Cube = Cover[i];
        Cover[i] = Cover[63-i]; 
        Cover[63-i] = Cube;
    }
}

static inline int Sbd_ManAddCube1( int nRowLimit, word Cover[], int nRows, word Cube )
{
    int n, m;
    if ( 0 )
    {
        printf( "Adding cube: " );
        for ( n = 0; n < nRowLimit; n++ )
            printf( "%d", (int)((Cube >> n) & 1) );
        printf( "\n" );
    }
    // do not add contained Cube
    assert( nRows <= nRowLimit );
    for ( n = 0; n < nRows; n++ )
        if ( (Cover[n] & Cube) == Cover[n] ) // Cube is contained
            return nRows;
    // remove rows contained by Cube
    for ( n = m = 0; n < nRows; n++ )
        if ( (Cover[n] & Cube) != Cube ) // Cover[n] is not contained
            Cover[m++] = Cover[n];
    if ( m < nRowLimit )
        Cover[m++] = Cube;
    for ( n = m; n < nRows; n++ )
        Cover[n] = 0;
    nRows = m;
    return nRows;
}
static inline int Sbd_ManAddCube2( word Cover[2][64], int nRows, word Cube[2] )
{
    int n, m;
    // do not add contained Cube
    assert( nRows <= 64 );
    for ( n = 0; n < nRows; n++ )
        if ( (Cover[0][n] & Cube[0]) == Cover[0][n] && (Cover[1][n] & Cube[1]) == Cover[1][n] ) // Cube is contained
            return nRows;
    // remove rows contained by Cube
    for ( n = m = 0; n < nRows; n++ )
        if ( (Cover[0][n] & Cube[0]) != Cube[0] || (Cover[1][n] & Cube[1]) != Cube[1] ) // Cover[n] is not contained
        {
            Cover[0][m] = Cover[0][n];
            Cover[1][m] = Cover[1][n];
            m++;
        }
    if ( m < 64 )
    {
        Cover[0][m] = Cube[0];
        Cover[1][m] = Cube[1];
        m++;
    }
    for ( n = m; n < nRows; n++ )
        Cover[0][n] = Cover[1][n] = 0;
    nRows = m;
    return nRows;
}

static inline int Sbd_ManFindCandsSimple( Sbd_Man_t * p, word Cover[], int nDivs )
{
    int c0, c1, c2, c3;
    word Target = Cover[nDivs];
    Vec_IntClear( p->vDivSet );
    for ( c0 = 0;    c0 < nDivs; c0++ )
        if ( Cover[c0] == Target )
        {
            Vec_IntPush( p->vDivSet, c0 );
            return 1;
        }

    for ( c0 = 0;    c0 < nDivs; c0++ )
    for ( c1 = c0+1; c1 < nDivs; c1++ )
        if ( (Cover[c0] | Cover[c1]) == Target )
        {
            Vec_IntPush( p->vDivSet, c0 );
            Vec_IntPush( p->vDivSet, c1 );
            return 1;
        }

    if ( p->pPars->nLutSize == 2 )
        return 0;
    for ( c0 = 0;    c0 < nDivs; c0++ )
    for ( c1 = c0+1; c1 < nDivs; c1++ )
    for ( c2 = c1+1; c2 < nDivs; c2++ )
        if ( (Cover[c0] | Cover[c1] | Cover[c2]) == Target )
        {
            Vec_IntPush( p->vDivSet, c0 );
            Vec_IntPush( p->vDivSet, c1 );
            Vec_IntPush( p->vDivSet, c2 );
            return 1;
        }

    if ( p->pPars->nLutSize == 3 )
        return 0;
    for ( c0 = 0;    c0 < nDivs; c0++ )
    for ( c1 = c0+1; c1 < nDivs; c1++ )
    for ( c2 = c1+1; c2 < nDivs; c2++ )
    for ( c3 = c2+1; c3 < nDivs; c3++ )
    {
        if ( (Cover[c0] | Cover[c1] | Cover[c2] | Cover[c3]) == Target )
        {
            Vec_IntPush( p->vDivSet, c0 );
            Vec_IntPush( p->vDivSet, c1 );
            Vec_IntPush( p->vDivSet, c2 );
            Vec_IntPush( p->vDivSet, c3 );
            return 1;
        }
    }
    return 0;
}

static inline int Sbd_ManFindCands( Sbd_Man_t * p, word Cover[64], int nDivs )
{
    int Ones[64], Order[64];
    int Limits[4] = { nDivs/4+1, nDivs/3+2, nDivs/2+3, nDivs };
    int c0, c1, c2, c3;
    word Target = Cover[nDivs];

    if ( nDivs < 8 || p->pPars->fCover )
        return Sbd_ManFindCandsSimple( p, Cover, nDivs );

    Vec_IntClear( p->vDivSet );
    for ( c0 = 0; c0 < nDivs; c0++ )
        if ( Cover[c0] == Target )
        {
            Vec_IntPush( p->vDivSet, c0 );
            return 1;
        }

    for ( c0 = 0;    c0 < nDivs; c0++ )
    for ( c1 = c0+1; c1 < nDivs; c1++ )
        if ( (Cover[c0] | Cover[c1]) == Target )
        {
            Vec_IntPush( p->vDivSet, c0 );
            Vec_IntPush( p->vDivSet, c1 );
            return 1;
        }

    if ( p->pPars->nLutSize == 2 )
        return 0;
    // count ones
    for ( c0 = 0; c0 < nDivs; c0++ )
        Ones[c0] = Abc_TtCountOnes( Cover[c0] );

    // sort by the number of ones
    for ( c0 = 0; c0 < nDivs; c0++ )
        Order[c0] = c0;
    Vec_IntSelectSortCost2Reverse( Order, nDivs, Ones );

    // sort with limits
    for ( c0 = 0;    c0 < Limits[0]; c0++ )
    for ( c1 = c0+1; c1 < Limits[1]; c1++ )
    for ( c2 = c1+1; c2 < Limits[2]; c2++ )
        if ( (Cover[Order[c0]] | Cover[Order[c1]] | Cover[Order[c2]]) == Target )
        {
            Vec_IntPush( p->vDivSet, Order[c0] );
            Vec_IntPush( p->vDivSet, Order[c1] );
            Vec_IntPush( p->vDivSet, Order[c2] );
            return 1;
        }

    if ( p->pPars->nLutSize == 3 )
        return 0;
    for ( c0 = 0;    c0 < Limits[0]; c0++ )
    for ( c1 = c0+1; c1 < Limits[1]; c1++ )
    for ( c2 = c1+1; c2 < Limits[2]; c2++ )
    for ( c3 = c2+1; c3 < Limits[3]; c3++ )
    {
        if ( (Cover[Order[c0]] | Cover[Order[c1]] | Cover[Order[c2]] | Cover[Order[c3]]) == Target )
        {
            Vec_IntPush( p->vDivSet, Order[c0] );
            Vec_IntPush( p->vDivSet, Order[c1] );
            Vec_IntPush( p->vDivSet, Order[c2] );
            Vec_IntPush( p->vDivSet, Order[c3] );
            return 1;
        }
    }
    return 0;
}


int Sbd_ManExplore( Sbd_Man_t * p, int Pivot, word * pTruth )
{
    int fVerbose = 0;
    abctime clk;
    int nIters, nItersMax = 32;

    word MatrS[64] = {0}, MatrC[2][64] = {{0}}, Cubes[2][2][64] = {{{0}}}, Cover[64] = {0}, Cube, CubeNew[2];
    int i, k, n, Node, Index, nCubes[2] = {0}, nRows = 0, nRowsOld;

    int nDivs = Vec_IntSize(p->vDivValues);
    int PivotVar = Vec_IntEntry(p->vObj2Var, Pivot);
    int FreeVar = Vec_IntSize(p->vWinObjs) + Vec_IntSize(p->vTfo) + Vec_IntSize(p->vRoots);
    int RetValue = 0, Status;

    if ( p->pPars->fVerbose )
        printf( "Node %d.  Useful divisors = %d.\n", Pivot, nDivs );

    if ( fVerbose )
        Sbd_ManPrintObj( p, Pivot );

    // collect bit-matrices
    Vec_IntForEachEntry( p->vDivVars, Node, i )
    {
        MatrS[63-i]    = *Sbd_ObjSim0( p, Vec_IntEntry(p->vWinObjs, Node) );
        MatrC[0][63-i] = *Sbd_ObjSim2( p, Vec_IntEntry(p->vWinObjs, Node) );
        MatrC[1][63-i] = *Sbd_ObjSim3( p, Vec_IntEntry(p->vWinObjs, Node) );
    }
    MatrS[63-i]    = *Sbd_ObjSim0( p, Pivot );
    MatrC[0][63-i] = *Sbd_ObjSim2( p, Pivot );
    MatrC[1][63-i] = *Sbd_ObjSim3( p, Pivot );

    //Sbd_PrintMatrix64( MatrS );
    Sbd_TransposeMatrix64( MatrS );
    Sbd_TransposeMatrix64( MatrC[0] );
    Sbd_TransposeMatrix64( MatrC[1] );
    //Sbd_PrintMatrix64( MatrS );

    // collect cubes
    for ( i = 0; i < 64; i++ )
    {
        assert( Abc_TtGetBit(&MatrC[0][i], nDivs) == Abc_TtGetBit(&MatrC[1][i], nDivs) );
        if ( !Abc_TtGetBit(&MatrC[0][i], nDivs) )
            continue;
        Index = Abc_TtGetBit(&MatrS[i], nDivs); // Index==0 offset; Index==1 onset
        for ( n = 0; n < 2; n++ )
        {
            if ( n && MatrC[0][i] == MatrC[1][i] )
                continue;
            assert( MatrC[n][i] );
            CubeNew[0] = ~MatrS[i] & MatrC[n][i];
            CubeNew[1] =  MatrS[i] & MatrC[n][i];
            assert( CubeNew[0] || CubeNew[1] );
            nCubes[Index] = Sbd_ManAddCube2( Cubes[Index], nCubes[Index], CubeNew );
        }
    }

    if ( p->pPars->fVerbose )
        printf( "Generated matrix with %d x %d entries.\n", nCubes[0], nCubes[1] );

    if ( p->pPars->fVerbose )
    for ( n = 0; n < 2; n++ )
    {
        printf( "%s:\n", n ? "Onset" : "Offset" );
        for ( i = 0; i < nCubes[n]; i++, printf( "\n" ) )
            for ( k = 0; k < 64; k++ )
                if ( Abc_TtGetBit(&Cubes[n][0][i], k) )
                    printf( "0" );
                else if ( Abc_TtGetBit(&Cubes[n][1][i], k) )
                    printf( "1" );
                else 
                    printf( "." );
        printf( "\n" );
    }

    // create covering table
    nRows = 0;
    for ( i = 0; i < nCubes[0] && nRows < 32; i++ )
    for ( k = 0; k < nCubes[1] && nRows < 32; k++ )
    {
        Cube = (Cubes[0][1][i] & Cubes[1][0][k]) | (Cubes[0][0][i] & Cubes[1][1][k]);
        assert( Cube );
        nRows = Sbd_ManAddCube1( 64, Cover, nRows, Cube );
    }

    Sbd_ManCoverReverseOrder( Cover );

    if ( p->pPars->fVerbose )
        printf( "Generated cover with %d entries.\n", nRows );

    //if ( p->pPars->fVerbose )
    //Sbd_PrintMatrix64( Cover );
    Sbd_TransposeMatrix64( Cover );
    //if ( p->pPars->fVerbose )
    //Sbd_PrintMatrix64( Cover );

    Sbd_ManCoverReverseOrder( Cover );

    nRowsOld = nRows;
    for ( nIters = 0; nIters < nItersMax && nRows < 64; nIters++ )
    {
        if ( p->pPars->fVerbose )
            Sbd_ManMatrPrint( p, Cover, nDivs, nRows );

        clk = Abc_Clock();
        if ( !Sbd_ManFindCands( p, Cover, nDivs ) )
        {
            if ( p->pPars->fVerbose )
                printf( "Cannot find a feasible cover.\n" );
            p->timeCov += Abc_Clock() - clk;
            return RetValue;
        }
        p->timeCov += Abc_Clock() - clk;
    
        if ( p->pPars->fVerbose )
            printf( "Candidate support:  " ),
            Vec_IntPrint( p->vDivSet );

        clk = Abc_Clock();
        Vec_IntForEachEntry( p->vDivSet, Node, i )
            Vec_IntWriteEntry( p->vDivSet, i, Vec_IntEntry(p->vDivVars, Node) );
        Status = Sbd_ManSolve( p->pSat, PivotVar, FreeVar+nIters, p->vDivSet, p->vDivVars, p->vDivValues, p->vLits, p->pPars->nBTLimit, pTruth );
        p->timeSat += Abc_Clock() - clk;

        if ( Status == l_Undef )
            return 0;
        else if ( Status == l_True )
        {
            if ( p->pPars->fVerbose )
            {
                int i;
                printf( "Node %d:  SAT.\n", Pivot );
                for ( i = 0; i < nDivs; i++ )
                    printf( "%d", i % 10 );
                printf( "\n" );
                for ( i = 0; i < nDivs; i++ )
                    printf( "%c", (Vec_IntEntry(p->vDivValues, i) & 0x4) ? '0' + (Vec_IntEntry(p->vDivValues, i) & 1) : 'x' );
                printf( "\n" );
                for ( i = 0; i < nDivs; i++ )
                    printf( "%c", (Vec_IntEntry(p->vDivValues, i) & 0x8) ? '0' + ((Vec_IntEntry(p->vDivValues, i) >> 1) & 1) : 'x' );
                printf( "\n" );
            }
            // add row to the covering table
            for ( i = 0; i < nDivs; i++ )
                if ( Vec_IntEntry(p->vDivValues, i) == 0xE || Vec_IntEntry(p->vDivValues, i) == 0xD )
                    Cover[i] |= ((word)1 << nRows);
            Cover[nDivs] |= ((word)1 << nRows);
            nRows++;
        }
        else
        {
            if ( p->pPars->fVerbose )
            {
                printf( "Node %d:  UNSAT.\n", Pivot );
                Extra_PrintBinary( stdout, (unsigned *)pTruth, 1 << Vec_IntSize(p->vDivSet) ), printf( "\n" );
            }
            RetValue = 1;
            break;
        }
        //break;
    }
    return RetValue;
}

int Sbd_ManExplore2( Sbd_Man_t * p, int Pivot, word * pTruth )
{
    abctime clk;
    word Onset[64] = {0}, Offset[64] = {0}, Cube;
    word CoverRows[64] = {0}, CoverCols[64] = {0};
    int nIters, nItersMax = 32;
    int i, k, Node, nRows = 0;

    int PivotVar = Vec_IntEntry(p->vObj2Var, Pivot);
    int FreeVar = Vec_IntSize(p->vWinObjs) + Vec_IntSize(p->vTfo) + Vec_IntSize(p->vRoots);
    int nDivs = Vec_IntSize( p->vDivVars );
    int nConsts = 4;
    int RetValue, Status;

    clk = Abc_Clock();
    p->pSat = Sbd_ManSatSolver( p->pSat, p->pGia, p->vMirrors, Pivot, p->vWinObjs, p->vObj2Var, p->vTfo, p->vRoots, 0 );
    p->timeCnf += Abc_Clock() - clk;
    if ( p->pSat == NULL )
        return 0;
    assert( nConsts <= 8 );
    clk = Abc_Clock();
    RetValue = Sbd_ManCollectConstantsNew( p->pSat, p->vDivVars, nConsts, PivotVar, Onset, Offset, p->pPars->nBTLimit );
    p->timeSat += Abc_Clock() - clk;
    if ( RetValue == -2 )
        return 0;
    if ( RetValue >= 0 )
    {
        if ( p->pPars->fVeryVerbose )
            printf( "Found stuck-at-%d node %d.\n", RetValue, Pivot );
        Vec_IntClear( p->vDivSet );
        *pTruth = RetValue ? ~(word)0 : 0;
        p->nLuts[0]++;
        return 1;
    }
    RetValue = 0;

    // create rows of the table
    nRows = 0;
    for ( i = 0; i < nConsts; i++ )
    for ( k = 0; k < nConsts; k++ )
    {
        Cube = Onset[i] ^ Offset[k];
        assert( Cube );
        nRows = Sbd_ManAddCube1( 256, CoverRows, nRows, Cube );
    }
    assert( nRows <= 64 );
    
    // create columns of the table
    for ( i = 0; i < nRows; i++ )
        for ( k = 0; k <= nDivs; k++ )
            if ( (CoverRows[i] >> k) & 1 )
                Abc_TtXorBit(&CoverCols[k], i);

    // solve the covering problem
    for ( nIters = 0; nIters < nItersMax && nRows < 64; nIters++ )
    {
        if ( p->pPars->fVeryVerbose )
            Sbd_ManMatrPrint( p, CoverCols, nDivs, nRows );

        clk = Abc_Clock();
        if ( !Sbd_ManFindCands( p, CoverCols, nDivs ) )
        {
            if ( p->pPars->fVeryVerbose )
                printf( "Cannot find a feasible cover.\n" );
            p->timeCov += Abc_Clock() - clk;
            return 0;
        }
        p->timeCov += Abc_Clock() - clk;

        if ( p->pPars->fVeryVerbose )
            printf( "Candidate support:  " ),
            Vec_IntPrint( p->vDivSet );

        clk = Abc_Clock();
        Vec_IntForEachEntry( p->vDivSet, Node, i )
            Vec_IntWriteEntry( p->vDivSet, i, Vec_IntEntry(p->vDivVars, Node) );
        Status = Sbd_ManSolve( p->pSat, PivotVar, FreeVar+nIters, p->vDivSet, p->vDivVars, p->vDivValues, p->vLits, p->pPars->nBTLimit, pTruth );
        p->timeSat += Abc_Clock() - clk;

        if ( Status == l_Undef )
            return 0;
        else if ( Status == l_True )
        {
            if ( p->pPars->fVeryVerbose )
            {
                int i;
                printf( "Node %d:  SAT.\n", Pivot );
                for ( i = 0; i < nDivs; i++ )
                    printf( "%d", Vec_IntEntry(p->vLutLevs, Vec_IntEntry(p->vWinObjs, Vec_IntEntry(p->vDivVars, i))) );
                printf( "\n" );
                for ( i = 0; i < nDivs; i++ )
                    printf( "%d", i % 10 );
                printf( "\n" );
                for ( i = 0; i < nDivs; i++ )
                    printf( "%c", (Vec_IntEntry(p->vDivValues, i) & 0x4) ? '0' + (Vec_IntEntry(p->vDivValues, i) & 1) : 'x' );
                printf( "\n" );
                for ( i = 0; i < nDivs; i++ )
                    printf( "%c", (Vec_IntEntry(p->vDivValues, i) & 0x8) ? '0' + ((Vec_IntEntry(p->vDivValues, i) >> 1) & 1) : 'x' );
                printf( "\n" );
            }
            // add row to the covering table
            for ( i = 0; i < nDivs; i++ )
                if ( Vec_IntEntry(p->vDivValues, i) == 0xE || Vec_IntEntry(p->vDivValues, i) == 0xD )
                    CoverCols[i] |= ((word)1 << nRows);
            CoverCols[nDivs] |= ((word)1 << nRows);
            nRows++;
        }
        else
        {
            if ( p->pPars->fVeryVerbose )
            {
                printf( "Node %d:  UNSAT.   ", Pivot );
                Extra_PrintBinary( stdout, (unsigned *)pTruth, 1 << Vec_IntSize(p->vDivSet) ), printf( "\n" );
            }
            p->nLuts[1]++;
            RetValue = 1;
            break;
        }
    }
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Simulates an AIG cone in terms of a structural cut.]

  Description [Returns a truth-table literal, or -1 if a CI is reached
  outside the cut. Mirrors include changes made at earlier pivots.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Sbd_ManAcdTruth_rec( Sbd_Man_t * p, int iObj, int nWords )
{
    Gia_Obj_t * pObj;
    int Lit0, Lit1, Lit, Offset;
    if ( Vec_IntEntry(p->vAcdMap, iObj) >= 0 )
        return Vec_IntEntry(p->vAcdMap, iObj);
    Lit = Vec_IntEntry(p->vMirrors, iObj);
    if ( Lit >= 0 )
    {
        Lit0 = Sbd_ManAcdTruth_rec( p, Abc_Lit2Var(Lit), nWords );
        return Lit0 < 0 ? -1 : Abc_LitNotCond(Lit0, Abc_LitIsCompl(Lit));
    }
    pObj = Gia_ManObj( p->pGia, iObj );
    if ( !Gia_ObjIsAnd(pObj) )
        return -1;
    Lit0 = Sbd_ManAcdTruth_rec( p, Gia_ObjFaninId0(pObj, iObj), nWords );
    if ( Lit0 < 0 )
        return -1;
    Lit1 = Sbd_ManAcdTruth_rec( p, Gia_ObjFaninId1(pObj, iObj), nWords );
    if ( Lit1 < 0 )
        return -1;
    Offset = Vec_WrdSize(p->vAcdTruth);
    Vec_WrdFillExtra( p->vAcdTruth, Offset + nWords, 0 );
    Abc_TtAndCompl( Vec_WrdEntryP(p->vAcdTruth, Offset),
        Vec_WrdEntryP(p->vAcdTruth, Abc_Lit2Var(Lit0) * nWords), Abc_LitIsCompl(Lit0) ^ Gia_ObjFaninC0(pObj),
        Vec_WrdEntryP(p->vAcdTruth, Abc_Lit2Var(Lit1) * nWords), Abc_LitIsCompl(Lit1) ^ Gia_ObjFaninC1(pObj), nWords );
    Lit = Abc_Var2Lit( Offset / nWords, 0 );
    Vec_IntWriteEntry( p->vAcdMap, iObj, Lit );
    Vec_IntPush( p->vAcdNodes, iObj );
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Computes a cut truth table without SAT enumeration.]

  Description [A support obtained using don't-cares may not be a
  structural cut. In this case, leave synthesis to the QBF fallback.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Sbd_ManAcdTruth( Sbd_Man_t * p, int Pivot, word * pTruth )
{
    int nVars = Vec_IntSize(p->vDivSet), nWords = Abc_Truth6WordNum(nVars);
    int i, iVar, iObj, Lit;
    Vec_IntFillExtra( p->vAcdMap, Gia_ManObjNum(p->pGia), -1 );
    Vec_IntClear( p->vAcdNodes );
    Vec_WrdFill( p->vAcdTruth, (nVars + 1) * nWords, 0 );
    Vec_IntWriteEntry( p->vAcdMap, 0, 0 );
    Vec_IntPush( p->vAcdNodes, 0 );
    Vec_IntForEachEntry( p->vDivSet, iVar, i )
    {
        iObj = Vec_IntEntry( p->vWinObjs, iVar );
        assert( iObj > 0 && Vec_IntEntry(p->vAcdMap, iObj) == -1 );
        Vec_IntWriteEntry( p->vAcdMap, iObj, Abc_Var2Lit(i + 1, 0) );
        Vec_IntPush( p->vAcdNodes, iObj );
        Abc_TtIthVar( Vec_WrdEntryP(p->vAcdTruth, (i + 1) * nWords), i, nVars );
    }
    Lit = Sbd_ManAcdTruth_rec( p, Pivot, nWords );
    if ( Lit >= 0 )
        Abc_TtCopy( pTruth, Vec_WrdEntryP(p->vAcdTruth, Abc_Lit2Var(Lit) * nWords), nWords, Abc_LitIsCompl(Lit) );
    Vec_IntForEachEntry( p->vAcdNodes, iObj, i )
        Vec_IntWriteEntry( p->vAcdMap, iObj, -1 );
    return Lit >= 0;
}

/**Function*************************************************************

  Synopsis    [Converts an ACD record and checks its actual LUT depth.]

  Description [ACD numbers LUTs from inputs to output; SBD stores the
  output first. Preserve truth-table pin order while reversing LUT IDs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Sbd_ManAcdImport( Sbd_Man_t * p, int Pivot, unsigned char * pRecord, int * pnStrs, Sbd_Str_t * Strs )
{
    int nVars = Vec_IntSize(p->vDivSet), nLuts = pRecord[1];
    int Levels[SBD_DIV_MAX + 3], i, k, iVar, Pos = 2;
    if ( nLuts < 1 || nLuts > p->pPars->nLutNum )
        return 0;
    Vec_IntForEachEntry( p->vDivSet, iVar, i )
        Levels[i] = Vec_IntEntry( p->vLutLevs, Vec_IntEntry(p->vWinObjs, iVar) );
    for ( i = 0; i < nLuts; i++ )
    {
        Sbd_Str_t * pStr = Strs + nLuts - 1 - i;
        int nBytes, Level = 0;
        if ( Pos >= pRecord[0] )
            return 0;
        pStr->fLut = 1;
        pStr->nVarIns = pRecord[Pos++];
        if ( pStr->nVarIns > p->pPars->nLutSize )
            return 0;
        nBytes = pStr->nVarIns <= 3 ? 1 : 1 << (pStr->nVarIns - 3);
        if ( Pos + pStr->nVarIns + nBytes > pRecord[0] )
            return 0;
        for ( k = 0; k < pStr->nVarIns; k++ )
        {
            int Fan = pRecord[Pos++];
            if ( Fan >= nVars + i )
                return 0;
            Level = Abc_MaxInt( Level, Levels[Fan] );
            pStr->VarIns[k] = Fan < nVars ? Fan : nVars + nLuts - 1 - (Fan - nVars);
        }
        Levels[nVars + i] = Level + 1;
        pStr->Res = 0;
        for ( k = 0; k < nBytes; k++ )
            pStr->Res |= (word)pRecord[Pos++] << (8 * k);
        pStr->Res = Abc_Tt6Stretch( pStr->Res, pStr->nVarIns );
    }
    if ( Pos != pRecord[0] || Levels[nVars + nLuts - 1] >= Vec_IntEntry(p->vLutLevs, Pivot) )
        return 0;
    *pnStrs = nLuts;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Tries truth-table decomposition before QBF synthesis.]

  Description [Use ACD's C interface on a fully specified structural
  function. Late divisors must feed the output LUT directly. Failures
  retain the existing QBF search, including its don't-care flexibility.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Sbd_ManTryAcd( Sbd_Man_t * p, int Pivot, int * pnStrs, Sbd_Str_t * Strs )
{
    word Truth[1 << (SBD_DIV_MAX - 6)];
    unsigned char Record[256];
    unsigned Mask = 0, Profile;
    int nVars = Vec_IntSize(p->vDivSet), K = p->pPars->nLutSize;
    int i, iVar, Delay = Vec_IntEntry(p->vLutLevs, Pivot);
    if ( K < 4 || nVars <= K )
        return 0;
    p->nAcdTried++;
    if ( !Sbd_ManAcdTruth(p, Pivot, Truth) || Abc_TtSupportSize(Truth, nVars) != nVars )
        return 0;
    p->nAcdTruths++;
    Vec_IntForEachEntry( p->vDivSet, iVar, i )
        if ( Vec_IntEntry(p->vLutLevs, Vec_IntEntry(p->vWinObjs, iVar)) == Delay - 2 )
            Mask |= 1u << i;
    Profile = Mask;
    if ( nVars < 2 * K && acd2_decompose(Truth, nVars, K, &Profile, Record) == 0 &&
         Sbd_ManAcdImport(p, Pivot, Record, pnStrs, Strs) )
        return 1;
    Profile = Mask;
    return p->pPars->nLutNum >= 3 && acd_decompose(Truth, nVars, K, &Profile, Record) == 0 &&
           Sbd_ManAcdImport(p, Pivot, Record, pnStrs, Strs);
}

int Sbd_ManExploreCut( Sbd_Man_t * p, int Pivot, int nLeaves, int * pLeaves, int * pnStrs, Sbd_Str_t * Strs, int * pFreeVar )
{
    abctime clk = Abc_Clock();
    int PivotVar = Vec_IntEntry(p->vObj2Var, Pivot);
    int Delay = Vec_IntEntry( p->vLutLevs, Pivot );
    int pNodesTop[SBD_DIV_MAX], pNodesBot[SBD_DIV_MAX], pNodesBot1[SBD_DIV_MAX], pNodesBot2[SBD_DIV_MAX];
    int nNodesTop = 0, nNodesBot = 0, nNodesBot1 = 0, nNodesBot2 = 0, nNodesDiff = 0, nNodesDiff1 = 0, nNodesDiff2 = 0;
    int i, k, iObj, nIters, RetValue = 0, Status;

    // The revisit uses structural cuts directly; only the full pass uses
    // SAT to remove fanins and exploit window don't-cares.
    for ( nIters = 0; !p->fRevisit && nIters < nLeaves; nIters++ )
    {
        // try to remove one variable from divisors
        Vec_IntClear( p->vDivSet );
        for ( i = 0; i < nLeaves; i++ )
            if ( i != nLeaves-1-nIters && pLeaves[i] != -1 )
                Vec_IntPush( p->vDivSet, Vec_IntEntry(p->vObj2Var, pLeaves[i]) );
        assert( Vec_IntSize(p->vDivSet) < nLeaves );
        // compute truth table
        clk = Abc_Clock();
        Status = Sbd_ManSolve( p->pSat, PivotVar, (*pFreeVar)++, p->vDivSet, p->vDivVars, p->vDivValues, p->vLits, p->pPars->nBTLimit, NULL );
        p->timeSat += Abc_Clock() - clk;
        if ( Status == l_Undef )
            return 0;
        else if ( Status == l_True )
        {
            int DelayDiff = Vec_IntEntry(p->vLutLevs, pLeaves[nLeaves-1-nIters]) - Delay;
            if ( DelayDiff > -2 )
                return 0;
        }
        else
            pLeaves[nLeaves-1-nIters] = -1;
    }
    Vec_IntClear( p->vDivSet );
    for ( i = 0; i < nLeaves; i++ )
        if ( pLeaves[i] != -1 )
            Vec_IntPush( p->vDivSet, pLeaves[i] );
    //printf( "Reduced %d -> %d\n", nLeaves, Vec_IntSize(p->vDivSet) );
    if ( Vec_IntSize(p->vDivSet) <= p->pPars->nLutSize )
    {
        word Truth;
        *pnStrs = 1;
        // remap divisors
        Vec_IntForEachEntry( p->vDivSet, iObj, i )
            Vec_IntWriteEntry( p->vDivSet, i, Vec_IntEntry(p->vObj2Var, iObj) );
        // compute truth table
        clk = Abc_Clock();
        if ( p->fRevisit )
        {
            Status = Sbd_ManAcdTruth(p, Pivot, &Truth) ? l_False : l_Undef;
            p->timeAcd += Abc_Clock() - clk;
        }
        else
        {
            Status = Sbd_ManSolve( p->pSat, PivotVar, (*pFreeVar)++, p->vDivSet, p->vDivVars, p->vDivValues, p->vLits, p->pPars->nBTLimit, &Truth );
            p->timeSat += Abc_Clock() - clk;
        }
        if ( Status == l_Undef )
            return 0;
        if ( Status == l_True )
        {
            if ( p->pPars->fVerbose )
                printf( "The cut at node %d is not topological.\n", p->Pivot );
            return 0;
        }
        assert( Status == l_False );
        // create structure
        Strs->fLut = 1;
        Strs->nVarIns = Vec_IntSize( p->vDivSet );
        for ( i = 0; i < Strs->nVarIns; i++ )
            Strs->VarIns[i] = i;
        Strs->Res = Truth;
        p->nLuts[1]++;
        //Extra_PrintBinary( stdout, (unsigned *)&Truth, 1 << Strs->nVarIns ), printf( "\n" );
        return 1;
    }
    assert( Vec_IntSize(p->vDivSet) > p->pPars->nLutSize );
    if ( p->pPars->nLutNum < 2 )
        return 0;

    // count number of nodes on each level
    nNodesTop = nNodesBot = nNodesBot1 = nNodesBot2 = 0;
    Vec_IntForEachEntry( p->vDivSet, iObj, i )
    {
        int DelayDiff = Vec_IntEntry(p->vLutLevs, iObj) - Delay;
        if ( DelayDiff > -2 )
            break;
        if ( DelayDiff == -2 )
            pNodesTop[nNodesTop++] = i;
        else // if ( DelayDiff < -2 )
        {
            pNodesBot[nNodesBot++] = i;
            if ( DelayDiff == -3 )
                pNodesBot1[nNodesBot1++] = i;
            else // if ( DelayDiff < -3 )
                pNodesBot2[nNodesBot2++] = i;
        }
        Vec_IntWriteEntry( p->vDivSet, i, Vec_IntEntry(p->vObj2Var, iObj) );
    }
    assert( nNodesBot == nNodesBot1 + nNodesBot2 );
    if ( i < Vec_IntSize(p->vDivSet) )
        return 0;
    if ( nNodesTop > p->pPars->nLutSize-1 || Vec_IntSize(p->vDivSet) > 3*p->pPars->nLutSize-2 )
        return 0;

    clk = Abc_Clock();
    RetValue = Sbd_ManTryAcd( p, Pivot, pnStrs, Strs );
    p->timeAcd += Abc_Clock() - clk;
    if ( RetValue )
    {
        p->nAcdFound++;
        p->fAcdFound = 1;
        p->nLuts[*pnStrs]++;
        return 1;
    }

    if ( p->fRevisit )
        return 0;
    // try 44
    if ( Vec_IntSize(p->vDivSet) <= 2*p->pPars->nLutSize-1 )
    {
        int nMoved = 0;
        if ( nNodesBot > p->pPars->nLutSize ) // need to move bottom left-over to the top
        {
            while ( nNodesBot > p->pPars->nLutSize )
                pNodesTop[nNodesTop++] = pNodesBot[--nNodesBot], nMoved++;
            assert( nNodesBot == p->pPars->nLutSize );
        }
        assert( nNodesBot <= p->pPars->nLutSize );
        assert( nNodesTop <= p->pPars->nLutSize-1 );

        Strs[0].fLut = 1;
        Strs[0].nVarIns = p->pPars->nLutSize;
        for ( i = 0; i < nNodesTop; i++ )
            Strs[0].VarIns[i] = pNodesTop[i];
        for ( ; i < p->pPars->nLutSize; i++ )
            Strs[0].VarIns[i] = Vec_IntSize(p->vDivSet)+1 + i-nNodesTop;
        Strs[0].Res = 0;

        Strs[1].fLut = 1;
        Strs[1].nVarIns = nNodesBot;
        for ( i = 0; i < nNodesBot; i++ )
            Strs[1].VarIns[i] = pNodesBot[i];
        Strs[1].Res = 0;

        nNodesDiff = p->pPars->nLutSize-1 - nNodesTop;
        assert( nNodesDiff >= 0 && nNodesDiff <= p->pPars->nLutSize-1 );
        for ( k = 0; k < nNodesDiff; k++ )
        {
            Strs[2+k].fLut = 0;
            Strs[2+k].nVarIns = nNodesBot;
            for ( i = 0; i < nNodesBot; i++ )
                Strs[2+k].VarIns[i] = pNodesBot[i];
            Strs[2+k].Res = 0;
        }

        *pnStrs = 2 + nNodesDiff;
        clk = Abc_Clock();
        p->nQbfCalls++;
        RetValue = Sbd_ProblemSolve( p->pGia, p->vMirrors,   Pivot, p->vWinObjs, p->vObj2Var, p->vTfo, p->vRoots,   p->vDivSet, *pnStrs, Strs, p->pPars->nBTLimit, &p->pSatCec, &p->pSatQbf );
        p->timeQbf += Abc_Clock() - clk;
        if ( RetValue ) 
            p->nLuts[2]++;

        while ( nMoved-- )
            pNodesBot[nNodesBot++] = pNodesTop[--nNodesTop];
    }

    if ( RetValue )
        return RetValue;
    if ( p->pPars->nLutNum < 3 )
        return 0;
    if ( Vec_IntSize(p->vDivSet) < 2*p->pPars->nLutSize-1 )
        return 0;

    // try 444 -- LUT(LUT, LUT)
    if ( nNodesTop <= p->pPars->nLutSize-2 )
    {
        int nMoved = 0;
        if ( nNodesBot > 2*p->pPars->nLutSize ) // need to move bottom left-over to the top
        {
            while ( nNodesBot > 2*p->pPars->nLutSize )
                pNodesTop[nNodesTop++] = pNodesBot[--nNodesBot], nMoved++;
            assert( nNodesBot == 2*p->pPars->nLutSize );
        }
        assert( nNodesBot > p->pPars->nLutSize );
        assert( nNodesBot <= 2*p->pPars->nLutSize );
        assert( nNodesTop <= p->pPars->nLutSize-2 );

        Strs[0].fLut = 1;
        Strs[0].nVarIns = p->pPars->nLutSize;
        for ( i = 0; i < nNodesTop; i++ )
            Strs[0].VarIns[i] = pNodesTop[i];
        for ( ; i < p->pPars->nLutSize; i++ )
            Strs[0].VarIns[i] = Vec_IntSize(p->vDivSet)+1 + i-nNodesTop;
        Strs[0].Res = 0;

        Strs[1].fLut = 1;
        Strs[1].nVarIns = p->pPars->nLutSize;
        for ( i = 0; i < Strs[1].nVarIns; i++ )
            Strs[1].VarIns[i] = pNodesBot[i];
        Strs[1].Res = 0;

        Strs[2].fLut = 1;
        Strs[2].nVarIns = p->pPars->nLutSize;
        for ( i = 0; i < Strs[2].nVarIns; i++ )
            Strs[2].VarIns[i] = pNodesBot[nNodesBot-p->pPars->nLutSize+i];
        Strs[2].Res = 0;

        nNodesDiff = p->pPars->nLutSize-2 - nNodesTop;
        assert( nNodesDiff >= 0 && nNodesDiff <= p->pPars->nLutSize-2 );
        for ( k = 0; k < nNodesDiff; k++ )
        {
            Strs[3+k].fLut = 0;
            Strs[3+k].nVarIns = nNodesBot;
            for ( i = 0; i < nNodesBot; i++ )
                Strs[3+k].VarIns[i] = pNodesBot[i];
            Strs[3+k].Res = 0;
        }

        *pnStrs = 3 + nNodesDiff;
        clk = Abc_Clock();
        p->nQbfCalls++;
        RetValue = Sbd_ProblemSolve( p->pGia, p->vMirrors,   Pivot, p->vWinObjs, p->vObj2Var, p->vTfo, p->vRoots,   p->vDivSet, *pnStrs, Strs, p->pPars->nBTLimit, &p->pSatCec, &p->pSatQbf );
        p->timeQbf += Abc_Clock() - clk;
        if ( RetValue ) 
            p->nLuts[3]++;

        while ( nMoved-- )
            pNodesBot[nNodesBot++] = pNodesTop[--nNodesTop];
    }
    if ( RetValue )
        return RetValue;

    // try 444 -- LUT(LUT(LUT))
    if ( nNodesBot1 + nNodesTop <= 2*p->pPars->nLutSize-2 )
    {
        if ( nNodesBot2 > p->pPars->nLutSize ) // need to move bottom left-over to the top
        {
            while ( nNodesBot2 > p->pPars->nLutSize )
                pNodesBot1[nNodesBot1++] = pNodesBot2[--nNodesBot2];
            assert( nNodesBot2 == p->pPars->nLutSize );
        }
        if ( nNodesBot1 > p->pPars->nLutSize-1 ) // need to move bottom left-over to the top
        {
            while ( nNodesBot1 > p->pPars->nLutSize-1 )
                pNodesTop[nNodesTop++] = pNodesBot1[--nNodesBot1];
            assert( nNodesBot1 == p->pPars->nLutSize-1 );
        }
        assert( nNodesBot2 <= p->pPars->nLutSize );
        assert( nNodesBot1 <= p->pPars->nLutSize-1 );
        assert( nNodesTop <= p->pPars->nLutSize-1 );

        Strs[0].fLut = 1;
        Strs[0].nVarIns = p->pPars->nLutSize;
        for ( i = 0; i < nNodesTop; i++ )
            Strs[0].VarIns[i] = pNodesTop[i];
        Strs[0].VarIns[i++] = Vec_IntSize(p->vDivSet)+1;
        for ( ; i < p->pPars->nLutSize; i++ )
            Strs[0].VarIns[i] = Vec_IntSize(p->vDivSet)+2 + i-nNodesTop;
        Strs[0].Res = 0;
        nNodesDiff1 = p->pPars->nLutSize-1 - nNodesTop;

        Strs[1].fLut = 1;
        Strs[1].nVarIns = p->pPars->nLutSize;
        for ( i = 0; i < nNodesBot1; i++ )
            Strs[1].VarIns[i] = pNodesBot1[i];
        Strs[1].VarIns[i++] = Vec_IntSize(p->vDivSet)+2;
        for ( ; i < p->pPars->nLutSize; i++ )
            Strs[1].VarIns[i] = Vec_IntSize(p->vDivSet)+2+nNodesDiff1 + i-nNodesBot1;
        Strs[1].Res = 0;
        nNodesDiff2 = p->pPars->nLutSize-1 - nNodesBot1;

        Strs[2].fLut = 1;
        Strs[2].nVarIns = nNodesBot2;
        for ( i = 0; i < Strs[2].nVarIns; i++ )
            Strs[2].VarIns[i] = pNodesBot2[i];
        Strs[2].Res = 0;

        nNodesDiff = nNodesDiff1 + nNodesDiff2;
        assert( nNodesDiff >= 0 && nNodesDiff <= p->pPars->nLutSize-1 );
        for ( k = 0; k < nNodesDiff; k++ )
        {
            Strs[3+k].fLut = 0;
            Strs[3+k].nVarIns = nNodesBot2;
            for ( i = 0; i < nNodesBot2; i++ )
                Strs[3+k].VarIns[i] = pNodesBot2[i];
            Strs[3+k].Res = 0;
            if ( k >= nNodesDiff1 )
                continue;
            Strs[3+k].nVarIns += nNodesBot1;
            for ( i = 0; i < nNodesBot1; i++ )
                Strs[3+k].VarIns[nNodesBot2 + i] = pNodesBot1[i];
        }

        *pnStrs = 3 + nNodesDiff;
        clk = Abc_Clock();
        p->nQbfCalls++;
        RetValue = Sbd_ProblemSolve( p->pGia, p->vMirrors,   Pivot, p->vWinObjs, p->vObj2Var, p->vTfo, p->vRoots,   p->vDivSet, *pnStrs, Strs, p->pPars->nBTLimit, &p->pSatCec, &p->pSatQbf );
        p->timeQbf += Abc_Clock() - clk;
        if ( RetValue ) 
            p->nLuts[4]++;
    }
    return RetValue;
}
int Sbd_ManExplore3( Sbd_Man_t * p, int Pivot, int * pnStrs, Sbd_Str_t * Strs )
{
    int FreeVar = Vec_IntSize(p->vWinObjs) + Vec_IntSize(p->vTfo) + Vec_IntSize(p->vRoots);
    int FreeVarStart = FreeVar;
    (void)FreeVarStart;
    int nSize, nLeaves, pLeaves[SBD_DIV_MAX];
    abctime clk = Abc_Clock();
    if ( !p->fRevisit )
    {
        p->pSat = Sbd_ManSatSolver( p->pSat, p->pGia, p->vMirrors, Pivot, p->vWinObjs, p->vObj2Var, p->vTfo, p->vRoots, 0 );
        p->timeCnf += Abc_Clock() - clk;
        if ( p->pSat == NULL )
            return 0;
    }
    // extract one cut
    if ( p->pSrv )
    {
        nLeaves = Sbd_ManCutServerFirst( p->pSrv, Pivot, pLeaves );
        if ( nLeaves == -1 )
            return 0;
        assert( nLeaves <= p->pPars->nCutSize );
        if ( Sbd_ManExploreCut( p, Pivot, nLeaves, pLeaves, pnStrs, Strs, &FreeVar ) )
            return 1;
        return 0;
    }
    // extract one cut
    for ( nSize = p->pPars->nLutSize + 1; nSize <= p->pPars->nCutSize; nSize++ )
    {
        nLeaves = Sbd_StoObjBestCut( p->pSto, Pivot, nSize, pLeaves );
        if ( nLeaves == -1 )
            continue;
        assert( nLeaves == nSize );
        if ( Sbd_ManExploreCut( p, Pivot, nLeaves, pLeaves, pnStrs, Strs, &FreeVar ) )
            return 1;
    }
    assert( FreeVar - FreeVarStart <= SBD_FVAR_MAX ); 
    return 0;
}


/**Function*************************************************************

  Synopsis    [Computes delay-oriented k-feasible cut at the node.]

  Description [Return 1 if node's LUT level does not exceed those of the fanins.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sbd_CutMergeSimple( Sbd_Man_t * p, int * pCut1, int * pCut2, int * pCut )
{
    int * pBeg  = pCut + 1;
    int * pBeg1 = pCut1 + 1;
    int * pBeg2 = pCut2 + 1;
    int * pEnd1 = pCut1 + 1 + pCut1[0];
    int * pEnd2 = pCut2 + 1 + pCut2[0];
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        if ( *pBeg1 == *pBeg2 )
            *pBeg++ = *pBeg1++, pBeg2++;
        else if ( *pBeg1 < *pBeg2 )
            *pBeg++ = *pBeg1++;
        else 
            *pBeg++ = *pBeg2++;
    }
    while ( pBeg1 < pEnd1 )
        *pBeg++ = *pBeg1++;
    while ( pBeg2 < pEnd2 )
        *pBeg++ = *pBeg2++;
    return (pCut[0] = pBeg - pCut - 1);
}
//
// int Sbd_ManMergeCuts( Sbd_Man_t * p, int Node )
// {
//     int Result  = 1; // no need to resynthesize
//     int pCut[2*SBD_MAX_LUTSIZE+1];
//     int iFan0   = Gia_ObjFaninId0( Gia_ManObj(p->pGia, Node), Node );
//     int iFan1   = Gia_ObjFaninId1( Gia_ManObj(p->pGia, Node), Node );
//     int Level0  = Vec_IntEntry( p->vLutLevs, iFan0 );
//     int Level1  = Vec_IntEntry( p->vLutLevs, iFan1 );
//     int LevMax  = (Level0 || Level1) ? Abc_MaxInt(Level0, Level1) : 1;
//     int * pCut0 = Sbd_ObjCut( p, iFan0 );
//     int * pCut1 = Sbd_ObjCut( p, iFan1 );
//     int nSize   = Sbd_CutMergeSimple( p, pCut0, pCut1, pCut );
//     if ( nSize > p->pPars->nLutSize )
//     {
//         if ( Level0 != Level1 )
//         {
//             int Cut0[2] = {1, iFan0}, * pCut0Temp = Level0 < LevMax ? Cut0 : pCut0;
//             int Cut1[2] = {1, iFan1}, * pCut1Temp = Level1 < LevMax ? Cut1 : pCut1;
//             nSize = Sbd_CutMergeSimple( p, pCut0Temp, pCut1Temp, pCut );
//         }
//         if ( nSize > p->pPars->nLutSize )
//         {
//             pCut[0] = 2;
//             pCut[1] = iFan0 < iFan1 ? iFan0 : iFan1;
//             pCut[2] = iFan0 < iFan1 ? iFan1 : iFan0;
//             Result  = LevMax ? 0 : 1;
//             LevMax++;
//         }
//     }
//     assert( iFan0 != iFan1 );
//     assert( Vec_IntEntry(p->vLutLevs, Node) == 0 );
//     Vec_IntWriteEntry( p->vLutLevs, Node, LevMax );
//     memcpy( Sbd_ObjCut(p, Node), pCut, sizeof(int) * (pCut[0] + 1) );
//     //printf( "Setting node %d with delay %d (result = %d).\n", Node, LevMax, Result );
//     return Result;
// }
//
int Sbd_ManMergeCuts( Sbd_Man_t * p, int Node )
{
    int pCut11[2*SBD_MAX_LUTSIZE+1];     
    int pCut01[2*SBD_MAX_LUTSIZE+1];     
    int pCut10[2*SBD_MAX_LUTSIZE+1];     
    int pCut00[2*SBD_MAX_LUTSIZE+1];     
    int iFan0   = Gia_ObjFaninId0( Gia_ManObj(p->pGia, Node), Node );
    int iFan1   = Gia_ObjFaninId1( Gia_ManObj(p->pGia, Node), Node );
    int Level0  = Vec_IntEntry( p->vLutLevs, iFan0 ) ? Vec_IntEntry( p->vLutLevs, iFan0 ) : 1;
    int Level1  = Vec_IntEntry( p->vLutLevs, iFan1 ) ? Vec_IntEntry( p->vLutLevs, iFan1 ) : 1;
    int * pCut0 = Sbd_ObjCut( p, iFan0 );
    int * pCut1 = Sbd_ObjCut( p, iFan1 );
    int Cut0[2] = {1, iFan0}; 
    int Cut1[2] = {1, iFan1}; 
    int nSize11 = Sbd_CutMergeSimple( p, pCut0, pCut1, pCut11 );
    int nSize01 = Sbd_CutMergeSimple( p,  Cut0, pCut1, pCut01 );
    int nSize10 = Sbd_CutMergeSimple( p, pCut0,  Cut1, pCut10 );
    int nSize00 = Sbd_CutMergeSimple( p,  Cut0,  Cut1, pCut00 );
    int Lev11   = nSize11 <= p->pPars->nLutSize ? Abc_MaxInt(Level0,   Level1)   : ABC_INFINITY;
    int Lev01   = nSize01 <= p->pPars->nLutSize ? Abc_MaxInt(Level0+1, Level1)   : ABC_INFINITY;
    int Lev10   = nSize10 <= p->pPars->nLutSize ? Abc_MaxInt(Level0,   Level1+1) : ABC_INFINITY;
    int Lev00   = nSize00 <= p->pPars->nLutSize ? Abc_MaxInt(Level0+1, Level1+1) : ABC_INFINITY;
    int * pCutRes = pCut11;
    int LevCur    = Lev11;
    if ( Lev01 < LevCur || (Lev01 == LevCur && pCut01[0] < pCutRes[0]) )
    {
        pCutRes = pCut01;
        LevCur  = Lev01;
    }
    if ( Lev10 < LevCur || (Lev10 == LevCur && pCut10[0] < pCutRes[0]) )
    {
        pCutRes = pCut10;
        LevCur  = Lev10;
    }
    if ( Lev00 < LevCur || (Lev00 == LevCur && pCut00[0] < pCutRes[0]) )
    {
        pCutRes = pCut00;
        LevCur  = Lev00;
    }
    assert( iFan0 != iFan1 );
    assert( Vec_IntEntry(p->vLutLevs, Node) == 0 );
    Vec_IntWriteEntry( p->vLutLevs, Node, LevCur );
    //Vec_IntWriteEntry( p->vLevs, Node, 1+Abc_MaxInt(Vec_IntEntry(p->vLevs, iFan0), Vec_IntEntry(p->vLevs, iFan1)) );
    assert( pCutRes[0] <= p->pPars->nLutSize );
    memcpy( Sbd_ObjCut(p, Node), pCutRes, sizeof(int) * (pCutRes[0] + 1) );
//printf( "Setting node %d with delay %d.\n", Node, LevCur );
    return LevCur == 1; // LevCur == Abc_MaxInt(Level0, Level1);
}
int Sbd_ManDelay( Sbd_Man_t * p )
{
    int i, Id, Delay = 0;
    Gia_ManForEachCoDriverId( p->pGia, Id, i )
        Delay = Abc_MaxInt( Delay, Vec_IntEntry(p->vLutLevs, Id) );
    return Delay;
}
void Sbd_ManMergeTest( Sbd_Man_t * p )
{
    int Node;
    Gia_ManForEachAndId( p->pGia, Node )
        Sbd_ManMergeCuts( p, Node );
    printf( "Delay %d.\n", Sbd_ManDelay(p) );
}

void Sbd_ManFindCut_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( pObj->fMark1 )
        return;
    pObj->fMark1 = 1;
    if ( pObj->fMark0 )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Sbd_ManFindCut_rec( p, Gia_ObjFanin0(pObj) );
    Sbd_ManFindCut_rec( p, Gia_ObjFanin1(pObj) );
}
void Sbd_ManFindCutUnmark_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( !pObj->fMark1 )
        return;
    pObj->fMark1 = 0;
    if ( pObj->fMark0 )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Sbd_ManFindCutUnmark_rec( p, Gia_ObjFanin0(pObj) );
    Sbd_ManFindCutUnmark_rec( p, Gia_ObjFanin1(pObj) );
}
void Sbd_ManFindCut( Sbd_Man_t * p, int Node, Vec_Int_t * vCutLits )
{
    int pCut[SBD_MAX_LUTSIZE+1];     
    int i, LevelMax = 0;
    // label reachable nodes 
    Gia_Obj_t * pTemp, * pObj = Gia_ManObj(p->pGia, Node);
    Sbd_ManFindCut_rec( p->pGia, pObj );
    // collect 
    pCut[0] = 0;
    Gia_ManForEachObjVec( vCutLits, p->pGia, pTemp, i )
        if ( pTemp->fMark1 )
        {
            LevelMax = Abc_MaxInt( LevelMax, Vec_IntEntry(p->vLutLevs, Gia_ObjId(p->pGia, pTemp)) );
            pCut[1+pCut[0]++] = Gia_ObjId(p->pGia, pTemp);
        }
    assert( pCut[0] <= p->pPars->nLutSize );
    // unlabel reachable nodes
    Sbd_ManFindCutUnmark_rec( p->pGia, pObj );
    // create cut
    assert( Vec_IntEntry(p->vLutLevs, Node) == 0 );
    Vec_IntWriteEntry( p->vLutLevs, Node, LevelMax+1 );
    //Vec_IntWriteEntry( p->vLevs, Node, 1+Abc_MaxInt(Vec_IntEntry(p->vLevs, Gia_ObjFaninId0(pObj, Node)), Vec_IntEntry(p->vLevs, Gia_ObjFaninId1(pObj, Node))) );
    memcpy( Sbd_ObjCut(p, Node), pCut, sizeof(int) * (pCut[0] + 1) );
}

int Sbd_ManImplement( Sbd_Man_t * p, int Pivot, word Truth )
{
    Gia_Obj_t * pObj;
    int i, k, w, iLit, Entry, Node;
    int iObjLast = Gia_ManObjNum(p->pGia);
    int iCurLev = Vec_IntEntry(p->vLutLevs, Pivot);
    (void)iCurLev;
    int iNewLev;
    // collect leaf literals
    Vec_IntClear( p->vLits );
    Vec_IntForEachEntry( p->vDivSet, Node, i )
    {
        Node = Vec_IntEntry( p->vWinObjs, Node );
        if ( Vec_IntEntry(p->vMirrors, Node) >= 0 )
            Vec_IntPush( p->vLits, Vec_IntEntry(p->vMirrors, Node) );
        else
            Vec_IntPush( p->vLits, Abc_Var2Lit(Node, 0) );
    }
    // pretend to have MUXes
//    assert( p->pGia->pMuxes == NULL );
    if ( p->pGia->nXors && p->pGia->pMuxes == NULL )
        p->pGia->pMuxes = (unsigned *)p;
    // derive new function of the node
    iLit = Dsm_ManTruthToGia( p->pGia, &Truth, p->vLits, p->vCover );
    if ( p->pGia->pMuxes == (unsigned *)p )
        p->pGia->pMuxes = NULL;
    // remember this function
    assert( Vec_IntEntry(p->vMirrors, Pivot) == -1 );
    Vec_IntWriteEntry( p->vMirrors, Pivot, iLit );
    if ( p->pPars->fVerbose )
        printf( "Replacing node %d by literal %d.\n", Pivot, iLit );
    // translate literals into variables
    Vec_IntForEachEntry( p->vLits, Entry, i )
        Vec_IntWriteEntry( p->vLits, i, Abc_Lit2Var(Entry) );
    // label inputs
    Gia_ManForEachObjVec( p->vLits, p->pGia, pObj, i )
        pObj->fMark0 = 1;
    // extend data-structure to accommodate new nodes
    assert( Vec_IntSize(p->vLutLevs) == iObjLast );
    for ( i = iObjLast; i < Gia_ManObjNum(p->pGia); i++ )
    {
        Vec_IntPush( p->vLutLevs, 0 );
        Vec_IntPush( p->vObj2Var, 0 );
        Vec_IntPush( p->vMirrors, -1 );
        Vec_IntFillExtra( p->vLutCuts, Vec_IntSize(p->vLutCuts) + p->pPars->nLutSize + 1, 0 );
        Sbd_ManFindCut( p, i, p->vLits );
        for ( k = 0; k < 4; k++ )
            for ( w = 0; w < p->pPars->nWords; w++ )
                Vec_WrdPush( p->vSims[k], 0 );
    }
    // unlabel inputs
    Gia_ManForEachObjVec( p->vLits, p->pGia, pObj, i )
        pObj->fMark0 = 0;
    // make sure delay reduction is achieved
    iNewLev = Vec_IntEntry( p->vLutLevs, Abc_Lit2Var(iLit) );
    assert( iNewLev < iCurLev );
    // update delay of the initial node
    assert( Vec_IntEntry(p->vLutLevs, Pivot) == iCurLev );
    Vec_IntWriteEntry( p->vLutLevs, Pivot, iNewLev );
    //Vec_IntWriteEntry( p->vLevs, Pivot, 1+Abc_MaxInt(Vec_IntEntry(p->vLevs, Gia_ObjFaninId0(pObj, Pivot)), Vec_IntEntry(p->vLevs, Gia_ObjFaninId1(pObj, Pivot))) );
    return 0;
}

int Sbd_ManImplement2( Sbd_Man_t * p, int Pivot, int nStrs, Sbd_Str_t * pStrs )
{
    //Gia_Obj_t * pObj = NULL;
    int i, k, w, iLit, Node;
    int iObjLast = Gia_ManObjNum(p->pGia);
    int iCurLev = Vec_IntEntry(p->vLutLevs, Pivot);
    (void)iCurLev;
    int iNewLev;
    // collect leaf literals
    Vec_IntClear( p->vLits );
    Vec_IntForEachEntry( p->vDivSet, Node, i )
    {
        Node = Vec_IntEntry( p->vWinObjs, Node );
        if ( Vec_IntEntry(p->vMirrors, Node) >= 0 )
            Vec_IntPush( p->vLits, Vec_IntEntry(p->vMirrors, Node) );
        else
            Vec_IntPush( p->vLits, Abc_Var2Lit(Node, 0) );
    }
    // collect structure nodes
    for ( i = 0; i < nStrs; i++ )
        Vec_IntPush( p->vLits, -1 );
    // implement structures
    for ( i = nStrs-1; i >= 0; i-- )
    {
        if ( pStrs[i].fLut )
        {
            // collect local literals
            Vec_IntClear( p->vLits2 );
            for ( k = 0; k < (int)pStrs[i].nVarIns; k++ )
                Vec_IntPush( p->vLits2, Vec_IntEntry(p->vLits, pStrs[i].VarIns[k]) );
            // pretend to have MUXes
        //    assert( p->pGia->pMuxes == NULL );
            if ( p->pGia->nXors && p->pGia->pMuxes == NULL )
                p->pGia->pMuxes = (unsigned *)p;
            // derive new function of the node
            iLit = Dsm_ManTruthToGia( p->pGia, &pStrs[i].Res, p->vLits2, p->vCover );
            if ( p->pGia->pMuxes == (unsigned *)p )
                p->pGia->pMuxes = NULL;
        }
        else
        {
            iLit = Vec_IntEntry( p->vLits, (int)pStrs[i].Res );
            assert( iLit > 0 );
        }
        // update literal
        assert( Vec_IntEntry(p->vLits, Vec_IntSize(p->vLits)-nStrs+i) == -1 );
        Vec_IntWriteEntry( p->vLits, Vec_IntSize(p->vLits)-nStrs+i, iLit );
    }
    iLit = Vec_IntEntry( p->vLits, Vec_IntSize(p->vDivSet) );
    //assert( iObjLast == Gia_ManObjNum(p->pGia) || Abc_Lit2Var(iLit) == Gia_ManObjNum(p->pGia)-1 );
    // remember this function
    assert( Vec_IntEntry(p->vMirrors, Pivot) == -1 );
    Vec_IntWriteEntry( p->vMirrors, Pivot, iLit );
    if ( p->pPars->fVeryVerbose )
        printf( "Replacing node %d by literal %d.\n", Pivot, iLit );

    // extend data-structure to accommodate new nodes
    assert( Vec_IntSize(p->vLutLevs) == iObjLast );
    for ( i = iObjLast; i < Gia_ManObjNum(p->pGia); i++ )
    {
        assert( i == Vec_IntSize(p->vMirrors) );
        Vec_IntPush( p->vMirrors, -1 );
        Sbd_StoRefObj( p->pSto, i, -1 );
    }
    for ( i = iObjLast; i < Gia_ManObjNum(p->pGia); i++ )
    {
        //Gia_Obj_t * pObjI = Gia_ManObj( p->pGia, i );
        abctime clk = Abc_Clock();
        int Delay = Sbd_StoComputeCutsNode( p->pSto, i );
        p->timeCut += Abc_Clock() - clk;
        assert( i == Vec_IntSize(p->vLutLevs) );
        Vec_IntPush( p->vLutLevs, Delay );
        //Vec_IntPush( p->vLevs, 1+Abc_MaxInt(Vec_IntEntry(p->vLevs, Gia_ObjFaninId0(pObjI, i)), Vec_IntEntry(p->vLevs, Gia_ObjFaninId1(pObjI, i))) );
        Vec_IntPush( p->vObj2Var, 0 );
        Vec_IntFillExtra( p->vLutCuts, Vec_IntSize(p->vLutCuts) + p->pPars->nLutSize + 1, 0 );
        Sbd_StoSaveBestDelayCut( p->pSto, i, Sbd_ObjCut(p, i) );
        //Sbd_ManFindCut( p, i, p->vLits );
        for ( k = 0; k < 4; k++ )
            for ( w = 0; w < p->pPars->nWords; w++ )
                Vec_WrdPush( p->vSims[k], 0 );
    }
    // make sure delay reduction is achieved
    iNewLev = Vec_IntEntry( p->vLutLevs, Abc_Lit2Var(iLit) );
    // Bounded cut enumeration may miss the synthesized LUT structure.
    // Keep the original pivot if its implementation did not realize the gain.
    if ( iNewLev && iNewLev >= iCurLev )
    {
        Vec_IntWriteEntry( p->vMirrors, Pivot, -1 );
        return 0;
    }
    // Trial nodes remain until cleanup, but only an accepted root takes the refs.
    if ( Gia_ManObjNum(p->pGia) > iObjLast )
        Sbd_StoTransferRefs( p->pSto, Gia_ManObjNum(p->pGia)-1, Pivot );
    Sbd_StoDerefObj( p->pSto, Pivot );
    // update delay of the initial node
    //pObj = Gia_ManObj( p->pGia, Pivot );
    assert( Vec_IntEntry(p->vLutLevs, Pivot) == iCurLev );
    Vec_IntWriteEntry( p->vLutLevs, Pivot, iNewLev );
    //Vec_IntWriteEntry( p->vLevs, Pivot, Pivot ? 1+Abc_MaxInt(Vec_IntEntry(p->vLevs, Gia_ObjFaninId0(pObj, Pivot)), Vec_IntEntry(p->vLevs, Gia_ObjFaninId1(pObj, Pivot))) : 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Derives new AIG after resynthesis.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sbd_ManDeriveMapping_rec( Sbd_Man_t * p, Gia_Man_t * pNew, int iObj )
{
    Gia_Obj_t * pObj; int k, * pCut;
    if ( !iObj || Gia_ObjIsTravIdCurrentId(pNew, iObj) )
        return;
    Gia_ObjSetTravIdCurrentId(pNew, iObj);
    pObj = Gia_ManObj( pNew, iObj );
    if ( Gia_ObjIsCi(pObj) )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    pCut = Sbd_ObjCut2( p, iObj );
    for ( k = 1; k <= pCut[0]; k++ )
        Sbd_ManDeriveMapping_rec( p, pNew, pCut[k] );
    // add mapping
    Vec_IntWriteEntry( pNew->vMapping, iObj, Vec_IntSize(pNew->vMapping) );
    for ( k = 0; k <= pCut[0]; k++ )
        Vec_IntPush( pNew->vMapping, pCut[k] );
    Vec_IntPush( pNew->vMapping, iObj );
}
void Sbd_ManDeriveMapping( Sbd_Man_t * p, Gia_Man_t * pNew )
{
    Gia_Obj_t * pObj, * pFan; 
    int i, k, iFan, iObjNew, iFanNew, * pCut, * pCutNew;
    Vec_Int_t * vLeaves = Vec_IntAlloc( 100 );
    // derive cuts for the new manager
    p->vLutCuts2 = Vec_IntStart( Gia_ManObjNum(pNew) * (p->pPars->nLutSize + 1) );
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        if ( Vec_IntEntry(p->vMirrors, i) >= 0 )
            continue;
        if ( pObj->Value == ~0 )
            continue;
        iObjNew = Abc_Lit2Var( pObj->Value );
        if ( !Gia_ObjIsAnd(Gia_ManObj(pNew, iObjNew)) )
            continue;
        pCutNew = Sbd_ObjCut2( p, iObjNew );
        pCut    = Sbd_ObjCut( p, i );
        Vec_IntClear( vLeaves );
        for ( k = 1; k <= pCut[0]; k++ )
        {
            iFan = Vec_IntEntry(p->vMirrors, pCut[k]) >= 0 ? Abc_Lit2Var(Vec_IntEntry(p->vMirrors, pCut[k])) : pCut[k];
            pFan = Gia_ManObj( p->pGia, iFan );
            if ( pFan->Value == ~0 )
                continue;
            iFanNew = Abc_Lit2Var( pFan->Value );
            // A collapsed node must not overwrite the cut of its surviving fanin.
            if ( iFanNew == iObjNew )
                break;
            if ( iFanNew == 0 )
                continue;
            Vec_IntPushUniqueOrder( vLeaves, iFanNew );
        }
        if ( k <= pCut[0] )
            continue;
        assert( Vec_IntSize(vLeaves) <= p->pPars->nLutSize );
        //assert( Vec_IntSize(vLeaves) > 1 );
        pCutNew[0] = Vec_IntSize(vLeaves);
        memcpy( pCutNew+1, Vec_IntArray(vLeaves), sizeof(int) * Vec_IntSize(vLeaves) );
    }
    Vec_IntFree( vLeaves );
    // create new mapping
    Vec_IntFreeP( &pNew->vMapping );
    pNew->vMapping = Vec_IntAlloc( (p->pPars->nLutSize + 2) * Gia_ManObjNum(pNew) );
    Vec_IntFill( pNew->vMapping, Gia_ManObjNum(pNew), 0 );
    Gia_ManIncrementTravId( pNew );
    Gia_ManForEachCo( pNew, pObj, i )
        Sbd_ManDeriveMapping_rec( p, pNew, Gia_ObjFaninId0p(pNew, pObj) );
    Vec_IntFreeP( &p->vLutCuts2 );
}
void Sbd_ManDerive_rec( Gia_Man_t * pNew, Gia_Man_t * p, int Node, Vec_Int_t * vMirrors )
{
    Gia_Obj_t * pObj;
    int Obj = Node;
    if ( Vec_IntEntry(vMirrors, Node) >= 0 )
        Obj = Abc_Lit2Var( Vec_IntEntry(vMirrors, Node) );
    pObj = Gia_ManObj( p, Obj );
    if ( !~pObj->Value )
    {
        assert( Gia_ObjIsAnd(pObj) );
        Sbd_ManDerive_rec( pNew, p, Gia_ObjFaninId0(pObj, Obj), vMirrors );
        Sbd_ManDerive_rec( pNew, p, Gia_ObjFaninId1(pObj, Obj), vMirrors );
        if ( Gia_ObjIsXor(pObj) )
            pObj->Value = Gia_ManHashXorReal( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    // set the original node as well
    if ( Obj != Node )
        Gia_ManObj(p, Node)->Value = Abc_LitNotCond( pObj->Value, Abc_LitIsCompl(Vec_IntEntry(vMirrors, Node)) );
} 
Gia_Man_t * Sbd_ManDerive( Sbd_Man_t * pMan, Gia_Man_t * p, Vec_Int_t * vMirrors )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    if ( p->pMuxes )
        pNew->pMuxes = ABC_CALLOC( unsigned, Gia_ManObjNum(p) );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachCo( p, pObj, i )
        Sbd_ManDerive_rec( pNew, p, Gia_ObjFaninId0p(p, pObj), vMirrors );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Gia_ManTransferTiming( pNew, p );
    if ( pMan->pPars->fMapping )
        Sbd_ManDeriveMapping( pMan, pNew );
    // remove dangling nodes
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManTransferTiming( pNew, pTemp );
    Gia_ManTransferMapping( pNew, pTemp );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Performs delay optimization for the given LUT size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sbd_NtkPerformOne( Sbd_Man_t * p, int Pivot )
{
    Sbd_Str_t Strs[SBD_DIV_MAX]; word Truth = 0;
    int RetValue, nStrs = 0, Counts[6];
    p->fAcdFound = 0;
    if ( !p->pSto && Sbd_ManMergeCuts( p, Pivot ) )
        return;
    if ( !Sbd_ManWindow( p, Pivot ) )
        return;
    //if ( Vec_IntSize(p->vWinObjs) > 100 )
    //    printf( "Obj %d : Win = %d   TFO = %d.  Roots = %d.\n", Pivot, Vec_IntSize(p->vWinObjs), Vec_IntSize(p->vTfo), Vec_IntSize(p->vRoots) );
    p->nTried++;
    p->nUsed++;
    RetValue = p->fRevisit ? -1 : Sbd_ManCheckConst( p, Pivot );
    if ( RetValue == -2 )
    {
        p->nUsed--;
        return;
    }
    if ( RetValue >= 0 )
    {
        Vec_IntWriteEntry( p->vMirrors, Pivot, RetValue );
        //if ( p->pPars->fVerbose ) printf( "Node %5d:  Detected constant %d.\n", Pivot, RetValue );
        return;
    }
    memcpy( Counts, p->nLuts, sizeof(Counts) );
    if ( !p->fRevisit && p->pPars->fFindDivs && Sbd_ManExplore2( p, Pivot, &Truth ) )
    {
        int i;
        Strs->fLut = 1;
        Strs->nVarIns = Vec_IntSize( p->vDivSet );
        for ( i = 0; i < Strs->nVarIns; i++ )
            Strs->VarIns[i] = i;
        Strs->Res = Truth;
        RetValue = Sbd_ManImplement2( p, Pivot, 1, Strs );
        //if ( p->pPars->fVerbose ) printf( "Node %5d:  Detected LUT%d\n", Pivot, p->pPars->nLutSize );
    }
    else if ( Sbd_ManExplore3( p, Pivot, &nStrs, Strs ) )
        RetValue = Sbd_ManImplement2( p, Pivot, nStrs, Strs );
    else
        RetValue = 0;
    if ( RetValue && p->fAcdFound )
        p->nAcdUsed++;
    if ( !RetValue )
    {
        p->nUsed--;
        memcpy( p->nLuts, Counts, sizeof(Counts) );
    }
}
/**Function*************************************************************

  Synopsis    [Copies box attributes without consuming the input manager.]

  Description [Every transformation preserves the complete box interface.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Sbd_ManCopyBoxes( Gia_Man_t * pNew, Gia_Man_t * p )
{
    if ( p->pManTime == NULL )
        return;
    assert( pNew->pManTime == NULL && pNew->pAigExtra == NULL );
    pNew->pManTime = Tim_ManDup( (Tim_Man_t *)p->pManTime, 0 );
    if ( p->pAigExtra )
        pNew->pAigExtra = Gia_ManDup( p->pAigExtra );
    if ( p->vRegClasses )
        pNew->vRegClasses = Vec_IntDup( p->vRegClasses );
    if ( p->vRegInits )
        pNew->vRegInits = Vec_IntDup( p->vRegInits );
    if ( p->vFlopClasses )
        pNew->vFlopClasses = Vec_IntDup( p->vFlopClasses );
    pNew->nAnd2Delay = p->nAnd2Delay;
}

/**Function*************************************************************

  Synopsis    [Returns LUT depth including unit delays through boxes.]

  Description [Register inputs and outputs are combinational boundaries.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Sbd_ManLutLevel( Gia_Man_t * p )
{
    int nRegs, nLevel;
    if ( Gia_ManBoxNum(p) == 0 )
        return Gia_ManLutLevel( p, NULL );
    nRegs = p->nRegs;
    p->nRegs = 0;
    nLevel = Gia_ManLutLevelWithBoxes( p );
    p->nRegs = nRegs;
    return nLevel;
}

/**Function*************************************************************

  Synopsis    [Checks physical box order and removes incompatible choices.]

  Description [A box input may depend only on preceding box outputs. Unlike
  logical support, this condition includes every pin of a multi-output box.
  Choices are checked against the earliest box input in their fanout.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Sbd_ManBoxRank_rec( Gia_Man_t * p, int Id, Vec_Int_t * vRanks )
{
    Gia_Obj_t * pObj = Gia_ManObj(p, Id);
    int i, iFan, Rank = Vec_IntEntry(vRanks, Id);
    if ( Rank >= 0 )
        return Rank;
    if ( Rank == -2 )
        return ABC_INFINITY;
    Vec_IntWriteEntry( vRanks, Id, -2 );
    Rank = 0;
    if ( Gia_ObjIsLut(p, Id) )
    {
        Gia_LutForEachFanin( p, Id, iFan, i )
            Rank = Abc_MaxInt( Rank, Sbd_ManBoxRank_rec(p, iFan, vRanks) );
    }
    else
    {
        assert( Gia_ObjIsAnd(pObj) );
        Rank = Abc_MaxInt( Sbd_ManBoxRank_rec(p, Gia_ObjFaninId0p(p, pObj), vRanks),
                          Sbd_ManBoxRank_rec(p, Gia_ObjFaninId1p(p, pObj), vRanks) );
    }
    Vec_IntWriteEntry( vRanks, Id, Rank );
    return Rank;
}
static int Sbd_ManCheckBoxOrder( Gia_Man_t * p )
{
    Tim_Man_t * pTim = (Tim_Man_t *)p->pManTime;
    Vec_Int_t * vRanks, * vLimits;
    Gia_Obj_t * pObj;
    int i, k, Id, Rank, iSibl, fValid = 1, nBoxes = Gia_ManBoxNum(p);
    if ( nBoxes == 0 )
        return 1;
    vRanks = Vec_IntStart( Gia_ManObjNum(p) );
    vLimits = Vec_IntStartFull( Gia_ManObjNum(p) );
    Vec_IntFill( vLimits, Gia_ManObjNum(p), nBoxes + 1 );
    for ( i = 0; i < nBoxes; i++ )
    {
        for ( k = 0; k < Tim_ManBoxOutputNum(pTim, i); k++ )
            Vec_IntWriteEntry( vRanks, Gia_ObjId(p, Gia_ManCi(p, Tim_ManBoxOutputFirst(pTim, i) + k)), i + 1 );
        for ( k = 0; k < Tim_ManBoxInputNum(pTim, i); k++ )
        {
            Id = Gia_ObjFaninId0p( p, Gia_ManCo(p, Tim_ManBoxInputFirst(pTim, i) + k) );
            Vec_IntWriteEntry( vLimits, Id, Abc_MinInt(Vec_IntEntry(vLimits, Id), i + 1) );
        }
    }
    Gia_ManForEachAndReverse( p, pObj, Id )
    {
        Rank = Vec_IntEntry( vLimits, Id );
        i = Gia_ObjFaninId0p( p, pObj );
        k = Gia_ObjFaninId1p( p, pObj );
        Vec_IntWriteEntry( vLimits, i, Abc_MinInt(Vec_IntEntry(vLimits, i), Rank) );
        Vec_IntWriteEntry( vLimits, k, Abc_MinInt(Vec_IntEntry(vLimits, k), Rank) );
    }
    Gia_ManForEachAnd( p, pObj, Id )
    {
        Rank = Abc_MaxInt( Vec_IntEntry(vRanks, Gia_ObjFaninId0p(p, pObj)),
                          Vec_IntEntry(vRanks, Gia_ObjFaninId1p(p, pObj)) );
        iSibl = Gia_ObjSibl( p, Id );
        if ( iSibl )
        {
            assert( iSibl < Id );
            if ( Vec_IntEntry(vRanks, iSibl) >= Vec_IntEntry(vLimits, Id) )
                p->pSibls[Id] = 0;
            else
                Rank = Abc_MaxInt( Rank, Vec_IntEntry(vRanks, iSibl) );
        }
        Vec_IntWriteEntry( vRanks, Id, Rank );
    }
    for ( i = 0; i < nBoxes && fValid; i++ )
        for ( k = 0; k < Tim_ManBoxInputNum(pTim, i); k++ )
        {
            Id = Gia_ObjFaninId0p( p, Gia_ManCo(p, Tim_ManBoxInputFirst(pTim, i) + k) );
            if ( Vec_IntEntry(vRanks, Id) >= i + 1 )
                fValid = 0;
        }
    if ( fValid && Gia_ManHasMapping(p) )
    {
        // LUT pins can contain dependencies absent from the AIG support.
        // Check the physical mapping as well as the underlying AIG.
        Vec_IntFill( vRanks, Gia_ManObjNum(p), -1 );
        Vec_IntWriteEntry( vRanks, 0, 0 );
        Gia_ManForEachCiId( p, Id, i )
            Vec_IntWriteEntry( vRanks, Id, 0 );
        for ( i = 0; i < nBoxes; i++ )
            for ( k = 0; k < Tim_ManBoxOutputNum(pTim, i); k++ )
                Vec_IntWriteEntry( vRanks, Gia_ObjId(p, Gia_ManCi(p, Tim_ManBoxOutputFirst(pTim, i) + k)), i + 1 );
        for ( i = 0; i < nBoxes && fValid; i++ )
            for ( k = 0; k < Tim_ManBoxInputNum(pTim, i); k++ )
            {
                Id = Gia_ObjFaninId0p( p, Gia_ManCo(p, Tim_ManBoxInputFirst(pTim, i) + k) );
                if ( Sbd_ManBoxRank_rec(p, Id, vRanks) >= i + 1 )
                    fValid = 0;
            }
    }
    Vec_IntFree( vRanks );
    Vec_IntFree( vLimits );
    return fValid;
}

/**Function*************************************************************

  Synopsis    [Remaps with IF under an optional unit-delay bound.]

  Description [Remapping may miss a synthesized cut.  Accept its result
  only after checking the actual LUT depth and area.  Retry with more
  priority cuts when the first mapping misses the depth target. Optional
  structural choices are computed once and retained for the retry.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Sbd_ManRecoverArea( Gia_Man_t * pGia, Sbd_Par_t * pPars, int nLevel, int fChoices )
{
    Gia_Man_t * pWork, * pNew, * pChoices = NULL;
    If_Par_t Pars;
    int i, nLutSize = pPars->nLutSize, fVerbose = pPars->fVerbose;
    int nLuts = Gia_ManLutNum(pGia);
    abctime clk = fChoices && fVerbose ? Abc_Clock() : 0;
    if ( nLuts == 0 )
        return pGia;
    if ( fChoices )
    {
        Dch_Pars_t DchPars;
        int nRegs = Gia_ManRegNum(pGia);
        Dch_ManSetDefaultParams( &DchPars );
        DchPars.fLightSynth = 1;
        // Bound choice recovery independently of the SAT/QBF delay search.
        DchPars.nBTLimit = pPars->nBTLimitDch;
        if ( pPars->nBTLimit && (!DchPars.nBTLimit || pPars->nBTLimit < DchPars.nBTLimit) )
            DchPars.nBTLimit = pPars->nBTLimit;
        pWork = Gia_ManCleanup( pGia );
        // Compute combinational choices across all register boundaries.
        pWork->nRegs = 0;
        pChoices = Gia_ManPerformDch( pWork, &DchPars );
        Gia_ManStop( pWork );
        if ( pChoices == NULL )
            return pGia;
        Gia_ManSetRegNum( pChoices, nRegs );
        Sbd_ManCopyBoxes( pChoices, pGia );
        if ( !Sbd_ManCheckBoxOrder(pChoices) )
        {
            Gia_ManStop( pChoices );
            return pGia;
        }
    }
    // SAT resubstitution can leave dangling AIG nodes; prepare IF's input once.
    pWork = pChoices ? Gia_ManDup(pChoices) : Gia_ManCleanup(pGia);
    for ( i = 0; i < 2; i++ )
    {
        // Mapping transfers timing to its result, so the retry needs a new copy.
        if ( pWork->pManTime == NULL )
            Sbd_ManCopyBoxes( pWork, pGia );
        If_ManSetDefaultPars( &Pars );
        Pars.nLutSize = nLutSize;
        Pars.DelayTarget = (float)nLevel;
        Pars.fArea = nLevel < 0;
        Pars.fNoDelayWarn = 1;
        if ( i )
            Pars.nCutsMax = 32;
        pNew = Gia_ManPerformMapping( pWork, &Pars );
        if ( pNew && Sbd_ManCheckBoxOrder(pNew) && (nLevel < 0 || Sbd_ManLutLevel(pNew) <= nLevel) )
        {
            if ( Gia_ManLutNum(pNew) < nLuts )
            {
                if ( pNew->pManTime == NULL )
                    Gia_ManTransferTiming( pNew, pGia );
                Gia_ManStop( pGia );
                pGia = pNew;
            }
            else
                Gia_ManStop( pNew );
            break;
        }
        if ( pNew )
            Gia_ManStop( pNew );
        if ( fVerbose )
            Abc_Print( 1, "IF remapping with %d cuts missed depth %d; %s.\n", Pars.nCutsMax, nLevel,
                i ? "retaining the optimized mapping" : "retrying with 32 cuts" );
    }
    Gia_ManStop( pWork );
    if ( pChoices )
        Gia_ManStop( pChoices );
    if ( fChoices && fVerbose )
    {
        Abc_Print( 1, "Choice recovery: LUTs %d -> %d. Depth bound %d, result %d. ",
            nLuts, Gia_ManLutNum(pGia), nLevel, Sbd_ManLutLevel(pGia) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Performs delay optimization and guarded IF area recovery.]

  Description [The initial pass uses SAT/QBF and ACD. A revisit uses only
  structural truth tables and ACD to limit the cost of refreshing the
  critical region. The input mapping remains the fallback in both cases.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Sbd_NtkPerformDelay( Gia_Man_t * pGia, Sbd_Par_t * pPars, int fRevisit )
{
    Gia_Man_t * pNew, * pBest = NULL;
    Gia_Obj_t * pObj;
    Vec_Bit_t * vPath;
    Sbd_Man_t * p;
    int nNodesOld = Gia_ManObjNum(pGia);
    int fUsePath = pPars->fUsePath > 0 || (pPars->fUsePath < 0 && Gia_ManHasMapping(pGia) && Gia_ManLutSizeMax(pGia) <= pPars->nLutSize);
    int fRecover = pPars->fMapping && !pGia->vCiArrs && !pGia->vCoReqs && !pGia->nXors;
    int k, Pivot;
    // Retain a compatible input mapping when restructuring does not improve it.
    if ( fRecover && Gia_ManHasMapping(pGia) && Gia_ManLutSizeMax(pGia) <= pPars->nLutSize )
    {
        pBest = Gia_ManDup( pGia );
        pBest->vMapping = Vec_IntDup( pGia->vMapping );
        Sbd_ManCopyBoxes( pBest, pGia );
    }
    p = Sbd_ManStart( pGia, pPars );
    p->fRevisit = fRevisit;
    assert( pPars->nLutSize <= 6 );
    // prepare references
    Gia_ManForEachObj( p->pGia, pObj, Pivot )
        Sbd_StoRefObj( p->pSto, Pivot, -1 );
    //return NULL;
    vPath = (fUsePath && Gia_ManHasMapping(pGia)) ? Sbc_ManCriticalPath(pGia) : NULL;
    if ( pGia->pManTime != NULL && Tim_ManBoxNum((Tim_Man_t*)pGia->pManTime) )
    {
        Vec_Int_t * vNodes = Gia_ManOrderWithBoxes( pGia );
        Tim_Man_t * pTimOld = (Tim_Man_t *)pGia->pManTime;
        if ( vNodes == NULL )
        {
            Vec_BitFreeP( &vPath );
            Sbd_ManStop( p );
            return pBest;
        }
        pGia->pManTime = Tim_ManDup( pTimOld, 1 );
        //Tim_ManPrint( pGia->pManTime );
        Tim_ManIncrementTravId( (Tim_Man_t *)pGia->pManTime );
        Gia_ManForEachObjVec( vNodes, pGia, pObj, k )
        {
            Pivot = Gia_ObjId( pGia, pObj );
            if ( Pivot >= nNodesOld )
                break;
            if ( Gia_ObjIsAnd(pObj) )
            {
                abctime clk = Abc_Clock();
                int Delay = Sbd_StoComputeCutsNode( p->pSto, Pivot );
                Sbd_StoSaveBestDelayCut( p->pSto, Pivot, Sbd_ObjCut(p, Pivot) );
                p->timeCut += Abc_Clock() - clk;
                Vec_IntWriteEntry( p->vLutLevs, Pivot, Delay );
                if ( Delay > 1 && (!vPath || Vec_BitEntry(vPath, Pivot)) )
                    Sbd_NtkPerformOne( p, Pivot );
            }
            else if ( Gia_ObjIsCi(pObj) )
            {
                int arrTime = Tim_ManGetCiArrival( (Tim_Man_t*)pGia->pManTime, Gia_ObjCioId(pObj) );
                Vec_IntWriteEntry( p->vLutLevs, Pivot, arrTime );
                Sbd_StoComputeCutsCi( p->pSto, Pivot, arrTime, arrTime );
            }
            else if ( Gia_ObjIsCo(pObj) )
            {
                int arrTime = Vec_IntEntry( p->vLutLevs, Gia_ObjFaninId0(pObj, Pivot) );
                Tim_ManSetCoArrival( (Tim_Man_t*)pGia->pManTime, Gia_ObjCioId(pObj), arrTime );
            }
            else if ( Gia_ObjIsConst0(pObj) )
                Sbd_StoComputeCutsConst0( p->pSto, 0 );
            else assert( 0 );
        }
        Tim_ManStop( (Tim_Man_t *)pGia->pManTime );
        pGia->pManTime = pTimOld;
        Vec_IntFree( vNodes );
    }
    else
    {
        Sbd_StoComputeCutsConst0( p->pSto, 0 );
        Gia_ManForEachObj( pGia, pObj, Pivot )
        {
            if ( Pivot >= nNodesOld )
                break;
            if ( Gia_ObjIsCi(pObj) )
                Sbd_StoComputeCutsCi( p->pSto, Pivot, 0, 0 );
            else if ( Gia_ObjIsAnd(pObj) )
            {
                abctime clk = Abc_Clock();
                int Delay = Sbd_StoComputeCutsNode( p->pSto, Pivot );
                Sbd_StoSaveBestDelayCut( p->pSto, Pivot, Sbd_ObjCut(p, Pivot) );
                p->timeCut += Abc_Clock() - clk;
                Vec_IntWriteEntry( p->vLutLevs, Pivot, Delay );
                if ( Delay > 1 && (!vPath || Vec_BitEntry(vPath, Pivot)) )
                    Sbd_NtkPerformOne( p, Pivot );
            }
            //if ( nNodesOld != Gia_ManObjNum(pGia) )
            //    break;
        }
    }
    Vec_BitFreeP( &vPath );
    {
        abctime clk = Abc_Clock();
        pNew = Sbd_ManDerive( p, pGia, p->vMirrors );
        if ( fRecover )
            pNew = Sbd_ManRecoverArea( pNew, pPars, Sbd_ManLutLevel(pNew), 0 );
        if ( pBest )
        {
            int LevelBest = Sbd_ManLutLevel(pBest);
            int LevelNew = Sbd_ManLutLevel(pNew);
            if ( LevelBest < LevelNew || (LevelBest == LevelNew && Gia_ManLutNum(pBest) <= Gia_ManLutNum(pNew)) )
            {
                if ( pBest->pManTime == NULL )
                    Gia_ManTransferTiming( pBest, pNew );
                ABC_SWAP( Gia_Man_t *, pBest, pNew );
            }
            Gia_ManStop( pBest );
        }
        p->timeNew = Abc_Clock() - clk;
    }
    p->timeTotal = Abc_Clock() - p->timeTotal;
    if ( p->pPars->fVerbose )
    {
        printf( "K = %d. S = %d. N = %d. P = %d.  ", 
            p->pPars->nLutSize, p->pPars->nLutNum, p->pPars->nCutSize, p->pPars->nCutNum );
        printf( "Try = %d. Use = %d.  C = %d. 1 = %d. 2 = %d. 3a = %d. 3b = %d.  Lev = %d.  ", 
            p->nTried, p->nUsed, p->nLuts[0], p->nLuts[1], p->nLuts[2], p->nLuts[3], p->nLuts[4], fRecover ? Sbd_ManLutLevel(pNew) : Sbd_ManDelay(p) );
        Abc_PrintTime( 1, "Time", p->timeTotal );
    }
    // print runtime statistics
    p->timeOther = p->timeTotal - p->timeWin - p->timeCut - p->timeCov - p->timeCnf - p->timeSat - p->timeQbf - p->timeAcd - p->timeNew;
    if ( p->pPars->fVerbose )
    {
        ABC_PRTP( "Win", p->timeWin  ,  p->timeTotal );
        ABC_PRTP( "Cut", p->timeCut  ,  p->timeTotal );
        ABC_PRTP( "Cov", p->timeCov  ,  p->timeTotal );
        ABC_PRTP( "Cnf", p->timeCnf  ,  p->timeTotal );
        ABC_PRTP( "Sat", p->timeSat  ,  p->timeTotal );
        printf( "ACD: tried %d, structural %d, solved %d, accepted %d. QBF calls %d.\n",
            p->nAcdTried, p->nAcdTruths, p->nAcdFound, p->nAcdUsed, p->nQbfCalls );
        ABC_PRTP( "Acd", p->timeAcd  ,  p->timeTotal );
        ABC_PRTP( "Qbf", p->timeQbf  ,  p->timeTotal );
        ABC_PRTP( "Map", p->timeNew  ,  p->timeTotal );
        ABC_PRTP( "Oth", p->timeOther,  p->timeTotal );
        ABC_PRTP( "ALL", p->timeTotal,  p->timeTotal );
    }
    Sbd_ManStop( p );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Optimizes LUT area using SAT resubstitution and IF remapping.]

  Description [A negative depth bound selects unconstrained area optimization.
  The SFM engine updates forward and reverse levels during resubstitution.
  Check the reconstructed mapping as well before replacing the incumbent.]

  SideEffects [Consumes pGia and returns the selected mapping.]

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Sbd_ManOptimizeArea( Gia_Man_t * pGia, Sbd_Par_t * pPars, int nLevel )
{
    extern Gia_Man_t * Gia_ManPerformMfs( Gia_Man_t * p, Sfm_Par_t * pPars );
    Gia_Man_t * pNew;
    Sfm_Par_t Pars;
    int nRegs = Gia_ManRegNum(pGia);
    int nLuts = Gia_ManLutNum(pGia);
    int nDepth = Sbd_ManLutLevel(pGia);
    if ( nLuts == 0 )
        return pGia;
    assert( nLevel < 0 || nDepth <= nLevel );
    Sfm_ParSetDefault( &Pars );
    // Redundant-edge removal can expose area savings in later remapping.
    Pars.fArea = pPars->fDelay;
    Pars.fAllBoxes = Gia_ManBoxNum(pGia) > 0;
    Pars.fBoxOrder = Gia_ManBoxNum(pGia) > 0;
    Pars.nTfoLevMax = pPars->nTfoLevels;
    Pars.nFanoutMax = pPars->nTfoFanMax;
    Pars.nWinSizeMax = pPars->nWinSizeMax;
    Pars.nBTLimit = pPars->nBTLimit;
    Pars.nDepthMax = 0;
    // An acyclic path uses each LUT and box at most once.
    Pars.nGrowthLevel = nLevel < 0 ? Abc_MaxInt(0, nLuts + Gia_ManBoxNum(pGia) - nDepth) : nLevel - nDepth;
    Pars.fVerbose = pPars->fVerbose;
    Pars.fVeryVerbose = pPars->fVeryVerbose;
    // Optimize the combinational logic between register boundaries.
    pGia->nRegs = 0;
    pNew = Gia_ManPerformMfs( pGia, &Pars );
    pGia->nRegs = nRegs;
    // MFS transfers box attributes when no nodes change. Restore the input
    // before checking the candidate, so either manager can be discarded.
    if ( pNew && pNew->pManTime && pGia->pManTime == NULL )
    {
        Gia_ManTransferTiming( pGia, pNew );
        Sbd_ManCopyBoxes( pNew, pGia );
    }
    if ( pNew && !Sbd_ManCheckBoxOrder(pNew) )
    {
        if ( pPars->fVerbose )
            Abc_Print( 1, "SAT area recovery violated the box order; retaining the input mapping.\n" );
        Gia_ManStop( pNew );
        pNew = NULL;
    }
    if ( pNew )
    {
        int nLutsNew = Gia_ManLutNum(pNew);
        int nDepthNew = Sbd_ManLutLevel(pNew);
        Gia_ManSetRegNum( pNew, nRegs );
        if ( (nLevel < 0 || nDepthNew <= nLevel) &&
             (nLutsNew < nLuts || (nLutsNew == nLuts && nDepthNew <= nDepth)) )
        {
            Gia_ManStop( pGia );
            pGia = pNew;
        }
        else
        {
            if ( pPars->fVerbose && nLevel >= 0 && nDepthNew > nLevel )
                Abc_Print( 1, "SAT area recovery reached depth %d above bound %d; retaining the input mapping.\n", nDepthNew, nLevel );
            Gia_ManStop( pNew );
        }
    }
    return Sbd_ManRecoverArea( pGia, pPars, nLevel, 0 );
}

/**Function*************************************************************

  Synopsis    [Runs one complete optimization round including area recovery.]

  Description [Parameters are resolved and the input has a LUT mapping.]

  SideEffects [Consumes the input manager.]

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Sbd_NtkPerformRound( Gia_Man_t * pWork, Sbd_Par_t * pPars, Sbd_Par_t * pAreaPars )
{
    Gia_Man_t * pNew;
    int nBound;
    if ( pPars->fDelay )
    {
        int iPass;
        for ( iPass = 0; iPass < 2; iPass++ )
        {
            int nLevelPrev = Sbd_ManLutLevel(pWork);
            if ( pPars->fVerbose )
                Abc_Print( 1, "Delay pass %d (%s): starting at depth %d.\n", iPass + 1,
                    iPass ? "structural revisit" : "SAT/QBF and ACD", nLevelPrev );
            pNew = Sbd_NtkPerformDelay( pWork, pPars, iPass != 0 );
            Gia_ManStop( pWork );
            if ( pNew == NULL )
                return NULL;
            nBound = Sbd_ManLutLevel(pNew);
            pNew = Sbd_ManOptimizeArea( pNew, pPars, nBound );
            if ( nBound >= nLevelPrev || iPass == 1 )
                break;
            // Rebuild cuts and criticality on the changed mapping. This also
            // revisits earlier pivots and the nodes introduced by synthesis.
            pWork = pNew;
        }
    }
    else
    {
        pNew = pWork;
        nBound = pPars->fArea ? -1 : Sbd_ManLutLevel(pNew);
        pNew = Sbd_ManOptimizeArea( pNew, pPars, nBound );
    }
    if ( pPars->fDelay || pPars->fChoices )
    {
        int nLutsPrev;
        nBound = pPars->fArea ? -1 : Sbd_ManLutLevel(pNew);
        pNew = Sbd_ManRecoverArea( pNew, pPars, nBound, 1 );
        nLutsPrev = Gia_ManLutNum(pNew);
        // The choice remap can expose new SAT resubstitutions.
        nBound = pPars->fArea ? -1 : Sbd_ManLutLevel(pNew);
        pNew = Sbd_ManOptimizeArea( pNew, pAreaPars, nBound );
        if ( pPars->fVerbose )
            Abc_Print( 1, "Final area recovery: LUTs %d -> %d. Depth %d.\n",
                nLutsPrev, Gia_ManLutNum(pNew), Sbd_ManLutLevel(pNew) );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Selects bounded area, unconstrained area, or delay optimization.]

  Description [The default preserves the input LUT depth while reducing area.
  Unmapped inputs are first mapped with IF to establish an initial depth.
  Delay mode recovers area after its full SAT/QBF and ACD pass. If the
  delay pass reduced depth, one structural revisit refreshes cuts and
  criticality, followed by area recovery under the new depth bound. A final
  remap with structural choices is accepted only if it saves LUTs within
  the achieved depth bound. One more SAT/IF area pass exploits the changed
  LUT mapping while preserving its depth. This final pass uses the area
  window profile; intermediate passes retain the delay profile to preserve
  the mapping seen by the structural revisit. Area modes can request this extra
  recovery with fChoices. With boxes, depth counts one level
  per box arc and the existing box order is preserved. Box dependency checks
  are disabled for ordinary AIGs. Optional extra delay rounds retain the
  incumbent unless depth improves or equal depth uses fewer LUTs. Stop at
  the first round without improvement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Sbd_NtkPerform( Gia_Man_t * pGia, Sbd_Par_t * pPars )
{
    Gia_Man_t * pWork, * pNew;
    Sbd_Par_t Settings = *pPars, Pars, AreaPars = *pPars;
    int iIter, nLuts, nLevel;
    int nRegsBox = Gia_ManIsSeqWithBoxes(pGia) ? Gia_ManRegNum(pGia) : 0;
    abctime clk = Abc_Clock();
    // Explicit caller settings, including zero limits, apply to both profiles.
    Sbd_ParResolve( &Settings );
    // Use the area profile only after all delay-search passes have finished.
    AreaPars.fDelay = 0;
    Sbd_ParResolve( &AreaPars );
    pPars = &Settings;
    Pars = Settings;
    if ( pGia->vCiArrs || pGia->vCoReqs || pGia->vInArrs || pGia->vOutReqs || pGia->nXors || Gia_ManBufNum(pGia) )
    {
        Abc_Print( -1, "LUT optimization requires an AIG without external timing constraints, explicit XOR nodes, or barrier buffers.\n" );
        return NULL;
    }
    if ( Gia_ManBoxNum(pGia) && (pGia->pAigExtra == NULL || Gia_ManCiNum(pGia->pAigExtra) > 15) )
    {
        Abc_Print( -1, "LUT optimization with boxes requires box functions with at most 15 inputs.\n" );
        return NULL;
    }
    if ( pPars->fArea && pPars->fDelay )
    {
        Abc_Print( -1, "Area-only (-a) and delay (-d) modes cannot be combined.\n" );
        return NULL;
    }
    if ( pPars->nIters < 1 || (pPars->nIters > 1 && !pPars->fDelay) )
    {
        Abc_Print( -1, "The iteration count must be positive; multiple iterations require delay mode (-d).\n" );
        return NULL;
    }
    if ( Gia_ManHasMapping(pGia) && Gia_ManLutSizeMax(pGia) > pPars->nLutSize )
    {
        Abc_Print( -1, "The input mapping has LUTs larger than K; remap with &if -K %d first.\n", pPars->nLutSize );
        return NULL;
    }
    if ( nRegsBox )
    {
        if ( !Gia_ManIsNormalized(pGia) )
        {
            Abc_Print( -1, "LUT optimization with sequential boxes requires a normalized AIG.\n" );
            return NULL;
        }
        // TIM numbers real inputs (including register outputs) before box
        // outputs. Restore this order for the combinational optimization.
        pWork = Gia_ManDupUnshuffleInputs( pGia );
        pWork->nRegs = 0;
        if ( Gia_ManHasMapping(pGia) )
            Gia_ManTransferMapping( pWork, pGia );
    }
    else
        pWork = Gia_ManHasMapping(pGia) ? Gia_ManDup(pGia) : Gia_ManCleanup(pGia);
    Sbd_ManCopyBoxes( pWork, pGia );
    // Unmapped inputs must be checked before IF; mapped inputs are checked below.
    if ( !Gia_ManHasMapping(pGia) && !Sbd_ManCheckBoxOrder(pWork) )
    {
        Abc_Print( -1, "LUT optimization requires boxes in topological order.\n" );
        Gia_ManStop( pWork );
        return NULL;
    }
    if ( pWork->pManTime )
    {
        // Use one level per box arc, matching levB, without changing the
        // input's physical timing tables or interface timing constraints.
        Tim_Man_t * pTim = (Tim_Man_t *)pWork->pManTime;
        pWork->pManTime = Tim_ManDup( pTim, 1 );
        Tim_ManStop( pTim );
        Tim_ManInitPiArrivalAll( (Tim_Man_t *)pWork->pManTime, 0 );
        Tim_ManInitPoRequiredAll( (Tim_Man_t *)pWork->pManTime, (float)TIM_ETERNITY );
    }
    if ( Gia_ManHasMapping(pGia) )
    {
        if ( !nRegsBox )
            pWork->vMapping = Vec_IntDup( pGia->vMapping );
    }
    else
    {
        If_Par_t MapPars;
        If_ManSetDefaultPars( &MapPars );
        MapPars.nLutSize = pPars->nLutSize;
        pNew = Gia_ManPerformMapping( pWork, &MapPars );
        Gia_ManStop( pWork );
        pWork = pNew;
        if ( pWork == NULL )
            return NULL;
    }
    if ( !Sbd_ManCheckBoxOrder(pWork) )
    {
        Abc_Print( -1, "The input LUT mapping violates the box order.\n" );
        Gia_ManStop( pWork );
        return NULL;
    }
    nLuts = Gia_ManLutNum(pWork);
    nLevel = Sbd_ManLutLevel(pWork);
    // All objectives use LUT mapping internally, including when -m is given.
    Pars.fMapping = 1;
    pNew = Sbd_NtkPerformRound( pWork, &Pars, &AreaPars );
    if ( pNew == NULL )
        return NULL;
    for ( iIter = 1; iIter < pPars->nIters; iIter++ )
    {
        int nLutsPrev = Gia_ManLutNum(pNew), nLevelPrev = Sbd_ManLutLevel(pNew);
        int nLutsNew, nLevelNew, fImprove;
        // Preserve the incumbent while the next round restructures its copy.
        pWork = Gia_ManDup( pNew );
        pWork->vMapping = Vec_IntDup( pNew->vMapping );
        Sbd_ManCopyBoxes( pWork, pNew );
        if ( pPars->fVerbose )
            Abc_Print( 1, "Optimization iteration %d of %d.\n", iIter + 1, pPars->nIters );
        pWork = Sbd_NtkPerformRound( pWork, &Pars, &AreaPars );
        if ( pWork == NULL )
            break;
        nLutsNew = Gia_ManLutNum(pWork);
        nLevelNew = Sbd_ManLutLevel(pWork);
        fImprove = nLevelNew < nLevelPrev || (nLevelNew == nLevelPrev && nLutsNew < nLutsPrev);
        if ( pPars->fVerbose )
            Abc_Print( 1, "Optimization iteration %d: depth %d -> %d. LUTs %d -> %d. %s.\n",
                iIter + 1, nLevelPrev, nLevelNew, nLutsPrev, nLutsNew,
                fImprove ? "Accepted" : "No improvement; stopping" );
        if ( !fImprove )
        {
            Gia_ManStop( pWork );
            break;
        }
        Gia_ManStop( pNew );
        pNew = pWork;
    }
    assert( pPars->fArea || Sbd_ManLutLevel(pNew) <= nLevel );
    assert( pPars->fDelay || Gia_ManLutNum(pNew) <= nLuts );
    assert( Gia_ManCiNum(pNew) == Gia_ManCiNum(pGia) );
    assert( Gia_ManCoNum(pNew) == Gia_ManCoNum(pGia) );
    assert( Gia_ManRegNum(pNew) == (nRegsBox ? 0 : Gia_ManRegNum(pGia)) );
    if ( pPars->fVerbose )
    {
        Abc_Print( 1, "Mfs2 %s: LUTs %d -> %d. Depth %d -> %d. ",
            pPars->fDelay ? "delay then area" : (pPars->fArea ? "area only" : "area under input depth"),
            nLuts, Gia_ManLutNum(pNew), nLevel, Sbd_ManLutLevel(pNew) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    if ( !pPars->fMapping )
    {
        // Choice mapping may retain AIG nodes used only by the LUT mapping.
        Vec_IntFreeP( &pNew->vMapping );
        pWork = Gia_ManCleanup( pNew );
        Gia_ManTransferTiming( pWork, pNew );
        Gia_ManStop( pNew );
        pNew = pWork;
    }
    if ( pGia->pManTime )
    {
        if ( nRegsBox )
        {
            // Return register outputs to their usual position after all PIs.
            pNew->nRegs = nRegsBox;
            pWork = Gia_ManDupNormalize( pNew, 0 );
            if ( Gia_ManHasMapping(pNew) )
                Gia_ManTransferMapping( pWork, pNew );
            Gia_ManTransferTiming( pWork, pNew );
            Gia_ManStop( pNew );
            pNew = pWork;
        }
        assert( Gia_ManBoxNum(pNew) == Gia_ManBoxNum(pGia) );
        Tim_ManStop( (Tim_Man_t *)pNew->pManTime );
        pNew->pManTime = Tim_ManDup( (Tim_Man_t *)pGia->pManTime, 0 );
        pNew->nAnd2Delay = pGia->nAnd2Delay;
        if ( pGia->vFlopClasses )
        {
            Vec_IntFreeP( &pNew->vFlopClasses );
            pNew->vFlopClasses = Vec_IntDup( pGia->vFlopClasses );
        }
    }
    // Register boundaries and their sequential attributes are unchanged.
    pNew->nConstrs = pGia->nConstrs;
    if ( pGia->vRegClasses )
    {
        Vec_IntFreeP( &pNew->vRegClasses );
        pNew->vRegClasses = Vec_IntSize(pGia->vRegClasses) ? Vec_IntDup(pGia->vRegClasses) : Vec_IntAlloc(0);
    }
    if ( pGia->vRegInits )
    {
        Vec_IntFreeP( &pNew->vRegInits );
        pNew->vRegInits = Vec_IntSize(pGia->vRegInits) ? Vec_IntDup(pGia->vRegInits) : Vec_IntAlloc(0);
    }
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
