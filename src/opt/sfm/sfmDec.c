/**CFile****************************************************************

  FileName    [sfmDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [SAT-based decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmDec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"
#include "base/abc/abc.h"
#include "misc/util/utilTruth.h"
#include "opt/dau/dau.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sfm_Dec_t_ Sfm_Dec_t;
struct Sfm_Dec_t_
{
    // external
    Sfm_Par_t *       pPars;       // parameters
    Sfm_Lib_t *       pLib;        // library
    // library
    Vec_Int_t         vGateSizes;  // fanin counts
    Vec_Wrd_t         vGateFuncs;  // gate truth tables
    Vec_Wec_t         vGateCnfs;   // gate CNFs
    Vec_Ptr_t         vGateHands;  // gate handles
    int               GateConst0;  // special gates
    int               GateConst1;  // special gates
    int               GateBuffer;  // special gates
    int               GateInvert;  // special gates
    int               GateAnd[4];  // special gates
    int               GateOr[4];   // special gates
    // objects
    int               nDivs;       // the number of divisors
    int               nMffc;       // the number of divisors
    int               AreaMffc;    // the area of gates in MFFC
    int               iTarget;     // target node
    int               fUseLast;    // internal switch
    Vec_Int_t         vObjRoots;   // roots of the window
    Vec_Int_t         vObjGates;   // functionality
    Vec_Wec_t         vObjFanins;  // fanin IDs
    Vec_Int_t         vObjMap;     // object map
    Vec_Int_t         vObjDec;     // decomposition
    // solver
    sat_solver *      pSat;        // reusable solver 
    Vec_Wec_t         vClauses;    // CNF clauses for the node
    Vec_Int_t         vImpls[2];   // onset/offset implications
    Vec_Wrd_t         vSets[2];    // onset/offset patterns
    int               nPats[2];    // CEX count
    word              uMask[2];    // mask count
    word              TtElems[SFM_SUPP_MAX][SFM_WORD_MAX];
    word *            pTtElems[SFM_SUPP_MAX];
    // temporary
    Vec_Int_t         vTemp;
    Vec_Int_t         vTemp2;
    // statistics
    abctime           timeWin;
    abctime           timeCnf;
    abctime           timeSat;
    abctime           timeOther;
    abctime           timeStart;
    abctime           timeTotal;
    int               nTotalNodesBeg;
    int               nTotalEdgesBeg;
    int               nTotalNodesEnd;
    int               nTotalEdgesEnd;
    int               nNodesTried;
    int               nNodesChanged;
    int               nNodesConst0;
    int               nNodesConst1;
    int               nNodesBuf;
    int               nNodesInv;
    int               nNodesResyn;
    int               nSatCalls;
    int               nTimeOuts;
    int               nNoDecs;
    int               nMaxDivs;
    int               nMaxWin;
    word              nAllDivs;
    word              nAllWin;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Setup parameter structure.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_ParSetDefault3( Sfm_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Sfm_Par_t) );
    pPars->nTfoLevMax   = 1000;  // the maximum fanout levels
    pPars->nTfiLevMax   = 1000;  // the maximum fanin levels
    pPars->nFanoutMax   =   30;  // the maximum number of fanoutsp
    pPars->nMffcMax     =    3;  // the maximum MFFC size
    pPars->nWinSizeMax  =  300;  // the maximum window size
    pPars->nGrowthLevel =    0;  // the maximum allowed growth in level
    pPars->nBTLimit     = 5000;  // the maximum number of conflicts in one SAT run
    pPars->fArea        =    0;  // performs optimization for area
    pPars->fVerbose     =    0;  // enable basic stats
    pPars->fVeryVerbose =    0;  // enable detailed stats
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sfm_Dec_t * Sfm_DecStart( Sfm_Par_t * pPars )
{
    Sfm_Dec_t * p = ABC_CALLOC( Sfm_Dec_t, 1 ); int i;
    p->pPars = pPars;
    p->pSat = sat_solver_new();
    p->timeStart = Abc_Clock();
    for ( i = 0; i < SFM_SUPP_MAX; i++ )
        p->pTtElems[i] = p->TtElems[i];
    Abc_TtElemInit( p->pTtElems, SFM_SUPP_MAX );
    p->pLib = Sfm_LibPrepare( pPars->nMffcMax + 1, 1, pPars->fVerbose );
    if ( pPars->fVeryVerbose )
//    if ( pPars->fVerbose )
        Sfm_LibPrint( p->pLib );
    return p;
}
void Sfm_DecStop( Sfm_Dec_t * p )
{
    Sfm_LibStop( p->pLib );
    // library
    Vec_IntErase( &p->vGateSizes );
    Vec_WrdErase( &p->vGateFuncs );
    Vec_WecErase( &p->vGateCnfs );
    Vec_PtrErase( &p->vGateHands );
    // objects
    Vec_IntErase( &p->vObjRoots );
    Vec_IntErase( &p->vObjGates );
    Vec_WecErase( &p->vObjFanins );
    Vec_IntErase( &p->vObjMap );
    Vec_IntErase( &p->vObjDec );
    // solver
    sat_solver_delete( p->pSat );
    Vec_WecErase( &p->vClauses );
    Vec_IntErase( &p->vImpls[0] );
    Vec_IntErase( &p->vImpls[1] );
    Vec_WrdErase( &p->vSets[0] );
    Vec_WrdErase( &p->vSets[1] );
    // temporary
    Vec_IntErase( &p->vTemp );
    Vec_IntErase( &p->vTemp2 );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_DecPrepareSolver( Sfm_Dec_t * p )
{
    Vec_Int_t * vRoots = &p->vObjRoots;
    Vec_Int_t * vFaninVars = &p->vTemp2;
    Vec_Int_t * vLevel, * vClause;
    int i, k, Gate, iObj, RetValue;
    int nTfiSize = p->iTarget + 1; // including node
    int nWinSize = Vec_IntSize(&p->vObjGates);
    int nSatVars = 2 * nWinSize - nTfiSize;
    assert( nWinSize == Vec_IntSize(&p->vObjGates) );
    assert( p->iTarget < nWinSize );
    // create SAT solver
    sat_solver_restart( p->pSat );
    sat_solver_setnvars( p->pSat, nSatVars + Vec_IntSize(vRoots) );
    // add CNF clauses for the TFI
    Vec_IntForEachEntry( &p->vObjGates, Gate, i )
    {
        if ( Gate == -1 )
            continue;
        // generate CNF 
        vLevel = Vec_WecEntry( &p->vObjFanins, i );
        Vec_IntPush( vLevel, i );
        Sfm_TranslateCnf( &p->vClauses, (Vec_Str_t *)Vec_WecEntry(&p->vGateCnfs, Gate), vLevel, -1 );
        Vec_IntPop( vLevel );
        // add clauses
        Vec_WecForEachLevel( &p->vClauses, vClause, k )
        {
            if ( Vec_IntSize(vClause) == 0 )
                break;
            RetValue = sat_solver_addclause( p->pSat, Vec_IntArray(vClause), Vec_IntArray(vClause) + Vec_IntSize(vClause) );
            if ( RetValue == 0 )
                return 0;
        }
    }
    // add CNF clauses for the TFO
    Vec_IntForEachEntryStart( &p->vObjGates, Gate, i, nTfiSize )
    {
        assert( Gate != -1 );
        vLevel = Vec_WecEntry( &p->vObjFanins, i );
        Vec_IntClear( vFaninVars );
        Vec_IntForEachEntry( vLevel, iObj, k )
            Vec_IntPush( vFaninVars, iObj <= p->iTarget ? iObj : iObj + nWinSize - nTfiSize );
        Vec_IntPush( vFaninVars, i + nWinSize - nTfiSize );
        // generate CNF 
        Sfm_TranslateCnf( &p->vClauses, (Vec_Str_t *)Vec_WecEntry(&p->vGateCnfs, Gate), vFaninVars, p->iTarget );
        // add clauses
        Vec_WecForEachLevel( &p->vClauses, vClause, k )
        {
            if ( Vec_IntSize(vClause) == 0 )
                break;
            RetValue = sat_solver_addclause( p->pSat, Vec_IntArray(vClause), Vec_IntArray(vClause) + Vec_IntSize(vClause) );
            if ( RetValue == 0 )
                return 0;
        }
    }
    if ( nTfiSize < nWinSize )
    {
        // create XOR clauses for the roots
        Vec_IntClear( vFaninVars );
        Vec_IntForEachEntry( vRoots, iObj, i )
        {
            Vec_IntPush( vFaninVars, Abc_Var2Lit(nSatVars, 0) );
            sat_solver_add_xor( p->pSat, iObj, iObj + nWinSize - nTfiSize, nSatVars++, 0 );
        }
        // make OR clause for the last nRoots variables
        RetValue = sat_solver_addclause( p->pSat, Vec_IntArray(vFaninVars), Vec_IntLimit(vFaninVars) );
        if ( RetValue == 0 )
            return 0;
        assert( nSatVars == sat_solver_nvars(p->pSat) );
    }
    else assert( Vec_IntSize(vRoots) == 1 );
    // finalize
    RetValue = sat_solver_simplify( p->pSat );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_DecFindWeight( Sfm_Dec_t * p, int c, int iLit, word Mask )
{
    int Value0 = Abc_TtCountOnes( Vec_WrdEntry(&p->vSets[!c], Abc_Lit2Var(iLit)) & Mask );
    int Weight0 = Abc_LitIsCompl(iLit) ? Abc_TtCountOnes( p->uMask[!c] & Mask ) - Value0 : Value0;
    return Weight0;
}
void Sfm_DecPrint( Sfm_Dec_t * p, word * Masks )
{
    int c, i, k, Entry;
    for ( c = 0; c < 2; c++ )
    {
        Vec_Int_t * vLevel = Vec_WecEntry( &p->vObjFanins, p->iTarget );
        printf( "\n%s-SET of object %d (divs = %d) with gate \"%s\" and fanins: ", 
            c ? "OFF": "ON", p->iTarget, p->nDivs, 
            Mio_GateReadName((Mio_Gate_t *)Vec_PtrEntry(&p->vGateHands, Vec_IntEntry(&p->vObjGates,p->iTarget))) );
        Vec_IntForEachEntry( vLevel, Entry, i )
            printf( "%d ", Entry );
        printf( "\n" );

        printf( "Implications: " );
        Vec_IntForEachEntry( &p->vImpls[c], Entry, i )
            printf( "%s%d(%d) ", Abc_LitIsCompl(Entry)? "!":"", Abc_Lit2Var(Entry), Sfm_DecFindWeight(p, c, Entry, Masks ? Masks[!c] : ~(word)0) );
        printf( "\n" );
        printf( "     " );
        for ( i = 0; i <= p->iTarget; i++ )
            printf( "%d", i / 10 );
        printf( "\n" );
        printf( "     " );
        for ( i = 0; i <= p->iTarget; i++ )
            printf( "%d", i % 10 );
        printf( "\n" );
        for ( k = 0; k < p->nPats[c]; k++ )
        {
            printf( "%2d : ", k );
            for ( i = 0; i <= p->iTarget; i++ )
                printf( "%d", (int)((Vec_WrdEntry(&p->vSets[c], i) >> k) & 1) );
            printf( "\n" );
        }
        printf( "\n" );
    }
}
int Sfm_DecPeformDecOne( Sfm_Dec_t * p, int * pfConst )
{
    int fVerbose = p->pPars->fVeryVerbose;
    int nBTLimit = 0;
    int i, k, c, Entry, status, Lits[3], RetValue;
    int iLitBest = -1, iCBest = -1, WeightBest = ABC_INFINITY, Weight;
    *pfConst = -1;
    // check stuck-at-0/1 (on/off-set empty)
    p->nPats[0] = p->nPats[1] = 0;
    p->uMask[0] = p->uMask[1] = 0;
    Vec_IntClear( &p->vImpls[0] );
    Vec_IntClear( &p->vImpls[1] );
    Vec_WrdClear( &p->vSets[0] );
    Vec_WrdClear( &p->vSets[1] );
    for ( c = 0; c < 2; c++ )
    {
        Lits[0] = Abc_Var2Lit( p->iTarget, c );
        p->nSatCalls++;
        status = sat_solver_solve( p->pSat, Lits, Lits + 1, nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
        {
            p->nTimeOuts++;
            return -2;
        }
        if ( status == l_False )
        {
            *pfConst = c;
            return -1;
        }
        assert( status == l_True );
        // record this status
        for ( i = 0; i <= p->iTarget; i++ )
            Vec_WrdPush( &p->vSets[c], (word)sat_solver_var_value(p->pSat, i) );
        p->nPats[c]++;
        p->uMask[c] = 1;
    }
    // proceed checking divisors based on their values
    for ( c = 0; c < 2; c++ )
    {
        Lits[0] = Abc_Var2Lit( p->iTarget, c );
        for ( i = 0; i < p->nDivs; i++ )
        {
            word Column = Vec_WrdEntry(&p->vSets[c], i);
            if ( Column != 0 && Column != p->uMask[c] ) // diff value is possible
                continue;
            Lits[1] = Abc_Var2Lit( i, Column != 0 );
            p->nSatCalls++;
            status = sat_solver_solve( p->pSat, Lits, Lits + 2, nBTLimit, 0, 0, 0 );
            if ( status == l_Undef )
                return 0;
            if ( status == l_False )
            {
                Vec_IntPush( &p->vImpls[c], Abc_LitNot(Lits[1]) );
                continue;
            }
            assert( status == l_True );
            if ( p->nPats[c] == 64 )
                continue;
            // record this status
            for ( k = 0; k <= p->iTarget; k++ )
                if ( sat_solver_var_value(p->pSat, k) )
                    *Vec_WrdEntryP(&p->vSets[c], k) |= ((word)1 << p->nPats[c]);
            p->uMask[c] |= ((word)1 << p->nPats[c]++);
        }
    }
    // find the best decomposition
    for ( c = 0; c < 2; c++ )
    {
        Vec_IntForEachEntry( &p->vImpls[c], Entry, i )
        {
            Weight = Sfm_DecFindWeight(p, c, Entry, (~(word)0));
            if ( WeightBest > Weight )
            {
                WeightBest = Weight;
                iLitBest = Entry;
                iCBest = c;
            }
        }
    }
    if ( WeightBest == ABC_INFINITY )
    {
        p->nNoDecs++;
        return -2;
    }

    // add clause
    Lits[0] = Abc_Var2Lit( p->iTarget, iCBest );
    Lits[1] = iLitBest;
    RetValue = sat_solver_addclause( p->pSat, Lits, Lits + 2 );
    if ( RetValue == 0 )
        return -1;

    // print the results
    if ( fVerbose )
    {
        printf( "\nBest literal (%d; %s%d) with weight %d.\n\n", iCBest, Abc_LitIsCompl(iLitBest)? "!":"", Abc_Lit2Var(iLitBest), WeightBest );
        Sfm_DecPrint( p, NULL );
    }
    return Abc_Var2Lit( iLitBest, iCBest );
}
int Sfm_DecPeformDec( Sfm_Dec_t * p )
{
    Vec_Int_t * vLevel;
    int i, Dec, Last, fCompl, Pol, fConst = -1, nNodes = Vec_IntSize(&p->vObjGates);
    // perform decomposition
    Vec_IntClear( &p->vObjDec );
    for ( i = 0; i <= p->nMffc; i++ )
    {
        Dec = Sfm_DecPeformDecOne( p, &fConst );
        if ( Dec == -2 )
        {
            if ( p->pPars->fVeryVerbose )
                printf( "There is no decomposition (or time out occurred).\n" );
            return -1;
        }
        if ( Dec == -1 )
            break;
        Vec_IntPush( &p->vObjDec, Dec );
    }
    if ( i == p->nMffc + 1 )
    {
        if ( p->pPars->fVeryVerbose )
        printf( "Area-reducing decomposition is not found.\n" );
        return -1;
    }
    // check constant
    if ( Vec_IntSize(&p->vObjDec) == 0 )
    {
        assert( fConst >= 0 );
        // add gate
        Vec_IntPush( &p->vObjGates, fConst ? p->GateConst1 : p->GateConst0 );
        vLevel = Vec_WecPushLevel( &p->vObjFanins );
        // report
        if ( p->pPars->fVeryVerbose )
            printf( "Create constant %d.\n", fConst );
        return Vec_IntSize(&p->vObjDec);
    }
    // create network
    Last = Vec_IntPop( &p->vObjDec );
    fCompl = Abc_LitIsCompl(Last);
    Last = Abc_LitNotCond( Abc_Lit2Var(Last), fCompl );
    if ( Vec_IntSize(&p->vObjDec) == 0 )
    {
        // add gate
        Vec_IntPush( &p->vObjGates, Abc_LitIsCompl(Last) ? p->GateInvert : p->GateBuffer );
        vLevel = Vec_WecPushLevel( &p->vObjFanins );
        Vec_IntPush( vLevel, Abc_Lit2Var(Last) );
        // report
        if ( p->pPars->fVeryVerbose )
            printf( "Create buf/inv %d = %s%d.\n", nNodes, Abc_LitIsCompl(Last) ? "!":"", Abc_Lit2Var(Last) );
        return Vec_IntSize(&p->vObjDec);
    }
    Vec_IntForEachEntryReverse( &p->vObjDec, Dec, i )
    {
        fCompl = Abc_LitIsCompl(Dec);
        Dec = Abc_LitNotCond( Abc_Lit2Var(Dec), fCompl );
        // add gate
        Pol = (Abc_LitIsCompl(Last) << 1) | Abc_LitIsCompl(Dec);
        if ( fCompl )
            Vec_IntPush( &p->vObjGates, p->GateOr[Pol] );
        else
            Vec_IntPush( &p->vObjGates, p->GateAnd[Pol] );
        vLevel = Vec_WecPushLevel( &p->vObjFanins );
        Vec_IntPush( vLevel, Abc_Lit2Var(Dec) );
        Vec_IntPush( vLevel, Abc_Lit2Var(Last) );
        // report
        if ( p->pPars->fVeryVerbose )
            printf( "Create node %s%d = %s%d and %s%d (gate %d).\n", 
                fCompl? "!":"", nNodes,
                Abc_LitIsCompl(Last)? "!":"", Abc_Lit2Var(Last),  
                Abc_LitIsCompl(Dec)? "!":"", Abc_Lit2Var(Dec), Pol  );
        // prepare for the next one
        Last = Abc_Var2Lit( nNodes, 0 );
        nNodes++;
    }
    //printf( "\n" );
    return Vec_IntSize(&p->vObjDec);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_DecCombineDec( Sfm_Dec_t * p, word * pTruth0, word * pTruth1, int * pSupp0, int * pSupp1, int nSupp0, int nSupp1, word * pTruth, int * pSupp, int Var )
{
    Vec_Int_t vVec0 = { 2*SFM_SUPP_MAX, nSupp0, pSupp0 };
    Vec_Int_t vVec1 = { 2*SFM_SUPP_MAX, nSupp1, pSupp1 };
    Vec_Int_t vVec  = { 2*SFM_SUPP_MAX, 0,      pSupp  };
    int nWords0 = Abc_TtWordNum(nSupp0);
    int nSupp, iSuppVar;
    // check the case of equal cofactors
    if ( nSupp0 == nSupp1 && !memcmp(pSupp0, pSupp1, sizeof(int)*nSupp0) && !memcmp(pTruth0, pTruth1, sizeof(word)*nWords0) )
    {
        memcpy( pSupp,  pSupp0,  sizeof(int)*nSupp0   );
        memcpy( pTruth, pTruth0, sizeof(word)*nWords0 );
        return nSupp0;
    }
    // merge support variables
    Vec_IntTwoMerge2Int( &vVec0, &vVec1, &vVec );
    Vec_IntPushOrder( &vVec, Var );
    nSupp = Vec_IntSize( &vVec );
    if ( nSupp > SFM_SUPP_MAX )
        return -2;
    // expand truth tables
    Abc_TtStretch6( pTruth0, nSupp0, nSupp );
    Abc_TtStretch6( pTruth1, nSupp1, nSupp );
    Abc_TtExpand( pTruth0, nSupp, pSupp0, nSupp0, pSupp, nSupp );
    Abc_TtExpand( pTruth1, nSupp, pSupp1, nSupp1, pSupp, nSupp );
    // perform operation
    iSuppVar = Vec_IntFind( &vVec, Var );
    Abc_TtMux( pTruth, p->pTtElems[iSuppVar], pTruth1, pTruth0, Abc_TtWordNum(nSupp) );
    return nSupp;
}
int Sfm_DecPeformDec_rec( Sfm_Dec_t * p, word * pTruth, int * pSupp, int * pAssump, int nAssump, word Masks[2], int fCofactor )
{
    int nBTLimit = 0;
//    int fVerbose = p->pPars->fVeryVerbose;
    int c, i, d, Var, WeightBest, status;
//    Vec_Int_t vAss = { SFM_SUPP_MAX, nAssump, pAssump };
//    if ( nAssump > SFM_SUPP_MAX )
    if ( nAssump > p->nMffc )
        return -2;
    // check constant
    for ( c = 0; c < 2; c++ )
    {
        if ( p->uMask[c] & Masks[c] ) // there are some patterns
            continue;
        p->nSatCalls++;
        pAssump[nAssump] = Abc_Var2Lit( p->iTarget, c );
        status = sat_solver_solve( p->pSat, pAssump, pAssump + nAssump + 1, nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return -2;
        if ( status == l_False )
        {
            pTruth[0] = c ? ~((word)0) : 0;
            return 0;
        }
        assert( status == l_True );
        if ( p->nPats[c] == 64 )
            return -2;//continue;
        for ( i = 0; i <= p->iTarget; i++ )
            if ( sat_solver_var_value(p->pSat, i) )
                *Vec_WrdEntryP(&p->vSets[c], i) |= ((word)1 << p->nPats[c]);
        p->uMask[c] |= ((word)1 << p->nPats[c]++);
    }
    // check implications
    Vec_IntClear( &p->vImpls[0] );
    Vec_IntClear( &p->vImpls[1] );
    for ( d = 0; d < p->nDivs; d++ )
    {
        int Impls[2] = {-1, -1};
        for ( c = 0; c < 2; c++ )
        {
            word MaskAll = p->uMask[c] & Masks[c];
            word MaskCur = Vec_WrdEntry(&p->vSets[c], d) & Masks[c];
            assert( MaskAll );
            if ( MaskCur != 0 && MaskCur != MaskAll ) // has both ones and zeros
                continue;
            pAssump[nAssump]   = Abc_Var2Lit( p->iTarget, c );
            pAssump[nAssump+1] = Abc_Var2Lit( d, MaskCur != 0 );
            p->nSatCalls++;
            status = sat_solver_solve( p->pSat, pAssump, pAssump + nAssump + 2, nBTLimit, 0, 0, 0 );
            if ( status == l_Undef )
                return -2;
            if ( status == l_False )
            {
                Impls[c] = Abc_LitNot(pAssump[nAssump+1]);
                Vec_IntPush( &p->vImpls[c], Abc_LitNot(pAssump[nAssump+1]) );
                continue;
            }
            assert( status == l_True );
            if ( p->nPats[c] == 64 )
                return -2;//continue;
            // record this status
            for ( i = 0; i <= p->iTarget; i++ )
                if ( sat_solver_var_value(p->pSat, i) )
                    *Vec_WrdEntryP(&p->vSets[c], i) |= ((word)1 << p->nPats[c]);
            p->uMask[c] |= ((word)1 << p->nPats[c]++);
        }
        if ( Impls[0] == -1 || Impls[1] == -1 || Impls[0] == Impls[1] )
            continue;
        assert( Abc_Lit2Var(Impls[0]) == Abc_Lit2Var(Impls[1]) );
        // found buffer/inverter
        pTruth[0] = Abc_LitIsCompl(Impls[0]) ? ~p->pTtElems[0][0] : p->pTtElems[0][0];
        pSupp[0] = Abc_Lit2Var(Impls[0]);
        return 1;        
    }

    // find the best cofactoring variable
    Var = -1, WeightBest = ABC_INFINITY;
    for ( c = 0; c < 2; c++ )
    {
        int iLit, Weight;
        Vec_IntForEachEntry( &p->vImpls[c], iLit, i )
        {
            Weight = Sfm_DecFindWeight( p, c, iLit, Masks[!c] );
            if ( WeightBest > Weight )
            {
                WeightBest = Weight;
                Var = Abc_Lit2Var(iLit);
            }
        }
    }
    if ( Var == -1 && fCofactor )
    {
        if ( p->fUseLast )
            Var = p->nDivs - 1;
        else
            Var = p->nDivs - 2;
        fCofactor = 0;
    }

//    printf( "Assumptions: " );
//    Vec_IntPrint( &vAss );
//    Sfm_DecPrint( p, Masks );
//printf( "Best var %d with weight %d.\n", Var, WeightBest );

    // cofactor the problem
    if ( Var >= 0 )
    {
        word uTruth[2][SFM_WORD_MAX], MasksNext[2];
        int Supp[2][2*SFM_SUPP_MAX], nSupp[2], nSuppAll;
        for ( i = 0; i < 2; i++ )
        {
            for ( c = 0; c < 2; c++ )
            {
                word MaskVar = Vec_WrdEntry(&p->vSets[c], Var);
                MasksNext[c] = Masks[c] & (i ? MaskVar | ~p->uMask[c] : ~MaskVar);
            }
            pAssump[nAssump] = Abc_Var2Lit( Var, !i );
            nSupp[i] = Sfm_DecPeformDec_rec( p, uTruth[i], Supp[i], pAssump, nAssump+1, MasksNext, fCofactor );
            if ( nSupp[i] == -2 )
                return -2;
        }
        // combine solutions
        nSuppAll = Sfm_DecCombineDec( p, uTruth[0], uTruth[1], Supp[0], Supp[1], nSupp[0], nSupp[1], pTruth, pSupp, Var );
        //if ( nSuppAll > p->nMffc )
        //    return -2;
        return nSuppAll;
    }
    return -2;
}
int Sfm_DecPeformDec2Int( Sfm_Dec_t * p )
{
    word uTruth[SFM_WORD_MAX];
    word Masks[2] = { ~((word)0), ~((word)0) };
    int pAssump[2*SFM_SUPP_MAX];
    int pSupp[2*SFM_SUPP_MAX], nSupp;
    p->nPats[0] = p->nPats[1] = 0;
    p->uMask[0] = p->uMask[1] = 0;
    Vec_WrdFill( &p->vSets[0], p->iTarget+1, 0 );
    Vec_WrdFill( &p->vSets[1], p->iTarget+1, 0 );
    nSupp = Sfm_DecPeformDec_rec( p, uTruth, pSupp, pAssump, 0, Masks, 1 );
//printf( "%d %d  ", p->nPats[0], p->nPats[1] );

//    printf( "Node %4d : ", p->iTarget );
//    printf( "MFFC %2d  ", p->nMffc );
    if ( nSupp == -2 )
    {
//        printf( "NO DEC.\n" );
        p->nNoDecs++;
        return -2;
    }
    // transform truth table
    Dau_DsdPrintFromTruth( uTruth, nSupp );
    return -1;
}
int Sfm_DecPeformDec2( Sfm_Dec_t * p )
{
    word uTruth[SFM_WORD_MAX];
    word Masks[2] = { ~((word)0), ~((word)0) };
    int pAssump[2*SFM_SUPP_MAX];
    int pSupp[2*SFM_SUPP_MAX], nSupp, RetValue;
    p->nPats[0] = p->nPats[1] = 0;
    p->uMask[0] = p->uMask[1] = 0;
    Vec_WrdFill( &p->vSets[0], p->iTarget+1, 0 );
    Vec_WrdFill( &p->vSets[1], p->iTarget+1, 0 );
    p->fUseLast = 1;
    nSupp = Sfm_DecPeformDec_rec( p, uTruth, pSupp, pAssump, 0, Masks, 1 );
    if ( p->pPars->fVeryVerbose )
        printf( "Node %4d : ", p->iTarget );
    if ( p->pPars->fVeryVerbose )
        printf( "MFFC %2d  ", p->nMffc );
    if ( nSupp == -2 )
    {
        if ( p->pPars->fVeryVerbose )
            printf( "NO DEC.\n" );
        p->nNoDecs++;
        return -2;
    }
    // transform truth table
    if ( p->pPars->fVeryVerbose )
        Dau_DsdPrintFromTruth( uTruth, nSupp );
    RetValue = Sfm_LibImplement( p->pLib, uTruth[0], pSupp, nSupp, p->AreaMffc, &p->vObjGates, &p->vObjFanins );
    if ( p->pPars->fVeryVerbose )
        printf( "Implementation %sfound.\n", RetValue < 0 ? "NOT " : "" );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Incremental level update.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkUpdateIncLevel_rec( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, LevelNew = Abc_ObjLevelNew(pObj);
    if ( LevelNew == (int)pObj->Level )
        return;
    pObj->Level = LevelNew;
    if ( Abc_ObjIsNode(pObj) )
        Abc_ObjForEachFanout( pObj, pFanout, i )
            Abc_NtkUpdateIncLevel_rec( pFanout );
}

/**Function*************************************************************

  Synopsis    [Testbench for AIG minimization.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#define SFM_MASK_PI     1  // supp(node) is contained in supp(TFI(pivot))
#define SFM_MASK_INPUT  2  // supp(node) does not overlap with supp(TFI(pivot))
#define SFM_MASK_FANIN  4  // the same as above (pointed to by node with SFM_MASK_PI | SFM_MASK_INPUT)
#define SFM_MASK_MFFC   8  // MFFC nodes, including the target node

void Abc_NtkDfsReverseOne_rec( Abc_Obj_t * pObj, Vec_Int_t * vTfo, int nLevelMax, int nFanoutMax )
{
    Abc_Obj_t * pFanout; int i;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    if ( Abc_ObjIsCo(pObj) || Abc_ObjLevel(pObj) > nLevelMax )
        return;
    assert( Abc_ObjIsNode( pObj ) );
    if ( Abc_ObjFanoutNum(pObj) <= nFanoutMax )
    {
        Abc_ObjForEachFanout( pObj, pFanout, i )
            if ( Abc_ObjIsCo(pFanout) || Abc_ObjLevel(pFanout) > nLevelMax )
                break;
        if ( i == Abc_ObjFanoutNum(pObj) )
            Abc_ObjForEachFanout( pObj, pFanout, i )
                Abc_NtkDfsReverseOne_rec( pFanout, vTfo, nLevelMax, nFanoutMax );
    }
    Vec_IntPush( vTfo, Abc_ObjId(pObj) );
    pObj->iTemp = 0;
}
int Abc_NtkDfsOne_rec( Abc_Obj_t * pObj, Vec_Int_t * vTfi, int nLevelMin, int CiLabel )
{
    Abc_Obj_t * pFanin; int i, Mask = 0;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return pObj->iTemp;
    Abc_NodeSetTravIdCurrent( pObj );
    if ( Abc_ObjIsCi(pObj) || Abc_ObjLevel(pObj) < nLevelMin )
    {
        Vec_IntPush( vTfi, Abc_ObjId(pObj) );
        return (pObj->iTemp = CiLabel);
    }
    assert( Abc_ObjIsNode(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Mask |= Abc_NtkDfsOne_rec( pFanin, vTfi, nLevelMin, CiLabel );
    Vec_IntPush( vTfi, Abc_ObjId(pObj) );
    //assert( Mask > 0 );
    return (pObj->iTemp = Mask);
}
void Sfm_DecAddNode( Abc_Obj_t * pObj, Vec_Int_t * vMap, Vec_Int_t * vGates, int fSkip, int fVeryVerbose )
{
    if ( fVeryVerbose )
        printf( "%d:%d(%d) ", Vec_IntSize(vMap), Abc_ObjId(pObj), pObj->iTemp );
    if ( fVeryVerbose )
        Abc_ObjPrint( stdout, pObj );
    Vec_IntPush( vMap, Abc_ObjId(pObj) );
    Vec_IntPush( vGates, fSkip ? -1 : Mio_GateReadValue((Mio_Gate_t *)pObj->pData) );
}
int Sfm_DecMarkMffc( Abc_Obj_t * pPivot, int nLevelMin, int nMffcMax, int fVeryVerbose, int * pAreaMffc )
{
    Abc_Obj_t * pFanin, * pFanin2;
    int i, k, nMffc = 1;
    *pAreaMffc = (int)(MIO_NUM * Mio_GateReadArea((Mio_Gate_t *)pPivot->pData));
    pPivot->iTemp |= SFM_MASK_MFFC;
if ( fVeryVerbose )
printf( "Mffc = %d.\n", pPivot->Id );
    Abc_ObjForEachFanin( pPivot, pFanin, i )
        if ( Abc_ObjIsNode(pFanin) && Abc_ObjLevel(pFanin) >= nLevelMin && Abc_ObjFanoutNum(pFanin) == 1 && Abc_NodeIsTravIdCurrent(pFanin) )
        {
            if ( nMffc == nMffcMax )
                return nMffc;
            *pAreaMffc += (int)(MIO_NUM * Mio_GateReadArea((Mio_Gate_t *)pFanin->pData));
            pFanin->iTemp |= SFM_MASK_MFFC;
            nMffc++;
if ( fVeryVerbose )
printf( "Mffc = %d.\n", pFanin->Id );
        }
    Abc_ObjForEachFanin( pPivot, pFanin, i )
        if ( Abc_ObjIsNode(pFanin) && Abc_ObjLevel(pFanin) >= nLevelMin && Abc_ObjFanoutNum(pFanin) == 1 && Abc_NodeIsTravIdCurrent(pFanin) )
        {
            if ( nMffc == nMffcMax )
                return nMffc;
            Abc_ObjForEachFanin( pFanin, pFanin2, k )
                if ( Abc_ObjIsNode(pFanin2) && Abc_ObjLevel(pFanin2) >= nLevelMin && Abc_ObjFanoutNum(pFanin2) == 1 && Abc_NodeIsTravIdCurrent(pFanin2) )
                {
                    if ( nMffc == nMffcMax )
                        return nMffc;
                    *pAreaMffc += (int)(MIO_NUM * Mio_GateReadArea((Mio_Gate_t *)pFanin2->pData));
                    pFanin2->iTemp |= SFM_MASK_MFFC;
                    nMffc++;
if ( fVeryVerbose )
printf( "Mffc = %d.\n", pFanin2->Id );
                }
        }
    return nMffc;
}
int Abc_NtkDfsCheck_rec( Abc_Obj_t * pObj, Abc_Obj_t * pPivot )
{
    Abc_Obj_t * pFanin; int i;
    if ( pObj == pPivot )
        return 0;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return 1;
    Abc_NodeSetTravIdCurrent( pObj );
    if ( Abc_ObjIsCi(pObj) )
        return 1;
    assert( Abc_ObjIsNode(pObj) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        if ( !Abc_NtkDfsCheck_rec(pFanin, pPivot) )
            return 0;
    return 1;
}
int Sfm_DecExtract( Abc_Ntk_t * pNtk, Sfm_Par_t * pPars, Abc_Obj_t * pPivot, Vec_Int_t * vRoots, Vec_Int_t * vGates, Vec_Wec_t * vFanins, Vec_Int_t * vMap, Vec_Int_t * vTfi, Vec_Int_t * vTfo, int * pnMffc, int * pnAreaMffc )
{
    Vec_Int_t * vLevel;
    Abc_Obj_t * pObj, * pFanin;
    int nLevelMax = pPivot->Level + pPars->nTfoLevMax;
    int nLevelMin = pPivot->Level - pPars->nTfiLevMax;
    int i, k, nTfiSize, nDivs = -1;
    assert( Abc_ObjIsNode(pPivot) );
if ( pPars->fVeryVerbose )
printf( "\n\nTarget %d\n", Abc_ObjId(pPivot) );
    // collect TFO nodes
    Vec_IntClear( vTfo );
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkDfsReverseOne_rec( pPivot, vTfo, nLevelMax, pPars->nFanoutMax );
    // count internal fanouts
    Abc_NtkForEachObjVec( vTfo, pNtk, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            pFanin->iTemp++;
    // compute roots
    Vec_IntClear( vRoots );
    Abc_NtkForEachObjVec( vTfo, pNtk, pObj, i )
        if ( pObj->iTemp != Abc_ObjFanoutNum(pObj) )
            Vec_IntPush( vRoots, Abc_ObjId(pObj) );
    assert( Vec_IntSize(vRoots) > 0 );
    // collect TFI and mark nodes
    Vec_IntClear( vTfi );
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkDfsOne_rec( pPivot, vTfi, nLevelMin, SFM_MASK_PI );
    nTfiSize = Vec_IntSize(vTfi);
    // additinally mark MFFC
    *pnMffc = Sfm_DecMarkMffc( pPivot, nLevelMin, pPars->nMffcMax, pPars->fVeryVerbose, pnAreaMffc );
    assert( *pnMffc <= pPars->nMffcMax );
if ( pPars->fVeryVerbose )
printf( "Mffc size = %d. Mffc area = %.2f\n", *pnMffc, *pnAreaMffc*MIO_NUMINV );
    // collect TFI(TFO)
    Abc_NtkForEachObjVec( vTfo, pNtk, pObj, i )
        Abc_NtkDfsOne_rec( pObj, vTfi, nLevelMin, SFM_MASK_INPUT );
    // mark input-only nodes pointed to by mixed nodes
    Abc_NtkForEachObjVecStart( vTfi, pNtk, pObj, i, nTfiSize )
        if ( pObj->iTemp != SFM_MASK_INPUT )
            Abc_ObjForEachFanin( pObj, pFanin, k )
                if ( pFanin->iTemp == SFM_MASK_INPUT )
                    pFanin->iTemp = SFM_MASK_FANIN;
    // collect nodes supported only on TFI fanins and not MFFC
if ( pPars->fVeryVerbose )
printf( "\nDivs: " );
    Vec_IntClear( vMap );
    Vec_IntClear( vGates );
    Abc_NtkForEachObjVec( vTfi, pNtk, pObj, i )
        if ( pObj->iTemp == SFM_MASK_PI )
            Sfm_DecAddNode( pObj, vMap, vGates, Abc_ObjIsCi(pObj) || Abc_ObjLevel(pObj) < nLevelMin, pPars->fVeryVerbose );
    nDivs = Vec_IntSize(vMap);
    // add other nodes that are not in TFO and not in MFFC
if ( pPars->fVeryVerbose )
printf( "\nSides: " );
    Abc_NtkForEachObjVec( vTfi, pNtk, pObj, i )
        if ( pObj->iTemp == (SFM_MASK_PI | SFM_MASK_INPUT) || pObj->iTemp == SFM_MASK_FANIN || pObj->iTemp == 0 ) // const
            Sfm_DecAddNode( pObj, vMap, vGates, pObj->iTemp == SFM_MASK_FANIN, pPars->fVeryVerbose );
    // add the TFO nodes
if ( pPars->fVeryVerbose )
printf( "\nTFO: " );
    Abc_NtkForEachObjVec( vTfi, pNtk, pObj, i )
        if ( pObj->iTemp >= SFM_MASK_MFFC )
            Sfm_DecAddNode( pObj, vMap, vGates, 0, pPars->fVeryVerbose );
    assert( Vec_IntSize(vMap) == Vec_IntSize(vGates) );
if ( pPars->fVeryVerbose )
printf( "\n" );
    // create node IDs
    Vec_WecClear( vFanins );
    Abc_NtkForEachObjVec( vMap, pNtk, pObj, i )
    {
        pObj->iTemp = i;
        vLevel = Vec_WecPushLevel( vFanins );
        if ( Vec_IntEntry(vGates, i) >= 0 )
            Abc_ObjForEachFanin( pObj, pFanin, k )
                Vec_IntPush( vLevel, pFanin->iTemp );
    }
    // remap roots
    Abc_NtkForEachObjVec( vRoots, pNtk, pObj, i )
        Vec_IntWriteEntry( vRoots, i, pObj->iTemp );
/*
    // check
    Abc_NtkForEachObjVec( vMap, pNtk, pObj, i )
    {
        if ( i == nDivs )
            break;
        Abc_NtkIncrementTravId( pNtk );
        assert( Abc_NtkDfsCheck_rec(pObj, pPivot) );
    }
*/  
    return nDivs;
}
void Sfm_DecInsert( Abc_Ntk_t * pNtk, Abc_Obj_t * pPivot, int Limit, Vec_Int_t * vGates, Vec_Wec_t * vFanins, Vec_Int_t * vMap, Vec_Ptr_t * vGateHandles, int GateBuf, int GateInv, Vec_Wrd_t * vFuncs )
{
    Abc_Obj_t * pObjNew = NULL; 
    Vec_Int_t * vLevel;
    int i, k, iObj, Gate;
    // assuming that new gates are appended at the end
    assert( Limit < Vec_IntSize(vGates) );
    assert( Limit == Vec_IntSize(vMap) );
    if ( Limit + 1 == Vec_IntSize(vGates) )
    {
        Gate = Vec_IntEntryLast(vGates);
        if ( Gate == GateBuf )
        {
            iObj = Vec_WecEntryEntry( vFanins, Limit, 0 );
            pObjNew = Abc_NtkObj( pNtk, Vec_IntEntry(vMap, iObj) );
            Abc_ObjReplace( pPivot, pObjNew );
            // update level
            pObjNew->Level = 0;
            Abc_NtkUpdateIncLevel_rec( pObjNew );
            return;
        }
        else if ( Gate == GateInv )
        {
            // check if fanouts can be updated
            Abc_Obj_t * pFanout;
            Abc_ObjForEachFanout( pPivot, pFanout, i )
                if ( !Abc_ObjIsNode(pFanout) || Sfm_LibFindComplInputGate(vFuncs, Mio_GateReadValue((Mio_Gate_t*)pFanout->pData), Abc_ObjFaninNum(pFanout), Abc_NodeFindFanin(pFanout, pPivot), NULL) == -1 )
                    break;
            // update fanouts
            if ( i == Abc_ObjFanoutNum(pPivot) )
            {
                Abc_ObjForEachFanout( pPivot, pFanout, i )
                {
                    int iFanin = Abc_NodeFindFanin(pFanout, pPivot), iFaninNew = -1;
                    int iGate = Mio_GateReadValue((Mio_Gate_t*)pFanout->pData);
                    int iGateNew = Sfm_LibFindComplInputGate( vFuncs, iGate, Abc_ObjFaninNum(pFanout), iFanin, &iFaninNew );
                    assert( iGateNew >= 0 && iGateNew != iGate && iFaninNew >= 0 );
                    pFanout->pData = Vec_PtrEntry( vGateHandles, iGateNew );
                    //assert( iFanin == iFaninNew );
                    // swap fanins
                    if ( iFanin != iFaninNew )
                    {
                        int * pArray = Vec_IntArray( &pFanout->vFanouts );
                        ABC_SWAP( int, pArray[iFanin], pArray[iFaninNew] );
                    }
                }
                iObj = Vec_WecEntryEntry( vFanins, Limit, 0 );
                pObjNew = Abc_NtkObj( pNtk, Vec_IntEntry(vMap, iObj) );
                Abc_ObjReplace( pPivot, pObjNew );
                // update level
                pObjNew->Level = 0;
                Abc_NtkUpdateIncLevel_rec( pObjNew );
                return;
            }
        }
    }
    // introduce new gates
    Vec_IntForEachEntryStart( vGates, Gate, i, Limit )
    {
        vLevel = Vec_WecEntry( vFanins, i );
        pObjNew = Abc_NtkCreateNode( pNtk );
        Vec_IntForEachEntry( vLevel, iObj, k )
            Abc_ObjAddFanin( pObjNew, Abc_NtkObj(pNtk, Vec_IntEntry(vMap, iObj)) );
        pObjNew->pData = Vec_PtrEntry( vGateHandles, Gate );
        Vec_IntPush( vMap, Abc_ObjId(pObjNew) );
    }
    Abc_ObjReplace( pPivot, pObjNew );
    // update level
    Abc_NtkForEachObjVecStart( vMap, pNtk, pObjNew, i, Limit )
        Abc_NtkUpdateIncLevel_rec( pObjNew );
}
void Sfm_DecPrintStats( Sfm_Dec_t * p )
{
    printf( "Node = %d. Try = %d. Change = %d.   Const0 = %d. Const1 = %d. Buf = %d. Inv = %d. Gate = %d.\n",
        p->nTotalNodesBeg, p->nNodesTried, p->nNodesChanged, p->nNodesConst0, p->nNodesConst1, p->nNodesBuf, p->nNodesInv, p->nNodesResyn );
    printf( "MaxDiv = %d. MaxWin = %d.   AveDiv = %d. AveWin = %d.   Calls = %d. T/O = %d. NoDec = %d.\n",
        p->nMaxDivs, p->nMaxWin, (int)(p->nAllDivs/Abc_MaxInt(1, p->nNodesTried)), (int)(p->nAllWin/Abc_MaxInt(1, p->nNodesTried)), p->nSatCalls, p->nTimeOuts, p->nNoDecs );

    p->timeTotal = Abc_Clock() - p->timeStart;
    p->timeOther = p->timeTotal - p->timeWin - p->timeCnf - p->timeSat;

    ABC_PRTP( "Win", p->timeWin  ,  p->timeTotal );
    ABC_PRTP( "Cnf", p->timeCnf  ,  p->timeTotal );
    ABC_PRTP( "Sat", p->timeSat  ,  p->timeTotal );
    ABC_PRTP( "Oth", p->timeOther,  p->timeTotal );
    ABC_PRTP( "ALL", p->timeTotal,  p->timeTotal );
//    ABC_PRTP( "   ", p->time1    ,  p->timeTotal );

    printf( "Reduction:   " );
    printf( "Nodes  %6d out of %6d (%6.2f %%)   ", p->nTotalNodesBeg-p->nTotalNodesEnd, p->nTotalNodesBeg, 100.0*(p->nTotalNodesBeg-p->nTotalNodesEnd)/Abc_MaxInt(1, p->nTotalNodesBeg) );
    printf( "Edges  %6d out of %6d (%6.2f %%)   ", p->nTotalEdgesBeg-p->nTotalEdgesEnd, p->nTotalEdgesBeg, 100.0*(p->nTotalEdgesBeg-p->nTotalEdgesEnd)/Abc_MaxInt(1, p->nTotalEdgesBeg) );
    printf( "\n" );
}
void Abc_NtkCountStats( Sfm_Dec_t * p, int Limit )
{
    int Gate, nGates = Vec_IntSize(&p->vObjGates);
    if ( nGates == Limit )
        return;
    Gate = Vec_IntEntryLast(&p->vObjGates);
    if ( nGates > Limit + 1 )
        p->nNodesResyn++;
    else if ( Gate == p->GateConst0 )
        p->nNodesConst0++;
    else if ( Gate == p->GateConst1 )
        p->nNodesConst1++;
    else if ( Gate == p->GateBuffer )
        p->nNodesBuf++;
    else if ( Gate == p->GateInvert )
        p->nNodesInv++;
    else 
        p->nNodesResyn++;
}
void Abc_NtkPerformMfs3( Abc_Ntk_t * pNtk, Sfm_Par_t * pPars )
{
    extern void Sfm_LibPreprocess( Mio_Library_t * pLib, Vec_Int_t * vGateSizes, Vec_Wrd_t * vGateFuncs, Vec_Wec_t * vGateCnfs, Vec_Ptr_t * vGateHands );
    Mio_Library_t * pLib = (Mio_Library_t *)pNtk->pManFunc;
    Sfm_Dec_t * p = Sfm_DecStart( pPars );
    Abc_Obj_t * pObj; 
    abctime clk;
    int i = 0, Limit, RetValue, Count = 0, nStop = Abc_NtkObjNumMax(pNtk);
    //int iNode = 8;//70; //2341;//8;//70;
    printf( "Running remapping with parameters: " );
    printf( "TFO = %d. ", pPars->nTfoLevMax );
    printf( "TFI = %d. ", pPars->nTfiLevMax );
    printf( "FanMax = %d. ", pPars->nFanoutMax );
    printf( "MffcMax = %d. ", pPars->nMffcMax );
    printf( "\n" );
    // enter library
    assert( Abc_NtkIsMappedLogic(pNtk) );
    Sfm_LibPreprocess( pLib, &p->vGateSizes, &p->vGateFuncs, &p->vGateCnfs, &p->vGateHands );
    p->GateConst0 = Mio_GateReadValue( Mio_LibraryReadConst0(pLib) );
    p->GateConst1 = Mio_GateReadValue( Mio_LibraryReadConst1(pLib) );
    p->GateBuffer = Mio_GateReadValue( Mio_LibraryReadBuf(pLib) );
    p->GateInvert = Mio_GateReadValue( Mio_LibraryReadInv(pLib) );
    p->GateAnd[0] = Mio_GateReadValue( Mio_LibraryReadGateByName(pLib, "and00", NULL) );
    p->GateAnd[1] = Mio_GateReadValue( Mio_LibraryReadGateByName(pLib, "and01", NULL) );
    p->GateAnd[2] = Mio_GateReadValue( Mio_LibraryReadGateByName(pLib, "and10", NULL) );
    p->GateAnd[3] = Mio_GateReadValue( Mio_LibraryReadGateByName(pLib, "and11", NULL) );
    p->GateOr[0] = Mio_GateReadValue( Mio_LibraryReadGateByName(pLib, "or00", NULL) );
    p->GateOr[1] = Mio_GateReadValue( Mio_LibraryReadGateByName(pLib, "or01", NULL) );
    p->GateOr[2] = Mio_GateReadValue( Mio_LibraryReadGateByName(pLib, "or10", NULL) );
    p->GateOr[3] = Mio_GateReadValue( Mio_LibraryReadGateByName(pLib, "or11", NULL) );
    if ( pPars->fVerbose )
    p->nTotalNodesBeg = Abc_NtkNodeNum(pNtk);
    if ( pPars->fVerbose )
    p->nTotalEdgesBeg = Abc_NtkGetTotalFanins(pNtk);
    // iterate over nodes
    Abc_NtkLevel( pNtk );
    Abc_NtkForEachNode( pNtk, pObj, i )
    //for ( ; (pObj = Abc_NtkObj(pNtk, iNode));  )
    {
        if ( i >= nStop || (pPars->nNodesMax && i > pPars->nNodesMax) )
            break;
        //if ( i == pPars->nNodesMax )
        //    pPars->fVeryVerbose = 1;
        p->nNodesTried++;
clk = Abc_Clock();
        p->nDivs = Sfm_DecExtract( pNtk, pPars, pObj, &p->vObjRoots, &p->vObjGates, &p->vObjFanins, &p->vObjMap, &p->vTemp, &p->vTemp2, &p->nMffc, &p->AreaMffc );
p->timeWin += Abc_Clock() - clk;
        p->nMaxDivs = Abc_MaxInt( p->nMaxDivs, p->nDivs );
        p->nAllDivs += p->nDivs;
        p->iTarget = pObj->iTemp;
        Limit = Vec_IntSize( &p->vObjGates );
        p->nMaxWin = Abc_MaxInt( p->nMaxWin, Limit );
        p->nAllWin += Limit;
clk = Abc_Clock();
        RetValue = Sfm_DecPrepareSolver( p );
p->timeCnf += Abc_Clock() - clk;
        if ( !RetValue )
            continue;
clk = Abc_Clock();
        if ( pPars->fRrOnly )
            RetValue = Sfm_DecPeformDec( p );
        else
            RetValue = Sfm_DecPeformDec2( p );
p->timeSat += Abc_Clock() - clk;
        if ( RetValue < 0 )
            continue;
        p->nNodesChanged++;
        Abc_NtkCountStats( p, Limit );
        Sfm_DecInsert( pNtk, pObj, Limit, &p->vObjGates, &p->vObjFanins, &p->vObjMap, &p->vGateHands, p->GateBuffer, p->GateInvert, &p->vGateFuncs );
if ( pPars->fVeryVerbose )
printf( "This was modification %d\n", Count );
        //if ( Count == 2 )
        //    break;
        Count++;
    }
    if ( pPars->fVerbose )
    p->nTotalNodesEnd = Abc_NtkNodeNum(pNtk);
    if ( pPars->fVerbose )
    p->nTotalEdgesEnd = Abc_NtkGetTotalFanins(pNtk);
    if ( pPars->fVerbose )
    Sfm_DecPrintStats( p );
    Sfm_DecStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

