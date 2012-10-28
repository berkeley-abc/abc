/**CFile****************************************************************

  FileName    [abcRec2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Record of semi-canonical AIG subgraphs.]

  Author      [Allan Yang, Alan Mishchenko]
  
  Affiliation [Fudan University in Shanghai, UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "map/if/if.h"
#include "bool/kit/kit.h"
#include "aig/gia/giaAig.h"
#include "misc/vec/vecMem.h"
#include "bool/lucky/lucky.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Lms_Man_t_ Lms_Man_t;
struct Lms_Man_t_
{
    // parameters
    int               nVars;        // the number of variables
    int               nWords;       // the number of TT words
    int               nCuts;        // the max number of cuts to use
    int               fFuncOnly;    // record only functions
    // internal data
    Gia_Man_t *       pGia;         // the record
    Vec_Mem_t *       vTtMem;       // truth tables of primary outputs
    Vec_Int_t *       vTruthPo;     // for each semi-canonical class, last PO where this truth table was seen
    // subgraph attributes (1-to-1 correspondence with POs of Gia)
    Vec_Int_t *       vTruthIds;    // truth table IDs of this PO
    Vec_Int_t *       vEquivs;      // link to the previous PO of the same functional class
    Vec_Wrd_t *       vDelays;      // pin-to-pin delays of this PO
    Vec_Str_t *       vCosts;       // number of AND gates in this PO
    // sugraph usage statistics
//    Vec_Int_t *       vFreqs;       // frequencies
    // temporaries
    Vec_Ptr_t *       vNodes;       // the temporary nodes
    Vec_Int_t *       vLabels;      // temporary storage for AIG node labels
    word              pTemp1[1024]; // copy of the truth table
    word              pTemp2[1024]; // copy of the truth table
    // statistics 
    int               nTried;
    int               nFilterSize;
    int               nFilterRedund;
    int               nFilterVolume;
    int               nFilterTruth;
    int               nFilterError;
    int               nFilterSame;
    int               nAdded;
    int               nAddedFuncs;
    // runtime
    clock_t           timeCollect;
    clock_t           timeCanon;
    clock_t           timeBuild;
    clock_t           timeCheck;
    clock_t           timeInsert;
    clock_t           timeOther;
    clock_t           timeTotal;
};

static Lms_Man_t * s_pMan = NULL;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecIsRunning3()
{
    return s_pMan != NULL;
}
Gia_Man_t * Abc_NtkRecGetGia3()
{
    return s_pMan->pGia;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Lms_Man_t * Lms_ManStart( int nVars, int nCuts, int fFuncOnly, int fVerbose )
{
    Lms_Man_t * p;
    int i;
    p = ABC_CALLOC( Lms_Man_t, 1 );
    // parameters
    p->nVars = nVars;
    p->nCuts = nCuts;
    p->nWords = Abc_Truth6WordNum( nVars );
    p->fFuncOnly = fFuncOnly;
    // GIA
    p->pGia = Gia_ManStart( 10000 );
    p->pGia->pName = Abc_UtilStrsav( "record" );
    for ( i = 0; i < nVars; i++ )
        Gia_ManAppendCi( p->pGia );
    // truth tables
    p->vTtMem = Vec_MemAlloc( p->nWords, 12 ); // 32 KB/page for 6-var functions
    Vec_MemHashAlloc( p->vTtMem, 10000 );
    p->vTruthPo  = Vec_IntAlloc( 1000 );
    // subgraph attributes
    p->vTruthIds = Vec_IntAlloc( 1000 );
    p->vEquivs   = Vec_IntAlloc( 1000 );
    p->vDelays   = Vec_WrdAlloc( 1000 );
    p->vCosts    = Vec_StrAlloc( 1000 );
    // sugraph usage statistics
//    p->vFreqs    = Vec_IntAlloc( 1000 );
    // temporaries
    p->vNodes    = Vec_PtrAlloc( 1000 );
    p->vLabels   = Vec_IntAlloc( 1000 );
    return p;    
}
void Lms_ManStop( Lms_Man_t * p )
{
    // temporaries
    Vec_IntFree( p->vLabels );
    Vec_PtrFree( p->vNodes );
    // subgraph attributes
    Vec_IntFree( p->vEquivs );
    Vec_WrdFree( p->vDelays );
    Vec_StrFree( p->vCosts );
    Vec_IntFree( p->vTruthPo );
    // sugraph usage statistics
//    Vec_IntFree( p->vFreqs );
    // truth tables
    Vec_IntFree( p->vTruthIds );
    Vec_MemHashFree( p->vTtMem );
    Vec_MemFree( p->vTtMem );
    // GIA
    Gia_ManStop( p->pGia );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecStart3( Gia_Man_t * p, int nVars, int nCuts, int fTrim )
{
    assert( s_pMan == NULL );
    if ( p == NULL )
        s_pMan = Lms_ManStart( nVars, nCuts, 0, 0 );
    else
        s_pMan = NULL;
}

void Abc_NtkRecStop3()
{
    assert( s_pMan != NULL );
    Lms_ManStop( s_pMan );
    s_pMan = NULL;
}

void Abc_NtkRecPs3(int fPrintLib)
{
    Lms_Man_t * p = s_pMan;

    printf( "Subgraphs tried                             = %10d. (%6.2f %%)\n", p->nTried,        !p->nTried? 0 : 100.0*p->nTried/p->nTried );
    printf( "Subgraphs filtered by support size          = %10d. (%6.2f %%)\n", p->nFilterSize,   !p->nTried? 0 : 100.0*p->nFilterSize/p->nTried );
    printf( "Subgraphs filtered by structural redundancy = %10d. (%6.2f %%)\n", p->nFilterRedund, !p->nTried? 0 : 100.0*p->nFilterRedund/p->nTried );
    printf( "Subgraphs filtered by volume                = %10d. (%6.2f %%)\n", p->nFilterVolume, !p->nTried? 0 : 100.0*p->nFilterVolume/p->nTried );
    printf( "Subgraphs filtered by TT redundancy         = %10d. (%6.2f %%)\n", p->nFilterTruth,  !p->nTried? 0 : 100.0*p->nFilterTruth/p->nTried );
    printf( "Subgraphs filtered by error                 = %10d. (%6.2f %%)\n", p->nFilterError,  !p->nTried? 0 : 100.0*p->nFilterError/p->nTried );
    printf( "Subgraphs filtered by isomorphism           = %10d. (%6.2f %%)\n", p->nFilterSame,   !p->nTried? 0 : 100.0*p->nFilterSame/p->nTried );
    printf( "Subgraphs added                             = %10d. (%6.2f %%)\n", p->nAdded,        !p->nTried? 0 : 100.0*p->nAdded/p->nTried );
    printf( "Functions added                             = %10d. (%6.2f %%)\n", p->nAddedFuncs,   !p->nTried? 0 : 100.0*p->nAddedFuncs/p->nTried );

    p->timeOther = p->timeTotal 
                        - p->timeCollect 
                        - p->timeCanon
                        - p->timeBuild
                        - p->timeCheck
                        - p->timeInsert;

    ABC_PRTP( "Runtime: Collect", p->timeCollect, p->timeTotal );
    ABC_PRTP( "Runtime: Canon  ", p->timeCanon,   p->timeTotal );
    ABC_PRTP( "Runtime: Build  ", p->timeBuild,   p->timeTotal );
    ABC_PRTP( "Runtime: Check  ", p->timeCheck,   p->timeTotal );
    ABC_PRTP( "Runtime: Insert ", p->timeInsert,  p->timeTotal );
    ABC_PRTP( "Runtime: Other  ", p->timeOther,   p->timeTotal );
    ABC_PRTP( "Runtime: TOTAL  ", p->timeTotal,   p->timeTotal );
}


/**Function*************************************************************

  Synopsis    [stretch the truthtable to have more input variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_TtStretch( word * pInOut, int nVarS, int nVarB )
{
    int w, i, step, nWords;
    if ( nVarS == nVarB )
        return;
    assert( nVarS < nVarB );
    step = Abc_Truth6WordNum(nVarS);
    nWords = Abc_Truth6WordNum(nVarB);
    if ( step == nWords )
        return;
    assert( step < nWords );
    for ( w = 0; w < nWords; w += step )
        for ( i = 0; i < step; i++ )
            pInOut[w + i] = pInOut[i];              
}


/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecAddCut3( If_Man_t * pIfMan, If_Obj_t * pRoot, If_Cut_t * pCut )
{
    char pCanonPerm[16];
    unsigned uCanonPhase;
    int i, Index, iFanin0, iFanin1;
    int nLeaves = If_CutLeaveNum(pCut);
    Vec_Ptr_t * vNodes = s_pMan->vNodes;
    Gia_Man_t * pGia = s_pMan->pGia;
    Gia_Obj_t * pDriver;
    If_Obj_t * pIfObj;
    unsigned * pTruth;
    clock_t clk;
    s_pMan->nTried++;

    // skip small cuts
    assert( s_pMan->nVars == (int)pCut->nLimit );
    if ( nLeaves < 2 )
    {
        s_pMan->nFilterSize++;
        return 1;
    }

    // collect internal nodes and skip redundant cuts
clk = clock();
    If_CutTraverse( pIfMan, pRoot, pCut, vNodes );
s_pMan->timeCollect += clock() - clk;

    // semi-canonicize truth table
clk = clock();
    for ( i = 0; i < Abc_MaxInt(nLeaves, 6); i++ )
        pCanonPerm[i] = i;
    memcpy( s_pMan->pTemp1, If_CutTruthW(pCut), s_pMan->nWords * sizeof(word) );
//    uCanonPhase = luckyCanonicizer_final_fast( s_pMan->pTemp1, nLeaves, pCanonPerm );
    uCanonPhase = Kit_TruthSemiCanonicize( (unsigned *)s_pMan->pTemp1, (unsigned *)s_pMan->pTemp2, nLeaves, pCanonPerm );
    if ( nLeaves < 6 )
        s_pMan->pTemp1[0] = (s_pMan->pTemp1[0] & 0xFFFFFFFF) | (s_pMan->pTemp1[0] << 32);
    Abc_TtStretch( If_CutTruthW(pCut), nLeaves, s_pMan->nVars );
s_pMan->timeCanon += clock() - clk;
    // pCanonPerm and uCanonPhase show what was the variable corresponding to each var in the current truth

clk = clock();
    // map cut leaves into elementary variables of GIA
    for ( i = 0; i < nLeaves; i++ )
    {
//        printf( "Leaf  " );
//        If_ObjPrint( If_ManObj( pIfMan, pCut->pLeaves[pCanonPerm[i]] ) );
        If_ManObj( pIfMan, pCut->pLeaves[pCanonPerm[i]] )->iCopy = Abc_Var2Lit( Gia_ObjId(pGia, Gia_ManPi(pGia, i)), (uCanonPhase >> i) & 1 );
    }
    // build internal nodes
//    printf( "\n" );
    assert( Vec_PtrSize(vNodes) > 0 );
    Vec_PtrForEachEntryStart( If_Obj_t *, vNodes, pIfObj, i, nLeaves )
    {
//        If_ObjPrint( pIfObj );
        if ( If_ObjIsCi(pIfObj) )
        {
//printf( "Seeing PI in %d.\n", Vec_WrdSize(s_pMan->vDelays) );
            pIfObj->iCopy = 0;
            continue;
        }
        iFanin0 = Abc_LitNotCond( If_ObjFanin0(pIfObj)->iCopy, If_ObjFaninC0(pIfObj) );
        iFanin1 = Abc_LitNotCond( If_ObjFanin1(pIfObj)->iCopy, If_ObjFaninC1(pIfObj) );
        pIfObj->iCopy = Gia_ManHashAnd( pGia, iFanin0, iFanin1 );
    }
s_pMan->timeBuild += clock() - clk;

    // check if this node is already driving a PO
    pDriver = Gia_ManObj(pGia, Abc_Lit2Var(pIfObj->iCopy));
    if ( pDriver->fMark1 )
    {
        s_pMan->nFilterSame++;
        return 1;
    }

    // create output
    assert( If_ObjIsAnd(pIfObj) );
    Gia_ManAppendCo( pGia, Abc_LitNotCond( pIfObj->iCopy, (uCanonPhase >> nLeaves) & 1 ) );
    // mark the driver
    pDriver = Gia_ManObj(pGia, Abc_Lit2Var(pIfObj->iCopy));
    pDriver->fMark1 = 1;

    // verify truth table
clk = clock();
    pTruth = Gia_ObjComputeTruthTable( pGia, Gia_ManPo(pGia, Gia_ManPoNum(pGia)-1) );
    if ( memcmp( s_pMan->pTemp1, pTruth, s_pMan->nWords * sizeof(word) ) != 0 )
    {
/*
        Kit_DsdPrintFromTruth( pTruth, nLeaves ); printf( "\n" );
        Kit_DsdPrintFromTruth( (unsigned *)s_pMan->pTemp1, nLeaves ); printf( "\n" );
        printf( "Truth table verification has failed.\n" );
*/
        Vec_IntPush( s_pMan->vTruthIds, -1 ); // truth table IDs
        Vec_IntPush( s_pMan->vEquivs, -1 );   // truth table IDs
        Vec_WrdPush( s_pMan->vDelays, 0 );
        Vec_StrPush( s_pMan->vCosts, 0 );
        s_pMan->nFilterTruth++;
        return 1;
    }
s_pMan->timeCheck += clock() - clk;

    // add the resulting truth table to the hash table 
clk = clock();
    s_pMan->nAdded++;
    Index = Vec_MemHashInsert( s_pMan->vTtMem, s_pMan->pTemp1 );
    Vec_IntPush( s_pMan->vTruthIds, Index ); // truth table IDs
    assert( Gia_ManPoNum(pGia) == Vec_IntSize(s_pMan->vTruthIds) );
    if ( Index < Vec_IntSize(s_pMan->vTruthPo) ) // old ID -- add to linked list
    {
        Vec_IntPush( s_pMan->vEquivs, Vec_IntEntry(s_pMan->vTruthPo, Index) );
        Vec_IntWriteEntry( s_pMan->vTruthPo, Index, Gia_ManPoNum(pGia) - 1 );
    }
    else
    {
        assert( Index == Vec_IntSize(s_pMan->vTruthPo) );
        Vec_IntPush( s_pMan->vTruthPo, Gia_ManPoNum(pGia) - 1 );
        Vec_IntPush( s_pMan->vEquivs, -1 );
        s_pMan->nAddedFuncs++;
    }
    Vec_WrdPush( s_pMan->vDelays, 0 );
    Vec_StrPush( s_pMan->vCosts, 0 );
s_pMan->timeInsert += clock() - clk;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecAdd3( Abc_Ntk_t * pNtk, int fUseSOPB )
{
    extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
    If_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkNew;
    int clk = clock();
    if ( Abc_NtkGetChoiceNum( pNtk ) )
        printf( "Performing recoding structures with choices.\n" );
    // create hash table if not available
    if ( s_pMan->pGia->pHTable == NULL )
        Gia_ManHashStart( s_pMan->pGia );

    // set defaults
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
    pPars->nLutSize    =  s_pMan->nVars;
    pPars->nCutsMax    =  s_pMan->nCuts;
    pPars->DelayTarget = -1;
    pPars->Epsilon     =  (float)0.005;
    pPars->fArea       =  1;
    // internal parameters
    if ( fUseSOPB )
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  0;
        pPars->fUsePerm    =  1; 
        pPars->fDelayOpt   =  1;
    }
    else
    {
        pPars->fTruth      =  1;
        pPars->fCutMin     =  1;
        pPars->fUsePerm    =  0; 
        pPars->fDelayOpt   =  0;
    }
    pPars->fSkipCutFilter = 0;
    pPars->pFuncCost   =  NULL;
    pPars->pFuncUser   =  Abc_NtkRecAddCut3;
    // perform recording
    pNtkNew = Abc_NtkIf( pNtk, pPars );
    Abc_NtkDelete( pNtkNew );
s_pMan->timeTotal += clock() - clk;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END