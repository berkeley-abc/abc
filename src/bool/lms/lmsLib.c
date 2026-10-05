/**CFile****************************************************************

  FileName    [lmsLib.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation.]

  Synopsis    [Record, validate, canonicalize, and filter generated libraries.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 4, 2026.]

  Revision    [$Id: lmsLib.c,v 1.00 2026/10/04 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lmsInt.h"
#include "aig/gia/gia.h"
#include "opt/dau/dau.h"
#include "misc/util/utilTruth.h"
#include <fcntl.h>
#ifndef O_BINARY
#define O_BINARY 0
#endif
#include <errno.h>
#ifdef _MSC_VER
#include <io.h>
#include <sys/stat.h>
#else
#include <unistd.h>
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Lms_Output_t_ {
    word Truth;
    int Lit, Area, Depths[6], fKeep;
} Lms_Output_t;
typedef struct Lms_Record_t_ {
    Gia_Man_t * pGia;
    Vec_Int_t * vSeen;
    Lms_Output_t * pOutputs;
    int nOutputs, nCapacity, nChecked, nSkipped;
    int fXor;
    word Truth;
} Lms_Record_t;

////////////////////////////////////////////////////////////////////////
///                     CANDIDATE RECORDING                          ///
////////////////////////////////////////////////////////////////////////

// Check the complete truth table and every pin depth before recording.
// Canonicalization is solely a file-format step; generation uses raw pins.
static int Lms_RecordCandidate( void * pData, int nVars, const int * pFans,
    int nAnds, int Root, const int * pDepths )
{
    Lms_Record_t * p = (Lms_Record_t *)pData;
    word Values[135] = {0}, Canon = p->Truth;
    int Pins[135][6], Map[135], i, k, Lit;
    unsigned Phase;
    char Perm[16];
    if ( nAnds < 0 || nAnds > 128 || Root < 0 || (Root>>1) >= nVars+1+nAnds ) return 0;
    memset(Pins, -1, sizeof(Pins));
    for ( i = 0; i < nVars; ++i )
    {
        Values[i+1] = s_Truths6[i]; Pins[i+1][i] = 0;
    }
    for ( i = 0; i < nAnds; ++i )
    {
        int a = pFans[2*i], b = pFans[2*i+1], Id = nVars+1+i;
        if ( a < 0 || b < 0 || (a>>1) >= Id || (b>>1) >= Id ) return 0;
        Values[Id] = (Values[a>>1] ^ ((a&1) ? ~(word)0 : 0)) &
                    (Values[b>>1] ^ ((b&1) ? ~(word)0 : 0));
        for ( k = 0; k < nVars; ++k )
        {
            int d = Abc_MaxInt(Pins[a>>1][k], Pins[b>>1][k]);
            Pins[Id][k] = d < 0 ? -1 : d+1;
        }
    }
    if ( (Values[Root>>1] ^ ((Root&1) ? ~(word)0 : 0)) != p->Truth ) return 0;
    if ( p->fXor ) Lms_AigXorMetrics(nVars, pFans, nAnds, Root, Pins[Root>>1]);
    for ( i = 0; i < nVars; ++i )
        if ( Pins[Root>>1][i] != pDepths[i] ) return 0;
    ++p->nChecked;
    for ( i = 0; i < nVars; ++i )
        if ( pDepths[i] > 14 ) { ++p->nSkipped; return 1; }
    Phase = Abc_TtCanonicize(&Canon, nVars, Perm);
    Map[0] = 0;
    for ( i = 0; i < nVars; ++i )
        Map[(int)Perm[i]+1] = Gia_Obj2Lit(p->pGia, Gia_ManCi(p->pGia, i)) ^ ((Phase>>i)&1);
    for ( i = 0; i < nAnds; ++i )
    {
        int a = pFans[2*i], b = pFans[2*i+1];
        Map[nVars+1+i] = Gia_ManHashAnd(p->pGia, Map[a>>1]^(a&1), Map[b>>1]^(b&1));
    }
    Lit = Map[Root>>1] ^ (Root&1) ^ ((Phase>>nVars)&1);
    Vec_IntFillExtra(p->vSeen, Lit+1, 0);
    if ( Vec_IntEntry(p->vSeen, Lit) ) return 1;
    Vec_IntWriteEntry(p->vSeen, Lit, 1);
    if ( p->nOutputs == p->nCapacity )
    {
        p->nCapacity = p->nCapacity ? 2*p->nCapacity : 1024;
        p->pOutputs = ABC_REALLOC(Lms_Output_t, p->pOutputs, p->nCapacity);
    }
    memset(p->pOutputs+p->nOutputs, 0, sizeof(Lms_Output_t));
    p->pOutputs[p->nOutputs].Truth = Canon;
    p->pOutputs[p->nOutputs++].Lit = Lit;
    return 1;
}
static int Lms_OutputCompare( const void * pA, const void * pB )
{
    const Lms_Output_t * a = (const Lms_Output_t *)pA, * b = (const Lms_Output_t *)pB;
    if ( a->Truth != b->Truth ) return a->Truth < b->Truth ? -1 : 1;
    return a->Lit-b->Lit;
}
static int Lms_OutputDominates( const Lms_Output_t * a, const Lms_Output_t * b )
{
    int i;
    if ( a->Area > b->Area ) return 0;
    for ( i = 0; i < 6; ++i ) if ( a->Depths[i] > b->Depths[i] ) return 0;
    return 1;
}
// Recompute metrics after structural hashing, which can remove gates.
// Stable root order supplies a deterministic representative for equal profiles.
static int Lms_RecordFilter( Lms_Record_t * p )
{
    int (*pDepths)[6] = (int (*)[6])ABC_ALLOC(int, 6*Gia_ManObjNum(p->pGia));
    word * pTruths = ABC_CALLOC(word, Gia_ManObjNum(p->pGia));
    Vec_Int_t * vStack = Vec_IntAlloc(128);
    Gia_Obj_t * pObj;
    int i, k, j, Start = 0, fOk = 1;
    memset(pDepths, -1, 6*Gia_ManObjNum(p->pGia)*sizeof(int));
    Gia_ManForEachCi(p->pGia, pObj, i)
    {
        pDepths[Gia_ObjId(p->pGia, pObj)][i] = 0;
        pTruths[Gia_ObjId(p->pGia, pObj)] = s_Truths6[i];
    }
    Gia_ManForEachAnd(p->pGia, pObj, i)
    {
        Gia_Obj_t * pA, * pB;
        int a = Gia_ObjFaninId0(pObj, i), b = Gia_ObjFaninId1(pObj, i);
        pTruths[i] = (pTruths[a] ^ (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0)) &
                    (pTruths[b] ^ (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0));
        Lms_GiaMetricFans(pObj, p->fXor, &pA, &pB);
        a = Gia_ObjId(p->pGia, pA); b = Gia_ObjId(p->pGia, pB);
        for ( k = 0; k < 6; ++k )
        {
            int d = Abc_MaxInt(pDepths[a][k], pDepths[b][k]);
            pDepths[i][k] = d < 0 ? -1 : d+1;
        }
    }
    qsort(p->pOutputs, p->nOutputs, sizeof(Lms_Output_t), Lms_OutputCompare);
    for ( i = 0; i < p->nOutputs; ++i )
    {
        Lms_Output_t * q = p->pOutputs+i;
        if ( (pTruths[q->Lit>>1] ^ ((q->Lit&1) ? ~(word)0 : 0)) != q->Truth ) { fOk = 0; break; }
        if ( i && q->Truth != p->pOutputs[i-1].Truth ) Start = i;
        memcpy(q->Depths, pDepths[q->Lit>>1], sizeof(q->Depths));
        Gia_ManIncrementTravId(p->pGia);
        Vec_IntPush(vStack, q->Lit>>1);
        while ( Vec_IntSize(vStack) )
        {
            Gia_Obj_t * pA, * pB;
            int Id = Vec_IntPop(vStack);
            pObj = Gia_ManObj(p->pGia, Id);
            if ( !Gia_ObjIsAnd(pObj) || Gia_ObjIsTravIdCurrent(p->pGia, pObj) ) continue;
            Gia_ObjSetTravIdCurrent(p->pGia, pObj); ++q->Area;
            Lms_GiaMetricFans(pObj, p->fXor, &pA, &pB);
            Vec_IntPush(vStack, Gia_ObjId(p->pGia, pA));
            Vec_IntPush(vStack, Gia_ObjId(p->pGia, pB));
        }
        for ( j = Start; j < i; ++j )
            if ( p->pOutputs[j].fKeep && Lms_OutputDominates(p->pOutputs+j, q) ) break;
        if ( j < i ) continue;
        for ( j = Start; j < i; ++j )
            if ( p->pOutputs[j].fKeep && Lms_OutputDominates(q, p->pOutputs+j) ) p->pOutputs[j].fKeep = 0;
        q->fKeep = 1;
    }
    Vec_IntFree(vStack); ABC_FREE(pDepths); ABC_FREE(pTruths);
    return fOk;
}
static int Lms_LibGenerateMode( const char * pInput, const char * pOutput, FILE * pError, int fXor )
{
    Lms_Collect_t * pCollect = NULL;
    Lms_Sample_t * pSamples = NULL;
    Lms_Gen_t * pGen = NULL;
    Lms_Record_t R;
    Gia_Man_t * pClean = NULL;
    Vec_Str_t * vData = NULL;
    FILE * pFile = NULL;
    int i, fd, fOk = 0, nClasses = 0, nStructures = 0, nDropped = 0;
    abctime Started = Abc_Clock();
    memset(&R, 0, sizeof(R));
    R.fXor = fXor;
    pCollect = Lms_SamplesRead(pInput, pError);
    if ( !pCollect ) return 0;
    // Reserve a new output before doing expensive work. Exclusive creation
    // also prevents a concurrent writer from being overwritten.
#ifdef _MSC_VER
    fd = _open(pOutput, _O_WRONLY|_O_CREAT|_O_EXCL|_O_BINARY, _S_IREAD|_S_IWRITE);
#else
    fd = open(pOutput, O_WRONLY|O_CREAT|O_EXCL|O_BINARY, 0666);
#endif
    if ( fd < 0 )
    {
        fprintf(pError, errno == EEXIST ? "LMS library output already exists: %s.\n" :
            "Cannot create LMS library: %s.\n", pOutput);
        goto cleanup;
    }
#ifdef _MSC_VER
    pFile = _fdopen(fd, "wb");
    if ( !pFile ) _close(fd);
#else
    pFile = fdopen(fd, "wb");
    if ( !pFile ) close(fd);
#endif
    if ( !pFile ) { remove(pOutput); fprintf(pError, "Cannot open LMS library stream: %s.\n", pOutput); goto cleanup; }
    pSamples = Lms_SamplesSorted(pCollect);
    pGen = fXor ? Lms_GenStartXor() : Lms_GenStart();
    R.pGia = Gia_ManStart(100000);
    for ( i = 0; i < 6; ++i ) Gia_ManAppendCi(R.pGia);
    Gia_ManHashStart(R.pGia); R.vSeen = Vec_IntAlloc(100000);
    for ( i = 0; i < pCollect->nSamples; ++i )
    {
        R.Truth = pSamples[i].Truth;
        if ( Lms_GenGenerate(pGen, R.Truth, pSamples[i].nVars, pSamples[i].Times, Lms_RecordCandidate, &R) <= 0 )
        {
            fprintf(pError, "LMS generation or candidate validation failed at %s:%d (%016llx).\n",
                pInput, pSamples[i].Line, (unsigned long long)R.Truth);
            goto cleanup;
        }
        nDropped += Lms_GenSkipped(pGen);
    }
    Gia_ManHashStop(R.pGia);
    if ( !Lms_RecordFilter(&R) )
    {
        fprintf(pError, "LMS canonical candidate validation failed.\n");
        goto cleanup;
    }
    for ( i = 0; i < R.nOutputs; ++i )
    {
        if ( i == 0 || R.pOutputs[i].Truth != R.pOutputs[i-1].Truth ) ++nClasses;
        if ( !R.pOutputs[i].fKeep ) continue;
        Gia_ManAppendCo(R.pGia, R.pOutputs[i].Lit); ++nStructures;
    }
    if ( !nStructures ) { fprintf(pError, "LMS generation produced no representable structures.\n"); goto cleanup; }
    pClean = Gia_ManCleanup(R.pGia);
    vData = Gia_AigerWriteIntoMemoryStr(pClean);
    fOk = fwrite(Vec_StrArray(vData), 1, Vec_StrSize(vData), pFile) == (size_t)Vec_StrSize(vData);
    if ( fclose(pFile) ) fOk = 0;
    pFile = NULL;
    if ( !fOk ) { remove(pOutput); fprintf(pError, "Failed writing LMS library: %s.\n", pOutput); goto cleanup; }
    Abc_Print(1, "LMS: %d samples, %d checked candidates, %d classes, %d structures, %d ANDs; %.2f seconds.\n",
        pCollect->nSamples, R.nChecked, nClasses, nStructures, Gia_ManAndNum(pClean),
        (double)(Abc_Clock()-Started)/CLOCKS_PER_SEC);
    if ( R.nSkipped || nDropped )
        Abc_Print(1, "LMS: skipped %d candidates above the pin-depth limit and %d profiles above the pool capacity.\n",
            R.nSkipped, nDropped);
    if ( fXor ) Abc_Print(1, "LMS: unit AND/XOR profiles, stored as ordinary AND-only AIGER; load with rec_start3 -x.\n");
cleanup:
    if ( pFile ) { fclose(pFile); remove(pOutput); }
    if ( vData ) Vec_StrFree(vData);
    if ( pClean ) Gia_ManStop(pClean);
    if ( R.pGia ) Gia_ManStop(R.pGia);
    if ( R.vSeen ) Vec_IntFree(R.vSeen);
    ABC_FREE(R.pOutputs); ABC_FREE(pSamples);
    Lms_GenStop(pGen); Lms_CollectStop(pCollect);
    return fOk;
}
/**Function*************************************************************

  Synopsis    [Generate a six-input AND-cost LMS library.]

  Description [Returns 1 on success and 0 on failure. The output must be new.]

  SideEffects [Reads samples and writes a binary AIGER library.]

  SeeAlso     []

***********************************************************************/
int Lms_LibGenerate( const char * pInput, const char * pOutput, FILE * pError )
{
    return Lms_LibGenerateMode(pInput, pOutput, pError, 0);
}
/**Function*************************************************************

  Synopsis    [Generate a six-input unit AND/XOR-cost LMS library.]

  Description [Uses ordinary AND nodes for XOR patterns. The output must be new.]

  SideEffects [Reads samples and writes a binary AIGER library.]

  SeeAlso     []

***********************************************************************/
int Lms_LibGenerateXor( const char * pInput, const char * pOutput, FILE * pError )
{
    return Lms_LibGenerateMode(pInput, pOutput, pError, 1);
}

ABC_NAMESPACE_IMPL_END
