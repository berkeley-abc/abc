/**CFile****************************************************************

  FileName    [lmsCollect.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation.]

  Synopsis    [Collect, read, and write truth/arrival samples.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 4, 2026.]

  Revision    [$Id: lmsCollect.c,v 1.00 2026/10/04 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lmsInt.h"
#include "misc/util/utilTruth.h"
#include <errno.h>
#include <ctype.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     SAMPLE COLLECTION                            ///
////////////////////////////////////////////////////////////////////////

static unsigned Lms_SampleHash( const Lms_Sample_t * p )
{
    unsigned h = (unsigned)p->Truth ^ (unsigned)(p->Truth >> 32);
    int i;
    for ( i = 0; i < 6; ++i ) h = h*33 + (unsigned)p->Times[i];
    return h ^ (unsigned)p->nVars*12582917u;
}
static int Lms_SampleCompare( const void * pA, const void * pB )
{
    const Lms_Sample_t * a = (const Lms_Sample_t *)pA, * b = (const Lms_Sample_t *)pB;
    int i;
    if ( a->Truth != b->Truth ) return a->Truth < b->Truth ? -1 : 1;
    if ( a->nVars != b->nVars ) return a->nVars-b->nVars;
    for ( i = 0; i < 6; ++i )
        if ( a->Times[i] != b->Times[i] ) return a->Times[i]-b->Times[i];
    return 0;
}
static void Lms_SampleInsert( Lms_Collect_t * p, Lms_Sample_t * pSample )
{
    unsigned Slot = Lms_SampleHash(pSample) & (p->nSlots-1);
    while ( p->pTable[Slot].nVars )
    {
        if ( !Lms_SampleCompare(p->pTable+Slot, pSample) ) return;
        Slot = (Slot+1) & (p->nSlots-1);
    }
    p->pTable[Slot] = *pSample;
    ++p->nSamples;
}
/**Function*************************************************************

  Synopsis    [Allocate a truth/arrival sample collector.]

  Description [Creates an empty collector owned by the caller.]

  SideEffects [Allocates memory.]

  SeeAlso     []

***********************************************************************/
Lms_Collect_t * Lms_CollectStart( void )
{
    Lms_Collect_t * p = ABC_CALLOC(Lms_Collect_t, 1);
    p->nSlots = 1024;
    p->pTable = ABC_CALLOC(Lms_Sample_t, p->nSlots);
    return p;
}
/**Function*************************************************************

  Synopsis    [Free a sample collector.]

  Description [Accepts NULL.]

  SideEffects [Frees the collector and its samples.]

  SeeAlso     []

***********************************************************************/
void Lms_CollectStop( Lms_Collect_t * p )
{
    if ( !p ) return;
    ABC_FREE(p->pTable);
    ABC_FREE(p);
}
static void Lms_SampleAdd( Lms_Collect_t * p, word Truth, int nVars, const int * pArrivals, int Line )
{
    Lms_Sample_t Sample;
    int i, Base = ABC_INFINITY;
    if ( !p || nVars < 2 || nVars > 6 || p->fOverflow ) return;
    memset(&Sample, 0, sizeof(Sample));
    Sample.Truth = Truth; Sample.nVars = nVars; Sample.Line = Line;
    for ( i = 0; i < nVars; ++i ) Base = Abc_MinInt(Base, pArrivals[i]);
    for ( i = 0; i < nVars; ++i ) Sample.Times[i] = pArrivals[i]-Base;
    {
        unsigned Slot = Lms_SampleHash(&Sample) & (p->nSlots-1);
        while ( p->pTable[Slot].nVars )
        {
            if ( !Lms_SampleCompare(p->pTable+Slot, &Sample) ) return;
            Slot = (Slot+1) & (p->nSlots-1);
        }
    }
    if ( p->nSamples >= p->nSlots/2 )
    {
        Lms_Sample_t * pOld = p->pTable;
        int nOld = p->nSlots;
        if ( p->nSamples >= LMS_SAMPLE_LIMIT ) { p->fOverflow = 1; return; }
        p->nSlots *= 2;
        p->pTable = ABC_CALLOC(Lms_Sample_t, p->nSlots); p->nSamples = 0;
        for ( i = 0; i < nOld; ++i )
            if ( pOld[i].nVars ) Lms_SampleInsert(p, pOld+i);
        ABC_FREE(pOld);
    }
    Lms_SampleInsert(p, &Sample);
}
/**Function*************************************************************

  Synopsis    [Record a function and its input arrivals.]

  Description [Duplicate samples share an entry. The truth is stretched to six inputs.]

  SideEffects [Updates the collector.]

  SeeAlso     []

***********************************************************************/
void Lms_CollectAdd( Lms_Collect_t * p, word Truth, int nVars, const int * pArrivals )
{
    Lms_SampleAdd(p, Truth, nVars, pArrivals, 0);
}
/**Function*************************************************************

  Synopsis    [Copy samples in deterministic truth/arrival order.]

  Description [Returns storage owned by the caller.]

  SideEffects [Allocates memory.]

  SeeAlso     []

***********************************************************************/
Lms_Sample_t * Lms_SamplesSorted( Lms_Collect_t * p )
{
    Lms_Sample_t * pSamples = ABC_ALLOC(Lms_Sample_t, p->nSamples);
    int i, k = 0;
    for ( i = 0; i < p->nSlots; ++i )
        if ( p->pTable[i].nVars ) pSamples[k++] = p->pTable[i];
    qsort(pSamples, p->nSamples, sizeof(*pSamples), Lms_SampleCompare);
    return pSamples;
}
/**Function*************************************************************

  Synopsis    [Write collected samples to a text file.]

  Description [Returns 1 on success and 0 on failure; diagnostics use pError.]

  SideEffects [Writes the sample file.]

  SeeAlso     []

***********************************************************************/
int Lms_CollectWrite( Lms_Collect_t * p, const char * pName, FILE * pError )
{
    Lms_Sample_t * pSamples;
    FILE * pFile;
    int i, k, fOk;
    if ( p->fOverflow )
    {
        fprintf(pError, "LMS sampling exceeded %d distinct samples; export smaller batches.\n", LMS_SAMPLE_LIMIT);
        return 0;
    }
    pFile = fopen(pName, "w");
    if ( !pFile ) { fprintf(pError, "Cannot write LMS samples: %s.\n", pName); return 0; }
    pSamples = Lms_SamplesSorted(p);
    for ( i = 0; i < p->nSamples; ++i )
    {
        fprintf(pFile, "%016llx %d", (unsigned long long)pSamples[i].Truth, pSamples[i].nVars);
        for ( k = 0; k < 6; ++k ) fprintf(pFile, " %d", pSamples[i].Times[k]);
        fprintf(pFile, "\n");
    }
    fOk = !ferror(pFile);
    if ( fclose(pFile) ) fOk = 0;
    ABC_FREE(pSamples);
    if ( !fOk ) fprintf(pError, "Failed writing LMS samples: %s.\n", pName);
    else Abc_Print(1, "LMS: wrote %d distinct truth/arrival samples.\n", p->nSamples);
    return fOk;
}
/**Function*************************************************************

  Synopsis    [Read truth/arrival samples from a text file.]

  Description [Returns a collector owned by the caller, or NULL on error.]

  SideEffects [Reads the file and allocates memory.]

  SeeAlso     []

***********************************************************************/
Lms_Collect_t * Lms_SamplesRead( const char * pName, FILE * pError )
{
    FILE * pFile = fopen(pName, "r");
    Lms_Collect_t * p;
    char Line[1024], * s, * e;
    int LineNo = 0, Values[7], i;
    word Truth;
    if ( !pFile ) { fprintf(pError, "Cannot read LMS samples: %s.\n", pName); return NULL; }
    p = Lms_CollectStart();
    while ( fgets(Line, sizeof(Line), pFile) )
    {
        ++LineNo; s = Line;
        if ( !strchr(Line, '\n') && !feof(pFile) ) goto malformed;
        while ( isspace((unsigned char)*s) ) ++s;
        if ( !*s || *s == '#' ) continue;
        if ( !isxdigit((unsigned char)*s) ) goto malformed;
        errno = 0; Truth = (word)strtoull(s, &e, 16);
        if ( errno || e == s || !isspace((unsigned char)*e) ) goto malformed;
        s = e;
        for ( i = 0; i < 7; ++i )
        {
            long Value;
            errno = 0; Value = strtol(s, &e, 10);
            if ( errno || e == s || Value < 0 || Value > 1000000 ||
                 (*e && !isspace((unsigned char)*e) && *e != '#') ) goto malformed;
            Values[i] = (int)Value; s = e;
        }
        while ( isspace((unsigned char)*s) ) ++s;
        if ( *s && *s != '#' ) goto malformed;
        if ( Values[0] < 2 || Values[0] > 6 ||
             Abc_TtSupport(&Truth, 6) != (1 << Values[0])-1 ) goto malformed;
        for ( i = Values[0]+1; i < 7; ++i ) if ( Values[i] ) goto malformed;
        Lms_SampleAdd(p, Truth, Values[0], Values+1, LineNo);
    }
    if ( ferror(pFile) || !p->nSamples || p->fOverflow )
    {
        fprintf(pError, "LMS sample file is unreadable, empty, or exceeds %d samples: %s.\n", LMS_SAMPLE_LIMIT, pName);
        goto fail;
    }
    fclose(pFile);
    return p;
malformed:
    fprintf(pError, "Invalid LMS sample at %s:%d (truth, support 2..6, six nonnegative arrivals expected).\n", pName, LineNo);
fail:
    fclose(pFile); Lms_CollectStop(p);
    return NULL;
}


ABC_NAMESPACE_IMPL_END
