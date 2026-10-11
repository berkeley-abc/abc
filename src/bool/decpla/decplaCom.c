/**CFile****************************************************************

  FileName    [decplaCom.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cube-based decomposition of incompletely specified functions.]

  Synopsis    [Standalone PLA analysis command.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: decplaCom.c,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "decpla.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"
#include <errno.h>
#include <limits.h>
ABC_NAMESPACE_IMPL_START
static int Decpla_Command( Abc_Frame_t * frame, int argc, char ** argv )
{
    FILE * out = Abc_FrameReadOut(frame), * err = Abc_FrameReadErr(frame);
    Decpla_Man_t * p = NULL, * q = NULL;
    const char * dest = NULL; int c, minimize = 0, result = 1, i, nFiles;
    int baseline = 0, seedSet = 0; unsigned seed = 0;
    int decompose, statistics = 0, optionSet = 0, verify = 0, attempts = 1;
    Decpla_Options_t options;
    Decpla_OptionsDefault(&options);
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc,argv,"pmbS:Q:o:C:N:K:O:rcwxh")) != EOF ) {
        if ( c == 'm' ) minimize = 1;
        else if ( c == 'o' ) dest = globalUtilOptarg;
        else if ( c == 'b' ) baseline = 1;
        else if ( c == 'p' ) statistics = 1;
        else if ( c == 'c' ) verify = 1;
        else if ( c == 'O' ) {
            if ( strlen(globalUtilOptarg) != 1 || globalUtilOptarg[0] < '0' || globalUtilOptarg[0] > '3' ) goto usage;
            options.OutputOrder = globalUtilOptarg[0]-'0'; optionSet = 1;
        }
        else if ( c == 'w' ) { options.Features ^= 1; optionSet = 1; }
        else if ( c == 'x' ) { options.Features ^= 8; optionSet = 1; }
        else if ( c == 'r' ) { options.fReuse = 0; optionSet = 1; }
        else if ( c == 'C' || c == 'N' || c == 'K' ) {
            char * end; unsigned long value;
            errno = 0; value = strtoul(globalUtilOptarg,&end,10);
            if ( globalUtilOptarg[0] < '0' || globalUtilOptarg[0] > '9' || *end || errno || !value || value > INT_MAX ) goto usage;
            if ( c == 'C' ) options.nConfLimit = (int)value;
            else if ( c == 'N' ) options.nNodesMax = (int)value;
            else attempts = (int)value;
            optionSet = 1;
        }
        else if ( c == 'S' || c == 'Q' ) {
            char * end; unsigned long value;
            errno = 0; value = strtoul(globalUtilOptarg,&end,10);
            if ( globalUtilOptarg[0] < '0' || globalUtilOptarg[0] > '9' || *end || errno || value > UINT_MAX ) goto usage;
            if ( c == 'S' ) { seed = (unsigned)value; seedSet = 1; }
            else { options.OrderSeed = (unsigned)value; options.fOrderSeed = 1; optionSet = 1; }
        }
        else goto usage;
    }
    nFiles = argc-globalUtilOptind;
    if ( nFiles < 1 || nFiles > 2 ) goto usage;
    if ( statistics + minimize + verify > 1 ) goto usage;
    if ( nFiles == 2 && (statistics || minimize || verify || dest) ) goto usage;
    decompose = nFiles == 1 && !statistics && !minimize && !verify;
    if ( options.fOrderSeed && options.OutputOrder != 3 ) goto usage;
    if ( (baseline || seedSet) && !minimize && !decompose ) goto usage;
    if ( baseline && seedSet ) goto usage;
    if ( optionSet && !decompose ) goto usage;
    if ( dest && !statistics && !minimize ) goto usage;
    // Never truncate an existing file (including an input through an alias).
    if ( dest ) { FILE * f = fopen(dest,"rb"); if ( f ) { fclose(f); fprintf(err,"decpla: output already exists: %s\n",dest); return 1; } }
    p = Decpla_Read(argv[globalUtilOptind],err); if ( !p ) goto done;
    fprintf(out,"decpla: inputs = %d  outputs = %d  rows = %lu\n",p->nInputs,p->nOutputs,(unsigned long)p->nRows);
    for ( i = 0; i < p->nOutputs; ++i ) fprintf(out,"  output %d: on = %lu  off = %lu  literal support = %d\n",i,(unsigned long)p->pIsfs[i].On.nCubes,(unsigned long)p->pIsfs[i].Off.nCubes,Decpla_SupportSize(&p->pIsfs[i],p->nInputs));
    if ( verify ) {
        Gia_Man_t * g = Abc_FrameReadGia(frame);
        if ( !g ) { fprintf(err,"decpla: no current GIA to verify\n"); goto done; }
        if ( Decpla_Verify(p,g,options.nConfLimit,err) != 1 ) goto done;
        fprintf(out,"decpla: current GIA VERIFIED against original PLA\n"); result = 0; goto done;
    }
    if ( decompose ) {
        Gia_Man_t * g = NULL;
        int attempt;
        options.fBaseline = baseline;
        for ( attempt = 0; attempt < attempts; ++attempt ) {
            Gia_Man_t * trial;
            options.Seed = seed+(unsigned)attempt;
            if ( attempts > 1 ) fprintf(out,"decpla: attempt %d/%d seed %u\n",attempt+1,attempts,options.Seed);
            trial = Decpla_Decompose(p,&options,out,err);
            if ( !trial ) continue;
            if ( !g || Gia_ManAndNum(trial) < Gia_ManAndNum(g) || (Gia_ManAndNum(trial) == Gia_ManAndNum(g) && Gia_ManLevelNum(trial) < Gia_ManLevelNum(g)) ) {
                if ( g ) Gia_ManStop(g);
                g = trial;
            } else Gia_ManStop(trial);
        }
        if ( !g ) goto done;
        if ( attempts > 1 ) fprintf(out,"decpla: selected best verified AIG: ANDs = %d  levels = %d\n",Gia_ManAndNum(g),Gia_ManLevelNum(g));
        Abc_FrameUpdateGia(frame,g); result = 0; goto done;
    }
    if ( argc-globalUtilOptind == 2 ) {
        q = Decpla_Read(argv[globalUtilOptind+1],err); if ( !q ) goto done;
        c = Decpla_Compatible(p,q,err);
        if ( c < 0 ) goto done;
        fprintf(out,"decpla: %s (compatibility, not specification equality)\n",c ? "COMPATIBLE" : "INCOMPATIBLE");
        result = !c; goto done;
    }
    if ( minimize ) {
        fprintf(out,"decpla: support method = %s  seed = %u\n", baseline ? "input-order baseline" : "weighted separation",seed);
        if ( baseline ? !Decpla_Minimize(p,err) : !Decpla_MinimizeSeeded(p,seed,8*1024*1024,err) ) goto done;
        for ( i = 0; i < p->nOutputs; ++i ) fprintf(out,"  minimized output %d: on = %lu  off = %lu  support = %d\n",i,(unsigned long)p->pIsfs[i].On.nCubes,(unsigned long)p->pIsfs[i].Off.nCubes,Decpla_SupportSize(&p->pIsfs[i],p->nInputs));
    }
    if ( dest && !Decpla_Write(p,dest,err) ) goto done;
    result = 0;
done:
    Decpla_Free(p); Decpla_Free(q); return result;
usage:
    fprintf(err,"usage: &decpla [-KOSQCN num] [-o file] [-pcmbrwxh] <file> [file2]\n"
                "\t         decomposes and verifies an explicit .type fr PLA by default\n"
                "\t-K num : decomposition attempts with consecutive seeds [default = 1]\n"
                "\t         retain minimum AND count, breaking ties by logic levels\n"
                "\t-O num : output synthesis order [default = 0]\n"
                "\t         0 = file, 1 = smallest first, 2 = largest first, 3 = random\n"
                "\t         size orders use independent AND counts from an extra synthesis pass\n"
                "\t         size ties use file order; the output interface order is preserved\n"
                "\t-S num : unsigned support/grouping seed [default = 0]\n"
                "\t-Q num : independent output-order seed (requires -O 3)\n"
                "\t-C num : final verification conflict limit per SAT query [default = 10000]\n"
                "\t-N num : committed AND limit, excluding speculative nodes [default = 200000]\n"
                "\t-o file: write the FR PLA to a new file, preserving its interface\n"
                "\t-p     : only validate and print PLA statistics; leave the current AIG unchanged\n"
                "\t-c     : verify the current combinational &-space AIG against the PLA (positional)\n"
                "\t-m     : minimize each output support using weighted separation\n"
                "\t-b     : use input-order deletion for support minimization (incompatible with -S)\n"
                "\t-r     : disable completed-function reuse\n"
                "\t-w     : toggle weak AND/OR decomposition [default = yes]\n"
                "\t-x     : toggle XOR decomposition [default = yes]\n"
                "\t-h     : print the command usage\n"
                "\t<file> : input PLA to decompose by default\n"
                "\t[file2]: optional PLA for compatibility checking, using labels if both have them\n"
                "\t         otherwise, ports are matched by position\n"
                "\t         -p, -c, and -m are mutually exclusive and accept one input file\n"
                "\t         -K, -O, -Q, -C, -N, -r, -w, and -x apply only to decomposition\n"
                "\t         -b and -S apply to decomposition or -m; -o requires -p or -m\n"
                "\t         reuse-aware selection and internal-node caching are enabled with reuse\n"
                "\t         use &w <file.aig> after decomposition to write the resulting AIG\n");
    return 1;
}
void Decpla_Init( Abc_Frame_t * p )
{ Cmd_CommandAdd(p,"ABC9","&decpla",Decpla_Command,0); }
ABC_NAMESPACE_IMPL_END
