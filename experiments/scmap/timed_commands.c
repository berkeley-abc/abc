#define _POSIX_C_SOURCE 200809L
#include "base/main/main.h"
#include "base/cmd/cmd.h"
#include "base/abc/abc.h"
#include <time.h>

#ifdef ABC_NAMESPACE
using namespace ABC_NAMESPACE;
#endif

static double ReadClock( clockid_t Id )
{
    struct timespec Time;
    if ( clock_gettime(Id, &Time) != 0 )
    {
        perror("clock_gettime");
        exit(2);
    }
    return Time.tv_sec + 1.0e-9 * Time.tv_nsec;
}

int main( int argc, char ** argv )
{
    Abc_Frame_t * pAbc, * pPrevious;
    FILE * pScript, * pTimes;
    char * pLine = NULL;
    size_t Capacity = 0;
    int Status = 0, Line = 0;
    if ( argc != 3 )
    {
        fprintf(stderr, "usage: %s commands.abc timings.tsv\n", argv[0]);
        return 2;
    }
    pScript = fopen(argv[1], "r");
    if ( !pScript ) { perror(argv[1]); return 2; }
    pTimes = fopen(argv[2], "w");
    if ( !pTimes ) { perror(argv[2]); fclose(pScript); return 2; }
    fprintf(pTimes, "line\tstatus\tcpu_seconds\twall_seconds\tcommand\n");
    pAbc = Abc_FrameCreate();
    if ( !pAbc ) { fclose(pTimes); fclose(pScript); return 2; }
    pPrevious = Abc_FrameEnter(pAbc);
    while ( getline(&pLine, &Capacity, pScript) >= 0 )
    {
        double Cpu, Wall;
        Line++;
        pLine[strcspn(pLine, "\r\n")] = '\0';
        if ( !pLine[0] || pLine[0] == '#' ) continue;
        printf("\n@@BEGIN %d %s\n", Line, pLine);
        fflush(stdout);
        Cpu = ReadClock(CLOCK_PROCESS_CPUTIME_ID);
        Wall = ReadClock(CLOCK_MONOTONIC);
        Status = Cmd_CommandExecute(pAbc, pLine);
        Wall = ReadClock(CLOCK_MONOTONIC) - Wall;
        Cpu = ReadClock(CLOCK_PROCESS_CPUTIME_ID) - Cpu;
        fprintf(pTimes, "%d\t%d\t%.9f\t%.9f\t%s\n", Line, Status, Cpu, Wall, pLine);
        fflush(pTimes);
        printf("@@END %d status=%d\n", Line, Status);
        fflush(stdout);
        if ( Status ) break;
    }
    if ( ferror(pScript) ) Status = 2;
    free(pLine);
    fclose(pScript);
    Abc_FrameLeave(pPrevious);
    Abc_FrameDestroy(pAbc);
    if ( fclose(pTimes) ) Status = 2;
    return Status ? 1 : 0;
}
