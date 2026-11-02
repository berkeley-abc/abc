/**CFile****************************************************************

  FileName    [decplaRead.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cube-based decomposition of incompletely specified functions.]

  Synopsis    [Strict FR PLA reader and writer.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: decplaRead.c,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "decpla.h"
#include <errno.h>
#include <limits.h>
#include <ctype.h>
ABC_NAMESPACE_IMPL_START

int Decpla_CoverPush( Decpla_Cover_t * p, const word * c )
{
    if ( p->nCubes == p->nCap ) {
        size_t cap = p->nCap ? 2 * p->nCap : 16;
        word * data;
        if ( cap < p->nCap || cap > (size_t)-1 / sizeof(word) / p->nWords ) return 0;
        data = (word *)realloc(p->pData, cap * p->nWords * sizeof(word));
        if ( !data ) return 0;
        p->pData = data; p->nCap = cap;
    }
    memcpy(p->pData + p->nCubes++ * p->nWords, c, p->nWords * sizeof(word));
    return 1;
}
void Decpla_Free( Decpla_Man_t * p )
{
    int i;
    if ( !p ) return;
    for ( i = 0; i < p->nInputs; ++i ) if ( p->pInputs ) free(p->pInputs[i]);
    for ( i = 0; i < p->nOutputs; ++i ) {
        if ( p->pOutputs ) free(p->pOutputs[i]);
        if ( p->pIsfs ) { free(p->pIsfs[i].On.pData); free(p->pIsfs[i].Off.pData); }
    }
    free(p->pInputs); free(p->pOutputs); free(p->pIsfs); free(p);
}
// Local tokenizer: does not use strtok's process-global state.
static char * Decpla_Token( char ** cursor )
{
    char * s = *cursor, * start;
    while ( *s && isspace((unsigned char)*s) ) ++s;
    if ( !*s ) { *cursor = s; return NULL; }
    start = s;
    while ( *s && !isspace((unsigned char)*s) ) ++s;
    if ( *s ) *s++ = 0;
    *cursor = s; return start;
}
static int Decpla_Number( const char * s, int * v )
{
    char * end; long n;
    if ( !s || !isdigit((unsigned char)*s) ) return 0;
    errno = 0; n = strtol(s, &end, 10);
    if ( errno || *end || n > INT_MAX ) return 0;
    *v = (int)n; return 1;
}
static int Decpla_Names( char ** cur, char *** names, int n )
{
    int i, j; char * s;
    *names = (char **)calloc(n, sizeof(char *));
    if ( !*names ) return 0;
    for ( i = 0; i < n; ++i ) {
        s = Decpla_Token(cur);
        if ( !s ) return 0;
        for ( j = 0; j < i; ++j ) if ( !strcmp(s, (*names)[j]) ) return 0;
        (*names)[i] = (char *)malloc(strlen(s)+1);
        if ( !(*names)[i] ) return 0;
        strcpy((*names)[i], s);
    }
    return Decpla_Token(cur) == NULL;
}
Decpla_Man_t * Decpla_Read( const char * file, FILE * err )
{
    FILE * f = fopen(file, "rb");
    Decpla_Man_t * p = NULL;
    char * line = NULL; size_t cap = 0, len, lineno = 0;
    word * cube = NULL;
    int ch, type = 0, ended = 0, products = -1, n, i;
    const char * reason = "out of memory";
    if ( !f ) { fprintf(err, "decpla: cannot open %s\n", file); return NULL; }
    p = (Decpla_Man_t *)calloc(1, sizeof(*p));
    if ( !p ) goto fail;
    for (;;) {
        char * cur, * a, * b, * comment;
        len = 0;
        while ( (ch = fgetc(f)) != EOF && ch != '\n' ) {
            if ( ch == 0 ) { reason = "NUL byte in PLA"; goto fail; }
            if ( len + 1 >= cap ) {
                size_t next = cap ? cap * 2 : 256;
                char * tmp;
                if ( next < cap ) goto fail;
                tmp = (char *)realloc(line, next);
                if ( !tmp ) goto fail;
                line = tmp; cap = next;
            }
            line[len++] = (char)ch;
        }
        if ( !len && ch == EOF ) break;
        ++lineno;
        if ( !line ) { line = (char *)malloc(1); if ( !line ) goto fail; cap = 1; }
        line[len] = 0;
        comment = strchr(line, '#'); if ( comment ) *comment = 0;
        cur = line; a = Decpla_Token(&cur);
        if ( !a ) continue;
        reason = "content after .e";
        if ( ended ) goto fail;
        if ( a[0] == '.' ) {
            reason = "header directive after product rows";
            if ( p->nRows && strcmp(a, ".e") && strcmp(a, ".end") ) goto fail;
            reason = "invalid or repeated directive";
            if ( !strcmp(a, ".ilb") || !strcmp(a, ".ob") ) {
                int input = !strcmp(a, ".ilb");
                char *** names = input ? &p->pInputs : &p->pOutputs;
                n = input ? p->nInputs : p->nOutputs;
                reason = "invalid, duplicate, or missing labels";
                if ( !n || *names || !Decpla_Names(&cur, names, n) ) goto fail;
                continue;
            }
            b = Decpla_Token(&cur);
            if ( Decpla_Token(&cur) ) goto fail;
            if ( !strcmp(a, ".i") ) {
                if ( p->nInputs || !Decpla_Number(b, &n) || n < 1 || n > 1000000 ) goto fail;
                p->nInputs = n;
            } else if ( !strcmp(a, ".o") ) {
                if ( p->nOutputs || !Decpla_Number(b, &n) || n < 1 || n > 1000000 ) goto fail;
                p->nOutputs = n;
            } else if ( !strcmp(a, ".p") ) {
                if ( products >= 0 || !Decpla_Number(b, &products) ) goto fail;
            } else if ( !strcmp(a, ".type") ) {
                reason = "only explicit .type fr is supported";
                if ( type || !b || strcmp(b, "fr") ) goto fail;
                type = 1;
            } else if ( !strcmp(a, ".e") || !strcmp(a, ".end") ) {
                if ( b ) goto fail;
                ended = 1;
            } else { reason = "unsupported directive"; goto fail; }
            continue;
        }
        reason = "expected .i, .o, and .type fr before rows";
        if ( !p->nInputs || !p->nOutputs || !type ) goto fail;
        if ( !p->pIsfs ) {
            n = (p->nInputs + 31) / 32;
            p->pIsfs = (Decpla_Isf_t *)calloc(p->nOutputs, sizeof(Decpla_Isf_t));
            cube = (word *)calloc(n, sizeof(word));
            reason = "out of memory";
            if ( !p->pIsfs || !cube ) goto fail;
            for ( i = 0; i < p->nOutputs; ++i ) p->pIsfs[i].On.nWords = p->pIsfs[i].Off.nWords = n;
        }
        b = Decpla_Token(&cur);
        reason = "invalid product width or extra tokens";
        if ( !b || strlen(a) != (size_t)p->nInputs || strlen(b) != (size_t)p->nOutputs || Decpla_Token(&cur) ) goto fail;
        memset(cube, 0, p->pIsfs[0].On.nWords * sizeof(word));
        reason = "invalid cube character (expected 0, 1, or -)";
        for ( i = 0; i < p->nInputs; ++i ) {
            if ( a[i] != '0' && a[i] != '1' && a[i] != '-' ) goto fail;
            Decpla_CubeSet(cube, i, a[i] == '-' ? 0 : a[i] == '0' ? 1 : 2);
        }
        for ( i = 0; i < p->nOutputs; ++i ) {
            if ( b[i] == '-' ) continue;
            if ( b[i] != '0' && b[i] != '1' ) goto fail;
            if ( !Decpla_CoverPush(b[i] == '1' ? &p->pIsfs[i].On : &p->pIsfs[i].Off, cube) ) { reason = "out of memory"; goto fail; }
        }
        ++p->nRows;
    }
    reason = "incomplete header, missing .e, I/O error, or .p count mismatch";
    if ( ferror(f) || !ended || !type || !p->nInputs || !p->nOutputs || (products >= 0 && (size_t)products != p->nRows) ) goto fail;
    if ( !p->pIsfs ) {
        p->pIsfs = (Decpla_Isf_t *)calloc(p->nOutputs, sizeof(Decpla_Isf_t));
        if ( !p->pIsfs ) { reason = "out of memory"; goto fail; }
        for ( i = 0; i < p->nOutputs; ++i ) p->pIsfs[i].On.nWords = p->pIsfs[i].Off.nWords = (p->nInputs+31)/32;
    }
    fclose(f); free(line); free(cube);
    if ( !Decpla_Check(p, err) ) { Decpla_Free(p); return NULL; }
    return p;
fail:
    fprintf(err, "decpla: %s:%lu: %s\n", file, (unsigned long)lineno, reason);
    fclose(f); free(line); free(cube); Decpla_Free(p); return NULL;
}
int Decpla_Write( const Decpla_Man_t * p, const char * file, FILE * err )
{
    FILE * f = fopen(file, "w"); int i, j, phase, ok; size_t k, count = 0;
    if ( !f ) { fprintf(err, "decpla: cannot write %s\n", file); return 0; }
    for ( i = 0; i < p->nOutputs; ++i ) count += p->pIsfs[i].On.nCubes + p->pIsfs[i].Off.nCubes;
    fprintf(f, ".i %d\n.o %d\n.type fr\n", p->nInputs, p->nOutputs);
    if ( p->pInputs ) { fprintf(f, ".ilb"); for ( i = 0; i < p->nInputs; ++i ) fprintf(f, " %s", p->pInputs[i]); fprintf(f, "\n"); }
    if ( p->pOutputs ) { fprintf(f, ".ob"); for ( i = 0; i < p->nOutputs; ++i ) fprintf(f, " %s", p->pOutputs[i]); fprintf(f, "\n"); }
    fprintf(f, ".p %lu\n", (unsigned long)count);
    for ( i = 0; i < p->nOutputs; ++i ) for ( phase = 0; phase < 2; ++phase ) {
        const Decpla_Cover_t * c = phase ? &p->pIsfs[i].On : &p->pIsfs[i].Off;
        for ( k = 0; k < c->nCubes; ++k ) {
            for ( j = 0; j < p->nInputs; ++j ) fputc("-01"[Decpla_CubeLit(c->pData + k*c->nWords, j)], f);
            fputc(' ', f);
            for ( j = 0; j < p->nOutputs; ++j ) fputc(j == i ? '0'+phase : '-', f);
            fputc('\n', f);
        }
    }
    fprintf(f, ".e\n"); ok = !ferror(f); if ( fclose(f) ) ok = 0;
    if ( !ok ) fprintf(err, "decpla: write failed: %s\n", file);
    return ok;
}
ABC_NAMESPACE_IMPL_END
