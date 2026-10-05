/**CFile****************************************************************

  FileName    [lmsBuiltin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation.]

  Synopsis    [Encode and lazily decode the embedded AIGER library.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 5, 2026.]

  Revision    [$Id: lmsBuiltin.c,v 1.00 2026/10/05 00:00:00 alanmi Exp $]

***********************************************************************/
#include "lms.h"
#include <errno.h>
#include <fcntl.h>
#ifndef O_BINARY
#define O_BINARY 0
#endif
#ifdef _MSC_VER
#include <io.h>
#include <sys/stat.h>
#else
#include <unistd.h>
#endif

ABC_NAMESPACE_IMPL_START

#include "lmsBuiltinData.inc"

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// This maintenance format preserves the header and trailer verbatim, keeps
// output literals as unsigned integers, and Base64-encodes only AND deltas.
// It accepts canonical six-input, zero-register binary AIGER libraries.
typedef char Lms_UnsignedMustBe32Bits[(sizeof(unsigned) == 4) ? 1 : -1];
static unsigned Lms_EmbedChecksum( const unsigned char * p, int n )
{
    unsigned Hash = 2166136261u;
    int i;
    for ( i = 0; i < n; i++ )
        Hash = (Hash ^ p[i]) * 16777619u;
    return Hash;
}
static int Lms_EmbedBase64Value( unsigned char c )
{
    if ( c >= 'A' && c <= 'Z' ) return c-'A';
    if ( c >= 'a' && c <= 'z' ) return c-'a'+26;
    if ( c >= '0' && c <= '9' ) return c-'0'+52;
    if ( c == '+' ) return 62;
    if ( c == '/' ) return 63;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Reconstruct the exact AIGER bytes from the compact initializer.]

  Description [Returns writable, zero-terminated storage owned by the caller,
  or NULL on invalid data/allocation failure. Length excludes the terminator.
  Short independent string rows avoid compiler limits on long C strings.
  The checksum detects accidental corruption, not malicious modification.]

  SideEffects [Allocates memory, without file I/O or loading an LMS manager.]

  SeeAlso     [Lms_EmbedWrite]

***********************************************************************/
char * Lms_BuiltinDecode( int * pnBytes )
{
    char * pData, * p;
    char Number[16];
    size_t i, j, nRows = sizeof(s_LmsBuiltinAnds)/sizeof(s_LmsBuiltinAnds[0]);
    int n, a, b, c, d, nAnd = 0;
    unsigned Value;
    *pnBytes = 0;
    if ( LMS_BUILTIN_SIZE <= 0 || LMS_BUILTIN_SIZE >= (1 << 24) ||
         sizeof(s_LmsBuiltinHeader) > LMS_BUILTIN_SIZE ) return NULL;
    pData = ABC_ALLOC(char, LMS_BUILTIN_SIZE+1);
    if ( !pData ) return NULL;
    p = pData;
    memcpy(p, s_LmsBuiltinHeader, sizeof(s_LmsBuiltinHeader));
    p += sizeof(s_LmsBuiltinHeader);
    for ( i = 0; i < sizeof(s_LmsBuiltinOutputs)/sizeof(unsigned); i++ )
    {
        n = sprintf(Number, "%u\n", s_LmsBuiltinOutputs[i]);
        if ( n > LMS_BUILTIN_SIZE-(p-pData) ) goto fail;
        memcpy(p, Number, n); p += n;
    }
    if ( LMS_BUILTIN_AND_SIZE > LMS_BUILTIN_SIZE-(p-pData) ) goto fail;
    for ( i = 0; i < nRows; i++ )
    {
        const char * pRow = s_LmsBuiltinAnds[i];
        const char * pZero = (const char *)memchr(pRow, 0, sizeof(s_LmsBuiltinAnds[0]));
        if ( !pZero || (pZero-pRow) % 4 ) goto fail;
        for ( j = 0; j < (size_t)(pZero-pRow); j += 4 )
        {
            a = Lms_EmbedBase64Value(pRow[j]);
            b = Lms_EmbedBase64Value(pRow[j+1]);
            c = pRow[j+2] == '=' ? 0 : Lms_EmbedBase64Value(pRow[j+2]);
            d = pRow[j+3] == '=' ? 0 : Lms_EmbedBase64Value(pRow[j+3]);
            if ( a < 0 || b < 0 || c < 0 || d < 0 ) goto fail;
            n = pRow[j+2] == '=' ? 1 : pRow[j+3] == '=' ? 2 : 3;
            if ( n < 3 && (i+1 != nRows || j+4 != (size_t)(pZero-pRow)) ) goto fail;
            if ( n == 1 && (pRow[j+3] != '=' || (b & 15)) ) goto fail;
            if ( n == 2 && (c & 3) ) goto fail;
            if ( n > LMS_BUILTIN_AND_SIZE-nAnd ) goto fail;
            Value = ((unsigned)a << 18) | ((unsigned)b << 12) | ((unsigned)c << 6) | (unsigned)d;
            *p++ = (char)(Value >> 16);
            if ( n > 1 ) *p++ = (char)(Value >> 8);
            if ( n > 2 ) *p++ = (char)Value;
            nAnd += n;
        }
    }
    if ( nAnd != LMS_BUILTIN_AND_SIZE || LMS_BUILTIN_TAIL_SIZE > (int)sizeof(s_LmsBuiltinTail) ||
         LMS_BUILTIN_TAIL_SIZE != LMS_BUILTIN_SIZE-(p-pData) ) goto fail;
    memcpy(p, s_LmsBuiltinTail, LMS_BUILTIN_TAIL_SIZE);
    pData[LMS_BUILTIN_SIZE] = 0;
    if ( Lms_EmbedChecksum((unsigned char *)pData, LMS_BUILTIN_SIZE) != LMS_BUILTIN_CHECKSUM ) goto fail;
    *pnBytes = LMS_BUILTIN_SIZE;
    return pData;
fail:
    ABC_FREE(pData);
    return NULL;
}
static int Lms_EmbedNumber( const unsigned char ** pp, const unsigned char * pEnd, unsigned * pValue )
{
    const unsigned char * p = *pp, * pStart = p;
    unsigned Value = 0;
    while ( p < pEnd && *p >= '0' && *p <= '9' )
    {
        if ( Value > (0xffffffffu - (*p - '0')) / 10u ) return 0;
        Value = 10u * Value + (*p++ - '0');
    }
    if ( p == pStart || p == pEnd || *p++ != '\n' || (p-pStart > 2 && *pStart == '0') ) return 0;
    *pp = p;
    *pValue = Value;
    return 1;
}
static int Lms_EmbedDelta( const unsigned char ** pp, const unsigned char * pEnd, unsigned * pValue )
{
    unsigned Value = 0, Byte;
    int Shift;
    for ( Shift = 0; Shift <= 28; Shift += 7 )
    {
        if ( *pp == pEnd ) return 0;
        Byte = *(*pp)++;
        if ( Shift == 28 && (Byte & 0xf0) ) return 0;
        Value |= (Byte & 127u) << Shift;
        if ( !(Byte & 128u) ) { *pValue = Value; return 1; }
    }
    return 0;
}
static void Lms_EmbedBytes( FILE * pFile, const char * pName, const unsigned char * pData, int nBytes )
{
    int i;
    fprintf(pFile, "static const unsigned char %s[] = {\n", pName);
    if ( !nBytes ) fprintf(pFile, "    0\n");
    for ( i = 0; i < nBytes; i++ )
    {
        if ( i % 16 == 0 ) fprintf(pFile, "    ");
        fprintf(pFile, "0x%02x,%s", (unsigned)pData[i], i % 16 == 15 || i+1 == nBytes ? "\n" : "");
    }
    fprintf(pFile, "};\n");
}
static FILE * Lms_EmbedOpen( const char * pName, FILE * pError )
{
    FILE * pFile;
    int fd;
    // Reserve atomically, including against another encoder or a symlink.
#ifdef _MSC_VER
    fd = _open(pName, _O_WRONLY|_O_CREAT|_O_EXCL|_O_BINARY, _S_IREAD|_S_IWRITE);
#else
    fd = open(pName, O_WRONLY|O_CREAT|O_EXCL|O_BINARY, 0666);
#endif
    if ( fd < 0 )
    {
        if ( errno == EEXIST ) fprintf(pError, "Error: LMS output already exists: %s\n", pName);
        else fprintf(pError, "Error: cannot create LMS output %s: %s\n", pName, strerror(errno));
        return NULL;
    }
#ifdef _MSC_VER
    pFile = _fdopen(fd, "wb");
    if ( !pFile ) _close(fd);
#else
    pFile = fdopen(fd, "wb");
    if ( !pFile ) close(fd);
#endif
    if ( !pFile )
    {
        remove(pName);
        fprintf(pError, "Error: cannot open LMS output stream: %s\n", pName);
    }
    return pFile;
}

/**Function*************************************************************

  Synopsis    [Write a portable C initializer from a validated LMS library.]

  Description [Does not load or replace the active LMS manager. Output must
  not already exist. The bounded parser checks layout and literal ranges;
  callers should validate library functions before publishing the result.]

  SideEffects [Writes the requested file.]

  SeeAlso     [Lms_BuiltinDecode]

***********************************************************************/
int Lms_EmbedWrite( const char * pInput, const char * pOutput, FILE * pError )
{
    static const char Alphabet[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    FILE * pFile = fopen(pInput, "rb");
    unsigned char * pData = NULL;
    const unsigned char * p, * pEnd, * pAnd, * pTail;
    unsigned * pOutputs = NULL, nMax, nInputs, nRegs, nOutputs, nAnds, d0, d1, i;
    int nBytes, nHeader, nAndBytes, nTail, nChars = 0, c, k, fOk = 0;
    long Size;
    char Header[160], Quartet[4];
    if ( !pFile )
    {
        fprintf(pError, "Error: cannot read LMS input %s: %s\n", pInput, strerror(errno));
        return 0;
    }
    if ( fseek(pFile, 0, SEEK_END) || (Size = ftell(pFile)) <= 0 )
        goto malformed;
    if ( Size >= (1 << 24) )
    {
        fprintf(pError, "Error: LMS input %s is %ld bytes; rec_embed3 requires less than 16 MiB (16777216 bytes).\n", pInput, Size);
        goto cleanup;
    }
    if ( fseek(pFile, 0, SEEK_SET) ) goto malformed;
    nBytes = (int)Size;
    pData = ABC_ALLOC(unsigned char, nBytes+1);
    if ( !pData || fread(pData, 1, nBytes, pFile) != (size_t)nBytes ) goto malformed;
    fclose(pFile); pFile = NULL;
    pData[nBytes] = 0;
    pEnd = pData + nBytes;
    p = (const unsigned char *)memchr(pData, '\n', nBytes);
    if ( !p || p-pData >= (int)sizeof(Header)-1 ) goto malformed;
    nHeader = (int)(p+1-pData);
    memcpy(Header, pData, nHeader); Header[nHeader] = 0;
    if ( sscanf(Header, "aig %u %u %u %u %u", &nMax, &nInputs, &nRegs, &nOutputs, &nAnds) != 5 ) goto malformed;
    if ( nInputs != 6 || nRegs || !nOutputs || nAnds > (unsigned)nBytes/2 || nOutputs > (unsigned)nBytes/2 || nMax != 6+nAnds ) goto malformed;
    sprintf(Header, "aig %u %u %u %u %u\n", nMax, nInputs, nRegs, nOutputs, nAnds);
    if ( (int)strlen(Header) != nHeader || memcmp(Header, pData, nHeader) ) goto malformed;
    pOutputs = ABC_ALLOC(unsigned, nOutputs);
    if ( !pOutputs ) goto malformed;
    p = pData + nHeader;
    for ( i = 0; i < nOutputs; i++ )
        if ( !Lms_EmbedNumber(&p, pEnd, &pOutputs[i]) || pOutputs[i] > 2*nMax+1 ) goto malformed;
    pAnd = p;
    for ( i = 0; i < nAnds; i++ )
        if ( !Lms_EmbedDelta(&p, pEnd, &d0) || !Lms_EmbedDelta(&p, pEnd, &d1) || !d0 || d0 > 2*(7+i) || d1 > 2*(7+i)-d0 ) goto malformed;
    pTail = p;
    nAndBytes = (int)(pTail-pAnd);
    nTail = (int)(pEnd-pTail);
    pFile = Lms_EmbedOpen(pOutput, pError);
    if ( !pFile ) goto cleanup;
    fprintf(pFile,
        "/**HFile****************************************************************\n\n"
        "  FileName    [lmsBuiltinData.inc]\n\n"
        "  SystemName  [ABC: Logic synthesis and verification system.]\n\n"
        "  PackageName [LMS library generation.]\n\n"
        "  Synopsis    [Generated compact AIGER data; do not edit manually.]\n\n"
        "  Author      [Alan Mishchenko]\n\n"
        "  Affiliation [UC Berkeley]\n\n"
        "  Date        [Ver. 1.0. Started - October 5, 2026.]\n\n"
        "  Revision    [$Id: lmsBuiltinData.inc,v 1.00 2026/10/05 00:00:00 alanmi Exp $]\n\n"
        "***********************************************************************/\n"
        "// Generated by rec_embed3. Unsigned output literals and Base64 ANDs.\n"
        "#define LMS_BUILTIN_SIZE %d\n"
        "#define LMS_BUILTIN_AND_SIZE %d\n"
        "#define LMS_BUILTIN_TAIL_SIZE %d\n"
        "#define LMS_BUILTIN_CHECKSUM 0x%08xu\n",
        nBytes, nAndBytes, nTail, Lms_EmbedChecksum(pData, nBytes));
    Lms_EmbedBytes(pFile, "s_LmsBuiltinHeader", pData, nHeader);
    fprintf(pFile, "static const unsigned s_LmsBuiltinOutputs[] = {\n");
    for ( i = 0; i < nOutputs; i++ )
    {
        if ( i % 12 == 0 ) fprintf(pFile, "    ");
        fprintf(pFile, "%u,%s", pOutputs[i], i % 12 == 11 || i+1 == nOutputs ? "\n" : "");
    }
    fprintf(pFile, "};\nstatic const char s_LmsBuiltinAnds[][77] = {\n");
    for ( c = 0; c < nAndBytes; c += 3 )
    {
        unsigned Value = (unsigned)pAnd[c] << 16;
        if ( c+1 < nAndBytes ) Value |= (unsigned)pAnd[c+1] << 8;
        if ( c+2 < nAndBytes ) Value |= pAnd[c+2];
        Quartet[0] = Alphabet[Value >> 18];
        Quartet[1] = Alphabet[(Value >> 12) & 63];
        Quartet[2] = c+1 < nAndBytes ? Alphabet[(Value >> 6) & 63] : '=';
        Quartet[3] = c+2 < nAndBytes ? Alphabet[Value & 63] : '=';
        for ( k = 0; k < 4; k++, nChars++ )
        {
            if ( nChars % 76 == 0 ) fprintf(pFile, "    \"");
            fputc(Quartet[k], pFile);
            if ( nChars % 76 == 75 ) fprintf(pFile, "\",\n");
        }
    }
    if ( nChars % 76 ) fprintf(pFile, "\",\n");
    if ( !nChars ) fprintf(pFile, "    \"\",\n");
    fprintf(pFile, "};\n");
    Lms_EmbedBytes(pFile, "s_LmsBuiltinTail", pTail, nTail);
    fOk = !ferror(pFile);
    if ( fclose(pFile) ) fOk = 0;
    pFile = NULL;
    if ( !fOk )
    {
        fprintf(pError, "Error: failed writing LMS output %s.\n", pOutput);
        remove(pOutput);
    }
    goto cleanup;
malformed:
    fprintf(pError, "Error: expected a canonical six-input, zero-register binary AIGER library (under 16 MiB): %s\n", pInput);
cleanup:
    if ( pFile ) fclose(pFile);
    ABC_FREE(pOutputs);
    ABC_FREE(pData);
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Export the compiled-in library using the lazy-load decoder.]

  Description [Does not parse the resulting AIGER or create an LMS manager.]

  SideEffects [Writes a new file; never replaces an existing output.]

  SeeAlso     [Lms_BuiltinDecode Lms_EmbedWrite]

***********************************************************************/
int Lms_BuiltinWrite( const char * pOutput, FILE * pError )
{
    int nBytes, fOk;
    char * pData = Lms_BuiltinDecode(&nBytes);
    FILE * pFile;
    if ( !pData )
    {
        fprintf(pError, "Error: cannot decode the built-in LMS library.\n");
        return 0;
    }
    pFile = Lms_EmbedOpen(pOutput, pError);
    if ( !pFile ) { ABC_FREE(pData); return 0; }
    fOk = fwrite(pData, 1, nBytes, pFile) == (size_t)nBytes;
    ABC_FREE(pData);
    if ( fclose(pFile) ) fOk = 0;
    if ( !fOk )
    {
        fprintf(pError, "Error: failed writing LMS output %s.\n", pOutput);
        remove(pOutput);
    }
    return fOk;
}

ABC_NAMESPACE_IMPL_END
