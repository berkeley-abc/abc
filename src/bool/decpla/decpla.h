/**CFile****************************************************************

  FileName    [decpla.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cube-based decomposition of incompletely specified functions.]

  Synopsis    [Minimal packed cube covers and public operations.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: decpla.h,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__bool__decpla__decpla_h
#define ABC__bool__decpla__decpla_h
#include "misc/util/abc_global.h"
ABC_NAMESPACE_HEADER_START

// Two bits per input: 00 = don't-care, 01 = zero, 10 = one.
// 11 is a contradiction and is never stored. Cubes are contiguous;
// padding bits are zero. Missing points in an ISF are unspecified.
typedef struct Decpla_Cover_t_ {
    word * pData;
    size_t nCubes, nCap;
    int nWords;
} Decpla_Cover_t;
typedef struct Decpla_Isf_t_ {
    Decpla_Cover_t On, Off;
} Decpla_Isf_t;
typedef struct Decpla_Man_t_ {
    int nInputs, nOutputs;
    char ** pInputs, ** pOutputs; // NULL means positional interface.
    Decpla_Isf_t * pIsfs;
    size_t nRows;
} Decpla_Man_t;

static inline unsigned Decpla_CubeLit( const word * p, int i )
{ return (unsigned)((p[i / 32] >> (2 * (i % 32))) & 3); }
static inline void Decpla_CubeSet( word * p, int i, unsigned v )
{ p[i / 32] = (p[i / 32] & ~((word)3 << (2 * (i % 32)))) | ((word)v << (2 * (i % 32))); }

extern int Decpla_CoverPush( Decpla_Cover_t * p, const word * pCube );
extern Decpla_Man_t * Decpla_Read( const char * pFile, FILE * pErr );
extern void Decpla_Free( Decpla_Man_t * p );
extern int Decpla_Write( const Decpla_Man_t * p, const char * pFile, FILE * pErr );
extern int Decpla_Check( const Decpla_Man_t * p, FILE * pErr );
extern int Decpla_SupportSize( const Decpla_Isf_t * p, int nInputs );
extern int Decpla_Minimize( Decpla_Man_t * p, FILE * pErr );
// Weighted hitting set, then baseline pruning. Zero cache bytes forces
// streaming; the cache changes memory/time only, never selection results.
extern int Decpla_MinimizeSeeded( Decpla_Man_t * p, unsigned Seed, size_t nCacheBytes, FILE * pErr );
// Return 1 compatible, 0 conflicting requirements, -1 interface error.
// Compatibility is not specification equality or implementation proof.
extern int Decpla_Compatible( const Decpla_Man_t * p, const Decpla_Man_t * q, FILE * pErr );
typedef struct Gia_Man_t_ Gia_Man_t;
typedef struct Decpla_Options_t_ {
    unsigned Seed;
    unsigned OrderSeed;
    int fOrderSeed; // independent output-order stream; otherwise preserve legacy Seed behavior
    int nCubesMax, nWorkMax, nNodesMax, nConfLimit;
    // nNodesMax limits distinct ANDs reachable from completed outputs.
    int fBaseline, fReuse;
    int OutputOrder; // 0 file, 1 ascending independent AND count, 2 descending, 3 random
    unsigned Features; // 1 weak, 2 reuse-aware, 4 internal-node reuse, 8 XOR, 16 early reuse, 32 BDC leaves, 64 root reuse
} Decpla_Options_t;
extern void Decpla_OptionsDefault( Decpla_Options_t * p );
// Returns a verified combinational AIG, or NULL. Does not mutate the PLA.
extern Gia_Man_t * Decpla_Decompose( const Decpla_Man_t * p, const Decpla_Options_t * options, FILE * out, FILE * err );
// 1 proved, 0 mismatch, -1 resource/solver failure. Positional interfaces.
extern int Decpla_Verify( const Decpla_Man_t * p, Gia_Man_t * g, int nConfLimit, FILE * err );
ABC_NAMESPACE_HEADER_END
#endif
