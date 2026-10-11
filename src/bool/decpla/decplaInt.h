/**CFile****************************************************************

  FileName    [decplaInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cube-based decomposition of incompletely specified functions.]

  Synopsis    [Internal AIG/cube verification interface.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: decplaInt.h,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__bool__decpla__decplaInt_h
#define ABC__bool__decpla__decplaInt_h
#include "decpla.h"
#include "aig/gia/gia.h"
ABC_NAMESPACE_HEADER_START
// The optional order is a permutation of all declared input indices.
extern int Decpla_MinimizeOrder( Decpla_Man_t * p, const int * order, FILE * err );
typedef struct Decpla_Sat_t_ Decpla_Sat_t;
extern Decpla_Sat_t * Decpla_SatStart( Gia_Man_t * g );
extern void Decpla_SatStop( Decpla_Sat_t * p );
// Prepare the literal's cone; return its work cost (at least one), or -1 on error.
extern int Decpla_ConePrepare( Decpla_Sat_t * p, int literal );
// First unspecified cone input in the last cube evaluation, or -1 if none.
extern int Decpla_CubeSplit( Decpla_Sat_t * p );
// Universal cube evaluation: 0/1 proved constant, 2 unknown, -1 error.
extern int Decpla_CubeEval( Decpla_Sat_t * p, const word * cube, int literal );
// Is the literal equal to value everywhere on cube? 1 yes, 0 no, -1 unknown/error.
extern int Decpla_CubeProve( Decpla_Sat_t * p, const word * cube, int literal, int value, int limit );
ABC_NAMESPACE_HEADER_END
#endif
