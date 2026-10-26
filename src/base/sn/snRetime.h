/**CFile****************************************************************

  FileName    [snRetime.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Restricted word-level retiming interface.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

***********************************************************************/
#ifndef ABC__base__sn__snRetime_h
#define ABC__base__sn__snRetime_h
#include "sn.h"
ABC_NAMESPACE_HEADER_START
// Mutates only the supplied private design. Callers install it after @check.
// ignore_init treats moved state as don't-care, including known initial bits.
// New registers then have no initialization; existing retained state is unchanged.
// Otherwise forward moves evaluate initialization, and backward moves use SAT
// to find a preimage, with no time or conflict limit. Infeasible or interrupted
// moves are excluded.
// Moves preserve matching clock/edge, enable, reset/set signals, polarity and
// sync/async kinds. Reset values are always preserved, independently of ignore_init.
// Visits clock/edge domains separately. Latches, LOOP pairs and opaque objects
// are fixed zero-arrival boundaries; clock cones are protected from moves.
// All RTL operators contribute delay, independently of their move eligibility.
// direction: 0 forward, 1 backward, 2 either.
extern int Sn_DesignRetime(sn_design_t * design, sn_module_id_t module, int preview,
                          int steps, int ignore_init, int direction, int verbose, FILE * out, FILE * error);
// Optional limits: growth is the maximum register bits as a percentage of the
// input module (100..100000); conflicts bounds each initial/reset SAT query.
// Zero disables either limit. A rejected batch retains the best earlier prefix.
extern int Sn_DesignRetimeWithLimits(sn_design_t * design, sn_module_id_t module, int preview,
                                    int steps, int ignore_init, int direction, int verbose,
                                    int growth, int conflicts, FILE * out, FILE * error);
ABC_NAMESPACE_HEADER_END
#endif
