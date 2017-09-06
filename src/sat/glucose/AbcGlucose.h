/**CFile****************************************************************

  FileName    [AbcGlucose.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT solver Glucose 3.0.]

  Synopsis    [Interface to Glucose.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 6, 2017.]

  Revision    [$Id: AbcGlucose.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SRC_EXTSAT_GLUCOSE_ABC_H_
#define SRC_EXTSAT_GLUCOSE_ABC_H_

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig/gia/gia.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct ExtSat_Pars_ ExtSat_Pars;
struct ExtSat_Pars_ {
    int pre;     // preprocessing
    int verb;    // verbosity
    int cust;    // customizable
    int nConfls; // conflict limit (0 = no limit)
};

static inline ExtSat_Pars ExtSat_CreatePars(int p, int v, int c, int nConfls)
{
    ExtSat_Pars pars;
    pars.pre = p;
    pars.verb = v;
    pars.cust = c;
    pars.nConfls = nConfls;
    return pars;
}

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

extern void Glucose_SolveCnf( char * pFilename, ExtSat_Pars * pPars );
extern int  Glucose_SolveAig( Gia_Man_t * p, ExtSat_Pars * pPars );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

