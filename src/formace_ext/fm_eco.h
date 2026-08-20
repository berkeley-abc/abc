/**CFile****************************************************************

  FileName    [fm_eco.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ForMACE ECO with proof interpolation.]

***********************************************************************/

#ifndef ABC__formace_ext__fm_eco_h
#define ABC__formace_ext__fm_eco_h

#include "base/main/main.h"
#include "aig/gia/gia.h"
#include "sat/cnf/cnf.h"

ABC_NAMESPACE_HEADER_START

extern int         Fm_CommandEco( Abc_Frame_t * pAbc, int argc, char ** argv );
extern Gia_Man_t * Fm_EcoDeriveInterpolant( Cnf_Dat_t * pCnf, int iTar,
                                            int nTargets, Vec_Int_t * vUsed,
                                            int fVerbose );

ABC_NAMESPACE_HEADER_END

#endif
