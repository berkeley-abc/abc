/**CFile****************************************************************

  FileName    [fm_minunsat.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [ForMACE minimum-UNSAT shell command.]

***********************************************************************/

#ifndef ABC__formace_ext__fm_minunsat_h
#define ABC__formace_ext__fm_minunsat_h

#include "misc/util/abc_global.h"
#include "base/main/abcapis.h"

ABC_NAMESPACE_HEADER_START

extern int Fm_CommandMinUnsat( Abc_Frame_t * pAbc, int argc, char ** argv );

ABC_NAMESPACE_HEADER_END

#endif
