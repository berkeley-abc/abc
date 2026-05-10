/**CFile****************************************************************

  FileName    [emap.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Multi-output gate mapper.]

  Synopsis    [External declarations.]

***********************************************************************/

#ifndef ABC__map__emap__emap_h
#define ABC__map__emap__emap_h

#include "base/main/main.h"

ABC_NAMESPACE_HEADER_START

typedef struct Abc_Ntk_t_ Abc_Ntk_t;
typedef struct Mio_LibraryStruct_t_ Mio_Library_t;

extern void Emap_Init   ( Abc_Frame_t * pAbc );
extern void Emap_End    ( Abc_Frame_t * pAbc );
extern int  Emap_Command( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Abc_Ntk_t * Emap_ManMapAigStructural( Abc_Ntk_t * pNtk, Mio_Library_t * pLib, int fUseMogs, int fAreaMode, int fVerbose );

ABC_NAMESPACE_HEADER_END

#endif
