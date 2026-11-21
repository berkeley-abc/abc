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

typedef struct Emap_Par_t_ Emap_Par_t;
struct Emap_Par_t_
{
    int              nCutNum;       // priority cuts per node
    int              nFlowRounds;   // area-flow rounds
    int              nAreaRounds;   // exact-area rounds
    int              fUseMogs;      // use multi-output gates
    int              fAreaMode;     // area mode without required times
    int              fNldm;         // use NLDM timing if a Liberty library is loaded
    int              nPropBudget;   // incremental timing budget: retimed nodes per AIG node and round (0 = no limit)
    float            DelayTarget;   // delay target (0 = the best delay)
    int              fLegacy;       // run the original implementation
    int              fVerbose;      // verbose output
};

extern void Emap_Init   ( Abc_Frame_t * pAbc );
extern void Emap_End    ( Abc_Frame_t * pAbc );
extern int  Emap_Command( Abc_Frame_t * pAbc, int argc, char ** argv );

extern Abc_Ntk_t * Emap_ManMapAigStructural( Abc_Ntk_t * pNtk, Mio_Library_t * pLib, int fUseMogs, int fAreaMode, int fVerbose );
extern Abc_Ntk_t * Emap_ManMapNew( Abc_Ntk_t * pNtk, Mio_Library_t * pLib, Emap_Par_t * pPars );

ABC_NAMESPACE_HEADER_END

#endif
