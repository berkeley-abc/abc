/**CFile****************************************************************

  FileName    [fxu.h]

  PackageName [MVSIS 2.0: Multi-valued logic synthesis system.]

  Synopsis    [External declarations of fast extract for unate covers.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - February 1, 2003.]

  Revision    [$Id: fxu.h,v 1.0 2003/02/01 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __FXU_H__
#define __FXU_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "vec.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

#ifndef bool
#define bool int
#endif

typedef struct FxuDataStruct   Fxu_Data_t;

// structure for the FX input/output data 
struct FxuDataStruct
{
    // user specified parameters
    bool              fOnlyS;           // set to 1 to have only single-cube divs
    bool              fOnlyD;           // set to 1 to have only double-cube divs
    bool              fUse0;            // set to 1 to have 0-weight also extracted
    bool              fUseCompl;        // set to 1 to have complement taken into account
    bool              fVerbose;         // set to 1 to have verbose output
    int               nPairsMax;        // the maximum number of cube pairs to consider
/*
    // parameters of the network
    int               fMvNetwork;       // the network has some MV nodes
    // the information about nodes
    int               nNodesCi;         // the number of CI nodes of the network
    int               nNodesInt;        // the number of internal nodes of the network
    int               nNodesOld;        // the number of CI and int nodes
    int               nNodesNew;        // the number of added nodes
    int               nNodesExt;        // the max number of (binary) nodes to be added by FX
    int               nNodesAlloc;      // the total number of all nodes
    int *             pNode2Value;      // for each node, the number of its first value
    // the information about values
    int               nValuesCi;        // the total number of values of CI nodes
    int               nValuesInt;       // the total number of values of int nodes
    int               nValuesOld;       // the number of CI and int values
    int               nValuesNew;       // the number of values added nodes
    int               nValuesExt;       // the total number of values of the added nodes
    int               nValuesAlloc;     // the total number of all values of all nodes
    int *             pValue2Node;      // for each value, the number of its node
    // the information about covers
    Mvc_Cover_t **    ppCovers;         // for each value, the corresponding cover
    Mvc_Cover_t **    ppCoversNew;      // for each value, the corresponding cover after FX
    // the MVC manager
    Mvc_Manager_t *   pManMvc;
*/
    // statistics   
    int               nNodesOld;        // the old number of nodes
    int               nNodesExt;        // the number of divisors to extract
    int               nNodesNew;        // the number of divisors extracted

    // the input information
    Vec_Ptr_t *       vSops;            // the SOPs for each node in the network
    Vec_Ptr_t *       vFanins;          // the fanins of each node in the network
    // output information
    Vec_Ptr_t *       vSopsNew;         // the SOPs for each node in the network after extraction
    Vec_Ptr_t *       vFaninsNew;       // the fanins of each node in the network after extraction
    // the SOP manager
    Extra_MmFlex_t *  pManSop;
};

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFITIONS                            ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/*===== fxu.c ==========================================================*/
extern int          Fxu_FastExtract( Fxu_Data_t * pData );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

