/**CFile****************************************************************

  FileName    [giaSolver.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Circuit-based SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSolver.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sat_Cla_t_ Sat_Cla_t;
struct Sat_Cla_t_
{
    unsigned       hWatch0;          // watched list for 0 literal
    unsigned       hWatch1;          // watched list for 1 literal
    int            Activity;         // activity of the clause
    int            nLits;            // the number of literals
    int            pLits[0];         // the array of literals  
};

typedef struct Sat_Fan_t_ Sat_Fan_t;
struct Sat_Fan_t_
{
    unsigned       iFan      : 31;   // ID of the fanin/fanout
    unsigned       fCompl    :  1;   // complemented attribute
};

typedef struct Sat_Obj_t_ Sat_Obj_t;
struct Sat_Obj_t_
{
    unsigned       hHandle;          // node handle
    unsigned       fAssign   :  1;   // terminal node (CI/CO)
    unsigned       fValue    :  1;   // value under 000 pattern
    unsigned       fMark0    :  1;   // first user-controlled mark
    unsigned       fMark1    :  1;   // second user-controlled mark
    unsigned       nFanouuts : 28;   // the number of fanouts
    unsigned       nFanins   :  8;   // the number of fanins
    unsigned       Level     : 24;   // logic level
    unsigned       hNext;            // next one on this level 
    unsigned       hWatch0;          // watched list for 0 literal
    unsigned       hWatch1;          // watched list for 1 literal
    unsigned       hReason;          // reason for this variable
    unsigned       Depth;            // decision depth
    Sat_Fan_t      Fanios[0];        // the array of fanins/fanouts
};

typedef struct Sat_Man_t_ Sat_Man_t;
struct Sat_Man_t_
{
    Gia_Man_t *    pGia;             // the original AIG manager
    // circuit
    Vec_Int_t      vCis;             // the vector of CIs (PIs + LOs)
    Vec_Int_t      vObjs;            // the vector of objects
    // learned clauses         
    Vec_Int_t      vClauses;         // the vector of clauses
    // solver data
    Vec_Int_t      vTrail;           // variable queue               
    Vec_Int_t      vTrailLim;        // pointer into the trail               
    int            iHead;            // variable queue 
    int            iTail;            // variable queue
    int            iRootLevel;       // first decision
    // levelized order
    int            iLevelTop;        // the largest unassigned level 
    Vec_Int_t      vLevels;          // the linked lists of levels
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


