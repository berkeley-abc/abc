/**CFile****************************************************************

  FileName    [csat_apis.h]

  PackageName [Interface to CSAT.]

  Synopsis    [APIs, enums, and data structures expected from the use of CSAT.]

  Author      [Alan Mishchenko <alanmi@eecs.berkeley.edu>]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 28, 2005]

  Revision    [$Id: csat_apis.h,v 1.00 2005/08/28 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __CSAT_APIS_H__
#define __CSAT_APIS_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


typedef struct CSAT_ManagerStruct_t     CSAT_Manager_t;
typedef struct CSAT_ManagerStruct_t *   CSAT_Manager;


// GateType defines the gate type that can be added to circuit by
// CSAT_AddGate();
#ifndef _CSAT_GATE_TYPE_
#define _CSAT_GATE_TYPE_
enum GateType
{
    CSAT_CONST = 0,  // constant gate
    CSAT_BPI,        // boolean PI
    CSAT_BPPI,       // bit level PSEUDO PRIMARY INPUT
    CSAT_BAND,       // bit level AND
    CSAT_BNAND,      // bit level NAND
    CSAT_BOR,        // bit level OR
    CSAT_BNOR,       // bit level NOR
    CSAT_BXOR,       // bit level XOR
    CSAT_BXNOR,      // bit level XNOR
    CSAT_BINV,       // bit level INVERTER
    CSAT_BBUF,       // bit level BUFFER
    CSAT_BPPO,       // bit level PSEUDO PRIMARY OUTPUT
    CSAT_BPO         // boolean PO
};
#endif


//CSAT_StatusT defines the return value by CSAT_Solve();
#ifndef _CSAT_STATUS_
#define _CSAT_STATUS_
enum CSAT_StatusT 
{
    UNDETERMINED = 0,
    UNSATISFIABLE,
    SATISFIABLE,
    TIME_OUT,
    FRAME_OUT,
    NO_TARGET,
    ABORTED,
    SEQ_SATISFIABLE     
};
#endif


// CSAT_OptionT defines the solver option about learning
// which is used by CSAT_SetSolveOption();
#ifndef _CSAT_OPTION_
#define _CSAT_OPTION_
enum CSAT_OptionT
{
    BASE_LINE = 0,
    IMPLICT_LEARNING, //default
    EXPLICT_LEARNING
};
#endif


#ifndef _CSAT_Target_Result
#define _CSAT_Target_Result
typedef struct _CSAT_Target_ResultT CSAT_Target_ResultT;
struct _CSAT_Target_ResultT
{
    enum CSAT_StatusT status; // solve status of the target
    int num_dec;              // num of decisions to solve the target
    int num_imp;              // num of implications to solve the target
    int num_cftg;             // num of conflict gates learned 
    int num_cfts;             // num of conflict signals in conflict gates
    double time;              // time(in second) used to solve the target
    int no_sig;               // if "status" is SATISFIABLE, "no_sig" is the number of 
                              // primary inputs, if the "status" is TIME_OUT, "no_sig" is the
                              // number of constant signals found.
    char** names;             // if the "status" is SATISFIABLE, "names" is the name array of
                              // primary inputs, "values" is the value array of primary 
                              // inputs that satisfy the target. 
                              // if the "status" is TIME_OUT, "names" is the name array of
                              // constant signals found (signals at the root of decision 
                              // tree), "values" is the value array of constant signals found.
    int* values;
};
#endif

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

// create a new manager
extern CSAT_Manager          CSAT_InitManager(void);

// set solver options for learning
extern void                  CSAT_SetSolveOption(CSAT_Manager mng, enum CSAT_OptionT option);

// add a gate to the circuit
// the meaning of the parameters are:
// type: the type of the gate to be added
// name: the name of the gate to be added, name should be unique in a circuit.
// nofi: number of fanins of the gate to be added;
// fanins: the name array of fanins of the gate to be added
extern int                   CSAT_AddGate(CSAT_Manager mng,
                                      enum GateType type,
                                      char* name,
                                      int nofi,
                                      char** fanins,
                                      int dc_attr);

// check if there are gates that are not used by any primary ouput.
// if no such gates exist, return 1 else return 0;
extern int                   CSAT_Check_Integrity(CSAT_Manager mng);

// set time limit for solving a target.
// runtime: time limit (in second).
extern void                  CSAT_SetTimeLimit(CSAT_Manager mng, int runtime);
extern void                  CSAT_SetLearnLimit(CSAT_Manager mng, int num);
extern void                  CSAT_SetSolveBacktrackLimit(CSAT_Manager mng, int num);
extern void                  CSAT_SetLearnBacktrackLimit(CSAT_Manager mng, int num);
extern void                  CSAT_EnableDump(CSAT_Manager mng, char* dump_file);

// the meaning of the parameters are:
// nog: number of gates that are in the targets
// names: name array of gates
// values: value array of the corresponding gates given in "names" to be
// solved. the relation of them is AND.
extern int                   CSAT_AddTarget(CSAT_Manager mng, int nog, char**names, int* values);

// initialize the solver internal data structure.
extern void                  CSAT_SolveInit(CSAT_Manager mng);
extern void                  CSAT_AnalyzeTargets(CSAT_Manager mng);

// solve the targets added by CSAT_AddTarget()
extern enum CSAT_StatusT     CSAT_Solve(CSAT_Manager mng);

// get the solve status of a target
// TargetID: the target id returned by  CSAT_AddTarget().
extern CSAT_Target_ResultT * CSAT_Get_Target_Result(CSAT_Manager mng, int TargetID);
extern void                  CSAT_Dump_Bench_File(CSAT_Manager mng);

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif
