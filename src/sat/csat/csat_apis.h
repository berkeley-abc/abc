/**CFile****************************************************************

  FileName    [csat_apis.h]

  PackageName [Interface to CSAT.]

  Synopsis    [APIs, enums, and data structures expected from the use of CSAT.]

  Author      [Alan Mishchenko <alanmi@eecs.berkeley.edu>]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 28, 2005]

  Revision    [$Id: csat_apis.h,v 1.00 2005/08/28 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __ABC_APIS_H__
#define __ABC_APIS_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


typedef struct ABC_ManagerStruct_t     ABC_Manager_t;
typedef struct ABC_ManagerStruct_t *   ABC_Manager;


// GateType defines the gate type that can be added to circuit by
// ABC_AddGate();
#ifndef _ABC_GATE_TYPE_
#define _ABC_GATE_TYPE_
enum GateType
{
    ABC_CONST = 0,  // constant gate
    ABC_BPI,        // boolean PI
    ABC_BPPI,       // bit level PSEUDO PRIMARY INPUT
    ABC_BAND,       // bit level AND
    ABC_BNAND,      // bit level NAND
    ABC_BOR,        // bit level OR
    ABC_BNOR,       // bit level NOR
    ABC_BXOR,       // bit level XOR
    ABC_BXNOR,      // bit level XNOR
    ABC_BINV,       // bit level INVERTER
    ABC_BBUF,       // bit level BUFFER
    ABC_BPPO,       // bit level PSEUDO PRIMARY OUTPUT
    ABC_BPO         // boolean PO
};
#endif


//ABC_StatusT defines the return value by ABC_Solve();
#ifndef _ABC_STATUS_
#define _ABC_STATUS_
enum ABC_StatusT 
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


// ABC_OptionT defines the solver option about learning
// which is used by ABC_SetSolveOption();
#ifndef _ABC_OPTION_
#define _ABC_OPTION_
enum ABC_OptionT
{
    BASE_LINE = 0,
    IMPLICT_LEARNING, //default
    EXPLICT_LEARNING
};
#endif


#ifndef _ABC_Target_Result
#define _ABC_Target_Result
typedef struct _ABC_Target_ResultT ABC_Target_ResultT;
struct _ABC_Target_ResultT
{
    enum ABC_StatusT status; // solve status of the target
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
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// create a new manager
extern ABC_Manager           ABC_InitManager(void);

// set solver options for learning
extern void                  ABC_SetSolveOption(ABC_Manager mng, enum ABC_OptionT option);

// add a gate to the circuit
// the meaning of the parameters are:
// type: the type of the gate to be added
// name: the name of the gate to be added, name should be unique in a circuit.
// nofi: number of fanins of the gate to be added;
// fanins: the name array of fanins of the gate to be added
extern int                   ABC_AddGate(ABC_Manager mng,
                                      enum GateType type,
                                      char* name,
                                      int nofi,
                                      char** fanins,
                                      int dc_attr);

// check if there are gates that are not used by any primary ouput.
// if no such gates exist, return 1 else return 0;
extern int                   ABC_Check_Integrity(ABC_Manager mng);

// set time limit for solving a target.
// runtime: time limit (in second).
extern void                  ABC_SetTimeLimit(ABC_Manager mng, int runtime);
extern void                  ABC_SetLearnLimit(ABC_Manager mng, int num);
extern void                  ABC_SetSolveBacktrackLimit(ABC_Manager mng, int num);
extern void                  ABC_SetLearnBacktrackLimit(ABC_Manager mng, int num);
extern void                  ABC_EnableDump(ABC_Manager mng, char* dump_file);

// the meaning of the parameters are:
// nog: number of gates that are in the targets
// names: name array of gates
// values: value array of the corresponding gates given in "names" to be
// solved. the relation of them is AND.
extern int                   ABC_AddTarget(ABC_Manager mng, int nog, char**names, int* values);

// initialize the solver internal data structure.
extern void                  ABC_SolveInit(ABC_Manager mng);
extern void                  ABC_AnalyzeTargets(ABC_Manager mng);

// solve the targets added by ABC_AddTarget()
extern enum ABC_StatusT      ABC_Solve(ABC_Manager mng);

// get the solve status of a target
// TargetID: the target id returned by  ABC_AddTarget().
extern ABC_Target_ResultT *  ABC_Get_Target_Result(ABC_Manager mng, int TargetID);
extern void                  ABC_Dump_Bench_File(ABC_Manager mng);

// ADDED PROCEDURES:
extern void                  ABC_QuitManager( ABC_Manager mng );
extern void                  ABC_TargetResFree( ABC_Target_ResultT * p );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif
