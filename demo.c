// Demo program for the static library project of ABC

#include <stdio.h>
#include "src/sat/csat/csat_apis.h"

// procedures to start and stop the ABC framework
extern void  Abc_Start();
extern void  Abc_Stop();

// simple test prog
int main( int argc, char * argv[] )
{
    CSAT_Manager_t * mng;
    CSAT_Target_ResultT * pResult;
    char * Names[2];
    int Values[2];
    int i;

    // start ABC
    // (calling Abc_Start() for each problem is timeconsuming
    //  because it allocates some internal data structures used by decomposition packages
    //  so Abc_Start should be called once before creating many solution managers)
    Abc_Start();

    // start the solution manager
    // (the manager can be reused for several targets if the targets
    //  use the same network and only differ in the asserted values;
    //  however, only one target can be loaded into the manager at any time)
    mng = CSAT_InitManager();

    // create a simple circuit
    // PIs: A, B, C
    // POs: F = ((AB)C) <+> (A(BC))
    // Internal nodes:
    // X = AB   U = XC
    // Y = BC   W = AY
    // G = U <+> W
    // F = G

    // PIs should be added first
    CSAT_AddGate( mng, CSAT_BPI, "A", 0, NULL, 0 );
    CSAT_AddGate( mng, CSAT_BPI, "B", 0, NULL, 0 );
    CSAT_AddGate( mng, CSAT_BPI, "C", 0, NULL, 0 );
    // internal nodes should be added next
    Names[0] = "A";
    Names[1] = "B";
    CSAT_AddGate( mng, CSAT_BAND, "X", 2, Names, 0 );
//    CSAT_AddGate( mng, CSAT_BOR, "X", 2, Names, 0 ); // use this line to make the problem SATISFIABLE
    Names[0] = "X";
    Names[1] = "C";
    CSAT_AddGate( mng, CSAT_BAND, "U", 2, Names, 0 );
    Names[0] = "B";
    Names[1] = "C";
    CSAT_AddGate( mng, CSAT_BAND, "Y", 2, Names, 0 );
    Names[0] = "A";
    Names[1] = "Y";
    CSAT_AddGate( mng, CSAT_BAND, "W", 2, Names, 0 );
    Names[0] = "U";
    Names[1] = "W";
    CSAT_AddGate( mng, CSAT_BXOR, "G", 2, Names, 0 );
    // POs should be added last
    Names[0] = "G";
    CSAT_AddGate( mng, CSAT_BPO,  "F", 1, Names, 0 );

    // check integrity of the manager (and finalize ABC network in the manager!)
    if ( CSAT_Check_Integrity( mng ) )
        printf( "Integrity is okey.\n" );
    else
        printf( "Integrity is NOT okey.\n" );

    // dump the problem into a BENCH file
    // currently BENCH file can only be written for an AIG
    // so we will transform the network into AIG before dumping it
    CSAT_EnableDump( mng, "simple.bench" );
    CSAT_Dump_Bench_File( mng );

    // set the solving target (only one target at a time!)
    // the target can be expressed sing PI/PO or internal nodes
    Names[0] = "F";
    Values[0] = 1;
    CSAT_AddTarget( mng, 1, Names, Values );

    // initialize the sover
    CSAT_SolveInit( mng );

    // set the solving option (0 = brute-force SAT; 1 = resource-aware FRAIG)
    CSAT_SetSolveOption( mng, 1 );

    // solves the last added target
    CSAT_Solve( mng );

    // get the result of solving
    pResult = CSAT_Get_Target_Result( mng, 0 );

    // print the report
    if ( pResult->status == UNDETERMINED )
        printf( "The problem is UNDETERMINED.\n" );
    else if ( pResult->status == UNSATISFIABLE )
        printf( "The problem is UNSATISFIABLE.\n" );
    else if ( pResult->status == SATISFIABLE )
    {
        printf( "The problem is SATISFIABLE.\n" );
        printf( "Satisfying assignment is: " );
        for ( i = 0; i < pResult->no_sig; i++ )
            printf( "%s=%d ", pResult->names[i], pResult->values[i] );
        printf( "\n" );
    }

    // free everything to prevent memory leaks
    CSAT_TargetResFree( pResult );
    CSAT_QuitManager( mng );
    Abc_Stop();
    return 0;
}

