#include "base/main/mainInt.h"

int main( int argc, char ** argv )
{
    Abc_Frame_t * pAbc;
    Abc_Ntk_t * pNtk;
    int i, fPassed = 1;
    char Command[100];
    Abc_Start();
    pAbc = Abc_FrameGetGlobalFrame();
    fPassed &= Cmd_CommandExecute(pAbc, "read good.v; strash") == 0;
    pNtk = Abc_FrameReadNtk( pAbc );
    fPassed &= pNtk != NULL;
    for ( i = 0; i < 3; i++ )
    {
        sprintf( Command, "read bad%d.v", i );
        Cmd_CommandExecute( pAbc, Command );
        fPassed &= Abc_FrameReadNtk(pAbc) == pNtk;
    }
    fPassed &= Cmd_CommandExecute(pAbc, "write_aiger preserved.aig") == 0;
    Abc_Stop();
    printf( "%s: Issue #300\n", fPassed ? "PASS" : "FAIL" );
    return !fPassed;
}
