#include "base/main/mainInt.h"
#include "base/wln/wln.h"

static int CheckCommand( Abc_Frame_t * p, char * pCommand, int fReject )
{
    Gia_Man_t * pOld = p->pGia;
    int Ret = Cmd_CommandExecute( p, pCommand );
    if ( (Ret != 0) != fReject || (fReject && p->pGia != pOld) )
    {
        fprintf( stderr, "Unexpected result: %s\n", pCommand );
        return 0;
    }
    return 1;
}

int main( int argc, char ** argv )
{
    Abc_Frame_t * p;
    int fPassed;
    if ( argc != 2 )
        return 2;
    Abc_Start();
    p = Abc_FrameGetGlobalFrame();
    p->pAbcRtl = Rtl_LibReadFile( argv[1], argv[1] );
    fPassed = CheckCommand( p, "%collapse -T comb", 0 ) &&
              p->pGia && Gia_ManCiNum(p->pGia) == 2 && Gia_ManCoNum(p->pGia) == 1 && Gia_ManAndNum(p->pGia) == 1 &&
              CheckCommand( p, "%collapse -T seq", 1 ) &&
              CheckCommand( p, "%collapse -c -T hier", 1 ) &&
              CheckCommand( p, "%collapse -T missing", 1 ) &&
              CheckCommand( p, "%collapse", 1 ) &&
              CheckCommand( p, "%collapse -T comb", 0 );
    Abc_Stop();
    return !fPassed;
}
