#include "base/main/mainInt.h"
#include "aig/gia/gia.h"

extern Vec_Int_t * Gia_ManDetectFullAdders( Gia_Man_t * p, int fVerbose, Vec_Int_t ** pvCutsXor2 );

int main( int argc, char ** argv )
{
    int a, b, c, s, t, i, fCarry, fPassed = 1;
    for ( fCarry = 0; fCarry < 2; fCarry++ )
    {
        Gia_Man_t * p = Gia_ManStart( 100 );
        Vec_Int_t * vAdds, * vXors;
        Gia_ManHashAlloc( p );
        a = Gia_ManAppendCi( p );
        b = Gia_ManAppendCi( p );
        c = Gia_ManAppendCi( p );
        s = Gia_ManHashXor( p, Gia_ManHashXor(p, a, b), c );
        t = fCarry ? Gia_ManHashOr(p, Gia_ManHashAnd(p, a, b), Gia_ManHashAnd(p, c, Gia_ManHashOr(p, a, b))) : c;
        Gia_ManAppendCo( p, s );
        Gia_ManAppendCo( p, t );
        Gia_ManHashStop( p );
        vAdds = Gia_ManDetectFullAdders( p, 0, &vXors );
        fPassed &= Vec_IntSize(vAdds) == 5 * fCarry;
        if ( fCarry && Vec_IntSize(vAdds) == 5 )
        {
            for ( i = 0; i < 3; i++ )
                fPassed &= Vec_IntEntry(vAdds, i) == i + 1;
            fPassed &= Vec_IntEntry(vAdds, 3) == Abc_Lit2Var(s);
            fPassed &= Vec_IntEntry(vAdds, 4) == Abc_Lit2Var(t);
        }
        fPassed &= Vec_IntSize(vXors) >= 3 && Vec_IntSize(vXors) % 3 == 0;
        Vec_IntFree( vXors );
        Vec_IntFree( vAdds );
        Gia_ManStop( p );
    }
    printf( "%s: Issue #346\n", fPassed ? "PASS" : "FAIL" );
    return !fPassed;
}
