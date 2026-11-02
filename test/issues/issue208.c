#include "base/main/mainInt.h"
#include "aig/gia/gia.h"

extern void Gia_ManHashResize( Gia_Man_t * p );

int main( int argc, char ** argv )
{
    Gia_Man_t * p = Gia_ManStart( 100 );
    int a, b, c, d, x, y, i, nObjs, fPassed = 1;
    a = Gia_ManAppendCi( p );
    b = Gia_ManAppendCi( p );
    c = Gia_ManAppendCi( p );
    d = Gia_ManAppendCi( p );
    x = Gia_ManAppendAnd( p, a, b );
    Gia_ManAppendAnd( p, a, b );
    y = Gia_ManAppendAnd( p, c, d );
    Gia_ManAppendAnd( p, c, d );
    nObjs = Gia_ManObjNum( p );
    Gia_ManHashStart( p );
    for ( i = 0; i < 3; i++ )
    {
        int u = Gia_ManHashAnd( p, a, b );
        int v = Gia_ManHashAnd( p, c, d );
        fPassed &= u == x || u == x + 2;
        fPassed &= v == y || v == y + 2;
        fPassed &= Gia_ManObjNum(p) == nObjs;
        // Keep all duplicate entries reachable across hash-table growth.
        Gia_ManHashResize( p );
    }
    Gia_ManStop( p );
    printf( "%s: Issue #208 hash growth\n", fPassed ? "PASS" : "FAIL" );
    return !fPassed;
}
