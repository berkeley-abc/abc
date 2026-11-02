#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "map/if/if.h"

extern void If_ManSetupSet( If_Man_t * p, If_Set_t * pSet );

static int IsAligned( void * p )
{
    return ((ABC_PTRUINT_T)p & 7) == 0;
}

int main( int argc, char ** argv )
{
    Aig_MmFlex_t * pMem = Aig_MmFlexStart();
    If_Par_t Pars;
    If_Man_t * p;
    If_Set_t * pSet;
    char * pSets;
    int i, k, c, j, fPerm, fPassed = 1;
    // Mixed byte strings and records, including chunk boundaries and restart.
    for ( k = 0; k < 2; k++ )
    {
        for ( i = 1; i < 10000; i++ )
            fPassed &= IsAligned( Aig_MmFlexEntryFetch(pMem, i % 79 + 1) );
        Aig_MmFlexRestart( pMem );
    }
    Aig_MmFlexStop( pMem, 0 );
    for ( k = 2; k <= 16; k++ )
    for ( c = 1; c <= 9; c++ )
    for ( fPerm = 0; fPerm < 2; fPerm++ )
    {
        If_ManSetDefaultPars( &Pars );
        Pars.nLutSize = k;
        Pars.nCutsMax = c;
        Pars.fUsePerm = fPerm;
        p = If_ManStart( &Pars );
        for ( i = 0; i < 10; i++ )
            fPassed &= IsAligned( If_ManCreateCi(p) );
        pSets = ABC_ALLOC( char, 3 * p->nSetBytes );
        for ( i = 0; i < 3; i++ )
        {
            pSet = (If_Set_t *)(pSets + i * p->nSetBytes);
            If_ManSetupSet( p, pSet );
            fPassed &= IsAligned( pSet );
            for ( j = 0; j <= c; j++ )
                fPassed &= IsAligned( pSet->ppCuts[j] );
        }
        ABC_FREE( pSets );
        If_ManStop( p );
    }
    printf( "%s: Issue #407\n", fPassed ? "PASS" : "FAIL" );
    return !fPassed;
}
