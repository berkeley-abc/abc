/**CFile****************************************************************

  FileName    [extraUtilCube.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [Permutation computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: extraUtilCube.c,v 1.0 2003/02/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "misc/vec/vec.h"
#include "misc/vec/vecHsh.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline void Abc_StatePush( Vec_Int_t * vData, char * pState, int k )  { int i; for ( i = 0; i < 6; i++ ) Vec_IntWriteEntry(vData, 6*k+i, ((int*)pState)[i]);  }
static inline void Abc_StatePerm( char * pState, char * pPerm, char * pRes ) { int i; for ( i = 0; i < 24; i++ ) pRes[i] = pState[(int)pPerm[i]];                    }
static inline void Abc_StatePrint( char * pState )                           { int i; for ( i = 0; i < 24; i++ ) printf(" %2d", pState[i]); printf( "\n" );          }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_EnumerateCubeStates2()
{
    int pXYZ[3][9][2] = {
        { {3, 5}, {3,17}, {3,15}, {1, 6}, {1,16}, {1,14}, {2, 4}, {2,18}, {2,13} },
        { {2,14}, {2,24}, {2,12}, {3,13}, {3,23}, {3,10}, {1,15}, {1,22}, {1,11} },
        { {1,10}, {1, 7}, {1, 4}, {3,12}, {3, 9}, {3, 6}, {2,11}, {2, 8}, {2, 5} }  };

    Vec_Int_t * vData = Vec_IntStart( 6 * (1 << 22) );
    Hsh_IntMan_t * vHash = Hsh_IntManStart( vData, 6, 1 << 22 );
    int i, k, v, RetValue, Beg, End, Counter = 0;
    char pStart[24], pFirst[9][24];
    abctime clk = Abc_Clock();
    printf( "Enumerating states of 2x2x2 cube.\n" );
    // init state
    for ( v = 0; v < 24; v++ )
        pStart[v] = v;
    Abc_StatePush( vData, pStart, Counter );
    RetValue = Hsh_IntManAdd( vHash, Counter );
    assert( RetValue == Counter );
    Counter++;
    // first nine states
    for ( i = 0; i < 3; i++ )
    {
        memcpy( pFirst[i], pStart, 24 );
        for ( v = 0; v < 9; v++ )
            ABC_SWAP( char, pFirst[i][pXYZ[i][v][0]-1], pFirst[i][pXYZ[i][v][1]-1] );
        Abc_StatePush( vData, pFirst[i], Counter );
        RetValue = Hsh_IntManAdd( vHash, Counter );
        assert( RetValue == Counter );
        Counter++;
        //Abc_StatePrint( pFirst[i] );

        memcpy( pFirst[3+i], pFirst[i], 24 );
        for ( v = 0; v < 9; v++ )
            ABC_SWAP( char, pFirst[3+i][pXYZ[i][v][0]-1], pFirst[3+i][pXYZ[i][v][1]-1] );
        Abc_StatePush( vData, pFirst[3+i], Counter );
        RetValue = Hsh_IntManAdd( vHash, Counter );
        assert( RetValue == Counter );
        Counter++;
        //Abc_StatePrint( pFirst[3+i] );

        memcpy( pFirst[6+i], pFirst[3+i], 24 );
        for ( v = 0; v < 9; v++ )
            ABC_SWAP( char, pFirst[6+i][pXYZ[i][v][0]-1], pFirst[6+i][pXYZ[i][v][1]-1] );
        Abc_StatePush( vData, pFirst[6+i], Counter );
        RetValue = Hsh_IntManAdd( vHash, Counter );
        assert( RetValue == Counter );
        Counter++;
        //Abc_StatePrint( pFirst[6+i] );
    }
    printf( "Iter %2d -> %8d   ", 0, 1 );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    printf( "Iter %2d -> %8d   ", 1, Counter );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Beg = 1;  End = 10;
    for ( i = 2; i <= 100; i++ )
    {
        if ( Beg == End )
            break;
        for ( k = Beg; k < End; k++ )
            for ( v = 0; v < 9; v++ )
            {
                Abc_StatePerm( (char *)Vec_IntEntryP(vData, 6*k), pFirst[v], (char *)Vec_IntEntryP(vData, 6*Counter) );
                RetValue = Hsh_IntManAdd( vHash, Counter );
                if ( RetValue == Counter )
                    Counter++;
                if ( Counter == (1<<22) )
                {
                    printf( "Did not converge.  " );
                    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
                    return;
                }
            }
        Beg = End;  End = Counter;
        printf( "Iter %2d -> %8d   ", i, Counter );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
    Hsh_IntManStop( vHash );
    Vec_IntFree( vData );
}

/*
Enumerating states of 2x2x2 cube.
Iter  0 ->        1   Time =     0.00 sec
Iter  1 ->       10   Time =     0.00 sec
Iter  2 ->       64   Time =     0.00 sec
Iter  3 ->      385   Time =     0.00 sec
Iter  4 ->     2232   Time =     0.00 sec
Iter  5 ->    12224   Time =     0.00 sec
Iter  6 ->    62360   Time =     0.02 sec
Iter  7 ->   289896   Time =     0.09 sec
Iter  8 ->  1159968   Time =     0.90 sec
Iter  9 ->  3047716   Time =    11.62 sec
Iter 10 ->  3671516   Time =    52.00 sec
Iter 11 ->  3674160   Time =    70.38 sec
Iter 12 ->  3674160   Time =    70.48 sec 
*/

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int  Abc_DataHasBit( word * p, word i )  { return (p[(i)>>6] & (1<<((i) & 63))) > 0; }
static inline void Abc_DataSetBit( word * p, word i )  { p[(i)>>6] |= (1<<((i) & 63));             }
static inline void Abc_DataXorBit( word * p, word i )  { p[(i)>>6] ^= (1<<((i) & 63));             }
static inline int  Abc_DataGetCube( word w, int i )         { return (w >> (5*i)) & 31;            }
static inline word Abc_DataXorCube( word w, int i, int c )  { return w ^ (((word)c) << (5*i));     }
void Abc_EnumerateCubeStates()
{
    extern word Aig_ManRandom64( int fReset );

    int pXYZ[3][4][3] = {
        { {0, 4, 0}, {4, 6, 0}, {6, 3, 1}, {3, 0,-1} }, 
        { {1, 3, 1}, {3, 6, 0}, {6, 5, 0}, {5, 1,-1} }, 
        { {2, 5, 0}, {5, 6,-1}, {6, 4, 1}, {4, 2, 0} } 
    }; 
    int pPerms[9][4][3] = {0};
    int i, k, v, u, Beg, End, Cube0, Cube1;
    Vec_Wrd_t * vStates = Vec_WrdAlloc( 1 << 22 ); // 16 MB
    word * pHash = ABC_CALLOC( word, 1 << 29 );    //  4 GB
    word New, Init = 0;

    // estimate
    int Counter = 0;    
    abctime clk = Abc_Clock();
    Aig_ManRandom64( 1 );
    for ( i = 0; i < 3674160; i++ )
        for ( v = 0; v < 9; v++ )
        {
            Init = Aig_ManRandom64( 0 ) & ABC_CONST(0x7FFFFFFFF);
            if ( Abc_DataHasBit(pHash, Init) )
                Counter++;
            else
                Abc_DataSetBit(pHash, Init);
        }
    printf( "Counter = %d   ", Counter );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

    if ( Counter == -1 )
    {
    for ( i = 0; i < 7; i++ )
        Init = Abc_DataXorCube( Init, i, i << 2 );
    Vec_WrdPush( vStates, Init );
    Abc_DataSetBit( pHash, Init );
    Beg = 0; End = 1;
    for ( i = 1; i <= 100; i++ )
    {
        if ( Beg == End )
            break;
        Vec_WrdForEachEntryStartStop( vStates, Init, k, Beg, End )
            for ( v = 0; v < 9; v++ )
            {
                New = Init;
                for ( u = 0; u < 4; u++ )
                {
                    Cube0 = Abc_DataGetCube( Init, pPerms[v][u][0] );
                    Cube1 = Abc_DataGetCube( Init, pPerms[v][u][1] );
                    New = Abc_DataXorCube( New, pPerms[v][u][1], Cube0 - pPerms[v][u][2] );
                    New = Abc_DataXorCube( New, pPerms[v][u][0], Cube1 + pPerms[v][u][2] );
                }
                if ( !Abc_DataHasBit( pHash, New ) )
                    Vec_WrdPush( vStates, New );
            }
    }
    }

    Vec_WrdFree( vStates );
    ABC_FREE( pHash );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

