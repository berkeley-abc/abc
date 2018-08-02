/**CFile****************************************************************

  FileName    [dau.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware unmapping.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: dau.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dauInt.h"
#include "misc/util/utilTruth.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

//#define USE4VARS 1

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dau_TruthEnum()
{
    int fUseTable = 1;
    abctime clk = Abc_Clock();
#ifdef USE4VARS
    int nVars   = 4;
    int nSizeW  = 1 << 14;
    char * pFileName = "tableW14.data";
#else
    int nVars   = 5;
    int nSizeW  = 1 << 30;
    char * pFileName = "tableW30.data";
#endif
    int nPerms  = Extra_Factorial( nVars );
    int nMints  = 1 << nVars;
    int * pPerm = Extra_PermSchedule( nVars );
    int * pComp = Extra_GreyCodeSchedule( nVars );
    word nFuncs = ((word)1 << (((word)1 << nVars)-1));
    word * pPres = ABC_CALLOC( word, 1 << ((1<<nVars)-7) );
    unsigned * pTable = fUseTable ? (unsigned *)ABC_CALLOC(word, nSizeW) : NULL;
    Vec_Int_t * vNpns = Vec_IntAlloc( 1000 );
    word tMask = Abc_Tt6Mask( 1 << nVars );
    word tTemp, tCur;
    int i, k;
    if ( pPres == NULL )
    {
        printf( "Cannot alloc memory for marks.\n" );
        return;
    }
    if ( pTable == NULL )
        printf( "Cannot alloc memory for table.\n" );
    for ( tCur = 0; tCur < nFuncs; tCur++ )
    {
        if ( (tCur & 0x3FFFF) == 0 )
        {
            printf( "Finished %08x.  Classes = %6d.  ", (int)tCur, Vec_IntSize(vNpns) );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            fflush(stdout);
        }
        if ( Abc_TtGetBit(pPres, (int)tCur) )
            continue;
        //Extra_PrintBinary( stdout, (unsigned *)&tCur, 16 ); printf( " %04x\n", (int)tCur );
        //Dau_DsdPrintFromTruth( &tCur, 4 ); printf( "\n" );
        Vec_IntPush( vNpns, (int)tCur );
        tTemp = tCur;
        for ( i = 0; i < nPerms; i++ )
        {
            for ( k = 0; k < nMints; k++ )
            {
                if ( tCur < nFuncs )
                {
                    if ( pTable ) pTable[(int)tCur] = tTemp;
                    Abc_TtSetBit( pPres, (int)tCur );
                }
                if ( (tMask & ~tCur) < nFuncs )
                {
                    if ( pTable ) pTable[(int)(tMask & ~tCur)] = tTemp;
                    Abc_TtSetBit( pPres, (int)(tMask & ~tCur) );
                }
                tCur = Abc_Tt6Flip( tCur, pComp[k] );
            }
            tCur = Abc_Tt6SwapAdjacent( tCur, pPerm[i] );
        }
        assert( tTemp == tCur );
    }
    printf( "Computed %d NPN classes of %d variables.  ", Vec_IntSize(vNpns), nVars );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    fflush(stdout);
    Vec_IntFree( vNpns );
    ABC_FREE( pPres );
    ABC_FREE( pPerm );
    ABC_FREE( pComp );
    // write into file
    if ( pTable )
    {
        FILE * pFile = fopen( pFileName, "wb" );
        int RetValue = fwrite( pTable, 8, nSizeW, pFile );
        fclose( pFile );
        ABC_FREE( pTable );
    }
}

 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Dau_ReadFile( char * pFileName, int nSizeW )
{
    abctime clk = Abc_Clock();
    FILE * pFile = fopen( pFileName, "rb" );
    unsigned * p = (unsigned *)ABC_CALLOC(word, nSizeW);
    int RetValue = fread( p, sizeof(word), nSizeW, pFile );
    fclose( pFile );
    Abc_PrintTime( 1, "File reading", Abc_Clock() - clk );
    return p;
}
void Dau_AddFunction( word tCur, int nVars, unsigned * pTable, Vec_Int_t * vNpns )
{
    int Digit  = (1 << nVars)-1;
    word tMask = Abc_Tt6Mask( 1 << nVars );
    word tNorm = (tCur >> Digit) & 1 ? ~tCur : tCur;
    unsigned t = (unsigned)tNorm & tMask;
    unsigned tRep  = pTable[t];
    unsigned tRep2 = pTable[tRep & tMask];
    assert( ((tNorm >> Digit) & 1) == 0 );
    //assert( (tRep & (tMask>>1)) == (tRep2 & (tMask>>1)) );
    if ( (tRep2 >> 31) == 0 ) // first time
    {
        Vec_IntPush( vNpns, tRep2 );
        pTable[tRep2] |= (1 << 31);
    }
}
void Dau_NetworkEnum()
{
    abctime clk = Abc_Clock();
    int Limit = 2;
#ifdef USE4VARS
    int nVars = 4;
    int nSizeW  = 1 << 14;
    char * pFileName = "tableW14.data";
#else
    int nVars = 5;
    int nSizeW  = 1 << 30;
    char * pFileName = "tableW30.data";
#endif
    unsigned * pTable = Dau_ReadFile( pFileName, nSizeW );
    Vec_Int_t * vNpns = Vec_IntAlloc( 1000 );
    int i, v, g, k, m, Entry, Count = 1, iPrev = 0, iLast = 1;
    unsigned Inv = (unsigned)Abc_Tt6Mask(1 << (nVars-1));
    pTable[0]   |= (1 << 31);
    pTable[Inv] |= (1 << 31);
    Vec_IntPushTwo( vNpns, 0, Inv );
    Vec_IntForEachEntryStart( vNpns, Entry, i, 1 )
    {
        word uTruth = (((word)Entry) << 32) | (word)Entry;
        int nSupp = Abc_TtSupportSize( &uTruth, nVars );
        //printf( "Exploring function %4d with %d vars: ", i, nSupp );
        //printf( " %04x\n", (int)uTruth );
        //Dau_DsdPrintFromTruth( &uTruth, 4 );
        for ( v = 0; v < nSupp; v++ )
        {
            word Cof0 = Abc_Tt6Cofactor0( uTruth, nVars-1-v );
            word Cof1 = Abc_Tt6Cofactor1( uTruth, nVars-1-v );
            for ( g = 0; g < Limit; g++ )
            {
                if ( nSupp < nVars )
                {
                    word tGate = g ? s_Truths6[nVars-1-v] ^ s_Truths6[nVars-1-nSupp] : s_Truths6[nVars-1-v] & s_Truths6[nVars-1-nSupp];
                    word tCur  = (tGate & Cof1) | (~tGate & Cof0);
                    Dau_AddFunction( tCur, nVars, pTable, vNpns );
                }
            }
            for ( g = 0; g < Limit; g++ )
            {
                // add one cross bar
                for ( k = 0; k < nSupp; k++ ) if ( k != v )
                {
                    word tGate = g ? s_Truths6[nVars-1-v] ^ s_Truths6[nVars-1-k] : s_Truths6[nVars-1-v] & s_Truths6[nVars-1-k];
                    word tCur  = (tGate & Cof1) | (~tGate & Cof0);
                    Dau_AddFunction( tCur, nVars, pTable, vNpns );
                    if ( g == 0 ) // skip XOR
                    {
                        word tGate = s_Truths6[nVars-1-v] & ~s_Truths6[nVars-1-k];
                        word tCur  = (tGate & Cof1) | (~tGate & Cof0);
                        Dau_AddFunction( tCur, nVars, pTable, vNpns );
                    }
                }
            }
            for ( g = 0; g < Limit; g++ )
            {
                // add two cross bars
                for ( k = 0;   k < nSupp; k++ ) if ( k != v )
                for ( m = k+1; m < nSupp; m++ ) if ( m != v )
                {
                    word tGate = g ? s_Truths6[nVars-1-m] ^ s_Truths6[nVars-1-k] : s_Truths6[nVars-1-m] & s_Truths6[nVars-1-k];
                    word tCur  = (tGate & Cof1) | (~tGate & Cof0);
                    Dau_AddFunction( tCur, nVars, pTable, vNpns );
                    if ( g == 0 ) // skip XOR
                    {
                        tGate =  s_Truths6[nVars-1-m] & ~s_Truths6[nVars-1-k];
                        tCur  = (tGate & Cof1) | (~tGate & Cof0);
                        Dau_AddFunction( tCur, nVars, pTable, vNpns );

                        tGate = ~s_Truths6[nVars-1-m] &  s_Truths6[nVars-1-k];
                        tCur  = (tGate & Cof1) | (~tGate & Cof0);
                        Dau_AddFunction( tCur, nVars, pTable, vNpns );

                        tGate = ~s_Truths6[nVars-1-m] & ~s_Truths6[nVars-1-k];
                        tCur  = (tGate & Cof1) | (~tGate & Cof0);
                        Dau_AddFunction( tCur, nVars, pTable, vNpns );
                    }
                }
            }
        }
        if ( i == iLast )
        {
            //printf("Finished %d nodes with %d functions.\n", Count++, Vec_IntSize(vNpns) );
            iPrev = iLast;
            iLast = Vec_IntSize(vNpns)-1;
            printf("Finished %2d nodes with %6d functions our of %6d.  ", Count++, iLast - iPrev, Vec_IntSize(vNpns) );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            fflush(stdout);
        }
    }
    Vec_IntFree( vNpns );
    ABC_FREE( pTable );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    fflush(stdout);
}
void Dau_NetworkEnumTest()
{
    //Dau_TruthEnum();
    Dau_NetworkEnum();
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

