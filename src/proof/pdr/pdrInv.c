/**CFile****************************************************************

  FileName    [pdrInv.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [Invariant computation, printing, verification.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdrInv.c,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdrInt.h"
#include "src/base/abc/abc.h"      // for Abc_NtkCollectCioNames()
#include "src/base/main/main.h"    // for Abc_FrameReadGlobalFrame()

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManPrintProgress( Pdr_Man_t * p, int fClose, int Time )
{
    static int PastSize;
    Vec_Ptr_t * vVec;
    int i, ThisSize, Length, LengthStart;
    if ( Vec_PtrSize(p->vSolvers) < 2 )
        return;
    // count the total length of the printout
    Length = 0;
    Vec_VecForEachLevel( p->vClauses, vVec, i )
        Length += 1 + Abc_Base10Log(Vec_PtrSize(vVec)+1);
    // determine the starting point
    LengthStart = Abc_MaxInt( 0, Length - 70 );
    printf( "%3d :", Vec_PtrSize(p->vSolvers)-1 );
    ThisSize = 6;
    if ( LengthStart > 0 )
    {
        printf( " ..." );
        ThisSize += 4;
    }
    Length = 0;
    Vec_VecForEachLevel( p->vClauses, vVec, i )
    {
        if ( Length < LengthStart )
        {
            Length += 1 + Abc_Base10Log(Vec_PtrSize(vVec)+1);
            continue;
        }
        printf( " %d", Vec_PtrSize(vVec) );
        Length += 1 + Abc_Base10Log(Vec_PtrSize(vVec)+1);
        ThisSize += 1 + Abc_Base10Log(Vec_PtrSize(vVec)+1);
    }
    if ( fClose )
    {
        for ( i = 0; i < PastSize - ThisSize; i++ )
            printf( " " );
        printf( "\n" );
    }
    else
    {
        printf( "\r" );
        PastSize = ThisSize;
    }
//    printf(" %.2f sec", (float)(Time)/(float)(CLOCKS_PER_SEC));
}

/**Function*************************************************************

  Synopsis    [Counts how many times each flop appears in the set of cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Pdr_ManCountFlops( Pdr_Man_t * p, Vec_Ptr_t * vCubes )
{
    Vec_Int_t * vFlopCount;
    Pdr_Set_t * pCube;
    int i, n;
    vFlopCount = Vec_IntStart( Aig_ManRegNum(p->pAig) );
    Vec_PtrForEachEntry( Pdr_Set_t *, vCubes, pCube, i )
        for ( n = 0; n < pCube->nLits; n++ )
        {
            assert( pCube->Lits[n] >= 0 && pCube->Lits[n] < 2*Aig_ManRegNum(p->pAig) );
            Vec_IntAddToEntry( vFlopCount, pCube->Lits[n] >> 1, 1 );
        }
    return vFlopCount;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManFindInvariantStart( Pdr_Man_t * p )
{
    Vec_Ptr_t * vArrayK;
    int k, kMax = Vec_PtrSize(p->vSolvers)-1;
    Vec_VecForEachLevelStartStop( p->vClauses, vArrayK, k, 1, kMax+1 )
        if ( Vec_PtrSize(vArrayK) == 0 )
            return k;
//    return -1;
    // if there is no starting point (as in case of SAT or undecided), return the last frame
//    printf( "The last timeframe contains %d clauses.\n", Vec_PtrSize(Vec_VecEntry(p->vClauses, kMax)) );
    return kMax;
}

/**Function*************************************************************

  Synopsis    [Counts the number of variables used in the clauses.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Pdr_ManCollectCubes( Pdr_Man_t * p, int kStart )
{
    Vec_Ptr_t * vResult;
    Vec_Ptr_t * vArrayK;
    Pdr_Set_t * pSet;
    int i, j;
    vResult = Vec_PtrAlloc( 100 );
    Vec_VecForEachLevelStart( p->vClauses, vArrayK, i, kStart )
        Vec_PtrForEachEntry( Pdr_Set_t *, vArrayK, pSet, j )
            Vec_PtrPush( vResult, pSet );
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Counts the number of variables used in the clauses.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManCountVariables( Pdr_Man_t * p, int kStart )
{
    Vec_Int_t * vFlopCounts;
    Vec_Ptr_t * vCubes;
    int i, Entry, Counter = 0;
    vCubes = Pdr_ManCollectCubes( p, kStart );
    vFlopCounts = Pdr_ManCountFlops( p, vCubes );
    Vec_IntForEachEntry( vFlopCounts, Entry, i )
        Counter += (Entry > 0);
    Vec_IntFreeP( &vFlopCounts );
    Vec_PtrFree( vCubes );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManPrintClauses( Pdr_Man_t * p, int kStart )
{
    Vec_Ptr_t * vArrayK;
    Pdr_Set_t * pCube;
    int i, k, Counter = 0;
    Vec_VecForEachLevelStart( p->vClauses, vArrayK, k, kStart )
    {
        Vec_PtrSort( vArrayK, (int (*)(void))Pdr_SetCompare );
        Vec_PtrForEachEntry( Pdr_Set_t *, vArrayK, pCube, i )
        {
            printf( "C=%4d. F=%4d ", Counter++, k );
            Pdr_SetPrint( stdout, pCube, Aig_ManRegNum(p->pAig), NULL );  
            printf( "\n" ); 
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     [] 

***********************************************************************/
void Pdr_ManDumpClauses( Pdr_Man_t * p, char * pFileName, int fProved )
{
    int fUseSupp = 1;
    FILE * pFile;
    Vec_Int_t * vFlopCounts;
    Vec_Ptr_t * vCubes;
    Pdr_Set_t * pCube;
    char ** pNamesCi;
    int i, kStart;
    // create file
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for writing invariant.\n", pFileName );
        return;
    } 
    // collect cubes
    kStart = Pdr_ManFindInvariantStart( p );
    vCubes = Pdr_ManCollectCubes( p, kStart );
    Vec_PtrSort( vCubes, (int (*)(void))Pdr_SetCompare );
    // collect variable appearances
    vFlopCounts = fUseSupp ? Pdr_ManCountFlops( p, vCubes ) : NULL; 
    // output the header
    if ( fProved )
        fprintf( pFile, "# Inductive invariant for \"%s\"\n", p->pAig->pName );
    else
        fprintf( pFile, "# Clauses of the last timeframe for \"%s\"\n", p->pAig->pName );
    fprintf( pFile, "# generated by PDR in ABC on %s\n", Aig_TimeStamp() );
    fprintf( pFile, ".i %d\n", fUseSupp ? Pdr_ManCountVariables(p, kStart) : Aig_ManRegNum(p->pAig) );
    fprintf( pFile, ".o 1\n" );
    fprintf( pFile, ".p %d\n", Vec_PtrSize(vCubes) );
    // output flop names
    pNamesCi = Abc_NtkCollectCioNames( Abc_FrameReadNtk( Abc_FrameReadGlobalFrame() ), 0 );
    if ( pNamesCi )
    {
        fprintf( pFile, ".ilb" );
        for ( i = 0; i < Aig_ManRegNum(p->pAig); i++ )
            if ( !fUseSupp || Vec_IntEntry( vFlopCounts, i ) )
                fprintf( pFile, " %s", pNamesCi[Saig_ManPiNum(p->pAig) + i] );
        fprintf( pFile, "\n" );
        ABC_FREE( pNamesCi );
        fprintf( pFile, ".ob inv\n" );
    }
    // output cubes
    Vec_PtrForEachEntry( Pdr_Set_t *, vCubes, pCube, i )
    {
        Pdr_SetPrint( pFile, pCube, Aig_ManRegNum(p->pAig), vFlopCounts );  
        fprintf( pFile, " 1\n" ); 
    }
    fprintf( pFile, ".e\n\n" );
    fclose( pFile );
    Vec_IntFreeP( &vFlopCounts );
    Vec_PtrFree( vCubes );
    if ( fProved )
        printf( "Inductive invariant was written into file \"%s\".\n", pFileName );
    else
        printf( "Clauses of the last timeframe were written into file \"%s\".\n", pFileName );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManReportInvariant( Pdr_Man_t * p )
{
    Vec_Ptr_t * vCubes;
    int kStart = Pdr_ManFindInvariantStart( p );
    vCubes = Pdr_ManCollectCubes( p, kStart );
    printf( "Invariant F[%d] : %d clauses with %d flops (out of %d)\n", 
        kStart, Vec_PtrSize(vCubes), Pdr_ManCountVariables(p, kStart), Aig_ManRegNum(p->pAig) );
    Vec_PtrFree( vCubes );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManVerifyInvariant( Pdr_Man_t * p )
{
    sat_solver * pSat;
    Vec_Int_t * vLits;
    Vec_Ptr_t * vCubes;
    Pdr_Set_t * pCube;
    int i, kStart, kThis, RetValue, Counter = 0, clk = clock();
    // collect cubes used in the inductive invariant
    kStart = Pdr_ManFindInvariantStart( p );
    vCubes = Pdr_ManCollectCubes( p, kStart );
    // create solver with the cubes
    kThis = Vec_PtrSize(p->vSolvers);
    pSat  = Pdr_ManCreateSolver( p, kThis );
    // add the property output
    Pdr_ManSetPropertyOutput( p, kThis );
    // add the clauses
    Vec_PtrForEachEntry( Pdr_Set_t *, vCubes, pCube, i )
    {
        vLits = Pdr_ManCubeToLits( p, kThis, pCube, 1, 0 );
        RetValue = sat_solver_addclause( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits) );
        assert( RetValue );
        sat_solver_compress( pSat );
    }
    // check each clause
    Vec_PtrForEachEntry( Pdr_Set_t *, vCubes, pCube, i )
    {
        vLits = Pdr_ManCubeToLits( p, kThis, pCube, 0, 1 );
        RetValue = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), 0, 0, 0, 0 );
        if ( RetValue != l_False )
        {
            printf( "Verification of clause %d failed.\n", i );
            Counter++;
        }
    }
    if ( Counter )
        printf( "Verification of %d clauses has failed.\n", Counter );
    else
    {
        printf( "Verification of invariant with %d clauses was successful.  ", Vec_PtrSize(vCubes) );
        Abc_PrintTime( 1, "Time", clock() - clk );
    }
//    sat_solver_delete( pSat );
    Vec_PtrFree( vCubes );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

