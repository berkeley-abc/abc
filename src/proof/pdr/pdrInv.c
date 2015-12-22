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
#include "base/abc/abc.h"      // for Abc_NtkCollectCioNames()
#include "base/main/main.h"    // for Abc_FrameReadGlobalFrame()
#include "aig/ioa/ioa.h"

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
void Pdr_ManPrintProgress( Pdr_Man_t * p, int fClose, abctime Time )
{
    Vec_Ptr_t * vVec;
    int i, ThisSize, Length, LengthStart;
    if ( Vec_PtrSize(p->vSolvers) < 2 )
        return;
    if ( Abc_FrameIsBatchMode() && !fClose )
        return;
    // count the total length of the printout
    Length = 0;
    Vec_VecForEachLevel( p->vClauses, vVec, i )
        Length += 1 + Abc_Base10Log(Vec_PtrSize(vVec)+1);
    // determine the starting point
    LengthStart = Abc_MaxInt( 0, Length - 60 );
    Abc_Print( 1, "%3d :", Vec_PtrSize(p->vSolvers)-1 );
    ThisSize = 5;
    if ( LengthStart > 0 )
    {
        Abc_Print( 1, " ..." );
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
        Abc_Print( 1, " %d", Vec_PtrSize(vVec) );
        Length += 1 + Abc_Base10Log(Vec_PtrSize(vVec)+1);
        ThisSize += 1 + Abc_Base10Log(Vec_PtrSize(vVec)+1);
    }
    for ( i = ThisSize; i < 70; i++ )
        Abc_Print( 1, " " );
    Abc_Print( 1, "%6d", p->nQueMax );
    Abc_Print( 1, "%10.2f sec", 1.0*Time/CLOCKS_PER_SEC );
    if ( p->pPars->fSolveAll )
        Abc_Print( 1, "  CEX =%4d", p->pPars->nFailOuts );
    if ( p->pPars->nTimeOutOne )
        Abc_Print( 1, "  T/O =%3d", p->pPars->nDropOuts );
    Abc_Print( 1, "%s", fClose ? "\n":"\r" );
    if ( fClose )
        p->nQueMax = 0;
    fflush( stdout );
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
//    Abc_Print( 1, "The last timeframe contains %d clauses.\n", Vec_PtrSize(Vec_VecEntry(p->vClauses, kMax)) );
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

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Pdr_ManCountFlopsInv( Pdr_Man_t * p )
{
    int kStart = Pdr_ManFindInvariantStart(p);
    Vec_Ptr_t *vCubes = Pdr_ManCollectCubes(p, kStart);
    Vec_Int_t * vInv = Pdr_ManCountFlops( p, vCubes );
    Vec_PtrFree(vCubes);
    return vInv;
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
            Abc_Print( 1, "C=%4d. F=%4d ", Counter++, k );
            Pdr_SetPrint( stdout, pCube, Aig_ManRegNum(p->pAig), NULL );  
            Abc_Print( 1, "\n" ); 
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     [] 

***********************************************************************/
void Pdr_SetPrintOne( Pdr_Set_t * p )
{
    int i;
    printf( "Clause: {" );
    for ( i = 0; i < p->nLits; i++ )
        printf( " %s%d", Abc_LitIsCompl(p->Lits[i])? "!":"", Abc_Lit2Var(p->Lits[i]) );
    printf( " }\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     [] 

***********************************************************************/
Aig_Man_t * Pdr_ManDupAigWithClauses( Aig_Man_t * p, Vec_Ptr_t * vCubes )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew, * pLit;
    Pdr_Set_t * pCube;
    int i, n;
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachCi( p, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );
    // create outputs for each cube
    Vec_PtrForEachEntry( Pdr_Set_t *, vCubes, pCube, i )
    {
//        Pdr_SetPrintOne( pCube );
        pObjNew = Aig_ManConst1(pNew);
        for ( n = 0; n < pCube->nLits; n++ )
        {
            assert( Abc_Lit2Var(pCube->Lits[n]) < Saig_ManRegNum(p) );
            pLit = Aig_NotCond( Aig_ManCi(pNew, Saig_ManPiNum(p) + Abc_Lit2Var(pCube->Lits[n])), Abc_LitIsCompl(pCube->Lits[n]) );
            pObjNew = Aig_And( pNew, pObjNew, pLit );
        }
        Aig_ObjCreateCo( pNew, pObjNew );
    }
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // add the POs
    Saig_ManForEachLi( p, pObj, i )
        Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pNew );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    // check the resulting network
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupSimple(): The check has failed.\n" );
    return pNew;
}
void Pdr_ManDumpAig( Aig_Man_t * p, Vec_Ptr_t * vCubes )
{
    Aig_Man_t * pNew = Pdr_ManDupAigWithClauses( p, vCubes );
    Ioa_WriteAiger( pNew, "aig_with_clauses.aig", 0, 0 );
    Aig_ManStop( pNew );
    printf( "Dumped modified AIG into file \"aig_with_clauses.aig\".\n" );
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
        Abc_Print( 1, "Cannot open file \"%s\" for writing invariant.\n", pFileName );
        return;
    } 
    // collect cubes
    kStart = Pdr_ManFindInvariantStart( p );
    vCubes = Pdr_ManCollectCubes( p, kStart );
    Vec_PtrSort( vCubes, (int (*)(void))Pdr_SetCompare );
//    Pdr_ManDumpAig( p->pAig, vCubes );
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
        Abc_Print( 1, "Inductive invariant was written into file \"%s\".\n", pFileName );
    else
        Abc_Print( 1, "Clauses of the last timeframe were written into file \"%s\".\n", pFileName );
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
    Abc_Print( 1, "Invariant F[%d] : %d clauses with %d flops (out of %d)\n", 
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
    int i, kStart, kThis, RetValue, Counter = 0;
    abctime clk = Abc_Clock();
    // collect cubes used in the inductive invariant
    kStart = Pdr_ManFindInvariantStart( p );
    vCubes = Pdr_ManCollectCubes( p, kStart );
    // create solver with the cubes
    kThis = Vec_PtrSize(p->vSolvers);
    pSat  = Pdr_ManCreateSolver( p, kThis );
    // add the property output
//    Pdr_ManSetPropertyOutput( p, kThis );
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
            Abc_Print( 1, "Verification of clause %d failed.\n", i );
            Counter++;
        }
    }
    if ( Counter )
        Abc_Print( 1, "Verification of %d clauses has failed.\n", Counter );
    else
    {
        Abc_Print( 1, "Verification of invariant with %d clauses was successful.  ", Vec_PtrSize(vCubes) );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }
//    sat_solver_delete( pSat );
    Vec_PtrFree( vCubes );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

