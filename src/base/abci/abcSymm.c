/**CFile****************************************************************

  FileName    [abcSymm.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Computation of two-variable symmetries.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcSymm.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "opt/sim/sim.h"
#include "opt/dau/dau.h"
#include "misc/util/utilTruth.h"

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#endif

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
#ifdef ABC_USE_CUDD

static void Abc_NtkSymmetriesUsingBdds( Abc_Ntk_t * pNtk, int fNaive, int fReorder, int fVerbose );
static void Abc_NtkSymmetriesUsingSandS( Abc_Ntk_t * pNtk, int fVerbose );
static void Ntk_NetworkSymmsBdd( DdManager * dd, Abc_Ntk_t * pNtk, int fNaive, int fVerbose );
static void Ntk_NetworkSymmsPrint( Abc_Ntk_t * pNtk, Extra_SymmInfo_t * pSymms );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [The top level procedure to compute symmetries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSymmetries( Abc_Ntk_t * pNtk, int fUseBdds, int fNaive, int fReorder, int fVerbose )
{
    if ( fUseBdds || fNaive )
        Abc_NtkSymmetriesUsingBdds( pNtk, fNaive, fReorder, fVerbose );
    else
        Abc_NtkSymmetriesUsingSandS( pNtk, fVerbose );
}

/**Function*************************************************************

  Synopsis    [Symmetry computation using simulation and SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSymmetriesUsingSandS( Abc_Ntk_t * pNtk, int fVerbose )
{
//    extern int Sim_ComputeTwoVarSymms( Abc_Ntk_t * pNtk, int fVerbose );
    int nSymms = Sim_ComputeTwoVarSymms( pNtk, fVerbose );
    printf( "The total number of symmetries is %d.\n", nSymms );
}

/**Function*************************************************************

  Synopsis    [Symmetry computation using BDDs (both naive and smart).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSymmetriesUsingBdds( Abc_Ntk_t * pNtk, int fNaive, int fReorder, int fVerbose )
{
    DdManager * dd;
    abctime clk, clkBdd, clkSym;
    int fGarbCollect = 1;

    // compute the global functions
clk = Abc_Clock();
    dd = (DdManager *)Abc_NtkBuildGlobalBdds( pNtk, 10000000, 1, fReorder, 0, fVerbose );
    printf( "Shared BDD size = %d nodes.\n", Abc_NtkSizeOfGlobalBdds(pNtk) ); 
    Cudd_AutodynDisable( dd );
    if ( !fGarbCollect )
        Cudd_DisableGarbageCollection( dd );
    Cudd_zddVarsFromBddVars( dd, 2 );
clkBdd = Abc_Clock() - clk;
    // create the collapsed network
clk = Abc_Clock();
    Ntk_NetworkSymmsBdd( dd, pNtk, fNaive, fVerbose );
clkSym = Abc_Clock() - clk;
    // undo the global functions
    Abc_NtkFreeGlobalBdds( pNtk, 1 );
printf( "Statistics of BDD-based symmetry detection:\n" );
printf( "Algorithm = %s. Reordering = %s. Garbage collection = %s.\n", 
       fNaive? "naive" : "fast", fReorder? "yes" : "no", fGarbCollect? "yes" : "no" );
ABC_PRT( "Constructing BDDs", clkBdd );
ABC_PRT( "Computing symms  ", clkSym );
ABC_PRT( "TOTAL            ", clkBdd + clkSym );
}

/**Function*************************************************************

  Synopsis    [Symmetry computation using BDDs (both naive and smart).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_NetworkSymmsBdd( DdManager * dd, Abc_Ntk_t * pNtk, int fNaive, int fVerbose )
{
    Extra_SymmInfo_t * pSymms;
    Abc_Obj_t * pNode;
    DdNode * bFunc;
    int nSymms = 0;
    int nSupps = 0;
    int i;

    // compute symmetry info for each PO
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
//      bFunc = pNtk->vFuncsGlob->pArray[i];
        bFunc = (DdNode *)Abc_ObjGlobalBdd( pNode );
        nSupps += Cudd_SupportSize( dd, bFunc );
        if ( Cudd_IsConstant(bFunc) )
            continue;
        if ( fNaive )
            pSymms = Extra_SymmPairsComputeNaive( dd, bFunc );
        else
            pSymms = Extra_SymmPairsCompute( dd, bFunc );
        nSymms += pSymms->nSymms;
        if ( fVerbose )
        {
            printf( "Output %6s (%d): ", Abc_ObjName(pNode), pSymms->nSymms );
            Ntk_NetworkSymmsPrint( pNtk, pSymms );
        }
//Extra_SymmPairsPrint( pSymms );
        Extra_SymmPairsDissolve( pSymms );
    }
    printf( "Total number of vars in functional supports = %8d.\n", nSupps );
    printf( "Total number of two-variable symmetries     = %8d.\n", nSymms );
}

/**Function*************************************************************

  Synopsis    [Printing symmetry groups from the symmetry data structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_NetworkSymmsPrint( Abc_Ntk_t * pNtk, Extra_SymmInfo_t * pSymms )
{
    char ** pInputNames;
    int * pVarTaken;
    int i, k, nVars, nSize, fStart;

    // get variable names
    nVars = Abc_NtkCiNum(pNtk);
    pInputNames = Abc_NtkCollectCioNames( pNtk, 0 );

    // alloc the array of marks
    pVarTaken = ABC_ALLOC( int, nVars );
    memset( pVarTaken, 0, sizeof(int) * nVars );

    // print the groups
    fStart = 1;
    nSize = pSymms->nVars;
    for ( i = 0; i < nSize; i++ )
    {
        // skip the variable already considered
        if ( pVarTaken[i] )
            continue;
        // find all the vars symmetric with this one
        for ( k = 0; k < nSize; k++ )
        {
            if ( k == i )
                continue;
            if ( pSymms->pSymms[i][k] == 0 )
                continue;
            // vars i and k are symmetric
            assert( pVarTaken[k] == 0 );
            // there is a new symmetry pair 
            if ( fStart == 1 )
            {  // start a new symmetry class
                fStart = 0;
                printf( "  { %s", pInputNames[ pSymms->pVars[i] ] );
                // mark the var as taken
                pVarTaken[i] = 1;
            }
            printf( " %s", pInputNames[ pSymms->pVars[k] ] );
            // mark the var as taken
            pVarTaken[k] = 1;
        }
        if ( fStart == 0 )
        {
            printf( " }" );
            fStart = 1; 
        }   
    }   
    printf( "\n" );

    ABC_FREE( pInputNames );
    ABC_FREE( pVarTaken );
}

#else

void Abc_NtkSymmetries( Abc_Ntk_t * pNtk, int fUseBdds, int fNaive, int fReorder, int fVerbose ) {}

#endif

/**Function*************************************************************

  Synopsis    [Generating NPN classes of all symmetric function of N variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_SymFunGenerate( int nVars )
{
    char Ones[100] = {0};
    word * pFun;
    int k, m, * pComp, * pPerm, Func;
    Vec_Wrd_t * vCanons = NULL;
    Abc_TtHieMan_t * pMan;
    assert( !(nVars < 1 || nVars > 16) );
	pMan = Abc_TtHieManStart(nVars, 5);
    printf( "Generating truth tables of all symmetric functions of %d variables.\n", nVars );
    pComp = nVars == 6 ? Extra_GreyCodeSchedule( 6 ) : NULL;
    pPerm = nVars == 6 ? Extra_PermSchedule( 6 )     : NULL;
    vCanons = Vec_WrdAlloc( 100 );
    for ( m = 0; m < (1 << (nVars+1)); m++ )
    {
        for ( k = 0; k <= nVars; k++ )
            Ones[k] = '0' + ((m >> k) & 1);
        printf( "%s : ", Ones );
        pFun = Abc_TtSymFunGenerate( Ones, nVars );
        Extra_PrintHex( stdout, (unsigned *)pFun, nVars );
        // compute NPN canicical form
        if ( nVars < 6 )
        {
            unsigned Canon = Extra_TruthCanonNPN( (unsigned)Abc_Tt6Stretch(pFun[0], nVars), nVars );
            printf( " : NPN " );
            Extra_PrintHex( stdout, &Canon, nVars );
            if ( (Func = Vec_WrdFind(vCanons, (word)Canon)) == -1 )
            {
                Func = Vec_WrdSize(vCanons);
                Vec_WrdPush( vCanons, (word)Canon );
            }
            printf( "  Class %3d", Func );
        }
        else if ( nVars == 6 )
        {
            word Canon = Extra_Truth6MinimumExact( pFun[0], pComp, pPerm );
            printf( " : NPN " );
            Extra_PrintHex( stdout, (unsigned *)&Canon, nVars );
            if ( (Func = Vec_WrdFind(vCanons, (word)Canon)) == -1 )
            {
                Func = Vec_WrdSize(vCanons);
                Vec_WrdPush( vCanons, (word)Canon );
            }
            printf( "  Class %3d", Func );
        }
        if ( 0 )
        {
            unsigned Abc_TtCanonicizeWrap(TtCanonicizeFunc func, Abc_TtHieMan_t * p, word * pTruth, int nVars, char * pCanonPerm, int flag);
            unsigned Abc_TtCanonicizeAda(Abc_TtHieMan_t * p, word * pTruth, int nVars, char * pCanonPerm, int iThres);
            char pCanonPerm[16];
            unsigned uCanonPhase;
            if ( nVars < 6 )
            {
                word Truth = Abc_Tt6Stretch(pFun[0], nVars);
                uCanonPhase = Abc_TtCanonicizeWrap(Abc_TtCanonicizeAda, pMan, &Truth, nVars, pCanonPerm, 1199); // -A 9, adjustable algorithm (exact)
                printf( " : NPN " );
                Extra_PrintHex( stdout, (unsigned *)&Truth, nVars );
            }
            else
            {
                uCanonPhase = Abc_TtCanonicizeWrap(Abc_TtCanonicizeAda, pMan, pFun, nVars, pCanonPerm, 1199); // -A 9, adjustable algorithm (exact)
                printf( " : NPN " );
                Extra_PrintHex( stdout, (unsigned *)pFun, nVars );
            }
        }
        printf( "\n" );
        ABC_FREE( pFun );
    }
	Abc_TtHieManStop(pMan);
    if ( Vec_WrdSize(vCanons) )
        printf( "The number of different NPN classes is %d.\n", Vec_WrdSize(vCanons) );
    Vec_WrdFreeP( &vCanons );
    ABC_FREE( pPerm );
    ABC_FREE( pComp );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

