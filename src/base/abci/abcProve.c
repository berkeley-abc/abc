/**CFile****************************************************************

  FileName    [abcProve.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Proves the miter using AIG rewriting, FRAIGing, and SAT solving.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcProve.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "fraig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int  Abc_NtkRewrite( Abc_Ntk_t * pNtk, int fUpdateLevel, int fUseZeros, int fVerbose );
extern int  Abc_NtkRefactor( Abc_Ntk_t * pNtk, int nNodeSizeMax, int nConeSizeMax, bool fUpdateLevel, bool fUseZeros, bool fUseDcs, bool fVerbose );
extern Abc_Ntk_t * Abc_NtkFromFraig( Fraig_Man_t * pMan, Abc_Ntk_t * pNtk );

static Abc_Ntk_t * Abc_NtkMiterFraig( Abc_Ntk_t * pNtk, int nBTLimit, int * pRetValue, int * pNumFails );
static void Abc_NtkMiterPrint( Abc_Ntk_t * pNtk, char * pString, int clk, int fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Attempts to solve the miter using a number of tricks.]

  Description [Returns -1 if timed out; 0 if SAT; 1 if UNSAT. Returns
  a simplified version of the original network (or a constant 0 network).
  In case the network is not a constant zero and a SAT assignment is found,
  pNtk->pModel contains a satisfying assignment.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMiterProve( Abc_Ntk_t ** ppNtk, int nConfLimit, int nImpLimit, int fUseRewrite, int fUseFraig, int fVerbose )
{
    Abc_Ntk_t * pNtk, * pNtkTemp;
    int nConfsStart = 1000, nImpsStart = 0, nBTLimitStart = 2;  // was 5000
    int nConfs, nImps, nBTLimit, RetValue, nSatFails;
    int nIter = 0, clk, timeStart = clock();

    // get the starting network
    pNtk = *ppNtk;
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkPoNum(pNtk) == 1 );

    // set the initial limits
    nConfs   = !nConfLimit? nConfsStart : ABC_MIN( nConfsStart, nConfLimit );
    nImps    = !nImpLimit ? nImpsStart  : ABC_MIN( nImpsStart , nImpLimit );
    nBTLimit = nBTLimitStart;

    if ( fVerbose )
        printf( "Global resource limits: ConfsLim = %6d. ImpsLim = %d.\n", nConfLimit, nImpLimit );

    // if SAT only, solve without iteration
    if ( !fUseRewrite && !fUseFraig )
    {
        clk = clock();
        RetValue = Abc_NtkMiterSat( pNtk, nConfLimit, nImpLimit, 0 );
        Abc_NtkMiterPrint( pNtk, "SAT solving", clk, fVerbose );
        *ppNtk = pNtk;
        return RetValue;
    }

    // check the current resource limits
    do {
        nIter++;

        if ( fVerbose )
        {
            printf( "ITERATION %2d : Confs = %6d. FraigBTL = %3d. \n", nIter, nConfs, nBTLimit );
            fflush( stdout );
        }

        // try brute-force SAT
        clk = clock();
        RetValue = Abc_NtkMiterSat( pNtk, nConfs, nImps, 0 );
        Abc_NtkMiterPrint( pNtk, "SAT solving", clk, fVerbose );
        if ( RetValue >= 0 )
            break;

        if ( fUseRewrite )
        {
            clk = clock();

            // try rewriting
            Abc_NtkRewrite( pNtk, 0, 0, 0 );
            if ( (RetValue = Abc_NtkMiterIsConstant(pNtk)) >= 0 )
                break;
            Abc_NtkRefactor( pNtk, 10, 16, 0, 0, 0, 0 );
            if ( (RetValue = Abc_NtkMiterIsConstant(pNtk)) >= 0 )
                break;
            pNtk = Abc_NtkBalance( pNtkTemp = pNtk, 0, 0, 0 );  Abc_NtkDelete( pNtkTemp );
            if ( (RetValue = Abc_NtkMiterIsConstant(pNtk)) >= 0 )
                break;

            Abc_NtkMiterPrint( pNtk, "Rewriting  ", clk, fVerbose );
        }

        if ( fUseFraig )
        {
            // try FRAIGing
            clk = clock();
            pNtk = Abc_NtkMiterFraig( pNtkTemp = pNtk, nBTLimit, &RetValue, &nSatFails );  Abc_NtkDelete( pNtkTemp );
            Abc_NtkMiterPrint( pNtk, "FRAIGing   ", clk, fVerbose );
//            printf( "NumFails = %d\n", nSatFails );
            if ( RetValue >= 0 )
                break;
        }
        else
            nSatFails = 1000;

        // increase resource limits
//        nConfs   = ABC_MIN( nConfs * 3 / 2, 1000000000 );   // was 4/2
        nConfs   = nSatFails * nBTLimit / 2;   
        nImps    = ABC_MIN( nImps  * 3 / 2, 1000000000 );
        nBTLimit = ABC_MIN( nBTLimit * 8,   1000000000 );

        // timeout at 5 minutes
//        if ( clock() - timeStart >= 1200 * CLOCKS_PER_SEC )
//            break;
        if ( nIter == 7 )
            break;
    }    
//    while ( (nConfLimit == 0 || nConfs <= nConfLimit) && 
//            (nImpLimit  == 0 || nImps  <= nImpLimit ) );
    while ( 1 );

    // try to prove it using brute force SAT
    if ( RetValue < 0 )
    {
        clk = clock();
        RetValue = Abc_NtkMiterSat( pNtk, nConfLimit, nImpLimit, 0 );
        Abc_NtkMiterPrint( pNtk, "SAT solving", clk, fVerbose );
    }

    // assign the model if it was proved by rewriting (const 1 miter)
    if ( RetValue == 0 && pNtk->pModel == NULL )
    {
        pNtk->pModel = ALLOC( int, Abc_NtkCiNum(pNtk) );
        memset( pNtk->pModel, 0, sizeof(int) * Abc_NtkCiNum(pNtk) );
    }
    *ppNtk = pNtk;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Attempts to solve the miter using a number of tricks.]

  Description [Returns -1 if timed out; 0 if SAT; 1 if UNSAT.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkMiterFraig( Abc_Ntk_t * pNtk, int nBTLimit, int * pRetValue, int * pNumFails )
{
    Abc_Ntk_t * pNtkNew;
    Fraig_Params_t Params, * pParams = &Params;
    Fraig_Man_t * pMan;
    int nWords1, nWords2, nWordsMin, RetValue;
    int * pModel;

    // to determine the number of simulation patterns
    // use the following strategy
    // at least 64 words (32 words random and 32 words dynamic)
    // no more than 256M for one circuit (128M + 128M)
    nWords1 = 32;
    nWords2 = (1<<27) / (Abc_NtkNodeNum(pNtk) + Abc_NtkCiNum(pNtk));
    nWordsMin = ABC_MIN( nWords1, nWords2 );

    // set the FRAIGing parameters
    Fraig_ParamsSetDefault( pParams );
    pParams->nPatsRand  = nWordsMin * 32; // the number of words of random simulation info
    pParams->nPatsDyna  = nWordsMin * 32; // the number of words of dynamic simulation info
    pParams->nBTLimit   = nBTLimit;       // the max number of backtracks
    pParams->nSeconds   = -1;             // the runtime limit
    pParams->fTryProve  = 0;              // do not try to prove the final miter
    pParams->fDoSparse  = 1;              // try proving sparse functions
    pParams->fVerbose   = 0;

    // transform the target into a fraig
    pMan = Abc_NtkToFraig( pNtk, pParams, 0, 0 ); 
    Fraig_ManProveMiter( pMan );
    RetValue = Fraig_ManCheckMiter( pMan );

    // create the network 
    pNtkNew = Abc_NtkFromFraig( pMan, pNtk );

    // save model
    if ( RetValue == 0 )
    {
        pModel = Fraig_ManReadModel( pMan );
        FREE( pNtkNew->pModel );
        pNtkNew->pModel = ALLOC( int, Abc_NtkCiNum(pNtkNew) );
        memcpy( pNtkNew->pModel, pModel, sizeof(int) * Abc_NtkCiNum(pNtkNew) );
    }

    // save the return values
    *pRetValue = RetValue;
    *pNumFails = Fraig_ManReadSatFails( pMan );

    // delete the fraig manager
    Fraig_ManFree( pMan );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Attempts to solve the miter using a number of tricks.]

  Description [Returns -1 if timed out; 0 if SAT; 1 if UNSAT.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMiterPrint( Abc_Ntk_t * pNtk, char * pString, int clk, int fVerbose )
{
    if ( !fVerbose )
        return;
    printf( "Nodes = %7d.  Levels = %4d.  ", Abc_NtkNodeNum(pNtk), Abc_AigGetLevelNum(pNtk) );
    PRT( pString, clock() - clk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


