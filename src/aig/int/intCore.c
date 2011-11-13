/**CFile****************************************************************

  FileName    [intCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation engine.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 24, 2008.]

  Revision    [$Id: intCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "intInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedure sets default values of interpolation parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Inter_ManSetDefaultParams( Inter_ManParams_t * p )
{ 
    memset( p, 0, sizeof(Inter_ManParams_t) );
    p->nBTLimit     = 10000; // limit on the number of conflicts
    p->nFramesMax   = 40;    // the max number timeframes to unroll
    p->nSecLimit    = 0;     // time limit in seconds
    p->nFramesK     = 1;     // the number of timeframes to use in induction
    p->fRewrite     = 0;     // use additional rewriting to simplify timeframes
    p->fTransLoop   = 0;     // add transition into the init state under new PI var
    p->fUsePudlak   = 0;     // use Pudluk interpolation procedure
    p->fUseOther    = 0;     // use other undisclosed option
    p->fUseMiniSat  = 0;     // use MiniSat-1.14p instead of internal proof engine
    p->fCheckKstep  = 1;     // check using K-step induction
    p->fUseBias     = 0;     // bias decisions to global variables
    p->fUseBackward = 0;     // perform backward interpolation
    p->fUseSeparate = 0;     // solve each output separately
    p->fDropSatOuts = 0;     // replace by 1 the solved outputs
    p->fVerbose     = 0;     // print verbose statistics
    p->iFrameMax    =-1;
}

/**Function*************************************************************

  Synopsis    [Interplates while the number of conflicts is not exceeded.]

  Description [Returns 1 if proven. 0 if failed. -1 if undecided.]
               
  SideEffects [Does not check the property in 0-th frame.]

  SeeAlso     []

***********************************************************************/
int Inter_ManPerformInterpolation( Aig_Man_t * pAig, Inter_ManParams_t * pPars, int * piFrame )
{
    extern int Inter_ManCheckInductiveContainment( Aig_Man_t * pTrans, Aig_Man_t * pInter, int nSteps, int fBackward );
    Inter_Man_t * p;
    Inter_Check_t * pCheck = NULL;
    Aig_Man_t * pAigTemp;
    int s, i, RetValue, Status, clk, clk2, clkTotal = clock(), timeTemp;
    int nTimeNewOut = pPars->nSecLimit ? time(NULL) + pPars->nSecLimit : 0;

    // sanity checks
    assert( Saig_ManRegNum(pAig) > 0 );
    assert( Saig_ManPiNum(pAig) > 0 );
    assert( Saig_ManPoNum(pAig)-Saig_ManConstrNum(pAig) == 1 );
    if ( pPars->fVerbose && Saig_ManConstrNum(pAig) )
        printf( "Performing interpolation with %d constraints...\n", Saig_ManConstrNum(pAig) );

    if ( Inter_ManCheckInitialState(pAig) )
    {
        *piFrame = 0;
        printf( "Property trivially fails in the initial state.\n" );
        return 0;
    }
/*
    if ( Inter_ManCheckAllStates(pAig) )
    {
        printf( "Property trivially holds in all states.\n" );
        return 1;
    }
*/
    // create interpolation manager
    // can perform SAT sweeping and/or rewriting of this AIG...
    p = Inter_ManCreate( pAig, pPars );
    if ( pPars->fTransLoop )
        p->pAigTrans = Inter_ManStartOneOutput( pAig, 0 );
    else
        p->pAigTrans = Inter_ManStartDuplicated( pAig );
    // derive CNF for the transformed AIG
clk = clock();
    p->pCnfAig = Cnf_Derive( p->pAigTrans, Aig_ManRegNum(p->pAigTrans) ); 
p->timeCnf += clock() - clk;    
    if ( pPars->fVerbose )
    { 
        printf( "AIG: PI/PO/Reg = %d/%d/%d. And = %d. Lev = %d.  CNF: Var/Cla = %d/%d.\n",
            Saig_ManPiNum(pAig), Saig_ManPoNum(pAig), Saig_ManRegNum(pAig), 
            Aig_ManAndNum(pAig), Aig_ManLevelNum(pAig),
            p->pCnfAig->nVars, p->pCnfAig->nClauses );
    }
 
    // derive interpolant
    *piFrame = -1;
    p->nFrames = 1;
    for ( s = 0; ; s++ )
    {
        Cnf_Dat_t * pCnfInter2;

clk2 = clock();
        // initial state
        if ( pPars->fUseBackward )
            p->pInter = Inter_ManStartOneOutput( pAig, 1 );
        else
            p->pInter = Inter_ManStartInitState( Aig_ManRegNum(pAig) );
        assert( Aig_ManPoNum(p->pInter) == 1 );
clk = clock();
        p->pCnfInter = Cnf_Derive( p->pInter, 0 );  
p->timeCnf += clock() - clk;    
        // timeframes
        p->pFrames = Inter_ManFramesInter( pAig, p->nFrames, pPars->fUseBackward );
clk = clock();
        if ( pPars->fRewrite )
        {
            p->pFrames = Dar_ManRwsat( pAigTemp = p->pFrames, 1, 0 );
            Aig_ManStop( pAigTemp );
//        p->pFrames = Fra_FraigEquivence( pAigTemp = p->pFrames, 100, 0 );
//        Aig_ManStop( pAigTemp );
        }
p->timeRwr += clock() - clk;
        // can also do SAT sweeping on the timeframes...
clk = clock();
        if ( pPars->fUseBackward )
            p->pCnfFrames = Cnf_Derive( p->pFrames, Aig_ManPoNum(p->pFrames) );  
        else
//            p->pCnfFrames = Cnf_Derive( p->pFrames, 0 );  
            p->pCnfFrames = Cnf_DeriveSimple( p->pFrames, 0 );  
p->timeCnf += clock() - clk;    
        // report statistics
        if ( pPars->fVerbose )
        {
            printf( "Step = %2d. Frames = 1 + %d. And = %5d. Lev = %5d.  ", 
                s+1, p->nFrames, Aig_ManNodeNum(p->pFrames), Aig_ManLevelNum(p->pFrames) );
            ABC_PRT( "Time", clock() - clk2 );
        }


        //////////////////////////////////////////
        // start containment checking
        if ( !(pPars->fTransLoop || pPars->fUseBackward) )
        {
            pCheck = Inter_CheckStart( p->pAigTrans, pPars->nFramesK );
            // try new containment check for the initial state
clk = clock();
            pCnfInter2 = Cnf_Derive( p->pInter, 1 );  
p->timeCnf += clock() - clk;    
            RetValue = Inter_CheckPerform( pCheck, pCnfInter2, nTimeNewOut );
//            assert( RetValue == 0 );
            Cnf_DataFree( pCnfInter2 );
            if ( p->vInters )
                Vec_PtrPush( p->vInters, Aig_ManDupSimple(p->pInter) );
        }
        //////////////////////////////////////////

        // iterate the interpolation procedure
        for ( i = 0; ; i++ )
        {
            if ( p->nFrames + i >= pPars->nFramesMax )
            { 
                if ( pPars->fVerbose )
                    printf( "Reached limit (%d) on the number of timeframes.\n", pPars->nFramesMax );
                p->timeTotal = clock() - clkTotal;
                Inter_ManStop( p, 0 );
                Inter_CheckStop( pCheck );
                return -1;
            }

            // perform interpolation
            clk = clock();
#ifdef ABC_USE_LIBRARIES
            if ( pPars->fUseMiniSat )
            {
                assert( !pPars->fUseBackward );
                RetValue = Inter_ManPerformOneStepM114p( p, pPars->fUsePudlak, pPars->fUseOther );
            }
            else 
#endif
                RetValue = Inter_ManPerformOneStep( p, pPars->fUseBias, pPars->fUseBackward, nTimeNewOut );

            if ( pPars->fVerbose )
            {
                printf( "   I = %2d. Bmc =%3d. IntAnd =%6d. IntLev =%5d. Conf =%6d.  ", 
                    i+1, i + 1 + p->nFrames, Aig_ManNodeNum(p->pInter), Aig_ManLevelNum(p->pInter), p->nConfCur );
                ABC_PRT( "Time", clock() - clk );
            }
            // remember the number of timeframes completed
            pPars->iFrameMax = i + 1 + p->nFrames;
            if ( RetValue == 0 ) // found a (spurious?) counter-example
            {
                if ( i == 0 ) // real counterexample
                {
                    if ( pPars->fVerbose )
                        printf( "Found a real counterexample in frame %d.\n", p->nFrames );
                    p->timeTotal = clock() - clkTotal;
                    *piFrame = p->nFrames;
//                    pAig->pSeqModel = (Abc_Cex_t *)Inter_ManGetCounterExample( pAig, p->nFrames+1, pPars->fVerbose );
                    {
                        int RetValue;
                        Saig_ParBmc_t ParsBmc, * pParsBmc = &ParsBmc;
                        Saig_ParBmcSetDefaultParams( pParsBmc );
                        pParsBmc->nConfLimit = 100000000;
                        pParsBmc->nStart     = p->nFrames;
                        pParsBmc->fVerbose   = pPars->fVerbose;
                        RetValue = Saig_ManBmcScalable( pAig, pParsBmc );
                        if ( RetValue == 1 )
                            printf( "Error: The problem should be SAT but it is UNSAT.\n" );
                        else if ( RetValue == -1 )
                            printf( "Error: The problem timed out.\n" );
                    }
                    Inter_ManStop( p, 0 );
                    Inter_CheckStop( pCheck );
                    return 0;
                }
                // likely spurious counter-example
                p->nFrames += i;
                Inter_ManClean( p ); 
                break;
            }
            else if ( RetValue == -1 ) 
            {
                if ( pPars->nSecLimit && time(NULL) > nTimeNewOut ) // timed out
                {
                    if ( pPars->fVerbose )
                        printf( "Reached timeout (%d seconds).\n",  pPars->nSecLimit );
                }
                else
                {
                    assert( p->nConfCur >= p->nConfLimit );
                    if ( pPars->fVerbose )
                        printf( "Reached limit (%d) on the number of conflicts.\n", p->nConfLimit );
                }
                p->timeTotal = clock() - clkTotal;
                Inter_ManStop( p, 0 );
                Inter_CheckStop( pCheck );
                return -1;
            }
            assert( RetValue == 1 ); // found new interpolant
            // compress the interpolant
clk = clock();
            if ( p->pInterNew )
            {
//                Ioa_WriteAiger( p->pInterNew, "interpol.aig", 0, 0 );
                p->pInterNew = Dar_ManRwsat( pAigTemp = p->pInterNew, 1, 0 );
//                p->pInterNew = Dar_ManRwsat( pAigTemp = p->pInterNew, 0, 0 );
                Aig_ManStop( pAigTemp );
            }
p->timeRwr += clock() - clk;

            // check if interpolant is trivial
            if ( p->pInterNew == NULL || Aig_ObjChild0(Aig_ManPo(p->pInterNew,0)) == Aig_ManConst0(p->pInterNew) )
            { 
//                printf( "interpolant is constant 0\n" );
                if ( pPars->fVerbose )
                    printf( "The problem is trivially true for all states.\n" );
                p->timeTotal = clock() - clkTotal;
                Inter_ManStop( p, 1 );
                Inter_CheckStop( pCheck );
                return 1;
            }

            // check containment of interpolants
clk = clock();
            if ( pPars->fCheckKstep ) // k-step unique-state induction
            {
                if ( Aig_ManPiNum(p->pInterNew) == Aig_ManPiNum(p->pInter) )
                {
                    if ( pPars->fTransLoop || pPars->fUseBackward )
                        Status = Inter_ManCheckInductiveContainment( p->pAigTrans, p->pInterNew, pPars->nFramesK, pPars->fUseBackward );
                    else
                    {   // new containment check
clk2 = clock();
                        pCnfInter2 = Cnf_Derive( p->pInterNew, 1 );  
p->timeCnf += clock() - clk2;
timeTemp = clock() - clk2;
            
                        Status = Inter_CheckPerform( pCheck, pCnfInter2, nTimeNewOut );
                        Cnf_DataFree( pCnfInter2 );
                        if ( p->vInters )
                            Vec_PtrPush( p->vInters, Aig_ManDupSimple(p->pInterNew) );
                    }
                }
                else
                    Status = 0;
            }
            else // combinational containment
            {
                if ( Aig_ManPiNum(p->pInterNew) == Aig_ManPiNum(p->pInter) )
                    Status = Inter_ManCheckContainment( p->pInterNew, p->pInter );
                else
                    Status = 0;
            }
p->timeEqu += clock() - clk - timeTemp;
            if ( Status ) // contained
            {
                if ( pPars->fVerbose )
                    printf( "Proved containment of interpolants.\n" );
                p->timeTotal = clock() - clkTotal;
                Inter_ManStop( p, 1 );
                Inter_CheckStop( pCheck );
                return 1;
            }
            if ( pPars->nSecLimit && time(NULL) > nTimeNewOut )
            {
                printf( "Reached timeout (%d seconds).\n",  pPars->nSecLimit );
                p->timeTotal = clock() - clkTotal;
                Inter_ManStop( p, 1 );
                Inter_CheckStop( pCheck );
                return -1;
            }
            // save interpolant and convert it into CNF
            if ( pPars->fTransLoop )
            {
                Aig_ManStop( p->pInter );
                p->pInter = p->pInterNew; 
            }
            else
            {
                if ( pPars->fUseBackward )
                {
                    p->pInter = Aig_ManCreateMiter( pAigTemp = p->pInter, p->pInterNew, 2 );
                    Aig_ManStop( pAigTemp );
                    Aig_ManStop( p->pInterNew );
                    // compress the interpolant
clk = clock();
                    p->pInter = Dar_ManRwsat( pAigTemp = p->pInter, 1, 0 );
                    Aig_ManStop( pAigTemp );
p->timeRwr += clock() - clk;
                }
                else // forward with the new containment checking (using only the frontier)
                {
                    Aig_ManStop( p->pInter );
                    p->pInter = p->pInterNew; 
                }
            }
            p->pInterNew = NULL;
            Cnf_DataFree( p->pCnfInter );
clk = clock();
            p->pCnfInter = Cnf_Derive( p->pInter, 0 );  
p->timeCnf += clock() - clk;
        }

        // start containment checking
        Inter_CheckStop( pCheck );
    }
    assert( 0 );
    return RetValue;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

