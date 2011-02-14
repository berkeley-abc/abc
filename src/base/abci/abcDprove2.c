/**CFile****************************************************************

  FileName    [abcDprove2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Implementation of "dprove2".]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDprove2.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "aig.h"
#include "saig.h"
#include "fra.h"
#include "ssw.h"
#include "gia.h"
#include "giaAig.h"
#include "cec.h"
#include "int.h"

ABC_NAMESPACE_IMPL_START

 
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Abc_NtkDarBmcInter_int( Aig_Man_t * pMan, Inter_ManParams_t * pPars );

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern Abc_Ntk_t * Abc_NtkFromDar( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan );
extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
extern int         Abc_NtkDarProve( Abc_Ntk_t * pNtk, Fra_Sec_t * pSecPar );

extern void * Abc_FrameReadSave1();
extern void * Abc_FrameReadSave2();

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Implements model checking based on abstraction and speculation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDProve2( Abc_Ntk_t * pNtk, int nConfLast, int fSeparate, int fVeryVerbose, int fVerbose )
{
    Abc_Ntk_t * pNtk2;
    Aig_Man_t * pMan, * pTemp;
    Aig_Man_t * pSave1 = NULL;
    Gia_Man_t * pGia, * pSrm;
    int spectried = 0;
    int absquit   = 0;
    int absfail   = 0;
    int RetValue = -1;
    int clkTotal = clock();
    // derive the AIG manager
    ABC_FREE( pNtk->pModel );
    ABC_FREE( pNtk->pSeqModel );
    pMan = Abc_NtkToDar( pNtk, 0, 1 );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return RetValue;
    }
    assert( pMan->nRegs > 0 );

    if ( fVerbose )
    {
        printf( "Starting BMC...\n" );
        Aig_ManPrintStats( pMan );
    }
    // bmc2 -C 10000
    {
        int nFrames     = 2000;
        int nNodeDelta  = 2000;
        int nBTLimit    = 10000; // different from default
        int nBTLimitAll = 2000000;
        Saig_BmcPerform( pMan, 0, nFrames, nNodeDelta, 0, nBTLimit, nBTLimitAll, fVeryVerbose, 0, NULL );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
        if ( pNtk->pSeqModel )
            goto finish;
    }

    if ( fVerbose )
    {
        printf( "Starting \"dprove\"...\n" );
        Aig_ManPrintStats( pMan );
    }
    // dprove -r -F 8
    {
        Fra_Sec_t SecPar, * pSecPar = &SecPar;
        Fra_SecSetDefaultParams( pSecPar );
        pSecPar->fTryBmc       ^= 1;
        pSecPar->fRetimeFirst  ^= 1;
        pSecPar->nFramesMax     = 8;
        pSecPar->fInterSeparate = 0; //fSeparate;
        pSecPar->fVerbose       = fVeryVerbose;
        RetValue = Abc_NtkDarProve( pNtk, pSecPar );
        // analize the result
        if ( RetValue != -1 )
            goto finish;
    }
    Aig_ManStop( pMan );
    pSave1 = (Aig_Man_t *)Abc_FrameReadSave1();
    pMan = Aig_ManDupSimple( pSave1 );

    // abstraction

    if ( fVerbose )
    {
        printf( "Abstraction...\n" );
        Aig_ManPrintStats( pMan );
    }
abstraction:
    {
        Gia_ParAbs_t Pars, * pPars = &Pars;
        Gia_ManAbsSetDefaultParams( pPars );
        pPars->nConfMaxBmc = 25000;
        pPars->nRatio      =     2;
        pPars->fVerbose    = fVeryVerbose;
/*
        int nFramesMax  =    10;
        int nConfMax    = 10000;
        int fDynamic    =     1;
        int fExtend     =     0;
        int fSkipProof  =     0;
        int nFramesBmc  =  2000;
        int nConfMaxBmc = 25000;  // default 5000;
        int nRatio      =     2;  // default 10;
        int fUseBdds    =     0;
        int fUseDprove  =     0;
        int fVerbose    = fVeryVerbose;
        fExtend    ^= 1;
        fSkipProof ^= 1;
*/
        pMan = Saig_ManCexAbstraction( pTemp = pMan, pPars );
        // if abstractin has solved the problem
        if ( pTemp->pSeqModel )
        {
            pNtk->pSeqModel = pTemp->pSeqModel; pTemp->pSeqModel = NULL;
            Aig_ManStop( pTemp );
            goto finish;
        }
        Aig_ManStop( pTemp );
        if ( pMan == NULL ) // abstraction quits
        {
            absquit = 1;
            pMan = Aig_ManDupSimple( pSave1 );
            goto speculation;
        }
    }
    if ( fVerbose )
    {
        printf( "Problem before trimming...\n" );
        Aig_ManPrintStats( pMan );
    }
    // trim off useless primary inputs
    pMan = Aig_ManDupTrim( pTemp = pMan );
    Aig_ManStop( pTemp );
    if ( fVerbose )
    {
        printf( "\"dprove\" after abstraction...\n" );
        Aig_ManPrintStats( pMan );
    }
    // dprove -r -F 8
    {
        Fra_Sec_t SecPar, * pSecPar = &SecPar;
        Fra_SecSetDefaultParams( pSecPar );
        pSecPar->fTryBmc       ^= 1;
        pSecPar->fRetimeFirst  ^= 1;
        pSecPar->nFramesMax     = 8;
        pSecPar->fInterSeparate = 0; //fSeparate;
        pSecPar->fVerbose       = fVeryVerbose;
        // convert pMan into pNtk
        pNtk2 = Abc_NtkFromAigPhase( pMan );
        RetValue = Abc_NtkDarProve( pNtk2, pSecPar );
        Abc_NtkDelete( pNtk2 );
        // analize the result
        if ( RetValue == 1 )
            goto finish;
        if ( RetValue == 0 )
        {
            // transfer the counter-example!!!
            goto finish;
        }
        assert( RetValue == -1 );
        Aig_ManStop( pMan );
        pMan = (Aig_Man_t *)Abc_FrameReadSave1(); // save2
    }

speculation:
    if ( spectried )
        goto finalbmc;
    spectried = 1;

    if ( fVerbose )
    {
        printf( "Speculation...\n" );
        Aig_ManPrintStats( pMan );
    }
    // convert AIG into GIA
//    pGia = Gia_ManFromAigSimple( pMan ); // DID NOT WORK!
    pGia = Gia_ManFromAig( pMan );
    Aig_ManStop( pMan );
    // &get, eclass, 
    {
        Cec_ParSim_t Pars, * pPars = &Pars;
        Cec_ManSimSetDefaultParams( pPars );
        pPars->fSeqSimulate ^= 1;
        pPars->nWords        = 255;
        pPars->nFrames       = 1000;
        Cec_ManSimulation( pGia, pPars );
    }
    // (spech)*  where spech = &srm; restore save3; bmc2 -F 100 -C 25000; &resim
    while ( 1 )
    {
        // perform speculative reduction
        pSrm = Gia_ManSpecReduce( pGia, 0, 0, fVeryVerbose ); // save3
//        Gia_ManPrintStats( pGia, 0 );
//        Gia_ManPrintStats( pSrm, 0 );
        // bmc2 -F 100 -C 25000
        {
            Abc_Cex_t * pCex;
            int nFrames     = 100; // different from default
            int nNodeDelta  = 2000;
            int nBTLimit    = 25000; // different from default
            int nBTLimitAll = 2000000;
            pTemp = Gia_ManToAig( pSrm, 0 );
//            Aig_ManPrintStats( pTemp );
            Gia_ManStop( pSrm );
            Saig_BmcPerform( pTemp, 0, nFrames, nNodeDelta, 0, nBTLimit, nBTLimitAll, fVeryVerbose, 0, NULL );
            pCex = pTemp->pSeqModel; pTemp->pSeqModel = NULL;
            Aig_ManStop( pTemp );
            if ( pCex == NULL )
                break;
            // perform simulation
            {
                Cec_ParSim_t Pars, * pPars = &Pars;
                Cec_ManSimSetDefaultParams( pPars );
                Cec_ManSeqResimulateCounter( pGia, pPars, pCex );
                ABC_FREE( pCex );
            }
        } 
    }
    Gia_ManStop( pGia );
    // speculatively reduced model is available in pTemp
    // trim off useless primary inputs
    if ( fVerbose )
    {
        printf( "Problem before trimming...\n" );
        Aig_ManPrintStats( pTemp );
    }
    pMan = Aig_ManDupTrim( pTemp );
    Aig_ManStop( pTemp );
    if ( fVerbose )
    {
        printf( "After speculation...\n" );
        Aig_ManPrintStats( pMan );
    }
/*
    // solve the speculatively reduced model
    // dprove -r -F 8
    {
        Fra_Sec_t SecPar, * pSecPar = &SecPar;
        Fra_SecSetDefaultParams( pSecPar );
        pSecPar->fTryBmc       ^= 1;
        pSecPar->fRetimeFirst  ^= 1;
        pSecPar->nFramesMax     = 8;
        pSecPar->fVerbose       = fVeryVerbose;
        pSecPar->fInterSeparate = 0; //fSeparate;
        // convert pMan into pNtk
        pNtk2 = Abc_NtkFromAigPhase( pMan );
        RetValue = Abc_NtkDarProve( pNtk2, pSecPar );
        Abc_NtkDelete( pNtk2 );
        // analize the result
        if ( RetValue == 1 )
            goto finish;
        if ( RetValue == 0 )
            goto finalbmc;
        // could not solve
        Aig_ManStop( pMan );
        pMan = Abc_FrameReadSave1(); // save4
        if ( absquit || absfail )
            goto abstraction;
    }
*/
    // scorr; dc2; orpos; int -r -C 25000
    {
        Ssw_Pars_t Pars, * pPars = &Pars;
        Ssw_ManSetDefaultParams( pPars );
        pMan = Ssw_SignalCorrespondence( pTemp = pMan, pPars );
        Aig_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "After \"scorr\"...\n" );
            Aig_ManPrintStats( pMan );
        }
        pMan = Dar_ManCompress2( pTemp = pMan, 1, 0, 1, 0, 0 ); 
        Aig_ManStop( pTemp );
        if ( fVerbose )
        {
            printf( "After \"dc2\"...\n" );
            Aig_ManPrintStats( pMan );
        }
    }
    {
        Inter_ManParams_t Pars, * pPars = &Pars;
        Inter_ManSetDefaultParams( pPars );
        pPars->fUseSeparate = fSeparate;
        pPars->fRewrite     = 1;
        pPars->nBTLimit     = 25000;
        if ( Saig_ManPoNum(pMan) > 1 && !fSeparate )
        {
            Aig_Man_t * pAux = Aig_ManDupSimple(pMan);
            pTemp = Aig_ManDupOrpos( pAux, 1 );
            RetValue = Abc_NtkDarBmcInter_int( pTemp, pPars );
            Aig_ManStop( pTemp );
            Aig_ManStop( pAux );
        }
        else
            RetValue = Abc_NtkDarBmcInter_int( pMan, pPars );
        // analize the result
        if ( RetValue == 1 )
            goto finish;
        if ( RetValue == 0 )
            goto finalbmc;
        // could not solve
//        Aig_ManStop( pMan );
//        pMan = Abc_FrameReadSave1(); // save4
        if ( absquit || absfail )
            goto abstraction;
    }    

finalbmc:
    Aig_ManStop( pMan );
    pMan = pSave1; pSave1 = NULL;
    if ( fVerbose )
    {
        printf( "Final BMC...\n" );
        Aig_ManPrintStats( pMan );
    }
    // bmc2 unlimited
    {
        int nFrames     = 2000;
        int nNodeDelta  = 2000;
        int nBTLimit    = nConfLast; // different from default
        int nBTLimitAll = 2000000;
        Saig_BmcPerform( pMan, 0, nFrames, nNodeDelta, 0, nBTLimit, nBTLimitAll, fVeryVerbose, 0, NULL );
        ABC_FREE( pNtk->pModel );
        ABC_FREE( pNtk->pSeqModel );
        pNtk->pSeqModel = pMan->pSeqModel; pMan->pSeqModel = NULL;
        if ( pNtk->pSeqModel )
            goto finish;
    }

finish:
    if ( RetValue == 1 )
        printf( "Networks are equivalent.   " );
    if ( RetValue == 0 )
        printf( "Networks are not equivalent.   " );
    if ( RetValue == -1 )
        printf( "Networks are UNDECIDED.   " );
    ABC_PRT( "Time", clock() - clkTotal );
    if ( pNtk->pSeqModel ) 
        printf( "Output %d was asserted in frame %d (use \"write_counter\" to dump a witness).\n", pNtk->pSeqModel->iPo, pNtk->pSeqModel->iFrame );
    // verify counter-example
    if ( pNtk->pSeqModel ) 
    {
        int status = Saig_ManVerifyCex( pMan, pNtk->pSeqModel );
        if ( status == 0 )
            printf( "Abc_NtkDarBmc(): Counter-example verification has FAILED.\n" );
    }
    if ( pSave1 )  
        Aig_ManStop( pSave1 );
    Aig_ManStop( pMan );
    return RetValue;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

