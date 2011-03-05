/**CFile****************************************************************

  FileName    [giaAbs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Counter-example-guided abstraction refinement.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#include "gia.h"
#include "giaAig.h"
#include "giaAbs.h"
#include "saig.h"

#ifndef _WIN32
#include <unistd.h>
#endif

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Vec_Int_t * Saig_ManProofAbstractionFlops( Aig_Man_t * p, Gia_ParAbs_t * pPars );
extern Vec_Int_t * Saig_ManCexAbstractionFlops( Aig_Man_t * p, Gia_ParAbs_t * pPars );
extern int         Saig_ManCexRefineStep( Aig_Man_t * p, Vec_Int_t * vFlops, Abc_Cex_t * pCex, int fTryFour, int fSensePath, int fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManAbsSetDefaultParams( Gia_ParAbs_t * p )
{
    memset( p, 0, sizeof(Gia_ParAbs_t) );
    p->Algo        =        0;    // algorithm: CBA
    p->nFramesMax  =       10;    // timeframes for PBA
    p->nConfMax    =    10000;    // conflicts for PBA
    p->fDynamic    =        1;    // dynamic unfolding for PBA
    p->fConstr     =        0;    // use constraints
    p->nFramesBmc  =      250;    // timeframes for BMC
    p->nConfMaxBmc =     5000;    // conflicts for BMC
    p->nStableMax  =  1000000;    // the number of stable frames to quit
    p->nRatio      =       10;    // ratio of flops to quit
    p->nBobPar     =  1000000;    // the number of frames before trying to quit
    p->fUseBdds    =        0;    // use BDDs to refine abstraction
    p->fUseDprove  =        0;    // use 'dprove' to refine abstraction
    p->fUseStart   =        1;    // use starting frame
    p->fVerbose    =        0;    // verbose output
    p->fVeryVerbose=        0;    // printing additional information
    p->Status      =       -1;    // the problem status
    p->nFramesDone =       -1;    // the number of rames covered
}

/**Function*************************************************************

  Synopsis    [Transform flop list into flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManFlops2Classes( Gia_Man_t * pGia, Vec_Int_t * vFlops )
{
    Vec_Int_t * vFlopClasses;
    int i, Entry;
    vFlopClasses = Vec_IntStart( Gia_ManRegNum(pGia) );
    Vec_IntForEachEntry( vFlops, Entry, i )
        Vec_IntWriteEntry( vFlopClasses, Entry, 1 );
    return vFlopClasses;
}

/**Function*************************************************************

  Synopsis    [Transform flop map into flop list.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManClasses2Flops( Vec_Int_t * vFlopClasses )
{
    Vec_Int_t * vFlops;
    int i, Entry;
    vFlops = Vec_IntAlloc( 100 );
    Vec_IntForEachEntry( vFlopClasses, Entry, i )
        if ( Entry )
            Vec_IntPush( vFlops, i );
    return vFlops;
}


/**Function*************************************************************

  Synopsis    [Performs abstraction on the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCexAbstraction( Gia_Man_t * p, Vec_Int_t * vFlops )
{
    Gia_Man_t * pGia;
    Aig_Man_t * pNew, * pTemp;
    pNew = Gia_ManToAig( p, 0 );
    pNew = Saig_ManDeriveAbstraction( pTemp = pNew, vFlops );
    Aig_ManStop( pTemp );
    pGia = Gia_ManFromAig( pNew );
    pGia->vCiNumsOrig = pNew->vCiNumsOrig; 
    pNew->vCiNumsOrig = NULL;
    Aig_ManStop( pNew );
    return pGia;

}

/**Function*************************************************************

  Synopsis    [Computes abstracted flops for the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManCexAbstractionFlops( Gia_Man_t * p, Gia_ParAbs_t * pPars )
{
    Vec_Int_t * vFlops;
    Aig_Man_t * pNew;
    pNew = Gia_ManToAig( p, 0 );
    vFlops = Saig_ManCexAbstractionFlops( pNew, pPars );
    p->pCexSeq = pNew->pSeqModel; pNew->pSeqModel = NULL;
    Aig_ManStop( pNew );
    return vFlops;
}

/**Function*************************************************************

  Synopsis    [Computes abstracted flops for the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManProofAbstractionFlops( Gia_Man_t * p, Gia_ParAbs_t * pPars )
{
    Vec_Int_t * vFlops;
    Aig_Man_t * pNew;
    pNew = Gia_ManToAig( p, 0 );
    vFlops = Saig_ManProofAbstractionFlops( pNew, pPars );
    p->pCexSeq = pNew->pSeqModel; pNew->pSeqModel = NULL;
    Aig_ManStop( pNew );
    return vFlops;
}

/**Function*************************************************************

  Synopsis    [Starts abstraction by computing latch map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCexAbstractionStart( Gia_Man_t * p, Gia_ParAbs_t * pPars )
{
    Vec_Int_t * vFlops;
    if ( p->vFlopClasses != NULL )
    {
        printf( "Gia_ManCexAbstractionStart(): Abstraction latch map is present but will be rederived.\n" );
        Vec_IntFreeP( &p->vFlopClasses );
    }
    vFlops = Gia_ManCexAbstractionFlops( p, pPars );
    if ( vFlops )
    {
        p->vFlopClasses = Gia_ManFlops2Classes( p, vFlops );
        Vec_IntFree( vFlops );
    }
}

/**Function*************************************************************

  Synopsis    [Derives abstraction using the latch map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCexAbstractionDerive( Gia_Man_t * pGia )
{
    Vec_Int_t * vFlops;
    Gia_Man_t * pAbs = NULL;
    if ( pGia->vFlopClasses == NULL )
    {
        printf( "Gia_ManCexAbstractionDerive(): Abstraction latch map is missing.\n" );
        return NULL;
    }
    vFlops = Gia_ManClasses2Flops( pGia->vFlopClasses );
    pAbs = Gia_ManCexAbstraction( pGia, vFlops );
    Vec_IntFree( vFlops );
    return pAbs;
}

/**Function*************************************************************

  Synopsis    [Refines abstraction using the latch map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCexAbstractionRefine( Gia_Man_t * pGia, Abc_Cex_t * pCex, int fTryFour, int fSensePath, int fVerbose )
{
    Aig_Man_t * pNew;
    Vec_Int_t * vFlops;
    if ( pGia->vFlopClasses == NULL )
    {
        printf( "Gia_ManCexAbstractionRefine(): Abstraction latch map is missing.\n" );
        return -1;
    }
    pNew = Gia_ManToAig( pGia, 0 );
    vFlops = Gia_ManClasses2Flops( pGia->vFlopClasses );
    if ( !Saig_ManCexRefineStep( pNew, vFlops, pCex, fTryFour, fSensePath, fVerbose ) )
    {
        pGia->pCexSeq = pNew->pSeqModel; pNew->pSeqModel = NULL;
        Vec_IntFree( vFlops );
        Aig_ManStop( pNew );
        return 0;
    }
    Vec_IntFree( pGia->vFlopClasses );
    pGia->vFlopClasses = Gia_ManFlops2Classes( pGia, vFlops );
    Vec_IntFree( vFlops );
    Aig_ManStop( pNew );
    return -1;
}

/**Function*************************************************************

  Synopsis    [Starts abstraction by computing latch map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManProofAbstractionStart( Gia_Man_t * pGia, Gia_ParAbs_t * pPars )
{
    Vec_Int_t * vFlops;
    if ( pGia->vFlopClasses != NULL )
    {
        printf( "Gia_ManProofAbstractionStart(): Abstraction latch map is present but will be rederived.\n" );
        Vec_IntFreeP( &pGia->vFlopClasses );
    }
    vFlops = Gia_ManProofAbstractionFlops( pGia, pPars );
    if ( vFlops )
    {
        pGia->vFlopClasses = Gia_ManFlops2Classes( pGia, vFlops );
        Vec_IntFree( vFlops );
    }
}


/**Function*************************************************************

  Synopsis    [Read flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Gia_ManReadFile( char * pFileName )
{
    FILE * pFile;
    Vec_Str_t * vStr;
    int c;
    pFile = fopen( pFileName, "r" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\".\n", pFileName );
        return NULL;
    }
    vStr = Vec_StrAlloc( 100 );
    while ( (c = fgetc(pFile)) != EOF )
        Vec_StrPush( vStr, (char)c );
    Vec_StrPush( vStr, '\0' );
    fclose( pFile );
    return vStr;
}

/**Function*************************************************************

  Synopsis    [Read flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManReadBinary( char * pFileName, char * pToken )
{
    Vec_Int_t * vMap = NULL;
    Vec_Str_t * vStr;
    char * pStr;
    int i, Length;
    vStr = Gia_ManReadFile( pFileName );
    if ( vStr == NULL )
        return NULL;
    pStr = Vec_StrArray( vStr );
    pStr = strstr( pStr, pToken );
    if ( pStr != NULL )
    {
        pStr  += strlen( pToken );
        vMap   = Vec_IntAlloc( 100 );
        Length = strlen( pStr );
        for ( i = 0; i < Length; i++ )
        {
            if ( pStr[i] == '0' )
                Vec_IntPush( vMap, 0 );
            else if ( pStr[i] == '1' )
                Vec_IntPush( vMap, 1 );
            if ( ('a' <= pStr[i] && pStr[i] <= 'z') || 
                 ('A' <= pStr[i] && pStr[i] <= 'Z') )
                break;
        }
    }
    Vec_StrFree( vStr );
    return vMap;
}

/**Function*************************************************************

  Synopsis    [Read flop map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManReadInteger( char * pFileName, char * pToken )
{
    int Result = -1;
    Vec_Str_t * vStr;
    char * pStr;
    vStr = Gia_ManReadFile( pFileName );
    if ( vStr == NULL )
        return -1;
    pStr = Vec_StrArray( vStr );
    pStr = strstr( pStr, pToken );
    if ( pStr != NULL )
        Result = atoi( pStr + strlen(pToken) );
    Vec_StrFree( vStr );
    return Result;
}


/**Function*************************************************************

  Synopsis    [Starts abstraction by computing latch map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCexAbstractionStartNew( Gia_Man_t * pGia, Gia_ParAbs_t * pPars )
{
    char BufTimeOut[100];
    char BufTimeOutVT[100];
    char Command[1000];
    char * pFileNameIn  = "cex_abstr_in_.aig";
    char * pFileNameOut = "cex_abstr_out_.txt";
    FILE * pFile;
    Vec_Int_t * vCex;
    int RetValue, clk; 
    if ( pGia->vFlopClasses != NULL )
    {
        printf( "Gia_ManCexAbstractionStartNew(): Abstraction latch map is present but will be rederived.\n" );
        Vec_IntFreeP( &pGia->vFlopClasses );
    }
    Gia_WriteAiger( pGia, pFileNameIn, 0, 0 );
    sprintf( BufTimeOut, "-timeout=%d", pPars->TimeOut );
    sprintf( BufTimeOutVT, "-vt=%d", pPars->TimeOutVT );
//ABC switch  =>  cex_abstr switch
//-cba   =>  <input> <output>
//-pba   =>  ,bmc -pba-soft <input> <output>
//-cba-then-pba  =>  -pba-soft <input> <output>
//-cba-with-pba  =>  -pba <input> <output>
    if ( pPars->Algo == 0 )
    {
        sprintf( Command, "cex_abstr %s %s -depth=%d -stable=%d -confl=%d -bob=%d %s %s %s %s", 
            pPars->fVerbose? "":"-quiet", 
            pPars->fVeryVerbose? "-sat-verbosity=1":"", 
            pPars->nFramesBmc, pPars->nStableMax, pPars->nConfMaxBmc, pPars->nBobPar,
            pPars->TimeOut? BufTimeOut : "", 
            pPars->TimeOutVT? BufTimeOutVT : "", 
            pFileNameIn, pFileNameOut );
    }
    else if ( pPars->Algo == 1 )
    {
        sprintf( Command, "cex_abstr %s %s -depth=%d -confl=%d -bob=%d ,bmc -pba-soft %s %s %s %s", 
            pPars->fVerbose? "":"-quiet", 
            pPars->fVeryVerbose? "-sat-verbosity=1":"", 
            pPars->nFramesBmc, pPars->nConfMaxBmc, pPars->nBobPar,
            pPars->TimeOut? BufTimeOut : "", 
            pPars->TimeOutVT? BufTimeOutVT : "", 
            pFileNameIn, pFileNameOut );
    }
    else if ( pPars->Algo == 2 )
    {
        sprintf( Command, "cex_abstr %s %s -depth=%d -stable=%d -confl=%d -bob=%d -pba-soft %s %s %s %s", 
            pPars->fVerbose? "":"-quiet", 
            pPars->fVeryVerbose? "-sat-verbosity=1":"", 
            pPars->nFramesBmc, pPars->nStableMax, pPars->nConfMaxBmc, pPars->nBobPar,
            pPars->TimeOut? BufTimeOut : "", 
            pPars->TimeOutVT? BufTimeOutVT : "", 
            pFileNameIn, pFileNameOut );
    }
    else if ( pPars->Algo == 3 )
    {
        sprintf( Command, "cex_abstr %s %s -depth=%d -stable=%d -confl=%d -bob=%d -pba %s %s %s %s", 
            pPars->fVerbose? "":"-quiet", 
            pPars->fVeryVerbose? "-sat-verbosity=1":"", 
            pPars->nFramesBmc, pPars->nStableMax, pPars->nConfMaxBmc, pPars->nBobPar,
            pPars->TimeOut? BufTimeOut : "", 
            pPars->TimeOutVT? BufTimeOutVT : "", 
            pFileNameIn, pFileNameOut );
    }
    else
    {
        printf( "Unnknown option (algo=%d). CBA (algo=0) is assumed.\n", pPars->Algo );
        sprintf( Command, "cex_abstr %s %s -depth=%d -stable=%d -confl=%d -bob=%d %s %s %s %s", 
            pPars->fVerbose? "":"-quiet", 
            pPars->fVeryVerbose? "-sat-verbosity=1":"", 
            pPars->nFramesBmc, pPars->nStableMax, pPars->nConfMaxBmc, pPars->nBobPar,
            pPars->TimeOut? BufTimeOut : "", 
            pPars->TimeOutVT? BufTimeOutVT : "", 
            pFileNameIn, pFileNameOut );
    }
    // run the command
    printf( "Executing command line \"%s\"\n", Command );
    clk = clock();
    RetValue = system( Command );
    clk = clock() - clk;
#ifdef WIN32
    _unlink( pFileNameIn );
#else
    unlink( pFileNameIn );
#endif
    if ( RetValue == -1 )
    {
        fprintf( stdout, "Command \"%s\" did not succeed.\n", Command );
        return;
    }
    // check that the input PostScript file is okay
    if ( (pFile = fopen( pFileNameOut, "r" )) == NULL )
    {
        fprintf( stdout, "Cannot open intermediate file \"%s\".\n", pFileNameOut );
        return;
    }
    fclose( pFile ); 
    pPars->nFramesDone = Gia_ManReadInteger( pFileNameOut, "depth:" );
    if ( pPars->nFramesDone == -1 )
        printf( "Gia_ManCexAbstractionStartNew(): Cannot read the number of frames covered by BMC.\n" );
    pGia->vFlopClasses = Gia_ManReadBinary( pFileNameOut, "abstraction:" );
    vCex = Gia_ManReadBinary( pFileNameOut, "counter-example:" );
    if ( vCex )
    {
        int nFrames = (Vec_IntSize(vCex) - Gia_ManRegNum(pGia)) / Gia_ManPiNum(pGia);
        int nRemain = (Vec_IntSize(vCex) - Gia_ManRegNum(pGia)) % Gia_ManPiNum(pGia);
        if ( nRemain != 0 )
        {
            printf( "Counter example has a wrong length.\n" );
        }
        else
        {
            printf( "Problem is satisfiable. Found counter-example in frame %d.  ", nFrames-1 );
            Abc_PrintTime( 1, "Time", clk );
            pGia->pCexSeq = Abc_CexCreate( Gia_ManRegNum(pGia), Gia_ManPiNum(pGia), Vec_IntArray(vCex), nFrames-1, 0, 0 );
            if ( !Gia_ManVerifyCex( pGia, pGia->pCexSeq, 0 ) )
                Abc_Print( 1, "Generated counter-example is INVALID.\n" );
            pPars->Status = 0;
        }
        Vec_IntFreeP( &vCex );
    }
#ifdef WIN32
    _unlink( pFileNameOut );
#else
    unlink( pFileNameOut );
#endif
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

