/**CFile****************************************************************

  FileName    [giaDeep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Experiments with synthesis.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaDeep.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"

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
Gia_Man_t * Gia_ManDeepSynOne( int nNoImpr, int TimeOut, int nAnds, int Seed, int fUseTwo, int fVerbose, Vec_Ptr_t * vGias )
{
    abctime nTimeToStop = TimeOut ? Abc_Clock() + TimeOut * CLOCKS_PER_SEC : 0;
    abctime clkStart    = Abc_Clock();
    int s, i, IterMax   = 100000, nAndsMin = -1, iIterLast = -1;
    Gia_Man_t * pTemp   = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
    Gia_Man_t * pNew    = Gia_ManDup( pTemp );
    Abc_Random(1);
    for ( s = 0; s < 10+Seed; s++ )
        Abc_Random(0);
    for ( i = 0; i < IterMax; i++ )
    {
        char * pCompress2rs = "balance -l; resub -K 6 -l; rewrite -l; resub -K 6 -N 2 -l; refactor -l; resub -K 8 -l; balance -l; resub -K 8 -N 2 -l; rewrite -l; resub -K 10 -l; rewrite -z -l; resub -K 10 -N 2 -l; balance -l; resub -K 12 -l; refactor -z -l; resub -K 12 -N 2 -l; rewrite -z -l; balance -l";
        unsigned Rand = Abc_Random(0);
        int fDch = Rand & 1;
        //int fCom = (Rand >> 1) & 3;
        int fCom = (Rand >> 1) & 1;
        int fFx  = (Rand >> 2) & 1;
        int KLut = fUseTwo ? 2 + (i % 5) : 3 + (i % 4);
        int fChange = 0;
        char Command[2000];
        char pComp[1000];
        if ( fCom == 3 )
            sprintf( pComp, "; &put; %s; %s; %s; &get", pCompress2rs, pCompress2rs, pCompress2rs );
        else if ( fCom == 2 )
            sprintf( pComp, "; &put; %s; %s; &get", pCompress2rs, pCompress2rs );
        else if ( fCom == 1 )
            sprintf( pComp, "; &put; %s; &get", pCompress2rs );
        else if ( fCom == 0 )
            sprintf( pComp, "; &dc2" );
        sprintf( Command, "&dch%s; &if -a -K %d; &mfs -e -W 20 -L 20%s%s",
            fDch ? " -f" : "", KLut, fFx ? "; &fx; &st" : "", pComp );
        if ( Abc_FrameIsBatchMode() )
        {
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) )
            {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
                return NULL;
            }
        }
        else
        {
            Abc_FrameSetBatchMode( 1 );
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) )
            {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
                return NULL;
            }
            Abc_FrameSetBatchMode( 0 );
        }
        pTemp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
        if ( Gia_ManAndNum(pNew) > Gia_ManAndNum(pTemp) )
        {
            Gia_ManStop( pNew );
            pNew = Gia_ManDup( pTemp );
            fChange = 1;
            iIterLast = i;
            if ( vGias ) 
                Vec_PtrPush( vGias, Gia_ManDup(pTemp) );
        }
        else if ( Gia_ManAndNum(pNew) + Gia_ManAndNum(pNew)/10 < Gia_ManAndNum(pTemp) ) 
        {
            //printf( "Updating\n" );
            //Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), Gia_ManDup(pNew) );
        }
        if ( fChange && fVerbose )
        {
            printf( "Iter %6d : ", i );
            printf( "Time %8.2f sec : ", (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC );
            printf( "And = %6d  ", Gia_ManAndNum(pNew) );
            printf( "Lev = %3d  ", Gia_ManLevelNum(pNew) );
            if ( fChange ) 
                printf( "<== best : " );
            else if ( fVerbose )
                printf( "           " );
            printf( "%s", Command );
            printf( "\n" );
        }
        if ( nTimeToStop && Abc_Clock() > nTimeToStop )
        {
            if ( !Abc_FrameIsBatchMode() )
            printf( "Runtime limit (%d sec) is reached after %d iterations.\n", TimeOut, i );
            break;
        }
        if ( i - iIterLast > nNoImpr )
        {
            printf( "Completed %d iterations without improvement in %.2f seconds.\n", 
                nNoImpr, (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC );
            break;
        }
    }
    if ( i == IterMax )
        printf( "Iteration limit (%d iters) is reached after %.2f seconds.\n", IterMax, (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC );
    else if ( nAnds && nAndsMin <= nAnds )
        printf( "Quality goal (%d nodes <= %d nodes) is achieved after %d iterations and %.2f seconds.\n", 
            nAndsMin, nAnds, i, (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC );
    return pNew;
}
Gia_Man_t * Gia_ManDeepSyn( Gia_Man_t * pGia, int nIters, int nNoImpr, int TimeOut, int nAnds, int Seed, int fUseTwo, int fChoices, int fVerbose )
{
    Vec_Ptr_t * vGias = fChoices ? Vec_PtrAlloc(100) : NULL;
    Gia_Man_t * pInit = Gia_ManDup(pGia);
    Gia_Man_t * pBest = Gia_ManDup(pGia);
    Gia_Man_t * pThis;
    int i;
    if ( vGias ) 
        Vec_PtrPush( vGias, Gia_ManDup(pGia) );    
    for ( i = 0; i < nIters; i++ )
    {
        Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), Gia_ManDup(pInit) );
        pThis = Gia_ManDeepSynOne( nNoImpr, TimeOut, nAnds, Seed+i, fUseTwo, fVerbose, vGias );
        if ( Gia_ManAndNum(pBest) > Gia_ManAndNum(pThis) ) 
        {
            Gia_ManStop( pBest );
            pBest = pThis;
        }
        else 
            Gia_ManStop( pThis );
        
    }
    Gia_ManStop( pInit );
    if ( vGias) {
        if ( Vec_PtrSize(vGias) > 1 ) {
            extern Gia_Man_t * Gia_ManCreateChoicesArray( Vec_Ptr_t * vGias, int fVerbose );
            Gia_ManStopP( &pBest );
            pBest = Gia_ManCreateChoicesArray( vGias, fVerbose );
        }
        // cleanup
        Gia_Man_t * pTemp;
        Vec_PtrForEachEntry( Gia_Man_t *, vGias, pTemp, i )
            Gia_ManStop( pTemp );
        Vec_PtrFree( vGias ); 
    }
    return pBest;
}

/**Function*************************************************************

  Synopsis    [Generating one AIG by applying a randomized script.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManRandSyn( Gia_Man_t * p, unsigned random_seed )
{
    char * pCompress2rs = "balance -l; resub -K 6 -l; rewrite -l; resub -K 6 -N 2 -l; refactor -l; resub -K 8 -l; balance -l; resub -K 8 -N 2 -l; rewrite -l; resub -K 10 -l; rewrite -z -l; resub -K 10 -N 2 -l; balance -l; resub -K 12 -l; refactor -z -l; resub -K 12 -N 2 -l; rewrite -z -l; balance -l";
    unsigned Rand = random_seed;
    int fDch = Rand & 1;
    //int fCom = (Rand >> 1) & 3;
    int fCom = (Rand >> 1) & 1;
    int fFx  = (Rand >> 2) & 1;
    int fUseTwo = 0;
    int KLut = fUseTwo ? 2 + (Rand % 5) : 3 + (Rand % 4);
    //int fChange = 0;
    char Command[2000];
    char pComp[1000];
    if ( fCom == 3 )
        sprintf( pComp, "; &put; %s; %s; %s; &get", pCompress2rs, pCompress2rs, pCompress2rs );
    else if ( fCom == 2 )
        sprintf( pComp, "; &put; %s; %s; &get", pCompress2rs, pCompress2rs );
    else if ( fCom == 1 )
        sprintf( pComp, "; &put; %s; &get", pCompress2rs );
    else if ( fCom == 0 )
        sprintf( pComp, "; &dc2" );
    sprintf( Command, "&dch%s; &if -a -K %d; &mfs -e -W 20 -L 20%s%s",
        fDch ? " -f" : "", KLut, fFx ? "; &fx; &st" : "", pComp );
    Gia_Man_t * pOld = Abc_FrameGetGia(Abc_FrameGetGlobalFrame());
    Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), Gia_ManDup(p) );
    if ( Abc_FrameIsBatchMode() )
    {
        if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) )
        {
            Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
            return NULL;
        }
    }
    else
    {
        Abc_FrameSetBatchMode( 1 );
        if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) )
        {
            Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
            return NULL;
        }
        Abc_FrameSetBatchMode( 0 );
    }
    Gia_Man_t * pRes = Abc_FrameGetGia(Abc_FrameGetGlobalFrame());
    Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pOld );
    return pRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Gia_ManDeepSynParetoUpdate( Vec_Ptr_t * vPareto, Gia_Man_t * pCand, int nLevels, int nAnds )
{
    Gia_Man_t * pBest = (Gia_Man_t *)Vec_PtrGetEntry( vPareto, nLevels );
    if ( pBest == NULL || Gia_ManAndNum(pBest) > nAnds )
    {
        if ( pBest )
            Gia_ManStop( pBest );
        Vec_PtrSetEntry( vPareto, nLevels, Gia_ManDup(pCand) );
    }
}

static void Gia_ManDeepSynParetoPrint( Vec_Ptr_t * vPareto )
{
    Gia_Man_t * pTemp;
    int i, fFirst = 1;
    printf( "Pareto points:" );
    Vec_PtrForEachEntry( Gia_Man_t *, vPareto, pTemp, i )
    {
        if ( pTemp == NULL )
            continue;
        printf( "%s%d:%d", fFirst ? " " : " ", i, Gia_ManAndNum(pTemp) );
        fFirst = 0;
    }
    if ( fFirst )
        printf( " none" );
    printf( "\n" );
}

static void Gia_ManDeepSynParetoSave( Vec_Ptr_t * vPareto, char * pBase )
{
    Gia_Man_t * pTemp;
    char FileName[1000];
    int i;
    if ( pBase == NULL )
        pBase = Extra_UtilStrsav( "gia" );
    Vec_PtrForEachEntry( Gia_Man_t *, vPareto, pTemp, i )
    {
        if ( pTemp == NULL )
            continue;
        sprintf( FileName, "%s_%d_%d.aig", pBase, i, Gia_ManAndNum(pTemp) );
        Gia_AigerWrite( pTemp, FileName, 0, 0, 0 );
    }
    ABC_FREE( pBase );
}

Gia_Man_t * Gia_ManDeepSynOne2( int nNoImpr, int TimeOut, int nAnds, int Seed, int fUseTwo, int fVerbose, Vec_Ptr_t * vGias, Vec_Ptr_t * vPareto )
{
    abctime nTimeToStop = TimeOut ? Abc_Clock() + TimeOut * CLOCKS_PER_SEC : 0;
    abctime clkStart    = Abc_Clock();
    int s, i, k, IterMax = 100000, nLevelsMin = -1, nAndsMin = -1;
    int nNoImprCount = 0;
    Gia_Man_t * pTemp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
    Gia_Man_t * pNew  = Gia_ManDup( pTemp );
    (void)fUseTwo;
    Abc_Random(1);
    for ( s = 0; s < 10+Seed; s++ )
        Abc_Random(0);
    nLevelsMin = Gia_ManLevelNum(pNew);
    nAndsMin = Gia_ManAndNum(pNew);
    for ( i = 0; i < IterMax; )
    {
        unsigned Rand = Abc_Random(0);
        int fDch = Rand & 1;
        int fResyn = (Rand >> 1) % 3;
        int fChange = 0;
        char Command[2000];
        char pResyn[200];
        if ( fResyn == 0 )
            sprintf( pResyn, "&resyn3" );
        else if ( fResyn == 1 )
            sprintf( pResyn, "&resyn3rs" );
        else
            sprintf( pResyn, "&resyn3; &resyn3rs" );
        sprintf( Command, "&dch%s; &if -y -K 6; %s", fDch ? " -f" : "", pResyn );
        if ( Abc_FrameIsBatchMode() )
        {
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) )
            {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
                return NULL;
            }
        }
        else
        {
            Abc_FrameSetBatchMode( 1 );
            if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) )
            {
                Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
                return NULL;
            }
            Abc_FrameSetBatchMode( 0 );
        }
        pTemp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
        {
            int nLevelTemp = Gia_ManLevelNum(pTemp);
            int nAndsTemp = Gia_ManAndNum(pTemp);
            if ( vPareto )
                Gia_ManDeepSynParetoUpdate( vPareto, pTemp, nLevelTemp, nAndsTemp );
            if ( nLevelsMin > nLevelTemp || (nLevelsMin == nLevelTemp && nAndsMin > nAndsTemp) )
            {
                Gia_ManStop( pNew );
                pNew = Gia_ManDup( pTemp );
                nLevelsMin = nLevelTemp;
                nAndsMin = nAndsTemp;
                fChange = 1;
                if ( vGias ) 
                    Vec_PtrPush( vGias, Gia_ManDup(pTemp) );
                nNoImprCount = 0;
            }
            else
                nNoImprCount++;
        }
        if ( fChange && fVerbose )
        {
            printf( "Iter %6d : ", i );
            printf( "Time %8.2f sec : ", (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC );
            printf( "Lev = %3d  ", nLevelsMin );
            printf( "And = %6d  ", nAndsMin );
            printf( "<== best : " );
            printf( "%s", Command );
            printf( "\n" );
        }
        if ( nTimeToStop && Abc_Clock() > nTimeToStop )
        {
            if ( !Abc_FrameIsBatchMode() )
            printf( "Runtime limit (%d sec) is reached after %d iterations.\n", TimeOut, i );
            break;
        }
        i++;
        if ( nNoImprCount > nNoImpr )
        {
            int nOuter = 1 + (Abc_Random(0) % 3);
            int nKmax = nAnds ? nAnds : 6;
            int nKmin = 3;
            int nLuts[3];
            if ( nKmax < nKmin )
                nKmin = nKmax;
            for ( k = 0; k < nOuter; k++ )
                nLuts[k] = nKmin + (Abc_Random(0) % (nKmax - nKmin + 1));
            if ( fVerbose )
            {
                printf( "Completed %d iterations without improvement. Trying %d outer iterations with ", nNoImpr, nOuter );
                for ( k = 0; k < nOuter; k++ )
                    printf( "%sK=%d", k ? ", " : "", nLuts[k] );
                printf( ". Time = %.2f sec\n", (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC );
            }
            nNoImprCount = 0;
            for ( k = 0; k < nOuter && i < IterMax; k++ )
            {
                int nLut = nLuts[k];
                int fOuterChange = 0;
                sprintf( Command, "&dch; &if -K %d -m; &mfs; &st", nLut );
                if ( Abc_FrameIsBatchMode() )
                {
                    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) )
                    {
                        Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
                        return NULL;
                    }
                }
                else
                {
                    Abc_FrameSetBatchMode( 1 );
                    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) )
                    {
                        Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
                        return NULL;
                    }
                    Abc_FrameSetBatchMode( 0 );
                }
                pTemp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
                {
                    int nLevelTemp = Gia_ManLevelNum(pTemp);
                    int nAndsTemp = Gia_ManAndNum(pTemp);
                    if ( vPareto )
                        Gia_ManDeepSynParetoUpdate( vPareto, pTemp, nLevelTemp, nAndsTemp );
                    if ( nLevelsMin > nLevelTemp || (nLevelsMin == nLevelTemp && nAndsMin > nAndsTemp) )
                    {
                        Gia_ManStop( pNew );
                        pNew = Gia_ManDup( pTemp );
                        nLevelsMin = nLevelTemp;
                        nAndsMin = nAndsTemp;
                        fOuterChange = 1;
                        if ( vGias ) 
                            Vec_PtrPush( vGias, Gia_ManDup(pTemp) );
                    }
                }
                if ( fOuterChange && fVerbose )
                {
                    printf( "Iter %6d : ", i );
                    printf( "Time %8.2f sec : ", (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC );
                    printf( "Lev = %3d  ", nLevelsMin );
                    printf( "And = %6d  ", nAndsMin );
                    printf( "<== best : " );
                    printf( "%s", Command );
                    printf( "\n" );
                }
                if ( nTimeToStop && Abc_Clock() > nTimeToStop )
                {
                    if ( !Abc_FrameIsBatchMode() )
                    printf( "Runtime limit (%d sec) is reached after %d iterations.\n", TimeOut, i );
                    return pNew;
                }
                i++;
            }
        }
    }
    if ( i == IterMax )
        printf( "Iteration limit (%d iters) is reached after %.2f seconds.\n", IterMax, (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDeepSyn2( Gia_Man_t * pGia, int nIters, int nNoImpr, int TimeOut, int nAnds, int Seed, int fUseTwo, int fChoices, int fVerbose )
{
    Vec_Ptr_t * vGias = fChoices ? Vec_PtrAlloc(100) : NULL;
    Vec_Ptr_t * vPareto = fUseTwo ? Vec_PtrStart(100) : NULL;
    char * pParetoBase = NULL;
    Gia_Man_t * pInit;
    Gia_Man_t * pBest;
    Gia_Man_t * pThis;
    int i, nBestLev, nBestAnd;
    if ( !Abc_NtkRecIsRunning3() )
    {
        Abc_Print( -1, "Gia_ManDeepSyn2(): LMS library is not loaded.\n" );
        Abc_Print( -1, "Download \"rec6Lib_final_filtered3_recanon.aig\" and run \"rec_start3 _/rec6Lib_final_filtered3_recanon.aig\".\n" );
        if ( vGias )
            Vec_PtrFree( vGias );
        if ( vPareto )
            Vec_PtrFree( vPareto );
        return Gia_ManDup( pGia );
    }
    if ( vPareto )
    {
        if ( pGia->pSpec && pGia->pSpec[0] )
            pParetoBase = Extra_FileNameGeneric( pGia->pSpec );
        else if ( pGia->pName && pGia->pName[0] )
            pParetoBase = Extra_FileNameGeneric( pGia->pName );
        else
            pParetoBase = Extra_UtilStrsav( "gia" );
    }
    pInit = Gia_ManDup(pGia);
    pBest = Gia_ManDup(pGia);
    nBestLev = Gia_ManLevelNum(pBest);
    nBestAnd = Gia_ManAndNum(pBest);
    if ( vPareto )
        Gia_ManDeepSynParetoUpdate( vPareto, pGia, nBestLev, nBestAnd );
    if ( vGias ) 
        Vec_PtrPush( vGias, Gia_ManDup(pGia) );    
    for ( i = 0; i < nIters; i++ )
    {
        if ( fVerbose )
            printf( "ITER %d (out of %d) running for %d seconds\n", i + 1, nIters, TimeOut );
        int nThisLev, nThisAnd;
        Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), Gia_ManDup(pInit) );
        pThis = Gia_ManDeepSynOne2( nNoImpr, TimeOut, nAnds, Seed+i, fUseTwo, fVerbose, vGias, vPareto );
        nThisLev = Gia_ManLevelNum(pThis);
        nThisAnd = Gia_ManAndNum(pThis);
        if ( nBestLev > nThisLev || (nBestLev == nThisLev && nBestAnd > nThisAnd) )
        {
            Gia_ManStop( pBest );
            pBest = pThis;
            nBestLev = nThisLev;
            nBestAnd = nThisAnd;
        }
        else 
            Gia_ManStop( pThis );
        if ( vPareto )
            Gia_ManDeepSynParetoPrint( vPareto );
    }
    Gia_ManStop( pInit );
    if ( vGias) {
        if ( Vec_PtrSize(vGias) > 1 ) {
            extern Gia_Man_t * Gia_ManCreateChoicesArray( Vec_Ptr_t * vGias, int fVerbose );
            Gia_ManStopP( &pBest );
            pBest = Gia_ManCreateChoicesArray( vGias, fVerbose );
        }
        // cleanup
        Gia_Man_t * pTemp;
        Vec_PtrForEachEntry( Gia_Man_t *, vGias, pTemp, i )
            Gia_ManStop( pTemp );
        Vec_PtrFree( vGias ); 
    }
    if ( vPareto )
    {
        Gia_ManDeepSynParetoSave( vPareto, pParetoBase );
        Gia_Man_t * pTemp;
        Vec_PtrForEachEntry( Gia_Man_t *, vPareto, pTemp, i )
            if ( pTemp )
                Gia_ManStop( pTemp );
        Vec_PtrFree( vPareto );
    }
    return pBest;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
