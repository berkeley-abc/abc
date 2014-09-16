/**CFile****************************************************************

  FileName    [giaScript.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Various hardcoded scripts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaScript.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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

  Synopsis    [Synthesis script.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManAigPrintPiLevels( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachPi( p, pObj, i )
        printf( "%d ", Gia_ObjLevel(p, pObj) );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Synthesis script.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManAigSyn2( Gia_Man_t * pInit, int fOldAlgo, int fCoarsen, int fCutMin, int nRelaxRatio, int fDelayMin, int fVerbose, int fVeryVerbose )
{
    Gia_Man_t * p, * pNew, * pTemp;
    Jf_Par_t Pars, * pPars = &Pars;
    if ( fOldAlgo )
    {
        Jf_ManSetDefaultPars( pPars );
        pPars->fCutMin     = fCutMin;
    }
    else
    {
        Lf_ManSetDefaultPars( pPars );
        pPars->fCutMin     = fCutMin;
        pPars->fCoarsen    = fCoarsen;
        pPars->nRelaxRatio = nRelaxRatio;
        pPars->nAreaTuner  = 1;
        pPars->nCutNum     = 4;
    }
    if ( fVerbose )  Gia_ManPrintStats( pInit, NULL );
    p = Gia_ManDup( pInit );
    Gia_ManTransferTiming( p, pInit );
    if ( Gia_ManAndNum(p) == 0 )
        return p;
    // delay optimization
    if ( fDelayMin && p->pManTime == NULL )
    {
        int Area0, Area1, Delay0, Delay1;
        int fCutMin = pPars->fCutMin;
        int fCoarsen = pPars->fCoarsen;
        int nRelaxRatio = pPars->nRelaxRatio;
        pPars->fCutMin = 0;
        pPars->fCoarsen = 0;
        pPars->nRelaxRatio = 0;
        // perform mapping
        if ( fOldAlgo )
            Jf_ManPerformMapping( p, pPars );
        else
            Lf_ManPerformMapping( p, pPars );
        Area0  = (int)pPars->Area;
        Delay0 = (int)pPars->Delay;
        // perform balancing
        pNew = Gia_ManPerformDsdBalance( p, 6, 4, 0, 0 );
        // perform mapping again
        if ( fOldAlgo )
            Jf_ManPerformMapping( pNew, pPars );
        else
            Lf_ManPerformMapping( pNew, pPars );
        Area1  = (int)pPars->Area;
        Delay1 = (int)pPars->Delay;
        // choose the best result
        if ( Delay1 < Delay0 - 1 || (Delay1 == Delay0 + 1 && 100.0 * (Area1 - Area0) / Area1 < 3.0) )
        {
            Gia_ManStop( p );
            p = pNew;
        }
        else
        {
            Gia_ManStop( pNew );
            Vec_IntFreeP( &p->vMapping );
        }
        // reset params
        pPars->fCutMin = fCutMin;
        pPars->fCoarsen = fCoarsen;
        pPars->nRelaxRatio = nRelaxRatio;
    }
    // perform balancing
    pNew = Gia_ManAreaBalance( p, 0, ABC_INFINITY, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    Gia_ManStop( p );
    // perform mapping
    if ( fOldAlgo )
        pNew = Jf_ManPerformMapping( pTemp = pNew, pPars );
    else
        pNew = Lf_ManPerformMapping( pTemp = pNew, pPars );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    if ( pTemp != pNew )
        Gia_ManStop( pTemp );
    // perform balancing
    pNew = Gia_ManAreaBalance( pTemp = pNew, 0, ABC_INFINITY, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    Gia_ManStop( pTemp );
    return pNew;
}
Gia_Man_t * Gia_ManAigSyn3( Gia_Man_t * p, int fVerbose, int fVeryVerbose )
{
    Gia_Man_t * pNew, * pTemp;
    Jf_Par_t Pars, * pPars = &Pars;
    Jf_ManSetDefaultPars( pPars );
    pPars->nRelaxRatio = 40;
    if ( fVerbose )     Gia_ManPrintStats( p, NULL );
    if ( Gia_ManAndNum(p) == 0 )
        return Gia_ManDup(p);
    // perform balancing
    pNew = Gia_ManAreaBalance( p, 0, ABC_INFINITY, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    // perform mapping
    pPars->nLutSize = 6;
    pNew = Jf_ManPerformMapping( pTemp = pNew, pPars );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
//    Gia_ManStop( pTemp );
    // perform balancing
    pNew = Gia_ManAreaBalance( pTemp = pNew, 0, ABC_INFINITY, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    Gia_ManStop( pTemp );
    // perform mapping
    pPars->nLutSize = 4;
    pNew = Jf_ManPerformMapping( pTemp = pNew, pPars );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
//    Gia_ManStop( pTemp );
    // perform balancing
    pNew = Gia_ManAreaBalance( pTemp = pNew, 0, ABC_INFINITY, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    Gia_ManStop( pTemp );
    return pNew;
}
Gia_Man_t * Gia_ManAigSyn4( Gia_Man_t * p, int fVerbose, int fVeryVerbose )
{
    Gia_Man_t * pNew, * pTemp;
    Jf_Par_t Pars, * pPars = &Pars;
    Jf_ManSetDefaultPars( pPars );
    pPars->nRelaxRatio = 40;
    if ( fVerbose )     Gia_ManPrintStats( p, NULL );
    if ( Gia_ManAndNum(p) == 0 )
        return Gia_ManDup(p);
//Gia_ManAigPrintPiLevels( p );
    // perform balancing
    pNew = Gia_ManAreaBalance( p, 0, ABC_INFINITY, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    // perform mapping
    pPars->nLutSize = 7;
    pNew = Jf_ManPerformMapping( pTemp = pNew, pPars );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
//    Gia_ManStop( pTemp );
    // perform extraction
    pNew = Gia_ManPerformFx( pTemp = pNew, ABC_INFINITY, 0, 0, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    Gia_ManStop( pTemp );
    // perform balancing
    pNew = Gia_ManAreaBalance( pTemp = pNew, 0, ABC_INFINITY, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    Gia_ManStop( pTemp );
    // perform mapping
    pPars->nLutSize = 5;
    pNew = Jf_ManPerformMapping( pTemp = pNew, pPars );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
//    Gia_ManStop( pTemp );
    // perform extraction
    pNew = Gia_ManPerformFx( pTemp = pNew, ABC_INFINITY, 0, 0, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    Gia_ManStop( pTemp );
    // perform balancing
    pNew = Gia_ManAreaBalance( pTemp = pNew, 0, ABC_INFINITY, fVeryVerbose, 0 );
    if ( fVerbose )     Gia_ManPrintStats( pNew, NULL );
    Gia_ManStop( pTemp );
//Gia_ManAigPrintPiLevels( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPerformMap( int nAnds, int nLutSize, int nCutNum, int fVerbose )
{
    char Command[200];
    sprintf( Command, "&unmap; &lf -K %d -C %d -k; &save", nLutSize, nCutNum );
    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), Command );
    if ( fVerbose )
    {
        printf( "MAPPING:\n" );
        printf( "Mapping with &lf -k:\n" );
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&ps" );
    }
    sprintf( Command, "&unmap; &lf -K %d -C %d; &save", nLutSize, nCutNum );
    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), Command );
    if ( fVerbose )
    {
        printf( "Mapping with &lf:\n" );
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&ps" );
    }
    if ( (nLutSize == 4 && nAnds < 100000) || (nLutSize == 6 && nAnds < 2000) )
    {
        sprintf( Command, "&unmap; &if -sz -S %d%d -K %d -C %d", nLutSize, nLutSize, 2*nLutSize-1, 2*nCutNum );
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), Command );
        Vec_IntFreeP( &Abc_FrameReadGia(Abc_FrameGetGlobalFrame())->vPacking );
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&save" );
        if ( fVerbose )
        {
            printf( "Mapping with &if -sz -S %d%d -K %d -C %d:\n", nLutSize, nLutSize, 2*nLutSize-1, 2*nCutNum );
            Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&ps" );
        }
    }
    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&load" );
    if ( fVerbose )
    {
        printf( "Mapping final:\n" );
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&ps" );
    }
}
void Gia_ManPerformRound( int fIsMapped, int nAnds, int nLevels, int nLutSize, int nCutNum, int nRelaxRatio, int fVerbose )
{
    char Command[200];

    // perform AIG-based synthesis
    if ( nAnds < 50000 )
    {
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "" );
        sprintf( Command, "&dsdb; &dch -f; &if -K %d -C %d; &save", nLutSize, nCutNum );
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), Command );
        if ( fVerbose )
        {
            printf( "Mapping with &dch -f; &if -K %d -C %d:\n", nLutSize, nCutNum );
            Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&ps" );
        }
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&st" );
    }

    // perform AIG-based synthesis
    if ( nAnds < 20000 )
    {
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "" );
        sprintf( Command, "&dsdb; &dch -f; &if -K %d -C %d; &save", nLutSize, nCutNum );
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), Command );
        if ( fVerbose )
        {
            printf( "Mapping with &dch -f; &if -K %d -C %d:\n", nLutSize, nCutNum );
            Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&ps" );
        }
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&st" );
    }

    // perform first round of mapping
    Gia_ManPerformMap( nAnds, nLutSize, nCutNum, fVerbose );
    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&st" );

    // perform synthesis
    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&dsdb" );

    // perform second round of mapping
    Gia_ManPerformMap( nAnds, nLutSize, nCutNum, fVerbose );
    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&st" );

    // perform synthesis
    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&syn2 -m -R 10; &dsdb" );

    // prepare for final mapping
    sprintf( Command, "&blut -a -K %d", nLutSize );
    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), Command );

    // perform third round of mapping
    Gia_ManPerformMap( nAnds, nLutSize, nCutNum, fVerbose );
}
void Gia_ManPerformFlow( int fIsMapped, int nAnds, int nLevels, int nLutSize, int nCutNum, int nRelaxRatio, int fVerbose )
{
    // remove comb equivs
    if ( fIsMapped )
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&st" );
    if ( Abc_FrameReadGia(Abc_FrameGetGlobalFrame())->pManTime )
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&sweep" );
    else
        Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&fraig -c" );

    // perform first round
    Gia_ManPerformRound( fIsMapped, nAnds, nLevels, nLutSize, nCutNum, nRelaxRatio, fVerbose );

    // perform synthesis
    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "&st; &sopb" );

    // perform first round
    Gia_ManPerformRound( fIsMapped, nAnds, nLevels, nLutSize, nCutNum, nRelaxRatio, fVerbose );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManAigSynch2( Gia_Man_t * p, int fVerbose )
{
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

