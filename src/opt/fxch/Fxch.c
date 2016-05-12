/**CFile****************************************************************

  FileName    [ Fxch.c ]

  PackageName [ Fast eXtract with Cube Hashing (FXCH) ]

  Synopsis    [ The entrance into the fast extract module. ]

  Author      [ Bruno Schmitt - boschmitt at inf.ufrgs.br ]

  Affiliation [ UFRGS ]

  Date        [ Ver. 1.0. Started - March 6, 2016. ]

  Revision    []

***********************************************************************/

#include "Fxch.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [ Performs fast extract with cube hashing on a set
                of covers. ]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fxch_FastExtract( Vec_Wec_t* vCubes,
                      int ObjIdMax,
                      int nMaxDivExt,
                      int SMode, 
                      int fVerbose,
                      int fVeryVerbose )
{
    abctime TempTime;
    Fxch_Man_t* pFxchMan = Fxch_ManAlloc( vCubes, SMode );

    TempTime = Abc_Clock();
    Fxch_ManMapLiteralsIntoCubes( pFxchMan, ObjIdMax );
    Fxch_ManGenerateLitHashKeys( pFxchMan );
    Fxch_ManComputeLevel( pFxchMan );
    Fxch_ManSCHashTablesInit( pFxchMan );
    Fxch_ManDivCreate( pFxchMan );
    pFxchMan->timeInit = Abc_Clock() - TempTime;

    if ( fVeryVerbose )
        Fxch_ManPrintDivs( pFxchMan );

    if ( fVerbose )
        Fxch_ManPrintStats( pFxchMan );

    TempTime = Abc_Clock();
    for ( int i = 0; i < nMaxDivExt && Vec_QueTopPriority( pFxchMan->vDivPrio ) > 0.0; i++ )
    {
        int iDiv = Vec_QuePop( pFxchMan->vDivPrio );

        if ( fVeryVerbose )
            Fxch_DivPrint( pFxchMan, iDiv );

        Fxch_ManUpdate( pFxchMan, iDiv );
    }
    pFxchMan->timeExt = Abc_Clock() - TempTime;

    if ( fVerbose )
    {
        Fxch_ManPrintStats( pFxchMan );
        Abc_PrintTime( 1, "\n[FXCH] Elapsed Time", pFxchMan->timeInit + pFxchMan->timeExt );
        Abc_PrintTime( 1, "[FXCH]    +-> Init", pFxchMan->timeInit );
        Abc_PrintTime( 1, "[FXCH]    +-> Extr", pFxchMan->timeExt );
    }

    Fxch_ManSCHashTablesFree( pFxchMan );
    Fxch_ManFree( pFxchMan );
    Vec_WecRemoveEmpty( vCubes );

    return 1;
}

/**Function*************************************************************

  Synopsis    [ Retrives the necessary information for the fast extract
                with cube hashing. ]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkFxchPerform( Abc_Ntk_t* pNtk,
                        int nMaxDivExt,
                        int SMode,
                        int fVerbose,
                        int fVeryVerbose )
{
    Vec_Wec_t* vCubes;

    assert( Abc_NtkIsSopLogic( pNtk ) );

    if ( !Abc_NtkFxCheck( pNtk ) )
    {
        printf( "Abc_NtkFxchPerform(): Nodes have duplicated fanins. FXCH is not performed.\n" );
        return 0;
    }

    vCubes = Abc_NtkFxRetrieve( pNtk );
    if ( Fxch_FastExtract( vCubes, Abc_NtkObjNumMax( pNtk ), nMaxDivExt, SMode, fVerbose, fVeryVerbose ) > 0 )
    {
        Abc_NtkFxInsert( pNtk, vCubes );
        Vec_WecFree( vCubes );

        if ( !Abc_NtkCheck( pNtk ) )
            printf( "Abc_NtkFxchPerform(): The network check has failed.\n" );

        return 1;
    }
    else
        printf( "Warning: The network has not been changed by \"fxch\".\n" );

    Vec_WecFree( vCubes );

    return 0;
}
////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
