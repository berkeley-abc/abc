/**CFile****************************************************************

  FileName    [abcVerify.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Combinational and sequential verification for two networks.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcVerify.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "fraig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Verifies combinational equivalence by brute-force SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 )
{
    Abc_Ntk_t * pMiter;
    Abc_Ntk_t * pCnf;
    int RetValue;

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 1 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        return;
    }
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return;
    }

    // convert the miter into a CNF
    pCnf = Abc_NtkRenode( pMiter, 0, 100, 1, 0, 0 );
    Abc_NtkDelete( pMiter );
    if ( pCnf == NULL )
    {
        printf( "Renoding for CNF has failed.\n" );
        return;
    }

    // solve the CNF using the SAT solver
    if ( Abc_NtkMiterSat( pCnf, 0 ) )
        printf( "Networks are NOT EQUIVALENT after SAT.\n" );
    else
        printf( "Networks are equivalent after SAT.\n" );
    Abc_NtkDelete( pCnf );
}


/**Function*************************************************************

  Synopsis    [Verifies sequential equivalence by fraiging followed by SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fVerbose )
{
    Fraig_Params_t Params;
    Abc_Ntk_t * pMiter;
    Abc_Ntk_t * pFraig;
    int RetValue;

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 1 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        return;
    }
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return;
    }

    // convert the miter into a FRAIG
    Fraig_ParamsSetDefault( &Params );
    Params.fVerbose = fVerbose;
    pFraig = Abc_NtkFraig( pMiter, &Params, 0 );
    Abc_NtkDelete( pMiter );
    if ( pFraig == NULL )
    {
        printf( "Fraiging has failed.\n" );
        return;
    }
    RetValue = Abc_NtkMiterIsConstant( pFraig );
    Abc_NtkDelete( pFraig );
    if ( RetValue == 0 )
    {
        printf( "Networks are equivalent after fraiging.\n" );
        return;
    }
    printf( "Networks are NOT EQUIVALENT after fraiging.\n" );
}

/**Function*************************************************************

  Synopsis    [Verifies sequential equivalence by brute-force SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames )
{
    Abc_Ntk_t * pMiter;
    Abc_Ntk_t * pFrames;
    Abc_Ntk_t * pCnf;
    int RetValue;

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 0 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        return;
    }
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return;
    }

    // create the timeframes
    pFrames = Abc_NtkFrames( pMiter, nFrames, 1 );
    Abc_NtkDelete( pMiter );
    if ( pFrames == NULL )
    {
        printf( "Frames computation has failed.\n" );
        return;
    }
    RetValue = Abc_NtkMiterIsConstant( pFrames );
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are NOT EQUIVALENT after framing.\n" );
        return;
    }
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are equivalent after framing.\n" );
        return;
    }

    // convert the miter into a CNF
    pCnf = Abc_NtkRenode( pFrames, 0, 100, 1, 0, 0 );
    Abc_NtkDelete( pFrames );
    if ( pCnf == NULL )
    {
        printf( "Renoding for CNF has failed.\n" );
        return;
    }

    // solve the CNF using the SAT solver
    if ( Abc_NtkMiterSat( pCnf, 0 ) )
        printf( "Networks are NOT EQUIVALENT after SAT.\n" );
    else
        printf( "Networks are equivalent after SAT.\n" );
    Abc_NtkDelete( pCnf );
}

/**Function*************************************************************

  Synopsis    [Verifies combinational equivalence by fraiging followed by SAT]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames )
{
    Fraig_Params_t Params;
    Abc_Ntk_t * pMiter;
    Abc_Ntk_t * pFraig;
    Abc_Ntk_t * pFrames;
    int RetValue;

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 0 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        return;
    }
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return;
    }

    // create the timeframes
    pFrames = Abc_NtkFrames( pMiter, nFrames, 1 );
    Abc_NtkDelete( pMiter );
    if ( pFrames == NULL )
    {
        printf( "Frames computation has failed.\n" );
        return;
    }
    RetValue = Abc_NtkMiterIsConstant( pFrames );
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are NOT EQUIVALENT after framing.\n" );
        return;
    }
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are equivalent after framing.\n" );
        return;
    }

    // convert the miter into a FRAIG
    Fraig_ParamsSetDefault( &Params );
    pFraig = Abc_NtkFraig( pFrames, &Params, 0 );
    Abc_NtkDelete( pFrames );
    if ( pFraig == NULL )
    {
        printf( "Fraiging has failed.\n" );
        return;
    }
    RetValue = Abc_NtkMiterIsConstant( pFraig );
    Abc_NtkDelete( pFraig );
    if ( RetValue == 0 )
    {
        printf( "Networks are equivalent after fraiging.\n" );
        return;
    }
    printf( "Networks are NOT EQUIVALENT after fraiging.\n" );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


