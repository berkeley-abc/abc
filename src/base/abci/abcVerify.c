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
 
static int * Abc_NtkVerifyGetCleanModel( Abc_Ntk_t * pNtk );
static int * Abc_NtkVerifySimulatePattern( Abc_Ntk_t * pNtk, int * pModel );
static void  Abc_NtkVerifyReportError( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int * pModel );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Verifies combinational equivalence by brute-force SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds )
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
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter );
        Abc_NtkVerifyReportError( pNtk1, pNtk2, pMiter->pModel );
        FREE( pMiter->pModel );
        return;
    }
    if ( RetValue == 1 )
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
    RetValue = Abc_NtkMiterSat( pCnf, nSeconds, 0 );
    if ( RetValue == -1 )
        printf( "Networks are undecided (SAT solver timed out).\n" );
    else if ( RetValue == 0 )
        printf( "Networks are NOT EQUIVALENT after SAT.\n" );
    else
        printf( "Networks are equivalent after SAT.\n" );
    if ( pCnf->pModel )
        Abc_NtkVerifyReportError( pNtk1, pNtk2, pCnf->pModel );
    FREE( pCnf->pModel );
    Abc_NtkDelete( pCnf );
}


/**Function*************************************************************

  Synopsis    [Verifies sequential equivalence by fraiging followed by SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose )
{
    Fraig_Params_t Params;
    Fraig_Man_t * pMan;
    Abc_Ntk_t * pMiter;
    int RetValue;

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 1 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter );
        Abc_NtkVerifyReportError( pNtk1, pNtk2, pMiter->pModel );
        FREE( pMiter->pModel );
        return;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return;
    }

    // convert the miter into a FRAIG
    Fraig_ParamsSetDefault( &Params );
    Params.fVerbose = fVerbose;
    Params.nSeconds = nSeconds;
    pMan = Abc_NtkToFraig( pMiter, &Params, 0 ); 
    Fraig_ManProveMiter( pMan );

    // analyze the result
    RetValue = Fraig_ManCheckMiter( pMan );
    // report the result
    if ( RetValue == -1 )
        printf( "Networks are undecided (SAT solver timed out on the final miter).\n" );
    else if ( RetValue == 1 )
        printf( "Networks are equivalent after fraiging.\n" );
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT after fraiging.\n" );
        Abc_NtkVerifyReportError( pNtk1, pNtk2, Fraig_ManReadModel(pMan) );
    }
    else assert( 0 );
    // delete the fraig manager
    Fraig_ManFree( pMan );
    // delete the miter
    Abc_NtkDelete( pMiter );
}

/**Function*************************************************************

  Synopsis    [Verifies sequential equivalence by brute-force SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nFrames )
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
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        return;
    }
    if ( RetValue == 1 )
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
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are NOT EQUIVALENT after framing.\n" );
        return;
    }
    if ( RetValue == 1 )
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
    RetValue = Abc_NtkMiterSat( pCnf, nSeconds, 0 );
    if ( RetValue == -1 )
        printf( "Networks are undecided (SAT solver timed out).\n" );
    else if ( RetValue == 0 )
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
void Abc_NtkSecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nFrames, int fVerbose )
{
    Fraig_Params_t Params;
    Fraig_Man_t * pMan;
    Abc_Ntk_t * pMiter;
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
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        return;
    }
    if ( RetValue == 1 )
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
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are NOT EQUIVALENT after framing.\n" );
        return;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are equivalent after framing.\n" );
        return;
    }

    // convert the miter into a FRAIG
    Fraig_ParamsSetDefault( &Params );
    Params.fVerbose = fVerbose;
    Params.nSeconds = nSeconds;
    pMan = Abc_NtkToFraig( pFrames, &Params, 0 ); 
    Fraig_ManProveMiter( pMan );

    // analyze the result
    RetValue = Fraig_ManCheckMiter( pMan );
    // report the result
    if ( RetValue == -1 )
        printf( "Networks are undecided (SAT solver timed out on the final miter).\n" );
    else if ( RetValue == 1 )
        printf( "Networks are equivalent after fraiging.\n" );
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT after fraiging.\n" );
//        Abc_NtkVerifyReportError( pNtk1, pNtk2, Fraig_ManReadModel(pMan) );
    }
    else assert( 0 );
    // delete the fraig manager
    Fraig_ManFree( pMan );
    // delete the miter
    Abc_NtkDelete( pFrames );
}

/**Function*************************************************************

  Synopsis    [Reports mismatch between the two networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkVerifyReportError( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int * pModel )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int * pValues1, * pValues2;
    int nMisses, nPrinted, i, iNode = -1;

    assert( Abc_NtkCiNum(pNtk1) == Abc_NtkCiNum(pNtk2) );
    assert( Abc_NtkCoNum(pNtk1) == Abc_NtkCoNum(pNtk2) );
    // get the CO values under this model
    pValues1 = Abc_NtkVerifySimulatePattern( pNtk1, pModel );
    pValues2 = Abc_NtkVerifySimulatePattern( pNtk2, pModel );
    // count the mismatches
    nMisses = 0;
    for ( i = 0; i < Abc_NtkCoNum(pNtk1); i++ )
        nMisses += (int)( pValues1[i] != pValues2[i] );
    printf( "Verification failed for %d outputs: ", nMisses );
    // print the first 3 outputs
    nPrinted = 0;
    for ( i = 0; i < Abc_NtkCoNum(pNtk1); i++ )
        if ( pValues1[i] != pValues2[i] )
        {
            if ( iNode == -1 )
                iNode = i;
            printf( " %s", Abc_ObjName(Abc_NtkCo(pNtk1,i)) );
            if ( ++nPrinted == 3 )
                break;
        }
    if ( nPrinted != nMisses )
        printf( " ..." );
    printf( "\n" );
    // report mismatch for the first output
    if ( iNode >= 0 )
    {
        printf( "Output %s: Value in Network1 = %d. Value in Network2 = %d.\n", 
            Abc_ObjName(Abc_NtkCo(pNtk1,iNode)), pValues1[iNode], pValues2[iNode] );
        printf( "Input pattern: " );
        // collect PIs in the cone
        pNode = Abc_NtkCo(pNtk1,iNode);
        vNodes = Abc_NtkNodeSupport( pNtk1, &pNode, 1 );
        // set the PI numbers
        Abc_NtkForEachCi( pNtk1, pNode, i )
            pNode->pCopy = (void*)i;
        // print the model
        Vec_PtrForEachEntry( vNodes, pNode, i )
        {
            assert( Abc_ObjIsCi(pNode) );
            printf( " %s=%d", Abc_ObjName(pNode), pModel[(int)pNode->pCopy] );
        }
        printf( "\n" );
        Vec_PtrFree( vNodes );
    }
    free( pValues1 );
    free( pValues2 );
}

/**Function*************************************************************

  Synopsis    [Returns a dummy pattern full of zeros.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Abc_NtkVerifyGetCleanModel( Abc_Ntk_t * pNtk )
{
    int * pModel = ALLOC( int, Abc_NtkCiNum(pNtk) );
    memset( pModel, 0, sizeof(int) * Abc_NtkCiNum(pNtk) );
    return pModel;
}

/**Function*************************************************************

  Synopsis    [Returns the PO values under the given input pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Abc_NtkVerifySimulatePattern( Abc_Ntk_t * pNtk, int * pModel )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int * pValues, Value0, Value1, i;
    int fStrashed = 0;
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash(pNtk, 0, 0);
        fStrashed = 1;
    }
    // increment the trav ID
    Abc_NtkIncrementTravId( pNtk );
    // set the CI values
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->pCopy = (void *)pModel[i];
    // simulate in the topological order
    vNodes = Abc_NtkDfs( pNtk, 1 );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        if ( Abc_NodeIsConst(pNode) )
            pNode->pCopy = NULL;
        else
        {
            Value0 = ((int)Abc_ObjFanin0(pNode)->pCopy) ^ Abc_ObjFaninC0(pNode);
            Value1 = ((int)Abc_ObjFanin1(pNode)->pCopy) ^ Abc_ObjFaninC1(pNode);
            pNode->pCopy = (void *)(Value0 & Value1);
        }
    }
    Vec_PtrFree( vNodes );
    // fill the output values
    pValues = ALLOC( int, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
        pValues[i] = ((int)Abc_ObjFanin0(pNode)->pCopy) ^ Abc_ObjFaninC0(pNode);
    if ( fStrashed )
        Abc_NtkDelete( pNtk );
    return pValues;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


