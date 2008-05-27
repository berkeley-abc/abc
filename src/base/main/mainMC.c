/**CFile****************************************************************

  FileName    [mainMC.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The main package.]

  Synopsis    [The main file for the model checker.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: main.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mainInt.h"
#include "aig.h"
#include "saig.h"
#include "fra.h"
#include "ioa.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [The main() procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int main( int argc, char * argv[] )
{
    Fra_Sec_t SecPar, * pSecPar = &SecPar;
    FILE * pFile;
    Aig_Man_t * pAig;
    int RetValue;
    // BMC parameters
    int nFrames  = 30;
    int nSizeMax = 200000;
    int nBTLimit = 10000;
    int fRewrite = 0;
    int fNewAlgo = 1;
    int fVerbose = 0;

    if ( argc != 2 )
    {
        printf( "  Expecting one command-line argument (an input file in AIGER format).\n" );
        printf( "  usage: %s <file.aig>", argv[0] );
        return 0;
    }
    pFile = fopen( argv[1], "r" );
    if ( pFile == NULL )
    {
        printf( "  Cannot open input AIGER file \"%s\".\n", argv[1] );
        printf( "  usage: %s <file.aig>", argv[0] );
        return 0;
    }
    fclose( pFile );
    pAig = Ioa_ReadAiger( argv[1], 1 );
    if ( pAig == NULL )
    {
        printf( "  Parsing the AIGER file \"%s\" has failed.\n", argv[1] );
        printf( "  usage: %s <file.aig>", argv[0] );
        return 0;
    }

    // perform BMC
    Aig_ManSetRegNum( pAig, pAig->nRegs );
    RetValue = Saig_ManBmcSimple( pAig, nFrames, nSizeMax, nBTLimit, fRewrite, fVerbose, NULL );

    // perform full-blown SEC
    if ( RetValue != 0 )
    {
        extern void Dar_LibStart();
        extern void Dar_LibStop();
        extern void Cnf_ClearMemory();

        Fra_SecSetDefaultParams( pSecPar );
        pSecPar->nFramesMax      =   2;  // the max number of frames used for induction

        Dar_LibStart();
        RetValue = Fra_FraigSec( pAig, pSecPar );
        Dar_LibStop();
        Cnf_ClearMemory();
    }

    // perform BMC again
    if ( RetValue == -1 )
    {
    }

    // decide how to report the output
    pFile = stdout;

    // report the result
    if ( RetValue == 0 ) 
    {
//        fprintf(stdout, "s SATIFIABLE\n");
        Fra_SmlWriteCounterExample( pFile, pAig, pAig->pSeqModel );
        if ( pFile != stdout )
            fclose(pFile);
        Aig_ManStop( pAig );
        exit(10);
    } 
    else if ( RetValue == 1 ) 
    {
//    fprintf(stdout, "s UNSATISFIABLE\n");
        fprintf( pFile, "0\n" );
        if ( pFile != stdout )
            fclose(pFile);
        Aig_ManStop( pAig );
        exit(20);
    } 
    else // if ( RetValue == -1 ) 
    {
//    fprintf(stdout, "s UNKNOWN\n");
        if ( pFile != stdout )
            fclose(pFile);
        Aig_ManStop( pAig );
        exit(0);
    }
    return 0;
}




////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


