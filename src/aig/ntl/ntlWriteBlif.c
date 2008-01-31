/**CFile****************************************************************

  FileName    [ntlWriteBlif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write BLIF files.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlWriteBlif.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"
#include "ioa.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writes one model into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ioa_WriteBlifModel( FILE * pFile, Ntl_Mod_t * pModel )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i, k;
    fprintf( pFile, ".model %s\n", pModel->pName );
    fprintf( pFile, ".inputs" );
    Ntl_ModelForEachPi( pModel, pObj, i )
        fprintf( pFile, " %s", Ntl_ObjFanout0(pObj)->pName );
    fprintf( pFile, "\n" );
    fprintf( pFile, ".outputs" );
    Ntl_ModelForEachPo( pModel, pObj, i )
        fprintf( pFile, " %s", Ntl_ObjFanin0(pObj)->pName );
    fprintf( pFile, "\n" );
    Ntl_ModelForEachObj( pModel, pObj, i )
    {
        if ( Ntl_ObjIsNode(pObj) )
        {
            fprintf( pFile, ".names" );
            Ntl_ObjForEachFanin( pObj, pNet, k )
                fprintf( pFile, " %s", pNet->pName );
            fprintf( pFile, " %s\n", Ntl_ObjFanout0(pObj)->pName );
            fprintf( pFile, "%s", pObj->pSop );
        }
        else if ( Ntl_ObjIsLatch(pObj) )
        {
            fprintf( pFile, ".latch" );
            fprintf( pFile, " %s", Ntl_ObjFanin0(pObj)->pName );
            fprintf( pFile, " %s", Ntl_ObjFanout0(pObj)->pName );
            if ( pObj->LatchId >> 2 )
                fprintf( pFile, " %d", pObj->LatchId >> 2 );
            if ( pObj->pFanio[1] != NULL )
                fprintf( pFile, " %s", Ntl_ObjFanin(pObj, 1)->pName );
            fprintf( pFile, " %d", pObj->LatchId & 3 );
            fprintf( pFile, "\n" );
        }
        else if ( Ntl_ObjIsBox(pObj) )
        {
            fprintf( pFile, ".subckt %s", pObj->pImplem->pName );
            Ntl_ObjForEachFanin( pObj, pNet, k )
                fprintf( pFile, " %s=%s", Ntl_ModelPiName(pObj->pImplem, k), pNet->pName );
            Ntl_ObjForEachFanout( pObj, pNet, k )
                fprintf( pFile, " %s=%s", Ntl_ModelPoName(pObj->pImplem, k), pNet->pName );
            fprintf( pFile, "\n" );
        }
    }
    fprintf( pFile, ".end\n\n" );
}

/**Function*************************************************************

  Synopsis    [Writes the network into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ioa_WriteBlif( Ntl_Man_t * p, char * pFileName )
{
    FILE * pFile;
    Ntl_Mod_t * pModel;
    int i;
    // start the output stream
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Ioa_WriteBlif(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "# Benchmark \"%s\" written by ABC-8 on %s\n", p->pName, Ioa_TimeStamp() );
    // write the models
    Ntl_ManForEachModel( p, pModel, i )
        Ioa_WriteBlifModel( pFile, pModel );
    // close the file
    fclose( pFile );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


