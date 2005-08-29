/**CFile****************************************************************

  FileName    [ioWriteBench.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write the network in BENCH format.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteBench.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int    Io_WriteBenchOne( FILE * pFile, Abc_Ntk_t * pNtk );
static int    Io_WriteBenchOneNode( FILE * pFile, Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writes the network in BENCH format.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteBench( Abc_Ntk_t * pNtk, char * pFileName )
{
    Abc_Ntk_t * pExdc;
    FILE * pFile;
    assert( Abc_NtkIsSopNetlist(pNtk) );
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteBench(): Cannot open the output file.\n" );
        return 0;
    }
    fprintf( pFile, "# Benchmark \"%s\" written by ABC on %s\n", pNtk->pName, Extra_TimeStamp() );
    // write the network
    Io_WriteBenchOne( pFile, pNtk );
    // write EXDC network if it exists
    pExdc = Abc_NtkExdc( pNtk );
    if ( pExdc )
        printf( "Io_WriteBench: EXDC is not written (warning).\n" );
    // finalize the file
    fclose( pFile );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Writes the network in BENCH format.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteBenchOne( FILE * pFile, Abc_Ntk_t * pNtk )
{
    ProgressBar * pProgress;
    Abc_Obj_t * pNode;
    int i;

    // write the PIs/POs/latches
    Abc_NtkForEachPi( pNtk, pNode, i )
        fprintf( pFile, "INPUT(%s)\n", Abc_ObjName(Abc_ObjFanout0(pNode)) );
    Abc_NtkForEachPo( pNtk, pNode, i )
        fprintf( pFile, "OUTPUT(%s)\n", Abc_ObjName(Abc_ObjFanin0(pNode)) );
    Abc_NtkForEachLatch( pNtk, pNode, i )
        fprintf( pFile, "%-11s = DFF(%s)\n", 
            Abc_ObjName(pNode), Abc_ObjName(Abc_ObjFanin0(pNode)) );

    // write internal nodes
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        Io_WriteBenchOneNode( pFile, pNode );
    }
    Extra_ProgressBarStop( pProgress );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Writes the network in BENCH format.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_WriteBenchOneNode( FILE * pFile, Abc_Obj_t * pNode )
{
    int nFanins;

    assert( Abc_ObjIsNode(pNode) );
    nFanins = Abc_ObjFaninNum(pNode);
    if ( nFanins == 0 )
    {   // write the constant 1 node
        assert( Abc_NodeIsConst1(pNode) );
        fprintf( pFile, "%-11s",          Abc_ObjName(Abc_ObjFanout0(pNode)) );
        fprintf( pFile, " = vdd\n" );
    }
    else if ( nFanins == 1 )
    {   // write the interver/buffer
        if ( Abc_NodeIsBuf(pNode) )
        {
            fprintf( pFile, "%-11s = BUFF(",  Abc_ObjName(Abc_ObjFanout0(pNode)) );
            fprintf( pFile, "%s)\n",          Abc_ObjName(Abc_ObjFanin0(pNode)) );
        }
        else
        {
            fprintf( pFile, "%-11s = NOT(",   Abc_ObjName(Abc_ObjFanout0(pNode)) );
            fprintf( pFile, "%s)\n",          Abc_ObjName(Abc_ObjFanin0(pNode)) );
        }
    }
    else
    {   // write the AND gate
        fprintf( pFile, "%-11s",       Abc_ObjName(Abc_ObjFanout0(pNode)) );
        fprintf( pFile, " = AND(%s, ", Abc_ObjName(Abc_ObjFanin0(pNode)) );
        fprintf( pFile, "%s)\n",       Abc_ObjName(Abc_ObjFanin1(pNode)) );
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


