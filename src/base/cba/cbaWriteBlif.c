/**CFile****************************************************************

  FileName    [cbaWriteBlif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaWriteVer.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "cbaPrs.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writing parser state into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_PrsWriteBlifArray( FILE * pFile, Cba_Ntk_t * p, Vec_Int_t * vFanins, int fFirst )
{
    int NameId, i;
    Vec_IntForEachEntryStart( vFanins, NameId, i, fFirst )
        fprintf( pFile, " %s", Cba_NtkStr(p, NameId) );
    if ( fFirst )
        fprintf( pFile, " %s", Cba_NtkStr(p, Vec_IntEntry(vFanins,0)) );
    fprintf( pFile, "\n" );
}
void Cba_PrsWriteBlifArray2( FILE * pFile, Cba_Ntk_t * p, Vec_Int_t * vFanins )
{
    int FormId, NameId, i;
    assert( Vec_IntSize(vFanins) % 2 == 0 );
    Vec_IntForEachEntryDouble( vFanins, FormId, NameId, i )
        fprintf( pFile, " %s=%s", Cba_NtkStr(p, FormId), Cba_NtkStr(p, NameId) );
    fprintf( pFile, "\n" );
}
void Cba_PrsWriteBlifLines( FILE * pFile, Cba_Ntk_t * p )
{
    Vec_Int_t * vFanins;
    int Type, Func, i;
    Cba_NtkForEachObjTypeFuncFanins( p, Type, Func, vFanins, i )
        if ( Type == CBA_PRS_NODE ) // .names/assign/box2 (no formal/actual binding)
        {
            fprintf( pFile, ".names" );
            Cba_PrsWriteBlifArray( pFile, p, vFanins, 1 );
            fprintf( pFile, "%s", Cba_NtkFuncStr(p,  Func) );
        }
        else if ( Type == CBA_PRS_BOX ) // .names/assign/box2 (no formal/actual binding)
        {
            fprintf( pFile, ".subckt" );
            fprintf( pFile, " %s", Cba_NtkStr(p,  Func) );
            Cba_PrsWriteBlifArray2( pFile, p, vFanins );
        }
        else if ( Type == CBA_PRS_LATCH ) // .names/assign/box2 (no formal/actual binding)
        {
            fprintf( pFile, ".latch" );
            fprintf( pFile, " %s", Cba_NtkStr(p,  Vec_IntEntry(vFanins, 1)) );
            fprintf( pFile, " %s", Cba_NtkStr(p,  Vec_IntEntry(vFanins, 0)) );
            fprintf( pFile, " %c\n", '0' + Func );
        }
}
void Cba_PrsWriteBlifNtk( FILE * pFile, Cba_Ntk_t * p )
{
    assert( Vec_IntSize(&p->vTypes)   == Cba_NtkObjNum(p) );
    assert( Vec_IntSize(&p->vFuncs)   == Cba_NtkObjNum(p) );
    // write header
    fprintf( pFile, ".model %s\n", Cba_NtkName(p) );
    if ( Vec_IntSize(&p->vInouts) )
    fprintf( pFile, ".inouts" );
    if ( Vec_IntSize(&p->vInouts) )
    Cba_PrsWriteBlifArray( pFile, p, &p->vInouts, 0 );
    fprintf( pFile, ".inputs" );
    Cba_PrsWriteBlifArray( pFile, p, &p->vInputs, 0 );
    fprintf( pFile, ".outputs" );
    Cba_PrsWriteBlifArray( pFile, p, &p->vOutputs, 0 );
    // write objects
    Cba_PrsWriteBlifLines( pFile, p );
    fprintf( pFile, ".end\n\n" );
}
void Cba_PrsWriteBlif( char * pFileName, Cba_Man_t * pDes )
{
    FILE * pFile;
    Cba_Ntk_t * pNtk; 
    int i;
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "// Design \"%s\" written by ABC on %s\n\n", Cba_ManName(pDes), Extra_TimeStamp() );
    Cba_ManForEachNtk( pDes, pNtk, i )
        Cba_PrsWriteBlifNtk( pFile, pNtk );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

