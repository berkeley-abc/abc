/**CFile****************************************************************

  FileName    [cbaPtr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Simple interface with external tools.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaPtr.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "base/main/mainInt.h"
#include "map/mio/mio.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/*
design = array containing design name (as the first entry in the array) followed by pointers to modules
module = array containing module name (as the first entry in the array) followed by pointers to 6 arrays: 
         {array of input names; array of output names; array of nodes; array of boxes, 
          array of floating-point input-arrival times; array of floating-point output-required times}
node   = array containing output name, followed by node type, followed by input names
box    = array containing model name, instance name, followed by pairs of formal/actual names for each port

  Comments:
  - in describing boxes
     - input formal/actual name pairs should be listed before output name pairs
     - the order of formal names should be the same as the order of inputs/outputs in the module description
     - all formal names present in the module description should be listed
     - if an input pin is not driven or an output pin has no fanout, the actual pin name is NULL
     - word-level formal name "a" is written as bit-level names (a[0]. a[1], etc) ordered LSB to MSB
     - the boxes can appear in any order (topological order is not expected)
  - in description of nodes and boxes, primitive names should be given as char*-strings ("AndT", "OrT", etc)
  - constant 0/1 nets should be driven by constant nodes having primitive names "Const0T" and "Const1T"
  - primitive modules should not be written, but the list of primitives and formal names should be provided
  - currently only "boxes" are supported (the array of "nodes" should contain no entries)
  - arrays of input-arrival/output-required times in the module description are optional
*/

// elementary gates
typedef enum { 
    PTR_GATE_NONE = 0,
    PTR_GATE_C0,         // Const0T
    PTR_GATE_C1,         // Const1T   
    PTR_GATE_BUF,        // BufT  
    PTR_GATE_INV,        // InvT  
    PTR_GATE_AND,        // AndT  
    PTR_GATE_NAND,       // NandT 
    PTR_GATE_OR,         // OrT   
    PTR_GATE_NOR,        // NorT  
    PTR_GATE_XOR,        // XorT  
    PTR_GATE_XNOR,       // XnorT 
    PTR_GATE_UNKNOWN
} Ptr_ObjType_t; 

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Free Ptr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_PtrFreeNtk( Vec_Ptr_t * vNtk )
{
    Vec_PtrFree( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1) );
    Vec_PtrFree( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2) );
    Vec_VecFree( (Vec_Vec_t *)Vec_PtrEntry(vNtk, 3) );
    Vec_VecFree( (Vec_Vec_t *)Vec_PtrEntry(vNtk, 4) );
    if ( Vec_PtrSize(vNtk) > 5 )
        Vec_FltFree( (Vec_Flt_t *)Vec_PtrEntry(vNtk, 5) );
    if ( Vec_PtrSize(vNtk) > 6 )
        Vec_FltFree( (Vec_Flt_t *)Vec_PtrEntry(vNtk, 6) );
    Vec_PtrFree( vNtk );
}
void Cba_PtrFree( Vec_Ptr_t * vDes )
{
    Vec_Ptr_t * vNtk; int i;
    if ( !vDes ) return;
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Cba_PtrFreeNtk( vNtk );
    Vec_PtrFree( vDes );
}

/**Function*************************************************************

  Synopsis    [Count memory used by Ptr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_PtrMemoryArray( Vec_Ptr_t * vArray )
{
    return (int)Vec_PtrMemory(vArray);
}
int Cba_PtrMemoryArrayArray( Vec_Ptr_t * vArrayArray )
{
    Vec_Ptr_t * vArray; int i, nBytes = 0;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vArrayArray, vArray, i )
        nBytes += Cba_PtrMemoryArray(vArray);
    return nBytes;
}
int Cba_PtrMemoryNtk( Vec_Ptr_t * vNtk )
{
    int nBytes = (int)Vec_PtrMemory(vNtk);
    nBytes += Cba_PtrMemoryArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1) );
    nBytes += Cba_PtrMemoryArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2) );
    nBytes += Cba_PtrMemoryArrayArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3) );
    nBytes += Cba_PtrMemoryArrayArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4) );
    return nBytes;
}
int Cba_PtrMemory( Vec_Ptr_t * vDes )
{
    Vec_Ptr_t * vNtk; int i, nBytes = (int)Vec_PtrMemory(vDes);
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        nBytes += Cba_PtrMemoryNtk(vNtk);
    return nBytes;
}

/**Function*************************************************************

  Synopsis    [Dumping Ptr into a BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_PtrDumpSignalsBlif( FILE * pFile, Vec_Ptr_t * vSigs, int fSkipLastComma )
{
    char * pSig; int i;
    Vec_PtrForEachEntry( char *, vSigs, pSig, i )
        fprintf( pFile, " %s", pSig );
}
void Cba_PtrDumpBoxBlif( FILE * pFile, Vec_Ptr_t * vBox )
{
    char * pName; int i;
    fprintf( pFile, ".subckt" );
    fprintf( pFile, " %s", (char *)Vec_PtrEntry(vBox, 0) );
    //fprintf( pFile, " %s", (char *)Vec_PtrEntry(vBox, 1) ); // do not write intance name in BLIF
    Vec_PtrForEachEntryStart( char *, vBox, pName, i, 2 )
        fprintf( pFile, " %s=%s", pName, (char *)Vec_PtrEntry(vBox, i+1) ), i++;
    fprintf( pFile, "\n" );
}
void Cba_PtrDumpBoxesBlif( FILE * pFile, Vec_Ptr_t * vBoxes )
{
    Vec_Ptr_t * vBox; int i;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vBoxes, vBox, i )
        Cba_PtrDumpBoxBlif( pFile, vBox );
}
void Cba_PtrDumpModuleBlif( FILE * pFile, Vec_Ptr_t * vNtk )
{
    fprintf( pFile, ".model %s\n", (char *)Vec_PtrEntry(vNtk, 0) );
    fprintf( pFile, ".inputs" );
    Cba_PtrDumpSignalsBlif( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1), 0 );
    fprintf( pFile, "\n" );
    fprintf( pFile, ".outputs" );
    Cba_PtrDumpSignalsBlif( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2), 1 );
    fprintf( pFile, "\n" );
    assert( Vec_PtrSize((Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3)) == 0 ); // no nodes; only boxes
    Cba_PtrDumpBoxesBlif( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4) );
    fprintf( pFile, ".end\n\n" );
}
void Cba_PtrDumpBlif( char * pFileName, Vec_Ptr_t * vDes )
{
    FILE * pFile;
    Vec_Ptr_t * vNtk; int i;
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "// Design \"%s\" written by ABC on %s\n\n", (char *)Vec_PtrEntry(vDes, 0), Extra_TimeStamp() );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Cba_PtrDumpModuleBlif( pFile, vNtk );
    fclose( pFile );
}


/**Function*************************************************************

  Synopsis    [Collect elementary gates from the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_ManCollectGateNameOne( Mio_Library_t * pLib, Ptr_ObjType_t Type, word Truth, Vec_Ptr_t * vGateNames )
{
    Mio_Gate_t * pGate = Mio_LibraryReadGateByTruth( pLib, Truth );
    if ( pGate != NULL )
        Vec_PtrWriteEntry( vGateNames, Type, Mio_GateReadName(pGate) );
}
Vec_Ptr_t * Cba_ManCollectGateNamesByTruth( Mio_Library_t * pLib )
{
    static word uTruths6[3] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
    };
    Vec_Ptr_t * vGateNames = Vec_PtrStart( PTR_GATE_UNKNOWN );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_C0,              0,                 vGateNames );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_C1,       ~(word)0,                 vGateNames );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_BUF,    uTruths6[0],                vGateNames );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_INV,   ~uTruths6[0],                vGateNames );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_AND,   (uTruths6[0] & uTruths6[1]), vGateNames );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_NAND, ~(uTruths6[0] & uTruths6[1]), vGateNames );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_OR,    (uTruths6[0] | uTruths6[1]), vGateNames );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_NOR,  ~(uTruths6[0] | uTruths6[1]), vGateNames );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_XOR,   (uTruths6[0] ^ uTruths6[1]), vGateNames );
    Cba_ManCollectGateNameOne( pLib, PTR_GATE_XNOR, ~(uTruths6[0] ^ uTruths6[1]), vGateNames );
    return vGateNames;
}

/**Function*************************************************************

  Synopsis    [This procedure transforms tech-ind Ptr into mapped Ptr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_PtrUpdateBox( Vec_Ptr_t * vBox, Vec_Ptr_t * vGatesNames )
{
    Mio_Gate_t * pGate;  Mio_Pin_t * pPin; int i = 1;
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen( Abc_FrameGetGlobalFrame() );
    // update gate name
    char * pNameNew, * pName = (char *)Vec_PtrEntry(vBox, 0);
    if ( !strcmp(pName, "Const0T") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_C0);
    else if ( !strcmp(pName, "Const1T") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_C1);
    else if ( !strcmp(pName, "BufT") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_BUF);
    else if ( !strcmp(pName, "InvT") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_INV);
    else if ( !strcmp(pName, "AndT") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_AND);
    else if ( !strcmp(pName, "NandT") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_NAND);
    else if ( !strcmp(pName, "OrT") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_OR);
    else if ( !strcmp(pName, "NorT") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_NOR);
    else if ( !strcmp(pName, "XorT") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_XOR);
    else if ( !strcmp(pName, "XnorT") )
        pNameNew = (char *)Vec_PtrEntry(vGatesNames, PTR_GATE_XNOR);
    else // user hierarchy
        return;
    ABC_FREE( pName );
    Vec_PtrWriteEntry( vBox, 0, Abc_UtilStrsav(pNameNew) );
    // remove instance name
    pName = (char *)Vec_PtrEntry(vBox, 1);
    ABC_FREE( pName );
    Vec_PtrWriteEntry( vBox, 1, NULL );
    // update formal input names
    pGate = Mio_LibraryReadGateByName( pLib, pNameNew, NULL );
    Mio_GateForEachPin( pGate, pPin )
    {
        pName = (char *)Vec_PtrEntry( vBox, 2 * i );
        ABC_FREE( pName );
        pNameNew = Mio_PinReadName(pPin);
        Vec_PtrWriteEntry( vBox, 2 * i++, Abc_UtilStrsav(pNameNew) );
    }
    // update output name
    pName = (char *)Vec_PtrEntry( vBox, 2 * i );
    pNameNew = Mio_GateReadOutName(pGate);
    Vec_PtrWriteEntry( vBox, 2 * i++, Abc_UtilStrsav(pNameNew) );
    assert( 2 * i == Vec_PtrSize(vBox) );
}
Vec_Ptr_t * Cba_PtrTransformSigs( Vec_Ptr_t * vSig )
{
    char * pName; int i;
    Vec_Ptr_t * vNew = Vec_PtrAllocExact( Vec_PtrSize(vSig) );
    Vec_PtrForEachEntry( char *, vSig, pName, i )
        Vec_PtrPush( vNew, Abc_UtilStrsav(pName) );
    return vNew;
}
Vec_Ptr_t * Cba_PtrTransformBox( Vec_Ptr_t * vBox, Vec_Ptr_t * vGatesNames )
{
    char * pName; int i;
    Vec_Ptr_t * vNew = Vec_PtrAllocExact( Vec_PtrSize(vBox) );
    Vec_PtrForEachEntry( char *, vBox, pName, i )
        Vec_PtrPush( vNew, Abc_UtilStrsav(pName) );
    if ( vGatesNames )
        Cba_PtrUpdateBox( vNew, vGatesNames );
    return vNew;
}
Vec_Ptr_t * Cba_PtrTransformBoxes( Vec_Ptr_t * vBoxes, Vec_Ptr_t * vGatesNames )
{
    Vec_Ptr_t * vBox; int i;
    Vec_Ptr_t * vNew = Vec_PtrAllocExact( Vec_PtrSize(vBoxes) );
    Vec_PtrForEachEntry( Vec_Ptr_t *, vBoxes, vBox, i )
        Vec_PtrPush( vNew, Cba_PtrTransformBox(vBox, vGatesNames) );
    return vNew;
}
Vec_Ptr_t * Cba_PtrTransformNtk( Vec_Ptr_t * vNtk, Vec_Ptr_t * vGatesNames )
{
    char * pName = (char *)Vec_PtrEntry(vNtk, 0);
    Vec_Ptr_t * vInputs  = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1);
    Vec_Ptr_t * vOutputs = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2);
    Vec_Ptr_t * vBoxes   = (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4);
    Vec_Ptr_t * vNew     = Vec_PtrAllocExact( Vec_PtrSize(vNtk) );
    Vec_PtrPush( vNew, Abc_UtilStrsav(pName) );
    Vec_PtrPush( vNew, Cba_PtrTransformSigs(vInputs) );
    Vec_PtrPush( vNew, Cba_PtrTransformSigs(vOutputs) );
    Vec_PtrPush( vNew, Vec_PtrAllocExact(0) );
    Vec_PtrPush( vNew, Cba_PtrTransformBoxes(vBoxes, vGatesNames) );
    return vNew;
}
Vec_Ptr_t * Cba_PtrTransformTest( Vec_Ptr_t * vDes )
{
    Mio_Library_t * pLib;
    Vec_Ptr_t * vGatesNames;
    Vec_Ptr_t * vNtk, * vNew; int i;
    // dump BLIF before transformation
    Cba_PtrDumpBlif( "test1.blif", vDes );
    if ( Abc_FrameGetGlobalFrame() == NULL )
    {
        printf( "ABC framework is not started.\n" );
        return NULL;
    }
    pLib = (Mio_Library_t *)Abc_FrameReadLibGen( Abc_FrameGetGlobalFrame() );
    if ( pLib == NULL )
    {
        printf( "Standard cell library is not entered.\n" );
        return NULL;
    }
    vGatesNames = Cba_ManCollectGateNamesByTruth( pLib );
    // transform
    vNew = Vec_PtrAllocExact( Vec_PtrSize(vDes) );
    Vec_PtrPush( vNew, Abc_UtilStrsav((char *)Vec_PtrEntry(vDes, 0)) );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Vec_PtrPush( vNew, Cba_PtrTransformNtk(vNtk, vGatesNames) );
    // dump BLIF after transformation
    Cba_PtrDumpBlif( "test2.blif", vNew );
    Vec_PtrFree( vGatesNames );
    return vNew;
}

/**Function*************************************************************

  Synopsis    [Test the testing procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_PtrTransformTestTest()
{
    char * pFileName = "c/hie/dump/1/netlist_1.v";
    Abc_Ntk_t * pNtk = Io_ReadNetlist( pFileName, Io_ReadFileType(pFileName), 0 );
    extern Vec_Ptr_t * Ptr_AbcDeriveDes( Abc_Ntk_t * pNtk );
    Vec_Ptr_t * vDes = Ptr_AbcDeriveDes( pNtk );
    Vec_Ptr_t * vNew = Cba_PtrTransformTest( vDes );
    Cba_PtrFree( vDes );
    Cba_PtrFree( vNew );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

