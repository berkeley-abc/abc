/**CFile****************************************************************

  FileName    [cbaSimple.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaSimple.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "base/abc/abc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/*
design = array containing design name (as the first entry in the array) followed by pointers to modules
module = array containing module name (as the first entry in the array) followed by pointers to four arrays: 
         {array of input names; array of output names; array of nodes; array of boxes}
node   = array containing output name, followed by node type, followed by input names
box    = array containing model name, instance name, followed by pairs of formal/actual names for each port
*/

typedef enum { 
    PTR_OBJ_NONE,    // 0: non-existent object
    PTR_OBJ_CONST0,  // 1: constant node
    PTR_OBJ_PI,      // 2: primary input
    PTR_OBJ_PO,      // 3: primary output
    PTR_OBJ_FAN,     // 4: box output
    PTR_OBJ_FLOP,    // 5: flip-flop
    PTR_OBJ_BOX,     // 6: box
    PTR_OBJ_NODE,    // 7: logic node

    PTR_OBJ_C0,      // 8: logic node
    PTR_OBJ_C1,      // 9: logic node
    PTR_OBJ_BUF,     // 0: logic node
    PTR_OBJ_INV,     // 1: logic node
    PTR_OBJ_AND,     // 2: logic node
    PTR_OBJ_OR,      // 3: logic node
    PTR_OBJ_XOR,     // 4: logic node
    PTR_OBJ_NAND,    // 5: logic node
    PTR_OBJ_NOR,     // 6: logic node
    PTR_OBJ_XNOR,    // 7: logic node
    PTR_OBJ_MUX,     // 8: logic node
    PTR_OBJ_MAJ,     // 9: logic node

    PTR_VOID         // 0: placeholder
} Ptr_ObjType_t;


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Node type conversions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ptr_TypeToName( Ptr_ObjType_t Type )
{
    if ( Type == PTR_OBJ_BUF )   return "buf";
    if ( Type == PTR_OBJ_INV )   return "not";
    if ( Type == PTR_OBJ_AND )   return "and";
    if ( Type == PTR_OBJ_OR )    return "or";
    if ( Type == PTR_OBJ_XOR )   return "xor";
    if ( Type == PTR_OBJ_XNOR )  return "xnor";
    assert( 0 );
    return "???";
}
char * Ptr_TypeToSop( Ptr_ObjType_t Type )
{
    if ( Type == PTR_OBJ_BUF )   return "1 1\n";
    if ( Type == PTR_OBJ_INV )   return "0 1\n";
    if ( Type == PTR_OBJ_AND )   return "11 1\n";
    if ( Type == PTR_OBJ_OR )    return "00 0\n";
    if ( Type == PTR_OBJ_XOR )   return "01 1\n10 1\n";
    if ( Type == PTR_OBJ_XNOR )  return "00 1\n11 1\n";
    assert( 0 );
    return "???";
}
Ptr_ObjType_t Ptr_SopToType( char * pSop )
{
    if ( !strcmp(pSop, "1 1\n") )        return PTR_OBJ_BUF;
    if ( !strcmp(pSop, "0 1\n") )        return PTR_OBJ_INV;
    if ( !strcmp(pSop, "11 1\n") )       return PTR_OBJ_AND;
    if ( !strcmp(pSop, "00 0\n") )       return PTR_OBJ_OR;
    if ( !strcmp(pSop, "-1 1\n1- 1\n") ) return PTR_OBJ_OR;
    if ( !strcmp(pSop, "1- 1\n-1 1\n") ) return PTR_OBJ_OR;
    if ( !strcmp(pSop, "01 1\n10 1\n") ) return PTR_OBJ_XOR;
    if ( !strcmp(pSop, "10 1\n01 1\n") ) return PTR_OBJ_XOR;
    if ( !strcmp(pSop, "11 1\n00 1\n") ) return PTR_OBJ_XNOR;
    if ( !strcmp(pSop, "00 1\n11 1\n") ) return PTR_OBJ_XNOR;
    assert( 0 );
    return PTR_OBJ_NONE;
}
Ptr_ObjType_t Ptr_HopToType( Abc_Obj_t * pObj )
{
    static word uTruth, uTruths6[3] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
    };
    assert( Abc_ObjIsNode(pObj) );
    uTruth = Hop_ManComputeTruth6( (Hop_Man_t *)Abc_ObjNtk(pObj)->pManFunc, (Hop_Obj_t *)pObj->pData, Abc_ObjFaninNum(pObj) );
    if ( uTruth ==  uTruths6[0] )                 return PTR_OBJ_BUF;
    if ( uTruth == ~uTruths6[0] )                 return PTR_OBJ_INV;
    if ( uTruth == (uTruths6[0] & uTruths6[1]) )  return PTR_OBJ_AND;
    if ( uTruth == (uTruths6[0] | uTruths6[1]) )  return PTR_OBJ_OR;
    if ( uTruth == (uTruths6[0] ^ uTruths6[1]) )  return PTR_OBJ_XOR;
    if ( uTruth == (uTruths6[0] ^~uTruths6[1]) )  return PTR_OBJ_XNOR;
    assert( 0 );
    return PTR_OBJ_NONE;
}

/**Function*************************************************************

  Synopsis    [Dumping hierarchical Abc_Ntk_t in Ptr form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline char * Ptr_ObjName( Abc_Obj_t * pObj )
{
    if ( Abc_ObjIsNet(pObj) || Abc_ObjIsBox(pObj) )
        return Abc_ObjName(pObj);
    if ( Abc_ObjIsCi(pObj) || Abc_ObjIsNode(pObj) )
        return Ptr_ObjName(Abc_ObjFanout0(pObj));
    if ( Abc_ObjIsCo(pObj) )
        return Ptr_ObjName(Abc_ObjFanin0(pObj));
    assert( 0 );
    return NULL;
}
static int Ptr_ManCheckArray( Vec_Ptr_t * vArray )
{
    if ( Vec_PtrSize(vArray) == 0 )
        return 1;
    if ( Abc_MaxInt(8, Vec_PtrSize(vArray)) == Vec_PtrCap(vArray) )
        return 1;
    assert( 0 );
    return 0;
}
Vec_Ptr_t * Ptr_ManDeriveNode( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin; int i;
    Vec_Ptr_t * vNode = Vec_PtrAlloc( 2 + Abc_ObjFaninNum(pObj) );
    assert( Abc_ObjIsNode(pObj) );
    Vec_PtrPush( vNode, Ptr_ObjName(pObj) );
    Vec_PtrPush( vNode, Abc_Int2Ptr(Ptr_HopToType(pObj)) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Vec_PtrPush( vNode, Ptr_ObjName(pFanin) );
    assert( Ptr_ManCheckArray(vNode) );
    return vNode;
}
Vec_Ptr_t * Ptr_ManDeriveNodes( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vNodes = Vec_PtrAlloc( Abc_NtkNodeNum(pNtk) );
    Abc_NtkForEachNode( pNtk, pObj, i )
        Vec_PtrPush( vNodes, Ptr_ManDeriveNode(pObj) );
    assert( Ptr_ManCheckArray(vNodes) );
    return vNodes;
}

Vec_Ptr_t * Ptr_ManDeriveBox( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pNext; int i;
    Abc_Ntk_t * pModel = Abc_ObjModel(pObj);
    Vec_Ptr_t * vBox = Vec_PtrAlloc( 2 + 2 * Abc_ObjFaninNum(pObj) + 2 * Abc_ObjFanoutNum(pObj) );
    assert( Abc_ObjIsBox(pObj) );
    Vec_PtrPush( vBox, Abc_NtkName(pModel) );
    Vec_PtrPush( vBox, Ptr_ObjName(pObj) );
    Abc_ObjForEachFanin( pObj, pNext, i )
    {
        Vec_PtrPush( vBox, Ptr_ObjName(Abc_NtkPi(pModel, i)) );
        Vec_PtrPush( vBox, Ptr_ObjName(pNext) );
    }
    Abc_ObjForEachFanout( pObj, pNext, i )
    {
        Vec_PtrPush( vBox, Ptr_ObjName(Abc_NtkPo(pModel, i)) );
        Vec_PtrPush( vBox, Ptr_ObjName(pNext) );
    }
    assert( Ptr_ManCheckArray(vBox) );
    return vBox;
}
Vec_Ptr_t * Ptr_ManDeriveBoxes( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vBoxes = Vec_PtrAlloc( Abc_NtkBoxNum(pNtk) );
    Abc_NtkForEachBox( pNtk, pObj, i )
        Vec_PtrPush( vBoxes, Ptr_ManDeriveBox(pObj) );
    assert( Ptr_ManCheckArray(vBoxes) );
    return vBoxes;
}

Vec_Ptr_t * Ptr_ManDeriveInputs( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vSigs = Vec_PtrAlloc( Abc_NtkPiNum(pNtk) );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Vec_PtrPush( vSigs, Ptr_ObjName(pObj) );
    assert( Ptr_ManCheckArray(vSigs) );
    return vSigs;
}
Vec_Ptr_t * Ptr_ManDeriveOutputs( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vSigs = Vec_PtrAlloc( Abc_NtkPoNum(pNtk) );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Vec_PtrPush( vSigs, Ptr_ObjName(pObj) );
    assert( Ptr_ManCheckArray(vSigs) );
    return vSigs;
}
Vec_Ptr_t * Ptr_ManDeriveNtk( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNtk = Vec_PtrAlloc( 5 );
    Vec_PtrPush( vNtk, Abc_NtkName(pNtk) );
    Vec_PtrPush( vNtk, Ptr_ManDeriveInputs(pNtk) );
    Vec_PtrPush( vNtk, Ptr_ManDeriveOutputs(pNtk) );
    Vec_PtrPush( vNtk, Ptr_ManDeriveNodes(pNtk) );
    Vec_PtrPush( vNtk, Ptr_ManDeriveBoxes(pNtk) );
    assert( Ptr_ManCheckArray(vNtk) );
    return vNtk;
}
Vec_Ptr_t * Ptr_ManDeriveDes( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vDes;
    Abc_Ntk_t * pTemp; int i;
    vDes = Vec_PtrAlloc( 1 + Vec_PtrSize(pNtk->pDesign->vModules) );
    Vec_PtrPush( vDes, pNtk->pDesign->pName );
    Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pTemp, i )
        Vec_PtrPush( vDes, Ptr_ManDeriveNtk(pTemp) );
    assert( Ptr_ManCheckArray(vDes) );
    return vDes;
}

/**Function*************************************************************

  Synopsis    [Dumping Ptr into a Verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ptr_ManDumpNodeBlif( FILE * pFile, Vec_Ptr_t * vNode )
{
    char * pName;  int i;
    fprintf( pFile, ".names" );
    Vec_PtrForEachEntryStart( char *, vNode, pName, i, 2 )
        fprintf( pFile, " %s", pName );
    fprintf( pFile, " %s\n", (char *)Vec_PtrEntry(vNode, 0) );
    fprintf( pFile, "%s", Ptr_TypeToSop( (Ptr_ObjType_t)Abc_Ptr2Int(Vec_PtrEntry(vNode, 1)) ) );
}
void Ptr_ManDumpNodesBlif( FILE * pFile, Vec_Ptr_t * vNodes )
{
    Vec_Ptr_t * vNode; int i;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vNodes, vNode, i )
        Ptr_ManDumpNodeBlif( pFile, vNode );
}

void Ptr_ManDumpBoxBlif( FILE * pFile, Vec_Ptr_t * vBox )
{
    char * pName; int i;
    fprintf( pFile, ".subckt %s", (char *)Vec_PtrEntry(vBox, 0) );
    Vec_PtrForEachEntryStart( char *, vBox, pName, i, 2 )
        fprintf( pFile, " %s=%s", pName, (char *)Vec_PtrEntry(vBox, i+1) ), i++;
    fprintf( pFile, "\n" );
}
void Ptr_ManDumpBoxesBlif( FILE * pFile, Vec_Ptr_t * vBoxes )
{
    Vec_Ptr_t * vBox; int i;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vBoxes, vBox, i )
        Ptr_ManDumpBoxBlif( pFile, vBox );
}

void Ptr_ManDumpSignalsBlif( FILE * pFile, Vec_Ptr_t * vSigs, int fSkipLastComma )
{
    char * pSig; int i;
    Vec_PtrForEachEntry( char *, vSigs, pSig, i )
        fprintf( pFile, " %s", pSig );
}
void Ptr_ManDumpModuleBlif( FILE * pFile, Vec_Ptr_t * vNtk )
{
    fprintf( pFile, ".model %s\n", (char *)Vec_PtrEntry(vNtk, 0) );
    fprintf( pFile, ".inputs" );
    Ptr_ManDumpSignalsBlif( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1), 0 );
    fprintf( pFile, "\n" );
    fprintf( pFile, ".outputs" );
    Ptr_ManDumpSignalsBlif( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2), 1 );
    fprintf( pFile, "\n\n" );
    Ptr_ManDumpNodesBlif( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3) );
    fprintf( pFile, "\n" );
    Ptr_ManDumpBoxesBlif( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4) );
    fprintf( pFile, "\n" );
    fprintf( pFile, ".end\n\n" );
}
void Ptr_ManDumpBlif( char * pFileName, Vec_Ptr_t * vDes )
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
        Ptr_ManDumpModuleBlif( pFile, vNtk );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Dumping Ptr into a Verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ptr_ManDumpNodeVerilog( FILE * pFile, Vec_Ptr_t * vNode )
{
    char * pName;  int i;
    fprintf( pFile, "%s", Ptr_TypeToName( (Ptr_ObjType_t)Abc_Ptr2Int(Vec_PtrEntry(vNode, 1)) ) );
    fprintf( pFile, "( %s", (char *)Vec_PtrEntry(vNode, 0) );
    Vec_PtrForEachEntryStart( char *, vNode, pName, i, 2 )
        fprintf( pFile, ", %s", pName );
    fprintf( pFile, " );\n" );
}
void Ptr_ManDumpNodesVerilog( FILE * pFile, Vec_Ptr_t * vNodes )
{
    Vec_Ptr_t * vNode; int i;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vNodes, vNode, i )
        Ptr_ManDumpNodeVerilog( pFile, vNode );
}

void Ptr_ManDumpBoxVerilog( FILE * pFile, Vec_Ptr_t * vBox )
{
    char * pName; int i;
    fprintf( pFile, "%s %s (", (char *)Vec_PtrEntry(vBox, 0), (char *)Vec_PtrEntry(vBox, 1) );
    Vec_PtrForEachEntryStart( char *, vBox, pName, i, 2 )
        fprintf( pFile, " .%s(%s)%s", pName, (char *)Vec_PtrEntry(vBox, i+1), i >= Vec_PtrSize(vBox)-2 ? "" : "," ), i++;
    fprintf( pFile, " );\n" );
}
void Ptr_ManDumpBoxesVerilog( FILE * pFile, Vec_Ptr_t * vBoxes )
{
    Vec_Ptr_t * vBox; int i;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vBoxes, vBox, i )
        Ptr_ManDumpBoxVerilog( pFile, vBox );
}

void Ptr_ManDumpSignalsVerilog( FILE * pFile, Vec_Ptr_t * vSigs, int fSkipLastComma )
{
    char * pSig; int i;
    Vec_PtrForEachEntry( char *, vSigs, pSig, i )
        fprintf( pFile, " %s%s", pSig, (fSkipLastComma && i == Vec_PtrSize(vSigs)-1) ? "" : "," );
}
void Ptr_ManDumpModuleVerilog( FILE * pFile, Vec_Ptr_t * vNtk )
{
    fprintf( pFile, "module %s\n", (char *)Vec_PtrEntry(vNtk, 0) );
    fprintf( pFile, "(\n" );
    Ptr_ManDumpSignalsVerilog( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1), 0 );
    fprintf( pFile, "\n" );
    Ptr_ManDumpSignalsVerilog( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2), 1 );
    fprintf( pFile, "\n);\ninput" );
    Ptr_ManDumpSignalsVerilog( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1), 1 );
    fprintf( pFile, ";\noutput" );
    Ptr_ManDumpSignalsVerilog( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2), 1 );
    fprintf( pFile, ";\n\n" );
    Ptr_ManDumpNodesVerilog( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3) );
    fprintf( pFile, "\n" );
    Ptr_ManDumpBoxesVerilog( pFile, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4) );
    fprintf( pFile, "endmodule\n\n" );
}
void Ptr_ManDumpVerilog( char * pFileName, Vec_Ptr_t * vDes )
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
        Ptr_ManDumpModuleVerilog( pFile, vNtk );
    fclose( pFile );
}


/**Function*************************************************************

  Synopsis    [Count memory used by Ptr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ptr_ManMemArray( Vec_Ptr_t * vArray )
{
    return (int)Vec_PtrMemory(vArray);
}
int Ptr_ManMemArrayArray( Vec_Ptr_t * vArrayArray )
{
    Vec_Ptr_t * vArray; int i, nBytes = 0;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vArrayArray, vArray, i )
        nBytes += Ptr_ManMemArray(vArray);
    return nBytes;
}
int Ptr_ManMemNtk( Vec_Ptr_t * vNtk )
{
    int nBytes = (int)Vec_PtrMemory(vNtk);
    nBytes += Ptr_ManMemArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1) );
    nBytes += Ptr_ManMemArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2) );
    nBytes += Ptr_ManMemArrayArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3) );
    nBytes += Ptr_ManMemArrayArray( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4) );
    return nBytes;
}
int Ptr_ManMemDes( Vec_Ptr_t * vDes )
{
    Vec_Ptr_t * vNtk; int i, nBytes = (int)Vec_PtrMemory(vDes);
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        nBytes += Ptr_ManMemNtk(vNtk);
    return nBytes;
}

/**Function*************************************************************

  Synopsis    [Free Ptr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ptr_ManFreeNtk( Vec_Ptr_t * vNtk )
{
    Vec_PtrFree( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1) );
    Vec_PtrFree( (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2) );
    Vec_VecFree( (Vec_Vec_t *)Vec_PtrEntry(vNtk, 3) );
    Vec_VecFree( (Vec_Vec_t *)Vec_PtrEntry(vNtk, 4) );
    Vec_PtrFree( vNtk );
}
void Ptr_ManFreeDes( Vec_Ptr_t * vDes )
{
    Vec_Ptr_t * vNtk; int i;
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Ptr_ManFreeNtk( vNtk );
    Vec_PtrFree( vDes );
}

/**Function*************************************************************

  Synopsis    [Count memory use used by Ptr.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ptr_ManExperiment( Abc_Ntk_t * pNtk )
{
    abctime clk = Abc_Clock();
    char * pFileName = Extra_FileNameGenericAppend(pNtk->pDesign->pName, "_out.blif");
    Vec_Ptr_t * vDes = Ptr_ManDeriveDes( pNtk );
    printf( "Converting to Ptr:  Memory = %6.3f MB  ", 1.0*Ptr_ManMemDes(vDes)/(1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Ptr_ManDumpBlif( pFileName, vDes );
    printf( "Finished writing output file \"%s\".  ", pFileName );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Ptr_ManFreeDes( vDes );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

