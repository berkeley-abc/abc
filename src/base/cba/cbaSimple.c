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
#include "cbaPrs.h"
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
char * Ptr_TypeToSop( int Type )
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
char * Ptr_AbcObjName( Abc_Obj_t * pObj )
{
    if ( Abc_ObjIsNet(pObj) || Abc_ObjIsBox(pObj) )
        return Abc_ObjName(pObj);
    if ( Abc_ObjIsCi(pObj) || Abc_ObjIsNode(pObj) )
        return Ptr_AbcObjName(Abc_ObjFanout0(pObj));
    if ( Abc_ObjIsCo(pObj) )
        return Ptr_AbcObjName(Abc_ObjFanin0(pObj));
    assert( 0 );
    return NULL;
}
static int Ptr_CheckArray( Vec_Ptr_t * vArray )
{
    if ( Vec_PtrSize(vArray) == 0 )
        return 1;
    if ( Abc_MaxInt(8, Vec_PtrSize(vArray)) == Vec_PtrCap(vArray) )
        return 1;
    assert( 0 );
    return 0;
}
Vec_Ptr_t * Ptr_AbcDeriveNode( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin; int i;
    Vec_Ptr_t * vNode = Vec_PtrAlloc( 2 + Abc_ObjFaninNum(pObj) );
    assert( Abc_ObjIsNode(pObj) );
    Vec_PtrPush( vNode, Ptr_AbcObjName(pObj) );
    Vec_PtrPush( vNode, Abc_Int2Ptr(Ptr_HopToType(pObj)) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Vec_PtrPush( vNode, Ptr_AbcObjName(pFanin) );
    assert( Ptr_CheckArray(vNode) );
    return vNode;
}
Vec_Ptr_t * Ptr_AbcDeriveNodes( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vNodes = Vec_PtrAlloc( Abc_NtkNodeNum(pNtk) );
    Abc_NtkForEachNode( pNtk, pObj, i )
        Vec_PtrPush( vNodes, Ptr_AbcDeriveNode(pObj) );
    assert( Ptr_CheckArray(vNodes) );
    return vNodes;
}

Vec_Ptr_t * Ptr_AbcDeriveBox( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pNext; int i;
    Abc_Ntk_t * pModel = Abc_ObjModel(pObj);
    Vec_Ptr_t * vBox = Vec_PtrAlloc( 2 + 2 * Abc_ObjFaninNum(pObj) + 2 * Abc_ObjFanoutNum(pObj) );
    assert( Abc_ObjIsBox(pObj) );
    Vec_PtrPush( vBox, Abc_NtkName(pModel) );
    Vec_PtrPush( vBox, Ptr_AbcObjName(pObj) );
    Abc_ObjForEachFanin( pObj, pNext, i )
    {
        Vec_PtrPush( vBox, Ptr_AbcObjName(Abc_NtkPi(pModel, i)) );
        Vec_PtrPush( vBox, Ptr_AbcObjName(pNext) );
    }
    Abc_ObjForEachFanout( pObj, pNext, i )
    {
        Vec_PtrPush( vBox, Ptr_AbcObjName(Abc_NtkPo(pModel, i)) );
        Vec_PtrPush( vBox, Ptr_AbcObjName(pNext) );
    }
    assert( Ptr_CheckArray(vBox) );
    return vBox;
}
Vec_Ptr_t * Ptr_AbcDeriveBoxes( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vBoxes = Vec_PtrAlloc( Abc_NtkBoxNum(pNtk) );
    Abc_NtkForEachBox( pNtk, pObj, i )
        Vec_PtrPush( vBoxes, Ptr_AbcDeriveBox(pObj) );
    assert( Ptr_CheckArray(vBoxes) );
    return vBoxes;
}

Vec_Ptr_t * Ptr_AbcDeriveInputs( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vSigs = Vec_PtrAlloc( Abc_NtkPiNum(pNtk) );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Vec_PtrPush( vSigs, Ptr_AbcObjName(pObj) );
    assert( Ptr_CheckArray(vSigs) );
    return vSigs;
}
Vec_Ptr_t * Ptr_AbcDeriveOutputs( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj; int i;
    Vec_Ptr_t * vSigs = Vec_PtrAlloc( Abc_NtkPoNum(pNtk) );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Vec_PtrPush( vSigs, Ptr_AbcObjName(pObj) );
    assert( Ptr_CheckArray(vSigs) );
    return vSigs;
}
Vec_Ptr_t * Ptr_AbcDeriveNtk( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNtk = Vec_PtrAlloc( 5 );
    Vec_PtrPush( vNtk, Abc_NtkName(pNtk) );
    Vec_PtrPush( vNtk, Ptr_AbcDeriveInputs(pNtk) );
    Vec_PtrPush( vNtk, Ptr_AbcDeriveOutputs(pNtk) );
    Vec_PtrPush( vNtk, Ptr_AbcDeriveNodes(pNtk) );
    Vec_PtrPush( vNtk, Ptr_AbcDeriveBoxes(pNtk) );
    assert( Ptr_CheckArray(vNtk) );
    return vNtk;
}
Vec_Ptr_t * Ptr_AbcDeriveDes( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vDes;
    Abc_Ntk_t * pTemp; int i;
    vDes = Vec_PtrAlloc( 1 + Vec_PtrSize(pNtk->pDesign->vModules) );
    Vec_PtrPush( vDes, pNtk->pDesign->pName );
    Vec_PtrForEachEntry( Abc_Ntk_t *, pNtk->pDesign->vModules, pTemp, i )
        Vec_PtrPush( vDes, Ptr_AbcDeriveNtk(pTemp) );
    assert( Ptr_CheckArray(vDes) );
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
    fprintf( pFile, "%s", Ptr_TypeToSop( Abc_Ptr2Int(Vec_PtrEntry(vNode, 1)) ) );
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
    Vec_Ptr_t * vDes = Ptr_AbcDeriveDes( pNtk );
    printf( "Converting to Ptr:  Memory = %6.3f MB  ", 1.0*Ptr_ManMemDes(vDes)/(1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Ptr_ManDumpBlif( pFileName, vDes );
    printf( "Finished writing output file \"%s\".  ", pFileName );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Ptr_ManFreeDes( vDes );
}



/**Function*************************************************************

  Synopsis    [Dumping hierarchical Cba_Ntk_t in Ptr form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ptr_CbaDeriveNode( Cba_Ntk_t * pNtk, int iObj )
{
    Vec_Int_t * vFanins = Cba_ObjFaninVec( pNtk, iObj );
    Vec_Ptr_t * vNode = Vec_PtrAlloc( 2 + Vec_IntSize(vFanins) );
    int i, iFanin;
    assert( Cba_ObjIsNode(pNtk, iObj) );
    Vec_PtrPush( vNode, Cba_ObjNameStr(pNtk, iObj) );
    if ( Abc_NamObjNumMax(pNtk->pDesign->pFuncs) > 1 )
        Vec_PtrPush( vNode, Cba_NtkFuncStr( pNtk, Cba_ObjFuncId(pNtk, iObj) ) );
    else
        Vec_PtrPush( vNode, Abc_Int2Ptr(Cba_ObjFuncId(pNtk, iObj)) );
    Vec_IntForEachEntry( vFanins, iFanin, i )
        Vec_PtrPush( vNode, Cba_ObjNameStr(pNtk, iFanin) );
    assert( Ptr_CheckArray(vNode) );
    return vNode;
}
Vec_Ptr_t * Ptr_CbaDeriveNodes( Cba_Ntk_t * pNtk )
{
    int Type, iObj;
    Vec_Ptr_t * vNodes = Vec_PtrAlloc( Cba_NtkNodeNum(pNtk) );
    Cba_NtkForEachObjType( pNtk, Type, iObj )
        if ( Type == CBA_OBJ_NODE )
            Vec_PtrPush( vNodes, Ptr_CbaDeriveNode(pNtk, iObj) );
    assert( Ptr_CheckArray(vNodes) );
    return vNodes;
}

Vec_Ptr_t * Ptr_CbaDeriveBox( Cba_Ntk_t * pNtk, int iObj )
{
    int i, iTerm;
    Vec_Int_t * vFanins = Cba_ObjFaninVec( pNtk, iObj );
    Cba_Ntk_t * pModel = Cba_ObjBoxModel( pNtk, iObj );
    Vec_Ptr_t * vBox = Vec_PtrAlloc( 2 + Cba_NtkPiNum(pModel) + Cba_NtkPoNum(pModel) );
    assert( Cba_ObjIsBox(pNtk, iObj) );
    assert( Cba_NtkPiNum(pModel) == Vec_IntSize(vFanins) );
    Vec_PtrPush( vBox, Cba_NtkName(pModel) );
    Vec_PtrPush( vBox, Vec_IntSize(&pNtk->vInstIds) ? Cba_ObjInstStr(pNtk, iObj) : NULL );
    Cba_NtkForEachPi( pModel, iTerm, i )
    {
        Vec_PtrPush( vBox, Cba_ObjNameStr(pModel, iTerm) );
        Vec_PtrPush( vBox, Cba_ObjNameStr(pNtk, Vec_IntEntry(vFanins, i)) );
    }
    Cba_NtkForEachPo( pModel, iTerm, i )
    {
        Vec_PtrPush( vBox, Cba_ObjNameStr(pModel, iTerm) );
        Vec_PtrPush( vBox, Cba_ObjNameStr(pNtk, iObj+1+i) );
    }
    assert( Ptr_CheckArray(vBox) );
    return vBox;
}
Vec_Ptr_t * Ptr_CbaDeriveBoxes( Cba_Ntk_t * pNtk )
{
    int Type, iObj;
    Vec_Ptr_t * vBoxes = Vec_PtrAlloc( Cba_NtkBoxNum(pNtk) );
    Cba_NtkForEachObjType( pNtk, Type, iObj )
        if ( Type == CBA_OBJ_BOX )
            Vec_PtrPush( vBoxes, Ptr_CbaDeriveBox(pNtk, iObj) );
    assert( Ptr_CheckArray(vBoxes) );
    return vBoxes;
}

Vec_Ptr_t * Ptr_CbaDeriveInputs( Cba_Ntk_t * pNtk )
{
    int i, iObj;
    Vec_Ptr_t * vSigs = Vec_PtrAlloc( Cba_NtkPiNum(pNtk) );
    Cba_NtkForEachPi( pNtk, iObj, i )
        Vec_PtrPush( vSigs, Cba_ObjNameStr(pNtk, iObj) );
    assert( Ptr_CheckArray(vSigs) );
    return vSigs;
}
Vec_Ptr_t * Ptr_CbaDeriveOutputs( Cba_Ntk_t * pNtk )
{
    int i, iObj;
    Vec_Ptr_t * vSigs = Vec_PtrAlloc( Cba_NtkPoNum(pNtk) );
    Cba_NtkForEachPo( pNtk, iObj, i )
        Vec_PtrPush( vSigs, Cba_ObjNameStr(pNtk, iObj) );
    assert( Ptr_CheckArray(vSigs) );
    return vSigs;
}
Vec_Ptr_t * Ptr_CbaDeriveNtk( Cba_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNtk = Vec_PtrAlloc( 5 );
    Vec_PtrPush( vNtk, Cba_NtkName(pNtk) );
    Vec_PtrPush( vNtk, Ptr_CbaDeriveInputs(pNtk) );
    Vec_PtrPush( vNtk, Ptr_CbaDeriveOutputs(pNtk) );
    Vec_PtrPush( vNtk, Ptr_CbaDeriveNodes(pNtk) );
    Vec_PtrPush( vNtk, Ptr_CbaDeriveBoxes(pNtk) );
    assert( Ptr_CheckArray(vNtk) );
    return vNtk;
}
Vec_Ptr_t * Ptr_CbaDeriveDes( Cba_Man_t * p )
{
    Vec_Ptr_t * vDes;
    Cba_Ntk_t * pTemp; int i;
    vDes = Vec_PtrAlloc( 1 + Cba_ManNtkNum(p) );
    Vec_PtrPush( vDes, p->pName );
    Cba_ManForEachNtk( p, pTemp, i )
        Vec_PtrPush( vDes, Ptr_CbaDeriveNtk(pTemp) );
    assert( Ptr_CheckArray(vDes) );
    return vDes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cba_PrsReadList( Cba_Man_t * p, Vec_Ptr_t * vNames, Vec_Int_t * vList, int nSkip, int nSkip2 )
{
    char * pName; int i;
    Vec_IntClear( vList );
    Vec_PtrForEachEntry( char *, vNames, pName, i )
        if ( i != nSkip && i != nSkip2 )
            Vec_IntPush( vList, Abc_NamStrFindOrAdd(p->pNames, pName, NULL) );
    return vList;
}
void Cba_PrsReadNodes( Cba_Man_t * p, Vec_Ptr_t * vNodes, Vec_Int_t * vTypesCur, Vec_Int_t * vFuncsCur, Vec_Int_t * vInstIdsCur, Vec_Int_t * vFaninsCur, Vec_Int_t * vList )
{
    Vec_Ptr_t * vNode; int i;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vNodes, vNode, i )
    {
        Vec_IntPush( vTypesCur,   CBA_OBJ_NODE );
        Vec_IntPush( vFuncsCur,   (Ptr_ObjType_t)Abc_Ptr2Int(Vec_PtrEntry(vNode, 1)) );
        Vec_IntPush( vInstIdsCur, 0 );
        Vec_IntPush( vFaninsCur,  Cba_ManHandleArray(p, Cba_PrsReadList(p, vNode, vList, 1, -1)) ); 
    }
}
void Cba_PrsReadBoxes( Cba_Man_t * p, Vec_Ptr_t * vBoxes, Vec_Int_t * vTypesCur, Vec_Int_t * vFuncsCur, Vec_Int_t * vInstIdsCur, Vec_Int_t * vFaninsCur, Vec_Int_t * vList )
{
    Vec_Ptr_t * vBox; int i;
    Vec_PtrForEachEntry( Vec_Ptr_t *, vBoxes, vBox, i )
    {
        Vec_IntPush( vTypesCur,   CBA_OBJ_BOX );
        Vec_IntPush( vFuncsCur,   Abc_NamStrFindOrAdd(p->pModels, Vec_PtrEntry(vBox, 0), NULL) );
        Vec_IntPush( vInstIdsCur, Abc_NamStrFindOrAdd(p->pNames, Vec_PtrEntry(vBox, 1), NULL) );
        Vec_IntPush( vFaninsCur,  Cba_ManHandleArray(p, Cba_PrsReadList(p, vBox, vList, 0, 1)) ); 
    }
}
void Cba_PrsReadModule( Cba_Man_t * p, Vec_Ptr_t * vNtk )   
{
    Vec_Int_t * vInputsCur  = Vec_IntAlloc( 1000 );
    Vec_Int_t * vOutputsCur = Vec_IntAlloc( 1000 );
    Vec_Int_t * vTypesCur   = Vec_IntAlloc( 1000 );
    Vec_Int_t * vFuncsCur   = Vec_IntAlloc( 1000 );
    Vec_Int_t * vInstIdsCur = Vec_IntAlloc( 1000 );
    Vec_Int_t * vFaninsCur  = Vec_IntAlloc( 1000 );
    Vec_Int_t * vList       = Vec_IntAlloc( 1000 );

    Cba_Ntk_t * pNtk = Cba_NtkAlloc( p, (char *)Vec_PtrEntry(vNtk, 0) );
    Cba_PrsReadList( p, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 1), vInputsCur,  -1, -1 );
    Cba_PrsReadList( p, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 2), vOutputsCur, -1, -1 );
    Cba_PrsReadNodes( p, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 3), vTypesCur, vFuncsCur, vInstIdsCur, vFaninsCur, vList );
    Cba_PrsReadBoxes( p, (Vec_Ptr_t *)Vec_PtrEntry(vNtk, 4), vTypesCur, vFuncsCur, vInstIdsCur, vFaninsCur, vList );

    Cba_ManSetupArray( p, &pNtk->vInputs,  vInputsCur  );
    Cba_ManSetupArray( p, &pNtk->vOutputs, vOutputsCur );
    Cba_ManSetupArray( p, &pNtk->vTypes,   vTypesCur   );
    Cba_ManSetupArray( p, &pNtk->vFuncs,   vFuncsCur   );
    Cba_ManSetupArray( p, &pNtk->vInstIds, vInstIdsCur );
    Cba_ManSetupArray( p, &pNtk->vFanins,  vFaninsCur  );

    Vec_IntFree( vInputsCur );
    Vec_IntFree( vOutputsCur );
    Vec_IntFree( vTypesCur );
    Vec_IntFree( vFuncsCur );
    Vec_IntFree( vInstIdsCur );
    Vec_IntFree( vFaninsCur );
    Vec_IntFree( vList );
}
Cba_Man_t * Cba_PrsReadPtr( Vec_Ptr_t * vDes )
{
    Vec_Ptr_t * vNtk; int i;
    Cba_Man_t * p = Cba_ManAlloc( (char *)Vec_PtrEntry(vDes, 0) );
    Vec_PtrForEachEntryStart( Vec_Ptr_t *, vDes, vNtk, i, 1 )
        Cba_PrsReadModule( p, vNtk );
    return p;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_ManReadDesExperiment( Abc_Ntk_t * pNtk )
{
    abctime clk = Abc_Clock();
    Cba_Man_t * p, * pTemp;
    char * pFileName;

    // derive Ptr from ABC
    Vec_Ptr_t * vDes = Ptr_AbcDeriveDes( pNtk );
    printf( "Converting to Ptr:  Memory = %6.3f MB  ", 1.0*Ptr_ManMemDes(vDes)/(1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    // dump
    pFileName = Extra_FileNameGenericAppend(pNtk->pDesign->pName, "_out1.blif");
    Ptr_ManDumpBlif( pFileName, vDes );
    printf( "Finished writing output file \"%s\".  ", pFileName );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    
    // derive CBA from Ptr
    p = Cba_PrsReadPtr( vDes );
    Ptr_ManFreeDes( vDes );
    // dump
    pFileName = Extra_FileNameGenericAppend(pNtk->pDesign->pName, "_out2.blif");
    Cba_PrsWriteBlif( pFileName, p );
    printf( "Finished writing output file \"%s\".  ", pFileName );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    //    Abc_NamPrint( p->pNames );

    // build CBA from CBA
    p = Cba_ManBuild( pTemp = p );
    Cba_ManFree( pTemp );
    // dump
    pFileName = Extra_FileNameGenericAppend(pNtk->pDesign->pName, "_out3.blif");
    Cba_ManWriteBlif( pFileName, p );
    Cba_ManFree( p );
    printf( "Finished writing output file \"%s\".  ", pFileName );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

