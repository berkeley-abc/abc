/**CFile****************************************************************

  FileName    [abcFunc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Experimental procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcFunc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acb.h"
#include "aig/miniaig/ndr.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "sat/satoko/satoko.h"
#include "map/mio/mio.h"
#include "misc/util/utilTruth.h"
#include "aig/gia/giaAig.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
#define ACB_LAST_NAME_ID 14

typedef enum {
    ACB_NONE = 0,  // 0:  unused
    ACB_MODULE,    // 1:  "module"
    ACB_ENDMODULE, // 2:  "endmodule"
    ACB_INPUT,     // 3:  "input"
    ACB_OUTPUT,    // 4:  "output"
    ACB_WIRE,      // 5:  "wire"
    ACB_BUF,       // 6:  "buf"
    ACB_NOT,       // 7:  "not"
    ACB_AND,       // 8:  "and"
    ACB_NAND,      // 9:  "nand"
    ACB_OR,        // 10: "or"
    ACB_NOR,       // 11: "nor"
    ACB_XOR,       // 12: "xor"
    ACB_XNOR,      // 13: "xnor"
    ACB_UNUSED     // 14: unused
} Acb_KeyWords_t; 

static inline char * Acb_Num2Name( int i )
{
    if ( i == 1  )  return "module";
    if ( i == 2  )  return "endmodule";
    if ( i == 3  )  return "input";
    if ( i == 4  )  return "output";
    if ( i == 5  )  return "wire";
    if ( i == 6  )  return "buf";
    if ( i == 7  )  return "not";
    if ( i == 8  )  return "and";
    if ( i == 9  )  return "nand";
    if ( i == 10 )  return "or";
    if ( i == 11 )  return "nor";
    if ( i == 12 )  return "xor";
    if ( i == 13 )  return "xnor";
    return NULL;
}

static inline int Acb_Type2Oper( int i )
{
    if ( i == 6  )  return ABC_OPER_BIT_BUF;
    if ( i == 7  )  return ABC_OPER_BIT_INV;
    if ( i == 8  )  return ABC_OPER_BIT_AND;
    if ( i == 9  )  return ABC_OPER_BIT_NAND;
    if ( i == 10 )  return ABC_OPER_BIT_OR;
    if ( i == 11 )  return ABC_OPER_BIT_NOR;
    if ( i == 12 )  return ABC_OPER_BIT_XOR;
    if ( i == 13 )  return ABC_OPER_BIT_NXOR;
    assert( 0 );
    return -1;
}

static inline char * Acb_Oper2Name( int i )
{
    if ( i == ABC_OPER_CONST_F  )  return "const0";
    if ( i == ABC_OPER_CONST_T  )  return "const1";
    if ( i == ABC_OPER_BIT_BUF  )  return "buf";
    if ( i == ABC_OPER_BIT_INV  )  return "not";
    if ( i == ABC_OPER_BIT_AND  )  return "and";
    if ( i == ABC_OPER_BIT_NAND )  return "nand";
    if ( i == ABC_OPER_BIT_OR   )  return "or";
    if ( i == ABC_OPER_BIT_NOR  )  return "nor";
    if ( i == ABC_OPER_BIT_XOR  )  return "xor";
    if ( i == ABC_OPER_BIT_NXOR )  return "xnor";
    assert( 0 );
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Installs the required standard cell library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * pLibStr[25] = {
    "GATE buf        1       O=a;            PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE inv        1       O=!a;           PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE and2       1       O=a*b;          PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE and3       1       O=a*b*c;        PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE and4       1       O=a*b*c*d;      PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE or2        1       O=a+b;          PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE or3        1       O=a+b+c;        PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE or4        1       O=a+b+c+d;      PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE nand2      1       O=!(a*b);       PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE nand3      1       O=!(a*b*c);     PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE nand4      1       O=!(a*b*c*d);   PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE nor2       1       O=!(a+b);       PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE nor3       1       O=!(a+b+c);     PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE nor4       1       O=!(a+b+c+d);   PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE xor        1       O=!a*b+a*!b;    PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE xnor       1       O=a*b+!a*!b;    PIN * INV 1 999 1.0 0.0 1.0 0.0\n"
    "GATE zero       0       O=CONST0;\n"
    "GATE one        0       O=CONST1;\n"
};
void Acb_IntallLibrary()
{
    extern Mio_Library_t * Mio_LibraryReadBuffer( char * pBuffer, int fExtendedFormat, st__table * tExcludeGate, int fVerbose );
    Mio_Library_t * pLib;
    int i;
    // create library string
    Vec_Str_t * vLibStr = Vec_StrAlloc( 1000 );
    for ( i = 0; pLibStr[i]; i++ )
        Vec_StrAppend( vLibStr, pLibStr[i] );
    Vec_StrPush( vLibStr, '\0' );
    // create library
    pLib = Mio_LibraryReadBuffer( Vec_StrArray(vLibStr), 0, NULL, 0 );
    Mio_LibrarySetName( pLib, Abc_UtilStrsav("iccad17.genlib") );
    Mio_UpdateGenlib( pLib );
    Vec_StrFree( vLibStr );
}

/**Function*************************************************************

  Synopsis    [Parse Verilog file into an intermediate representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Nam_t * Acb_VerilogStartNames()
{
    Abc_Nam_t * pNames = Abc_NamStart( 100, 16 ); 
    int i, NameId, fFound;
    for ( i = 1; i < ACB_UNUSED; i++ )
    {
        NameId = Abc_NamStrFindOrAdd( pNames, Acb_Num2Name(i), &fFound );
        assert( i == NameId && !fFound );
    }
    return pNames;
}
Vec_Int_t * Acb_VerilogSimpleLex( char * pFileName, Abc_Nam_t * pNames )
{
    Vec_Int_t * vBuffer = Vec_IntAlloc( 1000 );
    char * pBuffer = Extra_FileReadContents( pFileName );
    char * pToken;
    if ( pBuffer == NULL )
        return NULL;
    pToken = strtok( pBuffer, "  \n\r()," );
    while ( pToken )
    {
        Vec_IntPush( vBuffer, Abc_NamStrFindOrAdd(pNames, pToken, NULL) );
        pToken = strtok( NULL, "  \n\r(),;" );
    }
    ABC_FREE( pBuffer );
    return vBuffer;
}
int Acb_WireIsTarget( int Token, Abc_Nam_t * pNames )
{
    char * pStr = Abc_NamStr(pNames, Token);
    return pStr[0] == 't' && pStr[1] == '_';
}
void * Acb_VerilogSimpleParse( Vec_Int_t * vBuffer, Abc_Nam_t * pNames )
{
    void * pDesign = NULL;
    Vec_Int_t * vInputs  = Vec_IntAlloc(100);
    Vec_Int_t * vOutputs = Vec_IntAlloc(100);
    Vec_Int_t * vWires   = Vec_IntAlloc(100);
    Vec_Int_t * vTypes   = Vec_IntAlloc(100);
    Vec_Int_t * vFanins  = Vec_IntAlloc(100);
    Vec_Int_t * vCur = NULL;  
    int i, ModuleID, Token, Size, Count = 0;
    assert( Vec_IntEntry(vBuffer, 0) == ACB_MODULE );
    Vec_IntForEachEntryStart( vBuffer, Token, i, 2 )
    {
        if ( vCur == NULL && Token >= ACB_UNUSED )
            continue;
        if ( Token == ACB_ENDMODULE )
            break;
        if ( Token == ACB_INPUT )
            vCur = vInputs;
        else if ( Token == ACB_OUTPUT )
            vCur = vOutputs;
        else if ( Token == ACB_WIRE )
            vCur = vWires;
        else if ( Token >= ACB_BUF && Token <= ACB_XNOR )
        {
            Vec_IntPush( vTypes, Token );
            Vec_IntPush( vTypes, Vec_IntSize(vFanins) );
            vCur = vFanins;
        }
        else 
            Vec_IntPush( vCur, Token );
    }
    Vec_IntPush( vTypes, -1 );
    Vec_IntPush( vTypes, Vec_IntSize(vFanins) );
    // create design
    pDesign = Ndr_Create( Vec_IntEntry(vBuffer, 1) );
    ModuleID = Ndr_AddModule( pDesign, Vec_IntEntry(vBuffer, 1) );
    // create inputs
    Ndr_DataResize( pDesign, Vec_IntSize(vInputs) );
    Vec_IntForEachEntry( vInputs, Token, i )
        Ndr_DataPush( pDesign, NDR_INPUT, Token );
    Ndr_DataAddTo( pDesign, ModuleID-256, Vec_IntSize(vInputs) );
    Ndr_DataAddTo( pDesign, 0, Vec_IntSize(vInputs) );
    // create outputs
    Ndr_DataResize( pDesign, Vec_IntSize(vOutputs) );
    Vec_IntForEachEntry( vOutputs, Token, i )
        Ndr_DataPush( pDesign, NDR_OUTPUT, Token );
    Ndr_DataAddTo( pDesign, ModuleID-256, Vec_IntSize(vOutputs) );
    Ndr_DataAddTo( pDesign, 0, Vec_IntSize(vOutputs) );
    // create targets
    Ndr_DataResize( pDesign, Vec_IntSize(vWires) );
    Vec_IntForEachEntry( vWires, Token, i )
        if ( Acb_WireIsTarget(Token, pNames) )
            Ndr_DataPush( pDesign, NDR_TARGET, Token ), Count++;
    Ndr_DataAddTo( pDesign, ModuleID-256, Count );
    Ndr_DataAddTo( pDesign, 0, Count );
    // create nodes
    Vec_IntForEachEntry( vInputs, Token, i )
        Ndr_AddObject( pDesign, ModuleID, ABC_OPER_CI, 0, 0, 0, 0,   0, NULL,  1, &Token,   NULL  ); // no fanins
    if ( (Token = Abc_NamStrFind(pNames, "1\'b0")) )
        Ndr_AddObject( pDesign, ModuleID, ABC_OPER_CONST_F, 0, 0, 0, 0,   0, NULL,  1, &Token,   NULL  ); // no fanins
    if ( (Token = Abc_NamStrFind(pNames, "1\'b1")) )
        Ndr_AddObject( pDesign, ModuleID, ABC_OPER_CONST_T, 0, 0, 0, 0,   0, NULL,  1, &Token,   NULL  ); // no fanins
    Vec_IntForEachEntryDouble( vTypes, Token, Size, i ) 
        if ( Token > 0 )
        {
            int Output = Vec_IntEntry(vFanins, Size);
            int nFanins = Vec_IntEntry(vTypes, i+3) - Size - 1;
            int * pFanins = Vec_IntEntryP(vFanins, Size+1);
            Ndr_AddObject( pDesign, ModuleID, Acb_Type2Oper(Token), 0, 0, 0, 0, nFanins, pFanins, 1, &Output, NULL ); // many fanins
        }
    Vec_IntForEachEntry( vOutputs, Token, i )
        Ndr_AddObject( pDesign, ModuleID, ABC_OPER_CO, 0, 0, 0, 0,   1, &Token, 1, &Token,  NULL  ); // one fanin
    // cleanup
    Vec_IntFree( vInputs );
    Vec_IntFree( vOutputs );
    Vec_IntFree( vWires );
    Vec_IntFree( vTypes );
    Vec_IntFree( vFanins );
    return pDesign;
}

/**Function*************************************************************

  Synopsis    [Read weights of nodes from the weight file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acb_ReadWeightMap( char * pFileName, Abc_Nam_t * pNames )
{
    Vec_Int_t * vWeights = Vec_IntStartFull( Abc_NamObjNumMax(pNames) );
    char * pBuffer = Extra_FileReadContents( pFileName );
    char * pToken, * pNum;
    if ( pBuffer == NULL )
        return NULL;
    pToken = strtok( pBuffer, "  \n\r()," );
    pNum   = strtok( NULL, "  \n\r()," );
    while ( pToken )
    {
        int NameId = Abc_NamStrFind(pNames, pToken);
        int Number = atoi(pNum);
        if ( NameId <= 0 )
        {
            printf( "Cannot find name \"%s\" among node names of this network.\n", pToken );
            continue;
        }
        Vec_IntWriteEntry( vWeights, NameId, Number );
        pToken = strtok( NULL, "  \n\r(),;" );
        pNum = strtok( NULL, "  \n\r(),;" );
    }
    ABC_FREE( pBuffer );
    return vWeights;
}

/**Function*************************************************************

  Synopsis    [Create network from the intermediate representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Acb_Ntk_t * Acb_VerilogSimpleRead( char * pFileName, char * pFileNameW )
{
    extern Acb_Ntk_t * Acb_NtkFromNdr( char * pFileName, void * pModule, Abc_Nam_t * pNames, Vec_Int_t * vWeights, int nNameIdMax );
    Acb_Ntk_t * pNtk;
    Abc_Nam_t * pNames = Acb_VerilogStartNames();
    Vec_Int_t * vBuffer = Acb_VerilogSimpleLex( pFileName, pNames );
    void * pModule = vBuffer ? Acb_VerilogSimpleParse( vBuffer, pNames ) : NULL;
    Vec_Int_t * vWeights = pFileNameW ? Acb_ReadWeightMap( pFileNameW, pNames ) : NULL;
    if ( pFileName && pModule == NULL )
    {
        printf( "Cannot read input file \"%s\".\n", pFileName );
        return NULL;
    }
    if ( pFileNameW && vWeights == NULL )
    {
        printf( "Cannot read weight file \"%s\".\n", pFileNameW );
        return NULL;
    }
//    Ndr_ModuleWriteVerilog( "iccad17/unit1/test.v", pModule, pNameStrs );
    pNtk = Acb_NtkFromNdr( pFileName, pModule, pNames, vWeights, Abc_NamObjNumMax(pNames) );
    Ndr_Delete( pModule );
    Vec_IntFree( vBuffer );
    Vec_IntFreeP( &vWeights );
    Abc_NamDeref( pNames );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Write Verilog for sanity checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_VerilogSimpleWrite( Acb_Ntk_t * p, char * pFileName )
{
    int i, iObj, fFirst = 1;
    FILE * pFile = fopen( pFileName, "wb" ); 
    if ( pFile == NULL ) { printf( "Cannot open file \"%s\" for writing.\n", pFileName ); return; }

    fprintf( pFile, "\nmodule %s (\n  ", Acb_NtkName(p) );

    Acb_NtkForEachPi( p, iObj, i )
        fprintf( pFile, "%s, ", Acb_ObjNameStr(p, iObj) );
    fprintf( pFile, "\n  " );

    Acb_NtkForEachPo( p, iObj, i )
        fprintf( pFile, "%s%s", fFirst ? "":", ", Acb_ObjNameStr(p, iObj) ), fFirst = 0;
    fprintf( pFile, "\n);\n\n" );

    Acb_NtkForEachPi( p, iObj, i )
        fprintf( pFile, "  input %s;\n", Acb_ObjNameStr(p, iObj) );
    fprintf( pFile, "\n" );

    Acb_NtkForEachPo( p, iObj, i )
        fprintf( pFile, "  output %s;\n", Acb_ObjNameStr(p, iObj) );
    fprintf( pFile, "\n" );

    Acb_NtkForEachNode( p, iObj )
        if ( Acb_ObjFaninNum(p, iObj) > 0 )
            fprintf( pFile, "  wire %s;\n", Acb_ObjNameStr(p, iObj) );
    fprintf( pFile, "\n" );

    Acb_NtkForEachNode( p, iObj )
        if ( Acb_ObjFaninNum(p, iObj) > 0 )
        {
            int * pFanin, iFanin, k, start = ftell(pFile)+55;
            fprintf( pFile, "  %s (", Acb_Oper2Name( Acb_ObjType(p, iObj) ) );
            fprintf( pFile, " %s", Acb_ObjNameStr(p, iObj) );
            Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, k )
                //if ( iFanin == 0 ) fprintf( pFile, ", <zero>" ); else
                fprintf( pFile, ", %s", Acb_ObjNameStr(p, iFanin) );
            fprintf( pFile, " );" );
            if ( Acb_NtkHasObjWeights(p) && Acb_ObjWeight(p, iObj) > 0 )
                fprintf( pFile, " %*s // weight = %d", (int)(start-ftell(pFile)), "", Acb_ObjWeight(p, iObj) );
            fprintf( pFile, "\n" );
        }
        else // constant nodes
        {
            assert( Acb_ObjType(p, iObj) == ABC_OPER_CONST_F || Acb_ObjType(p, iObj) == ABC_OPER_CONST_T );
            fprintf( pFile, "  %s (", Acb_Oper2Name( ABC_OPER_BIT_BUF ) );
            fprintf( pFile, " 1\'b%d", Acb_ObjType(p, iObj) == ABC_OPER_CONST_T );
            fprintf( pFile, " );" );
        }

    fprintf( pFile, "\nendmodule\n\n" );
    fclose( pFile );
}







/**Function*************************************************************

  Synopsis    [Compute roots (PO nodes in the TFO of the targets in F).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_NtkFindRoots_rec( Acb_Ntk_t * p, int iObj, Vec_Bit_t * vBlock )
{
    int * pFanin, iFanin, i, Res = 0;
    if ( Acb_ObjIsTravIdPrev(p, iObj) )
        return 1;
    if ( Acb_ObjSetTravIdCur(p, iObj) )  
        return 0;
    assert( !Acb_ObjIsCi(p, iObj) );
    Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, i )
        Res |= Acb_NtkFindRoots_rec( p, iFanin, vBlock );
    if ( Res ) Acb_ObjSetTravIdPrev( p, iObj );
    if ( Res ) Vec_BitWriteEntry( vBlock, iObj, 1 );
    return Res;
}
Vec_Int_t * Acb_NtkFindRoots( Acb_Ntk_t * p, Vec_Int_t * vTargets, Vec_Bit_t ** pvBlock )
{
    int i, iObj;
    Vec_Int_t * vRoots = Vec_IntAlloc( 1000 );
    Vec_Bit_t * vBlock = Vec_BitStart( Acb_NtkObjNum(p) );
    *pvBlock = vBlock;
    // mark targets
    Acb_NtkIncTravId( p );
    assert( Vec_IntSize(vTargets) > 0 );
    Vec_IntForEachEntry( vTargets, iObj, i )
    {
        Acb_ObjSetTravIdCur( p, iObj );
        Vec_BitWriteEntry( vBlock, iObj, 1 );
    }
    // mark inputs
    Acb_NtkIncTravId( p );
    Acb_NtkForEachCi( p, iObj, i )
        Acb_ObjSetTravIdCur( p, iObj );
    // collect outputs reachable from targets
    Acb_NtkForEachCoDriver( p, iObj, i )
        if ( Acb_NtkFindRoots_rec(p, iObj, vBlock) )
            Vec_IntPush( vRoots, i );
    //Vec_IntPrint( vRoots );
    return vRoots;
}

/**Function*************************************************************

  Synopsis    [Compute support in the TFI of the roots.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkFindSupp_rec( Acb_Ntk_t * p, int iObj, Vec_Int_t * vSupp )
{
    int * pFanin, iFanin, i;
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    if ( Acb_ObjIsCi(p, iObj) )
        Vec_IntPush( vSupp, Acb_ObjCioId(p, iObj) );
    else
        Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, i )
            Acb_NtkFindSupp_rec( p, iFanin, vSupp );
}
Vec_Int_t * Acb_NtkFindSupp( Acb_Ntk_t * p, Vec_Int_t * vRoots )
{
    int i, iObj;
    Vec_Int_t * vSupp  = Vec_IntAlloc( 1000 );
    Acb_NtkIncTravId( p );
    Acb_NtkForEachCoDriverVec( vRoots, p, iObj, i )
        Acb_NtkFindSupp_rec( p, iObj, vSupp );
    Vec_IntSort( vSupp, 0 );
    //Vec_IntPrint( vSupp );
    return vSupp;
}

/**Function*************************************************************

  Synopsis    [Collect divisors whose support is completely contained in vSupp.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_NtkFindDivs_rec( Acb_Ntk_t * p, int iObj )
{
    int * pFanin, iFanin, i, Res = 1;
    if ( Acb_ObjIsTravIdPrev(p, iObj) )
        return 1;
    if ( Acb_ObjSetTravIdCur(p, iObj) )  
        return 0;
    if ( Acb_ObjIsCi(p, iObj) )
        return 0;
    Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, i )
        Res &= Acb_NtkFindDivs_rec( p, iFanin );
    if ( Res ) Acb_ObjSetTravIdPrev( p, iObj );
    return Res;
}
Vec_Int_t * Acb_NtkFindDivsCis( Acb_Ntk_t * p, Vec_Int_t * vSupp )
{
    int i, iObj;
    Vec_Int_t * vDivs = Vec_IntAlloc( Vec_IntSize(vSupp) );
    Acb_NtkForEachCiVec( vSupp, p, iObj, i )
    {
        assert( Acb_ObjWeight(p, iObj) > 0 );
        Vec_IntPush( vDivs, iObj );
    }
    printf( "Divisors are %d support variables (CIs in the TFO of the targets).\n", Vec_IntSize(vSupp) );
    return vDivs;
}
Vec_Int_t * Acb_NtkFindDivs( Acb_Ntk_t * p, Vec_Int_t * vSupp, Vec_Bit_t * vBlock )
{
    int fPrintWeights = 0;
    int nDivLimit = 3000;
    int i, iObj;
    Vec_Int_t * vDivs = Vec_IntAlloc( 1000 );
    // mark inputs
    Acb_NtkIncTravId( p );
    Acb_NtkForEachCiVec( vSupp, p, iObj, i )
    {
        Acb_ObjSetTravIdCur( p, iObj );
        if ( Acb_ObjWeight(p, iObj) > 0 )
            Vec_IntPush( vDivs, iObj );
    }
    // collect nodes whose support is contained in vSupp
    Acb_NtkIncTravId( p );
    Acb_NtkForEachNode( p, iObj )
        if ( !Vec_BitEntry(vBlock, iObj) && Acb_ObjWeight(p, iObj) > 0 && Acb_NtkFindDivs_rec(p, iObj) )
            Vec_IntPush( vDivs, iObj );
    // sort divisors by cost (first cheap ones; later expensive ones)
    Vec_IntSelectSortCost( Vec_IntArray(vDivs), Vec_IntSize(vDivs), &p->vObjWeight );
    //Vec_IntPrint( vDivs );
    nDivLimit = Abc_MinInt( Vec_IntSize(vDivs), nDivLimit );
    if ( fPrintWeights )
    {
//        Vec_IntForEachEntryStop( vDivs, iObj, i, nDivLimit )
//            printf( "%d:%d (w=%d)   ", i, iObj, Vec_IntEntry(&p->vObjWeight, iObj) );
//        printf( "\n" );

        printf( "    : " );
        Vec_IntForEachEntryStop( vDivs, iObj, i, nDivLimit )
            printf( "%d", (Vec_IntEntry(&p->vObjWeight, iObj) / 100) % 10 );
        printf( "\n" );
        printf( "    : " );
        Vec_IntForEachEntryStop( vDivs, iObj, i, nDivLimit )
            printf( "%d", (Vec_IntEntry(&p->vObjWeight, iObj) / 10) % 10 );
        printf( "\n" );
        printf( "    : " );
        Vec_IntForEachEntryStop( vDivs, iObj, i, nDivLimit )
            printf( "%d", (Vec_IntEntry(&p->vObjWeight, iObj) / 1) % 10 );
        printf( "\n" );
    }
    printf( "Reducing divisor set from %d to ", Vec_IntSize(vDivs) );
    Vec_IntShrink( vDivs, nDivLimit );
    printf( "%d.\n", Vec_IntSize(vDivs) );
    return vDivs;
}

/**Function*************************************************************

  Synopsis    [Compute support and internal nodes in the TFI of the roots.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkFindNodes_rec( Acb_Ntk_t * p, int iObj, Vec_Int_t * vNodes )
{
    int * pFanin, iFanin, i;
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    if ( Acb_ObjIsCi(p, iObj) )
        return;
    Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, i )
        Acb_NtkFindNodes_rec( p, iFanin, vNodes );
    assert( !Acb_ObjIsCo(p, iObj) );
    Vec_IntPush( vNodes, iObj );
}
Vec_Int_t * Acb_NtkFindNodes( Acb_Ntk_t * p, Vec_Int_t * vRoots, Vec_Int_t * vDivs )
{
    int i, iObj;
    Vec_Int_t * vNodes = Vec_IntAlloc( 1000 );
    Acb_NtkIncTravId( p );
    Acb_NtkForEachCoDriverVec( vRoots, p, iObj, i )
        Acb_NtkFindNodes_rec( p, iObj, vNodes );
    if ( vDivs )
        Vec_IntForEachEntry( vDivs, iObj, i )
            Acb_NtkFindNodes_rec( p, iObj, vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Derive AIG for one network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_ObjToGia( Gia_Man_t * pNew, Acb_Ntk_t * p, int iObj, Vec_Int_t * vTemp )
{
    int * pFanin, iFanin, k, Type, Res;
    assert( !Acb_ObjIsCio(p, iObj) );
    Vec_IntClear( vTemp );
    Acb_ObjForEachFaninFast( p, iObj, pFanin, iFanin, k )
        Vec_IntPush( vTemp, Acb_ObjCopy(p, iFanin) );
    Type = Acb_ObjType( p, iObj );
    if ( Type == ABC_OPER_CONST_F ) 
        return 0;
    if ( Type == ABC_OPER_CONST_T ) 
        return 1;
    if ( Type == ABC_OPER_BIT_BUF ) 
        return Vec_IntEntry(vTemp, 0);
    if ( Type == ABC_OPER_BIT_INV ) 
        return Abc_LitNot( Vec_IntEntry(vTemp, 0) );
    if ( Type == ABC_OPER_BIT_AND || Type == ABC_OPER_BIT_NAND )
    {
        Res = 1;
        Vec_IntForEachEntry( vTemp, iFanin, k )
            Res = Gia_ManHashAnd( pNew, Res, iFanin );
        return Abc_LitNotCond( Res, Type == ABC_OPER_BIT_NAND );
    }
    if ( Type == ABC_OPER_BIT_OR || Type == ABC_OPER_BIT_NOR )
    {
        Res = 0;
        Vec_IntForEachEntry( vTemp, iFanin, k )
            Res = Gia_ManHashOr( pNew, Res, iFanin );
        return Abc_LitNotCond( Res, Type == ABC_OPER_BIT_NOR );
    }
    if ( Type == ABC_OPER_BIT_XOR || Type == ABC_OPER_BIT_NXOR )
    {
        Res = 0;
        Vec_IntForEachEntry( vTemp, iFanin, k )
            Res = Gia_ManHashXor( pNew, Res, iFanin );
        return Abc_LitNotCond( Res, Type == ABC_OPER_BIT_NXOR );
    }
    assert( 0 );
    return -1;
}
Gia_Man_t * Acb_NtkToGia( Acb_Ntk_t * p, Vec_Int_t * vSupp, Vec_Int_t * vNodes, Vec_Int_t * vRoots, Vec_Int_t * vDivs, Vec_Int_t * vTargets )
{
    Gia_Man_t * pNew, * pOne;
    Vec_Int_t * vFanins;
    int i, iObj;
    pNew = Gia_ManStart( 2 * Acb_NtkObjNum(p) + 1000 );
    Gia_ManHashAlloc( pNew );
    Acb_NtkCleanObjCopies( p );
    // create primary inputs
    Acb_NtkForEachCiVec( vSupp, p, iObj, i )
        Acb_ObjSetCopy( p, iObj, Gia_ManAppendCi(pNew) );
    // add targets as primary inputs
    if ( vTargets )
        Vec_IntForEachEntry( vTargets, iObj, i )
            Acb_ObjSetCopy( p, iObj, Gia_ManAppendCi(pNew) );
    // bit-blast internal nodes
    vFanins = Vec_IntAlloc( 4 );
    Vec_IntForEachEntry( vNodes, iObj, i )
        if ( Acb_ObjCopy(p, iObj) == -1 ) // skip targets assigned above
            Acb_ObjSetCopy( p, iObj, Acb_ObjToGia(pNew, p, iObj, vFanins) );
    Vec_IntFree( vFanins );
    // create primary outputs
    Acb_NtkForEachCoDriverVec( vRoots, p, iObj, i )
        Gia_ManAppendCo( pNew, Acb_ObjCopy(p, iObj) );
    // add divisor as primary outputs (if the divisors are not primary inputs)
    if ( vDivs && Vec_IntSize(vDivs) > Vec_IntSize(vSupp) ) 
        Vec_IntForEachEntry( vDivs, iObj, i )
            Gia_ManAppendCo( pNew, Acb_ObjCopy(p, iObj) );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pOne = pNew );
    Gia_ManStop( pOne );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derive miter of two AIGs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Acb_CreateMiter( Gia_Man_t * pF, Gia_Man_t * pG )
{
    Gia_Man_t * pNew, * pOne;
    Gia_Obj_t * pObj;
    int i, iMiter = 0, iXor;
    Gia_ManFillValue( pF );
    Gia_ManFillValue( pG );
    pNew = Gia_ManStart( Gia_ManObjNum(pF) + Gia_ManObjNum(pF) + 1000 );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(pF)->Value = 0;
    Gia_ManConst0(pG)->Value = 0;
    Gia_ManForEachCi( pF, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachCi( pG, pObj, i )
        pObj->Value = Gia_ManCi(pF, i)->Value;
    Gia_ManForEachAnd( pF, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachAnd( pG, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( pG, pObj, i )
    {
        iXor = Gia_ManHashXor( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin0Copy(Gia_ManCo(pF, i)) );
        iMiter = Gia_ManHashOr( pNew, iMiter, iXor );
    }
    Gia_ManAppendCo( pNew, iMiter );
    Gia_ManForEachCo( pF, pObj, i )
        if ( i >= Gia_ManCoNum(pG) )
            Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pOne = pNew );
    Gia_ManStop( pOne );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#define NWORDS 64

void Vec_IntPermute( Vec_Int_t * p )
{
    int i, nSize = Vec_IntSize( p );
    int * pArray = Vec_IntArray( p );
    srand( time(NULL) );
    for ( i = 0; i < nSize; i++ )
    {
        int j = rand()%nSize;
        ABC_SWAP( int, pArray[i], pArray[j] );
    }
}

void Acb_PrintPatterns( Vec_Wrd_t * vPats, int nPats, Vec_Int_t * vWeights )
{
    int i, k, Entry, nDivs = Vec_IntSize(vWeights);
    printf( "    : " );
    Vec_IntForEachEntry( vWeights, Entry, i )
        printf( "%d", (Entry / 100) % 10 );
    printf( "\n" );
    printf( "    : " );
    Vec_IntForEachEntry( vWeights, Entry, i )
        printf( "%d", (Entry / 10) % 10 );
    printf( "\n" );
    printf( "    : " );
    Vec_IntForEachEntry( vWeights, Entry, i )
        printf( "%d", (Entry / 1) % 10 );
    printf( "\n" );
    printf( "\n" );

    printf( "    : " );
    for ( i = 0; i < nDivs; i++ )
        printf( "%d", (i / 100) % 10 );
    printf( "\n" );
    printf( "    : " );
    for ( i = 0; i < nDivs; i++ )
        printf( "%d", (i / 10) % 10 );
    printf( "\n" );
    printf( "    : " );
    for ( i = 0; i < nDivs; i++ )
        printf( "%d", i % 10 );
    printf( "\n" );
    printf( "\n" );

    for ( k = 0; k < nPats; k++ )
    {
        printf( "%3d : ", k );
        for ( i = 0; i < nDivs; i++ )
            printf( "%c", Abc_TtGetBit(Vec_WrdEntryP(vPats, NWORDS*i), k) ? '*' : '|' );
        printf( "\n" );
    }
    printf( "\n" );
}

Vec_Int_t * Acb_DeriveWeights( Vec_Int_t * vDivs, Acb_Ntk_t * pNtkF )
{
    int i, iDiv;
    Vec_Int_t * vWeights = Vec_IntAlloc( Vec_IntSize(vDivs) );
    Vec_IntForEachEntry( vDivs, iDiv, i )
        Vec_IntPush( vWeights, Vec_IntEntry(&pNtkF->vObjWeight, iDiv) );
    return vWeights;
}
int Acb_ComputeSuppCost( Vec_Int_t * vSupp, Vec_Int_t * vWeights, int iFirstDiv )
{
    int i, Entry, Cost = 0;
    Vec_IntForEachEntry( vSupp, Entry, i )
        Cost += Vec_IntEntry( vWeights, Abc_Lit2Var(Entry) - iFirstDiv );
    return Cost;
}
Vec_Int_t * Acb_FindSupportStart( sat_solver * pSat, int iFirstDiv, Vec_Int_t * vWeights, Vec_Wrd_t ** pvPats, int * piPats )
{
    int i, status, nDivs = Vec_IntSize(vWeights);
    Vec_Int_t * vSupp = Vec_IntAlloc( 100 );
    Vec_Wrd_t * vPats = Vec_WrdStart( NWORDS * nDivs );
    int iPat = 0;
    while ( 1 )
    {
        int fFound = 0;
        // try one run
        status = sat_solver_solve( pSat, Vec_IntArray(vSupp), Vec_IntLimit(vSupp), 0, 0, 0, 0 );
        if ( status == l_False )
            break;
        assert( status == l_True );
        // collect pattern
        for ( i = 0; i < nDivs; i++ )
        {
            if ( sat_solver_var_value(pSat, iFirstDiv+i) == 0 )
                continue;
            Abc_TtSetBit( Vec_WrdEntryP(vPats, NWORDS*i), iPat );
            if ( fFound )
                continue;
            // process new divisor
            Vec_IntPush( vSupp, Abc_Var2Lit(iFirstDiv+i, 1) );
            //printf( "Selecting divisor %d with weight %d\n", i, Vec_IntEntry(vWeights, i) );
            fFound = 1;
        }
        assert( fFound );
        iPat++;
    }
    *piPats = iPat;
    *pvPats = vPats;
    Vec_IntSort( vSupp, 0 );
    return vSupp;
}
int Acb_FindArgMaxUnderMask( Vec_Wrd_t * vPats, word Mask[NWORDS], Vec_Int_t * vWeights, int nPats )
{
    int nDivs = Vec_WrdSize(vPats)/NWORDS;
    int nWords = Abc_Bit6WordNum(nPats);
    int i, iBest = -1;
    int Cost, CostBest = -1;
    for ( i = 0; i < nDivs; i++ )
    {
        word * pPat = Vec_WrdEntryP(vPats, NWORDS*i);
        Cost = Abc_TtCountOnesVecMask(Mask, pPat, nWords, 0);
        if ( CostBest < Cost )
//        if ( CostBest == -1 || (float)CostBest/Cost < 0.6*(float)Vec_IntEntry(vWeights, iBest)/Vec_IntEntry(vWeights, i) )
//        if ( CostBest == -1 || (float)CostBest/Cost < 0.67*(float)Vec_IntEntry(vWeights, iBest)/Vec_IntEntry(vWeights, i) )
        {
            CostBest = Cost;
            iBest = i;
        }
    }
    return iBest;
}
int Acb_FindArgMaxUnderMask2( Vec_Wrd_t * vPats, word Mask[NWORDS], Vec_Int_t * vWeights, int nPats )
{
    int nDivs = Vec_WrdSize(vPats)/NWORDS;
    int i, b, iBest = -1;
    int Cost, CostBest = -1;
    // count how many times each of them appears
    Vec_Int_t * vCounts = Vec_IntStart(nPats);
    for ( i = 0; i < nDivs; i++ )
    {
        word * pPat = Vec_WrdEntryP(vPats, NWORDS*i);
        for ( b = 0; b < nPats; b++ )
            if ( Abc_TtGetBit(pPat, b) )
                Vec_IntAddToEntry( vCounts, b, 1 );
    }
    for ( i = 0; i < nDivs; i++ )
    {
        word * pPat = Vec_WrdEntryP(vPats, NWORDS*i);
//        Cost = Abc_TtCountOnesVecMask(Mask, pPat, NWORDS, 0);
        Cost = 0;
        for ( b = 0; b < nPats; b++ )
            if ( Abc_TtGetBit(pPat, b) && Abc_TtGetBit(Mask, b) )
                Cost += 1000000/Vec_IntEntry(vCounts, b);
        if ( CostBest < Cost )
        {
            CostBest = Cost;
            iBest = i;
        }
    }
    Vec_IntFree( vCounts );
    return iBest;
}

Vec_Int_t * Acb_FindSupportNext( sat_solver * pSat, int iFirstDiv, Vec_Int_t * vWeights, Vec_Wrd_t * vPats, int * pnPats )
{
    int i, status, nDivs = Vec_IntSize(vWeights);
    Vec_Int_t * vSupp = Vec_IntAlloc( 100 );
    word * pMask, Mask[NWORDS]; Abc_TtConst( Mask, NWORDS, 1 );
    while ( 1 )
    {
        int iDivBest = Acb_FindArgMaxUnderMask( vPats, Mask, vWeights, *pnPats ); 
        Vec_IntPush( vSupp, Abc_Var2Lit(iFirstDiv+iDivBest, 1) );
        //printf( "Selecting divisor %d with weight %d\n", iDivBest, Vec_IntEntry(vWeights, iDivBest) );
//        Mask &= ~Vec_WrdEntry( vPats, iDivBest );
        pMask = Vec_WrdEntryP( vPats, NWORDS*iDivBest );
        Abc_TtAndSharp( Mask, Mask, pMask, NWORDS, 1 );

        // try one run
        status = sat_solver_solve( pSat, Vec_IntArray(vSupp), Vec_IntLimit(vSupp), 0, 0, 0, 0 );
        if ( status == l_False )
            break;
        assert( status == l_True );
        // collect pattern
        for ( i = 0; i < nDivs; i++ )
        {
            if ( sat_solver_var_value(pSat, iFirstDiv+i) == 0 )
                continue;
            Abc_TtSetBit( Vec_WrdEntryP(vPats, NWORDS*i), *pnPats );
        }
        (*pnPats)++;
        if ( *pnPats == NWORDS*64 )
        {
            Vec_IntFreeP( &vSupp );
            return NULL;
        }
        assert( *pnPats < NWORDS*64 );
        //Acb_PrintPatterns( vPats, *pnPats, vWeights );
        //i = i;
    }
    Vec_IntSort( vSupp, 0 );
    return vSupp;
}
Vec_Int_t * Acb_FindSupportMinOne( sat_solver * pSat, int iFirstDiv, Vec_Wrd_t * vPats, int * pnPats, Vec_Int_t * vSupp, int iVar )
{
    int i, iLit, status;
    int nDivs = Vec_WrdSize(vPats)/NWORDS;
    Vec_Int_t * vLits = Vec_IntAlloc( Vec_IntSize(vSupp) );
    Vec_IntForEachEntry( vSupp, iLit, i )
        if ( i != iVar )
            Vec_IntPush( vLits, iLit );
    // try one run
    status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits), 0, 0, 0, 0 );
    if ( status == l_False )
        return vLits;
    Vec_IntFree( vLits );
    assert( status == l_True );
    // collect pattern
    for ( i = 0; i < nDivs; i++ )
    {
        if ( sat_solver_var_value(pSat, iFirstDiv+i) == 0 )
            continue;
        Abc_TtSetBit( Vec_WrdEntryP(vPats, NWORDS*i), *pnPats );
    }
    (*pnPats)++;
    if ( *pnPats == NWORDS*64 )
        return NULL;
    return vSupp;
}
Vec_Int_t * Acb_FindSupportMin( sat_solver * pSat, int iFirstDiv, Vec_Wrd_t * vPats, int * pnPats, Vec_Int_t * vSuppStart )
{
    Vec_Int_t * vTemp, * vSupp = Vec_IntDup( vSuppStart ); int i;
    for ( i = Vec_IntSize(vSupp)-1; i >= 0; i-- )
    {
        vSupp = Acb_FindSupportMinOne( pSat, iFirstDiv, vPats, pnPats, vTemp = vSupp, i );
        if ( vTemp != vSupp )
            Vec_IntFree( vTemp );
        if ( vSupp == NULL )
            return NULL;
    }
    return vSupp;
}
void Acb_FindReplace( sat_solver * pSat, int iFirstDiv, Vec_Int_t * vWeights, Vec_Wrd_t * vPats, int nPats, Vec_Int_t * vSupp )
{
    int i, k, iLit, iLit2, status, nWords = Abc_Bit6WordNum(nPats);
    word Covered[NWORDS], Both[NWORDS], Mask[NWORDS], * pMask; 
    assert( nWords <= NWORDS );
    // prepare constant pattern
    Abc_TtConst( Mask, nWords, 0 );
    for ( i = 0; i < nPats; i++ )
        Abc_TtSetBit( Mask, i );
    // try to replace each by a cheaper one
    Vec_IntForEachEntry( vSupp, iLit, i )
    {
        int iDiv = Abc_Lit2Var(iLit) - iFirstDiv;
        // collect covered except by this one
        Abc_TtConst( Covered, nWords, 0 );
        Vec_IntForEachEntry( vSupp, iLit2, k )
        {
            if ( iLit2 == iLit )
                continue;
            pMask = Vec_WrdEntryP( vPats, NWORDS*(Abc_Lit2Var(iLit2) - iFirstDiv) );
            Abc_TtOr( Covered, Covered, pMask, nWords );
        }
        // consider any cheaper ones that this one
        for ( k = 0; k < iDiv; k++ )
        {
            if ( Vec_IntEntry(vWeights, k) == Vec_IntEntry(vWeights, iDiv) )
                continue;
            assert( Vec_IntEntry(vWeights, k) < Vec_IntEntry(vWeights, iDiv) );
            pMask = Vec_WrdEntryP( vPats, NWORDS*k );
            // check if it covers the remaining ones
            Abc_TtOr( Both, Covered, pMask, nWords );
            if ( !Abc_TtEqual(Both, Mask, nWords) )
                continue;
            // try this one
            Vec_IntWriteEntry( vSupp, i, Abc_Var2Lit(iFirstDiv+k, 1) );
            status = sat_solver_solve( pSat, Vec_IntArray(vSupp), Vec_IntLimit(vSupp), 0, 0, 0, 0 );
            if ( status == l_False ) // success
            {
                //printf( "Replacing %d(%d) by %d(%d) with const difference %d.\n",
                //    iDiv, Vec_IntEntry(vWeights, iDiv), k, Vec_IntEntry(vWeights, k), 
                //    Vec_IntEntry(vWeights, iDiv) - Vec_IntEntry(vWeights, k) );
                break;
            }
            Vec_IntWriteEntry( vSupp, i, iLit );
        }
    }
}

Vec_Int_t * Acb_FindSupport( sat_solver * pSat, int iFirstDiv, Vec_Int_t * vWeights, Vec_Int_t * vSuppStart, int TimeOut )
{
    abctime clkLimit = TimeOut * CLOCKS_PER_SEC + Abc_Clock();
    Vec_Wrd_t * vPats = NULL;
    int nPats = 0;
    Vec_Int_t * vSuppBest, * vSupp;//, * vTemp;
    int CostBest, Cost;
    int Iter;

    // find initial best
    CostBest = Acb_ComputeSuppCost( vSuppStart, vWeights, iFirstDiv );
    vSuppBest = Vec_IntDup( vSuppStart );
    printf( "Starting cost = %d.\n", CostBest );

    // interatively find the one with the most ones in the uncovered rows
    for ( Iter = 0; Iter < 200; Iter++ )
    {
        if ( Abc_Clock() > clkLimit )
        {
            Vec_IntFree( vSuppBest );
            Vec_WrdFree( vPats );
            return NULL;
        }
        if ( Iter == 0 )
            vSupp = Acb_FindSupportStart( pSat, iFirstDiv, vWeights, &vPats, &nPats );
        else
            vSupp = Acb_FindSupportNext( pSat, iFirstDiv, vWeights, vPats, &nPats );
        if ( vSupp == NULL )
            break;
        //vSupp = Acb_FindSupportMin( pSat, iFirstDiv, vPats, &nPats, vTemp = vSupp );
        //Vec_IntFree( vTemp );
        if ( vSupp == NULL )
            break;
        Cost = Acb_ComputeSuppCost( vSupp, vWeights, iFirstDiv );
        //Acb_PrintPatterns( vPats, nPats, vWeights );
        if ( CostBest > Cost )
        {
            CostBest = Cost;
            ABC_SWAP( Vec_Int_t *, vSuppBest, vSupp );
            printf( "Iter %4d:  Next cost = %d.  ", Iter, Cost );
            printf( "Updating best solution.\n" );
        }
        Vec_IntFree( vSupp );
    }
    Acb_FindReplace( pSat, iFirstDiv, vWeights, vPats, nPats, vSuppBest );

    //printf( "Number of patterns = %d.\n", nPats );
    Vec_WrdFree( vPats );
    return vSuppBest;
}

/**Function*************************************************************

  Synopsis    [Compute the best support of the targets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acb_DerivePatchSupport( Cnf_Dat_t * pCnf, int iTar, int nTargets, int nCoDivs, Vec_Int_t * vDivs, Acb_Ntk_t * pNtkF, Vec_Int_t * vSuppOld, int TimeOut )
{
    Vec_Int_t * vSupp = Vec_IntAlloc( 100 );
    int i, Lit;
    int iCoVarBeg = 1;
    int iCiVarBeg = pCnf->nVars - nTargets;
    sat_solver * pSat = sat_solver_new();
    sat_solver_setnvars( pSat, 2 * pCnf->nVars + nCoDivs );
    // add clauses
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            return NULL;
    // add output clause
    Lit = Abc_Var2Lit( iCoVarBeg, 0 );
    if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
        return NULL;
    // add clauses
    pCnf->pMan = NULL;
    Cnf_DataLift( pCnf, pCnf->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            return NULL;
    Cnf_DataLift( pCnf, -pCnf->nVars );
    // add output clause
    Lit = Abc_Var2Lit( iCoVarBeg+pCnf->nVars, 0 );
    if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
        return NULL;
    // create XORs for targets
    // add negative literal
    Lit = Abc_Var2Lit( iCiVarBeg + iTar, 1 );
    if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
        return NULL;
    // add positive literal
    Lit = Abc_Var2Lit( iCiVarBeg+pCnf->nVars + iTar, 0 );
    if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
        return NULL;
    // create XORs for divisors
    if ( nCoDivs > 0 )
    {
        abctime clk = Abc_Clock();
        int fUseMinAssump = 1;
        int iLit, nSuppNew, status;
        int iDivVar = 2 * pCnf->nVars;
        int pLits[2];
        int j = 0, iDivOld;
        Vec_IntClear( vSupp );
        if ( vSuppOld )
        {
            // start with predefined support
            Vec_IntForEachEntry( vSuppOld, iDivOld, j )
            {
                int iVar0 = iCoVarBeg+1+iDivOld;
                int iVar1 = iCoVarBeg+1+iDivOld+pCnf->nVars;
                //printf( "Selecting predefined divisor %d with weight %d\n", 
                //    iDivOld, Vec_IntEntry(&pNtkF->vObjWeight, Vec_IntEntry(vDivs, iDivOld)) );
                // add equality clauses
                pLits[0] = Abc_Var2Lit( iVar0, 0 );
                pLits[1] = Abc_Var2Lit( iVar1, 1 );
                if ( !sat_solver_addclause( pSat, pLits, pLits+2 ) )
                {
                    printf( "Unsat is detected earlier.\n" );
                    status = l_False;
                    break;
                }
                pLits[0] = Abc_Var2Lit( iVar0, 1 );
                pLits[1] = Abc_Var2Lit( iVar1, 0 );
                if ( !sat_solver_addclause( pSat, pLits, pLits+2 ) )
                {
                    printf( "Unsat is detected earlier.\n" );
                    status = l_False;
                    break;
                }
            }
        }
        if ( vSuppOld == NULL || j == Vec_IntSize(vSuppOld) )
        {
            for ( i = 0; i < nCoDivs; i++ )
            {
                sat_solver_add_xor( pSat, iDivVar+i, iCoVarBeg+1+i, iCoVarBeg+1+i+pCnf->nVars, 0 );
                Vec_IntPush( vSupp, Abc_Var2Lit(iDivVar+i, 1) );
            }
            // try one run
            if ( TimeOut ) sat_solver_set_runtime_limit( pSat, TimeOut * CLOCKS_PER_SEC + Abc_Clock() );
            status = sat_solver_solve( pSat, Vec_IntArray(vSupp), Vec_IntLimit(vSupp), 0, 0, 0, 0 );
            if ( TimeOut ) sat_solver_set_runtime_limit( pSat, 0 );
            if ( status != l_False )
            {
                printf( "Support computation timed out after %d sec.\n", TimeOut );
                sat_solver_delete( pSat );
                Vec_IntFree( vSupp );
                return NULL;
            }
            assert( status == l_False );
            printf( "Proved that the problem has a solution.  " );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            // find minimum subset
            if ( fUseMinAssump )
            {
                // solve in a standard way
                abctime clk = Abc_Clock();
                nSuppNew = sat_solver_minimize_assumptions( pSat, Vec_IntArray(vSupp), Vec_IntSize(vSupp), 0 );
                Vec_IntShrink( vSupp, nSuppNew );
                Vec_IntSort( vSupp, 0 );
                printf( "Found one feasible set of %d divisors.  ", Vec_IntSize(vSupp) );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

                // perform minimization
                if ( Vec_IntSize(vSupp) > 0 )
                {
                    abctime clk = Abc_Clock();
                    Vec_Int_t * vTemp, * vWeights = Acb_DeriveWeights( vDivs, pNtkF );
                    vSupp = Acb_FindSupport( pSat, iDivVar, vWeights, vTemp = vSupp, TimeOut );
                    Vec_IntFree( vWeights );
                    Vec_IntFree( vTemp );
                    if ( vSupp == NULL )
                    {
                        printf( "Support minimization timed out after %d sec.\n", TimeOut );
                        sat_solver_delete( pSat );
                        return NULL;
                    }
                    printf( "Minimized support to %d supp vars.  ", Vec_IntSize(vSupp) );
                    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
                }
            }
            else
            {
                int * pFinal, nFinal = sat_solver_final( pSat, &pFinal );
                printf( "AnalyzeFinal returned %d (out of %d).\n", nFinal, Vec_IntSize(vSupp) );
                Vec_IntClear( vSupp ); 
                for ( i = 0; i < nFinal; i++ )
                    Vec_IntPush( vSupp, Abc_LitNot(pFinal[i]) );
                // try one run
                status = sat_solver_solve( pSat, Vec_IntArray(vSupp), Vec_IntLimit(vSupp), 0, 0, 0, 0 );
                assert( status == l_False );
                // try again
                nFinal = sat_solver_final( pSat, &pFinal );
                printf( "AnalyzeFinal returned %d (out of %d).\n", nFinal, Vec_IntSize(vSupp) );
            }
            // remap them into numbers
            Vec_IntForEachEntry( vSupp, iLit, i )
                Vec_IntWriteEntry( vSupp, i, Abc_Lit2Var(iLit)-iDivVar );
            Vec_IntSort( vSupp, 0 );
        }
    }
    sat_solver_delete( pSat );
    if ( vSupp ) Vec_IntSort( vSupp, 0 );
    return vSupp;
}

static inline int satoko_add_xor( satoko_t * pSat, int iVarA, int iVarB, int iVarC, int fCompl )
{
    int Lits[3];
    int Cid;
    assert( iVarA >= 0 && iVarB >= 0 && iVarC >= 0 );

    Lits[0] = toLitCond( iVarA, !fCompl );
    Lits[1] = toLitCond( iVarB, 1 );
    Lits[2] = toLitCond( iVarC, 1 );
    Cid = satoko_add_clause( pSat, Lits, 3 );
    assert( Cid );

    Lits[0] = toLitCond( iVarA, !fCompl );
    Lits[1] = toLitCond( iVarB, 0 );
    Lits[2] = toLitCond( iVarC, 0 );
    Cid = satoko_add_clause( pSat, Lits, 3 );
    assert( Cid );

    Lits[0] = toLitCond( iVarA, fCompl );
    Lits[1] = toLitCond( iVarB, 1 );
    Lits[2] = toLitCond( iVarC, 0 );
    Cid = satoko_add_clause( pSat, Lits, 3 );
    assert( Cid );

    Lits[0] = toLitCond( iVarA, fCompl );
    Lits[1] = toLitCond( iVarB, 0 );
    Lits[2] = toLitCond( iVarC, 1 );
    Cid = satoko_add_clause( pSat, Lits, 3 );
    assert( Cid );
    return 4;
}
Vec_Int_t * Acb_DerivePatchSupportS( Cnf_Dat_t * pCnf, int nCiTars, int nCoDivs, Vec_Int_t * vDivs, Acb_Ntk_t * pNtkF, Vec_Int_t * vSuppOld, int TimeOut )
{
    Vec_Int_t * vSupp = Vec_IntAlloc( 100 );
    int i, Lit;
    int iCoVarBeg = 1;
    int iCiVarBeg = pCnf->nVars - nCiTars;
    satoko_t * pSat = satoko_create();
    satoko_setnvars( pSat, 2 * pCnf->nVars + nCiTars + nCoDivs );
    satoko_options(pSat)->no_simplify = 1;
    // add clauses
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !satoko_add_clause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1]-pCnf->pClauses[i] ) )
            return NULL;
    // add output clause
    Lit = Abc_Var2Lit( iCoVarBeg, 0 );
    if ( !satoko_add_clause( pSat, &Lit, 1 ) )
        return NULL;
    // add clauses
    pCnf->pMan = NULL;
    Cnf_DataLift( pCnf, pCnf->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !satoko_add_clause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1]-pCnf->pClauses[i] ) )
            return NULL;
    Cnf_DataLift( pCnf, -pCnf->nVars );
    // add output clause
    Lit = Abc_Var2Lit( iCoVarBeg+pCnf->nVars, 0 );
    if ( !satoko_add_clause( pSat, &Lit, 1 ) )
        return NULL;
    // create XORs for targets
    if ( nCiTars > 0 )
    {
/*
        int iXorVar = 2 * pCnf->nVars;
        int Lit;
        Vec_IntClear( vSupp );
        for ( i = 0; i < nCiTars; i++ )
        {
            satoko_add_xor( pSat, iXorVar+i, iCiVarBeg+i, iCiVarBeg+i+pCnf->nVars, 0 );
            Vec_IntPush( vSupp, Abc_Var2Lit(iXorVar+i, 0) );
        }
        if ( !satoko_add_clause( pSat, Vec_IntArray(vSupp), Vec_IntSize(vSupp) ) )
            return NULL;
*/
        // add negative literal
        Lit = Abc_Var2Lit( iCiVarBeg, 1 );
        if ( !satoko_add_clause( pSat, &Lit, 1 ) )
            return NULL;
        // add positive literal
        Lit = Abc_Var2Lit( iCiVarBeg+pCnf->nVars, 0 );
        if ( !satoko_add_clause( pSat, &Lit, 1 ) )
            return NULL;
    }
    // create XORs for divisors
    if ( nCoDivs > 0 )
    {
        abctime clk = Abc_Clock();
        int fUseMinAssump = 1;
        int iLit, status, nSuppNew;
        int iDivVar = 2 * pCnf->nVars + nCiTars;
        Vec_IntClear( vSupp );
        for ( i = 0; i < nCoDivs; i++ )
        {
            satoko_add_xor( pSat, iDivVar+i, iCoVarBeg+1+i, iCoVarBeg+1+i+pCnf->nVars, 0 );
            Vec_IntPush( vSupp, Abc_Var2Lit(iDivVar+i, 1) );
/*                
            pLits[0] = Abc_Var2Lit(iCoVarBeg+1+i,             1);
            pLits[1] = Abc_Var2Lit(iCoVarBeg+1+i+pCnf->nVars, 0);
            pLits[2] = Abc_Var2Lit(iDivVar+i,                 1);
            if ( !satoko_add_clause( pSat, pLits, 3 ) )
                assert( 0 );

            pLits[0] = Abc_Var2Lit(iCoVarBeg+1+i,             0);
            pLits[1] = Abc_Var2Lit(iCoVarBeg+1+i+pCnf->nVars, 1);
            pLits[2] = Abc_Var2Lit(iDivVar+i,                 1);
            if ( !satoko_add_clause( pSat, pLits, 3 ) )
                assert( 0 );

            Vec_IntPush( vSupp, Abc_Var2Lit(iDivVar+i, 0) );
*/
        }

        // try one run
        status = satoko_solve_assumptions( pSat, Vec_IntArray(vSupp), Vec_IntSize(vSupp) );
        if ( status != l_False )
        {
            printf( "Demonstrated that the problem has NO solution.  " );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            satoko_destroy( pSat );
            Vec_IntFree( vSupp );
            return NULL;
        }
        assert( status == l_False );
        printf( "Proved that the problem has a solution.  " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

        // find minimum subset
        if ( fUseMinAssump )
        {
            abctime clk = Abc_Clock();
            nSuppNew = satoko_minimize_assumptions( pSat, Vec_IntArray(vSupp), Vec_IntSize(vSupp), 0 );
            Vec_IntShrink( vSupp, nSuppNew );
            printf( "Solved the problem with %d supp vars.  ", Vec_IntSize(vSupp) );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        }
        else
        {
            int * pFinal, nFinal = satoko_final_conflict( pSat, &pFinal );
            printf( "AnalyzeFinal returned %d (out of %d).\n", nFinal, Vec_IntSize(vSupp) );
            Vec_IntClear( vSupp ); 
            for ( i = 0; i < nFinal; i++ )
                Vec_IntPush( vSupp, Abc_LitNot(pFinal[i]) );
            // try one run
            status = satoko_solve_assumptions( pSat, Vec_IntArray(vSupp), Vec_IntSize(vSupp) );
            assert( status == l_False );
            // try again
            nFinal = satoko_final_conflict( pSat, &pFinal );
            printf( "AnalyzeFinal returned %d (out of %d).\n", nFinal, Vec_IntSize(vSupp) );
        }

        // remap them into numbers
        Vec_IntForEachEntry( vSupp, iLit, i )
            Vec_IntWriteEntry( vSupp, i, Abc_Lit2Var(iLit)-iDivVar );
        Vec_IntSort( vSupp, 0 );
        //Vec_IntPrint( vSupp );
    }
    satoko_destroy( pSat );
    Vec_IntSort( vSupp, 0 );
    return vSupp;
}


/**Function*************************************************************

  Synopsis    [Compute functions of the targets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Acb_EnumerateSatAssigns( sat_solver * pSat, int PivotVar, int FreeVar, Vec_Int_t * vDivVars, Vec_Int_t * vTempLits, Vec_Str_t * vTempSop )
{
    int fCreatePrime = 1;
    int status, i, iMint, iVar, iLit, nFinal, * pFinal, pLits[2];
    Vec_Int_t * vTemp, * vLits;
    assert( FreeVar < sat_solver_nvars(pSat) );
    pLits[0] = Abc_Var2Lit( PivotVar, 1 ); // F = 1
    pLits[1] = Abc_Var2Lit( FreeVar, 0 );  // iNewLit
    Vec_StrClear( vTempSop );
    Vec_StrGrow( vTempSop, 8 * (Vec_IntSize(vDivVars) + 3) + 1 );
    // check constant 0
    status = sat_solver_solve( pSat, pLits, pLits + 2, 0, 0, 0, 0 );
    if ( status == l_False )
    {
        Vec_StrPush( vTempSop, ' ' );
        Vec_StrPush( vTempSop, '0' );
        Vec_StrPush( vTempSop, '\n' );
        Vec_StrPush( vTempSop, '\0' );
        return Vec_StrReleaseArray(vTempSop);
    }
    // check constant 1
    pLits[0] = Abc_LitNot(pLits[0]);
    status = sat_solver_solve( pSat, pLits, pLits + 2, 0, 0, 0, 0 );
    pLits[0] = Abc_LitNot(pLits[0]);
    if ( status == l_False || Vec_IntSize(vDivVars) == 0 )
    {
        Vec_StrPush( vTempSop, ' ' );
        Vec_StrPush( vTempSop, '1' );
        Vec_StrPush( vTempSop, '\n' );
        Vec_StrPush( vTempSop, '\0' );
        return Vec_StrReleaseArray(vTempSop);
    }
    //Vec_IntPrint( vDivVars );
    vTemp = Vec_IntAlloc( 100 );
    vLits = Vec_IntAlloc( 100 );
    for ( iMint = 0; ; iMint++ )
    {
        if ( iMint == 1000 )
        {
            printf( "Reached the limit on the number of cubes (1000).\n" );
            Vec_IntFree( vTemp );
            Vec_IntFree( vLits );
            return NULL;
        }
        //int Offset = Vec_StrSize(vTempSop);
        // find onset minterm
        status = sat_solver_solve( pSat, pLits, pLits + 2, 0, 0, 0, 0 );
        if ( status == l_False )
        {
            printf( "Finished enumerating %d cubes.\n", iMint );
            Vec_IntFree( vTemp );
            Vec_IntFree( vLits );
            Vec_StrPush( vTempSop, '\0' );
            return Vec_StrReleaseArray(vTempSop);
        }
        assert( status == l_True );
        // collect divisor literals
        Vec_IntClear( vTempLits );
        Vec_IntPush( vTempLits, Abc_LitNot(pLits[0]) ); // F = 0
        //printf( "%8d %3d  ", 0, 0 );
//        Vec_IntForEachEntry( vDivVars, iVar, i )
        Vec_IntForEachEntryReverse( vDivVars, iVar, i )
        {
            Vec_IntPush( vTempLits, sat_solver_var_literal(pSat, iVar) );
            //printf( "%c", '0' + sat_solver_var_value(pSat, iVar) );
        }
        //printf( "\n" );
        // create new cube
        for ( i = 0; i < Vec_IntSize(vDivVars); i++ )
            Vec_StrPush( vTempSop, '-' );
        if ( fCreatePrime )
        {
            // expand against offset
            status = sat_solver_push(pSat, Vec_IntEntry(vTempLits, 0));
            assert( status == 1 );
            nFinal = sat_solver_minimize_assumptions( pSat, Vec_IntArray(vTempLits)+1, Vec_IntSize(vTempLits)-1, 0 );
            Vec_IntShrink( vTempLits, nFinal+1 );
            sat_solver_pop(pSat);
            // compute cube and add clause
            Vec_IntWriteEntry( vTempLits, 0, Abc_LitNot(pLits[1]) ); // NOT(iNewLit)
            Vec_IntForEachEntryStart( vTempLits, iLit, i, 1 )
            {
                Vec_IntWriteEntry( vTempLits, i, Abc_LitNot(iLit) );
                iVar = Vec_IntFind( vDivVars, Abc_Lit2Var(iLit) );   assert( iVar >= 0 );
                //uCube &= Abc_LitIsCompl(pFinal[i]) ? s_Truths6[iVar] : ~s_Truths6[iVar];
                Vec_StrWriteEntry( vTempSop, Vec_StrSize(vTempSop) - Vec_IntSize(vDivVars) + iVar, (char)('0' + !Abc_LitIsCompl(iLit)) );
            }
        }
        else
        {
            // expand against offset
            status = sat_solver_solve( pSat, Vec_IntArray(vTempLits), Vec_IntLimit(vTempLits), 0, 0, 0, 0 );
            if ( status != l_False )
                printf( "Selected onset minterm number %d belongs to the offset (this is a bug).\n", iMint );
            assert( status == l_False );

            // compute cube and add clause
            nFinal = sat_solver_final( pSat, &pFinal );
            Vec_IntSelectSort( pFinal, nFinal );
/*
            // pretend that this is final
            veci_resize(&pSat->conf_final,0);
            Vec_IntForEachEntry( vTempLits, iLit, i )
                veci_push(&pSat->conf_final, lit_neg(iLit));
            pFinal = pSat->conf_final.ptr;
            nFinal = Vec_IntSize(vTempLits);
*/
            ////////////////////////////////////////////////////////
            // create new cube
            Vec_IntClear( vTemp );
            Vec_IntPush( vTemp, Abc_LitNot(pLits[0]) ); // F = 0
            for ( i = 0; i < nFinal; i++ )
            {
                if ( pFinal[i] == pLits[0] )
                    continue;
                Vec_IntPush( vTemp, Abc_LitNot(pFinal[i]) );
            }

            //Vec_IntPrint( vTemp );
            // try removing each one starting with the last one
            //printf( "Started with %d lits   ", nFinal-1 );
            for ( i = nFinal - 1; i > 0; i-- )
            {
                int iLit = Vec_IntEntry( vTemp, i );
                Vec_IntDrop( vTemp, i );
                // try SAT
                status = sat_solver_solve( pSat, Vec_IntArray(vTemp), Vec_IntLimit(vTemp), 0, 0, 0, 0 );
                if ( status == l_False )
                {
                //    printf( "U" );
                    continue;
                }
                //if ( status == l_True )
                //    printf( "S" );
                //else if ( status == l_Undef )
                //    printf( "T" );
                Vec_IntInsert( vTemp, i, iLit );
            }
            //printf( "   Ended up with %d lits\n", Vec_IntSize(vTemp)-1 );
            //Vec_IntPrint( vTemp );

            Vec_IntForEachEntry( vTemp, iLit, i )
                pFinal[i] = Abc_LitNot(iLit);
            nFinal = Vec_IntSize(vTemp);
            ////////////////////////////////////////////////////////


            Vec_IntClear( vTempLits );
            Vec_IntPush( vTempLits, Abc_LitNot(pLits[1]) ); // NOT(iNewLit)
            for ( i = 0; i < nFinal; i++ )
            {
                if ( pFinal[i] == pLits[0] )
                    continue;
                Vec_IntPush( vTempLits, pFinal[i] );
                iVar = Vec_IntFind( vDivVars, Abc_Lit2Var(pFinal[i]) );   assert( iVar >= 0 );
                //uCube &= Abc_LitIsCompl(pFinal[i]) ? s_Truths6[iVar] : ~s_Truths6[iVar];
                Vec_StrWriteEntry( vTempSop, Vec_StrSize(vTempSop) - Vec_IntSize(vDivVars) + iVar, (char)('0' + Abc_LitIsCompl(pFinal[i])) );
            }
        }
        //printf( "%6d : %8d %3d  ", iMint, (int)pSat->stats.conflicts, Vec_IntSize(vTempLits)-1 );

        Vec_StrAppend( vTempSop, " 1\n" );
        status = sat_solver_addclause( pSat, Vec_IntArray(vTempLits), Vec_IntLimit(vTempLits) );
        assert( status );

        //Vec_StrPush( vTempSop, '\0' );
        //printf( "%s", Vec_StrEntryP(vTempSop, Offset) );
        //Vec_StrPop( vTempSop );
    }
    assert( 0 ); 
    return NULL;
}
char * Acb_DeriveOnePatchFunction( Cnf_Dat_t * pCnf, int iTar, int nTargets, int nCoDivs, Vec_Int_t * vUsed, int fCisOnly )
{
    char * pSop = NULL;
    Vec_Int_t * vTempLits = Vec_IntAlloc( Vec_IntSize(vUsed)+1 );
    Vec_Str_t * vTempSop = Vec_StrAlloc(0);
    int i, Lit;
    int iCiVarBeg = pCnf->nVars - nTargets - Vec_IntSize(vUsed);
    int iCoVarBeg = 1, Index;
    sat_solver * pSat = sat_solver_new(); 
    sat_solver_setnvars( pSat, pCnf->nVars + 1 );
    // add clauses
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            return NULL;
    // add output clause
    Lit = Abc_Var2Lit( iCoVarBeg, 0 );
    if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
        return NULL;
    // remap vUsed to be in terms of divisor variables
    if ( fCisOnly )
    {
        Vec_IntForEachEntry( vUsed, Index, i )
            Vec_IntWriteEntry( vUsed, i, iCiVarBeg + Index );
    }
    else
    {
        Vec_IntForEachEntry( vUsed, Index, i )
            Vec_IntWriteEntry( vUsed, i, iCoVarBeg + 1 + Index );
    }
    // enumerate assignments for each target in terms of used divisors
    pSop = Acb_EnumerateSatAssigns( pSat, pCnf->nVars - nTargets + iTar, pCnf->nVars, vUsed, vTempLits, vTempSop );
    Vec_IntFree( vTempLits );
    Vec_StrFree( vTempSop );
    sat_solver_delete( pSat );
    if ( pSop == NULL )
        return NULL;
    //printf( "Function %d:\n%s", i, pSop );
    // remap vUsed to be in terms of original divisors
    if ( fCisOnly )
    {
        Vec_IntForEachEntry( vUsed, Index, i )
            Vec_IntWriteEntry( vUsed, i, Index - iCiVarBeg );
    }
    else
    {
        Vec_IntForEachEntry( vUsed, Index, i )
            Vec_IntWriteEntry( vUsed, i, Index - (iCoVarBeg + 1) );
    }
    return pSop;
}
int Acb_CheckMiter( Cnf_Dat_t * pCnf )
{
    int iCoVarBeg = 1, i, Lit, status;
    sat_solver * pSat = sat_solver_new(); 
    sat_solver_setnvars( pSat, pCnf->nVars );
    // add clauses
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            return 1;
    // add output clause
    Lit = Abc_Var2Lit( iCoVarBeg, 0 );
    if ( !sat_solver_addclause( pSat, &Lit, &Lit+1 ) )
        return 1;
    status = sat_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
    sat_solver_delete( pSat );
    return status == l_False;
}


/**Function*************************************************************

  Synopsis    [Update miter by substituting the last target by a given function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_CollectIntNodes_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vNodes )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    assert( Gia_ObjIsAnd(pObj) );
    Acb_CollectIntNodes_rec( p, Gia_ObjFanin0(pObj), vNodes );
    Acb_CollectIntNodes_rec( p, Gia_ObjFanin1(pObj), vNodes );
    Vec_IntPush( vNodes, Gia_ObjId(p, pObj) );
}
void Acb_CollectIntNodes( Gia_Man_t * p, Vec_Int_t * vNodes0, Vec_Int_t * vNodes1 )
{
    Gia_Obj_t * pObj; int i;
    Vec_IntClear( vNodes0 );
    Vec_IntClear( vNodes1 );
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    Gia_ManForEachCi( p, pObj, i )
        Gia_ObjSetTravIdCurrent( p, pObj );
    Gia_ManForEachCo( p, pObj, i )
        if ( i > 0 )
            Acb_CollectIntNodes_rec( p, Gia_ObjFanin0(pObj), vNodes1 );
    Gia_ManForEachCo( p, pObj, i )
        if ( i == 0 )
            Acb_CollectIntNodes_rec( p, Gia_ObjFanin0(pObj), vNodes0 );
}
Gia_Man_t * Acb_UpdateMiter( Gia_Man_t * pM, Gia_Man_t * pOne, int iTar, int nTargets, Vec_Int_t * vUsed, int fCisOnly )
{
    Gia_Man_t * pRes, * pTemp;
    Gia_Obj_t * pObj; int i;
    Vec_Int_t * vNodes0 = Vec_IntAlloc( Gia_ManAndNum(pM) );
    Vec_Int_t * vNodes1 = Vec_IntAlloc( Gia_ManAndNum(pM) );
    Acb_CollectIntNodes( pM, vNodes0, vNodes1 );
    Gia_ManFillValue( pM );
    Gia_ManFillValue( pOne );
    // create new
    pRes = Gia_ManStart( Gia_ManObjNum(pM) + Gia_ManObjNum(pOne) );
    Gia_ManHashAlloc( pRes );
    Gia_ManConst0(pM)->Value = 0;
    Gia_ManConst0(pOne)->Value = 0;
    // copy first part of the miter
    Gia_ManForEachCi( pM, pObj, i )
//        if ( i < Gia_ManCiNum(pM) - 1 )
            pObj->Value = Gia_ManAppendCi( pRes );
    Gia_ManForEachObjVec( vNodes1, pM, pObj, i )
        pObj->Value = Gia_ManHashAnd( pRes, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( pM, pObj, i )
        if ( i > 0 )
            pObj->Value = Gia_ObjFanin0Copy(pObj);
    // transfer to New
    //assert( Gia_ManCiNum(pOne) <= Vec_IntSize(vUsed) );
    assert( Gia_ManCoNum(pOne) == 1 );
    if ( fCisOnly )
    {
        Gia_ManForEachCi( pOne, pObj, i )
            if ( i < Vec_IntSize(vUsed) )
                pObj->Value = Gia_ManCi(pM, Vec_IntEntry(vUsed, i))->Value;
    }
    else
    {
        Gia_ManForEachCi( pOne, pObj, i )
            pObj->Value = Gia_ManCo(pM, 1+Vec_IntEntry(vUsed, i))->Value;
    }
    Gia_ManForEachAnd( pOne, pObj, i )
        pObj->Value = Gia_ManHashAnd( pRes, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    // transfer to miter
    pObj = Gia_ManCi( pM, Gia_ManCiNum(pM) - nTargets + iTar );
    pObj->Value = Gia_ObjFanin0Copy( Gia_ManCo(pOne, 0) );
    Gia_ManForEachObjVec( vNodes0, pM, pObj, i )
        pObj->Value = Gia_ManHashAnd( pRes, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( pM, pObj, i )
        Gia_ManAppendCo( pRes, Gia_ObjFanin0Copy(pObj) );
    // cleanup
    Vec_IntFree( vNodes0 );
    Vec_IntFree( vNodes1 );
    Gia_ManHashStop( pRes );
    pRes = Gia_ManCleanup( pTemp = pRes );
    Gia_ManStop( pTemp );
    assert( Gia_ManCiNum(pRes) == Gia_ManCiNum(pM) );
    assert( Gia_ManCoNum(pRes) == Gia_ManCoNum(pM) );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Generate strings representing instance and the patch.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Acb_GenerateInstance( Acb_Ntk_t * p, Vec_Int_t * vDivs, Vec_Int_t * vUsed, Vec_Int_t * vTars )
{
    int i, iObj;
    Vec_Str_t * vStr = Vec_StrAlloc( 100 );
    Vec_StrAppend( vStr, "patch p0 (" );
    Vec_IntForEachEntry( vTars, iObj, i )
        Vec_StrPrintF( vStr, "%s .%s(%s)", i ? ",":"", Acb_ObjNameStr(p, iObj), Acb_ObjNameStr(p, iObj) );
    Vec_IntForEachEntryInVec( vDivs, vUsed, iObj, i )
        Vec_StrPrintF( vStr, ", .%s(%s)", Acb_ObjNameStr(p, iObj), Acb_ObjNameStr(p, iObj) );
    Vec_StrAppend( vStr, " );\n" );
    Vec_StrPush( vStr, '\0' );
    return vStr;
}
Vec_Ptr_t * Acb_GenerateSignalNames( Acb_Ntk_t * p, Vec_Int_t * vDivs, Vec_Int_t * vUsed, int nNodes, Vec_Int_t * vTars, Vec_Wec_t * vGates )
{
    Vec_Ptr_t * vRes = Vec_PtrStart( Vec_IntSize(vUsed) + nNodes );
    Vec_Str_t * vStr = Vec_StrAlloc(1000); int i, iObj, nWires = 1;
    // create input names
    Vec_IntForEachEntryInVec( vDivs, vUsed, iObj, i )
        Vec_PtrWriteEntry( vRes, i, Abc_UtilStrsav(Acb_ObjNameStr(p, iObj)) );
    // create names for nodes driving outputs
    assert( Vec_WecSize(vGates) == Vec_IntSize(vUsed) + nNodes + Vec_IntSize(vTars) );
    Vec_IntForEachEntry( vTars, iObj, i )
    {
        Vec_Int_t * vGate = Vec_WecEntry( vGates, Vec_IntSize(vUsed) + nNodes + i );
        assert( Vec_IntEntry(vGate, 0) == ABC_OPER_BIT_BUF );
        Vec_PtrWriteEntry( vRes, Vec_IntEntry(vGate, 1), Abc_UtilStrsav(Acb_ObjNameStr(p, iObj)) );
    }
    for ( i = Vec_IntSize(vUsed); i < Vec_IntSize(vUsed) + nNodes; i++ )
        if ( Vec_PtrEntry(vRes, i) == NULL )
        {
            Vec_StrPrintF( vStr, "ww%d", nWires++ );
            Vec_StrPush( vStr, '\0' );
            Vec_PtrWriteEntry( vRes, i, Vec_StrReleaseArray(vStr) );
        }
    Vec_StrFree( vStr );
    return vRes;
}
Vec_Str_t * Acb_GeneratePatch( Acb_Ntk_t * p, Vec_Int_t * vDivs, Vec_Int_t * vUsed, Vec_Ptr_t * vSops, Vec_Ptr_t * vGias, Vec_Int_t * vTars )
{
    extern Vec_Wec_t * Abc_SopSynthesize( Vec_Ptr_t * vSops );
    extern Vec_Wec_t * Abc_GiaSynthesize( Vec_Ptr_t * vGias );
    Vec_Wec_t * vGates = vGias ? Abc_GiaSynthesize(vGias) : Abc_SopSynthesize(vSops);  Vec_Int_t * vGate;
    int nOuts = vGias ? Vec_PtrSize(vGias) : Vec_PtrSize(vSops);
    int i, k, iObj, nWires = Vec_WecSize(vGates) - Vec_IntSize(vUsed) - nOuts, fFirst = 1;
    Vec_Ptr_t * vNames = Acb_GenerateSignalNames( p, vDivs, vUsed, nWires, vTars, vGates );

    Vec_Str_t * vStr = Vec_StrAlloc( 100 );
    Vec_StrAppend( vStr, "module patch (" );

    assert( Vec_IntSize(vTars) == nOuts );
    Vec_IntForEachEntry( vTars, iObj, i )
        Vec_StrPrintF( vStr, "%s %s", i ? ",":"", Acb_ObjNameStr(p, iObj) );
    Vec_IntForEachEntryInVec( vDivs, vUsed, iObj, i )
        Vec_StrPrintF( vStr, ", %s", Acb_ObjNameStr(p, iObj) );
    Vec_StrAppend( vStr, " );\n\n" );

    Vec_StrAppend( vStr, "  output" );
    Vec_IntForEachEntry( vTars, iObj, i )
        Vec_StrPrintF( vStr, "%s %s", i ? ",":"", Acb_ObjNameStr(p, iObj) );
    Vec_StrAppend( vStr, ";\n" );

    Vec_StrAppend( vStr, "  input" );
    Vec_IntForEachEntryInVec( vDivs, vUsed, iObj, i )
        Vec_StrPrintF( vStr, "%s %s", i ? ",":"", Acb_ObjNameStr(p, iObj) );
    Vec_StrAppend( vStr, ";\n" );

    if ( nWires > nOuts )
    {
        Vec_StrAppend( vStr, "  wire" );
        for ( i = 0; i < nWires; i++ )
        {
            char * pName = (char *)Vec_PtrEntry( vNames, Vec_IntSize(vUsed)+i );
            if ( !strncmp(pName, "ww", 2) )
                Vec_StrPrintF( vStr, "%s %s", fFirst ? "":",", pName ), fFirst = 0;
        }
        Vec_StrAppend( vStr, ";\n\n" );
    }

    // create internal nodes
    Vec_WecForEachLevelStartStop( vGates, vGate, i, Vec_IntSize(vUsed), Vec_IntSize(vUsed)+nWires )
    {
        if ( Vec_IntSize(vGate) > 2 )
        {
            Vec_StrPrintF( vStr, "  %s (", Acb_Oper2Name(Vec_IntEntry(vGate, 0)) );
            Vec_IntForEachEntryStart( vGate, iObj, k, 1 )
                Vec_StrPrintF( vStr, "%s %s", k > 1 ? ",":"", (char *)Vec_PtrEntry(vNames, iObj) );
            Vec_StrAppend( vStr, " );\n" );
        }
        else
        {
            assert( Vec_IntEntry(vGate, 0) == ABC_OPER_CONST_F || Vec_IntEntry(vGate, 0) == ABC_OPER_CONST_T );
            Vec_StrPrintF( vStr, "  %s (", Acb_Oper2Name( ABC_OPER_BIT_BUF ) );
            Vec_StrPrintF( vStr, " %s, ", (char *)Vec_PtrEntry(vNames, Vec_IntEntry(vGate, 1)) );
            Vec_StrPrintF( vStr, " 1\'b%d", Vec_IntEntry(vGate, 0) == ABC_OPER_CONST_T );
            Vec_StrPrintF( vStr, " );" );
        }
    }
    Vec_StrAppend( vStr, "\nendmodule\n\n" );
    Vec_StrPush( vStr, '\0' );
    Vec_PtrFreeFree( vNames );
    Vec_WecFree( vGates );

    printf( "Synthesized patch with %d inputs, %d outputs and %d gates.\n", Vec_IntSize(vUsed), nOuts, nWires );
    return vStr;
}

/**Function*************************************************************

  Synopsis    [Produce output files.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_GenerateFilePatch( Vec_Str_t * p, char * pFileNamePatch )
{
    FILE * pFile = fopen( pFileNamePatch, "wb" );
    if ( !pFile )
        return;
    fprintf( pFile, "%s", Vec_StrArray(p) );
    fclose( pFile );
}
void Acb_GenerateFileOut( Vec_Str_t * vPatchLine, char * pFileNameF, char * pFileNameOut, Vec_Str_t * vPatch )
{
    char * pBuffer = ABC_ALLOC( char, 10000 );
    FILE * pFileIn, * pFileOut;
    // input file
    pFileIn = fopen( pFileNameF, "rb" );
    if ( !pFileIn )
        return;
    // output file
    pFileOut = fopen( pFileNameOut, "wb" );
    if ( !pFileOut )
        return;
    // copy line by line
    while ( fgets(pBuffer, 10000, pFileIn) )
    {
        if ( strstr(pBuffer, "endmodule") )
            fprintf( pFileOut, "\n%s", Vec_StrArray(vPatchLine) );
        fputs( pBuffer, pFileOut );
    }
    if ( vPatch )
        fprintf( pFileOut, "\n\n%s\n", Vec_StrArray(vPatch) );
    fclose( pFileIn );
    fclose( pFileOut );
    ABC_FREE( pBuffer );
}

/**Function*************************************************************

  Synopsis    [Print parameters of the patch.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_PrintPatch( Acb_Ntk_t * pNtkF, Vec_Int_t * vDivs, Vec_Int_t * vUsed, abctime clk )
{
    int i, iObj, Weight = 0;
    printf( "Patch has %d inputs: ", Vec_IntSize(vUsed) );
    Vec_IntForEachEntryInVec( vDivs, vUsed, iObj, i )
    {
        printf( "%d=%s(w=%d) ", Vec_IntEntry(vUsed, i), Acb_ObjNameStr(pNtkF, iObj), Acb_ObjWeight(pNtkF, iObj) );
        Weight += Acb_ObjWeight(pNtkF, iObj);
    }
    printf( "\nTotal weight = %d  ", Weight );
    Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clk );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Quantifies targets 0 up to iTar (out of nTars).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Acb_NtkEcoSynthesize( Gia_Man_t * p )
{
    int Iter, fVerbose = 0;
    Gia_Man_t * pNew = Gia_ManDup( p );

    if ( fVerbose ) printf( "M_quo: " );
    if ( fVerbose ) Gia_ManPrintStats( pNew, NULL );

    pNew = Gia_ManAreaBalance( p = pNew, 0, 0, 0, 0 );
    Gia_ManStop( p );

    if ( fVerbose ) printf( "M_bal: " );
    if ( fVerbose ) Gia_ManPrintStats( pNew, NULL );

    for ( Iter = 0; Iter < 2; Iter++ )
    {
        pNew = Gia_ManCompress2( p = pNew, 1, 0 );
        Gia_ManStop( p );

        if ( fVerbose ) printf( "M_dc2: " );
        if ( fVerbose ) Gia_ManPrintStats( pNew, NULL );
    }

    pNew = Gia_ManAigSyn2( p = pNew, 0, 1, 0, 100, 0, 0, 0 );
    Gia_ManStop( p );

    if ( fVerbose ) printf( "M_sn2: " );
    if ( fVerbose ) Gia_ManPrintStats( pNew, NULL );

    for ( Iter = 0; Iter < 2; Iter++ )
    {
        pNew = Gia_ManCompress2( p = pNew, 1, 0 );
        Gia_ManStop( p );

        if ( fVerbose ) printf( "M_dc2: " );
        if ( fVerbose ) Gia_ManPrintStats( pNew, NULL );
    }
    return pNew;
}
Cnf_Dat_t * Acb_NtkEcoCompute( Gia_Man_t * p, int iTar, int nTars )
{
    Gia_Man_t * pCof = Gia_ManDup( p );
    Cnf_Dat_t * pCnf; int v, fVerbose = 1;
    for ( v = 0; v < iTar; v++ )
    {
        pCof = Gia_ManDupUniv( p = pCof, Gia_ManCiNum(pCof) - nTars + v );
        assert( Gia_ManCiNum(pCof) == Gia_ManCiNum(p) );
        Gia_ManStop( p );
    }
    if ( fVerbose ) printf( "M_quo: " );
    if ( fVerbose ) Gia_ManPrintStats( pCof, NULL );
    pCof = Acb_NtkEcoSynthesize( p = pCof );
    Gia_ManStop( p );
    if ( fVerbose ) printf( "M_syn: " );
    if ( fVerbose ) Gia_ManPrintStats( pCof, NULL );
    if ( 0 && iTar < nTars )
    {
        Gia_Man_t * pCof0 = Gia_ManDupCofactorVar( pCof, Gia_ManCiNum(pCof) - nTars + iTar, 0 );
        Gia_Man_t * pCof1 = Gia_ManDupCofactorVar( pCof, Gia_ManCiNum(pCof) - nTars + iTar, 1 );
        pCof0 = Acb_NtkEcoSynthesize( p = pCof0 );
        Gia_ManStop( p );
        pCof1 = Acb_NtkEcoSynthesize( p = pCof1 );
        Gia_ManStop( p );
        Gia_AigerWrite( pCof0, "eco_qbf0.aig", 0, 0 );
        Gia_AigerWrite( pCof1, "eco_qbf1.aig", 0, 0 );
        Gia_ManStop( pCof0 );
        Gia_ManStop( pCof1 );
        printf( "Dumped cof0 into file \"%s\".\n", "eco_qbf0.aig" );
        printf( "Dumped cof1 into file \"%s\".\n", "eco_qbf1.aig" );
    }
//    Gia_AigerWrite( pCof, "eco_qbf.aig", 0, 0 );
//    printf( "Dumped the result of quantification into file \"%s\".\n", "eco_qbf.aig" );
    pCnf = (Cnf_Dat_t *)Mf_ManGenerateCnf( pCof, 8, 0, 0, 0, 0 );
    Gia_ManStop( pCof );
    return pCnf;
}
Gia_Man_t * Gia_ManInterOneInt( Gia_Man_t * pCof1, Gia_Man_t * pCof0, int Depth )
{
    extern Gia_Man_t * Gia_ManInterOne( Gia_Man_t * pNtkOn, Gia_Man_t * pNtkOff, int fVerbose );
    extern Gia_Man_t * Abc_GiaSynthesizeInter( Gia_Man_t * p );
    Gia_Man_t * pGia[2] = { pCof0, pCof1 };
    Gia_Man_t * pCof[2][2] = {{0}}, * pTemp;
    Gia_Man_t * pInter[2], * pFinal;
    Gia_Obj_t * pObj; 
    int i, n, m, Count, CountBest = 0, iVarBest = -1;
    // find PIs with the highest fanout
    Vec_Int_t * vFanCount;
    if ( Gia_ManAndNum(pCof1) == 0 || Gia_ManAndNum(pCof0) == 0 )
        return Gia_ManDup(pCof1);
    vFanCount = Vec_IntStart( Gia_ManCiNum(pCof0) );
    for ( n = 0; n < 2; n++ )
    {
        Gia_ManForEachAnd( pGia[n], pObj, i )
        {
            if ( Gia_ObjIsCi(Gia_ObjFanin0(pObj)) )
                Vec_IntAddToEntry( vFanCount, Gia_ObjCioId(Gia_ObjFanin0(pObj)), 1 );
            if ( Gia_ObjIsCi(Gia_ObjFanin1(pObj)) )
                Vec_IntAddToEntry( vFanCount, Gia_ObjCioId(Gia_ObjFanin1(pObj)), 1 );
        }
    }
    Vec_IntForEachEntry( vFanCount, Count, i )
        if ( CountBest < Count )
        {
            CountBest = Count;
            iVarBest = i;
        }
    Vec_IntFree( vFanCount );
    // Gia_Man_t * Gia_ManDupCofactorVar( Gia_Man_t * p, int iVar, int Value )
    for ( n = 0; n < 2; n++ )
    for ( m = 0; m < 2; m++ )
    {
        pCof[n][m] = Gia_ManDupCofactorVar( pGia[n], iVarBest, m );
        pCof[n][m] = Acb_NtkEcoSynthesize( pTemp = pCof[n][m] );
        Gia_ManStop( pTemp );
        printf( "%*sCof%d%d : ", 8-Depth, "", n, m );
        Gia_ManPrintStats( pCof[n][m], NULL );
    }
    for ( m = 0; m < 2; m++ )
    {
        if ( Gia_ManAndNum(pCof[1][m]) == 0 || Gia_ManAndNum(pCof[0][m]) == 0 )
            pInter[m] = Gia_ManDup( pCof[1][m] );
        else if ( Depth == 1 )
            pInter[m] = Gia_ManInterOne( pCof[1][m], pCof[0][m], 1 );
        else
            pInter[m] = Gia_ManInterOneInt( pCof[1][m], pCof[0][m], Depth-1 );
        printf( "%*sInter%d : ", 8-Depth, "", m );
        Gia_ManPrintStats( pInter[m], NULL );
        pInter[m] = Abc_GiaSynthesizeInter( pTemp = pInter[m] );
        Gia_ManStop( pTemp );
        printf( "%*sInter%d : ", 8-Depth, "", m );
        Gia_ManPrintStats( pInter[m], NULL );
    }
    for ( n = 0; n < 2; n++ )
    for ( m = 0; m < 2; m++ )
        Gia_ManStop( pCof[n][m] );
    pFinal = Gia_ManDupMux( iVarBest, pInter[1], pInter[0] );
    for ( m = 0; m < 2; m++ )
        Gia_ManStop( pInter[m] );
    return pFinal;
}
Gia_Man_t * Acb_NtkEcoComputeInter2( Gia_Man_t * p, int iTar, int nTars )
{
//    extern Gia_Man_t * Gia_ManInterOne( Gia_Man_t * pNtkOn, Gia_Man_t * pNtkOff, int fVerbose );
    extern Gia_Man_t * Abc_GiaSynthesizeInter( Gia_Man_t * p );
    Gia_Man_t * pInter, * pCof0, * pCof1, * pCof = Gia_ManDup( p ); int v;
    for ( v = 0; v < iTar; v++ )
    {
        pCof = Gia_ManDupUniv( p = pCof, Gia_ManCiNum(pCof) - nTars + v );
        assert( Gia_ManCiNum(pCof) == Gia_ManCiNum(p) );
        Gia_ManStop( p );

        pCof = Acb_NtkEcoSynthesize( p = pCof );
        Gia_ManStop( p );
    }
    pCof0 = Gia_ManDupCofactorVar( pCof, Gia_ManCiNum(pCof) - nTars + iTar, 1 );
    pCof1 = Gia_ManDupCofactorVar( pCof, Gia_ManCiNum(pCof) - nTars + iTar, 0 );
    Gia_ManStop( pCof );
    pCof0 = Acb_NtkEcoSynthesize( p = pCof0 );
    Gia_ManStop( p );
    pCof1 = Acb_NtkEcoSynthesize( p = pCof1 );
    Gia_ManStop( p );

    printf( "Cof0 : " );
    Gia_ManPrintStats( pCof0, NULL );
    printf( "Cof1 : " );
    Gia_ManPrintStats( pCof1, NULL );

    if ( Gia_ManAndNum(pCof1) == 0 || Gia_ManAndNum(pCof0) == 0 )
        pInter = Gia_ManDup(pCof1);
    else
        pInter = Gia_ManInterOneInt( pCof1, pCof0, 7 );
    Gia_ManStop( pCof0 );
    Gia_ManStop( pCof1 );
    pInter = Abc_GiaSynthesizeInter( p = pInter );
    Gia_ManStop( p );
    //Gia_ManPrintStats( pInter, NULL );
    pInter = Gia_ManDupRemovePis( p = pInter, nTars );
    Gia_ManStop( p );
    //Gia_ManPrintStats( pInter, NULL );
    return pInter;
}
Gia_Man_t * Acb_NtkEcoComputeInter( Gia_Man_t * p, int iTar, int nTars )
{
    Gia_Man_t * pCof1, * pCof = Gia_ManDup( p ); int v;
    for ( v = 0; v < iTar; v++ )
    {
        pCof = Gia_ManDupUniv( p = pCof, Gia_ManCiNum(pCof) - nTars + v );
        assert( Gia_ManCiNum(pCof) == Gia_ManCiNum(p) );
        Gia_ManStop( p );

        pCof = Acb_NtkEcoSynthesize( p = pCof );
        Gia_ManStop( p );
    }
    pCof1 = Gia_ManDupCofactorVar( pCof, Gia_ManCiNum(pCof) - nTars + iTar, 0 );
    Gia_ManStop( pCof );

    pCof1 = Acb_NtkEcoSynthesize( p = pCof1 );
    Gia_ManStop( p );

    pCof1 = Gia_ManDupRemovePis( p = pCof1, nTars );
    Gia_ManStop( p );
    return pCof1;
}

/**Function*************************************************************

  Synopsis    [Transform patch functions to have common support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Acb_RemapOneFunction( char * pStr, Vec_Int_t * vSupp, Vec_Int_t * vMap, int nVars )
{
    Vec_Str_t * vTempSop = Vec_StrAlloc( 100 );
    char * pToken = strtok( pStr, "\n" );  int i; 
    while ( pToken != NULL )
    {
        for ( i = 0; i < nVars; i++ )
            Vec_StrPush( vTempSop, '-' );
        for ( i = 0; pToken[i] != ' '; i++ )
            if ( pToken[i] != '-' )
            {
                int iVar = Vec_IntEntry( vMap, Vec_IntEntry(vSupp, i) );
                assert( iVar >= 0 && iVar < nVars );
                Vec_StrWriteEntry( vTempSop, Vec_StrSize(vTempSop) - nVars + iVar, pToken[i] );
            }
        Vec_StrPrintF( vTempSop, " %d\n", pToken[i+1] - '0' );
        pToken = strtok( NULL, "\n" );
    }
    Vec_StrPush( vTempSop, '\0' );
    pToken = Vec_StrReleaseArray(vTempSop);
    Vec_StrFree( vTempSop );
    return pToken;
}
Vec_Ptr_t * Acb_TransformPatchFunctions( Vec_Ptr_t * vSops, Vec_Wec_t * vSupps, Vec_Int_t ** pvUsed, int nDivs )
{
    Vec_Ptr_t * vFuncs = Vec_PtrAlloc( Vec_PtrSize(vSops) );
    Vec_Int_t * vUsed = Vec_IntAlloc( 100 ); 
    Vec_Int_t * vMap = Vec_IntStartFull( nDivs );
    Vec_Int_t * vPres = Vec_IntStart( nDivs );
    Vec_Int_t * vLevel;
    int i, k, iVar;
    // check what divisors are used
    Vec_WecForEachLevel( vSupps, vLevel, i )
    {
        char * pSop = (char *)Vec_PtrEntry( vSops, i );
        char * pStrCopy = Abc_UtilStrsav( pSop );
        char * pToken = strtok( pStrCopy, "\n" ); 
        while ( pToken != NULL )
        {
            for ( k = 0; pToken[k] != ' '; k++ )
                if ( pToken[k] != '-' )
                    Vec_IntWriteEntry( vPres, Vec_IntEntry(vLevel, k), 1 );
            pToken = strtok( NULL, "\n" );
        }
        ABC_FREE( pStrCopy );
    }
    // create common order
    Vec_WecForEachLevel( vSupps, vLevel, i )
        Vec_IntForEachEntry( vLevel, iVar, k )
        {
            if ( !Vec_IntEntry(vPres, iVar) )
                continue;
            if ( Vec_IntEntry(vMap, iVar) >= 0 )
                continue;
            Vec_IntWriteEntry( vMap, iVar, Vec_IntSize(vUsed) );
            Vec_IntPush( vUsed, iVar );
        }
    printf( "The number of used variables %d (out of %d).\n", Vec_IntSum(vPres), Vec_IntSize(vPres) );
    // remap SOPs
    Vec_WecForEachLevel( vSupps, vLevel, i )
    {
        char * pSop = (char *)Vec_PtrEntry( vSops, i );
        pSop = Acb_RemapOneFunction( pSop, vLevel, vMap, Vec_IntSize(vUsed) );
        //printf( "Function %d\n%s", i, pSop );
        Vec_PtrPush( vFuncs, pSop );
    }
    Vec_IntFree( vPres );
    Vec_IntFree( vMap );
    *pvUsed = vUsed;
    return vFuncs;
}

/**Function*************************************************************

  Synopsis    [Performs ECO for two networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_NtkEcoPerform( Acb_Ntk_t * pNtkF, Acb_Ntk_t * pNtkG, char * pFileNameF, int fCisOnly )
{
    extern Gia_Man_t * Abc_SopSynthesizeOne( char * pSop, int fClp );

    abctime clk  = Abc_Clock();
    int nTargets = Vec_IntSize(&pNtkF->vTargets);
    int TimeOut  = fCisOnly ? 0 : 60;  // 60 seconds
    int RetValue = 1;

    // compute various sets of nodes
    Vec_Bit_t * vBlock;
    Vec_Int_t * vRoots  = Acb_NtkFindRoots( pNtkF, &pNtkF->vTargets, &vBlock );
    Vec_Int_t * vSuppF  = Acb_NtkFindSupp( pNtkF, vRoots );
    Vec_Int_t * vSuppG  = Acb_NtkFindSupp( pNtkG, vRoots );
    Vec_Int_t * vSupp   = Vec_IntTwoMerge( vSuppF, vSuppG );
    Vec_Int_t * vDivs   = fCisOnly ? Acb_NtkFindDivsCis( pNtkF, vSupp ) : Acb_NtkFindDivs( pNtkF, vSupp, vBlock );
    Vec_Int_t * vNodesF = Acb_NtkFindNodes( pNtkF, vRoots, vDivs );
    Vec_Int_t * vNodesG = Acb_NtkFindNodes( pNtkG, vRoots, NULL );

    // create AIGs
    Gia_Man_t * pGiaF   = Acb_NtkToGia( pNtkF, vSupp, vNodesF, vRoots, vDivs, &pNtkF->vTargets );
    Gia_Man_t * pGiaG   = Acb_NtkToGia( pNtkG, vSupp, vNodesG, vRoots, NULL, NULL );
    Gia_Man_t * pGiaM   = Acb_CreateMiter( pGiaF, pGiaG );

    Cnf_Dat_t * pCnf;
    Gia_Man_t * pTemp, * pOne;
    Vec_Ptr_t * vSops    = Vec_PtrAlloc( nTargets );
    Vec_Wec_t * vSupps   = Vec_WecAlloc( nTargets );
    Vec_Int_t * vSuppOld = Vec_IntAlloc( 100 );

    Vec_Int_t * vUsed  = NULL; 
    Vec_Ptr_t * vFuncs = NULL;
    Vec_Ptr_t * vGias  = fCisOnly ? Vec_PtrAlloc(nTargets) : NULL;
    Vec_Str_t * vInst  = NULL, * vPatch = NULL;

    char * pSop = NULL;
    int i, Res;

    printf( "The number of targets = %d.\n", nTargets );

    printf( "NtkF:  " );
    Gia_ManPrintStats( pGiaF, NULL );
    printf( "NtkG:  " );
    Gia_ManPrintStats( pGiaG, NULL );
    printf( "Miter: " );
    Gia_ManPrintStats( pGiaM, NULL );

    // check that the problem has a solution
    if ( 0 )//fCisOnly )
    {
        int Lit, status;
        sat_solver * pSat;
        pCnf = Acb_NtkEcoCompute( pGiaM, nTargets, nTargets );
        pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
        Cnf_DataFree( pCnf );
        // add output clause
        Lit = Abc_Var2Lit( 1, 0 );
        status = sat_solver_addclause( pSat, &Lit, &Lit+1 );
        status = status == 0 ? l_False : sat_solver_solve( pSat, NULL, NULL, 0, 0, 0, 0 );
        sat_solver_delete( pSat );
        printf( "The ECO problem has %s solution. ", status == l_False ? "a" : "NO" );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        if ( status != l_False )
        {
            RetValue = 0;
            goto cleanup;
        }
    }

    for ( i = nTargets-1; i >= 0; i-- )
    {
        Vec_Int_t * vSupp = NULL;
        printf( "\nConsidering target %d (out of %d)...\n", i, nTargets );
        // compute support of this target
        if ( fCisOnly )
        {
            vSupp = Vec_IntStartNatural( Vec_IntSize(vDivs) );
            printf( "Target %d has support with %d variables.\n", i, Vec_IntSize(vSupp) );

            pOne = Acb_NtkEcoComputeInter( pGiaM, i, nTargets );
            printf( "Tar%02d: ", i );
            Gia_ManPrintStats( pOne, NULL );

            // update miter
            pGiaM = Acb_UpdateMiter( pTemp = pGiaM, pOne, i, nTargets, vSupp, fCisOnly );
            Gia_ManStop( pTemp );

            // add to functions
            Vec_PtrPush( vGias, pOne );
        }
        else
        {
            pCnf = Acb_NtkEcoCompute( pGiaM, i, nTargets );
//            vSupp = Acb_DerivePatchSupportS( pCnf, i, nTargets, Vec_IntSize(vDivs), vDivs, pNtkF, NULL, TimeOut );
            vSupp = Acb_DerivePatchSupport( pCnf, i, nTargets, Vec_IntSize(vDivs), vDivs, pNtkF, vSuppOld, TimeOut );
            if ( vSupp == NULL )
            {
                Vec_IntFree( vSuppOld );
                Cnf_DataFree( pCnf );
                RetValue = 0;
                goto cleanup;
            }
            Vec_IntAppend( vSuppOld, vSupp );
            Vec_IntClear( vSupp );
            Vec_IntAppend( vSupp, vSuppOld );
            //Vec_IntClear( vSuppOld );

            // derive function of this target
            pSop  = Acb_DeriveOnePatchFunction( pCnf, i, nTargets, Vec_IntSize(vDivs), vSupp, fCisOnly );
            Cnf_DataFree( pCnf );
            if ( pSop == NULL )
            {
                Vec_IntFree( vSuppOld );
                RetValue = 0;
                goto cleanup;
            }

            // add new function to the miter
            pOne  = Abc_SopSynthesizeOne( pSop, 1 );
            printf( "Tar%02d: ", i );
            Gia_ManPrintStats( pOne, NULL );

            // update miter
            pGiaM = Acb_UpdateMiter( pTemp = pGiaM, pOne, i, nTargets, vSupp, fCisOnly );
            Gia_ManStop( pTemp );
            Gia_ManStop( pOne );

            // add to functions
            Vec_PtrPush( vSops, pSop );
        }
        // add to supports
        Vec_IntAppend( Vec_WecPushLevel(vSupps), vSupp );
        Vec_IntFree( vSupp );
    }
    Vec_IntFree( vSuppOld );

    // make sure the function is UNSAT
    printf( "\n" );
    if ( !fCisOnly )
    {
        abctime clk  = Abc_Clock();
        pCnf = (Cnf_Dat_t *)Mf_ManGenerateCnf( pGiaM, 8, 0, 0, 0, 0 );
        Res = Acb_CheckMiter( pCnf );
        Cnf_DataFree( pCnf );
        if ( Res == 1 )
            printf( "The ECO solution was verified successfully.  " );
        else
            printf( "The ECO solution verification FAILED.  " );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    }

    // derive new patch functions
    if ( fCisOnly )
    {
        vUsed = Vec_IntStartNatural( Vec_IntSize(vDivs) );
        Vec_PtrReverseOrder( vGias );
    }
    else
    {
        vFuncs = Acb_TransformPatchFunctions( vSops, vSupps, &vUsed, Vec_IntSize(vDivs) );
        Vec_PtrReverseOrder( vFuncs );
    }

    // generate instance and patch
    vInst   = Acb_GenerateInstance( pNtkF, vDivs, vUsed, &pNtkF->vTargets );
    vPatch  = Acb_GeneratePatch( pNtkF, vDivs, vUsed, vFuncs, vGias, &pNtkF->vTargets );

    // print the results
    //printf( "%s", Vec_StrArray(vPatch) );
    Acb_PrintPatch( pNtkF, vDivs, vUsed, clk );

    // generate output files
    Acb_GenerateFilePatch( vPatch, "patch.v" );
    Acb_GenerateFileOut( vInst, pFileNameF, "out.v", vPatch );
    //Gia_AigerWrite( pGiaG, "test.aig", 0, 0 );
cleanup:
    // cleanup
    if ( vGias )
    {
        Gia_Man_t * pTemp; int i;
        Vec_PtrForEachEntry( Gia_Man_t *, vGias, pTemp, i )
            Gia_ManStop( pTemp );
        Vec_PtrFree( vGias );
    }
    Vec_StrFreeP( &vPatch );
    Vec_StrFreeP( &vInst );

    Vec_PtrFreeFree( vSops );
    Vec_WecFree( vSupps );

    if ( vFuncs ) Vec_PtrFreeFree( vFuncs );
    Vec_IntFreeP( &vUsed );

    Gia_ManStop( pGiaF );
    Gia_ManStop( pGiaG );
    Gia_ManStop( pGiaM );

    Vec_IntFreeP( &vSuppF );
    Vec_IntFreeP( &vSuppG );
    Vec_IntFreeP( &vSupp );
    Vec_IntFreeP( &vNodesF );
    Vec_IntFreeP( &vNodesG );
    Vec_IntFreeP( &vRoots );
    Vec_IntFreeP( &vDivs );
    Vec_BitFreeP( &vBlock );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Read/write test.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkTestRun2( char * pFileNames[3], int fVerbose )
{
    char * pFileNameOut = Extra_FileNameGenericAppend( pFileNames[0], "_w.v" );
    Acb_Ntk_t * pNtk = Acb_VerilogSimpleRead( pFileNames[0], pFileNames[2] );
    Acb_VerilogSimpleWrite( pNtk, pFileNameOut );
    Acb_ManFree( pNtk->pDesign );
    Acb_IntallLibrary();
}


/**Function*************************************************************

  Synopsis    [Top level procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkRunEco( char * pFileNames[3], int fVerbose )
{
    Acb_Ntk_t * pNtkF = Acb_VerilogSimpleRead( pFileNames[0], pFileNames[2] );
    Acb_Ntk_t * pNtkG = Acb_VerilogSimpleRead( pFileNames[1], NULL );
    if ( !pNtkF || !pNtkG )
        return;
    //int * pArray = Vec_IntArray( &pNtkF->vTargets );
    //ABC_SWAP( int, pArray[7], pArray[4] );
    //Vec_IntReverseOrder( &pNtkF->vTargets );
    //Vec_IntPermute( &pNtkF->vTargets );
    //Vec_IntPrint( &pNtkF->vTargets );
        
    assert( Acb_NtkCiNum(pNtkF) == Acb_NtkCiNum(pNtkG) );
    assert( Acb_NtkCoNum(pNtkF) == Acb_NtkCoNum(pNtkG) );

    Acb_IntallLibrary();

    if ( !Acb_NtkEcoPerform( pNtkF, pNtkG, pFileNames[0], 0 ) )
    {
        printf( "General ECO computation timed out. Trying inputs only.\n\n" );
        if ( !Acb_NtkEcoPerform( pNtkF, pNtkG, pFileNames[0], 1 ) )
            printf( "Input-only ECO computation also timed out.\n\n" );
    }

    Acb_ManFree( pNtkF->pDesign );
    Acb_ManFree( pNtkG->pDesign );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

