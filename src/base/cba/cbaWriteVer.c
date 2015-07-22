/**CFile****************************************************************

  FileName    [cbaWriteVer.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Verilog writer.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaWriteVer.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "cbaPrs.h"
#include "map/mio/mio.h"
#include "base/main/main.h"

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
static void Prs_ManWriteVerilogConcat( FILE * pFile, Prs_Ntk_t * p, int Con )
{
    extern void Prs_ManWriteVerilogArray( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs, int Start, int Stop, int fOdd );
    Vec_Int_t * vSigs = Prs_CatSignals(p, Con);
    fprintf( pFile, "{" );
    Prs_ManWriteVerilogArray( pFile, p, vSigs, 0, Vec_IntSize(vSigs), 0 );
    fprintf( pFile, "}" );
}
static void Prs_ManWriteVerilogSignal( FILE * pFile, Prs_Ntk_t * p, int Sig )
{
    int Value = Abc_Lit2Var2( Sig );
    Prs_ManType_t Type = (Prs_ManType_t)Abc_Lit2Att2( Sig );
    if ( Type == CBA_PRS_NAME || Type == CBA_PRS_CONST )
        fprintf( pFile, "%s", Prs_NtkStr(p, Value) );
    else if ( Type == CBA_PRS_SLICE )
        fprintf( pFile, "%s%s", Prs_NtkStr(p, Prs_SliceName(p, Value)), Prs_NtkStr(p, Prs_SliceRange(p, Value)) );
    else if ( Type == CBA_PRS_CONCAT )
        Prs_ManWriteVerilogConcat( pFile, p, Value );
    else assert( 0 );
}
static void Prs_ManWriteVerilogArray( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs, int Start, int Stop, int fOdd )
{
    int i, Sig;
    assert( Vec_IntSize(vSigs) > 0 );
    Vec_IntForEachEntryStartStop( vSigs, Sig, i, Start, Stop )
    {
        if ( fOdd && !(i & 1) )
            continue;
        Prs_ManWriteVerilogSignal( pFile, p, Sig );
        fprintf( pFile, "%s", i == Stop - 1 ? "" : ", " );
    }
}
static void Prs_ManWriteVerilogArray2( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs )
{
    int i, FormId, ActSig;
    assert( Vec_IntSize(vSigs) % 2 == 0 );
    Vec_IntForEachEntryDouble( vSigs, FormId, ActSig, i )
    {
        fprintf( pFile, "." );
        fprintf( pFile, "%s", Prs_NtkStr(p, FormId) );
        fprintf( pFile, "(" );
        Prs_ManWriteVerilogSignal( pFile, p, ActSig );
        fprintf( pFile, ")%s", (i == Vec_IntSize(vSigs) - 2) ? "" : ", " );
    }
}
static void Prs_ManWriteVerilogMux( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs )
{
    int i, FormId, ActSig;
    char * pStrs[4] = { " = ", " ? ", " : ", ";\n" };
    assert( Vec_IntSize(vSigs) == 8 );
    fprintf( pFile, "  assign " );
    Prs_ManWriteVerilogSignal( pFile, p, Vec_IntEntryLast(vSigs) );
    fprintf( pFile, "%s", pStrs[0] );
    Vec_IntForEachEntryDouble( vSigs, FormId, ActSig, i )
    {
        Prs_ManWriteVerilogSignal( pFile, p, ActSig );
        fprintf( pFile, "%s", pStrs[1+i/2] );
        if ( i == 4 )
            break;
    }
}
static void Prs_ManWriteVerilogBoxes( FILE * pFile, Prs_Ntk_t * p )
{
    Vec_Int_t * vBox; int i;
    Prs_NtkForEachBox( p, vBox, i )
    {
        Cba_ObjType_t NtkId = Prs_BoxNtk(p, i);
        if ( NtkId == CBA_BOX_MUX )
            Prs_ManWriteVerilogMux( pFile, p, vBox );
        else if ( Prs_BoxIsNode(p, i) ) // node   ------- check order of fanins
        {
            fprintf( pFile, "  %s (", Ptr_TypeToName(NtkId) );
            Prs_ManWriteVerilogSignal( pFile, p, Vec_IntEntryLast(vBox) );
            if ( Prs_BoxIONum(p, i) > 1 )
                fprintf( pFile, ", " );                
            Prs_ManWriteVerilogArray( pFile, p, vBox, 0, Vec_IntSize(vBox)-2, 1 );
            fprintf( pFile, ");\n" );
        }
        else // box
        {
            //char * s = Prs_NtkStr(p, Vec_IntEntry(vBox, 0));
            fprintf( pFile, "  %s %s (", Prs_NtkStr(p, NtkId), Prs_BoxName(p, i) ? Prs_NtkStr(p, Prs_BoxName(p, i)) : "" );
            Prs_ManWriteVerilogArray2( pFile, p, vBox );
            fprintf( pFile, ");\n" );
        }
    }
}
static void Prs_ManWriteVerilogIos( FILE * pFile, Prs_Ntk_t * p, int SigType )
{
    int NameId, RangeId, i;
    char * pSigNames[4]   = { "inout", "input", "output", "wire" }; 
    Vec_Int_t * vSigs[4]  = { &p->vInouts,  &p->vInputs,  &p->vOutputs,  &p->vWires };
    Vec_Int_t * vSigsR[4] = { &p->vInoutsR, &p->vInputsR, &p->vOutputsR, &p->vWiresR };
    if ( SigType == 3 )
        fprintf( pFile, "\n" );
    Vec_IntForEachEntryTwo( vSigs[SigType], vSigsR[SigType], NameId, RangeId, i )
        fprintf( pFile, "  %s %s%s;\n", pSigNames[SigType], RangeId ? Prs_NtkStr(p, RangeId) : "", Prs_NtkStr(p, NameId) );
}
static void Prs_ManWriteVerilogIoOrder( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vOrder )
{
    int i, NameId;
    Vec_IntForEachEntry( vOrder, NameId, i )
        fprintf( pFile, "%s%s", Prs_NtkStr(p, NameId), i == Vec_IntSize(vOrder) - 1 ? "" : ", " );
}
static void Prs_ManWriteVerilogNtk( FILE * pFile, Prs_Ntk_t * p )
{
    int s;
    // write header
    fprintf( pFile, "module %s (\n    ", Prs_NtkStr(p, p->iModuleName) );
    Prs_ManWriteVerilogIoOrder( pFile, p, &p->vOrder );
    fprintf( pFile, "\n  );\n" );
    // write declarations
    for ( s = 0; s < 4; s++ )
        Prs_ManWriteVerilogIos( pFile, p, s );
    fprintf( pFile, "\n" );
    // write objects
    Prs_ManWriteVerilogBoxes( pFile, p );
    fprintf( pFile, "endmodule\n\n" );
}
void Prs_ManWriteVerilog( char * pFileName, Vec_Ptr_t * vPrs )
{
    Prs_Ntk_t * pNtk = Prs_ManRoot(vPrs); int i;
    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "// Design \"%s\" written by ABC on %s\n\n", Prs_NtkStr(pNtk, pNtk->iModuleName), Extra_TimeStamp() );
    Vec_PtrForEachEntry( Prs_Ntk_t *, vPrs, pNtk, i )
        Prs_ManWriteVerilogNtk( pFile, pNtk );
    fclose( pFile );
}


#if 0

/**Function*************************************************************

  Synopsis    [Writing word-level Verilog.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// compute range of a name (different from range of a multi-bit wire)
static inline int Cba_ObjGetRange( Cba_Ntk_t * p, int iObj )
{
    int i, NameId = Cba_ObjName(p, iObj);
    assert( Cba_ObjIsCi(p, iObj) );
//    if ( Cba_NameType(NameId) == CBA_NAME_INDEX )
//        NameId = Cba_ObjName(p, iObj - Abc_Lit2Var2(NameId));
    assert( Cba_NameType(NameId) == CBA_NAME_WORD || Cba_NameType(NameId) == CBA_NAME_INFO );
    for ( i = iObj + 1; i < Cba_NtkObjNum(p); i++ )
        if ( !Cba_ObjIsCi(p, i) || Cba_ObjNameType(p, i) != CBA_NAME_INDEX )
            break;
    return i - iObj;
}

static inline void Cba_ManWriteVar( Cba_Ntk_t * p, int RealName )
{
    Vec_StrPrintStr( p->pDesign->vOut, Cba_NtkStr(p, RealName) );
}
static inline void Cba_ManWriteRange( Cba_Ntk_t * p, int Beg, int End )
{
    Vec_Str_t * vStr = p->pDesign->vOut;
    Vec_StrPrintStr( vStr, "[" );
    if ( End >= 0 )
    {
        Vec_StrPrintNum( vStr, End );
        Vec_StrPrintStr( vStr, ":" );
    }
    Vec_StrPrintNum( vStr, Beg );
    Vec_StrPrintStr( vStr, "]" );
}
static inline void Cba_ManWriteConstBit( Cba_Ntk_t * p, int iObj, int fHead )
{
    Vec_Str_t * vStr = p->pDesign->vOut;
    int Const = Cba_ObjGetConst(p, iObj);
    assert( Const );
    if ( fHead )
        Vec_StrPrintStr( vStr, "1\'b" );
    if ( Const == CBA_BOX_CF )
        Vec_StrPush( vStr, '0' );
    else if ( Const == CBA_BOX_CT )
        Vec_StrPush( vStr, '1' );
    else if ( Const == CBA_BOX_CX )
        Vec_StrPush( vStr, 'x' );
    else if ( Const == CBA_BOX_CZ )
        Vec_StrPush( vStr, 'z' );
    else assert( 0 );
}
static inline int Cba_ManFindRealNameId( Cba_Ntk_t * p, int iObj )
{
    int NameId = Cba_ObjName(p, iObj);
    assert( Cba_ObjIsCi(p, iObj) );
    if ( Cba_NameType(NameId) == CBA_NAME_INDEX )
        NameId = Cba_ObjName(p, iObj - Abc_Lit2Var2(NameId));
    if ( Cba_NameType(NameId) == CBA_NAME_INFO )
        return Cba_NtkInfoName(p, Abc_Lit2Var2(NameId));
    assert( Cba_NameType(NameId) == CBA_NAME_BIN || Cba_NameType(NameId) == CBA_NAME_WORD );
    return Abc_Lit2Var2(NameId);
}
static inline int Cba_ManFindRealIndex( Cba_Ntk_t * p, int iObj )
{
    int iBit = 0, NameId = Cba_ObjName(p, iObj);
    assert( Cba_ObjIsCi(p, iObj) );
    assert( Cba_NameType(NameId) != CBA_NAME_BIN );
    if ( Cba_NameType(NameId) == CBA_NAME_INDEX )
        NameId = Cba_ObjName(p, iObj - (iBit = Abc_Lit2Var2(NameId)));
    if ( Cba_NameType(NameId) == CBA_NAME_INFO )
        return Cba_NtkInfoIndex(p, Abc_Lit2Var2(NameId), iBit);
    assert( Cba_NameType(NameId) == CBA_NAME_WORD );
    return iBit;
}
static inline void Cba_ManWriteSig( Cba_Ntk_t * p, int iObj )
{
    if ( Cba_ObjIsCo(p, iObj) )
        iObj = Cba_ObjFanin(p, iObj);
    assert( Cba_ObjIsCi(p, iObj) );
    if ( Cba_ObjGetConst(p, iObj) )
        Cba_ManWriteConstBit( p, iObj, 1 );
    else
    {
        int NameId = Cba_ObjName(p, iObj);
        if ( Cba_NameType(NameId) == CBA_NAME_BIN )
            Cba_ManWriteVar( p, Abc_Lit2Var2(NameId) );
        else
        {
            Cba_ManWriteVar( p, Cba_ManFindRealNameId(p, iObj) );
            Cba_ManWriteRange( p, Cba_ManFindRealIndex(p, iObj), -1 );
        }
    }
}
static inline void Cba_ManWriteConcat( Cba_Ntk_t * p, int iStart, int nObjs )
{
    Vec_Str_t * vStr = p->pDesign->vOut; 
    assert( nObjs >= 1 );
    if ( nObjs == 1 )
    {
        Cba_ManWriteSig( p, iStart );
        return;
    }
    Vec_StrPrintStr( vStr, "{" );
    if ( Cba_ObjIsBo(p, iStart) ) // box output
    {
        int i;
        for ( i = iStart + nObjs - 1; i >= iStart; i-- )
        {
            if ( Cba_ObjNameType(p, i) == CBA_NAME_INDEX )
                continue;
            if ( Vec_StrEntryLast(vStr) != '{' )
                Vec_StrPrintStr( vStr, ", " );
            Cba_ManWriteVar( p, Cba_ManFindRealNameId(p, i) );
        }
    }
    else if ( Cba_ObjIsBi(p, iStart) ) // box input
    {
        int e, b, k, NameId;
        for ( e = iStart - nObjs + 1; e <= iStart; )
        {
            if ( Vec_StrEntryLast(vStr) != '{' )
                Vec_StrPrintStr( vStr, ", " );
            // write constant
            if ( Cba_ObjGetConst(p, Cba_ObjFanin(p, e)) )
            {
                int fBinary = Cba_ObjIsConstBin(p, Cba_ObjFanin(p, e)-1);                
                for ( b = e + 1; b <= iStart; b++ )
                {
                    if ( !Cba_ObjGetConst(p, Cba_ObjFanin(p, b)) )
                        break;
                    if ( !Cba_ObjIsConstBin(p, Cba_ObjFanin(p, b)-1) )
                        fBinary = 0;
                }
                Vec_StrPrintNum( vStr, b - e );
                if ( fBinary && b - e > 8 ) // write hex if more than 8 bits
                {
                    int Digit = 0, nBits = ((b - e) & 3) ? (b - e) & 3 : 4;
                    Vec_StrPrintStr( vStr, "\'h" );
                    for ( k = e; k < b; k++ )
                    {
                        Digit = 2*Digit + Cba_ObjGetConst(p, Cba_ObjFanin(p, k)) - CBA_BOX_CF;
                        assert( Digit < 16 );
                        if ( --nBits == 0 )
                        {
                            Vec_StrPush( vStr, (char)(Digit < 10 ? '0' + Digit : 'a' + Digit - 10) );
                            nBits = 4;
                            Digit = 0;
                        }
                    }
                    assert( nBits == 4 );
                    assert( Digit == 0 );
                }
                else
                {
                    Vec_StrPrintStr( vStr, "\'b" );
                    for ( k = e; k < b; k++ )
                        Cba_ManWriteConstBit( p, Cba_ObjFanin(p, k), 0 );
                }
                e = b;
                continue;
            }
            // try replication
            for ( b = e + 1; b <= iStart; b++ )
                if ( Cba_ObjFanin(p, b) != Cba_ObjFanin(p, e) )
                    break;
            if ( b > e + 2 ) // more than two
            {
                Vec_StrPrintNum( vStr, b - e );
                Vec_StrPrintStr( vStr, "{" );
                Cba_ManWriteSig( p, e );
                Vec_StrPrintStr( vStr, "}" );
                e = b;
                continue;
            }
            NameId = Cba_ObjName(p, Cba_ObjFanin(p, e));
            if ( Cba_NameType(NameId) == CBA_NAME_BIN )
            {
                Cba_ManWriteVar( p, Abc_Lit2Var2(NameId) );
                e++;
                continue;
            }
            // find end of the slice
            for ( b = e + 1; b <= iStart; b++ )
                if ( Cba_ObjFanin(p, e) - Cba_ObjFanin(p, b) != b - e )
                    break;
            // write signal name
            Cba_ManWriteVar( p, Cba_ManFindRealNameId(p, Cba_ObjFanin(p, e)) );
            if ( b == e + 1 ) // literal
                Cba_ManWriteRange( p, Cba_ManFindRealIndex(p, Cba_ObjFanin(p, e)), -1 );
            else // slice or complete variable
            {
                // consider first variable of the slice
                int f = Cba_ObjFanin( p, b-1 );
                assert( Cba_ObjNameType(p, f) != CBA_NAME_BIN );
                if ( Cba_ObjNameType(p, f) == CBA_NAME_INDEX || Cba_ObjGetRange(p, f) != b - e ) // slice
                    Cba_ManWriteRange( p, Cba_ManFindRealIndex(p, f), Cba_ManFindRealIndex(p, Cba_ObjFanin(p, e)) );
                // else this is complete variable
            }
            e = b;
        }
    }
    else assert( 0 );
    Vec_StrPrintStr( vStr, "}" );
}
static inline void Cba_ManWriteGate( Cba_Ntk_t * p, int iObj )
{
    Vec_Str_t * vStr = p->pDesign->vOut; int iTerm, k;
    char * pGateName = Abc_NamStr(p->pDesign->pMods, Cba_BoxNtkId(p, iObj));
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen();
    Mio_Gate_t * pGate = Mio_LibraryReadGateByName( pLib, pGateName, NULL );
    Vec_StrPrintStr( vStr, "  " );
    Vec_StrPrintStr( vStr, pGateName );
    Vec_StrPrintStr( vStr, " " );
    Vec_StrPrintStr( vStr, Cba_ObjName(p, iObj) ? Cba_ObjNameStr(p, iObj) : "" );
    Vec_StrPrintStr( vStr, " (" );
    Cba_BoxForEachBi( p, iObj, iTerm, k )
    {
        Vec_StrPrintStr( vStr, k ? ", ." : "." );
        Vec_StrPrintStr( vStr, Mio_GateReadPinName(pGate, k) );
        Vec_StrPrintStr( vStr, "(" );
        Cba_ManWriteSig( p, iTerm );
        Vec_StrPrintStr( vStr, ")" );
    }
    Cba_BoxForEachBo( p, iObj, iTerm, k )
    {
        Vec_StrPrintStr( vStr, Cba_BoxBiNum(p, iObj) ? ", ." : "." );
        Vec_StrPrintStr( vStr, Mio_GateReadOutName(pGate) );
        Vec_StrPrintStr( vStr, "(" );
        Cba_ManWriteSig( p, iTerm );
        Vec_StrPrintStr( vStr, ")" );
    }
    Vec_StrPrintStr( vStr, ");\n" );
}
static inline void Cba_ManWriteAssign( Cba_Ntk_t * p, int iObj )
{
    Vec_Str_t * vStr = p->pDesign->vOut;
    Cba_ObjType_t Type = Cba_ObjType(p, iObj);
    int nInputs = Cba_BoxBiNum(p, iObj);
    int nOutputs = Cba_BoxBoNum(p, iObj);
    assert( nOutputs == 1 );
    Vec_StrPrintStr( vStr, "  assign " );
    Cba_ManWriteSig( p, iObj + 1 );
    Vec_StrPrintStr( vStr, " = " );
    if ( nInputs == 0 )
    {
        if ( Type == CBA_BOX_CF )
            Vec_StrPrintStr( vStr, "1\'b0" );
        else if ( Type == CBA_BOX_CT )
            Vec_StrPrintStr( vStr, "1\'b1" );
        else if ( Type == CBA_BOX_CX )
            Vec_StrPrintStr( vStr, "1\'bx" );
        else if ( Type == CBA_BOX_CZ )
            Vec_StrPrintStr( vStr, "1\'bz" );
        else assert( 0 );       
    }
    else if ( nInputs == 1 )
    {
        if ( Type == CBA_BOX_INV )
            Vec_StrPrintStr( vStr, "~" );
        else assert( Type == CBA_BOX_BUF );
        Cba_ManWriteSig( p, iObj - 1 );
    }
    else if ( nInputs == 2 )
    {
        if ( Type == CBA_BOX_NAND || Type == CBA_BOX_NOR || Type == CBA_BOX_XNOR || Type == CBA_BOX_SHARPL )
            Vec_StrPrintStr( vStr, "~" );
        Cba_ManWriteSig( p, iObj - 1 );
        if ( Type == CBA_BOX_AND || Type == CBA_BOX_SHARPL )
            Vec_StrPrintStr( vStr, " & " );
        else if ( Type == CBA_BOX_SHARP || Type == CBA_BOX_NOR )
            Vec_StrPrintStr( vStr, " & ~" );
        else if ( Type == CBA_BOX_OR )
            Vec_StrPrintStr( vStr, " | " );
        else if ( Type == CBA_BOX_NAND )
            Vec_StrPrintStr( vStr, " | ~" );
        else if ( Type == CBA_BOX_XOR || Type == CBA_BOX_XNOR )
            Vec_StrPrintStr( vStr, " ^ " );
        else assert( 0 );
        Cba_ManWriteSig( p, iObj - 2 );
    }
    Vec_StrPrintStr( vStr, ";\n" );
}
void Cba_ManWriteVerilogBoxes( Cba_Ntk_t * p, int fUseAssign )
{
    Vec_Str_t * vStr = p->pDesign->vOut;
    int iObj, k, i, o, StartPos;
    Cba_NtkForEachBox( p, iObj ) // .subckt/.gate/box (formal/actual binding) 
    {
        // skip constants
        if ( Cba_ObjIsConst(p, iObj) )
            continue;
        // write mapped
        if ( Cba_ObjIsGate(p, iObj) )
        {
            Cba_ManWriteGate( p, iObj );
            continue;
        }
        // write primitives as assign-statements
        if ( !Cba_ObjIsBoxUser(p, iObj) && fUseAssign )
        {
            Cba_ManWriteAssign( p, iObj );
            continue;
        }
        // write header
        StartPos = Vec_StrSize(vStr);
        if ( Cba_ObjIsBoxUser(p, iObj) )
        {
            int Value, Beg, End, Range;
            Cba_Ntk_t * pModel = Cba_BoxNtk( p, iObj );
            Vec_StrPrintStr( vStr, "  " );
            Vec_StrPrintStr( vStr, Cba_NtkName(pModel) );
            Vec_StrPrintStr( vStr, " " );
            Vec_StrPrintStr( vStr, Cba_ObjName(p, iObj) ? Cba_ObjNameStr(p, iObj) : ""  );
            Vec_StrPrintStr( vStr, " (" );
            // write arguments
            i = o = 0;
            assert( Cba_NtkInfoNum(pModel) );
            Vec_IntForEachEntryTriple( &pModel->vInfo, Value, Beg, End, k )
            {
                int NameId = Abc_Lit2Var2( Value );
                int Type = Abc_Lit2Att2( Value );
                Vec_StrPrintStr( vStr, k ? ", " : "" );
                if ( Vec_StrSize(vStr) > StartPos + 70 )
                {
                    StartPos = Vec_StrSize(vStr);
                    Vec_StrPrintStr( vStr, "\n    " );
                }
                Vec_StrPrintStr( vStr, "." );
                Vec_StrPrintStr( vStr, Cba_NtkStr(p, NameId) );
                Vec_StrPrintStr( vStr, "(" );
                Range = Cba_InfoRange( Beg, End );
                assert( Range > 0 );
                if ( Type == 1 )
                    Cba_ManWriteConcat( p, Cba_BoxBi(p, iObj, i), Range ), i += Range;
                else if ( Type == 2 )
                    Cba_ManWriteConcat( p, Cba_BoxBo(p, iObj, o), Range ), o += Range;
                else assert( 0 );
                Vec_StrPrintStr( vStr, ")" );
            }
            assert( i == Cba_BoxBiNum(p, iObj) );
            assert( o == Cba_BoxBoNum(p, iObj) );
        }
        else
        {
            int iTerm, k, Range, iSig = 0;
            Vec_Int_t * vBits = Cba_BoxCollectRanges( p, iObj );
            char * pName = Cba_NtkGenerateName( p, Cba_ObjType(p, iObj), vBits );
            char * pSymbs = Cba_ManPrimSymb( p->pDesign, Cba_ObjType(p, iObj) );
            Vec_StrPrintStr( vStr, "  " );
            Vec_StrPrintStr( vStr, pName );
            Vec_StrPrintStr( vStr, " " );
            Vec_StrPrintStr( vStr, Cba_ObjName(p, iObj) ? Cba_ObjNameStr(p, iObj) : ""  );
            Vec_StrPrintStr( vStr, " (" );
            // write inputs
            Cba_BoxForEachBiMain( p, iObj, iTerm, k )
            {
                Range = Vec_IntEntry( vBits, iSig );
                Vec_StrPrintStr( vStr, iSig ? ", " : "" );
                if ( Vec_StrSize(vStr) > StartPos + 70 )
                {
                    StartPos = Vec_StrSize(vStr);
                    Vec_StrPrintStr( vStr, "\n    " );
                }
                Vec_StrPrintStr( vStr, "." );
                Vec_StrPush( vStr, pSymbs[iSig] );
                Vec_StrPrintStr( vStr, "(" );
                Cba_ManWriteConcat( p, iTerm, Range );
                Vec_StrPrintStr( vStr, ")" );
                iSig++;
            }
            Cba_BoxForEachBoMain( p, iObj, iTerm, k )
            {
                Range = Vec_IntEntry( vBits, iSig );
                Vec_StrPrintStr( vStr, iSig ? ", " : "" );
                if ( Vec_StrSize(vStr) > StartPos + 70 )
                {
                    StartPos = Vec_StrSize(vStr);
                    Vec_StrPrintStr( vStr, "\n    " );
                }
                Vec_StrPrintStr( vStr, "." );
                Vec_StrPush( vStr, pSymbs[iSig] );
                Vec_StrPrintStr( vStr, "(" );
                Cba_ManWriteConcat( p, iTerm, Range );
                Vec_StrPrintStr( vStr, ")" );
                iSig++;
            }
            assert( iSig == Vec_IntSize(vBits) );
        }
        Vec_StrPrintStr( vStr, ");\n" );
    }
}
void Cba_ManWriteVerilogNtk( Cba_Ntk_t * p, int fUseAssign )
{
    char * pKeyword[4] = { "wire ", "input ", "output ", "inout " };
    Vec_Str_t * vStr = p->pDesign->vOut;
    int k, iObj, iTerm, Value, Beg, End, Length, fHaveWires, StartPos;
//    assert( Cba_NtkInfoNum(p) );
    assert( Vec_IntSize(&p->vFanin) == Cba_NtkObjNum(p) );
//    Cba_NtkPrint( p );
    // write header
    Vec_StrPrintStr( vStr, "module " );
    Vec_StrPrintStr( vStr, Cba_NtkName(p) );
    Vec_StrPrintStr( vStr, " (\n    " );
    StartPos = Vec_StrSize(vStr);
    Vec_IntForEachEntryTriple( &p->vInfo, Value, Beg, End, k )
    if ( Abc_Lit2Att2(Value) != 0 )
    {
        Vec_StrPrintStr( vStr, k ? ", " : "" );
        if ( Vec_StrSize(vStr) > StartPos + 70 )
        {
            StartPos = Vec_StrSize(vStr);
            Vec_StrPrintStr( vStr, "\n    " );
        }
        Cba_ManWriteVar( p, Abc_Lit2Var2(Value) );
    }
    Vec_StrPrintStr( vStr, "\n  );\n" );
    // write inputs/outputs
    Vec_IntForEachEntryTriple( &p->vInfo, Value, Beg, End, k )
    if ( Abc_Lit2Att2(Value) != 0 )
    {
        Vec_StrPrintStr( vStr, "  " );
        Vec_StrPrintStr( vStr, pKeyword[Abc_Lit2Att2(Value)] );
        if ( Beg >= 0 )
            Cba_ManWriteRange( p, Beg, End );
        Cba_ManWriteVar( p, Abc_Lit2Var2(Value) );
        Vec_StrPrintStr( vStr, ";\n" );
    }
    Vec_StrPrintStr( vStr, "\n" );
    // write word-level wires
    Cba_NtkForEachBox( p, iObj )
    if ( !Cba_ObjIsConst(p, iObj) )
        Cba_BoxForEachBo( p, iObj, iTerm, k )
        if ( Cba_ObjNameType(p, iTerm) == CBA_NAME_WORD || Cba_ObjNameType(p, iTerm) == CBA_NAME_INFO )
        {
            Vec_StrPrintStr( vStr, "  wire " );
            Cba_ManWriteRange( p, Cba_ManFindRealIndex(p, iTerm), Cba_ManFindRealIndex(p, iTerm + Cba_ObjGetRange(p, iTerm) - 1) );
            Cba_ManWriteVar( p, Cba_ManFindRealNameId(p, iTerm) );
            Vec_StrPrintStr( vStr, ";\n" );
        }
    // check if there are any wires left
    fHaveWires = 0;
    Cba_NtkForEachBox( p, iObj )
    if ( !Cba_ObjIsConst(p, iObj) )
        Cba_BoxForEachBo( p, iObj, iTerm, k )
        if ( Cba_ObjNameType(p, iTerm) == CBA_NAME_BIN )
        { fHaveWires = 1; iObj = Cba_NtkObjNum(p); break; }
    // write bit-level wires
    if ( fHaveWires )
    {
        Length = 7;
        Vec_StrPrintStr( vStr, "\n  wire " );
        Cba_NtkForEachBox( p, iObj )
        if ( !Cba_ObjIsConst(p, iObj) )
            Cba_BoxForEachBo( p, iObj, iTerm, k )
            if ( Cba_ObjNameType(p, iTerm) == CBA_NAME_BIN )
            {
                if ( Length > 72 )
                    Vec_StrPrintStr( vStr, ";\n  wire " ), Length = 7;
                if ( Length > 7 )
                    Vec_StrPrintStr( vStr, ", " );
                Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iTerm) ); 
                Length += strlen(Cba_ObjNameStr(p, iTerm));
            }
        Vec_StrPrintStr( vStr, ";\n" );
    }
    Vec_StrPrintStr( vStr, "\n" );
    // write objects
    Cba_ManWriteVerilogBoxes( p, fUseAssign );
    Vec_StrPrintStr( vStr, "endmodule\n\n" );
}
void Cba_ManWriteVerilog( char * pFileName, Cba_Man_t * p, int fUseAssign )
{
    Cba_Ntk_t * pNtk; int i;
    // check the library
    if ( p->pMioLib && p->pMioLib != Abc_FrameReadLibGen() )
    {
        printf( "Genlib library used in the mapped design is not longer a current library.\n" );
        return;
    }
    // derive the stream
    p->vOut = Vec_StrAlloc( 10000 );
    p->vOut2 = Vec_StrAlloc( 1000 );
    Vec_StrPrintStr( p->vOut, "// Design \"" );
    Vec_StrPrintStr( p->vOut, Cba_ManName(p) );
    Vec_StrPrintStr( p->vOut, "\" written via CBA package in ABC on " );
    Vec_StrPrintStr( p->vOut, Extra_TimeStamp() );
    Vec_StrPrintStr( p->vOut, "\n\n" );
    Cba_ManAssignInternWordNames( p );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManWriteVerilogNtk( pNtk, fUseAssign );
    // dump into file
    if ( p->vOut && Vec_StrSize(p->vOut) > 0 )
    {
        FILE * pFile = fopen( pFileName, "wb" );
        if ( pFile == NULL )
            printf( "Cannot open file \"%s\" for writing.\n", pFileName );
        else
        {
            fwrite( Vec_StrArray(p->vOut), 1, Vec_StrSize(p->vOut), pFile );
            fclose( pFile );
        }
    }
    Vec_StrFreeP( &p->vOut );
    Vec_StrFreeP( &p->vOut2 );
}

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

