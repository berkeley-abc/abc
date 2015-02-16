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
void Prs_ManWriteVerilogConcat( FILE * pFile, Prs_Ntk_t * p, int Con )
{
    extern void Prs_ManWriteVerilogArray( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs, int Start, int Stop, int fOdd );
    Vec_Int_t * vSigs = Prs_CatSignals(p, Con);
    fprintf( pFile, "{" );
    Prs_ManWriteVerilogArray( pFile, p, vSigs, 0, Vec_IntSize(vSigs), 0 );
    fprintf( pFile, "}" );
}
void Prs_ManWriteVerilogSignal( FILE * pFile, Prs_Ntk_t * p, int Sig )
{
    int Value = Abc_Lit2Var2( Sig );
    Prs_ManType_t Type = Abc_Lit2Att2( Sig );
    if ( Type == CBA_PRS_NAME || Type == CBA_PRS_CONST )
        fprintf( pFile, "%s", Prs_NtkStr(p, Value) );
    else if ( Type == CBA_PRS_SLICE )
        fprintf( pFile, "%s%s", Prs_NtkStr(p, Prs_SliceName(p, Value)), Prs_NtkStr(p, Prs_SliceRange(p, Value)) );
    else if ( Type == CBA_PRS_CONCAT )
        Prs_ManWriteVerilogConcat( pFile, p, Value );
    else assert( 0 );
}
void Prs_ManWriteVerilogArray( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs, int Start, int Stop, int fOdd )
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
void Prs_ManWriteVerilogArray2( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs )
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
void Prs_ManWriteVerilogMux( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs )
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
void Prs_ManWriteVerilogBoxes( FILE * pFile, Prs_Ntk_t * p )
{
    Vec_Int_t * vBox; int i;
    Prs_NtkForEachBox( p, vBox, i )
    {
        int NtkId = Prs_BoxNtk(p, i);
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
void Prs_ManWriteVerilogIos( FILE * pFile, Prs_Ntk_t * p, int SigType )
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
void Prs_ManWriteVerilogIoOrder( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vOrder )
{
    int i, NameId;
    Vec_IntForEachEntry( vOrder, NameId, i )
        fprintf( pFile, "%s%s", Prs_NtkStr(p, NameId), i == Vec_IntSize(vOrder) - 1 ? "" : ", " );
}
void Prs_ManWriteVerilogNtk( FILE * pFile, Prs_Ntk_t * p )
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



/**Function*************************************************************

  Synopsis    [Writing word-level Verilog.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_ManWriteRange( Cba_Ntk_t * p, int Beg, int End )
{
    Vec_Str_t * vStr = p->pDesign->vOut;
    Vec_StrPrintStr( vStr, "[" );
    Vec_StrPrintNum( vStr, End );
    Vec_StrPrintStr( vStr, ":" );
    Vec_StrPrintNum( vStr, Beg );
    Vec_StrPrintStr( vStr, "]" );
}
void Cba_ManWriteLit( Cba_Ntk_t * p, int NameId, int iBit )
{
    Vec_Str_t * vStr = p->pDesign->vOut;
    Vec_StrPrintStr( vStr, Cba_NtkStr(p, NameId) );
    if ( iBit == -1 )
        return;
    Vec_StrPrintStr( vStr, "[" );
    Vec_StrPrintNum( vStr, iBit );
    Vec_StrPrintStr( vStr, "]" );
}
void Cba_ManWriteSig( Cba_Ntk_t * p, int iObj )
{
    int iNameId = Cba_ObjName(p, iObj);
    if ( Cba_NameType(iNameId) == CBA_NAME_BIN )
        Cba_ManWriteLit( p, Abc_Lit2Var2(iNameId), -1 );
    else if ( Cba_NameType(iNameId) == CBA_NAME_WORD )
        Cba_ManWriteLit( p, Abc_Lit2Var2(iNameId), 0 );
    else if ( Cba_NameType(iNameId) == CBA_NAME_INDEX )
    {
        int iBit = Abc_Lit2Var2(iNameId);
        iNameId = Cba_ObjName(p, iObj - iBit);
        if ( Cba_NameType(iNameId) == CBA_NAME_WORD )
            Cba_ManWriteLit( p, Abc_Lit2Var2(iNameId), iBit );
        else if ( Cba_NameType(iNameId) == CBA_NAME_INFO )
            Cba_ManWriteLit( p, Cba_NtkInfoName(p, Abc_Lit2Var2(iNameId)), Cba_NtkInfoIndex(p, Abc_Lit2Var2(iNameId), iBit) );
        else assert( 0 );
    }
    else if ( Cba_NameType(iNameId) == CBA_NAME_INFO )
        Cba_ManWriteLit( p, Cba_NtkInfoName(p, Abc_Lit2Var2(iNameId)), Cba_NtkInfoIndex(p, Abc_Lit2Var2(iNameId), 0) );
    else assert( 0 );
}
/*
void Cba_ManWriteSlices( Cba_Ntk_t * p, Vec_Int_t * vSigs )
{
    int Entry, NameId, Beg, End, j;
    Vec_Str_t * vStr = p->pDesign->vOut; 
    Vec_StrClear( vStr );
    Vec_StrPrintStr( vStr, "{" );
    Vec_IntForEachEntry( vSigs, NameId, Beg )
    {
        if ( Vec_StrEntryLast(vStr) != '{' )
            Vec_StrPrintStr( vStr, ", " );
        if ( NameId < 0 ) // constant
        {
            Vec_IntForEachEntryStart( vSigs, Entry, End, Beg+1 )
                if ( Entry >= 0 )
                    break;
            Vec_StrPrintNum( vStr, End - Beg );
            Vec_StrPrintStr( vStr, "b\'" );
            Vec_IntForEachEntryStartStop( vSigs, NameId, j, Beg, End )
            {
                if ( -NameId == CBA_BOX_CF )
                    Vec_StrPush( vStr, '0' );
                else if ( -NameId == CBA_BOX_CT )
                    Vec_StrPush( vStr, '1' );
                else if ( -NameId == CBA_BOX_CX )
                    Vec_StrPush( vStr, 'x' );
                else if ( -NameId == CBA_BOX_CZ )
                    Vec_StrPush( vStr, 'z' );
                else assert( 0 );
            }
        }
        else if ( Cba_NameType(NameId) == CBA_NAME_BIN ) // bin
        {
            Cba_ManWriteLit( p, Abc_Lit2Var2(NameId), -1 );
        }
        else if ( Cba_NameType(NameId) == CBA_NAME_WORD || Cba_NameType(NameId) == CBA_NAME_INDEX ) // word
        {
            Vec_IntForEachEntryStart( vSigs, Entry, End, Beg+1 )
                if ( Cba_NameType(Entry) != CBA_NAME_INDEX )
                    break;
            // the whole word is there
            if ( Cba_NameType(NameId) == CBA_NAME_WORD && Cba_ObjGetRange(p, 0) == End - Beg )
                Cba_ManWriteLit( p, Abc_Lit2Var2(NameId), -1 );
            else if ( End - Beg == 1 )
                Cba_ManWriteLit( p, Abc_Lit2Var2(NameId), Beg );
            else
            {
                Cba_ManWriteLit( p, Abc_Lit2Var2(NameId), -1 );
                Cba_ManWriteRange( p, Beg, End-1 );
            }
        }
        else assert( 0 );
    }
    Vec_StrPrintStr( vStr, "}" );
    Vec_StrReverseOrder( vStr );
    Vec_StrPush( vStr, '\0' );
}
void Cba_ManWriteConcat( Cba_Ntk_t * p, int iStart, int nObjs )
{
    Vec_Str_t * vStr = p->pDesign->vOut; int i;
    assert( nObjs >= 1 );
    if ( nObjs == 1 )
        Cba_ManWriteSig( p, iStart );
    else
    {
        // collect fanins
        Vec_IntClear( &p->vArray );
        for ( i = 0; i < nObjs; i++ )
        {
            if ( Cba_ObjIsBo(p, iStart) )
                Vec_IntPush( &p->vArray, iStart + i );
            else if ( Cba_ObjIsBi(p, iStart) )
            {
                int iFanin = Cba_ObjFanin(p, iStart - i);
                int Const  = Cba_ObjGetConst(p, iFanin);
                Vec_IntPush( &p->vArray, Const ? Const : Cba_ObjName(p, iFanin) );
            }
            else assert( 0 );
        }
        ABC_SWAP( Vec_Str_t *, p->pDesign->vOut, p->pDesign->vOut2 );
        Cba_ManWriteSlices( p, &p->vArray );
        ABC_SWAP( Vec_Str_t *, p->pDesign->vOut, p->pDesign->vOut2 );
        Vec_StrAppend( vStr, Vec_StrArray(p->pDesign->vOut2) );
    }
}
*/
void Cba_ManWriteConcat( Cba_Ntk_t * p, int iStart, int nObjs )
{
    Vec_Str_t * vStr = p->pDesign->vOut; int i;
    assert( nObjs >= 1 );
    if ( nObjs == 1 )
        Cba_ManWriteSig( p, iStart );
    else
    {
        Vec_StrPrintStr( vStr, "{" );
        for ( i = nObjs - 1; i >= 0; i-- )
        {
            Vec_StrPrintStr( vStr, i < nObjs - 1 ? ", " : "" );
            if ( Cba_ObjIsBo(p, iStart) )
                Cba_ManWriteSig( p, iStart + i );
            else if ( Cba_ObjIsBi(p, iStart) )
                Cba_ManWriteSig( p, Cba_ObjFanin(p, iStart - i) );
            else assert( 0 );
        }
        Vec_StrPrintStr( vStr, "}" );
    }
}
void Cba_ManWriteGate( Cba_Ntk_t * p, int iObj )
{
    Vec_Str_t * vStr = p->pDesign->vOut; int iTerm, k;
    char * pGateName = Abc_NamStr(p->pDesign->pMods, Cba_BoxNtkId(p, iObj));
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen( Abc_FrameGetGlobalFrame() );
    Mio_Gate_t * pGate = Mio_LibraryReadGateByName( pLib, pGateName, NULL );
    Vec_StrPrintStr( vStr, "  " );
    Vec_StrPrintStr( vStr, pGateName );
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
    Vec_StrPrintStr( vStr, " );\n" );
}
void Cba_ManWriteAssign( Cba_Ntk_t * p, int iObj )
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
        if ( Type == CBA_BOX_XNOR )
        {
            Vec_StrPrintStr( vStr, "~" );
            Type = CBA_BOX_XOR;
        }
        Cba_ManWriteSig( p, iObj - 1 );
        if ( Type == CBA_BOX_AND )
            Vec_StrPrintStr( vStr, " & " );
        else if ( Type == CBA_BOX_OR )
            Vec_StrPrintStr( vStr, " | " );
        else if ( Type == CBA_BOX_XOR )
            Vec_StrPrintStr( vStr, " ^ " );
        else assert( 0 );
        Cba_ManWriteSig( p, iObj - 2 );
    }
    Vec_StrPrintStr( vStr, ";\n" );
}
void Cba_ManWriteVerilogBoxes( Cba_Ntk_t * p )
{
    Vec_Str_t * vStr = p->pDesign->vOut;
    int iObj, k, i, o;
    Cba_NtkForEachBox( p, iObj ) // .subckt/.gate/box (formal/actual binding) 
    {
        Cba_Ntk_t * pModel = NULL;
        char * pName = NULL;
        // write mapped
        if ( Cba_ObjIsGate(p, iObj) )
        {
            Cba_ManWriteGate( p, iObj );
            continue;
        }
        // write primitives as assign-statements
        if ( Cba_BoxNtkName(p, iObj) == NULL )
        {
            Cba_ManWriteAssign( p, iObj );
            continue;
        }

        // write header
        if ( Cba_ObjIsBoxUser(p, iObj) )
            pModel = Cba_BoxNtk( p, iObj );
        else if ( Cba_BoxNtkId(p, iObj) )
            pName = Cba_BoxNtkName(p, iObj);
        else assert( 0 );
        Vec_StrPrintStr( vStr, "  " );
        Vec_StrPrintStr( vStr, pModel ? Cba_NtkName(pModel) : pName );
        Vec_StrPrintStr( vStr, " " );
        Vec_StrPrintStr( vStr, Cba_ObjName(p, iObj) ? Cba_ObjNameStr(p, iObj) : ""  );

        // write arguments
        i = o = 0;
        Vec_StrPrintStr( vStr, " (" );
        if ( pModel )
        {
            int Value, Beg, End, Range;
            assert( Cba_NtkInfoNum(pModel) );
            Vec_IntForEachEntryTriple( &pModel->vInfo, Value, Beg, End, k )
            {
                int NameId = Abc_Lit2Var2( Value );
                int Type = Abc_Lit2Att2( Value );
                Vec_StrPrintStr( vStr, k ? ", ." : "." );
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
        }
        else
        {
            int pRanges[8]; char pSymbs[8];
            int nSigs = Cba_NtkNameRanges( pName, pRanges, pSymbs );
            for ( k = 0; k < nSigs; k++ )
            {
                Vec_StrPrintStr( vStr, k ? ", ." : "." );
                Vec_StrPush( vStr, pSymbs[k] );
                Vec_StrPrintStr( vStr, "(" );
                if ( k < nSigs - 1 )
                    Cba_ManWriteConcat( p, Cba_BoxBi(p, iObj, i), pRanges[k] ), i += pRanges[k];
                else 
                    Cba_ManWriteConcat( p, Cba_BoxBo(p, iObj, o), pRanges[k] ), o += pRanges[k];
                Vec_StrPrintStr( vStr, ")" );
            }
        }
        Vec_StrPrintStr( vStr, " );\n" );
        assert( i == Cba_BoxBiNum(p, iObj) );
        assert( o == Cba_BoxBoNum(p, iObj) );
    }
}
void Cba_ManWriteVerilogNtk( Cba_Ntk_t * p )
{
    char * pKeyword[4] = { "wire ", "input ", "output ", "inout " };
    Vec_Str_t * vStr = p->pDesign->vOut;
    int k, iObj, iTerm, Value, Beg, End, Length;
    assert( Cba_NtkInfoNum(p) );
    assert( Vec_IntSize(&p->vFanin) == Cba_NtkObjNum(p) );
//    Cba_NtkPrint( p );
    // write header
    Vec_StrPrintStr( vStr, "module " );
    Vec_StrPrintStr( vStr, Cba_NtkName(p) );
    Vec_StrPrintStr( vStr, " (\n    " );
    Vec_IntForEachEntryTriple( &p->vInfo, Value, Beg, End, k )
    if ( Abc_Lit2Att2(Value) != 0 )
    {
        Vec_StrPrintStr( vStr, k ? ", " : "" );
        Vec_StrPrintStr( vStr, Cba_NtkStr(p, Abc_Lit2Var2(Value)) );
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
        Vec_StrPrintStr( vStr, Cba_NtkStr(p, Abc_Lit2Var2(Value)) );
        Vec_StrPrintStr( vStr, ";\n" );
    }
    Vec_StrPrintStr( vStr, "\n" );
    // write word-level wires
    Cba_NtkForEachBox( p, iObj )
    Cba_BoxForEachBo( p, iObj, iTerm, k )
        if ( Cba_NameType(Cba_ObjName(p, iTerm)) == CBA_NAME_WORD )
        {
            int Beg, End;
            Cba_ObjGetRange( p, iTerm, &Beg, &End );
            Vec_StrPrintStr( vStr, "  wire " );
            Cba_ManWriteRange( p, Beg, End );
            Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iTerm) );
            Vec_StrPrintStr( vStr, ";\n" );
        }
    // write bit-level wires
    Length = 7;
    Vec_StrPrintStr( vStr, "  wire " );
    Cba_NtkForEachBox( p, iObj )
    Cba_BoxForEachBo( p, iObj, iTerm, k )
        if ( Cba_NameType(Cba_ObjName(p, iTerm)) == CBA_NAME_BIN )
        {
            if ( Length > 72 )
                Vec_StrPrintStr( vStr, ";\n  wire " ), Length = 7;
            if ( Length > 7 )
                Vec_StrPrintStr( vStr, ", " );
            Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iTerm) ); 
            Length += strlen(Cba_ObjNameStr(p, iTerm));
        }
    Vec_StrPrintStr( vStr, ";\n\n" );
    // write objects
    Cba_ManWriteVerilogBoxes( p );
    Vec_StrPrintStr( vStr, "endmodule\n\n" );
}
void Cba_ManWriteVerilog( char * pFileName, Cba_Man_t * p )
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
    Cba_ManAssignInternNames( p );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManWriteVerilogNtk( pNtk );
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


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

