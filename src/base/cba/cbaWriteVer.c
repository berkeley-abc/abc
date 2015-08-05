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
    extern void Prs_ManWriteVerilogArray( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs, int fOdd );
    Vec_Int_t * vSigs = Prs_CatSignals(p, Con);
    fprintf( pFile, "{" );
    Prs_ManWriteVerilogArray( pFile, p, vSigs, 0 );
    fprintf( pFile, "}" );
}
static void Prs_ManWriteVerilogSignal( FILE * pFile, Prs_Ntk_t * p, int Sig )
{
    int Value = Abc_Lit2Var2( Sig );
    Prs_ManType_t Type = (Prs_ManType_t)Abc_Lit2Att2( Sig );
    if ( Type == CBA_PRS_NAME )
        fprintf( pFile, "%s", Prs_NtkStr(p, Value) );
    else if ( Type == CBA_PRS_CONST )
        fprintf( pFile, "%s", Prs_NtkConst(p, Value) );
    else if ( Type == CBA_PRS_SLICE )
        fprintf( pFile, "%s%s", Prs_NtkStr(p, Prs_SliceName(p, Value)), Prs_NtkStr(p, Prs_SliceRange(p, Value)) );
    else if ( Type == CBA_PRS_CONCAT )
        Prs_ManWriteVerilogConcat( pFile, p, Value );
    else assert( 0 );
}
void Prs_ManWriteVerilogArray( FILE * pFile, Prs_Ntk_t * p, Vec_Int_t * vSigs, int fOdd )
{
    int i, Sig, fFirst = 1;
    assert( Vec_IntSize(vSigs) > 0 );
    Vec_IntForEachEntry( vSigs, Sig, i )
    {
        if ( fOdd && !(i & 1) )
            continue;
        fprintf( pFile, "%s", fFirst ? "" : ", " );
        Prs_ManWriteVerilogSignal( pFile, p, Sig );
        fFirst = 0;
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
    Prs_ManWriteVerilogSignal( pFile, p, Vec_IntEntry(vSigs, 1) );
    fprintf( pFile, "%s", pStrs[0] );
    Vec_IntForEachEntryDoubleStart( vSigs, FormId, ActSig, i, 2 )
    {
        Prs_ManWriteVerilogSignal( pFile, p, ActSig );
        fprintf( pFile, "%s", pStrs[i/2] );
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
            Prs_ManWriteVerilogArray( pFile, p, vBox, 1 );
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
        fprintf( pFile, "%s%s", Prs_NtkStr(p, Abc_Lit2Var2(NameId)), i == Vec_IntSize(vOrder) - 1 ? "" : ", " );
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




/**Function*************************************************************
  
  Synopsis    []  
  
  Description []  
                 
  SideEffects []  
  
  SeeAlso     []  
  
***********************************************************************/
void Cba_ManCreatePrimMap( char ** pMap )
{
    memset( pMap, 0, sizeof(char *) * CBA_BOX_LAST );
    pMap[ CBA_BOX_BUF    ] = "";
    pMap[ CBA_BOX_INV    ] = "~";
    pMap[ CBA_BOX_AND    ] = "&"; 
    pMap[ CBA_BOX_NAND   ] = "~&"; 
    pMap[ CBA_BOX_OR     ] = "|"; 
    pMap[ CBA_BOX_NOR    ] = "~|"; 
    pMap[ CBA_BOX_XOR    ] = "^"; 
    pMap[ CBA_BOX_XNOR   ] = "~^"; 
    pMap[ CBA_BOX_SHARP  ] = "&"; 
    pMap[ CBA_BOX_SHARPL ] = "&"; 
    pMap[ CBA_BOX_MUX    ] = "?"; 
    pMap[ CBA_BOX_MAJ    ] = NULL; 
    pMap[ CBA_BOX_RAND   ] = "&"; 
    pMap[ CBA_BOX_RNAND  ] = "~&"; 
    pMap[ CBA_BOX_ROR    ] = "|"; 
    pMap[ CBA_BOX_RNOR   ] = "~|"; 
    pMap[ CBA_BOX_RXOR   ] = "^"; 
    pMap[ CBA_BOX_RXNOR  ] = "~^"; 
    pMap[ CBA_BOX_LNOT   ] = "!"; 
    pMap[ CBA_BOX_LAND   ] = "&&"; 
    pMap[ CBA_BOX_LNAND  ] = NULL; 
    pMap[ CBA_BOX_LOR    ] = "||"; 
    pMap[ CBA_BOX_LNOR   ] = NULL; 
    pMap[ CBA_BOX_LXOR   ] = "^^"; 
    pMap[ CBA_BOX_LXNOR  ] = NULL; 
    pMap[ CBA_BOX_NMUX   ] = NULL; 
    pMap[ CBA_BOX_SEL    ] = NULL; 
    pMap[ CBA_BOX_PSEL   ] = NULL; 
    pMap[ CBA_BOX_ENC    ] = NULL; 
    pMap[ CBA_BOX_PENC   ] = NULL; 
    pMap[ CBA_BOX_DEC    ] = NULL; 
    pMap[ CBA_BOX_EDEC   ] = NULL; 
    pMap[ CBA_BOX_ADD    ] = "+"; 
    pMap[ CBA_BOX_SUB    ] = "-"; 
    pMap[ CBA_BOX_MUL    ] = "*"; 
    pMap[ CBA_BOX_DIV    ] = "/"; 
    pMap[ CBA_BOX_MOD    ] = NULL; 
    pMap[ CBA_BOX_REM    ] = "%%"; 
    pMap[ CBA_BOX_POW    ] = "**"; 
    pMap[ CBA_BOX_MIN    ] = "-"; 
    pMap[ CBA_BOX_ABS    ] = NULL; 
    pMap[ CBA_BOX_LTHAN  ] = "<"; 
    pMap[ CBA_BOX_LETHAN ] = "<="; 
    pMap[ CBA_BOX_METHAN ] = ">="; 
    pMap[ CBA_BOX_MTHAN  ] = ">"; 
    pMap[ CBA_BOX_EQU    ] = "=="; 
    pMap[ CBA_BOX_NEQU   ] = "!="; 
    pMap[ CBA_BOX_SHIL   ] = "<<"; 
    pMap[ CBA_BOX_SHIR   ] = ">>"; 
    pMap[ CBA_BOX_ROTL   ] = NULL; 
    pMap[ CBA_BOX_ROTR   ] = NULL; 
}


#ifdef WIN32
#define vsnprintf _vsnprintf
#endif

#include <stdio.h>

//extern int vsnprintf(char * s, size_t n, const char * format, va_list arg);

static inline void Vec_StrPrintF( Vec_Str_t * p, const char * format, ... )
{
    va_list args;
    char * pBuffer;
    int nBuffer, nSize = 1000; 
    va_start( args, format );
    Vec_StrGrow( p, Vec_StrSize(p) + nSize );
    pBuffer = Vec_StrArray(p) + Vec_StrSize(p);
    nBuffer = vsnprintf( pBuffer, nSize, format, args );
    if ( nBuffer > nSize )
    {
        Vec_StrGrow( p, Vec_StrSize(p) + nBuffer + nSize );
        pBuffer = Vec_StrArray(p) + Vec_StrSize(p);
        nSize = vsnprintf( pBuffer, nBuffer, format, args );
        assert( nSize == nBuffer );
    }
    p->nSize += nBuffer;
    va_end( args );
}


// considers word-level signal and returns bit-level signal
int Cba_ObjFindOne( Cba_Ntk_t * p, int iFon )
{
    int Range = Cba_FonRange( p, iFon );
    if ( Range == 1 )
    {
        if ( Cba_FonIsConst(iFon) )
            return Cba_FonConst(iFon) == 1 ? 0 : -1;
        return iFon;
    }
    assert( Range > 1 );
    if ( Cba_FonIsConst(iFon) )
    {
        int i; char Digit = 0;
        char * s = Cba_NtkConst( p, Cba_FonConst(iFon) );
        while ( *s != 'b' ) s++;
        assert( *s == 'b' );
        for ( i = 1; i <= Range; i++ )
        {
            if ( Digit == 0 )
                Digit = s[i];
            else if ( Digit != s[i] )
                return -1;
        }
        return s[1] == '0' ? 0 : -1;
    }
    else
    {
        int iObj = Cba_FonObj( p, iFon );
        int i, iFin, iFon, OneFon = ABC_INFINITY;
        if ( Cba_ObjType(p, iObj) != CBA_BOX_CATIN )
            return -1;
        Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
            if ( OneFon == ABC_INFINITY )
                OneFon = iFon;
            else if ( OneFon != iFon )
                return -1;
        assert( Cba_FonIsReal(OneFon) );
        Range = Cba_FonRange( p, OneFon );
        return Range == 1 ? OneFon : -1;
    }
}
void Cba_ManWriteFonRange( Cba_Ntk_t * p, int iFon )
{
    Vec_Str_t * vStr = &p->pDesign->vOut;
    if ( Cba_FonIsConst(iFon) || (Cba_FonRange(p, iFon) == 1 && Cba_FonRight(p, iFon) == 0) )
        return;
/*
    Vec_StrPush( vStr, '[' );
    Vec_StrPrintNum( vStr, Cba_FonLeft(p, iFon) );
    Vec_StrPush( vStr, ':' );
    Vec_StrPrintNum( vStr, Cba_FonRight(p, iFon) );
    Vec_StrPush( vStr, ']' );
    Vec_StrPush( vStr, ' ' );
*/
    Vec_StrPrintF( vStr, "[%d:%d] ", Cba_FonLeft(p, iFon), Cba_FonRight(p, iFon) );

}
void Cba_ManWriteFonName( Cba_Ntk_t * p, int iFon, int fInlineConcat, int fInput )
{
    extern void Cba_ManWriteCatIn( Cba_Ntk_t * p, int iObj );
    Vec_Str_t * vStr = &p->pDesign->vOut;
    if ( !iFon || (!Cba_FonIsConst(iFon) && !Cba_FonName(p, iFon)) ) 
//    {
//        Vec_StrPrintStr( vStr, "Open_" );
//        Vec_StrPrintNum( vStr, Cba_NtkMan(p)->nOpens++ );
//        return;
//    }
        Vec_StrPrintF( vStr, "Open_%d", Cba_NtkMan(p)->nOpens++ );
    else

    if ( fInlineConcat && !Cba_FonIsConst(iFon) && Cba_ObjIsCatIn(p, Cba_FonObj(p, iFon)) )
        Cba_ManWriteCatIn( p, Cba_FonObj(p, iFon) );
    else
    {
        int Range = fInput ? Cba_FonRange( p, iFon ) : 0;
        if ( fInput && Range > 1 )
            Vec_StrPush( vStr, '{' );
//        if ( Cba_FonIsConst(iFon) )
//            Vec_StrPrintStr( vStr, Cba_NtkConst(p, Cba_FonConst(iFon)) );
//        else 
//            Vec_StrPrintStr( vStr, Cba_FonNameStr(p, iFon) );
        Vec_StrPrintStr( vStr, Cba_FonIsConst(iFon) ? Cba_NtkConst(p, Cba_FonConst(iFon)) : Cba_FonNameStr(p, iFon) );
        if ( fInput && Range > 1 )
            Vec_StrPush( vStr, '}' );
    }
}
void Cba_ManWriteCatIn( Cba_Ntk_t * p, int iObj )
{
    int i, iFin, iFon;
    Vec_Str_t * vStr = &p->pDesign->vOut;
    assert( Cba_ObjIsCatIn(p, iObj) );
    Vec_StrPush( vStr, '{' );
    Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
    {
        Vec_StrPrintStr( vStr, i ? ", " : "" );
        Cba_ManWriteFonName( p, iFon, 1, 0 );
    }
    Vec_StrPush( vStr, '}' );
}
void Cba_ManWriteCatOut( Cba_Ntk_t * p, int iObj )
{
    int i, iFon;
    Vec_Str_t * vStr = &p->pDesign->vOut;
    assert( Cba_ObjIsCatOut(p, iObj) );
    if ( Cba_ObjFonNum(p, iObj) > 1 )
        Vec_StrPush( vStr, '{' );
    Cba_ObjForEachFon( p, iObj, iFon, i )
    {
        Vec_StrPrintStr( vStr, i ? ", " : "" );
        Cba_ManWriteFonName( p, iFon, 0, 0 );
    }
    if ( Cba_ObjFonNum(p, iObj) > 1 )
        Vec_StrPush( vStr, '}' );
}
int Cba_ManWriteLineFile( Cba_Ntk_t * p, int iObj, int FileAttr, int LineAttr )
{
    Vec_Str_t * vStr = &p->pDesign->vOut;
    int FileId = 0, LineId = 0;
    if ( FileAttr && (FileId = Cba_ObjAttrValue(p, iObj, FileAttr)) )
    {
        LineId = Cba_ObjAttrValue(p, iObj, LineAttr);
        Vec_StrPrintF( vStr, "  // %s(%d)", Cba_NtkStr(p, FileId), LineId );
        return 1;
    }
    return 0;
}
void Cba_ManWriteVerilogNtk( Cba_Ntk_t * p, int fInlineConcat )
{
    Vec_Str_t * vStr = &p->pDesign->vOut;
    int i, k, iObj, iFin, iFon, StartPos, Status;
    int FileAttr = Cba_NtkStrId( p, "file" );
    int LineAttr = Cba_NtkStrId( p, "line" );
    int fUseNewLine = (int)(Cba_NtkPioNum(p) > 5);
    // mark PO fons
    Vec_Bit_t * vPoFons = Vec_BitStart( Cba_NtkFonNum(p)+1 );
    Cba_NtkForEachPoDriverFon( p, iObj, iFon, i )
        if ( Cba_FonIsReal(iFon) && Cba_FonName(p, iFon) == Cba_ObjName(p, iObj) )
            Vec_BitWriteEntry( vPoFons, iFon, 1 );
    // write header
    Vec_StrPrintStr( vStr, "module " );
    Vec_StrPrintStr( vStr, Cba_NtkName(p) );
    Vec_StrPrintStr( vStr, fUseNewLine ? " (\n    " : " ( " );
    StartPos = Vec_StrSize(vStr);
    Cba_NtkForEachPioOrder( p, iObj, i )
    {
        Vec_StrPrintStr( vStr, i ? ", " : "" );
        if ( Vec_StrSize(vStr) > StartPos + 70 )
        {
            StartPos = Vec_StrSize(vStr);
            Vec_StrPrintStr( vStr, "\n    " );
        }
        Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iObj) );
    }
    Vec_StrPrintStr( vStr, fUseNewLine ? "\n  );" : " );" );
    Cba_ManWriteLineFile( p, 0, FileAttr, LineAttr );
    Vec_StrPrintStr( vStr, fUseNewLine ? "\n" : "\n\n" );
    // write inputs/outputs
    Cba_NtkForEachPioOrder( p, iObj, i )
    {
        int Offset = Vec_StrSize(vStr);
        Vec_StrPrintStr( vStr, "  " );
        Vec_StrPrintStr( vStr, Cba_ObjIsPi(p, iObj) ? "input " : "output " );
        Cba_ManWriteFonRange( p, Cba_ObjIsPi(p, iObj) ? Cba_ObjFon0(p, iObj) : Cba_ObjFinFon(p, iObj, 0) );
        Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iObj) );
//        Vec_StrPush( vStr, ';' );
//        for ( k = Vec_StrSize(vStr); k < Offset + 40; k++ )
//            Vec_StrPush( vStr, ' ' );
        Vec_StrPrintF( vStr, ";%*s", Offset + 40 - Vec_StrSize(vStr), "" );

        Cba_ManWriteLineFile( p, iObj, FileAttr, LineAttr );
        Vec_StrPush( vStr, '\n' );
    }
    Vec_StrPrintStr( vStr, "\n" );
    // write objects
    Cba_NtkForEachBox( p, iObj )
    {
        int Type = Cba_ObjType(p, iObj);
        if ( Cba_ObjIsSlice(p, iObj) )
            continue;
        if ( fInlineConcat && Cba_ObjIsCatIn(p, iObj) )
            continue;
        if ( Cba_ObjIsBoxUser(p, iObj) )
        {
            Cba_Ntk_t * pNtk = Cba_ObjNtk(p, iObj);
            // write output wire declarations
            Cba_ObjForEachFon( p, iObj, iFon, i )
            {
                if ( Vec_BitEntry(vPoFons, iFon) )
                    continue;
                Vec_StrPrintStr( vStr, "  wire " );
                Cba_ManWriteFonRange( p, iFon );
                Cba_ManWriteFonName( p, iFon, 0, 0 );
                Vec_StrPrintStr( vStr, ";\n" );
            }
            // write box
            Vec_StrPrintStr( vStr, "  " );
            Vec_StrPrintStr( vStr, Cba_NtkName(pNtk) );
            Vec_StrPush( vStr, ' ' );
            if ( Cba_ObjName(p, iObj) )
//                Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iObj) ),
//                Vec_StrPush( vStr, ' ' );
                Vec_StrPrintF( vStr, "%s ", Cba_ObjNameStr(p, iObj) );
            // write input binding
            Vec_StrPrintStr( vStr, "( " );
            Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
            {
//                Vec_StrPrintStr( vStr, i ? ", " : "" );
//                Vec_StrPush( vStr, '.' );
//                Vec_StrPrintStr( vStr, Cba_ObjNameStr(pNtk, Cba_NtkPi(pNtk, i)) );
//                Vec_StrPush( vStr, '(' );
                Vec_StrPrintF( vStr, "%s.%s(", i ? ", " : "", Cba_ObjNameStr(pNtk, Cba_NtkPi(pNtk, i)) );

                Cba_ManWriteFonName( p, iFon, fInlineConcat, 1 );
                Vec_StrPush( vStr, ')' );
            }
            // write output binding
            Cba_ObjForEachFon( p, iObj, iFon, i )
            {
//                Vec_StrPrintStr( vStr, Cba_ObjFinNum(p, iObj) ? ", " : "" );
//                Vec_StrPush( vStr, '.' );
//                Vec_StrPrintStr( vStr, Cba_ObjNameStr(pNtk, Cba_NtkPo(pNtk, i)) );
//                Vec_StrPush( vStr, '(' );
                Vec_StrPrintF( vStr, "%s.%s(", Cba_ObjFinNum(p, iObj) ? ", " : "", Cba_ObjNameStr(pNtk, Cba_NtkPo(pNtk, i)) );

                Cba_ManWriteFonName( p, iFon, 0, 1 );
                Vec_StrPush( vStr, ')' );
            }
            Vec_StrPrintStr( vStr, ");" );
        }
        else if ( Type == CBA_BOX_CATOUT )
        {
            // write declarations
            Cba_ObjForEachFon( p, iObj, iFon, i )
            {
                if ( !Cba_FonName(p, iFon) ) 
                    continue;
                if ( Vec_BitEntry(vPoFons, iFon) )
                    continue;
                Vec_StrPrintStr( vStr, "  wire " );
                Cba_ManWriteFonRange( p, iFon );
                Cba_ManWriteFonName( p, iFon, 0, 0 );
                Vec_StrPrintStr( vStr, ";\n" );
            }
            // write output concatenation
            Vec_StrPrintStr( vStr, "  assign " );
            Cba_ManWriteCatOut( p, iObj );
            Vec_StrPrintStr( vStr, " = " );
            Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 0), 0, 0 );
            Vec_StrPush( vStr, ';' );
        }
        else if ( Type == CBA_BOX_NMUX || Type == CBA_BOX_SEL )
        {
            int fUseSel = Type == CBA_BOX_SEL;
            int nBits   = fUseSel ? Cba_ObjFinNum(p, iObj) - 1 : Abc_Base2Log(Cba_ObjFinNum(p, iObj) - 1);
            int iFonIn  = Cba_ObjFinFon(p, iObj, 0);
            int iFonOut = Cba_ObjFon0(p, iObj);
            // function [15:0] res;
            Vec_StrPrintStr( vStr, "  function " );
            Cba_ManWriteFonRange( p, iFonOut );
            Vec_StrPrintStr( vStr, "_func_" );
            Cba_ManWriteFonName( p, iFonOut, 0, 0 );
            Vec_StrPrintStr( vStr, ";\n" );
            // input [1:0] s;
            Vec_StrPrintStr( vStr, "    input " );
            Cba_ManWriteFonRange( p, iFonIn );
            Vec_StrPrintStr( vStr, "s;\n" );
            // input [15:0] d0, d1, d2, d3;
            Vec_StrPrintStr( vStr, "    input " );
            Cba_ManWriteFonRange( p, iFonOut );
            Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
            {
                if ( i == 0 ) continue;
//                Vec_StrPrintStr( vStr, i > 1 ? ", " : "" );
//                Vec_StrPrintStr( vStr, "d" );
//                Vec_StrPrintNum( vStr, i-1 );
                Vec_StrPrintF( vStr, "%sd%d", i > 1 ? ", " : "", i-1 );
            }
            Vec_StrPrintStr( vStr, ";\n" );
            // casez (s)
            Vec_StrPrintStr( vStr, "    casez(s)" );
            if ( fUseSel )
                Vec_StrPrintStr( vStr, "  // synopsys full_case parallel_case" );
            Vec_StrPrintStr( vStr, "\n" );
            // 2'b00: res = b[15:0];
            Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
            {
                if ( i == 0 ) continue;
//                Vec_StrPrintStr( vStr, "      " );
//                Vec_StrPrintNum( vStr, nBits );
//                Vec_StrPrintStr( vStr, "\'b" );
                Vec_StrPrintF( vStr, "      %d\'b", nBits );
                if ( fUseSel )
                {
                    Vec_StrFillExtra( vStr, Vec_StrSize(vStr) + nBits, '?' );
                    Vec_StrWriteEntry( vStr, Vec_StrSize(vStr) - i, '1' );
                }
                else
                {
                    for ( k = nBits-1; k >= 0; k-- )
                        Vec_StrPrintNum( vStr, ((i-1) >> k) & 1 );
                }
                Vec_StrPrintStr( vStr, ": _func_" );
                Cba_ManWriteFonName( p, iFonOut, 0, 0 );
//                Vec_StrPrintStr( vStr, " = " );
//                Vec_StrPrintStr( vStr, "d" );
//                Vec_StrPrintNum( vStr, i-1 );
//                Vec_StrPrintStr( vStr, ";\n" );
                Vec_StrPrintF( vStr, " = d%d;\n", i-1 );
            }
            Vec_StrPrintStr( vStr, "    endcase\n" );
            Vec_StrPrintStr( vStr, "  endfunction\n" );
            // assign z = res(a, b, s);
            if ( Vec_BitEntry(vPoFons, iFonOut) ) 
                Vec_StrPrintStr( vStr, "  assign " );
            else
            {
                Vec_StrPrintStr( vStr, "  wire " );
                Cba_ManWriteFonRange( p, iFonOut );
            }
            Cba_ManWriteFonName( p, iFonOut, fInlineConcat, 0 );
            Vec_StrPrintStr( vStr, " = _func_" );
            Cba_ManWriteFonName( p, iFonOut, 0, 0 );
            Vec_StrPrintStr( vStr, " ( " );
            Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
            {
                Vec_StrPrintStr( vStr, i ? ", " : "" );
                Cba_ManWriteFonName( p, iFon, fInlineConcat, 0 );
            }
            Vec_StrPrintStr( vStr, " );" );
        }
        else if ( Type == CBA_BOX_DEC )
        {
            int iFonIn   = Cba_ObjFinFon(p, iObj, 0);
            int iFonOut  = Cba_ObjFon0(p, iObj);
            int nBitsIn  = Cba_FonRange(p, iFonIn);
            int nBitsOut = Cba_FonRange(p, iFonOut);
            assert( (1 << nBitsIn) == nBitsOut );
            // function [15:0] res;
            Vec_StrPrintStr( vStr, "  function " );
            Cba_ManWriteFonRange( p, iFonOut );
            Vec_StrPrintStr( vStr, "_func_" );
            Cba_ManWriteFonName( p, iFonOut, 0, 0 );
            Vec_StrPrintStr( vStr, ";\n" );
            // input [1:0] i;
            Vec_StrPrintStr( vStr, "    input " );
            Cba_ManWriteFonRange( p, iFonIn );
            Vec_StrPrintStr( vStr, "i;\n" );
            // casez (i)
            Vec_StrPrintStr( vStr, "    casez(i)\n" );
            // 2'b00: res = 4'b0001;
            Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
            {
                Vec_StrPrintF( vStr, "      %d\'b: ", nBitsIn );
                Vec_StrPrintStr( vStr, ": _func_" );
                Cba_ManWriteFonName( p, iFonOut, 0, 0 );
                Vec_StrPrintF( vStr, " = %d\'b%*d;\n", nBitsOut, nBitsOut, 0 );
                Vec_StrWriteEntry( vStr, Vec_StrSize(vStr) - i - 3, '1' );
            }
            Vec_StrPrintStr( vStr, "    endcase\n" );
            Vec_StrPrintStr( vStr, "  endfunction\n" );
            // assign z = res(i, o);
            if ( Vec_BitEntry(vPoFons, iFonOut) ) 
                Vec_StrPrintStr( vStr, "  assign " );
            else
            {
                Vec_StrPrintStr( vStr, "  wire " );
                Cba_ManWriteFonRange( p, iFonOut );
            }
            Cba_ManWriteFonName( p, iFonOut, fInlineConcat, 0 );
            Vec_StrPrintStr( vStr, " = _func_" );
            Cba_ManWriteFonName( p, iFonOut, 0, 0 );
            Vec_StrPrintStr( vStr, " ( " );
            Cba_ManWriteFonName( p, iFonIn, fInlineConcat, 0 );
            Vec_StrPrintStr( vStr, " );" );
         }
        else if ( Type == CBA_BOX_DFFRS || Type == CBA_BOX_LATCHRS )
        {
            int fUseFlop = Type == CBA_BOX_DFFRS;
            int iFonQ    = Cba_ObjFon0(p, iObj);
            int iFonD    = Cba_ObjFinFon(p, iObj, 0);
            int iFonC    = Cba_ObjFinFon(p, iObj, 3);
            int iFonSet  = Cba_ObjFindOne( p, Cba_ObjFinFon(p, iObj, 1) );
            int iFonRst  = Cba_ObjFindOne( p, Cba_ObjFinFon(p, iObj, 2) );
            int Range    = Cba_FonRange( p, iFonQ );
            if ( iFonSet < 0 || iFonRst < 0 )
            {
                printf( "Cba_ManWriteVerilog(): In module \"%s\", cannot write object \"%s\".\n", Cba_NtkName(p), Cba_ObjNameStr(p, iObj) );
                continue;
            }
            assert( iFonSet >= 0 && iFonRst >= 0 );
            // reg    [3:0] Q;
            Vec_StrPrintStr( vStr, "  reg " );
            Cba_ManWriteFonRange( p, iFonQ );
            Cba_ManWriteFonName( p, iFonQ, 0, 0 );
            Vec_StrPrintStr( vStr, ";\n" );
            // always @(posedge C or posedge PRE)
            Vec_StrPrintStr( vStr, "  always @(" );
            if ( fUseFlop )
                Vec_StrPrintStr( vStr, "posedge " );
            Cba_ManWriteFonName( p, iFonC, 0, 0 );
            if ( !fUseFlop )
            {
                Vec_StrPrintStr( vStr, " or " );
                Cba_ManWriteFonName( p, iFonD, 0, 0 );
            }
            if ( iFonSet > 0 )
            {
                Vec_StrPrintStr( vStr, " or " );
                if ( fUseFlop )
                    Vec_StrPrintStr( vStr, "posedge " );
                Cba_ManWriteFonName( p, iFonSet, 0, 0 );
            }
            if ( iFonRst > 0 )
            {
                Vec_StrPrintStr( vStr, " or " );
                if ( fUseFlop )
                    Vec_StrPrintStr( vStr, "posedge " );
                Cba_ManWriteFonName( p, iFonRst, 0, 0 );
            }
            Vec_StrPrintStr( vStr, ")\n" );
            //  if (Set)  Q <= 4'b1111;
            if ( iFonSet )
            {
                Vec_StrPrintStr( vStr, "    if (" );
                Cba_ManWriteFonName( p, iFonSet, 0, 0 );
                Vec_StrPrintStr( vStr, ")  " );
                Cba_ManWriteFonName( p, iFonQ, 0, 0 );
                Vec_StrPrintStr( vStr, fUseFlop ? " <= " : " = " );
                Vec_StrPrintNum( vStr, Range );
                Vec_StrPrintStr( vStr, "\'b" );
                Vec_StrFillExtra( vStr, Vec_StrSize(vStr) + Range, '1' );
                Vec_StrPrintStr( vStr, ";\n" );
            }
            if ( iFonRst )
            {
                Vec_StrPrintStr( vStr, iFonSet ? "    else if (" : "    if (" );
                Cba_ManWriteFonName( p, iFonRst, 0, 0 );
                Vec_StrPrintStr( vStr, ")  " );
                Cba_ManWriteFonName( p, iFonQ, 0, 0 );
                Vec_StrPrintStr( vStr, fUseFlop ? " <= " : " = " );
                Vec_StrPrintNum( vStr, Range );
                Vec_StrPrintStr( vStr, "\'b" );
                Vec_StrFillExtra( vStr, Vec_StrSize(vStr) + Range, '0' );
                Vec_StrPrintStr( vStr, ";\n" );
            }
            Vec_StrPrintStr( vStr, (iFonSet || iFonRst) ? "    else " : "    " );
            if ( !fUseFlop )
            {
                Vec_StrPrintStr( vStr, "    if (" );
                Cba_ManWriteFonName( p, iFonC, 0, 0 );
                Vec_StrPrintStr( vStr, ")  " );
            }
            Cba_ManWriteFonName( p, iFonQ, 0, 0 );
            Vec_StrPrintStr( vStr, fUseFlop ? " <= " : " = " );
            Cba_ManWriteFonName( p, iFonD, fInlineConcat, 0 );
            Vec_StrPrintStr( vStr, ";" );
        }
        else if ( Type == CBA_BOX_ADD )
        {
            int iFon0 = Cba_ObjFon0(p, iObj);
            int iFon1 = Cba_ObjFon(p, iObj, 1);
            // write outputs
            if ( Cba_FonName(p, iFon1) )
            {
                if ( !Vec_BitEntry(vPoFons, iFon0) )
                {
                    Vec_StrPrintStr( vStr, "  wire " );
                    Cba_ManWriteFonRange( p, iFon0 );
                    Cba_ManWriteFonName( p, iFon0, 0, 0 );
                    Vec_StrPrintStr( vStr, ";\n" );
                }
                if ( !Vec_BitEntry(vPoFons, iFon1) )
                {
                    Vec_StrPrintStr( vStr, "  wire " );
                    Cba_ManWriteFonRange( p, iFon1 );
                    Cba_ManWriteFonName( p, iFon1, 0, 0 );
                    Vec_StrPrintStr( vStr, ";\n" );
                }
                Vec_StrPrintStr( vStr, "  assign {" );
                Cba_ManWriteFonName( p, iFon1, 0, 0 );
                Vec_StrPrintStr( vStr, ", " );
                Cba_ManWriteFonName( p, iFon0, 0, 0 );
                Vec_StrPrintStr( vStr, "} = " );
            }
            else
            {
                if ( Vec_BitEntry(vPoFons, iFon0) ) 
                    Vec_StrPrintStr( vStr, "  assign " );
                else
                {
                    Vec_StrPrintStr( vStr, "  wire " );
                    Cba_ManWriteFonRange( p, iFon0 );
                }
                Cba_ManWriteFonName( p, iFon0, 0, 0 );
                Vec_StrPrintStr( vStr, " = " );
            }
            // write carry-in
            if ( Cba_ObjFinFon(p, iObj, 0) != Cba_FonFromConst(1) )
            {
                Vec_StrPush( vStr, ' ' );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 0), fInlineConcat, 0 );
                Vec_StrPush( vStr, ' ' );
                Vec_StrPrintStr( vStr, "+" );
            }
            Vec_StrPush( vStr, ' ' );
            Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 1), fInlineConcat, 0 );
            Vec_StrPush( vStr, ' ' );
            Vec_StrPrintStr( vStr, "+" );
            Vec_StrPush( vStr, ' ' );
            Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 2), fInlineConcat, 0 );
            Vec_StrPush( vStr, ';' );
        }
        else
        {
            if ( Vec_BitEntry(vPoFons, Cba_ObjFon0(p, iObj)) ) 
                Vec_StrPrintStr( vStr, "  assign " );
            else
            {
                Vec_StrPrintStr( vStr, "  wire " );
                Cba_ManWriteFonRange( p, Cba_ObjFon0(p, iObj) );
            }
            Cba_ManWriteFonName( p, Cba_ObjFon0(p, iObj), 0, 0 );
            Vec_StrPrintStr( vStr, " = " );
            if ( Cba_ObjIsCatIn(p, iObj) )
                Cba_ManWriteCatIn( p, iObj );
            else if ( Type == CBA_BOX_MUX )
            {
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 0), fInlineConcat, 0 );
                Vec_StrPrintStr( vStr, " ? " );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 1), fInlineConcat, 0 );
                Vec_StrPrintStr( vStr, " : " );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 2), fInlineConcat, 0 );
            }
            else if ( Type == CBA_BOX_LTHAN )
            {
                int fLessThan = (Cba_ObjFinFon(p, iObj, 0) == Cba_FonFromConst(1)); // const0
                Vec_StrPush( vStr, ' ' );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 1), fInlineConcat, 0 );
                Vec_StrPush( vStr, ' ' );
                Vec_StrPrintStr( vStr, fLessThan ? "<" : "<=" );
                Vec_StrPush( vStr, ' ' );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 2), fInlineConcat, 0 );
            }
            else if ( Cba_TypeIsUnary(Type) )
            {
                Vec_StrPrintStr( vStr, Cba_NtkTypeName(p, Type) );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 0), fInlineConcat, 0 );
            }
            else if ( Cba_NtkTypeName(p, Type) ) // binary operation
            {
                Vec_StrPush( vStr, ' ' );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 0), fInlineConcat, 0 );
                Vec_StrPush( vStr, ' ' );
                Vec_StrPrintStr( vStr, Cba_NtkTypeName(p, Type) );
                Vec_StrPush( vStr, ' ' );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 1), fInlineConcat, 0 );
            }
            else // unknown
            {
                Vec_StrPrintStr( vStr, "<unknown operator>" );
                printf( "Cba_ManWriteVerilog(): In module \"%s\", cannot write object \"%s\".\n", Cba_NtkName(p), Cba_ObjNameStr(p, iObj) );
            }
            Vec_StrPush( vStr, ';' );
        }
        // write attributes
        Status = Cba_ManWriteLineFile( p, iObj, FileAttr, LineAttr );
        if ( !Cba_ObjIsBoxUser(p, iObj) && Cba_ObjName(p, iObj) )
        {
            if ( !Status )
                Vec_StrPrintStr( vStr, "  //" );
            Vec_StrPrintStr( vStr, " name=" );
            Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iObj) );
        }
        Vec_StrPush( vStr, '\n' );
    }
    // write remaining outputs
    Cba_NtkForEachPo( p, iObj, i )
    {
        iFon = Cba_ObjFinFon(p, iObj, 0);
        if ( !Cba_FonIsConst(iFon) && Cba_FonName(p, iFon) == Cba_ObjName(p, iObj) ) // already written
            continue;
        Vec_StrPrintStr( vStr, "  assign " );
        Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iObj) );
        Vec_StrPrintStr( vStr, " = " );
        Cba_ManWriteFonName( p, iFon, fInlineConcat, 0 );
        Vec_StrPush( vStr, ';' );
        Vec_StrPush( vStr, '\n' );
    }
    Vec_StrPrintStr( vStr, "\n" );
    Vec_StrPrintStr( vStr, "endmodule\n\n" );
    Vec_BitFree( vPoFons );
}
void Cba_ManWriteVerilog( char * pFileName, Cba_Man_t * p, int fInlineConcat )
{
    Cba_Ntk_t * pNtk; int i;
    // check the library
    if ( p->pMioLib && p->pMioLib != Abc_FrameReadLibGen() )
    {
        printf( "Genlib library used in the mapped design is not longer a current library.\n" );
        return;
    }
    Cba_ManCreatePrimMap( p->pTypeNames );
    // derive the stream
    p->nOpens = 1;
    Vec_StrClear( &p->vOut );
    Vec_StrClear( &p->vOut2 );
    Vec_StrPrintStr( &p->vOut, "// Design \"" );
    Vec_StrPrintStr( &p->vOut, Cba_ManName(p) );
    Vec_StrPrintStr( &p->vOut, "\" written via CBA package in ABC on " );
    Vec_StrPrintStr( &p->vOut, Extra_TimeStamp() );
    Vec_StrPrintStr( &p->vOut, "\n\n" );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManWriteVerilogNtk( pNtk, fInlineConcat );
    // dump into file
    if ( Vec_StrSize(&p->vOut) > 0 )
    {
        FILE * pFile = fopen( pFileName, "wb" );
        if ( pFile == NULL )
            printf( "Cannot open file \"%s\" for writing.\n", pFileName );
        else
        {
            fwrite( Vec_StrArray(&p->vOut), 1, Vec_StrSize(&p->vOut), pFile );
            fclose( pFile );
        }
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

