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
    pMap[ CBA_BOX_MAJ    ] = "maj"; 
    pMap[ CBA_BOX_RAND   ] = "&"; 
    pMap[ CBA_BOX_RNAND  ] = "~&"; 
    pMap[ CBA_BOX_ROR    ] = "|"; 
    pMap[ CBA_BOX_RNOR   ] = "~|"; 
    pMap[ CBA_BOX_RXOR   ] = "^"; 
    pMap[ CBA_BOX_RXNOR  ] = "~^"; 
    pMap[ CBA_BOX_LNOT   ] = "!"; 
    pMap[ CBA_BOX_LAND   ] = "&&"; 
    pMap[ CBA_BOX_LNAND  ] = "!&&"; 
    pMap[ CBA_BOX_LOR    ] = "||"; 
    pMap[ CBA_BOX_LNOR   ] = "!||"; 
    pMap[ CBA_BOX_LXOR   ] = "^^"; 
    pMap[ CBA_BOX_LXNOR  ] = "!^^"; 
    pMap[ CBA_BOX_NMUX   ] = "??"; 
    pMap[ CBA_BOX_SEL    ] = "?|"; 
    pMap[ CBA_BOX_PSEL   ] = "?%"; 
    pMap[ CBA_BOX_ENC    ] = "enc"; 
    pMap[ CBA_BOX_PENC   ] = "penc"; 
    pMap[ CBA_BOX_DEC    ] = "dec"; 
    pMap[ CBA_BOX_EDEC   ] = "edec"; 
    pMap[ CBA_BOX_ADD    ] = "+"; 
    pMap[ CBA_BOX_SUB    ] = "-"; 
    pMap[ CBA_BOX_MUL    ] = "*"; 
    pMap[ CBA_BOX_DIV    ] = "/"; 
    pMap[ CBA_BOX_MOD    ] = "mod"; 
    pMap[ CBA_BOX_REM    ] = "%%"; 
    pMap[ CBA_BOX_POW    ] = "**"; 
    pMap[ CBA_BOX_MIN    ] = "-"; 
    pMap[ CBA_BOX_ABS    ] = "abs"; 
    pMap[ CBA_BOX_LTHAN  ] = "<"; 
    pMap[ CBA_BOX_LETHAN ] = "<="; 
    pMap[ CBA_BOX_METHAN ] = ">="; 
    pMap[ CBA_BOX_MTHAN  ] = ">"; 
    pMap[ CBA_BOX_EQU    ] = "=="; 
    pMap[ CBA_BOX_NEQU   ] = "!="; 
    pMap[ CBA_BOX_SHIL   ] = "<<"; 
    pMap[ CBA_BOX_SHIR   ] = ">>"; 
    pMap[ CBA_BOX_ROTL   ] = "rotL"; 
    pMap[ CBA_BOX_ROTR   ] = "rotR"; 
}

void Cba_ManWriteFonRange( Cba_Ntk_t * p, int iFon )
{
    Vec_Str_t * vStr = &p->pDesign->vOut;
    if ( Cba_FonIsConst(iFon) || Cba_FonRange(p, iFon) == 1 )
        return;
    Vec_StrPush( vStr, '[' );
    Vec_StrPrintNum( vStr, Cba_FonLeft(p, iFon) );
    Vec_StrPush( vStr, ':' );
    Vec_StrPrintNum( vStr, Cba_FonRight(p, iFon) );
    Vec_StrPush( vStr, ']' );
    Vec_StrPush( vStr, ' ' );
}
void Cba_ManWriteFonName( Cba_Ntk_t * p, int iFon, int fInlineConcat )
{
    extern void Cba_ManWriteConcat( Cba_Ntk_t * p, int iObj );
    Vec_Str_t * vStr = &p->pDesign->vOut;
    if ( Cba_FonIsConst(iFon) )
        Vec_StrPrintStr( vStr, Cba_NtkConst(p, Cba_FonConst(iFon)) );
    else if ( fInlineConcat && Cba_ObjIsConcat(p, Cba_FonObj(p, iFon)) )
        Cba_ManWriteConcat( p, Cba_FonObj(p, iFon) );
    else
        Vec_StrPrintStr( vStr, Cba_FonNameStr(p, iFon) );
}
void Cba_ManWriteConcat( Cba_Ntk_t * p, int iObj )
{
    int i, iFin, iFon;
    Vec_Str_t * vStr = &p->pDesign->vOut;
    assert( Cba_ObjIsConcat(p, iObj) );
    Vec_StrPush( vStr, '{' );
    Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
    {
        Vec_StrPrintStr( vStr, i ? ", " : "" );
        Cba_ManWriteFonName( p, iFon, 1 );
    }
    Vec_StrPush( vStr, '}' );
}
int Cba_ManWriteLineFile( Cba_Ntk_t * p, int iObj, int FileAttr, int LineAttr )
{
    Vec_Str_t * vStr = &p->pDesign->vOut;
    int FileId = 0, LineId = 0;
    if ( FileAttr && (FileId = Cba_ObjAttrValue(p, iObj, FileAttr)) )
    {
        LineId = Cba_ObjAttrValue(p, iObj, LineAttr);
        Vec_StrPrintStr( vStr, "  // " );
        Vec_StrPrintStr( vStr, Cba_NtkStr(p, FileId) );
        Vec_StrPush( vStr, '(' );
        Vec_StrPrintNum( vStr, LineId );
        Vec_StrPush( vStr, ')' );
        return 1;
    }
    return 0;
}
void Cba_ManWriteVerilogNtk( Cba_Ntk_t * p, int fInlineConcat )
{
    Vec_Str_t * vStr = &p->pDesign->vOut;
    int i, iObj, iFin, iFon, StartPos, Status;
    int FileAttr = Cba_NtkStrId( p, "file" );
    int LineAttr = Cba_NtkStrId( p, "line" );
    int fUseNewLine = (int)(Cba_NtkPioNum(p) > 5);
    // mark PO fons
    Vec_Bit_t * vPoFons = Vec_BitStart( Cba_NtkFonNum(p)+1 );
    Cba_NtkForEachPoDriverFon( p, iObj, iFon, i )
        if ( Cba_FonIsReal(iFon) )
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
        Vec_StrPrintStr( vStr, "  " );
        Vec_StrPrintStr( vStr, Cba_ObjIsPi(p, iObj) ? "input " : "output " );
        Cba_ManWriteFonRange( p, Cba_ObjIsPi(p, iObj) ? Cba_ObjFon0(p, iObj) : Cba_ObjFinFon(p, iObj, 0) );
        Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iObj) );
        Vec_StrPush( vStr, ';' );
        Cba_ManWriteLineFile( p, iObj, FileAttr, LineAttr );
        Vec_StrPush( vStr, '\n' );
    }
    Vec_StrPrintStr( vStr, "\n" );
    // write objects
    Cba_NtkForEachBox( p, iObj )
    {
        if ( Cba_ObjIsSlice(p, iObj) )
            continue;
        if ( fInlineConcat && Cba_ObjIsConcat(p, iObj) )
            continue;
        if ( Cba_ObjIsBoxUser(p, iObj) )
        {
            Cba_Ntk_t * pNtk = Cba_ObjNtk(p, iObj);
            // write output wire declarations
            Cba_ObjForEachFon( p, iObj, iFon, i )
            {
                Vec_StrPrintStr( vStr, "  wire " );
                Cba_ManWriteFonRange( p, iFon );
                Cba_ManWriteFonName( p, iFon, 0 );
                Vec_StrPrintStr( vStr, ";\n" );
            }
            // write box
            Vec_StrPrintStr( vStr, "  " );
            Vec_StrPrintStr( vStr, Cba_NtkName(pNtk) );
            Vec_StrPush( vStr, ' ' );
            if ( Cba_ObjName(p, iObj) )
                Vec_StrPrintStr( vStr, Cba_ObjNameStr(p, iObj) ),
                Vec_StrPush( vStr, ' ' );
            // write input binding
            Vec_StrPrintStr( vStr, "( " );
            Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
            {
                Vec_StrPrintStr( vStr, i ? ", " : "" );
                Vec_StrPush( vStr, '.' );
                Vec_StrPrintStr( vStr, Cba_ObjNameStr(pNtk, Cba_NtkPi(pNtk, i)) );
                Vec_StrPush( vStr, '(' );
                Cba_ManWriteFonName( p, iFon, fInlineConcat );
                Vec_StrPush( vStr, ')' );
            }
            // write output binding
            Cba_ObjForEachFon( p, iObj, iFon, i )
            {
                Vec_StrPrintStr( vStr, Cba_ObjFinNum(p, iObj) ? ", " : "" );
                Vec_StrPush( vStr, '.' );
                Vec_StrPrintStr( vStr, Cba_ObjNameStr(pNtk, Cba_NtkPo(pNtk, i)) );
                Vec_StrPush( vStr, '(' );
                Cba_ManWriteFonName( p, iFon, 0 );
                Vec_StrPush( vStr, ')' );
            }
            Vec_StrPrintStr( vStr, ");" );
        }
        else
        {
            int Type = Cba_ObjType(p, iObj);
            if ( Vec_BitEntry(vPoFons, Cba_ObjFon0(p, iObj)) )
                Vec_StrPrintStr( vStr, "  assign " );
            else
            {
                Vec_StrPrintStr( vStr, "  wire " );
                Cba_ManWriteFonRange( p, Cba_ObjFon0(p, iObj) );
            }
            Cba_ManWriteFonName( p, Cba_ObjFon0(p, iObj), 0 );
            Vec_StrPrintStr( vStr, " = " );
            if ( Cba_ObjIsConcat(p, iObj) )
                Cba_ManWriteConcat( p, iObj );
            else if ( Type == CBA_BOX_MUX || Type == CBA_BOX_NMUX )
            {
                char * pSymb = Type == CBA_BOX_MUX ? " ? " : " ?? ";
                Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
                {
                    Vec_StrPrintStr( vStr, i ? (i == 1 ? pSymb: " : ") : "" );
                    Cba_ManWriteFonName( p, iFon, fInlineConcat );
                }
            }
            else if ( Type == CBA_BOX_SEL || Type == CBA_BOX_PSEL )
            {
                char * pSymb = Type == CBA_BOX_SEL ? " ?| " : " ?% ";
                Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
                {
                    Vec_StrPrintStr( vStr, i ? (i == 1 ? pSymb: " : ") : "" );
                    Cba_ManWriteFonName( p, iFon, fInlineConcat );
                }
            }
            else if ( Cba_TypeIsUnary(Type) )
            {
                Vec_StrPrintStr( vStr, Cba_NtkTypeName(p, Type) );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 0), fInlineConcat );
            }
            else // binary operation
            {
                Vec_StrPush( vStr, ' ' );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 0), fInlineConcat );
                Vec_StrPush( vStr, ' ' );
                Vec_StrPrintStr( vStr, Cba_NtkTypeName(p, Type) );
                Vec_StrPush( vStr, ' ' );
                Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 1), fInlineConcat );
                if ( Type == CBA_BOX_ADD )
                {
                    Vec_StrPush( vStr, ' ' );
                    Vec_StrPrintStr( vStr, Cba_NtkTypeName(p, Type) );
                    Vec_StrPush( vStr, ' ' );
                    Cba_ManWriteFonName( p, Cba_ObjFinFon(p, iObj, 2), fInlineConcat );
                }
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
        Cba_ManWriteFonName( p, iFon, fInlineConcat );
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

