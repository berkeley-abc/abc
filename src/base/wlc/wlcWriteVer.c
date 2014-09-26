/**CFile****************************************************************

  FileName    [wlcWriteVer.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Writes word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcWriteVer.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_WriteTableOne( FILE * pFile, int nFans, int nOuts, word * pTable, int Id )
{
    int m, nMints = (1<<nFans);
//    Abc_TtPrintHexArrayRev( stdout, pTable, nMints );  printf( "\n" );
    assert( nOuts > 0 && nOuts <= 64 && (64 % nOuts) == 0 );
    fprintf( pFile, "module table%d(ind, val);\n", Id );
    fprintf( pFile, "  input  [%d:0] ind;\n", nFans-1 );
    fprintf( pFile, "  output [%d:0] val;\n", nOuts-1 );
    fprintf( pFile, "  reg    [%d:0] val;\n", nOuts-1 );
    fprintf( pFile, "  always @(ind)\n" );
    fprintf( pFile, "  begin\n" );
    fprintf( pFile, "    case (ind)\n" );
    for ( m = 0; m < nMints; m++ )
    fprintf( pFile, "      %d\'h%x: val = %d\'h%x;\n", nFans, m, nOuts, (unsigned)((pTable[(nOuts * m) >> 6] >> ((nOuts * m) & 63)) & Abc_Tt6Mask(nOuts)) );
    fprintf( pFile, "    endcase\n" );
    fprintf( pFile, "  end\n" );
    fprintf( pFile, "endmodule\n" );
    fprintf( pFile, "\n" );
}
void Wlc_WriteTables( FILE * pFile, Wlc_Ntk_t * p )
{
    Vec_Int_t * vNodes;
    Wlc_Obj_t * pObj, * pFanin;
    word * pTable;
    int i;
    if ( p->vTables == NULL || Vec_PtrSize(p->vTables) == 0 )
        return;
    // map tables into their nodes
    vNodes = Vec_IntStart( Vec_PtrSize(p->vTables) );
    Wlc_NtkForEachObj( p, pObj, i )
        if ( pObj->Type == WLC_OBJ_TABLE )
            Vec_IntWriteEntry( vNodes, Wlc_ObjTableId(pObj), i );
    // write tables
    Vec_PtrForEachEntry( word *, p->vTables, pTable, i )
    {
        pObj = Wlc_NtkObj( p, Vec_IntEntry(vNodes, i) );
        assert( pObj->Type == WLC_OBJ_TABLE );
        pFanin = Wlc_ObjFanin0( p, pObj );
        Wlc_WriteTableOne( pFile, Wlc_ObjRange(pFanin), Wlc_ObjRange(pObj), pTable, i );
    }
    Vec_IntFree( vNodes );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_WriteVerIntVec( FILE * pFile, Wlc_Ntk_t * p, Vec_Int_t * vVec, int Start )
{
    char * pName;
    int LineLength  = Start;
    int NameCounter = 0;
    int AddedLength, i, iObj;
    Vec_IntForEachEntry( vVec, iObj, i )
    {
        pName = Wlc_ObjName( p, iObj );
        // get the line length after this name is written
        AddedLength = strlen(pName) + 2;
        if ( NameCounter && LineLength + AddedLength + 3 > 70 )
        { // write the line extender
            fprintf( pFile, "\n   " );
            // reset the line length
            LineLength  = Start;
            NameCounter = 0;
        }
        fprintf( pFile, " %s%s", pName, (i==Vec_IntSize(vVec)-1)? "" : "," );
        LineLength += AddedLength;
        NameCounter++;
    }
} 
void Wlc_WriteVerInt( FILE * pFile, Wlc_Ntk_t * p )
{
    Wlc_Obj_t * pObj;
    int i, k, iFanin;
    char Range[100];
    fprintf( pFile, "module %s ( ", p->pName );
    fprintf( pFile, "\n   " );
    if ( Wlc_NtkPiNum(p) > 0  )
    {
        Wlc_WriteVerIntVec( pFile, p, &p->vPis, 3 );
        fprintf( pFile, ",\n   " );
    }
    if ( Wlc_NtkPoNum(p) > 0  )
        Wlc_WriteVerIntVec( pFile, p, &p->vPos, 3 );
    fprintf( pFile, "  );\n" );
    // mark fanins of rotation shifts
    Wlc_NtkForEachObj( p, pObj, i )
        if ( pObj->Type == WLC_OBJ_ROTATE_R || pObj->Type == WLC_OBJ_ROTATE_L )
            Wlc_ObjFanin1(p, pObj)->Mark = 1;
    Wlc_NtkForEachObj( p, pObj, i )
    {
        char * pName  = Wlc_ObjName(p, i);
        char * pName0 = Wlc_ObjFaninNum(pObj) ? Wlc_ObjName(p, Wlc_ObjFaninId0(pObj)) : NULL;
        int nDigits   = Abc_Base10Log(pObj->End+1) + Abc_Base10Log(pObj->Beg+1);
        if ( pObj->Mark ) 
        {
            pObj->Mark = 0;
            continue;
        }
        sprintf( Range, "%s[%d:%d]%*s", pObj->Signed ? "signed ":"       ", pObj->End, pObj->Beg, 8-nDigits, "" );
        fprintf( pFile, "  " );
        if ( pObj->Type == WLC_OBJ_PI )
            fprintf( pFile, "input  " );
        else if ( pObj->fIsPo )
            fprintf( pFile, "output " );
        else
            fprintf( pFile, "       " );
        if ( Wlc_ObjIsCi(pObj) )
            fprintf( pFile, "wire %s %s", Range, pName );
        else if ( pObj->Type == WLC_OBJ_TABLE )
        {
            // wire [3:0] s4972; table0 s4972_Index(s4971, s4972);
            fprintf( pFile, "wire %s %s ;              table%d s%d_Index(%s, %s)", Range, pName, Wlc_ObjTableId(pObj), i, pName0, pName );
        }
        else if ( pObj->Type == WLC_OBJ_CONST )
        {
            fprintf( pFile, "wire %s %-16s = %d\'%sh", Range, pName, Wlc_ObjRange(pObj), pObj->Signed ? "s":"" );
            Abc_TtPrintHexArrayRev( pFile, (word *)Wlc_ObjConstValue(pObj), (Wlc_ObjRange(pObj) + 3) / 4 );
        }
        else if ( pObj->Type == WLC_OBJ_ROTATE_R || pObj->Type == WLC_OBJ_ROTATE_L )
        {
            //  wire [27:0] s4960 = (s57 >> 17) | (s57 << 11);
            Wlc_Obj_t * pShift = Wlc_ObjFanin1(p, pObj);
            int Num0 = *Wlc_ObjConstValue(pShift);
            int Num1 = Wlc_ObjRange(pObj) - Num0;
            assert( pShift->Type == WLC_OBJ_CONST );
            assert( Num0 > 0 && Num0 < Wlc_ObjRange(pObj) );
            fprintf( pFile, "wire %s %-16s = ", Range, Wlc_ObjName(p, i) );
            if ( pObj->Type == WLC_OBJ_ROTATE_R )
                fprintf( pFile, "(%s >> %d) | (%s << %d)", pName0, Num0, pName0, Num1 );
            else
                fprintf( pFile, "(%s << %d) | (%s >> %d)", pName0, Num0, pName0, Num1 );
        }
        else if ( pObj->Type == WLC_OBJ_MUX && Wlc_ObjFaninNum(pObj) > 3 )
        {
            fprintf( pFile, "reg %s ;\n", pName );
            fprintf( pFile, "       " );
            fprintf( pFile, "always @( " );
            Wlc_ObjForEachFanin( pObj, iFanin, k )
                fprintf( pFile, "%s%s", k ? " or ":"", Wlc_ObjName(p, Wlc_ObjFaninId(pObj, k)) );
            fprintf( pFile, " )\n" );
            fprintf( pFile, "           " );
            fprintf( pFile, "begin\n" );
            fprintf( pFile, "             " );
            fprintf( pFile, "case ( %s )\n", Wlc_ObjName(p, Wlc_ObjFaninId(pObj, 0)) );
            Wlc_ObjForEachFanin( pObj, iFanin, k )
            {
                if ( !k ) continue;
                fprintf( pFile, "               " );
                fprintf( pFile, "%d : %s = %s ;\n", k-1, pName, Wlc_ObjName(p, Wlc_ObjFaninId(pObj, k)) );
            }
            fprintf( pFile, "             " );
            fprintf( pFile, "endcase\n" );
            fprintf( pFile, "           " );
            fprintf( pFile, "end\n" );
            continue;
        }
        else
        {
            fprintf( pFile, "wire %s %-16s = ", Range, Wlc_ObjName(p, i) );
            if ( pObj->Type == WLC_OBJ_BUF )
                fprintf( pFile, "%s", pName0 );
            else if ( pObj->Type == WLC_OBJ_MUX )
                fprintf( pFile, "%s ? %s : %s", pName0, Wlc_ObjName(p, Wlc_ObjFaninId2(pObj)), Wlc_ObjName(p, Wlc_ObjFaninId1(pObj)) );
            else if ( pObj->Type == WLC_OBJ_BIT_NOT )
                fprintf( pFile, "~%s", pName0 );
            else if ( pObj->Type == WLC_OBJ_LOGIC_NOT )
                fprintf( pFile, "!%s", pName0 );
            else if ( pObj->Type == WLC_OBJ_REDUCT_AND )
                fprintf( pFile, "&%s", pName0 );
            else if ( pObj->Type == WLC_OBJ_REDUCT_OR )
                fprintf( pFile, "|%s", pName0 );
            else if ( pObj->Type == WLC_OBJ_REDUCT_XOR )
                fprintf( pFile, "^%s", pName0 );
            else if ( pObj->Type == WLC_OBJ_BIT_SELECT )
                fprintf( pFile, "%s [%d:%d]", pName0, Wlc_ObjRangeEnd(pObj), Wlc_ObjRangeBeg(pObj) );
            else if ( pObj->Type == WLC_OBJ_BIT_SIGNEXT )
                fprintf( pFile, "{ {%d{%s[%d]}}, %s }", Wlc_ObjRange(pObj) - Wlc_ObjRange(Wlc_ObjFanin0(p, pObj)), pName0, Wlc_ObjRange(Wlc_ObjFanin0(p, pObj)) - 1, pName0 );
            else if ( pObj->Type == WLC_OBJ_BIT_ZEROPAD )
                fprintf( pFile, "{ {%d{1\'b0}}, %s }", Wlc_ObjRange(pObj) - Wlc_ObjRange(Wlc_ObjFanin0(p, pObj)), pName0 );
            else if ( pObj->Type == WLC_OBJ_BIT_CONCAT )
            {
                fprintf( pFile, "{" );
                Wlc_ObjForEachFanin( pObj, iFanin, k )
                    fprintf( pFile, " %s%s", Wlc_ObjName(p, Wlc_ObjFaninId(pObj, k)), k == Wlc_ObjFaninNum(pObj)-1 ? "":"," );
                fprintf( pFile, " }" );
            }
            else
            {
                fprintf( pFile, "%s ", Wlc_ObjName(p, Wlc_ObjFaninId(pObj, 0)) );
                if ( pObj->Type == WLC_OBJ_SHIFT_R )
                    fprintf( pFile, ">>" );
                else if ( pObj->Type == WLC_OBJ_SHIFT_RA )
                    fprintf( pFile, ">>>" );
                else if ( pObj->Type == WLC_OBJ_SHIFT_L )
                    fprintf( pFile, "<<" );
                else if ( pObj->Type == WLC_OBJ_SHIFT_LA )
                    fprintf( pFile, "<<<" );
                else if ( pObj->Type == WLC_OBJ_BIT_AND )
                    fprintf( pFile, "&" );
                else if ( pObj->Type == WLC_OBJ_BIT_OR )
                    fprintf( pFile, "|" );
                else if ( pObj->Type == WLC_OBJ_BIT_XOR )
                    fprintf( pFile, "^" );
                else if ( pObj->Type == WLC_OBJ_LOGIC_AND )
                    fprintf( pFile, "&&" );
                else if ( pObj->Type == WLC_OBJ_LOGIC_OR )
                    fprintf( pFile, "||" );
                else if ( pObj->Type == WLC_OBJ_COMP_EQU )
                    fprintf( pFile, "==" );
                else if ( pObj->Type == WLC_OBJ_COMP_NOTEQU )
                    fprintf( pFile, "!=" );
                else if ( pObj->Type == WLC_OBJ_COMP_LESS )
                    fprintf( pFile, "<" );
                else if ( pObj->Type == WLC_OBJ_COMP_MORE )
                    fprintf( pFile, ">" );
                else if ( pObj->Type == WLC_OBJ_COMP_LESSEQU )
                    fprintf( pFile, "<=" );
                else if ( pObj->Type == WLC_OBJ_COMP_MOREEQU )
                    fprintf( pFile, ">=" );
                else if ( pObj->Type == WLC_OBJ_ARI_ADD )
                    fprintf( pFile, "+" );
                else if ( pObj->Type == WLC_OBJ_ARI_SUB )
                    fprintf( pFile, "-" );
                else if ( pObj->Type == WLC_OBJ_ARI_MULTI )
                    fprintf( pFile, "*" );
                else if ( pObj->Type == WLC_OBJ_ARI_DIVIDE )
                    fprintf( pFile, "//" );
                else if ( pObj->Type == WLC_OBJ_ARI_MODULUS )
                    fprintf( pFile, "%%" );
                else if ( pObj->Type == WLC_OBJ_ARI_POWER )
                    fprintf( pFile, "**" );
                else assert( 0 );
                fprintf( pFile, " %s", Wlc_ObjName(p, Wlc_ObjFaninId(pObj, 1)) );
            }
        }
        fprintf( pFile, " ;\n" );
    }
    Wlc_NtkForEachCi( p, pObj, i )
    {
        char * pName  = Wlc_ObjName(p, Wlc_ObjId(p, pObj));
        assert( i == Wlc_ObjCiId(pObj) );
        if ( pObj->Type == WLC_OBJ_PI )
            continue;
//  CPL_FF#9  I_32890_reg ( .q ( E_42304 )  , .qbar (  )  , .d ( E_42305 )  , .clk ( E_65040 )  ,
//                .arst ( E_65037 )  , .arstval ( E_62126 )  );
        fprintf( pFile, "         " );
        fprintf( pFile, "CPL_FF" );
        if ( Wlc_ObjRange(pObj) > 1 )
            fprintf( pFile, "#%d", Wlc_ObjRange(pObj) );
        fprintf( pFile, " %reg%d (",       i );
        fprintf( pFile, " .q( %s ),",      pName );
        fprintf( pFile, " .qbar()," );
        fprintf( pFile, " .d( %s ),",      Wlc_ObjName(p, Wlc_ObjId(p, Wlc_ObjFoToFi(p, pObj))) );
        fprintf( pFile, " .clk( %s ),",    "1\'b0" );
        fprintf( pFile, " .arst( %s ),",   "1\'b0" );
        fprintf( pFile, " .arstval( %s )", "1\'b0" );
        fprintf( pFile, " ) ;\n" );
    }
    fprintf( pFile, "endmodule\n\n" );
} 
void Wlc_WriteVer( Wlc_Ntk_t * p, char * pFileName )
{
    FILE * pFile;
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Wlc_WriteVer(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "// Benchmark \"%s\" written by ABC on %s\n", p->pName, Extra_TimeStamp() );
    fprintf( pFile, "\n" );
    Wlc_WriteTables( pFile, p );
    Wlc_WriteVerInt( pFile, p );
    fprintf( pFile, "\n" );
    fclose( pFile );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

