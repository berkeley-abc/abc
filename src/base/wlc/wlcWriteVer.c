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
    Wlc_NtkForEachObj( p, pObj, i )
    {
        char * pName  = Wlc_ObjName(p, i);
        char * pName0 = Wlc_ObjFaninNum(pObj) ? Wlc_ObjName(p, Wlc_ObjFaninId0(pObj)) : NULL;
        int nDigits   = Abc_Base10Log(pObj->End+1) + Abc_Base10Log(pObj->Beg+1);
        sprintf( Range, "%s[%d:%d]%*s", pObj->Signed ? "signed ":"       ", pObj->End, pObj->Beg, 8-nDigits, "" );
        fprintf( pFile, "  " );
        assert( pObj->Type != WLC_OBJ_TABLE );
        if ( pObj->Type == WLC_OBJ_PI )
            fprintf( pFile, "input  wire %s %-16s", Range, pName );
        else if ( pObj->Type == WLC_OBJ_PO )
            fprintf( pFile, "output wire %s %-16s = %s", Range, pName, pName0 );
        else if ( pObj->Type == WLC_OBJ_CONST )
        {
            fprintf( pFile, "       wire %s %-16s = %d\'%sh", Range, pName, Wlc_ObjRange(pObj), pObj->Signed ? "s":"" );
            Abc_TtPrintHexArrayRev( pFile, (word *)Wlc_ObjConstValue(pObj), (Wlc_ObjRange(pObj) + 3) / 4 );
        }
        else
        {
            fprintf( pFile, "       wire %s %-16s = ", Range, Wlc_ObjName(p, i) );
            if ( pObj->Type == WLC_OBJ_BUF )
                fprintf( pFile, "%s", pName0 );
            else if ( pObj->Type == WLC_OBJ_MUX )
                fprintf( pFile, "%s ? %s : %s", pName0, Wlc_ObjName(p, Wlc_ObjFaninId1(pObj)), Wlc_ObjName(p, Wlc_ObjFaninId2(pObj)) );
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
                else if ( pObj->Type == WLC_OBJ_COMP_NOT )
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
    Wlc_WriteVerInt( pFile, p );
    fprintf( pFile, "\n" );
    fclose( pFile );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

