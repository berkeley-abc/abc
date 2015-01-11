/**CFile****************************************************************

  FileName    [cba.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cba.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "cbaPrs.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
/*

// node types during parsing
typedef enum { 
    CBA_NODE_NONE = 0,   // 0:  unused
    CBA_NODE_CONST,      // 1:  constant
    CBA_NODE_BUF,        // 2:  buffer
    CBA_NODE_INV,        // 3:  inverter
    CBA_NODE_AND,        // 4:  AND
    CBA_NODE_OR,         // 5:  OR
    CBA_NODE_XOR,        // 6:  XOR
    CBA_NODE_NAND,       // 7:  NAND
    CBA_NODE_NOR,        // 8:  NOR
    CBA_NODE_XNOR,       // 9  .XNOR
    CBA_NODE_MUX,        // 10: MUX
    CBA_NODE_MAJ,        // 11: MAJ
    CBA_NODE_KNOWN       // 12: unknown
    CBA_NODE_UNKNOWN     // 13: unknown
} Cba_NodeType_t; 

*/

const char * s_NodeTypes[CBA_NODE_UNKNOWN+1] = {
    NULL,       // 0:  unused 
    "const",    // 1:  constant 
    "buf",      // 2:  buffer 
    "not",      // 3:  inverter 
    "and",      // 4:  AND 
    "nand",     // 5:  OR 
    "or",       // 6:  XOR 
    "nor",      // 7:  NAND 
    "xor",      // 8:  NOR 
    "xnor",     // 9: .XNOR 
    "mux",      // 10: MUX  
    "maj",      // 11: MAJ 
    "???"       // 12: known
    "???"       // 13: unknown
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writing parser state into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_PrsWriteVerilogMux( FILE * pFile, Cba_Ntk_t * p, Vec_Int_t * vFanins )
{
    int NameId, RangeId, i;
    char * pStrs[4] = { " = ", " ? ", " : ", ";\n" };
    assert( Vec_IntSize(vFanins) == 8 );
    fprintf( pFile, "  assign " );
    Vec_IntForEachEntryDouble( vFanins, NameId, RangeId, i )
    {
        fprintf( pFile, "%s%s%s", Cba_NtkStr(p, NameId), RangeId > 0 ? Cba_NtkStr(p, RangeId) : "", pStrs[i/2] );
    }
}
void Cba_PrsWriteVerilogConcat( FILE * pFile, Cba_Ntk_t * p, int Id )
{
    extern void Cba_PrsWriteVerilogArray2( FILE * pFile, Cba_Ntk_t * p, Vec_Int_t * vFanins );
    fprintf( pFile, "{" );
    Cba_PrsWriteVerilogArray2( pFile, p, Cba_ObjFaninVec2(p, Id) );
    fprintf( pFile, "}" );
}
void Cba_PrsWriteVerilogArray2( FILE * pFile, Cba_Ntk_t * p, Vec_Int_t * vFanins )
{
    int NameId, RangeId, i;
    assert( Vec_IntSize(vFanins) % 2 == 0 );
    Vec_IntForEachEntryDouble( vFanins, NameId, RangeId, i )
    {
        assert( RangeId >= -2 );
        if ( RangeId == -2 )
            Cba_PrsWriteVerilogConcat( pFile, p, NameId-1 );
        else if ( RangeId == -1 )
            fprintf( pFile, "%s", Cba_NtkStr(p, NameId) );
        else
            fprintf( pFile, "%s%s", Cba_NtkStr(p, NameId), RangeId ? Cba_NtkStr(p, RangeId) : "" );
        fprintf( pFile, "%s", (i == Vec_IntSize(vFanins) - 2) ? "" : ", " );
    }
}
void Cba_PrsWriteVerilogArray3( FILE * pFile, Cba_Ntk_t * p, Vec_Int_t * vFanins )
{
    int FormId, NameId, RangeId, i;
    assert( Vec_IntSize(vFanins) % 3 == 0 );
    Vec_IntForEachEntryTriple( vFanins, FormId, NameId, RangeId, i )
    {
        fprintf( pFile, ".%s(", Cba_NtkStr(p, FormId) );
        if ( RangeId == -2 )
            Cba_PrsWriteVerilogConcat( pFile, p, NameId-1 );
        else if ( RangeId == -1 )
            fprintf( pFile, "%s", Cba_NtkStr(p, NameId) );
        else
            fprintf( pFile, "%s%s", Cba_NtkStr(p, NameId), RangeId ? Cba_NtkStr(p, RangeId) : "" );
        fprintf( pFile, ")%s", (i == Vec_IntSize(vFanins) - 3) ? "" : ", " );
    }
}
void Cba_PrsWriteVerilogNodes( FILE * pFile, Cba_Ntk_t * p )
{
    int Type, Func, i;
    Cba_NtkForEachObjType( p, Type, i )
        if ( Type == CBA_PRS_NODE ) // .names/assign/box2 (no formal/actual binding)
        {
            Func = Cba_ObjFuncId(p, i);
            if ( Func >= CBA_NODE_BUF && Func <= CBA_NODE_XNOR )
            {
                fprintf( pFile, "  %s (", s_NodeTypes[Func] );
                Cba_PrsWriteVerilogArray2( pFile, p, Cba_ObjFaninVec(p, i) );
                fprintf( pFile, ");\n" );
            }
            else if ( Func == CBA_NODE_MUX )
                Cba_PrsWriteVerilogMux( pFile, p, Cba_ObjFaninVec(p, i) );
            else
            {
                //char * pName = Cba_NtkStr(p, Func);
                assert( 0 );
            }
        }
}
void Cba_PrsWriteVerilogBoxes( FILE * pFile, Cba_Ntk_t * p )
{
    int Type, i;
    Cba_NtkForEachObjType( p, Type, i )
        if ( Type == CBA_PRS_BOX ) // .subckt/.gate/box (formal/actual binding) 
        {
            fprintf( pFile, "  %s %s (", Cba_ObjFuncStr(p, i), Cba_ObjInstStr(p, i) );
            Cba_PrsWriteVerilogArray3( pFile, p, Cba_ObjFaninVec(p, i) );
            fprintf( pFile, ");\n" );
        }
}
void Cba_PrsWriteVerilogSignals( FILE * pFile, Cba_Ntk_t * p, int SigType )
{
    int NameId, RangeId, i;
    char * pSigNames[4]  = { "inout", "input", "output", "wire" }; 
    Vec_Int_t * vSigs[4] = { &p->vInouts, &p->vInputs, &p->vOutputs, &p->vWires };
    Vec_IntForEachEntryDouble( vSigs[SigType], NameId, RangeId, i )
        fprintf( pFile, "  %s %s%s;\n", pSigNames[SigType], RangeId ? Cba_NtkStr(p, RangeId) : "", Cba_NtkStr(p, NameId) );
}
void Cba_PrsWriteVerilogSignalList( FILE * pFile, Cba_Ntk_t * p, int SigType, int fSkipComma )
{
    int NameId, RangeId, i;
    Vec_Int_t * vSigs[4] = { &p->vInouts, &p->vInputs, &p->vOutputs, &p->vWires };
    Vec_IntForEachEntryDouble( vSigs[SigType], NameId, RangeId, i )
        fprintf( pFile, "%s%s", Cba_NtkStr(p, NameId), (fSkipComma && i == Vec_IntSize(vSigs[SigType]) - 2) ? "" : ", " );
}
void Cba_PrsWriteVerilogNtk( FILE * pFile, Cba_Ntk_t * p )
{
    int s;
    assert( Vec_IntSize(&p->vTypes)   == Cba_NtkObjNum(p) );
    assert( Vec_IntSize(&p->vFuncs)   == Cba_NtkObjNum(p) );
    assert( Vec_IntSize(&p->vInstIds) == Cba_NtkObjNum(p) );
    // write header
    fprintf( pFile, "module %s (\n", Cba_NtkName(p) );
    for ( s = 0; s < 3; s++ )
    {
        if ( s == 0 && Vec_IntSize(&p->vInouts) == 0 ) 
            continue;
        fprintf( pFile, "    " );
        Cba_PrsWriteVerilogSignalList( pFile, p, s, s==2 );
        fprintf( pFile, "\n" );
    }
    fprintf( pFile, "  );\n" );
    // write declarations
    for ( s = 0; s < 4; s++ )
        Cba_PrsWriteVerilogSignals( pFile, p, s );
    fprintf( pFile, "\n" );
    // write objects
    Cba_PrsWriteVerilogNodes( pFile, p );
    Cba_PrsWriteVerilogBoxes( pFile, p );
    fprintf( pFile, "endmodule\n\n" );
}
void Cba_PrsWriteVerilog( char * pFileName, Cba_Man_t * pDes )
{
    FILE * pFile;
    Cba_Ntk_t * pNtk; 
    int i;
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "// Design \"%s\" written by ABC on %s\n\n", Cba_ManName(pDes), Extra_TimeStamp() );
    Cba_ManForEachNtk( pDes, pNtk, i )
        Cba_PrsWriteVerilogNtk( pFile, pNtk );
    fclose( pFile );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

