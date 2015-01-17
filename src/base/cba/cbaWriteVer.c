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
        if ( Type == CBA_OBJ_NODE ) // .names/assign/box2 (no formal/actual binding)
        {
            Func = Cba_ObjFuncId(p, i);
            if ( Func >= CBA_NODE_BUF && Func <= CBA_NODE_XNOR )
            {
                fprintf( pFile, "  %s (", Ptr_TypeToName(Func) );
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
        if ( Type == CBA_OBJ_BOX ) // .subckt/.gate/box (formal/actual binding) 
        {
            fprintf( pFile, "  %s %s (", Cba_NtkName(Cba_ObjBoxModel(p, i)), Cba_ObjInstStr(p, i) );
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
void Cba_PrsWriteVerilog( char * pFileName, Cba_Man_t * p )
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
    fprintf( pFile, "// Design \"%s\" written by ABC on %s\n\n", Cba_ManName(p), Extra_TimeStamp() );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_PrsWriteVerilogNtk( pFile, pNtk );
    fclose( pFile );
}


/**Function*************************************************************

  Synopsis    [Collect all nodes names used that are not inputs/outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cba_NtkCollectWires( Cba_Ntk_t * p, Vec_Int_t * vMap )
{
    Vec_Int_t * vWires = &p->vWires; 
    int i, iObj, iFanin, Type, NameId;
    Vec_IntClear( vWires );
    Cba_NtkForEachPi( p, iObj, i )
        Vec_IntWriteEntry( vMap, Cba_ObjNameId(p, iObj), 1 );
    Cba_NtkForEachPo( p, iObj, i )
        Vec_IntWriteEntry( vMap, Cba_ObjNameId(p, iObj), 1 );
    Cba_NtkForEachObjType( p, Type, iObj )
    {
        if ( Type == CBA_OBJ_NODE )
        {
            Vec_Int_t * vFanins = Cba_ObjFaninVec( p, iObj );
            Vec_IntForEachEntry( vFanins, iFanin, i )
            {
                NameId = Cba_ObjNameId( p, iFanin );
                if ( Vec_IntEntry(vMap, NameId) == 0 )
                {
                    Vec_IntWriteEntry( vMap, NameId, 1 );
                    Vec_IntPush( vWires, NameId );
                }
            }
        }
        else if ( Cba_ObjIsPo(p, iObj) || Cba_ObjIsBi(p, iObj) )
        {
            iFanin = Cba_ObjFanin0( p, iObj );
            NameId = Cba_ObjNameId( p, iFanin );
            if ( Vec_IntEntry(vMap, NameId) == 0 )
            {
                Vec_IntWriteEntry( vMap, NameId, 1 );
                Vec_IntPush( vWires, NameId );
            }
        }
    }
    Cba_NtkForEachPi( p, iObj, i )
        Vec_IntWriteEntry( vMap, Cba_ObjNameId(p, iObj), 0 );
    Cba_NtkForEachPo( p, iObj, i )
        Vec_IntWriteEntry( vMap, Cba_ObjNameId(p, iObj), 0 );
    Vec_IntForEachEntry( vWires, NameId, i )
        Vec_IntWriteEntry( vMap, NameId, 0 );
    return vWires;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_ManWriteVerilogArray2( FILE * pFile, Cba_Ntk_t * p, int iObj, Vec_Int_t * vFanins )
{
    int i, iFanin;
    fprintf( pFile, "%s%s", Cba_ObjNameStr(p, iObj), (Vec_IntSize(vFanins) == 0) ? "" : ", " );
    Vec_IntForEachEntry( vFanins, iFanin, i )
        fprintf( pFile, "%s%s", Cba_ObjNameStr(p, iFanin), (i == Vec_IntSize(vFanins) - 1) ? "" : ", " );
}
void Cba_ManWriteVerilogNodes( FILE * pFile, Cba_Ntk_t * p )
{
    int Type, Func, i;
    Cba_NtkForEachObjType( p, Type, i )
        if ( Type == CBA_OBJ_NODE ) // .names/assign/box2 (no formal/actual binding)
        {
            Func = Cba_ObjFuncId(p, i);
            if ( Func >= CBA_NODE_BUF && Func <= CBA_NODE_XNOR )
            {
                fprintf( pFile, "  %s (", Ptr_TypeToName(Func) );
                Cba_ManWriteVerilogArray2( pFile, p, i, Cba_ObjFaninVec(p, i) );
                fprintf( pFile, ");\n" );
            }
//            else if ( Func == CBA_NODE_MUX )
//                Cba_PrsWriteVerilogMux( pFile, p, Cba_ObjFaninVec(p, i) );
            else
            {
                //char * pName = Cba_NtkStr(p, Func);
                assert( 0 );
            }
        }
}
void Cba_ManWriteVerilogBoxes( FILE * pFile, Cba_Ntk_t * p )
{
    int i, k, iTerm, Type;
    Cba_NtkForEachObjType( p, Type, i )
        if ( Type == CBA_OBJ_BOX ) // .subckt/.gate/box (formal/actual binding) 
        {
            Cba_Ntk_t * pModel = Cba_ObjBoxModel( p, i );
            fprintf( pFile, "  %s %s (", Cba_NtkName(pModel), Vec_IntSize(&p->vInstIds) ? Cba_ObjInstStr(p, i) : "" );
            Cba_NtkForEachPi( pModel, iTerm, k )
                fprintf( pFile, " %s=%s", Cba_ObjNameStr(pModel, iTerm), Cba_ObjNameStr(p, Cba_ObjBoxBi(p, i, k)) );
            Cba_NtkForEachPo( pModel, iTerm, k )
                fprintf( pFile, " %s=%s", Cba_ObjNameStr(pModel, iTerm), Cba_ObjNameStr(p, Cba_ObjBoxBo(p, i, k)) );
            fprintf( pFile, "\n" );
        }
}
void Cba_ManWriteVerilogSignals( FILE * pFile, Cba_Ntk_t * p, int SigType, int fNoRange )
{
    int NameId, RangeId, i;
    char * pSigNames[4]  = { "inout", "input", "output", "wire" }; 
    Vec_Int_t * vSigs[4] = { &p->vInouts, &p->vInputs, &p->vOutputs, &p->vWires };
    if ( fNoRange )
    {
        Vec_IntForEachEntry( vSigs[SigType], NameId, i )
            fprintf( pFile, "  %s %s;\n", pSigNames[SigType], SigType==3 ? Cba_NtkStr(p, NameId) : Cba_ObjNameStr(p, NameId) );
    }
    else
    {
        Vec_IntForEachEntryDouble( vSigs[SigType], NameId, RangeId, i )
            fprintf( pFile, "  %s %s%s;\n", pSigNames[SigType], RangeId ? Cba_NtkStr(p, RangeId) : "", SigType==3 ? Cba_NtkStr(p, NameId) : Cba_ObjNameStr(p, NameId) );
    }
}
void Cba_ManWriteVerilogSignalList( FILE * pFile, Cba_Ntk_t * p, int SigType, int fSkipComma, int fNoRange )
{
    int NameId, RangeId, i;
    Vec_Int_t * vSigs[4] = { &p->vInouts, &p->vInputs, &p->vOutputs, &p->vWires };
    if ( fNoRange )
    {
        Vec_IntForEachEntry( vSigs[SigType], NameId, i )
            fprintf( pFile, "%s%s", Cba_ObjNameStr(p, NameId), (fSkipComma && i == Vec_IntSize(vSigs[SigType]) - 1) ? "" : ", " );
    }
    else
    {
        Vec_IntForEachEntryDouble( vSigs[SigType], NameId, RangeId, i )
            fprintf( pFile, "%s%s", Cba_ObjNameStr(p, NameId), (fSkipComma && i == Vec_IntSize(vSigs[SigType]) - 2) ? "" : ", " );
    }
}
void Cba_ManWriteVerilogNtk( FILE * pFile, Cba_Ntk_t * p, Vec_Int_t * vMap )
{
    int s;
    assert( Vec_IntSize(&p->vTypes)   == Cba_NtkObjNum(p) );
    assert( Vec_IntSize(&p->vFuncs)   == Cba_NtkObjNum(p) );
    // collect wires
    Cba_NtkCollectWires( p, vMap );
    // write header
    fprintf( pFile, "module %s (\n", Cba_NtkName(p) );
    for ( s = 0; s < 3; s++ )
    {
        if ( s == 0 && Vec_IntSize(&p->vInouts) == 0 ) 
            continue;
        fprintf( pFile, "    " );
        Cba_ManWriteVerilogSignalList( pFile, p, s, s==2, 1 );
        fprintf( pFile, "\n" );
    }
    fprintf( pFile, "  );\n" );
    // write declarations
    for ( s = 0; s < 4; s++ )
        Cba_ManWriteVerilogSignals( pFile, p, s, 1 );
    fprintf( pFile, "\n" );
    // write objects
    Cba_ManWriteVerilogNodes( pFile, p );
    Cba_ManWriteVerilogBoxes( pFile, p );
    fprintf( pFile, "endmodule\n\n" );
    Vec_IntErase( &p->vWires );
}
void Cba_ManWriteVerilog( char * pFileName, Cba_Man_t * p )
{
    FILE * pFile;
    Cba_Ntk_t * pNtk; 
    Vec_Int_t * vMap;
    int i;
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "// Design \"%s\" written by ABC on %s\n\n", Cba_ManName(p), Extra_TimeStamp() );
    Cba_ManAssignInternNames( p );
    vMap = Vec_IntStart( Abc_NamObjNumMax(p->pNames) + 1 );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManWriteVerilogNtk( pFile, pNtk, vMap );
    Vec_IntFree( vMap );
    fclose( pFile );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

