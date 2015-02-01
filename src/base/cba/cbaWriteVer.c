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

  Synopsis    [Collect all nodes names used that are not inputs/outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cba_NtkCollectWires( Cba_Ntk_t * p, Vec_Int_t * vMap, Vec_Int_t * vWires )
{
    int i, k, iTerm, iObj, NameId;
    Vec_IntClear( vWires );
    Cba_NtkForEachPi( p, iObj, i )
        Vec_IntWriteEntry( vMap, Cba_ObjName(p, iObj), 1 );
    Cba_NtkForEachPo( p, iObj, i )
        Vec_IntWriteEntry( vMap, Cba_ObjName(p, iObj), 1 );
    Cba_NtkForEachBox( p, iObj )
    {
        Cba_BoxForEachBi( p, iObj, iTerm, k )
        {
            NameId = Cba_ObjName( p, iTerm );
            if ( Vec_IntEntry(vMap, NameId) == 0 )
            {
                Vec_IntWriteEntry( vMap, NameId, 1 );
                Vec_IntPush( vWires, iTerm );
            }
        }
        Cba_BoxForEachBo( p, iObj, iTerm, k )
        {
            NameId = Cba_ObjName( p, iTerm );
            if ( Vec_IntEntry(vMap, NameId) == 0 )
            {
                Vec_IntWriteEntry( vMap, NameId, 1 );
                Vec_IntPush( vWires, iTerm );
            }
        }
    }
    Cba_NtkForEachPi( p, iObj, i )
        Vec_IntWriteEntry( vMap, Cba_ObjName(p, iObj), 0 );
    Cba_NtkForEachPo( p, iObj, i )
        Vec_IntWriteEntry( vMap, Cba_ObjName(p, iObj), 0 );
    Vec_IntForEachEntry( vWires, iObj, i )
        Vec_IntWriteEntry( vMap, Cba_ObjName(p, iObj), 0 );
    //Vec_IntSort( vWires, 0 );
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
void Cba_ManWriteVerilogBoxes( FILE * pFile, Cba_Ntk_t * p )
{
    int i, k, iTerm;
    Cba_NtkForEachBox( p, i ) // .subckt/.gate/box (formal/actual binding) 
    {
        if ( Cba_ObjIsBoxUser(p, i) )
        {
            Cba_Ntk_t * pModel = Cba_BoxNtk( p, i );
            fprintf( pFile, "  %s %s (", Cba_NtkName(pModel), Cba_ObjNameStr(p, i) ? Cba_ObjNameStr(p, i) : "" );
            Cba_NtkForEachPi( pModel, iTerm, k )
                fprintf( pFile, "%s.%s(%s)", k ? ", " : "", Cba_ObjNameStr(pModel, iTerm), Cba_ObjNameStr(p, Cba_BoxBi(p, i, k)) );
            Cba_NtkForEachPo( pModel, iTerm, k )
                fprintf( pFile, "%s.%s(%s)", Cba_NtkPiNum(pModel) ? ", " : "", Cba_ObjNameStr(pModel, iTerm), Cba_ObjNameStr(p, Cba_BoxBo(p, i, k)) );
            fprintf( pFile, ")\n" );
        }
        else
        {
            Cba_ObjType_t Type = Cba_ObjType( p, i );
            int nInputs = Cba_BoxBiNum(p, i);
            fprintf( pFile, "  %s (", Ptr_TypeToName(Type) );
            Cba_BoxForEachBo( p, i, iTerm, k )
                fprintf( pFile, "%s%s", Cba_ObjNameStr(p, iTerm), nInputs ? ", " : "" );
            Cba_BoxForEachBi( p, i, iTerm, k )
                fprintf( pFile, "%s%s", Cba_ObjNameStr(p, iTerm), k < nInputs - 1 ? ", " : "" );
            fprintf( pFile, ");\n" );
        }
    }
}
void Cba_ManWriteVerilogSignals( FILE * pFile, Cba_Ntk_t * p, int SigType, int fNoRange, Vec_Int_t * vWires )
{
    int NameId, RangeId, i;
    char * pSigNames[3]  = { "input", "output", "wire" }; 
    Vec_Int_t * vSigs[3] = { &p->vInputs, &p->vOutputs, vWires };
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
void Cba_ManWriteVerilogSignalList( FILE * pFile, Cba_Ntk_t * p, int SigType, int fSkipComma, int fNoRange, Vec_Int_t * vWires )
{
    int NameId, RangeId, i;
    Vec_Int_t * vSigs[3] = { &p->vInputs, &p->vOutputs, vWires };
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
void Cba_ManWriteVerilogNtk( FILE * pFile, Cba_Ntk_t * p, Vec_Int_t * vMap, Vec_Int_t * vWires )
{
    int s;
    assert( Vec_IntSize(&p->vFanin) == Cba_NtkObjNum(p) );
    // collect wires
    Cba_NtkCollectWires( p, vMap, vWires );
    // write header
    fprintf( pFile, "module %s (\n", Cba_NtkName(p) );
    for ( s = 0; s < 2; s++ )
    {
        fprintf( pFile, "    " );
        Cba_ManWriteVerilogSignalList( pFile, p, s, s==2, 1, vWires );
        fprintf( pFile, "\n" );
    }
    fprintf( pFile, "  );\n" );
    // write declarations
    for ( s = 0; s < 3; s++ )
        Cba_ManWriteVerilogSignals( pFile, p, s, 1, vWires );
    fprintf( pFile, "\n" );
    // write objects
    Cba_ManWriteVerilogBoxes( pFile, p );
    fprintf( pFile, "endmodule\n\n" );
}
void Cba_ManWriteVerilog( char * pFileName, Cba_Man_t * p )
{
    FILE * pFile;
    Cba_Ntk_t * pNtk; 
    Vec_Int_t * vMap, * vWires;
    int i;
    // check the library
    if ( p->pMioLib && p->pMioLib != Abc_FrameReadLibGen() )
    {
        printf( "Genlib library used in the mapped design is not longer a current library.\n" );
        return;
    }
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "// Design \"%s\" written by ABC on %s\n\n", Cba_ManName(p), Extra_TimeStamp() );
    Cba_ManAssignInternNames( p );
    vMap = Vec_IntStart( Abc_NamObjNumMax(p->pStrs) + 1 );
    vWires = Vec_IntAlloc( 1000 );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManWriteVerilogNtk( pFile, pNtk, vMap, vWires );
    Vec_IntFree( vWires );
    Vec_IntFree( vMap );
    fclose( pFile );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

