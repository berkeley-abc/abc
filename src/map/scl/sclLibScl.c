/**CFile****************************************************************

  FileName    [sclLibScl.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Liberty abstraction for delay-oriented mapping.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclLibScl.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclLib.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"
#include "bool/kit/kit.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reading library from file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_SclReadSurface( Vec_Str_t * vOut, int * pPos, SC_Surface * p )
{
    Vec_Flt_t * vVec;
    int i, j;

    for ( i = Vec_StrGetI(vOut, pPos); i != 0; i-- )
        Vec_FltPush( p->vIndex0, Vec_StrGetF(vOut, pPos) );

    for ( i = Vec_StrGetI(vOut, pPos); i != 0; i-- )
        Vec_FltPush( p->vIndex1, Vec_StrGetF(vOut, pPos) );

    for ( i = 0; i < Vec_FltSize(p->vIndex0); i++ )
    {
        vVec = Vec_FltAlloc( Vec_FltSize(p->vIndex1) );
        Vec_PtrPush( p->vData, vVec );
        for ( j = 0; j < Vec_FltSize(p->vIndex1); j++ )
            Vec_FltPush( vVec, Vec_StrGetF(vOut, pPos) );
    }

    for ( i = 0; i < 3; i++ ) 
        p->approx[0][i] = Vec_StrGetF( vOut, pPos );
    for ( i = 0; i < 4; i++ ) 
        p->approx[1][i] = Vec_StrGetF( vOut, pPos );
    for ( i = 0; i < 6; i++ ) 
        p->approx[2][i] = Vec_StrGetF( vOut, pPos );
}
static void Abc_SclReadLibrary( Vec_Str_t * vOut, int * pPos, SC_Lib * p )
{
    int i, j, k, n;
    int version = Vec_StrGetI( vOut, pPos );
    assert( version == 5 || version == ABC_SCL_CUR_VERSION ); // wrong version of the file

    // Read non-composite fields:
    p->pName                 = Vec_StrGetS(vOut, pPos);
    p->default_wire_load     = Vec_StrGetS(vOut, pPos);
    p->default_wire_load_sel = Vec_StrGetS(vOut, pPos);
    p->default_max_out_slew  = Vec_StrGetF(vOut, pPos);

    p->unit_time             = Vec_StrGetI(vOut, pPos);
    p->unit_cap_fst          = Vec_StrGetF(vOut, pPos);
    p->unit_cap_snd          = Vec_StrGetI(vOut, pPos);

    // Read 'wire_load' vector:
    for ( i = Vec_StrGetI(vOut, pPos); i != 0; i-- )
    {
        SC_WireLoad * pWL = Abc_SclWireLoadAlloc();
        Vec_PtrPush( p->vWireLoads, pWL );

        pWL->pName = Vec_StrGetS(vOut, pPos);
        pWL->res  = Vec_StrGetF(vOut, pPos);
        pWL->cap  = Vec_StrGetF(vOut, pPos);

        for ( j = Vec_StrGetI(vOut, pPos); j != 0; j-- )
        {
            Vec_IntPush( pWL->vFanout, Vec_StrGetI(vOut, pPos) );
            Vec_FltPush( pWL->vLen,    Vec_StrGetF(vOut, pPos) );
        }
    }

    // Read 'wire_load_sel' vector:
    for ( i = Vec_StrGetI(vOut, pPos); i != 0; i-- )
    {
        SC_WireLoadSel * pWLS = Abc_SclWireLoadSelAlloc();
        Vec_PtrPush( p->vWireLoadSels, pWLS );

        pWLS->pName = Vec_StrGetS(vOut, pPos);
        for ( j = Vec_StrGetI(vOut, pPos); j != 0; j-- )
        {
            Vec_FltPush( pWLS->vAreaFrom,      Vec_StrGetF(vOut, pPos) );
            Vec_FltPush( pWLS->vAreaTo,        Vec_StrGetF(vOut, pPos) );
            Vec_PtrPush( pWLS->vWireLoadModel, Vec_StrGetS(vOut, pPos) );
        }
    }

    for ( i = Vec_StrGetI(vOut, pPos); i != 0; i-- )
    {
        SC_Cell * pCell = Abc_SclCellAlloc();
        pCell->Id = SC_LibCellNum(p);
        Vec_PtrPush( p->vCells, pCell );

        pCell->pName           = Vec_StrGetS(vOut, pPos);     
        pCell->area           = Vec_StrGetF(vOut, pPos);
        pCell->drive_strength = Vec_StrGetI(vOut, pPos);

        pCell->n_inputs       = Vec_StrGetI(vOut, pPos);
        pCell->n_outputs      = Vec_StrGetI(vOut, pPos);
/*
        printf( "%s\n", pCell->pName );
        if ( !strcmp( "XOR3_X4M_A9TL", pCell->pName ) )
        {
            int s = 0;
        }
*/
        for ( j = 0; j < pCell->n_inputs; j++ )
        {
            SC_Pin * pPin = Abc_SclPinAlloc();
            Vec_PtrPush( pCell->vPins, pPin );

            pPin->dir      = sc_dir_Input;
            pPin->pName    = Vec_StrGetS(vOut, pPos); 
            pPin->rise_cap = Vec_StrGetF(vOut, pPos);
            pPin->fall_cap = Vec_StrGetF(vOut, pPos);
        }

        for ( j = 0; j < pCell->n_outputs; j++ )
        {
            SC_Pin * pPin = Abc_SclPinAlloc();
            Vec_PtrPush( pCell->vPins, pPin );

            pPin->dir          = sc_dir_Output;
            pPin->pName        = Vec_StrGetS(vOut, pPos); 
            pPin->max_out_cap  = Vec_StrGetF(vOut, pPos);
            pPin->max_out_slew = Vec_StrGetF(vOut, pPos);

            k = Vec_StrGetI(vOut, pPos);
            assert( k == pCell->n_inputs );

            // read function
            if ( version == 5 )
            { 
                // formula is not given
                assert( Vec_WrdSize(pPin->vFunc) == 0 );
                Vec_WrdGrow( pPin->vFunc, Abc_Truth6WordNum(pCell->n_inputs) );
                for ( k = 0; k < Vec_WrdCap(pPin->vFunc); k++ )
                    Vec_WrdPush( pPin->vFunc, Vec_StrGetW(vOut, pPos) );
            }
            else
            {
                // (possibly empty) formula is always given
                assert( version == ABC_SCL_CUR_VERSION );
                assert( pPin->func_text == NULL );
                pPin->func_text = Vec_StrGetS(vOut, pPos); 
                if ( pPin->func_text[0] == 0 )
                {
                    // formula is not given - read truth table
                    ABC_FREE( pPin->func_text );
                    assert( Vec_WrdSize(pPin->vFunc) == 0 );
                    Vec_WrdGrow( pPin->vFunc, Abc_Truth6WordNum(pCell->n_inputs) );
                    for ( k = 0; k < Vec_WrdCap(pPin->vFunc); k++ )
                        Vec_WrdPush( pPin->vFunc, Vec_StrGetW(vOut, pPos) );
                }
                else
                {
                    // formula is given - derive truth table
                    SC_Pin * pPin2;
                    Vec_Ptr_t * vNames;
                    // collect input names
                    vNames = Vec_PtrAlloc( pCell->n_inputs );
                    SC_CellForEachPinIn( pCell, pPin2, n )
                        Vec_PtrPush( vNames, pPin2->pName );
                    // derive truth table
                    assert( Vec_WrdSize(pPin->vFunc) == 0 );
                    Vec_WrdFree( pPin->vFunc );
                    pPin->vFunc = Mio_ParseFormulaTruth( pPin->func_text, (char **)Vec_PtrArray(vNames), pCell->n_inputs );
                    Vec_PtrFree( vNames );
                    // skip truth table
                    assert( Vec_WrdSize(pPin->vFunc) == Abc_Truth6WordNum(pCell->n_inputs) );
                    for ( k = 0; k < Vec_WrdSize(pPin->vFunc); k++ )
                    {
                        word Value = Vec_StrGetW(vOut, pPos);
                        assert( Value == Vec_WrdEntry(pPin->vFunc, k) );
                    }
                }
            }

            // Read 'rtiming': (pin-to-pin timing tables for this particular output)
            for ( k = 0; k < pCell->n_inputs; k++ )
            {
                SC_Timings * pRTime = Abc_SclTimingsAlloc();
                Vec_PtrPush( pPin->vRTimings, pRTime );

                pRTime->pName = Vec_StrGetS(vOut, pPos);
                n = Vec_StrGetI(vOut, pPos); assert( n <= 1 );
                if ( n == 1 )
                {
                    SC_Timing * pTime = Abc_SclTimingAlloc();
                    Vec_PtrPush( pRTime->vTimings, pTime );

                    pTime->tsense = (SC_TSense)Vec_StrGetI(vOut, pPos);
                    Abc_SclReadSurface( vOut, pPos, pTime->pCellRise );
                    Abc_SclReadSurface( vOut, pPos, pTime->pCellFall );
                    Abc_SclReadSurface( vOut, pPos, pTime->pRiseTrans );
                    Abc_SclReadSurface( vOut, pPos, pTime->pFallTrans );
                }
                else
                    assert( Vec_PtrSize(pRTime->vTimings) == 0 );
            }
        }
    }
}
SC_Lib * Abc_SclReadFromStr( Vec_Str_t * vOut )
{
    SC_Lib * p;
    int Pos = 0;
    // read the library
    p = Abc_SclLibAlloc();
    Abc_SclReadLibrary( vOut, &Pos, p );
    assert( Pos == Vec_StrSize(vOut) );
    // hash gates by name
    Abc_SclHashCells( p );
    Abc_SclLinkCells( p );
    return p;
}
SC_Lib * Abc_SclReadFromFile( char * pFileName )
{
    SC_Lib * p;
    FILE * pFile;
    Vec_Str_t * vOut;
    int nFileSize;
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return NULL;
    }
    // get the file size, in bytes
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile );  
    rewind( pFile ); 
    // load the contents
    vOut = Vec_StrAlloc( nFileSize );
    vOut->nSize = vOut->nCap;
    assert( nFileSize == Vec_StrSize(vOut) );
    nFileSize = fread( Vec_StrArray(vOut), 1, Vec_StrSize(vOut), pFile );
    assert( nFileSize == Vec_StrSize(vOut) );
    fclose( pFile );
    // read the library
    p = Abc_SclReadFromStr( vOut );
    p->pFileName = Abc_UtilStrsav( pFileName );
    Vec_StrFree( vOut );
    return p;
}

/**Function*************************************************************

  Synopsis    [Writing library into file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_SclWriteSurface( Vec_Str_t * vOut, SC_Surface * p )
{
    Vec_Flt_t * vVec;
    float Entry;
    int i, k;

    Vec_StrPutI( vOut, Vec_FltSize(p->vIndex0) );
    Vec_FltForEachEntry( p->vIndex0, Entry, i )
        Vec_StrPutF( vOut, Entry );

    Vec_StrPutI( vOut, Vec_FltSize(p->vIndex1) );
    Vec_FltForEachEntry( p->vIndex1, Entry, i )
        Vec_StrPutF( vOut, Entry );

    Vec_PtrForEachEntry( Vec_Flt_t *, p->vData, vVec, i )
        Vec_FltForEachEntry( vVec, Entry, k )
            Vec_StrPutF( vOut, Entry );

    for ( i = 0; i < 3; i++ ) 
        Vec_StrPutF( vOut, p->approx[0][i] );
    for ( i = 0; i < 4; i++ ) 
        Vec_StrPutF( vOut, p->approx[1][i] );
    for ( i = 0; i < 6; i++ ) 
        Vec_StrPutF( vOut, p->approx[2][i] );
}
static void Abc_SclWriteLibrary( Vec_Str_t * vOut, SC_Lib * p )
{
    SC_WireLoad * pWL;
    SC_WireLoadSel * pWLS;
    SC_Cell * pCell;
    SC_Pin * pPin;
    int n_valid_cells;
    int i, j, k;

    Vec_StrPutI( vOut, ABC_SCL_CUR_VERSION );

    // Write non-composite fields:
    Vec_StrPutS( vOut, p->pName );
    Vec_StrPutS( vOut, p->default_wire_load );
    Vec_StrPutS( vOut, p->default_wire_load_sel );
    Vec_StrPutF( vOut, p->default_max_out_slew );

    assert( p->unit_time >= 0 );
    assert( p->unit_cap_snd >= 0 );
    Vec_StrPutI( vOut, p->unit_time );
    Vec_StrPutF( vOut, p->unit_cap_fst );
    Vec_StrPutI( vOut, p->unit_cap_snd );

    // Write 'wire_load' vector:
    Vec_StrPutI( vOut, Vec_PtrSize(p->vWireLoads) );
    SC_LibForEachWireLoad( p, pWL, i )
    {
        Vec_StrPutS( vOut, pWL->pName );
        Vec_StrPutF( vOut, pWL->res );
        Vec_StrPutF( vOut, pWL->cap );

        Vec_StrPutI( vOut, Vec_IntSize(pWL->vFanout) );
        for ( j = 0; j < Vec_IntSize(pWL->vFanout); j++ )
        {
            Vec_StrPutI( vOut, Vec_IntEntry(pWL->vFanout, j) );
            Vec_StrPutF( vOut, Vec_FltEntry(pWL->vLen, j) );
        }
    }

    // Write 'wire_load_sel' vector:
    Vec_StrPutI( vOut, Vec_PtrSize(p->vWireLoadSels) );
    SC_LibForEachWireLoadSel( p, pWLS, i )
    {
        Vec_StrPutS( vOut, pWLS->pName );
        Vec_StrPutI( vOut, Vec_FltSize(pWLS->vAreaFrom) );
        for ( j = 0; j < Vec_FltSize(pWLS->vAreaFrom); j++)
        {
            Vec_StrPutF( vOut, Vec_FltEntry(pWLS->vAreaFrom, j) );
            Vec_StrPutF( vOut, Vec_FltEntry(pWLS->vAreaTo, j) );
            Vec_StrPutS( vOut, (char *)Vec_PtrEntry(pWLS->vWireLoadModel, j) );
        }
    }

    // Write 'cells' vector:
    n_valid_cells = 0;
    SC_LibForEachCell( p, pCell, i )
        if ( !(pCell->seq || pCell->unsupp) )
            n_valid_cells++;

    Vec_StrPutI( vOut, n_valid_cells );
    SC_LibForEachCell( p, pCell, i )
    {
        if ( pCell->seq || pCell->unsupp )
            continue;

        Vec_StrPutS( vOut, pCell->pName );
        Vec_StrPutF( vOut, pCell->area );
        Vec_StrPutI( vOut, pCell->drive_strength );

        // Write 'pins': (sorted at this point; first inputs, then outputs)
        Vec_StrPutI( vOut, pCell->n_inputs);
        Vec_StrPutI( vOut, pCell->n_outputs);

        SC_CellForEachPinIn( pCell, pPin, j )
        {
            assert(pPin->dir == sc_dir_Input);
            Vec_StrPutS( vOut, pPin->pName );
            Vec_StrPutF( vOut, pPin->rise_cap );
            Vec_StrPutF( vOut, pPin->fall_cap );
        }

        SC_CellForEachPinOut( pCell, pPin, j )
        {
            SC_Timings * pRTime;
            word uWord;

            assert(pPin->dir == sc_dir_Output);
            Vec_StrPutS( vOut, pPin->pName );
            Vec_StrPutF( vOut, pPin->max_out_cap );
            Vec_StrPutF( vOut, pPin->max_out_slew );

            // write function
            if ( pPin->func_text == NULL )
            {
                // formula is not given - write empty string
                Vec_StrPutS( vOut, "" );
                // write truth table
                assert( Vec_WrdSize(pPin->vFunc) == Abc_Truth6WordNum(pCell->n_inputs) );
                Vec_StrPutI( vOut, pCell->n_inputs );
                Vec_WrdForEachEntry( pPin->vFunc, uWord, k ) // -- 'size = 1u << (n_vars - 6)'
                    Vec_StrPutW( vOut, uWord );  // -- 64-bit number, written uncompressed (low-byte first)
            }
            else // formula is given
                Vec_StrPutS( vOut, pPin->func_text );

            // Write 'rtiming': (pin-to-pin timing tables for this particular output)
            assert( Vec_PtrSize(pPin->vRTimings) == pCell->n_inputs );
            SC_PinForEachRTiming( pPin, pRTime, k )
            {
                Vec_StrPutS( vOut, pRTime->pName );
                Vec_StrPutI( vOut, Vec_PtrSize(pRTime->vTimings) );
                    // -- NOTE! After post-processing, the size of the 'rtiming[k]' vector is either
                    // 0 or 1 (in static timing, we have merged all tables to get the worst case).
                    // The case with size 0 should only occur for multi-output gates.
                if ( Vec_PtrSize(pRTime->vTimings) == 1 )
                {
                    SC_Timing * pTime = (SC_Timing *)Vec_PtrEntry( pRTime->vTimings, 0 );
                        // -- NOTE! We don't need to save 'related_pin' string because we have sorted 
                        // the elements on input pins.
                    Vec_StrPutI( vOut, (int)pTime->tsense);
                    Abc_SclWriteSurface( vOut, pTime->pCellRise );
                    Abc_SclWriteSurface( vOut, pTime->pCellFall );
                    Abc_SclWriteSurface( vOut, pTime->pRiseTrans );
                    Abc_SclWriteSurface( vOut, pTime->pFallTrans );
                }
                else
                    assert( Vec_PtrSize(pRTime->vTimings) == 0 );
            }
        }
    }
}
void Abc_SclWriteScl( char * pFileName, SC_Lib * p )
{
    Vec_Str_t * vOut;
    vOut = Vec_StrAlloc( 10000 );
    Abc_SclWriteLibrary( vOut, p );
    if ( Vec_StrSize(vOut) > 0 )
    {
        FILE * pFile = fopen( pFileName, "wb" );
        if ( pFile == NULL )
            printf( "Cannot open file \"%s\" for writing.\n", pFileName );
        else
        {
            fwrite( Vec_StrArray(vOut), 1, Vec_StrSize(vOut), pFile );
            fclose( pFile );
        }
    }
    Vec_StrFree( vOut );    
}


/**Function*************************************************************

  Synopsis    [Writing library into text file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_SclWriteSurfaceText( FILE * s, SC_Surface * p )
{
    Vec_Flt_t * vVec;
    float Entry;
    int i, k;

    fprintf( s, "          index_1(\"" );  
    Vec_FltForEachEntry( p->vIndex0, Entry, i )
        fprintf( s, "%f%s", Entry, i == Vec_FltSize(p->vIndex0)-1 ? "":", " );
    fprintf( s, "\");\n" );

    fprintf( s, "          index_2(\"" );  
    Vec_FltForEachEntry( p->vIndex1, Entry, i )
        fprintf( s, "%f%s", Entry, i == Vec_FltSize(p->vIndex1)-1 ? "":", " );
    fprintf( s, "\");\n" );

    fprintf( s, "          values (\"" );  
    Vec_PtrForEachEntry( Vec_Flt_t *, p->vData, vVec, i )
    {
        Vec_FltForEachEntry( vVec, Entry, k )
            fprintf( s, "%f%s", Entry, i == Vec_PtrSize(p->vData)-1 && k == Vec_FltSize(vVec)-1 ? "\");":", " );
        if ( i == Vec_PtrSize(p->vData)-1 )
            fprintf( s, "\n" );
        else
        {
            fprintf( s, "\\\n" );
            fprintf( s, "                   " );  
        }
    }
/*
    fprintf( s, "       approximations: \n" );
    fprintf( s, "       " );
    for ( i = 0; i < 3; i++ ) 
        fprintf( s, "%f ", p->approx[0][i] );
    fprintf( s, "\n" );
    fprintf( s, "       " );
    for ( i = 0; i < 4; i++ ) 
        fprintf( s, "%f ", p->approx[1][i] );
    fprintf( s, "\n" );
    fprintf( s, "       " );
    for ( i = 0; i < 6; i++ ) 
        fprintf( s, "%f ", p->approx[2][i] );
    fprintf( s, "\n" );
    fprintf( s, "       \n" );
*/
}
static void Abc_SclWriteLibraryText( FILE * s, SC_Lib * p )
{
    SC_WireLoad * pWL;
    SC_WireLoadSel * pWLS;
    SC_Cell * pCell;
    SC_Pin * pPin;
    int n_valid_cells;
    int i, j, k;
    fprintf( s, "/* This Liberty file was generated by ABC on %s */\n", Extra_TimeStamp() );
    fprintf( s, "/* The original unabridged library came from file \"%s\".*/\n\n", p->pFileName );

//    fprintf( s, "%d", ABC_SCL_CUR_VERSION );
    fprintf( s, "library(%s) {\n\n",                         p->pName );
    if ( p->default_wire_load && strlen(p->default_wire_load) )
    fprintf( s, "  default_wire_load : \"%s\";\n",           p->default_wire_load );
    if ( p->default_wire_load_sel && strlen(p->default_wire_load_sel) )
    fprintf( s, "  default_wire_load_selection : \"%s\";\n", p->default_wire_load_sel );
    if ( p->default_max_out_slew != -1 )
    fprintf( s, "  default_max_transition : %f;\n",          p->default_max_out_slew );
    if ( p->unit_time == 9 )
    fprintf( s, "  time_unit : \"1ns\";\n" );
    else if ( p->unit_time == 10 )
    fprintf( s, "  time_unit : \"100ps\";\n" );
    else if ( p->unit_time == 11 )
    fprintf( s, "  time_unit : \"10ps\";\n" );
    else if ( p->unit_time == 12 )
    fprintf( s, "  time_unit : \"1ps\";\n" );
    else assert( 0 );
    fprintf( s, "  capacitive_load_unit(%.1f,%s);\n",        p->unit_cap_fst, p->unit_cap_snd == 12 ? "pf" : "ff" );
    fprintf( s, "\n" );

    // Write 'wire_load' vector:
    SC_LibForEachWireLoad( p, pWL, i )
    {
        fprintf( s, "  wire_load(\"%s\") {\n", pWL->pName );
        fprintf( s, "    resistance : %f;\n", pWL->res );
        fprintf( s, "    capacitance : %f;\n", pWL->cap );
        for ( j = 0; j < Vec_IntSize(pWL->vFanout); j++ )
            fprintf( s, "    fanout_length( %d, %f );\n", Vec_IntEntry(pWL->vFanout, j), Vec_FltEntry(pWL->vLen, j) );
        fprintf( s, "  }\n\n" );
    }

    // Write 'wire_load_sel' vector:
    SC_LibForEachWireLoadSel( p, pWLS, i )
    {
        fprintf( s, "  wire_load_selection(\"%s\") {\n", pWLS->pName );
        for ( j = 0; j < Vec_FltSize(pWLS->vAreaFrom); j++)
            fprintf( s, "    wire_load_from_area( %f, %f, %s );\n", 
                Vec_FltEntry(pWLS->vAreaFrom, j), 
                Vec_FltEntry(pWLS->vAreaTo, j), 
                (char *)Vec_PtrEntry(pWLS->vWireLoadModel, j) );
        fprintf( s, "  }\n\n" );
    }

    // Write 'cells' vector:
    n_valid_cells = 0;
    SC_LibForEachCell( p, pCell, i )
        if ( !(pCell->seq || pCell->unsupp) )
            n_valid_cells++;

    SC_LibForEachCell( p, pCell, i )
    {
        if ( pCell->seq || pCell->unsupp )
            continue;

        fprintf( s, "\n" );
        fprintf( s, "  cell(%s) {\n", pCell->pName );
        fprintf( s, "    /*  n_inputs = %d  n_outputs = %d */\n", pCell->n_inputs, pCell->n_outputs );
        fprintf( s, "    area : %f;\n", pCell->area );
        fprintf( s, "    drive_strength : %d;\n", pCell->drive_strength );

        SC_CellForEachPinIn( pCell, pPin, j )
        {
            assert(pPin->dir == sc_dir_Input);
            fprintf( s, "    pin(%s) {\n", pPin->pName );
            fprintf( s, "      direction : %s;\n", "input" );
            fprintf( s, "      fall_capacitance : %f;\n", pPin->fall_cap );
            fprintf( s, "      rise_capacitance : %f;\n", pPin->rise_cap );
            fprintf( s, "    }\n" );
        }

        SC_CellForEachPinOut( pCell, pPin, j )
        {
            SC_Timings * pRTime;
//            word uWord;
            assert(pPin->dir == sc_dir_Output);
            fprintf( s, "    pin(%s) {\n", pPin->pName );
            fprintf( s, "      direction : %s;\n", "output" );
            fprintf( s, "      max_capacitance : %f;\n", pPin->max_out_cap );
            fprintf( s, "      max_transition : %f;\n", pPin->max_out_slew );
            fprintf( s, "      function : \"%s\";\n", pPin->func_text ? pPin->func_text : "?" );
            fprintf( s, "      /*  truth table = " );
            Extra_PrintHex( s, (unsigned *)Vec_WrdArray(pPin->vFunc), pCell->n_inputs );
            fprintf( s, "  */\n" );

            // Write 'rtiming': (pin-to-pin timing tables for this particular output)
            assert( Vec_PtrSize(pPin->vRTimings) == pCell->n_inputs );
            SC_PinForEachRTiming( pPin, pRTime, k )
            {
                if ( Vec_PtrSize(pRTime->vTimings) == 1 )
                {
                    SC_Timing * pTime = (SC_Timing *)Vec_PtrEntry( pRTime->vTimings, 0 );
                    fprintf( s, "      timing() {\n" );
                    fprintf( s, "        related_pin : \"%s\"\n", pRTime->pName );
                    if ( pTime->tsense == sc_ts_Pos )
                        fprintf( s, "        timing_sense : positive_unate;\n" );
                    else if ( pTime->tsense == sc_ts_Neg )
                        fprintf( s, "        timing_sense : negative_unate;\n" );
                    else if ( pTime->tsense == sc_ts_Non )
                        fprintf( s, "        timing_sense : non_unate;\n" );
                    else assert( 0 );

                    fprintf( s, "        cell_rise() {\n" );
                    Abc_SclWriteSurfaceText( s, pTime->pCellRise );
                    fprintf( s, "        }\n" );

                    fprintf( s, "        cell_fall() {\n" );
                    Abc_SclWriteSurfaceText( s, pTime->pCellFall );
                    fprintf( s, "        }\n" );

                    fprintf( s, "        rise_transition() {\n" );
                    Abc_SclWriteSurfaceText( s, pTime->pRiseTrans );
                    fprintf( s, "        }\n" );

                    fprintf( s, "        fall_transition() {\n" );
                    Abc_SclWriteSurfaceText( s, pTime->pFallTrans );
                    fprintf( s, "        }\n" );
                    fprintf( s, "      }\n" );
                }
                else
                    assert( Vec_PtrSize(pRTime->vTimings) == 0 );
            }
            fprintf( s, "    }\n" );
        }
        fprintf( s, "  }\n" );
    }
    fprintf( s, "}\n\n" );
}
void Abc_SclWriteLiberty( char * pFileName, SC_Lib * p )
{
    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
        printf( "Cannot open text file \"%s\" for writing.\n", pFileName );
    else
    {
        Abc_SclWriteLibraryText( pFile, p );
        fclose( pFile );
        printf( "Dumped internal library into Liberty file \"%s\".\n", pFileName );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

