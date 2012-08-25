/**CFile****************************************************************

  FileName    [sclIo.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  Synopsis    [Standard-cell library representation.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclIo.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Binary IO for numbers (int, word, float) and string (char*).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_SclPutI( Vec_Str_t * vOut, word Val )
{
    int i;
    for ( i = 0; i < 4; i++ )
        Vec_StrPush( vOut, (char)(Val >> (8*i)) );
}
static inline int Abc_SclGetI( Vec_Str_t * vOut, int * pPos )
{
    int i;
    int Val = 0;
    for ( i = 0; i < 4; i++ )
        Val |= (int)(unsigned char)Vec_StrEntry(vOut, *pPos++) << (8*i);
    return Val;
}

static inline void Abc_SclPutW( Vec_Str_t * vOut, word Val )
{
    int i;
    for ( i = 0; i < 8; i++ )
        Vec_StrPush( vOut, (char)(Val >> (8*i)) );
}
static inline word Abc_SclGetW( Vec_Str_t * vOut, int * pPos )
{
    int i;
    word Val = 0;
    for ( i = 0; i < 8; i++ )
        Val |= (word)(unsigned char)Vec_StrEntry(vOut, *pPos++) << (8*i);
    return Val;
}

static inline void Abc_SclPutF( Vec_Str_t * vOut, float Val )
{
    union { float num; unsigned char data[4]; } tmp;
    tmp.num = Val;
    Vec_StrPush( vOut, tmp.data[0] );
    Vec_StrPush( vOut, tmp.data[1] );
    Vec_StrPush( vOut, tmp.data[2] );
    Vec_StrPush( vOut, tmp.data[3] );
}
static inline float Abc_SclGetF( Vec_Str_t * vOut, int * pPos )
{
    union { float num; unsigned char data[4]; } tmp;
    tmp.data[0] = Vec_StrEntry( vOut, *pPos++ );
    tmp.data[1] = Vec_StrEntry( vOut, *pPos++ );
    tmp.data[2] = Vec_StrEntry( vOut, *pPos++ );
    tmp.data[3] = Vec_StrEntry( vOut, *pPos++ );
    return tmp.num;
}

static inline void Abc_SclPutS( Vec_Str_t * vOut, char * pStr )
{
    while ( *pStr )
        Vec_StrPush( vOut, *pStr++ );
    Vec_StrPush( vOut, (char)0 );
}
static inline char * Abc_SclGetS( Vec_Str_t * vOut, int * pPos )
{
    char * pStr = Vec_StrEntryP( vOut, *pPos );
    while ( Vec_StrEntry(vOut, *pPos++) );
    return Abc_UtilStrsav(pStr);
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
    int i, k, Entry;
    float EntryF;

    Abc_SclPutI( vOut, Vec_FltSize(p->vIndex0) );
    Vec_FltForEachEntry( p->vIndex0, Entry, i )
        Abc_SclPutF( vOut, Entry );

    Abc_SclPutI( vOut, Vec_FltSize(p->vIndex1) );
    Vec_FltForEachEntry( p->vIndex1, Entry, i )
        Abc_SclPutF( vOut, Entry );

    Vec_PtrForEachEntry( Vec_Flt_t *, p->vData, vVec, k )
        Vec_FltForEachEntry( vVec, EntryF, i )
            Abc_SclPutF( vOut, EntryF );

    for ( i = 0; i < 3; i++ ) 
        Abc_SclPutF( vOut, 0 );
    for ( i = 0; i < 4; i++ ) 
        Abc_SclPutF( vOut, 0 );
    for ( i = 0; i < 6; i++ ) 
        Abc_SclPutF( vOut, 0 );
}
static void Abc_SclWriteLibrary( Vec_Str_t * vOut, SC_Lib * p )
{
    SC_WireLoad * pWL;
    SC_WireLoadSel * pWLS;
    SC_Cell * pCell;
    int n_valid_cells;
    int i, j, k;

    Abc_SclPutI( vOut, ABC_SCL_CUR_VERSION );

    // Write non-composite fields:
    Abc_SclPutS( vOut, p->lib_name );
    Abc_SclPutS( vOut, p->default_wire_load );
    Abc_SclPutS( vOut, p->default_wire_load_sel );
    Abc_SclPutF( vOut, p->default_max_out_slew );

    assert( p->unit_time >= 0 );
    assert( p->unit_cap_int >= 0 );
    Abc_SclPutI( vOut, p->unit_time );
    Abc_SclPutF( vOut, p->unit_cap_float );
    Abc_SclPutI( vOut, p->unit_cap_int );

    // Write 'wire_load' vector:
    Abc_SclPutI( vOut, Vec_PtrSize(p->vWireLoads) );
    Vec_PtrForEachEntry( SC_WireLoad *, p->vWireLoads, pWL, i )
    {
        Abc_SclPutS( vOut, pWL->name );
        Abc_SclPutF( vOut, pWL->res );
        Abc_SclPutF( vOut, pWL->cap );

        Abc_SclPutI( vOut, Vec_IntSize(pWL->vFanout) );
        for ( j = 0; j < Vec_IntSize(pWL->vFanout); j++ )
        {
            Abc_SclPutI( vOut, Vec_IntEntry(pWL->vFanout, j) );
            Abc_SclPutF( vOut, Vec_FltEntry(pWL->vLen, j) );
        }
    }

    // Write 'wire_load_sel' vector:
    Abc_SclPutI( vOut, Vec_PtrSize(p->vWireLoadSels) );
    Vec_PtrForEachEntry( SC_WireLoadSel *, p->vWireLoadSels, pWLS, i )
    {
        Abc_SclPutS( vOut, pWLS->name );
        Abc_SclPutI( vOut, Vec_FltSize(pWLS->vAreaFrom) );
        for ( j = 0; j < Vec_FltSize(pWLS->vAreaFrom); j++)
        {
            Abc_SclPutF( vOut, Vec_FltEntry(pWLS->vAreaFrom, j) );
            Abc_SclPutF( vOut, Vec_FltEntry(pWLS->vAreaTo, j) );
            Abc_SclPutS( vOut, Vec_PtrEntry(pWLS->vWireLoadModel, j) );
        }
    }

    // Write 'cells' vector:
    n_valid_cells = 0;
    Vec_PtrForEachEntry( SC_Cell *, p->vCells, pCell, i )
        if ( !pCell->seq && !pCell->unsupp )
            n_valid_cells++;

    Abc_SclPutI( vOut, n_valid_cells );
    Vec_PtrForEachEntry( SC_Cell *, p->vCells, pCell, i )
    {
        SC_Pin * pPin;
        if ( pCell->seq || pCell->unsupp )
            continue;

        Abc_SclPutS( vOut, pCell->name );
        Abc_SclPutF( vOut, pCell->area );
        Abc_SclPutI( vOut, pCell->drive_strength );

        // Write 'pins': (sorted at this point; first inputs, then outputs)
        Abc_SclPutI( vOut, pCell->n_inputs);
        Abc_SclPutI( vOut, pCell->n_outputs);

        Vec_PtrForEachEntryStop( SC_Pin *, pCell->vPins, pPin, j, pCell->n_inputs )
        {
            assert(pPin->dir == sc_dir_Input);
            Abc_SclPutS( vOut, pPin->name );
            Abc_SclPutF( vOut, pPin->rise_cap );
            Abc_SclPutF( vOut, pPin->fall_cap );
        }

        Vec_PtrForEachEntryStart( SC_Pin *, pCell->vPins, pPin, j, pCell->n_inputs )
        {
            SC_Timings * pRTime;
            word uWord;
            assert(pPin->dir == sc_dir_Output);

            Abc_SclPutS( vOut, pPin->name );
            Abc_SclPutF( vOut, pPin->max_out_cap );
            Abc_SclPutF( vOut, pPin->max_out_slew );

            Abc_SclPutI( vOut, Vec_WrdSize(pPin->vFunc) );
            Vec_WrdForEachEntry( pPin->vFunc, uWord, k ) // -- 'size = 1u << (n_vars - 6)'
                Abc_SclPutW( vOut, uWord );  // -- 64-bit number, written uncompressed (low-byte first)

            // Write 'rtiming': (pin-to-pin timing tables for this particular output)
            assert( Vec_PtrSize(pPin->vRTimings) == pCell->n_inputs );
            Vec_PtrForEachEntry( SC_Timings *, pPin->vRTimings, pRTime, k )
            {
                Abc_SclPutS( vOut, pRTime->name );
                Abc_SclPutI( vOut, Vec_PtrSize(pRTime->vTimings) );
                    // -- NOTE! After post-processing, the size of the 'rtiming[k]' vector is either
                    // 0 or 1 (in static timing, we have merged all tables to get the worst case).
                    // The case with size 0 should only occur for multi-output gates.
                if ( Vec_PtrSize(pRTime->vTimings) == 1 )
                {
                    SC_Timing * pTime = (SC_Timing *)Vec_PtrEntry( pRTime->vTimings, 0 );
                        // -- NOTE! We don't need to save 'related_pin' string because we have sorted 
                        // the elements on input pins.
                    Abc_SclPutI( vOut, (int)pTime->tsense);
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
void Abc_SclWrite( char * pFileName, SC_Lib * p )
{
    Vec_Str_t * vOut;
    vOut = Vec_StrAlloc( 10000 );
    Abc_SclWriteLibrary( vOut, p );
    if ( Vec_StrSize(vOut) > 0 )
    {
        FILE * pFile = fopen( pFileName, "wb" );
        if ( pFile != NULL )
        {
            fwrite( Vec_StrArray(vOut), Vec_StrSize(vOut), 1, pFile );
            fclose( pFile );
        }
    }
    Vec_StrFree( vOut );    
}
void Abc_SclSave( char * pFileName, void * pScl )
{
    if ( pScl == NULL ) return;
    Abc_SclWrite( pFileName, (SC_Lib *)pScl );
}


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

    for ( i = Abc_SclGetI(vOut, pPos); i != 0; i-- )
        Vec_FltPush( p->vIndex0, Abc_SclGetF(vOut, pPos) );

    for ( i = Abc_SclGetI(vOut, pPos); i != 0; i-- )
        Vec_FltPush( p->vIndex1, Abc_SclGetF(vOut, pPos) );

    for ( i = 0; i < Vec_FltSize(p->vIndex0); i++ )
    {
        vVec = Vec_FltAlloc( Vec_FltSize(p->vIndex1) );
        Vec_PtrPush( p->vData, vVec );
        for ( j = 0; j < Vec_FltSize(p->vIndex0); j++ )
            Vec_FltPush( vVec, Abc_SclGetF(vOut, pPos) );
    }

    for ( i = 0; i < 3; i++ ) 
        Abc_SclGetF( vOut, pPos );
    for ( i = 0; i < 4; i++ ) 
        Abc_SclGetF( vOut, pPos );
    for ( i = 0; i < 6; i++ ) 
        Abc_SclGetF( vOut, pPos );
}
static void Abc_SclReadLibrary( Vec_Str_t * vOut, int * pPos, SC_Lib * p )
{
    int i, j, k, n;
    int version = Abc_SclGetI( vOut, pPos );
    assert( version == ABC_SCL_CUR_VERSION );

    // Read non-composite fields:
    p->lib_name              = Abc_SclGetS(vOut, pPos);
    p->default_wire_load     = Abc_SclGetS(vOut, pPos);
    p->default_wire_load_sel = Abc_SclGetS(vOut, pPos);
    p->default_max_out_slew  = Abc_SclGetF(vOut, pPos);

    p->unit_time      = Abc_SclGetI(vOut, pPos);
    p->unit_cap_float = Abc_SclGetF(vOut, pPos);
    p->unit_cap_int   = Abc_SclGetI(vOut, pPos);

    // Read 'wire_load' vector:
    for ( i = Abc_SclGetI(vOut, pPos); i != 0; i-- )
    {
        SC_WireLoad * pWL = Abc_SclWireLoadAlloc();
        Vec_PtrPush( p->vWireLoads, pWL );

        pWL->name = Abc_SclGetS(vOut, pPos);
        pWL->res  = Abc_SclGetF(vOut, pPos);
        pWL->cap  = Abc_SclGetF(vOut, pPos);

        for ( j = Abc_SclGetI(vOut, pPos); j != 0; j-- )
        {
            Vec_IntPush( pWL->vFanout, Abc_SclGetI(vOut, pPos) );
            Vec_FltPush( pWL->vLen,    Abc_SclGetF(vOut, pPos) );
        }
    }

    // Read 'wire_load_sel' vector:
    for ( i = Abc_SclGetI(vOut, pPos); i != 0; i-- )
    {
        SC_WireLoadSel * pWLS = Abc_SclWireLoadSelAlloc();
        Vec_PtrPush( p->vWireLoadSels, pWLS );

        pWLS->name = Abc_SclGetS(vOut, pPos);
        for ( j = Abc_SclGetI(vOut, pPos); j != 0; j-- )
        {
            Vec_FltPush( pWLS->vAreaFrom,      Abc_SclGetF(vOut, pPos) );
            Vec_FltPush( pWLS->vAreaTo,        Abc_SclGetF(vOut, pPos) );
            Vec_PtrPush( pWLS->vWireLoadModel, Abc_SclGetS(vOut, pPos) );
        }
    }

    for ( i = Abc_SclGetI(vOut, pPos); i != 0; i-- )
    {
        SC_Cell * pCell = Abc_SclCellAlloc();
        Vec_PtrPush( p->vCells, pCell );

        pCell->name = Abc_SclGetS(vOut, pPos);     
        pCell->area = Abc_SclGetF(vOut, pPos);
        pCell->drive_strength = Abc_SclGetI(vOut, pPos);

        pCell->n_inputs  = Abc_SclGetI(vOut, pPos);
        pCell->n_outputs = Abc_SclGetI(vOut, pPos);

        for ( j = 0; j < pCell->n_inputs; j++ )
        {
            SC_Pin * pPin = Abc_SclPinAlloc();
            Vec_PtrPush( pCell->vPins, pPin );

            pPin->dir = sc_dir_Input;

            pPin->name     = Abc_SclGetS(vOut, pPos); 
            pPin->rise_cap = Abc_SclGetF(vOut, pPos);
            pPin->fall_cap = Abc_SclGetF(vOut, pPos);
        }

        for ( j = 0; j < pCell->n_outputs; j++ )
        {
            SC_Pin * pPin = Abc_SclPinAlloc();
            Vec_PtrPush( pCell->vPins, pPin );

            pPin->dir = sc_dir_Output;

            pPin->name         = Abc_SclGetS(vOut, pPos); 
            pPin->max_out_cap  = Abc_SclGetF(vOut, pPos);
            pPin->max_out_slew = Abc_SclGetF(vOut, pPos);

            Vec_WrdGrow( pPin->vFunc, Abc_SclGetI(vOut, pPos) );
            for ( k = 0; k < Vec_WrdSize(pPin->vFunc); k++ )
                Vec_WrdPush( pPin->vFunc, Abc_SclGetW(vOut, pPos) );

            // Read 'rtiming': (pin-to-pin timing tables for this particular output)
            for ( k = 0; k < pCell->n_inputs; k++ )
            {
                SC_Timings * pRTime = Abc_SclTimingsAlloc();
                Vec_PtrPush( pPin->vRTimings, pRTime );

                pRTime->name = Abc_SclGetS(vOut, pPos); 

                n = Abc_SclGetI(vOut, pPos); assert(n <= 1);
                if ( n == 1 )
                {
                    SC_Timing * pTime = Abc_SclTimingAlloc();
                    Vec_PtrPush( pRTime->vTimings, pTime );

                    pTime->tsense = (SC_TSense)Abc_SclGetI(vOut, pPos);
                    Abc_SclReadSurface( vOut, pPos, pTime->pCellRise );
                    Abc_SclReadSurface( vOut, pPos, pTime->pCellFall );
                    Abc_SclReadSurface( vOut, pPos, pTime->pRiseTrans );
                    Abc_SclReadSurface( vOut, pPos, pTime->pFallTrans );
                }
                else
                    assert( Vec_PtrSize(pPin->vRTimings) == 0 );
            }
        }
    }
}
SC_Lib * Abc_SclRead( char * pFileName )
{
    SC_Lib * p;
    FILE * pFile;
    Vec_Str_t * vOut;
    int nFileSize, Pos = 0;

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
    nFileSize = fread( Vec_StrArray(vOut), Vec_StrSize(vOut), 1, pFile );
    assert( nFileSize == Vec_StrSize(vOut) );
    fclose( pFile );
    // read the library
    p = Abc_SclLibAlloc();
    Abc_SclReadLibrary( vOut, &Pos, p );
    assert( Pos == Vec_StrSize(vOut) );
    Vec_StrFree( vOut );
    return p;
}
void Abc_SclLoad( char * pFileName, void ** ppScl )
{
    if ( *ppScl )
    {
        Abc_SclLibFree( *(SC_Lib **)ppScl );
        ppScl = NULL;
    }
    assert( *ppScl == NULL );
    if ( pFileName )
        *(SC_Lib **)ppScl = Abc_SclRead( pFileName );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

