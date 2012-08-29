/**CFile****************************************************************

  FileName    [sclInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Simplified library representation for STA.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclInt.h,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__map__scl__sclInt_h
#define ABC__map__scl__sclInt_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <math.h>

#include "base/abc/abc.h"

ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

#define ABC_SCL_CUR_VERSION 5

typedef enum  
{
    sc_dir_NULL,
    sc_dir_Input,
    sc_dir_Output,
    sc_dir_InOut,
    sc_dir_Internal,
} SC_Dir;

typedef enum      // -- timing sense, positive-, negative- or non-unate
{
    sc_ts_NULL,
    sc_ts_Pos,
    sc_ts_Neg,
    sc_ts_Non,
} SC_TSense;

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

typedef struct SC_WireLoad_    SC_WireLoad;
typedef struct SC_WireLoadSel_ SC_WireLoadSel;
typedef struct SC_TableTempl_  SC_TableTempl;
typedef struct SC_Surface_     SC_Surface;
typedef struct SC_Timing_      SC_Timing;
typedef struct SC_Timings_     SC_Timings;
typedef struct SC_Pin_         SC_Pin;
typedef struct SC_Cell_        SC_Cell;
typedef struct SC_Lib_         SC_Lib;

struct SC_WireLoad_ 
{
    char *         pName;
    float          res;            // (currently not used)
    float          cap;            // }- multiply estimation in 'fanout_len[].snd' with this value
    Vec_Int_t *    vFanout;        // Vec<Pair<uint,float> > -- pairs '(#fanouts, est-wire-len)'
    Vec_Flt_t *    vLen;
};

struct SC_WireLoadSel_
{
    char *         pName;
    Vec_Flt_t *    vAreaFrom;      // Vec<Trip<float,float,Str> > -- triplets '(from-area, upto-area, wire-load-model)'; range is [from, upto[
    Vec_Flt_t *    vAreaTo;
    Vec_Ptr_t *    vWireLoadModel;
};

struct SC_TableTempl_ 
{
    char *         pName;
    Vec_Ptr_t *    vVars;          // Vec<Str>         -- name of variable (numbered from 0, not 1 as in the Liberty file) 
    Vec_Ptr_t *    vIndex;         // Vec<Vec<float> > -- this is the point of measurement in table for the given variable 
};

struct SC_Surface_ 
{
    char *         pName;
    Vec_Flt_t *    vIndex0;        // Vec<float>       -- correspondes to "index_1" in the liberty file (for timing: slew)
    Vec_Flt_t *    vIndex1;        // Vec<float>       -- correspondes to "index_2" in the liberty file (for timing: load)
    Vec_Ptr_t *    vData;          // Vec<Vec<float> > -- 'data[i0][i1]' gives value at '(index0[i0], index1[i1])' 
    float          approx[3][6];
};

struct SC_Timing_ 
{
    char *         related_pin;    // -- related pin
    SC_TSense      tsense;         // -- timing sense (positive_unate, negative_unate, non_unate)
    char *         when_text;      // -- logic condition on inputs triggering this delay model for the output (currently not used)
    SC_Surface *   pCellRise;      // -- Used to compute pin-to-pin delay
    SC_Surface *   pCellFall;
    SC_Surface *   pRiseTrans;     // -- Used to compute output slew
    SC_Surface *   pFallTrans;
};

struct SC_Timings_ 
{
    char *         pName;          // -- the 'related_pin' field
    Vec_Ptr_t *    vTimings;       // structures of type SC_Timing
};

struct SC_Pin_ 
{
    char *         pName;
    SC_Dir         dir;
    float          cap;            // -- this value is used if 'rise_cap' and 'fall_cap' is missing (copied by 'postProcess()'). (not used)
    float          rise_cap;       // }- used for input pins ('cap' too).
    float          fall_cap;       // }
    float          max_out_cap;    // } (not used)
    float          max_out_slew;   // }- used only for output pins (max values must not be exceeded or else mapping is illegal) (not used)
    char *         func_text;      // }
    Vec_Wrd_t *    vFunc;          // }
    Vec_Ptr_t *    vRTimings;      // -- for output pins
};

struct SC_Cell_ 
{
    char *         pName;
    int            seq;            // -- set to TRUE by parser if a sequential element
    int            unsupp;         // -- set to TRUE by parser if cell contains information we cannot handle
    float          area;
    int            drive_strength; // -- some library files provide this field (currently unused, but may be a good hint for sizing) (not used)
    Vec_Ptr_t *    vPins;          // NamedSet<SC_Pin> 
    int            n_inputs;       // -- 'pins[0 .. n_inputs-1]' are input pins
    int            n_outputs;      // -- 'pins[n_inputs .. n_inputs+n_outputs-1]' are output pins
    SC_Cell *      pNext;          // same-functionality cells linked into a ring by area
    SC_Cell *      pPrev;          // same-functionality cells linked into a ring by area
};

struct SC_Lib_ 
{
    char *         pName;
    char *         default_wire_load;
    char *         default_wire_load_sel;
    float          default_max_out_slew;   // -- 'default_max_transition'; this is copied to each output pin where 'max_transition' is not defined  (not used)
    int            unit_time;      // -- Valid 9..12. Unit is '10^(-val)' seconds (e.g. 9=1ns, 10=100ps, 11=10ps, 12=1ps)
    float          unit_cap_fst;   // -- First part is a multiplier, second either 12 or 15 for 'pf' or 'ff'.
    int            unit_cap_snd;
    Vec_Ptr_t *    vWireLoads;     // NamedSet<SC_WireLoad>
    Vec_Ptr_t *    vWireLoadSels;  // NamedSet<SC_WireLoadSel>
    Vec_Ptr_t *    vTempls;        // NamedSet<SC_TableTempl>  
    Vec_Ptr_t *    vCells;         // NamedSet<SC_Cell>
    Vec_Ptr_t *    vCellOrder;     // NamedSet<SC_Cell>
    int *          pBins;          // hashing gateName -> gateId
    int            nBins;
};

////////////////////////////////////////////////////////////////////////
///                       GLOBAL VARIABLES                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFINITIONS                          ///
////////////////////////////////////////////////////////////////////////

static inline SC_Cell *   SC_LibCell( SC_Lib * p, int i )          { return (SC_Cell *)Vec_PtrEntry(p->vCells, i);                 }
static inline SC_Pin  *   SC_CellPin( SC_Cell * p, int i )         { return (SC_Pin *)Vec_PtrEntry(p->vPins, i);                   }
static inline Vec_Wrd_t * SC_CellFunc( SC_Cell * p )               { return SC_CellPin(p, p->n_inputs)->vFunc;                     }

static inline double      SC_LibCapFf( SC_Lib * p, double cap )    { return cap * p->unit_cap_fst * pow(10, 15 - p->unit_cap_snd); }
static inline double      SC_LibTimePs( SC_Lib * p, double time )  { return time * pow(10, 12 - p->unit_time);                     }

#define SC_LitForEachCell( p, pCell, i )      Vec_PtrForEachEntry( SC_Cell *, p->vCells, pCell, i )
#define SC_CellForEachPin( p, pPin, i )       Vec_PtrForEachEntry( SC_Pin *, pCell->vPins, pPin, i )
#define SC_CellForEachPinIn( p, pPin, i )     Vec_PtrForEachEntryStop( SC_Pin *, pCell->vPins, pPin, i, pCell->n_inputs )
#define SC_CellForEachPinOut( p, pPin, i )    Vec_PtrForEachEntryStart( SC_Pin *, pCell->vPins, pPin, i, pCell->n_inputs )

#define SC_RingForEachCell( pRing, pCell, i ) for ( i = 0, pCell = pRing; i == 0 || pCell != pRing; pCell = pCell->pNext, i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Constructors of the library data-structures.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline SC_WireLoad * Abc_SclWireLoadAlloc()
{
    SC_WireLoad * p;
    p = ABC_CALLOC( SC_WireLoad, 1 );
    p->vFanout = Vec_IntAlloc( 0 );
    p->vLen    = Vec_FltAlloc( 0 );
    return p;
}
static inline SC_WireLoadSel * Abc_SclWireLoadSelAlloc()
{
    SC_WireLoadSel * p;
    p = ABC_CALLOC( SC_WireLoadSel, 1 );
    p->vAreaFrom      = Vec_FltAlloc( 0 );
    p->vAreaTo        = Vec_FltAlloc( 0 );
    p->vWireLoadModel = Vec_PtrAlloc( 0 );
    return p;
}
static inline SC_TableTempl * Abc_SclTableTemplAlloc()
{
    SC_TableTempl * p;
    p = ABC_CALLOC( SC_TableTempl, 1 );
    p->vVars  = Vec_PtrAlloc( 0 );
    p->vIndex = Vec_PtrAlloc( 0 );
    return p;
}
static inline SC_Surface * Abc_SclSurfaceAlloc()
{
    SC_Surface * p;
    p = ABC_CALLOC( SC_Surface, 1 );
    p->vIndex0   = Vec_FltAlloc( 0 );
    p->vIndex1   = Vec_FltAlloc( 0 );
    p->vData     = Vec_PtrAlloc( 0 );
    return p;
}
static inline SC_Timing * Abc_SclTimingAlloc()
{
    SC_Timing * p;
    p = ABC_CALLOC( SC_Timing, 1 );
    p->pCellRise  = Abc_SclSurfaceAlloc();  
    p->pCellFall  = Abc_SclSurfaceAlloc();
    p->pRiseTrans = Abc_SclSurfaceAlloc(); 
    p->pFallTrans = Abc_SclSurfaceAlloc();
    return p;
}
static inline SC_Timings * Abc_SclTimingsAlloc()
{
    SC_Timings * p;
    p = ABC_CALLOC( SC_Timings, 1 );
    p->vTimings   = Vec_PtrAlloc( 0 );
    return p;
}
static inline SC_Pin * Abc_SclPinAlloc()
{
    SC_Pin * p;
    p = ABC_CALLOC( SC_Pin, 1 );
    p->max_out_slew = -1;
    p->vFunc        = Vec_WrdAlloc( 0 );
    p->vRTimings    = Vec_PtrAlloc( 0 );
    return p;
}
static inline SC_Cell * Abc_SclCellAlloc()
{
    SC_Cell * p;
    p = ABC_CALLOC( SC_Cell, 1 );
    p->vPins = Vec_PtrAlloc( 0 );
    return p;
}
static inline SC_Lib * Abc_SclLibAlloc()
{
    SC_Lib * p;
    p = ABC_CALLOC( SC_Lib, 1 );
    p->default_max_out_slew = -1;
    p->unit_time      = 9;
    p->unit_cap_fst   = 1;
    p->unit_cap_snd   = 12;
    p->vWireLoads     = Vec_PtrAlloc( 0 );
    p->vWireLoadSels  = Vec_PtrAlloc( 0 );
    p->vTempls        = Vec_PtrAlloc( 0 );
    p->vCells         = Vec_PtrAlloc( 0 );
    p->vCellOrder     = Vec_PtrAlloc( 0 );
    return p;
}


/**Function*************************************************************

  Synopsis    [Destructors of the library data-structures.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_SclWireLoadFree( SC_WireLoad * p )
{
    Vec_IntFree( p->vFanout );
    Vec_FltFree( p->vLen );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
static inline void Abc_SclWireLoadSelFree( SC_WireLoadSel * p )
{
    Vec_FltFree( p->vAreaFrom );
    Vec_FltFree( p->vAreaTo );
    Vec_PtrFreeFree( p->vWireLoadModel );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
static inline void Abc_SclTableTemplFree( SC_TableTempl * p )
{
    Vec_PtrFreeFree( p->vVars );
    Vec_VecFree( (Vec_Vec_t *)p->vIndex );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
static inline void Abc_SclSurfaceFree( SC_Surface * p )
{
    Vec_FltFree( p->vIndex0 );
    Vec_FltFree( p->vIndex1 );
    Vec_VecFree( (Vec_Vec_t *)p->vData );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
static inline void Abc_SclTimingFree( SC_Timing * p )
{
    Abc_SclSurfaceFree( p->pCellRise );
    Abc_SclSurfaceFree( p->pCellFall );
    Abc_SclSurfaceFree( p->pRiseTrans );
    Abc_SclSurfaceFree( p->pFallTrans );
    ABC_FREE( p->related_pin );
    ABC_FREE( p->when_text );
    ABC_FREE( p );
}
static inline void Abc_SclTimingsFree( SC_Timings * p )
{
    SC_Timing * pTemp;
    int i;
    Vec_PtrForEachEntry( SC_Timing *, p->vTimings, pTemp, i )
        Abc_SclTimingFree( pTemp );
    Vec_PtrFree( p->vTimings );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
static inline void Abc_SclPinFree( SC_Pin * p )
{
    SC_Timings * pTemp;
    int i;
    Vec_PtrForEachEntry( SC_Timings *, p->vRTimings, pTemp, i )
        Abc_SclTimingsFree( pTemp );
    Vec_PtrFree( p->vRTimings );
    Vec_WrdFree( p->vFunc );
    ABC_FREE( p->func_text );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
static inline void Abc_SclCellFree( SC_Cell * p )
{
    SC_Pin * pTemp;
    int i;
    Vec_PtrForEachEntry( SC_Pin *, p->vPins, pTemp, i )
        Abc_SclPinFree( pTemp );
    Vec_PtrFree( p->vPins );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
static inline void Abc_SclLibFree( SC_Lib * p )
{
    SC_WireLoad * pWL;
    SC_WireLoadSel * pWLS;
    SC_TableTempl * pTempl;
    SC_Cell * pCell;
    int i;
    Vec_PtrForEachEntry( SC_WireLoad *, p->vWireLoads, pWL, i )
        Abc_SclWireLoadFree( pWL );
    Vec_PtrFree( p->vWireLoads );
    Vec_PtrForEachEntry( SC_WireLoadSel *, p->vWireLoadSels, pWLS, i )
        Abc_SclWireLoadSelFree( pWLS );
    Vec_PtrFree( p->vWireLoadSels );
    Vec_PtrForEachEntry( SC_TableTempl *, p->vTempls, pTempl, i )
        Abc_SclTableTemplFree( pTempl );
    Vec_PtrFree( p->vTempls );
    SC_LitForEachCell( p, pCell, i )
        Abc_SclCellFree( pCell );
    Vec_PtrFree( p->vCells );
    Vec_PtrFree( p->vCellOrder );
    ABC_FREE( p->pName );
    ABC_FREE( p->default_wire_load );
    ABC_FREE( p->default_wire_load_sel );
    ABC_FREE( p->pBins );
    ABC_FREE( p );
}


/*=== sclBuff.c =============================================================*/
extern int         Abc_SclCheckNtk( Abc_Ntk_t * p, int fVerbose );
extern Abc_Ntk_t * Abc_SclPerformBuffering( Abc_Ntk_t * p, int Degree, int fVerbose );
/*=== sclFile.c =============================================================*/
extern SC_Lib *    Abc_SclRead( char * pFileName );
extern void        Abc_SclWrite( char * pFileName, SC_Lib * p );
extern void        Abc_SclWriteText( char * pFileName, SC_Lib * p );
extern void        Abc_SclLoad( char * pFileName, SC_Lib ** ppScl );
extern void        Abc_SclSave( char * pFileName, SC_Lib * pScl );
/*=== sclTime.c =============================================================*/
extern void        Abc_SclTimePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int fShowAll );
/*=== sclSize.c =============================================================*/
extern void        Abc_SclSizingPerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int nSteps, int fVerbose );
/*=== sclUtil.c =============================================================*/
extern void        Abc_SclHashCells( SC_Lib * p );
extern int         Abc_SclCellFind( SC_Lib * p, char * pName );
extern void        Abc_SclLinkCells( SC_Lib * p );
extern void        Abc_SclPrintCells( SC_Lib * p );
extern Vec_Int_t * Abc_SclManFindGates( SC_Lib * pLib, Abc_Ntk_t * p );
extern void        Abc_SclManSetGates( SC_Lib * pLib, Abc_Ntk_t * p, Vec_Int_t * vGates );



ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
