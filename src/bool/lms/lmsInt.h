/**HFile****************************************************************

  FileName    [lmsInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 4, 2026.]

  Revision    [$Id: lmsInt.h,v 1.00 2026/10/04 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__bool__lms__lmsInt_h
#define ABC__bool__lms__lmsInt_h

#include "lms.h"
#include "misc/vec/vec.h"
#include "lmsXor.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

#define LMS_SAMPLE_LIMIT (1 << 20)
typedef struct Lms_Sample_t_ {
    word Truth;
    int nVars, Times[6], Line;
} Lms_Sample_t;
struct Lms_Collect_t_ {
    Lms_Sample_t * pTable;
    int nSlots, nSamples, fOverflow;
};

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

// === lmsCollect.c ====================================================
extern Lms_Sample_t *  Lms_SamplesSorted( Lms_Collect_t * p );
extern Lms_Collect_t * Lms_SamplesRead( const char * pName, FILE * pError );

// === lmsKernel.c =====================================================
extern void * Lms_KernelStart( void );
extern void * Lms_KernelStartXor( void );
extern int    Lms_KernelIsXor( void * pData );
extern int    Lms_KernelSynth( void * pData, unsigned Truth, int * pTimes, Vec_Int_t * vAig, int * pDepths );
extern int    Lms_KernelSample( void * pData, unsigned Truth, int * pTimes, Vec_Int_t * vAig, int * pDepths );
extern int    Lms_KernelFrontier( void * pData, unsigned Truth, int * pTimes, Vec_Int_t * vAig, int * pDepths );
extern int    Lms_KernelProfile( void * pData, unsigned Truth, int Index, Vec_Int_t * vAig, int * pDepths );
extern void   Lms_KernelStop( void * pData );

ABC_NAMESPACE_HEADER_END
#endif
