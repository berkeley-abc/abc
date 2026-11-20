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

// === abcRec3.c =======================================================
// Borrowed library data remains valid until the active manager changes.
extern int Abc_RecTargetCost3( word, int, const int *, int *, Lms_CutMatch_t * );
extern int Abc_RecTargetData3( const unsigned char **, const word ** );
extern int Abc_RecTargetProfiles3( int, const int ** );
extern int Abc_RecTargetNext3( int );
extern void Abc_RecTargetRecipe3( int, Vec_Int_t * );
extern void Abc_RecTargetCache3( int );
extern int Abc_RecTargetXorReady3( void );
extern int Abc_RecTargetXorStart3( void **, int );
extern void Abc_RecTargetXorStop3( void * );
extern void Abc_RecTargetRecipeXor3( int, Vec_Int_t * );
extern int Abc_RecTargetCollect3( void *, int, int, const int *, word, const Lms_CutMatch_t * );
extern int Abc_RecTargetCount3( int );

// === lmsTarget.c =====================================================
// Optional CO arrivals use the same unit-XAG traversal as the returned depth.
extern int Lms_XorLevels( Gia_Man_t * pGia, Vec_Int_t * vCoArrs );

/**Function*************************************************************

  Synopsis    [Select ordinary AIG depth or unit AND/XOR output depth.]

***********************************************************************/
static inline int Lms_LevelNum( Gia_Man_t * pGia, int fXor )
{
    // Retain Gia_ManLevelNum's dangling-gate semantics for ordinary AIGs.
    return fXor ? Lms_XorLevelNum(pGia) : Gia_ManLevelNum(pGia);
}

ABC_NAMESPACE_HEADER_END
#endif
