/**CFile****************************************************************

  FileName    [tim.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [A timing manager.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: tim.h,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __TIM_H__
#define __TIM_H__

#ifdef __cplusplus
extern "C" {
#endif 

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Tim_Man_t_           Tim_Man_t;

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define TIME_ETERNITY 10000

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     SEQUENTIAL ITERATORS                         ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== time.c ===========================================================*/
extern Tim_Man_t *     Tim_ManStart( int nPis, int nPos );
extern Tim_Man_t *     Tim_ManDup( Tim_Man_t * p, int fDiscrete );
extern Tim_Man_t *     Tim_ManDupUnit( Tim_Man_t * p );
extern Tim_Man_t *     Tim_ManDupApprox( Tim_Man_t * p );
extern void            Tim_ManStop( Tim_Man_t * p );
extern void            Tim_ManPrint( Tim_Man_t * p );
extern void            Tim_ManTravIdDisable( Tim_Man_t * p );
extern void            Tim_ManTravIdEnable( Tim_Man_t * p );
extern void            Tim_ManSetCurrentTravIdBoxInputs( Tim_Man_t * p, int iBox );
extern void            Tim_ManSetCurrentTravIdBoxOutputs( Tim_Man_t * p, int iBox );
extern void            Tim_ManSetDelayTables( Tim_Man_t * p, Vec_Ptr_t * vDelayTables );
extern void            Tim_ManCreateBox( Tim_Man_t * p, int * pIns, int nIns, int * pOuts, int nOuts, float * pDelayTable );
extern void            Tim_ManCreateBoxFirst( Tim_Man_t * p, int firstIn, int nIns, int firstOut, int nOuts, float * pDelayTable );
extern void            Tim_ManIncrementTravId( Tim_Man_t * p );
extern void            Tim_ManInitPiArrival( Tim_Man_t * p, int iPi, float Delay );
extern void            Tim_ManInitPoRequired( Tim_Man_t * p, int iPo, float Delay );
extern void            Tim_ManSetPoArrival( Tim_Man_t * p, int iPo, float Delay );
extern void            Tim_ManSetPiRequired( Tim_Man_t * p, int iPi, float Delay );
extern void            Tim_ManSetPoRequired( Tim_Man_t * p, int iPo, float Delay );
extern void            Tim_ManSetPoRequiredAll( Tim_Man_t * p, float Delay );
extern float           Tim_ManGetPiArrival( Tim_Man_t * p, int iPi );
extern float           Tim_ManGetPoRequired( Tim_Man_t * p, int iPo );
extern int             Tim_ManBoxForCi( Tim_Man_t * p, int iCo );
extern int             Tim_ManBoxForCo( Tim_Man_t * p, int iCi );
extern int             Tim_ManBoxInputFirst( Tim_Man_t * p, int iBox );
extern int             Tim_ManBoxOutputFirst( Tim_Man_t * p, int iBox );
extern int             Tim_ManBoxInputNum( Tim_Man_t * p, int iBox );
extern int             Tim_ManBoxOutputNum( Tim_Man_t * p, int iBox );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

