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
extern void            Tim_ManStop( Tim_Man_t * p );
extern void            Tim_ManSetDelayTables( Tim_Man_t * p, Vec_Ptr_t * vDelayTables );
extern void            Tim_ManCreateBox( Tim_Man_t * p, int * pIns, int nIns, int * pOuts, int nOuts, float * pDelayTable );
extern void            Tim_ManCreateBoxFirst( Tim_Man_t * p, int firstIn, int nIns, int firstOut, int nOuts, float * pDelayTable );
extern void            Tim_ManIncrementTravId( Tim_Man_t * p );
extern void            Tim_ManInitPiArrival( Tim_Man_t * p, int iPi, float Delay );
extern void            Tim_ManInitPoRequired( Tim_Man_t * p, int iPo, float Delay );
extern void            Tim_ManSetPoArrival( Tim_Man_t * p, int iPo, float Delay );
extern void            Tim_ManSetPiRequired( Tim_Man_t * p, int iPi, float Delay );
extern float           Tim_ManGetPiArrival( Tim_Man_t * p, int iPi );
extern float           Tim_ManGetPoRequired( Tim_Man_t * p, int iPo );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

