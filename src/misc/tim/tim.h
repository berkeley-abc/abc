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

#ifndef ABC__aig__tim__tim_h
#define ABC__aig__tim__tim_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////



ABC_NAMESPACE_HEADER_START
 

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Tim_Man_t_           Tim_Man_t;

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define TIM_ETERNITY 10000

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
extern Tim_Man_t *     Tim_ManStart( int nCis, int nCos );
extern Tim_Man_t *     Tim_ManDup( Tim_Man_t * p, int fDiscrete );
extern Tim_Man_t *     Tim_ManDupUnit( Tim_Man_t * p );
extern Tim_Man_t *     Tim_ManDupApprox( Tim_Man_t * p );
extern void            Tim_ManStop( Tim_Man_t * p );
extern void            Tim_ManStopP( Tim_Man_t ** p );
extern void            Tim_ManPrint( Tim_Man_t * p );
extern void            Tim_ManTravIdDisable( Tim_Man_t * p );
extern void            Tim_ManTravIdEnable( Tim_Man_t * p );
extern void            Tim_ManSetCurrentTravIdBoxInputs( Tim_Man_t * p, int iBox );
extern void            Tim_ManSetCurrentTravIdBoxOutputs( Tim_Man_t * p, int iBox );
extern void            Tim_ManSetPreviousTravIdBoxInputs( Tim_Man_t * p, int iBox );
extern void            Tim_ManSetPreviousTravIdBoxOutputs( Tim_Man_t * p, int iBox );
extern int             Tim_ManIsCiTravIdCurrent( Tim_Man_t * p, int iCi );
extern int             Tim_ManIsCoTravIdCurrent( Tim_Man_t * p, int iCo );
extern void            Tim_ManSetDelayTables( Tim_Man_t * p, Vec_Ptr_t * vDelayTables );
extern void            Tim_ManCreateBox( Tim_Man_t * p, int * pIns, int nIns, int * pOuts, int nOuts, float * pDelayTable );
extern void            Tim_ManCreateBoxFirst( Tim_Man_t * p, int firstIn, int nIns, int firstOut, int nOuts, float * pDelayTable );
extern void            Tim_ManIncrementTravId( Tim_Man_t * p );
extern void            Tim_ManInitCiArrival( Tim_Man_t * p, int iCi, float Delay );
extern void            Tim_ManInitCoRequired( Tim_Man_t * p, int iCo, float Delay );
extern void            Tim_ManSetCoArrival( Tim_Man_t * p, int iCo, float Delay );
extern void            Tim_ManSetCiRequired( Tim_Man_t * p, int iCi, float Delay );
extern void            Tim_ManSetCoRequired( Tim_Man_t * p, int iCo, float Delay );
extern void            Tim_ManSetCiArrivalAll( Tim_Man_t * p, float Delay );
extern void            Tim_ManSetCoRequiredAll( Tim_Man_t * p, float Delay );
extern float           Tim_ManGetCiArrival( Tim_Man_t * p, int iCi );
extern float           Tim_ManGetCoRequired( Tim_Man_t * p, int iCo );
extern int             Tim_ManBoxForCi( Tim_Man_t * p, int iCo );
extern int             Tim_ManBoxForCo( Tim_Man_t * p, int iCi );
extern int             Tim_ManBoxInputFirst( Tim_Man_t * p, int iBox );
extern int             Tim_ManBoxOutputFirst( Tim_Man_t * p, int iBox );
extern int             Tim_ManBoxInputNum( Tim_Man_t * p, int iBox );
extern int             Tim_ManBoxOutputNum( Tim_Man_t * p, int iBox );
extern void            Tim_ManChangeForAdders( Tim_Man_t * p );



ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

