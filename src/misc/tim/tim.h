/**CFile****************************************************************

  FileName    [tim.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchy/timing manager.]

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

#define TIM_ETERNITY 1000000000

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     SEQUENTIAL ITERATORS                         ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== timBox.c ===========================================================*/
extern void            Tim_ManCreateBox( Tim_Man_t * p, int firstIn, int nIns, int firstOut, int nOuts, int iDelayTable );
extern int             Tim_ManBoxForCi( Tim_Man_t * p, int iCo );
extern int             Tim_ManBoxForCo( Tim_Man_t * p, int iCi );
extern int             Tim_ManBoxInputFirst( Tim_Man_t * p, int iBox );
extern int             Tim_ManBoxOutputFirst( Tim_Man_t * p, int iBox );
extern int             Tim_ManBoxInputNum( Tim_Man_t * p, int iBox );
extern int             Tim_ManBoxOutputNum( Tim_Man_t * p, int iBox );
extern float *         Tim_ManBoxDelayTable( Tim_Man_t * p, int iBox );
/*=== timDump.c ===========================================================*/
extern Vec_Str_t *     Tim_ManSave( Tim_Man_t * p );
extern Tim_Man_t *     Tim_ManLoad( Vec_Str_t * p );
/*=== timMan.c ===========================================================*/
extern Tim_Man_t *     Tim_ManStart( int nCis, int nCos );
extern Tim_Man_t *     Tim_ManDup( Tim_Man_t * p, int fUnitDelay );
extern void            Tim_ManStop( Tim_Man_t * p );
extern void            Tim_ManStopP( Tim_Man_t ** p );
extern void            Tim_ManPrint( Tim_Man_t * p );
extern int             Tim_ManCiNum( Tim_Man_t * p );
extern int             Tim_ManCoNum( Tim_Man_t * p );
extern int             Tim_ManPiNum( Tim_Man_t * p );
extern int             Tim_ManPoNum( Tim_Man_t * p );
extern int             Tim_ManBoxNum( Tim_Man_t * p );
extern int             Tim_ManDelayTableNum( Tim_Man_t * p );
extern void            Tim_ManSetDelayTables( Tim_Man_t * p, Vec_Ptr_t * vDelayTables );
extern void            Tim_ManTravIdDisable( Tim_Man_t * p );
extern void            Tim_ManTravIdEnable( Tim_Man_t * p );
/*=== timTime.c ===========================================================*/
extern void            Tim_ManInitPiArrival( Tim_Man_t * p, int iPi, float Delay );
extern void            Tim_ManInitPoRequired( Tim_Man_t * p, int iPo, float Delay );
extern void            Tim_ManInitPiArrivalAll( Tim_Man_t * p, float Delay );
extern void            Tim_ManInitPoRequiredAll( Tim_Man_t * p, float Delay );
extern void            Tim_ManSetCoArrival( Tim_Man_t * p, int iCo, float Delay );
extern void            Tim_ManSetCiRequired( Tim_Man_t * p, int iCi, float Delay );
extern void            Tim_ManSetCoRequired( Tim_Man_t * p, int iCo, float Delay );
extern float           Tim_ManGetCiArrival( Tim_Man_t * p, int iCi );
extern float           Tim_ManGetCoRequired( Tim_Man_t * p, int iCo );
/*=== timTrav.c ===========================================================*/
extern void            Tim_ManIncrementTravId( Tim_Man_t * p );
extern void            Tim_ManSetCurrentTravIdBoxInputs( Tim_Man_t * p, int iBox );
extern void            Tim_ManSetCurrentTravIdBoxOutputs( Tim_Man_t * p, int iBox );
extern void            Tim_ManSetPreviousTravIdBoxInputs( Tim_Man_t * p, int iBox );
extern void            Tim_ManSetPreviousTravIdBoxOutputs( Tim_Man_t * p, int iBox );
extern int             Tim_ManIsCiTravIdCurrent( Tim_Man_t * p, int iCi );
extern int             Tim_ManIsCoTravIdCurrent( Tim_Man_t * p, int iCo );


ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

