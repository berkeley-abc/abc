/**CFile****************************************************************

  FileName    [acec.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [CEC for arithmetic circuits.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: acec.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__proof__acec__acec_h
#define ABC__proof__acec__acec_h


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

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== acecCore.c ========================================================*/
extern int           Gia_PolynCec( Gia_Man_t * pGia0, Gia_Man_t * pGia1, Cec_ParCec_t * pPars );
/*=== acecFadds.c ========================================================*/
extern Vec_Int_t *   Gia_ManDetectFullAdders( Gia_Man_t * p, int fVerbose );
extern Vec_Int_t *   Gia_ManDetectHalfAdders( Gia_Man_t * p, int fVerbose );
/*=== acecOrder.c ========================================================*/
extern Vec_Int_t *   Gia_PolynReorder( Gia_Man_t * pGia, int fVerbose, int fVeryVerbose );
extern Vec_Int_t *   Gia_PolynFindOrder( Gia_Man_t * pGia, Vec_Int_t * vFadds, Vec_Int_t * vHadds, int fVerbose, int fVeryVerbose );
/*=== acecPolyn.c ========================================================*/
extern void          Gia_PolynBuild( Gia_Man_t * pGia, Vec_Int_t * vOrder, int fSigned, int fVerbose, int fVeryVerbose );


ABC_NAMESPACE_HEADER_END


#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

