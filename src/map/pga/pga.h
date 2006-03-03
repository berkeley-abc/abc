/**CFile****************************************************************

  FileName    [pga.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapper.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pga.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __PGA_H__
#define __PGA_H__

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

typedef struct Pga_ManStruct_t_      Pga_Man_t;
typedef struct Pga_ParamsStruct_t_   Pga_Params_t;

struct Pga_ParamsStruct_t_
{
    // data for mapping
    Abc_Ntk_t *        pNtk;          // the network to be mapped
    Fpga_LutLib_t *    pLutLib;       // the LUT library
    float *            pSwitching;    // switching activity for each node
    // mapping parameters
    int                fDropCuts;     // enables cut dropping
    int                fAreaFlow;     // enables area flow minimization
    int                fArea;         // enables area minimization
    int                fSwitching;    // enables switching activity minimization
    int                fVerbose;      // enables verbose output
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== pgaApi.c ==========================================================*/
extern Vec_Ptr_t *   Pga_DoMapping( Pga_Man_t * p );
/*=== pgaMan.c ==========================================================*/
extern Pga_Man_t *   Pga_ManStart( Pga_Params_t * pParams );
extern void          Pga_ManStop( Pga_Man_t * p );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

