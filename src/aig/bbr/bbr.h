/**CFile****************************************************************

  FileName    [bbr.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [BDD-based reachability analysis.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bbr.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __BBR_H__
#define __BBR_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include "cuddInt.h"
#include "aig.h"
#include "saig.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline DdNode * Aig_ObjGlobalBdd( Aig_Obj_t * pObj )  { return pObj->pData; }

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== bbrImage.c ==========================================================*/
typedef struct Bbr_ImageTree_t_  Bbr_ImageTree_t;
extern Bbr_ImageTree_t * Bbr_bddImageStart( 
    DdManager * dd, DdNode * bCare,
    int nParts, DdNode ** pbParts,
    int nVars, DdNode ** pbVars, int fVerbose );
extern DdNode *    Bbr_bddImageCompute( Bbr_ImageTree_t * pTree, DdNode * bCare );
extern void        Bbr_bddImageTreeDelete( Bbr_ImageTree_t * pTree );
extern DdNode *    Bbr_bddImageRead( Bbr_ImageTree_t * pTree );
typedef struct Bbr_ImageTree2_t_  Bbr_ImageTree2_t;
extern Bbr_ImageTree2_t * Bbr_bddImageStart2( 
    DdManager * dd, DdNode * bCare,
    int nParts, DdNode ** pbParts,
    int nVars, DdNode ** pbVars, int fVerbose );
extern DdNode *    Bbr_bddImageCompute2( Bbr_ImageTree2_t * pTree, DdNode * bCare );
extern void        Bbr_bddImageTreeDelete2( Bbr_ImageTree2_t * pTree );
extern DdNode *    Bbr_bddImageRead2( Bbr_ImageTree2_t * pTree );
/*=== bbrNtbdd.c ==========================================================*/
extern void        Aig_ManFreeGlobalBdds( Aig_Man_t * p, DdManager * dd );
extern int         Aig_ManSizeOfGlobalBdds( Aig_Man_t * p );
extern DdManager * Aig_ManComputeGlobalBdds( Aig_Man_t * p, int nBddSizeMax, int fDropInternal, int fReorder, int fVerbose );
/*=== bbrReach.c ==========================================================*/
extern int         Aig_ManVerifyUsingBdds( Aig_Man_t * p, int nBddMax, int nIterMax, int fPartition, int fReorder, int fVerbose, int fSilent );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

