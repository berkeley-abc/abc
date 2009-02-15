/**CFile****************************************************************

  FileName    [amap.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Technology mapper for standard cells.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: amap.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __AMAP_H__
#define __AMAP_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////


typedef struct Amap_Par_t_ Amap_Par_t;
struct Amap_Par_t_
{
    int    nIterFlow;   // iterations of area flow
    int    nIterArea;   // iteratoins of exact area
    int    fUseMuxes;   // enables the use of MUXes
    int    fUseXors;    // enables the use of XORs
    int    fFreeInvs;   // assume inverters are ABC_FREE (area = 0)
    float  fEpsilon;    // used to compare floating point numbers
    int    fVerbose;    // verbosity flag
};

typedef struct Amap_Out_t_ Amap_Out_t;
struct Amap_Out_t_
{
    char * pName;     // gate name
    short  Type;      // node type   (-1=input; 0=internal; 1=output)
    short  nFans;     // number of fanins
    int    pFans[0];  // fanin
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== amapCore.c ==========================================================*/
extern void        Amap_ManSetDefaultParams( Amap_Par_t * pPars );
//extern Vec_Ptr_t * Amap_ManTest( Aig_Man_t * pAig, Amap_Par_t * pPars );
/*=== amapLiberty.c ==========================================================*/
extern int         Amap_LibertyParse( char * pFileName, char * pFileGenlib, int fVerbose );


#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

