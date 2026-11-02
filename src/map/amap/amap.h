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
 
#ifndef ABC__map__amap__amap_h
#define ABC__map__amap__amap_h


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

typedef struct Amap_Lib_t_ Amap_Lib_t;

// object types
typedef enum {
    AMAP_OBJ_NONE,    // 0: non-existent object
    AMAP_OBJ_CONST1,  // 1: constant 1
    AMAP_OBJ_PI,      // 2: primary input
    AMAP_OBJ_PO,      // 3: primary output
    AMAP_OBJ_AND,     // 4: AND node
    AMAP_OBJ_XOR,     // 5: XOR node
    AMAP_OBJ_MUX,     // 6: MUX node
    AMAP_OBJ_VOID     // 7: unused object
} Amap_Type_t;

typedef struct Amap_Nod_t_ Amap_Nod_t;
typedef struct Amap_Set_t_ Amap_Set_t;
struct Amap_Nod_t_
{
    unsigned           Id       : 16;   // ID of the node
    unsigned           nSuppSize:  8;   // support size
    unsigned           Type     :  8;   // the type of node
    short              iFan0;           // fanin0
    short              iFan1;           // fanin1
    short              iFan2;           // fanin2
    short              Unused;
    Amap_Set_t *       pSets;           // implementable gates
};

// Borrowed pattern data. Treat all arrays as read-only; the library owns them.
// The view remains valid until the library is rebuilt or freed.
typedef struct Amap_PatView_t_ Amap_PatView_t;
struct Amap_PatView_t_
{
    int                nNodes;
    const Amap_Nod_t *  pNodes;
    int * const *      pRules;
    int * const *      pRulesX;
    Vec_Int_t *        vRules3;
};

typedef struct Amap_Par_t_ Amap_Par_t;
struct Amap_Par_t_
{
    int    nIterFlow;   // iterations of area flow
    int    nIterArea;   // iteratoins of exact area
    int    nCutsMax;    // the maximum number of cuts at a node
    int    fUseMuxes;   // enables the use of MUXes
    int    fUseXors;    // enables the use of XORs
    int    fFreeInvs;   // assume inverters are free (area = 0)
    float  fEpsilon;    // used to compare floating point numbers
    float  fADratio;    // ratio of area/delay improvement
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
extern void          Amap_ManSetDefaultParams( Amap_Par_t * pPars );
//extern Vec_Ptr_t * Amap_ManTest( Aig_Man_t * pAig, Amap_Par_t * pPars );
/*=== amapLib.c ==========================================================*/
extern void          Amap_LibFree( Amap_Lib_t * p );
extern void          Amap_LibReadPatterns( Amap_Lib_t * p, Amap_PatView_t * pView );
extern void          Amap_LibPrintSelectedGates( Amap_Lib_t * p, int fAllGates );
extern Amap_Lib_t *  Amap_LibReadAndPrepare( char * pFileName, char * pBuffer, int fVerbose, int fVeryVerbose );
/*=== amapLiberty.c ==========================================================*/
extern int           Amap_LibertyParse( char * pFileName, int fVerbose );
extern Vec_Str_t *   Amap_LibertyParseStr( char * pFileName, int fVerbose );



ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

