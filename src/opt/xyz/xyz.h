/**CFile****************************************************************

  FileName    [xyz.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cover manipulation package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: xyz.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "xyzInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Xyz_Man_t_  Xyz_Man_t;
typedef struct Xyz_Obj_t_  Xyz_Obj_t;

// storage for node information
struct Xyz_Obj_t_
{
    Min_Cube_t *      pCover[3];    // pos/neg/esop
    Vec_Int_t *       vSupp;        // computed support (all nodes except CIs)
};

// storage for additional information
struct Xyz_Man_t_
{
    // general characteristics
    int               nFaninMax;    // the number of vars
    int               nCubesMax;    // the limit on the number of cubes in the intermediate covers
    int               nWords;       // the number of words
    Vec_Int_t *       vFanCounts;   // fanout counts
    Vec_Ptr_t *       vObjStrs;     // object structures
    void *            pMemory;      // memory for the internal data strctures
    Min_Man_t *       pManMin;      // the cub manager
    int               fUseEsop;     // enables ESOPs
    int               fUseSop;      // enables SOPs
    // arrays to map local variables
    Vec_Int_t *       vComTo0;      // mapping of common variables into first fanin
    Vec_Int_t *       vComTo1;      // mapping of common variables into second fanin
    Vec_Int_t *       vPairs0;      // the first var in each pair of common vars
    Vec_Int_t *       vPairs1;      // the second var in each pair of common vars
    Vec_Int_t *       vTriv0;       // trival support of the first node
    Vec_Int_t *       vTriv1;       // trival support of the second node
    // statistics
    int               nSupps;       // supports created
    int               nSuppsMax;    // the maximum number of supports
    int               nBoundary;    // the boundary size
    int               nNodes;       // the number of nodes processed
};

static inline Xyz_Obj_t *  Abc_ObjGetStr( Abc_Obj_t * pObj )                       { return Vec_PtrEntry(((Xyz_Man_t *)pObj->pNtk->pManCut)->vObjStrs, pObj->Id); }

static inline void         Abc_ObjSetSupp( Abc_Obj_t * pObj, Vec_Int_t * vVec )    { Abc_ObjGetStr(pObj)->vSupp = vVec;   }
static inline Vec_Int_t *  Abc_ObjGetSupp( Abc_Obj_t * pObj )                      { return Abc_ObjGetStr(pObj)->vSupp;   }

static inline void         Abc_ObjSetCover2( Abc_Obj_t * pObj, Min_Cube_t * pCov ) { Abc_ObjGetStr(pObj)->pCover[2] = pCov; }
static inline Min_Cube_t * Abc_ObjGetCover2( Abc_Obj_t * pObj )                    { return Abc_ObjGetStr(pObj)->pCover[2]; }

static inline void         Abc_ObjSetCover( Abc_Obj_t * pObj, Min_Cube_t * pCov, int Pol ) { Abc_ObjGetStr(pObj)->pCover[Pol] = pCov; }
static inline Min_Cube_t * Abc_ObjGetCover( Abc_Obj_t * pObj, int Pol )                    { return Abc_ObjGetStr(pObj)->pCover[Pol]; }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== xyzBuild.c ==========================================================*/
extern Abc_Ntk_t * Abc_NtkXyzDerive( Xyz_Man_t * p, Abc_Ntk_t * pNtk );
extern Abc_Ntk_t * Abc_NtkXyzDeriveClean( Xyz_Man_t * p, Abc_Ntk_t * pNtk );
/*=== xyzCore.c ===========================================================*/
extern Abc_Ntk_t * Abc_NtkXyz( Abc_Ntk_t * pNtk, int nFaninMax, bool fUseEsop, bool fUseSop, bool fUseInvs, bool fVerbose );
/*=== xyzMan.c ============================================================*/
extern Xyz_Man_t * Xyz_ManAlloc( Abc_Ntk_t * pNtk, int nFaninMax );
extern void        Xyz_ManFree( Xyz_Man_t * p );
extern void        Abc_NodeXyzDropData( Xyz_Man_t * p, Abc_Obj_t * pObj );
/*=== xyzTest.c ===========================================================*/
extern Abc_Ntk_t * Abc_NtkXyzTestSop( Abc_Ntk_t * pNtk );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


