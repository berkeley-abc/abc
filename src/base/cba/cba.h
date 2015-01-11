/**CFile****************************************************************

  FileName    [cba.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cba.h,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__cba__cba_h
#define ABC__base__cba__cba_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig/gia/gia.h"
#include "misc/extra/extra.h"
#include "misc/util/utilNam.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "misc/vec/vecSet.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START 

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// network objects
typedef enum { 
    CBA_OBJ_NONE = 0,  // 0:  unused
    CBA_OBJ_BARBUF,    // 1:  barrier buffer
    CBA_OBJ_PI,        // 2:  input
    CBA_OBJ_PO,        // 3:  output
    CBA_OBJ_PIO,       // 4:  input
    CBA_OBJ_NODE,      // 5:  node
    CBA_OBJ_BOX,       // 6:  box
    CBA_OBJ_PIN,       // 7:  box output
    CBA_OBJ_LATCH,     // 8:  latch
    CBA_OBJ_UNKNOWN    // 9:  unknown
} Cba_ObjType_t; 

// Verilog predefined models
typedef enum { 
    CBA_NODE_NONE = 0,   // 0:  unused
    CBA_NODE_CONST,      // 1:  constant
    CBA_NODE_BUF,        // 2:  buffer
    CBA_NODE_INV,        // 3:  inverter
    CBA_NODE_AND,        // 4:  AND
    CBA_NODE_NAND,       // 5:  NAND
    CBA_NODE_OR,         // 6:  OR
    CBA_NODE_NOR,        // 7:  NOR
    CBA_NODE_XOR,        // 8:  XOR
    CBA_NODE_XNOR,       // 9  .XNOR
    CBA_NODE_MUX,        // 10: MUX
    CBA_NODE_MAJ,        // 11: MAJ
    CBA_NODE_KNOWN,      // 12: unknown
    CBA_NODE_UNKNOWN     // 13: unknown
} Cba_NodeType_t; 


// design
typedef struct Cba_Man_t_ Cba_Man_t;
struct Cba_Man_t_
{
    // design names
    char *       pName;    // design name
    char *       pSpec;    // spec file name
    Abc_Nam_t *  pNames;   // name manager
    Abc_Nam_t *  pModels;  // model name manager
    Abc_Nam_t *  pFuncs;   // functionality manager
    Cba_Man_t *  pLib;     // library
    // internal data
    Vec_Set_t    Mem;      // memory
    Vec_Ptr_t    vNtks;    // networks
    int          iRoot;    // root network
};

// network
typedef struct Cba_Ntk_t_ Cba_Ntk_t;
struct Cba_Ntk_t_
{
    char *       pName;    // name
    Cba_Man_t *  pDesign;  // design
    // interface
    Vec_Int_t    vInouts;  // inouts          (used by parser to store signals) 
    Vec_Int_t    vInputs;  // inputs          (used by parser to store signals)
    Vec_Int_t    vOutputs; // outputs         (used by parser to store signals) 
    Vec_Int_t    vWires;   // wires           (used by parser to store signals)
    // objects
    Vec_Int_t    vTypes;   // types           (used by parser to store Cba_PrsType_t)
    Vec_Int_t    vFuncs;   // functions       (used by parser to store function)
    Vec_Int_t    vInstIds; // instance names  (used by parser to store instance name as NameId)
    Vec_Int_t    vFanins;  // fanins          (used by parser to store fanin/fanout/range as NameId)      
    // attributes
    Vec_Int_t    vNameIds; // original names as NameId  
    Vec_Int_t    vRanges;  // ranges as NameId
    Vec_Int_t    vCopies;  // copy pointers
};


static inline char *        Cba_ManName( Cba_Man_t * p )                    { return p->pName;                                                                            }
static inline int           Cba_ManNtkNum( Cba_Man_t * p )                  { return Vec_PtrSize(&p->vNtks) - 1;                                                          }
static inline Cba_Ntk_t *   Cba_ManNtk( Cba_Man_t * p, int i )              { assert( i > 0 ); return (Cba_Ntk_t *)Vec_PtrEntry(&p->vNtks, i);                            }
static inline Cba_Ntk_t *   Cba_ManRoot( Cba_Man_t * p )                    { return Cba_ManNtk(p, p->iRoot);                                                             }
static inline Vec_Set_t *   Cba_ManMem( Cba_Man_t * p )                     { return &p->Mem;                                                                             }
static inline int           Cba_ManMemSave( Cba_Man_t * p, int * d, int s ) { return Vec_SetAppend(Cba_ManMem(p), d, s);                                                  }
static inline int *         Cba_ManMemRead( Cba_Man_t * p, int h )          { return (int *)Vec_SetEntry(Cba_ManMem(p), h);                                               }

static inline char *        Cba_NtkName( Cba_Ntk_t * p )                    { return p->pName;                                                                            }
static inline Cba_Man_t *   Cba_NtkMan( Cba_Ntk_t * p )                     { return p->pDesign;                                                                          }
static inline int           Cba_NtkObjNum( Cba_Ntk_t * p )                  { return Vec_IntSize(&p->vFanins);                                                            }
static inline char *        Cba_NtkStr( Cba_Ntk_t * p, int i )              { return Abc_NamStr(p->pDesign->pNames, i);                                                   }
static inline char *        Cba_NtkModelStr( Cba_Ntk_t * p, int i )         { return Abc_NamStr(p->pDesign->pModels, i);                                                  }
static inline char *        Cba_NtkFuncStr( Cba_Ntk_t * p, int i )          { return Abc_NamStr(p->pDesign->pFuncs, i);                                                   }
static inline Vec_Set_t *   Cba_NtkMem( Cba_Ntk_t * p )                     { return Cba_ManMem(p->pDesign);                                                              }
static inline int           Cba_NtkMemSave( Cba_Ntk_t * p, int * d, int s ) { return Cba_ManMemSave(p->pDesign, d, s);                                                    }
static inline int *         Cba_NtkMemRead( Cba_Ntk_t * p, int h )          { return Cba_ManMemRead(p->pDesign, h);                                                       }

static inline Cba_ObjType_t Cba_ObjType( Cba_Ntk_t * p, int i )             { return Vec_IntEntry(&p->vTypes, i);                                                         }
static inline int           Cba_ObjFuncId( Cba_Ntk_t * p, int i )           { return Vec_IntEntry(&p->vFuncs, i);                                                         }
static inline int           Cba_ObjInstId( Cba_Ntk_t * p, int i )           { return Vec_IntEntry(&p->vInstIds, i);                                                       }
static inline int *         Cba_ObjFaninArray( Cba_Ntk_t * p, int i )       { return Cba_NtkMemRead(p, Vec_IntEntry(&p->vFanins, i));                                     }
static inline int           Cba_ObjFaninNum( Cba_Ntk_t * p, int i )         { return *Cba_ObjFaninArray(p, i);                                                            }
static inline int *         Cba_ObjFanins( Cba_Ntk_t * p, int i )           { return Cba_ObjFaninArray(p, i) + 1;                                                         }
static inline Vec_Int_t *   Cba_ObjFaninVec( Cba_Ntk_t * p, int i )         { static Vec_Int_t V; V.pArray = Cba_ObjFaninArray(p, i); V.nSize = V.nCap = *V.pArray++; return &V; }
static inline Vec_Int_t *   Cba_ObjFaninVec2( Cba_Ntk_t * p, int i )        { static Vec_Int_t W; W.pArray = Cba_ObjFaninArray(p, i); W.nSize = W.nCap = *W.pArray++; return &W; }

static inline int           Cba_ObjNameId( Cba_Ntk_t * p, int i )           { return Vec_IntEntry(&p->vNameIds, i);                                                       }
static inline int           Cba_ObjRangeId( Cba_Ntk_t * p, int i )          { return Vec_IntEntry(&p->vRanges, i);                                                        }
static inline int           Cba_ObjCopyId( Cba_Ntk_t * p, int i )           { return Vec_IntEntry(&p->vCopies, i);                                                        }

static inline char *        Cba_ObjFuncStr( Cba_Ntk_t * p, int i )          { return Cba_NtkStr(p, Cba_ObjFuncId(p, i));                                                  }
static inline char *        Cba_ObjInstStr( Cba_Ntk_t * p, int i )          { return Cba_NtkStr(p, Cba_ObjInstId(p, i));                                                  }
static inline char *        Cba_ObjNameStr( Cba_Ntk_t * p, int i )          { return Cba_NtkStr(p, Cba_ObjNameId(p, i));                                                  }
static inline char *        Cba_ObjRangeStr( Cba_Ntk_t * p, int i )         { return Cba_NtkStr(p, Cba_ObjRangeId(p, i));                                                 }


////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////


#define Cba_ManForEachNtk( p, pNtk, i )                     \
    for ( i = 1; (i <= Cba_ManNtkNum(p)) && (((pNtk) = Cba_ManNtk(p, i)), 1); i++ ) 

#define Cba_NtkForEachObjType( p, Type, i )      \
    for ( i = 0; (i < Cba_NtkObjNum(p))  && (((Type) = Cba_ObjType(p, i)), 1); i++ ) 
#define Cba_NtkForEachObjTypeFuncFanins( p, Type, Func, vFanins, i )      \
    for ( i = 0; (i < Cba_NtkObjNum(p))  && (((Type) = Cba_ObjType(p, i)), 1)  && (((Func) = Cba_ObjFuncId(p, i)), 1)  && (((vFanins) = Cba_ObjFaninVec(p, i)), 1); i++ ) 


////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline Cba_Ntk_t * Cba_NtkAlloc( Cba_Man_t * p, char * pName )
{
    Cba_Ntk_t * pNtk = Vec_SetFetch( Cba_ManMem(p), sizeof(Cba_Ntk_t) );
    memset( pNtk, 0, sizeof(Cba_Ntk_t) );
    pNtk->pDesign = p;
    pNtk->pName = Vec_SetStrsav( Cba_ManMem(p), pName );
    Vec_PtrPush( &p->vNtks, pNtk );
    return pNtk;
}

static inline Cba_Man_t * Cba_ManAlloc( char * pFileName )
{
    Cba_Man_t * p;
    p = ABC_CALLOC( Cba_Man_t, 1 );
    // design names
    p->pName      = Extra_FileDesignName( pFileName );
    p->pSpec      = Abc_UtilStrsav( pFileName );
    p->pNames     = Abc_NamStart( 1000, 20 );
    p->pModels    = Abc_NamStart( 1000, 20 );
    p->pFuncs     = Abc_NamStart( 1000, 20 );
    // internal data
    Vec_SetAlloc_( &p->Mem, 20 );
    Vec_PtrPush( &p->vNtks, NULL );
    return p;
}
static inline void Cba_ManFree( Cba_Man_t * p )
{
    ABC_FREE( p->vNtks.pArray );
    Vec_SetFree_( &p->Mem );
    // design names
    Abc_NamStop( p->pNames );
    Abc_NamStop( p->pModels );
    Abc_NamStop( p->pFuncs );
    ABC_FREE( p->pName );
    ABC_FREE( p->pSpec );
    ABC_FREE( p );
}
static inline int Cba_ManMemory( Cba_Man_t * p )
{
    int nMem = sizeof(Cba_Man_t);
    nMem += Abc_NamMemUsed(p->pNames);
    nMem += Abc_NamMemUsed(p->pModels);
    nMem += Abc_NamMemUsed(p->pFuncs);
    nMem += Vec_SetMemoryAll(&p->Mem);
    nMem += (int)Vec_PtrMemory(&p->vNtks);
    return nMem;
}


/*=== cbaReadBlif.c =========================================================*/
extern Cba_Man_t * Cba_PrsReadBlif( char * pFileName );
/*=== cbaWriteBlif.c ========================================================*/
extern void        Cba_PrsWriteBlif( char * pFileName, Cba_Man_t * pDes );
/*=== cbaReadVer.c ==========================================================*/
extern Cba_Man_t * Cba_PrsReadVerilog( char * pFileName );
/*=== cbaWriteVer.c =========================================================*/
extern void        Cba_PrsWriteVerilog( char * pFileName, Cba_Man_t * pDes );



ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

