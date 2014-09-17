/**CFile****************************************************************

  FileName    [wlc.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlc.h,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__wlc__wlc_h
#define ABC__base__wlc__wlc_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig/gia/gia.h"
#include "misc/extra/extra.h"
#include "misc/util/utilNam.h"
#include "misc/mem/mem.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START 

// object types
typedef enum { 
    WLC_OBJ_NONE = 0,      // 00: unknown
    WLC_OBJ_PI,            // 01: primary input terminal
    WLC_OBJ_PO,            // 02: primary output terminal
    WLC_OBJ_BO,            // 03: box output
    WLC_OBJ_BI,            // 04: box input
    WLC_OBJ_FF,            // 05: flop
    WLC_OBJ_CONST,         // 06: constant
    WLC_OBJ_BUF,           // 07: buffer
    WLC_OBJ_MUX,           // 08: multiplexer
    WLC_OBJ_SHIFT_R,       // 09: shift right
    WLC_OBJ_SHIFT_RA,      // 10: shift right (arithmetic)
    WLC_OBJ_SHIFT_L,       // 11: shift left
    WLC_OBJ_SHIFT_LA,      // 12: shift left (arithmetic)
    WLC_OBJ_BIT_NOT,       // 13: bitwise NOT
    WLC_OBJ_BIT_AND,       // 14: bitwise AND
    WLC_OBJ_BIT_OR,        // 15: bitwise OR
    WLC_OBJ_BIT_XOR,       // 16: bitwise XOR
    WLC_OBJ_BIT_SELECT,    // 17: bit selection
    WLC_OBJ_BIT_CONCAT,    // 18: bit concatenation
    WLC_OBJ_BIT_ZEROPAD,   // 19: zero padding
    WLC_OBJ_BIT_SIGNEXT,   // 20: sign extension
    WLC_OBJ_LOGIC_NOT,     // 21: logic NOT
    WLC_OBJ_LOGIC_AND,     // 22: logic AND
    WLC_OBJ_LOGIC_OR,      // 23: logic OR
    WLC_OBJ_COMP_EQU,      // 24: compare equal
    WLC_OBJ_COMP_NOT,      // 25: compare not equal
    WLC_OBJ_COMP_LESS,     // 26: compare less
    WLC_OBJ_COMP_MORE,     // 27: compare more
    WLC_OBJ_COMP_LESSEQU,  // 28: compare less or equal
    WLC_OBJ_COMP_MOREEQU,  // 29: compare more or equal
    WLC_OBJ_REDUCT_AND,    // 30: reduction AND
    WLC_OBJ_REDUCT_OR,     // 31: reduction OR
    WLC_OBJ_REDUCT_XOR,    // 32: reduction XOR
    WLC_OBJ_ARI_ADD,       // 33: arithmetic addition
    WLC_OBJ_ARI_SUB,       // 34: arithmetic subtraction
    WLC_OBJ_ARI_MULTI,     // 35: arithmetic multiplier
    WLC_OBJ_ARI_DIVIDE,    // 36: arithmetic division
    WLC_OBJ_ARI_MODULUS,   // 37: arithmetic modulus
    WLC_OBJ_ARI_POWER,     // 38: arithmetic power
    WLC_OBJ_TABLE,         // 39: arithmetic power
    WLC_OBJ_NUMBER         // 40: unused
} Wlc_ObjType_t;


////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Wlc_Ntk_t_  Wlc_Ntk_t;
typedef struct Wlc_Obj_t_  Wlc_Obj_t;

struct Wlc_Obj_t_ // 16 bytes
{
    unsigned               Type    :  6;       // node type
    unsigned               Signed  :  1;       // signed
    unsigned               Mark    :  1;       // user mark
    unsigned               nFanins : 24;       // fanin count
    unsigned               End     : 16;       // range end
    unsigned               Beg     : 16;       // range begin
    union { int            Fanins[2];          // fanin IDs
            int *          pFanins[1]; };
};

struct Wlc_Ntk_t_ 
{
    char *                 pName;              // model name
    Vec_Int_t              vPis;               // primary inputs 
    Vec_Int_t              vPos;               // primary outputs
    Vec_Int_t              vCis;               // combinational inputs
    Vec_Int_t              vCos;               // combinational outputs
    Vec_Int_t              vFfs;               // flops
    int                    nObjs[WLC_OBJ_NUMBER]; // counter of objects of each type
    // memory for objects
    Wlc_Obj_t *            pObjs;
    int                    iObj;
    int                    nObjsAlloc;
    Mem_Flex_t *           pMemFanin;
    Mem_Flex_t *           pMemTable;
    Vec_Ptr_t *            vTables;
    // object names
    Abc_Nam_t *            pManName;           // object names
    Vec_Int_t              vNameIds;           // object name IDs
    // object attributes
    int                    nTravIds;           // counter of traversal IDs
    Vec_Int_t              vTravIds;           // trav IDs of the objects
    Vec_Int_t              vCopies;            // object first bits
};

static inline int          Wlc_NtkObjNum( Wlc_Ntk_t * p )                         { return p->iObj - 1;                                          }
static inline int          Wlc_NtkObjNumMax( Wlc_Ntk_t * p )                      { return p->iObj;                                              }
static inline int          Wlc_NtkPiNum( Wlc_Ntk_t * p )                          { return Vec_IntSize(&p->vPis);                                }
static inline int          Wlc_NtkPoNum( Wlc_Ntk_t * p )                          { return Vec_IntSize(&p->vPos);                                }
static inline int          Wlc_NtkCiNum( Wlc_Ntk_t * p )                          { return Vec_IntSize(&p->vCis);                                }
static inline int          Wlc_NtkCoNum( Wlc_Ntk_t * p )                          { return Vec_IntSize(&p->vCos);                                }
static inline int          Wlc_NtkFfNum( Wlc_Ntk_t * p )                          { return Vec_IntSize(&p->vFfs);                                }

static inline Wlc_Obj_t *  Wlc_NtkObj( Wlc_Ntk_t * p, int Id )                    { assert(Id > 0 && Id < p->nObjsAlloc); return p->pObjs + Id;  }
static inline Wlc_Obj_t *  Wlc_NtkPi( Wlc_Ntk_t * p, int i )                      { return Wlc_NtkObj( p, Vec_IntEntry(&p->vPis, i) );           }
static inline Wlc_Obj_t *  Wlc_NtkPo( Wlc_Ntk_t * p, int i )                      { return Wlc_NtkObj( p, Vec_IntEntry(&p->vPos, i) );           }
static inline Wlc_Obj_t *  Wlc_NtkCi( Wlc_Ntk_t * p, int i )                      { return Wlc_NtkObj( p, Vec_IntEntry(&p->vCis, i) );           }
static inline Wlc_Obj_t *  Wlc_NtkCo( Wlc_Ntk_t * p, int i )                      { return Wlc_NtkObj( p, Vec_IntEntry(&p->vCos, i) );           }
static inline Wlc_Obj_t *  Wlc_NtkFf( Wlc_Ntk_t * p, int i )                      { return Wlc_NtkObj( p, Vec_IntEntry(&p->vFfs, i) );           }

static inline int          Wlc_ObjId( Wlc_Ntk_t * p, Wlc_Obj_t * pObj )           { return pObj - p->pObjs;                                      }
static inline int          Wlc_ObjPioId( Wlc_Obj_t * p )                          { assert(p->Type==WLC_OBJ_PI||p->Type==WLC_OBJ_PO);return p->Fanins[1]; }
static inline int          Wlc_ObjFaninNum( Wlc_Obj_t * p )                       { return p->nFanins;                                           }
static inline int          Wlc_ObjHasArray( Wlc_Obj_t * p )                       { return p->nFanins > 2 || p->Type == WLC_OBJ_CONST;           }
static inline int *        Wlc_ObjFanins( Wlc_Obj_t * p )                         { return Wlc_ObjHasArray(p) ? p->pFanins[0] : p->Fanins;       }
static inline int          Wlc_ObjFaninId( Wlc_Obj_t * p, int i )                 { return Wlc_ObjFanins(p)[i];                                  }
static inline int          Wlc_ObjFaninId0( Wlc_Obj_t * p )                       { return Wlc_ObjFanins(p)[0];                                  }
static inline int          Wlc_ObjFaninId1( Wlc_Obj_t * p )                       { return Wlc_ObjFanins(p)[1];                                  }
static inline int          Wlc_ObjFaninId2( Wlc_Obj_t * p )                       { return Wlc_ObjFanins(p)[2];                                  }
static inline Wlc_Obj_t *  Wlc_ObjFanin( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, int i ) { return Wlc_NtkObj( p, Wlc_ObjFaninId(pObj, i) );             }
static inline Wlc_Obj_t *  Wlc_ObjFanin0( Wlc_Ntk_t * p, Wlc_Obj_t * pObj )       { return Wlc_NtkObj( p, Wlc_ObjFaninId(pObj, 0) );             }
static inline Wlc_Obj_t *  Wlc_ObjFanin1( Wlc_Ntk_t * p, Wlc_Obj_t * pObj )       { return Wlc_NtkObj( p, Wlc_ObjFaninId(pObj, 1) );             }
static inline Wlc_Obj_t *  Wlc_ObjFanin2( Wlc_Ntk_t * p, Wlc_Obj_t * pObj )       { return Wlc_NtkObj( p, Wlc_ObjFaninId(pObj, 2) );             }

static inline int          Wlc_ObjRange( Wlc_Obj_t * p )                          { return p->End - p->Beg + 1;                                  }
static inline int          Wlc_ObjRangeEnd( Wlc_Obj_t * p )                       { assert(p->Type == WLC_OBJ_BIT_SELECT); return p->Fanins[1] >> 16;     }
static inline int          Wlc_ObjRangeBeg( Wlc_Obj_t * p )                       { assert(p->Type == WLC_OBJ_BIT_SELECT); return p->Fanins[1] & 0xFFFF;  }
static inline int *        Wlc_ObjConstValue( Wlc_Obj_t * p )                     { assert(p->Type == WLC_OBJ_CONST);      return Wlc_ObjFanins(p);       }
static inline int          Wlc_ObjTableId( Wlc_Obj_t * p )                        { assert(p->Type == WLC_OBJ_TABLE);      return p->Fanins[1];           }

static inline void         Wlc_NtkCleanCopy( Wlc_Ntk_t * p )                      { Vec_IntFill( &p->vCopies, p->nObjsAlloc, 0 );                }
static inline int          Wlc_NtkHasCopy( Wlc_Ntk_t * p )                        { return Vec_IntSize( &p->vCopies ) > 0;                       }
static inline void         Wlc_ObjSetCopy( Wlc_Ntk_t * p, int iObj, int i )       { Vec_IntWriteEntry( &p->vCopies, iObj, i );                   }
static inline int          Wlc_ObjCopy( Wlc_Ntk_t * p, int iObj )                 { return Vec_IntEntry( &p->vCopies, iObj );                    }

static inline void         Wlc_NtkCleanNameId( Wlc_Ntk_t * p )                    { Vec_IntFill( &p->vNameIds, p->nObjsAlloc, 0 );               }
static inline int          Wlc_NtkHasNameId( Wlc_Ntk_t * p )                      { return Vec_IntSize( &p->vNameIds ) > 0;                      }
static inline void         Wlc_ObjSetNameId( Wlc_Ntk_t * p, int iObj, int i )     { Vec_IntWriteEntry( &p->vNameIds, iObj, i );                  }
static inline int          Wlc_ObjNameId( Wlc_Ntk_t * p, int iObj )               { return Vec_IntEntry( &p->vNameIds, iObj );                   }

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

#define Wlc_NtkForEachObj( p, pObj, i )                                             \
    for ( i = 1; (i < Wlc_NtkObjNumMax(p)) && (((pObj) = Wlc_NtkObj(p, i)), 1); i++ )
#define Wlc_NtkForEachPi( p, pPi, i )                                               \
    for ( i = 0; (i < Wlc_NtkPiNum(p)) && (((pPi) = Wlc_NtkPi(p, i)), 1); i++ )
#define Wlc_NtkForEachPo( p, pPo, i )                                               \
    for ( i = 0; (i < Wlc_NtkPoNum(p)) && (((pPo) = Wlc_NtkPo(p, i)), 1); i++ )
#define Wlc_NtkForEachCi( p, pCi, i )                                               \
    for ( i = 0; (i < Wlc_NtkCiNum(p)) && (((pCi) = Wlc_NtkCi(p, i)), 1); i++ )
#define Wlc_NtkForEachCo( p, pCo, i )                                               \
    for ( i = 0; (i < Wlc_NtkCoNum(p)) && (((pCo) = Wlc_NtkCo(p, i)), 1); i++ )

#define Wlc_ObjForEachFanin( pObj, iFanin, i )                                      \
    for ( i = 0; (i < Wlc_ObjFaninNum(pObj)) && (((iFanin) = Wlc_ObjFaninId(pObj, i)), 1); i++ )
#define Wlc_ObjForEachFaninReverse( pObj, iFanin, i )                               \
    for ( i = Wlc_ObjFaninNum(pObj) - 1; (i >= 0) && (((iFanin) = Wlc_ObjFaninId(pObj, i)), 1); i-- )


////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== wlcBlast.c ========================================================*/
extern Gia_Man_t *    Wlc_NtkBitBlast( Wlc_Ntk_t * p );
/*=== wlcNtk.c ========================================================*/
extern Wlc_Ntk_t *    Wlc_NtkAlloc( char * pName, int nObjsAlloc );
extern int            Wlc_ObjAlloc( Wlc_Ntk_t * p, int Type, int Signed, int End, int Beg );
extern char *         Wlc_ObjName( Wlc_Ntk_t * p, int iObj );
extern void           Wlc_ObjUpdateType( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, int Type );
extern void           Wlc_ObjAddFanins( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, Vec_Int_t * vFanins );
extern void           Wlc_NtkFree( Wlc_Ntk_t * p );
extern void           Wlc_NtkPrintNodes( Wlc_Ntk_t * p, int Type );
extern void           Wlc_NtkPrintStats( Wlc_Ntk_t * p, int fVerbose );
extern Wlc_Ntk_t *    Wlc_NtkDupDfs( Wlc_Ntk_t * p );
extern void           Wlc_NtkTransferNames( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p );
/*=== wlcReadWord.c ========================================================*/
extern Wlc_Ntk_t *    Wlc_ReadVer( char * pFileName );
/*=== wlcWriteWord.c ========================================================*/
extern void           Wlc_WriteVer( Wlc_Ntk_t * p, char * pFileName );


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

