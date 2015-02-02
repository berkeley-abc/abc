/**CFile****************************************************************

  FileName    [cba.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

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
    CBA_OBJ_PI,        // 1:  input
    CBA_OBJ_PO,        // 2:  output
    CBA_OBJ_BI,        // 3:  box input
    CBA_OBJ_BO,        // 4:  box output
    CBA_OBJ_BOX,       // 5:  box

    CBA_BOX_C0,   
    CBA_BOX_C1,   
    CBA_BOX_CX,   
    CBA_BOX_CZ,   
    CBA_BOX_BUF,  
    CBA_BOX_INV,  
    CBA_BOX_AND,  
    CBA_BOX_NAND, 
    CBA_BOX_OR,   
    CBA_BOX_NOR,  
    CBA_BOX_XOR,  
    CBA_BOX_XNOR, 
    CBA_BOX_SHARP,
    CBA_BOX_MUX,  
    CBA_BOX_MAJ,  

    CBA_BOX_RAND,
    CBA_BOX_RNAND,
    CBA_BOX_ROR,
    CBA_BOX_RNOR,
    CBA_BOX_RXOR,
    CBA_BOX_RXNOR,

    CBA_BOX_SEL,
    CBA_BOX_PSEL,
    CBA_BOX_ENC,
    CBA_BOX_PENC,
    CBA_BOX_DEC,

    CBA_BOX_ADD,
    CBA_BOX_SUB,
    CBA_BOX_MUL,
    CBA_BOX_DIV,
    CBA_BOX_MOD,
    CBA_BOX_REM,
    CBA_BOX_POW,
    CBA_BOX_ABS,

    CBA_BOX_LTHAN,
    CBA_BOX_LETHAN,
    CBA_BOX_METHAN,
    CBA_BOX_MTHAN,
    CBA_BOX_EQU,
    CBA_BOX_NEQU,

    CBA_BOX_SHIL,
    CBA_BOX_SHIR,
    CBA_BOX_ROTL,
    CBA_BOX_ROTR,

    CBA_BOX_GATE,  
    CBA_BOX_LUT,  
    CBA_BOX_ASSIGN,  

    CBA_BOX_TRI,
    CBA_BOX_RAM,
    CBA_BOX_RAMR,
    CBA_BOX_RAMW,
    CBA_BOX_RAMWC,

    CBA_BOX_LATCH,
    CBA_BOX_LATCHRS,
    CBA_BOX_DFF,
    CBA_BOX_DFFRS,

    CBA_BOX_UNKNOWN   // 50
} Cba_ObjType_t; 


typedef struct Cba_Ntk_t_ Cba_Ntk_t;
typedef struct Cba_Man_t_ Cba_Man_t;

// network
struct Cba_Ntk_t_
{
    Cba_Man_t *  pDesign;  // design
    int          NameId;   // name ID
    int          iCopy;    // copy module
    int          iBoxNtk;  // instance network ID
    int          iBoxObj;  // instance object ID
    int          Count;    // object counter
    int          Mark;     // visit mark 
    // interface
    Vec_Int_t    vInputs;  // inputs 
    Vec_Int_t    vOutputs; // outputs
    // object attributes
    Vec_Str_t    vType;    // types     
    Vec_Int_t    vIndex;   // index
    Vec_Int_t    vFanin;   // fanin
    Vec_Int_t    vName;    // original NameId or InstId
    Vec_Int_t    vRange;   // range
    Vec_Int_t    vCopy;    // copy
    // other
    Vec_Int_t    vArray;
};

// design
struct Cba_Man_t_
{
    // design names
    char *       pName;    // design name
    char *       pSpec;    // spec file name
    Abc_Nam_t *  pStrs;    // string manager
    Abc_Nam_t *  pMods;    // module name manager
    // internal data
    int          iRoot;    // root network
    int          nNtks;    // number of current networks
    Cba_Ntk_t *  pNtks;    // networks
    // user data
    Vec_Int_t *  vBuf2RootNtk;
    Vec_Int_t *  vBuf2RootObj;
    Vec_Int_t *  vBuf2LeafNtk;
    Vec_Int_t *  vBuf2LeafObj;
    void *       pMioLib;
    void **      ppGraphs;
    int          ElemGates[4];
};

static inline char *         Cba_ManName( Cba_Man_t * p )                    { return p->pName;                                                                            }
static inline char *         Cba_ManSpec( Cba_Man_t * p )                    { return p->pSpec;                                                                            }
static inline int            Cba_ManNtkNum( Cba_Man_t * p )                  { return p->nNtks;                                                                            }
static inline int            Cba_ManNtkIsOk( Cba_Man_t * p, int i )          { return i >= 0 && i < Cba_ManNtkNum(p);                                                      }
static inline Cba_Ntk_t *    Cba_ManNtk( Cba_Man_t * p, int i )              { return Cba_ManNtkIsOk(p, i) ? p->pNtks + i : NULL;                                          }
static inline int            Cba_ManNtkFindId( Cba_Man_t * p, char * pName ) { return Abc_NamStrFind(p->pMods, pName) - 1;                                                 }
static inline Cba_Ntk_t *    Cba_ManNtkFind( Cba_Man_t * p, char * pName )   { return Cba_ManNtk( p, Cba_ManNtkFindId(p, pName) );                                         }
static inline Cba_Ntk_t *    Cba_ManRoot( Cba_Man_t * p )                    { return Cba_ManNtk(p, p->iRoot);                                                             }
static inline char *         Cba_ManStr( Cba_Man_t * p, int i )              { return Abc_NamStr(p->pStrs, i);                                                             }
static inline int            Cba_ManStrId( Cba_Man_t * p, char * pStr )      { return Abc_NamStrFind(p->pStrs, pStr);                                                      }

static inline int            Cba_NtkId( Cba_Ntk_t * p )                      { int i = p - p->pDesign->pNtks; assert(Cba_ManNtkIsOk(p->pDesign, i)); return i;             }
static inline Cba_Man_t *    Cba_NtkMan( Cba_Ntk_t * p )                     { return p->pDesign;                                                                          }
static inline int            Cba_NtkNameId( Cba_Ntk_t * p )                  { return p->NameId;                                                                           }
static inline char *         Cba_NtkName( Cba_Ntk_t * p )                    { return Cba_ManStr(p->pDesign, Cba_NtkNameId(p));                                            }
static inline int            Cba_NtkCopy( Cba_Ntk_t * p )                    { return p->iCopy;                                                                            }
static inline Cba_Ntk_t *    Cba_NtkCopyNtk(Cba_Man_t * pNew, Cba_Ntk_t * p) { return Cba_ManNtk(pNew, Cba_NtkCopy(p));                                                    }
static inline void           Cba_NtkSetCopy( Cba_Ntk_t * p, int i )          { assert(p->iCopy == -1); p->iCopy = i;                                                       }

static inline int            Cba_NtkObjNum( Cba_Ntk_t * p )                  { return Vec_StrSize(&p->vType);                                                              }
static inline int            Cba_NtkAllocNum( Cba_Ntk_t * p )                { return Vec_StrCap(&p->vType);                                                               }
static inline int            Cba_NtkPiNum( Cba_Ntk_t * p )                   { return Vec_IntSize(&p->vInputs);                                                            }
static inline int            Cba_NtkPoNum( Cba_Ntk_t * p )                   { return Vec_IntSize(&p->vOutputs);                                                           }
static inline int            Cba_NtkPioNum( Cba_Ntk_t * p )                  { return Cba_NtkPiNum(p) + Cba_NtkPoNum(p);                                                   }
static inline int            Cba_NtkPiNumAlloc( Cba_Ntk_t * p )              { return Vec_IntCap(&p->vInputs);                                                             }
static inline int            Cba_NtkPoNumAlloc( Cba_Ntk_t * p )              { return Vec_IntCap(&p->vOutputs);                                                            }
static inline int            Cba_NtkBiNum( Cba_Ntk_t * p )                   { return Vec_StrCountEntry(&p->vType, (char)CBA_OBJ_BI);                                      }
static inline int            Cba_NtkBoNum( Cba_Ntk_t * p )                   { return Vec_StrCountEntry(&p->vType, (char)CBA_OBJ_BO);                                      }
static inline int            Cba_NtkCiNum( Cba_Ntk_t * p )                   { return Cba_NtkPiNum(p) + Cba_NtkBoNum(p);                                                   }
static inline int            Cba_NtkCoNum( Cba_Ntk_t * p )                   { return Cba_NtkPoNum(p) + Cba_NtkBiNum(p);                                                   }
static inline int            Cba_NtkBoxNum( Cba_Ntk_t * p )                  { return Cba_NtkObjNum(p) - Vec_StrCountSmaller(&p->vType, (char)CBA_OBJ_BOX);                }
static inline int            Cba_NtkPrimNum( Cba_Ntk_t * p )                 { return Vec_StrCountLarger(&p->vType, (char)CBA_OBJ_BOX);                                    }
static inline int            Cba_NtkUserNum( Cba_Ntk_t * p )                 { return Vec_StrCountEntry(&p->vType, (char)CBA_OBJ_BOX);                                     }
 
static inline int            Cba_NtkPi( Cba_Ntk_t * p, int i )               { return Vec_IntEntry(&p->vInputs, i);                                                        }
static inline int            Cba_NtkPo( Cba_Ntk_t * p, int i )               { return Vec_IntEntry(&p->vOutputs, i);                                                       }
static inline char *         Cba_NtkStr( Cba_Ntk_t * p, int i )              { return Cba_ManStr(p->pDesign, i);                                                           }
static inline Cba_Ntk_t *    Cba_NtkHostNtk( Cba_Ntk_t * p )                 { return p->iBoxNtk >= 0 ? Cba_ManNtk(p->pDesign, p->iBoxNtk) : NULL;                         }
static inline int            Cba_NtkHostObj( Cba_Ntk_t * p )                 { return p->iBoxObj;                                                                          }
static inline void           Cba_NtkSetHost( Cba_Ntk_t * p, int n, int i )   { assert(p->iBoxNtk == -1); p->iBoxNtk = n; p->iBoxObj = i;                                   }

static inline void           Cba_NtkStartNames( Cba_Ntk_t * p )              { assert(Cba_NtkAllocNum(p)); Vec_IntFill(&p->vName,  Cba_NtkAllocNum(p),  0);                }
static inline void           Cba_NtkStartRanges( Cba_Ntk_t * p )             { assert(Cba_NtkAllocNum(p)); Vec_IntFill(&p->vRange, Cba_NtkAllocNum(p),  0);                }
static inline void           Cba_NtkStartCopies( Cba_Ntk_t * p )             { assert(Cba_NtkAllocNum(p)); Vec_IntFill(&p->vCopy,  Cba_NtkAllocNum(p), -1);                }
static inline void           Cba_NtkFreeNames( Cba_Ntk_t * p )               { Vec_IntErase(&p->vName);                                                                    }
static inline void           Cba_NtkFreeRanges( Cba_Ntk_t * p )              { Vec_IntErase(&p->vRange);                                                                   }
static inline void           Cba_NtkFreeCopies( Cba_Ntk_t * p )              { Vec_IntErase(&p->vCopy);                                                                    }
static inline int            Cba_NtkHasNames( Cba_Ntk_t * p )                { return p->vName.pArray != NULL;                                                             }
static inline int            Cba_NtkHasRanges( Cba_Ntk_t * p )               { return p->vRange.pArray != NULL;                                                            }
static inline int            Cba_NtkHasCopies( Cba_Ntk_t * p )               { return p->vCopy.pArray != NULL;                                                             }

static inline int            Cba_TypeIsBox( Cba_ObjType_t Type )             { return Type >= CBA_OBJ_BOX && Type < CBA_BOX_UNKNOWN;                                       }

static inline Cba_ObjType_t  Cba_ObjType( Cba_Ntk_t * p, int i )             { return (Cba_ObjType_t)Vec_StrEntry(&p->vType, i);                                           }
static inline int            Cba_ObjIsPi( Cba_Ntk_t * p, int i )             { return Cba_ObjType(p, i) == CBA_OBJ_PI;                                                     }
static inline int            Cba_ObjIsPo( Cba_Ntk_t * p, int i )             { return Cba_ObjType(p, i) == CBA_OBJ_PO;                                                     }
static inline int            Cba_ObjIsPio( Cba_Ntk_t * p, int i )            { return Cba_ObjIsPi(p, i) || Cba_ObjIsPo(p, i);                                              }
static inline int            Cba_ObjIsBi( Cba_Ntk_t * p, int i )             { return Cba_ObjType(p, i) == CBA_OBJ_BI;                                                     }
static inline int            Cba_ObjIsBo( Cba_Ntk_t * p, int i )             { return Cba_ObjType(p, i) == CBA_OBJ_BO;                                                     }
static inline int            Cba_ObjIsBio( Cba_Ntk_t * p, int i )            { return Cba_ObjIsBi(p, i) || Cba_ObjIsBo(p, i);                                              }
static inline int            Cba_ObjIsBox( Cba_Ntk_t * p, int i )            { return Cba_TypeIsBox(Cba_ObjType(p, i));                                                    }
static inline int            Cba_ObjIsBoxUser( Cba_Ntk_t * p, int i )        { return Cba_ObjType(p, i) == CBA_OBJ_BOX;                                                    }
static inline int            Cba_ObjIsBoxPrim( Cba_Ntk_t * p, int i )        { return Cba_ObjIsBox(p, i) && !Cba_ObjIsBoxUser(p, i);                                       }
static inline int            Cba_ObjIsGate( Cba_Ntk_t * p, int i )           { return Cba_ObjType(p, i) == CBA_BOX_GATE;                                                   }
static inline int            Cba_ObjIsCi( Cba_Ntk_t * p, int i )             { return Cba_ObjIsPi(p, i) || Cba_ObjIsBo(p, i);                                              }
static inline int            Cba_ObjIsCo( Cba_Ntk_t * p, int i )             { return Cba_ObjIsPo(p, i) || Cba_ObjIsBi(p, i);                                              }
static inline int            Cba_ObjIsCio( Cba_Ntk_t * p, int i )            { return Cba_ObjIsCi(p, i) || Cba_ObjIsCo(p, i);                                              }

static inline int            Cba_ObjIndex( Cba_Ntk_t * p, int i )            { return Vec_IntEntry(&p->vIndex, i);                                                         }
static inline int            Cba_ObjFanin( Cba_Ntk_t * p, int i )            { assert(Cba_ObjIsCo(p, i)); return Vec_IntEntry(&p->vFanin, i);                              }
static inline int            Cba_ObjFaninTwo( Cba_Ntk_t * p, int i )         { return Cba_ObjFanin(p, Cba_ObjFanin(p, i));                                                 }
static inline int            Cba_ObjName( Cba_Ntk_t * p, int i )             { return Vec_IntEntry(&p->vName, i);                                                          }
static inline int            Cba_ObjRange( Cba_Ntk_t * p, int i )            { return Vec_IntEntry(&p->vRange, i);                                                         }
static inline int            Cba_ObjCopy( Cba_Ntk_t * p, int i )             { return Vec_IntEntry(&p->vCopy, i);                                                          }
static inline char *         Cba_ObjNameStr( Cba_Ntk_t * p, int i )          { return Cba_NtkStr(p, Cba_ObjName(p, i));                                                    }
static inline char *         Cba_ObjRangeStr( Cba_Ntk_t * p, int i )         { return Cba_NtkStr(p, Cba_ObjRange(p, i));                                                   }
static inline void           Cba_ObjSetFanin( Cba_Ntk_t * p, int i, int x )  { assert(Cba_ObjFanin(p, i) == -1); Vec_IntWriteEntry( &p->vFanin, i, x );                    }
static inline void           Cba_ObjSetName( Cba_Ntk_t * p, int i, int x )   { assert(Cba_ObjName(p, i) == 0);   Vec_IntWriteEntry( &p->vName,  i, x );                    }
static inline void           Cba_ObjSetRange( Cba_Ntk_t * p, int i, int x )  { assert(Cba_ObjRange(p, i) == 0);  Vec_IntWriteEntry( &p->vRange, i, x );                    }
static inline void           Cba_ObjSetCopy( Cba_Ntk_t * p, int i, int x )   { assert(Cba_ObjCopy(p, i) == -1);  Vec_IntWriteEntry( &p->vCopy,  i, x );                    }

static inline int            Cba_BoxBiNum( Cba_Ntk_t * p, int i )            { int s = i-1; assert(Cba_ObjIsBox(p, i)); while (i < Cba_NtkObjNum(p) && Cba_ObjIsBi(p, --i)); return s - i;         }
static inline int            Cba_BoxBoNum( Cba_Ntk_t * p, int i )            { int s = i+1; assert(Cba_ObjIsBox(p, i)); while (i < Cba_NtkObjNum(p) && Cba_ObjIsBo(p, ++i)); return i - s;         }
static inline int            Cba_BoxSize( Cba_Ntk_t * p, int i )             { return 1 + Cba_BoxBiNum(p, i) + Cba_BoxBoNum(p, i);                                         }
static inline int            Cba_BoxBi( Cba_Ntk_t * p, int b, int i )        { assert(Cba_ObjIsBox(p, b)); return b - 1 - i;                                               }
static inline int            Cba_BoxBo( Cba_Ntk_t * p, int b, int i )        { assert(Cba_ObjIsBox(p, b)); return b + 1 + i;                                               }
static inline int            Cba_BoxBiBox( Cba_Ntk_t * p, int i )            { assert(Cba_ObjIsBi(p, i)); return i + 1 + Cba_ObjIndex(p, i);                               }
static inline int            Cba_BoxBoBox( Cba_Ntk_t * p, int i )            { assert(Cba_ObjIsBo(p, i)); return i - 1 - Cba_ObjIndex(p, i);                               }
static inline int            Cba_BoxFanin( Cba_Ntk_t * p, int b, int i )     { return Cba_ObjFanin(p, Cba_BoxBi(p, b, i));                                                 }

static inline int            Cba_BoxNtkId( Cba_Ntk_t * p, int i )            { assert(Cba_ObjIsBox(p, i)); return Cba_ObjIndex(p, i);                                      }
static inline void           Cba_BoxSetNtkId( Cba_Ntk_t * p, int i, int x )  { assert(Cba_ManNtkIsOk(p->pDesign, x));Vec_IntWriteEntry(&p->vIndex, i, x);                  }
static inline int            Cba_BoxBiNtkId( Cba_Ntk_t * p, int i )          { assert(Cba_ObjIsBi(p, i)); return Cba_BoxNtkId(p, Cba_BoxBiBox(p, i));                      }
static inline int            Cba_BoxBoNtkId( Cba_Ntk_t * p, int i )          { assert(Cba_ObjIsBo(p, i)); return Cba_BoxNtkId(p, Cba_BoxBoBox(p, i));                      }
static inline Cba_Ntk_t *    Cba_BoxNtk( Cba_Ntk_t * p, int i )              { return Cba_ManNtk( p->pDesign, Cba_BoxNtkId(p, i) );                                        }
static inline Cba_Ntk_t *    Cba_BoxBiNtk( Cba_Ntk_t * p, int i )            { return Cba_ManNtk( p->pDesign, Cba_BoxBiNtkId(p, i) );                                      }
static inline Cba_Ntk_t *    Cba_BoxBoNtk( Cba_Ntk_t * p, int i )            { return Cba_ManNtk( p->pDesign, Cba_BoxBoNtkId(p, i) );                                      }
static inline char *         Cba_BoxNtkName( Cba_Ntk_t * p, int i )          { return Abc_NamStr( p->pDesign->pMods, Cba_BoxNtkId(p, i) );                                 }


////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

#define Cba_ManForEachNtk( p, pNtk, i )                                   \
    for ( i = 0; (i < Cba_ManNtkNum(p)) && (((pNtk) = Cba_ManNtk(p, i)), 1); i++ ) 

#define Cba_NtkForEachPi( p, iObj, i )                                    \
    for ( i = 0; (i < Cba_NtkPiNum(p))  && (((iObj) = Vec_IntEntry(&p->vInputs, i)), 1); i++ ) 
#define Cba_NtkForEachPo( p, iObj, i )                                    \
    for ( i = 0; (i < Cba_NtkPoNum(p))  && (((iObj) = Vec_IntEntry(&p->vOutputs, i)), 1); i++ ) 

#define Cba_NtkForEachObjType( p, Type, i )                               \
    for ( i = 0; (i < Cba_NtkObjNum(p))  && (((Type) = Cba_ObjType(p, i)), 1); i++ ) 

#define Cba_NtkForEachBox( p, i )                                         \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) if ( !Cba_ObjIsBox(p, i) ) {} else
#define Cba_NtkForEachBoxUser( p, i )                                     \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) if ( !Cba_ObjIsBoxUser(p, i) ) {} else
#define Cba_NtkForEachBoxPrim( p, i )                                     \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) if ( !Cba_ObjIsBoxPrim(p, i) ) {} else

#define Cba_NtkForEachCi( p, i )                                          \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) if ( !Cba_ObjIsCi(p, i) ) {} else
#define Cba_NtkForEachCo( p, i )                                          \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) if ( !Cba_ObjIsCo(p, i) ) {} else
#define Cba_NtkForEachCio( p, i )                                         \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) if ( !Cba_ObjIsCio(p, i) ){} else

#define Cba_NtkForEachBi( p, i )                                          \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) if ( !Cba_ObjIsBi(p, i) ){} else
#define Cba_NtkForEachBo( p, i )                                          \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) if ( !Cba_ObjIsBo(p, i) ){} else
#define Cba_NtkForEachBio( p, i )                                         \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) if ( !Cba_ObjIsBio(p, i) ){} else

#define Cba_BoxForEachBi( p, iBox, iTerm, i )                             \
    for ( iTerm = iBox - 1, i = 0; iTerm >= 0 && Cba_ObjIsBi(p, iTerm); iTerm--, i++ )
#define Cba_BoxForEachBo( p, iBox, iTerm, i )                             \
    for ( iTerm = iBox + 1, i = 0; iTerm < Cba_NtkObjNum(p) && Cba_ObjIsBo(p, iTerm); iTerm++, i++ )
#define Cba_BoxForEachBiReverse( p, iBox, iTerm, i )                      \
    for ( i = Cba_BoxBiNum(p, iBox), iTerm = iBox - i--; Cba_ObjIsBi(p, iTerm); iTerm++, i-- )

#define Cba_BoxForEachFanin( p, iBox, iFanin, i )                         \
    for ( i = 0; iBox - 1 - i >= 0 && Cba_ObjIsBi(p, iBox - 1 - i) && (((iFanin) = Cba_BoxFanin(p, iBox, i)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Object APIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cba_ObjAlloc( Cba_Ntk_t * p, Cba_ObjType_t Type, int Index, int Fanin )
{
    int iObj = Cba_NtkObjNum(p);
    assert( iObj == Vec_IntSize(&p->vIndex) );
    assert( iObj == Vec_IntSize(&p->vFanin) );
    if ( Type == CBA_OBJ_PI )
    {
        assert( Index == -1 || Index == Vec_IntSize(&p->vInputs) );
        Vec_IntPush( &p->vIndex, Vec_IntSize(&p->vInputs) );
        Vec_IntPush( &p->vInputs, iObj );
    }
    else if ( Type == CBA_OBJ_PO )
    {
        assert( Index == -1 || Index == Vec_IntSize(&p->vOutputs) );
        Vec_IntPush( &p->vIndex, Vec_IntSize(&p->vOutputs) );
        Vec_IntPush( &p->vOutputs, iObj );
    }
    else
    {
        assert( Type >= CBA_OBJ_BOX || Index >= 0 );
        Vec_IntPush( &p->vIndex, Index );
    }
    Vec_StrPush( &p->vType, (char)Type );
    Vec_IntPush( &p->vFanin, Fanin );
    return iObj;
}
static inline int Cba_ObjDup( Cba_Ntk_t * pNew, Cba_Ntk_t * p, int i )
{
    int iObj = Cba_ObjAlloc( pNew, Cba_ObjType(p, i), Cba_ObjIndex(p, i), -1 );
    if ( Cba_NtkHasNames(p) && Cba_NtkHasNames(pNew) ) 
        Cba_ObjSetName( pNew, iObj, Cba_ObjName(p, i) );
    if ( Cba_NtkHasRanges(p) && Cba_NtkHasRanges(pNew) ) 
        Cba_ObjSetRange( pNew, iObj, Cba_ObjRange(p, i) );
    Cba_ObjSetCopy( p, i, iObj );
    return iObj;
}
static inline int Cba_BoxAlloc( Cba_Ntk_t * p, Cba_ObjType_t Type, int nIns, int nOuts, int iNtk )
{
    int i, iObj;
    for ( i = nIns - 1; i >= 0; i-- )
        Cba_ObjAlloc( p, CBA_OBJ_BI, i, -1 );
    iObj = Cba_ObjAlloc( p, Type, iNtk, -1 );
    for ( i = 0; i < nOuts; i++ )
        Cba_ObjAlloc( p, CBA_OBJ_BO, i, iObj );
    return iObj;
}
static inline int Cba_BoxDup( Cba_Ntk_t * pNew, Cba_Ntk_t * p, int iBox )
{
    int i, iTerm, iBoxNew;
    Cba_BoxForEachBiReverse( p, iBox, iTerm, i )
        Cba_ObjDup( pNew, p, iTerm );
    iBoxNew = Cba_ObjDup( pNew, p, iBox );
    if ( Cba_BoxNtk(p, iBox) )
        Cba_BoxSetNtkId( pNew, iBoxNew, Cba_NtkCopy(Cba_BoxNtk(p, iBox)) );
    Cba_BoxForEachBo( p, iBox, iTerm, i )
        Cba_ObjDup( pNew, p, iTerm );
    return iBoxNew;
}


/**Function*************************************************************

  Synopsis    [Network APIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cba_NtkAlloc( Cba_Ntk_t * pNew, int NameId, int nIns, int nOuts, int nObjs )
{
    int NtkId, fFound;
    assert( pNew->pDesign != NULL );
    assert( Cba_NtkPiNum(pNew) == 0 );
    assert( Cba_NtkPoNum(pNew) == 0 );
    pNew->NameId  = NameId;
    pNew->iCopy   = -1;
    pNew->iBoxNtk = -1;
    pNew->iBoxObj = -1;
    Vec_IntGrow( &pNew->vInputs,  nIns );
    Vec_IntGrow( &pNew->vOutputs, nOuts );
    Vec_StrGrow( &pNew->vType,    nObjs );
    Vec_IntGrow( &pNew->vIndex,   nObjs );
    Vec_IntGrow( &pNew->vFanin,   nObjs );
    // check if the network is unique
    NtkId = Abc_NamStrFindOrAdd( pNew->pDesign->pMods, Cba_NtkStr(pNew, NameId), &fFound );
    if ( fFound )
        printf( "Network with name %s already exists.\n", Cba_NtkStr(pNew, NameId) );
    else
        assert( NtkId == Cba_NtkId(pNew) + 1 );
}
static inline void Cba_NtkDup( Cba_Ntk_t * pNew, Cba_Ntk_t * p )
{
    int i, iObj;
    assert( pNew != p );
    Cba_NtkAlloc( pNew, Cba_NtkNameId(p), Cba_NtkPiNum(p), Cba_NtkPoNum(p), Cba_NtkObjNum(p) );
    Cba_NtkStartCopies( p );
    if ( Cba_NtkHasNames(p) )
        Cba_NtkStartNames( pNew );
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjDup( pNew, p, iObj );
    Cba_NtkForEachBox( p, iObj )
        Cba_BoxDup( pNew, p, iObj );
    Cba_NtkForEachPo( p, iObj, i )
        Cba_ObjDup( pNew, p, iObj );
    Cba_NtkForEachCo( p, iObj )
        Cba_ObjSetFanin( pNew, Cba_ObjCopy(p, iObj), Cba_ObjCopy(p, Cba_ObjFanin(p, iObj)) );
    //Cba_NtkFreeCopies( p ); // needed for host ntk
    assert( Cba_NtkObjNum(pNew) == Cba_NtkAllocNum(pNew) );
}
static inline void Cba_NtkDupUserBoxes( Cba_Ntk_t * pNew, Cba_Ntk_t * p )
{
    int i, iObj;
    assert( pNew != p );
    Cba_NtkAlloc( pNew, Cba_NtkNameId(p), Cba_NtkPiNum(p), Cba_NtkPoNum(p), Cba_NtkObjNum(p) + 3*Cba_NtkCoNum(p) );
    Cba_NtkStartCopies( p );
    if ( Cba_NtkHasNames(p) )
        Cba_NtkStartNames( pNew );
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjDup( pNew, p, iObj );
    Cba_NtkForEachPo( p, iObj, i )
        Cba_ObjDup( pNew, p, iObj );
    Cba_NtkForEachBoxUser( p, iObj )
        Cba_BoxDup( pNew, p, iObj );
    // connect feed-throughs
    Cba_NtkForEachCo( p, iObj )
        if ( Cba_ObjCopy(p, iObj) >= 0 && 
             Cba_ObjCopy(p, Cba_ObjFanin(p, iObj)) >= 0 && 
             Cba_ObjName(p, iObj) == Cba_ObjName(p, Cba_ObjFanin(p, iObj)) )
            Cba_ObjSetFanin( pNew, Cba_ObjCopy(p, iObj), Cba_ObjCopy(p, Cba_ObjFanin(p, iObj)) );
}
static inline void Cba_NtkFree( Cba_Ntk_t * p )
{
    Vec_IntErase( &p->vInputs );
    Vec_IntErase( &p->vOutputs );
    Vec_StrErase( &p->vType );
    Vec_IntErase( &p->vIndex );
    Vec_IntErase( &p->vFanin );    
    Vec_IntErase( &p->vName );    
    Vec_IntErase( &p->vRange );    
    Vec_IntErase( &p->vCopy );    
    Vec_IntErase( &p->vArray );    
}
static inline int Cba_NtkMemory( Cba_Ntk_t * p )
{
    int nMem = sizeof(Cba_Ntk_t);
    nMem += Vec_IntMemory(&p->vInputs);
    nMem += Vec_IntMemory(&p->vOutputs);
    nMem += Vec_StrMemory(&p->vType);
    nMem += Vec_IntMemory(&p->vIndex);
    nMem += Vec_IntMemory(&p->vFanin);
    nMem += Vec_IntMemory(&p->vName);
    nMem += Vec_IntMemory(&p->vRange);
    nMem += Vec_IntMemory(&p->vCopy);
    return nMem;
}
static inline void Cba_NtkPrintStats( Cba_Ntk_t * p )
{
    printf( "pi =%5d  ",   Cba_NtkPiNum(p) );
    printf( "pi =%5d  ",   Cba_NtkPoNum(p) );
    printf( "box =%6d  ",  Cba_NtkBoxNum(p) );
    printf( "clp =%7d  ",  p->Count );
    printf( "obj =%7d  ",  Cba_NtkObjNum(p) );
    printf( "%s ",         Cba_NtkName(p) );
    if ( Cba_NtkHostNtk(p) )
        printf( "-> %s",   Cba_NtkName(Cba_NtkHostNtk(p)) );
    printf( "\n" );
}


/**Function*************************************************************

  Synopsis    [Manager APIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Cba_Man_t * Cba_ManAlloc( char * pFileName, int nNtks )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_Man_t * pNew = ABC_CALLOC( Cba_Man_t, 1 );
    pNew->pName = Extra_FileDesignName( pFileName );
    pNew->pSpec = Abc_UtilStrsav( pFileName );
    pNew->pStrs = Abc_NamStart( 1000, 24 );
    pNew->pMods = Abc_NamStart( 1000, 24 );
    pNew->iRoot = 0;
    pNew->nNtks = nNtks;
    pNew->pNtks = ABC_CALLOC( Cba_Ntk_t, pNew->nNtks );
    Cba_ManForEachNtk( pNew, pNtk, i )
        pNtk->pDesign = pNew;
    return pNew;
}
static inline Cba_Man_t * Cba_ManStart( Cba_Man_t * p, int nNtks )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_Man_t * pNew = ABC_CALLOC( Cba_Man_t, 1 );
    pNew->pName = Abc_UtilStrsav( Cba_ManName(p) );
    pNew->pSpec = Abc_UtilStrsav( Cba_ManSpec(p) );
    pNew->pStrs = Abc_NamRef( p->pStrs );  
    pNew->pMods = Abc_NamStart( 1000, 24 );
    pNew->iRoot = 0;
    pNew->nNtks = nNtks;
    pNew->pNtks = ABC_CALLOC( Cba_Ntk_t, nNtks );
    Cba_ManForEachNtk( pNew, pNtk, i )
        pNtk->pDesign = pNew;
    return pNew;
}
static inline Cba_Man_t * Cba_ManDup( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_Man_t * pNew = Cba_ManStart( p, Cba_ManNtkNum(p) );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkSetCopy( pNtk, i );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDup( Cba_NtkCopyNtk(pNew, pNtk), pNtk );
    return pNew;
}
static inline Cba_Man_t * Cba_ManDupUserBoxes( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk, * pHost; int i;
    Cba_Man_t * pNew = Cba_ManStart( p, Cba_ManNtkNum(p) );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkSetCopy( pNtk, i );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDupUserBoxes( Cba_NtkCopyNtk(pNew, pNtk), pNtk );
    Cba_ManForEachNtk( p, pNtk, i )
        if ( (pHost = Cba_NtkHostNtk(pNtk)) )
            Cba_NtkSetHost( Cba_NtkCopyNtk(pNew, pNtk), Cba_NtkCopy(pHost), Cba_ObjCopy(pHost, Cba_NtkHostObj(pNtk)) );
    return pNew;
}


static inline void Cba_ManFree( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkFree( pNtk );
    Vec_IntFreeP( &p->vBuf2LeafNtk );
    Vec_IntFreeP( &p->vBuf2LeafObj );
    Vec_IntFreeP( &p->vBuf2RootNtk );
    Vec_IntFreeP( &p->vBuf2RootObj );
    Abc_NamDeref( p->pStrs );
    Abc_NamDeref( p->pMods );
    ABC_FREE( p->pName );
    ABC_FREE( p->pSpec );
    ABC_FREE( p->pNtks );
    ABC_FREE( p );
}
static inline int Cba_ManMemory( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    int nMem = sizeof(Cba_Man_t);
    if ( p->pName )
    nMem += (int)strlen(p->pName);
    if ( p->pSpec )
    nMem += (int)strlen(p->pSpec);
    nMem += Abc_NamMemUsed(p->pStrs);
    nMem += Abc_NamMemUsed(p->pMods);
    Cba_ManForEachNtk( p, pNtk, i )
        nMem += Cba_NtkMemory( pNtk );
    return nMem;
}
static inline int Cba_ManObjNum( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i, Count = 0;
    Cba_ManForEachNtk( p, pNtk, i )
        Count += Cba_NtkObjNum(pNtk);
    return Count;
}
static inline int Cba_ManNodeNum( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i, Count = 0;
    Cba_ManForEachNtk( p, pNtk, i )
        Count += Cba_NtkBoxNum( pNtk );
    return Count;
}
static inline int Cba_ManBoxNum_rec( Cba_Ntk_t * p )
{
    int iObj, Counter = 0;
    if ( p->Count >= 0 )
        return p->Count;
    Cba_NtkForEachBox( p, iObj )
        Counter += Cba_ObjIsBoxUser(p, iObj) ? Cba_ManBoxNum_rec( Cba_BoxNtk(p, iObj) ) : 1;
    return (p->Count = Counter);
}
static inline int Cba_ManBoxNum( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        pNtk->Count = -1;
    return Cba_ManBoxNum_rec( Cba_ManRoot(p) );
}
static inline void Cba_ManPrintStats( Cba_Man_t * p, int nModules, int fVerbose )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_Ntk_t * pRoot = Cba_ManRoot( p );
    printf( "%-12s : ",   Cba_ManName(p) );
    printf( "pi =%5d  ",  Cba_NtkPiNum(pRoot) );
    printf( "po =%5d  ",  Cba_NtkPoNum(pRoot) );
    printf( "mod =%6d  ", Cba_ManNtkNum(p) );
    printf( "box =%7d  ", Cba_ManNodeNum(p) );
    printf( "obj =%7d  ", Cba_ManObjNum(p) );
    printf( "mem =%6.3f MB", 1.0*Cba_ManMemory(p)/(1<<20) );
    printf( "\n" );
    Cba_ManBoxNum( p );
    Cba_ManForEachNtk( p, pNtk, i )
    {
        if ( i == nModules )
            break;
        printf( "Module %5d : ", i );
        Cba_NtkPrintStats( pNtk );
    }
}



/**Function*************************************************************

  Synopsis    [Other APIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Cba_ObjType_t Ptr_SopToType( char * pSop )
{
    if ( !strcmp(pSop, " 0\n") )         return CBA_BOX_C0;
    if ( !strcmp(pSop, " 1\n") )         return CBA_BOX_C1;
    if ( !strcmp(pSop, "1 1\n") )        return CBA_BOX_BUF;
    if ( !strcmp(pSop, "0 1\n") )        return CBA_BOX_INV;
    if ( !strcmp(pSop, "11 1\n") )       return CBA_BOX_AND;
    if ( !strcmp(pSop, "00 1\n") )       return CBA_BOX_NOR;
    if ( !strcmp(pSop, "00 0\n") )       return CBA_BOX_OR;
    if ( !strcmp(pSop, "-1 1\n1- 1\n") ) return CBA_BOX_OR;
    if ( !strcmp(pSop, "1- 1\n-1 1\n") ) return CBA_BOX_OR;
    if ( !strcmp(pSop, "01 1\n10 1\n") ) return CBA_BOX_XOR;
    if ( !strcmp(pSop, "10 1\n01 1\n") ) return CBA_BOX_XOR;
    if ( !strcmp(pSop, "11 1\n00 1\n") ) return CBA_BOX_XNOR;
    if ( !strcmp(pSop, "00 1\n11 1\n") ) return CBA_BOX_XNOR;
    if ( !strcmp(pSop, "10 1\n") )       return CBA_BOX_SHARP;
    assert( 0 );
    return CBA_OBJ_NONE;
}
static inline char * Ptr_SopToTypeName( char * pSop )
{
    if ( !strcmp(pSop, " 0\n") )         return "CBA_BOX_C0";
    if ( !strcmp(pSop, " 1\n") )         return "CBA_BOX_C1";
    if ( !strcmp(pSop, "1 1\n") )        return "CBA_BOX_BUF";
    if ( !strcmp(pSop, "0 1\n") )        return "CBA_BOX_INV";
    if ( !strcmp(pSop, "11 1\n") )       return "CBA_BOX_AND";
    if ( !strcmp(pSop, "00 1\n") )       return "CBA_BOX_NOR";
    if ( !strcmp(pSop, "00 0\n") )       return "CBA_BOX_OR";
    if ( !strcmp(pSop, "-1 1\n1- 1\n") ) return "CBA_BOX_OR";
    if ( !strcmp(pSop, "1- 1\n-1 1\n") ) return "CBA_BOX_OR";
    if ( !strcmp(pSop, "01 1\n10 1\n") ) return "CBA_BOX_XOR";
    if ( !strcmp(pSop, "10 1\n01 1\n") ) return "CBA_BOX_XOR";
    if ( !strcmp(pSop, "11 1\n00 1\n") ) return "CBA_BOX_XNOR";
    if ( !strcmp(pSop, "00 1\n11 1\n") ) return "CBA_BOX_XNOR";
    if ( !strcmp(pSop, "10 1\n") )       return "CBA_BOX_SHARP";
    assert( 0 );
    return NULL;
}
static inline char * Ptr_TypeToName( Cba_ObjType_t Type )
{
    if ( Type == CBA_BOX_C0 )    return "const0";
    if ( Type == CBA_BOX_C1 )    return "const1";
    if ( Type == CBA_BOX_BUF )   return "buf";
    if ( Type == CBA_BOX_INV )   return "not";
    if ( Type == CBA_BOX_AND )   return "and";
    if ( Type == CBA_BOX_NAND )  return "nand";
    if ( Type == CBA_BOX_OR )    return "or";
    if ( Type == CBA_BOX_NOR )   return "nor";
    if ( Type == CBA_BOX_XOR )   return "xor";
    if ( Type == CBA_BOX_XNOR )  return "xnor";
    if ( Type == CBA_BOX_MUX )   return "mux";
    if ( Type == CBA_BOX_MAJ )   return "maj";
    if ( Type == CBA_BOX_SHARP ) return "sharp";
    assert( 0 );
    return "???";
}
static inline char * Ptr_TypeToSop( Cba_ObjType_t Type )
{
    if ( Type == CBA_BOX_C0 )    return " 0\n";
    if ( Type == CBA_BOX_C1 )    return " 1\n";
    if ( Type == CBA_BOX_BUF )   return "1 1\n";
    if ( Type == CBA_BOX_INV )   return "0 1\n";
    if ( Type == CBA_BOX_AND )   return "11 1\n";
    if ( Type == CBA_BOX_NAND )  return "11 0\n";
    if ( Type == CBA_BOX_OR )    return "00 0\n";
    if ( Type == CBA_BOX_NOR )   return "00 1\n";
    if ( Type == CBA_BOX_XOR )   return "01 1\n10 1\n";
    if ( Type == CBA_BOX_XNOR )  return "00 1\n11 1\n";
    if ( Type == CBA_BOX_SHARP ) return "10 1\n";
    if ( Type == CBA_BOX_MUX )   return "11- 1\n0-1 1\n";
    if ( Type == CBA_BOX_MAJ )   return "11- 1\n1-1 1\n-11 1\n";
    assert( 0 );
    return "???";
}

/*=== cbaCom.c ===============================================================*/
extern void        Abc_FrameImportPtr( Vec_Ptr_t * vPtr );
extern Vec_Ptr_t * Abc_FrameExportPtr();

/*=== cbaBlast.c =============================================================*/
extern Gia_Man_t * Cba_ManExtract( Cba_Man_t * p, int fBuffers, int fVerbose );
extern Cba_Man_t * Cba_ManInsertGia( Cba_Man_t * p, Gia_Man_t * pGia );
extern void *      Cba_ManInsertAbc( Cba_Man_t * p, void * pAbc );
/*=== cbaNtk.c ===============================================================*/
extern void        Cba_ManAssignInternNames( Cba_Man_t * p );
extern Cba_Man_t * Cba_ManCollapse( Cba_Man_t * p );
/*=== cbaPtr.c ===============================================================*/
extern void        Cba_PtrFree( Vec_Ptr_t * vDes );
extern int         Cba_PtrMemory( Vec_Ptr_t * vDes );
extern void        Cba_PtrDumpBlif( char * pFileName, Vec_Ptr_t * vDes );
extern Vec_Ptr_t * Cba_PtrTransformTest( Vec_Ptr_t * vDes );
/*=== cbaPtrAbc.c ============================================================*/
extern Cba_Man_t * Cba_PtrTransformToCba( Vec_Ptr_t * vDes );
extern Vec_Ptr_t * Cba_PtrDeriveFromCba( Cba_Man_t * p );
/*=== cbaPrsBuild.c ==========================================================*/
extern void        Prs_ManVecFree( Vec_Ptr_t * vPrs );
extern Cba_Man_t * Prs_ManBuildCba( char * pFileName, Vec_Ptr_t * vDes );
/*=== cbaReadBlif.c ==========================================================*/
extern Vec_Ptr_t * Prs_ManReadBlif( char * pFileName );
/*=== cbaReadVer.c ===========================================================*/
extern Vec_Ptr_t * Prs_ManReadVerilog( char * pFileName );
/*=== cbaWriteBlif.c =========================================================*/
extern void        Prs_ManWriteBlif( char * pFileName, Vec_Ptr_t * p );
extern void        Cba_ManWriteBlif( char * pFileName, Cba_Man_t * p );
/*=== cbaWriteVer.c ==========================================================*/
extern void        Prs_ManWriteVerilog( char * pFileName, Vec_Ptr_t * p );
extern void        Cba_ManWriteVerilog( char * pFileName, Cba_Man_t * p );


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

