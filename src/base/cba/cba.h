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

    CBA_BOX_CF,   
    CBA_BOX_CT,   
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
    CBA_BOX_SHARPL,
    CBA_BOX_MUX,  
    CBA_BOX_MAJ,  

    CBA_BOX_RAND,
    CBA_BOX_RNAND,
    CBA_BOX_ROR,
    CBA_BOX_RNOR,
    CBA_BOX_RXOR,
    CBA_BOX_RXNOR,

    CBA_BOX_LAND,
    CBA_BOX_LNAND,
    CBA_BOX_LOR,
    CBA_BOX_LNOR,
    CBA_BOX_LXOR,
    CBA_BOX_LXNOR,

    CBA_BOX_NMUX,  
    CBA_BOX_SEL,
    CBA_BOX_PSEL,
    CBA_BOX_ENC,
    CBA_BOX_PENC,
    CBA_BOX_DEC,
    CBA_BOX_EDEC,

    CBA_BOX_ADD,
    CBA_BOX_SUB,
    CBA_BOX_MUL,
    CBA_BOX_DIV,
    CBA_BOX_MOD,
    CBA_BOX_REM,
    CBA_BOX_POW,
    CBA_BOX_MIN,
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
    CBA_BOX_RAMBOX,

    CBA_BOX_LATCH,
    CBA_BOX_LATCHRS,
    CBA_BOX_DFF,
    CBA_BOX_DFFRS,

    CBA_BOX_UNKNOWN   // 67
} Cba_ObjType_t; 


// name types
typedef enum { 
    CBA_NAME_BIN = 0,        // 0:  binary ID real
    CBA_NAME_WORD,           // 1:  word-level ID real
    CBA_NAME_INFO,           // 2:  word-level offset
    CBA_NAME_INDEX,          // 3:  word-leveln index
} Cba_NameType_t; 


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
    Vec_Int_t    vInfo;    // input/output/wire info
    // object attributes
    Vec_Str_t    vType;    // types     
    Vec_Int_t    vFanin;   // fanin
    Vec_Int_t    vIndex;   // index
    Vec_Int_t    vName;    // original NameId or InstId
    Vec_Int_t    vFanout;  // fanout
    Vec_Int_t    vCopy;    // copy
    // other
    Vec_Int_t    vArray;
    Vec_Int_t    vArray2;
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
    Vec_Str_t *  vOut;     
    Vec_Int_t    vBuf2RootNtk;
    Vec_Int_t    vBuf2RootObj;
    Vec_Int_t    vBuf2LeafNtk;
    Vec_Int_t    vBuf2LeafObj;
    void *       pMioLib;
    void **      ppGraphs;
    int          ElemGates[4];
};

static inline char *         Cba_ManName( Cba_Man_t * p )                    { return p->pName;                                                                            }
static inline char *         Cba_ManSpec( Cba_Man_t * p )                    { return p->pSpec;                                                                            }
static inline int            Cba_ManNtkNum( Cba_Man_t * p )                  { return p->nNtks;                                                                            }
static inline int            Cba_ManPrimNum( Cba_Man_t * p )                 { return Abc_NamObjNumMax(p->pMods) - Cba_ManNtkNum(p);                                       }
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
static inline int            Cba_NtkObjNumAlloc( Cba_Ntk_t * p )             { return Vec_StrCap(&p->vType);                                                               }
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

static inline int            Cba_InfoRange( int Beg, int End )               { return End > Beg ? End - Beg + 1 : Beg - End + 1;                                           }
static inline int            Cba_NtkInfoNum( Cba_Ntk_t * p )                 { return Vec_IntSize(&p->vInfo)/3;                                                            }
static inline int            Cba_NtkInfoNumAlloc( Cba_Ntk_t * p )            { return Vec_IntCap(&p->vInfo)/3;                                                             }
static inline int            Cba_NtkInfoType( Cba_Ntk_t * p, int i )         { return Abc_Lit2Att2(Vec_IntEntry(&p->vInfo, 3*i));                                          }
static inline int            Cba_NtkInfoName( Cba_Ntk_t * p, int i )         { return Abc_Lit2Var2(Vec_IntEntry(&p->vInfo, 3*i));                                          }
static inline int            Cba_NtkInfoBeg( Cba_Ntk_t * p, int i )          { return Vec_IntEntry(&p->vInfo, 3*i+1);                                                      }
static inline int            Cba_NtkInfoEnd( Cba_Ntk_t * p, int i )          { return Vec_IntEntry(&p->vInfo, 3*i+2);                                                      }
static inline int            Cba_NtkInfoRange( Cba_Ntk_t * p, int i )        { int* a = Vec_IntEntryP(&p->vInfo, 3*i); return a[1]>=0 ? Cba_InfoRange( a[1], a[2] ) : 1;   }
static inline int            Cba_NtkInfoIndex( Cba_Ntk_t * p, int i, int j ) { int* a = Vec_IntEntryP(&p->vInfo, 3*i); assert(a[1]>=0); return a[1]<a[2] ? a[1]+j : a[1]-j;}
static inline void           Cba_NtkAddInfo( Cba_Ntk_t * p,int i,int b,int e){ Vec_IntPush(&p->vInfo, i); Vec_IntPushTwo(&p->vInfo, b, e);                                 }
static inline void           Cba_NtkSetInfoName( Cba_Ntk_t * p, int i, int n){ Vec_IntWriteEntry( &p->vInfo, 3*i, n );                                                     }

static inline void           Cba_NtkStartNames( Cba_Ntk_t * p )              { assert(Cba_NtkObjNumAlloc(p)); Vec_IntFill(&p->vName,   Cba_NtkObjNumAlloc(p),  0);         }
static inline void           Cba_NtkStartFanouts( Cba_Ntk_t * p )            { assert(Cba_NtkObjNumAlloc(p)); Vec_IntFill(&p->vFanout, Cba_NtkObjNumAlloc(p),  0);         }
static inline void           Cba_NtkStartCopies( Cba_Ntk_t * p )             { assert(Cba_NtkObjNumAlloc(p)); Vec_IntFill(&p->vCopy,   Cba_NtkObjNumAlloc(p), -1);         }
static inline void           Cba_NtkFreeNames( Cba_Ntk_t * p )               { Vec_IntErase(&p->vName);                                                                    }
static inline void           Cba_NtkFreeFanouts( Cba_Ntk_t * p )             { Vec_IntErase(&p->vFanout);                                                                  }
static inline void           Cba_NtkFreeCopies( Cba_Ntk_t * p )              { Vec_IntErase(&p->vCopy);                                                                    }
static inline int            Cba_NtkHasNames( Cba_Ntk_t * p )                { return p->vName.pArray != NULL;                                                             }
static inline int            Cba_NtkHasFanouts( Cba_Ntk_t * p )              { return p->vFanout.pArray != NULL;                                                           }
static inline int            Cba_NtkHasCopies( Cba_Ntk_t * p )               { return p->vCopy.pArray != NULL;                                                             }

static inline int            Cba_TypeIsBox( Cba_ObjType_t Type )             { return Type >= CBA_OBJ_BOX && Type < CBA_BOX_UNKNOWN;                                       }
static inline Cba_NameType_t Cba_NameType( int n )                           { assert( n ); return (Cba_NameType_t)Abc_Lit2Att2( n );                                      }

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
static inline int            Cba_ObjIsCio( Cba_Ntk_t * p, int i )            { return Cba_ObjType(p, i) < CBA_OBJ_BOX;                                                     }

static inline int            Cba_ObjFanin( Cba_Ntk_t * p, int i )            { assert(Cba_ObjIsCo(p, i)); return Vec_IntEntry(&p->vFanin, i);                              }
static inline int            Cba_ObjIndex( Cba_Ntk_t * p, int i )            { assert(Cba_ObjIsCio(p, i)); return Vec_IntEntry(&p->vIndex, i);                             }
static inline int            Cba_ObjNameInt( Cba_Ntk_t * p, int i )          { assert(!Cba_ObjIsCo(p, i)); return Vec_IntEntry(&p->vName, i);                              }
static inline int            Cba_ObjName( Cba_Ntk_t * p, int i )             { return Cba_ObjIsCo(p, i) ? Cba_ObjNameInt(p, Cba_ObjFanin(p,i)) : Cba_ObjNameInt(p, i);     }
static inline Cba_NameType_t Cba_ObjNameType( Cba_Ntk_t * p, int i )         { assert(!Cba_ObjIsCo(p, i)); return Cba_NameType( Cba_ObjName(p, i) );                       }
static inline int            Cba_ObjNameId( Cba_Ntk_t * p, int i )           { assert(!Cba_ObjIsCo(p, i)); return Abc_Lit2Var2( Cba_ObjName(p, i) );                       }
static inline char *         Cba_ObjNameStr( Cba_Ntk_t * p, int i )          { assert(Cba_ObjNameType(p, i) <= CBA_NAME_WORD); return Cba_NtkStr(p, Cba_ObjNameId(p, i));  }
static inline int            Cba_ObjCopy( Cba_Ntk_t * p, int i )             { return Vec_IntEntry(&p->vCopy, i);                                                          }
static inline int            Cba_ObjFanout( Cba_Ntk_t * p, int i )           { assert(Cba_ObjIsCi(p, i)); return Vec_IntEntry(&p->vFanout, i);                             }
static inline int            Cba_ObjNextFanout( Cba_Ntk_t * p, int i )       { assert(Cba_ObjIsCo(p, i)); return Vec_IntEntry(&p->vFanout, i);                             }
static inline void           Cba_ObjSetFanout( Cba_Ntk_t * p, int i, int x ) { assert(Cba_ObjIsCi(p, i)); Vec_IntSetEntry(&p->vFanout, i, x);                              }
static inline void           Cba_ObjSetNextFanout( Cba_Ntk_t * p,int i,int x){ assert(Cba_ObjIsCo(p, i)); Vec_IntSetEntry(&p->vFanout, i, x);                              }
static inline void           Cba_ObjCleanFanin( Cba_Ntk_t * p, int i )       { assert(Cba_ObjFanin(p, i) >= 0 && Cba_ObjIsCo(p, i)); Vec_IntSetEntry( &p->vFanin, i, -1);  }
static inline void           Cba_ObjSetFanin( Cba_Ntk_t * p, int i, int x )  { assert(Cba_ObjFanin(p, i) == -1 && Cba_ObjIsCo(p, i)); Vec_IntSetEntry( &p->vFanin, i, x);  }
static inline void           Cba_ObjSetIndex( Cba_Ntk_t * p, int i, int x )  { assert(Cba_ObjIndex(p, i) == -1); Vec_IntSetEntry( &p->vIndex, i, x );                      }
static inline void           Cba_ObjSetName( Cba_Ntk_t * p, int i, int x )   { assert(Cba_ObjName(p, i) == 0 && !Cba_ObjIsCo(p, i)); Vec_IntSetEntry( &p->vName, i, x );   }
static inline void           Cba_ObjSetCopy( Cba_Ntk_t * p, int i, int x )   { assert(Cba_ObjCopy(p, i) == -1);  Vec_IntSetEntry( &p->vCopy,  i, x );                      }

static inline int            Cba_BoxBiNum( Cba_Ntk_t * p, int i )            { int s = i-1; assert(Cba_ObjIsBox(p, i)); while (--i >= 0               && Cba_ObjIsBi(p, i)); return s - i;  }
static inline int            Cba_BoxBoNum( Cba_Ntk_t * p, int i )            { int s = i+1; assert(Cba_ObjIsBox(p, i)); while (++i < Cba_NtkObjNum(p) && Cba_ObjIsBo(p, i)); return i - s;  }
static inline int            Cba_BoxSize( Cba_Ntk_t * p, int i )             { return 1 + Cba_BoxBiNum(p, i) + Cba_BoxBoNum(p, i);                                         }
static inline int            Cba_BoxBi( Cba_Ntk_t * p, int b, int i )        { assert(Cba_ObjIsBox(p, b)); return b - 1 - i;                                               }
static inline int            Cba_BoxBo( Cba_Ntk_t * p, int b, int i )        { assert(Cba_ObjIsBox(p, b)); return b + 1 + i;                                               }
static inline int            Cba_BoxBiBox( Cba_Ntk_t * p, int i )            { assert(Cba_ObjIsBi(p, i)); return i + 1 + Cba_ObjIndex(p, i);                               }
static inline int            Cba_BoxBoBox( Cba_Ntk_t * p, int i )            { assert(Cba_ObjIsBo(p, i)); return i - 1 - Cba_ObjIndex(p, i);                               }
static inline int            Cba_BoxFanin( Cba_Ntk_t * p, int b, int i )     { return Cba_ObjFanin(p, Cba_BoxBi(p, b, i));                                                 }
static inline int            Cba_BoxFaninBox( Cba_Ntk_t * p, int b, int i )  { return Cba_BoxBoBox(p, Cba_BoxFanin(p, b, i));                                              }

static inline int            Cba_BoxNtkId( Cba_Ntk_t * p, int i )            { assert(Cba_ObjIsBox(p, i)); return Vec_IntEntry(&p->vFanin, i);                             }
static inline void           Cba_BoxSetNtkId( Cba_Ntk_t * p, int i, int x )  { assert(Cba_ObjIsBox(p, i)&&Cba_ManNtkIsOk(p->pDesign, x));Vec_IntSetEntry(&p->vFanin, i, x);}
static inline int            Cba_BoxBiNtkId( Cba_Ntk_t * p, int i )          { assert(Cba_ObjIsBi(p, i)); return Cba_BoxNtkId(p, Cba_BoxBiBox(p, i));                      }
static inline int            Cba_BoxBoNtkId( Cba_Ntk_t * p, int i )          { assert(Cba_ObjIsBo(p, i)); return Cba_BoxNtkId(p, Cba_BoxBoBox(p, i));                      }
static inline Cba_Ntk_t *    Cba_BoxNtk( Cba_Ntk_t * p, int i )              { return Cba_ManNtk( p->pDesign, Cba_BoxNtkId(p, i) );                                        }
static inline Cba_Ntk_t *    Cba_BoxBiNtk( Cba_Ntk_t * p, int i )            { return Cba_ManNtk( p->pDesign, Cba_BoxBiNtkId(p, i) );                                      }
static inline Cba_Ntk_t *    Cba_BoxBoNtk( Cba_Ntk_t * p, int i )            { return Cba_ManNtk( p->pDesign, Cba_BoxBoNtkId(p, i) );                                      }
static inline char *         Cba_BoxNtkName( Cba_Ntk_t * p, int i )          { return Abc_NamStr( p->pDesign->pMods, Cba_BoxNtkId(p, i) );                                 }

static inline int Cba_CharIsDigit( char c ) { return c >= '0' && c <= '9'; }
static inline int Cba_NtkNamePoNum( char * pName )
{
    int Multi = 1, Counter = 0;
    char * pTemp = pName + strlen(pName) - 1; 
    assert( Cba_CharIsDigit(*pTemp) );
    for ( ; pName < pTemp && Cba_CharIsDigit(*pTemp); pTemp--, Multi *= 10 )
        Counter += Multi * (*pTemp - '0');
    return Counter;
}
static inline int Cba_NtkNamePiNum( char * pName )
{
    char * pTemp; int CounterAll = 0, Counter = 0;
    for ( pTemp = pName; *pTemp; pTemp++ )
    {
        if ( Cba_CharIsDigit(*pTemp) )
            Counter = 10 * Counter + *pTemp - '0';
        else
            CounterAll += Counter, Counter = 0;
    }
    return CounterAll;
}
static inline int Cba_NtkNameRanges( char * pName, int * pRanges, char * pSymbs )
{
    char Symb, * pTemp; 
    int nSigs = 0, Num = 0;
    assert( !strncmp(pName, "ABC", 3) );
    for ( pTemp = pName; *pTemp && !Cba_CharIsDigit(*pTemp); pTemp++ );
    assert( Cba_CharIsDigit(*pTemp) );
    Symb = *(pTemp - 1);
    for ( ; *pTemp; pTemp++ )
    {
        if ( Cba_CharIsDigit(*pTemp) )
            Num = 10 * Num + *pTemp - '0';
        else
            pSymbs[nSigs] = Symb, Symb = *pTemp, pRanges[nSigs++] = Num, Num = 0;
    }
    assert( Num > 0 );
    pSymbs[nSigs] = Symb, pRanges[nSigs++] = Num;
    return nSigs;
}
static inline int Cba_NtkReadRangesPrim( char * pName, Vec_Int_t * vRanges, int fPo )
{
    char * pTemp; int Last, Num = 0, Count = 0;
    assert( !strncmp(pName, "ABC", 3) );
    for ( pTemp = pName; *pTemp && !Cba_CharIsDigit(*pTemp); pTemp++ );
    assert( Cba_CharIsDigit(*pTemp) );
    Vec_IntClear( vRanges );
    for ( ; *pTemp; pTemp++ )
    {
        if ( Cba_CharIsDigit(*pTemp) )
            Num = 10 * Num + *pTemp - '0';
        else
            Vec_IntPush( vRanges, Num ), Count += Num, Num = 0;
    }
    assert( Num > 0 );
    Vec_IntPush( vRanges, Num );  Count += Num;
    Last = Vec_IntPop(vRanges);
    if ( !fPo )
        return Count;
    if ( !strncmp(pName, "ABCADD", 6) )
        Vec_IntFillTwo( vRanges, 2, Last - 1, 1 );
    else
        Vec_IntFill( vRanges, 1, Last );
    return Vec_IntSum(vRanges);
}
static inline int Cba_NtkReadRangesUser( Cba_Ntk_t * p, Vec_Int_t * vRanges, int fPo )
{
    int Count = 0;
    assert( fPo == 0 || fPo == 1 );
    if ( Cba_NtkInfoNum(p) == 0 )
    {
        if ( vRanges )
            Vec_IntFill( vRanges, fPo ? Cba_NtkPoNum(p) : Cba_NtkPiNum(p), 1 );
        Count = fPo ? Cba_NtkPoNum(p) : Cba_NtkPiNum(p);
    }
    else
    {
        int Value, Beg, End, k;
        if ( vRanges )
            Vec_IntClear( vRanges );
        Vec_IntForEachEntryTriple( &p->vInfo, Value, Beg, End, k )
            if ( Abc_Lit2Att2(Value) == (fPo ? 2 : 1) )
            {
                if ( vRanges )
                    Vec_IntPush( vRanges, Cba_InfoRange(Beg, End) );
                Count += Cba_InfoRange(Beg, End);
            }
    }
    return Count;
}
static inline int Cba_ObjGetRange( Cba_Ntk_t * p, int iObj, int * pBeg, int * pEnd )
{
    int i, Beg, End, iNameId = Cba_ObjName(p, iObj);
    if ( pBeg ) *pBeg = -1;
    if ( pEnd ) *pEnd = -1;
    if ( Cba_NameType(iNameId) == CBA_NAME_BIN )
        return 1;
    if ( Cba_NameType(iNameId) == CBA_NAME_WORD )
    {
        if ( pBeg ) *pBeg = 0;
        for ( i = 0; iObj + i + 1 < Cba_NtkObjNum(p); i++ )
            if ( !Cba_ObjIsCi(p, iObj + i + 1) || Cba_ObjNameType(p, iObj + i + 1) != CBA_NAME_INDEX )
                break;
        if ( pEnd ) *pEnd = i;
        return i + 1;
    }
    assert( Cba_NameType(iNameId) == CBA_NAME_INFO );
    Beg = Cba_NtkInfoBeg( p, Abc_Lit2Var2(iNameId) );
    End = Cba_NtkInfoEnd( p, Abc_Lit2Var2(iNameId) );
    assert( Beg >= 0 );
    if ( pBeg ) *pBeg = Beg;
    if ( pEnd ) *pEnd = End;
    return Cba_InfoRange( Beg, End );
}


////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

#define Cba_ManForEachNtk( p, pNtk, i )                                   \
    for ( i = 0; (i < Cba_ManNtkNum(p)) && (((pNtk) = Cba_ManNtk(p, i)), 1); i++ ) 

#define Cba_NtkForEachPi( p, iObj, i )                                    \
    for ( i = 0; (i < Cba_NtkPiNum(p))  && (((iObj) = Cba_NtkPi(p, i)), 1); i++ ) 
#define Cba_NtkForEachPo( p, iObj, i )                                    \
    for ( i = 0; (i < Cba_NtkPoNum(p))  && (((iObj) = Cba_NtkPo(p, i)), 1); i++ ) 
#define Cba_NtkForEachPoDriver( p, iObj, i )                                    \
    for ( i = 0; (i < Cba_NtkPoNum(p))  && (((iObj) = Cba_ObjFanin(p, Cba_NtkPo(p, i))), 1); i++ ) 

#define Cba_NtkForEachObj( p, i )  if ( !Cba_ObjType(p, i) ) {} else      \
    for ( i = 0; (i < Cba_NtkObjNum(p)); i++ ) 
#define Cba_NtkForEachObjType( p, Type, i )                               \
    for ( i = 0; (i < Cba_NtkObjNum(p))  && (((Type) = Cba_ObjType(p, i)), 1); i++ ) if ( !Type ) {} else

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
#define Cba_BoxForEachFaninBox( p, iBox, iFanin, i )                      \
    for ( i = 0; iBox - 1 - i >= 0 && Cba_ObjIsBi(p, iBox - 1 - i) && (((iFanin) = Cba_BoxFaninBox(p, iBox, i)), 1); i++ )

#define Cba_ObjForEachFanout( p, iCi, iCo )                               \
    for ( iCo = Cba_ObjFanout(p, iCi); iCo; iCo = Cba_ObjNextFanout(p, iCo) )
#define Cba_BoxForEachFanoutBox( p, iBox, iCo, iFanBox )                  \
    for ( assert(Cba_BoxBoNum(p, iBox) == 1), iCo = Cba_ObjFanout(p, Cba_BoxBo(p, iBox, 0)); iCo && ((iFanBox = Cba_BoxBiBox(p, iCo)), 1); iCo = Cba_ObjNextFanout(p, iCo) )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Object APIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cba_ObjAlloc( Cba_Ntk_t * p, Cba_ObjType_t Type, int Fanin )
{
    int iObj = Cba_NtkObjNum(p);
    assert( iObj == Vec_IntSize(&p->vFanin) );
    if ( Type == CBA_OBJ_PI )
        Vec_IntPush( &p->vInputs, iObj );
    else if ( Type == CBA_OBJ_PO )
        Vec_IntPush( &p->vOutputs, iObj );
    Vec_StrPush( &p->vType, (char)Type );
    Vec_IntPush( &p->vFanin, Fanin );
    return iObj;
}
static inline int Cba_ObjDup( Cba_Ntk_t * pNew, Cba_Ntk_t * p, int i )
{
    int iObj = Cba_ObjAlloc( pNew, Cba_ObjType(p, i), Cba_ObjIsBox(p, i) ? Cba_BoxNtkId(p, i) : -1 );
    if ( Cba_NtkHasNames(p) && Cba_NtkHasNames(pNew) && !Cba_ObjIsCo(p, i) ) 
        Cba_ObjSetName( pNew, iObj, Cba_ObjName(p, i) );
    Cba_ObjSetCopy( p, i, iObj );
    return iObj;
}
static inline int Cba_BoxAlloc( Cba_Ntk_t * p, Cba_ObjType_t Type, int nIns, int nOuts, int iNtk )
{
    int i, iObj;
    for ( i = nIns - 1; i >= 0; i-- )
        Cba_ObjAlloc( p, CBA_OBJ_BI, -1 );
    iObj = Cba_ObjAlloc( p, Type, iNtk );
    for ( i = 0; i < nOuts; i++ )
        Cba_ObjAlloc( p, CBA_OBJ_BO, -1 );
    return iObj;
}
static inline int Cba_BoxDup( Cba_Ntk_t * pNew, Cba_Ntk_t * p, int iBox )
{
    int i, iTerm, iBoxNew;
    Cba_BoxForEachBiReverse( p, iBox, iTerm, i )
        Cba_ObjDup( pNew, p, iTerm );
    iBoxNew = Cba_ObjDup( pNew, p, iBox );
    if ( Cba_NtkHasNames(p) && Cba_NtkHasNames(pNew) && Cba_ObjName(p, iBox) ) 
        Cba_ObjSetName( pNew, iBoxNew, Cba_ObjName(p, iBox) );
    if ( Cba_BoxNtk(p, iBox) )
        Cba_BoxSetNtkId( pNew, iBoxNew, Cba_NtkCopy(Cba_BoxNtk(p, iBox)) );
    Cba_BoxForEachBo( p, iBox, iTerm, i )
        Cba_ObjDup( pNew, p, iTerm );
    return iBoxNew;
}
static inline void Cba_BoxDelete( Cba_Ntk_t * p, int iBox )
{
    int iStart = iBox - Cba_BoxBiNum(p, iBox);
    int i, iStop = iBox + Cba_BoxBoNum(p, iBox);
    for ( i = iStart; i <= iStop; i++ )
    {
        Vec_StrWriteEntry( &p->vType,  i, (char)0 );
        Vec_IntWriteEntry( &p->vFanin, i, -1 );
        if ( Cba_NtkHasNames(p) )
            Vec_IntWriteEntry( &p->vName, i, 0 );
        if ( Cba_NtkHasFanouts(p) )
            Vec_IntWriteEntry( &p->vFanout, i, 0 );
    }
}
static inline void Cba_BoxReplace( Cba_Ntk_t * p, int iBox, int * pArray, int nSize )
{
    extern void Cba_NtkUpdateFanout( Cba_Ntk_t * p, int iOld, int iNew );
    int i, Limit = Cba_BoxBoNum(p, iBox);
    assert( Limit == nSize );
    for ( i = 0; i < Limit; i++ )
        Cba_NtkUpdateFanout( p, Cba_BoxBo(p, iBox, i), pArray[i] );
}


/**Function*************************************************************

  Synopsis    [Prints vector.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_StrPrint( Vec_Str_t * p, int fInt )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        if ( fInt )
            printf( "%d ", (int)p->pArray[i] );
        else
            printf( "%c ", p->pArray[i] );
    printf( "\n" );
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
    if ( Vec_IntSize(&p->vInfo) )
        Vec_IntAppend( &pNew->vInfo, &p->vInfo );
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
    //Cba_NtkFreeCopies( p ); // needed for name transfer and host ntk
    assert( Cba_NtkObjNum(pNew) == Cba_NtkObjNumAlloc(pNew) );
}
static inline void Cba_NtkDupUserBoxes( Cba_Ntk_t * pNew, Cba_Ntk_t * p )
{
    int i, iObj;
    assert( pNew != p );
    Cba_NtkAlloc( pNew, Cba_NtkNameId(p), Cba_NtkPiNum(p), Cba_NtkPoNum(p), Cba_NtkObjNum(p) + 3*Cba_NtkCoNum(p) );
    if ( Vec_IntSize(&p->vInfo) )
        Vec_IntAppend( &pNew->vInfo, &p->vInfo );
    Cba_NtkStartCopies( p );
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjDup( pNew, p, iObj );
    Cba_NtkForEachPo( p, iObj, i )
        Cba_ObjDup( pNew, p, iObj );
    Cba_NtkForEachBoxUser( p, iObj )
        Cba_BoxDup( pNew, p, iObj );
    // connect feed-throughs
    Cba_NtkForEachCo( p, iObj )
        if ( Cba_ObjCopy(p, iObj) >= 0 && Cba_ObjCopy(p, Cba_ObjFanin(p, iObj)) >= 0 )
            Cba_ObjSetFanin( pNew, Cba_ObjCopy(p, iObj), Cba_ObjCopy(p, Cba_ObjFanin(p, iObj)) );
}
static inline void Cba_NtkMoveNames( Cba_Ntk_t * pNew, Cba_Ntk_t * p )
{
    int i, iBox, iObj;
    assert( Cba_NtkHasNames(p) );
    assert( !Cba_NtkHasNames(pNew) );
    Cba_NtkStartNames( pNew );
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjSetName( pNew, Cba_ObjCopy(p, iObj), Cba_ObjName(p, iObj) );
    Cba_NtkForEachBoxUser( p, iBox )
    {
        Cba_ObjSetName( pNew, Cba_ObjCopy(p, iBox), Cba_ObjName(p, iBox) );
        Cba_BoxForEachBo( p, iBox, iObj, i )
            Cba_ObjSetName( pNew, Cba_ObjCopy(p, iObj), Cba_ObjName(p, iObj) );
    }
    Cba_NtkForEachBoxUser( p, iBox )
        Cba_BoxForEachBi( p, iBox, iObj, i )
            if ( !Cba_ObjName(pNew, Cba_ObjFanin(pNew, Cba_ObjCopy(p, iObj))) )
                Cba_ObjSetName( pNew, Cba_ObjFanin(pNew, Cba_ObjCopy(p, iObj)), Cba_ObjName(p, iObj) );
    Cba_NtkForEachPo( p, iObj, i )
        if ( !Cba_ObjName(pNew, Cba_ObjFanin(pNew, Cba_ObjCopy(p, iObj))) )
            Cba_ObjSetName( pNew, Cba_ObjFanin(pNew, Cba_ObjCopy(p, iObj)), Cba_ObjName(p, iObj) );
}

static inline void Cba_NtkFree( Cba_Ntk_t * p )
{
    Vec_IntErase( &p->vInputs );
    Vec_IntErase( &p->vOutputs );
    Vec_IntErase( &p->vInfo );
    Vec_StrErase( &p->vType );
    Vec_IntErase( &p->vFanin );    
    Vec_IntErase( &p->vIndex );
    Vec_IntErase( &p->vName );    
    Vec_IntErase( &p->vFanout );    
    Vec_IntErase( &p->vCopy );    
    Vec_IntErase( &p->vArray );    
    Vec_IntErase( &p->vArray2 );    
}
static inline int Cba_NtkMemory( Cba_Ntk_t * p )
{
    int nMem = sizeof(Cba_Ntk_t);
    nMem += Vec_IntMemory(&p->vInputs);
    nMem += Vec_IntMemory(&p->vOutputs);
    nMem += Vec_IntMemory(&p->vInfo);
    nMem += Vec_StrMemory(&p->vType);
    nMem += Vec_IntMemory(&p->vFanin);
    nMem += Vec_IntMemory(&p->vIndex);
    nMem += Vec_IntMemory(&p->vName);
    nMem += Vec_IntMemory(&p->vFanout);
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
static inline void Cba_NtkDeriveIndex( Cba_Ntk_t * p )
{
    int i, iObj, iTerm;
    Vec_IntFill( &p->vIndex, Cba_NtkObjNum(p), -1 );
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjSetIndex( p, iObj, i );
    Cba_NtkForEachPo( p, iObj, i )
        Cba_ObjSetIndex( p, iObj, i );
    Cba_NtkForEachBox( p, iObj )
    {
        Cba_BoxForEachBi( p, iObj, iTerm, i )
            Cba_ObjSetIndex( p, iTerm, i );
        Cba_BoxForEachBo( p, iObj, iTerm, i )
            Cba_ObjSetIndex( p, iTerm, i );
    }
}
static inline void Cba_NtkPrint( Cba_Ntk_t * p )
{
    int i, Type, Value, Beg, End;
    printf( "Interface (%d):\n", Cba_NtkInfoNum(p) );
    Vec_IntForEachEntryTriple( &p->vInfo, Value, Beg, End, i )
    {
        printf( "%6d : ", i );
        printf( "Type =%3d  ", Cba_NtkInfoType(p, i/3) );
        if ( Beg >= 0 )
            printf( "[%d:%d]   ", End, Beg );
        else
            printf( "        " );
        printf( "Name =%3d   ", Cba_NtkInfoName(p, i/3) );
        if ( Cba_NtkInfoName(p, i/3) )
            printf( "%s", Cba_NtkStr( p, Cba_NtkInfoName(p, i/3) ) );
        printf( "\n" );
    }
    printf( "Objects (%d):\n", Cba_NtkObjNum(p) );
    Cba_NtkForEachObjType( p, Type, i )
    {
        printf( "%6d : ", i );
        printf( "Type =%3d  ", Type );
        if ( Cba_ObjIsCo(p, i) )
            printf( "Fanin =%6d  ", Cba_ObjFanin(p, i) );
        else if ( Cba_NtkHasNames(p) && Cba_ObjName(p, i) )
        {
            printf( "Name  =%6d(%d)  ", Cba_ObjNameId(p, i), Cba_ObjNameType(p, i) );
            if ( Cba_ObjNameType(p, i) <= CBA_NAME_WORD )
                printf( "%s", Cba_ObjNameStr(p, i) );
        }
        printf( "\n" );
    }
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
    Cba_Ntk_t * pNtk, * pHost; int i;
    Cba_Man_t * pNew = Cba_ManStart( p, Cba_ManNtkNum(p) );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkSetCopy( pNtk, i );
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDup( Cba_NtkCopyNtk(pNew, pNtk), pNtk );
    Cba_ManForEachNtk( p, pNtk, i )
        if ( (pHost = Cba_NtkHostNtk(pNtk)) )
            Cba_NtkSetHost( Cba_NtkCopyNtk(pNew, pNtk), Cba_NtkCopy(pHost), Cba_ObjCopy(pHost, Cba_NtkHostObj(pNtk)) );
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
static inline void Cba_ManMoveNames( Cba_Man_t * pNew, Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkMoveNames( Cba_NtkCopyNtk(pNew, pNtk), pNtk );
}


static inline void Cba_ManFree( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkFree( pNtk );
    Vec_IntErase( &p->vBuf2LeafNtk );
    Vec_IntErase( &p->vBuf2LeafObj );
    Vec_IntErase( &p->vBuf2RootNtk );
    Vec_IntErase( &p->vBuf2RootObj );
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
    printf( "pri =%4d  ", Cba_ManPrimNum(p) );
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
    if ( !strcmp(pSop, " 0\n") )         return CBA_BOX_CF;
    if ( !strcmp(pSop, " 1\n") )         return CBA_BOX_CT;
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
    if ( Type == CBA_BOX_CF )    return "const0";
    if ( Type == CBA_BOX_CT )    return "const1";
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
    if ( Type == CBA_BOX_CF )    return " 0\n";
    if ( Type == CBA_BOX_CT )    return " 1\n";
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
extern int         Cba_NtkBuildLibrary( Cba_Man_t * p );
extern Gia_Man_t * Cba_ManExtract( Cba_Man_t * p, int fBuffers, int fVerbose );
extern Cba_Man_t * Cba_ManInsertGia( Cba_Man_t * p, Gia_Man_t * pGia );
extern void *      Cba_ManInsertAbc( Cba_Man_t * p, void * pAbc );
/*=== cbaCba.c ===============================================================*/
extern Cba_Man_t * Cba_ManReadCba( char * pFileName );
extern void        Cba_ManWriteCba( char * pFileName, Cba_Man_t * p );
/*=== cbaNtk.c ===============================================================*/
extern void        Cba_NtkUpdateFanout( Cba_Ntk_t * p, int iOld, int iNew );
extern void        Cba_ManDeriveFanout( Cba_Man_t * p );
extern void        Cba_ManAssignInternNames( Cba_Man_t * p );
extern void        Cba_ManAssignInternWordNames( Cba_Man_t * p );
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
/*=== cbaReadSmt.c ===========================================================*/
extern Vec_Ptr_t * Prs_ManReadSmt( char * pFileName );
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

