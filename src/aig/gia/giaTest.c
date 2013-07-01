/**CFile****************************************************************

  FileName    [giaTest.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaTest.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/mem/mem2.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

//#define MIG_RUNTIME

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MIG_NONE 0x7FFFFFFF
//#define MIG_MASK 0x0000FFFF
//#define MIG_BASE 16
#define MIG_MASK 0x0000FFF
#define MIG_BASE 12

typedef struct Mig_Fan_t_ Mig_Fan_t;
struct Mig_Fan_t_
{
    unsigned       fCompl :  1;  // the complemented attribute
    unsigned       Id     : 31;  // fanin ID
};

typedef struct Mig_Obj_t_ Mig_Obj_t;
struct Mig_Obj_t_
{
    Mig_Fan_t      pFans[4];     // fanins
};

typedef struct Mig_Man_t_ Mig_Man_t;
struct Mig_Man_t_
{
    char *         pName;        // name
    int            nObjs;        // number of objects
    int            nRegs;        // number of flops
    Vec_Ptr_t      vPages;       // memory pages
    Vec_Int_t      vCis;         // CI IDs
    Vec_Int_t      vCos;         // CO IDs
    // object iterator
    Mig_Obj_t *    pPage;        // current page
    int            iPage;        // current page index
    // attributes
    int            nTravIds;     // traversal ID counter
    Vec_Int_t      vTravIds;     // traversal IDs
    Vec_Int_t      vLevels;      // levels
    Vec_Int_t      vSibls;       // choice nodes
    Vec_Int_t      vRefs;        // ref counters
    Vec_Int_t      vCopies;      // copies
    void *         pMan;         // mapping manager
};

/*
    Usage of fanin atrributes
    --------------------------------------------------------------------------------------------------------------
       Const0  Terminal    CI      CO     Buf     Node    Node2   Node3   And2    XOR2    MUX     MAJ    Sentinel
    --------------------------------------------------------------------------------------------------------------
    0    -     -/fanin0    -     fanin0  fanin0  fanin0  fanin0  fanin0  fanin0  fanin1  fanin0  fanin1     -
    1    -        -        -       -       -     fanin1  fanin1  fanin1  fanin1  fanin0  fanin1  fanin0     -
    2    -      CIO ID   CIO ID  CIO ID    -    -/fanin2    -    fanin2    -       -     fanin2  fanin2     -
    3    0        ID       ID      ID      ID      ID      ID      ID      ID      ID      ID      ID       -
    --------------------------------------------------------------------------------------------------------------

    One memory page contain 2^MIG_BASE+2 16-byte objects.
    - the first object contains the pointer to the manager (8 bytes)
    - the next 2^MIG_BASE are potentially used as objects
    - the last object is a sentinel to signal the end of the page
*/

static inline int          Mig_IdPage( int v )                 { return v >> MIG_BASE;                                                      }
static inline int          Mig_IdCell( int v )                 { return v & MIG_MASK;                                                       }

static inline char *       Mig_ManName( Mig_Man_t * p )        { return p->pName;                                                           }
static inline int          Mig_ManCiNum( Mig_Man_t * p )       { return Vec_IntSize(&p->vCis);                                              }
static inline int          Mig_ManCoNum( Mig_Man_t * p )       { return Vec_IntSize(&p->vCos);                                              }
static inline int          Mig_ManPiNum( Mig_Man_t * p )       { return Vec_IntSize(&p->vCis) - p->nRegs;                                   }
static inline int          Mig_ManPoNum( Mig_Man_t * p )       { return Vec_IntSize(&p->vCos) - p->nRegs;                                   }
static inline int          Mig_ManRegNum( Mig_Man_t * p )      { return p->nRegs;                                                           }
static inline int          Mig_ManObjNum( Mig_Man_t * p )      { return p->nObjs;                                                           }
static inline int          Mig_ManNodeNum( Mig_Man_t * p )     { return p->nObjs - Vec_IntSize(&p->vCis) - Vec_IntSize(&p->vCos) - 1;       }
static inline int          Mig_ManCandNum( Mig_Man_t * p )     { return Mig_ManCiNum(p) + Mig_ManNodeNum(p);                                }
static inline void         Mig_ManSetRegNum( Mig_Man_t * p, int v )   { p->nRegs = v;                                                       }

static inline Mig_Obj_t *  Mig_ManPage( Mig_Man_t * p, int v ) { return (Mig_Obj_t *)Vec_PtrEntry(&p->vPages, Mig_IdPage(v));               }
static inline Mig_Obj_t *  Mig_ManObj( Mig_Man_t * p, int v )  { assert(v >= 0 && v < p->nObjs);  return Mig_ManPage(p, v) + Mig_IdCell(v); }
static inline Mig_Obj_t *  Mig_ManCi( Mig_Man_t * p, int v )   { return Mig_ManObj( p, Vec_IntEntry(&p->vCis,v) );                          }
static inline Mig_Obj_t *  Mig_ManCo( Mig_Man_t * p, int v )   { return Mig_ManObj( p, Vec_IntEntry(&p->vCos,v) );                          }
static inline Mig_Obj_t *  Mig_ManPi( Mig_Man_t * p, int v )   { assert( v < Mig_ManPiNum(p) );  return Mig_ManCi( p, v );                  }
static inline Mig_Obj_t *  Mig_ManPo( Mig_Man_t * p, int v )   { assert( v < Mig_ManPoNum(p) );  return Mig_ManCo( p, v );                  }
static inline Mig_Obj_t *  Mig_ManRo( Mig_Man_t * p, int v )   { assert( v < Mig_ManRegNum(p) ); return Mig_ManCi( p, Mig_ManPiNum(p)+v );  }
static inline Mig_Obj_t *  Mig_ManRi( Mig_Man_t * p, int v )   { assert( v < Mig_ManRegNum(p) ); return Mig_ManCo( p, Mig_ManPoNum(p)+v );  }
static inline Mig_Obj_t *  Mig_ManConst0( Mig_Man_t * p )      { return Mig_ManObj(p, 0);                                                   }

static inline int          Mig_FanCompl( Mig_Obj_t * p, int i )                { return p->pFans[i].fCompl;                                 }
static inline int          Mig_FanId( Mig_Obj_t * p, int i )                   { return p->pFans[i].Id;                                     }
static inline int          Mig_FanIsNone( Mig_Obj_t * p, int i )               { return p->pFans[i].Id == MIG_NONE;                         }
static inline int          Mig_FanSetCompl( Mig_Obj_t * p, int i, int v )      { assert( !(v >> 1) ); return p->pFans[i].fCompl = v;        }
static inline int          Mig_FanSetId( Mig_Obj_t * p, int i, int v )         { assert(v >= 0 && v < MIG_NONE); return p->pFans[i].Id = v; }

static inline int          Mig_ObjIsNone( Mig_Obj_t * p )                      { return Mig_FanIsNone( p, 3 );                              }
static inline int          Mig_ObjIsConst0( Mig_Obj_t * p )                    { return Mig_FanId( p, 3 ) == 0;                             } 
static inline int          Mig_ObjIsTerm( Mig_Obj_t * p )                      { return Mig_FanIsNone( p, 1 ) && !Mig_FanIsNone( p, 2 );    }
static inline int          Mig_ObjIsCi( Mig_Obj_t * p )                        { return Mig_ObjIsTerm(p) &&  Mig_FanIsNone( p, 0 );         } 
static inline int          Mig_ObjIsCo( Mig_Obj_t * p )                        { return Mig_ObjIsTerm(p) && !Mig_FanIsNone( p, 0 );         } 
static inline int          Mig_ObjIsBuf( Mig_Obj_t * p )                       { return Mig_FanIsNone( p, 1 ) && Mig_FanIsNone( p, 2 ) && !Mig_FanIsNone( p, 0 );     } 
static inline int          Mig_ObjIsNode( Mig_Obj_t * p )                      { return!Mig_FanIsNone( p, 1 );                              } 
static inline int          Mig_ObjIsNode2( Mig_Obj_t * p )                     { return Mig_ObjIsNode( p ) &&  Mig_FanIsNone( p, 2 );       } 
static inline int          Mig_ObjIsNode3( Mig_Obj_t * p )                     { return Mig_ObjIsNode( p ) && !Mig_FanIsNone( p, 2 );       } 
static inline int          Mig_ObjIsAnd( Mig_Obj_t * p )                       { return Mig_ObjIsNode2( p ) && Mig_FanId(p, 0) < Mig_FanId(p, 1); } 
static inline int          Mig_ObjIsXor( Mig_Obj_t * p )                       { return Mig_ObjIsNode2( p ) && Mig_FanId(p, 0) > Mig_FanId(p, 1); } 
static inline int          Mig_ObjIsMux( Mig_Obj_t * p )                       { return Mig_ObjIsNode3( p );                                } 
static inline int          Mig_ObjIsCand( Mig_Obj_t * p )                      { return Mig_ObjIsNode(p) || Mig_ObjIsCi(p);                 } 

static inline int          Mig_ObjId( Mig_Obj_t * p )                          { return Mig_FanId( p, 3 );                                  }
static inline void         Mig_ObjSetId( Mig_Obj_t * p, int v )                { Mig_FanSetId( p, 3, v );                                   }
static inline int          Mig_ObjCioId( Mig_Obj_t * p )                       { assert( Mig_ObjIsTerm(p) ); return Mig_FanId( p, 2 );      }
static inline void         Mig_ObjSetCioId( Mig_Obj_t * p, int v )             { assert( Mig_FanIsNone(p, 1) ); Mig_FanSetId( p, 2, v );    }
static inline int          Mig_ObjPhase( Mig_Obj_t * p )                       { return Mig_FanCompl( p, 3 );                               }
static inline void         Mig_ObjSetPhase( Mig_Obj_t * p, int v )             { Mig_FanSetCompl( p, 3, 1 );                                }

static inline Mig_Man_t *  Mig_ObjMan( Mig_Obj_t * p )                         { return *((Mig_Man_t**)(p - Mig_IdCell(Mig_ObjId(p)) - 1)); }
//static inline Mig_Obj_t ** Mig_ObjPageP( Mig_Obj_t * p )                       { return *((Mig_Obj_t***)(p - Mig_IdCell(Mig_ObjId(p))) - 1);} 
static inline Mig_Obj_t *  Mig_ObjObj( Mig_Obj_t * p, int i )                  { return Mig_ManObj( Mig_ObjMan(p), i );                     } 

static inline int          Mig_ManIdToCioId( Mig_Man_t * p, int Id )           { return Mig_ObjCioId( Mig_ManObj(p, Id) );                  }
static inline int          Mig_ManCiIdToId( Mig_Man_t * p, int CiId )          { return Mig_ObjId( Mig_ManCi(p, CiId) );                    }
static inline int          Mig_ManCoIdToId( Mig_Man_t * p, int CoId )          { return Mig_ObjId( Mig_ManCo(p, CoId) );                    }

static inline int          Mig_ObjIsPi( Mig_Obj_t * p )                        { return Mig_ObjIsCi(p) && Mig_ObjCioId(p) < Mig_ManPiNum(Mig_ObjMan(p));   } 
static inline int          Mig_ObjIsPo( Mig_Obj_t * p )                        { return Mig_ObjIsCo(p) && Mig_ObjCioId(p) < Mig_ManPoNum(Mig_ObjMan(p));   } 
static inline int          Mig_ObjIsRo( Mig_Obj_t * p )                        { return Mig_ObjIsCi(p) && Mig_ObjCioId(p) >= Mig_ManPiNum(Mig_ObjMan(p));  } 
static inline int          Mig_ObjIsRi( Mig_Obj_t * p )                        { return Mig_ObjIsCo(p) && Mig_ObjCioId(p) >= Mig_ManPoNum(Mig_ObjMan(p));  } 

static inline Mig_Obj_t *  Mig_ObjRoToRi( Mig_Obj_t * p )                      { Mig_Man_t * pMan = Mig_ObjMan(p); assert( Mig_ObjIsRo(p) ); return Mig_ManCo(pMan, Mig_ManCoNum(pMan) - Mig_ManCiNum(pMan) + Mig_ObjCioId(p)); } 
static inline Mig_Obj_t *  Mig_ObjRiToRo( Mig_Obj_t * p )                      { Mig_Man_t * pMan = Mig_ObjMan(p); assert( Mig_ObjIsRi(p) ); return Mig_ManCi(pMan, Mig_ManCiNum(pMan) - Mig_ManCoNum(pMan) + Mig_ObjCioId(p)); } 

static inline int          Mig_ObjHasFanin( Mig_Obj_t * p, int i )             { return i < 3 && Mig_FanId(p, i) != MIG_NONE;               }
static inline int          Mig_ObjFaninId( Mig_Obj_t * p, int i )              { assert( i < 3 && Mig_FanId(p, i) < Mig_ObjId(p) ); return Mig_FanId( p, i );  }
static inline int          Mig_ObjFaninId0( Mig_Obj_t * p )                    { return Mig_FanId( p, 0 );                                  }
static inline int          Mig_ObjFaninId1( Mig_Obj_t * p )                    { return Mig_FanId( p, 1 );                                  }
static inline int          Mig_ObjFaninId2( Mig_Obj_t * p )                    { return Mig_FanId( p, 2 );                                  }
static inline Mig_Obj_t *  Mig_ObjFanin( Mig_Obj_t * p, int i )                { return Mig_ManObj( Mig_ObjMan(p), Mig_ObjFaninId(p, i) );    }
//static inline Mig_Obj_t *  Mig_ObjFanin( Mig_Obj_t * p, int i )                { return Mig_ObjPageP(p)[Mig_IdPage(Mig_ObjFaninId(p, i))] + Mig_IdCell(Mig_ObjFaninId(p, i));    }
static inline Mig_Obj_t *  Mig_ObjFanin0( Mig_Obj_t * p )                      { return Mig_FanIsNone(p, 0) ? NULL: Mig_ObjFanin(p, 0);     }
static inline Mig_Obj_t *  Mig_ObjFanin1( Mig_Obj_t * p )                      { return Mig_FanIsNone(p, 1) ? NULL: Mig_ObjFanin(p, 1);     }
static inline Mig_Obj_t *  Mig_ObjFanin2( Mig_Obj_t * p )                      { return Mig_FanIsNone(p, 2) ? NULL: Mig_ObjFanin(p, 2);     }
static inline int          Mig_ObjFaninC( Mig_Obj_t * p, int i )               { assert( i < 3 ); return Mig_FanCompl(p, i);                }
static inline int          Mig_ObjFaninC0( Mig_Obj_t * p )                     { return Mig_FanCompl(p, 0);                                 }
static inline int          Mig_ObjFaninC1( Mig_Obj_t * p )                     { return Mig_FanCompl(p, 1);                                 }
static inline int          Mig_ObjFaninC2( Mig_Obj_t * p )                     { return Mig_FanCompl(p, 2);                                 }
static inline int          Mig_ObjFaninLit( Mig_Obj_t * p, int i )             { return Abc_Var2Lit( Mig_FanId(p, i), Mig_FanCompl(p, i) ); }
static inline void         Mig_ObjFlipFaninC( Mig_Obj_t * p, int i )           { Mig_FanSetCompl( p, i, !Mig_FanCompl(p, i) );              }
static inline int          Mig_ObjWhatFanin( Mig_Obj_t * p, int i )            { if (Mig_FanId(p, 0) == i) return 0; if (Mig_FanId(p, 1) == i) return 1; if (Mig_FanId(p, 2) == i) return 2; return -1;           }
static inline void         Mig_ObjSetFaninLit( Mig_Obj_t * p, int i, int l )   { assert( l >= 0 && (l >> 1) < Mig_ObjId(p) ); Mig_FanSetId(p, i, Abc_Lit2Var(l)); Mig_FanSetCompl(p, i, Abc_LitIsCompl(l));       }

static inline int          Mig_ObjSiblId( Mig_Obj_t * p )                      { return Vec_IntSize(&Mig_ObjMan(p)->vSibls) == 0 ? 0: Vec_IntEntry(&Mig_ObjMan(p)->vSibls, Mig_ObjId(p));    }
static inline Mig_Obj_t *  Mig_ObjSibl( Mig_Obj_t * p )                        { return Mig_ObjSiblId(p) == 0 ? NULL: Mig_ObjObj(p, Mig_ObjSiblId(p));                                       }
static inline int          Mig_ObjRefNum( Mig_Obj_t * p )                      { return Vec_IntEntry(&Mig_ObjMan(p)->vRefs, Mig_ObjId(p));           }

static inline void         Mig_ManCleanCopy( Mig_Man_t * p )                   { if ( p->vCopies.pArray == NULL ) Vec_IntFill( &p->vCopies, Mig_ManObjNum(p), -1 );              }
static inline int          Mig_ObjCopy( Mig_Obj_t * p )                        { return Vec_IntSize(&Mig_ObjMan(p)->vCopies) == 0 ? -1: Vec_IntEntry(&Mig_ObjMan(p)->vCopies, Mig_ObjId(p));      }
static inline void         Mig_ObjSetCopy( Mig_Obj_t * p, int i )              { assert( Vec_IntSize(&Mig_ObjMan(p)->vCopies) != 0 ); Vec_IntWriteEntry(&Mig_ObjMan(p)->vCopies, Mig_ObjId(p), i); }

static inline void         Mig_ManIncrementTravId( Mig_Man_t * p )             { if ( p->vTravIds.pArray == NULL ) Vec_IntFill( &p->vTravIds, Mig_ManObjNum(p)+500, 0 ); p->nTravIds++;      }
static inline void         Mig_ObjIncrementTravId( Mig_Obj_t * p )             { if ( Mig_ObjMan(p)->vTravIds.pArray == NULL ) Vec_IntFill( &Mig_ObjMan(p)->vTravIds, Mig_ManObjNum(Mig_ObjMan(p))+500, 0 ); Mig_ObjMan(p)->nTravIds++;           }
static inline void         Mig_ObjSetTravIdCurrent( Mig_Obj_t * p )            { Vec_IntSetEntry(&Mig_ObjMan(p)->vTravIds, Mig_ObjId(p), Mig_ObjMan(p)->nTravIds );              }
static inline void         Mig_ObjSetTravIdPrevious( Mig_Obj_t * p )           { Vec_IntSetEntry(&Mig_ObjMan(p)->vTravIds, Mig_ObjId(p), Mig_ObjMan(p)->nTravIds-1 );            }
static inline int          Mig_ObjIsTravIdCurrent( Mig_Obj_t * p )             { return (Vec_IntGetEntry(&Mig_ObjMan(p)->vTravIds, Mig_ObjId(p)) == Mig_ObjMan(p)->nTravIds);    }
static inline int          Mig_ObjIsTravIdPrevious( Mig_Obj_t * p )            { return (Vec_IntGetEntry(&Mig_ObjMan(p)->vTravIds, Mig_ObjId(p)) == Mig_ObjMan(p)->nTravIds-1);  }
static inline void         Mig_ObjSetTravIdCurrentId( Mig_Man_t * p, int Id )  { Vec_IntSetEntry(&p->vTravIds, Id, p->nTravIds );                                                }
static inline int          Mig_ObjIsTravIdCurrentId( Mig_Man_t * p, int Id )   { return (Vec_IntGetEntry(&p->vTravIds, Id) == p->nTravIds);                                      }

// iterators over objects
#define Mig_ManForEachObj( p, pObj )                                    \
    for ( p->iPage = 0; p->iPage < Vec_PtrSize(&p->vPages) &&           \
        ((p->pPage) = (Mig_Obj_t *)Vec_PtrEntry(&p->vPages, p->iPage)); p->iPage++ ) \
        for ( pObj = p->pPage; !Mig_ObjIsNone(pObj); pObj++ )
#define Mig_ManForEachObj1( p, pObj )                                   \
    for ( p->iPage = 0; p->iPage < Vec_PtrSize(&p->vPages) &&           \
        ((p->pPage) = (Mig_Obj_t *)Vec_PtrEntry(&p->vPages, p->iPage)); p->iPage++ ) \
        for ( pObj = p->pPage + (p->iPage == 0); !Mig_ObjIsNone(pObj); pObj++ )
#define Mig_ManForEachObjReverse( p, pObj )                             \
    for ( p->iPage = Vec_PtrSize(&p->vPages) - 1; p->iPage >= 0 &&      \
        ((p->pPage) = (Mig_Obj_t *)Vec_PtrEntry(&p->vPages, p->iPage)); p->iPage-- ) \
        for ( pObj = (p->iPage == Vec_PtrSize(&p->vPages) - 1) ?        \
            Mig_ManObj(p, Mig_ManObjNum(p)-1) :  p->pPage + MIG_MASK;   \
                pObj - p->pPage >= 0; pObj-- )

#define Mig_ManForEachObjVec( vVec, p, pObj, i )                        \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pObj) = Mig_ManObj(p, Vec_IntEntry(vVec,i))); i++ )

#define Mig_ManForEachNode( p, pObj )                                   \
    Mig_ManForEachObj( p, pObj ) if ( !Mig_ObjIsNode(pObj) ) {} else
#define Mig_ManForEachCand( p, pObj )                                   \
    Mig_ManForEachObj( p, pObj ) if ( !Mig_ObjIsCand(pObj) ) {} else

#define Mig_ManForEachCi( p, pObj, i )                                  \
    for ( i = 0; (i < Vec_IntSize(&p->vCis)) && ((pObj) = Mig_ManCi(p, i)); i++ )
#define Mig_ManForEachCo( p, pObj, i )                                  \
    for ( i = 0; (i < Vec_IntSize(&p->vCos)) && ((pObj) = Mig_ManCo(p, i)); i++ )

// iterators over fanins
#define Mig_ObjForEachFaninId( p, iFanin, i )                           \
    for ( i = 0; Mig_ObjHasFanin(p, i) && ((iFanin) = Mig_ObjFaninId(p, i)); i++ )
#define Mig_ObjForEachFanin( p, pFanin, i )                             \
    for ( i = 0; Mig_ObjHasFanin(p, i) && ((pFanin) = Mig_ObjFanin(p, i)); i++ )


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Mig_Obj_t * Mig_ManAppendObj( Mig_Man_t * p )
{
    Mig_Obj_t * pObj;
    assert( p->nObjs < MIG_NONE );
    if ( p->nObjs >= (Vec_PtrSize(&p->vPages) << MIG_BASE) )
    {
        Mig_Obj_t * pPage;// int i;
        assert( p->nObjs == (Vec_PtrSize(&p->vPages) << MIG_BASE) );
        pPage = ABC_FALLOC( Mig_Obj_t, MIG_MASK + 3 ); // 1 for mask, 1 for prefix, 1 for sentinel
        *((void **)pPage) = p;
//        *((void ***)(pPage + 1) - 1) = Vec_PtrArray(&p->vPages);
        Vec_PtrPush( &p->vPages, pPage + 1 );
//        if ( *((void ***)(pPage + 1) - 1) != Vec_PtrArray(&p->vPages) )
//            Vec_PtrForEachEntry( Mig_Obj_t *, &p->vPages, pPage, i )
//                *((void ***)pPage - 1) = Vec_PtrArray(&p->vPages);
    }
    pObj = Mig_ManObj( p, p->nObjs++ );
    assert( Mig_ObjIsNone(pObj) );
    Mig_ObjSetId( pObj, p->nObjs-1 );
    return pObj;
}
static inline int Mig_ManAppendCi( Mig_Man_t * p )  
{ 
    Mig_Obj_t * pObj = Mig_ManAppendObj( p );
    Mig_ObjSetCioId( pObj, Vec_IntSize(&p->vCis) );
    Vec_IntPush( &p->vCis, Mig_ObjId(pObj) );
    return Mig_ObjId(pObj) << 1;
}
static inline int Mig_ManAppendCo( Mig_Man_t * p, int iLit0 )  
{ 
    Mig_Obj_t * pObj;
    assert( !Mig_ObjIsCo(Mig_ManObj(p, Abc_Lit2Var(iLit0))) );
    pObj = Mig_ManAppendObj( p );    
    Mig_ObjSetFaninLit( pObj, 0, iLit0 );
    Mig_ObjSetCioId( pObj, Vec_IntSize(&p->vCos) );
    Vec_IntPush( &p->vCos, Mig_ObjId(pObj) );
    return Mig_ObjId( pObj ) << 1;
}
static inline int Mig_ManAppendBuf( Mig_Man_t * p, int iLit0 )  
{ 
    Mig_Obj_t * pObj;
    pObj = Mig_ManAppendObj( p );    
    Mig_ObjSetFaninLit( pObj, 0, iLit0 );
    return Mig_ObjId( pObj ) << 1;
}
static inline int Mig_ManAppendAnd( Mig_Man_t * p, int iLit0, int iLit1 )  
{ 
    Mig_Obj_t * pObj = Mig_ManAppendObj( p );
    assert( iLit0 != iLit1 );
    Mig_ObjSetFaninLit( pObj, 0, iLit0 < iLit1 ? iLit0 : iLit1 );
    Mig_ObjSetFaninLit( pObj, 1, iLit0 < iLit1 ? iLit1 : iLit0 );
    return Mig_ObjId( pObj ) << 1;
}
static inline int Mig_ManAppendXor( Mig_Man_t * p, int iLit0, int iLit1 )  
{ 
    Mig_Obj_t * pObj = Mig_ManAppendObj( p );
    assert( iLit0 != iLit1 );
    assert( !Abc_LitIsCompl(iLit0) && !Abc_LitIsCompl(iLit1) );
    Mig_ObjSetFaninLit( pObj, 0, iLit0 < iLit1 ? iLit1 : iLit0 );
    Mig_ObjSetFaninLit( pObj, 1, iLit0 < iLit1 ? iLit0 : iLit1 );
    return Mig_ObjId( pObj ) << 1;
}
static inline int Mig_ManAppendMux( Mig_Man_t * p, int iLit0, int iLit1, int iCtrl )  
{ 
    Mig_Obj_t * pObj = Mig_ManAppendObj( p );
    assert( iLit0 != iLit1 && iLit0 != iCtrl && iLit1 != iCtrl );
    assert( !Abc_LitIsCompl(iLit0) || !Abc_LitIsCompl(iLit1) );
    Mig_ObjSetFaninLit( pObj, 0, iLit0 < iLit1 ? iLit0 : iLit1 );
    Mig_ObjSetFaninLit( pObj, 1, iLit0 < iLit1 ? iLit1 : iLit0 );
    Mig_ObjSetFaninLit( pObj, 2, iLit0 < iLit1 ? iCtrl : Abc_LitNot(iCtrl) );
    return Mig_ObjId( pObj ) << 1;
}
static inline int Mig_ManAppendMaj( Mig_Man_t * p, int iLit0, int iLit1, int iLit2 )  
{ 
    Mig_Obj_t * pObj = Mig_ManAppendObj( p );
    assert( iLit0 != iLit1 && iLit0 != iLit2 && iLit1 != iLit2 );
    Mig_ObjSetFaninLit( pObj, 0, iLit0 < iLit1 ? iLit1 : iLit0 );
    Mig_ObjSetFaninLit( pObj, 1, iLit0 < iLit1 ? iLit0 : iLit1 );
    Mig_ObjSetFaninLit( pObj, 2, iLit2 );
    return Mig_ObjId( pObj ) << 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Mig_Man_t * Mig_ManStart()
{
    Mig_Man_t * p;
    assert( sizeof(Mig_Obj_t) >= 16 );
    assert( (1 << MIG_BASE) == MIG_MASK + 1 );
    p = ABC_CALLOC( Mig_Man_t, 1 );
    Vec_IntGrow( &p->vCis, 1024 );
    Vec_IntGrow( &p->vCos, 1024 );
    Mig_ManAppendObj( p ); // const0
    return p;
}
static inline void Mig_ManStop( Mig_Man_t * p )
{
    if ( 0 )
    printf( "Subject graph uses %d pages of %d objects with %d entries. Total memory = %.2f MB.\n", 
        Vec_PtrSize(&p->vPages), MIG_MASK + 1, p->nObjs,
        1.0 * Vec_PtrSize(&p->vPages) * (MIG_MASK + 1) * 16 / (1 << 20) );
    // attributes
    ABC_FREE( p->vTravIds.pArray );
    ABC_FREE( p->vCopies.pArray );
    ABC_FREE( p->vLevels.pArray );
    ABC_FREE( p->vRefs.pArray );
    ABC_FREE( p->vSibls.pArray );
    // pages
    Vec_PtrForEachEntry( Mig_Obj_t *, &p->vPages, p->pPage, p->iPage )
        --p->pPage, ABC_FREE( p->pPage );
    // objects
    ABC_FREE( p->vPages.pArray );
    ABC_FREE( p->vCis.pArray );
    ABC_FREE( p->vCos.pArray );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
static inline int Mig_ManMemory( Mig_Man_t * p )
{
    return Vec_PtrSize(&p->vPages) * (MIG_MASK + 1) * sizeof(Mig_Obj_t);
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mig_ManSetRefs( Mig_Man_t * p, int fSkipCos )
{
    Mig_Obj_t * pObj;
    int i, iFanin;
    // increment references
    Vec_IntFill( &p->vRefs, Mig_ManObjNum(p), 0 );
    Mig_ManForEachNode( p, pObj )
        Mig_ObjForEachFaninId( pObj, iFanin, i )
            Vec_IntAddToEntry( &p->vRefs, iFanin, 1 );
    if ( !fSkipCos )
    {
        // and CO references
        Mig_ManForEachCo( p, pObj, i )
            Vec_IntAddToEntry( &p->vRefs, Mig_ObjFaninId(pObj, 0), 1 );
        // check that internal nodes have fanins
        Mig_ManForEachNode( p, pObj )
            assert( Vec_IntEntry(&p->vRefs, Mig_ObjId(pObj)) > 0 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mig_ManSuppSize_rec( Mig_Obj_t * pObj )
{
    if ( pObj == NULL )
        return 0;
    if ( Mig_ObjIsTravIdCurrent(pObj) )
        return 0;
    Mig_ObjSetTravIdCurrent(pObj);
    if ( Mig_ObjIsCi(pObj) )
        return 1;
    assert( Mig_ObjIsNode(pObj) );
    return Mig_ManSuppSize_rec( Mig_ObjFanin0(pObj) ) +
           Mig_ManSuppSize_rec( Mig_ObjFanin1(pObj) ) +
           Mig_ManSuppSize_rec( Mig_ObjFanin2(pObj) );
}
int Mig_ManSuppSize2_rec( Mig_Man_t * p, int iObj )
{
    Mig_Obj_t * pObj;
    if ( iObj == MIG_NONE )
        return 0;
    if ( Mig_ObjIsTravIdCurrentId(p, iObj) )
        return 0;
    Mig_ObjSetTravIdCurrentId(p, iObj);
    pObj = Mig_ManObj( p, iObj );
    if ( Mig_ObjIsCi(pObj) )
        return 1;
    assert( Mig_ObjIsNode(pObj) );
    return Mig_ManSuppSize2_rec( p, Mig_ObjFaninId0(pObj) ) +
           Mig_ManSuppSize2_rec( p, Mig_ObjFaninId1(pObj) ) +
           Mig_ManSuppSize2_rec( p, Mig_ObjFaninId2(pObj) );
}
int Mig_ManSuppSizeOne( Mig_Obj_t * pObj )
{
    Mig_ObjIncrementTravId( pObj );
//    return Mig_ManSuppSize_rec( pObj );
    return Mig_ManSuppSize2_rec( Mig_ObjMan(pObj), Mig_ObjId(pObj) );
}
int Mig_ManSuppSizeTest( Mig_Man_t * p )
{
    Mig_Obj_t * pObj;
    int Counter = 0;
    abctime clk = Abc_Clock();
    Mig_ManForEachObj( p, pObj )
        if ( Mig_ObjIsNode(pObj) )
            Counter += (Mig_ManSuppSizeOne(pObj) <= 16);
    printf( "Nodes with small support %d (out of %d)\n", Counter, Mig_ManNodeNum(p) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Mig_ObjFanin0Copy( Gia_Obj_t * pObj ) { return Abc_LitNotCond( Gia_ObjFanin0(pObj)->Value, Gia_ObjFaninC0(pObj) );     }
static inline int Mig_ObjFanin1Copy( Gia_Obj_t * pObj ) { return Abc_LitNotCond( Gia_ObjFanin1(pObj)->Value, Gia_ObjFaninC1(pObj) );     }
Mig_Man_t * Mig_ManCreate( Gia_Man_t * p )
{
    Mig_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    // create the new manager
    pNew = Mig_ManStart();
    pNew->pName = Abc_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    // create objects
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            pObj->Value = Mig_ManAppendAnd( pNew, Mig_ObjFanin0Copy(pObj), Mig_ObjFanin1Copy(pObj) );
        else if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Mig_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Mig_ManAppendCo( pNew, Mig_ObjFanin0Copy(pObj) );
        else assert( 0 );
    }
    Mig_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}
void Mig_ManTest2( Gia_Man_t * pGia )
{
    extern int Gia_ManSuppSizeTest( Gia_Man_t * p );
    Mig_Man_t * p;
    Gia_ManSuppSizeTest( pGia );
    p = Mig_ManCreate( pGia );
    Mig_ManSuppSizeTest( p );
    Mig_ManStop( p );
}

/*
        // check special cases
        if ( fUseFunc )
        {
            pCut0 = p->pCuts[0][0];  pCut1 = p->pCuts[1][0];
            if ( pCut0->iFunc < 2 || pCut1->iFunc < 2 )
            {
                assert( Mig_ObjIsAnd(pObj) );
                if (  Abc_LitNotCond(pCut0->iFunc, Mig_ObjFaninC0(pObj)) == 0 ||
                      Abc_LitNotCond(pCut1->iFunc, Mig_ObjFaninC1(pObj)) == 0 ) // set the resulting cut to 0
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCreateZero( p, pObj );
                else if ( Abc_LitNotCond(pCut0->iFunc, Mig_ObjFaninC0(pObj)) == 1 ) // set the resulting set to be that of Fanin1
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCopySet( p, Mig_ObjFanin1(pObj), 0 );
                else if ( Abc_LitNotCond(pCut1->iFunc, Mig_ObjFaninC1(pObj)) == 1 ) // set the resulting set to be that of Fanin0
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCopySet( p, Mig_ObjFanin0(pObj), 0 );
                else assert( 0 );
                goto finish;
            }
        }
            // compute cut function
            if ( fUseFunc )
            {
                extern int Mpm_FuncCompute( void * p, int iDsd0, int iDsd1, Vec_Str_t * vShared, int * pPerm, int * pnLeaves );
                int nLeavesOld = p->pCutTemp->nLeaves;
                int nLeaves    = p->pCutTemp->nLeaves;
                iDsd0 = Abc_LitNotCond( pCut0->iFunc, Mig_ObjFaninC0(pObj) );
                iDsd1 = Abc_LitNotCond( pCut1->iFunc, Mig_ObjFaninC1(pObj) );
                if ( iDsd0 > iDsd1 )
                {
                    ABC_SWAP( int, iDsd0, iDsd1 );
                    ABC_SWAP( Mpm_Cut_t *, pCut0, pCut1 );
                }
                // compute functionality and filter cuts dominated by support-reduced cuts
                p->pCutTemp->iFunc = Mpm_FuncCompute( p->pManDsd, iDsd0, iDsd1, &p->vObjShared, p->pPerm, &nLeaves );
                Mpm_ObjUpdateCut( p->pCutTemp, p->pPerm, nLeaves );
                // consider filtering based on functionality
                if ( nLeaves == 0 ) // derived const cut
                {
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCreateZero( p, pObj );
                    goto finish;
                }
                if ( nLeaves == 1 ) // derived unit cut
                {
                    pFanin = Mig_ManObj( p->pMig, Abc_Lit2Var(p->pCutTemp->pLeaves[0]) );
                    Mig_ManObj(p, pObj)->hCutList = Mpm_CutCopySet( p, pFanin, Abc_LitIsCompl(p->pCutTemp->pLeaves[0]) );
                    goto finish;
                }
                if ( nLeaves < nLeavesOld ) // reduced support of the cut
                {
                    ArrTime = Mpm_CutGetArrTime( p, p->pCutTemp );
                    if ( ArrTime > pMapObj->mRequired )
                        continue;
                }
            }
*/


#define MPM_CUT_MAX      64
#define MPM_VAR_MAX      32  

#define MPM_UNIT_TIME     1
#define MPM_UNIT_AREA    20
#define MPM_UNIT_EDGE    50
#define MPM_UNIT_REFS   100


typedef struct Mpm_LibLut_t_ Mpm_LibLut_t;
struct Mpm_LibLut_t_
{
    char *           pName;                    // the name of the LUT library
    int              LutMax;                   // the maximum LUT size 
    int              fVarPinDelays;            // set to 1 if variable pin delays are specified
    int              pLutAreas[MPM_VAR_MAX+1]; // the areas of LUTs
    int              pLutDelays[MPM_VAR_MAX+1][MPM_VAR_MAX+1];// the delays of LUTs
};

typedef struct Mpm_Cut_t_ Mpm_Cut_t;  // 8 bytes + NLeaves * 4 bytes
struct Mpm_Cut_t_
{
    int              hNext;                    // next cut
    unsigned         iFunc     : 26;           // function
    unsigned         fUseless  :  1;           // internal flag
    unsigned         nLeaves   :  5;           // leaves
    int              pLeaves[0];               // leaves
};

typedef struct Mpm_Inf_t_ Mpm_Inf_t;  // 32 bytes
struct Mpm_Inf_t_
{
    int              hCut;                     // cut handle
    unsigned         nLeaves   :  6;           // the number of leaves
    unsigned         mCost     : 26;           // area cost of this cut
    int              mTime;                    // arrival time
    int              mArea;                    // area (flow)
    int              mEdge;                    // edge (flow)
    int              mAveRefs;                 // area references
    word             uSign;                    // cut signature
};

typedef struct Mpm_Uni_t_ Mpm_Uni_t;  // 48 bytes
struct Mpm_Uni_t_
{
    Mpm_Inf_t        Inf;                      // information
    unsigned         iFunc     : 26;           // function
    unsigned         fUseless  :  1;           // internal flag
    unsigned         nLeaves   :  5;           // leaves
    int              pLeaves[MPM_VAR_MAX];     // leaves
};

typedef struct Mpm_Man_t_ Mpm_Man_t;
struct Mpm_Man_t_
{
    Mig_Man_t *      pMig;                     // AIG manager
    // mapping parameters
    int              nLutSize;                 // LUT size
    int              nNumCuts;                 // cut count
    Mpm_LibLut_t *   pLibLut;                  // LUT library
    // mapping attributes  
    int              GloRequired;              // global arrival time
    int              GloArea;                  // total area
    int              GloEdge;                  // total edge
    int              fMainRun;                 // after preprocessing is finished
    // cut management
    Mmr_Step_t *     pManCuts;                 // cut memory
    // temporary cut storage
    int              nCutStore;                // number of cuts in storage
    Mpm_Uni_t *      pCutStore[MPM_CUT_MAX+1]; // storage for cuts
    Mpm_Uni_t        pCutUnits[MPM_CUT_MAX+1]; // cut info units
    Vec_Int_t        vFreeUnits;               // free cut info units
    Vec_Ptr_t *      vTemp;                    // storage for cuts
    // object presence
    unsigned char *  pObjPres;                 // object presence
    Mpm_Cut_t *      pCutTemp;                 // temporary cut
    Vec_Str_t        vObjShared;               // object presence
    // cut comparison
    int (* pCutCmp) (Mpm_Inf_t *, Mpm_Inf_t *);// procedure to compare cuts
    // fanin cuts/signatures
    int              nCuts[3];                 // fanin cut counts
    Mpm_Cut_t *      pCuts[3][MPM_CUT_MAX+1];  // fanin cuts
    word             pSigns[3][MPM_CUT_MAX+1]; // fanin cut signatures
    // functionality
//    Dsd_Man_t *      pManDsd;
    void *           pManDsd;
    int              pPerm[MPM_VAR_MAX]; 
    // mapping attributes
    Vec_Int_t        vCutBests;                // cut best
    Vec_Int_t        vCutLists;                // cut list
    Vec_Int_t        vMigRefs;                 // original references
    Vec_Int_t        vMapRefs;                 // exact mapping references
    Vec_Int_t        vEstRefs;                 // estimated mapping references
    Vec_Int_t        vRequireds;               // required time
    Vec_Int_t        vTimes;                   // arrival time
    Vec_Int_t        vAreas;                   // area
    Vec_Int_t        vEdges;                   // edge
    // statistics
    int              nCutsMerged;
    abctime          timeFanin;
    abctime          timeDerive;
    abctime          timeMerge;
    abctime          timeEval;
    abctime          timeCompare;
    abctime          timeStore;
    abctime          timeOther;
    abctime          timeTotal;
};

static inline int    Mpm_ObjCutBest( Mpm_Man_t * p, Mig_Obj_t * pObj )              { return Vec_IntEntry(&p->vCutBests, Mig_ObjId(pObj));            }
static inline void   Mpm_ObjSetCutBest( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )    { Vec_IntWriteEntry(&p->vCutBests, Mig_ObjId(pObj), i);           }

static inline int    Mpm_ObjCutList( Mpm_Man_t * p, Mig_Obj_t * pObj )              { return Vec_IntEntry(&p->vCutLists, Mig_ObjId(pObj));            }
static inline int *  Mpm_ObjCutListP( Mpm_Man_t * p, Mig_Obj_t * pObj )             { return Vec_IntEntryP(&p->vCutLists, Mig_ObjId(pObj));           }
static inline void   Mpm_ObjSetCutList( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )    { Vec_IntWriteEntry(&p->vCutLists, Mig_ObjId(pObj), i);           }

static inline void   Mpm_ManSetMigRefs( Mpm_Man_t * p )                             { assert( Vec_IntSize(&p->vMigRefs) == Vec_IntSize(&p->pMig->vRefs) ); memcpy( Vec_IntArray(&p->vMigRefs), Vec_IntArray(&p->pMig->vRefs), sizeof(int) * Mig_ManObjNum(p->pMig) ); }
static inline int    Mig_ObjMigRefNum( Mpm_Man_t * p, Mig_Obj_t * pObj )            { return Vec_IntEntry(&p->vMigRefs, Mig_ObjId(pObj));             }
static inline int    Mig_ObjMigRefDec( Mpm_Man_t * p, Mig_Obj_t * pObj )            { return Vec_IntAddToEntry(&p->vMigRefs, Mig_ObjId(pObj), -1);    }

static inline void   Mpm_ManCleanMapRefs( Mpm_Man_t * p )                           { Vec_IntFill( &p->vMapRefs, Mig_ManObjNum(p->pMig), 0 );         }
static inline int    Mpm_ObjMapRef( Mpm_Man_t * p, Mig_Obj_t * pObj )               { return Vec_IntEntry(&p->vMapRefs, Mig_ObjId(pObj));             }
static inline void   Mpm_ObjSetMapRef( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )     { Vec_IntWriteEntry(&p->vMapRefs, Mig_ObjId(pObj), i);            }
 
static inline int    Mpm_ObjEstRef( Mpm_Man_t * p, Mig_Obj_t * pObj )               { return Vec_IntEntry(&p->vEstRefs, Mig_ObjId(pObj));             }
static inline void   Mpm_ObjSetEstRef( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )     { Vec_IntWriteEntry(&p->vEstRefs, Mig_ObjId(pObj), i);            }

static inline void   Mpm_ManCleanRequired( Mpm_Man_t * p )                          { Vec_IntFill(&p->vRequireds,Mig_ManObjNum(p->pMig),ABC_INFINITY);}
static inline int    Mpm_ObjRequired( Mpm_Man_t * p, Mig_Obj_t * pObj )             { return Vec_IntEntry(&p->vRequireds, Mig_ObjId(pObj));           }
static inline void   Mpm_ObjSetRequired( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )   { Vec_IntWriteEntry(&p->vRequireds, Mig_ObjId(pObj), i);          }

static inline int    Mpm_ObjTime( Mpm_Man_t * p, Mig_Obj_t * pObj )                 { return Vec_IntEntry(&p->vTimes, Mig_ObjId(pObj));               }
static inline void   Mpm_ObjSetTime( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )       { Vec_IntWriteEntry(&p->vTimes, Mig_ObjId(pObj), i);              }

static inline int    Mpm_ObjArea( Mpm_Man_t * p, Mig_Obj_t * pObj )                 { return Vec_IntEntry(&p->vAreas, Mig_ObjId(pObj));               }
static inline void   Mpm_ObjSetArea( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )       { Vec_IntWriteEntry(&p->vAreas, Mig_ObjId(pObj), i);              }

static inline int    Mpm_ObjEdge( Mpm_Man_t * p, Mig_Obj_t * pObj )                 { return Vec_IntEntry(&p->vEdges, Mig_ObjId(pObj));               }
static inline void   Mpm_ObjSetEdge( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )       { Vec_IntWriteEntry(&p->vEdges, Mig_ObjId(pObj), i);              }


// iterators over object cuts
#define Mpm_ObjForEachCut( p, pObj, hCut, pCut )                         \
    for ( hCut = Mpm_ObjCutList(p, pObj); hCut && (pCut = Mpm_CutFetch(p, hCut)); hCut = pCut->hNext )
#define Mpm_ObjForEachCutSafe( p, pObj, hCut, pCut, hNext )              \
    for ( hCut = Mpm_ObjCutList(p, pObj); hCut && (pCut = Mpm_CutFetch(p, hCut)) && ((hNext = pCut->hNext), 1); hCut = hNext )

// iterators over cut leaves
#define Mpm_CutForEachLeafId( pCut, iLeafId, i )                         \
    for ( i = 0; i < (int)pCut->nLeaves && ((iLeafId = Abc_Lit2Var(pCut->pLeaves[i])), 1); i++ )
#define Mpm_CutForEachLeaf( p, pCut, pLeaf, i )                          \
    for ( i = 0; i < (int)pCut->nLeaves && (pLeaf = Mig_ManObj(p, Abc_Lit2Var(pCut->pLeaves[i]))); i++ )

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mpm_LibLut_t * Mpm_LibLutSetSimple( int nLutSize )
{
    Mpm_LibLut_t * pLib;
    int i, k;
    assert( nLutSize < MPM_VAR_MAX );
    pLib = ABC_CALLOC( Mpm_LibLut_t, 1 );
    pLib->LutMax = nLutSize;
    for ( i = 1; i <= pLib->LutMax; i++ )
    {
        pLib->pLutAreas[i] = MPM_UNIT_AREA;
        for ( k = 0; k < i; k++ )
            pLib->pLutDelays[i][k] = MPM_UNIT_TIME;
    }
    return pLib;
}
void Mpm_LibLutFree( Mpm_LibLut_t * pLib )
{
    if ( pLib == NULL )
        return;
    ABC_FREE( pLib->pName );
    ABC_FREE( pLib );
}

/**Function*************************************************************

  Synopsis    [Cut manipulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Mpm_CutWordNum( int nLeaves )  { return (sizeof(Mpm_Cut_t)/sizeof(int) + nLeaves + 1) >> 1; }
static inline int Mpm_CutAlloc( Mpm_Man_t * p, int nLeaves, Mpm_Cut_t ** ppCut )  
{ 
    int hHandle = Mmr_StepFetch( p->pManCuts, Mpm_CutWordNum(nLeaves) );
    *ppCut      = (Mpm_Cut_t *)Mmr_StepEntry( p->pManCuts, hHandle );
    (*ppCut)->nLeaves  = nLeaves;
    (*ppCut)->hNext    = 0;
    (*ppCut)->fUseless = 0;
    return hHandle;
}
static inline Mpm_Cut_t * Mpm_CutFetch( Mpm_Man_t * p, int h )  
{ 
    Mpm_Cut_t * pCut = (Mpm_Cut_t *)Mmr_StepEntry( p->pManCuts, h );
    assert( Mpm_CutWordNum(pCut->nLeaves) == (h & p->pManCuts->uMask) );
    return pCut;
}
static inline Mpm_Cut_t * Mpm_ObjCutBestP( Mpm_Man_t * p, Mig_Obj_t * pObj )  
{ 
    return Mpm_CutFetch( p, Mpm_ObjCutBest(p, pObj) );
}
static inline int Mpm_CutCreateZero( Mpm_Man_t * p )  
{ 
    Mpm_Cut_t * pCut;
    int hCut = Mpm_CutAlloc( p, 0, &pCut );
    pCut->iFunc      = 0; // const0
    return hCut;
}
static inline int Mpm_CutCreateUnit( Mpm_Man_t * p, int Id )  
{ 
    Mpm_Cut_t * pCut;
    int hCut = Mpm_CutAlloc( p, 1, &pCut );
    pCut->iFunc      = 2; // var
    pCut->pLeaves[0] = Abc_Var2Lit( Id, 0 );
    return hCut;
}
static inline int Mpm_CutCreate( Mpm_Man_t * p, int * pLeaves, int nLeaves, int fUseless, Mpm_Cut_t ** ppCut )  
{ 
    int hCutNew = Mpm_CutAlloc( p, nLeaves, ppCut );
    (*ppCut)->fUseless = fUseless;
    (*ppCut)->nLeaves  = nLeaves;
    memcpy( (*ppCut)->pLeaves, pLeaves, sizeof(int) * nLeaves );
    return hCutNew;
}
static inline int Mpm_CutDup( Mpm_Man_t * p, Mpm_Cut_t * pCut, int fCompl )  
{ 
    Mpm_Cut_t * pCutNew;
    int hCutNew = Mpm_CutAlloc( p, pCut->nLeaves, &pCutNew );
    pCutNew->iFunc    = Abc_LitNotCond( pCut->iFunc, fCompl );
    pCutNew->fUseless = pCut->fUseless;
    pCutNew->nLeaves  = pCut->nLeaves;
    memcpy( pCutNew->pLeaves, pCut->pLeaves, sizeof(int) * pCut->nLeaves );
    return hCutNew;
}
static inline int Mpm_CutCopySet( Mpm_Man_t * p, Mig_Obj_t * pObj, int fCompl )  
{
    Mpm_Cut_t * pCut;
    int hCut, iList = 0, * pList = &iList;
    Mpm_ObjForEachCut( p, pObj, hCut, pCut )
    {
        *pList = Mpm_CutDup( p, pCut, fCompl );
        pList = &Mpm_CutFetch( p, *pList )->hNext;
    }
    *pList = 0;
    return iList;
}
/*
static inline void Mpm_CutRef( Mpm_Man_t * p, int * pLeaves, int nLeaves )  
{
    int i;
    for ( i = 0; i < nLeaves; i++ )
        Mig_ManObj( p->pMig, Abc_Lit2Var(pLeaves[i]) )->nMapRefs++;
}
static inline void Mpm_CutDeref( Mpm_Man_t * p, int * pLeaves, int nLeaves )  
{
    int i;
    for ( i = 0; i < nLeaves; i++ )
        Mig_ManObj( p->pMig, Abc_Lit2Var(pLeaves[i]) )->nMapRefs--;
}
*/
static inline void Mpm_CutPrint( int * pLeaves, int nLeaves )  
{ 
    int i;
    printf( "%d : { ", nLeaves );
    for ( i = 0; i < nLeaves; i++ )
        printf( "%d ", pLeaves[i] );
    printf( "}\n" );
}
static inline void Mpm_CutPrintAll( Mpm_Man_t * p )  
{ 
    int i;
    for ( i = 0; i < p->nCutStore; i++ )
    {
        printf( "%2d : ", i );
        Mpm_CutPrint( p->pCutStore[i]->pLeaves, p->pCutStore[i]->nLeaves );
    }
}

/**Function*************************************************************

  Synopsis    [Recursively derives the local AIG for the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Mpm_CutDataInt( Mpm_Cut_t * pCut )                    { return pCut->hNext;  }
static inline void     Mpm_CutSetDataInt( Mpm_Cut_t * pCut, unsigned Data )  { pCut->hNext = Data;  }
int Mpm_ManNodeIfToGia_rec( Gia_Man_t * pNew, Mpm_Man_t * pMan, Mig_Obj_t * pObj, Vec_Ptr_t * vVisited, int fHash )
{
    Mig_Obj_t * pTemp;
    Mpm_Cut_t * pCut;
    int iFunc, iFunc0, iFunc1;
    // get the best cut
    pCut = Mpm_ObjCutBestP( pMan, pObj );
    // if the cut is visited, return the result
    if ( Mpm_CutDataInt(pCut) )
        return Mpm_CutDataInt(pCut);
    // mark the node as visited
    Vec_PtrPush( vVisited, pCut );
    // insert the worst case
    Mpm_CutSetDataInt( pCut, ~0 );
    // skip in case of primary input
    if ( Mig_ObjIsCi(pObj) )
        return Mpm_CutDataInt(pCut);
    // compute the functions of the children
    for ( pTemp = pObj; pTemp; pTemp = Mig_ObjSibl(pTemp) )
    {
        iFunc0 = Mpm_ManNodeIfToGia_rec( pNew, pMan, Mig_ObjFanin0(pTemp), vVisited, fHash );
        if ( iFunc0 == ~0 )
            continue;
        iFunc1 = Mpm_ManNodeIfToGia_rec( pNew, pMan, Mig_ObjFanin1(pTemp), vVisited, fHash );
        if ( iFunc1 == ~0 )
            continue;
        // both branches are solved
        if ( fHash )
            iFunc = Gia_ManHashAnd( pNew, Abc_LitNotCond(iFunc0, Mig_ObjFaninC0(pTemp)), Abc_LitNotCond(iFunc1, Mig_ObjFaninC1(pTemp)) ); 
        else
            iFunc = Gia_ManAppendAnd( pNew, Abc_LitNotCond(iFunc0, Mig_ObjFaninC0(pTemp)), Abc_LitNotCond(iFunc1, Mig_ObjFaninC1(pTemp)) ); 
        if ( Mig_ObjPhase(pTemp) != Mig_ObjPhase(pObj) )
            iFunc = Abc_LitNot(iFunc);
        Mpm_CutSetDataInt( pCut, iFunc );
        break;
    }
    return Mpm_CutDataInt(pCut);
}
int Mpm_ManNodeIfToGia( Gia_Man_t * pNew, Mpm_Man_t * pMan, Mig_Obj_t * pObj, Vec_Int_t * vLeaves, int fHash )
{
    Mpm_Cut_t * pCut;
    Mig_Obj_t * pFanin;
    int i, iRes;
    // get the best cut
    pCut = Mpm_ObjCutBestP( pMan, pObj );
    assert( pCut->nLeaves > 1 );
    // set the leaf variables
    Mpm_CutForEachLeaf( pMan->pMig, pCut, pFanin, i )
        Mpm_CutSetDataInt( Mpm_ObjCutBestP(pMan, pFanin), Vec_IntEntry(vLeaves, i) );
    // recursively compute the function while collecting visited cuts
    Vec_PtrClear( pMan->vTemp );
    iRes = Mpm_ManNodeIfToGia_rec( pNew, pMan, pObj, pMan->vTemp, fHash ); 
    if ( iRes == ~0 )
    {
        Abc_Print( -1, "Mpm_ManNodeIfToGia(): Computing local AIG has failed.\n" );
        return ~0;
    }
    // clean the cuts
    Mpm_CutForEachLeaf( pMan->pMig, pCut, pFanin, i )
        Mpm_CutSetDataInt( Mpm_ObjCutBestP(pMan, pFanin), 0 );
    Vec_PtrForEachEntry( Mpm_Cut_t *, pMan->vTemp, pCut, i )
        Mpm_CutSetDataInt( pCut, 0 );
    return iRes;
}
Gia_Man_t * Mpm_ManFromIfLogic( Mpm_Man_t * pMan )
{
    Gia_Man_t * pNew;
    Mpm_Cut_t * pCutBest;
    Mig_Obj_t * pObj, * pFanin;
    Vec_Int_t * vMapping, * vMapping2, * vPacking = NULL;
    Vec_Int_t * vLeaves, * vLeaves2, * vCover;
    int i, k, Entry, iLitNew;
//    assert( !pMan->pPars->fDeriveLuts || pMan->pPars->fTruth );
    // start mapping and packing
    vMapping  = Vec_IntStart( Mig_ManObjNum(pMan->pMig) );
    vMapping2 = Vec_IntStart( 1 );
    if ( 0 ) // pMan->pPars->fDeriveLuts && pMan->pPars->pLutStruct )
    {
        vPacking = Vec_IntAlloc( 1000 );
        Vec_IntPush( vPacking, 0 );
    }
    // create new manager
    pNew = Gia_ManStart( Mig_ManObjNum(pMan->pMig) );
    // iterate through nodes used in the mapping
    vCover   = Vec_IntAlloc( 1 << 16 );
    vLeaves  = Vec_IntAlloc( 16 );
    vLeaves2 = Vec_IntAlloc( 16 );
    Mig_ManCleanCopy( pMan->pMig );
    Mig_ManForEachObj( pMan->pMig, pObj )
    {
        if ( !Mpm_ObjMapRef(pMan, pObj) && !Mig_ObjIsTerm(pObj) )
            continue;
        if ( Mig_ObjIsNode(pObj) )
        {
            // collect leaves of the best cut
            Vec_IntClear( vLeaves );
            pCutBest = Mpm_ObjCutBestP( pMan, pObj );
            Mpm_CutForEachLeaf( pMan->pMig, pCutBest, pFanin, k )
                Vec_IntPush( vLeaves, Mig_ObjCopy(pFanin) );
            // perform one of the two types of mapping: with and without structures
            iLitNew = Mpm_ManNodeIfToGia( pNew, pMan, pObj, vLeaves, 0 );
            // write mapping
            Vec_IntSetEntry( vMapping, Abc_Lit2Var(iLitNew), Vec_IntSize(vMapping2) );
            Vec_IntPush( vMapping2, Vec_IntSize(vLeaves) );
            Vec_IntForEachEntry( vLeaves, Entry, k )
                assert( Abc_Lit2Var(Entry) < Abc_Lit2Var(iLitNew) );
            Vec_IntForEachEntry( vLeaves, Entry, k )
                Vec_IntPush( vMapping2, Abc_Lit2Var(Entry)  );
            Vec_IntPush( vMapping2, Abc_Lit2Var(iLitNew) );
        }
        else if ( Mig_ObjIsCi(pObj) )
            iLitNew = Gia_ManAppendCi(pNew);
        else if ( Mig_ObjIsCo(pObj) )
            iLitNew = Gia_ManAppendCo( pNew, Abc_LitNotCond(Mig_ObjCopy(Mig_ObjFanin0(pObj)), Mig_ObjFaninC0(pObj)) );
        else if ( Mig_ObjIsConst0(pObj) )
        {
            iLitNew = 0;
            // create const LUT
            Vec_IntWriteEntry( vMapping, 0, Vec_IntSize(vMapping2) );
            Vec_IntPush( vMapping2, 0 );
            Vec_IntPush( vMapping2, 0 );
        }
        else assert( 0 );
        Mig_ObjSetCopy( pObj, iLitNew );
    }
    Vec_IntFree( vCover );
    Vec_IntFree( vLeaves );
    Vec_IntFree( vLeaves2 );
//    printf( "Mapping array size:  IfMan = %d. Gia = %d. Increase = %.2f\n", 
//        Mig_ManObjNum(pMan), Gia_ManObjNum(pNew), 1.0 * Gia_ManObjNum(pNew) / Mig_ManObjNum(pMan) );
    // finish mapping 
    if ( Vec_IntSize(vMapping) > Gia_ManObjNum(pNew) )
        Vec_IntShrink( vMapping, Gia_ManObjNum(pNew) );
    else
        Vec_IntFillExtra( vMapping, Gia_ManObjNum(pNew), 0 );
    assert( Vec_IntSize(vMapping) == Gia_ManObjNum(pNew) );
    Vec_IntForEachEntry( vMapping, Entry, i )
        if ( Entry > 0 )
            Vec_IntAddToEntry( vMapping, i, Gia_ManObjNum(pNew) );
    Vec_IntAppend( vMapping, vMapping2 );
    Vec_IntFree( vMapping2 );
    // attach mapping and packing
    assert( pNew->vMapping == NULL );
    assert( pNew->vPacking == NULL );
    pNew->vMapping = vMapping;
    pNew->vPacking = vPacking;
    // verify that COs have mapping
    {
        Gia_Obj_t * pObj;
        Gia_ManForEachCo( pNew, pObj, i )
           assert( !Gia_ObjIsAnd(Gia_ObjFanin0(pObj)) || Gia_ObjIsLut(pNew, Gia_ObjFaninId0p(pNew, pObj)) );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Mpm_Man_t * Mpm_ManStart( Mig_Man_t * pMig, Mpm_LibLut_t * pLib, int nNumCuts )
{
    Mpm_Man_t * p;
    assert( sizeof(Mpm_Inf_t) % sizeof(word) == 0 );      // aligned info to word boundary
    assert( Mpm_CutWordNum(32) < 32 ); // using 5 bits for word count
    assert( nNumCuts <= MPM_CUT_MAX );
    Mig_ManSetRefs( pMig, 1 );
    // alloc
    p = ABC_CALLOC( Mpm_Man_t, 1 );
    p->pMig      = pMig;
    p->pLibLut   = pLib;
    p->nLutSize  = pLib->LutMax;
    p->nNumCuts  = nNumCuts;
    p->timeTotal = Abc_Clock();
    // cuts
    p->pManCuts  = Mmr_StepStart( 13, Abc_Base2Log(Mpm_CutWordNum(p->nLutSize) + 1) );
    Vec_IntGrow( &p->vFreeUnits, nNumCuts + 1 );
    p->pObjPres  = ABC_FALLOC( unsigned char, Mig_ManObjNum(pMig) );
    p->pCutTemp  = (Mpm_Cut_t *)ABC_CALLOC( word, Mpm_CutWordNum(p->nLutSize) );
    Vec_StrGrow( &p->vObjShared, 32 );
    p->vTemp     = Vec_PtrAlloc( 1000 );
    // mapping attributes
    Vec_IntFill( &p->vCutBests, Mig_ManObjNum(pMig), 0 );
    Vec_IntFill( &p->vCutLists, Mig_ManObjNum(pMig), 0 );
    Vec_IntFill( &p->vMigRefs, Mig_ManObjNum(pMig), 0 );
    Vec_IntFill( &p->vMapRefs, Mig_ManObjNum(pMig), 0 );
    Vec_IntFill( &p->vEstRefs, Mig_ManObjNum(pMig), 0 );
    Vec_IntFill( &p->vRequireds, Mig_ManObjNum(pMig), ABC_INFINITY );
    Vec_IntFill( &p->vTimes, Mig_ManObjNum(pMig), 0 );
    Vec_IntFill( &p->vAreas, Mig_ManObjNum(pMig), 0 );
    Vec_IntFill( &p->vEdges, Mig_ManObjNum(pMig), 0 );
    // start DSD manager
    p->pManDsd   = NULL;
    pMig->pMan   = p;
    return p;
}
static inline void Mpm_ManStop( Mpm_Man_t * p )
{
    Vec_PtrFree( p->vTemp );
    Mmr_StepStop( p->pManCuts );
    ABC_FREE( p->vFreeUnits.pArray );
    ABC_FREE( p->vObjShared.pArray );
    ABC_FREE( p->pCutTemp );
    ABC_FREE( p->pObjPres );
    // mapping attributes
    ABC_FREE( p->vCutBests.pArray );
    ABC_FREE( p->vCutLists.pArray );
    ABC_FREE( p->vMigRefs.pArray );
    ABC_FREE( p->vMapRefs.pArray );
    ABC_FREE( p->vEstRefs.pArray );
    ABC_FREE( p->vRequireds.pArray );
    ABC_FREE( p->vTimes.pArray );
    ABC_FREE( p->vAreas.pArray );
    ABC_FREE( p->vEdges.pArray );
    ABC_FREE( p );
}
static inline void Mpm_ManPrintStatsInit( Mpm_Man_t * p )
{
    printf( "K = %d.  C = %d.  Cands = %d.  Choices = %d.\n", 
        p->nLutSize, p->nNumCuts, Mig_ManCiNum(p->pMig) + Mig_ManNodeNum(p->pMig), 0 );
}
static inline void Mpm_ManPrintStats( Mpm_Man_t * p )
{
    printf( "Memory usage:  Mig = %.2f MB  Map = %.2f MB  Cut = %.2f MB    Total = %.2f MB.  ", 
        1.0 * Mig_ManObjNum(p->pMig) * sizeof(Mig_Obj_t) / (1 << 20), 
        1.0 * Mig_ManObjNum(p->pMig) * 48 / (1 << 20), 
        1.0 * Mmr_StepMemory(p->pManCuts) / (1 << 17), 
        1.0 * Mig_ManObjNum(p->pMig) * sizeof(Mig_Obj_t) / (1 << 20) + 
        1.0 * Mig_ManObjNum(p->pMig) * 48 / (1 << 20) +
        1.0 * Mmr_StepMemory(p->pManCuts) / (1 << 17) );

#ifdef MIG_RUNTIME    
    printf( "\n" );
    p->timeTotal = Abc_Clock() - p->timeTotal;
    p->timeOther = p->timeTotal - (p->timeFanin + p->timeDerive);

    Abc_Print( 1, "Runtime breakdown:\n" );
    ABC_PRTP( "Precomputing fanin info    ", p->timeFanin  , p->timeTotal );
    ABC_PRTP( "Complete cut computation   ", p->timeDerive , p->timeTotal );
    ABC_PRTP( "- Merging cuts             ", p->timeMerge  , p->timeTotal );
    ABC_PRTP( "- Evaluting cut parameters ", p->timeEval   , p->timeTotal );
    ABC_PRTP( "- Checking cut containment ", p->timeCompare, p->timeTotal );
    ABC_PRTP( "- Adding cuts to storage   ", p->timeStore  , p->timeTotal );
    ABC_PRTP( "Other                      ", p->timeOther  , p->timeTotal );
    ABC_PRTP( "TOTAL                      ", p->timeTotal  , p->timeTotal );
#else
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->timeTotal );
#endif
}


/**Function*************************************************************

  Synopsis    [Cut merging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Mig_ManObjPresClean( Mpm_Man_t * p )                
{ 
    int i; 
    for ( i = 0; i < (int)p->pCutTemp->nLeaves; i++ )
        p->pObjPres[Abc_Lit2Var(p->pCutTemp->pLeaves[i])] = (unsigned char)0xFF; 
//    for ( i = 0; i < Mig_ManObjNum(p->pMig); i++ )
//        assert( p->pObjPres[i] == (unsigned char)0xFF );
    Vec_StrClear(&p->vObjShared);                      
}
static inline int Mig_ManObjPres( Mpm_Man_t * p, int k, int iLit ) 
{ 
    int iObj = Abc_Lit2Var(iLit);
//    assert( iLit > 1 && iLit < 2 * Mig_ManObjNum(p->pMig) );
    if ( p->pObjPres[iObj] != (unsigned char)0xFF )
        return 1;
    if ( (int)p->pCutTemp->nLeaves == p->nLutSize )
        return 0;
    p->pObjPres[iObj] = p->pCutTemp->nLeaves;        
    p->pCutTemp->pLeaves[p->pCutTemp->nLeaves++] = iLit;
    return 1;
}
static inline int Mpm_ObjDeriveCut( Mpm_Man_t * p, Mpm_Cut_t ** pCuts, Mpm_Cut_t * pCut )
{
    int i, c;
    pCut->nLeaves = 0;
    for ( c = 0; pCuts[c] && c < 3; c++ )
        for ( i = 0; i < (int)pCuts[c]->nLeaves; i++ )
            if ( !Mig_ManObjPres( p, i, pCuts[c]->pLeaves[i] ) )
                return 0;
    pCut->hNext    = 0;
    pCut->iFunc    = 0;  pCut->iFunc = ~pCut->iFunc;
    pCut->fUseless = 0;
    assert( pCut->nLeaves > 0 );
    p->nCutsMerged++;
    return 1;
}

static inline int Mpm_ManSetIsSmaller( Mpm_Man_t * p, int * pLits, int nLits ) // check if pCut is contained in the current one (p->pCutTemp)
{
    int i, Index;
    for ( i = 0; i < nLits; i++ )
    {
        Index = (int)p->pObjPres[Abc_Lit2Var(pLits[i])];
        if ( Index == 0xFF )
            return 0;
        assert( Index < (int)p->pCutTemp->nLeaves );
    }
    return 1;
}
static inline int Mpm_ManSetIsBigger( Mpm_Man_t * p, int * pLits, int nLits ) // check if pCut contains the current one (p->pCutTemp)
{
    int i, Index;
    unsigned uMask = 0;
    for ( i = 0; i < nLits; i++ )
    {
        Index = (int)p->pObjPres[Abc_Lit2Var(pLits[i])];
        if ( Index == 0xFF )
            continue;
        assert( Index < (int)p->pCutTemp->nLeaves );
        uMask |= (1 << Index);
    }
    return uMask == ~(~(unsigned)0 << p->pCutTemp->nLeaves);
}
static inline int Mpm_ManSetIsDisjoint( Mpm_Man_t * p, Mpm_Cut_t * pCut ) // check if pCut is disjoint
{
    int i;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        if ( (int)p->pObjPres[Abc_Lit2Var(pCut->pLeaves[i])] != 0xFF )
            return 0;
    return 1;
}


/**Function*************************************************************

  Synopsis    [Cut attibutes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Mpm_CutGetSign( Mpm_Cut_t * pCut )  
{
    int i, iLeaf;
    word uSign = 0;
    Mpm_CutForEachLeafId( pCut, iLeaf, i )
        uSign |= ((word)1 << (iLeaf & 0x3F));
    return uSign;
}
static inline int Mpm_CutGetArrTime( Mpm_Man_t * p, Mpm_Cut_t * pCut )  
{
    int * pmTimes = Vec_IntArray( &p->vTimes );
    int * pDelays = p->pLibLut->pLutDelays[pCut->nLeaves];
    int i, iLeaf, ArrTime = 0;
    Mpm_CutForEachLeafId( pCut, iLeaf, i )
        ArrTime = Abc_MaxInt( ArrTime, pmTimes[iLeaf] + pDelays[i] );
    return ArrTime;
}
static inline void Mpm_CutSetupInfo( Mpm_Man_t * p, Mpm_Cut_t * pCut, int ArrTime, Mpm_Inf_t * pInfo )  
{
    int * pMigRefs = Vec_IntArray( &p->vMigRefs );
    int * pMapRefs = Vec_IntArray( &p->vMapRefs );
    int * pEstRefs = Vec_IntArray( &p->vEstRefs );
    int * pmArea   = Vec_IntArray( &p->vAreas );
    int * pmEdge   = Vec_IntArray( &p->vEdges );
    int i, iLeaf;
    memset( pInfo, 0, sizeof(Mpm_Inf_t) );
    pInfo->nLeaves = pCut->nLeaves;
    pInfo->mTime   = ArrTime;
    pInfo->mArea   = p->pLibLut->pLutAreas[pCut->nLeaves];
    pInfo->mEdge   = MPM_UNIT_EDGE * pCut->nLeaves;
    Mpm_CutForEachLeafId( pCut, iLeaf, i )
    {
        if ( p->fMainRun && pMapRefs[iLeaf] == 0 ) // not used in the mapping
        {
            pInfo->mArea += pmArea[iLeaf];
            pInfo->mEdge += pmEdge[iLeaf];
        }
        else
        {
            assert( pEstRefs[iLeaf] > 0 );
            pInfo->mArea += MPM_UNIT_REFS * pmArea[iLeaf] / pEstRefs[iLeaf];
            pInfo->mEdge += MPM_UNIT_REFS * pmEdge[iLeaf] / pEstRefs[iLeaf];
            pInfo->mAveRefs += p->fMainRun ? pMapRefs[iLeaf] : pMigRefs[iLeaf];
        }
        pInfo->uSign |= ((word)1 << (iLeaf & 0x3F));
    }
    pInfo->mAveRefs = pInfo->mAveRefs * MPM_UNIT_EDGE / pCut->nLeaves;
}

/**Function*************************************************************

  Synopsis    [Cut translation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Mpm_Uni_t * Mpm_CutToUnit( Mpm_Man_t * p, Mpm_Cut_t * pCut )  
{
    Mpm_Uni_t * pUnit = p->pCutUnits + Vec_IntPop(&p->vFreeUnits);
    pUnit->iFunc    = pCut->iFunc;
    pUnit->fUseless = pCut->fUseless;
    pUnit->nLeaves  = pCut->nLeaves;
    memcpy( pUnit->pLeaves, pCut->pLeaves, sizeof(int) * pCut->nLeaves );
    return pUnit;
}
static inline void Mpm_UnitRecycle( Mpm_Man_t * p, Mpm_Uni_t * pUnit )  
{
    Vec_IntPush( &p->vFreeUnits, pUnit - p->pCutUnits );
}
static inline void Mpm_ManPrepareCutStore( Mpm_Man_t * p )  
{
    int i;
    p->nCutStore = 0;
    Vec_IntClear( &p->vFreeUnits );
    for ( i = p->nNumCuts; i >= 0; i-- )
        Vec_IntPush( &p->vFreeUnits, i );
    assert( Vec_IntSize(&p->vFreeUnits) == p->nNumCuts + 1 );
}
// compares cut against those present in the store
int Mpm_ObjAddCutToStore( Mpm_Man_t * p, Mpm_Cut_t * pCut, int ArrTime )
{
    int fEnableContainment = 1;
    Mpm_Uni_t * pUnit, * pUnitNew;
    int k, iPivot, last;
    // create new unit
#ifdef MIG_RUNTIME
    abctime clk;
clk = Abc_Clock();
#endif
    pUnitNew = Mpm_CutToUnit( p, pCut );
    Mpm_CutSetupInfo( p, pCut, ArrTime, &pUnitNew->Inf );
#ifdef MIG_RUNTIME
p->timeEval += Abc_Clock() - clk;
#endif
    // special case when the cut store is empty
    if ( p->nCutStore == 0 )
    {
        p->pCutStore[p->nCutStore++] = pUnitNew;
        return 1;
    }
    // special case when the cut store is full and last cut is better than new cut
    if ( p->nCutStore == p->nNumCuts-1 && p->pCutCmp(&pUnitNew->Inf, &p->pCutStore[p->nCutStore-1]->Inf) > 0 )
    {
        Mpm_UnitRecycle( p, pUnitNew );
        return 0;
    }
    // find place of the given cut in the store
    assert( p->nCutStore <= p->nNumCuts );
    for ( iPivot = p->nCutStore - 1; iPivot >= 0; iPivot-- )
        if ( p->pCutCmp(&pUnitNew->Inf, &p->pCutStore[iPivot]->Inf) > 0 ) // iPivot-th cut is better than new cut
            break;

    if ( fEnableContainment )
    {
#ifdef MIG_RUNTIME
clk = Abc_Clock();
#endif
    // filter this cut using other cuts
    for ( k = 0; k <= iPivot; k++ )
    {
        pUnit = p->pCutStore[k];
        if ( pUnitNew->Inf.nLeaves >= pUnit->Inf.nLeaves && 
            (pUnitNew->Inf.uSign & pUnit->Inf.uSign) == pUnit->Inf.uSign && 
             Mpm_ManSetIsSmaller(p, pUnit->pLeaves, pUnit->nLeaves) )
        {
//            printf( "\n" );
//            Mpm_CutPrint( pUnitNew->pLeaves, pUnitNew->nLeaves );
//            Mpm_CutPrint( pUnit->pLeaves, pUnit->nLeaves );
            Mpm_UnitRecycle( p, pUnitNew );
#ifdef MIG_RUNTIME
p->timeCompare += Abc_Clock() - clk;
#endif
            return 0;
        }
    }
    }

    // special case when the best cut is useless while the new cut is not
    if ( p->pCutStore[0]->fUseless && !pUnitNew->fUseless )
        iPivot = -1;
    // insert this cut at location iPivot
    iPivot++;
    for ( k = p->nCutStore++; k > iPivot; k-- )
        p->pCutStore[k] = p->pCutStore[k-1];
    p->pCutStore[iPivot] = pUnitNew;

    if ( fEnableContainment )
    {
    // filter other cuts using this cut
    for ( k = last = iPivot+1; k < p->nCutStore; k++ )
    {
        pUnit = p->pCutStore[k];
        if ( pUnitNew->Inf.nLeaves <= pUnit->Inf.nLeaves && 
            (pUnitNew->Inf.uSign & pUnit->Inf.uSign) == pUnitNew->Inf.uSign && 
             Mpm_ManSetIsBigger(p, pUnit->pLeaves, pUnit->nLeaves) )
        {
//            printf( "\n" );
//            Mpm_CutPrint( pUnitNew->pLeaves, pUnitNew->nLeaves );
//            Mpm_CutPrint( pUnit->pLeaves, pUnit->nLeaves );
            Mpm_UnitRecycle( p, pUnit );
            continue;
        }
        p->pCutStore[last++] = p->pCutStore[k];
    }
    p->nCutStore = last;
#ifdef MIG_RUNTIME
p->timeCompare += Abc_Clock() - clk;
#endif
    }

    // remove the last cut if too many
    if ( p->nCutStore == p->nNumCuts )
        Mpm_UnitRecycle( p, p->pCutStore[--p->nCutStore] );
    assert( p->nCutStore < p->nNumCuts );
    return 1;
}
// create storage from cuts at the node
void Mpm_ObjAddChoiceCutsToStore( Mpm_Man_t * p, Mig_Obj_t * pObj, int ReqTime )
{
    Mpm_Cut_t * pCut;
    int hCut, hNext, ArrTime;
    assert( p->nCutStore == 0 );
    assert( Vec_IntSize(&p->vFreeUnits) == p->nNumCuts + 1 );
    Mpm_ObjForEachCutSafe( p, pObj, hCut, pCut, hNext )
    {
        ArrTime = Mpm_CutGetArrTime( p, pCut );
        if ( ArrTime > ReqTime )
            continue;
        Mpm_ObjAddCutToStore( p, pCut, ArrTime );
        Mmr_StepRecycle( p->pManCuts, hCut );
    }
}

// create cuts at the node from storage
void Mpm_ObjTranslateCutsFromStore( Mpm_Man_t * p, Mig_Obj_t * pObj, int fAddUnit )
{
    Mpm_Cut_t * pCut;
    Mpm_Uni_t * pUnit;
    int i, *pList = Mpm_ObjCutListP( p, pObj );
    assert( p->nCutStore > 0 && p->nCutStore <= p->nNumCuts );
    assert( *pList == 0 );
    // translate cuts
    for ( i = 0; i < p->nCutStore; i++ )
    {
        pUnit  = p->pCutStore[i];
        *pList = Mpm_CutCreate( p, pUnit->pLeaves, pUnit->nLeaves, pUnit->fUseless, &pCut );
        pList  = &pCut->hNext;
        Mpm_UnitRecycle( p, pUnit );
    }
    *pList = fAddUnit ? Mpm_CutCreateUnit( p, Mig_ObjId(pObj) ) : 0;
    assert( Vec_IntSize(&p->vFreeUnits) == p->nNumCuts + 1 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Mpm_ObjUpdateCut( Mpm_Cut_t * pCut, int * pPerm, int nLeaves )
{
    int i;
    assert( nLeaves <= (int)pCut->nLeaves );
    for ( i = 0; i < nLeaves; i++ )
        pPerm[i] = Abc_LitNotCond( pCut->pLeaves[Abc_Lit2Var(pPerm[i])], Abc_LitIsCompl(pPerm[i]) );
    memcpy( pCut->pLeaves, pPerm, sizeof(int) * nLeaves );
    pCut->nLeaves = nLeaves;
}
static inline void Mpm_ObjRecycleCuts( Mpm_Man_t * p, Mig_Obj_t * pObj )
{
    Mpm_Cut_t * pCut;
    int hCut, hNext;
    Mpm_ObjForEachCutSafe( p, pObj, hCut, pCut, hNext )
        Mmr_StepRecycle( p->pManCuts, hCut );
    Mpm_ObjSetCutList( p, pObj, 0 );
}
static inline void Mpm_ObjDerefFaninCuts( Mpm_Man_t * p, Mig_Obj_t * pObj )
{
    Mig_Obj_t * pFanin;
    int i;
    Mig_ObjForEachFanin( pObj, pFanin, i )
        if ( Mig_ObjIsNode(pFanin) && Mig_ObjMigRefDec(p, pFanin) == 0 )
            Mpm_ObjRecycleCuts( p, pFanin );
    if ( Mig_ObjSiblId(pObj) )
        Mpm_ObjRecycleCuts( p, Mig_ObjSibl(pObj) );
    if ( Mig_ObjMigRefNum(p, pObj) == 0 )
        Mpm_ObjRecycleCuts( p, pObj );
}
static inline void Mpm_ObjCollectFaninsAndSigns( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )
{
    Mpm_Cut_t * pCut;
    int hCut, nCuts = 0;
    Mpm_ObjForEachCut( p, pObj, hCut, pCut )
    {
        p->pCuts[i][nCuts] = pCut;
        p->pSigns[i][nCuts++] = Mpm_CutGetSign( pCut );
    }
    p->nCuts[i] = nCuts;
}
static inline void Mpm_ObjPrepareFanins( Mpm_Man_t * p, Mig_Obj_t * pObj )
{
    Mig_Obj_t * pFanin;
    int i;
    Mig_ObjForEachFanin( pObj, pFanin, i )
        Mpm_ObjCollectFaninsAndSigns( p, pFanin, i );
}

/**Function*************************************************************

  Synopsis    [Cut enumeration.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Mpm_ManDeriveCutNew( Mpm_Man_t * p, Mpm_Cut_t ** pCuts, int Required )
{
//    int fUseFunc = 0;
    Mpm_Cut_t * pCut = p->pCutTemp;
    int ArrTime;
#ifdef MIG_RUNTIME
abctime clk = clock();
#endif

    Mig_ManObjPresClean( p );
    if ( !Mpm_ObjDeriveCut( p, pCuts, pCut ) )
    {
#ifdef MIG_RUNTIME
p->timeMerge += clock() - clk;
#endif
        return 1;
    }
#ifdef MIG_RUNTIME
p->timeMerge += clock() - clk;
clk = clock();
#endif
    ArrTime = Mpm_CutGetArrTime( p, pCut );
#ifdef MIG_RUNTIME
p->timeEval += clock() - clk;
#endif

    if ( p->fMainRun && ArrTime > Required )
        return 1;
#ifdef MIG_RUNTIME
clk = Abc_Clock();
#endif
    Mpm_ObjAddCutToStore( p, pCut, ArrTime );
#ifdef MIG_RUNTIME
p->timeStore += Abc_Clock() - clk;
#endif
    return 1;
    // return 0 if const or buffer cut is derived - reset all cuts to contain only one
}
int Mpm_ManDeriveCuts( Mpm_Man_t * p, Mig_Obj_t * pObj )
{
//    static int Flag = 0;
    Mpm_Cut_t * pCuts[3];
    int Required = Mpm_ObjRequired( p, pObj );
    int hCutBest = Mpm_ObjCutBest( p, pObj );
    int c0, c1, c2;
#ifdef MIG_RUNTIME
    abctime clk;
#endif
    Mpm_ManPrepareCutStore( p );
    assert( Mpm_ObjCutList(p, pObj) == 0 );
    if ( hCutBest > 0 ) // cut list is assigned
    {
        Mpm_Cut_t * pCut = Mpm_ObjCutBestP( p, pObj ); 
        int Times = Mpm_CutGetArrTime( p, pCut );
        assert( pCut->hNext == 0 );
        if ( Times > Required )
            printf( "Arrival time (%d) exceeds required time (%d) at object %d.\n", Times, Required, Mig_ObjId(pObj) );
        if ( p->fMainRun )
            Mpm_ObjAddCutToStore( p, pCut, Times );
        else
            Mpm_ObjSetTime( p, pObj, Times );
    }
    // start storage with choice cuts
    if ( p->pMig->vSibls.nSize && Mig_ObjSiblId(pObj) )
        Mpm_ObjAddChoiceCutsToStore( p, Mig_ObjSibl(pObj), Required );
    // compute signatures for fanin cuts
#ifdef MIG_RUNTIME
clk = Abc_Clock();
#endif
    Mpm_ObjPrepareFanins( p, pObj );
#ifdef MIG_RUNTIME
p->timeFanin += Abc_Clock() - clk;
#endif
    // compute cuts in the internal storage
#ifdef MIG_RUNTIME
clk = Abc_Clock();
#endif
    if ( Mig_ObjIsNode2(pObj) )
    {
        // go through cut pairs
        pCuts[2] = NULL;
        for ( c0 = 0; c0 < p->nCuts[0] && (pCuts[0] = p->pCuts[0][c0]); c0++ )
        for ( c1 = 0; c1 < p->nCuts[1] && (pCuts[1] = p->pCuts[1][c1]); c1++ )
            if ( Abc_TtCountOnes(p->pSigns[0][c0] | p->pSigns[1][c1]) <= p->nLutSize )
                if ( !Mpm_ManDeriveCutNew( p, pCuts, Required ) )
                    goto finish;
    }
    else if ( Mig_ObjIsNode3(pObj) )
    {
        // go through cut triples
        for ( c0 = 0; c0 < p->nCuts[0] && (pCuts[0] = p->pCuts[0][c0]); c0++ )
        for ( c1 = 0; c1 < p->nCuts[1] && (pCuts[1] = p->pCuts[1][c1]); c1++ )
        for ( c2 = 0; c2 < p->nCuts[2] && (pCuts[2] = p->pCuts[2][c2]); c2++ )
            if ( Abc_TtCountOnes(p->pSigns[0][c0] | p->pSigns[1][c1] | p->pSigns[2][c2]) <= p->nLutSize )
                if ( !Mpm_ManDeriveCutNew( p, pCuts, Required ) )
                    goto finish;
    }
    else assert( 0 );
#ifdef MIG_RUNTIME
p->timeDerive += Abc_Clock() - clk;
#endif
finish:
    // transform internal storage into regular cuts
//    if ( Flag == 0 && p->nCutStore == p->nNumCuts - 1 )
//        Flag = 1, Mpm_CutPrintAll( p );
//    printf( "%d ", p->nCutStore );
    // save best cut
    assert( p->nCutStore > 0 );
    if ( p->pCutStore[0]->Inf.mTime <= Required )
    {
        Mpm_Cut_t * pCut;
        if ( hCutBest )
            Mmr_StepRecycle( p->pManCuts, hCutBest );
        hCutBest = Mpm_CutCreate( p, p->pCutStore[0]->pLeaves, p->pCutStore[0]->nLeaves, p->pCutStore[0]->fUseless, &pCut );
        Mpm_ObjSetCutBest( p, pObj, hCutBest );
        Mpm_ObjSetTime( p, pObj, p->pCutStore[0]->Inf.mTime );
        Mpm_ObjSetArea( p, pObj, p->pCutStore[0]->Inf.mArea );
        Mpm_ObjSetEdge( p, pObj, p->pCutStore[0]->Inf.mEdge );
    }
    else assert( !p->fMainRun );
    assert( hCutBest > 0 );
    // transform internal storage into regular cuts
    Mpm_ObjTranslateCutsFromStore( p, pObj, Mig_ObjRefNum(pObj) > 0 );
    // dereference fanin cuts and reference node
    Mpm_ObjDerefFaninCuts( p, pObj );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Required times.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Mpm_ManFindArrivalMax( Mpm_Man_t * p )
{
    int * pmTimes = Vec_IntArray( &p->vTimes );
    Mig_Obj_t * pObj;
    int i, ArrMax = 0;
    Mig_ManForEachCo( p->pMig, pObj, i )
        ArrMax = Abc_MaxInt( ArrMax, pmTimes[ Mig_ObjFaninId0(pObj) ] );
    return ArrMax;
}
static inline void Mpm_ManFinalizeRound( Mpm_Man_t * p )
{
    int * pMapRefs  = Vec_IntArray( &p->vMapRefs );
    int * pRequired = Vec_IntArray( &p->vRequireds );
    Mig_Obj_t * pObj;
    Mpm_Cut_t * pCut;
    int * pDelays;
    int i, iLeaf;
    p->GloArea = 0;
    p->GloEdge = 0;
    p->GloRequired = Mpm_ManFindArrivalMax(p);
    Mpm_ManCleanMapRefs( p );
    Mpm_ManCleanRequired( p );
    Mig_ManForEachObjReverse( p->pMig, pObj )
    {
        if ( Mig_ObjIsCo(pObj) )
        {
            pRequired[Mig_ObjFaninId0(pObj)] = p->GloRequired;
            pMapRefs [Mig_ObjFaninId0(pObj)]++;
        }
        else if ( Mig_ObjIsNode(pObj) )
        {
            int Required = pRequired[Mig_ObjId(pObj)];
            assert( Required > 0 );
            if ( pMapRefs[Mig_ObjId(pObj)] > 0 )
            {
                pCut = Mpm_ObjCutBestP( p, pObj );
                pDelays = p->pLibLut->pLutDelays[pCut->nLeaves];
                Mpm_CutForEachLeafId( pCut, iLeaf, i )
                {
                    pRequired[iLeaf] = Abc_MinInt( pRequired[iLeaf], Required - pDelays[i] );
                    pMapRefs [iLeaf]++;
                }
                p->GloArea += p->pLibLut->pLutAreas[pCut->nLeaves];
                p->GloEdge += pCut->nLeaves;
            }
        }
        else if ( Mig_ObjIsBuf(pObj) )
        {
        }
    }
    p->GloArea /= MPM_UNIT_AREA;
}
static inline void Mpm_ManComputeEstRefs( Mpm_Man_t * p )
{
    int * pMapRefs  = Vec_IntArray( &p->vMapRefs );
    int * pEstRefs  = Vec_IntArray( &p->vEstRefs );
    int i;
    assert( p->fMainRun );
//  pObj->EstRefs = (float)((2.0 * pObj->EstRefs + pObj->nRefs) / 3.0);
    for ( i = 0; i < Mig_ManObjNum(p->pMig); i++ )
        pEstRefs[i] = (1 * pEstRefs[i] + MPM_UNIT_REFS * pMapRefs[i]) / 2;
}

/**Function*************************************************************

  Synopsis    [Cut comparison.]

  Description [Returns positive number if new one is better than old one.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mpm_CutCompareDelay( Mpm_Inf_t * pOld, Mpm_Inf_t * pNew )
{
    if ( pOld->mTime    != pNew->mTime    ) return pOld->mTime    - pNew->mTime;
    if ( pOld->nLeaves  != pNew->nLeaves  ) return pOld->nLeaves  - pNew->nLeaves;
    if ( pOld->mArea    != pNew->mArea    ) return pOld->mArea    - pNew->mArea;
    if ( pOld->mEdge    != pNew->mEdge    ) return pOld->mEdge    - pNew->mEdge;
    return 0;
}
int Mpm_CutCompareDelay2( Mpm_Inf_t * pOld, Mpm_Inf_t * pNew )
{
    if ( pOld->mTime    != pNew->mTime    ) return pOld->mTime    - pNew->mTime;
    if ( pOld->mArea    != pNew->mArea    ) return pOld->mArea    - pNew->mArea;
    if ( pOld->mEdge    != pNew->mEdge    ) return pOld->mEdge    - pNew->mEdge;
    if ( pOld->nLeaves  != pNew->nLeaves  ) return pOld->nLeaves  - pNew->nLeaves;
    return 0;
}
int Mpm_CutCompareArea( Mpm_Inf_t * pOld, Mpm_Inf_t * pNew )
{
    if ( pOld->mArea    != pNew->mArea    ) return pOld->mArea    - pNew->mArea;
    if ( pOld->nLeaves  != pNew->nLeaves  ) return pOld->nLeaves  - pNew->nLeaves;
    if ( pOld->mEdge    != pNew->mEdge    ) return pOld->mEdge    - pNew->mEdge;
    if ( pOld->mAveRefs != pNew->mAveRefs ) return pOld->mAveRefs - pNew->mAveRefs;
    if ( pOld->mTime    != pNew->mTime    ) return pOld->mTime    - pNew->mTime;
    return 0;
}
int Mpm_CutCompareArea2( Mpm_Inf_t * pOld, Mpm_Inf_t * pNew )
{
    if ( pOld->mArea    != pNew->mArea    ) return pOld->mArea    - pNew->mArea;
    if ( pOld->mEdge    != pNew->mEdge    ) return pOld->mEdge    - pNew->mEdge;
    if ( pOld->mAveRefs != pNew->mAveRefs ) return pOld->mAveRefs - pNew->mAveRefs;
    if ( pOld->nLeaves  != pNew->nLeaves  ) return pOld->nLeaves  - pNew->nLeaves;
    if ( pOld->mTime    != pNew->mTime    ) return pOld->mTime    - pNew->mTime;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Technology mapping experiment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mpm_ManPerformRound( Mpm_Man_t * p )
{
    Mig_Obj_t * pObj;
    abctime clk = Abc_Clock();
    p->nCutsMerged = 0;
    Mpm_ManSetMigRefs( p );
    Mig_ManForEachNode( p->pMig, pObj )
        Mpm_ManDeriveCuts( p, pObj );
    Mpm_ManFinalizeRound( p );
    printf( "Del =%5d.  Ar =%8d.  Edge =%8d.  Cut =%10d. Max =%10d.  Rem =%6d.  ", 
        p->GloRequired, p->GloArea, p->GloEdge, 
        p->nCutsMerged, p->pManCuts->nEntriesMax, p->pManCuts->nEntries );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}
void Mpm_ManPerform( Mpm_Man_t * p )
{
    p->pCutCmp = Mpm_CutCompareDelay;
    Mpm_ManPerformRound( p );
    
    p->pCutCmp = Mpm_CutCompareDelay2;
    Mpm_ManPerformRound( p );
    
    p->pCutCmp = Mpm_CutCompareArea;
    Mpm_ManPerformRound( p );   

    p->fMainRun = 1;

    p->pCutCmp = Mpm_CutCompareArea;
    Mpm_ManComputeEstRefs( p );
    Mpm_ManPerformRound( p );

    p->pCutCmp = Mpm_CutCompareArea2;
    Mpm_ManComputeEstRefs( p );
    Mpm_ManPerformRound( p );
}
Gia_Man_t * Mpm_ManPerformTest( Mig_Man_t * pMig )
{
    Gia_Man_t * pNew;
    Mpm_LibLut_t * pLib;
    Mpm_Man_t * p;
    Mig_Obj_t * pObj;
    int i, hCut;
    pLib = Mpm_LibLutSetSimple( 6 );
    p = Mpm_ManStart( pMig, pLib, 8 );
    Mpm_ManPrintStatsInit( p );
    Mig_ManForEachCi( p->pMig, pObj, i )
    {
        hCut = Mpm_CutCreateUnit( p, Mig_ObjId(pObj) );
        Mpm_ObjSetCutBest( p, pObj, hCut );
        Mpm_ObjSetCutList( p, pObj, hCut );
    }
    Mig_ManForEachCand( p->pMig, pObj )
        Mpm_ObjSetEstRef( p, pObj, MPM_UNIT_REFS * Mig_ObjRefNum(pObj) );
    Mpm_ManPerform( p );
    Mpm_ManPrintStats( p );
    pNew = Mpm_ManFromIfLogic( p );
    Mpm_ManStop( p );
    Mpm_LibLutFree( pLib );
    return pNew;
}
Gia_Man_t * Mig_ManTest( Gia_Man_t * pGia )
{
    Mig_Man_t * p;
    Gia_Man_t * pNew;
    p = Mig_ManCreate( pGia );
    pNew = Mpm_ManPerformTest( p );
    Mig_ManStop( p );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

