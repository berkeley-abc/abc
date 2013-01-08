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


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MIG_NONE 0x3FFFFFFF
//#define MIG_MASK 0x0000FFFF
//#define MIG_BASE 16
#define MIG_MASK 0x000003FF
#define MIG_BASE 10

typedef struct Mig_Fan_t_ Mig_Fan_t;
struct Mig_Fan_t_
{
    unsigned       fCompl :   1;  // the complemented attribute
    unsigned       fType  :   1;  // the type attribute
    unsigned       Id     :  30;  // fanin ID
};

typedef struct Mig_Obj_t_ Mig_Obj_t;
struct Mig_Obj_t_
{
    Mig_Fan_t      pFans[4];
};

typedef struct Mig_Man_t_ Mig_Man_t;
struct Mig_Man_t_
{
    char *         pName;         // name
    int            nObjs;         // number of objects
    int            nRegs;         // number of flops
    Vec_Ptr_t      vPages;        // pages
    Vec_Int_t      vCis;          // CI IDs
    Vec_Int_t      vCos;          // CO IDs
    // object iterator
    Mig_Obj_t *    pPage;         // current page
    int            iPage;         // current page index
    // attributes
    int            nTravIds;      // traversal ID counter
    Vec_Int_t      vTravIds;      // traversal IDs
    Vec_Int_t      vCopies;       // copies
    Vec_Int_t      vNexts;        // next pointer
    Vec_Int_t      vLevels;       // levels
    Vec_Int_t      vRefs;         // ref counters
    Vec_Int_t      vEquivs;       // equivalent nodes
    Vec_Int_t      vReprs;        // representatives
};


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
static inline Mig_Obj_t *  Mig_ManObj( Mig_Man_t * p, int v )  { assert(v >= 0 && v < p->nObjs); return Mig_ManPage(p, v) + Mig_IdCell(v);  }
static inline Mig_Obj_t *  Mig_ManCi( Mig_Man_t * p, int v )   { return Mig_ManObj( p, Vec_IntEntry(&p->vCis,v) );                          }
static inline Mig_Obj_t *  Mig_ManCo( Mig_Man_t * p, int v )   { return Mig_ManObj( p, Vec_IntEntry(&p->vCos,v) );                          }
static inline Mig_Obj_t *  Mig_ManPi( Mig_Man_t * p, int v )   { assert( v < Mig_ManPiNum(p) );  return Mig_ManCi( p, v );                  }
static inline Mig_Obj_t *  Mig_ManPo( Mig_Man_t * p, int v )   { assert( v < Mig_ManPoNum(p) );  return Mig_ManCo( p, v );                  }
static inline Mig_Obj_t *  Mig_ManRo( Mig_Man_t * p, int v )   { assert( v < Mig_ManRegNum(p) ); return Mig_ManCi( p, Mig_ManPiNum(p)+v );  }
static inline Mig_Obj_t *  Mig_ManRi( Mig_Man_t * p, int v )   { assert( v < Mig_ManRegNum(p) ); return Mig_ManCo( p, Mig_ManPoNum(p)+v );  }
static inline Mig_Obj_t *  Mig_ManConst0( Mig_Man_t * p )      { return Mig_ManObj(p, 0);                                                   }

static inline int          Mig_FanCompl( Mig_Obj_t * p, int i )                { return p->pFans[i].fCompl;                                 }
static inline int          Mig_FanType( Mig_Obj_t * p, int i )                 { return p->pFans[i].fType;                                  }
static inline int          Mig_FanId( Mig_Obj_t * p, int i )                   { return p->pFans[i].Id;                                     }
static inline int          Mig_FanIsNone( Mig_Obj_t * p, int i )               { return p->pFans[i].Id == MIG_NONE;                         }
static inline int          Mig_FanSetCompl( Mig_Obj_t * p, int i, int v )      { assert( !(v >> 1) ); return p->pFans[i].fCompl = v;        }
static inline int          Mig_FanSetType( Mig_Obj_t * p, int i, int v )       { assert( !(v >> 1) ); return p->pFans[i].fType = v;         }
static inline int          Mig_FanSetId( Mig_Obj_t * p, int i, int v )         { assert(v >= 0 && v < MIG_NONE); return p->pFans[i].Id = v; }

static inline int          Mig_ObjIsNone( Mig_Obj_t * p )                      { return Mig_FanIsNone( p, 3 );                              }
static inline int          Mig_ObjIsTerm( Mig_Obj_t * p )                      { return Mig_FanIsNone( p, 1 );                              }
static inline int          Mig_ObjIsCi( Mig_Obj_t * p )                        { return Mig_ObjIsTerm(p) &&  Mig_FanIsNone( p, 0 );         } 
static inline int          Mig_ObjIsCo( Mig_Obj_t * p )                        { return Mig_ObjIsTerm(p) && !Mig_FanIsNone( p, 0 );         } 
static inline int          Mig_ObjIsNode( Mig_Obj_t * p )                      { return!Mig_FanIsNone( p, 0 ) &&!Mig_FanIsNone( p, 1 );     } 
static inline int          Mig_ObjIsAnd( Mig_Obj_t * p )                       { return Mig_FanType( p, 0 );                                } 
static inline int          Mig_ObjIsXor( Mig_Obj_t * p )                       { return Mig_FanType( p, 1 );                                } 
static inline int          Mig_ObjIsMux( Mig_Obj_t * p )                       { return Mig_FanType( p, 2 );                                } 
static inline int          Mig_ObjIsMaj( Mig_Obj_t * p )                       { return Mig_FanType( p, 3 );                                } 
static inline int          Mig_ObjIsConst0( Mig_Obj_t * p )                    { return Mig_FanId( p, 0 ) == 0;                             } 
static inline int          Mig_ObjIsCand( Mig_Obj_t * p )                      { return Mig_ObjIsNode(p) || Mig_ObjIsCi(p);                 } 
static inline int          Mig_ObjSetAnd( Mig_Obj_t * p )                      { return Mig_FanSetType( p, 0, 1 );                          } 
static inline int          Mig_ObjSetXor( Mig_Obj_t * p )                      { return Mig_FanSetType( p, 1, 1 );                          } 
static inline int          Mig_ObjSetMux( Mig_Obj_t * p )                      { return Mig_FanSetType( p, 2, 1 );                          } 
static inline int          Mig_ObjSetMaj( Mig_Obj_t * p )                      { return Mig_FanSetType( p, 3, 1 );                          } 

static inline int          Mig_ObjId( Mig_Obj_t * p )                          { return Mig_FanId( p, 3 );                                  }
static inline void         Mig_ObjSetId( Mig_Obj_t * p, int v )                { Mig_FanSetId( p, 3, v );                                   }
static inline int          Mig_ObjCioId( Mig_Obj_t * p )                       { assert( Mig_ObjIsTerm(p) ); return Mig_FanId( p, 2 );      }
static inline void         Mig_ObjSetCioId( Mig_Obj_t * p, int v )             { assert( Mig_ObjIsTerm(p) ); Mig_FanSetId( p, 2, v );       }
static inline int          Mig_ObjPhase( Mig_Obj_t * p )                       { return Mig_FanCompl( p, 2 );                               }
static inline int          Mig_ObjSetPhase( Mig_Obj_t * p, int v )             { Mig_FanSetCompl( p, 2, 1 );                                }

static inline Mig_Man_t *  Mig_ObjMan( Mig_Obj_t * p )                         { return *((Mig_Man_t**)(p - Mig_IdCell(Mig_ObjId(p)) - 1)); }
static inline Mig_Obj_t ** Mig_ObjPageP( Mig_Obj_t * p )                       { return *((Mig_Obj_t***)(p - Mig_IdCell(Mig_ObjId(p))) - 1);} 
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
//static inline Mig_Obj_t *  Mig_ObjFanin( Mig_Obj_t * p, int i )                { return Mig_ManObj( Mig_ObjMan(p), Mig_ObjFaninId(p, i) );    }
static inline Mig_Obj_t *  Mig_ObjFanin( Mig_Obj_t * p, int i )                { return Mig_ObjPageP(p)[Mig_IdPage(Mig_ObjFaninId(p, i))] + Mig_IdCell(Mig_ObjFaninId(p, i));    }
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
static inline void         Mig_ObjSetFaninLit( Mig_Obj_t * p, int i, int v )   { assert( v >= 0 && (v >> 1) < Mig_ObjId(p) ); Mig_FanSetId(p, i, Abc_Lit2Var(v)); Mig_FanSetCompl(p, i, Abc_LitIsCompl(v));       }

static inline int          Mig_ObjEquivId( Mig_Obj_t * p )                     { return Vec_IntSize(&Mig_ObjMan(p)->vEquivs) == 0 ? 0: Vec_IntEntry(&Mig_ObjMan(p)->vEquivs, Mig_ObjId(p));  }
static inline Mig_Obj_t *  Mig_ObjEquiv( Mig_Obj_t * p )                       { return Mig_ObjEquivId(p) == 0 ? NULL: Mig_ObjObj(p, Mig_ObjEquivId(p));                                     }
static inline int          Mig_ObjRefNum( Mig_Obj_t * p )                      { return Vec_IntSize(&Mig_ObjMan(p)->vRefs) == 0 ? -1: Vec_IntEntry(&Mig_ObjMan(p)->vRefs, Mig_ObjId(p));     }

static inline void         Mig_NtkIncrementTravId( Mig_Man_t * p )             { if ( p->vTravIds.pArray == NULL ) Vec_IntFill( &p->vTravIds, Mig_ManObjNum(p)+500, 0 ); p->nTravIds++;      }
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
            Mig_ManObj(p, Mig_ManObjNum(p)-1) :  p->pPage + MIG_BASE;   \
                pObj - p->pPage >= 0; pObj-- )
#define Mig_ManForEachObjVec( vVec, p, pObj, i )                        \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pObj) = Mig_ManObj(p, Vec_IntEntry(vVec,i))); i++ )
#define Mig_ManForEachNode( p, pObj )                                   \
    Mig_ManForEachObj( p, pObj ) if ( !Mig_ObjIsNode(pObj) ) {} else

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
    if ( p->nObjs >= (Vec_PtrSize(&p->vPages) << MIG_BASE) )
    {
        Mig_Obj_t * pPage;
        int i;
        assert( p->nObjs == (Vec_PtrSize(&p->vPages) << MIG_BASE) );
        pPage = ABC_FALLOC( Mig_Obj_t, MIG_MASK + 3 );
        *((void **)pPage) = p;
        *((void ***)(pPage + 1) - 1) = Vec_PtrArray(&p->vPages);
        Vec_PtrPush( &p->vPages, pPage + 1 );
        if ( *((void ***)(pPage + 1) - 1) != Vec_PtrArray(&p->vPages) )
            Vec_PtrForEachEntry( Mig_Obj_t *, &p->vPages, pPage, i )
                *((void ***)pPage - 1) = Vec_PtrArray(&p->vPages);
    }
    pObj = Mig_ManObj( p, p->nObjs++ );
    Mig_FanSetCompl( pObj, 0, 0 );
    Mig_FanSetCompl( pObj, 1, 0 );
    Mig_FanSetCompl( pObj, 2, 0 );
    Mig_FanSetCompl( pObj, 3, 0 );
    Mig_FanSetType( pObj, 0, 0 );
    Mig_FanSetType( pObj, 1, 0 );
    Mig_FanSetType( pObj, 2, 0 );
    Mig_FanSetType( pObj, 3, 0 );
    assert( Mig_ObjIsNone(pObj) );
    Mig_ObjSetId( pObj, p->nObjs - 1 );
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
static inline int Mig_ManAppendAnd( Mig_Man_t * p, int iLit0, int iLit1 )  
{ 
    Mig_Obj_t * pObj = Mig_ManAppendObj( p );
    assert( iLit0 != iLit1 );
    Mig_ObjSetFaninLit( pObj, 0, iLit0 < iLit1 ? iLit0 : iLit1 );
    Mig_ObjSetFaninLit( pObj, 1, iLit0 < iLit1 ? iLit1 : iLit0 );
    Mig_ObjSetAnd( pObj );
    return Mig_ObjId( pObj ) << 1;
}
/*
static inline int Mig_ManAppendOr( Mig_Man_t * p, int iLit0, int iLit1 )
{
    return Abc_LitNot(Mig_ManAppendAnd( p, Abc_LitNot(iLit0), Abc_LitNot(iLit1) ));
}
static inline int Mig_ManAppendMux( Mig_Man_t * p, int iCtrl, int iData1, int iData0 )  
{ 
    int iTemp0 = Mig_ManAppendAnd( p, Abc_LitNot(iCtrl), iData0 );
    int iTemp1 = Mig_ManAppendAnd( p, iCtrl, iData1 );
    return Abc_LitNotCond( Mig_ManAppendAnd( p, Abc_LitNot(iTemp0), Abc_LitNot(iTemp1) ), 1 );
}
static inline int Mig_ManAppendXor( Mig_Man_t * p, int iLit0, int iLit1 )  
{ 
    return Mig_ManAppendMux( p, iLit0, Abc_LitNot(iLit1), iLit1 );
}
*/
static inline int Mig_ManAppendXor( Mig_Man_t * p, int iLit0, int iLit1 )  
{ 
    Mig_Obj_t * pObj = Mig_ManAppendObj( p );
    assert( iLit0 != iLit1 );
    assert( !Abc_LitIsCompl(iLit0) && !Abc_LitIsCompl(iLit1) );
    Mig_ObjSetFaninLit( pObj, 0, iLit0 < iLit1 ? iLit0 : iLit1 );
    Mig_ObjSetFaninLit( pObj, 1, iLit0 < iLit1 ? iLit1 : iLit0 );
    Mig_ObjSetXor( pObj );
    return Mig_ObjId( pObj ) << 1;
}
static inline int Mig_ManAppendMux( Mig_Man_t * p, int iLit0, int iLit1, int iCtrl )  
{ 
    Mig_Obj_t * pObj = Mig_ManAppendObj( p );
    assert( iLit0 != iLit1 );
    assert( !Abc_LitIsCompl(iLit0) || !Abc_LitIsCompl(iLit1) );
    Mig_ObjSetFaninLit( pObj, 0, iLit0 < iLit1 ? iLit0 : iLit1 );
    Mig_ObjSetFaninLit( pObj, 1, iLit0 < iLit1 ? iLit1 : iLit0 );
    Mig_ObjSetFaninLit( pObj, 2, iLit0 < iLit1 ? iCtrl : Abc_LitNot(iCtrl) );
    Mig_ObjSetMux( pObj );
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
    assert( sizeof(Mig_Obj_t) == 16 );
    assert( (1 << MIG_BASE) == MIG_MASK + 1 );
    p = ABC_CALLOC( Mig_Man_t, 1 );
    Vec_IntGrow( &p->vCis, 1024 );
    Vec_IntGrow( &p->vCos, 1024 );
    Mig_ManAppendObj( p ); // const0
    return p;
}
static inline void Mig_ManStop( Mig_Man_t * p )
{
    printf( "Using %d pages of %d entries each. Total memory %.2f MB.\n", 
        Vec_PtrSize(&p->vPages), MIG_MASK + 1, 
        1.0 * Vec_PtrSize(&p->vPages) * (MIG_MASK + 1) * 16 / (1 << 20) );
    // attributes
    ABC_FREE( p->vTravIds.pArray );
    ABC_FREE( p->vCopies.pArray );
    ABC_FREE( p->vNexts.pArray );
    ABC_FREE( p->vLevels.pArray );
    ABC_FREE( p->vRefs.pArray );
    ABC_FREE( p->vEquivs.pArray );
    ABC_FREE( p->vReprs.pArray );
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

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mig_ManSetRefs( Mig_Man_t * p )
{
    Mig_Obj_t * pObj;
    int i, iFanin;
    clock_t clk = clock();
    Vec_IntFill( &p->vRefs, Mig_ManObjNum(p), 0 );
    // increment references
    Mig_ManForEachObj( p, pObj )
        Mig_ObjForEachFaninId( pObj, iFanin, i )
            if ( Mig_ObjHasFanin(pObj, i) )
                Vec_IntAddToEntry( &p->vRefs, Mig_ObjFaninId(pObj, i), 1 );
    // check that internal nodes have fanins
    Mig_ManForEachNode( p, pObj )
        assert( Vec_IntEntry(&p->vRefs, Mig_ObjId(pObj)) > 0 );
    Abc_PrintTime( 1, "Time", clock() - clk );
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
    if ( iObj == 0x3FFFFFFF )
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
    clock_t clk = clock();
    Mig_ManForEachObj( p, pObj )
        if ( Mig_ObjIsNode(pObj) )
            Counter += (Mig_ManSuppSizeOne(pObj) <= 16);
    printf( "Nodes with small support %d (out of %d)\n", Counter, Mig_ManNodeNum(p) );
    Abc_PrintTime( 1, "Time", clock() - clk );
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
void Mig_ManTest( Gia_Man_t * pGia )
{
    extern int Gia_ManSuppSizeTest( Gia_Man_t * p );
    Mig_Man_t * p;
    Gia_ManSuppSizeTest( pGia );
    p = Mig_ManCreate( pGia );
    Mig_ManSuppSizeTest( p );
    Mig_ManStop( p );
}



#define MPM_CUT_MAX     64
#define MPM_VAR_MAX     20

#define MPM_UNIT_TIME    1
#define MPM_UNIT_AREA   10
#define MPM_UNIT_EDGE  100


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
    unsigned         iFunc     : 25;           // function
    unsigned         fUseless  :  1;           // internal flag
    unsigned         nLeaves   :  6;           // leaves
    int              pLeaves[MPM_VAR_MAX];     // leaves
};

typedef struct Mpm_Obj_t_ Mpm_Obj_t;  // 32 bytes
struct Mpm_Obj_t_
{
    int              nRefs;                    // original references
    int              nMapRefs;                 // exact mapping references
    int              nEstRefs;                 // estimated mapping references
    int              mRequired;                // required time
    int              mTime;                    // arrival time
    int              mArea;                    // area
    int              mEdge;                    // edge
    int              iCutList;                 // cut list
};

typedef struct Mpm_LibLut_t_ Mpm_LibLut_t;
struct Mpm_LibLut_t_
{
    char *           pName;                    // the name of the LUT library
    int              LutMax;                   // the maximum LUT size 
    int              fVarPinDelays;            // set to 1 if variable pin delays are specified
    int              pLutAreas[MPM_VAR_MAX+1]; // the areas of LUTs
    int              pLutDelays[MPM_VAR_MAX+1][MPM_VAR_MAX+1];// the delays of LUTs
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
    Mpm_Obj_t *      pMapObjs;                 // mapping objects
    // cut computation
    Mmr_Step_t *     pManCuts;                 // cut memory
    // temporary cut storage
    int              nCutStore;                // number of cuts in storage
    Mpm_Uni_t *      pCutStore[MPM_CUT_MAX+1]; // storage for cuts
    // cut information
    Mpm_Uni_t        pCutUnits[MPM_CUT_MAX+1]; // cut info units
    Vec_Int_t        vFreeUnits;               // free cut info units
    // object presence
    unsigned char *  pObjPres;                 // object presence
    Mpm_Cut_t *      pCutTemp;                 // temporary cut
    Vec_Str_t        vObjShared;               // object presence
    // cut comparison
    int (* pCutCmp) (Mpm_Inf_t *, Mpm_Inf_t *); 
    // fanin cuts/signatures
    int              nCuts[3];                 // fanin cut counts
    Mpm_Cut_t *      pCuts[3][MPM_CUT_MAX+1];  // fanin cuts
    word             pSigns[3][MPM_CUT_MAX+1]; // fanin cut signatures
    // functionality
//    Dsd_Man_t *      pManDsd;
    void *           pManDsd;
    int              pPerm[MPM_VAR_MAX]; 
};

// iterators over object cuts
#define Mpm_ObjForEachCut( p, pObj, hCut, pCut )                         \
    for ( hCut = Mpm_ObjCutList(p, pObj); hCut && (pCut = Mpm_CutFetch(p, hCut)); hCut = pCut->hNext )
#define Mpm_ObjForEachCutSafe( p, pObj, hCut, pCut, hNext )              \
    for ( hCut = Mpm_ObjCutList(p, pObj); hCut && (pCut = Mpm_CutFetch(p, hCut)) && ((hNext = pCut->hNext), 1); hCut = hNext )
// iterators over cut leaves
#define Mpm_CutForEachLeafId( pCut, iLeafId, i )                         \
    for ( i = 0; i < (int)pCut->nLeaves && ((iLeafId = Abc_Lit2Var(pCut->pLeaves[i])), 1); i++ )
#define Mpm_CutForEachLeafMap( p, pCut, pLeaf, i )                       \
    for ( i = 0; i < (int)pCut->nLeaves && (pLeaf = Mpm_ManObjId(p, Abc_Lit2Var(pCut->pLeaves[i]))); i++ )
#define Mpm_CutForEachLeaf( p, pCut, pLeaf, i )                          \
    for ( i = 0; i < (int)pCut->nLeaves && (pLeaf = Mig_ManObj(p, Abc_Lit2Var(pCut->pLeaves[i]))); i++ )


static inline Mpm_Obj_t *  Mpm_ManObj( Mpm_Man_t * p, Mig_Obj_t * pObj )       { return p->pMapObjs + Mig_ObjId(pObj);                      }
static inline Mpm_Obj_t *  Mpm_ManObjId( Mpm_Man_t * p, int iObj )             { return p->pMapObjs + iObj;                                 }

static inline int          Mpm_ObjRefDec( Mpm_Man_t * p, Mig_Obj_t * pObj )    { return --Mpm_ManObj(p, pObj)->nRefs;                       }
static inline int          Mpm_ObjMapRef( Mpm_Man_t * p, Mig_Obj_t * pObj )    { return Mpm_ManObj(p, pObj)->nMapRefs;                      }
static inline int          Mpm_ObjMapRefDec( Mpm_Man_t * p, Mig_Obj_t * pObj ) { return --Mpm_ManObj(p, pObj)->nMapRefs;                    }
static inline int          Mpm_ObjEstRefInc( Mpm_Man_t * p, Mig_Obj_t * pObj ) { return Mpm_ManObj(p, pObj)->nEstRefs++;                    }
static inline int          Mpm_ObjCutList( Mpm_Man_t * p, Mig_Obj_t * pObj )   { return Mpm_ManObj(p, pObj)->iCutList;                      }
static inline int          Mpm_ObjArrTime( Mpm_Man_t * p, Mig_Obj_t * pObj )   { return Mpm_ManObj(p, pObj)->mTime;                         }
static inline int          Mpm_ObjReqTime( Mpm_Man_t * p, Mig_Obj_t * pObj )   { return Mpm_ManObj(p, pObj)->mRequired;                     }
static inline int          Mpm_ObjArrTimeId( Mpm_Man_t * p, int iObj )         { return Mpm_ManObjId(p, iObj)->mTime;                       }
static inline int          Mpm_ObjReqTimeId( Mpm_Man_t * p, int iObj )         { return Mpm_ManObjId(p, iObj)->mRequired;                   }

static inline int          Mpm_CutWordNum( int nLeaves )                       { return (sizeof(Mpm_Cut_t)/sizeof(int) + nLeaves + 1) >> 1; }

/**Function*************************************************************

  Synopsis    [Cut manipulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Mpm_CutAlloc( Mpm_Man_t * p, int nLeaves )  
{ 
    Mpm_Cut_t * pCut;
    int nWords  = Mpm_CutWordNum( nLeaves );
    int hHandle = Mmr_StepFetch( p->pManCuts, nWords );
    assert( nLeaves < 32 );
    assert( (hHandle >> 26) == 0 );
    pCut           = (Mpm_Cut_t *)Mmr_StepEntry( p->pManCuts, nWords, hHandle );
    pCut->nLeaves  = nLeaves;
    pCut->hNext    = 0;
    pCut->fUseless = 0;
    assert( pCut->iFunc == ~(unsigned)0 );
    return (hHandle << 5) | nWords;
}
static inline Mpm_Cut_t * Mpm_CutFetch( Mpm_Man_t * p, int h )  
{ 
    Mpm_Cut_t * pCut = (Mpm_Cut_t *)Mmr_StepEntry( p->pManCuts, h & 0x1F, h >> 5 );
    assert( Mpm_CutWordNum(pCut->nLeaves) == (h & 0x1F) );
    return pCut;
}
static inline Mpm_Cut_t * Mpm_ObjCutBest( Mpm_Man_t * p, Mig_Obj_t * pObj )   
{ 
    return Mpm_CutFetch( p, Mpm_ManObj(p, pObj)->iCutList );   
}
static inline int  Mpm_CutCreateZero( Mpm_Man_t * p, Mig_Obj_t * pObj )  
{ 
    Mpm_Cut_t * pCut;
    int hCut = Mpm_CutAlloc( p, 0 );
    pCut = Mpm_CutFetch( p, hCut );
    pCut->iFunc      = 0; // const0
    return hCut;
}
static inline int  Mpm_CutCreateUnit( Mpm_Man_t * p, Mig_Obj_t * pObj )  
{ 
    Mpm_Cut_t * pCut;
    int hCut = Mpm_CutAlloc( p, 1 );
    pCut = Mpm_CutFetch( p, hCut );
    pCut->iFunc      = 2; // var
    pCut->pLeaves[0] = Abc_Var2Lit( Mig_ObjId(pObj), 0 );
    return hCut;
}
static inline int Mpm_CutCreate( Mpm_Man_t * p, int * pLeaves, int nLeaves, int fUseless )  
{ 
    int hCutNew = Mpm_CutAlloc( p, nLeaves );
    Mpm_Cut_t * pCutNew = Mpm_CutFetch( p, hCutNew );
    pCutNew->fUseless = fUseless;
    pCutNew->nLeaves  = nLeaves;
    memcpy( pCutNew->pLeaves, pLeaves, sizeof(int) * nLeaves );
    return hCutNew;
}
static inline int Mpm_CutDup( Mpm_Man_t * p, Mpm_Cut_t * pCut, int fCompl )  
{ 
    int hCutNew = Mpm_CutAlloc( p, pCut->nLeaves );
    Mpm_Cut_t * pCutNew = Mpm_CutFetch( p, hCutNew );
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
static inline void Mpm_CutRecycle( Mpm_Man_t * p, int h )  
{ 
    Mmr_StepRecycle( p->pManCuts, h & 0x1F, h >> 5 );
}

/**Function*************************************************************

  Synopsis    [Cut merging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Mpm_ManObjPresClean( Mpm_Man_t * p )                
{ 
    int i; 
    for ( i = 0; i < (int)p->pCutTemp->nLeaves; i++ )
        p->pObjPres[Abc_Lit2Var(p->pCutTemp->pLeaves[i])] = (unsigned char)0xFF; 
    p->pCutTemp->nLeaves = 0;
    Vec_StrClear(&p->vObjShared);                      
}
static inline void Mpm_ManObjPres( Mpm_Man_t * p, int k, int iLit ) 
{ 
    int iObj = Abc_Lit2Var(iLit);
    if ( p->pObjPres[iObj] == (unsigned char)0xFF ) 
    { 
        p->pObjPres[iObj] = p->pCutTemp->nLeaves; 
        p->pCutTemp->pLeaves[p->pCutTemp->nLeaves++] = iLit;
    } 
    else
    {
        int iLit0 = p->pCutTemp->pLeaves[p->pObjPres[iObj]];
        assert( Abc_Lit2Var(iLit0) == Abc_Lit2Var(iLit) );
        Vec_StrPush( &p->vObjShared, (unsigned char)k );
        Vec_StrPush( &p->vObjShared, (unsigned char)Abc_Var2Lit((int)p->pObjPres[iObj], iLit0 != iLit) );
    }
}
static inline int  Mpm_ManSetIsSmaller( Mpm_Man_t * p, int * pLits, int nLits ) // check if pCut is contained in the current one
{
    int i, Index;
    for ( i = 0; i < nLits; i++ )
    {
        Index = (int)p->pObjPres[Abc_Lit2Var(pLits[i])];
        if ( Index == 0xFF )
            return 0;
        assert( Index < nLits );
    }
    return 1;
}
static inline int  Mpm_ManSetIsBigger( Mpm_Man_t * p, int * pLits, int nLits ) // check if pCut contains the current one
{
    int i, Index;
    unsigned uMask = 0;
    for ( i = 0; i < nLits; i++ )
    {
        Index = (int)p->pObjPres[Abc_Lit2Var(pLits[i])];
        if ( Index == 0xFF )
            continue;
        assert( Index < nLits );
        uMask |= (1 << Index);
    }
    return uMask == ~(~(unsigned)0 << nLits);
}
static inline int  Mpm_ManSetIsDisjoint( Mpm_Man_t * p, Mpm_Cut_t * pCut ) // check if pCut is disjoint
{
    int i;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        if ( (int)p->pObjPres[Abc_Lit2Var(pCut->pLeaves[i])] != 0xFF )
            return 0;
    return 1;
}
static inline int Mpm_ObjDeriveCut( Mpm_Man_t * p, Mpm_Cut_t * pCut0, Mpm_Cut_t * pCut1 ) // pCut0 is bigger
{
    int i;
    Mpm_Cut_t * pCut = p->pCutTemp;
//    assert( pCut1 == NULL || pCut0->nLeaves >= pCut1->nLeaves );
    Mpm_ManObjPresClean( p );
    for ( i = 0; i < (int)pCut0->nLeaves; i++ )
        Mpm_ManObjPres( p, i, pCut0->pLeaves[i] );
    if ( pCut1 )
    {
        for ( i = 0; i < (int)pCut1->nLeaves; i++ )
        {
            Mpm_ManObjPres( p, i, pCut1->pLeaves[i] );
            if ( (int)pCut->nLeaves > p->nLutSize )
                return 0;
        }
    }
    pCut->hNext    =  0;
    pCut->iFunc    = ~(unsigned)0;
    pCut->fUseless =  0;
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
    int i;
    word uSign = 0;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        uSign |= (1 << (Abc_Lit2Var(pCut->pLeaves[i]) & 0x3F));
    return uSign;
}
static inline int  Mpm_CutGetArrTime( Mpm_Man_t * p, Mpm_Cut_t * pCut )  
{
    Mpm_Obj_t * pLeaf;
    int i, ArrTime = 0;
    if ( p->pLibLut == NULL )
    {
        Mpm_CutForEachLeafMap( p, pCut, pLeaf, i )
            ArrTime = Abc_MaxInt( ArrTime, pLeaf->mTime );
        ArrTime += MPM_UNIT_TIME;
    }
    else
    {
        int * pDelays = p->pLibLut->pLutDelays[pCut->nLeaves];
        Mpm_CutForEachLeafMap( p, pCut, pLeaf, i )
            ArrTime = Abc_MaxInt( ArrTime, pLeaf->mTime + pDelays[i] );
    }
    return ArrTime;
}
static inline void Mpm_CutSetupInfo( Mpm_Man_t * p, Mpm_Cut_t * pCut, int ArrTime, Mpm_Inf_t * pInfo )  
{
    Mpm_Obj_t * pLeaf;
    int i;
    memset( pInfo, 0, sizeof(Mpm_Inf_t) );
    pInfo->mTime = ArrTime;
    pInfo->mCost = p->pLibLut ? p->pLibLut->pLutAreas[pCut->nLeaves] : MPM_UNIT_AREA;
    pInfo->mArea = pInfo->mCost;
    pInfo->mEdge = pInfo->nLeaves;
    Mpm_CutForEachLeafMap( p, pCut, pLeaf, i )
    {
        if ( pLeaf->nMapRefs )
        {
            pInfo->mArea += pLeaf->mArea;
            pInfo->mEdge += pLeaf->mEdge;
        }
        else
        {
            assert( pLeaf->nEstRefs > 0 );
            pInfo->mArea += pLeaf->mArea / pLeaf->nEstRefs;
            pInfo->mEdge += pLeaf->mEdge / pLeaf->nEstRefs;
            pInfo->mAveRefs += MPM_UNIT_EDGE * pLeaf->nMapRefs;
        }
        pInfo->uSign |= (1 << Abc_Lit2Var(pCut->pLeaves[i]));
    }
    pInfo->mAveRefs /= pCut->nLeaves;
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
    if ( pOld->mEdge    != pNew->mEdge    ) return pOld->mEdge    - pNew->mEdge;
    if ( pOld->mAveRefs != pNew->mAveRefs ) return pOld->mAveRefs - pNew->mAveRefs;
    if ( pOld->nLeaves  != pNew->nLeaves  ) return pOld->nLeaves  - pNew->nLeaves;
    if ( pOld->mTime    != pNew->mTime    ) return pOld->mTime    - pNew->mTime;
    return 0;
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
static inline void Mpm_UnitRecycleAll( Mpm_Man_t * p )  
{
    int i;
    Vec_IntClear( &p->vFreeUnits );
    for ( i = p->nNumCuts; i >= 0; i-- )
        Vec_IntPush( &p->vFreeUnits, i );
    assert( Vec_IntSize(&p->vFreeUnits) == p->nNumCuts + 1 );
}
// compares cut against those present in the store
int Mpm_ObjAddCutToStore( Mpm_Man_t * p, Mpm_Cut_t * pCut, int ArrTime )
{
    Mpm_Uni_t * pUnit, * pUnitNew;
    int k, iPivot, last;
    // create new unit
    pUnitNew = Mpm_CutToUnit( p, pCut );
    Mpm_CutSetupInfo( p, pCut, ArrTime, &pUnitNew->Inf );
    // special case when the cut store is empty
    if ( p->nCutStore == 0 )
    {
        p->pCutStore[p->nCutStore++] = pUnitNew;
        return 1;
    }
    // special case when the cut store is full and last cut is better than new cut
    pUnit = p->pCutStore[p->nCutStore-1];
    if ( p->nCutStore == p->nNumCuts && p->pCutCmp(&pUnitNew->Inf, &pUnit->Inf) > 0 )
    {
        Mpm_UnitRecycle( p, pUnitNew );
        return 0;
    }
    // find place of the given cut in the store
    assert( p->nCutStore <= p->nNumCuts );
    for ( iPivot = p->nCutStore - 1; iPivot >= 0; iPivot-- )
        if ( p->pCutCmp(&pUnitNew->Inf, &p->pCutStore[iPivot]->Inf) > 0 ) // iPivot-th cut is better than new cut
            break;
    // filter this cut using other cuts
    for ( k = 0; k <= iPivot; k++ )
    {
        pUnit = p->pCutStore[k];
        if ( pUnitNew->Inf.nLeaves >= pUnit->Inf.nLeaves && 
            (pUnitNew->Inf.uSign & pUnit->Inf.uSign) == pUnit->Inf.uSign && 
             Mpm_ManSetIsSmaller(p, pUnit->pLeaves, pUnit->nLeaves) )
        {
            Mpm_UnitRecycle( p, pUnitNew );
            return 0;
        }
    }
    // special case when the best cut is useless
    if ( p->pCutStore[0]->fUseless )
        iPivot = -1;
    // insert this cut at location iPivot
    for ( k = p->nCutStore++; k > iPivot; k-- )
        p->pCutStore[k] = p->pCutStore[k-1];
    p->pCutStore[iPivot] = pUnitNew;
    // filter other cuts using this cut
    for ( k = last = iPivot + 1; k < p->nCutStore; k++ )
    {
        pUnit = p->pCutStore[k];
        if ( pUnitNew->Inf.nLeaves <= pUnit->Inf.nLeaves && 
            (pUnitNew->Inf.uSign & pUnit->Inf.uSign) == pUnitNew->Inf.uSign && 
             Mpm_ManSetIsBigger(p, pUnit->pLeaves, pUnit->nLeaves) )
        {
            Mpm_UnitRecycle( p, pUnit );
            continue;
        }
        p->pCutStore[last++] = p->pCutStore[k];
    }
    p->nCutStore = last;
    // remove the last cut if too many
    if ( p->nCutStore >= p->nNumCuts )
        Mpm_UnitRecycle( p, p->pCutStore[--p->nCutStore] );
    assert( p->nCutStore <= p->nNumCuts );
    return 1;
}
// create storage from cuts at the node
void Mpm_ObjTranslateCutsToStore( Mpm_Man_t * p, Mig_Obj_t * pObj, int ReqTime )
{
    Mpm_Cut_t * pCut;
    int hCut, ArrTime;
    assert( p->nCutStore == 0 );
    assert( Vec_IntSize(&p->vFreeUnits) == p->nNumCuts + 1 );
    Mpm_ObjForEachCut( p, pObj, hCut, pCut )
    {
        ArrTime = Mpm_CutGetArrTime( p, pCut );
        if ( ArrTime > ReqTime )
            continue;
        Mpm_ObjAddCutToStore( p, pCut, ArrTime );
    }
}
// create cuts at the node from storage
void Mpm_ObjTranslateCutsFromStore( Mpm_Man_t * p, Mig_Obj_t * pObj, int fAddUnit )
{
    Mpm_Uni_t * pUnit;
    int i, *pList = &Mpm_ManObj(p, pObj)->iCutList;
    assert( *pList == 0 ); 
    assert( p->nCutStore > 0 && p->nCutStore <= p->nNumCuts );
    for ( i = 0; i < p->nCutStore; i++ )
    {
        pUnit = p->pCutStore[i];
        *pList = Mpm_CutCreate( p, pUnit->pLeaves, pUnit->nLeaves, pUnit->fUseless );
        pList = &Mpm_CutFetch(p, *pList)->hNext;
        Mpm_UnitRecycle( p, pUnit );
    }
    *pList = fAddUnit ? Mpm_CutCreateUnit( p, pObj ) : 0;
    assert( Vec_IntSize(&p->vFreeUnits) == p->nNumCuts + 1 );
}


/**Function*************************************************************

  Synopsis    [Required times.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Mpm_ManResetRequired( Mpm_Man_t * p )
{
    int i;
    for ( i = 0; i < Mig_ManObjNum(p->pMig); i++ )
        p->pMapObjs[i].mRequired = ABC_INFINITY;
}
static inline int Mpm_ManFindArrivalMax( Mpm_Man_t * p )
{
    Mig_Obj_t * pObj;
    int i, ArrMax = 0;
    Mig_ManForEachCo( p->pMig, pObj, i )
        ArrMax = Abc_MaxInt( ArrMax, Mpm_ObjArrTimeId(p, Mig_ObjFaninId0(pObj)) );
    return ArrMax;
}
static inline void Mpm_ManComputeRequired( Mpm_Man_t * p, int ArrMax )
{
    Mig_Obj_t * pObj;
    Mpm_Obj_t * pFanin;
    Mpm_Cut_t * pCut;
    int i, Required;
    Mpm_ManResetRequired( p );
    Mig_ManForEachObjReverse( p->pMig, pObj )
    {
        if ( Mig_ObjIsCo(pObj) )
            Mpm_ManObjId(p, Mig_ObjFaninId0(pObj))->mRequired = ArrMax;
        else if ( Mig_ObjIsNode(pObj) && Mig_ObjRefNum(pObj) )
        {
            pCut = Mpm_ObjCutBest( p, pObj );
            Required = Mpm_ManObj(p,pObj)->mRequired;
            if ( p->pLibLut == NULL )
            {
                Mpm_CutForEachLeafMap( p, pCut, pFanin, i )
                    pFanin->mRequired = Abc_MinInt( pFanin->mRequired, Required - MPM_UNIT_TIME );
            }
            else
            {
                int * pDelays = p->pLibLut->pLutDelays[pCut->nLeaves];
                Mpm_CutForEachLeafMap( p, pCut, pFanin, i )
                    pFanin->mRequired = Abc_MinInt( pFanin->mRequired, Required - pDelays[i] );
            }
        }
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Mpm_Man_t * Mpm_ManStart( Mig_Man_t * pMig, int nLutSize, int nNumCuts )
{
    Mpm_Man_t * p;
    assert( sizeof(Mpm_Inf_t) % sizeof(word) == 0 );      // aligned info to word boundary
    assert( Mpm_CutWordNum(32) < 32 ); // using 5 bits for word count
    assert( nNumCuts <= MPM_CUT_MAX );
    Mig_ManSetRefs( pMig );
    // alloc
    p = ABC_CALLOC( Mpm_Man_t, 1 );
    p->pMig     = pMig;
    p->nLutSize = nLutSize;
    p->nNumCuts = nNumCuts;
    // mapping attributes
    p->pMapObjs = ABC_CALLOC( Mpm_Obj_t, Mig_ManObjNum(pMig) );
    Mpm_ManResetRequired( p );
    // cuts
    p->pManCuts = Mmr_StepStart( Mpm_CutWordNum(nLutSize) );
    Vec_IntGrow( &p->vFreeUnits, nNumCuts + 1 );
    Mpm_UnitRecycleAll( p );
    p->pObjPres = ABC_FALLOC( unsigned char, Mig_ManObjNum(pMig) );
    p->pCutTemp = (Mpm_Cut_t *)ABC_CALLOC( word, Mpm_CutWordNum(nLutSize) );
    Vec_StrGrow( &p->vObjShared, 32 );
    p->pCutCmp  = Mpm_CutCompareDelay;
    // start DSD manager
    p->pManDsd  = NULL;
    return p;
}
static inline void Mpm_ManStop( Mpm_Man_t * p )
{
    ABC_FREE( p->pMapObjs );
    Mmr_StepStop( p->pManCuts );
    ABC_FREE( p->vFreeUnits.pArray );
    ABC_FREE( p->vObjShared.pArray );
    ABC_FREE( p->pCutCmp );
    ABC_FREE( p->pObjPres );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mpm_ObjRecycleCuts( Mpm_Man_t * p, Mig_Obj_t * pObj, int fKeepBest )
{
    Mpm_Cut_t * pCut;
    int hCut, hNext, hList = Mpm_ObjCutList(p, pObj);
    Mpm_ObjForEachCutSafe( p, pObj, hCut, pCut, hNext )
        if ( fKeepBest && hCut == hList )
            pCut->hNext = 0;
        else
            Mpm_CutRecycle( p, hCut );
    if ( !fKeepBest )
        Mpm_ManObj(p, pObj)->iCutList = 0;
}
void Mpm_ObjCollectFaninsAndSigns( Mpm_Man_t * p, Mig_Obj_t * pObj, int i )
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
void Mpm_ObjUpdateCut( Mpm_Cut_t * pCut, int * pPerm, int nLeaves )
{
    int i;
    assert( nLeaves <= (int)pCut->nLeaves );
    for ( i = 0; i < nLeaves; i++ )
        pPerm[i] = Abc_LitNotCond( pCut->pLeaves[Abc_Lit2Var(pPerm[i])], Abc_LitIsCompl(pPerm[i]) );
    memcpy( pCut->pLeaves, pPerm, sizeof(int) * nLeaves );
    pCut->nLeaves = nLeaves;
}

/**Function*************************************************************

  Synopsis    [Cut enumeration.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mpm_ManDeriveCuts( Mpm_Man_t * p, Mig_Obj_t * pObj )
{
    int fUseFunc = 0;
    Mpm_Obj_t * pMapObj = Mpm_ManObj(p, pObj);
    Mpm_Cut_t * pCut0, * pCut1;
    Mig_Obj_t * pFanin;
    int i, c0, c1, iDsd0, iDsd1, ArrTime;

    // start storage with choice cuts
    p->nCutStore = 0;
    if ( Mig_ObjEquivId(pObj) )
        Mpm_ObjTranslateCutsToStore( p, Mig_ObjEquiv(pObj), pMapObj->mRequired );

    // check that the best cut is ok
    if ( Mpm_ObjCutList(p, pObj) > 0 ) // cut list is assigned
    {
        Mpm_Cut_t * pCut = Mpm_ObjCutBest( p, pObj ); assert( pCut->hNext == 0 );
        pMapObj->iCutList = 0;
        pMapObj->mTime = Mpm_CutGetArrTime(p, pCut);
        if ( pMapObj->mTime > pMapObj->mRequired )
            printf( "Arrival time (%d) exceeds required time (%d) at object %d.\n", 
                pMapObj->mTime, pMapObj->mRequired, Mig_ObjId(pObj) );
        if ( p->nCutStore > 0 )
            Mpm_ObjDeriveCut( p, pCut, NULL );
        Mpm_ObjAddCutToStore( p, p->pCutTemp, pMapObj->mTime );
    }

    // compute cuts
    if ( !Mig_ObjHasFanin(pObj, 2) )
    {
        // compute signatures for fanin cuts
        Mig_ObjForEachFanin( pObj, pFanin, i )
            Mpm_ObjCollectFaninsAndSigns( p, pFanin, i );
        // check special cases
        if ( fUseFunc )
        {
            pCut0 = p->pCuts[0][0];  pCut1 = p->pCuts[1][0];
            if ( pCut0->iFunc < 2 || pCut1->iFunc < 2 )
            {
                assert( Mig_ObjIsAnd(pObj) );
                Mpm_UnitRecycleAll( p );
                if (  Abc_LitNotCond(pCut0->iFunc, Mig_ObjFaninC0(pObj)) == 0 ||
                      Abc_LitNotCond(pCut1->iFunc, Mig_ObjFaninC1(pObj)) == 0 ) // set the resulting cut to 0
                    Mpm_ManObj(p, pObj)->iCutList = Mpm_CutCreateZero( p, pObj );
                else if ( Abc_LitNotCond(pCut0->iFunc, Mig_ObjFaninC0(pObj)) == 1 ) // set the resulting set to be that of Fanin1
                    Mpm_ManObj(p, pObj)->iCutList = Mpm_CutCopySet( p, Mig_ObjFanin1(pObj), 0 );
                else if ( Abc_LitNotCond(pCut1->iFunc, Mig_ObjFaninC1(pObj)) == 1 ) // set the resulting set to be that of Fanin0
                    Mpm_ManObj(p, pObj)->iCutList = Mpm_CutCopySet( p, Mig_ObjFanin0(pObj), 0 );
                else assert( 0 );
                goto finish;
            }
        }
        // go through cut pairs
        for ( c0 = 0; c0 < p->nCuts[0] && (pCut0 = p->pCuts[0][c0]); c0++ )
        for ( c1 = 0; c1 < p->nCuts[1] && (pCut1 = p->pCuts[1][c1]); c1++ )
        {
            if ( Abc_TtCountOnes(p->pSigns[0][c0] | p->pSigns[1][c1]) > p->nLutSize )
                continue;
            iDsd0 = Abc_LitNotCond( pCut0->iFunc, Mig_ObjFaninC0(pObj) );
            iDsd1 = Abc_LitNotCond( pCut1->iFunc, Mig_ObjFaninC1(pObj) );
            if ( fUseFunc )
            {
                if ( iDsd0 > iDsd1 )
                {
                    ABC_SWAP( int, iDsd0, iDsd1 );
                    ABC_SWAP( Mpm_Cut_t *, pCut0, pCut1 );
                }
            }
            else
            {
                if ( pCut0->nLeaves < pCut1->nLeaves )
                    ABC_SWAP( Mpm_Cut_t *, pCut0, pCut1 );
            }
            if ( !Mpm_ObjDeriveCut( p, pCut0, pCut1 ) )
                continue;
            ArrTime = Mpm_CutGetArrTime( p, p->pCutTemp );
            if ( ArrTime > pMapObj->mRequired )
                continue;
            // compute cut function
            if ( fUseFunc )
            {
                extern int Mpm_FuncCompute( void * p, int iDsd0, int iDsd1, Vec_Str_t * vShared, int * pPerm, int * pnLeaves );
                int nLeavesOld = p->pCutTemp->nLeaves;
                int nLeaves    = p->pCutTemp->nLeaves;
                // compute functionality and filter cuts dominated by support-reduced cuts
                p->pCutTemp->iFunc = Mpm_FuncCompute( p->pManDsd, iDsd0, iDsd1, &p->vObjShared, p->pPerm, &nLeaves );
                Mpm_ObjUpdateCut( p->pCutTemp, p->pPerm, nLeaves );
                // consider filtering based on functionality
                if ( nLeaves == 0 ) // derived const cut
                {
                    Mpm_UnitRecycleAll( p );
                    Mpm_ManObj(p, pObj)->iCutList = Mpm_CutCreateZero( p, pObj );
                    goto finish;
                }
                if ( nLeaves == 1 ) // derived unit cut
                {
                    Mpm_UnitRecycleAll( p );
                    pFanin = Mig_ManObj( p->pMig, Abc_Lit2Var(p->pCutTemp->pLeaves[0]) );
                    Mpm_ManObj(p, pObj)->iCutList = Mpm_CutCopySet( p, pFanin, Abc_LitIsCompl(p->pCutTemp->pLeaves[0]) );
                    goto finish;
                }
                if ( nLeaves < nLeavesOld ) // reduced support of the cut
                {
                    ArrTime = Mpm_CutGetArrTime( p, p->pCutTemp );
                    if ( ArrTime > pMapObj->mRequired )
                        continue;
                }
            }
            Mpm_ObjAddCutToStore( p, p->pCutTemp, ArrTime );
        }
    }
    else assert( 0 );

    // transform internal storage into cuts
    Mpm_ObjTranslateCutsFromStore( p, pObj, Mig_ObjRefNum(pObj) > 0 );

finish:
    // dereference cuts
    Mig_ObjForEachFanin( pObj, pFanin, i )
        if ( Mpm_ObjRefDec( p, pFanin ) == 0 )
            Mpm_ObjRecycleCuts( p, pFanin, 1 );
    // reference node
    Mpm_ManObj(p, pObj)->nRefs = Mig_ObjRefNum(pObj);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Cut computation experiment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mpm_ManPerform( Mpm_Man_t * p )
{
    Mig_Obj_t * pObj;
    clock_t clk = clock();
    int i;
    Mig_ManForEachCi( p->pMig, pObj, i )
        Mpm_ManObj(p, pObj)->iCutList = Mpm_CutCreateUnit( p, pObj );
    Mig_ManForEachNode( p->pMig, pObj )
        Mpm_ManDeriveCuts( p, pObj );
    Abc_PrintTime( 1, "Time", clock() - clk );
}
void Mpm_ManPerformTest( Mig_Man_t * pMig )
{
    Mpm_Man_t * p;
    p = Mpm_ManStart( pMig, 6, 10 );
    Mpm_ManPerform( p );
    Mpm_ManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

