/**CFile****************************************************************

  FileName    [abcHieNew.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [New hierarchy manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcHieNew.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "vec.h"
#include "utilNam.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define AU_MAX_FANINS 0x1FFFFFFF
 
typedef enum { 
    AU_OBJ_NONE,           // 0: non-existent object
    AU_OBJ_CONST0,         // 1: constant node
    AU_OBJ_PI,             // 2: primary input
    AU_OBJ_PO,             // 3: primary output
    AU_OBJ_FAN,            // 4: box output
    AU_OBJ_FLOP,           // 5: flip-flop
    AU_OBJ_BOX,            // 6: box
    AU_OBJ_NODE,           // 7: logic node
    AU_OBJ_VOID            // 8: placeholder
} Au_Type_t;


typedef struct Au_Man_t_   Au_Man_t;
typedef struct Au_Ntk_t_   Au_Ntk_t;
typedef struct Au_Obj_t_   Au_Obj_t;

struct Au_Obj_t_ // 16 bytes
{
    unsigned               Func;               // functionality
    unsigned               Type    :  3;       // object type
    unsigned               nFanins : 29;       // fanin count (related to AU_MAX_FANIN_NUM)
    int                    Fanins[2];          // fanin literals
};

struct Au_Ntk_t_ 
{
    char *                 pName;              // model name
    Au_Man_t *             pMan;               // model manager
    int                    Id;                 // model ID
    // objects
    Vec_Int_t              vPis;               // primary inputs (CI id -> handle)
    Vec_Int_t              vPos;               // primary outputs (CI id -> handle)
    Vec_Int_t              vObjs;              // internal nodes (obj id -> handle)
    int                    nObjs[AU_OBJ_VOID]; // counter of objects of each type
    // memory for objects
    Vec_Ptr_t *            vChunks;            // memory pages
    Vec_Ptr_t              vPages;             // memory pages
    int                    iHandle;            // currently available ID
    int                    nObjsAlloc;         // the total number of objects allocated
    int                    nObjsUsed;          // the number of useful entries
    // object attributes
    int                    nTravIds;           // counter of traversal IDs
    Vec_Int_t              vTravIds;           // trav IDs of the objects
    Vec_Int_t              vCopies;            // object copies
    // structural hashing
    int                    nHTable;            // hash table size
    int *                  pHTable;            // hash table
    Au_Obj_t *             pConst0;            // constant node
};

struct Au_Man_t_ 
{
    char *                 pName;              // the name of the library
    Vec_Ptr_t              vNtks;              // the array of modules
    Abc_Nam_t *            pFuncs;             // hashing functions into integers
    int                    nRefs;              // reference counter
    // statistics
    int                    nGiaObjMax;         // max number of GIA objects
};


static inline int          Au_Var2Lit( int Var, int fCompl )             { return Var + Var + fCompl;                       }
static inline int          Au_Lit2Var( int Lit )                         { return Lit >> 1;                                 }
static inline int          Au_LitIsCompl( int Lit )                      { return Lit & 1;                                  }
static inline int          Au_LitNot( int Lit )                          { return Lit ^ 1;                                  }
static inline int          Au_LitNotCond( int Lit, int c )               { return Lit ^ (int)(c > 0);                       }
static inline int          Au_LitRegular( int Lit )                      { return Lit & ~01;                                }

static inline Au_Obj_t *   Au_Regular( Au_Obj_t * p )                    { return (Au_Obj_t *)((ABC_PTRUINT_T)(p) & ~01);   }
static inline Au_Obj_t *   Au_Not( Au_Obj_t * p )                        { return (Au_Obj_t *)((ABC_PTRUINT_T)(p) ^  01);   }
static inline Au_Obj_t *   Au_NotCond( Au_Obj_t * p, int c )             { return (Au_Obj_t *)((ABC_PTRUINT_T)(p) ^ (c));   }
static inline int          Au_IsComplement( Au_Obj_t * p )               { return (int)((ABC_PTRUINT_T)(p) & 01);           }
 
static inline char *       Au_UtilStrsav( char * s )                     { return s ? strcpy(ABC_ALLOC(char, strlen(s)+1), s) : NULL;             }

static inline char *       Au_ManName( Au_Man_t * p )                    { return p->pName;                                                       }
static inline Au_Ntk_t *   Au_ManNtk( Au_Man_t * p, int i )              { return (Au_Ntk_t *)Vec_PtrEntry(&p->vNtks, i);                         }

static inline char *       Au_NtkName( Au_Ntk_t * p )                    { return p->pName;                                                       }
static inline Au_Man_t *   Au_NtkMan( Au_Ntk_t * p )                     { return p->pMan;                                                        }
static inline int          Au_NtkPiNum( Au_Ntk_t * p )                   { return p->nObjs[AU_OBJ_PI];                                            } 
static inline int          Au_NtkPoNum( Au_Ntk_t * p )                   { return p->nObjs[AU_OBJ_PO];                                            } 
static inline int          Au_NtkFanNum( Au_Ntk_t * p )                  { return p->nObjs[AU_OBJ_FAN];                                           } 
static inline int          Au_NtkFlopNum( Au_Ntk_t * p )                 { return p->nObjs[AU_OBJ_FLOP];                                          } 
static inline int          Au_NtkBoxNum( Au_Ntk_t * p )                  { return p->nObjs[AU_OBJ_BOX];                                           } 
static inline int          Au_NtkNodeNum( Au_Ntk_t * p )                 { return p->nObjs[AU_OBJ_NODE];                                          } 
static inline int          Au_NtkObjNumMax( Au_Ntk_t * p )               { return (Vec_PtrSize(&p->vPages) - 1) * (1 << 12) + p->iHandle;         } 
static inline int          Au_NtkObjNum( Au_Ntk_t * p )                  { return Vec_IntSize(&p->vObjs);                                         } 
static inline Au_Obj_t *   Au_NtkObj( Au_Ntk_t * p, int h )              { return (Au_Obj_t *)p->vPages.pArray[h >> 12] + (h & 0xFFF);            }

static inline Au_Obj_t *   Au_NtkPi( Au_Ntk_t * p, int i )               { return Au_NtkObj(p, Vec_IntEntry(&p->vPis, i));                        }
static inline Au_Obj_t *   Au_NtkPo( Au_Ntk_t * p, int i )               { return Au_NtkObj(p, Vec_IntEntry(&p->vPos, i));                        }
static inline Au_Obj_t *   Au_NtkObjI( Au_Ntk_t * p, int i )             { return Au_NtkObj(p, Vec_IntEntry(&p->vObjs, i));                       }

static inline int          Au_ObjIsNone( Au_Obj_t * p )                  { return p->Type == AU_OBJ_NONE;                                         } 
static inline int          Au_ObjIsConst0( Au_Obj_t * p )                { return p->Type == AU_OBJ_CONST0;                                       } 
static inline int          Au_ObjIsPi( Au_Obj_t * p )                    { return p->Type == AU_OBJ_PI;                                           } 
static inline int          Au_ObjIsPo( Au_Obj_t * p )                    { return p->Type == AU_OBJ_PO;                                           } 
static inline int          Au_ObjIsFan( Au_Obj_t * p )                   { return p->Type == AU_OBJ_FAN;                                          } 
static inline int          Au_ObjIsFlop( Au_Obj_t * p )                  { return p->Type == AU_OBJ_FLOP;                                         } 
static inline int          Au_ObjIsBox( Au_Obj_t * p )                   { return p->Type == AU_OBJ_BOX;                                          } 
static inline int          Au_ObjIsNode( Au_Obj_t * p )                  { return p->Type == AU_OBJ_NODE;                                         }
static inline int          Au_ObjIsTerm( Au_Obj_t * p )                  { return p->Type >= AU_OBJ_PI && p->Type <= AU_OBJ_FLOP;                 } 

static inline char *       Au_ObjBase( Au_Obj_t * p )                    { return (char *)p - ((ABC_PTRINT_T)p & 0x3FF);                          } 
static inline Au_Ntk_t *   Au_ObjNtk( Au_Obj_t * p )                     { return ((Au_Ntk_t **)Au_ObjBase(p))[0];                                } 
static inline int          Au_ObjId( Au_Obj_t * p )                      { return ((int *)Au_ObjBase(p))[2] | (((ABC_PTRINT_T)p & 0x3FF) >> 4);   }
static inline int          Au_ObjPioNum( Au_Obj_t * p )                  { assert(Au_ObjIsTerm(p)); return p->Fanins[p->nFanins];                 }
static inline int          Au_ObjFunc( Au_Obj_t * p )                    { return p->Func;                                                        }
static inline Au_Ntk_t *   Au_ObjNtkel( Au_Obj_t * p )                   { assert(Au_ObjIsFan(p)||Au_ObjIsBox(p)); return Au_ManNtk(Au_NtkMan(Au_ObjNtk(p)), p->Func); }

static inline int          Au_ObjFaninNum( Au_Obj_t * p )                { return p->nFanins;                                                     }
static inline int          Au_ObjFaninId( Au_Obj_t * p, int i )          { assert(i >= 0 && i < (int)p->nFanins && p->Fanins[i]); return Au_Lit2Var(p->Fanins[i]);     }
static inline int          Au_ObjFaninId0( Au_Obj_t * p )                { return Au_ObjFaninId(p, 0);                                                                 }
static inline int          Au_ObjFaninId1( Au_Obj_t * p )                { return Au_ObjFaninId(p, 1);                                                                 }
static inline Au_Obj_t *   Au_ObjFanin( Au_Obj_t * p, int i )            { return Au_NtkObj(Au_ObjNtk(p), Au_ObjFaninId(p, i));                                        }
static inline Au_Obj_t *   Au_ObjFanin0( Au_Obj_t * p )                  { return Au_ObjFanin( p, 0 );                                                                 }
static inline Au_Obj_t *   Au_ObjFanin1( Au_Obj_t * p )                  { return Au_ObjFanin( p, 1 );                                                                 }
static inline int          Au_ObjFaninC( Au_Obj_t * p, int i )           { assert(i >= 0 && i < (int)p->nFanins && p->Fanins[i]); return Au_LitIsCompl(p->Fanins[i]);  }
static inline int          Au_ObjFaninC0( Au_Obj_t * p )                 { return Au_ObjFaninC(p, 0);                                                                  }
static inline int          Au_ObjFaninC1( Au_Obj_t * p )                 { return Au_ObjFaninC(p, 1);                                                                  }
static inline int          Au_ObjFaninLit( Au_Obj_t * p, int i )         { assert(i >= 0 && i < (int)p->nFanins && p->Fanins[i]); return p->Fanins[i];                 }
static inline void         Au_ObjSetFanin( Au_Obj_t * p, int i, int f )  { assert(f > 0 && p->Fanins[i] == 0); p->Fanins[i] = Au_Var2Lit(f,0);                         }
static inline void         Au_ObjSetFaninLit( Au_Obj_t * p, int i, int f){ assert(f >= 0 && p->Fanins[i] == 0); p->Fanins[i] = f;                                      }

static inline int          Au_BoxFanoutNum( Au_Obj_t * p )               { assert(Au_ObjIsBox(p)); return p->Fanins[p->nFanins];                                       }
static inline int          Au_BoxFanoutId( Au_Obj_t * p, int i )         { assert(i >= 0 && i < Au_BoxFanoutNum(p)); return p->Fanins[p->nFanins+1+i];                 }
static inline Au_Obj_t *   Au_BoxFanout( Au_Obj_t * p, int i )           { return Au_NtkObj(Au_ObjNtk(p), Au_BoxFanoutId(p, i));                                       }

static inline int          Au_ObjCopy( Au_Obj_t * p )                    { return Vec_IntEntry( &Au_ObjNtk(p)->vCopies, Au_ObjId(p) );                                 }
static inline void         Au_ObjSetCopy( Au_Obj_t * p, int c )          { Vec_IntWriteEntry( &Au_ObjNtk(p)->vCopies, Au_ObjId(p), c );                                }

static inline int          Au_ObjFanout( Au_Obj_t * p, int i )           { assert(p->Type == AU_OBJ_BOX && i >= 0 && i < p->Fanins[p->nFanins] && p->Fanins[i]); return p->Fanins[p->nFanins + 1 + i];             }
static inline int          Au_ObjSetFanout( Au_Obj_t * p, int i, int f ) { assert(p->Type == AU_OBJ_BOX && i >= 0 && i < p->Fanins[p->nFanins] && p->Fanins[i] == 0 && f > 0); p->Fanins[p->nFanins + 1 + i] = f;  }

static inline void         Au_NtkIncrementTravId( Au_Ntk_t * p )            { if (p->vTravIds.pArray == NULL) Vec_IntFill(&p->vTravIds, Au_NtkObjNumMax(p)+500, 0); p->nTravIds++; assert(p->nTravIds < (1<<30));  }
static inline void         Au_ObjSetTravIdCurrent( Au_Obj_t * p )           { Vec_IntSetEntry(&Au_ObjNtk(p)->vTravIds, Au_ObjId(p), Au_ObjNtk(p)->nTravIds );                        }
static inline void         Au_ObjSetTravIdPrevious( Au_Obj_t * p )          { Vec_IntSetEntry(&Au_ObjNtk(p)->vTravIds, Au_ObjId(p), Au_ObjNtk(p)->nTravIds-1 );                      }
static inline int          Au_ObjIsTravIdCurrent( Au_Obj_t * p )            { return (Vec_IntGetEntry(&Au_ObjNtk(p)->vTravIds, Au_ObjId(p)) == Au_ObjNtk(p)->nTravIds);              }
static inline int          Au_ObjIsTravIdPrevious( Au_Obj_t * p )           { return (Vec_IntGetEntry(&Au_ObjNtk(p)->vTravIds, Au_ObjId(p)) == Au_ObjNtk(p)->nTravIds-1);            }
static inline void         Au_ObjSetTravIdCurrentId( Au_Ntk_t * p, int Id ) { Vec_IntSetEntry(&p->vTravIds, Id, p->nTravIds );                                                       }
static inline int          Au_ObjIsTravIdCurrentId( Au_Ntk_t * p, int Id )  { return (Vec_IntGetEntry(&p->vTravIds, Id) == p->nTravIds);                                             }

#define Au_ManForEachNtk( p, pNtk, i )           \
    for ( i = 1; (i < Vec_PtrSize(&p->vNtks))   && (((pNtk) = Au_ManNtk(p, i)), 1); i++ ) 
#define Au_ManForEachNtkReverse( p, pNtk, i )    \
    for ( i = Vec_PtrSize(&p->vNtks) - 1;(i>=1) && (((pNtk) = Au_ManNtk(p, i)), 1); i-- ) 

#define Au_ObjForEachFaninId( pObj, hFanin, i )  \
    for ( i = 0; (i < Au_ObjFaninNum(pObj))     && (((hFanin) = Au_ObjFaninId(pObj, i)), 1); i++ )  
#define Au_BoxForEachFanoutId( pObj, hFanout, i) \
    for ( i = 0; (i < Au_BoxFanoutNum(pObj))    && (((hFanout) = Au_BoxFanoutId(pObj, i)), 1); i++ )

#define Au_ObjForEachFanin( pObj, pFanin, i )    \
    for ( i = 0; (i < Au_ObjFaninNum(pObj))     && (((pFanin) = Au_ObjFanin(pObj, i)), 1); i++ )  
#define Au_BoxForEachFanout( pObj, pFanout, i)   \
    for ( i = 0; (i < Au_BoxFanoutNum(pObj))    && (((pFanout) = Au_BoxFanout(pObj, i)), 1); i++ )

#define Au_NtkForEachPi( p, pObj, i )            \
    for ( i = 0; (i < Vec_IntSize(&p->vPis))    && (((pObj) = Au_NtkPi(p, i)), 1); i++ )
#define Au_NtkForEachPo( p, pObj, i )            \
    for ( i = 0; (i < Vec_IntSize(&p->vPos))    && (((pObj) = Au_NtkPo(p, i)), 1); i++ )
#define Au_NtkForEachObj( p, pObj, i )           \
    for ( i = 0; (i < Vec_IntSize(&p->vObjs))   && (((pObj) = Au_NtkObjI(p, i)), 1); i++ )
#define Au_NtkForEachBox( p, pObj, i )           \
    for ( i = 0; (i < Vec_IntSize(&p->vObjs))   && (((pObj) = Au_NtkObjI(p, i)), 1); i++ ) if ( !Au_ObjIsBox(pObj) ) {} else


extern void Au_ManAddNtk( Au_Man_t * pMan, Au_Ntk_t * p );
extern void Au_ManFree( Au_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Working with models.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Au_Ntk_t * Au_NtkAlloc( Au_Man_t * pMan, char * pName )
{
    Au_Ntk_t * p;
    p = ABC_CALLOC( Au_Ntk_t, 1 );
    p->pName = Au_UtilStrsav( pName );
    p->vChunks = Vec_PtrAlloc( 111 );
    Vec_IntGrow( &p->vPis,  111 );
    Vec_IntGrow( &p->vPos,  111 );
    Vec_IntGrow( &p->vObjs, 1111 );
    Vec_PtrGrow( &p->vPages, 11 );
    Au_ManAddNtk( pMan, p );
    return p;
}
void Au_NtkFree( Au_Ntk_t * p )
{
    Au_ManFree( p->pMan );
    Vec_PtrFreeFree( p->vChunks );
    ABC_FREE( p->vCopies.pArray );
    ABC_FREE( p->vPages.pArray );
    ABC_FREE( p->vObjs.pArray );
    ABC_FREE( p->vPis.pArray );
    ABC_FREE( p->vPos.pArray );
    ABC_FREE( p->pHTable );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
int Au_NtkMemUsage( Au_Ntk_t * p )
{
    int Mem = sizeof(Au_Ntk_t);
    Mem += 4 * p->vPis.nCap;
    Mem += 4 * p->vPos.nCap;
    Mem += 4 * p->vObjs.nCap;
    Mem += 16 * p->nObjsAlloc;
    return Mem;
}
void Au_NtkPrintStats( Au_Ntk_t * p )
{
    printf( "%-30s:",        Au_NtkName(p) );
    printf( " i/o =%6d/%6d", Au_NtkPiNum(p), Au_NtkPoNum(p) );
    if ( Au_NtkFlopNum(p) )
        printf( "  lat =%5d",    Au_NtkFlopNum(p) );
    printf( "  nd =%6d",     Au_NtkNodeNum(p) );
    if ( Au_NtkBoxNum(p) )
        printf( "  box =%5d",    Au_NtkBoxNum(p) );
    printf( "  obj =%7d",    Au_NtkObjNum(p) );
//    printf( "  max =%7d",    Au_NtkObjNumMax(p) );
//    printf( "  use =%7d",    p->nObjsUsed );
    printf( " %5.1f %%",     100.0 * (Au_NtkObjNumMax(p) - Au_NtkObjNum(p)) / Au_NtkObjNumMax(p) );
    printf( " %6.1f Mb",     1.0 * Au_NtkMemUsage(p) / (1 << 20) );
    printf( " %5.1f %%",     100.0 * (p->nObjsAlloc - p->nObjsUsed) / p->nObjsAlloc );
    printf( "\n" );
}
void Au_NtkCleanCopy( Au_Ntk_t * p )
{
    Vec_IntFill( &p->vCopies, Au_NtkObjNumMax(p), -1 );
}

/**Function*************************************************************

  Synopsis    [Working with manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Au_Man_t * Au_ManAlloc( char * pName )
{
    Au_Man_t * p;
    p = ABC_CALLOC( Au_Man_t, 1 );
    p->pName = Au_UtilStrsav( pName );
    Vec_PtrGrow( &p->vNtks,  111 );
    Vec_PtrPush( &p->vNtks, NULL );
    return p;
}
void Au_ManFree( Au_Man_t * p )
{
    assert( p->nRefs > 0 );
    if ( --p->nRefs > 0 )
        return;
    if ( p->pFuncs )
        Abc_NamStop( p->pFuncs );
    ABC_FREE( p->vNtks.pArray );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
void Au_ManDelete( Au_Man_t * p )
{
    Au_Ntk_t * pNtk;
    int i;
    Au_ManForEachNtk( p, pNtk, i )
        Au_NtkFree( pNtk );
}
int Au_ManFindNtk( Au_Man_t * p, char * pName )
{
    Au_Ntk_t * pNtk;
    int i;
    Au_ManForEachNtk( p, pNtk, i )
        if ( !strcmp(Au_NtkName(pNtk), pName) )
            return i;
    return -1;
}
void Au_ManAddNtk( Au_Man_t * pMan, Au_Ntk_t * p )
{
    assert( Au_ManFindNtk(pMan, Au_NtkName(p)) == -1 );
    p->pMan = pMan; pMan->nRefs++;
    p->Id = Vec_PtrSize( &pMan->vNtks );
    Vec_PtrPush( &pMan->vNtks, p );
}
int Au_ManMemUsage( Au_Man_t * p )
{
    Au_Ntk_t * pNtk;
    int i, Mem = 0;
    Au_ManForEachNtk( p, pNtk, i )
        Mem += 16 * pNtk->nObjsAlloc;
    return Mem;
}
int Au_ManMemUsageUseful( Au_Man_t * p )
{
    Au_Ntk_t * pNtk;
    int i, Mem = 0;
    Au_ManForEachNtk( p, pNtk, i )
        Mem += 16 * pNtk->nObjsUsed;
    return Mem;
}
void Au_ManPrintStats( Au_Man_t * p )
{
    Au_Ntk_t * pNtk;
    int i;
    if ( Vec_PtrSize(&p->vNtks) > 2 )
        printf( "Design %-13s\n", Au_ManName(p) );
    Au_ManForEachNtk( p, pNtk, i )
        Au_NtkPrintStats( pNtk );
    printf( "Different functions = %d. ", p->pFuncs ? Abc_NamObjNumMax(p->pFuncs) : 0 );
    printf( "Memory = %.1f Mb",  1.0 * Au_ManMemUsage(p) / (1 << 20) );
    printf( " %5.1f %%",       100.0 * (Au_ManMemUsage(p) - Au_ManMemUsageUseful(p)) / Au_ManMemUsage(p) );
    printf( "\n" );
//    Abc_NamPrint( pMan->pFuncs );
}

// count the number of support variables
int Au_ObjSuppSize_rec( Au_Ntk_t * p, int Id )
{
    Au_Obj_t * pObj;
    int i, iFanin, Counter = 0;
    if ( Au_ObjIsTravIdCurrentId(p, Id) )
        return 0;
    Au_ObjSetTravIdCurrentId(p, Id);
    pObj = Au_NtkObj( p, Id );
    if ( Au_ObjIsPi(pObj) )
        return 1;
    assert( Au_ObjIsNode(pObj) || Au_ObjIsBox(pObj) || Au_ObjIsFan(pObj) );
    Au_ObjForEachFaninId( pObj, iFanin, i )
        Counter += Au_ObjSuppSize_rec( p, iFanin );
    return Counter;
}
int Au_ObjSuppSize( Au_Obj_t * pObj )
{
    Au_Ntk_t * p = Au_ObjNtk(pObj);
    Au_NtkIncrementTravId( p );
    return Au_ObjSuppSize_rec( p, Au_ObjId(pObj) );
}
/*
// this version is 50% slower than above
int Au_ObjSuppSize_rec( Au_Obj_t * pObj )
{
    Au_Obj_t * pFanin;
    int i, Counter = 0;
    if ( Au_ObjIsTravIdCurrent(pObj) )
        return 0;
    Au_ObjSetTravIdCurrent(pObj);
    if ( Au_ObjIsPi(pObj) )
        return 1;
    assert( Au_ObjIsNode(pObj) || Au_ObjIsBox(pObj) || Au_ObjIsFan(pObj) );
    Au_ObjForEachFanin( pObj, pFanin, i )
        Counter += Au_ObjSuppSize_rec( pFanin );
    return Counter;
}
int Au_ObjSuppSize( Au_Obj_t * pObj )
{
    Au_NtkIncrementTravId( Au_ObjNtk(pObj) );
    return Au_ObjSuppSize_rec( pObj );
}
*/
int Au_NtkSuppSizeTest( Au_Ntk_t * p )
{
    Au_Obj_t * pObj;
    int i, Counter = 0;
    Au_NtkForEachObj( p, pObj, i )
        if ( Au_ObjIsNode(pObj) )
            Counter += (Au_ObjSuppSize(pObj) <= 16);
    printf( "Nodes with small support %d (out of %d)\n", Counter, Au_NtkNodeNum(p) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Returns memory for the next object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Au_NtkInsertHeader( Au_Ntk_t * p )
{
    Au_Obj_t * pMem = (Au_Obj_t *)Vec_PtrEntryLast( &p->vPages );
    assert( (((ABC_PTRINT_T)(pMem + p->iHandle) & 0x3FF) >> 4) == 0 );
    ((Au_Ntk_t **)(pMem + p->iHandle))[0] = p;
    ((int *)(pMem + p->iHandle))[2] = ((Vec_PtrSize(&p->vPages) - 1) << 12) | (p->iHandle & 0xFC0);
    p->iHandle++;
}
int Au_NtkAllocObj( Au_Ntk_t * p, int nFanins, int Type )
{
    Au_Obj_t * pMem, * pObj, * pTemp;
    int nObjInt = ((2+nFanins) >> 2) + (((2+nFanins) & 3) > 0);
    int Id, nObjIntReal = nObjInt;
    if ( nObjInt > 63 )
        nObjInt = 63 + 64 * (((nObjInt-63) >> 6) + (((nObjInt-63) & 63) > 0));
    if ( Vec_PtrSize(&p->vPages) == 0 || p->iHandle + nObjInt > (1 << 12) )
    {
        if ( nObjInt + 64 > (1 << 12) )
            pMem = ABC_CALLOC( Au_Obj_t, nObjInt + 64 ), p->nObjsAlloc += nObjInt + 64;
        else
            pMem = ABC_CALLOC( Au_Obj_t, (1 << 12) + 64 ), p->nObjsAlloc += (1 << 12) + 64;
        Vec_PtrPush( p->vChunks, pMem );
        if ( ((ABC_PTRINT_T)pMem & 0xF) )
            pMem = (Au_Obj_t *)((char *)pMem + 16 - ((ABC_PTRINT_T)pMem & 0xF));
        assert( ((ABC_PTRINT_T)pMem & 0xF) == 0 );
        p->iHandle = (((ABC_PTRINT_T)pMem & 0x3FF) >> 4);
        if ( p->iHandle )
        {
            pMem += 64 - (p->iHandle & 63);
            p->iHandle = 0; 
        }
        Vec_PtrPush( &p->vPages, pMem );
        Au_NtkInsertHeader( p );
    }
    else
    {
        pMem = (Au_Obj_t *)Vec_PtrEntryLast( &p->vPages );
        if ( (p->iHandle & 63) == 0 || nObjInt > (64 - (p->iHandle & 63)) )
        {
            if ( p->iHandle & 63 )
                p->iHandle += 64 - (p->iHandle & 63); 
            Au_NtkInsertHeader( p );
        }
        if ( p->iHandle + nObjInt > (1 << 12) )
            return Au_NtkAllocObj( p, nFanins, Type );
    }
    pObj = pMem + p->iHandle;
    assert( *((int *)pObj) == 0 );
    pObj->nFanins = nFanins;
    p->nObjs[pObj->Type = Type]++;
    if ( Type == AU_OBJ_PI )
    {
        Au_ObjSetFaninLit( pObj, 0, Vec_IntSize(&p->vPis) );
        Vec_IntPush( &p->vPis, Au_ObjId(pObj) );
    }
    else if ( Type == AU_OBJ_PO )
    {
        Au_ObjSetFaninLit( pObj, 1, Vec_IntSize(&p->vPos) );
        Vec_IntPush( &p->vPos, Au_ObjId(pObj) );
    }
    p->iHandle += nObjInt;
    p->nObjsUsed += nObjIntReal;

    Id = Au_ObjId(pObj);
    Vec_IntPush( &p->vObjs, Id );
    pTemp = Au_NtkObj( p, Id );
    assert( pTemp == pObj );
    return Id;
}
int Au_NtkCreateConst0( Au_Ntk_t * pNtk )
{
    return Au_NtkAllocObj( pNtk, 0, AU_OBJ_CONST0 );
}
int Au_NtkCreatePi( Au_Ntk_t * pNtk )
{
    return Au_NtkAllocObj( pNtk, 0, AU_OBJ_PI );
}
int Au_NtkCreatePo( Au_Ntk_t * pNtk, int iFanin )
{
    int Id = Au_NtkAllocObj( pNtk, 1, AU_OBJ_PO );
    if ( iFanin )
        Au_ObjSetFaninLit( Au_NtkObj(pNtk, Id), 0, iFanin );
    return Id;
}
int Au_NtkCreateFan( Au_Ntk_t * pNtk, int iFanin, int iFanout, int iModel )
{
    int Id = Au_NtkAllocObj( pNtk, 1, AU_OBJ_FAN );
    Au_Obj_t * p = Au_NtkObj( pNtk, Id );
    if ( iFanin )
        Au_ObjSetFaninLit( p, 0, iFanin );
    Au_ObjSetFaninLit( p, 1, iFanout );
    p->Func = iModel;
    return Id;
}
int Au_NtkCreateNode( Au_Ntk_t * pNtk, Vec_Int_t * vFanins, int iFunc )
{
    int i, iFanin;
    int Id = Au_NtkAllocObj( pNtk, Vec_IntSize(vFanins), AU_OBJ_NODE );
    Au_Obj_t * p = Au_NtkObj( pNtk, Id );
    Vec_IntForEachEntry( vFanins, iFanin, i )
        Au_ObjSetFaninLit( p, i, iFanin );
    p->Func = iFunc;
    return Id;
}
int Au_NtkCreateBox( Au_Ntk_t * pNtk, Vec_Int_t * vFanins, int nFanouts, int iModel )
{
    int i, iFanin, nFanins = Vec_IntSize(vFanins);
    int Id = Au_NtkAllocObj( pNtk, nFanins + 1 + nFanouts, AU_OBJ_BOX );
    Au_Obj_t * p = Au_NtkObj( pNtk, Id );
    Vec_IntForEachEntry( vFanins, iFanin, i )
        Au_ObjSetFaninLit( p, i, iFanin );
    Au_ObjSetFaninLit( p, nFanins, nFanouts );
    for ( i = 0; i < nFanouts; i++ )
        Au_ObjSetFaninLit( p, nFanins + 1 + i, Au_NtkCreateFan(pNtk, Au_Var2Lit(Id,0), i, iModel) );
    p->nFanins = nFanins;
    p->Func = iModel;
    assert( iModel > 0 );
    return Id;
}

/*
 * 0/1 would denote false/true respectively.
 * Signals would be even numbers, and negation would be handled by xor with 1.
 * The output signal for each gate or subckt could be implicitly generated just use the next signal number.
 * For ranges, we could use "start:cnt" to denote the sequence "start, start+2, ..., start + 2*(cnt- 1)".
    - "cnt" seems more intuitive when signals are restricted to even numbers.
 * We'd have subckts and specialized gates .and, .xor, and .mux.

Here is a small example:

.model test
.inputs 3 # Inputs 2 4 6
.subckt and3 3 1 2:3 # 8 is implicit output
.outputs 1 8
.end

.model and3
.inputs 3 # Inputs 2 4 6
.and 2 4 # 8 output
.and 6 8 # 10 output
.outputs 1 10
.end
*/

/**Function*************************************************************

  Synopsis    [Reads one entry.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Au_NtkRemapNum( Vec_Int_t * vNum2Obj, int Num )
{
    return Au_Var2Lit(Vec_IntEntry(vNum2Obj, Au_Lit2Var(Num)), Au_LitIsCompl(Num));
}
/**Function*************************************************************

  Synopsis    [Reads one entry.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Au_NtkParseCBlifNum( Vec_Int_t * vFanins, char * pToken, Vec_Int_t * vNum2Obj )
{
    char * pCur;
    int Num1, Num2, i;
    assert( pToken[0] >= '0' && pToken[0] <= '9' );
    Num1 = atoi( pToken );
    for ( pCur = pToken; *pCur; pCur++ )
        if ( *pCur == ':' )
        {
            Num2 = atoi( pCur+1 );
            for ( i = 0; i < Num2; i++ )
                Vec_IntPush( vFanins, Au_NtkRemapNum(vNum2Obj, Num1 + i + i) );
            return;
        }
        else if ( *pCur == '*' )
        {
            Num2 = atoi( pCur+1 );
            for ( i = 0; i < Num2; i++ )
                Vec_IntPush( vFanins, Au_NtkRemapNum(vNum2Obj, Num1) );
            return;
        }
    assert( *pCur == 0 );
    Vec_IntPush( vFanins, Au_NtkRemapNum(vNum2Obj, Num1) );
}

/**Function*************************************************************

  Synopsis    [Parses CBLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Au_Ntk_t * Au_NtkParseCBlif( char * pFileName )
{
    extern char * Extra_FileRead( FILE * pFile );
    FILE * pFile;
    Au_Man_t * pMan;
    Au_Ntk_t * pRoot;
    Au_Obj_t * pBox, * pFan;
    char * pBuffer, * pCur;
    Vec_Int_t * vLines, * vNum2Obj, * vFanins;
    int i, k, j, Id, nInputs, nOutputs;
    int Line, Num, Func;
    // read the file
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\".\n", pFileName );
        return NULL;
    }
    pBuffer = Extra_FileRead( pFile );
    fclose( pFile );
    // split into lines
    vLines = Vec_IntAlloc( 1000 );
    Vec_IntPush( vLines, 0 );
    for ( pCur = pBuffer; *pCur; pCur++ )
        if ( *pCur == '\n' )
        {
            *pCur = 0;
            Vec_IntPush( vLines, pCur - pBuffer + 1 );
        }
    // start the manager
    pMan = Au_ManAlloc( pFileName );
    // parse the lines
    vNum2Obj = Vec_IntAlloc( 1000 );
    vFanins = Vec_IntAlloc( 1000 );
    Vec_IntForEachEntry( vLines, Line, i )
    {
        pCur = strtok( pBuffer + Line, " \t\r" );
        if ( pCur == NULL || *pCur == '#' )
            continue;
        if ( *pCur != '.' )
        {
            printf( "Cannot read directive in line %d: \"%s\".\n", i, pBuffer + Line );
            continue;
        }
        Vec_IntClear( vFanins );
        if ( !strcmp(pCur, ".and") )
        {
            for ( k = 0; k < 2; k++ )
            {
                pCur = strtok( NULL, " \t\r" );
                Num  = atoi( pCur );
                Vec_IntPush( vFanins, Au_NtkRemapNum(vNum2Obj, Num) );
            }
            Id = Au_NtkCreateNode( pRoot, vFanins, 1 );
            Vec_IntPush( vNum2Obj, Id );
        }
        else if ( !strcmp(pCur, ".xor") )
        {
            for ( k = 0; k < 2; k++ )
            {
                pCur = strtok( NULL, " \t\r" );
                Num  = atoi( pCur );
                Vec_IntPush( vFanins, Au_NtkRemapNum(vNum2Obj, Num) );
            }
            Id = Au_NtkCreateNode( pRoot, vFanins, 2 );
            Vec_IntPush( vNum2Obj, Id );
        }
        else if ( !strcmp(pCur, ".mux") )
        {
            for ( k = 0; k < 3; k++ )
            {
                pCur = strtok( NULL, " \t\r" );
                Num  = atoi( pCur );
                Vec_IntPush( vFanins, Au_NtkRemapNum(vNum2Obj, Num) );
            }
            Id = Au_NtkCreateNode( pRoot, vFanins, 3 );
            Vec_IntPush( vNum2Obj, Id );
        }
        else if ( !strcmp(pCur, ".subckt") )
        {
            pCur = strtok( NULL, " \t\r" );
            Func = pCur - pBuffer;
            pCur = strtok( NULL, " \t\r" );
            nInputs = atoi( pCur );
            pCur = strtok( NULL, " \t\r" );
            nOutputs = atoi( pCur );
            while ( 1 )
            {
                pCur = strtok( NULL, " \t\r" );
                if ( pCur == NULL || *pCur == '#' )
                    break;
                Au_NtkParseCBlifNum( vFanins, pCur, vNum2Obj );
            }
            assert( Vec_IntSize(vFanins) == nInputs );
            Id = Au_NtkCreateBox( pRoot, vFanins, nOutputs, Func );
            pBox = Au_NtkObj( pRoot, Id );
            Au_BoxForEachFanoutId( pBox, Num, k )
                Vec_IntPush( vNum2Obj, Num );
        }
        else if ( !strcmp(pCur, ".model") )
        {
            pCur  = strtok( NULL, " \t\r" );
            pRoot = Au_NtkAlloc( pMan, pCur );
            Id    = Au_NtkCreateConst0( pRoot );
            Vec_IntClear( vNum2Obj );
            Vec_IntPush( vNum2Obj, Id );
        }
        else if ( !strcmp(pCur, ".inputs") )
        {
            pCur = strtok( NULL, " \t\r" );
            Num  = atoi( pCur );
            for ( k = 0; k < Num; k++ )
                Vec_IntPush( vNum2Obj, Au_NtkCreatePi(pRoot) );
        }
        else if ( !strcmp(pCur, ".outputs") )
        {
            pCur = strtok( NULL, " \t\r" );
            nOutputs = atoi( pCur );
            while ( 1 )
            {
                pCur = strtok( NULL, " \t\r" );
                if ( pCur == NULL || *pCur == '#' )
                    break; 
                Au_NtkParseCBlifNum( vFanins, pCur, vNum2Obj );
            }
            assert( Vec_IntSize(vFanins) == nOutputs );
            Vec_IntForEachEntry( vFanins, Num, k )
                Au_NtkCreatePo( pRoot, Num );
        }
        else if ( strcmp(pCur, ".end") )
            printf( "Unknown directive in line %d: \"%s\".\n", i, pBuffer + Line );
    }
    Vec_IntFree( vFanins );
    Vec_IntFree( vNum2Obj );
    Vec_IntFree( vLines );
    // set pointers to models
    Au_ManForEachNtk( pMan, pRoot, i )
        Au_NtkForEachBox( pRoot, pBox, k )
        {
            pBox->Func = Au_ManFindNtk( pMan, pBuffer + pBox->Func );
            assert( pBox->Func > 0 );
            Au_BoxForEachFanout( pBox, pFan, j )
                pFan->Func = pBox->Func;
        }
    ABC_FREE( pBuffer );
    // return the root network
    return (Au_Ntk_t *)Vec_PtrEntry( &pMan->vNtks, 1 );
}


#include "abc.h"
#include "gia.h"

extern Vec_Ptr_t * Abc_NtkDfsBoxes( Abc_Ntk_t * pNtk );
extern int Abc_NtkDeriveFlatGiaSop( Gia_Man_t * pGia, int * gFanins, char * pSop );
extern int Abc_NtkCheckRecursive( Abc_Ntk_t * pNtk );

/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Au_NtkDeriveFlatGia_rec( Gia_Man_t * pGia, Au_Ntk_t * p )
{ 
    Au_Obj_t * pObj, * pTerm;
    int i, k, Lit;
    Au_NtkForEachPi( p, pTerm, i )
        assert( Au_ObjCopy(pTerm) >= 0 );
    if ( strcmp(Au_NtkName(p), "ref_egcd") == 0 )
    {
        printf( "Replacing one instance of recursive model \"%s\" by a black box.\n", "ref_egcd" );
        Au_NtkForEachPo( p, pTerm, i )
            Au_ObjSetCopy( pTerm, Gia_ManAppendCi(pGia) );
        return;
    }
    Au_NtkForEachObj( p, pObj, i )
    {
        if ( Au_ObjIsNode(pObj) )
        {
            if ( p->pMan->pFuncs )
            {
                int gFanins[16];
                char * pSop = Abc_NamStr( p->pMan->pFuncs, pObj->Func );
                int nLength = strlen(pSop);
                assert( Au_ObjFaninNum(pObj) <= 16 );
                assert( Au_ObjFaninNum(pObj) == Abc_SopGetVarNum(pSop) );
                Au_ObjForEachFanin( pObj, pTerm, k )
                {
                    gFanins[k] = Au_ObjCopy(pTerm);
                    assert( gFanins[k] >= 0 );
                }
                Lit = Abc_NtkDeriveFlatGiaSop( pGia, gFanins, pSop );
            }
            else
            {
                int Lit0, Lit1, Lit2;
                assert( pObj->Func >= 1 && pObj->Func <= 3 );
                Lit0 = Gia_LitNotCond( Au_ObjCopy(Au_ObjFanin0(pObj)), Au_ObjFaninC0(pObj) );
                Lit1 = Gia_LitNotCond( Au_ObjCopy(Au_ObjFanin1(pObj)), Au_ObjFaninC1(pObj) );
                if ( pObj->Func == 1 )
                    Lit = Gia_ManHashAnd( pGia, Lit0, Lit1 );
                else if ( pObj->Func == 2 )
                    Lit = Gia_ManHashXor( pGia, Lit0, Lit1 );
                else if ( pObj->Func == 3 )
                {
                    Lit2 = Gia_LitNotCond( Au_ObjCopy(Au_ObjFanin(pObj, 2)), Au_ObjFaninC(pObj, 2) );
                    Lit = Gia_ManHashMux( pGia, Lit0, Lit1, Lit2 );
                }
                else assert( 0 ); 
            } 
            assert( Lit >= 0 );
            Au_ObjSetCopy( pObj, Lit );
        }
        else if ( Au_ObjIsBox(pObj) )
        {
            Au_Ntk_t * pModel = Au_ObjNtkel(pObj);
            Au_NtkCleanCopy( pModel );
            // check the match between the number of actual and formal parameters
            assert( Au_ObjFaninNum(pObj) == Au_NtkPiNum(pModel) );
            assert( Au_BoxFanoutNum(pObj) == Au_NtkPoNum(pModel) );
            // assign PIs
            Au_ObjForEachFanin( pObj, pTerm, k )
                Au_ObjSetCopy( Au_NtkPi(pModel, k), Au_ObjCopy(pTerm) );
            // call recursively
            Au_NtkDeriveFlatGia_rec( pGia, pModel );
            // assign POs
            Au_BoxForEachFanout( pObj, pTerm, k )
                Au_ObjSetCopy( pTerm, Au_ObjCopy(Au_NtkPo(pModel, k)) );
        }
        else if ( Au_ObjIsConst0(pObj) )
            Au_ObjSetCopy( pObj, 0 );
            
    }
    Au_NtkForEachPo( p, pTerm, i )
    {
        Lit = Gia_LitNotCond( Au_ObjCopy(Au_ObjFanin0(pTerm)), Au_ObjFaninC0(pTerm) );
        Au_ObjSetCopy( pTerm, Lit );
    }
    Au_NtkForEachPo( p, pTerm, i )
        assert( Au_ObjCopy(pTerm) >= 0 );
//    p->pMan->nGiaObjMax = Abc_MaxInt( p->pMan->nGiaObjMax, Gia_ManObjNum(pGia) );
}

/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Au_NtkDeriveFlatGia( Au_Ntk_t * p )
{
    Gia_Man_t * pTemp, * pGia = NULL;
    Au_Obj_t * pTerm;
    int i;
    Au_NtkCleanCopy( p );
    // start the network
    pGia = Gia_ManStart( (1<<16) );
    pGia->pName = Gia_UtilStrsav( Au_NtkName(p) );
    Gia_ManHashAlloc( pGia );
    Gia_ManFlipVerbose( pGia );
    // create PIs
    Au_NtkForEachPi( p, pTerm, i )
        Au_ObjSetCopy( pTerm, Gia_ManAppendCi(pGia) );
    // recursively flatten hierarchy
    Au_NtkDeriveFlatGia_rec( pGia, p );
    // create POs
    Au_NtkForEachPo( p, pTerm, i )
        Gia_ManAppendCo( pGia, Au_ObjCopy(pTerm) );
    // prepare return value
    Gia_ManHashStop( pGia );
    Gia_ManSetRegNum( pGia, 0 );
    pGia = Gia_ManCleanup( pTemp = pGia );
    Gia_ManStop( pTemp );
    return pGia;
}


/**Function*************************************************************

  Synopsis    [Duplicates ABC network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Au_Ntk_t * Au_NtkDerive( Au_Man_t * pMan, Abc_Ntk_t * pNtk, Vec_Ptr_t * vOrder )
{
    Au_Ntk_t * p;
    Au_Obj_t * pAuObj;
    Abc_Obj_t * pObj, * pTerm;
//    Vec_Ptr_t * vOrder;
    Vec_Int_t * vFanins;
    int i, k, iFunc;
    assert( Abc_NtkIsNetlist(pNtk) );
    Abc_NtkCleanCopy( pNtk );
    p = Au_NtkAlloc( pMan, Abc_NtkName(pNtk) );
    // copy PIs
    Abc_NtkForEachPi( pNtk, pTerm, i )
        Abc_ObjFanout0(pTerm)->iTemp = Au_NtkCreatePi(p);
    // copy nodes and boxes
    vFanins = Vec_IntAlloc( 100 );
//    vOrder = Abc_NtkDfsBoxes( pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vOrder, pObj, i )
    {
        Vec_IntClear( vFanins );
        if ( Abc_ObjIsNode(pObj) )
        {
            Abc_ObjForEachFanin( pObj, pTerm, k )
                Vec_IntPush( vFanins, Au_Var2Lit(pTerm->iTemp, 0) );
            iFunc = Abc_NamStrFindOrAdd( pMan->pFuncs, (char *)pObj->pData, NULL );
            Abc_ObjFanout0(pObj)->iTemp = Au_NtkCreateNode(p, vFanins, iFunc);
            continue;
        }
        assert( Abc_ObjIsBox(pObj) );
        Abc_ObjForEachFanin( pObj, pTerm, k )
            Vec_IntPush( vFanins, Au_Var2Lit(Abc_ObjFanin0(pTerm)->iTemp, 0) );
        pObj->iTemp = Au_NtkCreateBox(p, vFanins, Abc_ObjFanoutNum(pObj), ((Abc_Ntk_t *)pObj->pData)->iStep );
        pAuObj = Au_NtkObj(p, pObj->iTemp);
        Abc_ObjForEachFanout( pObj, pTerm, k )
            Abc_ObjFanout0(pTerm)->iTemp = Au_ObjFanout(pAuObj, k);
    }
//    Vec_PtrFree( vOrder );
    Vec_IntFree( vFanins );
    // copy POs
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Au_NtkCreatePo( p, Au_Var2Lit(Abc_ObjFanin0(pTerm)->iTemp, 0) );

//    Au_NtkPrintStats( p );
    return p;
}

Gia_Man_t * Au_ManDeriveTest( Abc_Ntk_t * pRoot )
{
    extern Vec_Ptr_t * Abc_NtkCollectHie( Abc_Ntk_t * pNtk );

    Gia_Man_t * pGia = NULL;
    Vec_Ptr_t * vOrder, * vModels;
    Abc_Ntk_t * pMod;
    Au_Man_t * pMan;
    Au_Ntk_t * pNtk;
    int i, clk1, clk2 = 0, clk3 = 0, clk4 = 0, clk = clock();

    clk1 = clock();
    pMan = Au_ManAlloc( pRoot->pDesign ? pRoot->pDesign->pName : pRoot->pName );
    pMan->pFuncs = Abc_NamStart( 100, 16 );
    clk2 += clock() - clk1;

    vModels = Abc_NtkCollectHie( pRoot );
    Vec_PtrForEachEntry( Abc_Ntk_t *, vModels, pMod, i )
    {
        vOrder = Abc_NtkDfsBoxes( pMod );

        clk1 = clock();
        pNtk = Au_NtkDerive( pMan, pMod, vOrder );
        pMod->iStep = pNtk->Id;
        pMod->pData = pNtk;
        clk2 += clock() - clk1;

        Vec_PtrFree( vOrder );
    }
    Vec_PtrFree( vModels );

    Au_ManPrintStats( pMan );

//    if ( !Abc_NtkCheckRecursive(pRoot) )
    {
        clk1 = clock();
        pGia = Au_NtkDeriveFlatGia( (Au_Ntk_t *)pRoot->pData );
        clk3 = clock() - clk1;
//        printf( "GIA objects max = %d.\n", pMan->nGiaObjMax );
    }

//    clk1 = clock();
//    Au_NtkSuppSizeTest( (Au_Ntk_t *)pRoot->pData );
//    clk4 = clock() - clk1;

    clk1 = clock();
    Au_ManDelete( pMan );
    clk2 += clock() - clk1;
    
    Abc_PrintTime( 1, "Time all ", clock() - clk );
    Abc_PrintTime( 1, "Time new ", clk2 );
    Abc_PrintTime( 1, "Time GIA ", clk3 );
//    Abc_PrintTime( 1, "Time supp", clk4 );

    return pGia;
}

/**Function*************************************************************

  Synopsis    [Performs hierarchical equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abc_NtkHieCecTest2( char * pFileName, int fVerbose )
{
    Au_Ntk_t * pNtk;
    Gia_Man_t * pGia;
    int clk1 = 0, clk2 = 0, clk3 = 0, clk = clock();

    // read hierarchical netlist
    pNtk = Au_NtkParseCBlif( pFileName );
    if ( pNtk == NULL )
    {
        printf( "Reading CBLIF file has failed.\n" );
        return NULL;
    }
    if ( pNtk->pMan == NULL || pNtk->pMan->vNtks.pArray == NULL )
    {
        printf( "There is no hierarchy information.\n" );
        Au_NtkFree( pNtk );
        return NULL;
    }
    Abc_PrintTime( 1, "Reading file", clock() - clk );

    Au_ManPrintStats( pNtk->pMan );

//    if ( !Abc_NtkCheckRecursive(pNtk) )
    {
        clk1 = clock();
        pGia = Au_NtkDeriveFlatGia( pNtk );
        clk3 = clock() - clk1;
    }

    clk1 = clock();
    Au_ManDelete( pNtk->pMan );
    clk2 += clock() - clk1;
    
    Abc_PrintTime( 1, "Time all ", clock() - clk );
    Abc_PrintTime( 1, "Time new ", clk2 );
    Abc_PrintTime( 1, "Time GIA ", clk3 );
    return pGia;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

