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
    int                    nObjsUsed;          // used objects
    int                    nObjs[AU_OBJ_VOID]; // counter of objects of each type
    // memory for objects
    Vec_Ptr_t *            vChunks;            // memory pages
    Vec_Ptr_t              vPages;             // memory pages
    int                    iHandle;            // currently available ID
    int                    nUseful;            // the number of useful entries
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
static inline int          Au_NtkObjNum( Au_Ntk_t * p )                  { return p->nObjsUsed;                                                   } 
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
static inline Au_Ntk_t *   Au_ObjModel( Au_Obj_t * p )                   { assert(Au_ObjIsFan(p)||Au_ObjIsBox(p)); return Au_ManNtk(Au_NtkMan(Au_ObjNtk(p)), p->Func); }

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
    Mem += 16 * Vec_PtrSize(p->vChunks) * ((1<<12) + 64);
    return Mem;
}
void Au_NtkPrintStats( Au_Ntk_t * p )
{
    printf( "%-32s:",         Au_NtkName(p) );
    printf( " i/o =%6d/%6d",  Au_NtkPiNum(p), Au_NtkPoNum(p) );
//    printf( "  lat =%5d",     Au_NtkFlopNum(p) );
    printf( "  nd =%6d",      Au_NtkNodeNum(p) );
    printf( "  box =%5d",     Au_NtkBoxNum(p) );
    printf( "  obj =%7d",     Au_NtkObjNum(p) );
    printf( "  max =%7d",     Au_NtkObjNumMax(p) );
    printf( "  use =%7d",     p->nUseful );
    printf( "  %4.1f %%",     100.0 * (Au_NtkObjNumMax(p) - p->nUseful) / Au_NtkObjNumMax(p) );
    printf( "  %5.1f Mb",     1.0 * Au_NtkMemUsage(p) / (1 << 20) );
    printf( "\n" );
}
void Au_NtkStartCopy( Au_Ntk_t * p )
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
    p->pFuncs = Abc_NamStart( 100, 16 );
    return p;
}
void Au_ManFree( Au_Man_t * p )
{
    assert( p->nRefs > 0 );
    if ( --p->nRefs > 0 )
        return;
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
        Mem += Au_NtkMemUsage( pNtk );
    return Mem;
}
void Au_ManPrintStats( Au_Man_t * p )
{
    Au_Ntk_t * pNtk;
    int i;
    printf( "Design %-13s\n", Au_ManName(p) );
    Au_ManForEachNtk( p, pNtk, i )
        Au_NtkPrintStats( pNtk );
    printf( "Different functions = %d. ", Abc_NamObjNumMax(p->pFuncs) );
    printf( "Memory = %.2f Mb",  1.0 * Au_ManMemUsage(p) / (1 << 20) );
    printf( "\n" );
//    Abc_NamPrint( pMan->pFuncs );
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
    int Id, nObjInt = ((2+nFanins) >> 2) + (((2+nFanins) & 3) > 0);
    if ( nObjInt > 63 )
    {
        int nObjInt2 = 63 + 64 * (((nObjInt-63) >> 6) + (((nObjInt-63) & 63) > 0));
        assert( nObjInt2 >= nObjInt );
//        if ( nObjInt2 + 64 < (1 << 12) )
//            p->nUseful += nObjInt - nObjInt2;
        nObjInt = nObjInt2;
    }

    if ( Vec_PtrSize(&p->vPages) == 0 || p->iHandle + nObjInt > (1 << 12) )
    {
        if ( nObjInt + 64 > (1 << 12) )
            pMem = ABC_CALLOC( Au_Obj_t, nObjInt + 64 );
        else
            pMem = ABC_CALLOC( Au_Obj_t, (1 << 12) + 64 );
        Vec_PtrPush( p->vChunks, pMem );
        if ( ((ABC_PTRINT_T)pMem & 0xF) )
            pMem = (Au_Obj_t *)((char *)pMem + 16 - ((ABC_PTRINT_T)pMem & 0xF));
        assert( ((ABC_PTRINT_T)pMem & 0xF) == 0 );
        p->iHandle = (((ABC_PTRINT_T)pMem & 0x3FF) >> 4);
        if ( p->iHandle )
        {
            pMem += 64 - (p->iHandle & 63);
            // can introduce p->iHandleMax = (1 << 12) - (64 - (p->iHandle & 63))
            p->iHandle = 0; 
        }
        Vec_PtrPush( &p->vPages, pMem );
        Au_NtkInsertHeader( p );
    }
    else
    {
        pMem = (Au_Obj_t *)Vec_PtrEntryLast( &p->vPages );
        if ( !(p->iHandle & 63) || nObjInt > (64 - (p->iHandle & 63)) )
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
    p->nUseful += nObjInt;
    p->nObjsUsed++;

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
        Au_ObjSetFanin( Au_NtkObj(pNtk, Id), 0, iFanin );
    return Id;
}
int Au_NtkCreateFan( Au_Ntk_t * pNtk, int iFanin, int iFanout, int iModel )
{
    int Id = Au_NtkAllocObj( pNtk, 1, AU_OBJ_FAN );
    Au_Obj_t * p = Au_NtkObj( pNtk, Id );
    if ( iFanin )
        Au_ObjSetFanin( p, 0, iFanin );
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
        Au_ObjSetFanin( p, i, iFanin );
    p->Func = iFunc;
    return Id;
}
int Au_NtkCreateBox( Au_Ntk_t * pNtk, Vec_Int_t * vFanins, int nFanouts, int iModel )
{
    int i, iFanin, nFanins = Vec_IntSize(vFanins);
    int Id = Au_NtkAllocObj( pNtk, nFanins + 1 + nFanouts, AU_OBJ_BOX );
    Au_Obj_t * p = Au_NtkObj( pNtk, Id );
    Vec_IntForEachEntry( vFanins, iFanin, i )
        Au_ObjSetFanin( p, i, iFanin );
    Au_ObjSetFaninLit( p, nFanins, nFanouts );
    for ( i = 0; i < nFanouts; i++ )
        Au_ObjSetFaninLit( p, nFanins + 1 + i, Au_NtkCreateFan(pNtk, Id, i, iModel) );
    p->nFanins = nFanins;
    p->Func = iModel;
    assert( iModel > 0 );
    return Id;
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
    int i, k;
    Au_NtkForEachPi( p, pTerm, i )
        assert( Au_ObjCopy(pTerm) >= 0 );
    Au_NtkForEachObj( p, pObj, i )
    {
        if ( Au_ObjIsNode(pObj) )
        {
            int Lit, gFanins[16];
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
            Au_ObjSetCopy( pObj, Lit );
        }
        else if ( Au_ObjIsBox(pObj) )
        {
            Au_Ntk_t * pModel = Au_ObjModel(pObj);
            Vec_IntFill( &pModel->vCopies, Au_NtkObjNumMax(pModel), -1 );
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
    }
    Au_NtkForEachPo( p, pTerm, i )
        Au_ObjSetCopy( pTerm, Au_ObjCopy(Au_ObjFanin0(pTerm)) );
    Au_NtkForEachPo( p, pTerm, i )
        assert( Au_ObjCopy(pTerm) >= 0 );

    p->pMan->nGiaObjMax = Abc_MaxInt( p->pMan->nGiaObjMax, Gia_ManObjNum(pGia) );
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
    Vec_IntFill( &p->vCopies, Au_NtkObjNumMax(p), -1 );
    // start the network
    pGia = Gia_ManStart( (1<<16) );
    pGia->pName = Gia_UtilStrsav( Au_NtkName(p) );
    Gia_ManHashAlloc( pGia );
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
                Vec_IntPush( vFanins, pTerm->iTemp );
            iFunc = Abc_NamStrFindOrAdd( pMan->pFuncs, (char *)pObj->pData, NULL );
            Abc_ObjFanout0(pObj)->iTemp = Au_NtkCreateNode(p, vFanins, iFunc);
            continue;
        }
        assert( Abc_ObjIsBox(pObj) );
        Abc_ObjForEachFanin( pObj, pTerm, k )
            Vec_IntPush( vFanins, Abc_ObjFanin0(pTerm)->iTemp );
        pObj->iTemp = Au_NtkCreateBox(p, vFanins, Abc_ObjFanoutNum(pObj), ((Abc_Ntk_t *)pObj->pData)->iStep );
        pAuObj = Au_NtkObj(p, pObj->iTemp);
        Abc_ObjForEachFanout( pObj, pTerm, k )
            Abc_ObjFanout0(pTerm)->iTemp = Au_ObjFanout(pAuObj, k);
    }
//    Vec_PtrFree( vOrder );
    Vec_IntFree( vFanins );
    // copy POs
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Au_NtkCreatePo( p, Abc_ObjFanin0(pTerm)->iTemp );

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
    int i, clk1, clk2 = 0, clk3 = 0, clk = clock();

    clk1 = clock();
    pMan = Au_ManAlloc( pRoot->pDesign->pName );
    clk2 += clock() - clk1;

    vModels = Abc_NtkCollectHie( pRoot );
//    Vec_PtrForEachEntry( Abc_Ntk_t *, pLib->vModules, pMod, i )
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

    if ( !Abc_NtkCheckRecursive(pRoot) )
    {
        clk1 = clock();
        pGia = Au_NtkDeriveFlatGia( (Au_Ntk_t *)pRoot->pData );
        clk3 = clock() - clk1;
        printf( "GIA objects max = %d.\n", pMan->nGiaObjMax );
    }

    clk1 = clock();
    Au_ManDelete( pMan );
    clk2 += clock() - clk1;
    
    Abc_PrintTime( 1, "Time all", clock() - clk );
    Abc_PrintTime( 1, "Time new", clk2 );
    Abc_PrintTime( 1, "Time GIA", clk3 );

    return pGia;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

