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
static inline Au_Obj_t *   Au_NtkObj( Au_Ntk_t * p, int i )              { return (Au_Obj_t *)p->vPages.pArray[i >> 12] + (i & 0xFFF);            }

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

static inline int          Au_ObjFanin( Au_Obj_t * p, int i )            { assert(i >= 0 && i < (int)p->nFanins && p->Fanins[i]); return Au_Lit2Var(p->Fanins[i]);     }
static inline int          Au_ObjFaninC( Au_Obj_t * p, int i )           { assert(i >= 0 && i < (int)p->nFanins && p->Fanins[i]); return Au_LitIsCompl(p->Fanins[i]);  }
static inline int          Au_ObjFaninLit( Au_Obj_t * p, int i )         { assert(i >= 0 && i < (int)p->nFanins && p->Fanins[i]); return p->Fanins[i];                 }
static inline void         Au_ObjSetFanin( Au_Obj_t * p, int i, int f )  { assert(f > 0 && p->Fanins[i] == 0); p->Fanins[i] = Au_Var2Lit(f,0);                         }
static inline void         Au_ObjSetFaninLit( Au_Obj_t * p, int i, int f){ assert(f >= 0 && p->Fanins[i] == 0); p->Fanins[i] = f;                                      }

static inline int          Au_ObjFanout( Au_Obj_t * p, int i )           { assert(p->Type == AU_OBJ_BOX && i >= 0 && i < p->Fanins[p->nFanins] && p->Fanins[i]); return p->Fanins[p->nFanins + 1 + i];             }
static inline int          Au_ObjSetFanout( Au_Obj_t * p, int i, int f ) { assert(p->Type == AU_OBJ_BOX && i >= 0 && i < p->Fanins[p->nFanins] && p->Fanins[i] == 0 && f > 0); p->Fanins[p->nFanins + 1 + i] = f;  }

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
    Vec_PtrGrow( &p->vPages, 11 );
    Au_ManAddNtk( pMan, p );
    return p;
}
void Au_NtkFree( Au_Ntk_t * p )
{
    Au_ManFree( p->pMan );
    Vec_PtrFreeFree( p->vChunks );
    ABC_FREE( p->vPages.pArray );
    ABC_FREE( p->vPis.pArray );
    ABC_FREE( p->vPos.pArray );
    ABC_FREE( p->pHTable );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
int Au_NtkMemUsage( Au_Ntk_t * p )
{
    int Mem = sizeof(Au_Ntk_t);
    Mem += 4 * Vec_IntSize(&p->vPis);
    Mem += 4 * Vec_IntSize(&p->vPos);
    Mem += 16 * Vec_PtrSize(p->vChunks) * ((1<<12) + 64);
    return Mem;
}
void Au_NtkPrintStats( Au_Ntk_t * p )
{
    printf( "%-13s:",         Au_NtkName(p) );
    printf( " i/o =%5d/%5d",  Au_NtkPiNum(p), Au_NtkPoNum(p) );
//    printf( "  lat =%5d",     Au_NtkFlopNum(p) );
    printf( "  nd =%6d",      Au_NtkNodeNum(p) );
    printf( "  box =%5d",     Au_NtkBoxNum(p) );
    printf( "  obj =%6d",     Au_NtkObjNum(p) );
    printf( "  max =%6d",     Au_NtkObjNumMax(p) );
    printf( "  use =%6d",     p->nUseful );
    printf( " (%.2f %%)",      100.0 * (Au_NtkObjNumMax(p) - p->nUseful) / Au_NtkObjNumMax(p) );
    printf( "    %.2f Mb",    1.0 * Au_NtkMemUsage(p) / (1 << 20) );
    printf( "\n" );
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
    Vec_PtrForEachEntryStart( Au_Ntk_t *, &p->vNtks, pNtk, i, 1 )
        Au_NtkFree( pNtk );
}
int Au_ManFindNtk( Au_Man_t * p, char * pName )
{
    Au_Ntk_t * pNtk;
    int i;
    Vec_PtrForEachEntryStart( Au_Ntk_t *, &p->vNtks, pNtk, i, 1 )
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
    Vec_PtrForEachEntryStart( Au_Ntk_t *, &p->vNtks, pNtk, i, 1 )
        Mem += Au_NtkMemUsage( pNtk );
    return Mem;
}
void Au_ManPrintStats( Au_Man_t * p )
{
    Au_Ntk_t * pNtk;
    int i;
    printf( "Design %-13s\n", Au_ManName(p) );
    Vec_PtrForEachEntryStart( Au_Ntk_t *, &p->vNtks, pNtk, i, 1 )
        Au_NtkPrintStats( pNtk );
    printf( "Different functions = %d. ", Abc_NamObjNumMax(p->pFuncs) );
    printf( "Memory = %.2f Mb",  1.0 * Au_ManMemUsage(p) / (1 << 20) );
    printf( "\n" );
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
        p->nUseful += nObjInt - nObjInt2;
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

extern Vec_Ptr_t * Abc_NtkDfsBoxes( Abc_Ntk_t * pNtk );

/**Function*************************************************************

  Synopsis    [Duplicates ABC network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Au_Ntk_t * Au_NtkDerive( Au_Man_t * pMan, Abc_Ntk_t * pNtk )
{
    Au_Ntk_t * p;
    Au_Obj_t * pAuObj;
    Abc_Obj_t * pObj, * pTerm;
    Abc_Ntk_t * pNtkModel;
    Vec_Ptr_t * vOrder;
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
    vOrder = Abc_NtkDfsBoxes( pNtk );
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
        pNtkModel = (Abc_Ntk_t *)pObj->pData;
        pObj->iTemp = Au_NtkCreateBox(p, vFanins, Abc_ObjFanoutNum(pObj), pNtkModel->iStep );
        pAuObj = Au_NtkObj(p, pObj->iTemp);
        Abc_ObjForEachFanout( pObj, pTerm, k )
            Abc_ObjFanout0(pTerm)->iTemp = Au_ObjFanout(pAuObj, k);
    }
    Vec_PtrFree( vOrder );
    Vec_IntFree( vFanins );
    // copy POs
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Au_NtkCreatePo( p, Abc_ObjFanin0(pTerm)->iTemp );
    return p;
}

void Au_ManDeriveTest( Abc_Ntk_t * pRoot )
{
    extern Vec_Ptr_t * Abc_NtkCollectHie( Abc_Ntk_t * pNtk );

    Vec_Ptr_t * vOrder;
    Abc_Ntk_t * pMod;
    Au_Man_t * pMan;
    Au_Ntk_t * pNtk;
    int i, clk = clock();

    pMan = Au_ManAlloc( pRoot->pDesign->pName );

    vOrder = Abc_NtkCollectHie( pRoot );
//    Vec_PtrForEachEntry( Abc_Ntk_t *, pLib->vModules, pMod, i )
    Vec_PtrForEachEntry( Abc_Ntk_t *, vOrder, pMod, i )
    {
        pNtk = Au_NtkDerive( pMan, pMod );
        pMod->iStep = pNtk->Id;
    }
    Vec_PtrFree( vOrder );

    Au_ManPrintStats( pMan );
    Au_ManDelete( pMan );
    
    Abc_PrintTime( 1, "Time", clock() - clk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

