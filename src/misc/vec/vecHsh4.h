/**CFile****************************************************************

  FileName    [vecHsh4.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resizable arrays.]

  Synopsis    [Hashing pairs of integers into an integer.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: vecHsh4.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__misc__vec__vecHsh4_h
#define ABC__misc__vec__vecHsh4_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>

ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Hsh_Int4Obj_t_ Hsh_Int4Obj_t;
struct Hsh_Int4Obj_t_
{
    int          iData0;
    int          iData1;
    int          iRes;
    int          iNext;
};

typedef struct Hsh_Int4Man_t_ Hsh_Int4Man_t;
struct Hsh_Int4Man_t_
{
    Vec_Int_t *  vTable;      // hash table
    Vec_Int_t *  vObjs;       // hash objects
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline Hsh_Int4Obj_t * Hsh_Int4Obj( Hsh_Int4Man_t * p, int iObj )    { return iObj ? (Hsh_Int4Obj_t *)Vec_IntEntryP(p->vObjs, 4*iObj) : NULL;  }
static inline int             Hsh_Int4ObjRes( Hsh_Int4Man_t * p, int i )    { return Hsh_Int4Obj(p, i)->iRes;                                         }
static inline void            Hsh_Int4ObjInc( Hsh_Int4Man_t * p, int i )    { Hsh_Int4Obj(p, i)->iRes++;                                              }
static inline void            Hsh_Int4ObjDec( Hsh_Int4Man_t * p, int i )    { Hsh_Int4Obj(p, i)->iRes--;                                              }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Hashing data entries composed of nSize integers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Hsh_Int4Man_t * Hsh_Int4ManStart( int nSize )
{
    Hsh_Int4Man_t * p;  nSize += 100;
    p = ABC_CALLOC( Hsh_Int4Man_t, 1 );
    p->vTable = Vec_IntStart( Abc_PrimeCudd(nSize) );
    p->vObjs  = Vec_IntAlloc( 4*nSize );
    Vec_IntFill( p->vObjs, 4, 0 );
    return p;
}
static inline void Hsh_Int4ManStop( Hsh_Int4Man_t * p )
{
    Vec_IntFree( p->vObjs );
    Vec_IntFree( p->vTable );
    ABC_FREE( p );
}
static inline int Hsh_Int4ManEntryNum( Hsh_Int4Man_t * p )
{
    return Vec_IntSize(p->vObjs)/4 - 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Hsh_Int4ManHash( int iData0, int iData1, int nTableSize )
{
    return (4177 * iData0 + 7873 * iData1) % nTableSize;
}
static inline int * Hsh_Int4ManLookup( Hsh_Int4Man_t * p, int iData0, int iData1 )
{
    Hsh_Int4Obj_t * pObj;
    int * pPlace = Vec_IntEntryP( p->vTable, Hsh_Int4ManHash(iData0, iData1, Vec_IntSize(p->vTable)) );
    for ( ; (pObj = Hsh_Int4Obj(p, *pPlace)); pPlace = &pObj->iNext )
        if ( pObj->iData0 == iData0 && pObj->iData1 == iData1 )
            return pPlace;
    assert( *pPlace == 0 );
    return pPlace;
}
static inline int Hsh_Int4ManFind( Hsh_Int4Man_t * p, int iData0, int iData1 )
{
    Hsh_Int4Obj_t * pObj;
    int * pPlace = Vec_IntEntryP( p->vTable, Hsh_Int4ManHash(iData0, iData1, Vec_IntSize(p->vTable)) );
    for ( ; (pObj = Hsh_Int4Obj(p, *pPlace)); pPlace = &pObj->iNext )
        if ( pObj->iData0 == iData0 && pObj->iData1 == iData1 )
            return pObj->iRes;
    assert( *pPlace == 0 );
    return -1;
}
static inline int Hsh_Int4ManInsert( Hsh_Int4Man_t * p, int iData0, int iData1, int iRes )
{
    Hsh_Int4Obj_t * pObj;
    int i, nObjs, * pPlace;
    nObjs = Vec_IntSize(p->vObjs)/4;
    if ( nObjs > Vec_IntSize(p->vTable) )
    {
        Vec_IntFill( p->vTable, Abc_PrimeCudd(2*Vec_IntSize(p->vTable)), 0 );
        for ( i = 1; i < nObjs; i++ )
        {
            pObj = Hsh_Int4Obj( p, i );
            pObj->iNext = 0;
            pPlace = Hsh_Int4ManLookup( p, pObj->iData0, pObj->iData1 );
            assert( *pPlace == 0 );
            *pPlace = i;
        }
    }
    pPlace = Hsh_Int4ManLookup( p, iData0, iData1 );
    if ( *pPlace )
        return 0;
    assert( *pPlace == 0 );
    *pPlace = nObjs;
    Vec_IntPush( p->vObjs, iData0 );
    Vec_IntPush( p->vObjs, iData1 );
    Vec_IntPush( p->vObjs, iRes );
    Vec_IntPush( p->vObjs, 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Test procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Hsh_Int4ManHashArrayTest()
{
    Hsh_Int4Man_t * p;
    int RetValue;

    p = Hsh_Int4ManStart( 10 );

    RetValue = Hsh_Int4ManInsert( p, 10, 11, 12 );
    assert( RetValue );

    RetValue = Hsh_Int4ManInsert( p, 20, 21, 22 );
    assert( RetValue );

    RetValue = Hsh_Int4ManInsert( p, 10, 11, 12 );
    assert( !RetValue );

    RetValue = Hsh_Int4ManFind( p, 20, 21 );
    assert( RetValue == 22 );

    RetValue = Hsh_Int4ManFind( p, 20, 22 );
    assert( RetValue == -1 );
 
    Hsh_Int4ManStop( p );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_END

#endif

