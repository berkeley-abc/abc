/**CFile****************************************************************

  FileName    [sscUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT sweeping under constraints.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: sscUtil.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sscInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Hsh_Obj_t_ Hsh_Obj_t;
struct Hsh_Obj_t_
{
    int              iThis;
    int              iNext;
};

typedef struct Hsh_Man_t_ Hsh_Man_t;
struct Hsh_Man_t_
{
    unsigned *       pData;   // user's data
    int *            pTable;  // hash table
    Hsh_Obj_t *      pObjs;
    int              nObjs;
    int              nSize;
    int              nTableSize;
};

static inline unsigned *   Hsh_ObjData( Hsh_Man_t * p, int iThis )      { return p->pData + p->nSize * iThis;         }
static inline Hsh_Obj_t *  Hsh_ObjGet( Hsh_Man_t * p, int iObj )        { return iObj == -1 ? NULL : p->pObjs + iObj;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hsh_Man_t * Hsh_ManStart( unsigned * pData, int nDatas, int nSize )
{
    Hsh_Man_t * p;
    p = ABC_CALLOC( Hsh_Man_t, 1 );
    p->pData = pData;
    p->nSize = nSize;
    p->nTableSize = Abc_PrimeCudd( nDatas );
    p->pTable = ABC_FALLOC( int, p->nTableSize );
    p->pObjs  = ABC_FALLOC( Hsh_Obj_t, p->nTableSize );
    return p;
}
void Hsh_ManStop( Hsh_Man_t * p )
{
    ABC_FREE( p->pObjs );
    ABC_FREE( p->pTable );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Hsh_ManHash( unsigned * pData, int nSize, int nTableSize )
{
    static unsigned s_BigPrimes[7] = {12582917, 25165843, 50331653, 100663319, 201326611, 402653189, 805306457};
    unsigned char * pDataC = (unsigned char *)pData;
    int c, nChars = nSize * 4, Key = 0;
    for ( c = 0; c < nChars; c++ )
        Key += pDataC[c] * s_BigPrimes[c % 7];
    return Key % nTableSize;
}
int Hsh_ManAdd( Hsh_Man_t * p, int iThis )
{
    Hsh_Obj_t * pObj;
    unsigned * pThis = Hsh_ObjData( p, iThis );
    int * pPlace = p->pTable + Hsh_ManHash( pThis, p->nSize, p->nTableSize );
    for ( pObj = Hsh_ObjGet(p, *pPlace); pObj; pObj = Hsh_ObjGet(p, pObj->iNext) )
        if ( !memcmp( pThis, Hsh_ObjData(p, pObj->iThis), sizeof(unsigned) * p->nSize ) )
            return pObj - p->pObjs;
    assert( p->nObjs < p->nTableSize );
    pObj = p->pObjs + p->nObjs;
    pObj->iThis = iThis;
    return (*pPlace = p->nObjs++);
}

/**Function*************************************************************

  Synopsis    [Hashes data by value.]

  Description [Array of 'nTotal' int entries, each of size 'nSize' ints,
  is hashed and the resulting unique numbers is returned in the array.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Hsh_ManHashData( int * pData, int nDatas, int nSize, int nInts )
{
    Vec_Int_t * vRes;
    Hsh_Man_t * p;
    int i;
    assert( nDatas * nSize == nInts );
    p = Hsh_ManStart( pData, nDatas, nSize );
    vRes = Vec_IntAlloc( 1000 );
    for ( i = 0; i < nDatas; i++ )
        Vec_IntPush( vRes, Hsh_ManAdd(p, i) );
    Hsh_ManStop( p );
    return vRes;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

