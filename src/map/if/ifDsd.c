/**CFile****************************************************************

  FileName    [ifDsd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Sequential mapping.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifDsd.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "misc/vec/vecHsh.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ifd_Obj_t_ Ifd_Obj_t;
struct Ifd_Obj_t_
{
    unsigned          nFreq : 24;   // frequency
    unsigned          nSupp :  5;   // support size
    unsigned          Type  :  2;   // type
    unsigned          fWay  :  1;   // transparent edge
    unsigned          pFans[3];     // fanins
};

typedef struct Ifd_Man_t_ Ifd_Man_t;
struct Ifd_Man_t_
{
    Ifd_Obj_t *       pObjs;
    int               nObjs;
    int               nObjsAlloc;
    // hashing operations
    Vec_Int_t *       vArgs;     // iDsd1 op iDsdC
    Vec_Int_t *       vRes;      // result of operation
    Vec_Int_t *       vOffs;     // offsets in the array of permutations
    Vec_Str_t *       vPerms;    // storage for permutations
    Hsh_IntMan_t *    vHash;     // hash table 
    // other data
    Vec_Int_t *       vSuper;

};

static inline int         Ifd_ObjIsVar( Ifd_Obj_t * p ) { return p->Type == 0; }
static inline int         Ifd_ObjIsAnd( Ifd_Obj_t * p ) { return p->Type == 1; }
static inline int         Ifd_ObjIsXor( Ifd_Obj_t * p ) { return p->Type == 2; }
static inline int         Ifd_ObjIsMux( Ifd_Obj_t * p ) { return p->Type == 3; }

static inline Ifd_Obj_t * Ifd_ManObj( Ifd_Man_t * p, int i )           { assert( i >= 0 && i < p->nObjs );                              return p->pObjs + i;    }
static inline Ifd_Obj_t * Ifd_ManObjFromLit( Ifd_Man_t * p, int iLit ) { return Ifd_ManObj( p, Abc_Lit2Var(iLit) );                                             }
static inline int         Ifd_ObjId( Ifd_Man_t * p, Ifd_Obj_t * pObj ) { assert( pObj - p->pObjs >= 0 && pObj - p->pObjs < p->nObjs );  return pObj - p->pObjs; }
static inline int         Ifd_LitSuppSize( Ifd_Man_t * p, int iLit )   { return iLit ? Ifd_ManObjFromLit(p, iLit)->nSupp : 0;                                   }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ifd_Man_t * Ifd_ManStart()
{
    Ifd_Man_t * p;
    p = ABC_CALLOC( Ifd_Man_t, 1 );
    p->nObjsAlloc = Abc_PrimeCudd( 1000000 );
    p->nObjs      = 2;
    p->pObjs      = ABC_CALLOC( Ifd_Obj_t, p->nObjsAlloc );
    memset( p->pObjs, 0xFF, sizeof(Ifd_Obj_t) ); // const node
    (p->pObjs + 1)->nSupp = 1;  // variable
    (p->pObjs + 1)->fWay  = 1;  // variable
    // hashing operations
    p->vArgs      = Vec_IntAlloc( 4000 );
    p->vRes       = Vec_IntAlloc( 1000 );
//    p->vOffs      = Vec_IntAlloc( 1000 );
//    p->vPerms     = Vec_StrAlloc( 1000 );
    p->vHash      = Hsh_IntManStart( p->vArgs, 4, 1000 );
    // other data
    p->vSuper     = Vec_IntAlloc( 1000 );
    return p;
}
void Ifd_ManStop( Ifd_Man_t * p )
{
    Vec_IntFree( p->vArgs );
    Vec_IntFree( p->vRes );
//    Vec_IntFree( p->vOffs );
//    Vec_StrFree( p->vPerms );
    Hsh_IntManStop( p->vHash );
    Vec_IntFree( p->vSuper );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Printing structures.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ifd_ObjPrint_rec( Ifd_Man_t * p, int iLit, int * pCounter, int DiffType )
{
    char Symb[2][4] = { {'?','(','[','<'}, {'?',')',']','>'} };
    Ifd_Obj_t * pDsd;
    if ( Abc_LitIsCompl(iLit) )
        printf( "!" ), iLit = Abc_LitNot(iLit);
    if ( iLit == 2 )
        { printf( "%c", 'a' + (*pCounter)++ ); return; }
    pDsd = Ifd_ManObjFromLit( p, iLit );
    if ( DiffType )
        printf( "%c", Symb[0][pDsd->Type] );
    Ifd_ObjPrint_rec( p, pDsd->pFans[0], pCounter, pDsd->Type == 3 || pDsd->Type != Ifd_ManObjFromLit(p, pDsd->pFans[0])->Type );
    Ifd_ObjPrint_rec( p, pDsd->pFans[1], pCounter, pDsd->Type == 3 || pDsd->Type != Ifd_ManObjFromLit(p, pDsd->pFans[1])->Type );
    if ( pDsd->pFans[2] )
    Ifd_ObjPrint_rec( p, pDsd->pFans[2], pCounter, pDsd->Type == 3 || pDsd->Type != Ifd_ManObjFromLit(p, pDsd->pFans[2])->Type );
    if ( DiffType )
        printf( "%c", Symb[1][pDsd->Type] );
}
void Ifd_ObjPrint( Ifd_Man_t * p, int iLit )
{
    int Counter = 0;
    if ( iLit == 0 )
        { printf( "0" ); return; }
    if ( iLit == 1 )
        { printf( "1" ); return; }
    Ifd_ObjPrint_rec( p, iLit, &Counter, 1 );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Canonicizing DSD structures.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ifd_ManHashLookup( Ifd_Man_t * p, int iDsd0, int iDsd1, int iDsdC, int Type )
{
    int pData[4];
    assert( iDsdC == 0 || iDsd0 >= iDsd1 );
    assert( iDsdC == 0 || !Abc_LitIsCompl(iDsd1) );
    pData[0] = (iDsd0 >= iDsd1) ? iDsd0 : iDsd1;
    pData[1] = (iDsd0 >= iDsd1) ? iDsd1 : iDsd0;
    pData[2] = iDsdC;
    pData[3] = Type;
    return *Hsh_IntManLookup( p->vHash, pData );
}
void Ifd_ManHashInsert( Ifd_Man_t * p, int iDsd0, int iDsd1, int iDsdC, int Type, int Res )
{
    int iObj;
    assert( iDsdC == 0 || iDsd0 >= iDsd1 );
    assert( iDsdC == 0 || !Abc_LitIsCompl(iDsd1) );
    Vec_IntPush( p->vArgs, (iDsd0 >= iDsd1) ? iDsd0 : iDsd1 );
    Vec_IntPush( p->vArgs, (iDsd0 >= iDsd1) ? iDsd1 : iDsd0 );
    Vec_IntPush( p->vArgs, iDsdC );
    Vec_IntPush( p->vArgs, Type );
    iObj = Hsh_IntManAdd( p->vHash, Vec_IntSize(p->vRes) );
    assert( iObj == Vec_IntSize(p->vRes) );
    Vec_IntPush( p->vRes, Res );
    assert( 4 * Vec_IntSize(p->vRes) == Vec_IntSize(p->vArgs) );
}
int Ifd_ManHashFindOrAdd( Ifd_Man_t * p, int iDsd0, int iDsd1, int iDsdC, int Type )
{
    Ifd_Obj_t * pObj;
    int iObj, Value;
    Vec_IntPush( p->vArgs, (iDsd0 >= iDsd1) ? iDsd0 : iDsd1 );
    Vec_IntPush( p->vArgs, (iDsd0 >= iDsd1) ? iDsd1 : iDsd0 );
    Vec_IntPush( p->vArgs, iDsdC );
    Vec_IntPush( p->vArgs, Type );
    Value = Hsh_IntManAdd( p->vHash, Vec_IntSize(p->vRes) );
    if ( Value < Vec_IntSize(p->vRes) )
    {
        iObj = Vec_IntEntry(p->vRes, Value);
        Vec_IntShrink( p->vArgs, Vec_IntSize(p->vArgs) - 4 );
        pObj = Ifd_ManObj( p, iObj );
        pObj->nFreq++;
        assert( (int)pObj->Type == Type );
        assert( (int)pObj->nSupp == Ifd_LitSuppSize(p, iDsd0) + Ifd_LitSuppSize(p, iDsd1) + Ifd_LitSuppSize(p, iDsdC) );
    }
    else
    {
        assert( p->nObjs < p->nObjsAlloc );
        iObj = p->nObjs;
        pObj = Ifd_ManObj( p, p->nObjs++ );
        pObj->nFreq = 1;
        pObj->nSupp = Ifd_LitSuppSize(p, iDsd0) + Ifd_LitSuppSize(p, iDsd1) + Ifd_LitSuppSize(p, iDsdC); 
        pObj->Type  = Type;
        if ( Type == 1 )
            pObj->fWay = 0;
        else if ( Type == 2 )
            pObj->fWay = Ifd_ManObjFromLit(p, iDsd0)->fWay | Ifd_ManObjFromLit(p, iDsd1)->fWay;
        else if ( Type == 3 )
            pObj->fWay = Ifd_ManObjFromLit(p, iDsd0)->fWay & Ifd_ManObjFromLit(p, iDsd1)->fWay;
        else assert( 0 );
        pObj->pFans[0] = (iDsd0 >= iDsd1) ? iDsd0 : iDsd1;
        pObj->pFans[1] = (iDsd0 >= iDsd1) ? iDsd1 : iDsd0;
        pObj->pFans[2] = iDsdC;
        Vec_IntPush( p->vRes, iObj );
    }
    assert( 4 * Vec_IntSize(p->vRes) == Vec_IntSize(p->vArgs) );
    return iObj;
}
void Ifd_ManOperSuper_rec( Ifd_Man_t * p, int iLit, int Type, Vec_Int_t * vObjs )
{
    Ifd_Obj_t * pDsd = Ifd_ManObjFromLit( p, iLit );
    if ( Abc_LitIsCompl(iLit) || (int)pDsd->Type != Type )
        Vec_IntPush( vObjs, iLit );
    else
    {
        Ifd_ManOperSuper_rec( p, pDsd->pFans[0], Type, vObjs );
        Ifd_ManOperSuper_rec( p, pDsd->pFans[1], Type, vObjs );
    }
}
int Ifd_ManOper( Ifd_Man_t * p, int iDsd0, int iDsd1, int iDsdC, int Type )
{
    int i, iLit0, iLit1, iThis, fCompl = 0;
    if ( Type == 1 ) // AND
    {
        if ( iDsd0 == 0 || iDsd1 == 0 )
            return 0;
        if ( iDsd0 == 1 || iDsd1 == 1 )
            return (iDsd0 == 1) ? iDsd1 : iDsd0;
    }
    else if ( Type == 2 ) // XOR
    {
        if ( iDsd0 < 2 )
            return Abc_LitNotCond( iDsd1, iDsd0 );
        if ( iDsd1 < 2 )
            return Abc_LitNotCond( iDsd0, iDsd1 );
        if ( Abc_LitIsCompl(iDsd0) )
            fCompl ^= 1, iDsd0 = Abc_LitNot(iDsd0);
        if ( Abc_LitIsCompl(iDsd1) )
            fCompl ^= 1, iDsd1 = Abc_LitNot(iDsd1);
    }
    else if ( Type == 3 )
    {
        iDsd0 = (iDsd0 >= iDsd1) ? iDsd0 : iDsd1; // data0
        iDsd1 = (iDsd0 >= iDsd1) ? iDsd1 : iDsd0; // data1
        iDsdC = (iDsd0 >= iDsd1) ? iDsdC : Abc_LitNot(iDsdC); // ctrl
        if ( Abc_LitIsCompl(iDsd1) )
            fCompl ^= 1, iDsd0 = Abc_LitNot(iDsd0), iDsd1 = Abc_LitNot(iDsd1);
    }
    assert( iDsd0 > 1 && iDsd1 > 1 && Type >= 1 && Type <= 3 );
    // check cache
    iThis = Ifd_ManHashLookup( p, iDsd0, iDsd1, iDsdC, Type );
    if ( iThis != -1 )
        return Abc_Var2Lit( iThis, fCompl );
    // create new entry
    if ( Type == 3 )
    {
        iThis = Ifd_ManHashFindOrAdd( p, iDsd0, iDsd1, iDsdC, Type );
        return Abc_Var2Lit( iThis, fCompl );
    }
    assert( iDsdC == 0 );
    Vec_IntClear( p->vSuper );
    Ifd_ManOperSuper_rec( p, iDsd0, Type, p->vSuper );
    Ifd_ManOperSuper_rec( p, iDsd1, Type, p->vSuper );
    Vec_IntSort( p->vSuper, 1 );
    iLit0 = Vec_IntEntry( p->vSuper, 0 );
    Vec_IntForEachEntryStart( p->vSuper, iLit1, i, 1 )
        iLit0 = Abc_Var2Lit( Ifd_ManHashFindOrAdd(p, iLit0, iLit1, 0, Type), 0 );
    assert( !Abc_LitIsCompl(iLit0) );
    // insert into cache
//    if ( Vec_IntSize(p->vSuper) > 2 )
//        Ifd_ManHashInsert( p, iDsd0, iDsd1, iDsdC, Type, iLit0 );
    return Abc_LitNotCond( iLit0, fCompl );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ifd_ManFindDsd_rec( Ifd_Man_t * pMan, char * pStr, char ** p, int * pMatches )
{
    int fCompl = 0;
    if ( **p == '!' )
        (*p)++, fCompl = 1;
    if ( **p >= 'a' && **p <= 'f' ) // var
    {
        assert( **p - 'a' >= 0 && **p - 'a' < 6 );
        return Abc_Var2Lit( 1, fCompl );
    }
    if ( **p == '(' ) // and/or
    {
        char * q = pStr + pMatches[ *p - pStr ];
        int Lit, Res = 1;
        assert( **p == '(' && *q == ')' );
        for ( (*p)++; *p < q; (*p)++ )
        {
            Lit = Ifd_ManFindDsd_rec( pMan, pStr, p, pMatches );
            Res = Ifd_ManOper( pMan, Res, Lit, 0, 1 );
        }
        assert( *p == q );
        return Abc_LitNotCond( Res, fCompl );
    }
    if ( **p == '[' ) // xor
    {
        char * q = pStr + pMatches[ *p - pStr ];
        int Lit, Res = 0;
        assert( **p == '[' && *q == ']' );
        for ( (*p)++; *p < q; (*p)++ )
        {
            Lit = Ifd_ManFindDsd_rec( pMan, pStr, p, pMatches );
            Res = Ifd_ManOper( pMan, Res, Lit, 0, 2 );
        }
        assert( *p == q );
        return Abc_LitNotCond( Res, fCompl );
    }
    if ( **p == '<' ) // mux
    {
        int Temp[3], * pTemp = Temp, Res;
        char * pOld = *p;
        char * q = pStr + pMatches[ *p - pStr ];
        assert( **p == '<' && *q == '>' );
        // derive MAX components
        for ( (*p)++; *p < q; (*p)++ )
            *pTemp++ = Ifd_ManFindDsd_rec( pMan, pStr, p, pMatches );
        assert( pTemp == Temp + 3 );
        assert( *p == q );
//        Res = (Temp[0] & Temp[1]) | (~Temp[0] & Temp[2]);
        Res = Ifd_ManOper( pMan, Temp[2], Temp[1], Temp[0], 3 );
        return Abc_LitNotCond( Res, fCompl );
    }
    assert( 0 );
    return 0;
}
#define IFM_MAX_STR  100
#define IFM_MAX_VAR   16
int * Ifd_ManComputeMatches( char * p )
{
    static int pMatches[IFM_MAX_STR];
    int pNested[IFM_MAX_VAR];
    int v, nNested = 0;
    for ( v = 0; p[v]; v++ )
    {
        pMatches[v] = 0;
        if ( p[v] == '(' || p[v] == '[' || p[v] == '<' || p[v] == '{' )
            pNested[nNested++] = v;
        else if ( p[v] == ')' || p[v] == ']' || p[v] == '>' || p[v] == '}' )
            pMatches[pNested[--nNested]] = v;
        assert( nNested < IFM_MAX_VAR );
    }
    assert( nNested == 0 );
    return pMatches;
}
int Ifd_ManFindDsd( Ifd_Man_t * pMan, char * p )
{
    int Res;
    if ( *p == '0' && *(p+1) == 0 )
        Res = 0;
    else if ( *p == '1' && *(p+1) == 0 )
        Res = 1;
    else
        Res = Ifd_ManFindDsd_rec( pMan, p, &p, Ifd_ManComputeMatches(p) );
    assert( *++p == 0 );
    return Res;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ifd_ManDsdTest()
{
    char * p = "(abc)";
    char * q = "(a[bc])";
    char * r = "[<abc>(def)]";
    Ifd_Man_t * pMan = Ifd_ManStart();
    int iLit = Ifd_ManFindDsd( pMan, p );
    Ifd_ObjPrint( pMan, iLit );
    Ifd_ManStop( pMan );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

