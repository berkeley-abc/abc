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
#include "misc/extra/extra.h"

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
    Vec_Int_t *       vMarks;    // marks where given N begins
    Vec_Wrd_t *       vTruths;   // truth tables
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
static inline int         Ifd_LitSuppSize( Ifd_Man_t * p, int iLit )   { return iLit > 0 ? Ifd_ManObjFromLit(p, iLit)->nSupp : 0;                               }

#define Ifd_ManForEachNodeWithSupp( p, nVars, pLeaf, i )                       \
    for ( i = Vec_IntEntry(p->vMarks, nVars); (i < Vec_IntEntry(p->vMarks, nVars+1)) && (pLeaf = Ifd_ManObj(p, i)); i++ )


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
    p->nObjsAlloc = Abc_PrimeCudd( 50000000 );
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
    p->vMarks     = Vec_IntAlloc( 100 );
    Vec_IntPush( p->vMarks, 0 );
    Vec_IntPush( p->vMarks, 1 );
    Vec_IntPush( p->vMarks, p->nObjs );
    // other data
    p->vSuper     = Vec_IntAlloc( 1000 );
    p->vTruths    = Vec_WrdAlloc( 1000 );
    return p;
}
void Ifd_ManStop( Ifd_Man_t * p )
{
    int i, This, Prev = 0;
    Vec_IntForEachEntryStart( p->vMarks, This, i, 1 )
    {
        printf( "%d(%d:%d) ", i-1, This, This - Prev );
        Prev = This;
    }
    printf( "\n" );

    Vec_IntFreeP( &p->vArgs );
    Vec_IntFreeP( &p->vRes );
//    Vec_IntFree( p->vOffs );
//    Vec_StrFree( p->vPerms );
    Vec_WrdFreeP( &p->vTruths );
    Vec_IntFreeP( &p->vMarks );
    Hsh_IntManStop( p->vHash );
    Vec_IntFreeP( &p->vSuper );
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
    Ifd_ObjPrint_rec( p, pDsd->pFans[0], pCounter, pDsd->Type == 3 || Abc_LitIsCompl(pDsd->pFans[0]) || pDsd->Type != Ifd_ManObjFromLit(p, pDsd->pFans[0])->Type );
    Ifd_ObjPrint_rec( p, pDsd->pFans[1], pCounter, pDsd->Type == 3 || Abc_LitIsCompl(pDsd->pFans[1]) || pDsd->Type != Ifd_ManObjFromLit(p, pDsd->pFans[1])->Type );
    if ( pDsd->pFans[2] != -1 )
    Ifd_ObjPrint_rec( p, pDsd->pFans[2], pCounter, pDsd->Type == 3 || Abc_LitIsCompl(pDsd->pFans[2]) || pDsd->Type != Ifd_ManObjFromLit(p, pDsd->pFans[2])->Type );
    if ( DiffType )
        printf( "%c", Symb[1][pDsd->Type] );
}
void Ifd_ObjPrint( Ifd_Man_t * p, int iLit )
{
    int Counter = 0;
    if ( iLit == 0 )
        { printf( "0\n" ); return; }
    if ( iLit == 1 )
        { printf( "1\n" ); return; }
    Ifd_ObjPrint_rec( p, iLit, &Counter, 1 );
    printf( "\n" );
}
void Ifd_ManPrint( Ifd_Man_t * p )
{
    int i;
    for ( i = 0; i < p->nObjs; i++ )
    {
        printf( "%4d : ", i );
        Ifd_ObjPrint( p, Abc_Var2Lit( i, 0 ) );
    }
}


/**Function*************************************************************

  Synopsis    [Computing truth tables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Ifd_ObjTruth_rec( Ifd_Man_t * p, int iLit, int * pCounter )
{
    static word s_Truths6[6] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
        ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000),
        ABC_CONST(0xFFFFFFFF00000000)
    };
    Ifd_Obj_t * pDsd;
    word Fun0, Fun1, Fun2;
    assert( !Abc_LitIsCompl(iLit) );
    if ( iLit == 2 )
        return s_Truths6[(*pCounter)++];
    pDsd = Ifd_ManObjFromLit( p, iLit );

    Fun0 = Ifd_ObjTruth_rec( p, Abc_LitRegular(pDsd->pFans[0]), pCounter );
    Fun1 = Ifd_ObjTruth_rec( p, Abc_LitRegular(pDsd->pFans[1]), pCounter );
    if ( pDsd->pFans[2] != -1 )
    Fun2 = Ifd_ObjTruth_rec( p, Abc_LitRegular(pDsd->pFans[2]), pCounter );

    Fun0 = Abc_LitIsCompl(pDsd->pFans[0]) ? ~Fun0 : Fun0;
    Fun1 = Abc_LitIsCompl(pDsd->pFans[1]) ? ~Fun1 : Fun1;
    if ( pDsd->pFans[2] != -1 )
    Fun2 = Abc_LitIsCompl(pDsd->pFans[2]) ? ~Fun2 : Fun2;

    if ( pDsd->Type == 1 )
        return Fun0 & Fun1;
    if ( pDsd->Type == 2 )
        return Fun0 ^ Fun1;
    if ( pDsd->Type == 3 )
        return (Fun2 & Fun1) | (~Fun2 & Fun0);
    assert( 0 );
    return -1;
}
word Ifd_ObjTruth( Ifd_Man_t * p, int iLit )
{
    word Fun;
    int Counter = 0;
    if ( iLit == 0 )
        return 0;
    if ( iLit == 1 )
        return ~(word)0;
    Fun = Ifd_ObjTruth_rec( p, Abc_LitRegular(iLit), &Counter );
    return Abc_LitIsCompl(iLit) ? ~Fun : Fun;
}
void Ifd_ManTruthAll( Ifd_Man_t * p )
{
    word Fun;
    int i;
    assert( Vec_WrdSize(p->vTruths) == 0 );
    for ( i = 0; i < p->nObjs; i++ )
    {
        Fun = Ifd_ObjTruth( p, Abc_Var2Lit( i, 0 ) );
        Vec_WrdPush( p->vTruths, Fun );
//        Extra_PrintHex( stdout, (unsigned *)&Fun, 6 ); printf( " " );
//        Kit_DsdPrintFromTruth( (unsigned *)&Fun, 6 ); printf( "\n" );
    }
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
    assert( iDsdC != -1 || iDsd0 >= iDsd1 );
    assert( iDsdC == -1 || !Abc_LitIsCompl(iDsd1) );
    pData[0] = iDsd0;
    pData[1] = iDsd1;
    pData[2] = iDsdC;
    pData[3] = Type;
    return *Hsh_IntManLookup( p->vHash, pData );
}
void Ifd_ManHashInsert( Ifd_Man_t * p, int iDsd0, int iDsd1, int iDsdC, int Type, int Res )
{
    int iObj;
    assert( iDsdC != -1 || iDsd0 >= iDsd1 );
    assert( iDsdC == -1 || !Abc_LitIsCompl(iDsd1) );
    Vec_IntPush( p->vArgs, iDsd0 );
    Vec_IntPush( p->vArgs, iDsd1 );
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
    assert( iDsdC != -1 || iDsd0 >= iDsd1 );
    assert( iDsdC == -1 || !Abc_LitIsCompl(iDsd1) );
    Vec_IntPush( p->vArgs, iDsd0 );
    Vec_IntPush( p->vArgs, iDsd1 );
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
        if ( p->nObjs == p->nObjsAlloc )
            printf( "The number of nodes is more than %d\n", p->nObjs );
        assert( p->nObjs < p->nObjsAlloc );
        iObj = p->nObjs;
        pObj = Ifd_ManObj( p, p->nObjs++ );
        pObj->nFreq = 1;
        pObj->nSupp = Ifd_LitSuppSize(p, iDsd0) + Ifd_LitSuppSize(p, iDsd1) + Ifd_LitSuppSize(p, iDsdC); 
        pObj->Type  = Type;
        if ( Type == 1 )
            pObj->fWay = 0;
        else if ( Type == 2 )
            pObj->fWay = Ifd_ManObjFromLit(p, iDsd0)->fWay || Ifd_ManObjFromLit(p, iDsd1)->fWay;
        else if ( Type == 3 )
            pObj->fWay = (Ifd_ManObjFromLit(p, iDsd0)->fWay && Ifd_ManObjFromLit(p, iDsd1)->fWay) || (iDsd0 == iDsd1 && Ifd_ManObjFromLit(p, iDsdC)->fWay);
        else assert( 0 );
        pObj->pFans[0] = iDsd0;
        pObj->pFans[1] = iDsd1;
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
        if ( Abc_LitIsCompl(iDsdC) )
        {
            ABC_SWAP( int, iDsd0, iDsd1 );
            iDsdC = Abc_LitNot(iDsdC);
        }
        if ( Abc_LitIsCompl(iDsd1) )
            fCompl ^= 1, iDsd0 = Abc_LitNot(iDsd0), iDsd1 = Abc_LitNot(iDsd1);
    }
    assert( iDsd0 > 1 && iDsd1 > 1 && Type >= 1 && Type <= 3 );
/*
    // check cache
    iThis = Ifd_ManHashLookup( p, iDsd0, iDsd1, iDsdC, Type );
    if ( iThis != -1 )
        return Abc_Var2Lit( iThis, fCompl );
*/
    // create new entry
    if ( Type == 3 )
    {
        iThis = Ifd_ManHashFindOrAdd( p, iDsd0, iDsd1, iDsdC, Type );
        return Abc_Var2Lit( iThis, fCompl );
    }
    assert( iDsdC == -1 );
    Vec_IntClear( p->vSuper );
    Ifd_ManOperSuper_rec( p, iDsd0, Type, p->vSuper );
    Ifd_ManOperSuper_rec( p, iDsd1, Type, p->vSuper );
    Vec_IntSort( p->vSuper, 1 );
    iLit0 = Vec_IntEntry( p->vSuper, 0 );
    Vec_IntForEachEntryStart( p->vSuper, iLit1, i, 1 )
        iLit0 = Abc_Var2Lit( Ifd_ManHashFindOrAdd(p, iLit0, iLit1, -1, Type), 0 );
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
        assert( v < IFM_MAX_STR );
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
void Ifd_ManDsdTest2()
{
    char * p = "(abc)";
    char * q = "(a[bc])";
    char * r = "[<abc>(def)]";
    Ifd_Man_t * pMan = Ifd_ManStart();
    int iLit = Ifd_ManFindDsd( pMan, p );
    Ifd_ObjPrint( pMan, iLit );
    Ifd_ManStop( pMan );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wrd_t * Ifd_ManDsdTruths( int nVars )
{
    int fUseMux = 1;
    Vec_Wrd_t * vTruths;
    Ifd_Man_t * pMan = Ifd_ManStart();
    Ifd_Obj_t * pLeaf0, * pLeaf1, * pLeaf2;
    int v, i, j, k, c0, c1, c2;
    for ( v = 2; v <= nVars; v++ )
    {
        // create ANDs/XORs
        for ( i = 1; i < v; i++ )
        for ( j = 1; j < v; j++ )
        if ( i + j == v )
        {
            Ifd_ManForEachNodeWithSupp( pMan, i, pLeaf0, c0 )
            Ifd_ManForEachNodeWithSupp( pMan, j, pLeaf1, c1 )
            {
                assert( (int)pLeaf0->nSupp == i );
                assert( (int)pLeaf1->nSupp == j );
                Ifd_ManOper( pMan, Abc_Var2Lit(c0, 0), Abc_Var2Lit(c1, 0), -1, 1 );
                if ( !pLeaf1->fWay )
                Ifd_ManOper( pMan, Abc_Var2Lit(c0, 0), Abc_Var2Lit(c1, 1), -1, 1 );
                if ( !pLeaf0->fWay )
                Ifd_ManOper( pMan, Abc_Var2Lit(c0, 1), Abc_Var2Lit(c1, 0), -1, 1 );
                if ( !pLeaf0->fWay && !pLeaf1->fWay )
                Ifd_ManOper( pMan, Abc_Var2Lit(c0, 1), Abc_Var2Lit(c1, 1), -1, 1 );
                Ifd_ManOper( pMan, Abc_Var2Lit(c0, 0), Abc_Var2Lit(c1, 0), -1, 2 );
            }
        }
        // create MUX
        if ( fUseMux )
        for ( i = 1; i < v-1; i++ )
        for ( j = 1; j < v-1; j++ )
        for ( k = 1; k < v-1; k++ )
        if ( i + j + k == v )
        {
            Ifd_ManForEachNodeWithSupp( pMan, i, pLeaf0, c0 )
            Ifd_ManForEachNodeWithSupp( pMan, j, pLeaf1, c1 )
            Ifd_ManForEachNodeWithSupp( pMan, k, pLeaf2, c2 )
            {
                assert( (int)pLeaf0->nSupp == i );
                assert( (int)pLeaf1->nSupp == j );
                assert( (int)pLeaf2->nSupp == k );
//printf( "%d %d %d   ", i, j, k );
//printf( "%d %d %d\n", Ifd_ObjId(pMan, pLeaf0), Ifd_ObjId(pMan, pLeaf1), Ifd_ObjId(pMan, pLeaf2) );
                if ( pLeaf2->fWay && c0 < c1 )
                    continue;
                Ifd_ManOper( pMan, Abc_Var2Lit(c0, 0), Abc_Var2Lit(c1, 0), Abc_Var2Lit(c2, 0), 3 );
                if ( !pLeaf0->fWay && !pLeaf1->fWay )
                Ifd_ManOper( pMan, Abc_Var2Lit(c0, 1), Abc_Var2Lit(c1, 0), Abc_Var2Lit(c2, 0), 3 );
            }
        }
        // bookmark
        Vec_IntPush( pMan->vMarks, pMan->nObjs );
    }
//    Ifd_ManPrint( pMan );
    Ifd_ManTruthAll( pMan );
    vTruths = pMan->vTruths; pMan->vTruths = NULL;
    Ifd_ManStop( pMan );
    return vTruths;
}


/**Function*************************************************************

  Synopsis    [Generating the guided array for minimal permutations.]

  Description [http://icodesnip.com/search/johnson%20trotter/]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ifd_ManDsdPermPrint( int * perm, int size ) 
{
    int i;
    for ( i = 0; i < size; i++ )
        printf( "%d", perm[i] );
    printf( "\n" );
}
Vec_Int_t * Ifd_ManDsdPermJT( int n ) 
{
    Vec_Int_t * vGuide = Vec_IntAlloc( 100 );
    int *array, *dir, tmp, tmp2, i, max;
    array = (int*)malloc(sizeof(int) * n);
    dir = (int*)calloc(n, sizeof(int));
    for (i = 0; i < n; i++)
    array[i] = i;
    max = n - 1;
    if (n != 1)
    do 
    {
//        Ifd_ManDsdPermPrint(array, n);
        tmp = array[max];
        tmp2 = dir[max];
        i = !dir[max] ? max - 1 : max + 1;
        array[max] = array[i];
        array[i] = tmp;
        Vec_IntPush( vGuide, Abc_MinInt(max, i) );
        dir[max] = dir[i];
        dir[i] = tmp2;
        for (i = 0; i < n; i++)
            if (array[i] > tmp)
                dir[i] = !dir[i];
        max = n;
        for (i = 0; i < n; i++)
            if (((!dir[i] && i != 0 && array[i] > array[i-1]) || (dir[i] && i != n-1 && array[i] > array[i+1])) && (array[i] > array[max] || max == n))
                max = i;
    } 
    while (max < n);
//    Ifd_ManDsdPermPrint(array,n);
    Vec_IntPush( vGuide, 0 );
    free(dir);
    free(array);
    return vGuide;
}
int Ifd_ManDsdTest4() 
{
    int pPerm[6] = { 0, 1, 2, 3, 4, 5 };
    Vec_Int_t * vGuide = Ifd_ManDsdPermJT( 6 );
    int i, Entry;
    Vec_IntForEachEntry( vGuide, Entry, i )
    {
        ABC_SWAP( int, pPerm[Entry], pPerm[Entry+1] );
        Ifd_ManDsdPermPrint( pPerm, 6 );
    }
    Vec_IntFree( vGuide );
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Extra_Truth6SwapAdjacent( word t, int iVar )
{
    // variable swapping code
    static word PMasks[5][3] = {
        { ABC_CONST(0x9999999999999999), ABC_CONST(0x2222222222222222), ABC_CONST(0x4444444444444444) },
        { ABC_CONST(0xC3C3C3C3C3C3C3C3), ABC_CONST(0x0C0C0C0C0C0C0C0C), ABC_CONST(0x3030303030303030) },
        { ABC_CONST(0xF00FF00FF00FF00F), ABC_CONST(0x00F000F000F000F0), ABC_CONST(0x0F000F000F000F00) },
        { ABC_CONST(0xFF0000FFFF0000FF), ABC_CONST(0x0000FF000000FF00), ABC_CONST(0x00FF000000FF0000) },
        { ABC_CONST(0xFFFF00000000FFFF), ABC_CONST(0x00000000FFFF0000), ABC_CONST(0x0000FFFF00000000) }
    };
    assert( iVar < 5 );
    return (t & PMasks[iVar][0]) | ((t & PMasks[iVar][1]) << (1 << iVar)) | ((t & PMasks[iVar][2]) >> (1 << iVar));
}
static inline word Extra_Truth6ChangePhase( word t, int iVar)
{
    // elementary truth tables
    static word Truth6[6] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
        ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000),
        ABC_CONST(0xFFFFFFFF00000000)
    };
    assert( iVar < 6 );
    return ((t & ~Truth6[iVar]) << (1 << iVar)) | ((t & Truth6[iVar]) >> (1 << iVar));
}
Vec_Wrd_t * Extra_Truth6AllConfigs2( word t, int * pComp, int * pPerm, int nVars )
{
    int nPerms = Extra_Factorial( nVars );
    int nSwaps = (1 << nVars);
    Vec_Wrd_t * vTruths = Vec_WrdStart( nPerms * (1 << (nVars+1)) );
    word tCur, tTemp1, tTemp2;
    int i, p, c;
    for ( i = 0; i < 2; i++ )
    {
        tCur = i ? t : ~t;
        tTemp1 = tCur;
        for ( p = 0; p < nPerms; p++ )
        {
            tTemp2 = tCur;
            for ( c = 0; c < nSwaps; c++ )
            {
                Vec_WrdWriteEntry( vTruths, (p << (nVars+1))|(i << nVars)|c, tCur );
                tCur = Extra_Truth6ChangePhase( tCur, pComp[c] );
            }
            assert( tTemp2 == tCur );
            tCur = Extra_Truth6SwapAdjacent( tCur, pPerm[p] );
        }
        assert( tTemp1 == tCur );
    }
    if ( t )
    {
        int i;
        word Truth;
        Vec_WrdForEachEntry( vTruths, Truth, i )
            assert( Truth );
    }
    return vTruths;
}
Vec_Wrd_t * Extra_Truth6AllConfigs( word t, int * pComp, int * pPerm, int nVars )
{
    int nPerms = Extra_Factorial( nVars );
    int nSwaps = (1 << nVars);
    Vec_Wrd_t * vTruths = Vec_WrdStart( nPerms * nSwaps );
    word tCur, tTemp1, tTemp2;
    int i, p, c;
    for ( i = 1; i < 2; i++ )
    {
        tCur = i ? ~t : t;
        tTemp1 = tCur;
        for ( p = 0; p < nPerms; p++ )
        {
            tTemp2 = tCur;
            for ( c = 0; c < nSwaps; c++ )
            {
                Vec_WrdWriteEntry( vTruths, (p << (nVars))|c, tCur );
                tCur = Extra_Truth6ChangePhase( tCur, pComp[c] );
            }
            assert( tTemp2 == tCur );
            tCur = Extra_Truth6SwapAdjacent( tCur, pPerm[p] );
        }
        assert( tTemp1 == tCur );
    }
    if ( t )
    {
        int i;
        word Truth;
        Vec_WrdForEachEntry( vTruths, Truth, i )
            assert( Truth );
    }
    return vTruths;
}
int Ifd_ManDsdTest() 
{
    int nVars = 6;
    Vec_Wrd_t * vTruths = Ifd_ManDsdTruths( nVars );
    Vec_Wrd_t * vConfigs;
    Vec_Int_t * vUniques;
    int * pComp, * pPerm;
    word Truth;
    int i, Counter = 0;
    pComp = Extra_GreyCodeSchedule( nVars );
    pPerm = Extra_PermSchedule( nVars );
    Vec_WrdForEachEntry( vTruths, Truth, i )
    {
        vConfigs = Extra_Truth6AllConfigs( Truth, pComp, pPerm, nVars );
        vUniques = Hsh_WrdManHashArray( vConfigs, 1 );
        Vec_IntUniqify( vUniques );
        Counter += Vec_IntSize(vUniques);

//printf( "%5d : ", i ); Kit_DsdPrintFromTruth( &Truth, nVars ), printf( "  " ), Vec_IntPrint( vUniques ), printf( "\n" );

        Vec_IntFree( vUniques );
        Vec_WrdFree( vConfigs );
    }
    Vec_WrdFree( vTruths );
    ABC_FREE( pPerm );
    ABC_FREE( pComp );
    printf( "Total = %d.\n", Counter );
    return 1;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

