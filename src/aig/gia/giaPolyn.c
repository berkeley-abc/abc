/**CFile****************************************************************

  FileName    [giaPolyn.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Polynomial manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaPolyn.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/vec/vecWec.h"
#include "misc/vec/vecHsh.h"
#include "misc/vec/vecQue.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/*
!a            ->   1 - a
a & b         ->   ab
a | b         ->   a + b - ab
a ^ b         ->   a + b - 2ab
MUX(a, b, c)  ->   ab | (1 - a)c = ab + (1-a)c - ab(1-a)c = ab + c - ac

!a & b        ->   (1 - a)b = b - ab
 a & !b       ->   a(1 - b) = a - ab
!a & !b       ->   1 - a - b + ab
!(a & b)      ->   1 - ab
*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_PolynAddNew( Hsh_VecMan_t * pHash, Vec_Int_t * vCoef, int Coef, Vec_Int_t * vProd, Vec_Wec_t * vMap )
{
    int i, Lit, Value;
    //Vec_IntPrint( vProd );

    Value = Hsh_VecManAdd( pHash, vProd );
    if ( Value == Vec_IntSize(vCoef) )
    {
        Vec_IntPush( vCoef, 0 );
        Vec_IntForEachEntry( vProd, Lit, i )
            Vec_WecPush( vMap, Abc_Lit2Var(Lit), Value );
    }
    assert( Value < Vec_IntSize(vCoef) );
    Vec_IntAddToEntry( vCoef, Value, Coef );
}
int Gia_PolynTransform1( Hsh_VecMan_t * pHash, Vec_Int_t * vCoef, int Coef, Vec_Int_t * vProd, Vec_Wec_t * vMap, int Id )
{
    int i, Lit;
    Vec_IntForEachEntry( vProd, Lit, i )
        if ( Abc_Lit2Var(Lit) == Id )
            break;
    assert( i < Vec_IntSize(vProd) );
    if ( !Abc_LitIsCompl(Lit) )
        return 0;
    // update array
    Vec_IntWriteEntry( vProd, i, Abc_LitNot(Lit) );
    Gia_PolynAddNew( pHash, vCoef, Coef, vProd, vMap );
    Vec_IntWriteEntry( vProd, i, Lit );
    return 1;
}
void Gia_PolynTransform( Hsh_VecMan_t * pHash, Vec_Int_t * vCoef, int Coef, Vec_Int_t * vProd, Vec_Wec_t * vMap, int Id, int Lit0, int Lit1, Vec_Int_t * vTemp )
{
    int pArray[2] = { Lit0, Lit1 };
    Vec_Int_t vTwo = { 2, 2, pArray };

    int Var0 = Abc_Lit2Var( Lit0 );
    int Var1 = Abc_Lit2Var( Lit1 );
    int i, Lit = Vec_IntPop(vProd);

    assert( Abc_Lit2Var(Lit) == Id );
    if ( Abc_LitIsCompl(Lit) )
    {
        Gia_PolynAddNew( pHash, vCoef, Coef, vProd, vMap );
        Coef = -Coef;
    }

    assert( Var0 < Var1 );
    Vec_IntForEachEntry( vProd, Lit, i )
        if ( Abc_LitNot(Lit) == Lit0 || Abc_LitNot(Lit) == Lit1 )
            return;
    assert( Vec_IntCap(vTemp) >= Vec_IntSize(vTemp) + 2 );

    // merge inputs
    Vec_IntTwoMerge2Int( vProd, &vTwo, vTemp );
/*
    printf( "\n" );
    Vec_IntPrint( vProd );
    Vec_IntPrint( &vTwo );
    Vec_IntPrint( vTemp );
    printf( "\n" );
*/
    // create new
    Gia_PolynAddNew( pHash, vCoef, Coef, vTemp, vMap );
}
int Gia_PolynPrint( Hsh_VecMan_t * pHash, Vec_Int_t * vCoef )
{
    Vec_Int_t * vProd;
    int Value, Coef, Lit, i, Count = 0;
    Vec_IntForEachEntry( vCoef, Coef, Value )
    {
        if ( Coef == 0 )
            continue;
        vProd = Hsh_VecReadEntry( pHash, Value );
        printf( "(%d)", Coef );
        Vec_IntForEachEntry( vProd, Lit, i )
            printf( "*%d", Lit );
        printf( " " );
        Count++;
    }
    printf( "\n" );
    return Count;
}
void Gia_PolynTest( Gia_Man_t * pGia )
{
    Hsh_VecMan_t * pHash = Hsh_VecManStart( 1000000 );
    Vec_Int_t * vCoef = Vec_IntAlloc( 1000000 );
    Vec_Wec_t * vMap = Vec_WecStart( Gia_ManObjNum(pGia) );
    Vec_Int_t * vTemp = Vec_IntAlloc( 100000 );
    Vec_Int_t * vThisOne, * vProd;
    Gia_Obj_t * pObj;
    int i, k, Value, Coef, Count;
    abctime clk = Abc_Clock();

    assert( Gia_ManPoNum(pGia) < 32 );

    // add constant
    Value = Hsh_VecManAdd( pHash, vTemp );
    assert( Value == 0 );
    Vec_IntPush( vCoef, 0 );

    // start the outputs
    Gia_ManForEachPo( pGia, pObj, i )
    {
        assert( Gia_ObjFaninId0p(pGia, pObj) > 0 );
        Vec_IntFill( vTemp, 1, Gia_ObjFaninLit0p(pGia, pObj) );
        Value = Hsh_VecManAdd( pHash, vTemp );
        //assert( Value == i + 1 );
        Vec_IntPush( vCoef, 1 << i );
        Vec_WecPush( vMap, Gia_ObjFaninId0p(pGia, pObj), Value );
    }
    assert( Vec_IntSize(vCoef) == Hsh_VecSize(pHash) );

    Gia_PolynPrint( pHash, vCoef );

    // substitute
    Gia_ManForEachAndReverse( pGia, pObj, i )
    {
        vThisOne = Vec_WecEntry( vMap, i );
        assert( Vec_IntSize(vThisOne) > 0 );
        Vec_IntForEachEntry( vThisOne, Value, k )
        {
            vProd = Hsh_VecReadEntry( pHash, Value );
            Coef = Vec_IntEntry( vCoef, Value );
            if ( Coef == 0 )
                continue;
            Gia_PolynTransform( pHash, vCoef, Coef, vProd, vMap, i, Gia_ObjFaninLit0p(pGia, pObj), Gia_ObjFaninLit1p(pGia, pObj), vTemp );
            Vec_IntWriteEntry( vCoef, Value, 0 );
        }
        Vec_IntErase( vThisOne );
    }

    // inputs
    Gia_ManForEachCiReverse( pGia, pObj, i )
    {
        vThisOne = Vec_WecEntry( vMap, Gia_ObjId(pGia, pObj) );
        if ( Vec_IntSize(vThisOne) == 0 )
            continue;
        assert( Vec_IntSize(vThisOne) > 0 );
        Vec_IntForEachEntry( vThisOne, Value, k )
        {
            vProd = Hsh_VecReadEntry( pHash, Value );
            Coef = Vec_IntEntry( vCoef, Value );
            if ( Coef == 0 )
                continue;
            if ( Gia_PolynTransform1( pHash, vCoef, Coef, vProd, vMap, Gia_ObjId(pGia, pObj) ) )
                Vec_IntWriteEntry( vCoef, Value, 0 );
        }
        Vec_IntErase( vThisOne );
    }

    Count = Gia_PolynPrint( pHash, vCoef );
    printf( "Entries = %d. Useful = %d.  ", Vec_IntSize(vCoef), Count );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

    Hsh_VecManStop( pHash );
    Vec_IntFree( vCoef );
    Vec_WecFree( vMap );
    Vec_IntFree( vTemp );
}





typedef struct Pln_Man_t_ Pln_Man_t;
struct Pln_Man_t_
{
    Gia_Man_t *    pGia;      // AIG manager
    Hsh_VecMan_t * pHashC;    // hash table for constants
    Hsh_VecMan_t * pHashM;    // hash table for monomials
    Vec_Que_t *    vQue;      // queue by largest node
    Vec_Flt_t *    vCounts;   // largest node
    Vec_Int_t *    vCoefs;    // coefficients for each monomial
    Vec_Int_t *    vTempC[2]; // polynomial representation
    Vec_Int_t *    vTempM[4]; // polynomial representation
    int            nBuilds;   // builds
};
    
/**Function*************************************************************

  Synopsis    [Computation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pln_Man_t * Pln_ManAlloc( Gia_Man_t * pGia )
{
    Pln_Man_t * p = ABC_CALLOC( Pln_Man_t, 1 );
    p->pGia      = pGia;
    p->pHashC    = Hsh_VecManStart( 1000 );
    p->pHashM    = Hsh_VecManStart( 1000 );
    p->vQue      = Vec_QueAlloc( 1000 );
    p->vCounts   = Vec_FltAlloc( 1000 );
    p->vCoefs    = Vec_IntAlloc( 1000 );
    p->vTempC[0] = Vec_IntAlloc( 100 );
    p->vTempC[1] = Vec_IntAlloc( 100 );
    p->vTempM[0] = Vec_IntAlloc( 100 );
    p->vTempM[1] = Vec_IntAlloc( 100 );
    p->vTempM[2] = Vec_IntAlloc( 100 );
    p->vTempM[3] = Vec_IntAlloc( 100 );
    Vec_QueSetPriority( p->vQue, Vec_FltArrayP(p->vCounts) );
    // add 0-constant and 1-monomial
    Hsh_VecManAdd( p->pHashC, p->vTempC[0] );
    Hsh_VecManAdd( p->pHashM, p->vTempM[0] );
    Vec_FltPush( p->vCounts, 0 );
    Vec_IntPush( p->vCoefs, 0 );
    return p;
}
void Pln_ManStop( Pln_Man_t * p )
{
    Hsh_VecManStop( p->pHashC );
    Hsh_VecManStop( p->pHashM );
    Vec_QueFree( p->vQue );
    Vec_FltFree( p->vCounts );
    Vec_IntFree( p->vCoefs );
    Vec_IntFree( p->vTempC[0] );
    Vec_IntFree( p->vTempC[1] );
    Vec_IntFree( p->vTempM[0] );
    Vec_IntFree( p->vTempM[1] );
    Vec_IntFree( p->vTempM[2] );
    Vec_IntFree( p->vTempM[3] );
    ABC_FREE( p );
}
void Pln_ManPrintFinal( Pln_Man_t * p )
{
    Vec_Int_t * vArray;
    int k, Entry, iMono, iConst, Count = 0;
    Vec_IntForEachEntry( p->vCoefs, iConst, iMono )
    {
        if ( iConst == 0 ) 
            continue;

        Count++;

        if ( Vec_IntSize(p->vCoefs) > 1000 )
            continue;

        vArray = Hsh_VecReadEntry( p->pHashC, iConst );
        Vec_IntForEachEntry( vArray, Entry, k )
            printf( "%s%s2^%d", k ? " + " : "", Entry < 0 ? "-" : "+", Abc_AbsInt(Entry)-1 );

        vArray = Hsh_VecReadEntry( p->pHashM, iMono );
        Vec_IntForEachEntry( vArray, Entry, k )
            printf( " * %d", Entry );
        printf( "\n" );
    }
    printf( "HashC = %d. HashM = %d.  Total = %d. Used = %d.\n", Hsh_VecSize(p->pHashC), Hsh_VecSize(p->pHashM), p->nBuilds, Count );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_PolynMergeConstOne( Vec_Int_t * vConst, int New )
{
    int i, Old;
    assert( New != 0 );
    Vec_IntForEachEntry( vConst, Old, i )
    {
        assert( Old != 0 );
        if ( Old == New ) // A == B
        {
            Vec_IntDrop( vConst, i );
            Gia_PolynMergeConstOne( vConst, New > 0 ? New + 1 : New - 1 );
            return;
        }
        if ( Abc_AbsInt(Old) == Abc_AbsInt(New) ) // A == -B
        {
            Vec_IntDrop( vConst, i );
            return;
        }
        if ( Old + New == 1 || Old + New == -1 )  // sign(A) != sign(B)  &&  abs(abs(A)-abs(B)) == 1 
        {
            int Value = Abc_MinInt( Abc_AbsInt(Old), Abc_AbsInt(New) );
            Vec_IntDrop( vConst, i );
            Gia_PolynMergeConstOne( vConst, (Old + New == 1) ? Value : -Value );
            return;
        }
    }
    Vec_IntPushUniqueOrder( vConst, New );
}
static inline void Gia_PolynMergeConst( Vec_Int_t * vConst, Pln_Man_t * p, int iConstAdd )
{
    int i, New;
    Vec_Int_t * vConstAdd = Hsh_VecReadEntry( p->pHashC, iConstAdd );
    Vec_IntForEachEntry( vConstAdd, New, i )
    {
        Gia_PolynMergeConstOne( vConst, New );
        vConstAdd = Hsh_VecReadEntry( p->pHashC, iConstAdd );
    }
}
static inline void Gia_PolynBuildAdd( Pln_Man_t * p, Vec_Int_t * vTempC, Vec_Int_t * vTempM )
{
    int iConst, iMono = vTempM ? Hsh_VecManAdd(p->pHashM, vTempM) : 0;
    p->nBuilds++;
    if ( iMono == Vec_IntSize(p->vCoefs) ) // new monomial
    {
        iConst = Hsh_VecManAdd( p->pHashC, vTempC );
        Vec_IntPush( p->vCoefs, iConst );
        Vec_FltPush( p->vCounts, Vec_IntEntryLast(vTempM) );
        Vec_QuePush( p->vQue, iMono );
//        Vec_QueUpdate( p->vQue, iMono );
        return;
    }
    // this monomial exists
    iConst = Vec_IntEntry( p->vCoefs, iMono );
    if ( iConst )
        Gia_PolynMergeConst( vTempC, p, iConst );
    iConst = Hsh_VecManAdd( p->pHashC, vTempC );
    Vec_IntWriteEntry( p->vCoefs, iMono, iConst );
}
void Gia_PolynBuildOne( Pln_Man_t * p, int iMono )
{
    Gia_Obj_t * pObj; 
    Vec_Int_t * vArray, * vConst;
    int iFan0, iFan1;
    int k, iConst, iDriver;

    assert( Vec_IntSize(p->vCoefs) == Hsh_VecSize(p->pHashM) );
    vArray  = Hsh_VecReadEntry( p->pHashM, iMono );
    iDriver = Vec_IntEntryLast( vArray );
    pObj    = Gia_ManObj( p->pGia, iDriver );
    if ( !Gia_ObjIsAnd(pObj) )
        return;

    iConst = Vec_IntEntry( p->vCoefs, iMono );
    if ( iConst == 0 )
        return;
    Vec_IntWriteEntry( p->vCoefs, iMono, 0 );

    iFan0 = Gia_ObjFaninId0p(p->pGia, pObj);
    iFan1 = Gia_ObjFaninId1p(p->pGia, pObj);
    for ( k = 0; k < 4; k++ )
    {
        Vec_IntClear( p->vTempM[k] );
        Vec_IntAppend( p->vTempM[k], vArray );
        Vec_IntPop( p->vTempM[k] );
        if ( k == 1 || k == 3 )
            Vec_IntPushUniqueOrder( p->vTempM[k], iFan0 );    // x
        if ( k == 2 || k == 3 )
            Vec_IntPushUniqueOrder( p->vTempM[k], iFan1 );    // y
    }

    vConst = Hsh_VecReadEntry( p->pHashC, iConst );
    for ( k = 0; k < 2; k++ )
        Vec_IntAppendMinus( p->vTempC[k], vConst, k );

    if ( Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) )       //  C * (1 - x) * (1 - y)
    {
        Gia_PolynBuildAdd( p, p->vTempC[0], p->vTempM[0] );   //  C * 1
        Gia_PolynBuildAdd( p, p->vTempC[1], p->vTempM[1] );   // -C * x
        vConst = Hsh_VecReadEntry( p->pHashC, iConst );
        for ( k = 0; k < 2; k++ )
            Vec_IntAppendMinus( p->vTempC[k], vConst, k );
        Gia_PolynBuildAdd( p, p->vTempC[1], p->vTempM[2] );   // -C * y 
        Gia_PolynBuildAdd( p, p->vTempC[0], p->vTempM[3] );   //  C * x * y
    }
    else if ( Gia_ObjFaninC0(pObj) && !Gia_ObjFaninC1(pObj) ) //  C * (1 - x) * y
    {
        Gia_PolynBuildAdd( p, p->vTempC[0], p->vTempM[2] );   //  C * y 
        Gia_PolynBuildAdd( p, p->vTempC[1], p->vTempM[3] );   // -C * x * y
    }
    else if ( !Gia_ObjFaninC0(pObj) && Gia_ObjFaninC1(pObj) ) //  C * x * (1 - y)
    {
        Gia_PolynBuildAdd( p, p->vTempC[0], p->vTempM[1] );   //  C * x 
        Gia_PolynBuildAdd( p, p->vTempC[1], p->vTempM[3] );   // -C * x * y
    }
    else   
        Gia_PolynBuildAdd( p, p->vTempC[0], p->vTempM[3] );   //  C * x * y
}
int Gia_PolyFindNext2( Pln_Man_t * p )
{
    Gia_Obj_t * pObj; 
    Vec_Int_t * vArray;
    int Max = 0, iBest = 0, iConst, iMono, iDriver;
    Vec_IntForEachEntryStart( p->vCoefs, iConst, iMono, 1 )
    {
        if ( iConst == 0 ) 
            continue;
        vArray  = Hsh_VecReadEntry( p->pHashM, iMono );
        iDriver = Vec_IntEntryLast( vArray );
        pObj    = Gia_ManObj( p->pGia, iDriver );
        if ( !Gia_ObjIsAnd(pObj) )
            continue;
        if ( Max < Vec_IntEntryLast(vArray) )
        {
            Max   = Vec_IntEntryLast(vArray);
            iBest = iMono;
        }
    }
    //Vec_IntPrint( Hsh_VecReadEntry(p->pHashM, iBest) );
    return iBest;
}
int Gia_PolyFindNext( Pln_Man_t * p )
{
    int iBest = Vec_QueSize(p->vQue) ?  Vec_QuePop(p->vQue) : 0;
    //Vec_IntPrint( Hsh_VecReadEntry(p->pHashM, iBest) );
    return iBest;
}
void Gia_PolynBuildTest( Gia_Man_t * pGia )
{
    abctime clk = Abc_Clock();//, clk2 = 0;
    Gia_Obj_t * pObj; 
    int i, iMono, iDriver;
    Pln_Man_t * p = Pln_ManAlloc( pGia );
    Gia_ManForEachCoReverse( pGia, pObj, i )
    {
        Vec_IntFill( p->vTempC[0], 1,  i+1 );      //  2^i
        Vec_IntFill( p->vTempC[1], 1, -i-1 );      // -2^i

        iDriver = Gia_ObjFaninId0p( pGia, pObj );
        Vec_IntFill( p->vTempM[0], 1, iDriver );   //  Driver

        if ( Gia_ObjFaninC0(pObj) )
        {
            Gia_PolynBuildAdd( p, p->vTempC[0], NULL );           //  C
            Gia_PolynBuildAdd( p, p->vTempC[1], p->vTempM[0] );   // -C * Driver
        }
        else
            Gia_PolynBuildAdd( p, p->vTempC[0], p->vTempM[0] );   //  C * Driver
    }
    while ( 1 )
    {
        //abctime temp = Abc_Clock();
        iMono = Gia_PolyFindNext(p);
        if ( !iMono )
            break;
        Gia_PolynBuildOne( p, iMono );
        //clk2 += Abc_Clock() - temp;
    }
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    //Abc_PrintTime( 1, "Time2", clk2 );
    Pln_ManPrintFinal( p );
    Pln_ManStop( p );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

