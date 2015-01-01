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


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

