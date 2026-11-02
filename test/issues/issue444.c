#include "base/main/mainInt.h"
#include "misc/tim/tim.h"
#include "proof/cec/cec.h"

static Gia_Man_t * MakeNetwork( int fChange, int fSeq )
{
    Gia_Man_t * p = Gia_ManStart( 20 );
    Gia_Obj_t * pObj;
    Tim_Man_t * pTime;
    int a, b, c, x, y, z, i;
    p->pName = Abc_UtilStrsav( "zero_boxes" );
    a = Gia_ManAppendCi( p );
    b = Gia_ManAppendCi( p );
    c = Gia_ManAppendCi( p );
    x = Gia_ManAppendAnd( p, a, b );
    if ( fChange )
    {
        // ((a & b) | (a & !b)) & c has redundant mapped LUTs.
        y = Gia_ManAppendAnd( p, a, Abc_LitNot(b) );
        z = Gia_ManAppendAnd( p, Abc_LitNot(x), Abc_LitNot(y) );
        x = Gia_ManAppendAnd( p, Abc_LitNot(z), c );
    }
    Gia_ManAppendCo( p, x );
    if ( fSeq )
        Gia_ManAppendCo( p, a );
    Gia_ManSetRegNum( p, fSeq );
    p->vMapping = Vec_IntStart( Gia_ManObjNum(p) );
    Gia_ManForEachAnd( p, pObj, i )
    {
        Vec_IntWriteEntry( p->vMapping, i, Vec_IntSize(p->vMapping) );
        Vec_IntPush( p->vMapping, 2 );
        Vec_IntPush( p->vMapping, Gia_ObjFaninId0(pObj, i) );
        Vec_IntPush( p->vMapping, Gia_ObjFaninId1(pObj, i) );
        Vec_IntPush( p->vMapping, i );
    }
    p->pManTime = pTime = Tim_ManStart( 3, 1 + fSeq );
    for ( i = 0; i < 3; i++ )
        Tim_ManInitPiArrival( pTime, i, i + 1.25f );
    for ( i = 0; i < 1 + fSeq; i++ )
        Tim_ManInitPoRequired( pTime, i, i + 20.5f );
    return p;
}

static int Check( Abc_Frame_t * pAbc, int fChange, int fSeq )
{
    Gia_Man_t * pOld = MakeNetwork( fChange, fSeq ), * pNew;
    Gia_Man_t * pRef = Gia_ManDup(pOld), * pCheck = NULL;
    Tim_Man_t * pTime;
    int i, fPassed = 0;
    Abc_FrameUpdateGia( pAbc, pOld );
    if ( Cmd_CommandExecute(pAbc, "&mfs -v") )
        goto cleanup;
    pNew = pAbc->pGia;
    if ( pNew == pOld || !pNew || !pNew->pManTime || pNew->pAigExtra ||
         Gia_ManRegNum(pNew) != fSeq || Gia_ManCiNum(pNew) != 3 || Gia_ManCoNum(pNew) != 1 + fSeq )
        goto cleanup;
    if ( fChange && Gia_ManLutNum(pNew) >= 4 )
        goto cleanup;
    pTime = (Tim_Man_t *)pNew->pManTime;
    if ( Tim_ManBoxNum(pTime) || Tim_ManCiNum(pTime) != 3 || Tim_ManCoNum(pTime) != 1 + fSeq )
        goto cleanup;
    for ( i = 0; i < 3; i++ )
        if ( Tim_ManGetCiArrival(pTime, i) != i + 1.25f )
            goto cleanup;
    for ( i = 0; i < 1 + fSeq; i++ )
        if ( Tim_ManGetCoRequired(pTime, i) != i + 20.5f )
            goto cleanup;
    // MFS preserves state boundaries: prove the combinational cut interfaces.
    pCheck = Gia_ManDup( pNew );
    pRef->nRegs = pCheck->nRegs = 0;
    fPassed = Cec_ManVerifyTwo( pRef, pCheck, 0 ) == 1;
cleanup:
    Gia_ManStop( pRef );
    if ( pCheck ) Gia_ManStop( pCheck );
    return fPassed;
}

int main( int argc, char ** argv )
{
    Abc_Frame_t * p;
    Gia_Man_t * pBad;
    int fPassed = 1, fChange, fSeq;
    setbuf( stdout, NULL );
    Abc_Start();
    p = Abc_FrameGetGlobalFrame();
    for ( fSeq = 0; fSeq < 2; fSeq++ )
        for ( fChange = 0; fChange < 2; fChange++ )
            if ( !Check(p, fChange, fSeq) )
            {
                printf( "FAIL: zero boxes, change=%d, sequential=%d\n", fChange, fSeq );
                fPassed = 0;
            }
    // A real box with a missing model must still be rejected.
    for ( fSeq = 0; fSeq < 2; fSeq++ )
    {
        pBad = MakeNetwork( 0, fSeq );
        Tim_ManCreateBox( (Tim_Man_t *)pBad->pManTime, 0, 1, 2, 1, 0, 0 );
        Abc_FrameUpdateGia( p, pBad );
        Cmd_CommandExecute( p, "&mfs" );
        fPassed &= p->pGia == pBad && Gia_ManRegNum(p->pGia) == fSeq;
    }
    Abc_Stop();
    return !fPassed;
}
