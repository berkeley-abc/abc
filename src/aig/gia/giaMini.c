/**CFile****************************************************************

  FileName    [giaMini.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Reader/writer for MiniAIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaMini.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "opt/dau/dau.h"
#include "base/main/main.h"
#include "misc/util/utilTruth.h"
#include "aig/miniaig/miniaig.h"
#include "aig/miniaig/minilut.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts MiniAIG into GIA.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjFromMiniFanin0Copy( Gia_Man_t * pGia, Vec_Int_t * vCopies, Mini_Aig_t * p, int Id )
{
    int Lit = Mini_AigNodeFanin0( p, Id );
    return Abc_LitNotCond( Vec_IntEntry(vCopies, Abc_Lit2Var(Lit)), Abc_LitIsCompl(Lit) );
}
int Gia_ObjFromMiniFanin1Copy( Gia_Man_t * pGia, Vec_Int_t * vCopies, Mini_Aig_t * p, int Id )
{
    int Lit = Mini_AigNodeFanin1( p, Id );
    return Abc_LitNotCond( Vec_IntEntry(vCopies, Abc_Lit2Var(Lit)), Abc_LitIsCompl(Lit) );
}
Gia_Man_t * Gia_ManFromMiniAig( Mini_Aig_t * p )
{
    Gia_Man_t * pGia, * pTemp;
    Vec_Int_t * vCopies;
    int i, iGiaLit, nNodes;
    // get the number of nodes
    nNodes = Mini_AigNodeNum(p);
    // create ABC network
    pGia = Gia_ManStart( nNodes );
    pGia->pName = Abc_UtilStrsav( "MiniAig" );
    // create mapping from MiniAIG objects into ABC objects
    vCopies = Vec_IntAlloc( nNodes );
    Vec_IntPush( vCopies, 0 );
    // iterate through the objects
    Gia_ManHashAlloc( pGia );
    for ( i = 1; i < nNodes; i++ )
    {
        if ( Mini_AigNodeIsPi( p, i ) )
            iGiaLit = Gia_ManAppendCi(pGia);
        else if ( Mini_AigNodeIsPo( p, i ) )
            iGiaLit = Gia_ManAppendCo(pGia, Gia_ObjFromMiniFanin0Copy(pGia, vCopies, p, i));
        else if ( Mini_AigNodeIsAnd( p, i ) )
            iGiaLit = Gia_ManHashAnd(pGia, Gia_ObjFromMiniFanin0Copy(pGia, vCopies, p, i), Gia_ObjFromMiniFanin1Copy(pGia, vCopies, p, i));
        else assert( 0 );
        Vec_IntPush( vCopies, iGiaLit );
    }
    Gia_ManHashStop( pGia );
    assert( Vec_IntSize(vCopies) == nNodes );
    Vec_IntFree( vCopies );
    Gia_ManSetRegNum( pGia, Mini_AigRegNum(p) );
    pGia = Gia_ManCleanup( pTemp = pGia );
    Gia_ManStop( pTemp );
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Converts GIA into MiniAIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mini_Aig_t * Gia_ManToMiniAig( Gia_Man_t * pGia )
{
    Mini_Aig_t * p;
    Gia_Obj_t * pObj;
    int i;
    // create the manager
    p = Mini_AigStart();
    Gia_ManConst0(pGia)->Value = Mini_AigLitConst0();
    // create primary inputs
    Gia_ManForEachCi( pGia, pObj, i )
        pObj->Value = Mini_AigCreatePi(p);
    // create internal nodes
    Gia_ManForEachAnd( pGia, pObj, i )
        pObj->Value = Mini_AigAnd( p, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    // create primary outputs
    Gia_ManForEachCo( pGia, pObj, i )
        pObj->Value = Mini_AigCreatePo( p, Gia_ObjFanin0Copy(pObj) );
    // set registers
    Mini_AigSetRegNum( p, Gia_ManRegNum(pGia) );
    return p;
}

/**Function*************************************************************

  Synopsis    [Procedures to input/output MiniAIG into/from internal GIA.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameGiaInputMiniAig( Abc_Frame_t * pAbc, void * p )
{
    Gia_Man_t * pGia;
    if ( pAbc == NULL )
        printf( "ABC framework is not initialized by calling Abc_Start()\n" );
    pGia = Gia_ManFromMiniAig( (Mini_Aig_t *)p );
    Abc_FrameUpdateGia( pAbc, pGia );
//    Gia_ManDelete( pGia );
}
void * Abc_FrameGiaOutputMiniAig( Abc_Frame_t * pAbc )
{
    Gia_Man_t * pGia;
    if ( pAbc == NULL )
        printf( "ABC framework is not initialized by calling Abc_Start()\n" );
    pGia = Abc_FrameReadGia( pAbc );
    if ( pGia == NULL )
        printf( "Current network in ABC framework is not defined.\n" );
    return Gia_ManToMiniAig( pGia );
}

/**Function*************************************************************

  Synopsis    [Procedures to read/write GIA to/from MiniAIG file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManReadMiniAig( char * pFileName )
{
    Mini_Aig_t * p = Mini_AigLoad( pFileName );
    Gia_Man_t * pGia = Gia_ManFromMiniAig( p );
    ABC_FREE( pGia->pName );
    pGia->pName = Extra_FileNameGeneric( pFileName ); 
    Mini_AigStop( p );
    return pGia;
}
void Gia_ManWriteMiniAig( Gia_Man_t * pGia, char * pFileName )
{
    Mini_Aig_t * p = Gia_ManToMiniAig( pGia );
    Mini_AigDump( p, pFileName );
    Mini_AigStop( p );
}




/**Function*************************************************************

  Synopsis    [Converts MiniLUT into GIA.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManFromMiniLut( Mini_Lut_t * p )
{
    Gia_Man_t * pGia, * pTemp;
    Vec_Int_t * vCopies;
    Vec_Int_t * vCover = Vec_IntAlloc( 1000 );
    Vec_Int_t * vLits = Vec_IntAlloc( 100 );
    int i, k, Fan, iGiaLit, nNodes;
    int LutSize = Abc_MaxInt( 2, Mini_LutSize(p) );
    assert( LutSize <= 6 );
    // get the number of nodes
    nNodes = Mini_LutNodeNum(p);
    // create ABC network
    pGia = Gia_ManStart( 3 * nNodes );
    pGia->pName = Abc_UtilStrsav( "MiniLut" );
    // create mapping from MiniLUT objects into ABC objects
    vCopies = Vec_IntAlloc( nNodes );
    Vec_IntPush( vCopies, 0 );
    Vec_IntPush( vCopies, 1 );
    // iterate through the objects
    Gia_ManHashAlloc( pGia );
    for ( i = 2; i < nNodes; i++ )
    {
        if ( Mini_LutNodeIsPi( p, i ) )
            iGiaLit = Gia_ManAppendCi(pGia);
        else if ( Mini_LutNodeIsPo( p, i ) )
            iGiaLit = Gia_ManAppendCo(pGia, Vec_IntEntry(vCopies, Mini_LutNodeFanin(p, i, 0)));
        else if ( Mini_LutNodeIsNode( p, i ) )
        {
            unsigned * puTruth = Mini_LutNodeTruth( p, i );
            word Truth = LutSize == 6 ? *(word *)puTruth : ((word)*puTruth << 32) | (word)*puTruth; 
            Vec_IntClear( vLits );
            Mini_LutForEachFanin( p, i, Fan, k )
                Vec_IntPush( vLits, Vec_IntEntry(vCopies, Fan) );
            iGiaLit = Dsm_ManTruthToGia( pGia, &Truth, vLits, vCover );
        }
        else assert( 0 );
        Vec_IntPush( vCopies, iGiaLit );
    }
    Vec_IntFree( vCover );
    Vec_IntFree( vLits );
    Gia_ManHashStop( pGia );
    assert( Vec_IntSize(vCopies) == nNodes );
    Vec_IntFree( vCopies );
    Gia_ManSetRegNum( pGia, Mini_LutRegNum(p) );
    pGia = Gia_ManCleanup( pTemp = pGia );
    Gia_ManStop( pTemp );
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Marks LUTs that should be complemented.]

  Description [These are LUTs whose all PO fanouts require them
  in negative polarity.  Other fanouts may require them in 
  positive polarity.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Bit_t * Gia_ManFindComplLuts( Gia_Man_t * pGia )
{
    Gia_Obj_t * pObj;  int i;
    // mark objects pointed by COs in negative polarity
    Vec_Bit_t * vMarks = Vec_BitStart( Gia_ManObjNum(pGia) );
    Gia_ManForEachCo( pGia, pObj, i )
        if ( Gia_ObjIsAnd(Gia_ObjFanin0(pObj)) && Gia_ObjFaninC0(pObj) )
            Vec_BitWriteEntry( vMarks, Gia_ObjFaninId0p(pGia, pObj), 1 );
    // unmark objects pointed by COs in positive polarity
    Gia_ManForEachCo( pGia, pObj, i )
        if ( Gia_ObjIsAnd(Gia_ObjFanin0(pObj)) && !Gia_ObjFaninC0(pObj) )
            Vec_BitWriteEntry( vMarks, Gia_ObjFaninId0p(pGia, pObj), 0 );
    return vMarks;
}

/**Function*************************************************************

  Synopsis    [Converts GIA into MiniLUT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mini_Lut_t * Gia_ManToMiniLut( Gia_Man_t * pGia )
{
    Mini_Lut_t * p;
    Vec_Wrd_t * vTruths;
    Vec_Bit_t * vMarks;
    Gia_Obj_t * pObj, * pFanin;
    int i, k, iFanin, LutSize, pVars[16];
    word Truth;
    assert( Gia_ManHasMapping(pGia) );
    LutSize = Gia_ManLutSizeMax( pGia );
    LutSize = Abc_MaxInt( LutSize, 2 );
    assert( LutSize >= 2 );
    // create the manager
    p = Mini_LutStart( LutSize );
    // create primary inputs
    Gia_ManFillValue( pGia );
    Gia_ManForEachCi( pGia, pObj, i )
        pObj->Value = Mini_LutCreatePi(p);
    // create internal nodes
    vTruths = Vec_WrdStart( Gia_ManObjNum(pGia) );
    vMarks = Gia_ManFindComplLuts( pGia );
    Gia_ManForEachLut( pGia, i )
    {
        pObj = Gia_ManObj( pGia, i );
        Gia_LutForEachFaninObj( pGia, i, pFanin, k )
            pVars[k] = pFanin->Value;
        Truth = Gia_LutComputeTruth6( pGia, i, vTruths );
        Truth = Vec_BitEntry(vMarks, i) ? ~Truth : Truth;
        Gia_LutForEachFanin( pGia, i, iFanin, k )
            if ( Vec_BitEntry(vMarks, iFanin) )
                Truth = Abc_Tt6Flip( Truth, k );
        pObj->Value = Mini_LutCreateNode( p, Gia_ObjLutSize(pGia, i), pVars, (unsigned *)&Truth );
    }
    Vec_WrdFree( vTruths );
    // create primary outputs
    Gia_ManForEachCo( pGia, pObj, i )
    {
        if ( Gia_ObjFanin0(pObj) == Gia_ManConst0(pGia) )
            pObj->Value = Mini_LutCreatePo( p, Gia_ObjFaninC0(pObj) );
        else if ( Gia_ObjFaninC0(pObj) == Vec_BitEntry(vMarks, Gia_ObjFaninId0p(pGia, pObj)) )
            pObj->Value = Mini_LutCreatePo( p, Gia_ObjFanin0(pObj)->Value );
        else // add inverter LUT
        {
            word TruthInv = ABC_CONST(0x5555555555555555);
            int Fanin = Gia_ObjFanin0(pObj)->Value;
            int LutInv = Mini_LutCreateNode( p, 1, &Fanin, (unsigned *)&TruthInv );
            pObj->Value = Mini_LutCreatePo( p, LutInv );
        }
    }
    Vec_BitFree( vMarks );
    // set registers
    Mini_LutSetRegNum( p, Gia_ManRegNum(pGia) );
    //Mini_LutPrintStats( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Procedures to input/output MiniAIG into/from internal GIA.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameGiaInputMiniLut( Abc_Frame_t * pAbc, void * p )
{
    Gia_Man_t * pGia;
    if ( pAbc == NULL )
        printf( "ABC framework is not initialized by calling Abc_Start()\n" );
    pGia = Gia_ManFromMiniLut( (Mini_Lut_t *)p );
    Abc_FrameUpdateGia( pAbc, pGia );
//    Gia_ManDelete( pGia );
}
void * Abc_FrameGiaOutputMiniLut( Abc_Frame_t * pAbc )
{
    Gia_Man_t * pGia;
    if ( pAbc == NULL )
        printf( "ABC framework is not initialized by calling Abc_Start()\n" );
    pGia = Abc_FrameReadGia( pAbc );
    if ( pGia == NULL )
        printf( "Current network in ABC framework is not defined.\n" );
    return Gia_ManToMiniLut( pGia );
}

/**Function*************************************************************

  Synopsis    [Procedures to read/write GIA to/from MiniAIG file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManReadMiniLut( char * pFileName )
{
    Mini_Lut_t * p = Mini_LutLoad( pFileName );
    Gia_Man_t * pGia = Gia_ManFromMiniLut( p );
    ABC_FREE( pGia->pName );
    pGia->pName = Extra_FileNameGeneric( pFileName ); 
    Mini_LutStop( p );
    return pGia;
}
void Gia_ManWriteMiniLut( Gia_Man_t * pGia, char * pFileName )
{
    Mini_Lut_t * p = Gia_ManToMiniLut( pGia );
    Mini_LutDump( p, pFileName );
    Mini_LutStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

