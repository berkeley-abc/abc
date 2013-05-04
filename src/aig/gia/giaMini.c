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
#include "base/main/main.h"
#include "aig/miniaig/miniaig.h"

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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

