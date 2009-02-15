/**CFile****************************************************************

  FileName    [abcLatch.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures working with latches.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcLatch.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks if latches form self-loop.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkLatchIsSelfFeed_rec( Abc_Obj_t * pLatch, Abc_Obj_t * pLatchRoot )
{
    Abc_Obj_t * pFanin;
    assert( Abc_ObjIsLatch(pLatch) );
    if ( pLatch == pLatchRoot )
        return 1;
    pFanin = Abc_ObjFanin0(Abc_ObjFanin0(pLatch));
    if ( !Abc_ObjIsBo(pFanin) || !Abc_ObjIsLatch(Abc_ObjFanin0(pFanin)) )
        return 0;
    return Abc_NtkLatchIsSelfFeed_rec( Abc_ObjFanin0(pFanin), pLatch );
}

/**Function*************************************************************

  Synopsis    [Checks if latches form self-loop.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkLatchIsSelfFeed( Abc_Obj_t * pLatch )
{
    Abc_Obj_t * pFanin;
    assert( Abc_ObjIsLatch(pLatch) );
    pFanin = Abc_ObjFanin0(Abc_ObjFanin0(pLatch));
    if ( !Abc_ObjIsBo(pFanin) || !Abc_ObjIsLatch(Abc_ObjFanin0(pFanin)) )
        return 0;
    return Abc_NtkLatchIsSelfFeed_rec( Abc_ObjFanin0(pFanin), pLatch );
}

/**Function*************************************************************

  Synopsis    [Checks if latches form self-loop.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCountSelfFeedLatches( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pLatch;
    int i, Counter;
    Counter = 0;
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
//        if ( Abc_NtkLatchIsSelfFeed(pLatch) && Abc_ObjFanoutNum(pLatch) > 1 )
//            printf( "Fanouts = %d.\n", Abc_ObjFanoutNum(pLatch) );
        Counter += Abc_NtkLatchIsSelfFeed( pLatch );
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Replaces self-feeding latches by latches with constant inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRemoveSelfFeedLatches( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pLatch, * pConst1;
    int i, Counter;
    Counter = 0;
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        if ( Abc_NtkLatchIsSelfFeed( pLatch ) )
        {
            if ( Abc_NtkIsStrash(pNtk) )
                pConst1 = Abc_AigConst1(pNtk);
            else
                pConst1 = Abc_NtkCreateNodeConst1(pNtk);
            Abc_ObjPatchFanin( Abc_ObjFanin0(pLatch), Abc_ObjFanin0(Abc_ObjFanin0(pLatch)), pConst1 );
            Counter++;
        }
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Pipelines the network with latches.]

  Description []
               
  SideEffects [Does not check the names of the added latches!!!]

  SeeAlso     []

***********************************************************************/
void Abc_NtkLatchPipe( Abc_Ntk_t * pNtk, int nLatches )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pLatch, * pFanin, * pFanout;
    int i, k, nTotal, nDigits;
    if ( nLatches < 1 )
        return;
    nTotal = nLatches * Abc_NtkPiNum(pNtk);
    nDigits = Extra_Base10Log( nTotal );
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        // remember current fanins of the PI
        Abc_NodeCollectFanouts( pObj, vNodes );
        // create the latches
        for ( pFanin = pObj, k = 0; k < nLatches; k++, pFanin = pLatch )
        {
            pLatch = Abc_NtkCreateLatch( pNtk );
            Abc_ObjAddFanin( pLatch, pFanin );
            Abc_LatchSetInitDc( pLatch );
            // create the name of the new latch
            Abc_ObjAssignName( pLatch, Abc_ObjNameDummy("LL", i*nLatches + k, nDigits), NULL );
        }
        // patch the PI fanouts
        Vec_PtrForEachEntry( vNodes, pFanout, k )
            Abc_ObjPatchFanin( pFanout, pObj, pFanin );
    }
    Vec_PtrFree( vNodes );
    Abc_NtkLogicMakeSimpleCos( pNtk, 0 );
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkCollectLatchValues( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vValues;
    Abc_Obj_t * pLatch;
    int i;
    vValues = Vec_IntAlloc( Abc_NtkLatchNum(pNtk) );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        Vec_IntPush( vValues, Abc_LatchIsInit1(pLatch) );
    return vValues;
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkInsertLatchValues( Abc_Ntk_t * pNtk, Vec_Int_t * vValues )
{
    Abc_Obj_t * pLatch;
    int i;
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        pLatch->pData = (void *)(ABC_PTRINT_T)(vValues? (Vec_IntEntry(vValues,i)? ABC_INIT_ONE : ABC_INIT_ZERO) : ABC_INIT_DC);
}

/**Function*************************************************************

  Synopsis    [Creates latch with the given initial value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkAddLatch( Abc_Ntk_t * pNtk, Abc_Obj_t * pDriver, Abc_InitType_t Init )
{
    Abc_Obj_t * pLatchOut, * pLatch, * pLatchIn;
    pLatchOut = Abc_NtkCreateBo(pNtk);
    pLatch    = Abc_NtkCreateLatch(pNtk);
    pLatchIn  = Abc_NtkCreateBi(pNtk);
    Abc_ObjAssignName( pLatchOut, Abc_ObjName(pLatch), "_lo" );
    Abc_ObjAssignName( pLatchIn,  Abc_ObjName(pLatch), "_li" );
    Abc_ObjAddFanin( pLatchOut, pLatch );
    Abc_ObjAddFanin( pLatch, pLatchIn );
    Abc_ObjAddFanin( pLatchIn, pDriver );
    pLatch->pData = (void *)Init;
    return pLatchOut;
}

/**Function*************************************************************

  Synopsis    [Creates MUX.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkNodeConvertToMux( Abc_Ntk_t * pNtk, Abc_Obj_t * pNodeC, Abc_Obj_t * pNode1, Abc_Obj_t * pNode0, Abc_Obj_t * pMux )
{
    assert( Abc_NtkIsLogic(pNtk) );
    Abc_ObjAddFanin( pMux, pNodeC );
    Abc_ObjAddFanin( pMux, pNode1 );
    Abc_ObjAddFanin( pMux, pNode0 );
    if ( Abc_NtkHasSop(pNtk) )
        pMux->pData = Abc_SopRegister( pNtk->pManFunc, "11- 1\n0-1 1\n" );
    else if ( Abc_NtkHasBdd(pNtk) )
        pMux->pData = Cudd_bddIte(pNtk->pManFunc,Cudd_bddIthVar(pNtk->pManFunc,0),Cudd_bddIthVar(pNtk->pManFunc,1),Cudd_bddIthVar(pNtk->pManFunc,2)), Cudd_Ref( pMux->pData );
    else if ( Abc_NtkHasAig(pNtk) )
        pMux->pData = Hop_Mux(pNtk->pManFunc,Hop_IthVar(pNtk->pManFunc,0),Hop_IthVar(pNtk->pManFunc,1),Hop_IthVar(pNtk->pManFunc,2));
    else
        assert( 0 );
}

/**Function*************************************************************

  Synopsis    [Converts registers with DC values into additional PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkConvertDcLatches( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pCtrl, * pLatch, * pMux, * pPi;
    Abc_InitType_t Init = ABC_INIT_ZERO;
    int i, fFound = 0, Counter;
    // check if there are latches with DC values
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        if ( Abc_LatchIsInitDc(pLatch) )
        {
            fFound = 1;
            break;
        }
    if ( !fFound )
        return;
    // add control latch
    pCtrl = Abc_NtkAddLatch( pNtk, Abc_NtkCreateNodeConst1(pNtk), Init );
    // add fanouts for each latch with DC values
    Counter = 0;
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        if ( !Abc_LatchIsInitDc(pLatch) )
            continue;
        // change latch value
        pLatch->pData = (void *)Init;
        // if the latch output has the same name as a PO, rename it
        if ( Abc_NodeFindCoFanout( Abc_ObjFanout0(pLatch) ) )
        {
            Nm_ManDeleteIdName( pLatch->pNtk->pManName, Abc_ObjFanout0(pLatch)->Id );
            Abc_ObjAssignName( Abc_ObjFanout0(pLatch), Abc_ObjName(pLatch), "_lo" );
        }
        // create new PIs
        pPi = Abc_NtkCreatePi( pNtk );
        Abc_ObjAssignName( pPi, Abc_ObjName(pLatch), "_pi" );
        // create a new node and transfer fanout from latch output to the new node
        pMux = Abc_NtkCreateNode( pNtk );
        Abc_ObjTransferFanout( Abc_ObjFanout0(pLatch), pMux );
        // convert the node into a mux
        Abc_NtkNodeConvertToMux( pNtk, pCtrl, Abc_ObjFanout0(pLatch), pPi, pMux );
        Counter++;
    }
    printf( "The number of converted latches with DC values = %d.\n", Counter );
}

/**Function*************************************************************

  Synopsis    [Transfors the array of latch names into that of latch numbers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkConverLatchNamesIntoNumbers( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vResult, * vNames;
    Vec_Int_t * vNumbers;
    Abc_Obj_t * pObj;
    char * pName;
    int i, k, Num;
    if ( pNtk->vOnehots == NULL )
        return NULL;
    // set register numbers
    Abc_NtkForEachLatch( pNtk, pObj, i )
        pObj->pNext = (Abc_Obj_t *)(ABC_PTRINT_T)i;
    // add the numbers
    vResult = Vec_PtrAlloc( Vec_PtrSize(pNtk->vOnehots) );
    Vec_PtrForEachEntry( pNtk->vOnehots, vNames, i )
    {
        vNumbers = Vec_IntAlloc( Vec_PtrSize(vNames) );
        Vec_PtrForEachEntry( vNames, pName, k )
        {
            Num = Nm_ManFindIdByName( pNtk->pManName, pName, ABC_OBJ_BO );
            if ( Num < 0 )
                continue;
            pObj = Abc_NtkObj( pNtk, Num );
            if ( Abc_ObjFaninNum(pObj) != 1 || !Abc_ObjIsLatch(Abc_ObjFanin0(pObj)) )
                continue;
            Vec_IntPush( vNumbers, (int)(ABC_PTRINT_T)pObj->pNext );
        }
        if ( Vec_IntSize( vNumbers ) > 1 )
        {
            Vec_PtrPush( vResult, vNumbers );
printf( "Converted %d one-hot registers.\n", Vec_IntSize(vNumbers) );
        }
        else
            Vec_IntFree( vNumbers );
    }
    // clean the numbers
    Abc_NtkForEachLatch( pNtk, pObj, i )
        pObj->pNext = NULL;
    return vResult;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


