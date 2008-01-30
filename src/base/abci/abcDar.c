/**CFile****************************************************************

  FileName    [abcDar.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [DAG-aware rewriting.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDar.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "aig.h"
#include "dar.h"
#include "cnf.h"
//#include "fra.h"
//#include "fraig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define Vec_PtrForEachEntryStop( vVec, pEntry, i, Stop )                                     \
    for ( i = 0; (i < Stop) && (((pEntry) = Vec_PtrEntry(vVec, i)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description [Assumes that registers are ordered after PIs/POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fRegisters )
{
    Aig_Man_t * pMan;
    Aig_Obj_t * pObjNew;
    Abc_Obj_t * pObj;
    int i, nNodes, nDontCares;
    // make sure the latches follow PIs/POs
    if ( fRegisters ) 
    { 
        // print warning about initial values
        nDontCares = 0;
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInitDc(pObj) )
            {
                Abc_LatchSetInit0(pObj);
                nDontCares++;
            }
        if ( nDontCares )
        {
            printf( "Warning: %d registers in this network have don't-care init values.\n", nDontCares );
            printf( "The don't-care are assumed to be 0. The result may not verify.\n" );
            printf( "Use command \"print_latch\" to see the init values of registers.\n" );
            printf( "Use command \"init\" to change the values.\n" );
        }
    }
    // create the manager
    pMan = Aig_ManStart( Abc_NtkNodeNum(pNtk) + 100 );
    pMan->pName = util_strsav( pNtk->pName );
    // save the number of registers
    if ( fRegisters )
    {
        pMan->nRegs = Abc_NtkLatchNum(pNtk);
//        pMan->vFlopNums = Vec_IntStartNatural( pMan->nRegs );
        pMan->vFlopNums = NULL;
    }
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk->pManFunc)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Aig_ObjCreatePi(pMan);
    // complement the 1-values registers
    if ( fRegisters )
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInit1(pObj) )
                Abc_ObjFanout0(pObj)->pCopy = Abc_ObjNot(Abc_ObjFanout0(pObj)->pCopy);
    // perform the conversion of the internal nodes (assumes DFS ordering)
//    pMan->fAddStrash = 1;
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 )
            continue;
        pObj->pCopy = (Abc_Obj_t *)Aig_And( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj), (Aig_Obj_t *)Abc_ObjChild1Copy(pObj) );
//        printf( "%d->%d ", pObj->Id, ((Aig_Obj_t *)pObj->pCopy)->Id );
    }
    pMan->fAddStrash = 0;
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Aig_ObjCreatePo( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj) );
    // complement the 1-valued registers
    if ( fRegisters )
        Aig_ManForEachLiSeq( pMan, pObjNew, i )
//            if ( Abc_LatchIsInit1(Abc_ObjFanout0(Abc_NtkCo(pNtk,i))) )
            if ( Abc_LatchIsInit1(Abc_NtkCo(pNtk,i)) )
                pObjNew->pFanin0 = Aig_Not(pObjNew->pFanin0);
    // remove dangling nodes
    if ( nNodes = Aig_ManCleanup( pMan ) )
        printf( "Abc_NtkToDar(): Unexpected %d dangling nodes when converting to AIG!\n", nNodes );
//Aig_ManDumpVerilog( pMan, "test.v" );
    if ( !Aig_ManCheck( pMan ) )
    {
        printf( "Abc_NtkToDar: AIG check has failed.\n" );
        Aig_ManStop( pMan );
        return NULL;
    }
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromDar( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
//    Abc_Obj_t * pObjNew;
    Aig_Obj_t * pObj;
    int i;
//    assert( Aig_ManRegNum(pMan) == Abc_NtkLatchNum(pNtkOld) );
    // perform strashing
    pNtkNew = Abc_NtkStartFrom( pNtkOld, ABC_TYPE_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew->pManFunc);
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
    {
        if ( pMan->nAsserts && i == Aig_ManPoNum(pMan) - pMan->nAsserts )
            break;
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), (Abc_Obj_t *)Aig_ObjChild0Copy(pObj) );
    }
/*
    // if there are assertions, add them
    if ( pMan->nAsserts > 0 )
        Aig_ManForEachAssert( pMan, pObj, i )
        {
            pObjNew = Abc_NtkCreateAssert(pNtkNew);
            Abc_ObjAssignName( pObjNew, "assert_", Abc_ObjName(pObjNew) );
            Abc_ObjAddFanin( pObjNew, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj) );
        }
*/
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromDar(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Adds dummy names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkAddDummyLatchNames( Abc_Ntk_t * pNtk )
{
    char Buffer[100];
    Abc_Obj_t * pObj;
    int nDigits, i;
    nDigits = Extra_Base10Log( Abc_NtkLatchNum(pNtk) );
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        sprintf( Buffer, "L%0*d", nDigits, i );
        Abc_NtkLogicStoreName( pObj, Buffer );
    }
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description [This procedure should be called after seq sweeping, 
  which changes the number of registers.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromDarSeqSweep( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObjOld, * pObjNew;
    Aig_Obj_t * pObj, * pObjLo, * pObjLi;
    int i;
    // start the network
    pNtkNew = Abc_NtkAlloc( ABC_TYPE_STRASH, ABC_FUNC_AIG );
    // duplicate the name and the spec
    pNtkNew->pName = util_strsav(pNtkOld->pName);
    pNtkNew->pSpec = util_strsav(pNtkOld->pSpec);
    // create PIs/POs/latches
    Abc_NtkForEachPi( pNtkOld, pObjOld, i )
    {
        pObjNew = Abc_NtkDupObj( pNtkNew, pObjOld );
        Abc_NtkLogicStoreName( pObjNew, Abc_ObjName(pObjOld) );
    }
    Abc_NtkForEachPo( pNtkOld, pObjOld, i )
    {
        pObjNew = Abc_NtkDupObj( pNtkNew, pObjOld );
        Abc_NtkLogicStoreName( pObjNew, Abc_ObjName(pObjOld) );
    }
    Aig_ManForEachLiLoSeq( pMan, pObjLi, pObjLo, i )
    {
        pObjNew = Abc_NtkCreateLatch( pNtkNew );
        Vec_PtrPush( pNtkNew->vCis, pObjNew );
        Vec_PtrPush( pNtkNew->vCos, pObjNew );
        Abc_LatchSetInit0( pObjNew );
    }
    Abc_NtkAddDummyLatchNames( pNtkNew );
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew->pManFunc);
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);
    // rebuild the AIG
    vNodes = Aig_ManDfs( pMan );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( Aig_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
    {
        pObjNew = (Abc_Obj_t *)Aig_ObjChild0Copy(pObj);
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), pObjNew );
    }
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromDar(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromDarChoices( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Aig_Obj_t * pObj, * pTemp;
    int i;
    assert( pMan->pEquivs != NULL );
    assert( Aig_ManBufNum(pMan) == 0 );
    // perform strashing
    pNtkNew = Abc_NtkStartFrom( pNtkOld, ABC_TYPE_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew->pManFunc);
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);

    // rebuild the AIG
    vNodes = Aig_ManDfsChoices( pMan );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        pObj->pData = Abc_AigAnd( pNtkNew->pManFunc, (Abc_Obj_t *)Aig_ObjChild0Copy(pObj), (Abc_Obj_t *)Aig_ObjChild1Copy(pObj) );
        if ( pTemp = pMan->pEquivs[pObj->Id] )
        {
            Abc_Obj_t * pAbcRepr, * pAbcObj;
            assert( pTemp->pData != NULL );
            pAbcRepr = pObj->pData;
            pAbcObj  = pTemp->pData;
            pAbcObj->pData  = pAbcRepr->pData;
            pAbcRepr->pData = pAbcObj;
        }
    }
//printf( "Total = %d.  Collected = %d.\n", Aig_ManNodeNum(pMan), Vec_PtrSize(vNodes) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Aig_ManForEachPo( pMan, pObj, i )
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), (Abc_Obj_t *)Aig_ObjChild0Copy(pObj) );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromDar(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDar( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkAig = NULL;
    Aig_Man_t * pMan;
    extern void Fra_ManPartitionTest( Aig_Man_t * p, int nComLim );

    assert( Abc_NtkIsStrash(pNtk) );
    // convert to the AIG manager
    pMan = Abc_NtkToDar( pNtk, 0 );
    if ( pMan == NULL )
        return NULL;

    // perform computation
//    Fra_ManPartitionTest( pMan, 4 );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Aig_ManStop( pMan );

    // make sure everything is okay
    if ( pNtkAig && !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkDar: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarLatchSweep( Abc_Ntk_t * pNtk, int fLatchSweep, int fVerbose )
{
    Abc_Ntk_t * pNtkAig;
    Aig_Man_t * pMan;
    pMan = Abc_NtkToDar( pNtk, 1 );
    if ( pMan == NULL )
        return NULL;
    Aig_ManSeqCleanup( pMan );
    if ( fLatchSweep )
    {
        if ( pMan->nRegs )
            pMan = Aig_ManReduceLaches( pMan, fVerbose );
        if ( pMan->nRegs )
            pMan = Aig_ManConstReduce( pMan, fVerbose );
    }
    pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Computes latch correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Abc_Ntk_t * Abc_NtkDarLcorr( Abc_Ntk_t * pNtk, int nFramesP, int nConfMax, int fVerbose )
{
    extern Aig_Man_t * Fra_FraigLatchCorrespondence( Aig_Man_t * pAig, int nFramesP, int nConfMax, int fProve, int fVerbose, int * pnIter );
    Aig_Man_t * pMan, * pTemp;
    Abc_Ntk_t * pNtkAig;
    pMan = Abc_NtkToDar( pNtk, 1 );
    if ( pMan == NULL )
        return NULL;
    pMan = Fra_FraigLatchCorrespondence( pTemp = pMan, nFramesP, nConfMax, 0, fVerbose, NULL );
    Aig_ManStop( pTemp );
    if ( Aig_ManRegNum(pMan) < Abc_NtkLatchNum(pNtk) )
        pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    else
    {
        Abc_Obj_t * pObj;
        int i;
        pNtkAig = Abc_NtkFromDar( pNtk, pMan );
        Abc_NtkForEachLatch( pNtkAig, pObj, i )
            Abc_LatchSetInit0( pObj );
    }
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarSeqSweep( Abc_Ntk_t * pNtk, int nFramesP, int nFramesK, int nMaxImps, int nMaxLevs, int fRewrite, int fUseImps, int fLatchCorr, int fWriteImps, int fVerbose )
{
    extern Aig_Man_t * Fra_FraigInduction( Aig_Man_t * pManAig, int nFramesP, int nFramesK, int nMaxImps, int nMaxLevs, int fRewrite, int fUseImps, int fLatchCorr, int fWriteImps, int fVerbose, int * pnIter );
//    Fraig_Params_t Params;
    Abc_Ntk_t * pNtkAig, * pNtkFraig;
    Aig_Man_t * pMan, * pTemp;
    int clk = clock();

    // preprocess the miter by fraiging it
    // (note that for each functional class, fraiging leaves one representative;
    // so fraiging does not reduce the number of functions represented by nodes
//    Fraig_ParamsSetDefault( &Params );
//    Params.nBTLimit = 100000;
//    pNtkFraig = Abc_NtkFraig( pNtk, &Params, 0, 0 );
    pNtkFraig = Abc_NtkDup( pNtk );
if ( fVerbose ) 
{
PRT( "Initial fraiging time", clock() - clk );
}

    pMan = Abc_NtkToDar( pNtkFraig, 1 );
    Abc_NtkDelete( pNtkFraig );
    if ( pMan == NULL )
        return NULL;

    pMan = Fra_FraigInduction( pTemp = pMan, nFramesP, nFramesK, nMaxImps, nMaxLevs, fRewrite, fUseImps, fLatchCorr, fWriteImps, fVerbose, NULL );
    Aig_ManStop( pTemp );

    if ( Aig_ManRegNum(pMan) < Abc_NtkLatchNum(pNtk) )
        pNtkAig = Abc_NtkFromDarSeqSweep( pNtk, pMan );
    else
    {
        Abc_Obj_t * pObj;
        int i;
        pNtkAig = Abc_NtkFromDar( pNtk, pMan );
        Abc_NtkForEachLatch( pNtkAig, pObj, i )
            Abc_LatchSetInit0( pObj );
    }
    Aig_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDarSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames, int fRetimeFirst, int fVerbose, int fVeryVerbose )
{
    extern int Fra_FraigSec( Aig_Man_t * p, int nFramesMax, int fRetimeFirst, int fVerbose, int fVeryVerbose );
//    Fraig_Params_t Params;
    Aig_Man_t * pMan;
    Abc_Ntk_t * pMiter;//, * pTemp;
    int RetValue;
 
    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 0 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return 0;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        extern void Abc_NtkVerifyReportErrorSeq( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int * pModel, int nFrames );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
/*
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, nFrames );
        Abc_NtkVerifyReportErrorSeq( pNtk1, pNtk2, pMiter->pModel, nFrames );
        FREE( pMiter->pModel );
*/
        Abc_NtkDelete( pMiter );
        return 0;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return 1;
    }

    // commented out because something became non-inductive
/*
    // preprocess the miter by fraiging it
    // (note that for each functional class, fraiging leaves one representative;
    // so fraiging does not reduce the number of functions represented by nodes
    Fraig_ParamsSetDefault( &Params );
    Params.nBTLimit = 100000;
    pMiter = Abc_NtkFraig( pTemp = pMiter, &Params, 0, 0 );
    Abc_NtkDelete( pTemp );
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        extern void Abc_NtkVerifyReportErrorSeq( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int * pModel, int nFrames );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, nFrames );
        Abc_NtkVerifyReportErrorSeq( pNtk1, pNtk2, pMiter->pModel, nFrames );
        FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        return 0;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return 1;
    }
*/
    // derive the AIG manager
    pMan = Abc_NtkToDar( pMiter, 1 );
    Abc_NtkDelete( pMiter );
    if ( pMan == NULL )
    {
        printf( "Converting miter into AIG has failed.\n" );
        return -1;
    }
    assert( pMan->nRegs > 0 );

    // perform verification
    RetValue = Fra_FraigSec( pMan, nFrames, fRetimeFirst, fVerbose, fVeryVerbose );
    Aig_ManStop( pMan );
    return RetValue;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


