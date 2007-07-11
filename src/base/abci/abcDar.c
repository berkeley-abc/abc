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
#include "dar.h"
#include "cnf.h"
#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk )
{
    Dar_Man_t * pMan;
    Abc_Obj_t * pObj;
    int i;
    // create the manager
    pMan = Dar_ManStart( Abc_NtkNodeNum(pNtk) + 100 );
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Dar_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Dar_ObjCreatePi(pMan);
    // perform the conversion of the internal nodes (assumes DFS ordering)
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        pObj->pCopy = (Abc_Obj_t *)Dar_And( pMan, (Dar_Obj_t *)Abc_ObjChild0Copy(pObj), (Dar_Obj_t *)Abc_ObjChild1Copy(pObj) );
//        printf( "%d->%d ", pObj->Id, ((Dar_Obj_t *)pObj->pCopy)->Id );
    }
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Dar_ObjCreatePo( pMan, (Dar_Obj_t *)Abc_ObjChild0Copy(pObj) );
    Dar_ManCleanup( pMan );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromDar( Abc_Ntk_t * pNtkOld, Dar_Man_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Dar_Obj_t * pObj;
    int i;
    // perform strashing
    pNtkNew = Abc_NtkStartFrom( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Dar_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    Dar_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkCi(pNtkNew, i);
    // rebuild the AIG
    vNodes = Dar_ManDfs( pMan );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( Dar_ObjIsBuf(pObj) )
            pObj->pData = (Abc_Obj_t *)Dar_ObjChild0Copy(pObj);
        else
            pObj->pData = Abc_AigAnd( pNtkNew->pManFunc, (Abc_Obj_t *)Dar_ObjChild0Copy(pObj), (Abc_Obj_t *)Dar_ObjChild1Copy(pObj) );
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Dar_ManForEachPo( pMan, pObj, i )
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), (Abc_Obj_t *)Dar_ObjChild0Copy(pObj) );
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
Abc_Ntk_t * Abc_NtkFromDarSeq( Abc_Ntk_t * pNtkOld, Dar_Man_t * pMan )
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew, * pFaninNew, * pFaninNew0, * pFaninNew1;
    Dar_Obj_t * pObj;
    int i;
//    assert( Dar_ManLatchNum(pMan) > 0 );
    // perform strashing
    pNtkNew = Abc_NtkStartFromNoLatches( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Dar_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    Dar_ManForEachPi( pMan, pObj, i )
        pObj->pData = Abc_NtkPi(pNtkNew, i);
    // create latches of the new network
    Dar_ManForEachObj( pMan, pObj, i )
    {
        if ( !Dar_ObjIsLatch(pObj) )
            continue;
        pObjNew = Abc_NtkCreateLatch( pNtkNew );
        pFaninNew0 = Abc_NtkCreateBi( pNtkNew );
        pFaninNew1 = Abc_NtkCreateBo( pNtkNew );
        Abc_ObjAddFanin( pObjNew, pFaninNew0 );
        Abc_ObjAddFanin( pFaninNew1, pObjNew );
        Abc_LatchSetInit0( pObjNew );
        pObj->pData = Abc_ObjFanout0( pObjNew );
    }
    Abc_NtkAddDummyBoxNames( pNtkNew );
    // rebuild the AIG
    vNodes = Dar_ManDfs( pMan );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        // add the first fanin
        pObj->pData = pFaninNew0 = (Abc_Obj_t *)Dar_ObjChild0Copy(pObj);
        if ( Dar_ObjIsBuf(pObj) )
            continue;
        // add the second fanin
        pFaninNew1 = (Abc_Obj_t *)Dar_ObjChild1Copy(pObj);
        // create the new node
        if ( Dar_ObjIsExor(pObj) )
            pObj->pData = pObjNew = Abc_AigXor( pNtkNew->pManFunc, pFaninNew0, pFaninNew1 );
        else
            pObj->pData = pObjNew = Abc_AigAnd( pNtkNew->pManFunc, pFaninNew0, pFaninNew1 );
    }
    Vec_PtrFree( vNodes );
    // connect the PO nodes
    Dar_ManForEachPo( pMan, pObj, i )
    {
        pFaninNew = (Abc_Obj_t *)Dar_ObjChild0Copy( pObj );
        Abc_ObjAddFanin( Abc_NtkPo(pNtkNew, i), pFaninNew );
    }
    // connect the latches
    Dar_ManForEachObj( pMan, pObj, i )
    {
        if ( !Dar_ObjIsLatch(pObj) )
            continue;
        pFaninNew = (Abc_Obj_t *)Dar_ObjChild0Copy( pObj );
        Abc_ObjAddFanin( Abc_ObjFanin0(Abc_ObjFanin0(pObj->pData)), pFaninNew );
    }
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkFromIvySeq(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Collect latch values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Abc_NtkGetLatchValues( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pLatch;
    int i, * pArray;
    pArray = ALLOC( int, Abc_NtkLatchNum(pNtk) );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        pArray[i] = Abc_LatchIsInit1(pLatch);
    return pArray;
}

/**Function*************************************************************

  Synopsis    [Performs verification after retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSecRetime( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 )
{
    int fRemove1, fRemove2;
    Dar_Man_t * pMan1, * pMan2;
    int * pArray;

    fRemove1 = (!Abc_NtkIsStrash(pNtk1)) && (pNtk1 = Abc_NtkStrash(pNtk1, 0, 0, 0));
    fRemove2 = (!Abc_NtkIsStrash(pNtk2)) && (pNtk2 = Abc_NtkStrash(pNtk2, 0, 0, 0));


    pMan1 = Abc_NtkToDar( pNtk1 );
    pMan2 = Abc_NtkToDar( pNtk2 );

    Dar_ManPrintStats( pMan1 );
    Dar_ManPrintStats( pMan2 );

    pArray = Abc_NtkGetLatchValues(pNtk1);
    Dar_ManSeqStrash( pMan1, Abc_NtkLatchNum(pNtk1), pArray );
    free( pArray );

    pArray = Abc_NtkGetLatchValues(pNtk2);
    Dar_ManSeqStrash( pMan2, Abc_NtkLatchNum(pNtk2), pArray );
    free( pArray );

    Dar_ManPrintStats( pMan1 );
    Dar_ManPrintStats( pMan2 );

    Dar_ManStop( pMan1 );
    Dar_ManStop( pMan2 );


    if ( fRemove1 )  Abc_NtkDelete( pNtk1 );
    if ( fRemove2 )  Abc_NtkDelete( pNtk2 );
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDar( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkAig;
    Dar_Man_t * pMan;//, * pTemp;
//    int * pArray;

    assert( Abc_NtkIsStrash(pNtk) );
    // convert to the AIG manager
    pMan = Abc_NtkToDar( pNtk );
    if ( pMan == NULL )
        return NULL;
    if ( !Dar_ManCheck( pMan ) )
    {
        printf( "Abc_NtkDar: AIG check has failed.\n" );
        Dar_ManStop( pMan );
        return NULL;
    }
    // perform balance
    Dar_ManPrintStats( pMan );
/*
    pArray = Abc_NtkGetLatchValues(pNtk);
    Dar_ManSeqStrash( pMan, Abc_NtkLatchNum(pNtk), pArray );
    free( pArray );
*/

//    Dar_ManDumpBlif( pMan, "aig_temp.blif" );
//    pMan->pPars = Dar_ManDefaultParams();
    Dar_ManRewrite( pMan );
    Dar_ManPrintStats( pMan );
    Dar_ManPrintRuntime( pMan );
//    Dar_ManComputeCuts( pMan );

/*
{
extern Dar_Cnf_t * Dar_ManDeriveCnf( Dar_Man_t * p );
extern void Dar_CnfFree( Dar_Cnf_t * pCnf );
Dar_Cnf_t * pCnf;
pCnf = Dar_ManDeriveCnf( pMan );
Dar_CnfFree( pCnf );
}
*/

    // convert from the AIG manager
    if ( Dar_ManLatchNum(pMan) )
        pNtkAig = Abc_NtkFromDarSeq( pNtk, pMan );
    else
        pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    if ( pNtkAig == NULL )
        return NULL;
    Dar_ManStop( pMan );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkAig ) )
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
Abc_Ntk_t * Abc_NtkConstructFromCnf( Abc_Ntk_t * pNtk, Cnf_Man_t * p, Vec_Ptr_t * vMapped )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pNodeNew;
    Dar_Obj_t * pObj, * pLeaf;
    Cnf_Cut_t * pCut;
    Vec_Int_t * vCover;
    unsigned uTruth;
    int i, k, nDupGates;
    // create the new network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    // make the mapper point to the new network
    Dar_ManConst1(p->pManAig)->pData = Abc_NtkCreateNodeConst1(pNtkNew);
    Abc_NtkForEachCi( pNtk, pNode, i )
        Dar_ManPi(p->pManAig, i)->pData = pNode->pCopy;
    // process the nodes in topological order
    vCover = Vec_IntAlloc( 1 << 16 );
    Vec_PtrForEachEntry( vMapped, pObj, i )
    {
        // create new node
        pNodeNew = Abc_NtkCreateNode( pNtkNew );
        // add fanins according to the cut
        pCut = pObj->pData;
        Cnf_CutForEachLeaf( p->pManAig, pCut, pLeaf, k )
            Abc_ObjAddFanin( pNodeNew, pLeaf->pData );
        // add logic function
        if ( pCut->nFanins < 5 )
        {
            uTruth = 0xFFFF & *Cnf_CutTruth(pCut);
            Cnf_SopConvertToVector( p->pSops[uTruth], p->pSopSizes[uTruth], vCover );
            pNodeNew->pData = Abc_SopCreateFromIsop( pNtkNew->pManFunc, pCut->nFanins, vCover );
        }
        else
            pNodeNew->pData = Abc_SopCreateFromIsop( pNtkNew->pManFunc, pCut->nFanins, pCut->vIsop[1] );
        // save the node
        pObj->pData = pNodeNew;
    }
    Vec_IntFree( vCover );
    // add the CO drivers
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        pObj = Dar_ManPo(p->pManAig, i);
        pNodeNew = Abc_ObjNotCond( Dar_ObjFanin0(pObj)->pData, Dar_ObjFaninC0(pObj) );
        Abc_ObjAddFanin( pNode->pCopy, pNodeNew );
    }

    // remove the constant node if not used
    pNodeNew = (Abc_Obj_t *)Dar_ManConst1(p->pManAig)->pData;
    if ( Abc_ObjFanoutNum(pNodeNew) == 0 )
        Abc_NtkDeleteObj( pNodeNew );
    // minimize the node
//    Abc_NtkSweep( pNtkNew, 0 );
    // decouple the PO driver nodes to reduce the number of levels
    nDupGates = Abc_NtkLogicMakeSimpleCos( pNtkNew, 1 );
//    if ( nDupGates && If_ManReadVerbose(pIfMan) )
//        printf( "Duplicated %d gates to decouple the CO drivers.\n", nDupGates );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkConstructFromCnf(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarToCnf( Abc_Ntk_t * pNtk, char * pFileName )
{
    Abc_Ntk_t * pNtkNew = NULL;
    Cnf_Man_t * pCnf;
    Dar_Man_t * pMan;
    Cnf_Dat_t * pData;
    assert( Abc_NtkIsStrash(pNtk) );
    // convert to the AIG manager
    pMan = Abc_NtkToDar( pNtk );
    if ( pMan == NULL )
        return NULL;
    if ( !Dar_ManCheck( pMan ) )
    {
        printf( "Abc_NtkDarToCnf: AIG check has failed.\n" );
        Dar_ManStop( pMan );
        return NULL;
    }
    // perform balance
    Dar_ManPrintStats( pMan );

    // derive CNF
    pCnf = Cnf_ManStart();
    pData = Cnf_Derive( pCnf, pMan );

    {
        Vec_Ptr_t * vMapped;
        vMapped = Cnf_ManScanMapping( pCnf, 1 );
        pNtkNew = Abc_NtkConstructFromCnf( pNtk, pCnf, vMapped );
        Vec_PtrFree( vMapped );
    }

    Dar_ManStop( pMan );
    Cnf_ManStop( pCnf );

    // write CNF into a file
//    Cnf_DataWriteIntoFile( pData, pFileName );
    Cnf_DataFree( pData );

    return pNtkNew;
}


/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDarFraig( Abc_Ntk_t * pNtk, int nConfLimit, int fDoSparse, int fProve, int fTransfer, int fSpeculate, int fVerbose )
{
    Fra_Par_t Params, * pParams = &Params; 
    Abc_Ntk_t * pNtkAig;
    Dar_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk );
    if ( pMan == NULL )
        return NULL;
    Fra_ParamsDefault( pParams );
    pParams->nBTLimitNode = nConfLimit;
    pParams->fVerbose     = fVerbose;
    pParams->fProve       = fProve;
    pParams->fDoSparse    = fDoSparse;
    pParams->fSpeculate   = fSpeculate;
    pMan = Fra_Perform( pTemp = pMan, pParams );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Dar_ManStop( pTemp );
    Dar_ManStop( pMan );
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCSweep( Abc_Ntk_t * pNtk, int nCutsMax, int nLeafMax, int fVerbose )
{
    extern Dar_Man_t * Csw_Sweep( Dar_Man_t * pAig, int nCutsMax, int nLeafMax, int fVerbose );
    Abc_Ntk_t * pNtkAig;
    Dar_Man_t * pMan, * pTemp;
    pMan = Abc_NtkToDar( pNtk );
    if ( pMan == NULL )
        return NULL;
    pMan = Csw_Sweep( pTemp = pMan, nCutsMax, nLeafMax, fVerbose );
    pNtkAig = Abc_NtkFromDar( pNtk, pMan );
    Dar_ManStop( pTemp );
    Dar_ManStop( pMan );
    return pNtkAig;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


