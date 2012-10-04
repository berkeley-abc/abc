/**CFile****************************************************************

  FileName    [abcTim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Testing hierarchy/timing manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcTim.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "aig/gia/giaAig.h"
#include "misc/tim/tim.h"
#include "opt/dar/dar.h"
#include "proof/dch/dch.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define TIM_TEST_BOX_RATIO 30

// assume that every TIM_TEST_BOX_RATIO'th object is a white box
static inline int Abc_NodeIsWhiteBox( Abc_Obj_t * pObj )  { assert( Abc_ObjIsNode(pObj) ); return Abc_ObjId(pObj) % TIM_TEST_BOX_RATIO == 0; }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derives one delay table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float * Abc_NtkTestTimDelayTableOne( int nInputs, int nOutputs )
{
    float * pTable;
    int i, k;
    pTable = ABC_ALLOC( float, 3 + nInputs * nOutputs );
    pTable[0] = (float)-1;
    pTable[1] = (float)nInputs;
    pTable[2] = (float)nOutputs;
    for ( i = 0; i < nOutputs; i++ )
    for ( k = 0; k < nInputs; k++ )
        pTable[3 + i * nInputs + k] = 1.0;
    return pTable;
}

/**Function*************************************************************

  Synopsis    [Derives timing tables for each fanin size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkTestTimDelayTables( int nFaninsMax )
{
    Vec_Ptr_t * vTables;
    float * pTable;
    int i;
    vTables = Vec_PtrAlloc( nFaninsMax + 1 );
    for ( i = 0; i <= nFaninsMax; i++ )
    {
        // derive delay table
        pTable = Abc_NtkTestTimDelayTableOne( i, 1 );
        // set its table ID 
        pTable[0] = (float)Vec_PtrSize(vTables);
        // save in the resulting array
        Vec_PtrPush( vTables, pTable );
    }
    return vTables;
}



/**Function*************************************************************

  Synopsis    [Derives GIA for the output of the local function of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkTestTimNodeStrash_rec( Gia_Man_t * pGia, Hop_Obj_t * pObj )
{
    assert( !Hop_IsComplement(pObj) );
    if ( !Hop_ObjIsNode(pObj) || Hop_ObjIsMarkA(pObj) )
        return;
    Abc_NtkTestTimNodeStrash_rec( pGia, Hop_ObjFanin0(pObj) ); 
    Abc_NtkTestTimNodeStrash_rec( pGia, Hop_ObjFanin1(pObj) );
    pObj->iData = Gia_ManHashAnd( pGia, Hop_ObjChild0CopyI(pObj), Hop_ObjChild1CopyI(pObj) );
    assert( !Hop_ObjIsMarkA(pObj) ); // loop detection
    Hop_ObjSetMarkA( pObj );
}
int Abc_NtkTestTimNodeStrash( Gia_Man_t * pGia, Abc_Obj_t * pNode )
{
    Hop_Man_t * pMan;
    Hop_Obj_t * pRoot;
    Abc_Obj_t * pFanin;
    int i;
    assert( Abc_ObjIsNode(pNode) );
    assert( Abc_NtkIsAigLogic(pNode->pNtk) );
    // get the local AIG manager and the local root node
    pMan = (Hop_Man_t *)pNode->pNtk->pManFunc;
    pRoot = (Hop_Obj_t *)pNode->pData;
    // check the constant case
    if ( Abc_NodeIsConst(pNode) || Hop_Regular(pRoot) == Hop_ManConst1(pMan) )
        return !Hop_IsComplement(pRoot);
    // set elementary variables
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Hop_IthVar(pMan, i)->iData = pFanin->iTemp;
    // strash the AIG of this node
    Abc_NtkTestTimNodeStrash_rec( pGia, Hop_Regular(pRoot) );
    Hop_ConeUnmark_rec( Hop_Regular(pRoot) );
    // return the final node with complement if needed
    return Abc_LitNotCond( Hop_Regular(pRoot)->iData, Hop_IsComplement(pRoot) );
}



/**Function*************************************************************

  Synopsis    [Collect nodes reachable from this box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkTestTimCollectCone_rec( Abc_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanin;
    int i;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    if ( Abc_ObjIsCi(pObj) )
        return;
    assert( Abc_ObjIsNode( pObj ) );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkTestTimCollectCone_rec( pFanin, vNodes );
    Vec_PtrPush( vNodes, pObj );
}
Vec_Ptr_t * Abc_NtkTestTimCollectCone( Abc_Ntk_t * pNtk, Abc_Obj_t * pObj )
{
    Vec_Ptr_t * vCone = Vec_PtrAlloc( 1000 );
    if ( pObj != NULL )
    {
        // collect for one node
        assert( Abc_ObjIsNode(pObj) );
        assert( !Abc_NodeIsTravIdCurrent( pObj ) );
        Abc_NtkTestTimCollectCone_rec( pObj, vCone );
        // remove the node because it is a white box
        Vec_PtrPop( vCone );
    }
    else
    {
        // collect for all COs
        Abc_Obj_t * pObj;
        int i;
        Abc_NtkForEachCo( pNtk, pObj, i )
            Abc_NtkTestTimCollectCone_rec( Abc_ObjFanin0(pObj), vCone );
    }
    return vCone;

}

/**Function*************************************************************

  Synopsis    [Derives GIA manager together with the hierachy manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abc_NtkTestTimDeriveGia( Abc_Ntk_t * pNtk, int fVerbose  )
{
    Gia_Man_t * pTemp;
    Gia_Man_t * pGia = NULL;
    Tim_Man_t * pTim = NULL;
    Vec_Ptr_t * vNodes, * vCone;
    Abc_Obj_t * pObj, * pFanin;
    int i, k, curPi, curPo, TableID;

    // compute topological order
    vNodes = Abc_NtkDfs( pNtk, 0 );

    // construct GIA
    Abc_NtkFillTemp( pNtk );
    pGia = Gia_ManStart( Abc_NtkObjNumMax(pNtk) );
    Gia_ManHashAlloc( pGia );
    // create primary inputs
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->iTemp = Gia_ManAppendCi(pGia);
    // create internal nodes in a topologic order from white boxes
    Abc_NtkIncrementTravId( pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        if ( !Abc_NodeIsWhiteBox(pObj) )
            continue;
        // collect nodes in the DFS order from this box
        vCone = Abc_NtkTestTimCollectCone( pNtk, pObj );
        // perform GIA constructino for these nodes
        Vec_PtrForEachEntry( Abc_Obj_t *, vCone, pFanin, k )
            pFanin->iTemp = Abc_NtkTestTimNodeStrash( pGia, pFanin );
        // create inputs of the box
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Gia_ManAppendCo( pGia, pFanin->iTemp );
        // craete outputs of the box
        pObj->iTemp = Gia_ManAppendCi(pGia);
        if ( fVerbose )
            printf( "White box %7d :  Cone = %7d  Lit = %7d.\n", Abc_ObjId(pObj), Vec_PtrSize(vCone), pObj->iTemp );
        Vec_PtrFree( vCone );
    }
    // collect node in the DSF from the primary outputs
    vCone = Abc_NtkTestTimCollectCone( pNtk, NULL );
    // perform GIA constructino for these nodes
    Vec_PtrForEachEntry( Abc_Obj_t *, vCone, pFanin, k )
        pFanin->iTemp = Abc_NtkTestTimNodeStrash( pGia, pFanin );
    Vec_PtrFree( vCone );
    // create primary outputs
    Abc_NtkForEachCo( pNtk, pObj, i )
        pObj->iTemp = Gia_ManAppendCo( pGia, Abc_ObjFanin0(pObj)->iTemp );
    // finalize GIA
    Gia_ManHashStop( pGia );
    Gia_ManSetRegNum( pGia, 0 );
    // clean up GIA
    pGia = Gia_ManCleanup( pTemp = pGia );
    Gia_ManStop( pTemp );
//Gia_ManPrint( pGia );

    // construct the timing manager
    pTim = Tim_ManStart( Gia_ManPiNum(pGia), Gia_ManPoNum(pGia) );
    Tim_ManSetDelayTables( pTim, Abc_NtkTestTimDelayTables(Abc_NtkGetFaninMax(pNtk)) );
    // create timing boxes
    curPi = Abc_NtkPiNum( pNtk );
    curPo = 0;
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        if ( !Abc_NodeIsWhiteBox(pObj) )
            continue;
        TableID = Abc_ObjFaninNum(pObj); // in this case, the node size is the ID of its delay table
        Tim_ManCreateBox( pTim, curPo, Abc_ObjFaninNum(pObj), curPi, 1, TableID );
        curPi += 1;
        curPo += Abc_ObjFaninNum(pObj);
    }
    curPo += Abc_NtkPoNum( pNtk );
    assert( curPi == Gia_ManPiNum(pGia) );
    assert( curPo == Gia_ManPoNum(pGia) );
    Vec_PtrFree( vNodes );

    // attach the timing manager
    assert( pGia->pManTime == NULL );
    pGia->pManTime = pTim;
    // return 
    return pGia;
}


/**Function*************************************************************

  Synopsis    [Performs synthesis with or without structural choices.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abc_NtkTestTimPerformSynthesis( Gia_Man_t * p, int fChoices )
{
    Gia_Man_t * pGia;
    Aig_Man_t * pNew, * pTemp;
    Dch_Pars_t Pars, * pPars = &Pars;
    Dch_ManSetDefaultParams( pPars );
    pNew = Gia_ManToAig( p, 0 );
    if ( fChoices )
        pNew = Dar_ManChoiceNew( pNew, pPars );
    else
    {
        pNew = Dar_ManCompress2( pTemp = pNew, 1, 1, 1, 0, 0 );
        Aig_ManStop( pTemp );
    }
    pGia = Gia_ManFromAig( pNew );
    Aig_ManStop( pNew );
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Tests the hierarchy-timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkTestTimByWritingFile( Gia_Man_t * pGia, char * pFileName )
{
    Gia_Man_t * pGia2;

    // normalize choices
    if ( Gia_ManWithChoices(pGia) )
    {
        Gia_ManVerifyChoices( pGia );
        Gia_ManReverseClasses( pGia, 0 );
    }
    // write file
    Gia_WriteAiger( pGia, pFileName, 0, 0 );
    // unnormalize choices
    if ( Gia_ManWithChoices(pGia) )
        Gia_ManReverseClasses( pGia, 1 );

    // read file
    pGia2 = Gia_ReadAiger( pFileName, 1, 1 );

    // normalize choices
    if ( Gia_ManWithChoices(pGia2) )
    {
        Gia_ManVerifyChoices( pGia2 );
        Gia_ManReverseClasses( pGia2, 1 );
    }

    // compare resulting managers
    if ( Gia_ManCompare( pGia, pGia2 ) )
        printf( "Verification suceessful.\n" );

    Gia_ManStop( pGia2 );
}

/**Function*************************************************************

  Synopsis    [Tests construction and serialization.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkTestTim( Abc_Ntk_t * pNtk, int fVerbose )
{
    int fUseChoices = 0;
    Gia_Man_t * pGia, * pTemp;

    // this test only works for a logic network (for example, network with LUT mapping)
    assert( Abc_NtkIsLogic(pNtk) );
    // make sure local functions of the nodes are in the AIG form
    Abc_NtkToAig( pNtk );

    // create GIA manager (pGia) with hierarhy/timing manager attached (pGia->pManTime)
    // while assuming that some nodes are white boxes (see Abc_NodeIsWhiteBox)
    pGia = Abc_NtkTestTimDeriveGia( pNtk, fVerbose );
    printf( "Created GIA manager for network with %d white boxes.\n", Tim_ManBoxNum((Tim_Man_t *)pGia->pManTime) );

    // print the timing manager
    if ( fVerbose )
        Tim_ManPrint( (Tim_Man_t *)pGia->pManTime );

    // test writing both managers into a file and reading them back
    Abc_NtkTestTimByWritingFile( pGia, "test1.aig" );

    // perform synthesis
    pGia = Abc_NtkTestTimPerformSynthesis( pTemp = pGia, fUseChoices );
    Gia_ManStop( pTemp );

    // test writing both managers into a file and reading them back
    Abc_NtkTestTimByWritingFile( pGia, "test2.aig" );

    Gia_ManStop( pGia );
}




////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

