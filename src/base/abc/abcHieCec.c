/**CFile****************************************************************

  FileName    [abcHieCec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Hierarchical CEC manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcHieCec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "ioAbc.h"
#include "gia.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define Abc_ObjForEachFaninReal( pObj, pFanin, i )          \
    for ( i = 0; (i < Abc_ObjFaninNum(pObj)) && (((pFanin) = Abc_ObjFaninReal(pObj, i)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the real faniin of the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_Obj_t * Abc_ObjFaninReal( Abc_Obj_t * pObj, int i )    
{
    Abc_Obj_t * pRes;
    if ( Abc_ObjIsBox(pObj) )
        pRes = Abc_ObjFanin0( Abc_ObjFanin0( Abc_ObjFanin(pObj, i) ) );
    else
    {
        assert( Abc_ObjIsPo(pObj) || Abc_ObjIsNode(pObj) );
        pRes = Abc_ObjFanin0( Abc_ObjFanin(pObj, i) );
    }
    if ( Abc_ObjIsBo(pRes) )
        return Abc_ObjFanin0(pRes);
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDfsBoxes_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanin;
    int i;
    if ( Abc_ObjIsPi(pNode) )
        return;
    assert( Abc_ObjIsNode(pNode) || Abc_ObjIsBox(pNode) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    Abc_NodeSetTravIdCurrent( pNode );
    // visit the transitive fanin of the node
    Abc_ObjForEachFaninReal( pNode, pFanin, i )
        Abc_NtkDfsBoxes_rec( pFanin, vNodes );
    // add the node after the fanins have been added
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Returns the array of node and boxes reachable from POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkDfsBoxes( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsNetlist(pNtk) );
    // set the traversal ID
    Abc_NtkIncrementTravId( pNtk );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkDfsBoxes_rec( Abc_ObjFaninReal(pObj, 0), vNodes );
    return vNodes;
}


/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDeriveFlatGiaSop( Gia_Man_t * pGia, int * gFanins, char * pSop )
{
    char * pCube;
    int gAnd, gSum;
    int i, Value, nFanins;
    // get the number of variables
    nFanins = Abc_SopGetVarNum(pSop);
    if ( Abc_SopIsExorType(pSop) )
    {
        gSum = 0; 
        for ( i = 0; i < nFanins; i++ )
            gSum = Gia_ManHashXor( pGia, gSum, gFanins[i] );
    }
    else
    {
        // go through the cubes of the node's SOP
        gSum = 0; 
        Abc_SopForEachCube( pSop, nFanins, pCube )
        {
            // create the AND of literals
            gAnd = 1;
            Abc_CubeForEachVar( pCube, Value, i )
            {
                if ( Value == '1' )
                    gAnd = Gia_ManHashAnd( pGia, gAnd, gFanins[i] );
                else if ( Value == '0' )
                    gAnd = Gia_ManHashAnd( pGia, gAnd, Gia_LitNot(gFanins[i]) );
            }
            // add to the sum of cubes
            gSum = Gia_ManHashAnd( pGia, Gia_LitNot(gSum), Gia_LitNot(gAnd) );
            gSum = Gia_LitNot( gSum );
        }
    }
    // decide whether to complement the result
    if ( Abc_SopIsComplement(pSop) )
        gSum = Gia_LitNot(gSum);
    return gSum;
}

/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDeriveFlatGia_rec( Gia_Man_t * pGia, Abc_Ntk_t * pNtk )
{
    int gFanins[16];
    Vec_Ptr_t * vOrder = (Vec_Ptr_t *)pNtk->pData;
    Abc_Obj_t * pObj, * pTerm;
    Abc_Ntk_t * pNtkModel;
    int i, k;
    Abc_NtkForEachPi( pNtk, pTerm, i )
        assert( Abc_ObjFanout0(pTerm)->iTemp >= 0 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vOrder, pObj, i )
    {
        if ( Abc_ObjIsNode(pObj) )
        {
            char * pSop = (char *)pObj->pData;
            int nLength = strlen(pSop);
            if ( nLength == 4 ) // buf/inv
            {
                assert( pSop[2] == '1' );
                assert( pSop[0] == '0' || pSop[0] == '1' );
                assert( Abc_ObjFanin0(pObj)->iTemp >= 0 );
                Abc_ObjFanout0(pObj)->iTemp = Gia_LitNotCond( Abc_ObjFanin0(pObj)->iTemp, pSop[0]=='0' );
                continue;
            }
            if ( nLength == 5 ) // and2
            {
                assert( pSop[3] == '1' );
                assert( pSop[0] == '0' || pSop[0] == '1' );
                assert( pSop[1] == '0' || pSop[1] == '1' );
                assert( Abc_ObjFanin0(pObj)->iTemp >= 0 );
                assert( Abc_ObjFanin1(pObj)->iTemp >= 0 );
                Abc_ObjFanout0(pObj)->iTemp = Gia_ManHashAnd( pGia, 
                    Gia_LitNotCond( Abc_ObjFanin0(pObj)->iTemp, pSop[0]=='0' ),
                    Gia_LitNotCond( Abc_ObjFanin1(pObj)->iTemp, pSop[1]=='0' )
                    );
                continue;
            }
            assert( Abc_ObjFaninNum(pObj) <= 16 );
            assert( Abc_ObjFaninNum(pObj) == Abc_SopGetVarNum(pSop) );
            Abc_ObjForEachFanin( pObj, pTerm, k )
            {
                gFanins[k] = pTerm->iTemp;
                assert( gFanins[k] >= 0 );
            }
            Abc_ObjFanout0(pObj)->iTemp = Abc_NtkDeriveFlatGiaSop( pGia, gFanins, pSop );
            continue;
        }
        assert( Abc_ObjIsBox(pObj) );
        pNtkModel = (Abc_Ntk_t *)pObj->pData;
        Abc_NtkFillTemp( pNtkModel );
        // check the match between the number of actual and formal parameters
        assert( Abc_ObjFaninNum(pObj) == Abc_NtkPiNum(pNtkModel) );
        assert( Abc_ObjFanoutNum(pObj) == Abc_NtkPoNum(pNtkModel) );
        // assign PIs
        Abc_ObjForEachFanin( pObj, pTerm, k )
            Abc_ObjFanout0( Abc_NtkPi(pNtkModel, k) )->iTemp = Abc_ObjFanin0(pTerm)->iTemp;
        // call recursively
        Abc_NtkDeriveFlatGia_rec( pGia, pNtkModel );
        // assign POs
        Abc_ObjForEachFanout( pObj, pTerm, k )
            Abc_ObjFanout0(pTerm)->iTemp = Abc_ObjFanin0( Abc_NtkPo(pNtkModel, k) )->iTemp;
    }
    Abc_NtkForEachPo( pNtk, pTerm, i )
        assert( Abc_ObjFanin0(pTerm)->iTemp >= 0 );
}

/**Function*************************************************************

  Synopsis    [Flattens the logic hierarchy of the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abc_NtkDeriveFlatGia( Abc_Ntk_t * pNtk )
{
    Gia_Man_t * pTemp, * pGia = NULL;
    Abc_Obj_t * pTerm;
    int i;

    assert( Abc_NtkIsNetlist(pNtk) );
    assert( !Abc_NtkLatchNum(pNtk) );
    Abc_NtkFillTemp( pNtk );
    // start the network
    pGia = Gia_ManStart( (1<<16) );
    pGia->pName = Gia_UtilStrsav( Abc_NtkName(pNtk) );
    Gia_ManHashAlloc( pGia );
    // create PIs
    Abc_NtkForEachPi( pNtk, pTerm, i )
        Abc_ObjFanout0(pTerm)->iTemp = Gia_ManAppendCi( pGia );
    // recursively flatten hierarchy
    Abc_NtkDeriveFlatGia_rec( pGia, pNtk );
    // create POs
    Abc_NtkForEachPo( pNtk, pTerm, i )
        Gia_ManAppendCo( pGia, Abc_ObjFanin0(pTerm)->iTemp );
    // prepare return value
    Gia_ManHashStop( pGia );
    Gia_ManSetRegNum( pGia, 0 );
    pGia = Gia_ManCleanup( pTemp = pGia );
    Gia_ManStop( pTemp );
    return pGia;
}

/**Function*************************************************************

  Synopsis    [Count the number of instances and I/O pins in the hierarchy.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCountInstances_rec( Abc_Ntk_t * pNtk, int * pCountInst, int * pCountPins )
{
    Vec_Ptr_t * vOrder = (Vec_Ptr_t *)pNtk->pData;
    Abc_Obj_t * pObj;
    int i;
    *pCountInst += 1;
    *pCountPins += Abc_NtkPiNum(pNtk) + Abc_NtkPoNum(pNtk);
    Vec_PtrForEachEntry( Abc_Obj_t *, vOrder, pObj, i )
        if ( Abc_ObjIsBox(pObj) )
            Abc_NtkCountInstances_rec( (Abc_Ntk_t *)pObj->pData, pCountInst, pCountPins );
}

/**Function*************************************************************

  Synopsis    [Count the number of instances and I/O pins in the hierarchy.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCountInstances( Abc_Ntk_t * pNtk )
{
    int CountInst = 0, CountPins = 0;
    assert( Abc_NtkIsNetlist(pNtk) );
    assert( !Abc_NtkLatchNum(pNtk) );
    // recursively flatten hierarchy
    Abc_NtkCountInstances_rec( pNtk, &CountInst, &CountPins );
    printf( "Instances = %10d.  I/O pins = %10d.\n", CountInst, CountPins );
}

/**Function*************************************************************

  Synopsis    [Performs hierarchical equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abc_NtkHieCecTest( char * pFileName, int fVerbose )
{
    int fCheck = 1;
    Vec_Ptr_t * vMods;
    Abc_Ntk_t * pNtk, * pModel;
    Gia_Man_t * pGia;
    int i, clk = clock();

    // read hierarchical netlist
    pNtk = Io_ReadBlifMv( pFileName, 0, fCheck );
    if ( pNtk == NULL )
    {
        printf( "Reading BLIF file has failed.\n" );
        return NULL;
    }
    if ( pNtk->pDesign == NULL || pNtk->pDesign->vModules == NULL )
    {
        printf( "There is no hierarchy information.\n" );
        Abc_NtkDelete( pNtk );
        return NULL;
    }
    Abc_PrintTime( 1, "Reading file", clock() - clk );

    // print stats
    if ( fVerbose )
        Abc_NtkPrintBoxInfo( pNtk );

    // order nodes/boxes of all models
    vMods = pNtk->pDesign->vModules;
    Vec_PtrForEachEntry( Abc_Ntk_t *, vMods, pModel, i )
        pModel->pData = Abc_NtkDfsBoxes( pModel );

    // derive GIA
    clk = clock();
    pGia = Abc_NtkDeriveFlatGia( pNtk );
    Abc_PrintTime( 1, "Deriving GIA", clock() - clk );

    clk = clock();
    Abc_NtkCountInstances( pNtk );
    Abc_PrintTime( 1, "Gather stats", clock() - clk );

    // clean nodes/boxes of all nodes
    Vec_PtrForEachEntry( Abc_Ntk_t *, vMods, pModel, i )
        Vec_PtrFree( (Vec_Ptr_t *)pModel->pData );
    Abc_NtkDelete( pNtk );

    return pGia;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

