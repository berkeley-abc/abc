/**CFile****************************************************************

  FileName    [ntlUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts COs that are connected to the internal nodes through invs/bufs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCountLut1( Ntl_Mod_t * pRoot )
{
    Ntl_Obj_t * pObj;
    int i, Counter = 0;
    Ntl_ModelForEachNode( pRoot, pObj, i )
        if ( Ntl_ObjFaninNum(pObj) == 1 )
            Counter++;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Reads the maximum number of fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelGetFaninMax( Ntl_Mod_t * pRoot )
{
    Ntl_Obj_t * pNode;
    int i, nFaninsMax = 0;
    Ntl_ModelForEachNode( pRoot, pNode, i )
    {
        if ( nFaninsMax < Ntl_ObjFaninNum(pNode) )
            nFaninsMax = Ntl_ObjFaninNum(pNode);
    }
    return nFaninsMax;
}

/**Function*************************************************************

  Synopsis    [If the net is driven by an inv/buf, returns its fanin.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Net_t * Ntl_ModelFindSimpleNet( Ntl_Net_t * pNetCo )
{
    // skip the case when the net is not driven by a node
    if ( !Ntl_ObjIsNode(pNetCo->pDriver) )
        return NULL;
    // skip the case when the node is not an inv/buf
    if ( Ntl_ObjFaninNum(pNetCo->pDriver) != 1 )
        return NULL;
    return Ntl_ObjFanin0(pNetCo->pDriver);
}

/**Function*************************************************************

  Synopsis    [Connects COs to the internal nodes other than inv/bufs.]

  Description [Should be called immediately after reading from file.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCountSimpleCoDriversOne( Ntl_Net_t * pNetCo )
{
    Ntl_Net_t * pNetFanin;
    // skip the case when the net is not driven by a node
    if ( !Ntl_ObjIsNode(pNetCo->pDriver) )
        return 0;
    // skip the case when the node is not an inv/buf
    if ( Ntl_ObjFaninNum(pNetCo->pDriver) != 1 )
        return 0;
    // skip the case when the second-generation driver is not a node
    pNetFanin = Ntl_ObjFanin0(pNetCo->pDriver);
    if ( !Ntl_ObjIsNode(pNetFanin->pDriver) )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Counts COs that are connected to the internal nodes through invs/bufs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCountSimpleCoDrivers( Ntl_Man_t * p )
{
    Ntl_Net_t * pNetCo;
    Ntl_Obj_t * pObj;
    Ntl_Mod_t * pRoot;
    int i, k, Counter;
    Counter = 0;
    pRoot = Ntl_ManRootModel( p );
    Ntl_ModelForEachPo( pRoot, pObj, i )
        Counter += Ntl_ManCountSimpleCoDriversOne( Ntl_ObjFanin0(pObj) );
    Ntl_ModelForEachLatch( pRoot, pObj, i )
        Counter += Ntl_ManCountSimpleCoDriversOne( Ntl_ObjFanin0(pObj) );
    Ntl_ModelForEachBox( pRoot, pObj, i )
        Ntl_ObjForEachFanin( pObj, pNetCo, k )
            Counter += Ntl_ManCountSimpleCoDriversOne( pNetCo );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Derives the array of CI names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_ManCollectCiNames( Ntl_Man_t * p )
{
    Vec_Ptr_t * vNames;
    Ntl_Net_t * pNet;
    int i;
    vNames = Vec_PtrAlloc( 1000 );
    Ntl_ManForEachCiNet( p, pNet, i )
        Vec_PtrPush( vNames, pNet->pName );
    return vNames;
}

/**Function*************************************************************

  Synopsis    [Derives the array of CI names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_ManCollectCoNames( Ntl_Man_t * p )
{
    Vec_Ptr_t * vNames;
    Ntl_Net_t * pNet;
    int i;
    vNames = Vec_PtrAlloc( 1000 );
    Ntl_ManForEachCoNet( p, pNet, i )
        Vec_PtrPush( vNames, pNet->pName );
    return vNames;
}

/**Function*************************************************************

  Synopsis    [Marks the CI/CO nets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManMarkCiCoNets( Ntl_Man_t * p )
{
    Ntl_Net_t * pNet;
    int i;
    Ntl_ManForEachCiNet( p, pNet, i )
        pNet->fMark = 1;
    Ntl_ManForEachCoNet( p, pNet, i )
        pNet->fMark = 1;
}

/**Function*************************************************************

  Synopsis    [Unmarks the CI/CO nets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManUnmarkCiCoNets( Ntl_Man_t * p )
{
    Ntl_Net_t * pNet;
    int i;
    Ntl_ManForEachCiNet( p, pNet, i )
        pNet->fMark = 0;
    Ntl_ManForEachCoNet( p, pNet, i )
        pNet->fMark = 0;
}

/**Function*************************************************************

  Synopsis    [Convert initial values of registers to be zero.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManSetZeroInitValues( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    int i;
    pRoot = Ntl_ManRootModel(p);
    Ntl_ModelForEachLatch( pRoot, pObj, i )
        pObj->LatchId.regInit = 0;
}

/**Function*************************************************************

  Synopsis    [Transforms the netlist to have latches with const-0 init-values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManAddInverters( Ntl_Obj_t * pObj )
{
    char * pStore;
    Ntl_Mod_t * pRoot = pObj->pModel;
    Ntl_Man_t * pMan = pRoot->pMan;
    Ntl_Net_t * pNetLo, * pNetLi, * pNetLoInv, * pNetLiInv;
    Ntl_Obj_t * pNode;
    int nLength, RetValue;
    assert( Ntl_ObjIsInit1( pObj ) );
    // get the nets
    pNetLi = Ntl_ObjFanin0(pObj);
    pNetLo = Ntl_ObjFanout0(pObj);
    // get storage for net names
    nLength = strlen(pNetLi->pName) + strlen(pNetLo->pName) + 10; 
    pStore = Aig_MmFlexEntryFetch( pMan->pMemSops, nLength );
    // create input interter
    pNode = Ntl_ModelCreateNode( pRoot, 1 );
    pNode->pSop = Ntl_ManStoreSop( pMan->pMemSops, "0 1\n" );
    Ntl_ObjSetFanin( pNode, pNetLi, 0 );
    // create input net
    strcpy( pStore, pNetLi->pName );
    strcat( pStore, "_inv" );
    if ( Ntl_ModelFindNet( pRoot, pStore ) )
    {
        printf( "Ntl_ManTransformInitValues(): Internal error! Cannot create net with LI-name + _inv\n" );
        return;
    }
    pNetLiInv = Ntl_ModelFindOrCreateNet( pRoot, pStore );
    RetValue = Ntl_ModelSetNetDriver( pNode, pNetLiInv );
    assert( RetValue );
    // connect latch to the input net
    Ntl_ObjSetFanin( pObj, pNetLiInv, 0 );
    // disconnect latch from the output net
    RetValue = Ntl_ModelClearNetDriver( pObj, pNetLo );
    assert( RetValue );
    // create the output net
    strcpy( pStore, pNetLo->pName );
    strcat( pStore, "_inv" );
    if ( Ntl_ModelFindNet( pRoot, pStore ) )
    {
        printf( "Ntl_ManTransformInitValues(): Internal error! Cannot create net with LO-name + _inv\n" );
        return;
    }
    pNetLoInv = Ntl_ModelFindOrCreateNet( pRoot, pStore );
    RetValue = Ntl_ModelSetNetDriver( pObj, pNetLoInv );
    assert( RetValue );
    // create output interter
    pNode = Ntl_ModelCreateNode( pRoot, 1 );
    pNode->pSop = Ntl_ManStoreSop( pMan->pMemSops, "0 1\n" );
    Ntl_ObjSetFanin( pNode, pNetLoInv, 0 );
    // redirect the old output net
    RetValue = Ntl_ModelSetNetDriver( pNode, pNetLo );
    assert( RetValue );
}

/**Function*************************************************************

  Synopsis    [Transforms the netlist to have latches with const-0 init-values.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManTransformInitValues( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    int i;
    pRoot = Ntl_ManRootModel(p);
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        if ( Ntl_ObjIsInit1( pObj ) )
            Ntl_ManAddInverters( pObj );
        pObj->LatchId.regInit = 0;
    }
}

/**Function*************************************************************

  Synopsis    [Transforms register classes.]

  Description [Returns the vector of vectors containing the numbers
  of registers belonging to the same class. Skips classes containing
  less than the given number of registers.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * Ntl_ManTransformRegClasses( Ntl_Man_t * pMan, int nSizeMax, int fVerbose )
{
    Vec_Ptr_t * vParts;
    Vec_Int_t * vPart;
    int * pClassNums, nClasses;
    int Class, ClassMax, i, k;
    if ( Vec_IntSize(pMan->vRegClasses) == 0 )
    {
        printf( "Ntl_ManReportRegClasses(): Register classes are not defined.\n" );
        return NULL;
    }
    // find the largest class
    ClassMax = -1;
    Vec_IntForEachEntry( pMan->vRegClasses, Class, k )
    {
        if ( Class < 0 )
        {
            printf( "Ntl_ManReportRegClasses(): Register class (%d) is negative.\n", Class );
            return NULL;
        }
        if ( ClassMax < Class )
            ClassMax = Class;
    }
    if ( ClassMax > 1000000 )
    {
        printf( "Ntl_ManReportRegClasses(): The largest number of a register class (%d) is too large (> 1000000).\n", ClassMax );
        return NULL;
    }
    // count the number of classes
    pClassNums = ABC_CALLOC( int, ClassMax + 1 );
    Vec_IntForEachEntry( pMan->vRegClasses, Class, k )
        pClassNums[Class]++;
    // count the number of classes
    nClasses = 0;
    for ( i = 0; i <= ClassMax; i++ )
        nClasses += (int)(pClassNums[i] > 0);
    // report the classes
    if ( fVerbose && nClasses > 1 )
    {
        printf( "The number of register clases = %d.\n", nClasses );
        for ( i = 0; i <= ClassMax; i++ )
            if ( pClassNums[i] )
                printf( "(%d, %d)  ", i, pClassNums[i] );
        printf( "\n" );
    }
    // skip if there is only one class
    if ( nClasses == 1 )
    {
        vParts = NULL;
        if ( Vec_IntSize(pMan->vRegClasses) >= nSizeMax )
        {
            vParts = Vec_PtrAlloc( 100 );
            vPart = Vec_IntStartNatural( Vec_IntSize(pMan->vRegClasses) );
            Vec_PtrPush( vParts, vPart );
        }
        printf( "There is only one class with %d registers.\n", Vec_IntSize(pMan->vRegClasses) );
        ABC_FREE( pClassNums );
        return (Vec_Vec_t *)vParts;
    }
    // create classes
    vParts = Vec_PtrAlloc( 100 );
    for ( i = 0; i <= ClassMax; i++ )
    {
        if ( pClassNums[i] == 0 || pClassNums[i] < nSizeMax )
            continue;
        vPart = Vec_IntAlloc( pClassNums[i] );
        Vec_IntForEachEntry( pMan->vRegClasses, Class, k )
            if ( Class == i )
                Vec_IntPush( vPart, k );
        assert( Vec_IntSize(vPart) == pClassNums[i] );
        Vec_PtrPush( vParts, vPart );
    }
    ABC_FREE( pClassNums );
    Vec_VecSort( (Vec_Vec_t *)vParts, 1 );
    // report the selected classes
    if ( fVerbose )
    {
        printf( "The number of selected register clases = %d.\n", Vec_PtrSize(vParts) );
        Vec_PtrForEachEntry( vParts, vPart, i )
            printf( "(%d, %d)  ", i, Vec_IntSize(vPart) );
        printf( "\n" );
    }
    return (Vec_Vec_t *)vParts;
}

/**Function*************************************************************

  Synopsis    [Filter register clases using clock-domain information.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManFilterRegisterClasses( Aig_Man_t * pAig, Vec_Int_t * vRegClasses, int fVerbose )
{
    Aig_Obj_t * pObj, * pRepr;
    int i, k, nOmitted, nTotal;
    if ( pAig->pReprs == NULL )
        return;
    assert( pAig->nRegs > 0 );
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->PioNum = -1;
    k = 0;
    Aig_ManForEachLoSeq( pAig, pObj, i )
        pObj->PioNum = k++;
    // consider equivalences
    nOmitted = nTotal = 0;
    Aig_ManForEachObj( pAig, pObj, i )
    {
        pRepr = pAig->pReprs[pObj->Id];
        if ( pRepr == NULL )
            continue;
        nTotal++;
        assert( Aig_ObjIsPi(pObj) );
        assert( Aig_ObjIsPi(pRepr) || Aig_ObjIsConst1(pRepr) );
        if ( Aig_ObjIsConst1(pRepr) )
            continue;
        assert( pObj->PioNum >= 0 && pRepr->PioNum >= 0 );
        // remove equivalence if they belong to different classes
        if ( Vec_IntEntry( vRegClasses, pObj->PioNum ) == 
             Vec_IntEntry( vRegClasses, pRepr->PioNum ) )
             continue;
         pAig->pReprs[pObj->Id] = NULL;
         nOmitted++;
    }
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->PioNum = -1;
    if ( fVerbose )
        printf( "Omitted %d (out of %d) equivs due to register class mismatch.\n", 
            nOmitted, nTotal );
}


/**Function*************************************************************

  Synopsis    [Counts the number of CIs in the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManLatchNum( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    int i, Counter = 0;
    pRoot = Ntl_ManRootModel(p);
    Ntl_ModelForEachBox( pRoot, pObj, i )
        Counter += Ntl_ModelLatchNum( pObj->pImplem );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the design is combinational.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManIsComb( Ntl_Man_t * p )          
{ 
    return Ntl_ManLatchNum(p) == 0; 
} 

/**Function*************************************************************

  Synopsis    [Counts the number of CIs in the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCombLeafNum( Ntl_Mod_t * p )
{
    Ntl_Obj_t * pObj;
    int i, Counter = 0;
    Ntl_ModelForEachCombLeaf( p, pObj, i )
        Counter += Ntl_ObjFanoutNum( pObj );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Counts the number of COs in the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCombRootNum( Ntl_Mod_t * p )
{
    Ntl_Obj_t * pObj;
    int i, Counter = 0;
    Ntl_ModelForEachCombRoot( p, pObj, i )
        Counter += Ntl_ObjFaninNum( pObj );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Counts the number of CIs in the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelSeqLeafNum( Ntl_Mod_t * p )
{
    Ntl_Obj_t * pObj;
    int i, Counter = 0;
    Ntl_ModelForEachSeqLeaf( p, pObj, i )
        Counter += Ntl_ObjFanoutNum( pObj );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Counts the number of COs in the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelSeqRootNum( Ntl_Mod_t * p )
{
    Ntl_Obj_t * pObj;
    int i, Counter = 0;
    Ntl_ModelForEachSeqRoot( p, pObj, i )
        Counter += Ntl_ObjFaninNum( pObj );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Unmarks the CI/CO nets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCheckNetsAreNotMarked( Ntl_Mod_t * pModel )
{
    Ntl_Net_t * pNet;
    int i;
    Ntl_ModelForEachNet( pModel, pNet, i )
        assert( pNet->fMark == 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Unmarks the CI/CO nets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ModelClearNets( Ntl_Mod_t * pModel )
{
    Ntl_Net_t * pNet;
    int i;
    Ntl_ModelForEachNet( pModel, pNet, i )
    {
        pNet->nVisits = pNet->fMark = 0;
        pNet->pCopy = pNet->pCopy2 = NULL;
    }
}

/**Function*************************************************************

  Synopsis    [Removes nets without fanins and fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManRemoveUselessNets( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pNode;
    Ntl_Net_t * pNet;
    int i, k, Counter;
    pRoot = Ntl_ManRootModel( p );
    Ntl_ModelForEachNet( pRoot, pNet, i )
        pNet->fMark = 0;
    Ntl_ModelForEachPi( pRoot, pNode, i )
    {
        pNet = Ntl_ObjFanout0(pNode);
        pNet->fMark = 1;
    }
    Ntl_ModelForEachPo( pRoot, pNode, i )
    {
        pNet = Ntl_ObjFanin0(pNode);
        pNet->fMark = 1;
    }
    Ntl_ModelForEachNode( pRoot, pNode, i )
    {
        Ntl_ObjForEachFanin( pNode, pNet, k )
            pNet->fMark = 1;
        Ntl_ObjForEachFanout( pNode, pNet, k )
            pNet->fMark = 1;
    }
    Ntl_ModelForEachBox( pRoot, pNode, i )
    {
        Ntl_ObjForEachFanin( pNode, pNet, k )
            pNet->fMark = 1;
        Ntl_ObjForEachFanout( pNode, pNet, k )
            pNet->fMark = 1;
    }
    Counter = 0;
    Ntl_ModelForEachNet( pRoot, pNet, i )
    {
        if ( pNet->fMark )
        {
            pNet->fMark = 0;
            continue;
        }
        if ( pNet->fFixed )
            continue;
        Ntl_ModelDeleteNet( pRoot, pNet );
        Vec_PtrWriteEntry( pRoot->vNets, pNet->NetId, NULL );
        Counter++;
    }
    if ( Counter )
        printf( "Deleted %d nets without fanins/fanouts.\n", Counter );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


