/**CFile****************************************************************

  FileName    [abcMiter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures to derive the miter of two circuits.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcMiter.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t * Abc_NtkMiterInt( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb );
static void        Abc_NtkMiterPrepare( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Abc_Ntk_t * pNtkMiter, int fComb );
static void        Abc_NtkMiterAddOne( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkMiter );
static void        Abc_NtkMiterFinalize( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Abc_Ntk_t * pNtkMiter, int fComb );
static void        Abc_NtkAddFrame( Abc_Ntk_t * pNetNew, Abc_Ntk_t * pNet, int iFrame, Vec_Ptr_t * vNodes );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derives the miter of two networks.]

  Description [Preprocesses the networks to make sure that they are strashed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkMiter( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb )
{
    Abc_Ntk_t * pTemp = NULL;
    int fRemove1, fRemove2;
    // make sure the circuits are strashed 
    fRemove1 = (!Abc_NtkIsAig(pNtk1)) && (pNtk1 = Abc_NtkStrash(pNtk1, 0));
    fRemove2 = (!Abc_NtkIsAig(pNtk2)) && (pNtk2 = Abc_NtkStrash(pNtk2, 0));
    if ( pNtk1 && pNtk2 )
    {
        // check that the networks have the same PIs/POs/latches
        // reorder PIs/POs/latches of pNtk2 according to pNtk1
        // compute the miter of two strashed sequential networks
        if ( Abc_NtkCompareSignals( pNtk1, pNtk2, fComb ) )
            pTemp = Abc_NtkMiterInt( pNtk1, pNtk2, fComb );
    }
    if ( fRemove1 )  Abc_NtkDelete( pNtk1 );
    if ( fRemove2 )  Abc_NtkDelete( pNtk2 );
    return pTemp;
}

/**Function*************************************************************

  Synopsis    [Derives the miter of two sequential networks.]

  Description [Assumes that the networks are strashed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkMiterInt( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb )
{
    int fCheck = 1;
    char Buffer[100];
    Abc_Ntk_t * pNtkMiter;

    assert( Abc_NtkIsAig(pNtk1) );
    assert( Abc_NtkIsAig(pNtk2) );

    // start the new network
    pNtkMiter = Abc_NtkAlloc( ABC_NTK_AIG );
    sprintf( Buffer, "%s_%s_miter", pNtk1->pName, pNtk2->pName );
    pNtkMiter->pName = util_strsav(Buffer);

    // perform strashing
    Abc_NtkMiterPrepare( pNtk1, pNtk2, pNtkMiter, fComb );
    Abc_NtkMiterAddOne( pNtk1, pNtkMiter );
    Abc_NtkMiterAddOne( pNtk2, pNtkMiter );
    Abc_NtkMiterFinalize( pNtk1, pNtk2, pNtkMiter, fComb );

    // make sure that everything is okay
    if ( fCheck && !Abc_NtkCheck( pNtkMiter ) )
    {
        printf( "Abc_NtkMiter: The network check has failed.\n" );
        Abc_NtkDelete( pNtkMiter );
        return NULL;
    }
    return pNtkMiter;
}

/**Function*************************************************************

  Synopsis    [Prepares the network for mitering.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMiterPrepare( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Abc_Ntk_t * pNtkMiter, int fComb )
{
    Abc_Obj_t * pObj, * pObjNew;
    int i;
    // clean the copy field in all objects
    Abc_NtkCleanCopy( pNtk1 );
    Abc_NtkCleanCopy( pNtk2 );
    if ( fComb )
    {
        // create new PIs and remember them in the old PIs
        Abc_NtkForEachCi( pNtk1, pObj, i )
        {
            pObjNew = Abc_NtkCreateTermPi( pNtkMiter );
            // remember this PI in the old PIs
            pObj->pCopy = pObjNew;
            pObj = Abc_NtkCi(pNtk2, i);  
            pObj->pCopy = pObjNew;
            // add name
            Abc_NtkLogicStoreName( pObjNew, pNtk1->vNamesPi->pArray[i] );
        }
        // create the only PO
        pObjNew = Abc_NtkCreateTermPo( pNtkMiter );
        // add the PO name
        Abc_NtkLogicStoreName( pObjNew, "miter" );
    }
    else
    {
        // create new PIs and remember them in the old PIs
        Abc_NtkForEachPi( pNtk1, pObj, i )
        {
            pObjNew = Abc_NtkCreateTermPi( pNtkMiter );
            // remember this PI in the old PIs
            pObj->pCopy = pObjNew;
            pObj = Abc_NtkPi(pNtk2, i);  
            pObj->pCopy = pObjNew;
            // add name
            Abc_NtkLogicStoreName( pObjNew, pNtk1->vNamesPi->pArray[i] );
        }
        // create the only PO
        pObjNew = Abc_NtkCreateTermPo( pNtkMiter );
        // add the PO name
        Abc_NtkLogicStoreName( pObjNew, "miter" );
        // create the latches
        Abc_NtkForEachLatch( pNtk1, pObj, i )
        {
            pObjNew = Abc_NtkDupObj( pNtkMiter, pObj );
            Vec_PtrPush( pNtkMiter->vPis, pObjNew );
            Vec_PtrPush( pNtkMiter->vPos, pObjNew );
            // add name
            Abc_NtkLogicStoreNamePlus( pObjNew, pNtk1->vNamesLatch->pArray[i], "_1" );
        }
        Abc_NtkForEachLatch( pNtk2, pObj, i )
        {
            pObjNew = Abc_NtkDupObj( pNtkMiter, pObj );
            Vec_PtrPush( pNtkMiter->vPis, pObjNew );
            Vec_PtrPush( pNtkMiter->vPos, pObjNew );
            // add name
            Abc_NtkLogicStoreNamePlus( pObjNew, pNtk2->vNamesLatch->pArray[i], "_2" );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Performs mitering for one network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMiterAddOne( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkMiter )
{
    ProgressBar * pProgress;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode, * pNodeNew, * pConst1, * pConst1New;
    int i;
    // get the constant nodes
    pConst1    = Abc_AigConst1( pNtk->pManFunc );
    pConst1New = Abc_AigConst1( pNtkMiter->pManFunc );
    // perform strashing
    vNodes = Abc_NtkDfs( pNtk );
    pProgress = Extra_ProgressBarStart( stdout, vNodes->nSize );
    for ( i = 0; i < vNodes->nSize; i++ )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        pNode = vNodes->pArray[i];
        if ( pNode == pConst1 )
            pNodeNew = pConst1New;
        else
            pNodeNew = Abc_AigAnd( pNtkMiter->pManFunc, 
                Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) ),
                Abc_ObjNotCond( Abc_ObjFanin1(pNode)->pCopy, Abc_ObjFaninC1(pNode) ) );
        pNode->pCopy = pNodeNew;
    }
    Vec_PtrFree( vNodes );
    Extra_ProgressBarStop( pProgress );
}


/**Function*************************************************************

  Synopsis    [Finalizes the miter by adding the output part.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMiterFinalize( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Abc_Ntk_t * pNtkMiter, int fComb )
{
    Vec_Ptr_t * vPairs;
    Abc_Obj_t * pDriverNew, * pMiter, * pNode;
    int i;
    // collect the PO pairs from both networks
    vPairs = Vec_PtrAlloc( 100 );
    if ( fComb )
    {
        // collect the CO nodes for the miter
        Abc_NtkForEachCo( pNtk1, pNode, i )
        {
            pDriverNew = Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
            Vec_PtrPush( vPairs, pDriverNew );
            pNode = Abc_NtkPo( pNtk2, i );
            pDriverNew = Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
            Vec_PtrPush( vPairs, pDriverNew );
        }
    }
    else
    {
        // collect the PO nodes for the miter
        Abc_NtkForEachPo( pNtk1, pNode, i )
        {
            pDriverNew = Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
            Vec_PtrPush( vPairs, pDriverNew );
            pNode = Abc_NtkPo( pNtk2, i );
            pDriverNew = Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
            Vec_PtrPush( vPairs, pDriverNew );
        }
        // connect new latches
        Abc_NtkForEachLatch( pNtk1, pNode, i )
        {
            pDriverNew = Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
            Abc_ObjAddFanin( pNode->pCopy, pDriverNew );
        }
        Abc_NtkForEachLatch( pNtk2, pNode, i )
        {
            pDriverNew = Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
            Abc_ObjAddFanin( pNode->pCopy, pDriverNew );
        }
    }
    // add the miter
    pMiter = Abc_AigMiter( pNtkMiter->pManFunc, vPairs );
    Abc_ObjAddFanin( Abc_NtkPo(pNtkMiter,0), pMiter );
    Vec_PtrFree( vPairs );
}

/**Function*************************************************************

  Synopsis    [Checks the status of the miter.]

  Description [Return 1 if the miter is sat for at least one output.
  Return 0 if the miter is unsat for all its outputs. Returns -1 if the
  miter is undecided for some outputs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMiterIsConstant( Abc_Ntk_t * pMiter )
{
    Abc_Obj_t * pNodePo, * pChild;
    int i;
    assert( Abc_NtkIsAig(pMiter) );
    Abc_NtkForEachPo( pMiter, pNodePo, i )
    {
        pChild = Abc_ObjChild0( Abc_NtkPo(pMiter,i) );
        if ( Abc_NodeIsConst(pChild) )
        {
            assert( Abc_ObjRegular(pChild) == Abc_AigConst1(pMiter->pManFunc) );
            if ( !Abc_ObjIsComplement(pChild) )
            {
                // if the miter is constant 1, return immediately
                printf( "MITER IS CONSTANT 1!\n" );
                return 1;
            }
        }
        // if the miter is undecided (or satisfiable), return immediately
        else 
            return -1;
    }
    // return 0, meaning all outputs are constant zero
    return 0;
}

/**Function*************************************************************

  Synopsis    [Reports the status of the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMiterReport( Abc_Ntk_t * pMiter )
{
    Abc_Obj_t * pChild, * pNode;
    int i;
    if ( Abc_NtkPoNum(pMiter) == 1 )
    {
        pChild = Abc_ObjChild0( Abc_NtkPo(pMiter,0) );
        if ( Abc_NodeIsConst(Abc_ObjRegular(pChild)) )
        {
            if ( Abc_ObjIsComplement(pChild) )
                printf( "Unsatisfiable.\n" );
            else
                printf( "Satisfiable. (Constant 1).\n" );
        }
        else
            printf( "Satisfiable.\n" );
    }
    else
    {
        Abc_NtkForEachPo( pMiter, pNode, i )
        {
            pChild = Abc_ObjChild0( Abc_NtkPo(pMiter,i) );
            printf( "Output #%2d : ", i );
            if ( Abc_NodeIsConst(Abc_ObjRegular(pChild)) )
            {
                if ( Abc_ObjIsComplement(pChild) )
                    printf( "Unsatisfiable.\n" );
                else
                    printf( "Satisfiable. (Constant 1).\n" );
            }
            else
                printf( "Satisfiable.\n" );
        }
    }
}


/**Function*************************************************************

  Synopsis    [Derives the time frames of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFrames( Abc_Ntk_t * pNtk, int nFrames, int fInitial )
{
    int fCheck = 1;
    char Buffer[100];
    ProgressBar * pProgress;
    Abc_Ntk_t * pNtkFrames;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pLatch, * pLatchNew;
    int i;
    assert( nFrames > 0 );
    assert( Abc_NtkIsAig(pNtk) );
    // start the new network
    pNtkFrames = Abc_NtkAlloc( ABC_NTK_AIG );
    sprintf( Buffer, "%s_%d_frames", pNtk->pName, nFrames );
    pNtkFrames->pName = util_strsav(Buffer);
    // create new latches (or their initial values) and remember them in the new latches
    if ( !fInitial )
    {
        Abc_NtkForEachLatch( pNtk, pLatch, i )
            Abc_NtkDupObj( pNtkFrames, pLatch );
    }
    else
    {
        Abc_NtkForEachLatch( pNtk, pLatch, i )
            pLatch->pCopy = Abc_ObjNotCond( Abc_AigConst1(pNtkFrames->pManFunc), ((int)pLatch->pData)!=1 );
    }
    
    // create the timeframes
    vNodes = Abc_NtkDfs( pNtk );
    pProgress = Extra_ProgressBarStart( stdout, nFrames );
    for ( i = 0; i < nFrames; i++ )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        Abc_NtkAddFrame( pNtkFrames, pNtk, i, vNodes );
    }
    Extra_ProgressBarStop( pProgress );
    Vec_PtrFree( vNodes );
    
    // connect the new latches to the outputs of the last frame
    if ( !fInitial )
    {
        Abc_NtkForEachLatch( pNtk, pLatch, i )
        {
            pLatchNew = Abc_NtkLatch(pNtkFrames, i);
            Abc_ObjAddFanin( pLatchNew, Abc_ObjFanin0(pLatch)->pCopy );
            Vec_PtrPush( pNtkFrames->vPis, pLatchNew );
            Vec_PtrPush( pNtkFrames->vPos, pLatchNew );
            Abc_NtkLogicStoreName( pLatchNew, pNtk->vNamesLatch->pArray[i] );
        }
        assert( pNtkFrames->vPis->nSize == pNtkFrames->vNamesPi->nSize );
        assert( pNtkFrames->vPos->nSize == pNtkFrames->vNamesPo->nSize );
    }
    // make sure that everything is okay
    if ( fCheck && !Abc_NtkCheck( pNtkFrames ) )
    {
        printf( "Abc_NtkFrames: The network check has failed.\n" );
        Abc_NtkDelete( pNtkFrames );
        return NULL;
    }
    return pNtkFrames;
}

/**Function*************************************************************

  Synopsis    [Adds one time frame to the new network.]

  Description [Assumes that the latches of the old network point
  to the outputs of the previous frame of the new network (pLatch->pCopy). 
  In the end, updates the latches of the old network to point to the 
  outputs of the current frame of the new network.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkAddFrame( Abc_Ntk_t * pNtkFrames, Abc_Ntk_t * pNtk, int iFrame, Vec_Ptr_t * vNodes )
{
    char Buffer[10];
    Abc_Obj_t * pNode, * pNodeNew, * pLatch;
    Abc_Obj_t * pConst1, * pConst1New;
    int i;
    // get the constant nodes
    pConst1    = Abc_AigConst1( pNtk->pManFunc );
    pConst1New = Abc_AigConst1( pNtkFrames->pManFunc );
    // create the prefix to be added to the node names
    sprintf( Buffer, "_%02d", iFrame );
    // add the new PI nodes
    Abc_NtkForEachPi( pNtk, pNode, i )
    {
        pNodeNew = Abc_NtkDupObj( pNtkFrames, pNode );       
        Abc_NtkLogicStoreNamePlus( pNodeNew, pNtk->vNamesPi->pArray[i], Buffer );
    }
    // add the internal nodes
    for ( i = 0; i < vNodes->nSize; i++ )
    {
        pNode = vNodes->pArray[i];
        if ( pNode == pConst1 )
            pNodeNew = pConst1New;
        else
            pNodeNew = Abc_AigAnd( pNtkFrames->pManFunc, 
                Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) ),
                Abc_ObjNotCond( Abc_ObjFanin1(pNode)->pCopy, Abc_ObjFaninC1(pNode) ) );
        pNode->pCopy = pNodeNew;
    }
    // add the new POs
    Abc_NtkForEachPo( pNtk, pNode, i )
    {
        pNodeNew = Abc_NtkDupObj( pNtkFrames, pNode );       
        Abc_ObjAddFanin( pNodeNew, Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) ) );
        Abc_NtkLogicStoreNamePlus( pNodeNew, pNtk->vNamesPo->pArray[i], Buffer );
    }
    // transfer the implementation of the latch drivers to the latches
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        pLatch->pCopy = Abc_ObjNotCond( Abc_ObjFanin0(pLatch)->pCopy, Abc_ObjFaninC0(pLatch) );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


