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
static void        Abc_NtkMiterAddCone( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkMiter, Abc_Obj_t * pNode );
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
    // check that the networks have the same PIs/POs/latches
    if ( !Abc_NtkCompareSignals( pNtk1, pNtk2, fComb ) )
        return NULL;
    // make sure the circuits are strashed 
    fRemove1 = (!Abc_NtkIsStrash(pNtk1)) && (pNtk1 = Abc_NtkStrash(pNtk1, 0, 0));
    fRemove2 = (!Abc_NtkIsStrash(pNtk2)) && (pNtk2 = Abc_NtkStrash(pNtk2, 0, 0));
    if ( pNtk1 && pNtk2 )
        pTemp = Abc_NtkMiterInt( pNtk1, pNtk2, fComb );
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
    char Buffer[100];
    Abc_Ntk_t * pNtkMiter;

    assert( Abc_NtkIsStrash(pNtk1) );
    assert( Abc_NtkIsStrash(pNtk2) );

    // start the new network
    pNtkMiter = Abc_NtkAlloc( ABC_TYPE_STRASH, ABC_FUNC_AIG );
    sprintf( Buffer, "%s_%s_miter", pNtk1->pName, pNtk2->pName );
    pNtkMiter->pName = util_strsav(Buffer);

    // perform strashing
    Abc_NtkMiterPrepare( pNtk1, pNtk2, pNtkMiter, fComb );
    Abc_NtkMiterAddOne( pNtk1, pNtkMiter );
    Abc_NtkMiterAddOne( pNtk2, pNtkMiter );
    Abc_NtkMiterFinalize( pNtk1, pNtk2, pNtkMiter, fComb );
    Abc_AigCleanup(pNtkMiter->pManFunc);

    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkMiter ) )
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
//    Abc_NtkCleanCopy( pNtk1 );
//    Abc_NtkCleanCopy( pNtk2 );
    if ( fComb )
    {
        // create new PIs and remember them in the old PIs
        Abc_NtkForEachCi( pNtk1, pObj, i )
        {
            pObjNew = Abc_NtkCreatePi( pNtkMiter );
            // remember this PI in the old PIs
            pObj->pCopy = pObjNew;
            pObj = Abc_NtkCi(pNtk2, i);  
            pObj->pCopy = pObjNew;
            // add name
            Abc_NtkLogicStoreName( pObjNew, Abc_ObjName(pObj) );
        }
        // create the only PO
        pObjNew = Abc_NtkCreatePo( pNtkMiter );
        // add the PO name
        Abc_NtkLogicStoreName( pObjNew, "miter" );
    }
    else
    {
        // create new PIs and remember them in the old PIs
        Abc_NtkForEachPi( pNtk1, pObj, i )
        {
            pObjNew = Abc_NtkCreatePi( pNtkMiter );
            // remember this PI in the old PIs
            pObj->pCopy = pObjNew;
            pObj = Abc_NtkPi(pNtk2, i);  
            pObj->pCopy = pObjNew;
            // add name
            Abc_NtkLogicStoreName( pObjNew, Abc_ObjName(pObj) );
        }
        // create the only PO
        pObjNew = Abc_NtkCreatePo( pNtkMiter );
        // add the PO name
        Abc_NtkLogicStoreName( pObjNew, "miter" );
        // create the latches
        Abc_NtkForEachLatch( pNtk1, pObj, i )
        {
            pObjNew = Abc_NtkDupObj( pNtkMiter, pObj );
            Vec_PtrPush( pNtkMiter->vCis, pObjNew );
            Vec_PtrPush( pNtkMiter->vCos, pObjNew );
            // add name
            Abc_NtkLogicStoreNamePlus( pObjNew, Abc_ObjName(pObj), "_1" );
        }
        Abc_NtkForEachLatch( pNtk2, pObj, i )
        {
            pObjNew = Abc_NtkDupObj( pNtkMiter, pObj );
            Vec_PtrPush( pNtkMiter->vCis, pObjNew );
            Vec_PtrPush( pNtkMiter->vCos, pObjNew );
            // add name
            Abc_NtkLogicStoreNamePlus( pObjNew, Abc_ObjName(pObj), "_2" );
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
    Abc_Obj_t * pNode, * pConst1, * pConst1New;
    int i;
    // get the constant nodes
    pConst1    = Abc_AigConst1( pNtk->pManFunc );
    pConst1New = Abc_AigConst1( pNtkMiter->pManFunc );
    // perform strashing
    vNodes = Abc_NtkDfs( pNtk, 0 );
    pProgress = Extra_ProgressBarStart( stdout, vNodes->nSize );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        if ( pNode == pConst1 )
            pNode->pCopy = pConst1New;
        else
            pNode->pCopy = Abc_AigAnd( pNtkMiter->pManFunc, Abc_ObjChild0Copy(pNode), Abc_ObjChild1Copy(pNode) );
    }
    Vec_PtrFree( vNodes );
    Extra_ProgressBarStop( pProgress );
}

/**Function*************************************************************

  Synopsis    [Performs mitering for one network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkMiterAddCone( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkMiter, Abc_Obj_t * pRoot )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode, * pNodeNew, * pConst1, * pConst1New;
    int i;
    // get the constant nodes
    pConst1    = Abc_AigConst1( pNtk->pManFunc );
    pConst1New = Abc_AigConst1( pNtkMiter->pManFunc );
    // perform strashing
    vNodes = Abc_NtkDfsNodes( pNtk, &pRoot, 1 );
    for ( i = 0; i < vNodes->nSize; i++ )
    {
        pNode = vNodes->pArray[i];
        if ( pNode == pConst1 )
            pNodeNew = pConst1New;
        else
            pNodeNew = Abc_AigAnd( pNtkMiter->pManFunc, Abc_ObjChild0Copy(pNode), Abc_ObjChild1Copy(pNode) );
        pNode->pCopy = pNodeNew;
    }
    Vec_PtrFree( vNodes );
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
    Abc_Obj_t * pMiter, * pNode;
    int i;
    // collect the PO pairs from both networks
    vPairs = Vec_PtrAlloc( 100 );
    if ( fComb )
    {
        // collect the CO nodes for the miter
        Abc_NtkForEachCo( pNtk1, pNode, i )
        {
            Vec_PtrPush( vPairs, Abc_ObjChild0Copy(pNode) );
            pNode = Abc_NtkCo( pNtk2, i );
            Vec_PtrPush( vPairs, Abc_ObjChild0Copy(pNode) );
        }
    }
    else
    {
        // collect the PO nodes for the miter
        Abc_NtkForEachPo( pNtk1, pNode, i )
        {
            Vec_PtrPush( vPairs, Abc_ObjChild0Copy(pNode) );
            pNode = Abc_NtkPo( pNtk2, i );
            Vec_PtrPush( vPairs, Abc_ObjChild0Copy(pNode) );
        }
        // connect new latches
        Abc_NtkForEachLatch( pNtk1, pNode, i )
            Abc_ObjAddFanin( pNode->pCopy, Abc_ObjChild0Copy(pNode) );
        Abc_NtkForEachLatch( pNtk2, pNode, i )
            Abc_ObjAddFanin( pNode->pCopy, Abc_ObjChild0Copy(pNode) );
    }
    // add the miter
    pMiter = Abc_AigMiter( pNtkMiter->pManFunc, vPairs );
    Abc_ObjAddFanin( Abc_NtkPo(pNtkMiter,0), pMiter );
    Vec_PtrFree( vPairs );
}




/**Function*************************************************************

  Synopsis    [Derives the miter of two cofactors of one output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkMiterForCofactors( Abc_Ntk_t * pNtk, int Out, int In1, int In2 )
{
    char Buffer[100];
    Abc_Ntk_t * pNtkMiter;
    Abc_Obj_t * pRoot, * pOutput1, * pOutput2, * pMiter;

    assert( Abc_NtkIsStrash(pNtk) );
    assert( Out < Abc_NtkCoNum(pNtk) );
    assert( In1 < Abc_NtkCiNum(pNtk) );
    assert( In2 < Abc_NtkCiNum(pNtk) );

    // start the new network
    pNtkMiter = Abc_NtkAlloc( ABC_TYPE_STRASH, ABC_FUNC_AIG );
    sprintf( Buffer, "%s_miter", Abc_ObjName(Abc_NtkCo(pNtk, Out)) );
    pNtkMiter->pName = util_strsav(Buffer);

    // get the root output
    pRoot = Abc_NtkCo( pNtk, Out );

    // perform strashing
    Abc_NtkMiterPrepare( pNtk, pNtk, pNtkMiter, 1 );
    // set the first cofactor
    Abc_NtkCi(pNtk, In1)->pCopy = Abc_ObjNot( Abc_AigConst1(pNtkMiter->pManFunc) );
    if ( In2 >= 0 )
    Abc_NtkCi(pNtk, In2)->pCopy = Abc_AigConst1( pNtkMiter->pManFunc );
    // add the first cofactor
    Abc_NtkMiterAddCone( pNtk, pNtkMiter, pRoot );

    // save the output
    pOutput1 = Abc_ObjFanin0(pRoot)->pCopy;

    // set the second cofactor
    Abc_NtkCi(pNtk, In1)->pCopy = Abc_AigConst1( pNtkMiter->pManFunc );
    if ( In2 >= 0 )
    Abc_NtkCi(pNtk, In2)->pCopy = Abc_ObjNot( Abc_AigConst1(pNtkMiter->pManFunc) );
    // add the second cofactor
    Abc_NtkMiterAddCone( pNtk, pNtkMiter, pRoot );

    // save the output
    pOutput2 = Abc_ObjFanin0(pRoot)->pCopy;

    // create the miter of the two outputs
    pMiter = Abc_AigXor( pNtkMiter->pManFunc, pOutput1, pOutput2 );
    Abc_ObjAddFanin( Abc_NtkPo(pNtkMiter,0), pMiter );

    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkMiter ) )
    {
        printf( "Abc_NtkMiter: The network check has failed.\n" );
        Abc_NtkDelete( pNtkMiter );
        return NULL;
    }
    return pNtkMiter;
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
    assert( Abc_NtkIsStrash(pMiter) );
    Abc_NtkForEachPo( pMiter, pNodePo, i )
    {
        pChild = Abc_ObjChild0( Abc_NtkPo(pMiter,i) );
        if ( Abc_ObjIsNode(Abc_ObjRegular(pChild)) && Abc_NodeIsConst(pChild) )
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
        if ( Abc_ObjIsNode(Abc_ObjRegular(pChild)) && Abc_NodeIsConst(pChild) )
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
            if ( Abc_ObjIsNode(Abc_ObjRegular(pChild)) && Abc_NodeIsConst(pChild) )
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

  Synopsis    [Derives the timeframes of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFrames( Abc_Ntk_t * pNtk, int nFrames, int fInitial )
{
    char Buffer[100];
    ProgressBar * pProgress;
    Abc_Ntk_t * pNtkFrames;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pLatch, * pLatchNew;
    int i, Counter;
    assert( nFrames > 0 );
    assert( Abc_NtkIsStrash(pNtk) );
    // start the new network
    pNtkFrames = Abc_NtkAlloc( ABC_TYPE_STRASH, ABC_FUNC_AIG );
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
        Counter = 0;
        Abc_NtkForEachLatch( pNtk, pLatch, i )
        {
            if ( Abc_LatchIsInitDc(pLatch) ) // don't-care initial value - create a new PI
            {
                pLatch->pCopy = Abc_NtkCreatePi(pNtkFrames);
                Abc_NtkLogicStoreName( pLatch->pCopy, Abc_ObjName(pLatch) );
                Counter++;
            }
            else
                pLatch->pCopy = Abc_ObjNotCond( Abc_AigConst1(pNtkFrames->pManFunc), Abc_LatchIsInit0(pLatch) );
        }
        if ( Counter )
            printf( "Warning: %d uninitialized latches are replaced by free variables.\n", Counter );
    }
    
    // create the timeframes
    vNodes = Abc_NtkDfs( pNtk, 0 );
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
            Vec_PtrPush( pNtkFrames->vCis, pLatchNew );
            Vec_PtrPush( pNtkFrames->vCos, pLatchNew );
            Abc_NtkLogicStoreName( pLatchNew, Abc_ObjName(pLatch) );
        }
    }
    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkFrames ) )
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
        Abc_NtkLogicStoreNamePlus( pNodeNew, Abc_ObjName(pNode), Buffer );
    }
    // add the internal nodes
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        if ( pNode == pConst1 )
            pNodeNew = pConst1New;
        else
            pNodeNew = Abc_AigAnd( pNtkFrames->pManFunc, Abc_ObjChild0Copy(pNode), Abc_ObjChild1Copy(pNode) );
        pNode->pCopy = pNodeNew;
    }
    // add the new POs
    Abc_NtkForEachPo( pNtk, pNode, i )
    {
        pNodeNew = Abc_NtkDupObj( pNtkFrames, pNode );       
        Abc_ObjAddFanin( pNodeNew, Abc_ObjChild0Copy(pNode) );
        Abc_NtkLogicStoreNamePlus( pNodeNew, Abc_ObjName(pNode), Buffer );
    }
    // transfer the implementation of the latch drivers to the latches
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        pLatch->pCopy = Abc_ObjChild0Copy(pLatch);
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


