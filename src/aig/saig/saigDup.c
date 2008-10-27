/**CFile****************************************************************

  FileName    [saigDup.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Various duplication procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigDup.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Duplicates while ORing the POs of sequential circuit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Said_ManDupOrpos( Aig_Man_t * pAig )
{
    Aig_Man_t * pAigNew;
    Aig_Obj_t * pObj, * pMiter;
    int i;
    // start the new manager
    pAigNew = Aig_ManStart( Aig_ManNodeNum(pAig) );
    // map the constant node
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pAigNew );
    // create variables for PIs
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pAigNew );
    // add internal nodes of this frame
    Aig_ManForEachNode( pAig, pObj, i )
        pObj->pData = Aig_And( pAigNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create PO of the circuit
    pMiter = Aig_ManConst0( pAigNew );
    Saig_ManForEachPo( pAig, pObj, i )
        pMiter = Aig_Or( pAigNew, pMiter, Aig_ObjChild0Copy(pObj) );
    Aig_ObjCreatePo( pAigNew, pMiter );
    // transfer to register outputs
    Saig_ManForEachLi( pAig, pObj, i )
        Aig_ObjCreatePo( pAigNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManCleanup( pAigNew );
    Aig_ManSetRegNum( pAigNew, Aig_ManRegNum(pAig) );
    return pAigNew;
}

/**Function*************************************************************

  Synopsis    [Numbers of flops included in the abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManAbstraction( Aig_Man_t * pAig, Vec_Int_t * vFlops )
{
    Aig_Man_t * pAigNew;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, Entry;
    // start the new manager
    pAigNew = Aig_ManStart( Aig_ManNodeNum(pAig) );
    // map the constant node
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pAigNew );
    // label included flops
    Vec_IntForEachEntry( vFlops, Entry, i )
    {
        pObjLi = Saig_ManLi( pAig, Entry );
        assert( pObjLi->fMarkA == 0 );
        pObjLi->fMarkA = 1;
        pObjLo = Saig_ManLo( pAig, Entry );
        assert( pObjLo->fMarkA == 0 );
        pObjLo->fMarkA = 1;
    }
    // create variables for PIs
    Aig_ManForEachPi( pAig, pObj, i )
        if ( !pObj->fMarkA )
            pObj->pData = Aig_ObjCreatePi( pAigNew );
    // create variables for LOs
    Aig_ManForEachPi( pAig, pObj, i )
        if ( pObj->fMarkA )
        {
            pObj->fMarkA = 0;
            pObj->pData = Aig_ObjCreatePi( pAigNew );
        }
    // add internal nodes 
    Aig_ManForEachNode( pAig, pObj, i )
        pObj->pData = Aig_And( pAigNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create POs
    Saig_ManForEachPo( pAig, pObj, i )
        Aig_ObjCreatePo( pAigNew, Aig_ObjChild0Copy(pObj) );
    // create LIs
    Aig_ManForEachPo( pAig, pObj, i )
        if ( pObj->fMarkA )
        {
            pObj->fMarkA = 0;
            Aig_ObjCreatePo( pAigNew, Aig_ObjChild0Copy(pObj) );
        }
    Aig_ManSetRegNum( pAigNew, Vec_IntSize(vFlops) );
    Aig_ManSeqCleanup( pAigNew );
    return pAigNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


