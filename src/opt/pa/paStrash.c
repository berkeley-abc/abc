/**CFile****************************************************************

  FileName    [paStrash.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [AIG construction: strashing with coordinate transfer.]

  Author      [Anqi Lu, from abcStrash.c by Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paStrash.c,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "paInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Strashes the network and records the mapped cell of every new AIG node.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Pa_NtkStrash( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pAig;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int i;
    if ( Abc_NtkIsStrash(pNtk) )
        return Abc_NtkRestrash(pNtk, 1);
    if ( !Abc_NtkToAig(pNtk) )
        return NULL;
    pAig = Abc_NtkStartFrom(pNtk, ABC_NTK_STRASH, ABC_FUNC_AIG);
    vNodes = Abc_NtkDfsIter(pNtk, 0);
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pNode, i )
    {
        if ( Abc_ObjIsBarBuf(pNode) )
            pNode->pCopy = Abc_ObjChild0Copy(pNode);
        else
        {
            pNode->pCopy = Abc_NodeStrash(pAig, pNode, 0);
            Pa_ManCaptureUnmappedCell(pNode);
        }
    }
    Vec_PtrFree(vNodes);
    Abc_NtkFinalize(pNtk, pAig);
    if ( pNtk->vNameIds )
        Abc_NtkTransferNameIds(pNtk, pAig);
    Abc_AigCleanup((Abc_Aig_t *)pAig->pManFunc);
    if ( pNtk->pExdc )
        pAig->pExdc = Abc_NtkStrash(pNtk->pExdc, 0, 1, 0);
    if ( !Abc_NtkCheck(pAig) )
    {
        Abc_NtkDelete(pAig);
        return NULL;
    }
    return pAig;
}
/**Function*************************************************************

  Synopsis    [Creates the AIG nodes of a decomposition graph.]

  Description [Calls Dec_GraphToNetwork() of decAbc.c, which dec.h does not
               declare. Declared in this C file, it has the linkage of
               decAbc.c in every build mode, which a C++ caller cannot match.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Pa_GraphToNetwork( Abc_Ntk_t * pNtk, Dec_Graph_t * pGraph )
{
    extern Abc_Obj_t * Dec_GraphToNetwork( Abc_Ntk_t * pNtk, Dec_Graph_t * pGraph );
    return Dec_GraphToNetwork( pNtk, pGraph );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
