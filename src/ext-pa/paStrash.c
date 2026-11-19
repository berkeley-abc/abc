/* Strashing with mapped-cell coordinate transfer. Based on ABC strash. */
#include "base/abc/abc.h"
#include "ext-pa/paPlace.h"
ABC_NAMESPACE_IMPL_START
static void Pa_NtkStrashPerform( Abc_Ntk_t * pOld, Abc_Ntk_t * pNew, int fAllNodes, int fRecord )
{
    Vec_Ptr_t * vNodes = Abc_NtkDfsIter(pOld, fAllNodes);
    Abc_Obj_t * pNode;
    int i;
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pNode, i )
    {
        if ( Abc_ObjIsBarBuf(pNode) )
            pNode->pCopy = Abc_ObjChild0Copy(pNode);
        else
        {
            pNode->pCopy = Abc_NodeStrash(pNew, pNode, fRecord);
            Pa_ManCaptureUnmappedCell(pNode);
        }
    }
    Vec_PtrFree(vNodes);
}
Abc_Ntk_t * Pa_NtkStrash( Abc_Ntk_t * pNtk, int fAllNodes, int fCleanup, int fRecord )
{
    Abc_Ntk_t * pAig;
    if ( Abc_NtkIsStrash(pNtk) )
        return Abc_NtkRestrash(pNtk, fCleanup);
    if ( !Abc_NtkToAig(pNtk) )
        return NULL;
    pAig = Abc_NtkStartFrom(pNtk, ABC_NTK_STRASH, ABC_FUNC_AIG);
    Pa_NtkStrashPerform(pNtk, pAig, fAllNodes, fRecord);
    Abc_NtkFinalize(pNtk, pAig);
    if ( pNtk->vNameIds )
        Abc_NtkTransferNameIds(pNtk, pAig);
    if ( fCleanup )
        Abc_AigCleanup((Abc_Aig_t *)pAig->pManFunc);
    if ( pNtk->pExdc )
        pAig->pExdc = Abc_NtkStrash(pNtk->pExdc, fAllNodes, fCleanup, fRecord);
    if ( !Abc_NtkCheck(pAig) )
    {
        Abc_NtkDelete(pAig);
        return NULL;
    }
    return pAig;
}
ABC_NAMESPACE_IMPL_END
