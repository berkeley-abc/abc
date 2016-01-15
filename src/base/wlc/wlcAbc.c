/**CFile****************************************************************

  FileName    [wlcAbc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcAbc.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"
#include "base/abc/abc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_NtkPrintInvStats( Wlc_Ntk_t * pNtk, Vec_Int_t * vInv, int fVerbose )
{
    Wlc_Obj_t * pObj;
    int i, k, nNum, nRange, nBits = 0;
    Wlc_NtkForEachCi( pNtk, pObj, i )
    {
        if ( pObj->Type != WLC_OBJ_FO )
            continue;
        nRange = Wlc_ObjRange(pObj);
        for ( k = 0; k < nRange; k++ )
        {
            nNum = Vec_IntEntry(vInv, nBits + k);
            if ( nNum )
                break;
        }
        if ( k == nRange )
        {
            nBits += nRange;
            continue;
        }
        printf( "%s[%d:%d] : ", Wlc_ObjName(pNtk, Wlc_ObjId(pNtk, pObj)), pObj->End, pObj->Beg );
        for ( k = 0; k < nRange; k++ )
        {
            nNum = Vec_IntEntry( vInv, nBits + k );
            if ( nNum == 0 )
                continue;
            printf( "  [%d] -> %d", k, nNum );
        }
        printf( "\n");
        nBits += nRange;
    }
    //printf( "%d %d\n", Vec_IntSize(vInv), nBits );
    assert( Vec_IntSize(vInv) == nBits );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Wlc_NtkGetInv( Wlc_Ntk_t * pNtk, Vec_Int_t * vInv, Vec_Str_t * vSop, int fVerbose )
{
    Wlc_Obj_t * pObj;
    int i, k, nNum, nRange, nBits = 0;
    Abc_Ntk_t * pMainNtk = NULL;
    Abc_Obj_t * pMainObj, * pMainTemp;
    char Buffer[5000];
    // start the network
    pMainNtk = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    // duplicate the name and the spec
    pMainNtk->pName = Extra_UtilStrsav(pNtk->pName);
    // create primary inputs
    Wlc_NtkForEachCi( pNtk, pObj, i )
    {
        if ( pObj->Type != WLC_OBJ_FO )
            continue;
        nRange = Wlc_ObjRange(pObj);
        for ( k = 0; k < nRange; k++ )
        {
            nNum = Vec_IntEntry(vInv, nBits + k);
            if ( nNum )
                break;
        }
        if ( k == nRange )
        {
            nBits += nRange;
            continue;
        }
        //printf( "%s[%d:%d] : ", Wlc_ObjName(pNtk, Wlc_ObjId(pNtk, pObj)), pObj->End, pObj->Beg );
        for ( k = 0; k < nRange; k++ )
        {
            nNum = Vec_IntEntry( vInv, nBits + k );
            if ( nNum == 0 )
                continue;
            //printf( "  [%d] -> %d", k, nNum );
            pMainObj = Abc_NtkCreatePi( pMainNtk );
            sprintf( Buffer, "%s[%d]", Wlc_ObjName(pNtk, Wlc_ObjId(pNtk, pObj)), k );
            Abc_ObjAssignName( pMainObj, Buffer, NULL );

        }
        //printf( "\n");
        nBits += nRange;
    }
    //printf( "%d %d\n", Vec_IntSize(vInv), nBits );
    assert( Vec_IntSize(vInv) == nBits );
    // create node
    pMainObj = Abc_NtkCreateNode( pMainNtk );
    Abc_NtkForEachPi( pMainNtk, pMainTemp, i )
        Abc_ObjAddFanin( pMainObj, pMainTemp );
    pMainObj->pData = Abc_SopRegister( (Mem_Flex_t *)pMainNtk->pManFunc, Vec_StrArray(vSop) );
    // create PO
    pMainTemp = Abc_NtkCreatePo( pMainNtk );
    Abc_ObjAddFanin( pMainTemp, pMainObj );
    Abc_ObjAssignName( pMainTemp, "inv", NULL );
    return pMainNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

