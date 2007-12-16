/**CFile****************************************************************

  FileName    [ntlMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Derives mapped network from AIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlMap.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates mapping for the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_MappingAlloc( int nLuts, int nVars )
{
    char * pMemory;
    Ntl_Lut_t ** pArray;
    int nEntrySize, i;
    nEntrySize = sizeof(Ntl_Lut_t) + sizeof(int) * nVars + sizeof(unsigned) * Aig_TruthWordNum(nVars);
    pArray = (Ntl_Lut_t **)malloc( (sizeof(Ntl_Lut_t *) + nEntrySize) * nLuts );
    pMemory = (char *)(pArray + nLuts);
    memset( pMemory, 0, nEntrySize * nLuts );
    for ( i = 0; i < nLuts; i++ )
    {
        pArray[i] = (Ntl_Lut_t *)pMemory;
        pArray[i]->pFanins = (int *)(pMemory + sizeof(Ntl_Lut_t));
        pArray[i]->pTruth = (unsigned *)(pMemory + sizeof(Ntl_Lut_t) + sizeof(int) * nVars);
        pMemory += nEntrySize;
    }
    return Vec_PtrAllocArray( (void **)pArray, nLuts );
}

/**Function*************************************************************

  Synopsis    [Derives trivial mapping from the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntl_MappingFromAig( Aig_Man_t * p )
{
    Vec_Ptr_t * vMapping;
    Ntl_Lut_t * pLut;
    Aig_Obj_t * pObj;
    int i, k = 0, nBytes = 4;
    vMapping = Ntl_MappingAlloc( Aig_ManAndNum(p) + (int)(Aig_ManConst1(p)->nRefs > 0), 2 );
    if ( Aig_ManConst1(p)->nRefs > 0 )
    {
        pLut = Vec_PtrEntry( vMapping, k++ );
        pLut->Id = 0;
        pLut->nFanins = 0;
        memset( pLut->pTruth, 0xFF, nBytes );
    }
    Aig_ManForEachNode( p, pObj, i )
    {
        pLut = Vec_PtrEntry( vMapping, k++ );
        pLut->Id = pObj->Id;
        pLut->nFanins = 2;
        pLut->pFanins[0] = Aig_ObjFaninId0(pObj);
        pLut->pFanins[1] = Aig_ObjFaninId1(pObj);
        if      (  Aig_ObjFaninC0(pObj) &&  Aig_ObjFaninC1(pObj) ) 
            memset( pLut->pTruth, 0x11, nBytes );
        else if ( !Aig_ObjFaninC0(pObj) &&  Aig_ObjFaninC1(pObj) )
            memset( pLut->pTruth, 0x22, nBytes );
        else if (  Aig_ObjFaninC0(pObj) && !Aig_ObjFaninC1(pObj) )
            memset( pLut->pTruth, 0x44, nBytes );
        else if ( !Aig_ObjFaninC0(pObj) && !Aig_ObjFaninC1(pObj) )
            memset( pLut->pTruth, 0x88, nBytes );
    }
    assert( k == Vec_PtrSize(vMapping) );
    return vMapping;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


