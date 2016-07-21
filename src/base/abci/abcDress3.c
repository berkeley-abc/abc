/**CFile****************************************************************

  FileName    [abcDress3.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Transfers names from one netlist to the other.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcDress3.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "base/io/ioAbc.h"
#include "proof/cec/cec.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Compute equivalence classes of nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkComputeGiaEquivs( Gia_Man_t * pGia, int nConfs, int fVerbose )
{
    Gia_Man_t * pTemp;
    Cec_ParFra_t ParsFra, * pPars = &ParsFra;
    Cec_ManFraSetDefaultParams( pPars );
    pPars->fUseOrigIds = 1;
    pPars->fSatSweeping = 1;
    pPars->nBTLimit = nConfs;
    pPars->fVerbose = fVerbose;
    pTemp = Cec_ManSatSweeping( pGia, pPars, 0 );
    Gia_ManStop( pTemp );
    pTemp = Gia_ManOrigIdsReduce( pGia, pGia->vIdsEquiv );
    Gia_ManStop( pTemp );
}

/**Function*************************************************************

  Synopsis    [Add logic from pNtk to the AIG manager p.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkAigToGiaOne( Gia_Man_t * p, Abc_Ntk_t * pNtk )
{
    extern int Abc_ConvertAigToGia( Gia_Man_t * p, Hop_Obj_t * pRoot );
    Hop_Man_t * pHopMan;
    Hop_Obj_t * pHopObj;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode, * pFanin;
    int i, k;
    assert( Abc_NtkIsAigLogic(pNtk) );
    pHopMan = (Hop_Man_t *)pNtk->pManFunc;
    Hop_ManConst1(pHopMan)->iData = 1;
    // image primary inputs
    Abc_NtkCleanCopy( pNtk );
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->iTemp = Gia_ManCiLit(p, i);
    // iterate through nodes used in the mapping
    vNodes = Abc_NtkDfs( pNtk, 0 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pNode, i )
    {
        Abc_ObjForEachFanin( pNode, pFanin, k )
            Hop_ManPi(pHopMan, k)->iData = pFanin->iTemp;
        pHopObj = Hop_Regular( (Hop_Obj_t *)pNode->pData );
        assert( Abc_ObjFaninNum(pNode) <= Hop_ManPiNum(pHopMan) );
        if ( Hop_DagSize(pHopObj) > 0 )
            Abc_ConvertAigToGia( p, pHopObj );
        pNode->iTemp = Abc_LitNotCond( pHopObj->iData, Hop_IsComplement( (Hop_Obj_t *)pNode->pData ) );
    }
    Vec_PtrFree( vNodes );
    // create primary outputs
    Abc_NtkForEachCo( pNtk, pNode, i )
        Gia_ManAppendCo( p, Abc_ObjFanin0(pNode)->iTemp );
}
Gia_Man_t * Abc_NtkAigToGiaTwo( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 )
{
    Gia_Man_t * p;
    Gia_Obj_t * pObj;
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsAigLogic(pNtk1) );
    assert( Abc_NtkIsAigLogic(pNtk2) );
    // create new manager
    p = Gia_ManStart( 10000 );
    p->pName = Abc_UtilStrsav( Abc_NtkName(pNtk1) );
    p->pSpec = Abc_UtilStrsav( Abc_NtkSpec(pNtk1) );
    Abc_NtkForEachCi( pNtk1, pNode, i )
        Gia_ManAppendCi(p);
    // add logic
    Gia_ManHashAlloc( p );
    Abc_NtkAigToGiaOne( p, pNtk1 );
    Abc_NtkAigToGiaOne( p, pNtk2 );
    Gia_ManHashStop( p );
    // add extra POs to dangling nodes
    Gia_ManCreateValueRefs( p );
    Gia_ManForEachAnd( p, pObj, i )
        if ( pObj->Value == 0 )
            Gia_ManAppendCo( p, Abc_Var2Lit(i, 0) );
    return p;
}

/**Function*************************************************************

  Synopsis    [Collect equivalence class information.]

  Description [Each class is represented as follows: 
      <num_entries><entry1><entry2>...<entryN> 
  where <entry> is nodeId with 1-bit for complement and 1-bit for network.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_NtkCollectAddOne( int iNtk, int iObj, int iGiaLit, Gia_Man_t * pGia, Vec_Int_t * vGia2Cla, Vec_Int_t * vNexts[2] )
{
    int iRepr = Gia_ObjReprSelf( pGia, Abc_Lit2Var(iGiaLit) );
    int Compl = Abc_LitIsCompl(iGiaLit) ^ Gia_ObjPhase(Gia_ManObj(pGia, iRepr)) ^ Gia_ObjPhase(Gia_ManObj(pGia, Abc_Lit2Var(iGiaLit)));
    int Added = Abc_Var2Lit( Abc_Var2Lit(iObj, Compl), iNtk );
    int Entry = Vec_IntEntry( vGia2Cla, iRepr );
    Vec_IntWriteEntry( vNexts[iNtk], iObj, Entry );
    Vec_IntWriteEntry( vGia2Cla, iRepr, Added );
}
Vec_Int_t * Abc_NtkCollectEquivClasses( Abc_Ntk_t * pNtks[2], Gia_Man_t * pGia )
{
    Vec_Int_t * vClass = Vec_IntAlloc( 100 );
    Vec_Int_t * vClasses = Vec_IntAlloc( 1000 );
    Vec_Int_t * vGia2Cla = Vec_IntStartFull( Gia_ManObjNum(pGia) ); // mapping objId into classId
    Vec_Int_t * vNexts[2] = { Vec_IntStartFull(Abc_NtkObjNumMax(pNtks[0])), Vec_IntStartFull(Abc_NtkObjNumMax(pNtks[1])) };
    Abc_Obj_t * pObj;
    int n, i, k, Entry, fCompl;
    Abc_NtkForEachCi( pNtks[0], pObj, i )
        Abc_NtkCollectAddOne( 0, Abc_ObjId(pObj), pObj->iTemp, pGia, vGia2Cla, vNexts );
    for ( n = 0; n < 2; n++ )
        Abc_NtkForEachNode( pNtks[n], pObj, i )
            Abc_NtkCollectAddOne( n, Abc_ObjId(pObj), pObj->iTemp, pGia, vGia2Cla, vNexts );
    Vec_IntForEachEntry( vGia2Cla, Entry, i )
    {
        Vec_IntClear( vClass );
        for ( ; Entry >= 0; Entry = Vec_IntEntry(vNexts[Entry&1], Entry>>2) )
            Vec_IntPush( vClass, Entry );
        if ( Vec_IntSize(vClass) < 2 )
            continue;
        Vec_IntReverseOrder( vClass );
        fCompl = 2 & Vec_IntEntry( vClass, 0 );
        Vec_IntForEachEntry( vClass, Entry, k )
            Vec_IntWriteEntry( vClass, k, Entry ^ fCompl );        
        Vec_IntPush( vClasses, Vec_IntSize(vClass) );
        Vec_IntAppend( vClasses, vClass );
    }
    Vec_IntFree( vGia2Cla );
    Vec_IntFree( vNexts[0] );
    Vec_IntFree( vNexts[1] );
    Vec_IntFree( vClass );
    return vClasses;
}

/**Function*************************************************************

  Synopsis    [Write the output file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDumpEquivFile( char * pFileName, Vec_Int_t * vClasses, Abc_Ntk_t * pNtks[2] )
{
    int i, c, k, Entry;
    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL ) { printf( "Cannot open file %s for writing.\n", pFileName ); return; }
    fprintf( pFile, "# Node equivalences computed by ABC for networks \"%s\" and \"%s\" on %s\n\n", Abc_NtkName(pNtks[0]), Abc_NtkName(pNtks[1]), Extra_TimeStamp() );
    for ( i = c = 0; i < Vec_IntSize(vClasses); c++, i += 1 + Vec_IntEntry(vClasses, i) )
    {
        Vec_IntForEachEntryStartStop( vClasses, Entry, k, i + 1, i + 1 + Vec_IntEntry(vClasses, i) )
        {
            Abc_Ntk_t * pNtk = pNtks[Entry & 1];
            char * pObjName = Abc_ObjName( Abc_NtkObj(pNtk, Entry>>2) );
            fprintf( pFile, "%d:%s:%s%s\n", c+1, Abc_NtkName(pNtk), (Entry&2) ? "NOT:":"", pObjName );
        }
        fprintf( pFile, "\n" );
    }
    fclose( pFile );
}


/**Function*************************************************************

  Synopsis    [Compute and dump equivalent name classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDumpEquiv( Abc_Ntk_t * pNtks[2], char * pFileName, int nConfs, int fVerbose )
{
    //abctime clk = Abc_Clock();
    Vec_Int_t * vClasses;
    // derive shared AIG for the two networks
    Gia_Man_t * pGia = Abc_NtkAigToGiaTwo( pNtks[0], pNtks[1] );
    if ( fVerbose )
        printf( "Computing equivalences for networks \"%s\" and \"%s\" with conflict limit %d.\n", Abc_NtkName(pNtks[0]), Abc_NtkName(pNtks[1]), nConfs );
    // compute equivalences in this AIG
    Abc_NtkComputeGiaEquivs( pGia, nConfs, fVerbose );
    //if ( fVerbose )
    //    Abc_PrintTime( 1, "Equivalence computation time", Abc_Clock() - clk );
    if ( fVerbose )
        Gia_ManPrintStats( pGia, NULL );
    // collect equivalence class information
    vClasses = Abc_NtkCollectEquivClasses( pNtks, pGia );
    Gia_ManStop( pGia );
    // dump information into the output file
    Abc_NtkDumpEquivFile( pFileName, vClasses, pNtks );
    Vec_IntFree( vClasses );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

