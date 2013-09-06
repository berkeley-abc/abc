/**CFile****************************************************************

  FileName    [bmcBmcAnd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Memory-efficient BMC engine]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmcBmcAnd.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "aig/gia/giaAig.h"
#include "sat/bsat/satStore.h"
#include "sat/cnf/cnf.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Bmc_Mna_t_ Bmc_Mna_t; 
struct Bmc_Mna_t_
{
    Gia_Man_t *         pFrames;  // time frames
    Vec_Int_t *         vId2Var;  // maps GIA IDs into SAT vars
    Vec_Int_t *         vInputs;  // inputs of the cone
    Vec_Int_t *         vOutputs; // outputs of the cone
    Vec_Int_t *         vNodes;   // internal nodes of the cone
    sat_solver *        pSat;     // SAT solver
    int                 nSatVars; // the counter of SAT variables
    abctime             clkStart; // starting time
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [BMC manager manipulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Bmc_Mna_t * Bmc_MnaAlloc()
{
    Bmc_Mna_t * p;
    p = ABC_CALLOC( Bmc_Mna_t, 1 );
    p->vId2Var   = Vec_IntAlloc( 0 );
    p->vInputs   = Vec_IntAlloc( 1000 );
    p->vOutputs  = Vec_IntAlloc( 1000 );
    p->vNodes    = Vec_IntAlloc( 10000 );
    p->pSat      = sat_solver_new();
    p->nSatVars  = 1;
    p->clkStart  = Abc_Clock();
    return p;
}
void Bmc_MnaFree( Bmc_Mna_t * p )
{
    Vec_IntFreeP( &p->vId2Var );
    Vec_IntFreeP( &p->vInputs );
    Vec_IntFreeP( &p->vOutputs );
    Vec_IntFreeP( &p->vNodes );
    sat_solver_delete( p->pSat );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Derives GIA for the given cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManBmcDupCone( Gia_Man_t * p, Vec_Int_t * vIns, Vec_Int_t * vNodes, Vec_Int_t * vOuts )
{
    Gia_Man_t * pNew;
    Vec_Int_t * vTempIn, * vTempNode;
    Gia_Obj_t * pObj;
    int i;
    // save values
    vTempIn = Vec_IntAlloc( Vec_IntSize(vIns) );
    Gia_ManForEachObjVec( vIns, p, pObj, i )
        Vec_IntPush( vTempIn, pObj->Value );
    // save values
    vTempNode = Vec_IntAlloc( Vec_IntSize(vNodes) );
    Gia_ManForEachObjVec( vNodes, p, pObj, i )
        Vec_IntPush( vTempNode, pObj->Value );
    // derive new GIA
    pNew = Gia_ManDupFromVecs( p, vIns, vNodes, vOuts, 0 );
    // reset values
    Gia_ManForEachObjVec( vIns, p, pObj, i )
        pObj->Value = Vec_IntEntry( vTempIn, i );
    // reset values
    Gia_ManForEachObjVec( vNodes, p, pObj, i )
        pObj->Value = Vec_IntEntry( vTempNode, i );
    // reset values
    Gia_ManForEachObjVec( vOuts, p, pObj, i )
        pObj->Value = 0;
    Vec_IntFree( vTempIn );
    Vec_IntFree( vTempNode );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives GIA for the given cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManBmcAssignVarIds( Bmc_Mna_t * p, Vec_Int_t * vIns, Vec_Int_t * vUsed, Vec_Int_t * vOuts )
{
    int i, iObj, VarC0 = p->nSatVars++;
    Vec_IntForEachEntry( vIns, iObj, i )
        if ( Vec_IntEntry( p->vId2Var, iObj ) == 0 )
            Vec_IntWriteEntry( p->vId2Var, iObj, p->nSatVars++ );
    Vec_IntForEachEntryReverse( vUsed, iObj, i )
    {
        assert( Vec_IntEntry( p->vId2Var, iObj ) == 0 );
        Vec_IntWriteEntry( p->vId2Var, iObj, p->nSatVars++ );
    }
    Vec_IntForEachEntry( vOuts, iObj, i )
    {
        assert( Vec_IntEntry( p->vId2Var, iObj ) == 0 );
        Vec_IntWriteEntry( p->vId2Var, iObj, p->nSatVars++ );
    }
    // extend the SAT solver
    if ( p->nSatVars > sat_solver_nvars(p->pSat) )
        sat_solver_setnvars( p->pSat, p->nSatVars );
    return VarC0;
}

/**Function*************************************************************

  Synopsis    [Derives CNF for the given cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManBmcAddCnf( Bmc_Mna_t * p, Gia_Man_t * pGia, Vec_Int_t * vIns, Vec_Int_t * vNodes, Vec_Int_t * vOuts )
{
    Gia_Man_t * pNew = Gia_ManBmcDupCone( pGia, vIns, vNodes, vOuts );
    Aig_Man_t * pAig = Gia_ManToAigSimple( pNew );
    Cnf_Dat_t * pCnf = Cnf_Derive( pAig, Aig_ManCoNum(pAig) );
    Vec_Int_t * vUsed, * vMap;
    Gia_Obj_t * pObj;
    int i, iObj, VarC0;
    // collect used variables
    vUsed = Vec_IntAlloc( pCnf->nVars - Vec_IntSize(vIns) - Vec_IntSize(vOuts) );
    Gia_ManForEachAnd( pNew, pObj, i )
        if ( pCnf->pVarNums[i] >= 0 )
            Vec_IntPush( vUsed, Vec_IntEntry(vNodes, i - Vec_IntSize(vIns) - 1) );
    // assign variable IDs
    VarC0 = Gia_ManBmcAssignVarIds( p, vIns, vUsed, vOuts );
    Vec_IntFree( vUsed );
    // create variable map from CNF vars into SAT vars
    vMap = Vec_IntStartFull( pCnf->nVars );
    assert( pCnf->pVarNums[0] > 0 );
    Vec_IntWriteEntry( vMap, pCnf->pVarNums[0], VarC0 );
    Gia_ManForEachObj1( pNew, pObj, i )
    {
        if ( pCnf->pVarNums[i] < 0 )
            continue;
        assert( pCnf->pVarNums[i] >= 0 && pCnf->pVarNums[i] < pCnf->nVars );
        if ( Gia_ObjIsCi(pObj) )
            iObj = Vec_IntEntry( vIns, i - 1 );
        else if ( Gia_ObjIsAnd(pObj) )
            iObj = Vec_IntEntry( vNodes, i - Vec_IntSize(vIns) - 1 );
        else if ( Gia_ObjIsCo(pObj) )
            iObj = Vec_IntEntry( vOuts, i - Vec_IntSize(vIns) - Vec_IntSize(vNodes) - 1 );
        else assert( 0 );
        assert( Vec_IntEntry(p->vId2Var, iObj) > 0 );
        Vec_IntWriteEntry( vMap, pCnf->pVarNums[i], Vec_IntEntry(p->vId2Var, iObj) );
    }
//Vec_IntPrint( vMap );
    // remap CNF
    for ( i = 0; i < pCnf->nLiterals; i++ )
    {
        assert( pCnf->pClauses[0][i] > 1 && pCnf->pClauses[0][i] < 2 * pCnf->nVars );
        pCnf->pClauses[0][i] = Abc_Lit2LitV( Vec_IntArray(vMap), pCnf->pClauses[0][i] );
    }
    Vec_IntFree( vMap );
    // add clauses
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
/*
        int v;
        for ( v = 0; v < pCnf->pClauses[i+1] - pCnf->pClauses[i]; v++ )
            printf( "%d ", pCnf->pClauses[i][v] );
        printf( "\n" );
*/
        if ( !sat_solver_addclause( p->pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            break;
    }
    if ( i < pCnf->nClauses )
        printf( "SAT solver became UNSAT after adding clauses.\n" );
    Aig_ManStop( pAig );
    Cnf_DataFree( pCnf );
    Gia_ManStop( pNew );
}

/**Function*************************************************************

  Synopsis    [Collects new nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManBmcAddCone_rec( Bmc_Mna_t * p, Gia_Obj_t * pObj )
{
    int iObj;
    if ( pObj->fMark0 )
        return;
    pObj->fMark0 = 1;
    iObj = Gia_ObjId( p->pFrames, pObj );
    if ( Gia_ObjIsAnd(pObj) && Vec_IntEntry(p->vId2Var, iObj) == 0 )
    {
        Gia_ManBmcAddCone_rec( p, Gia_ObjFanin0(pObj) );
        Gia_ManBmcAddCone_rec( p, Gia_ObjFanin1(pObj) );
        Vec_IntPush( p->vNodes, iObj );
    }
    else
        Vec_IntPush( p->vInputs, iObj );
}
void Gia_ManBmcAddCone( Bmc_Mna_t * p, int iStart )
{
    Gia_Obj_t * pObj;
    int i;
    Vec_IntClear( p->vNodes );
    Vec_IntClear( p->vInputs );
    Vec_IntClear( p->vOutputs );
    Vec_IntFillExtra( p->vId2Var, Gia_ManObjNum(p->pFrames), 0 );
    for ( i = iStart; i < Gia_ManPoNum(p->pFrames); i++ )
    {
        pObj = Gia_ManPo(p->pFrames, i);
        if ( Gia_ObjChild0(pObj) == Gia_ManConst0(p->pFrames) )
            continue;
        Gia_ManBmcAddCone_rec( p, Gia_ObjFanin0(pObj) );
        Vec_IntPush( p->vOutputs, Gia_ObjId(p->pFrames, pObj) );
    }
    // clean attributes and create new variables
    Gia_ManForEachObjVec( p->vNodes, p->pFrames, pObj, i )
        pObj->fMark0 = 0;
    Gia_ManForEachObjVec( p->vInputs, p->pFrames, pObj, i )
        pObj->fMark0 = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManBmcCheckOutputs( Gia_Man_t * pFrames, int iStart )
{
    int i;
    for ( i = iStart; i < Gia_ManPoNum(pFrames); i++ )
        if ( Gia_ObjChild0(Gia_ManPo(pFrames, i)) != Gia_ManConst0(pFrames) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManBmcPerform( Gia_Man_t * pGia, Bmc_AndPar_t * pPars )
{
    Unr_Man_t * pUnroll;
    Bmc_Mna_t * p = Bmc_MnaAlloc();
    int nFramesMax = pPars->nFramesMax ? pPars->nFramesMax : ABC_INFINITY;
    int f, i, Lit, status, RetValue = -2;
    pUnroll = Unr_ManUnrollStart( pGia, pPars->fVeryVerbose );
    for ( f = 0; f < nFramesMax; f++ )
    {
        p->pFrames = Unr_ManUnrollFrame( pUnroll, f );
        if ( !Gia_ManBmcCheckOutputs( p->pFrames, f * Gia_ManPoNum(pGia) ) )
        {
            // create another slice
            Gia_ManBmcAddCone( p, f * Gia_ManPoNum(pGia) );
            // create CNF in the SAT solver
            Gia_ManBmcAddCnf( p, p->pFrames, p->vInputs, p->vNodes, p->vOutputs );
            // try solving the outputs
            for ( i = f * Gia_ManPoNum(pGia); i < Gia_ManPoNum(p->pFrames); i++ )
            {
                Gia_Obj_t * pObj = Gia_ManPo(p->pFrames, i);
                if ( Gia_ObjChild0(pObj) == Gia_ManConst0(p->pFrames) )
                    continue;
                Lit = Abc_Var2Lit( Vec_IntEntry(p->vId2Var, Gia_ObjId(p->pFrames, pObj)), 0 );
                status = sat_solver_solve( p->pSat, &Lit, &Lit + 1, (ABC_INT64_T)pPars->nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
                if ( status == l_False ) // unsat
                    continue;
                if ( status == l_True ) // sat
                    RetValue = 0;
                if ( status == l_Undef ) // undecided
                    RetValue = -1;
                break;
            }
        }
        // report statistics
        if ( pPars->fVerbose )
        {
            printf( "%4d :  PI =%9d.  AIG =%9d.  Var =%8d.  In =%6d.  And =%9d.  Cla =%9d.  Conf =%9d.  Mem =%7.1f MB   ", 
                f, Gia_ManPiNum(p->pFrames), Gia_ManAndNum(p->pFrames), 
                p->nSatVars-1, Vec_IntSize(p->vInputs), Vec_IntSize(p->vNodes), 
                sat_solver_nclauses(p->pSat), sat_solver_nconflicts(p->pSat), Gia_ManMemory(p->pFrames) );
            Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
        }
        if ( RetValue != -2 )
        {
            if ( RetValue == -1 )
                printf( "SAT solver reached conflict/runtime limit in frame %d.\n", f );
            else
            {
                printf( "Output %d of miter \"%s\" was asserted in frame %d.  ", 
                    i - f * Gia_ManPoNum(pGia), Gia_ManName(pGia), f );
                Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
            }
            break;
        }
    }
    if ( RetValue == -2 )
        RetValue = -1;
    // dump unfolded frames
    if ( pPars->fDumpFrames )
    {
        p->pFrames = Gia_ManCleanup( p->pFrames );
        Gia_AigerWrite( p->pFrames, "frames.aig", 0, 0 );
        printf( "Dumped unfolded frames into file \"frames.aig\".\n" );
        Gia_ManStop( p->pFrames );
    }
    // cleanup
    Unr_ManFree( pUnroll );
    Bmc_MnaFree( p );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

