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

  Synopsis    []

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

  Synopsis    [Returns 1 if all outputs are trivial.]

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

  Synopsis    [Collects new nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManBmcAndCone_rec( Bmc_Mna_t * p, Gia_Obj_t * pObj )
{
    int iObj;
    if ( pObj->fMark0 )
        return;
    pObj->fMark0 = 1;
    iObj = Gia_ObjId( p->pFrames, pObj );
    if ( Gia_ObjIsAnd(pObj) && Vec_IntEntry(p->vId2Var, iObj) == 0 )
    {
        Gia_ManBmcAndCone_rec( p, Gia_ObjFanin0(pObj) );
        Gia_ManBmcAndCone_rec( p, Gia_ObjFanin1(pObj) );
        Vec_IntPush( p->vNodes, iObj );
    }
    else
        Vec_IntPush( p->vInputs, iObj );
}
void Gia_ManBmcAndCone( Bmc_Mna_t * p, int iStart )
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
        Gia_ManBmcAndCone_rec( p, Gia_ObjFanin0(pObj) );
        Vec_IntPush( p->vOutputs, Gia_ObjId(p->pFrames, pObj) );
    }
    // clean attributes and create new variables
    Gia_ManForEachObjVec( p->vInputs, p->pFrames, pObj, i )
    {
        int iObj = Vec_IntEntry(p->vInputs, i);
        pObj->fMark0 = 0;
        if ( Vec_IntEntry( p->vId2Var, iObj ) == 0 )
            Vec_IntWriteEntry( p->vId2Var, iObj, p->nSatVars++ );
    }
    Gia_ManForEachObjVec( p->vNodes, p->pFrames, pObj, i )
    {
        int iObj = Vec_IntEntry(p->vNodes, i);
        pObj->fMark0 = 0;
        assert( Vec_IntEntry( p->vId2Var, iObj ) == 0 );
        Vec_IntWriteEntry( p->vId2Var, iObj, p->nSatVars++ );
    }
    // extend the SAT solver
    if ( p->nSatVars > sat_solver_nvars(p->pSat) )
        sat_solver_setnvars( p->pSat, p->nSatVars );

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
    int f, iStart, status = -1;
    pUnroll = Unr_ManUnrollStart( pGia, pPars->fVeryVerbose );
    for ( f = 0; f < nFramesMax; f++ )
    {
        p->pFrames = Unr_ManUnrollFrame( pUnroll, f );
        iStart = f * Gia_ManPoNum(pGia);
        if ( Gia_ManBmcCheckOutputs(p->pFrames, iStart) )
        {
            if ( pPars->fVerbose )
            {
                printf( "%4d :  PI =%9d.  AIG =%9d.  Var =%8d.  Trivially UNSAT.               Mem =%7.1f Mb   ", 
                    f, Gia_ManPiNum(p->pFrames), Gia_ManAndNum(p->pFrames), 
                    p->nSatVars-1, Gia_ManMemory(p->pFrames) );
                Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
            }
            continue;
        }
        // create another slice
        Gia_ManBmcAndCone(p, iStart);
        if ( pPars->fVerbose )
        {
            printf( "%4d :  PI =%9d.  AIG =%9d.  Var =%8d.  In =%6d.  And =%9d.   Mem =%7.1f Mb   ", 
                f, Gia_ManPiNum(p->pFrames), Gia_ManAndNum(p->pFrames), 
                p->nSatVars-1, Vec_IntSize(p->vInputs), Vec_IntSize(p->vNodes), Gia_ManMemory(p->pFrames) );
            Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
        }
    }
    // dump unfolded frames
    p->pFrames = Gia_ManCleanup( p->pFrames );
    Gia_AigerWrite( p->pFrames, "frames.aig", 0, 0 );
    printf( "Dumped unfolded frames into file \"frames.aig\".\n" );
    Gia_ManStop( p->pFrames );
    // cleanup
    Unr_ManFree( pUnroll );
    Bmc_MnaFree( p );
    return status;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

