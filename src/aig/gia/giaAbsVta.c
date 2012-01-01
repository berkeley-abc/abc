/**CFile****************************************************************

  FileName    [giaAbsVta.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Variable time-frame abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbsVta.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "satSolver2.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Vta_Man_t_ Vta_Man_t; // manager
struct Vta_Man_t_
{
    // user data
    Gia_Man_t *   pGia;
    int           nFramesMax;   // maximum number of frames
    int           nConfMax;
    int           nTimeMax;
    int           fVerbose;
    // internal data
    int           nSatVars;     // the number of SAT variables
    int           nObjUsed;     // the number objects used
    int           Shift;        // bit count for obj number
    int           Mask;         // bit mask for obj number
    Vec_Int_t *   vOrder;       // map Num to Id
    Vec_Int_t *   vId2Num;      // map Id to Num
    Vec_Int_t *   vFraLims;     // frame limits
    Vec_Int_t *   vOne2Sat;     // map (Frame; Num) to Sat
    Vec_Int_t *   vCla2One;     // map clause to (Frame; Num)
    Vec_Int_t *   vNumAbs;      // abstraction for each timeframe
    sat_solver2 * pSat;
};

static inline int Vta_FraNum2One( Vta_Man_t * p, int f, int n ) { return (f << p->Shift) | n; }
static inline int Vta_One2Fra( Vta_Man_t * p, int i )           { return i >> p->Shift;       }
static inline int Vta_One2Num( Vta_Man_t * p, int i )           { return i & p->Mask;         }

static inline void Vta_SetSatVar( Vta_Man_t * p, int f, int n )
{
    int One = Vta_FraNum2One( p, f, n );
    int * pPlace = Vec_IntEntryP( p->vOne2Sat, One );
    assert( *pPlace == 0 );
    *pPlace = p->nSatVars++;
    // create additional var for ROs of frame 0
}
static inline int Vta_GetSatVar( Vta_Man_t * p, int f, int n )
{
    int One = Vta_FraNum2One( p, f, n );
    int * pPlace = Vec_IntEntryP( p->vOne2Sat, One );
    assert( *pPlace == 0 );
    return *pPlace;
}
static inline int Vta_GetSatVarObj( Vta_Man_t * p, int f, Gia_Obj_t * pObj )
{
    return Vta_GetSatVar( p, f, Vec_IntEntry(p->vId2Num, Gia_ObjId(p->pGia, pObj)) );
}

extern Vec_Int_t * Gia_VtaCollect( Gia_Man_t * p, Vec_Int_t ** pvFraLims, Vec_Int_t ** pvRoots );

// check the first value of vOrder!!!

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline int sat_solver2_add_const( sat_solver2 * pSat, int iVar, int fCompl, int fMark )
{
    lit Lits[1];
    int Cid;
    assert( iVar >= 0 );

    Lits[0] = toLitCond( iVar, fCompl );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 1 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );
    return 1;
}
static inline int sat_solver2_add_buffer( sat_solver2 * pSat, int iVarA, int iVarB, int fCompl, int fMark )
{
    lit Lits[2];
    int Cid;
    assert( iVarA >= 0 && iVarB >= 0 );

    Lits[0] = toLitCond( iVarA, 0 );
    Lits[1] = toLitCond( iVarB, !fCompl );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 2 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );

    Lits[0] = toLitCond( iVarA, 1 );
    Lits[1] = toLitCond( iVarB, fCompl );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 2 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );
    return 2;
}
static inline int sat_solver2_add_and( sat_solver2 * pSat, int iVar, int iVar0, int iVar1, int fCompl0, int fCompl1, int fMark )
{
    lit Lits[3];
    int Cid;

    Lits[0] = toLitCond( iVar, 1 );
    Lits[1] = toLitCond( iVar0, fCompl0 );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 2 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );

    Lits[0] = toLitCond( iVar, 1 );
    Lits[1] = toLitCond( iVar1, fCompl1 );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 2 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );

    Lits[0] = toLitCond( iVar, 0 );
    Lits[1] = toLitCond( iVar0, !fCompl0 );
    Lits[2] = toLitCond( iVar1, !fCompl1 );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 3 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );
    return 3;
}
static inline int sat_solver2_add_xor( sat_solver2 * pSat, int iVarA, int iVarB, int iVarC, int fCompl, int fMark )
{
    lit Lits[3];
    int Cid;
    assert( iVarA >= 0 && iVarB >= 0 && iVarC >= 0 );

    Lits[0] = toLitCond( iVarA, !fCompl );
    Lits[1] = toLitCond( iVarB, 1 );
    Lits[2] = toLitCond( iVarC, 1 );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 3 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );

    Lits[0] = toLitCond( iVarA, !fCompl );
    Lits[1] = toLitCond( iVarB, 0 );
    Lits[2] = toLitCond( iVarC, 0 );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 3 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );

    Lits[0] = toLitCond( iVarA, fCompl );
    Lits[1] = toLitCond( iVarB, 1 );
    Lits[2] = toLitCond( iVarC, 0 );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 3 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );

    Lits[0] = toLitCond( iVarA, fCompl );
    Lits[1] = toLitCond( iVarB, 0 );
    Lits[2] = toLitCond( iVarC, 1 );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 3 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );
    return 4;
}
static inline int sat_solver2_add_constraint( sat_solver2 * pSat, int iVar, int fCompl, int fMark )
{
    lit Lits[2];
    int Cid;
    assert( iVar >= 0 );

    Lits[0] = toLitCond( iVar, fCompl );
    Lits[1] = toLitCond( iVar+1, 0 );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 2 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );

    Lits[0] = toLitCond( iVar, fCompl );
    Lits[1] = toLitCond( iVar+1, 1 );
    Cid = sat_solver2_addclause( pSat, Lits, Lits + 2 );
    if ( fMark )
        clause_set_partA( pSat, Cid, 1 );
    return 2;
}



/**Function*************************************************************

  Synopsis    [Adds one time-frame to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vga_ManGrow( Vta_Man_t * p, int fThis )
{
    static int PrevF = -1;
    Gia_Obj_t * pObj, * pObj2;
    int Beg, End, One, i, c, f, iOutVar, nClauses;
    assert( ++PrevF == fThis );
    assert( fThis >= 0 && fThis < p->nFramesMax );

    // create variable for the output
    iOutVar = p->nSatVars++;

    // add variables for this frame
    for ( f = fThis; f >= 0; f-- )
    {
        Beg = Vec_IntEntry( p->vFraLims, fThis-f );
        End = Vec_IntEntry( p->vFraLims, fThis-f+1 );
        for ( i = End-1; i >= Beg; i-- )
            Vta_SetSatVar( p, f, i );
    }

    // create clauses for the output
    pObj = Gia_ManPo( p->pGia, 0 );
    nClauses = sat_solver2_add_buffer( p->pSat,
        iOutVar,
        Vta_GetSatVarObj( p, f, Gia_ObjFanin0(pObj) ),
        Gia_ObjFaninC0(pObj), 0 );

    // add clauses for this frame
    for ( f = fThis; f >= 0; f-- )
    {
        Beg = Vec_IntEntry( p->vFraLims, fThis-f );
        End = Vec_IntEntry( p->vFraLims, fThis-f+1 );
        for ( i = End-1; i >= Beg; i-- )
        {
            nClauses = 0;
            pObj = Gia_ManObj( p->pGia, Vec_IntEntry(p->vOrder, i) );
            if ( Gia_ObjIsAnd(pObj) )
                nClauses = sat_solver2_add_and( p->pSat,
                    Vta_GetSatVarObj( p, f, pObj ),
                    Vta_GetSatVarObj( p, f, Gia_ObjFanin0(pObj) ),
                    Vta_GetSatVarObj( p, f, Gia_ObjFanin1(pObj) ),
                    Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), 0 );
            else if ( Gia_ObjIsRo(p->pGia, pObj) )
            {
                if ( f == 0 )
                {
                    nClauses = sat_solver2_add_constraint( p->pSat,
                        Vta_GetSatVarObj( p, f, pObj ),
                        1, 0 );
                }
                else
                {
                    pObj2 = Gia_ObjRoToRi(p->pGia, pObj);
                    nClauses = sat_solver2_add_buffer( p->pSat,
                        Vta_GetSatVarObj( p, f, pObj ),
                        Vta_GetSatVarObj( p, f-1, Gia_ObjFanin0(pObj2) ),
                        Gia_ObjFaninC0(pObj2), 0 );
                }
            }
            else if ( Gia_ObjIsConst0(pObj) )
            {
                nClauses = sat_solver2_add_const( p->pSat,
                    Vta_GetSatVarObj( p, f, pObj ),
                    1, 0 );
            }
            One = Vta_FraNum2One( p, f, i );
            for ( c = 0; c < nClauses; c++ )
                Vec_IntPush( p->vCla2One, One );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Create manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vta_Man_t * Vga_ManStart( Gia_Man_t * pGia, int nFramesMax, int nConfMax, int nTimeMax, int fVerbose )
{
    Vta_Man_t * p;
    assert( nFramesMax > 0 && nFramesMax < 32 );
    p = ABC_CALLOC( Vta_Man_t, 1 );
    p->pGia       = pGia;
    p->nFramesMax = nFramesMax;    
    p->nConfMax   = nConfMax;
    p->nTimeMax   = nTimeMax;
    p->fVerbose   = fVerbose;
    // internal data
    p->vOrder     = Gia_VtaCollect( pGia, &p->vFraLims, NULL );
    Vec_IntWriteEntry( p->vOrder, 0, 0 );
    p->vId2Num    = Vec_IntInvert( p->vOrder, 0 );
    Vec_IntWriteEntry( p->vOrder, 0, -1 );
    Vec_IntWriteEntry( p->vId2Num, 0, -1 );
    // internal data
    p->nObjUsed   = Vec_IntEntry( p->vFraLims, nFramesMax );
    p->Shift      = Gia_Base2Log( p->nObjUsed );
    p->Mask       = (1 << p->Shift) - 1;
    // internal data
    p->vOne2Sat   = Vec_IntStart( (1 << p->Shift) * nFramesMax );
    p->vCla2One   = Vec_IntAlloc( 100000 );  Vec_IntPush( p->vCla2One, -1 );
    p->vNumAbs    = Vec_IntAlloc( p->nObjUsed );
    p->pSat       = sat_solver2_new();
    sat_solver2_setnvars( p->pSat, 10000 );
    p->nSatVars   = 1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Delete manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vga_ManStop( Vta_Man_t * p )
{
    Vec_IntFreeP( &p->vOrder );
    Vec_IntFreeP( &p->vId2Num );
    Vec_IntFreeP( &p->vFraLims );
    Vec_IntFreeP( &p->vOne2Sat );
    Vec_IntFreeP( &p->vCla2One );
    sat_solver2_delete( p->pSat );
    ABC_FREE( p );
}



/**Function*************************************************************

  Synopsis    [Duplicate AIG with the given ordering of nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_VtaDup( Gia_Man_t * p, Vec_Int_t * vOrder )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, nFlops = 0;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Gia_UtilStrsav( p->pName );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachPi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachObjVec( vOrder, p, pObj, i )
        if ( i && Gia_ObjIsRo(p, pObj) )
            pObj->Value = Gia_ManAppendCi(pNew), nFlops++;
    Gia_ManForEachObjVec( vOrder, p, pObj, i )
        if ( i && Gia_ObjIsAnd(pObj) )
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachPo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManForEachObjVec( vOrder, p, pObj, i )
        if ( i && Gia_ObjIsRo(p, pObj) && (pObj = Gia_ObjRoToRi(p, pObj)) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, nFlops );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Collect nodes/flops involved in different timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_VtaCollect_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vOrder, Vec_Int_t * vRoots )
{
    if ( pObj->fMark0 )
        return;
    pObj->fMark0 = 1;
    if ( Gia_ObjIsConst0(pObj) )
        return;
    if ( Gia_ObjIsAnd(pObj) )
    {
        Gia_VtaCollect_rec( p, Gia_ObjFanin0(pObj), vOrder, vRoots );
        Gia_VtaCollect_rec( p, Gia_ObjFanin1(pObj), vOrder, vRoots );
    }
    else if ( Gia_ObjIsRo(p, pObj) )
        Vec_IntPush( vRoots, Gia_ObjId(p, Gia_ObjRoToRi(p, pObj)) );
    Vec_IntPush( vOrder, Gia_ObjId(p, pObj) );
}

/**Function*************************************************************

  Synopsis    [Collect nodes/flops involved in different timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_VtaCollect( Gia_Man_t * p, Vec_Int_t ** pvFraLims, Vec_Int_t ** pvRoots )
{
    Vec_Int_t * vOrder;    // resulting ordering of PI/RO/And
    Vec_Int_t * vFraLims;  // frame limits 
    Vec_Int_t * vRoots;    // CO roots
    Gia_Obj_t * pObj;
    int i, StopPoint;

    Gia_ManCheckMark0( p );

    // create roots
    vRoots = Vec_IntAlloc( 1000 );
    Gia_ManForEachPo( p, pObj, i )
        Vec_IntPush( vRoots, Gia_ObjId(p, pObj) );

    // start order
    vOrder = Vec_IntAlloc( Gia_ManObjNum(p) );
    Vec_IntPush( vOrder, -1 );

    // start limits
    vFraLims = Vec_IntAlloc( 1000 );
    Vec_IntPush( vFraLims, Vec_IntSize(vOrder) );

    // collect new nodes
    StopPoint = Vec_IntSize(vRoots);
    Gia_ManForEachObjVec( vRoots, p, pObj, i )
    {
        if ( i == StopPoint )
        {
            Vec_IntPush( vFraLims, Vec_IntSize(vOrder) );
            StopPoint = Vec_IntSize(vRoots);
        }
        Gia_VtaCollect_rec( p, Gia_ObjFanin0(pObj), vOrder, vRoots );
    }
    assert( i == StopPoint );
    Vec_IntPush( vFraLims, Vec_IntSize(vOrder) );

/*
    // add unmarked PIs
    Gia_ManForEachPi( p, pObj, i )
        if ( !pObj->fMark0 )
            Vec_IntPush( vOrder, Gia_ObjId(p, pObj) );
*/

    // clean/return
    Gia_ManCleanMark0( p );
    if ( pvFraLims )
        *pvFraLims = vFraLims;
    else
        Vec_IntFree( vFraLims );
    if ( pvRoots )
        *pvRoots = vRoots;
    else
        Vec_IntFree( vRoots );
    return vOrder;
}

/**Function*************************************************************

  Synopsis    [Collect nodes/flops involved in different timeframes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_VtaTest( Gia_Man_t * p )
{
    Vec_Int_t * vOrder, * vFraLims, * vRoots;
    Gia_Man_t * pCopy;
    int i, Entry;
    // the new AIG orders flops and PIs in the "natural" order
    vOrder = Gia_VtaCollect( p, &vFraLims, &vRoots );
 
    // print results
//  Gia_ManPrintStats( p, 0 );
    printf( "Obj =%8d.  Unused =%8d.  Frames =%6d.\n",
        Gia_ManObjNum(p), 
        Gia_ManObjNum(p) - Gia_ManCoNum(p) - Vec_IntSize(vOrder), 
        Vec_IntSize(vFraLims) - 1 );

    Vec_IntForEachEntry( vFraLims, Entry, i )
        printf( "%d=%d ", i, Entry );
    printf( "\n" );

    pCopy = Gia_VtaDup( p, vOrder );
//    Gia_ManStopP( &pCopy );

    // cleanup
    Vec_IntFree( vOrder );
    Vec_IntFree( vFraLims );
    Vec_IntFree( vRoots );
    return pCopy;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

