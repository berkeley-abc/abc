/**CFile****************************************************************

  FileName    [giaSatLut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSatLut.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "sat/bsat/satStore.h"
#include "misc/util/utilNam.h"
#include "map/scl/sclCon.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sbl_Man_t_ Sbl_Man_t;
struct Sbl_Man_t_
{
    sat_solver *     pSat;       // SAT solver
    Vec_Int_t *      vCardVars;  // candinality variables
    int              LogN;       // max vars
    int              FirstVar;   // first variable to be used
    int              LitShift;   // shift in terms of literals (2*Gia_ManCiNum(pGia)+2)
    int              nInputs;    // the number of inputs
    // window
    Gia_Man_t *      pGia;
    Vec_Int_t *      vLeaves;    // leaf nodes
    Vec_Int_t *      vAnds;      // AND-gates
    Vec_Int_t *      vNodes;     // internal LUTs
    Vec_Int_t *      vRoots;     // driver nodes (a subset of vAnds)
    Vec_Int_t *      vRootVars;  // driver nodes (as SAT variables)
    // cuts
    Vec_Wrd_t *      vCutsI;     // input bit patterns
    Vec_Wrd_t *      vCutsN;     // node bit patterns
    Vec_Int_t *      vCutsNum;   // cut counts for each obj
    Vec_Int_t *      vCutsStart; // starting cuts for each obj
    Vec_Int_t *      vCutsObj;   // object to which this cut belongs
    Vec_Wrd_t *      vTempI;     // temporary cuts
    Vec_Wrd_t *      vTempN;     // temporary cuts
    Vec_Int_t *      vSolCuts;   // cuts belonging to solution
    Vec_Int_t *      vSolCuts2;  // cuts belonging to solution
    // temporary
    Vec_Int_t *      vLits;      // literals
    Vec_Int_t *      vAssump;    // literals
    Vec_Int_t *      vPolar;     // variables polarity
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
void Sbl_ManUpdateMapping( Sbl_Man_t * p )
{
//    Gia_Obj_t * pObj;
    Vec_Int_t * vObj;
    word CutI, CutN;
    int i, c, b, iObj, iTemp; 
    assert( Vec_IntSize(p->vSolCuts2) < Vec_IntSize(p->vSolCuts) );
    Vec_IntForEachEntry( p->vAnds, iObj, i )
    {
        vObj = Vec_WecEntry(p->pGia->vMapping2, iObj);
        Vec_IntForEachEntry( vObj, iTemp, b )
            Gia_ObjLutRefDecId( p->pGia, iTemp );
        Vec_IntClear( vObj );
    }
    Vec_IntForEachEntry( p->vSolCuts2, c, i )
    {
        CutI = Vec_WrdEntry( p->vCutsI, c );
        CutN = Vec_WrdEntry( p->vCutsN, c );
        iObj = Vec_IntEntry( p->vCutsObj, c );
        iObj = Vec_IntEntry( p->vAnds, iObj );
        vObj = Vec_WecEntry( p->pGia->vMapping2, iObj );
        assert( Vec_IntSize(vObj) == 0 );
        for ( b = 0; b < 64; b++ )
            if ( (CutI >> b) & 1 )
                Vec_IntPush( vObj, Vec_IntEntry(p->vLeaves, b) );
        for ( b = 0; b < 64; b++ )
            if ( (CutN >> b) & 1 )
                Vec_IntPush( vObj, Vec_IntEntry(p->vAnds, b) );
        Vec_IntForEachEntry( vObj, iTemp, b )
            Gia_ObjLutRefIncId( p->pGia, iTemp );
    }
/*
    // verify
    Gia_ManForEachLut2Vec( p->pGia, vObj, i )
        Vec_IntForEachEntry( vObj, iTemp, b )
            Gia_ObjLutRefDecId( p->pGia, iTemp );
    Gia_ManForEachCo( p->pGia, pObj, i )
        Gia_ObjLutRefDecId( p->pGia, Gia_ObjFaninId0p(p->pGia, pObj) );

    for ( i = 0; i < Gia_ManObjNum(p->pGia); i++ )
        if ( p->pGia->pLutRefs[i] )
            printf( "Object %d has %d refs\n", i, p->pGia->pLutRefs[i] );

    Gia_ManForEachCo( p->pGia, pObj, i )
        Gia_ObjLutRefIncId( p->pGia, Gia_ObjFaninId0p(p->pGia, pObj) );
    Gia_ManForEachLut2Vec( p->pGia, vObj, i )
        Vec_IntForEachEntry( vObj, iTemp, b )
            Gia_ObjLutRefIncId( p->pGia, iTemp );
*/
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Sbl_ManPrintCut( word CutI, word CutN, int nInputs )
{
    int b, Count = 0; 
    printf( "{ " );
    for ( b = 0; b < 64; b++ )
        if ( (CutI >> b) & 1 )
            printf( "i%d ", b ), Count++;
    printf( " " );
    for ( b = 0; b < 64; b++ )
        if ( (CutN >> b) & 1 )
            printf( "n%d ", b ), Count++;
    printf( "};\n" );
    return Count;
}
static int Sbl_ManFindAndPrintCut( Sbl_Man_t * p, int c )
{
    return Sbl_ManPrintCut( Vec_WrdEntry(p->vCutsI, c), Vec_WrdEntry(p->vCutsN, c), Vec_IntSize(p->vLeaves) );
}
static inline int Sbl_CutIsFeasible( word CutI, word CutN )
{
    int Count = (CutI != 0) + (CutN != 0);
    CutI = CutI & (CutI-1);  CutN = CutN & (CutN-1);  Count += (CutI != 0) + (CutN != 0);
    CutI = CutI & (CutI-1);  CutN = CutN & (CutN-1);  Count += (CutI != 0) + (CutN != 0);
    CutI = CutI & (CutI-1);  CutN = CutN & (CutN-1);  Count += (CutI != 0) + (CutN != 0);  
    CutI = CutI & (CutI-1);  CutN = CutN & (CutN-1);  Count += (CutI != 0) + (CutN != 0);
    return Count <= 4;
}
static inline int Sbl_CutPushUncontained( Vec_Wrd_t * vCutsI, Vec_Wrd_t * vCutsN, word CutI, word CutN )
{
    int i, k = 0;
    assert( vCutsI->nSize == vCutsN->nSize );
    for ( i = 0; i < vCutsI->nSize; i++ )
        if ( (vCutsI->pArray[i] & CutI) == vCutsI->pArray[i] && (vCutsN->pArray[i] & CutN) == vCutsN->pArray[i]  )
            return 1;
    for ( i = 0; i < vCutsI->nSize; i++ )
        if ( (vCutsI->pArray[i] & CutI) != CutI || (vCutsN->pArray[i] & CutN) != CutN )
        {
            Vec_WrdWriteEntry( vCutsI, k, vCutsI->pArray[i] );
            Vec_WrdWriteEntry( vCutsN, k, vCutsN->pArray[i] );
            k++;
        }
    Vec_WrdShrink( vCutsI, k );
    Vec_WrdShrink( vCutsN, k );
    Vec_WrdPush( vCutsI, CutI );
    Vec_WrdPush( vCutsN, CutN );
    return 0;
}
static inline void Sbl_ManComputeCutsOne( Sbl_Man_t * p, int Fan0, int Fan1, int Obj )
{
    word * pCutsI = Vec_WrdArray(p->vCutsI);
    word * pCutsN = Vec_WrdArray(p->vCutsN);
    int Start0 = Vec_IntEntry( p->vCutsStart, Fan0 );
    int Start1 = Vec_IntEntry( p->vCutsStart, Fan1 );
    int Limit0 = Start0 + Vec_IntEntry( p->vCutsNum, Fan0 );
    int Limit1 = Start1 + Vec_IntEntry( p->vCutsNum, Fan1 );
    int i, k;
    Vec_WrdClear( p->vTempI );
    Vec_WrdClear( p->vTempN );
    for ( i = Start0; i < Limit0; i++ )
        for ( k = Start1; k < Limit1; k++ )
            if ( Sbl_CutIsFeasible(pCutsI[i] | pCutsI[k], pCutsN[i] | pCutsN[k]) )
                Sbl_CutPushUncontained( p->vTempI, p->vTempN, pCutsI[i] | pCutsI[k], pCutsN[i] | pCutsN[k] );
    Vec_IntPush( p->vCutsStart, Vec_WrdSize(p->vCutsI) );
    Vec_IntPush( p->vCutsNum, Vec_WrdSize(p->vTempI) + 1 );
    Vec_WrdAppend( p->vCutsI, p->vTempI );
    Vec_WrdAppend( p->vCutsN, p->vTempN );
    Vec_WrdPush( p->vCutsI, 0 );
    Vec_WrdPush( p->vCutsN, (((word)1) << Obj) );
    for ( i = 0; i <= Vec_WrdSize(p->vTempI); i++ )
        Vec_IntPush( p->vCutsObj, Obj );
}
static inline int Sbl_ManFindCut( Sbl_Man_t * p, int Obj, word CutI, word CutN )
{
    word * pCutsI = Vec_WrdArray(p->vCutsI);
    word * pCutsN = Vec_WrdArray(p->vCutsN);
    int Start0 = Vec_IntEntry( p->vCutsStart, Obj );
    int Limit0 = Start0 + Vec_IntEntry( p->vCutsNum, Obj );
    int i;
    //printf( "\nLooking for:\n" );
    //Sbl_ManPrintCut( CutI, CutN, p->nInputs );
    //printf( "\n" );
    for ( i = Start0; i < Limit0; i++ )
    {
        //Sbl_ManPrintCut( pCutsI[i], pCutsN[i], p->nInputs );
        if ( pCutsI[i] == CutI && pCutsN[i] == CutN )
            return i;
    }
    return -1;
}
int Sbl_ManComputeCuts( Sbl_Man_t * p )
{
    Gia_Obj_t * pObj; Vec_Int_t * vFanins;
    int i, k, Index, Fanin, nObjs = Vec_IntSize(p->vLeaves) + Vec_IntSize(p->vAnds);
    assert( Vec_IntSize(p->vLeaves) <= 64 && Vec_IntSize(p->vAnds) <= 64 );
    // assign leaf cuts
    Vec_IntClear( p->vCutsStart );
    Vec_IntClear( p->vCutsObj );
    Vec_IntClear( p->vCutsNum );
    Vec_WrdClear( p->vCutsI );
    Vec_WrdClear( p->vCutsN );
    Gia_ManForEachObjVec( p->vLeaves, p->pGia, pObj, i )
    {
        Vec_IntPush( p->vCutsStart, Vec_WrdSize(p->vCutsI) );
        Vec_IntPush( p->vCutsObj, -1 );
        Vec_IntPush( p->vCutsNum, 1 );
        Vec_WrdPush( p->vCutsI, (((word)1) << i) );
        Vec_WrdPush( p->vCutsN, 0 );
        pObj->Value = i;
    }
    // assign internal cuts
    Gia_ManForEachObjVec( p->vAnds, p->pGia, pObj, i )
    {
        assert( Gia_ObjIsAnd(pObj) );
        assert( ~Gia_ObjFanin0(pObj)->Value );
        assert( ~Gia_ObjFanin1(pObj)->Value );
        Sbl_ManComputeCutsOne( p, Gia_ObjFanin0(pObj)->Value, Gia_ObjFanin1(pObj)->Value, i );
        pObj->Value = Vec_IntSize(p->vLeaves) + i;
    }
    assert( Vec_IntSize(p->vCutsStart) == nObjs );
    assert( Vec_IntSize(p->vCutsNum)   == nObjs );
    assert( Vec_WrdSize(p->vCutsI)     == Vec_WrdSize(p->vCutsN) );
    assert( Vec_WrdSize(p->vCutsI)     == Vec_IntSize(p->vCutsObj) );
    // check that roots are mapped nodes
    Vec_IntClear( p->vRootVars );
    Gia_ManForEachObjVec( p->vRoots, p->pGia, pObj, i )
    {
        int Obj = Gia_ObjId(p->pGia, pObj);
        if ( Gia_ObjIsCi(pObj) )
            continue;
        assert( Gia_ObjIsLut2(p->pGia, Obj) );
        assert( ~pObj->Value );
        Vec_IntPush( p->vRootVars, pObj->Value - Vec_IntSize(p->vLeaves) );
    }
    // create current solution
    Vec_IntClear( p->vPolar );
    Vec_IntClear( p->vSolCuts );
    Gia_ManForEachObjVec( p->vAnds, p->pGia, pObj, i )
    {
        word CutI = 0, CutN = 0;
        int Obj = Gia_ObjId(p->pGia, pObj);
        if ( !Gia_ObjIsLut2(p->pGia, Obj) )
            continue;
        assert( (int)pObj->Value == Vec_IntSize(p->vLeaves) + i );
        // add node
        Vec_IntPush( p->vPolar, i );
        Vec_IntPush( p->vSolCuts, i );
        // add its cut
        //Gia_LutForEachFaninObj( p->pGia, Obj, pFanin, k )
        vFanins = Gia_ObjLutFanins2( p->pGia, Obj );
        Vec_IntForEachEntry( vFanins, Fanin, k )
        {
            Gia_Obj_t * pFanin = Gia_ManObj( p->pGia, Fanin );
            assert( (int)pFanin->Value < Vec_IntSize(p->vLeaves) || Gia_ObjIsLut2(p->pGia, Fanin) );
            assert( ~pFanin->Value );
            if ( (int)pFanin->Value < Vec_IntSize(p->vLeaves) )
                CutI |= ((word)1 << pFanin->Value);
            else
                CutN |= ((word)1 << (pFanin->Value - Vec_IntSize(p->vLeaves)));
        }
        // find the new cut
        Index = Sbl_ManFindCut( p, Vec_IntSize(p->vLeaves) + i, CutI, CutN );
        if ( Index < 0 )
        {
            printf( "Cannot find the available cut.\n" );
            continue;
        }
        assert( Index >= 0 );
        Vec_IntPush( p->vPolar, p->FirstVar+Index );
    }
    // clean value
    Gia_ManForEachObjVec( p->vLeaves, p->pGia, pObj, i )
        pObj->Value = ~0;
    Gia_ManForEachObjVec( p->vAnds, p->pGia, pObj, i )
        pObj->Value = ~0;
    return Vec_WrdSize(p->vCutsI);
}
int Sbl_ManCreateCnf( Sbl_Man_t * p )
{
    int i, k, c, pLits[2], value;
    word * pCutsN = Vec_WrdArray(p->vCutsN);
    assert( p->FirstVar == sat_solver_nvars(p->pSat) );
    sat_solver_setnvars( p->pSat, sat_solver_nvars(p->pSat) + Vec_WrdSize(p->vCutsI) );
    //printf( "\n" );
    for ( i = 0; i < Vec_IntSize(p->vAnds); i++ )
    {
        int Start0 = Vec_IntEntry( p->vCutsStart, Vec_IntSize(p->vLeaves) + i );
        int Limit0 = Start0 + Vec_IntEntry( p->vCutsNum, Vec_IntSize(p->vLeaves) + i ) - 1;
        // add main clause
        Vec_IntClear( p->vLits );
        Vec_IntPush( p->vLits, Abc_Var2Lit(i, 1) );
        //printf( "Node %d implies cuts: ", i );
        for ( k = Start0; k < Limit0; k++ )
        {
            Vec_IntPush( p->vLits, Abc_Var2Lit(p->FirstVar+k, 0) );
            //printf( "%d ", p->FirstVar+k );
        }
        //printf( "\n" );
        value = sat_solver_addclause( p->pSat, Vec_IntArray(p->vLits), Vec_IntLimit(p->vLits)  );
        assert( value );
        // binary clauses
        for ( k = Start0; k < Limit0; k++ )
        {
            word Cut = pCutsN[k];
            //printf( "Cut %d implies root node %d.\n", p->FirstVar+k, i );
            // root clause
            pLits[0] = Abc_Var2Lit( p->FirstVar+k, 1 );
            pLits[1] = Abc_Var2Lit( i, 0 );
            value = sat_solver_addclause( p->pSat, pLits, pLits + 2 );
            assert( value );
            // fanin clauses
            for ( c = 0; c < 64 && Cut; c++, Cut >>= 1 )
            {
                if ( (Cut & 1) == 0 )
                    continue;
                //printf( "Cut %d implies fanin %d.\n", p->FirstVar+k, c );
                pLits[1] = Abc_Var2Lit( c, 0 );
                value = sat_solver_addclause( p->pSat, pLits, pLits + 2 );
                assert( value );
            }
        }
    }
    sat_solver_set_polarity( p->pSat, Vec_IntArray(p->vPolar), Vec_IntSize(p->vPolar) );
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sbl_Man_t * Sbl_ManAlloc( Gia_Man_t * pGia, int LogN )
{
    Sbl_Man_t * p = ABC_CALLOC( Sbl_Man_t, 1 );
    extern sat_solver * Sbm_AddCardinSolver( int LogN, Vec_Int_t ** pvVars );
    p->pSat = Sbm_AddCardinSolver( LogN, &p->vCardVars );
    p->LogN = LogN;
    p->FirstVar  = sat_solver_nvars( p->pSat );
    // window
    p->pGia       = pGia;
    p->vLeaves    = Vec_IntAlloc( 64 );
    p->vAnds      = Vec_IntAlloc( 64 );
    p->vNodes     = Vec_IntAlloc( 64 );
    p->vRoots     = Vec_IntAlloc( 64 );
    p->vRootVars  = Vec_IntAlloc( 64 );
    // cuts
    p->vCutsI     = Vec_WrdAlloc( 1000 );     // input bit patterns
    p->vCutsN     = Vec_WrdAlloc( 1000 );     // node bit patterns
    p->vCutsNum   = Vec_IntAlloc( 64 );       // cut counts for each obj
    p->vCutsStart = Vec_IntAlloc( 64 );       // starting cuts for each obj
    p->vCutsObj   = Vec_IntAlloc( 1000 );
    p->vSolCuts   = Vec_IntAlloc( 64 );
    p->vSolCuts2  = Vec_IntAlloc( 64 );
    p->vTempI     = Vec_WrdAlloc( 32 ); 
    p->vTempN     = Vec_WrdAlloc( 32 ); 
    // internal
    p->vLits      = Vec_IntAlloc( 64 );
    p->vAssump    = Vec_IntAlloc( 64 );
    p->vPolar     = Vec_IntAlloc( 1000 );
    // other
    Gia_ManFillValue( pGia );
    return p;
}

void Sbl_ManStop( Sbl_Man_t * p )
{
    sat_solver_delete( p->pSat );
    Vec_IntFree( p->vCardVars );
    // internal
    Vec_IntFree( p->vLeaves );
    Vec_IntFree( p->vAnds );
    Vec_IntFree( p->vNodes );
    Vec_IntFree( p->vRoots );
    Vec_IntFree( p->vRootVars );
    // cuts
    Vec_WrdFree( p->vCutsI );
    Vec_WrdFree( p->vCutsN );
    Vec_IntFree( p->vCutsNum );
    Vec_IntFree( p->vCutsStart );
    Vec_IntFree( p->vCutsObj );
    Vec_IntFree( p->vSolCuts );
    Vec_IntFree( p->vSolCuts2 );
    Vec_WrdFree( p->vTempI );
    Vec_WrdFree( p->vTempN );
    // temporary
    Vec_IntFree( p->vLits );
    Vec_IntFree( p->vAssump );
    Vec_IntFree( p->vPolar );
    // other
    ABC_FREE( p );
}

void Sbl_ManWindow( Sbl_Man_t * p )
{
    int i, ObjId;
    // collect leaves
    Vec_IntClear( p->vLeaves );
    Gia_ManForEachCiId( p->pGia, ObjId, i )
        Vec_IntPush( p->vLeaves, ObjId );
    // collect internal
    Vec_IntClear( p->vAnds );
    Gia_ManForEachAndId( p->pGia, ObjId )
        Vec_IntPush( p->vAnds, ObjId );
    // collect roots
    Vec_IntClear( p->vRoots );
    Gia_ManForEachCoDriverId( p->pGia, ObjId, i )
        Vec_IntPush( p->vRoots, ObjId );
}

int Sbl_ManWindow2( Sbl_Man_t * p, int iPivot )
{
    Vec_Int_t * vRoots, * vNodes, * vLeaves, * vAnds;
    int Count = Gia_ManComputeOneWin( p->pGia, iPivot, &vRoots, &vNodes, &vLeaves, &vAnds );
    if ( Count == 0 )
        return 0;
    Vec_IntClear( p->vRoots );   Vec_IntAppend( p->vRoots,  vRoots );
    Vec_IntClear( p->vNodes );   Vec_IntAppend( p->vNodes,  vNodes );
    Vec_IntClear( p->vLeaves );  Vec_IntAppend( p->vLeaves, vLeaves );
    Vec_IntClear( p->vAnds );    Vec_IntAppend( p->vAnds,   vAnds );
//Vec_IntPrint( vRoots );
//Vec_IntPrint( vAnds );
//Vec_IntPrint( vLeaves );
    // recompute internal nodes
//    Gia_ManIncrementTravId( p->pGia );
//    Gia_ManCollectAnds( p->pGia, Vec_IntArray(p->vRoots), Vec_IntSize(p->vRoots), p->vAnds, p->vLeaves );
    return Count;
}

int Sbl_ManTestSat( Gia_Man_t * pGia, int nBTLimit, int iPivot, int fVerbose )
{
    int fKeepTrying = 1;
    abctime clk = Abc_Clock(), clk2;
    int i, LogN = 6, nVars = 1 << LogN, status, Root;
    Sbl_Man_t * p = Sbl_ManAlloc( pGia, LogN );
    int StartSol, Count, nConfTotal = 0;

    // compute one window
    Count = Sbl_ManWindow2( p, iPivot );
    if ( Count == 0 )
    {
        printf( "Obj %d: Window with less than %d inputs does not exist.\n", iPivot, 64 );
        Sbl_ManStop( p );
        return 0;
    }
    if ( fVerbose )
    printf( "\nObj = %6d : Leaf = %2d.  LUT = %2d.  AND = %2d.  Root = %2d.\n", 
        iPivot, Vec_IntSize(p->vLeaves), Vec_IntSize(p->vNodes), Vec_IntSize(p->vAnds), Vec_IntSize(p->vRoots) ); 
    if ( Vec_IntSize(p->vLeaves) > 64 || Vec_IntSize(p->vAnds) > 64 )
    {
        printf( "Obj %d: Encountered window with %d inputs and %d internal nodes.\n", iPivot, Vec_IntSize(p->vLeaves), Vec_IntSize(p->vAnds) );
        Sbl_ManStop( p );
        return 0;
    }

    if ( Vec_IntSize(p->vAnds) < 20 )
    {
        if ( fVerbose )
        printf( "Skipping.\n" );
        Sbl_ManStop( p );
        return 0;
    }

    // derive cuts
    Sbl_ManComputeCuts( p );
    // derive SAT instance
    Sbl_ManCreateCnf( p );

    if ( fVerbose )
    Vec_IntPrint( p->vSolCuts );

    if ( fVerbose )
    printf( "All clauses = %d.  Multi clauses = %d.  Binary clauses = %d.  Other clauses = %d.\n\n", 
        sat_solver_nclauses(p->pSat), Vec_IntSize(p->vAnds), Vec_WrdSize(p->vCutsI) - Vec_IntSize(p->vAnds), 
        sat_solver_nclauses(p->pSat) - Vec_WrdSize(p->vCutsI) );

    // create assumptions
    // cardinality
    Vec_IntClear( p->vAssump );
    Vec_IntPush( p->vAssump, -1 );
    // unused variables
    for ( i = Vec_IntSize(p->vAnds); i < nVars; i++ )
        Vec_IntPush( p->vAssump, Abc_Var2Lit(i, 1) );
    // root variables
    Vec_IntForEachEntry( p->vRootVars, Root, i )
        Vec_IntPush( p->vAssump, Abc_Var2Lit(Root, 0) );
//    Vec_IntPrint( p->vAssump );

    Vec_IntClear( p->vSolCuts2 );
    StartSol = Vec_IntSize(p->vSolCuts) + 1;
//    StartSol = 30;
    while ( fKeepTrying && StartSol-fKeepTrying > 0 )
    {
        int nConfBef, nConfAft;
        if ( fVerbose )
            printf( "Trying to find mapping with %d gates.\n", StartSol-fKeepTrying );
    //    for ( i = Vec_IntSize(p->vSolCuts)-5; i < nVars; i++ )
    //        Vec_IntPush( p->vAssump, Abc_Var2Lit(Vec_IntEntry(p->vCardVars, i), 1) );
        Vec_IntWriteEntry( p->vAssump, 0, Abc_Var2Lit(Vec_IntEntry(p->vCardVars, StartSol-fKeepTrying), 1) );
        // solve the problem
        clk2 = Abc_Clock();
        nConfBef = (int)p->pSat->stats.conflicts;
        status = sat_solver_solve( p->pSat, Vec_IntArray(p->vAssump), Vec_IntLimit(p->vAssump), nBTLimit, 0, 0, 0 );
        nConfAft = (int)p->pSat->stats.conflicts;
        nConfTotal += nConfAft - nConfBef;
        if ( status == l_Undef )
            break;
        if ( status == l_True )
        {
            int Count = 0, LitCount = 0;
            if ( fVerbose )
            {
                printf( "Inputs = %d.  ANDs = %d.  Total = %d. All vars = %d.\n", 
                    Vec_IntSize(p->vLeaves), Vec_IntSize(p->vAnds), 
                    Vec_IntSize(p->vLeaves)+Vec_IntSize(p->vAnds), nVars );
                for ( i = 0; i < Vec_IntSize(p->vAnds); i++ )
                    printf( "%d", sat_solver_var_value(p->pSat, i) );
                printf( "\n" );
                for ( i = 0; i < Vec_IntSize(p->vAnds); i++ )
                    if ( sat_solver_var_value(p->pSat, i) )
                    {
                        printf( "%d=%d ", i, sat_solver_var_value(p->pSat, i) );
                        Count++;
                    }
                printf( "Count = %d\n", Count );
            }
//            for ( i = p->FirstVar; i < sat_solver_nvars(p->pSat); i++ )
//                printf( "%d", sat_solver_var_value(p->pSat, i) );
//            printf( "\n" );
            Count = 1;
            Vec_IntClear( p->vSolCuts2 );
            for ( i = p->FirstVar; i < sat_solver_nvars(p->pSat); i++ )
                if ( sat_solver_var_value(p->pSat, i) )
                {
                    if ( fVerbose )
                        printf( "Cut %3d : Node = %3d  Node = %6d  ", Count++, Vec_IntEntry(p->vCutsObj, i-p->FirstVar), Vec_IntEntry(p->vAnds, Vec_IntEntry(p->vCutsObj, i-p->FirstVar)) );
                    if ( fVerbose )
                        LitCount += Sbl_ManFindAndPrintCut( p, i-p->FirstVar );
                    Vec_IntPush( p->vSolCuts2, i-p->FirstVar );
                }
            if ( fVerbose )
            printf( "LitCount = %d.\n", LitCount );
            if ( fVerbose )
            Vec_IntPrint( p->vRootVars );
            //Vec_IntPrint( p->vRoots );
            //Vec_IntPrint( p->vAnds );
            //Vec_IntPrint( p->vLeaves );
        }
        fKeepTrying = status == l_True ? fKeepTrying + 1 : 0;
        if ( fVerbose )
        {
            if ( status == l_False )
                printf( "UNSAT " );
            else if ( status == l_True )
                printf( "SAT   " );
            else 
                printf( "UNDEC " );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk2 );
            Abc_PrintTime( 1, "Total time", Abc_Clock() - clk );
            printf( "\n" );
        }
    }

    // update solution
    if ( Vec_IntSize(p->vSolCuts2) > 0 && Vec_IntSize(p->vSolCuts2) < Vec_IntSize(p->vSolCuts) )
    {
        Sbl_ManUpdateMapping( p );
        printf( "Object %d : Saved %d nodes.  (Conf = %d.)\n", iPivot, Vec_IntSize(p->vSolCuts)-Vec_IntSize(p->vSolCuts2), nConfTotal );
        Sbl_ManStop( p );
        return 2;
    }
    Sbl_ManStop( p );
    return 1;
}

void Gia_ManLutSat( Gia_Man_t * pGia, int nNumber, int nConfl, int fReverse, int fVerbose )
{
    int iLut;
    Gia_ManComputeOneWinStart( pGia, fReverse );
    Gia_ManForEachLut2( pGia, iLut )
    {
//        if ( iLut > 259 )
//            break;
        if ( Sbl_ManTestSat( pGia, nConfl, iLut, fVerbose ) != 2 )
            continue;
//        break;
    }
    Gia_ManComputeOneWin( pGia, -1, NULL, NULL, NULL, NULL );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

