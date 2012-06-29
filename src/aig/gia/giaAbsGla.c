/**CFile****************************************************************

  FileName    [giaAbsGla.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Gate-level abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAbsGla.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "giaAig.h"
#include "src/sat/cnf/cnf.h"
#include "src/sat/bsat/satSolver2.h"
#include "src/base/main/main.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Gla_Obj_t_ Gla_Obj_t; // object
struct Gla_Obj_t_
{
    int           iGiaObj;         // corresponding GIA obj
    unsigned      fAbs      :  1;  // belongs to abstraction
    unsigned      fCompl0   :  1;  // compl bit of the first fanin
//    unsigned      fCompl1   :  1;  // compl bit of the second fanin
    unsigned      fConst    :  1;  // object attribute
    unsigned      fPi       :  1;  // object attribute
    unsigned      fPo       :  1;  // object attribute
    unsigned      fRo       :  1;  // object attribute
    unsigned      fRi       :  1;  // object attribute
    unsigned      fAnd      :  1;  // object attribute
    unsigned      nFanins   : 24;  // fanin count
    int           Fanins[4];       // fanins
    Vec_Int_t     vFrames;         // variables in each timeframe
};

typedef struct Gla_Man_t_ Gla_Man_t; // manager
struct Gla_Man_t_
{
    // user data
    Gia_Man_t *   pGia;            // AIG manager
    Gia_ParVta_t* pPars;           // parameters
    // internal data
    Vec_Int_t *   vAbs;            // abstracted objects
    Gla_Obj_t *   pObjRoot;        // the primary output
    Gla_Obj_t *   pObjs;           // objects
    int           nObjs;           // the number of objects
    int           nAbsOld;         // previous abstraction
    // other data
    int           nCexes;          // the number of counter-examples
    int           nSatVars;        // the number of SAT variables
    Cnf_Dat_t *   pCnf;            // CNF derived for the nodes
    sat_solver2 * pSat;            // incremental SAT solver
    Vec_Int_t *   vCla2Obj;        // mapping of clauses into GLA objs
    Vec_Int_t *   vTemp;           // temporary array
    Vec_Int_t *   vAddedNew;       // temporary array
    // statistics 
    int           timeInit;
    int           timeSat;
    int           timeUnsat;
    int           timeCex;
    int           timeOther;
};

// object procedures
static inline int         Gla_ObjId( Gla_Man_t * p, Gla_Obj_t * pObj )     { assert( pObj > p->pObjs && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs;  }
static inline Gla_Obj_t * Gla_ManObj( Gla_Man_t * p, int i )               { assert( i >= 0 && i < p->nObjs ); return i ? p->pObjs + i : NULL;                 }
static inline Gia_Obj_t * Gla_ManGiaObj( Gla_Man_t * p, Gla_Obj_t * pObj ) { return Gia_ManObj( p->pGia, pObj->iGiaObj );                                      }

// iterator through abstracted objects
#define Gla_ManForEachObj( p, pObj )                       \
    for ( pObj = p->pObjs + 1; pObj < p->pObjs + p->nObjs; pObj++ ) 
#define Gla_ManForEachObjAbs( p, pObj, i )                 \
    for ( i = 0; i < Vec_IntSize(p->vAbs) && ((pObj = Gla_ManObj(p, Vec_IntEntry(p->vAbs, i))),1); i++) 
#define Gla_ManForEachObjAbsVec( vVec, p, pObj, i )        \
    for ( i = 0; i < Vec_IntSize(vVec) && ((pObj = Gla_ManObj(p, Vec_IntEntry(vVec, i))),1); i++) 

// iterator through fanins of an abstracted object
#define Gla_ObjForEachFanin( p, pObj, pFanin, i )    \
    for ( i = 0; (i < (int)pObj->nFanins) && ((pFanin = Gla_ManObj(p, pObj->Fanins[i])),1); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derive a new counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Gia_ManCexRemap( Gia_Man_t * p, Gia_Man_t * pAbs, Abc_Cex_t * pCexAbs, Vec_Int_t * vPis )
{
    Abc_Cex_t * pCex;
    int i, f, iPiNum;
    assert( pCexAbs->iPo == 0 );
    // start the counter-example
    pCex = Abc_CexAlloc( Gia_ManRegNum(p), Gia_ManPiNum(p), pCexAbs->iFrame+1 );
    pCex->iFrame = pCexAbs->iFrame;
    pCex->iPo    = pCexAbs->iPo;
    // copy the bit data
    for ( f = 0; f <= pCexAbs->iFrame; f++ )
        for ( i = 0; i < Vec_IntSize(vPis); i++ )
        {
            if ( Abc_InfoHasBit( pCexAbs->pData, pCexAbs->nRegs + pCexAbs->nPis * f + i ) )
            {
                iPiNum = Gia_ObjCioId( Gia_ManObj(p, Vec_IntEntry(vPis, i)) );
                Abc_InfoSetBit( pCex->pData, pCex->nRegs + pCex->nPis * f + iPiNum );
            }
        }
    // verify the counter example
    if ( !Gia_ManVerifyCex( p, pCex, 0 ) )
    {
        printf( "Gia_ManCexRemap(): Counter-example is invalid.\n" );
        Abc_CexFree( pCex );
        pCex = NULL;
    }
    else
    {
        printf( "Counter-example verification is successful.\n" );
        printf( "Output %d was asserted in frame %d (use \"write_counter\" to dump a witness). \n", pCex->iPo, pCex->iFrame );
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Refines gate-level abstraction using the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManGlaRefine( Gia_Man_t * p, Abc_Cex_t * pCex, int fMinCut, int fVerbose )
{
    extern void Nwk_ManDeriveMinCut( Gia_Man_t * p, int fVerbose );
    extern Abc_Cex_t * Saig_ManCbaFindCexCareBits( Aig_Man_t * pAig, Abc_Cex_t * pCex, int nInputs, int fVerbose );
    Gia_Man_t * pAbs;
    Aig_Man_t * pAig;
    Abc_Cex_t * pCare;
    Vec_Int_t * vPis, * vPPis;
    int f, i, iObjId, nOnes = 0, Counter = 0;
    if ( p->vGateClasses == NULL )
    {
        printf( "Gia_ManGlaRefine(): Abstraction gate map is missing.\n" );
        return -1;
    }
    // derive abstraction
    pAbs = Gia_ManDupAbsGates( p, p->vGateClasses );
    Gia_ManStop( pAbs );
    pAbs = Gia_ManDupAbsGates( p, p->vGateClasses );
    if ( Gia_ManPiNum(pAbs) != pCex->nPis )
    {
        printf( "Gia_ManGlaRefine(): The PI counts in GLA and in CEX do not match.\n" );
        Gia_ManStop( pAbs );
        return -1;
    }
    if ( !Gia_ManVerifyCex( pAbs, pCex, 0 ) )
    {
        printf( "Gia_ManGlaRefine(): The initial counter-example is invalid.\n" );
        Gia_ManStop( pAbs );
        return -1;
    }
//    else
//        printf( "Gia_ManGlaRefine(): The initial counter-example is correct.\n" );
    // get inputs
    Gia_GlaCollectInputs( p, p->vGateClasses, &vPis, &vPPis );
    assert( Vec_IntSize(vPis) + Vec_IntSize(vPPis) == Gia_ManPiNum(pAbs) );
    // minimize the CEX
    pAig = Gia_ManToAigSimple( pAbs );
    pCare = Saig_ManCbaFindCexCareBits( pAig, pCex, Vec_IntSize(vPis), fVerbose );
    Aig_ManStop( pAig );
    if ( pCare == NULL )
        printf( "Counter-example minimization has failed.\n" );
    // add new objects to the map
    iObjId = -1;
    for ( f = 0; f <= pCare->iFrame; f++ )
        for ( i = 0; i < pCare->nPis; i++ )
            if ( Abc_InfoHasBit( pCare->pData, pCare->nRegs + f * pCare->nPis + i ) )
            {
                nOnes++;
                assert( i >= Vec_IntSize(vPis) );
                iObjId = Vec_IntEntry( vPPis, i - Vec_IntSize(vPis) );
                assert( iObjId > 0 && iObjId < Gia_ManObjNum(p) );
                if ( Vec_IntEntry( p->vGateClasses, iObjId ) == 1 )
                    continue;
                assert( Vec_IntEntry( p->vGateClasses, iObjId ) == 0 );
                Vec_IntWriteEntry( p->vGateClasses, iObjId, 1 );
//                printf( "Adding object %d.\n", iObjId );
//                Gia_ObjPrint( p, Gia_ManObj(p, iObjId) );
                Counter++;
            }
    Abc_CexFree( pCare );
    if ( fVerbose )
        printf( "Essential bits = %d.  Additional objects = %d.\n", nOnes, Counter );
    // consider the case of SAT
    if ( iObjId == -1 )
    {
        ABC_FREE( p->pCexSeq );
        p->pCexSeq = Gia_ManCexRemap( p, pAbs, pCex, vPis );
        Vec_IntFree( vPis );
        Vec_IntFree( vPPis );
        Gia_ManStop( pAbs );
        return 0;
    }
    Vec_IntFree( vPis );
    Vec_IntFree( vPPis );
    Gia_ManStop( pAbs );

    // extract abstraction to include min-cut
    if ( fMinCut )
        Nwk_ManDeriveMinCut( p, fVerbose );
    return -1;
}







/**Function*************************************************************

  Synopsis    [Adds clauses for the given obj in the given frame.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gla_ManCollectFanins( Gla_Man_t * p, Gla_Obj_t * pGla, int iObj, Vec_Int_t * vFanins )
{
    int i, nClauses, iFirstClause, * pLit;
    nClauses = p->pCnf->pObj2Count[pGla->iGiaObj];
    iFirstClause = p->pCnf->pObj2Clause[pGla->iGiaObj];
    Vec_IntClear( vFanins );
    for ( i = iFirstClause; i < iFirstClause + nClauses; i++ )
        for ( pLit = p->pCnf->pClauses[i]; pLit < p->pCnf->pClauses[i+1]; pLit++ )
            if ( lit_var(*pLit) != iObj )
                Vec_IntPushUnique( vFanins, lit_var(*pLit) );
    assert( Vec_IntSize( vFanins ) <= 4 );
    Vec_IntSort( vFanins, 0 );
}

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gla_Man_t * Gla_ManStart( Gia_Man_t * pGia, Gia_ParVta_t * pPars )
{
    Gla_Man_t * p;
    Aig_Man_t * pAig;
    Gia_Obj_t * pObj;
    Gla_Obj_t * pGla;
    int i, * pLits;
    // start
    p = ABC_CALLOC( Gla_Man_t, 1 );
    p->pGia  = pGia;
    p->pPars = pPars;
    p->vAbs = Vec_IntAlloc( 100 );
    p->vTemp = Vec_IntAlloc( 100 );
    p->vAddedNew = Vec_IntAlloc( 100 );
    // internal data
    pAig = Gia_ManToAigSimple( p->pGia );
    p->pCnf  = Cnf_DeriveOther( pAig );
    Aig_ManStop( pAig );
    // count the number of variables
    p->nObjs = 1;
    Gia_ManForEachObj( p->pGia, pObj, i )
        if ( p->pCnf->pObj2Count[i] >= 0 )
            pObj->Value = p->nObjs++;
        else
            pObj->Value = ~0;
    // re-express CNF using new variable IDs
    pLits = p->pCnf->pClauses[0];
    for ( i = 0; i < p->pCnf->nLiterals; i++ )
    {
        pObj = Gia_ManObj( p->pGia, lit_var(pLits[i]) );
        assert( ~pObj->Value );
        pLits[i] = toLitCond( pObj->Value, lit_sign(pLits[i]) );
    }
    // create objects
    p->pObjs = ABC_CALLOC( Gla_Obj_t, p->nObjs );
    Gia_ManForEachObj( p->pGia, pObj, i )
    {
        if ( !~pObj->Value )
            continue;
        pGla = Gla_ManObj( p, pObj->Value );
        pGla->iGiaObj = i;
        pGla->fCompl0 = Gia_ObjFaninC0(pObj);
//        pGla->fCompl1 = Gia_ObjFaninC1(pObj);
        pGla->fConst  = Gia_ObjIsConst0(pObj);
        pGla->fPi     = Gia_ObjIsPi(p->pGia, pObj);
        pGla->fPo     = Gia_ObjIsPo(p->pGia, pObj);
        pGla->fRi     = Gia_ObjIsRi(p->pGia, pObj);
        pGla->fRo     = Gia_ObjIsRo(p->pGia, pObj);
        pGla->fAnd    = Gia_ObjIsAnd(pObj);
        if ( Gia_ObjIsConst0(pObj) || Gia_ObjIsPi(p->pGia, pObj) )
            continue;
        if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) )
        {
            Gla_ManCollectFanins( p, pGla, pObj->Value, p->vTemp );
            pGla->nFanins = Vec_IntSize( p->vTemp );
            memcpy( pGla->Fanins, Vec_IntArray(p->vTemp), sizeof(int) * Vec_IntSize(p->vTemp) );
            continue;
        }
        assert( Gia_ObjIsRo(p->pGia, pObj) );
        pGla->nFanins   = 1;
        pGla->Fanins[0] = Gia_ObjFanin0( Gia_ObjRoToRi(p->pGia, pObj) )->Value;
        pGla->fCompl0   = Gia_ObjFaninC0( Gia_ObjRoToRi(p->pGia, pObj) );
    }
    p->pObjRoot = Gla_ManObj( p, Gia_ManPo(p->pGia, 0)->Value );
    // abstraction 
    assert( pGia->vGateClasses != NULL );
    Gla_ManForEachObj( p, pGla )
    {
        if ( Vec_IntEntry( pGia->vGateClasses, pGla->iGiaObj ) == 0 )
            continue;
        pGla->fAbs = 1;
        Vec_IntPush( p->vAbs, Gla_ObjId(p, pGla) );
    }
    // other 
    p->vCla2Obj  = Vec_IntAlloc( 1000 );  Vec_IntPush( p->vCla2Obj, -1 );
    p->pSat      = sat_solver2_new();
    p->nSatVars  = 1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gla_ManStop( Gla_Man_t * p )
{
    Gla_Obj_t * pGla;
//    if ( p->pPars->fVerbose )
        Abc_Print( 1, "SAT solver:  Variables = %d. Clauses = %d. Conflicts = %d. Cexes = %d.\n", 
            sat_solver2_nvars(p->pSat), sat_solver2_nclauses(p->pSat), sat_solver2_nconflicts(p->pSat), p->nCexes );
    Gla_ManForEachObj( p, pGla )
        ABC_FREE( pGla->vFrames.pArray );
    Cnf_DataFree( p->pCnf );
    sat_solver2_delete( p->pSat );
    Vec_IntFree( p->vCla2Obj );
    Vec_IntFree( p->vAddedNew );
    Vec_IntFree( p->vTemp );
    Vec_IntFree( p->vAbs );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Creates a new manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_GlaAbsCount( Gla_Man_t * p, int fRo, int fAnd )
{
    Gla_Obj_t * pObj;
    int i, Counter = 0;
    if ( fRo )
        Gla_ManForEachObjAbs( p, pObj, i )
            Counter += (pObj->fRo && pObj->fAbs);
    else if ( fAnd )
        Gla_ManForEachObjAbs( p, pObj, i )
            Counter += (pObj->fAnd && pObj->fAbs);
    else
        Gla_ManForEachObjAbs( p, pObj, i )
            Counter += (pObj->fAbs);
    return Counter;
}


/**Function*************************************************************

  Synopsis    [Derives new abstraction map.]

  Description [Returns 1 if node contains abstracted leaf on the path.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gla_ManTranslate_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vMap )
{
    int Value0, Value1;
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 1;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
        return 0;
    assert( Gia_ObjIsAnd(pObj) );
    Value0 = Gla_ManTranslate_rec( p, Gia_ObjFanin0(pObj), vMap );
    Value1 = Gla_ManTranslate_rec( p, Gia_ObjFanin1(pObj), vMap );
    if ( Value0 || Value1 )
        Vec_IntWriteEntry( vMap, Gia_ObjId(p, pObj), 1 );
    return Value0 || Value1;
}
Vec_Int_t * Gla_ManTranslate( Gla_Man_t * p )
{
    Vec_Int_t * vRes;
    Gla_Obj_t * pObj, * pFanin;
    Gia_Obj_t * pGiaObj;
    int i, k;
    vRes = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    Gla_ManForEachObjAbs( p, pObj, i )
    {
        Vec_IntWriteEntry( vRes, pObj->iGiaObj, 1 );
        pGiaObj = Gla_ManGiaObj( p, pObj );
        if ( Gia_ObjIsConst0(pGiaObj) || Gia_ObjIsRo(p->pGia, pGiaObj) )
            continue;
        assert( Gia_ObjIsAnd(pGiaObj) );
        Gia_ManIncrementTravId( p->pGia );
        Gla_ObjForEachFanin( p, pObj, pFanin, k )
            Gia_ObjSetTravIdCurrent( p->pGia, Gla_ManGiaObj(p, pFanin) );
        Gla_ManTranslate_rec( p->pGia, pGiaObj, vRes );
    }
    return vRes;
}


/**Function*************************************************************

  Synopsis    [Collect pseudo-PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gla_ManCollectPPis( Gla_Man_t * p )
{
    Vec_Int_t * vPPis;
    Gla_Obj_t * pObj, * pFanin;
    int i, k;
    vPPis = Vec_IntAlloc( 1000 );
    Gla_ManForEachObjAbs( p, pObj, i )
    {
        assert( pObj->fConst || pObj->fRo || pObj->fAnd );
        Gla_ObjForEachFanin( p, pObj, pFanin, k )
            if ( !pFanin->fPi && !pFanin->fAbs )
                Vec_IntPush( vPPis, pObj->Fanins[k] );
    }
    Vec_IntUniqify( vPPis );
    Vec_IntReverseOrder( vPPis );
    return vPPis;
}
int Gla_ManCountPPis( Gla_Man_t * p )
{
    Vec_Int_t * vPPis = Gla_ManCollectPPis( p );
    int RetValue = Vec_IntSize( vPPis );
    Vec_IntFree( vPPis );
    return RetValue;
}

void Gla_ManExplorePPis( Gla_Man_t * p, Vec_Int_t * vPPis )
{
    static int Round = 0;
    Gla_Obj_t * pObj, * pFanin;
    int i, j, k, Count;
    if ( (Round++ % 3) == 0 )
        return;
//    printf( "\n" );
    j = 0;
    Gla_ManForEachObjAbsVec( vPPis, p, pObj, i )
    {
        assert( pObj->fAbs == 0 );
//        printf( "%6d ", Gla_ObjId(p, pObj) );
//        printf( "Fanins=%d ", pObj->nFanins );
//        Gla_ObjForEachFanin( p, pObj, pFanin, k )
//            printf( "%d", pFanin->fAbs );
//        printf( "\n" );

        Count = 0;
        Gla_ObjForEachFanin( p, pObj, pFanin, k )
            Count += pFanin->fAbs;
        if ( Count == 0 )
            continue;
        Vec_IntWriteEntry( vPPis, j++, Gla_ObjId(p, pObj) );
    }
//    printf( "\n%d -> %d\n", Vec_IntSize(vPPis), j );
    Vec_IntShrink( vPPis, j );
}


/**Function*************************************************************

  Synopsis    [Adds CNF for the given timeframe.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gla_ManGetVar( Gla_Man_t * p, int iObj, int iFrame )
{
    Gla_Obj_t * pGla = Gla_ManObj( p, iObj );
    int iVar = Vec_IntGetEntry( &pGla->vFrames, iFrame );
    assert( !pGla->fPo && !pGla->fRi );
    if ( iVar == 0 )
    {
        Vec_IntSetEntry( &pGla->vFrames, iFrame, (iVar = p->nSatVars++) );
        // remember the change
        Vec_IntPush( p->vAddedNew, iObj );
        Vec_IntPush( p->vAddedNew, iFrame );
    }
    return iVar;
}
void Gla_ManAddClauses( Gla_Man_t * p, int iObj, int iFrame, Vec_Int_t * vLits )
{
    Gla_Obj_t * pGlaObj = Gla_ManObj( p, iObj );
    int iVar, iVar1, iVar2;
    if ( pGlaObj->fConst )
    {
        iVar = Gla_ManGetVar( p, iObj, iFrame );
        sat_solver2_add_const( p->pSat, iVar, 1, 0 );
        // remember the clause
        Vec_IntPush( p->vCla2Obj, iObj );
    }
    else if ( pGlaObj->fRo )
    {
        assert( pGlaObj->nFanins == 1 );
        if ( iFrame == 0 )
        {
            iVar = Gla_ManGetVar( p, iObj, iFrame );
            sat_solver2_add_const( p->pSat, iVar, 1, 0 );
            // remember the clause
            Vec_IntPush( p->vCla2Obj, iObj );
        }
        else
        {
            iVar1 = Gla_ManGetVar( p, iObj, iFrame );
            iVar2 = Gla_ManGetVar( p, pGlaObj->Fanins[0], iFrame-1 );
            sat_solver2_add_buffer( p->pSat, iVar1, iVar2, pGlaObj->fCompl0, 0 );
            // remember the clause
            Vec_IntPush( p->vCla2Obj, iObj );
            Vec_IntPush( p->vCla2Obj, iObj );
        }
    }
    else if ( pGlaObj->fAnd )
    {
        int i, RetValue, nClauses, iFirstClause, * pLit;
        nClauses = p->pCnf->pObj2Count[pGlaObj->iGiaObj];
        iFirstClause = p->pCnf->pObj2Clause[pGlaObj->iGiaObj];
        for ( i = iFirstClause; i < iFirstClause + nClauses; i++ )
        {
            Vec_IntClear( vLits );
            for ( pLit = p->pCnf->pClauses[i]; pLit < p->pCnf->pClauses[i+1]; pLit++ )
            {
                iVar = Gla_ManGetVar( p, lit_var(*pLit), iFrame );
                Vec_IntPush( vLits, toLitCond( iVar, lit_sign(*pLit) ) );
            }
            RetValue = sat_solver2_addclause( p->pSat, Vec_IntArray(vLits), Vec_IntArray(vLits)+Vec_IntSize(vLits) );
            assert( RetValue );
            // remember the clause
            Vec_IntPush( p->vCla2Obj, iObj );
        }
    }
    else assert( 0 );
}
void Gia_GlaAddToAbs( Gla_Man_t * p, Vec_Int_t * vAbsAdd, int fCheck )
{
    Gla_Obj_t * pGla;
    int i;
    Gla_ManForEachObjAbsVec( vAbsAdd, p, pGla, i )
    {
        assert( !fCheck || pGla->fAbs == 0 );
        if ( pGla->fAbs )
            continue;
        pGla->fAbs = 1;
        Vec_IntPush( p->vAbs, Gla_ObjId(p, pGla) );
    }
}
void Gia_GlaAddTimeFrame( Gla_Man_t * p, int f )
{
    Gla_Obj_t * pObj;
    int i;
    Gla_ManForEachObjAbs( p, pObj, i )
        Gla_ManAddClauses( p, Gla_ObjId(p, pObj), f, p->vTemp );
    sat_solver2_simplify( p->pSat );
}
void Gia_GlaAddOneSlice( Gla_Man_t * p, int fCur, Vec_Int_t * vCore )
{
    int f, i, iGlaObj;
    for ( f = fCur; f >= 0; f-- )
        Vec_IntForEachEntry( vCore, iGlaObj, i )
            Gla_ManAddClauses( p, iGlaObj, f, p->vTemp );
    sat_solver2_simplify( p->pSat );
}
void Gla_ManRollBack( Gla_Man_t * p )
{
    int i, iObj, iFrame;
    Vec_IntForEachEntryDouble( p->vAddedNew, iObj, iFrame, i )
    {
        assert( Vec_IntEntry( &Gla_ManObj(p, iObj)->vFrames, iFrame ) > 0 );
        Vec_IntWriteEntry( &Gla_ManObj(p, iObj)->vFrames, iFrame, 0 );
    }
    Vec_IntForEachEntryStart( p->vAbs, iObj, i, p->nAbsOld )
    {
        assert( Gla_ManObj( p, iObj )->fAbs == 1 );
        Gla_ManObj( p, iObj )->fAbs = 0;
    }
    Vec_IntShrink( p->vAbs, p->nAbsOld );
}


            


/**Function*************************************************************

  Synopsis    [Finds the set of clauses involved in the UNSAT core.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gla_ManGetOutLit( Gla_Man_t * p, int f )
{
    Gla_Obj_t * pFanin = Gla_ManObj( p, p->pObjRoot->Fanins[0] );
    int iSat = Vec_IntEntry( &pFanin->vFrames, f );
    assert( iSat > 0 );
    return Abc_Var2Lit( iSat, p->pObjRoot->fCompl0 );
}
Vec_Int_t * Gla_ManUnsatCore( Gla_Man_t * p, int f, Vec_Int_t * vCla2Obj, sat_solver2 * pSat, int nConfMax, int fVerbose, int * piRetValue, int * pnConfls )
{
    Vec_Int_t * vCore;
    int iLit = Gla_ManGetOutLit( p, f );
    int nConfPrev = pSat->stats.conflicts;
    int i, Entry, RetValue, clk = clock();
    if ( piRetValue )
        *piRetValue = 1;
    // solve the problem
    RetValue = sat_solver2_solve( pSat, &iLit, &iLit+1, (ABC_INT64_T)nConfMax, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( pnConfls )
        *pnConfls = (int)pSat->stats.conflicts - nConfPrev;
    if ( RetValue == l_Undef )
    {
        if ( piRetValue )
            *piRetValue = -1;
        return NULL;
    }
    if ( RetValue == l_True )
    {
        if ( piRetValue )
            *piRetValue = 0;
        return NULL;
    }
    if ( fVerbose )
    {
//        Abc_Print( 1, "%6d", (int)pSat->stats.conflicts - nConfPrev );
//        Abc_Print( 1, "UNSAT after %7d conflicts.      ", pSat->stats.conflicts );
//        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    assert( RetValue == l_False );

    // derive the UNSAT core
    clk = clock();
    vCore = (Vec_Int_t *)Sat_ProofCore( pSat );
    if ( fVerbose )
    {
//        Abc_Print( 1, "Core is %8d clauses (out of %8d).   ", Vec_IntSize(vCore), sat_solver2_nclauses(pSat) );
//        Abc_PrintTime( 1, "Time", clock() - clk );
    }

    // remap core into original objects 
    Vec_IntForEachEntry( vCore, Entry, i )
        Vec_IntWriteEntry( vCore, i, Vec_IntEntry(p->vCla2Obj, Entry) );
    Vec_IntUniqify( vCore );
    Vec_IntReverseOrder( vCore );
    if ( fVerbose )
    {
//        Abc_Print( 1, "Core is %8d vars    (out of %8d).   ", Vec_IntSize(vCore), sat_solver2_nvars(pSat) );
//        Abc_PrintTime( 1, "Time", clock() - clk );
    }
    return vCore;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gla_ManAbsPrintFrame( Gla_Man_t * p, int nCoreSize, int nFrames, int nConfls, int nCexes, int Time )
{
    Abc_Print( 1, "%3d :", nFrames-1 );
    Abc_Print( 1, "%4d", Abc_MinInt(100, 100 * Gia_GlaAbsCount(p, 0, 0) / (p->nObjs - Gia_ManPoNum(p->pGia) + Gia_ManCoNum(p->pGia) + 1)) ); 
    Abc_Print( 1, "%6d", Gia_GlaAbsCount(p, 0, 0) );
    Abc_Print( 1, "%5d", Gla_ManCountPPis(p) );
    Abc_Print( 1, "%5d", Gia_GlaAbsCount(p, 1, 0) );
    Abc_Print( 1, "%6d", Gia_GlaAbsCount(p, 0, 1) );
    Abc_Print( 1, "%8d", nConfls );
    if ( nCexes == 0 )
        Abc_Print( 1, "%5c", '-' ); 
    else
        Abc_Print( 1, "%5d", nCexes ); 
    Abc_Print( 1, " %9d", sat_solver2_nvars(p->pSat) ); 
    Abc_Print( 1, " %6d", nCoreSize > 0 ? nCoreSize : 0 ); 
    Abc_Print( 1, "%9.2f sec", (float)(Time)/(float)(CLOCKS_PER_SEC) );
    Abc_Print( 1, "%s", nCoreSize > 0 ? "\n" : "\r" );
    fflush( stdout );
}
void Gla_ManReportMemory( Gla_Man_t * p )
{
    Gla_Obj_t * pGla;
    double memTot = 0;
    double memAig = Gia_ManObjNum(p->pGia) * sizeof(Gia_Obj_t);
    double memSat = sat_solver2_memory( p->pSat );
    double memPro = sat_solver2_memory_proof( p->pSat );
    double memMap = p->nObjs * sizeof(Gla_Obj_t);
    double memOth = sizeof(Gla_Man_t);
    for ( pGla = p->pObjs; pGla < p->pObjs + p->nObjs; pGla++ )
        memMap += Vec_IntCap(&pGla->vFrames) * sizeof(int);
    memOth += Vec_IntCap(p->vCla2Obj) * sizeof(int);
    memOth += Vec_IntCap(p->vAddedNew) * sizeof(int);
    memOth += Vec_IntCap(p->vTemp) * sizeof(int);
    memOth += Vec_IntCap(p->vAbs) * sizeof(int);
    memTot = memAig + memSat + memPro + memMap + memOth;
    ABC_PRMP( "Memory: AIG  ", memAig, memTot );
    ABC_PRMP( "Memory: SAT  ", memSat, memTot );
    ABC_PRMP( "Memory: Proof", memPro, memTot );
    ABC_PRMP( "Memory: Map  ", memMap, memTot );
    ABC_PRMP( "Memory: Other", memOth, memTot );
    ABC_PRMP( "Memory: TOTAL", memTot, memTot );
}


/**Function*************************************************************

  Synopsis    [Send abstracted model or send cancel.]

  Description [Counter-example will be sent automatically when &vta terminates.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_GlaDumpAbsracted( Gla_Man_t * p, int fVerbose )
{
    char * pFileName = p->pPars->pFileVabs ? p->pPars->pFileVabs : "glabs.aig";
    Gia_Man_t * pAbs;
    Vec_Int_t * vGateClasses;
    if ( fVerbose )
        Abc_Print( 1, "Dumping abstracted model into file \"%s\"...\n", pFileName );
//    if ( !Abc_FrameIsBridgeMode() )
//        return;
    // create abstraction
    vGateClasses = Gla_ManTranslate( p );
    pAbs = Gia_ManDupAbsGates( p->pGia, vGateClasses );
    Vec_IntFreeP( &vGateClasses );
    // write into file
    Gia_WriteAiger( pAbs, pFileName, 0, 0 );
    Gia_ManStop( pAbs );
}


/**Function*************************************************************

  Synopsis    [Performs gate-level abstraction]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_GlaPerform( Gia_Man_t * pAig, Gia_ParVta_t * pPars )
{
    extern int Gia_VtaPerformInt( Gia_Man_t * pAig, Gia_ParVta_t * pPars );
    Gla_Man_t * p;
    Vec_Int_t * vCore, * vPPis;
    Abc_Cex_t * pCex = NULL;
    int i, f, nConfls, Status, nCoreSize, RetValue = -1;
    int clk = clock(), clk2;
    // preconditions
    assert( Gia_ManPoNum(pAig) == 1 );
    assert( pPars->nFramesMax == 0 || pPars->nFramesStart <= pPars->nFramesMax );
    // compute intial abstraction
    if ( pAig->vGateClasses == NULL )
    {
        int nFramesMaxOld   = pPars->nFramesMax;
        int nFramesStartOld = pPars->nFramesStart;
        int nTimeOutOld     = pPars->nTimeOut;
        int nDumpOld        = pPars->fDumpVabs;
        pPars->nFramesMax   = pPars->nFramesStart;
        pPars->nFramesStart = Abc_MinInt( pPars->nFramesStart/2 + 1, 3 );
        pPars->nTimeOut     = 15;
        pPars->fDumpVabs    = 0;
        RetValue = Gia_VtaPerformInt( pAig, pPars );
        pPars->nFramesMax   = nFramesMaxOld;
        pPars->nFramesStart = nFramesStartOld;
        pPars->nTimeOut     = nTimeOutOld;
        pPars->fDumpVabs    = nDumpOld;
        // create gate classes
        Vec_IntFreeP( &pAig->vGateClasses );
        pAig->vGateClasses = Gia_VtaConvertToGla( pAig, pAig->vObjClasses );
        Vec_IntFreeP( &pAig->vObjClasses );
    }
    if ( RetValue == 0 || pAig->vGateClasses == NULL )
        return RetValue;
    // start the manager
    clk = clock();
    p = Gla_ManStart( pAig, pPars );
    p->timeInit = clock() - clk;
    p->pSat->fVerbose = p->pPars->fVerbose;
    sat_solver2_set_learntmax( p->pSat, pPars->nLearntMax );
    // set runtime limit
    if ( p->pPars->nTimeOut )
        sat_solver2_set_runtime_limit( p->pSat, time(NULL) + p->pPars->nTimeOut - 1 );
    // perform initial abstraction
    if ( p->pPars->fVerbose )
    {
        Abc_Print( 1, "Running gate-level abstraction (GLA) with the following parameters:\n" );
        Abc_Print( 1, "FrameStart = %d  FrameMax = %d  Conf = %d  Timeout = %d. RatioMin = %d %%.\n", 
            p->pPars->nFramesStart, p->pPars->nFramesMax, p->pPars->nConfLimit, p->pPars->nTimeOut, pPars->nRatioMin );
        Abc_Print( 1, "Frame   %%   Abs  PPI   FF   AND   Confl  Cex    SatVar   Core     Time\n" );
    }
    for ( f = i = 0; !p->pPars->nFramesMax || f < p->pPars->nFramesMax; f++ )
    {
        int nConflsBeg = sat_solver2_nconflicts(p->pSat);
        p->pPars->iFrame = f;
        // load timeframe
        Gia_GlaAddTimeFrame( p, f );
        // create bookmark to be used for rollback
//            sat_solver2_reducedb( p->pSat );
        sat_solver2_bookmark( p->pSat );
        Vec_IntClear( p->vAddedNew );
        p->nAbsOld = Vec_IntSize( p->vAbs );
//        nClaOld = Vec_IntSize( p->vCla2Obj );
        // iterate as long as there are counter-examples
        for ( i = 0; ; i++ )
        { 
            clk2 = clock();
            vCore = Gla_ManUnsatCore( p, f, p->vCla2Obj, p->pSat, pPars->nConfLimit, pPars->fVerbose, &Status, &nConfls );
            assert( (vCore != NULL) == (Status == 1) );
            if ( Status == -1 ) // resource limit is reached
            {
                Gla_ManRollBack( p );
                goto finish;
            }
            if ( vCore != NULL )
            {
                p->timeUnsat += clock() - clk2;
                break;
            }
            p->timeSat += clock() - clk2;
            assert( Status == 0 );
            p->nCexes++;
            // perform the refinement
            clk2 = clock();
//            pCex = Vta_ManRefineAbstraction( p, f );
            pCex = NULL;

            vPPis = Gla_ManCollectPPis( p );
            Gla_ManExplorePPis( p, vPPis );
            Gia_GlaAddToAbs( p, vPPis, 1 );
            Gia_GlaAddOneSlice( p, f, vPPis );
            Vec_IntFree( vPPis );

            p->timeCex += clock() - clk2;
            if ( pCex != NULL )
            {
                RetValue = 0;
                goto finish;
            }
            // print the result (do not count it towards change)
            if ( p->pPars->fVerbose )
            Gla_ManAbsPrintFrame( p, -1, f+1, sat_solver2_nconflicts(p->pSat)-nConflsBeg, i, clock() - clk );
        }
        assert( Status == 1 );
        // valid core is obtained
        nCoreSize = Vec_IntSize(vCore);
        if ( i == 0 )
            Vec_IntFree( vCore );
        else
        {
            // update the SAT solver
            sat_solver2_rollback( p->pSat );
            // update storage
            Gla_ManRollBack( p );
            Vec_IntShrink( p->vCla2Obj, (int)p->pSat->stats.clauses+1 );
            // load this timeframe
            Gia_GlaAddToAbs( p, vCore, 0 );
            Gia_GlaAddOneSlice( p, f, vCore );
            Vec_IntFree( vCore );
            // run SAT solver
            clk2 = clock();
            vCore = Gla_ManUnsatCore( p, f, p->vCla2Obj, p->pSat, pPars->nConfLimit, p->pPars->fVerbose, &Status, &nConfls );
            p->timeUnsat += clock() - clk2;
            assert( (vCore != NULL) == (Status == 1) );
            Vec_IntFree( vCore );
            if ( Status == -1 ) // resource limit is reached
                break;
            if ( Status == 0 )
            {
    //            Vta_ManSatVerify( p );
                // make sure, there was no initial abstraction (otherwise, it was invalid)
                assert( pAig->vObjClasses == NULL && f < p->pPars->nFramesStart );
    //            pCex = Vga_ManDeriveCex( p );
                RetValue = 0;
                break;
            }
        }
        // print the result
        if ( p->pPars->fVerbose )
        Gla_ManAbsPrintFrame( p, nCoreSize, f+1, sat_solver2_nconflicts(p->pSat)-nConflsBeg, i, clock() - clk );

        // dump the model
        if ( p->pPars->fDumpVabs && (f & 1) )
        {
            Abc_FrameSetCex( NULL );
            Abc_FrameSetNFrames( f+1 );
            Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "write_status gla.status" );
            Gia_GlaDumpAbsracted( p, pPars->fVerbose );
        }

        // check if the number of objects is below limit
        if ( Gia_GlaAbsCount(p,0,0) >= (p->nObjs - 1) * (100 - pPars->nRatioMin) / 100 )
        {
            Status = -1;
            break;
        }
    }
finish:
    // analize the results
    if ( pCex == NULL )
    {
        if ( pAig->vGateClasses != NULL )
            Abc_Print( 1, "Replacing the old abstraction by a new one.\n" );
        Vec_IntFreeP( &pAig->vGateClasses );
        pAig->vGateClasses = Gla_ManTranslate( p );
        if ( Status == -1 )
        {
            if ( p->pPars->nTimeOut && time(NULL) >= p->pSat->nRuntimeLimit ) 
                Abc_Print( 1, "SAT solver ran out of time at %d sec in frame %d.  ", p->pPars->nTimeOut, f );
            else if ( pPars->nConfLimit && sat_solver2_nconflicts(p->pSat) >= pPars->nConfLimit )
                Abc_Print( 1, "SAT solver ran out of resources at %d conflicts in frame %d.  ", pPars->nConfLimit, f );
            else if ( Gia_GlaAbsCount(p,0,0) >= (p->nObjs - 1) * (100 - pPars->nRatioMin) / 100 )
                Abc_Print( 1, "The ratio of abstracted objects is less than %d %% in frame %d.  ", pPars->nRatioMin, f );
            else
                Abc_Print( 1, "Abstraction stopped for unknown reason in frame %d.  ", f );
        }
        else
            Abc_Print( 1, "SAT solver completed %d frames and produced an abstraction.  ", f );
    }
    else
    {
        ABC_FREE( p->pGia->pCexSeq );
        p->pGia->pCexSeq = pCex;
        if ( !Gia_ManVerifyCex( p->pGia, pCex, 0 ) )
            Abc_Print( 1, "    Gia_GlaPerform(): CEX verification has failed!\n" );
        Abc_Print( 1, "Counter-example detected in frame %d.  ", f );
        p->pPars->iFrame = pCex->iFrame - 1;
    }
    Abc_PrintTime( 1, "Time", clock() - clk );
    p->timeOther = (clock() - clk) - p->timeUnsat - p->timeSat - p->timeCex - p->timeInit;
    ABC_PRTP( "Runtime: Initializing", p->timeInit,   clock() - clk );
    ABC_PRTP( "Runtime: Solver UNSAT", p->timeUnsat,  clock() - clk );
    ABC_PRTP( "Runtime: Solver SAT  ", p->timeSat,    clock() - clk );
    ABC_PRTP( "Runtime: Refinement  ", p->timeCex,    clock() - clk );
    ABC_PRTP( "Runtime: Other       ", p->timeOther,  clock() - clk );
    ABC_PRTP( "Runtime: TOTAL       ", clock() - clk, clock() - clk );
    Gla_ManReportMemory( p );
    Gla_ManStop( p );
    fflush( stdout );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

