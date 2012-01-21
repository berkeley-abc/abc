/**CFile****************************************************************

  FileName    [saigBmc3.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Simple BMC package.]

  Author      [Alan Mishchenko in collaboration with Niklas Een.]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigBmc3.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "src/proof/fra/fra.h"
#include "src/sat/cnf/cnf.h"
#include "src/sat/bsat/satStore.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Gia_ManBmc_t_ Gia_ManBmc_t;
struct Gia_ManBmc_t_
{
    // input/output data
    Saig_ParBmc_t *   pPars;       // parameters
    Aig_Man_t *       pAig;        // user AIG
    Vec_Ptr_t *       vCexes;      // counter-examples
    // intermediate data
    Vec_Int_t *       vMapping;    // mapping
    Vec_Vec_t *       vSects;      // sections
    Vec_Int_t *       vId2Num;     // number of each node 
    Vec_Int_t *       vVisited;    // visited nodes
    // SAT variables
    Vec_Int_t *       vPiVars;     // SAT vars for the PIs 
    Vec_Ptr_t *       vId2Var;     // SAT vars for each object
    // SAT solver
    sat_solver *      pSat;        // SAT solver
    int               nSatVars;    // SAT variables
    int               nObjNums;    // SAT objects
    int               nBufNum;     // the number of simple nodes
    int               nDupNum;     // the number of simple nodes
    char * pSopSizes, ** pSops;    // CNF representation
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

#define SAIG_TER_ZER 1
#define SAIG_TER_ONE 2
#define SAIG_TER_UND 3

static inline int Saig_ManBmcSimInfoNot( int Value )
{
    if ( Value == SAIG_TER_ZER )
        return SAIG_TER_ONE;
    if ( Value == SAIG_TER_ONE )
        return SAIG_TER_ZER;
    return SAIG_TER_UND;
}

static inline int Saig_ManBmcSimInfoAnd( int Value0, int Value1 )
{
    if ( Value0 == SAIG_TER_ZER || Value1 == SAIG_TER_ZER )
        return SAIG_TER_ZER;
    if ( Value0 == SAIG_TER_ONE && Value1 == SAIG_TER_ONE )
        return SAIG_TER_ONE;
    return SAIG_TER_UND;
}

static inline int Saig_ManBmcSimInfoGet( unsigned * pInfo, Aig_Obj_t * pObj )
{
    return 3 & (pInfo[Aig_ObjId(pObj) >> 4] >> ((Aig_ObjId(pObj) & 15) << 1));
}

static inline void Saig_ManBmcSimInfoSet( unsigned * pInfo, Aig_Obj_t * pObj, int Value )
{
    assert( Value >= SAIG_TER_ZER && Value <= SAIG_TER_UND );
    Value ^= Saig_ManBmcSimInfoGet( pInfo, pObj );
    pInfo[Aig_ObjId(pObj) >> 4] ^= (Value << ((Aig_ObjId(pObj) & 15) << 1));
}

/**Function*************************************************************

  Synopsis    [Returns the number of LIs with binary ternary info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManBmcTerSimCount01( Aig_Man_t * p, unsigned * pInfo )
{
    Aig_Obj_t * pObj;
    int i, Counter = 0;
    if ( pInfo == NULL )
        return Saig_ManRegNum(p);
    Saig_ManForEachLi( p, pObj, i )
        if ( !Aig_ObjIsConst1(Aig_ObjFanin0(pObj)) )
            Counter += (Saig_ManBmcSimInfoGet(pInfo, pObj) != SAIG_TER_UND);
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Performs ternary simulation of one frame.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Saig_ManBmcTerSimOne( Aig_Man_t * p, unsigned * pPrev )
{
    Aig_Obj_t * pObj, * pObjLi;
    unsigned * pInfo;
    int i, Val0, Val1;
    pInfo = ABC_CALLOC( unsigned, Abc_BitWordNum(2 * Aig_ManObjNumMax(p)) );
    Saig_ManBmcSimInfoSet( pInfo, Aig_ManConst1(p), SAIG_TER_ONE );
    Saig_ManForEachPi( p, pObj, i )
        Saig_ManBmcSimInfoSet( pInfo, pObj, SAIG_TER_UND );
    if ( pPrev == NULL )
    {
        Saig_ManForEachLo( p, pObj, i )
            Saig_ManBmcSimInfoSet( pInfo, pObj, SAIG_TER_ZER );
    }
    else
    {
        Saig_ManForEachLiLo( p, pObjLi, pObj, i )
            Saig_ManBmcSimInfoSet( pInfo, pObj, Saig_ManBmcSimInfoGet(pPrev, pObjLi) );
    }
    Aig_ManForEachNode( p, pObj, i )
    {
        Val0 = Saig_ManBmcSimInfoGet( pInfo, Aig_ObjFanin0(pObj) );
        Val1 = Saig_ManBmcSimInfoGet( pInfo, Aig_ObjFanin1(pObj) );
        if ( Aig_ObjFaninC0(pObj) )
            Val0 = Saig_ManBmcSimInfoNot( Val0 );
        if ( Aig_ObjFaninC1(pObj) )
            Val1 = Saig_ManBmcSimInfoNot( Val1 );
        Saig_ManBmcSimInfoSet( pInfo, pObj, Saig_ManBmcSimInfoAnd(Val0, Val1) );
    }
    Aig_ManForEachPo( p, pObj, i )
    {
        Val0 = Saig_ManBmcSimInfoGet( pInfo, Aig_ObjFanin0(pObj) );
        if ( Aig_ObjFaninC0(pObj) )
            Val0 = Saig_ManBmcSimInfoNot( Val0 );
        Saig_ManBmcSimInfoSet( pInfo, pObj, Val0 );
    }
    return pInfo;    
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes and PIs in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Saig_ManBmcTerSim( Aig_Man_t * p )
{
    Vec_Ptr_t * vInfos;
    unsigned * pInfo = NULL;
    int i, TerPrev = ABC_INFINITY, TerCur, CountIncrease = 0;
    vInfos = Vec_PtrAlloc( 100 );
    for ( i = 0; i < 1000 && CountIncrease < 5 && TerPrev > 0; i++ )
    {
        TerCur = Saig_ManBmcTerSimCount01( p, pInfo );
        if ( TerCur >= TerPrev )
            CountIncrease++;
        TerPrev = TerCur;
        pInfo = Saig_ManBmcTerSimOne( p, pInfo );
        Vec_PtrPush( vInfos, pInfo );
    }
    return vInfos;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManBmcTerSimTest( Aig_Man_t * p )
{
    Vec_Ptr_t * vInfos;
    unsigned * pInfo;
    int i;
    vInfos = Saig_ManBmcTerSim( p );
    Vec_PtrForEachEntry( unsigned *, vInfos, pInfo, i )
        printf( "%d=%d ", i, Saig_ManBmcTerSimCount01(p, pInfo) );
    printf( "\n" );
    Vec_PtrFreeFree( vInfos );
}



/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManBmcDfs_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    assert( !Aig_IsComplement(pObj) );
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    if ( Aig_ObjIsNode(pObj) )
    {
        Saig_ManBmcDfs_rec( p, Aig_ObjFanin0(pObj), vNodes );
        Saig_ManBmcDfs_rec( p, Aig_ObjFanin1(pObj), vNodes );
    }
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes and PIs in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Saig_ManBmcDfsNodes( Aig_Man_t * p, Vec_Ptr_t * vRoots )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj;
    int i;
    vNodes = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vRoots, pObj, i )
        Saig_ManBmcDfs_rec( p, Aig_ObjFanin0(pObj), vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * Saig_ManBmcSections( Aig_Man_t * p )
{
    Vec_Ptr_t * vSects, * vRoots, * vCone;
    Aig_Obj_t * pObj, * pObjPo;
    int i;
    Aig_ManIncrementTravId( p );
    Aig_ObjSetTravIdCurrent( p, Aig_ManConst1(p) );
    // start the roots
    vRoots = Vec_PtrAlloc( 1000 );
    Saig_ManForEachPo( p, pObjPo, i )
    {
        Aig_ObjSetTravIdCurrent( p, pObjPo );
        Vec_PtrPush( vRoots, pObjPo );
    }
    // compute the cones
    vSects = Vec_PtrAlloc( 20 );
    while ( Vec_PtrSize(vRoots) > 0 )
    {
        vCone = Saig_ManBmcDfsNodes( p, vRoots );
        Vec_PtrPush( vSects, vCone );
        // get the next set of roots
        Vec_PtrClear( vRoots );
        Vec_PtrForEachEntry( Aig_Obj_t *, vCone, pObj, i )
        {
            if ( !Saig_ObjIsLo(p, pObj) )
                continue;
            pObjPo = Saig_ObjLoToLi( p, pObj );
            if ( Aig_ObjIsTravIdCurrent(p, pObjPo) )
                continue;
            Aig_ObjSetTravIdCurrent( p, pObjPo );
            Vec_PtrPush( vRoots, pObjPo );
        }
    }
    Vec_PtrFree( vRoots );
    return (Vec_Vec_t *)vSects;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManBmcSectionsTest( Aig_Man_t * p )
{
    Vec_Vec_t * vSects;
    Vec_Ptr_t * vOne;
    int i;
    vSects = Saig_ManBmcSections( p );
    Vec_VecForEachLevel( vSects, vOne, i )
        printf( "%d=%d ", i, Vec_PtrSize(vOne) );
    printf( "\n" );
    Vec_VecFree( vSects );
}



/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManBmcSupergate_rec( Aig_Obj_t * pObj, Vec_Ptr_t * vSuper )
{
    // if the new node is complemented or a PI, another gate begins
    if ( Aig_IsComplement(pObj) || Aig_ObjIsPi(pObj) ) // || (Aig_ObjRefs(pObj) > 1) )
    {
        Vec_PtrPushUnique( vSuper, Aig_Regular(pObj) );
        return;
    }
    // go through the branches
    Saig_ManBmcSupergate_rec( Aig_ObjChild0(pObj), vSuper );
    Saig_ManBmcSupergate_rec( Aig_ObjChild1(pObj), vSuper );
}

/**Function*************************************************************

  Synopsis    [Collect the topmost supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Saig_ManBmcSupergate( Aig_Man_t * p, int iPo )
{
    Vec_Ptr_t * vSuper;
    Aig_Obj_t * pObj;
    vSuper = Vec_PtrAlloc( 10 );
    pObj = Aig_ManPo( p, iPo );
    pObj = Aig_ObjChild0( pObj );
    if ( !Aig_IsComplement(pObj) )
    {
        Vec_PtrPush( vSuper, pObj );
        return vSuper;
    }
    pObj = Aig_Regular( pObj );
    if ( !Aig_ObjIsNode(pObj) )
    {
        Vec_PtrPush( vSuper, pObj );
        return vSuper;
    }
    Saig_ManBmcSupergate_rec( Aig_ObjChild0(pObj), vSuper );
    Saig_ManBmcSupergate_rec( Aig_ObjChild1(pObj), vSuper );
    return vSuper;
}

/**Function*************************************************************

  Synopsis    [Returns the number of nodes with ref counter more than 1.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManBmcCountRefed( Aig_Man_t * p, Vec_Ptr_t * vSuper )
{
    Aig_Obj_t * pObj;
    int i, Counter = 0;
    Vec_PtrForEachEntry( Aig_Obj_t *, vSuper, pObj, i )
    {
        assert( !Aig_IsComplement(pObj) );
        Counter += (Aig_ObjRefs(pObj) > 1);
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManBmcSupergateTest( Aig_Man_t * p )
{
    Vec_Ptr_t * vSuper;
    Aig_Obj_t * pObj;
    int i;
    printf( "Supergates: " );
    Saig_ManForEachPo( p, pObj, i )
    {
        vSuper = Saig_ManBmcSupergate( p, i );
        printf( "%d=%d(%d) ", i, Vec_PtrSize(vSuper), Saig_ManBmcCountRefed(p, vSuper) );
        Vec_PtrFree( vSuper );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManBmcWriteBlif( Aig_Man_t * p, Vec_Int_t * vMapping, char * pFileName )
{
    FILE * pFile;
    char * pSopSizes, ** pSops;
    Aig_Obj_t * pObj;
    char Vals[4];
    int i, k, b, iFan, iTruth, * pData;
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file %s\n", pFileName );
        return;
    }
    fprintf( pFile, ".model test\n" );
    fprintf( pFile, ".inputs" );
    Aig_ManForEachPi( p, pObj, i )
        fprintf( pFile, " n%d", Aig_ObjId(pObj) );
    fprintf( pFile, "\n" );
    fprintf( pFile, ".outputs" );
    Aig_ManForEachPo( p, pObj, i )
        fprintf( pFile, " n%d", Aig_ObjId(pObj) );
    fprintf( pFile, "\n" );
    fprintf( pFile, ".names" );
    fprintf( pFile, " n%d\n", Aig_ObjId(Aig_ManConst1(p)) );
    fprintf( pFile, " 1\n" );

    Cnf_ReadMsops( &pSopSizes, &pSops );
    Aig_ManForEachNode( p, pObj, i )
    {
        if ( Vec_IntEntry(vMapping, i) == 0 )
            continue;
        pData = Vec_IntEntryP( vMapping, Vec_IntEntry(vMapping, i) );
        fprintf( pFile, ".names" );
        for ( iFan = 0; iFan < 4; iFan++ )
            if ( pData[iFan+1] >= 0 )
                fprintf( pFile, " n%d", pData[iFan+1] );
            else
                break;
        fprintf( pFile, " n%d\n", i );
        // write SOP
        iTruth = pData[0] & 0xffff;
        for ( k = 0; k < pSopSizes[iTruth]; k++ )
        {
            int Lit = pSops[iTruth][k];
            for ( b = 3; b >= 0; b-- )
            {
                if ( Lit % 3 == 0 )
                    Vals[b] = '0';
                else if ( Lit % 3 == 1 )
                    Vals[b] = '1';
                else
                    Vals[b] = '-';
                Lit = Lit / 3;
            }
            for ( b = 0; b < iFan; b++ )
                fprintf( pFile, "%c", Vals[b] );
            fprintf( pFile, " 1\n" );
        }
    }
    free( pSopSizes );
    free( pSops[1] );
    free( pSops );

    Aig_ManForEachPo( p, pObj, i )
    {
        fprintf( pFile, ".names" );
        fprintf( pFile, " n%d", Aig_ObjId(Aig_ObjFanin0(pObj)) );
        fprintf( pFile, " n%d\n", Aig_ObjId(pObj) );
        fprintf( pFile, "%d 1\n", !Aig_ObjFaninC0(pObj) );
    }
    fprintf( pFile, ".end\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManBmcMappingTest( Aig_Man_t * p )
{
    Vec_Int_t * vMapping;
    vMapping = Cnf_DeriveMappingArray( p );
    Saig_ManBmcWriteBlif( p, vMapping, "test.blif" );
    Vec_IntFree( vMapping );
}



/**Function*************************************************************

  Synopsis    [Create manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_ManBmc_t * Saig_Bmc3ManStart( Aig_Man_t * pAig )
{
    Gia_ManBmc_t * p;
    Aig_Obj_t * pObj;
    int i;
//    assert( Aig_ManRegNum(pAig) > 0 );
    p = ABC_CALLOC( Gia_ManBmc_t, 1 );
    p->pAig = pAig;
    // create mapping
    p->vMapping = Cnf_DeriveMappingArray( pAig );
    // create sections
    p->vSects = Saig_ManBmcSections( pAig );
    // map object IDs into their numbers and section numbers
    p->nObjNums = 0;
    p->vId2Num  = Vec_IntStartFull( Aig_ManObjNumMax(pAig) );
    Vec_IntWriteEntry( p->vId2Num,  Aig_ObjId(Aig_ManConst1(pAig)), p->nObjNums++ );
    Aig_ManForEachPi( pAig, pObj, i )
        Vec_IntWriteEntry( p->vId2Num,  Aig_ObjId(pObj), p->nObjNums++ );
    Aig_ManForEachNode( pAig, pObj, i )
        if ( Vec_IntEntry(p->vMapping, Aig_ObjId(pObj)) > 0 )
            Vec_IntWriteEntry( p->vId2Num,  Aig_ObjId(pObj), p->nObjNums++ );
    Aig_ManForEachPo( pAig, pObj, i )
        Vec_IntWriteEntry( p->vId2Num,  Aig_ObjId(pObj), p->nObjNums++ );
    p->vPiVars  = Vec_IntAlloc( 1000 );
    p->vId2Var  = Vec_PtrAlloc( 100 );
    p->vVisited = Vec_IntAlloc( 1000 );
    // create solver
    p->nSatVars = 1;
    p->pSat     = sat_solver_new();
    sat_solver_setnvars( p->pSat, 1000 );
    Cnf_ReadMsops( &p->pSopSizes, &p->pSops );
    return p;
}

/**Function*************************************************************

  Synopsis    [Delete manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_Bmc3ManStop( Gia_ManBmc_t * p )
{
    Aig_ManCleanMarkA( p->pAig );
    if ( p->vCexes )
    {
        assert( p->pAig->vSeqModelVec == NULL );
        p->pAig->vSeqModelVec = p->vCexes;
        p->vCexes = NULL;
    }
//    Vec_PtrFreeFree( p->vCexes );
    Vec_IntFree( p->vMapping );
    Vec_VecFree( p->vSects );
    Vec_IntFree( p->vId2Num );
    Vec_IntFree( p->vPiVars );
    Vec_IntFree( p->vVisited );
    Vec_VecFree( (Vec_Vec_t *)p->vId2Var );
    sat_solver_delete( p->pSat );
    free( p->pSopSizes );
    free( p->pSops[1] );
    free( p->pSops );
    free( p );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int * Saig_ManBmcMapping( Gia_ManBmc_t * p, Aig_Obj_t * pObj )
{
    if ( Vec_IntEntry(p->vMapping, Aig_ObjId(pObj)) == 0 )
        return NULL;
    return Vec_IntEntryP( p->vMapping, Vec_IntEntry(p->vMapping, Aig_ObjId(pObj)) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Saig_ManBmcLiteral( Gia_ManBmc_t * p, Aig_Obj_t * pObj, int iFrame )
{
    Vec_Int_t * vFrame;
    int ObjNum;
    assert( !Aig_ObjIsNode(pObj) || Saig_ManBmcMapping(p, pObj) );
    ObjNum  = Vec_IntEntry( p->vId2Num, Aig_ObjId(pObj) );
    assert( ObjNum >= 0 );
    vFrame  = (Vec_Int_t *)Vec_PtrEntry( p->vId2Var, iFrame );
    assert( vFrame != NULL );
    return Vec_IntEntry( vFrame, ObjNum );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Saig_ManBmcSetLiteral( Gia_ManBmc_t * p, Aig_Obj_t * pObj, int iFrame, int iLit )
{
    Vec_Int_t * vFrame;
    int ObjNum;
    assert( !Aig_ObjIsNode(pObj) || Saig_ManBmcMapping(p, pObj) );
    ObjNum  = Vec_IntEntry( p->vId2Num, Aig_ObjId(pObj) );
    vFrame  = (Vec_Int_t *)Vec_PtrEntry( p->vId2Var, iFrame );
    Vec_IntWriteEntry( vFrame, ObjNum, iLit );
    if ( iLit == ABC_INFINITY || iLit == ABC_INFINITY+1 )
    {
        Vec_IntPush( p->vVisited, Aig_ObjId(pObj) );
        Vec_IntPush( p->vVisited, iFrame );
    }
    else if ( iLit != ~0 && Saig_ObjIsPi(p->pAig, pObj) ) // save PI SAT var num
        Vec_IntWriteEntry( p->vPiVars, iFrame*Saig_ManPiNum(p->pAig)+Aig_ObjPioNum(pObj), lit_var(iLit) );
    return iLit;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Saig_ManBmcCof0( int t, int v )
{
    static int s_Truth[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    return 0xffff & ((t & ~s_Truth[v]) | ((t & ~s_Truth[v]) << (1<<v)));
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Saig_ManBmcCof1( int t, int v )
{
    static int s_Truth[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    return 0xffff & ((t & s_Truth[v]) | ((t & s_Truth[v]) >> (1<<v)));
}

/**Function*************************************************************

  Synopsis    [Derives CNF for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Saig_ManBmcDeriveTruth( int uTruth, int Lits[] )
{
    int v;
    for ( v = 0; v < 4; v++ )
        if ( Lits[v] == 0 )
        {
            uTruth = Saig_ManBmcCof0(uTruth, v);
            Lits[v] = -1;
        }
        else if ( Lits[v] == 1 )
        {
            uTruth = Saig_ManBmcCof1(uTruth, v);
            Lits[v] = -1;
        }
    for ( v = 0; v < 4; v++ )
        if ( Lits[v] == -1 )
            assert( Saig_ManBmcCof0(uTruth, v) == Saig_ManBmcCof1(uTruth, v) );
    return uTruth;
}

/*
void Cnf_SopConvertToVector( char * pSop, int nCubes, Vec_Int_t * vCover )
{
    int Lits[4], Cube, iCube, i, b;
    Vec_IntClear( vCover );
    for ( i = 0; i < nCubes; i++ )
    {
        Cube = pSop[i];
        for ( b = 0; b < 4; b++ )
        {
            if ( Cube % 3 == 0 )
                Lits[b] = 1;
            else if ( Cube % 3 == 1 )
                Lits[b] = 2;
            else
                Lits[b] = 0;
            Cube = Cube / 3;
        }
        iCube = 0;
        for ( b = 0; b < 4; b++ )
            iCube = (iCube << 2) | Lits[b];
        Vec_IntPush( vCover, iCube );
    }
}

        Vec_IntForEachEntry( vCover, Cube, k )
        {
            *pClas++ = pLits;
            *pLits++ = 2 * OutVar; 
            pLits += Cnf_IsopWriteCube( Cube, pCut->nFanins, pVars, pLits );
        }


int Cnf_IsopWriteCube( int Cube, int nVars, int * pVars, int * pLiterals )
{
    int nLits = nVars, b;
    for ( b = 0; b < nVars; b++ )
    {
        if ( (Cube & 3) == 1 ) // value 0 --> write positive literal
            *pLiterals++ = 2 * pVars[b];
        else if ( (Cube & 3) == 2 ) // value 1 --> write negative literal
            *pLiterals++ = 2 * pVars[b] + 1;
        else
            nLits--;
        Cube >>= 2;
    }
    return nLits;
}

        iTruth = pData[0] & 0xffff;
        for ( k = 0; k < pSopSizes[iTruth]; k++ )
        {
            int Lit = pSops[iTruth][k];
            for ( b = 3; b >= 0; b-- )
            {
                if ( Lit % 3 == 0 )
                    Vals[b] = '0';
                else if ( Lit % 3 == 1 )
                    Vals[b] = '1';
                else
                    Vals[b] = '-';
                Lit = Lit / 3;
            }
            for ( b = 0; b < iFan; b++ )
                fprintf( pFile, "%c", Vals[b] );
            fprintf( pFile, " 1\n" );
        }
*/

/**Function*************************************************************

  Synopsis    [Derives CNF for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Saig_ManBmcAddClauses( Gia_ManBmc_t * p, int uTruth, int Lits[], int iLitOut )
{
    int i, k, b, CutLit, nClaLits, ClaLits[5];
    assert( uTruth > 0 && uTruth < 0xffff );
    // write positive/negative polarity
    for ( i = 0; i < 2; i++ )
    {
        if ( i )
            uTruth = 0xffff & ~uTruth;
//        Extra_PrintBinary( stdout, &uTruth, 16 ); printf( "\n" );
        for ( k = 0; k < p->pSopSizes[uTruth]; k++ )
        {
            nClaLits = 0;
            ClaLits[nClaLits++] = i ? lit_neg(iLitOut) : iLitOut;
            CutLit = p->pSops[uTruth][k];
            for ( b = 3; b >= 0; b-- )
            {
                if ( CutLit % 3 == 0 ) // value 0 --> write positive literal
                {
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = Lits[b];
                }
                else if ( CutLit % 3 == 1 ) // value 1 --> write negative literal
                {
                    assert( Lits[b] > 1 );
                    ClaLits[nClaLits++] = lit_neg(Lits[b]);
                }
                CutLit = CutLit / 3;
            }

//            for ( b = 0; b < nClaLits; b++ )
//                printf( "%d ", ClaLits[b] );
//            printf( "\n" );

            if ( !sat_solver_addclause( p->pSat, ClaLits, ClaLits+nClaLits ) )
                assert( 0 );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Derives CNF for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManBmcCreateCnf_rec( Gia_ManBmc_t * p, Aig_Obj_t * pObj, int iFrame, int fAddClauses )
{
    int * pMapping, i, iLit, Lits[4], uTruth;
    iLit = Saig_ManBmcLiteral( p, pObj, iFrame );
    if ( iLit != ~0 )
        return iLit;
    assert( iFrame >= 0 );
    if ( Aig_ObjIsPi(pObj) )
    {
        if ( Saig_ObjIsPi(p->pAig, pObj) )
            iLit = fAddClauses ? toLit( p->nSatVars++ ) : ABC_INFINITY;
        else
            iLit = Saig_ManBmcCreateCnf_rec( p, Saig_ObjLoToLi(p->pAig, pObj), iFrame-1, fAddClauses );
        return Saig_ManBmcSetLiteral( p, pObj, iFrame, iLit );
    }
    if ( Aig_ObjIsPo(pObj) )
    {
        iLit = Saig_ManBmcCreateCnf_rec( p, Aig_ObjFanin0(pObj), iFrame, fAddClauses );
        if ( Aig_ObjFaninC0(pObj) )
            iLit = lit_neg(iLit);
        return Saig_ManBmcSetLiteral( p, pObj, iFrame, iLit );
    }
    assert( Aig_ObjIsNode(pObj) );
    pMapping = Saig_ManBmcMapping( p, pObj );
    for ( i = 0; i < 4; i++ )
        if ( pMapping[i+1] == -1 )
            Lits[i] = -1;
        else
            Lits[i] = Saig_ManBmcCreateCnf_rec( p, Aig_ManObj(p->pAig, pMapping[i+1]), iFrame, fAddClauses );
    // derive new truth table
//uTruth = 0xffff & (unsigned)pMapping[0];
//printf( "Truth : " );
//Extra_PrintBinary( stdout, &uTruth, 16 ); printf( "\n" );
    uTruth = Saig_ManBmcDeriveTruth( 0xffff & (unsigned)pMapping[0], Lits );
    if ( uTruth == 0 || uTruth == 0xffff )
    {
        iLit = (uTruth == 0xffff);
        return Saig_ManBmcSetLiteral( p, pObj, iFrame, iLit );
    }
    // create CNF
    if ( fAddClauses )
    {
        iLit = toLit( p->nSatVars++ );
        Saig_ManBmcAddClauses( p, uTruth, Lits, iLit );

        if ( uTruth == 0xAAAA || (0xffff & ~uTruth) == 0xAAAA ||
             uTruth == 0xCCCC || (0xffff & ~uTruth) == 0xCCCC ||
             uTruth == 0xF0F0 || (0xffff & ~uTruth) == 0xF0F0 ||
             uTruth == 0xFF00 || (0xffff & ~uTruth) == 0xFF00 )
                   p->nBufNum++;

        if ( (Lits[0] > 1 && (Lits[0] == Lits[1] || Lits[0] == Lits[2] || Lits[0] == Lits[3]))   ||
             (Lits[1] > 1 && (Lits[1] == Lits[2] || Lits[1] == Lits[2]))                         ||
             (Lits[2] > 1 && (Lits[2] == Lits[3]))    )
                   p->nDupNum++;

    }
    else
    {
        iLit = ABC_INFINITY;
    }
    return Saig_ManBmcSetLiteral( p, pObj, iFrame, iLit );
}

/**Function*************************************************************

  Synopsis    [Derives CNF for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManBmcCreateCnf( Gia_ManBmc_t * p, Aig_Obj_t * pObj, int iFrame )
{
    int i, iLit, Entry, iFrameOld, Value;
    Vec_IntClear( p->vVisited );
    iLit = Saig_ManBmcCreateCnf_rec( p, pObj, iFrame, 0 );
    Vec_IntForEachEntry( p->vVisited, Entry, i )
    {
        iFrameOld = Vec_IntEntry( p->vVisited, ++i );
        Value = Saig_ManBmcLiteral( p, Aig_ManObj(p->pAig, Entry), iFrameOld );
//        assert( Value == 0 || Value == 1 || Value == ABC_INFINITY || Value == ABC_INFINITY+1 );
        assert( Value == ABC_INFINITY || Value == ABC_INFINITY+1 );
        if ( !(Value == ABC_INFINITY || Value == ABC_INFINITY+1) )
            printf( "Internal error!\n" );
//        if ( Value == 0 || Value == 1 )
//            continue;
        Saig_ManBmcSetLiteral( p, Aig_ManObj(p->pAig, Entry), iFrameOld, ~0 );
    }
    if ( iLit < 2 )
        return iLit;
    return Saig_ManBmcCreateCnf_rec( p, pObj, iFrame, 1 );
}



/**Function*************************************************************

  Synopsis    [Procedure used for sorting the nodes in decreasing order of levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_NodeCompareRefsIncrease( Aig_Obj_t ** pp1, Aig_Obj_t ** pp2 )
{
    int Diff = Aig_ObjRefs(*pp1) - Aig_ObjRefs(*pp2);
    if ( Diff < 0 )
        return -1;
    if ( Diff > 0 ) 
        return 1;
    Diff = Aig_ObjId(*pp1) - Aig_ObjId(*pp2);
    if ( Diff < 0 )
        return -1;
    if ( Diff > 0 ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Mark PIs to be skipped based on nPisAbstract.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ManBmcMarkPis( Aig_Man_t * pAig, int nPisAbstract )
{
    Vec_Ptr_t * vPis;
    Aig_Obj_t * pObj;
    int i;
    if ( nPisAbstract < 1 )
        return;
    // sort PIs by the number of their fanouts
    vPis = Vec_PtrAlloc( 100 );
    Saig_ManForEachPi( pAig, pObj, i )
        Vec_PtrPush( vPis, pObj );
    Vec_PtrSort( vPis, (int (*)(void))Aig_NodeCompareRefsIncrease );
    Vec_PtrForEachEntry( Aig_Obj_t *, vPis, pObj, i )
    {
        if ( i < nPisAbstract )
        {
            pObj->fMarkA = 1;
//            printf( "%d=%d ", Aig_ObjPioNum(pObj), Aig_ObjRefs(pObj) );
        }
    }
//    printf( "\n" );
    // print primary inputs
//    Saig_ManForEachPi( pAig, pObj, i )
//        printf( "%d=%d ", i, Aig_ObjRefs(pObj) );
//    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_ParBmcSetDefaultParams( Saig_ParBmc_t * p )
{
    memset( p, 0, sizeof(Saig_ParBmc_t) );
    p->nStart         =     0;    // maximum number of timeframes 
    p->nFramesMax     =  2000;    // maximum number of timeframes 
    p->nConfLimit     =  2000;    // maximum number of conflicts at a node
    p->nConfLimitJump =     0;    // maximum number of conflicts after jumping
    p->nFramesJump    =     0;    // the number of tiemframes to jump
    p->nTimeOut       =     0;    // approximate timeout in seconds
    p->nPisAbstract   =     0;    // the number of PIs to abstract
    p->fSolveAll      =     0;    // stops on the first SAT instance
    p->fDropSatOuts   =     0;    // replace sat outputs by constant 0
    p->fVerbose       =     0;    // verbose 
    p->iFrame         =    -1;    // explored up to this frame
    p->nFailOuts      =     0;    // the number of failed outputs
}

/**Function*************************************************************

  Synopsis    [Bounded model checking engine.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManBmcScalable( Aig_Man_t * pAig, Saig_ParBmc_t * pPars )
{
    Gia_ManBmc_t * p;
    Aig_Obj_t * pObj;
    int RetValue = -1, fFirst = 1, nJumpFrame = 0, fUnfinished = 0;
    int nOutDigits = Abc_Base10Log( Saig_ManPoNum(pAig) - Saig_ManConstrNum(pAig) );
    int i, f, Lit, status, clk, clk2, clkOther = 0, clkTotal = clock();
    int nTimeToStop = time(NULL) + pPars->nTimeOut;
    if ( pPars->fVerbose && Aig_ManConstrNum(pAig) > 0 )
        printf( "Performing BMC with constraints...\n" );
    p = Saig_Bmc3ManStart( pAig );
    p->pPars = pPars;
    if ( pPars->fVerbose )
    {
        printf( "Running \"bmc3\". AIG:  PI/PO/Reg = %d/%d/%d.  Node = %6d. Lev = %5d.  Map = %6d. Sect =%3d.\n", 
            Saig_ManPiNum(pAig), Saig_ManPoNum(pAig), Saig_ManRegNum(pAig),
            Aig_ManNodeNum(pAig), Aig_ManLevelNum(pAig), (Vec_IntSize(p->vMapping)-Aig_ManObjNumMax(pAig))/5, Vec_VecSize(p->vSects) );
        printf( "Params: Start = %d. FramesMax = %d. ConfLimit = %d. TimeOut = %d. SolveAll = %d.\n", 
            pPars->nStart, pPars->nFramesMax, pPars->nConfLimit, pPars->nTimeOut, pPars->fSolveAll );
    } 
    // set runtime limit
    if ( p->pPars->nTimeOut )
        sat_solver_set_runtime_limit( p->pSat, nTimeToStop );
    // perform frames
    Aig_ManRandom( 1 );
    Saig_ManBmcMarkPis( pAig, pPars->nPisAbstract );
    for ( f = 0; f < pPars->nFramesMax; f++ )
    {
        // stop BMC after exploring all reachable states
        if ( Aig_ManRegNum(pAig) < 30 && f == (1 << Aig_ManRegNum(pAig)) )
        {
            Saig_Bmc3ManStop( p );
            return pPars->nFailOuts ? 0 : 1;
        }
        // stop BMC if all targets are solved
        if ( pPars->fSolveAll && pPars->nFailOuts == Saig_ManPoNum(pAig) - Saig_ManConstrNum(pAig) )
        {
            Saig_Bmc3ManStop( p );
            return 0;
        }
        // consider the next timeframe
        if ( RetValue == -1 && pPars->nStart == 0 && !nJumpFrame )
            pPars->iFrame = f-1;
        // resize the array
        Vec_IntFillExtra( p->vPiVars, (f+1)*Saig_ManPiNum(p->pAig), 0 );
        // map nodes of this section
        Vec_PtrPush( p->vId2Var, Vec_IntStartFull(p->nObjNums) );
/*
        if ( f > 2*Vec_VecSize(p->vSects) )
        {
            int iFrameOld = f - 2*Vec_VecSize( p->vSects );
            void * pMemory = Vec_IntReleaseArray( Vec_PtrEntry(p->vId2Var, iFrameOld) );
            ABC_FREE( pMemory );
        } 
*/
        // prepare some nodes
        Saig_ManBmcSetLiteral( p, Aig_ManConst1(pAig), f, 1 );
        if ( f == 0 )
            Saig_ManForEachLo( p->pAig, pObj, i )
                Saig_ManBmcSetLiteral( p, pObj, 0, 0 );
        // set PIs to zero if they are marked
        Saig_ManForEachPi( p->pAig, pObj, i )
            if ( pObj->fMarkA )
                Saig_ManBmcSetLiteral( p, pObj, f, Aig_ManRandom(0) & 1 );
        // add the constraints for this frame
        Saig_ManForEachPo( pAig, pObj, i )
        {
            if ( i < Saig_ManPoNum(pAig) - Saig_ManConstrNum(pAig) )
                continue;            
clk2 = clock();
            Lit = Saig_ManBmcCreateCnf( p, pObj, f );
            Lit = lit_neg( Lit );
clkOther += clock() - clk2;
            status = sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
            if ( status == 0 )
            {
                printf( "SAT problem became UNSAT after adding constraints in frame %d.\n", f );
                Saig_Bmc3ManStop( p );
                return 1;
            }
        }
        if ( (pPars->nStart && f < pPars->nStart) || (nJumpFrame && f < nJumpFrame) )
            continue;
        // solve SAT
        clk = clock(); 
        Saig_ManForEachPo( pAig, pObj, i )
        {
            if ( i >= Saig_ManPoNum(pAig) - Saig_ManConstrNum(pAig) )
                break;
            // skip solved outputs
            if ( p->vCexes && Vec_PtrEntry(p->vCexes, i) )
                continue;
            // add constraints for this output
clk2 = clock();
            Lit = Saig_ManBmcCreateCnf( p, pObj, f );
clkOther += clock() - clk2;
            if ( Lit == 0 )
                continue;
            if ( Lit == 1 )
            {
                Abc_Cex_t * pCex = Abc_CexMakeTriv( Aig_ManRegNum(pAig), Saig_ManPiNum(pAig), Saig_ManPoNum(pAig), f*Saig_ManPoNum(pAig)+i );
                if ( !pPars->fSolveAll )
                {
                    printf( "Output %d is trivially SAT in frame %d.\n", i, f );
                    ABC_FREE( pAig->pSeqModel );
                    pAig->pSeqModel = pCex;
                    Saig_Bmc3ManStop( p );
                    return 0;
                }
                pPars->nFailOuts++;
                printf( "Output %*d was asserted in frame %2d (solved %*d out of %*d outputs).\n",  
                    nOutDigits, i, f, nOutDigits, pPars->nFailOuts, nOutDigits, Saig_ManPoNum(pAig) - Saig_ManConstrNum(pAig) );
                if ( p->vCexes == NULL )
                    p->vCexes = Vec_PtrStart( Saig_ManPoNum(pAig) );
                Vec_PtrWriteEntry( p->vCexes, i, pCex );
                RetValue = 0;
                continue;
            }
            // solve this output
            fUnfinished = 0;
            sat_solver_compress( p->pSat );
            status = sat_solver_solve( p->pSat, &Lit, &Lit + 1, (ABC_INT64_T)pPars->nConfLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
            if ( status == l_False )
            {/*
                Lit = lit_neg( Lit );
                status = sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
                assert( status );
                sat_solver_compress( p->pSat );
              */
            }
            else if ( status == l_True )
            {
                int * pModel = Sat_SolverGetModel( p->pSat, Vec_IntArray(p->vPiVars), Vec_IntSize(p->vPiVars) );
                Abc_Cex_t * pCex = Abc_CexCreate( Aig_ManRegNum(pAig), Saig_ManPiNum(pAig), pModel, f, i, 1 );
                ABC_FREE( pModel );
                fFirst = 0;
                if ( !pPars->fSolveAll )
                {
//ABC_PRT( "CNF generation runtime", clkOther );
                    if ( pPars->fVerbose )
                    {
                        printf( "%3d %s : ", f, fUnfinished ? "-" : "+" );
                        printf( "Var =%8.0f. ", (double)p->nSatVars );
                        printf( "Cla =%9.0f. ", (double)p->pSat->stats.clauses );
                        printf( "Conf =%7.0f. ",(double)p->pSat->stats.conflicts );
                        printf( "Imp =%10.0f. ", (double)p->pSat->stats.propagations );
                        ABC_PRT( "Time", clock() - clk );
//                        ABC_PRM( "Id2Var", (f+1)*p->nObjNums*4 );
//                        ABC_PRM( "SAT", 42 * p->pSat->size + 16 * (int)p->pSat->stats.clauses + 4 * (int)p->pSat->stats.clauses_literals );
//                        printf( "Simples = %6d. ", p->nBufNum );
//                        printf( "Dups = %6d. ", p->nDupNum );
//                        printf( "\n" );
                        fflush( stdout );
                    }
                    ABC_FREE( pAig->pSeqModel );
                    pAig->pSeqModel = pCex;
                    Saig_Bmc3ManStop( p );
                    return 0;
                }
                pPars->nFailOuts++;
                printf( "Output %*d was asserted in frame %2d (solved %*d out of %*d outputs).\n",  
                    nOutDigits, i, f, nOutDigits, pPars->nFailOuts, nOutDigits, Saig_ManPoNum(pAig) - Saig_ManConstrNum(pAig) );
                if ( p->vCexes == NULL )
                    p->vCexes = Vec_PtrStart( Saig_ManPoNum(pAig) );
                Vec_PtrWriteEntry( p->vCexes, i, pCex );
                RetValue = 0;
            }
            else 
            {
                assert( status == l_Undef );
                if ( pPars->nTimeOut && time(NULL) > nTimeToStop )
                {
                    printf( "Reached timeout (%d seconds).\n",  pPars->nTimeOut );
                    Saig_Bmc3ManStop( p );
                    return RetValue;
                }
                if ( pPars->nFramesJump )
                {
                    pPars->nConfLimit = pPars->nConfLimitJump;
                    nJumpFrame = f + pPars->nFramesJump;
                    fUnfinished = 1;
                    break;
                }
                Saig_Bmc3ManStop( p );
                return RetValue;
            }
            if ( pPars->nTimeOut && time(NULL) > nTimeToStop )
            {
                printf( "Reached timeout (%d seconds).\n",  pPars->nTimeOut );
                Saig_Bmc3ManStop( p );
                return RetValue;
            }
        }
        if ( pPars->fVerbose )
        {
            if ( fFirst == 1 && f > 0 && p->pSat->stats.conflicts > 1 )
            {
                fFirst = 0;
//                printf( "Outputs of frames up to %d are trivially UNSAT.\n", f );
            }
            printf( "%3d %s : ", f, fUnfinished ? "-" : "+" );
            printf( "Var =%8.0f. ", (double)p->nSatVars );
            printf( "Cla =%9.0f. ", (double)p->pSat->stats.clauses );
            printf( "Conf =%7.0f. ",(double)p->pSat->stats.conflicts );
            printf( "Imp =%10.0f. ", (double)p->pSat->stats.propagations );
            ABC_PRT( "Time", clock() - clk );
//            ABC_PRM( "Id2Var", (f+1)*p->nObjNums*4 );
//            ABC_PRM( "SAT", 42 * p->pSat->size + 16 * (int)p->pSat->stats.clauses + 4 * (int)p->pSat->stats.clauses_literals );
//            printf( "Simples = %6d. ", p->nBufNum );
//            printf( "Dups = %6d. ", p->nDupNum );
//            printf( "\n" );
            fflush( stdout );
        }
    }
    // consider the next timeframe
    if ( nJumpFrame && pPars->nStart == 0 )
        pPars->iFrame = nJumpFrame - pPars->nFramesJump;
    else if ( RetValue == -1 && pPars->nStart == 0 )
        pPars->iFrame = f;
//ABC_PRT( "CNF generation runtime", clkOther );
    if ( pPars->fVerbose )
    {
//    ABC_PRM( "Id2Var", (f+1)*p->nObjNums*4 );
//    ABC_PRM( "SAT", 48 * p->pSat->size + 16 * (int)p->pSat->stats.clauses + 4 * (int)p->pSat->stats.clauses_literals );
//    printf( "Simples = %6d. ", p->nBufNum );
//    printf( "Dups = %6d. ", p->nDupNum );
//    printf( "\n" );
    }
    Saig_Bmc3ManStop( p );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

