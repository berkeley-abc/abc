/**CFile****************************************************************

  FileName    [abcFx.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface with the fast_extract package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 26, 2013.]

  Revision    [$Id: abcFx.c,v 1.00 2013/04/26 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "misc/vec/vecWec.h"
#include "misc/vec/vecQue.h"
#include "misc/vec/vecHsh.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Fx_FastExtract( Vec_Wec_t * vCubes, int nVars, int fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reroders fanins of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkOrderFanins( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vOrder;
    Abc_Obj_t * pNode;
    char * pSop, * pSopNew;
    char * pCube, * pCubeNew;
    int nVars, i, v, * pOrder;
    assert( Abc_NtkIsSopLogic(pNtk) );
    vOrder = Vec_IntAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        pSop = (char *)pNode->pData;
        nVars = Abc_SopGetVarNum(pSop);
        assert( nVars == Abc_ObjFaninNum(pNode) );
        Vec_IntClear( vOrder );
        for ( v = 0; v < nVars; v++ )
            Vec_IntPush( vOrder, v );
        pOrder = Vec_IntArray(vOrder);
        Vec_IntSelectSortCost( pOrder, nVars, &pNode->vFanins );
        pSopNew = pCubeNew = Abc_SopStart( (Mem_Flex_t *)pNtk->pManFunc, Abc_SopGetCubeNum(pSop), nVars );
        Abc_SopForEachCube( pSop, nVars, pCube )
        {
            for ( v = 0; v < nVars; v++ )
                if ( pCube[pOrder[v]] == '0' )
                    pCubeNew[v] = '0';
                else if ( pCube[pOrder[v]] == '1' )
                    pCubeNew[v] = '1';
            pCubeNew += nVars + 3;
        }
        pNode->pData = pSopNew;
        Vec_IntSort( &pNode->vFanins, 0 );
//        Vec_IntPrint( vOrder );
    }
    Vec_IntFree( vOrder );
}

/**Function*************************************************************

  Synopsis    [Extracts SOP information.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Abc_NtkFxExtract( Abc_Ntk_t * pNtk )
{
    Vec_Wec_t * vCubes;
    Vec_Int_t * vCube;
    Abc_Obj_t * pNode;
    char * pCube, * pSop;
    int nVars, i, v, Lit;
    assert( Abc_NtkIsSopLogic(pNtk) );
    vCubes = Vec_WecAlloc( 1000 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        pSop = (char *)pNode->pData;
        nVars = Abc_SopGetVarNum(pSop);
        assert( nVars == Abc_ObjFaninNum(pNode) );
        if ( nVars < 2 )
            continue;
        Abc_SopForEachCube( pSop, nVars, pCube )
        {
            vCube = Vec_WecPushLevel( vCubes );
            Vec_IntPush( vCube, Abc_ObjId(pNode) );
            Abc_CubeForEachVar( pCube, Lit, v )
            {
                if ( Lit == '0' )
                    Vec_IntPush( vCube, Abc_Var2Lit(Abc_ObjFaninId(pNode, v), 1) );
                else if ( Lit == '1' )
                    Vec_IntPush( vCube, Abc_Var2Lit(Abc_ObjFaninId(pNode, v), 0) );
            }
            Vec_IntSelectSort( Vec_IntArray(vCube) + 1, Vec_IntSize(vCube) - 1 );
        }
    }
    return vCubes;
}

/**Function*************************************************************

  Synopsis    [Inserts SOP information.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFxInsert( Abc_Ntk_t * pNtk, Vec_Wec_t * vCubes )
{
    Vec_Int_t * vCube, * vPres, * vFirst, * vCount;
    Abc_Obj_t * pNode, * pFanin;
    char * pCube, * pSop;
    int i, k, v, Lit, iFanin, iNodeMax = 0;
    assert( Abc_NtkIsSopLogic(pNtk) );
    // check that cubes have no gaps and are ordered by first node
    Lit = -1;
    Vec_WecForEachLevel( vCubes, vCube, i )
    {
        assert( Vec_IntSize(vCube) > 0 );
        assert( Lit <= Vec_IntEntry(vCube, 0) );
        Lit = Vec_IntEntry(vCube, 0);
    }
    // find the largest index
    Vec_WecForEachLevel( vCubes, vCube, i )
        iNodeMax = Abc_MaxInt( iNodeMax, Vec_IntEntry(vCube, 0) );
    // quit if nothing new
/*
    if ( iNodeMax < Abc_NtkObjNumMax(pNtk) )
    {
        printf( "The network is unchanged by fast extract.\n" );
        return;
    }
*/
    // create new nodes
    for ( i = Abc_NtkObjNumMax(pNtk); i <= iNodeMax; i++ )
    {
        pNode = Abc_NtkCreateNode( pNtk );
        assert( i == (int)Abc_ObjId(pNode) );
    }
    // create node fanins
    vFirst = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    vCount = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    Vec_WecForEachLevel( vCubes, vCube, i )
    {
        iFanin = Vec_IntEntry( vCube, 0 );
        if ( Vec_IntEntry(vCount, iFanin) == 0 )
            Vec_IntWriteEntry( vFirst, iFanin, i );
        Vec_IntAddToEntry( vCount, iFanin, 1 );
    }
    // create node SOPs
    vPres = Vec_IntStartFull( Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Vec_IntEntry(vCount, i) == 0 )
        {
            assert( Abc_ObjFaninNum(pNode) < 2 );
            continue;
        }
        Abc_ObjRemoveFanins( pNode );
        // create fanins
        assert( Vec_IntEntry(vCount, i) > 0 );
        for ( k = 0; k < Vec_IntEntry(vCount, i); k++ )
        {
            vCube = Vec_WecEntry( vCubes, Vec_IntEntry(vFirst, i) + k );
            assert( Vec_IntEntry( vCube, 0 ) == i );
            Vec_IntForEachEntryStart( vCube, Lit, v, 1 )
            {
                pFanin = Abc_NtkObj(pNtk, Abc_Lit2Var(Lit));
                if ( Vec_IntEntry(vPres, Abc_ObjId(pFanin)) >= 0 )
                    continue;
                Vec_IntWriteEntry(vPres, Abc_ObjId(pFanin), Abc_ObjFaninNum(pNode));
                Abc_ObjAddFanin( pNode, pFanin );
            }
        }
        // create SOP
        pSop = pCube = Abc_SopStart( (Mem_Flex_t *)pNtk->pManFunc, Vec_IntEntry(vCount, i), Abc_ObjFaninNum(pNode) );
        for ( k = 0; k < Vec_IntEntry(vCount, i); k++ )
        {
            vCube = Vec_WecEntry( vCubes, Vec_IntEntry(vFirst, i) + k );
            assert( Vec_IntEntry( vCube, 0 ) == i );
            Vec_IntForEachEntryStart( vCube, Lit, v, 1 )
            {
                pFanin = Abc_NtkObj(pNtk, Abc_Lit2Var(Lit));
                iFanin = Vec_IntEntry(vPres, Abc_ObjId(pFanin));
                assert( iFanin >= 0 && iFanin < Abc_ObjFaninNum(pNode) );
                pCube[iFanin] = Abc_LitIsCompl(Lit) ? '0' : '1';
            }
            pCube += Abc_ObjFaninNum(pNode) + 3;
        }
        if ( pNode->pData && Abc_SopIsComplement((char *)pNode->pData) )
            Abc_SopComplement( pSop );
        pNode->pData = pSop;
        // clean fanins
        Abc_ObjForEachFanin( pNode, pFanin, v )
            Vec_IntWriteEntry( vPres, Abc_ObjId(pFanin), -1 );
    }
    Vec_IntFree( vFirst );
    Vec_IntFree( vCount );
    Vec_IntFree( vPres );
}

/**Function*************************************************************

  Synopsis    [Makes sure the nodes do not have complemented and duplicated fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkFxCheck( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i;
//    Abc_NtkForEachObj( pNtk, pNode, i )
//        Abc_ObjPrint( stdout, pNode );
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( !Vec_IntCheckUniqueSmall( &pNode->vFanins ) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkFxPerform( Abc_Ntk_t * pNtk, int fVerbose )
{
    Vec_Wec_t * vCubes;
    assert( Abc_NtkIsSopLogic(pNtk) );
    // check unique fanins
    if ( !Abc_NtkFxCheck(pNtk) )
    {
        printf( "Abc_NtkFastExtract: Nodes have duplicated fanins. FX is not performed.\n" );
        return 0;
    }
    // sweep removes useless nodes
    Abc_NtkCleanup( pNtk, 0 );
//    Abc_NtkOrderFanins( pNtk );
    // collect information about the covers
    vCubes = Abc_NtkFxExtract( pNtk );
    // call the fast extract procedure
    if ( Fx_FastExtract( vCubes, Abc_NtkObjNumMax(pNtk), fVerbose ) > 0 )
    {
        // update the network
        Abc_NtkFxInsert( pNtk, vCubes );
        Vec_WecFree( vCubes );
        if ( !Abc_NtkCheck( pNtk ) )
            printf( "Abc_NtkFxPerform: The network check has failed.\n" );
        return 1;
    }
    else
        printf( "Warning: The network has not been changed by \"fx\".\n" );
    Vec_WecFree( vCubes );
    return 0;
}




typedef struct Fx_Man_t_ Fx_Man_t;
struct Fx_Man_t_
{
    Vec_Wec_t *     vCubes;   // cube -> lit (user data)
    Vec_Wec_t *     vLits;    // lit -> cube
    Vec_Int_t *     vCounts;  // literal counts
    Hsh_VecMan_t *  pHash;    // divisors 
    Vec_Flt_t *     vWeights; // divisor weights
    Vec_Que_t *     vPrio;    // priority queue
    Vec_Int_t *     vVarCube; // mapping var into its first cube
    // temporary arrays used for updating
    Vec_Int_t *     vCubesS;  // single cube divisors
    Vec_Int_t *     vCubesD;  // double cube divisors
    Vec_Int_t *     vPart0;   // cubes of given literal
    Vec_Int_t *     vPart1;   // cubes of given literal
    Vec_Int_t *     vFree;    // cube-free divisor
    Vec_Int_t *     vCube;    // one cube
    Vec_Int_t *     vDiv;     // divisor
    // statistics 
    int             nVars;    // original problem variables
    int             nLits;    // the number of SOP literals
    int             nPairsS;  // number of lit pairs
    int             nPairsD;  // number of cube pairs
    int             nDivsS;   // single cube divisors
};

static inline int Fx_ManGetFirstVarCube( Fx_Man_t * p, Vec_Int_t * vCube ) { return Vec_IntEntry( p->vVarCube, Vec_IntEntry(vCube, 0) ); }

#define Fx_ManForEachCubeVec( vVec, vCubes, vCube, i )           \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((vCube) = Vec_WecEntry(vCubes, Vec_IntEntry(vVec, i))); i++ )
#define Fx_ManForEachPairVec( vVec, vCubes, vCube1, vCube2, i )  \
    for ( i = 0; (i+1 < Vec_IntSize(vVec)) && ((vCube) = Vec_WecEntry(vCubes, Vec_IntEntry(vVec, i))) && ((vCube2) = Vec_WecEntry(vCubes, Vec_IntEntry(vVec, i+1))); i += 2 )

/**Function*************************************************************

  Synopsis    [Create literals.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fx_ManDivCanonicize( Vec_Int_t * vFree ) // return 1 if complemented
{
    int * A = Vec_IntArray(vFree);
    int C[4] = { Abc_Lit2Var(A[0]), Abc_Lit2Var(A[1]), Abc_Lit2Var(A[2]), Abc_Lit2Var(A[3]) };
    int L[4] = { Abc_Lit2Var(A[0]), Abc_Lit2Var(A[1]), Abc_Lit2Var(A[2]), Abc_Lit2Var(A[3]) };
    int V[4] = { Abc_Lit2Var(L[0]), Abc_Lit2Var(L[1]), Abc_Lit2Var(L[2]), Abc_Lit2Var(L[3]) };
    assert( Vec_IntSize(vFree) == 4 );
    if ( V[0] == V[1] && V[2] == V[3] ) // 2,2,2
    {
        assert( !Abc_LitIsCompl(L[0]) );
        assert(  Abc_LitIsCompl(L[1]) );
        if ( !Abc_LitIsCompl(L[2]) )
        {
            C[2] ^= 2;
            C[3] ^= 2;
            return 1;
        }
        return 0;
    }
    if ( V[0] == V[1] )
    {
        assert( V[0] != V[2] && V[0] != V[3] );
        if ( Abc_LitIsCompl(L[0]) == Abc_LitIsCompl(L[2]) && Abc_LitIsCompl(L[1]) == Abc_LitIsCompl(L[3]) )  // 2,2,3
        {
            if ( Abc_LitIsCompl(Abc_Lit2Var(L[0])) == Abc_LitIsCompl(Abc_Lit2Var(L[2])) )
            {
                L[2] = Abc_LitNot(L[2]);
                L[3] = Abc_LitNot(L[3]);
                return 1;
            }
            return 0;
        }
    }
    if ( V[0] == V[2] )
    {
    }
    if ( V[0] == V[3] )
    {
    }
    if ( V[1] == V[2] )
    {
    }
    if ( V[1] == V[3] )
    {
    }
    if ( V[2] == V[3] )
    {
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline char Fx_PrintDivLit( int Lit ) { return (Abc_LitIsCompl(Lit) ? 'A' : 'a') + Abc_Lit2Var(Lit); }
static inline void Fx_PrintDivOne( Vec_Int_t * vDiv )
{
    int i, Lit;
    Vec_IntForEachEntry( vDiv, Lit, i )
        if ( !Abc_LitIsCompl(Lit) )
            printf( "%c", Fx_PrintDivLit(Abc_Lit2Var(Lit)) );
    printf( " + " );
    Vec_IntForEachEntry( vDiv, Lit, i )
        if ( Abc_LitIsCompl(Lit) )
            printf( "%c", Fx_PrintDivLit(Abc_Lit2Var(Lit)) );
}
static inline void Fx_PrintDiv( Fx_Man_t * p, int iDiv )
{
    printf( "Div %6d : ", iDiv );
    printf( "Cost %4d  ", (int)Vec_FltEntry(p->vWeights, iDiv) );
    Fx_PrintDivOne( Hsh_VecReadEntry(p->pHash, iDiv) );
    printf( "\n" );
}
static void Fx_PrintDivisors( Fx_Man_t * p )
{
    int iDiv;
    for ( iDiv = 0; iDiv < Vec_FltSize(p->vWeights); iDiv++ )
        Fx_PrintDiv( p, iDiv );
}
static void Fx_PrintLiterals( Fx_Man_t * p )
{
    Vec_Int_t * vTemp;
    int i;
    Vec_WecForEachLevel( p->vLits, vTemp, i )
    {
        printf( "%c : ", Fx_PrintDivLit(i) );
        Vec_IntPrint( vTemp );
    }
}
static void Fx_PrintMatrix( Fx_Man_t * p )
{
    Vec_Int_t * vCube;
    int i, v, Lit, nObjs;
    char * pLine;
    printf( "         " );
    nObjs = Vec_WecSize(p->vLits)/2;
    for ( i = 0; i < Abc_MinInt(nObjs, 26); i++ )
        printf( "%c", 'a' + i );
    printf( "\n" );
    pLine = ABC_CALLOC( char, nObjs+1 );
    Vec_WecForEachLevel( p->vCubes, vCube, i )
    {
        if ( Vec_IntSize(vCube) == 0 )
            continue;
        memset( pLine, '-', nObjs );
        Vec_IntForEachEntryStart( vCube, Lit, v, 1 )
        {
            assert( Abc_Lit2Var(Lit) < nObjs );
            pLine[Abc_Lit2Var(Lit)] = Abc_LitIsCompl(Lit) ? '0' : '1';
        }
        printf( "%6d : %s %4d\n", i, pLine, Vec_IntEntry(vCube, 0) );
    }
    ABC_FREE( pLine );
    Fx_PrintLiterals( p );
    Fx_PrintDivisors( p );
}
static void Fx_PrintStats( Fx_Man_t * p, clock_t clk )
{
    printf( "Cubes =%6d  ", Vec_WecSizeUsed(p->vCubes) );
    printf( "Lits  =%6d  ", Vec_WecSizeUsed(p->vLits) );
    printf( "Divs  =%6d  ", Hsh_VecSize(p->pHash) );
    printf( "Divs+ =%6d  ", Vec_QueSize(p->vPrio) );
    printf( "DivsS =%6d  ", p->nDivsS );
    printf( "PairS =%6d  ", p->nPairsS );
    printf( "PairD =%6d  ", p->nPairsD );
    Abc_PrintTime( 1, "Time", clk );
//    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fx_ManDivFindCubeFree( Vec_Int_t * vArr1, Vec_Int_t * vArr2, Vec_Int_t * vFree )
{
    int * pBeg1 = vArr1->pArray + 1;
    int * pBeg2 = vArr2->pArray + 1;
    int * pEnd1 = vArr1->pArray + vArr1->nSize;
    int * pEnd2 = vArr2->pArray + vArr2->nSize;
    int Counter = 0, fAttr0 = 0, fAttr1 = 1;
    Vec_IntClear( vFree );
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        if ( *pBeg1 == *pBeg2 )
            pBeg1++, pBeg2++, Counter++;
        else if ( *pBeg1 < *pBeg2 )
            Vec_IntPush( vFree, Abc_Var2Lit(*pBeg1++, fAttr0) );
        else 
        {
            if ( Vec_IntSize(vFree) == 0 )
                fAttr0 = 1, fAttr1 = 0;
            Vec_IntPush( vFree, Abc_Var2Lit(*pBeg2++, fAttr1) );
        }
    }
    while ( pBeg1 < pEnd1 )
        Vec_IntPush( vFree, Abc_Var2Lit(*pBeg1++, fAttr0) );
    while ( pBeg2 < pEnd2 )
        Vec_IntPush( vFree, Abc_Var2Lit(*pBeg2++, fAttr1) );
    assert( Vec_IntSize(vFree) > 1 ); // the cover is not SCC-free
    assert( !Abc_LitIsCompl(Vec_IntEntry(vFree, 0)) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fx_ManDivFindPivots( Vec_Int_t * vDiv, int * pLit0, int * pLit1 )
{
    int i, Lit;
    *pLit0 = -1;
    *pLit1 = -1;
    Vec_IntForEachEntry( vDiv, Lit, i )
    {
        if ( Abc_LitIsCompl(Lit) )
        {
            if ( *pLit1 == -1 )
                *pLit1 = Abc_Lit2Var(Lit);
        }
        else
        {
            if ( *pLit0 == -1 )
                *pLit0 = Abc_Lit2Var(Lit);
        }
        if ( *pLit0 >= 0 && *pLit1 >= 0 )
            return;
    }
}
static inline int Fx_ManDivRemoveLits( Vec_Int_t * vCube, Vec_Int_t * vDiv )
{
    int i, Lit, Count = 0;
    Vec_IntForEachEntry( vDiv, Lit, i )
        Count += Vec_IntRemove1( vCube, Abc_Lit2Var(Lit) );
    return Count;
}
static inline void Fx_ManDivAddLits( Vec_Int_t * vCube, Vec_Int_t * vCube2, Vec_Int_t * vDiv )
{
    int i, Lit;
//    Vec_IntClear( vCube );
//    Vec_IntClear( vCube2 );
    Vec_IntForEachEntry( vDiv, Lit, i )
        if ( Abc_LitIsCompl(Lit) )
            Vec_IntPush( vCube2, Abc_Lit2Var(Lit) );
        else
            Vec_IntPush( vCube, Abc_Lit2Var(Lit) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fx_ManCreateLiterals( Fx_Man_t * p, int nVars )
{
    Vec_Int_t * vCube;
    int i, k, Lit, Count;
    // find the number of variables
    p->nVars = p->nLits = 0;
    Vec_WecForEachLevel( p->vCubes, vCube, i )
    {
        assert( Vec_IntSize(vCube) > 0 );
        p->nVars = Abc_MaxInt( p->nVars, Vec_IntEntry(vCube, 0) );
        p->nLits += Vec_IntSize(vCube) - 1;
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            p->nVars = Abc_MaxInt( p->nVars, Abc_Lit2Var(Lit) );
    }
//    p->nVars++;
    assert( p->nVars < nVars );
    p->nVars = nVars;
    // count literals
    p->vCounts = Vec_IntStart( 2*p->nVars );
    Vec_WecForEachLevel( p->vCubes, vCube, i )
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            Vec_IntAddToEntry( p->vCounts, Lit, 1 );
    // start literals
    p->vLits = Vec_WecStart( 2*p->nVars );
    Vec_IntForEachEntry( p->vCounts, Count, Lit )
        Vec_IntGrow( Vec_WecEntry(p->vLits, Lit), Count );
    // fill out literals
    Vec_WecForEachLevel( p->vCubes, vCube, i )
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            Vec_WecPush( p->vLits, Lit, i );
    // create mapping of variable into the first cube
    p->vVarCube = Vec_IntStartFull( p->nVars );
    Vec_WecForEachLevel( p->vCubes, vCube, i )
        if ( Vec_IntEntry(p->vVarCube, Vec_IntEntry(vCube, 0)) == -1 )
            Vec_IntWriteEntry( p->vVarCube, Vec_IntEntry(vCube, 0), i );
}
int Fx_ManCubeSingleCubeDivisors( Fx_Man_t * p, Vec_Int_t * vPivot, int fRemove, int fUpdate )
{
    int k, n, Lit, Lit2, iDiv;
    if ( Vec_IntSize(vPivot) < 2 )
        return 0;
    Vec_IntForEachEntryStart( vPivot, Lit, k, 1 )
    Vec_IntForEachEntryStart( vPivot, Lit2, n, k+1 )
    {
        assert( Lit < Lit2 );
        Vec_IntClear( p->vFree );
        Vec_IntPush( p->vFree, Abc_Var2Lit(Abc_LitNot(Lit), 0) );
        Vec_IntPush( p->vFree, Abc_Var2Lit(Abc_LitNot(Lit2), 1) );
        iDiv = Hsh_VecManAdd( p->pHash, p->vFree );
        if ( !fRemove )
        {
            if ( Vec_FltSize(p->vWeights) == iDiv )
            {
                Vec_FltPush(p->vWeights, -2);
                p->nDivsS++;
            }
            assert( iDiv < Vec_FltSize(p->vWeights) );
            Vec_FltAddToEntry( p->vWeights, iDiv, 1 );
            p->nPairsS++;
        }
        else
        {
            assert( iDiv < Vec_FltSize(p->vWeights) );
            Vec_FltAddToEntry( p->vWeights, iDiv, -1 );
            p->nPairsS--;
        }
        if ( fUpdate )
        {
            if ( Vec_QueIsMember(p->vPrio, iDiv) )
                Vec_QueUpdate( p->vPrio, iDiv );
            else if ( !fRemove )
                Vec_QuePush( p->vPrio, iDiv );
        }
    }
    return Vec_IntSize(vPivot) * (Vec_IntSize(vPivot) - 1) / 2;
}
void Fx_ManCubeDoubleCubeDivisors( Fx_Man_t * p, int iFirst, Vec_Int_t * vPivot, int fRemove, int fUpdate )
{
    Vec_Int_t * vCube;
    int i, iDiv, Base;
    Vec_WecForEachLevelStart( p->vCubes, vCube, i, iFirst )
    {
        if ( Vec_IntSize(vCube) == 0 || vCube == vPivot )
            continue;
        if ( Vec_WecIntHasMark(vCube) && Vec_WecIntHasMark(vPivot) && vCube > vPivot )
            continue;
        if ( Vec_IntEntry(vCube, 0) != Vec_IntEntry(vPivot, 0) )
            break;
        Base = Fx_ManDivFindCubeFree( vCube, vPivot, p->vFree );
/*
        if ( fUpdate )
        {
            printf( "Cubes %2d %2d : ", Vec_WecLevelId(p->vCubes, vCube), Vec_WecLevelId(p->vCubes, vPivot) );
            if ( fRemove )
                printf( "Rem " );
            else
                printf( "Add " );
            Fx_PrintDivOne( p->vFree ); printf( "\n" );
        }
*/
//        if ( Vec_IntSize(p->vFree) == 4 )
//            Fx_ManDivCanonicize( p->vFree );
        iDiv = Hsh_VecManAdd( p->pHash, p->vFree );
        if ( !fRemove )
        {
            if ( iDiv == Vec_FltSize(p->vWeights) )
                Vec_FltPush(p->vWeights, -Vec_IntSize(p->vFree));
            assert( iDiv < Vec_FltSize(p->vWeights) );
            Vec_FltAddToEntry( p->vWeights, iDiv, Base + Vec_IntSize(p->vFree) - 1 );
            p->nPairsD++;
        }
        else
        {
            assert( iDiv < Vec_FltSize(p->vWeights) );
            Vec_FltAddToEntry( p->vWeights, iDiv, -(Base + Vec_IntSize(p->vFree) - 1) );
            p->nPairsD--;
        }
        if ( fUpdate )
        {
            if ( Vec_QueIsMember(p->vPrio, iDiv) )
                Vec_QueUpdate( p->vPrio, iDiv );
            else if ( !fRemove )
                Vec_QuePush( p->vPrio, iDiv );
        }
    }
}
void Fx_ManCreateDivisors( Fx_Man_t * p )
{
    Vec_Int_t * vCube;
    float Weight;
    int i;
    // alloc hash table
    assert( p->pHash == NULL );
    p->pHash = Hsh_VecManStart( 1000 );
    p->vWeights = Vec_FltAlloc( 1000 );
    // create single-cube two-literal divisors
    Vec_WecForEachLevel( p->vCubes, vCube, i )
        Fx_ManCubeSingleCubeDivisors( p, vCube, 0, 0 ); // add - no update
    assert( p->nDivsS == Vec_FltSize(p->vWeights) );
    // create two-cube divisors
    Vec_WecForEachLevel( p->vCubes, vCube, i )
        Fx_ManCubeDoubleCubeDivisors( p, i+1, vCube, 0, 0 ); // add - no update
    // create queue with all divisors
    p->vPrio = Vec_QueAlloc( Vec_FltSize(p->vWeights) );
    Vec_QueSetCosts( p->vPrio, Vec_FltArrayP(p->vWeights) );
    Vec_FltForEachEntry( p->vWeights, Weight, i )
        if ( Weight > 0.0 )
            Vec_QuePush( p->vPrio, i );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fx_Man_t * Fx_ManStart( Vec_Wec_t * vCubes )
{
    Fx_Man_t * p;
    p = ABC_CALLOC( Fx_Man_t, 1 );
    p->vCubes   = vCubes;
    // temporary data
    p->vCubesS  = Vec_IntAlloc( 100 );
    p->vCubesD  = Vec_IntAlloc( 100 );
    p->vPart0   = Vec_IntAlloc( 100 );
    p->vPart1   = Vec_IntAlloc( 100 );
    p->vFree    = Vec_IntAlloc( 100 );
    p->vCube    = Vec_IntAlloc( 100 );
    p->vDiv     = Vec_IntAlloc( 100 );
    return p;
}
void Fx_ManStop( Fx_Man_t * p )
{
//    Vec_WecFree( p->vCubes );
    Vec_WecFree( p->vLits );
    Vec_IntFree( p->vCounts );
    Hsh_VecManStop( p->pHash );
    Vec_FltFree( p->vWeights );
    Vec_QueFree( p->vPrio );
    Vec_IntFree( p->vVarCube );
    // temporary data
    Vec_IntFree( p->vCubesS );
    Vec_IntFree( p->vCubesD );
    Vec_IntFree( p->vPart0 );
    Vec_IntFree( p->vPart1 );
    Vec_IntFree( p->vFree );
    Vec_IntFree( p->vCube );
    Vec_IntFree( p->vDiv );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fx_ManCompressCubes( Vec_Wec_t * vCubes, Vec_Int_t * vLit2Cube )
{
    int i, CubeId, k = 0;
    Vec_IntForEachEntry( vLit2Cube, CubeId, i )
        if ( Vec_IntSize(Vec_WecEntry(vCubes, CubeId)) > 0 )
            Vec_IntWriteEntry( vLit2Cube, k++, CubeId );
    Vec_IntShrink( vLit2Cube, k );
}
static inline int Fx_ManGetCubeVar( Vec_Wec_t * vCubes, int iCube )        { return Vec_IntEntry( Vec_WecEntry(vCubes, iCube), 0 );      }
void Fx_ManFindCommonPairs( Vec_Wec_t * vCubes, Vec_Int_t * vPart0, Vec_Int_t * vPart1, Vec_Int_t * vPairs, Vec_Int_t * vDiv, Vec_Int_t * vFree )
{
    int * pBeg1 = vPart0->pArray;
    int * pBeg2 = vPart1->pArray;
    int * pEnd1 = vPart0->pArray + vPart0->nSize;
    int * pEnd2 = vPart1->pArray + vPart1->nSize;
    int i, k, i_, k_;
    Vec_IntClear( vPairs );
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        int CubeId1 = Fx_ManGetCubeVar(vCubes, *pBeg1);
        int CubeId2 = Fx_ManGetCubeVar(vCubes, *pBeg2);
        if ( CubeId1 == CubeId2 )
        {
            for ( i = 1; pBeg1+i < pEnd1; i++ )
                if ( CubeId1 != Fx_ManGetCubeVar(vCubes, pBeg1[i]) )
                    break;
            for ( k = 1; pBeg2+k < pEnd2; k++ )
                if ( CubeId1 != Fx_ManGetCubeVar(vCubes, pBeg2[k]) )
                    break;
            for ( i_ = 0; i_ < i; i_++ )
            for ( k_ = 0; k_ < k; k_++ )
            {
                if ( pBeg1[i_] == pBeg2[k_] )
                    continue;
                Fx_ManDivFindCubeFree( Vec_WecEntry(vCubes, pBeg1[i_]), Vec_WecEntry(vCubes, pBeg2[k_]), vFree );
                if ( !Vec_IntEqual( vDiv, vFree ) )
                    continue;
                Vec_IntPush( vPairs, pBeg1[i_] );
                Vec_IntPush( vPairs, pBeg2[k_] );
            }
            pBeg1 += i;
            pBeg2 += k;
        }
        else if ( CubeId1 < CubeId2 )
            pBeg1++;
        else 
            pBeg2++;
    }
}

/**Function*************************************************************

  Synopsis    [Updates the data-structure when divisor is selected.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fx_ManUpdate( Fx_Man_t * p, int iDiv )
{
    Vec_Int_t * vCube, * vCube2, * vLitP, * vLitN;
    Vec_Int_t * vDiv = p->vDiv;
    int nLitsNew = p->nLits - (int)Vec_FltEntry(p->vWeights, iDiv);
    int i, k, Lit0, Lit1, iVarNew, RetValue;
    // get the divisor
    Vec_IntClear( vDiv );
    Vec_IntAppend( vDiv, Hsh_VecReadEntry(p->pHash, iDiv) );
    // select pivot variables
    Fx_ManDivFindPivots( vDiv, &Lit0, &Lit1 );
    assert( Lit0 >= 0 && Lit1 >= 0 );

    // collect single-cube-divisor cubes
    Vec_IntClear( p->vCubesS );
    if ( Vec_IntSize(vDiv) == 2 )
    {
        Fx_ManCompressCubes( p->vCubes, Vec_WecEntry(p->vLits, Abc_LitNot(Lit0)) );
        Fx_ManCompressCubes( p->vCubes, Vec_WecEntry(p->vLits, Abc_LitNot(Lit1)) );
        Vec_IntTwoRemoveCommon( Vec_WecEntry(p->vLits, Abc_LitNot(Lit0)), Vec_WecEntry(p->vLits, Abc_LitNot(Lit1)), p->vCubesS );
    }
//Vec_IntPrint( p->vCubesS );

    // collect double-cube-divisor cube pairs
    Fx_ManCompressCubes( p->vCubes, Vec_WecEntry(p->vLits, Lit0) );
    Fx_ManCompressCubes( p->vCubes, Vec_WecEntry(p->vLits, Lit1) );
    Fx_ManFindCommonPairs( p->vCubes, Vec_WecEntry(p->vLits, Lit0), Vec_WecEntry(p->vLits, Lit1), p->vCubesD, vDiv, p->vFree );
//Vec_IntPrint( p->vCubesD );

    // subtract cost of single-cube divisors
    Fx_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
        Fx_ManCubeSingleCubeDivisors( p, vCube, 1, 1 );  // remove - update
    Fx_ManForEachCubeVec( p->vCubesD, p->vCubes, vCube, i )
        Fx_ManCubeSingleCubeDivisors( p, vCube, 1, 1 );  // remove - update

    // mark the cubes to be removed
    Vec_WecMarkLevels( p->vCubes, p->vCubesS );
    Vec_WecMarkLevels( p->vCubes, p->vCubesD );

    // subtract cost of double-cube divisors
    Fx_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
        Fx_ManCubeDoubleCubeDivisors( p, Fx_ManGetFirstVarCube(p, vCube), vCube, 1, 1 );  // remove - update
    Fx_ManForEachCubeVec( p->vCubesD, p->vCubes, vCube, i )
        Fx_ManCubeDoubleCubeDivisors( p, Fx_ManGetFirstVarCube(p, vCube), vCube, 1, 1 );  // remove - update

    // unmark the cubes to be removed
    Vec_WecUnmarkLevels( p->vCubes, p->vCubesS );
    Vec_WecUnmarkLevels( p->vCubes, p->vCubesD );

    // create new divisor
    iVarNew = Vec_WecSize( p->vLits ) / 2;
    assert( Vec_IntSize(p->vVarCube) == iVarNew );
    Vec_IntPush( p->vVarCube, Vec_WecSize(p->vCubes) );
    vCube = Vec_WecPushLevel( p->vCubes );
    Vec_IntPush( vCube, iVarNew );
    if ( Vec_IntSize(vDiv) == 2 )
    {
        Vec_IntPush( vCube, Abc_LitNot(Lit0) );
        Vec_IntPush( vCube, Abc_LitNot(Lit1) );
    }
    else
    {
        vCube2 = Vec_WecPushLevel( p->vCubes );
        vCube = Vec_WecEntry( p->vCubes, Vec_WecSize(p->vCubes) - 2 );
        Vec_IntPush( vCube2, iVarNew );
        Fx_ManDivAddLits( vCube, vCube2, vDiv );
    }
    // do not add new cubes to the matrix 
    p->nLits += Vec_IntSize( vDiv );
    // create new literals
    vLitP = Vec_WecPushLevel( p->vLits );
    vLitN = Vec_WecPushLevel( p->vLits );
    vLitP = Vec_WecEntry( p->vLits, Vec_WecSize(p->vLits) - 2 );
    // create updated single-cube divisor cubes
    Fx_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
    {
        RetValue  = Vec_IntRemove1( vCube, Abc_LitNot(Lit0) );
        RetValue += Vec_IntRemove1( vCube, Abc_LitNot(Lit1) );
        assert( RetValue == 2 );
        Vec_IntPush( vCube, Abc_Var2Lit(iVarNew, 0) );
        Vec_IntPush( vLitP, Vec_WecLevelId(p->vCubes, vCube) );
        p->nLits--;
    }
    // create updated double-cube divisor cube pairs
    k = 0;
    assert( Vec_IntSize(p->vCubesD) % 2 == 0 );
    Fx_ManForEachPairVec( p->vCubesD, p->vCubes, vCube, vCube2, i )
    {
        RetValue  = Fx_ManDivRemoveLits( vCube, vDiv );  // cube 2*i
        RetValue += Fx_ManDivRemoveLits( vCube2, vDiv ); // cube 2*i+1
        assert( RetValue == Vec_IntSize(vDiv) );
        if ( Vec_IntSize(vDiv) == 2 )
        {
            Vec_IntPush( vCube, Abc_Var2Lit(iVarNew, 1) );
            Vec_IntPush( vLitN, Vec_WecLevelId(p->vCubes, vCube) );
        }
        else
        {
            Vec_IntPush( vCube, Abc_Var2Lit(iVarNew, 0) );
            Vec_IntPush( vLitP, Vec_WecLevelId(p->vCubes, vCube) );
        }
        p->nLits -= Vec_IntSize(vDiv) + Vec_IntSize(vCube2) - 2;
        // remove second cube
        Vec_IntWriteEntry( p->vCubesD, k++, Vec_WecLevelId(p->vCubes, vCube) );
        Vec_IntClear( vCube2 ); 
    }
    assert( k == Vec_IntSize(p->vCubesD) / 2 );
    Vec_IntShrink( p->vCubesD, k );
    Vec_IntSort( p->vCubesD, 0 );

    // add cost of single-cube divisors
    Fx_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
        Fx_ManCubeSingleCubeDivisors( p, vCube, 0, 1 );  // add - update
    Fx_ManForEachCubeVec( p->vCubesD, p->vCubes, vCube, i )
        Fx_ManCubeSingleCubeDivisors( p, vCube, 0, 1 );  // add - update

    // mark the cubes to be removed
    Vec_WecMarkLevels( p->vCubes, p->vCubesS );
    Vec_WecMarkLevels( p->vCubes, p->vCubesD );

    // add cost of double-cube divisors
    Fx_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
        Fx_ManCubeDoubleCubeDivisors( p, Fx_ManGetFirstVarCube(p, vCube), vCube, 0, 1 );  // add - update
    Fx_ManForEachCubeVec( p->vCubesD, p->vCubes, vCube, i )
        Fx_ManCubeDoubleCubeDivisors( p, Fx_ManGetFirstVarCube(p, vCube), vCube, 0, 1 );  // add - update

    // unmark the cubes to be removed
    Vec_WecUnmarkLevels( p->vCubes, p->vCubesS );
    Vec_WecUnmarkLevels( p->vCubes, p->vCubesD );

    // add cost of the new divisor
    if ( Vec_IntSize(vDiv) > 2 )
    {
        vCube  = Vec_WecEntry( p->vCubes, Vec_WecSize(p->vCubes) - 2 );
        vCube2 = Vec_WecEntry( p->vCubes, Vec_WecSize(p->vCubes) - 1 );
        Fx_ManCubeSingleCubeDivisors( p, vCube,  0, 1 );  // add - update
        Fx_ManCubeSingleCubeDivisors( p, vCube2, 0, 1 );  // add - update
        Vec_IntForEachEntryStart( vCube, Lit0, i, 1 )
            Vec_WecPush( p->vLits, Lit0, Vec_WecLevelId(p->vCubes, vCube) );
        Vec_IntForEachEntryStart( vCube2, Lit0, i, 1 )
            Vec_WecPush( p->vLits, Lit0, Vec_WecLevelId(p->vCubes, vCube2) );
    }

    // remove these cubes from the lit array of the divisor
    Vec_IntForEachEntry( vDiv, Lit0, i )
        Vec_IntTwoRemove( Vec_WecEntry(p->vLits, Abc_Lit2Var(Lit0)), p->vCubesD );

    assert( p->nLits == nLitsNew ); // new SOP lits == old SOP lits - divisor weight
}

/**Function*************************************************************

  Synopsis    [Implements the traditional fast_extract algorithm.]

  Description [J. Rajski and J. Vasudevamurthi, "The testability-
  preserving concurrent decomposition and factorization of Boolean
  expressions", IEEE TCAD, Vol. 11, No. 6, June 1992, pp. 778-793.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fx_FastExtract( Vec_Wec_t * vCubes, int nVars, int fVerbose )
{
    int fVeryVerbose = 0;
    Fx_Man_t * p;
    clock_t clk = clock();
    // initialize the data-structure
    p = Fx_ManStart( vCubes );
    Fx_ManCreateLiterals( p, nVars );
    Fx_ManCreateDivisors( p );
    if ( fVeryVerbose )
        Fx_PrintMatrix( p );
    if ( fVerbose )
        Fx_PrintStats( p, clock() - clk );
    // perform extraction
    while ( Vec_QueTopCost(p->vPrio) > 0.0 )
    {
        int iDiv = Vec_QuePop(p->vPrio);
        if ( fVerbose )
            Fx_PrintDiv( p, iDiv );
        Fx_ManUpdate( p, iDiv );
        if ( fVeryVerbose )
            Fx_PrintMatrix( p );
        if ( fVerbose )
            Fx_PrintStats( p, clock() - clk );
    }
    Fx_ManStop( p );
    // return the result
    Vec_WecRemoveEmpty( vCubes );
    return 1;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

