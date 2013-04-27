/**CFile****************************************************************

  FileName    [abcFx.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface with the fast extract package.]

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
        pSopNew = pCubeNew = Abc_SopStart( pNtk->pManFunc, Abc_SopGetCubeNum(pSop), nVars );
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
        pSop = pCube = Abc_SopStart( pNtk->pManFunc, Vec_IntEntry(vCount, i), Abc_ObjFaninNum(pNode) );
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
        if ( Abc_SopIsComplement((char *)pNode->pData) )
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
    int             nVars;   // original problem variables
    int             nPairsS; // number of lit pairs
    int             nPairsD; // number of cube pairs
    int             nDivsS;  // single cube divisors
    Vec_Wec_t *     vCubes;  // cube -> lit (user data)
    Vec_Wec_t *     vLits;   // lit -> cube
    Vec_Int_t *     vCounts; // literal counts
    Hsh_VecMan_t *  pHash;   // divisors 
    Vec_Flt_t *     vWeights;// divisor weights
    Vec_Que_t *     vPrio;   // priority queue
    // temporary variables
    Vec_Int_t *     vCube; 
};

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
    assert( Vec_IntSize(vFree) > 1 );
    assert( !Abc_LitIsCompl(Vec_IntEntry(vFree, 0)) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Fx_ManCreateLiterals( Vec_Wec_t * vCubes, Vec_Int_t ** pvCounts )
{
    Vec_Wec_t * vLits;
    Vec_Int_t * vCube, * vCounts;
    int i, k, Count, Lit, LitMax = 0;
    // find max literal
    Vec_WecForEachLevel( vCubes, vCube, i )
        Vec_IntForEachEntry( vCube, Lit, k )
            LitMax = Abc_MaxInt( LitMax, Lit );
    // count literals
    vCounts = Vec_IntStart( LitMax + 2 );
    Vec_WecForEachLevel( vCubes, vCube, i )
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            Vec_IntAddToEntry( vCounts, Lit, 1 );
    // start literals
    vLits = Vec_WecStart( 2 * LitMax );
    Vec_IntForEachEntry( vCounts, Count, Lit )
        Vec_IntGrow( Vec_WecEntry(vLits, Lit), Count );
    // fill out literals
    Vec_WecForEachLevel( vCubes, vCube, i )
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            Vec_WecPush( vLits, Lit, i );
    *pvCounts = vCounts;
    return vLits;
}
Hsh_VecMan_t * Fx_ManCreateDivisors( Vec_Wec_t * vCubes, Vec_Flt_t ** pvWeights, int * pnPairsS, int * pnPairsD, int * pnDivsS )
{
    Hsh_VecMan_t * p;
    Vec_Flt_t * vWeights;
    Vec_Int_t * vCube, * vCube2, * vFree;
    int i, k, n, Lit, Lit2, iDiv, Base;
    p = Hsh_VecManStart( 10000 );
    vWeights = Vec_FltAlloc( 10000 );
    vFree = Vec_IntAlloc( 100 );
    // create two-literal divisors
    Vec_WecForEachLevel( vCubes, vCube, i )
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            Vec_IntForEachEntryStart( vCube, Lit2, n, k+1 )
            {
                assert( Lit < Lit2 );
                Vec_IntClear( vFree );
                Vec_IntPush( vFree, Abc_Var2Lit(Abc_LitNot(Lit), 0) );
                Vec_IntPush( vFree, Abc_Var2Lit(Abc_LitNot(Lit2), 1) );
                iDiv = Hsh_VecManAdd( p, vFree );
                if ( Vec_FltSize(vWeights) == iDiv )
                    Vec_FltPush(vWeights, -2);
                assert( iDiv < Vec_FltSize(vWeights) );
                Vec_FltAddToEntry( vWeights, iDiv, 1 );
                (*pnPairsS)++;
            }
    *pnDivsS = Vec_FltSize(vWeights);
    // create two-cube divisors
    Vec_WecForEachLevel( vCubes, vCube, i )
    {
        Vec_WecForEachLevelStart( vCubes, vCube2, k, i+1 )
            if ( Vec_IntEntry(vCube, 0) == Vec_IntEntry(vCube2, 0) )
            {
//                extern void Fx_PrintDivOne( Vec_Int_t * p );
                Base = Fx_ManDivFindCubeFree( vCube, vCube2, vFree );
//                printf( "Cubes %2d %2d : ", i, k );
//                Fx_PrintDivOne( vFree ); printf( "\n" );

//                if ( Vec_IntSize(vFree) == 4 )
//                    Fx_ManDivCanonicize( vFree );
                iDiv = Hsh_VecManAdd( p, vFree );
                if ( Vec_FltSize(vWeights) == iDiv )
                    Vec_FltPush(vWeights, -Vec_IntSize(vFree));
                assert( iDiv < Vec_FltSize(vWeights) );
                Vec_FltAddToEntry( vWeights, iDiv, Base + Vec_IntSize(vFree) - 1 );
                (*pnPairsD)++;
            }
            else
                break;
    }
    Vec_IntFree( vFree );
    *pvWeights = vWeights;
    return p;
}
Vec_Que_t * Fx_ManCreateQueue( Vec_Flt_t * vWeights )
{
    Vec_Que_t * p;
    float Weight;
    int i;
    p = Vec_QueAlloc( Vec_FltSize(vWeights) );
    Vec_QueSetCosts( p, Vec_FltArray(vWeights) );
    Vec_FltForEachEntry( vWeights, Weight, i )
        if ( Weight > 0.0 )
            Vec_QuePush( p, i );
    return p;
}

/**Function*************************************************************

  Synopsis    [Removes 0-size cubes and sorts them by the first entry.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vec_WecSortSpecial( Vec_Wec_t * vCubes )
{
    Vec_Int_t * vCube;
    int i, k = 0;
    Vec_WecForEachLevel( vCubes, vCube, i )
        if ( Vec_IntSize(vCube) > 0 )
            vCubes->pArray[k++] = *vCube;
        else
            ABC_FREE( vCube->pArray );
    Vec_WecShrink( vCubes, k );
    Vec_WecSortByFirstInt( vCubes, 0 );
}


/**Function*************************************************************

  Synopsis    [Updates the data-structure when divisor is selected.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fx_ManUpdate( Fx_Man_t * p, int iDiv )
{
//    Vec_Int_t * vDiv = Hsh_VecReadEntry( p->pHash, iDiv );

    // select pivot variables

    // collect single-cube-divisor cubes

    // collect double-cube-divisor cube pairs

    // subtract old costs

    // create updated single-cube divisor cubes

    // create updated double-cube-divisor cube pairs

    // add new costs

    // assert (divisor weight == old cost - new cost)
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Fx_Man_t * Fx_ManStart( Vec_Wec_t * vCubes, int nVars )
{
    Fx_Man_t * p;
    p = ABC_CALLOC( Fx_Man_t, 1 );
    p->nVars  = nVars;
    p->vCubes = vCubes;
    p->vLits  = Fx_ManCreateLiterals( vCubes, &p->vCounts );
    p->pHash  = Fx_ManCreateDivisors( vCubes, &p->vWeights, &p->nPairsS, &p->nPairsD, &p->nDivsS );
    p->vPrio  = Fx_ManCreateQueue( p->vWeights );
    p->vCube  = Vec_IntAlloc( 100 );
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
    Vec_IntFree( p->vCube );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Fx_PrintMatrix( Vec_Wec_t * vCubes, int nObjs )
{
    Vec_Int_t * vCube;
    char * pLine;
    int i, v, Lit;
    printf( "         " );
    for ( i = 0; i < Abc_MinInt(nObjs, 26); i++ )
        printf( "%c", 'a' + i );
    printf( "\n" );
    pLine = ABC_CALLOC( char, nObjs + 1 );
    Vec_WecForEachLevel( vCubes, vCube, i )
    {
        memset( pLine, '-', nObjs );
        Vec_IntForEachEntryStart( vCube, Lit, v, 1 )
        {
            assert( Abc_Lit2Var(Lit) < nObjs );
            pLine[Abc_Lit2Var(Lit)] = Abc_LitIsCompl(Lit) ? '0' : '1';
        }
        printf( "%6d : %s %4d\n", i, pLine, Vec_IntEntry(vCube, 0) );
    }
    ABC_FREE( pLine );
}
static inline char Fx_PrintDivLit( int Lit ) { return (Abc_LitIsCompl(Abc_Lit2Var(Lit)) ? 'A' : 'a') + Abc_Lit2Var(Abc_Lit2Var(Lit)); }
static inline void Fx_PrintDivOne( Vec_Int_t * vDiv )
{
    int i, Lit;
    Vec_IntForEachEntry( vDiv, Lit, i )
        if ( !Abc_LitIsCompl(Lit) )
            printf( "%c", Fx_PrintDivLit(Lit) );
    printf( " + " );
    Vec_IntForEachEntry( vDiv, Lit, i )
        if ( Abc_LitIsCompl(Lit) )
            printf( "%c", Fx_PrintDivLit(Lit) );
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
int Fx_FastExtract( Vec_Wec_t * vCubes, int nVars, int fVerbose )
{
    Fx_Man_t * p;
    clock_t clk = clock();
    p = Fx_ManStart( vCubes, nVars );

    if ( fVerbose )
    {
        Fx_PrintMatrix( vCubes, nVars );
        Fx_PrintDivisors( p );
        printf( "Selecting divisors:\n" );
    }

    Fx_PrintStats( p, clock() - clk );
    while ( Vec_QueTopCost(p->vPrio) > 0.0 )
    {
        int iDiv = Vec_QuePop(p->vPrio);
        if ( fVerbose )
            Fx_PrintDiv( p, iDiv );
        Fx_ManUpdate( p, iDiv );
    }

    Fx_ManStop( p );
    return 1;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

