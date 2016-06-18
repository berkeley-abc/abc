/**CFile****************************************************************

  FileName    [ FxchMan.c ]

  PackageName [ Fast eXtract with Cube Hashing (FXCH) ]

  Synopsis    [ Fxch Manager implementation ]

  Author      [ Bruno Schmitt - boschmitt at inf.ufrgs.br ]

  Affiliation [ UFRGS ]

  Date        [ Ver. 1.0. Started - March 6, 2016. ]

  Revision    []

***********************************************************************/

#include "Fxch.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                LOCAL FUNCTIONS DEFINITIONS                       ///
////////////////////////////////////////////////////////////////////////
static inline int Fxch_ManSCAddRemove( Fxch_Man_t* pFxchMan,
                                       unsigned int SubCubeID,
                                       unsigned int iSubCube,
                                       unsigned int iCube,
                                       unsigned int iLit0,
                                       unsigned int iLit1,
                                       char fAdd,
                                       char fUpdate )
{
    int ret = 0;

    if ( fAdd )
    {
        ret = Fxch_SCHashTableInsert( pFxchMan->pSCHashTable, pFxchMan->vCubes,
                                      SubCubeID, iSubCube,
                                      iCube, iLit0, iLit1, fUpdate );
    }
    else
    {
        ret = Fxch_SCHashTableRemove( pFxchMan->pSCHashTable, pFxchMan->vCubes,
                                      SubCubeID, iSubCube,
                                      iCube, iLit0, iLit1, fUpdate );
    }

    return ret;
}


static inline int Fxch_ManDivSingleCube( Fxch_Man_t* pFxchMan,
                                         int iCube,
                                         int fAdd,
                                         int fUpdate )
{
    Vec_Int_t* vCube = Vec_WecEntry( pFxchMan->vCubes, iCube );
    int i, k,
        Lit0,
        Lit1,
        fSingleCube = 1,
        fBase = 0;

    if ( Vec_IntSize(vCube) < 2 )
        return 0;

    Vec_IntForEachEntryStart( vCube, Lit0, i, 1)
    Vec_IntForEachEntryStart( vCube, Lit1, k, (i + 1) )
    {
        assert( Lit0 < Lit1 );

        Vec_IntClear( pFxchMan->vCubeFree );
        Vec_IntPush( pFxchMan->vCubeFree, Abc_Var2Lit( Abc_LitNot( Lit0 ), 0 ) );
        Vec_IntPush( pFxchMan->vCubeFree, Abc_Var2Lit( Abc_LitNot( Lit1 ), 1 ) );

        if (fAdd)
        {
            Fxch_DivAdd( pFxchMan, fUpdate, fSingleCube, fBase );
            pFxchMan->nPairsS++;
        }
        else
        {
            Fxch_DivRemove( pFxchMan, fUpdate, fSingleCube, fBase );
            pFxchMan->nPairsS--;
        }
    }

    return Vec_IntSize( vCube ) * ( Vec_IntSize( vCube ) - 1 ) / 2;
}

static inline void Fxch_ManDivDoubleCube( Fxch_Man_t* pFxchMan,
                                          int iCube,
                                          int fAdd,
                                          int fUpdate )
{
    Vec_Int_t* vLitHashKeys = pFxchMan->vLitHashKeys,
             * vCube = Vec_WecEntry( pFxchMan->vCubes, iCube );
    int SubCubeID = 0,
        nHashedSC = 0,
        iLit0,
        Lit0;

    Vec_IntForEachEntryStart( vCube, Lit0, iLit0, 1)
        SubCubeID += Vec_IntEntry( vLitHashKeys, Lit0 );

    Fxch_ManSCAddRemove( pFxchMan,
                         SubCubeID, nHashedSC++,
                         iCube, 0, 0,
                         (char)fAdd, (char)fUpdate );

    Vec_IntForEachEntryStart( vCube, Lit0, iLit0, 1)
    {
        /* 1 Lit remove */
        SubCubeID -= Vec_IntEntry( vLitHashKeys, Lit0 );

        pFxchMan->nPairsD += Fxch_ManSCAddRemove( pFxchMan,
                                                  SubCubeID, nHashedSC++,
                                                  iCube, iLit0, 0,
                                                  (char)fAdd, (char)fUpdate );

        if ( Vec_IntSize( vCube ) >= 3 )
        {
            int Lit1,
                iLit1;

            Vec_IntForEachEntryStart( vCube, Lit1, iLit1, iLit0 + 1)
            {
                /* 2 Lit remove */
                SubCubeID -= Vec_IntEntry( vLitHashKeys, Lit1 );

                pFxchMan->nPairsD += Fxch_ManSCAddRemove( pFxchMan,
                                                          SubCubeID, nHashedSC++,
                                                          iCube, iLit0, iLit1,
                                                          (char)fAdd, (char)fUpdate );

                SubCubeID += Vec_IntEntry( vLitHashKeys, Lit1 );
            }
        }

        SubCubeID += Vec_IntEntry( vLitHashKeys, Lit0 );
    }
}

static inline void Fxch_ManCompressCubes( Vec_Wec_t* vCubes,
                                          Vec_Int_t* vLit2Cube )
{
    int i,
        k = 0,
        CubeId;

    Vec_IntForEachEntry( vLit2Cube, CubeId, i )
        if ( Vec_IntSize(Vec_WecEntry(vCubes, CubeId)) > 0 )
            Vec_IntWriteEntry( vLit2Cube, k++, CubeId );

    Vec_IntShrink( vLit2Cube, k );
}

////////////////////////////////////////////////////////////////////////
///                     PUBLIC INTERFACE                             ///
////////////////////////////////////////////////////////////////////////
Fxch_Man_t* Fxch_ManAlloc( Vec_Wec_t* vCubes )
{
    Fxch_Man_t* pFxchMan = ABC_CALLOC( Fxch_Man_t, 1 );

    pFxchMan->vCubes = vCubes;
    pFxchMan->pDivHash = Hsh_VecManStart( 1000 );
    pFxchMan->vDivWeights = Vec_FltAlloc( 1000 );
    pFxchMan->vDivCubePairs = Vec_WecAlloc( 1000 );
    pFxchMan->vCubeFree = Vec_IntAlloc( 100 );
    pFxchMan->vDiv = Vec_IntAlloc( 100 );
    pFxchMan->vSCC = Vec_IntAlloc( 64 );
    pFxchMan->vCubesS = Vec_IntAlloc( 100 );
    pFxchMan->vPairs = Vec_IntAlloc( 100 );

    return pFxchMan;
}

void Fxch_ManFree( Fxch_Man_t* pFxchMan )
{
    Vec_WecFree( pFxchMan->vLits );
    Vec_IntFree( pFxchMan->vLitCount );
    Vec_IntFree( pFxchMan->vLitHashKeys );
    Hsh_VecManStop( pFxchMan->pDivHash );
    Vec_FltFree( pFxchMan->vDivWeights );
    Vec_QueFree( pFxchMan->vDivPrio );
    Vec_WecFree( pFxchMan->vDivCubePairs );
    Vec_IntFree( pFxchMan->vLevels );
    Vec_IntFree( pFxchMan->vCubeFree );
    Vec_IntFree( pFxchMan->vDiv );
    Vec_IntFree( pFxchMan->vSCC );
    Vec_IntFree( pFxchMan->vCubesS );
    Vec_IntFree( pFxchMan->vPairs );
    ABC_FREE( pFxchMan );
}

void Fxch_ManMapLiteralsIntoCubes( Fxch_Man_t* pFxchMan,
                                   int nVars )
{

    Vec_Int_t* vCube;
    int i, k,
        Lit,
        Count;

    pFxchMan->nVars = 0;
    pFxchMan->nLits = 0;
    Vec_WecForEachLevel( pFxchMan->vCubes, vCube, i )
    {
        assert( Vec_IntSize(vCube) > 0 );
        pFxchMan->nVars = Abc_MaxInt( pFxchMan->nVars, Vec_IntEntry( vCube, 0 ) );
        pFxchMan->nLits += Vec_IntSize(vCube) - 1;
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            pFxchMan->nVars = Abc_MaxInt( pFxchMan->nVars, Abc_Lit2Var( Lit ) );
    }

    assert( pFxchMan->nVars < nVars );
    pFxchMan->nVars = nVars;

    /* Count the number of time each literal appears on the SOP */
    pFxchMan->vLitCount = Vec_IntStart( 2 * pFxchMan->nVars );
    Vec_WecForEachLevel( pFxchMan->vCubes, vCube, i )
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            Vec_IntAddToEntry( pFxchMan->vLitCount, Lit, 1 );

    /* Allocate space to the array of arrays wich maps Literals into cubes which uses them */
    pFxchMan->vLits = Vec_WecStart( 2 * pFxchMan->nVars );
    Vec_IntForEachEntry( pFxchMan->vLitCount, Count, Lit )
        Vec_IntGrow( Vec_WecEntry( pFxchMan->vLits, Lit ), Count );

    /* Maps Literals into cubes which uses them */
    Vec_WecForEachLevel( pFxchMan->vCubes, vCube, i )
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            Vec_WecPush( pFxchMan->vLits, Lit, i );
}

void Fxch_ManGenerateLitHashKeys( Fxch_Man_t* pFxchMan )
{
    int i;
    /* Generates the random number which will be used for hashing cubes */
    Gia_ManRandom( 1 );
    pFxchMan->vLitHashKeys = Vec_IntAlloc( ( 2 * pFxchMan->nVars ) );
    for ( i = 0; i < (2 * pFxchMan->nVars); i++ )
        Vec_IntPush( pFxchMan->vLitHashKeys, Gia_ManRandom(0) & 0x3FFFFFF );
}

void Fxch_ManSCHashTablesInit( Fxch_Man_t* pFxchMan )
{
    Vec_Wec_t* vCubes = pFxchMan->vCubes;
    Vec_Int_t* vCube,
             * vCubeLinks;
    int iCube,
        nTotalHashed = 0;

    vCubeLinks = Vec_IntAlloc( Vec_WecSize( vCubes ) + 1 );
    Vec_WecForEachLevel( vCubes, vCube, iCube )
    {
        int nLits = Vec_IntSize( vCube ) - 1,
            nSubCubes = nLits <= 2? nLits + 1: ( nLits * nLits + nLits ) / 2;

        Vec_IntPush( vCubeLinks, ( nTotalHashed + 1 ) );
        nTotalHashed += nSubCubes + 1;
    }

    pFxchMan->pSCHashTable = Fxch_SCHashTableCreate( pFxchMan, vCubeLinks, nTotalHashed );
}

void Fxch_ManSCHashTablesFree( Fxch_Man_t* pFxchMan )
{
    Fxch_SCHashTableDelete( pFxchMan->pSCHashTable );
}

void Fxch_ManDivCreate( Fxch_Man_t* pFxchMan )
{
    Vec_Int_t* vCube;
    float Weight;
    int fAdd = 1,
        fUpdate = 0,
        iCube;

    Vec_WecForEachLevel( pFxchMan->vCubes, vCube, iCube )
    {
        Fxch_ManDivSingleCube( pFxchMan, iCube, fAdd, fUpdate );
        Fxch_ManDivDoubleCube( pFxchMan, iCube, fAdd, fUpdate );
    }

    pFxchMan->vDivPrio = Vec_QueAlloc( Vec_FltSize( pFxchMan->vDivWeights ) );
    Vec_QueSetPriority( pFxchMan->vDivPrio, Vec_FltArrayP( pFxchMan->vDivWeights ) );
    Vec_FltForEachEntry( pFxchMan->vDivWeights, Weight, iCube )
    {
        if ( Weight > 0.0 )
            Vec_QuePush( pFxchMan->vDivPrio, iCube );
    }
}

/* Level Computation */
int Fxch_ManComputeLevelDiv( Fxch_Man_t* pFxchMan,
                             Vec_Int_t* vCubeFree )
{
    int i,
        Lit,
        Level = 0;

    Vec_IntForEachEntry( vCubeFree, Lit, i )
        Level = Abc_MaxInt( Level, Vec_IntEntry( pFxchMan->vLevels, Abc_Lit2Var( Abc_Lit2Var( Lit ) ) ) );

    return Abc_MinInt( Level, 800 );
}

int Fxch_ManComputeLevelCube( Fxch_Man_t* pFxchMan,
                              Vec_Int_t * vCube )
{
    int k,
        Lit,
        Level = 0;

    Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
        Level = Abc_MaxInt( Level, Vec_IntEntry( pFxchMan->vLevels, Abc_Lit2Var( Lit ) ) );

    return Level;
}

void Fxch_ManComputeLevel( Fxch_Man_t* pFxchMan )
{
    Vec_Int_t* vCube;
    int i,
        iVar,
        iFirst = 0;

    iVar = Vec_IntEntry( Vec_WecEntry( pFxchMan->vCubes, 0 ), 0 );
    pFxchMan->vLevels = Vec_IntStart( pFxchMan->nVars );

    Vec_WecForEachLevel( pFxchMan->vCubes, vCube, i )
    {
        if ( iVar != Vec_IntEntry( vCube, 0 ) )
        {
            Vec_IntAddToEntry( pFxchMan->vLevels, iVar, i - iFirst );
            iVar = Vec_IntEntry( vCube, 0 );
            iFirst = i;
        }
        Vec_IntUpdateEntry( pFxchMan->vLevels, iVar, Fxch_ManComputeLevelCube( pFxchMan, vCube ) );
    }
}

/* Extract divisor from single-cubes */
static inline void Fxch_ManExtractDivFromCube( Fxch_Man_t* pFxchMan,
                                               const int Lit0,
                                               const int Lit1,
                                               const int iVarNew )
{
    int i, iCube0;
    Vec_Int_t* vLitP = Vec_WecEntry( pFxchMan->vLits, Vec_WecSize( pFxchMan->vLits ) - 2 );

    Vec_IntForEachEntry( pFxchMan->vCubesS, iCube0, i )
    {
        int RetValue;
        Vec_Int_t* vCube0;

        vCube0 = Fxch_ManGetCube( pFxchMan, iCube0 );
        RetValue  = Vec_IntRemove1( vCube0, Abc_LitNot( Lit0 ) );
        RetValue += Vec_IntRemove1( vCube0, Abc_LitNot( Lit1 ) );
        assert( RetValue == 2 );

        Vec_IntPush( vCube0, Abc_Var2Lit( iVarNew, 0 ) );
        Vec_IntPush( vLitP, Vec_WecLevelId( pFxchMan->vCubes, vCube0 ) );

        pFxchMan->nLits--;
    }
}

/* Extract divisor from cube pairs */
static inline int Fxch_ManExtractDivFromCubePairs( Fxch_Man_t* pFxchMan,
                                                   const int iVarNew )
{
    /* For each pair (Ci, Cj) */
    int k = 0,
        iCube0, iCube1, i;

    Vec_Int_t* vLitP = Vec_WecEntry( pFxchMan->vLits, Vec_WecSize( pFxchMan->vLits ) - 2 ),
             * vLitN = Vec_WecEntry( pFxchMan->vLits, Vec_WecSize( pFxchMan->vLits ) - 1 );

    Vec_IntForEachEntryDouble( pFxchMan->vPairs, iCube0, iCube1, i )
    {
        int RetValue,  
            fCompl = 0;

        Vec_Int_t* vCube0 = Fxch_ManGetCube( pFxchMan, iCube0 ),
                 * vCube1 = Fxch_ManGetCube( pFxchMan, iCube1 );

        RetValue  = Fxch_DivRemoveLits( vCube0, vCube1, pFxchMan->vDiv, &fCompl );

        assert( RetValue == Vec_IntSize( pFxchMan->vDiv ) );

        pFxchMan->nLits -= Vec_IntSize( pFxchMan->vDiv ) + Vec_IntSize( vCube1 ) - 2;

        /* Remove second cube */
        Vec_IntClear( vCube1 );
        Vec_IntWriteEntry( pFxchMan->vPairs, k++, Vec_WecLevelId( pFxchMan->vCubes, vCube0 ) );

        if ( iVarNew )
        {
            if ( Vec_IntSize( pFxchMan->vDiv ) == 2 || fCompl )
            {
                Vec_IntPush( vCube0, Abc_Var2Lit( iVarNew, 1 ) );
                Vec_IntPush( vLitN, Vec_WecLevelId( pFxchMan->vCubes, vCube0 ) );
            }
            else
            {
                Vec_IntPush( vCube0, Abc_Var2Lit( iVarNew, 0 ) );
                Vec_IntPush( vLitP, Vec_WecLevelId( pFxchMan->vCubes, vCube0 ) );
            }
        }
    }

    return k;
}

static inline int Fxch_ManCreateCube( Fxch_Man_t* pFxchMan,
                                      int Lit0,
                                      int Lit1 )
{
    int Level,
        iVarNew;
    Vec_Int_t* vCube0,
             * vCube1;
 
    /* Create a new variable */
    iVarNew = pFxchMan->nVars;
    pFxchMan->nVars++;

    /* Create new Lit hash keys */
    Vec_IntPush( pFxchMan->vLitHashKeys, Gia_ManRandom(0) & 0x3FFFFFF );
    Vec_IntPush( pFxchMan->vLitHashKeys, Gia_ManRandom(0) & 0x3FFFFFF );

    /* Create new Cube */
    vCube0 = Vec_WecPushLevel( pFxchMan->vCubes );
    Vec_IntPush( vCube0, iVarNew );

    if ( Vec_IntSize( pFxchMan->vDiv ) == 2 )
    {
        if ( Lit0 > Lit1 )
            ABC_SWAP(int, Lit0, Lit1);

        Vec_IntPush( vCube0, Abc_LitNot( Lit0 ) );
        Vec_IntPush( vCube0, Abc_LitNot( Lit1 ) );
        Level = 1 + Fxch_ManComputeLevelCube( pFxchMan, vCube0 );
    }
    else
    {
        vCube1 = Vec_WecPushLevel( pFxchMan->vCubes );
        vCube0 = Fxch_ManGetCube( pFxchMan, Vec_WecSize( pFxchMan->vCubes ) - 2 );
        Vec_IntPush( vCube1, iVarNew );
        Fxch_DivSepareteCubes( pFxchMan->vDiv, vCube0, vCube1 );
        Level = 2 + Abc_MaxInt( Fxch_ManComputeLevelCube( pFxchMan, vCube0 ),
                                Fxch_ManComputeLevelCube( pFxchMan, vCube1 ) );
    }
    assert( Vec_IntSize( pFxchMan->vLevels ) == iVarNew );
    Vec_IntPush( pFxchMan->vLevels, Level );

    pFxchMan->nLits += Vec_IntSize( pFxchMan->vDiv );

    /* Create new literals */
    Vec_WecPushLevel( pFxchMan->vLits );
    Vec_WecPushLevel( pFxchMan->vLits );

    return iVarNew;
}

void Fxch_ManUpdate( Fxch_Man_t* pFxchMan,
                     int iDiv )
{
    int i, k, iCube0, iCube1,
        Lit0 = -1,
        Lit1 = -1,
        iVarNew;

    Vec_Int_t* vCube0,
             * vCube1,
             * vDivCubePairs;

    /* Get the selected candidate (divisor) */
    Vec_IntClear( pFxchMan->vDiv );
    Vec_IntAppend( pFxchMan->vDiv, Hsh_VecReadEntry( pFxchMan->pDivHash, iDiv ) );

    /* Find cubes associated with the divisor */
    Vec_IntClear( pFxchMan->vCubesS );
    if ( Vec_IntSize( pFxchMan->vDiv ) == 2 )
    {
        Lit0 = Abc_Lit2Var( Vec_IntEntry( pFxchMan->vDiv, 0 ) );
        Lit1 = Abc_Lit2Var( Vec_IntEntry( pFxchMan->vDiv, 1 ) );
        assert( Lit0 >= 0 && Lit1 >= 0 );

        Fxch_ManCompressCubes( pFxchMan->vCubes, Vec_WecEntry( pFxchMan->vLits, Abc_LitNot( Lit0 ) ) );
        Fxch_ManCompressCubes( pFxchMan->vCubes, Vec_WecEntry( pFxchMan->vLits, Abc_LitNot( Lit1 ) ) );
        Vec_IntTwoRemoveCommon( Vec_WecEntry( pFxchMan->vLits, Abc_LitNot( Lit0 ) ),
                                Vec_WecEntry( pFxchMan->vLits, Abc_LitNot( Lit1 ) ),
                                pFxchMan->vCubesS );
    }

    /* Find pairs associated with the divisor */
    Vec_IntClear( pFxchMan->vPairs );
    vDivCubePairs = Vec_WecEntry( pFxchMan->vDivCubePairs, iDiv );
    Vec_IntAppend( pFxchMan->vPairs, vDivCubePairs );
    Vec_IntErase( vDivCubePairs );

    Vec_IntForEachEntryDouble( pFxchMan->vPairs, iCube0, iCube1, i )
    {
        assert( Fxch_ManGetLit( pFxchMan, iCube0, 0) == Fxch_ManGetLit( pFxchMan, iCube1, 0) );
        if (iCube0 > iCube1)
        {
            Vec_IntSetEntry( pFxchMan->vPairs, i, iCube1);
            Vec_IntSetEntry( pFxchMan->vPairs, i+1, iCube0);
        }
    }

    Vec_IntUniqifyPairs( pFxchMan->vPairs );
    assert( Vec_IntSize( pFxchMan->vPairs ) % 2 == 0 );

    /* subtract cost of single-cube divisors */
    Vec_IntForEachEntry( pFxchMan->vCubesS, iCube0, i )
        Fxch_ManDivSingleCube( pFxchMan, iCube0, 0, 1); /* remove (fAdd = 0) - fUpdate = 1 */

    Vec_IntForEachEntryDouble( pFxchMan->vPairs, iCube0, iCube1, i )
        Fxch_ManDivSingleCube( pFxchMan, iCube0, 0, 1), /* remove (fAdd = 0) - fUpdate = 1 */
        Fxch_ManDivSingleCube( pFxchMan, iCube1, 0, 1); /* remove (fAdd = 0) - fUpdate = 1 */

    /* subtract cost of double-cube divisors */
    Vec_IntForEachEntry( pFxchMan->vCubesS, iCube0, i )
        if ( iCube0 < Vec_IntSize(pFxchMan->pSCHashTable->vCubeLinks) )
            Fxch_ManDivDoubleCube( pFxchMan, iCube0, 0, 1 ); /* remove (fAdd = 0) - fUpdate = 1 */

    Vec_IntForEachEntry( pFxchMan->vPairs, iCube0, i )
        if ( iCube0 < Vec_IntSize(pFxchMan->pSCHashTable->vCubeLinks) )
            Fxch_ManDivDoubleCube( pFxchMan, iCube0, 0, 1 ); /* remove (fAdd = 0) - fUpdate = 1 */

    k = 0;
    if ( Fxch_DivIsNotConstant1( pFxchMan->vDiv ) )
    {
        iVarNew = Fxch_ManCreateCube( pFxchMan, Lit0, Lit1 );
        Fxch_ManExtractDivFromCube( pFxchMan, Lit0, Lit1, iVarNew );
        k = Fxch_ManExtractDivFromCubePairs( pFxchMan, iVarNew );
    }
    else
        k = Fxch_ManExtractDivFromCubePairs( pFxchMan, 0 );
 
    assert( k == Vec_IntSize( pFxchMan->vPairs ) / 2 );
    Vec_IntShrink( pFxchMan->vPairs, k );

    /* Add cost of single-cube divisors */
    Vec_IntForEachEntry( pFxchMan->vCubesS, iCube0, i )
        Fxch_ManDivSingleCube( pFxchMan, iCube0, 1, 1 ); /* fAdd = 1 - fUpdate = 1 */

    Vec_IntForEachEntry( pFxchMan->vPairs, iCube0, i )
        Fxch_ManDivSingleCube( pFxchMan, iCube0, 1, 1 ); /* fAdd = 1 - fUpdate = 1 */

    /* Add cost of double-cube divisors */
    Vec_IntForEachEntry( pFxchMan->vCubesS, iCube0, i )
        if ( iCube0 < Vec_IntSize(pFxchMan->pSCHashTable->vCubeLinks) )
            Fxch_ManDivDoubleCube( pFxchMan, iCube0, 1, 1 ); /* fAdd = 1 - fUpdate = 1 */

    Vec_IntForEachEntry( pFxchMan->vPairs, iCube0, i )
        if ( iCube0 < Vec_IntSize(pFxchMan->pSCHashTable->vCubeLinks) )
            Fxch_ManDivDoubleCube( pFxchMan, iCube0, 1, 1 ); /* fAdd = 1 - fUpdate = 1 */

    /* Deal with SCC */
    if ( Vec_IntSize( pFxchMan->vSCC ) )
    {
        Vec_IntUniqify( pFxchMan->vSCC );
        Vec_IntForEachEntry( pFxchMan->vSCC, iCube0, i )
            if ( iCube0 < Vec_IntSize(pFxchMan->pSCHashTable->vCubeLinks) )
            {
                Fxch_ManDivDoubleCube( pFxchMan, iCube0, 0, 1 ); /* remove (fAdd = 0) - fUpdate = 1 */
                vCube0 = Fxch_ManGetCube( pFxchMan, iCube0 ),
                Vec_IntClear( vCube0 );
            }

        Vec_IntClear( pFxchMan->vSCC );
    }


    /* If it's a double-cube devisor add its cost */
    if ( Vec_IntSize( pFxchMan->vDiv ) > 2 )
    {
        iCube0 = Vec_WecSize( pFxchMan->vCubes ) - 2;
        iCube1 = Vec_WecSize( pFxchMan->vCubes ) - 1;

        Fxch_ManDivSingleCube( pFxchMan, iCube0, 1, 1 );  /* fAdd = 1 - fUpdate = 1 */
        Fxch_ManDivSingleCube( pFxchMan, iCube1, 1, 1 );  /* fAdd = 1 - fUpdate = 1 */

        vCube0 = Vec_WecEntry( pFxchMan->vCubes, iCube0 );
        Vec_IntForEachEntryStart( vCube0, Lit0, i, 1 )
            Vec_WecPush( pFxchMan->vLits, Lit0, Vec_WecLevelId( pFxchMan->vCubes, vCube0 ) );

        vCube1 = Vec_WecEntry( pFxchMan->vCubes, iCube1 );
        Vec_IntForEachEntryStart( vCube1, Lit0, i, 1 )
            Vec_WecPush( pFxchMan->vLits, Lit0, Vec_WecLevelId( pFxchMan->vCubes, vCube1 ) );
    }

    /* remove these cubes from the lit array of the divisor */
    Vec_IntForEachEntry( pFxchMan->vDiv, Lit0, i )
    {
        Vec_IntTwoRemove( Vec_WecEntry( pFxchMan->vLits, Abc_Lit2Var( Lit0 ) ), pFxchMan->vPairs );
        Vec_IntTwoRemove( Vec_WecEntry( pFxchMan->vLits, Abc_LitNot( Abc_Lit2Var( Lit0 ) ) ), pFxchMan->vPairs );
    }

    pFxchMan->nExtDivs++;
}

/* Print */
void Fxch_ManPrintDivs( Fxch_Man_t* pFxchMan )
{
    int iDiv;

    for ( iDiv = 0; iDiv < Vec_FltSize( pFxchMan->vDivWeights ); iDiv++ )
        Fxch_DivPrint( pFxchMan, iDiv );
}

void Fxch_ManPrintStats( Fxch_Man_t* pFxchMan )
{
    printf( "Cubes =%8d  ", Vec_WecSizeUsed( pFxchMan->vCubes ) );
    printf( "Lits  =%8d  ", Vec_WecSizeUsed( pFxchMan->vLits ) );
    printf( "Divs  =%8d  ", Hsh_VecSize( pFxchMan->pDivHash ) );
    printf( "Divs+ =%8d  ", Vec_QueSize( pFxchMan->vDivPrio ) );
    printf( "Extr  =%7d  \n", pFxchMan->nExtDivs );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
