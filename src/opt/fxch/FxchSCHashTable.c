/**CFile****************************************************************

  FileName    [ FxchSCHashTable.c ]

  PackageName [ Fast eXtract with Cube Hashing (FXCH) ]

  Synopsis    [ Sub-cubes hash table implementation ]

  Author      [ Bruno Schmitt - boschmitt at inf.ufrgs.br ]

  Affiliation [ UFRGS ]

  Date        [ Ver. 1.0. Started - March 6, 2016. ]

  Revision    []

***********************************************************************/
#include "Fxch.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
static inline void MurmurHash3_x86_32 ( const void* key,
                                        int len,
                                        uint32_t seed,
                                        void* out )
{
    const uint8_t* data = (const uint8_t*)key;
    const int nblocks = len / 4;

    uint32_t h1 = seed;

    const uint32_t c1 = 0xcc9e2d51;
    const uint32_t c2 = 0x1b873593;

    //----------
    // body

    const uint32_t * blocks = (const uint32_t *)(data + nblocks*4);

    for(int i = -nblocks; i; i++)
    {
        uint32_t k1 = blocks[i];

        k1 *= c1;
        k1 = (k1 << 15) | (k1 >> (32 - 15));
        k1 *= c2;

        h1 ^= k1;
        h1 = (h1 << 13) | (h1 >> (32 - 13));
        h1 = h1*5+0xe6546b64;
    }

    //----------
    // tail

    const uint8_t * tail = (const uint8_t*)(data + nblocks*4);

    uint32_t k1 = 0;

    switch(len & 3)
    {
        case 3: k1 ^= tail[2] << 16;
        case 2: k1 ^= tail[1] << 8;
        case 1: k1 ^= tail[0];
              k1 *= c1; k1 = (k1 << 15) | (k1 >> (32 - 15)); k1 *= c2; h1 ^= k1;
    };

    //----------
    // finalization

    h1 ^= len;

    h1 ^= h1 >> 16;
    h1 *= 0x85ebca6b;
    h1 ^= h1 >> 13;
    h1 *= 0xc2b2ae35;
    h1 ^= h1 >> 16;

    *(uint32_t*)out = h1;
}

Fxch_SCHashTable_t* Fxch_SCHashTableCreate( Fxch_Man_t* pFxchMan,
                                            Vec_Int_t* vCubeLinks,
                                            int nEntries )
{
    Fxch_SCHashTable_t* pSCHashTable = ABC_CALLOC( Fxch_SCHashTable_t, 1 );
    int nBits = Abc_Base2Log( nEntries + 1 ) + 1;


    pSCHashTable->pFxchMan = pFxchMan;
    pSCHashTable->SizeMask = (1 << nBits) - 1;
    pSCHashTable->vCubeLinks = vCubeLinks;
    pSCHashTable->pBins = ABC_CALLOC( Fxch_SCHashTable_Entry_t, pSCHashTable->SizeMask + 1 );

    return pSCHashTable;
}

void Fxch_SCHashTableDelete( Fxch_SCHashTable_t* pSCHashTable )
{
    Vec_IntFree( pSCHashTable->vCubeLinks );
    Vec_IntErase( &pSCHashTable->vSubCube0 );
    Vec_IntErase( &pSCHashTable->vSubCube1 );
    ABC_FREE( pSCHashTable->pBins );
    ABC_FREE( pSCHashTable );
}

static inline Fxch_SCHashTable_Entry_t* Fxch_SCHashTableBin( Fxch_SCHashTable_t* pSCHashTable,
                                                             unsigned int SubCubeID )
{
    return pSCHashTable->pBins + (SubCubeID & pSCHashTable->SizeMask);
}

static inline Fxch_SCHashTable_Entry_t* Fxch_SCHashTableEntry( Fxch_SCHashTable_t* pSCHashTable,
                                                               unsigned int iEntry )
{
    if ( ( iEntry > 0 ) && ( iEntry < ( pSCHashTable->SizeMask + 1 ) ) )
        return pSCHashTable->pBins + iEntry;

    return NULL;
}

static inline void Fxch_SCHashTableInsertLink( Fxch_SCHashTable_t* pSCHashTable,
                                               unsigned int iEntry0,
                                               unsigned int iEntry1 )
{
    Fxch_SCHashTable_Entry_t* pEntry0 = Fxch_SCHashTableEntry( pSCHashTable, iEntry0 ),
                            * pEntry1 = Fxch_SCHashTableEntry( pSCHashTable, iEntry1 ),
                            * pEntry0Next = Fxch_SCHashTableEntry( pSCHashTable, pEntry0->iNext );

    assert( pEntry0Next->iPrev == iEntry0 );

    pEntry1->iNext = pEntry0->iNext;
    pEntry0->iNext = iEntry1;
    pEntry1->iPrev = iEntry0;
    pEntry0Next->iPrev = iEntry1;
}

static inline void Fxch_SCHashTableRemoveLink( Fxch_SCHashTable_t* pSCHashTable,
                                               int iEntry0,
                                               int iEntry1 )
{
    Fxch_SCHashTable_Entry_t* pEntry0 = Fxch_SCHashTableEntry( pSCHashTable, iEntry0 ),
                            * pEntry1 = Fxch_SCHashTableEntry( pSCHashTable, iEntry1 ),
                            * pEntry1Next = Fxch_SCHashTableEntry( pSCHashTable, pEntry1->iNext );

    assert( pEntry0->iNext == iEntry1 );
    assert( pEntry1->iPrev == iEntry0 );
    assert( pEntry1Next->iPrev == iEntry1 );

    pEntry0->iNext = pEntry1->iNext;
    pEntry1->iNext = 0;
    pEntry1Next->iPrev = pEntry1->iPrev;
    pEntry1->iPrev = 0;
}

static inline int Fxch_SCHashTableEntryCompare( Fxch_SCHashTable_t* pSCHashTable,
                                                Vec_Wec_t* vCubes,
                                                Fxch_SubCube_t* pSCData0,
                                                Fxch_SubCube_t* pSCData1 )
{
    Vec_Int_t* vCube0 = Vec_WecEntry( vCubes, pSCData0->iCube ),
             * vCube1 = Vec_WecEntry( vCubes, pSCData1->iCube );

    if ( !Vec_IntSize( vCube0 ) ||
         !Vec_IntSize( vCube1 ) ||
         Vec_IntEntry( vCube0, 0 ) != Vec_IntEntry( vCube1, 0 ) ||
         pSCData0->Id != pSCData1->Id )
        return 0;

    Vec_IntClear( &pSCHashTable->vSubCube0 );
    Vec_IntClear( &pSCHashTable->vSubCube1 );

    if ( pSCData0->iLit1 == 0 && pSCData1->iLit1 == 0 &&
         Vec_IntEntry( vCube0, pSCData0->iLit0 ) == Abc_LitNot( Vec_IntEntry( vCube1, pSCData1->iLit0 ) ) )
        return 0;

    if ( pSCData0->iLit1 > 0 && pSCData1->iLit1 > 0 &&
         ( Vec_IntEntry( vCube0, pSCData0->iLit0 ) == Vec_IntEntry( vCube1, pSCData1->iLit0 ) ||
           Vec_IntEntry( vCube0, pSCData0->iLit0 ) == Vec_IntEntry( vCube1, pSCData1->iLit1 ) ||
           Vec_IntEntry( vCube0, pSCData0->iLit1 ) == Vec_IntEntry( vCube1, pSCData1->iLit0 ) ||
           Vec_IntEntry( vCube0, pSCData0->iLit1 ) == Vec_IntEntry( vCube1, pSCData1->iLit1 ) ) )
        return 0;


    if ( pSCData0->iLit0 > 0 )
        Vec_IntAppendSkip( &pSCHashTable->vSubCube0, vCube0, pSCData0->iLit0 );
    else
        Vec_IntAppend( &pSCHashTable->vSubCube0, vCube0 );

    if ( pSCData1->iLit0 > 0 )
        Vec_IntAppendSkip( &pSCHashTable->vSubCube1, vCube1, pSCData1->iLit0 );
    else
        Vec_IntAppend( &pSCHashTable->vSubCube1, vCube1 );


    if ( pSCData0->iLit1 > 0)
        Vec_IntDrop( &pSCHashTable->vSubCube0,
                       pSCData0->iLit0 < pSCData0->iLit1 ? pSCData0->iLit1 - 1 : pSCData0->iLit1 );

    if ( pSCData1->iLit1 > 0 )
        Vec_IntDrop( &pSCHashTable->vSubCube1,
                       pSCData1->iLit0 < pSCData1->iLit1 ? pSCData1->iLit1 - 1 : pSCData1->iLit1 );

    Vec_IntDrop( &pSCHashTable->vSubCube0, 0 );
    Vec_IntDrop( &pSCHashTable->vSubCube1, 0 );

    return Vec_IntEqual( &pSCHashTable->vSubCube0, &pSCHashTable->vSubCube1 );
}

int Fxch_SCHashTableInsert( Fxch_SCHashTable_t* pSCHashTable,
                            Vec_Wec_t* vCubes,
                            unsigned int SubCubeID, 
                            unsigned int iSubCube,
                            unsigned int iCube, 
                            unsigned int iLit0, 
                            unsigned int iLit1,
                            char fUpdate )
{
    unsigned int BinID;
    MurmurHash3_x86_32( ( void* ) &SubCubeID, sizeof( int ), 0x9747b28c, &BinID);
    
    unsigned int iNewEntry = ( unsigned int )( Vec_IntEntry( pSCHashTable->vCubeLinks, iCube ) ) + iSubCube;
    Fxch_SCHashTable_Entry_t* pBin = Fxch_SCHashTableBin( pSCHashTable, BinID ),
                            * pNewEntry = Fxch_SCHashTableEntry( pSCHashTable, iNewEntry );

    assert( pNewEntry->Used == 0 );

    pNewEntry->SCData.Id = SubCubeID;
    pNewEntry->SCData.iCube = iCube;
    pNewEntry->SCData.iLit0 = iLit0;
    pNewEntry->SCData.iLit1 = iLit1;

    pNewEntry->Used = 1;
    pSCHashTable->nEntries++;
    if ( pBin->iTable == 0 )
    {
        pBin->iTable = iNewEntry;
        pNewEntry->iNext = iNewEntry;
        pNewEntry->iPrev = iNewEntry;
        return 0;
    }

    Fxch_SCHashTable_Entry_t* pEntry;
    unsigned int iEntry;
    char Pairs = 0,
         fStart = 1;
    for ( iEntry = pBin->iTable; iEntry != pBin->iTable || fStart; iEntry = pEntry->iNext, fStart = 0 )
    {
        pEntry = Fxch_SCHashTableBin( pSCHashTable, iEntry );

        if ( !Fxch_SCHashTableEntryCompare( pSCHashTable, vCubes, &( pEntry->SCData ), &( pNewEntry->SCData ) ) )
            continue;

        if ( pEntry->SCData.iLit0 == 0 )
        {
            printf("[FXCH] SCC detected\n");
            continue;
        }
        if ( pNewEntry->SCData.iLit0 == 0 )
        {
            printf("[FXCH] SCC detected\n");
            continue;
        }

        int Base;
        if ( pEntry->SCData.iCube < pNewEntry->SCData.iCube )
            Base = Fxch_DivCreate( pSCHashTable->pFxchMan, &( pEntry->SCData ), &( pNewEntry->SCData ) );
        else
            Base = Fxch_DivCreate( pSCHashTable->pFxchMan, &( pNewEntry->SCData ), &( pEntry->SCData ) );

        if ( Base < 0 ) 
            continue;

        int iNewDiv = Fxch_DivAdd( pSCHashTable->pFxchMan, fUpdate, 0, Base );

        if ( pSCHashTable->pFxchMan->SMode == 0 )
        {
            Vec_WecPush( pSCHashTable->pFxchMan->vDivCubePairs, iNewDiv, pEntry->SCData.iCube );
            Vec_WecPush( pSCHashTable->pFxchMan->vDivCubePairs, iNewDiv, pNewEntry->SCData.iCube );
        }

        Pairs++;
    }
    assert( iEntry == (unsigned int)( pBin->iTable ) );

    pEntry = Fxch_SCHashTableBin( pSCHashTable, iEntry );
    Fxch_SCHashTableInsertLink( pSCHashTable, pEntry->iPrev, iNewEntry );

    return Pairs;
}

int Fxch_SCHashTableRemove( Fxch_SCHashTable_t* pSCHashTable,
                            Vec_Wec_t* vCubes,
                            unsigned int SubCubeID, 
                            unsigned int iSubCube,
                            unsigned int iCube, 
                            unsigned int iLit0, 
                            unsigned int iLit1,
                            char fUpdate )
{
    unsigned int BinID;
    MurmurHash3_x86_32( ( void* ) &SubCubeID, sizeof( int ), 0x9747b28c, &BinID);
    
    unsigned int iEntry = ( unsigned int )( Vec_IntEntry( pSCHashTable->vCubeLinks, iCube ) ) + iSubCube;
    Fxch_SCHashTable_Entry_t* pBin = Fxch_SCHashTableBin( pSCHashTable, BinID ),
                            * pEntry = Fxch_SCHashTableEntry( pSCHashTable, iEntry );
    
    assert( pEntry->Used == 1 );
    assert( pEntry->SCData.iCube == iCube );

    if ( pEntry->iNext == iEntry )
    {
        assert( pEntry->iPrev == iEntry );
        pBin->iTable = 0;
        pEntry->iNext = 0;
        pEntry->iPrev = 0;
        pEntry->Used = 0;
        return 0;
    }

    Fxch_SCHashTable_Entry_t* pNextEntry;
    int iNextEntry,
        Pairs = 0,
        fStart = 1;
    for ( iNextEntry = pEntry->iNext; iNextEntry != iEntry; iNextEntry = pNextEntry->iNext, fStart = 0 )
    {
        pNextEntry = Fxch_SCHashTableBin( pSCHashTable, iNextEntry );

        if ( !Fxch_SCHashTableEntryCompare( pSCHashTable, vCubes, &( pEntry->SCData ), &( pNextEntry->SCData ) ) 
             || pEntry->SCData.iLit0 == 0
             || pNextEntry->SCData.iLit0 == 0 )
            continue;

        int Base;
        if ( pNextEntry->SCData.iCube < pEntry->SCData.iCube )
            Base = Fxch_DivCreate( pSCHashTable->pFxchMan, &( pNextEntry->SCData ), &( pEntry->SCData ) );
        else
            Base = Fxch_DivCreate( pSCHashTable->pFxchMan, &( pEntry->SCData ), &( pNextEntry->SCData ) );

        if ( Base < 0 ) 
            continue;

        int iDiv = Fxch_DivRemove( pSCHashTable->pFxchMan, fUpdate, 0, Base );

        if ( pSCHashTable->pFxchMan->SMode == 0 )
        {
            int i,
                iCube0,
                iCube1;

            Vec_Int_t* vDivCubePairs = Vec_WecEntry( pSCHashTable->pFxchMan->vDivCubePairs, iDiv );
            Vec_IntForEachEntryDouble( vDivCubePairs, iCube0, iCube1, i )
                if ( ( iCube0 == pNextEntry->SCData.iCube &&  iCube1 == pEntry->SCData.iCube )  ||
                     ( iCube0 == pEntry->SCData.iCube &&  iCube1 == pNextEntry->SCData.iCube ) )
                {
                    Vec_IntDrop( vDivCubePairs, i+1 );
                    Vec_IntDrop( vDivCubePairs, i );
                }
            if ( Vec_IntSize( vDivCubePairs ) == 0 )
                Vec_IntErase( vDivCubePairs );
        }

        Pairs++;
    }

    if ( pBin->iTable == iEntry )
        pBin->iTable = ( pEntry->iNext != iEntry ) ? pEntry->iNext : 0;

    pEntry->Used = 0;
    Fxch_SCHashTableRemoveLink( pSCHashTable, pEntry->iPrev, iEntry );
    return Pairs;
}

unsigned int Fxch_SCHashTableMemory( Fxch_SCHashTable_t* pHashTable )
{
    unsigned int Memory = sizeof ( Fxch_SCHashTable_t );

    Memory += Vec_IntMemory( pHashTable->vCubeLinks );
    Memory += sizeof( Fxch_SubCube_t ) * ( pHashTable->SizeMask + 1 );

    return Memory;
}

void Fxch_SCHashTablePrint( Fxch_SCHashTable_t* pHashTable )
{
    printf( "SubCube Hash Table at %p\n", ( void* )pHashTable );
    printf("%20s %20s\n", "nEntries",
                          "Memory Usage (MB)" );

    int Memory = Fxch_SCHashTableMemory( pHashTable );
    printf("%20d %18.2f\n", pHashTable->nEntries,
                            ( ( double ) Memory / 1048576 ) );
}
////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
