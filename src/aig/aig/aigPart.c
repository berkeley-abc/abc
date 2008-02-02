/**CFile****************************************************************

  FileName    [aigPart.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [AIG partitioning package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigPart.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Part_Man_t_     Part_Man_t;
struct Part_Man_t_
{
    int              nChunkSize;    // the size of one chunk of memory (~1 Mb)
    int              nStepSize;     // the step size in saving memory (~64 bytes)
    char *           pFreeBuf;      // the pointer to free memory
    int              nFreeSize;     // the size of remaining free memory
    Vec_Ptr_t *      vMemory;       // the memory allocated
    Vec_Ptr_t *      vFree;         // the vector of free pieces of memory
};

typedef struct Part_One_t_     Part_One_t;
struct Part_One_t_
{
    int              nRefs;         // the number of references
    int              nOuts;         // the number of outputs
    int              nOutsAlloc;    // the array size
    int              pOuts[0];      // the array of outputs
};

static inline int    Part_SizeType( int nSize, int nStepSize )     { return nSize / nStepSize + ((nSize % nStepSize) > 0); }
static inline char * Part_OneNext( char * pPart )                  { return *((char **)pPart);                             }
static inline void   Part_OneSetNext( char * pPart, char * pNext ) { *((char **)pPart) = pNext;                            }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Start the memory manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Part_Man_t * Part_ManStart( int nChunkSize, int nStepSize )
{
    Part_Man_t * p;
    p = ALLOC( Part_Man_t, 1 );
    memset( p, 0, sizeof(Part_Man_t) );
    p->nChunkSize = nChunkSize;
    p->nStepSize  = nStepSize;
    p->vMemory    = Vec_PtrAlloc( 1000 );
    p->vFree      = Vec_PtrAlloc( 1000 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the memory manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Part_ManStop( Part_Man_t * p )
{
    void * pMemory;
    int i;
    Vec_PtrForEachEntry( p->vMemory, pMemory, i )
        free( pMemory );
    Vec_PtrFree( p->vMemory );
    Vec_PtrFree( p->vFree );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Fetches the memory entry of the given size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Part_ManFetch( Part_Man_t * p, int nSize )
{
    int Type, nSizeReal;
    char * pMemory;
    assert( nSize > 0 );
    Type = Part_SizeType( nSize, p->nStepSize );
    Vec_PtrFillExtra( p->vFree, Type + 1, NULL );
    if ( (pMemory = Vec_PtrEntry( p->vFree, Type )) )
    {
        Vec_PtrWriteEntry( p->vFree, Type, Part_OneNext(pMemory) );
        return pMemory;
    }
    nSizeReal = p->nStepSize * Type;
    if ( p->nFreeSize < nSizeReal )
    {
        p->pFreeBuf = ALLOC( char, p->nChunkSize );
        p->nFreeSize = p->nChunkSize;
        Vec_PtrPush( p->vMemory, p->pFreeBuf );
    }
    assert( p->nFreeSize >= nSizeReal );
    pMemory = p->pFreeBuf;
    p->pFreeBuf  += nSizeReal;
    p->nFreeSize -= nSizeReal;
    return pMemory;
}

/**Function*************************************************************

  Synopsis    [Recycles the memory entry of the given size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Part_ManRecycle( Part_Man_t * p, char * pMemory, int nSize )
{
    int Type;
    Type = Part_SizeType( nSize, p->nStepSize );
    Vec_PtrFillExtra( p->vFree, Type + 1, NULL );
    Part_OneSetNext( pMemory, Vec_PtrEntry(p->vFree, Type) );
    Vec_PtrWriteEntry( p->vFree, Type, pMemory );
}

/**Function*************************************************************

  Synopsis    [Fetches the memory entry of the given size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Part_One_t * Part_ManFetchEntry( Part_Man_t * p, int nWords, int nRefs )
{
    Part_One_t * pPart;
    pPart = (Part_One_t *)Part_ManFetch( p, sizeof(Part_One_t) + sizeof(int) * nWords );
    pPart->nRefs = nRefs;
    pPart->nOuts = 0;
    pPart->nOutsAlloc = nWords;
    return pPart;
}

/**Function*************************************************************

  Synopsis    [Recycles the memory entry of the given size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Part_ManRecycleEntry( Part_Man_t * p, Part_One_t * pEntry )
{
    assert( pEntry->nOuts <= pEntry->nOutsAlloc );
    assert( pEntry->nOuts >= pEntry->nOutsAlloc/2 );
    Part_ManRecycle( p, (char *)pEntry, sizeof(Part_One_t) + sizeof(int) * pEntry->nOutsAlloc );
}

/**Function*************************************************************

  Synopsis    [Merges two entries.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Part_One_t * Part_ManMergeEntry( Part_Man_t * pMan, Part_One_t * p1, Part_One_t * p2, int nRefs )
{
    Part_One_t * p = Part_ManFetchEntry( pMan, p1->nOuts + p2->nOuts, nRefs );
    int * pBeg1 = p1->pOuts;
    int * pBeg2 = p2->pOuts;
    int * pBeg  = p->pOuts;
    int * pEnd1 = p1->pOuts + p1->nOuts;
    int * pEnd2 = p2->pOuts + p2->nOuts;
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        if ( *pBeg1 == *pBeg2 )
            *pBeg++ = *pBeg1++, pBeg2++;
        else if ( *pBeg1 < *pBeg2 )
            *pBeg++ = *pBeg1++;
        else 
            *pBeg++ = *pBeg2++;
    }
    while ( pBeg1 < pEnd1 )
        *pBeg++ = *pBeg1++;
    while ( pBeg2 < pEnd2 )
        *pBeg++ = *pBeg2++;
    p->nOuts = pBeg - p->pOuts;
    assert( p->nOuts <= p->nOutsAlloc );
    assert( p->nOuts >= p1->nOuts );
    assert( p->nOuts >= p2->nOuts );
    return p;
}

/**Function*************************************************************

  Synopsis    [Tranfers the entry.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Part_ManTransferEntry( Part_One_t * p )
{
    Vec_Int_t * vSupp;
    int i;
    vSupp = Vec_IntAlloc( p->nOuts );
    for ( i = 0; i < p->nOuts; i++ )
        Vec_IntPush( vSupp, p->pOuts[i] );
    return vSupp;
}

/**Function*************************************************************

  Synopsis    [Computes supports of the POs in the multi-output AIG.]

  Description [Returns the array of integer arrays containing indices
  of the primary inputs.]
               
  SideEffects [Adds the integer PO number at end of each array.]

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManSupports( Aig_Man_t * pMan )
{
    Vec_Ptr_t * vSupports;
    Vec_Int_t * vSupp;
    Part_Man_t * p;
    Part_One_t * pPart0, * pPart1;
    Aig_Obj_t * pObj;
    int i;
    // set the number of PIs/POs
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pNext = (Aig_Obj_t *)(long)i;
    Aig_ManForEachPo( pMan, pObj, i )
        pObj->pNext = (Aig_Obj_t *)(long)i;
    // start the support computation manager
    p = Part_ManStart( 1 << 20, 1 << 6 );
    // consider objects in the topological order
    vSupports = Vec_PtrAlloc( Aig_ManPoNum(pMan) );
    Aig_ManCleanData(pMan);
    Aig_ManForEachObj( pMan, pObj, i )
    {
        if ( Aig_ObjIsNode(pObj) )
        {
            pPart0 = Aig_ObjFanin0(pObj)->pData;
            pPart1 = Aig_ObjFanin1(pObj)->pData;
            pObj->pData = Part_ManMergeEntry( p, pPart0, pPart1, pObj->nRefs );
            assert( pPart0->nRefs > 0 );
            if ( --pPart0->nRefs == 0 )
                Part_ManRecycleEntry( p, pPart0 );
            assert( pPart1->nRefs > 0 );
            if ( --pPart1->nRefs == 0 )
                Part_ManRecycleEntry( p, pPart1 );
            continue;
        }
        if ( Aig_ObjIsPo(pObj) )
        {
            pPart0 = Aig_ObjFanin0(pObj)->pData;
            vSupp = Part_ManTransferEntry(pPart0);
            Vec_IntPush( vSupp, (int)(long)pObj->pNext );
            Vec_PtrPush( vSupports, vSupp );
            assert( pPart0->nRefs > 0 );
            if ( --pPart0->nRefs == 0 )
                Part_ManRecycleEntry( p, pPart0 );
            continue;
        }
        if ( Aig_ObjIsPi(pObj) )
        {
            if ( pObj->nRefs )
            {
                pPart0 = Part_ManFetchEntry( p, 1, pObj->nRefs );
                pPart0->pOuts[ pPart0->nOuts++ ] = (int)(long)pObj->pNext;
                pObj->pData = pPart0;
            }
            continue;
        }
        if ( Aig_ObjIsConst1(pObj) )
        {
            if ( pObj->nRefs )
                pObj->pData = Part_ManFetchEntry( p, 0, pObj->nRefs );
            continue;
        }
        assert( 0 );
    }
//printf( "Memory usage = %d Mb.\n", Vec_PtrSize(p->vMemory) * p->nChunkSize / (1<<20) );
    Part_ManStop( p );
    // sort supports by size
    Vec_VecSort( (Vec_Vec_t *)vSupports, 1 );
    // clear the number of PIs/POs
    Aig_ManForEachPi( pMan, pObj, i )
        pObj->pNext = NULL;
    Aig_ManForEachPo( pMan, pObj, i )
        pObj->pNext = NULL;
/*
    Aig_ManForEachPo( pMan, pObj, i )
        printf( "%d ", Vec_IntSize( (Vec_Int_t *)Vec_VecEntry(vSupports, i) ) );
    printf( "\n" );
*/
    return vSupports;
}

/**Function*************************************************************

  Synopsis    [Start char-bases support representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Aig_ManSuppCharStart( Vec_Int_t * vOne, int nPis )
{
    unsigned * pBuffer;
    int i, Entry;
    int nWords = Aig_BitWordNum(nPis);
    pBuffer = ALLOC( unsigned, nWords );
    memset( pBuffer, 0, sizeof(unsigned) * nWords );
    Vec_IntForEachEntry( vOne, Entry, i )
    {
        assert( Entry < nPis );
        Aig_InfoSetBit( pBuffer, Entry );
    }
    return pBuffer;
}

/**Function*************************************************************

  Synopsis    [Add to char-bases support representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManSuppCharAdd( unsigned * pBuffer, Vec_Int_t * vOne, int nPis )
{
    int i, Entry;
    Vec_IntForEachEntry( vOne, Entry, i )
    {
        assert( Entry < nPis );
        Aig_InfoSetBit( pBuffer, Entry );
    }
}

/**Function*************************************************************

  Synopsis    [Find the common variables using char-bases support representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManSuppCharCommon( unsigned * pBuffer, Vec_Int_t * vOne )
{
    int i, Entry, nCommon = 0;
    Vec_IntForEachEntry( vOne, Entry, i )
        nCommon += Aig_InfoHasBit(pBuffer, Entry);
    return nCommon;
}

/**Function*************************************************************

  Synopsis    [Find the best partition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManPartitionSmartFindPart( Vec_Ptr_t * vPartSuppsAll, Vec_Ptr_t * vPartsAll, Vec_Ptr_t * vPartSuppsBit, int nSuppSizeLimit, Vec_Int_t * vOne )
{
    Vec_Int_t * vPartSupp;//, * vPart;
    int Attract, Repulse, Value, ValueBest;
    int i, nCommon, iBest;
    iBest = -1;
    ValueBest = 0;
    Vec_PtrForEachEntry( vPartSuppsAll, vPartSupp, i )
    {
//        vPart = Vec_PtrEntry( vPartsAll, i );
//        if ( nSuppSizeLimit > 0 && Vec_IntSize(vPart) >= nSuppSizeLimit )
//            continue;
//        nCommon = Vec_IntTwoCountCommon( vPartSupp, vOne );
        nCommon = Aig_ManSuppCharCommon( Vec_PtrEntry(vPartSuppsBit, i), vOne );
        if ( nCommon == 0 )
            continue;
        if ( nCommon == Vec_IntSize(vOne) )
            return i;
        // skip partitions whose size exceeds the limit
        if ( nSuppSizeLimit > 0 && Vec_IntSize(vPartSupp) >= 2 * nSuppSizeLimit )
            continue;
        Attract = 1000 * nCommon / Vec_IntSize(vOne);
        if ( Vec_IntSize(vPartSupp) < 100 )
            Repulse = 1;
        else
            Repulse = 1+Aig_Base2Log(Vec_IntSize(vPartSupp)-100);
        Value = Attract/Repulse;
        if ( ValueBest < Value )
        {
            ValueBest = Value;
            iBest = i;
        }
    }
    if ( ValueBest < 75 )
        return -1;
    return iBest;
}

/**Function*************************************************************

  Synopsis    [Perform the smart partitioning.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManPartitionPrint( Aig_Man_t * p, Vec_Ptr_t * vPartsAll, Vec_Ptr_t * vPartSuppsAll )
{
    Vec_Int_t * vOne;
    int i, nOutputs, Counter;

    Counter = 0;
    Vec_PtrForEachEntry( vPartSuppsAll, vOne, i )
    {
        nOutputs = Vec_IntSize(Vec_PtrEntry(vPartsAll, i));
        printf( "%d=(%d,%d) ", i, Vec_IntSize(vOne), nOutputs );
        Counter += nOutputs;
        if ( i == Vec_PtrSize(vPartsAll) - 1 )
            break;
    }
    assert( Counter == Aig_ManPoNum(p) );
//    printf( "\nTotal = %d. Outputs = %d.\n", Counter, Aig_ManPoNum(p) );
}

/**Function*************************************************************

  Synopsis    [Perform the smart partitioning.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManPartitionCompact( Vec_Ptr_t * vPartsAll, Vec_Ptr_t * vPartSuppsAll, int nSuppSizeLimit )
{
    Vec_Int_t * vOne, * vPart, * vPartSupp, * vTemp;
    int i, iPart;

    if ( nSuppSizeLimit == 0 )
        nSuppSizeLimit = 200;

    // pack smaller partitions into larger blocks
    iPart = 0;
    vPart = vPartSupp = NULL;
    Vec_PtrForEachEntry( vPartSuppsAll, vOne, i )
    {
        if ( Vec_IntSize(vOne) < nSuppSizeLimit )
        {
            if ( vPartSupp == NULL )
            {
                assert( vPart == NULL );
                vPartSupp = Vec_IntDup(vOne);
                vPart = Vec_PtrEntry(vPartsAll, i);
            }
            else
            {
                vPartSupp = Vec_IntTwoMerge( vTemp = vPartSupp, vOne );
                Vec_IntFree( vTemp );
                vPart = Vec_IntTwoMerge( vTemp = vPart, Vec_PtrEntry(vPartsAll, i) );
                Vec_IntFree( vTemp );
                Vec_IntFree( Vec_PtrEntry(vPartsAll, i) );
            }
            if ( Vec_IntSize(vPartSupp) < nSuppSizeLimit )
                continue;
        }
        else
            vPart = Vec_PtrEntry(vPartsAll, i);
        // add the partition 
        Vec_PtrWriteEntry( vPartsAll, iPart, vPart );  
        vPart = NULL;
        if ( vPartSupp ) 
        {
            Vec_IntFree( Vec_PtrEntry(vPartSuppsAll, iPart) );
            Vec_PtrWriteEntry( vPartSuppsAll, iPart, vPartSupp );  
            vPartSupp = NULL;
        }
        iPart++;
    }
    // add the last one
    if ( vPart )
    {
        Vec_PtrWriteEntry( vPartsAll, iPart, vPart );  
        vPart = NULL;

        assert( vPartSupp != NULL );
        Vec_IntFree( Vec_PtrEntry(vPartSuppsAll, iPart) );
        Vec_PtrWriteEntry( vPartSuppsAll, iPart, vPartSupp );  
        vPartSupp = NULL;
        iPart++;
    }
    Vec_PtrShrink( vPartsAll, iPart );
    Vec_PtrShrink( vPartsAll, iPart );
}

/**Function*************************************************************

  Synopsis    [Perform the smart partitioning.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManPartitionSmart( Aig_Man_t * p, int nSuppSizeLimit, int fVerbose, Vec_Ptr_t ** pvPartSupps )
{
    Vec_Ptr_t * vPartSuppsBit;
    Vec_Ptr_t * vSupports, * vPartsAll, * vPartsAll2, * vPartSuppsAll;//, * vPartPtr;
    Vec_Int_t * vOne, * vPart, * vPartSupp, * vTemp;
    int i, iPart, iOut, clk;

    // compute the supports for all outputs
clk = clock();
    vSupports = Aig_ManSupports( p );
if ( fVerbose )
{
PRT( "Supps", clock() - clk );
}
    // start char-based support representation
    vPartSuppsBit = Vec_PtrAlloc( 1000 );

    // create partitions
clk = clock();
    vPartsAll = Vec_PtrAlloc( 256 );
    vPartSuppsAll = Vec_PtrAlloc( 256 );
    Vec_PtrForEachEntry( vSupports, vOne, i )
    {
        // get the output number
        iOut = Vec_IntPop(vOne);
        // find closely matching part
        iPart = Aig_ManPartitionSmartFindPart( vPartSuppsAll, vPartsAll, vPartSuppsBit, nSuppSizeLimit, vOne );
        if ( iPart == -1 )
        {
            // create new partition
            vPart = Vec_IntAlloc( 32 );
            Vec_IntPush( vPart, iOut );
            // create new partition support
            vPartSupp = Vec_IntDup( vOne );
            // add this partition and its support
            Vec_PtrPush( vPartsAll, vPart );
            Vec_PtrPush( vPartSuppsAll, vPartSupp );

            Vec_PtrPush( vPartSuppsBit, Aig_ManSuppCharStart(vOne, Aig_ManPiNum(p)) );
        }
        else
        {
            // add output to this partition
            vPart = Vec_PtrEntry( vPartsAll, iPart );
            Vec_IntPush( vPart, iOut );
            // merge supports
            vPartSupp = Vec_PtrEntry( vPartSuppsAll, iPart );
            vPartSupp = Vec_IntTwoMerge( vTemp = vPartSupp, vOne );
            Vec_IntFree( vTemp );
            // reinsert new support
            Vec_PtrWriteEntry( vPartSuppsAll, iPart, vPartSupp );

            Aig_ManSuppCharAdd( Vec_PtrEntry(vPartSuppsBit, iPart), vOne, Aig_ManPiNum(p) );
        }
    }

    // stop char-based support representation
    Vec_PtrForEachEntry( vPartSuppsBit, vTemp, i )
        free( vTemp );
    Vec_PtrFree( vPartSuppsBit );

//printf( "\n" );
if ( fVerbose )
{
PRT( "Parts", clock() - clk );
}

clk = clock();
    // reorder partitions in the decreasing order of support sizes
    // remember partition number in each partition support
    Vec_PtrForEachEntry( vPartSuppsAll, vOne, i )
        Vec_IntPush( vOne, i );
    // sort the supports in the decreasing order
    Vec_VecSort( (Vec_Vec_t *)vPartSuppsAll, 1 );
    // reproduce partitions
    vPartsAll2 = Vec_PtrAlloc( 256 );
    Vec_PtrForEachEntry( vPartSuppsAll, vOne, i )
        Vec_PtrPush( vPartsAll2, Vec_PtrEntry(vPartsAll, Vec_IntPop(vOne)) );
    Vec_PtrFree( vPartsAll );
    vPartsAll = vPartsAll2;

    // compact small partitions
//    Aig_ManPartitionPrint( p, vPartsAll, vPartSuppsAll );
    Aig_ManPartitionCompact( vPartsAll, vPartSuppsAll, nSuppSizeLimit );
    if ( fVerbose )
//    Aig_ManPartitionPrint( p, vPartsAll, vPartSuppsAll );
    printf( "Created %d partitions.\n", Vec_PtrSize(vPartsAll) );

if ( fVerbose )
{
//PRT( "Comps", clock() - clk );
}

    // cleanup
    Vec_VecFree( (Vec_Vec_t *)vSupports );
    if ( pvPartSupps == NULL )
        Vec_VecFree( (Vec_Vec_t *)vPartSuppsAll );
    else
        *pvPartSupps = vPartSuppsAll;
/*
    // converts from intergers to nodes
    Vec_PtrForEachEntry( vPartsAll, vPart, iPart )
    {
        vPartPtr = Vec_PtrAlloc( Vec_IntSize(vPart) );
        Vec_IntForEachEntry( vPart, iOut, i )
            Vec_PtrPush( vPartPtr, Aig_ManPo(p, iOut) );
        Vec_IntFree( vPart );
        Vec_PtrWriteEntry( vPartsAll, iPart, vPartPtr );
    }
*/
    return vPartsAll;
}

/**Function*************************************************************

  Synopsis    [Perform the naive partitioning.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManPartitionNaive( Aig_Man_t * p, int nPartSize )
{
    Vec_Ptr_t * vParts;
    Aig_Obj_t * pObj;
    int nParts, i;
    nParts = (Aig_ManPoNum(p) / nPartSize) + ((Aig_ManPoNum(p) % nPartSize) > 0);
    vParts = (Vec_Ptr_t *)Vec_VecStart( nParts );
    Aig_ManForEachPo( p, pObj, i )
        Vec_IntPush( Vec_PtrEntry(vParts, i / nPartSize), i );
    return vParts;
}



/**Function*************************************************************

  Synopsis    [Adds internal nodes in the topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDupPart_rec( Aig_Man_t * pNew, Aig_Man_t * pOld, Aig_Obj_t * pObj, Vec_Int_t * vSuppMap )
{
    assert( !Aig_IsComplement(pObj) );
    if ( Aig_ObjIsTravIdCurrent(pOld, pObj) )
        return pObj->pData;
    Aig_ObjSetTravIdCurrent(pOld, pObj);
    if ( Aig_ObjIsPi(pObj) )
    {
        assert( Vec_IntSize(vSuppMap) == Aig_ManPiNum(pNew) );
        Vec_IntPush( vSuppMap, (int)(long)pObj->pNext );
        return pObj->pData = Aig_ObjCreatePi(pNew);
    }
    assert( Aig_ObjIsNode(pObj) );
    Aig_ManDupPart_rec( pNew, pOld, Aig_ObjFanin0(pObj), vSuppMap );
    Aig_ManDupPart_rec( pNew, pOld, Aig_ObjFanin1(pObj), vSuppMap );
    return pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Adds internal nodes in the topological order.]

  Description [Returns the array of new outputs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManDupPart( Aig_Man_t * pNew, Aig_Man_t * pOld, Vec_Int_t * vPart, Vec_Int_t * vSuppMap, int fInverse )
{
    Vec_Ptr_t * vOutsTotal;
    Aig_Obj_t * pObj;
    int Entry, i;
    // create the PIs
    Aig_ManIncrementTravId( pOld );
    Aig_ManConst1(pOld)->pData = Aig_ManConst1(pNew);
    Aig_ObjSetTravIdCurrent( pOld, Aig_ManConst1(pOld) );
    if ( !fInverse )
    {
        Vec_IntForEachEntry( vSuppMap, Entry, i )
        {
            pObj = Aig_ManPi( pOld, Entry );
            pObj->pData = Aig_ManPi( pNew, i );
            Aig_ObjSetTravIdCurrent( pOld, pObj );
        }
    }
    else
    {
        Vec_IntForEachEntry( vSuppMap, Entry, i )
        {
            pObj = Aig_ManPi( pOld, i );
            pObj->pData = Aig_ManPi( pNew, Entry );
            Aig_ObjSetTravIdCurrent( pOld, pObj );
        }
        vSuppMap = NULL; // should not be useful
    }
    // create the internal nodes
    vOutsTotal = Vec_PtrAlloc( Vec_IntSize(vPart) );
    if ( !fInverse )
    {
        Vec_IntForEachEntry( vPart, Entry, i )
        {
            pObj = Aig_ManPo( pOld, Entry );
            Aig_ManDupPart_rec( pNew, pOld, Aig_ObjFanin0(pObj), vSuppMap );
            Vec_PtrPush( vOutsTotal, Aig_ObjChild0Copy(pObj) );
        }
    }
    else
    {
        Aig_ManForEachObj( pOld, pObj, i )
        {
            if ( Aig_ObjIsPo(pObj) )
            {
                Aig_ManDupPart_rec( pNew, pOld, Aig_ObjFanin0(pObj), vSuppMap );
                Vec_PtrPush( vOutsTotal, Aig_ObjChild0Copy(pObj) );
            }
            else if ( Aig_ObjIsNode(pObj) && pObj->nRefs == 0 )
                Aig_ManDupPart_rec( pNew, pOld, pObj, vSuppMap );
            
        }
    }
    return vOutsTotal; 
}

/**Function*************************************************************

  Synopsis    [Create partitioned miter of the two AIGs.]

  Description [Assumes that each output in the second AIG cannot have 
  more supp vars than the same output in the first AIG.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_ManMiterPartitioned( Aig_Man_t * p1, Aig_Man_t * p2, int nPartSize )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pMiter;
    Vec_Ptr_t * vMiters, * vNodes1, * vNodes2;
    Vec_Ptr_t * vParts, * vPartSupps;
    Vec_Int_t * vPart, * vPartSupp;
    int i, k;
    // partition the first manager
    vParts = Aig_ManPartitionSmart( p1, nPartSize, 0, &vPartSupps );
    // derive miters
    vMiters = Vec_PtrAlloc( Vec_PtrSize(vParts) );
    for ( i = 0; i < Vec_PtrSize(vParts); i++ )
    {
        // get partition and its support
        vPart     = Vec_PtrEntry( vParts, i );
        vPartSupp = Vec_PtrEntry( vPartSupps, i );
        // create the new miter
        pNew = Aig_ManStart( 1000 );
//        pNew->pName = Extra_UtilStrsav( p1->pName );
        // create the PIs
        for ( k = 0; k < Vec_IntSize(vPartSupp); k++ )
            Aig_ObjCreatePi( pNew );
        // copy the components
        vNodes1 = Aig_ManDupPart( pNew, p1, vPart, vPartSupp, 0 );
        vNodes2 = Aig_ManDupPart( pNew, p2, vPart, vPartSupp, 0 );
        // create the miter
        pMiter = Aig_MiterTwo( pNew, vNodes1, vNodes2 );
        Vec_PtrFree( vNodes1 );
        Vec_PtrFree( vNodes2 );
        // create the output
        Aig_ObjCreatePo( pNew, pMiter );
        // clean up
        Aig_ManCleanup( pNew );
        Vec_PtrPush( vMiters, pNew );
    }
    Vec_VecFree( (Vec_Vec_t *)vParts );
    Vec_VecFree( (Vec_Vec_t *)vPartSupps );
    return vMiters;
}

/**Function*************************************************************

  Synopsis    [Performs partitioned choice computation.]

  Description [Assumes that each output in the second AIG cannot have 
  more supp vars than the same output in the first AIG.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManChoicePartitioned( Vec_Ptr_t * vAigs, int nPartSize, int fVerbose )
{
//    extern int Cmd_CommandExecute( void * pAbc, char * sCommand );
//    extern void * Abc_FrameGetGlobalFrame();
    extern Aig_Man_t * Fra_FraigChoice( Aig_Man_t * pManAig, int nConfMax );

    Vec_Ptr_t * vOutsTotal, * vOuts;
    Aig_Man_t * pAigTotal, * pAigPart, * pAig;
    Vec_Int_t * vPart, * vPartSupp;
    Vec_Ptr_t * vParts;
    Aig_Obj_t * pObj;
    void ** ppData;
    int i, k, m;

    // partition the first AIG in the array
    assert( Vec_PtrSize(vAigs) > 1 );
    pAig = Vec_PtrEntry( vAigs, 0 );
    vParts = Aig_ManPartitionSmart( pAig, nPartSize, 0, NULL );

    // start the total fraiged AIG
    pAigTotal = Aig_ManStartFrom( pAig );
    Aig_ManReprStart( pAigTotal, Vec_PtrSize(vAigs) * Aig_ManObjNumMax(pAig) + 10000 );
    vOutsTotal = Vec_PtrStart( Aig_ManPoNum(pAig) );

    // set the PI numbers
    Vec_PtrForEachEntry( vAigs, pAig, i )
        Aig_ManForEachPi( pAig, pObj, k )
            pObj->pNext = (Aig_Obj_t *)(long)k;

//    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "unset progressbar" );

    // create the total fraiged AIG
    vPartSupp = Vec_IntAlloc( 100 ); // maps part PI num into total PI num
    Vec_PtrForEachEntry( vParts, vPart, i )
    {
        // derive the partition AIG
        pAigPart = Aig_ManStart( 5000 );
//        pAigPart->pName = Extra_UtilStrsav( pAigPart->pName );
        Vec_IntClear( vPartSupp );
        Vec_PtrForEachEntry( vAigs, pAig, k )
        {
            vOuts = Aig_ManDupPart( pAigPart, pAig, vPart, vPartSupp, 0 );
            if ( k == 0 )
            {
                Vec_PtrForEachEntry( vOuts, pObj, m )
                    Aig_ObjCreatePo( pAigPart, pObj );
            }
            Vec_PtrFree( vOuts );
        }
        // derive the total AIG from the partitioned AIG
        vOuts = Aig_ManDupPart( pAigTotal, pAigPart, vPart, vPartSupp, 1 );
        // add to the outputs
        Vec_PtrForEachEntry( vOuts, pObj, k )
        {
            assert( Vec_PtrEntry( vOutsTotal, Vec_IntEntry(vPart,k) ) == NULL );
            Vec_PtrWriteEntry( vOutsTotal, Vec_IntEntry(vPart,k), pObj );
        }
        Vec_PtrFree( vOuts );
        // store contents of pData pointers
        ppData = ALLOC( void *, Aig_ManObjNumMax(pAigPart) );
        Aig_ManForEachObj( pAigPart, pObj, k )
            ppData[k] = pObj->pData;
        // report the process
        if ( fVerbose )
        printf( "Part %4d  (out of %4d)  PI = %5d. PO = %5d. And = %6d. Lev = %4d.\r", 
            i+1, Vec_PtrSize(vParts), Aig_ManPiNum(pAigPart), Aig_ManPoNum(pAigPart), 
            Aig_ManNodeNum(pAigPart), Aig_ManLevelNum(pAigPart) );
        // compute equivalence classes (to be stored in pNew->pReprs)
        pAig = Fra_FraigChoice( pAigPart, 1000 );
        Aig_ManStop( pAig );
        // reset the pData pointers
        Aig_ManForEachObj( pAigPart, pObj, k )
            pObj->pData = ppData[k];
        free( ppData );
        // transfer representatives to the total AIG
        if ( pAigPart->pReprs )
            Aig_ManTransferRepr( pAigTotal, pAigPart );
        Aig_ManStop( pAigPart );
    }
    if ( fVerbose )
    printf( "                                                                                          \r" );
    Vec_VecFree( (Vec_Vec_t *)vParts );
    Vec_IntFree( vPartSupp );

//    Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "set progressbar" );

    // clear the PI numbers
    Vec_PtrForEachEntry( vAigs, pAig, i )
        Aig_ManForEachPi( pAig, pObj, k )
            pObj->pNext = NULL;
/*
    // collect the missing outputs (outputs whose driver is not a node)
    pAig = Vec_PtrEntry( vAigs, 0 );
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pAigTotal);
    Aig_ManForEachPi( pAig, pObj, i )
        pAig->pData = Aig_ManPi( pAigTotal, i );
    Aig_ManForEachPo( pAig, pObj, i )
        if ( !Aig_ObjIsNode(Aig_ObjFanin0(pObj)) )
        {
            assert( Vec_PtrEntry( vOutsTotal, i ) == NULL );
            Vec_PtrWriteEntry( vOutsTotal, i, Aig_ObjChild0Copy(pObj) );
        }
*/
    // add the outputs in the same order
    Vec_PtrForEachEntry( vOutsTotal, pObj, i )
        Aig_ObjCreatePo( pAigTotal, pObj );
    Vec_PtrFree( vOutsTotal );

    // derive the result of choicing
    pAig = Aig_ManRehash( pAigTotal );
    // create the equivalent nodes lists
    Aig_ManMarkValidChoices( pAig );
    return pAig;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


