/**CFile****************************************************************

  FileName    [abcFx2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Independent fast_extract implementation with exact acceleration.]

  Author      [Alan Mishchenko, Bruno Schmitt]

  Affiliation [UC Berkeley, UFRGS]

  Date        [Ver. 1.0. Started - November 6, 2026.]

  Revision    [$Id: abcFx2.c,v 1.00 2026/11/06 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "misc/vec/vecWec.h"
#include "misc/vec/vecQue.h"


ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// The code in this file implements the traditional "fast_extract" algorithm,
//     which extracts two-cube divisors concurrently with single-cube two-literal divisors,
//     as proposed in the TCAD'92 paper by J. Rajski and J. Vasudevamurthi.
//
//     Integration notes:
//
//     It is assumed that each object (primary input or internal node) in the original network
//     is associated with a unique integer number, called object identifier (ObjId, for short).
//
//     The user's input data given to 'fast_extract" is an array of cubes (pMan->vCubes).
//     Each cube is an array of integers, in which the first entry contains ObjId of the node,
//     to which this cube belongs in the original network. The following entries of a cube are
//     SOP literals of this cube.  Each literal is represtned as 2*FaninId + ComplAttr, where FaninId
//     is ObjId of the fanin node and ComplAttr is 1 if literal is complemented, and 0 otherwise.
//
//     The user's output data produced by 'fast_extract' is also an array of cubes (pMan->vCubes).
//     If no divisors have been extracted, the output array is the same as the input array.
//     If some divisors have been extracted, the output array contains updated old cubes and new cubes
//     representing the extracted divisors. The new divisors have their ObjId starting from the
//     largest ObjId used in the cubes. To give the user more flexibility, which may be needed when some
//     ObjIds are already used for primary output nodes, which do not participate in fast_extract,
//     the parameter ObjIdMax is passed to procedure Fx2_FastExtract().  The new divisors will receive
//     their ObjId starting from ObjIdMax onward, as divisor extaction proceeds.
//
//     The following two requirements are imposed on the input and output array of cubes:
//     (1) The array of cubes should be sorted by the first entry in each cube (that is, cubes belonging
//     to the same node should form a contiguous range).
//     (2) Literals in a cube should be sorted in the increasing order of the integer numbers.
//
//     To integrate this code into a calling application, such as ABC, the input cube array should
//     be generated (below this is done by the procedure Abc_NtkFx2Retrieve) and the output cube array
//     should be incorporated into the current network (below this is done by the procedure Abc_NtkFx2Insert).
//     In essence, the latter procedure performs the following:
//     - removes the current fanins and SOPs of each node in the network
//     - adds new nodes for each new divisor introduced by "fast_extract"
//     - populates fanins and SOPs of each node, both old and new, as indicaded by the resulting cube array.
//
//     Implementation notes:
//
//     The implementation is optimized for simplicity and speed of computation.
//     (1) Main input/output data-structure (pMan->vCubes) is the array of cubes which is dynamically updated by the algorithm.
//     (2) Auxiliary data-structure (pMan->vLits) is the array of arrays. The i-th array contains IDs of cubes which have literal i.
//     It may be convenient to think about the first (second) array as rows (columns) of a sparse matrix,
//     although the sparse matrix data-structure is not used in the proposed implementation.
//     (3) Hash table (pMan->pHash) hashes the normalized divisors (represented as integer arrays) into integer numbers.
//     (4) Array of divisor weights (pMan->vWeights), that is, the number of SOP literals to be saved by extacting each divisor.
//     (5) Priority queue (pMan->vPrio), which sorts divisor (integer numbers) by their weight
//     (6) Integer array (pMan->vVarCube), which maps each ObjId into the first cube of this object,
//     or -1, if there is no cubes as in the case of a primary input.

typedef struct Fx2_Hash_t_ Fx2_Hash_t;
struct Fx2_Hash_t_
{
    Vec_Int_t *     vTable;     // open-addressed table of divisor IDs
    Vec_Int_t *     vData;      // size followed by literals of each divisor
    Vec_Int_t *     vMap;       // divisor ID -> offset in vData
    Vec_Int_t       vTemp;      // borrowed view used when reading a divisor
};

typedef struct Fx2_Man_t_ Fx2_Man_t;
struct Fx2_Man_t_
{
    // user's data
    Vec_Wec_t *     vCubes;     // cube -> lit
    int             LitCountMax;// max size of divisor to extract
    int             fCanonDivs; // use only AND/XOR/MUX
    int             fInvalid;  // unsupported cover; discard the private cube edits
    // internal data
    Vec_Wec_t *     vLits;      // lit -> cube
    Fx2_Hash_t *    pHash;      // hash table for normalized divisors
    Vec_Flt_t *     vWeights;   // divisor weights
    Vec_Que_t *     vPrio;      // priority queue for divisors by weight
    Vec_Int_t *     vVarCube;   // mapping ObjId into its first cube
    Vec_Int_t *     vVarStop;   // end of each object's cube range
    Vec_Int_t *     vCandidates;// pairs surviving the signature bound
    Vec_Int_t *     vLevels;    // variable levels
    Vec_Wrd_t *     vSigns;     // cube signatures for rejecting large divisors
    Vec_Wec_t *     vSingles;   // cube -> single-cube divisor IDs
    Vec_Wec_t *     vSingleLits;// literals used by each cached divisor list
    // temporary data to update the data-structure when a divisor is extracted
    Vec_Int_t *     vCubesS;    // single cubes for the given divisor
    Vec_Int_t *     vCubesD;    // cube pairs for the given divisor
    Vec_Int_t *     vCompls;    // complemented attribute of each cube pair
    Vec_Int_t *     vCubeFree;  // cube-free divisor
    Vec_Int_t *     vDiv;       // selected divisor
    Vec_Int_t *     vSCC;       // single cubes containment cubes
    Vec_Int_t *     vSingleNew; // replacement divisor list
    Vec_Int_t *     vSingleMap; // current literal -> old literal position
    // statistics
    abctime         timeStart;  // starting time
    int             nVars;      // original problem variables
    int             nLits;      // the number of SOP literals
    int             nDivs;      // the number of extracted divisors
    int             nCompls;    // the number of complements
    int             nPairsS;    // number of lit pairs
    int             nPairsD;    // number of cube pairs
    int             nDivsS;     // single cube divisors
    int             nDivMux[3]; // 0 = mux, 1 = compl mux, 2 = no mux
};

static inline int Fx2_ManGetFirstVarCube( Fx2_Man_t * p, Vec_Int_t * vCube ) { return Vec_IntEntry( p->vVarCube, Vec_IntEntry(vCube, 0) ); }

#define Fx2_ManForEachCubeVec( vVec, vCubes, vCube, i )           \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((vCube) = Vec_WecEntry(vCubes, Vec_IntEntry(vVec, i))); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Interns divisors in their original insertion order.]

  Description [Linear probing avoids chained lookups. The table is at
  most half full, and exact comparisons resolve every hash collision.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Fx2_Hash_t * Fx2_HashStart( int nEntries )
{
    Fx2_Hash_t * p = ABC_CALLOC( Fx2_Hash_t, 1 );
    int nBins = 16;
    while ( nBins < 2 * nEntries )
        nBins *= 2;
    p->vTable = Vec_IntStartFull( nBins );
    p->vData = Vec_IntAlloc( 4 * nEntries );
    p->vMap = Vec_IntAlloc( nEntries );
    return p;
}
static void Fx2_HashStop( Fx2_Hash_t * p )
{
    Vec_IntFree( p->vTable );
    Vec_IntFree( p->vData );
    Vec_IntFree( p->vMap );
    ABC_FREE( p );
}
static inline int Fx2_HashSize( Fx2_Hash_t * p )
{
    return Vec_IntSize( p->vMap );
}
static inline Vec_Int_t * Fx2_HashRead( Fx2_Hash_t * p, int i )
{
    int * pEntry = Vec_IntEntryP( p->vData, Vec_IntEntry(p->vMap, i) );
    p->vTemp.nSize = p->vTemp.nCap = pEntry[0];
    p->vTemp.pArray = pEntry + 1;
    return &p->vTemp;
}
static inline unsigned Fx2_HashKey( int * pLits, int nLits )
{
    unsigned Key = 2166136261u;
    int i;
    for ( i = 0; i < nLits; i++ )
        Key = (Key ^ (unsigned)pLits[i]) * 16777619u;
    Key ^= Key >> 16;
    Key *= 0x7feb352du;
    return Key ^ (Key >> 15);
}
static int Fx2_HashAdd( Fx2_Hash_t * p, Vec_Int_t * vLits )
{
    int i, iBin, iMask, iDiv, nLits = Vec_IntSize(vLits);
    int * pEntry, * pLits = Vec_IntArray(vLits);
    // Like ABC's vectors, this table uses signed-int indices. A table of
    // 2^30 bins is the largest power-of-two table representable by them.
    if ( Vec_IntSize(p->vMap) >= Vec_IntSize(p->vTable) / 2 )
    {
        if ( Vec_IntSize(p->vTable) > ABC_INT_MAX / 2 ||
             (size_t)Vec_IntSize(p->vTable) > (size_t)-1 / (2 * sizeof(int)) )
        {
            printf( "Cannot perform \"fx2\": the divisor hash exceeds the vector size limit.\n" );
            return -1;
        }
        Vec_IntFill( p->vTable, 2 * Vec_IntSize(p->vTable), -1 );
        iMask = Vec_IntSize(p->vTable) - 1;
        for ( i = 0; i < Vec_IntSize(p->vMap); i++ )
        {
            pEntry = Vec_IntEntryP( p->vData, Vec_IntEntry(p->vMap, i) );
            iBin = (int)(Fx2_HashKey(pEntry + 1, pEntry[0]) & (unsigned)iMask);
            while ( Vec_IntEntry(p->vTable, iBin) >= 0 )
                iBin = (iBin + 1) & iMask;
            Vec_IntWriteEntry( p->vTable, iBin, i );
        }
    }
    iMask = Vec_IntSize(p->vTable) - 1;
    iBin = (int)(Fx2_HashKey(pLits, nLits) & (unsigned)iMask);
    while ( (iDiv = Vec_IntEntry(p->vTable, iBin)) >= 0 )
    {
        pEntry = Vec_IntEntryP( p->vData, Vec_IntEntry(p->vMap, iDiv) );
        if ( pEntry[0] == nLits )
        {
            if ( nLits == 2 )
            {
                if ( pEntry[1] == pLits[0] && pEntry[2] == pLits[1] )
                    return iDiv;
            }
            else if ( nLits == 4 )
            {
                if ( pEntry[1] == pLits[0] && pEntry[2] == pLits[1] && pEntry[3] == pLits[2] && pEntry[4] == pLits[3] )
                    return iDiv;
            }
            else if ( !memcmp(pEntry + 1, pLits, sizeof(int) * (size_t)nLits) )
                return iDiv;
        }
        iBin = (iBin + 1) & iMask;
    }
    if ( nLits >= ABC_INT_MAX - Vec_IntSize(p->vData) ||
         (word)Vec_IntSize(p->vData) + 1 + nLits > (word)((size_t)-1 / sizeof(int)) )
    {
        printf( "Cannot perform \"fx2\": divisor storage exceeds the vector size limit.\n" );
        return -1;
    }
    iDiv = Vec_IntSize(p->vMap);
    Vec_IntWriteEntry( p->vTable, iBin, iDiv );
    Vec_IntPush( p->vMap, Vec_IntSize(p->vData) );
    Vec_IntPush( p->vData, nLits );
    Vec_IntAppend( p->vData, vLits );
    return iDiv;
}

/**Function*************************************************************

  Synopsis    [Retrieves SOP information for fast_extract.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Abc_NtkFx2Retrieve( Abc_Ntk_t * pNtk )
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
//        if ( nVars < 2 ) continue;
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

  Synopsis    [Inserts SOP information after fast_extract.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFx2Insert( Abc_Ntk_t * pNtk, Vec_Wec_t * vCubes )
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
    // quit if nothing changes
    if ( iNodeMax < Abc_NtkObjNumMax(pNtk) )
    {
        //printf( "The network is unchanged by fast extract.\n" );
        return;
    }
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
//        if ( Vec_IntEntry(vCount, i) == 0 ) continue;
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
        // complement SOP if the original one was complemented
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
int Abc_NtkFx2Check( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i;
//    Abc_NtkForEachObj( pNtk, pNode, i )
//        Abc_ObjPrint( stdout, pNode );
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( !Vec_IntCheckUniqueSmall( &pNode->vFanins ) ) {
            printf( "Fanins of node %d: ", i );
            Vec_IntPrint( &pNode->vFanins );
            return 0;
        }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkFx2Perform( Abc_Ntk_t * pNtk, int nNewNodesMax, int LitCountMax, int fCanonDivs, int fVerbose, int fVeryVerbose )
{
    extern int Fx2_FastExtract( Vec_Wec_t * vCubes, int ObjIdMax, int nNewNodesMax, int LitCountMax, int fCanonDivs, int fVerbose, int fVeryVerbose );
    Vec_Wec_t * vCubes;
    int RetValue;
    assert( Abc_NtkIsSopLogic(pNtk) );
    // check unique fanins
    if ( !Abc_NtkFx2Check(pNtk) )
    {
        printf( "Abc_NtkFx2Perform: Nodes have duplicated fanins. FX2 is not performed.\n" );
        return 0;
    }
    // collect information about the covers
    vCubes = Abc_NtkFx2Retrieve( pNtk );
    // call the fast extract procedure
    RetValue = Fx2_FastExtract( vCubes, Abc_NtkObjNumMax(pNtk), nNewNodesMax, LitCountMax, fCanonDivs, fVerbose, fVeryVerbose );
    if ( RetValue > 0 )
    {
        // update the network
        Abc_NtkFx2Insert( pNtk, vCubes );
        Vec_WecFree( vCubes );
        if ( !Abc_NtkCheck( pNtk ) )
            printf( "Abc_NtkFx2Perform: The network check has failed.\n" );
        return 1;
    }
    else if ( RetValue == 0 )
        printf( "Warning: The network has not been changed by \"fx2\".\n" );
    Vec_WecFree( vCubes );
    return RetValue;
}



/**Function*************************************************************

  Synopsis    [Starting the manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Fx2_Man_t * Fx2_ManStart( Vec_Wec_t * vCubes )
{
    Fx2_Man_t * p;
    p = ABC_CALLOC( Fx2_Man_t, 1 );
    p->vCubes   = vCubes;
    // temporary data
    p->vCubesS   = Vec_IntAlloc( 100 );
    p->vCubesD   = Vec_IntAlloc( 100 );
    p->vCompls   = Vec_IntAlloc( 100 );
    p->vCubeFree = Vec_IntAlloc( 100 );
    p->vDiv      = Vec_IntAlloc( 100 );
    p->vSCC      = Vec_IntAlloc( 100 );
    p->vCandidates = Vec_IntAlloc( 1000 );
    p->vSigns    = Vec_WrdAlloc( Vec_WecSize(vCubes) );
    p->vSingles  = Vec_WecStart( Vec_WecSize(vCubes) );
    p->vSingleLits = Vec_WecStart( Vec_WecSize(vCubes) );
    p->vSingleNew = Vec_IntAlloc( 100 );
    p->vSingleMap = Vec_IntAlloc( 100 );
    return p;
}
void Fx2_ManStop( Fx2_Man_t * p )
{
    // The caller owns p->vCubes.
    Vec_WecFree( p->vLits );
    Fx2_HashStop( p->pHash );
    Vec_FltFree( p->vWeights );
    if ( p->vPrio )
        Vec_QueFree( p->vPrio );
    Vec_IntFree( p->vVarCube );
    Vec_IntFree( p->vVarStop );
    Vec_IntFree( p->vCandidates );
    Vec_IntFree( p->vLevels );
    Vec_WrdFree( p->vSigns );
    Vec_WecFree( p->vSingles );
    Vec_WecFree( p->vSingleLits );
    Vec_IntFree( p->vSingleNew );
    Vec_IntFree( p->vSingleMap );
    // temporary data
    Vec_IntFree( p->vCubesS );
    Vec_IntFree( p->vCubesD );
    Vec_IntFree( p->vCompls );
    Vec_IntFree( p->vCubeFree );
    Vec_IntFree( p->vDiv );
    Vec_IntFree( p->vSCC );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Compute levels of the nodes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Fx2_ManComputeLevelDiv( Fx2_Man_t * p, Vec_Int_t * vCubeFree )
{
    int i, Lit, Level = 0;
    Vec_IntForEachEntry( vCubeFree, Lit, i )
        Level = Abc_MaxInt( Level, Vec_IntEntry(p->vLevels, Abc_Lit2Var(Abc_Lit2Var(Lit))) );
    return Abc_MinInt( Level, 800 );
}
static inline int Fx2_ManComputeLevelCube( Fx2_Man_t * p, Vec_Int_t * vCube )
{
    int k, Lit, Level = 0;
    Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
        Level = Abc_MaxInt( Level, Vec_IntEntry(p->vLevels, Abc_Lit2Var(Lit)) );
    return Level;
}
void Fx2_ManComputeLevel( Fx2_Man_t * p )
{
    Vec_Int_t * vCube;
    int i, iVar, iFirst = 0;
    iVar = Vec_IntEntry( Vec_WecEntry(p->vCubes,0), 0 );
    p->vLevels = Vec_IntStart( p->nVars );
    Vec_WecForEachLevel( p->vCubes, vCube, i )
    {
        if ( iVar != Vec_IntEntry(vCube, 0) )
        {
            // add the number of cubes
            Vec_IntAddToEntry( p->vLevels, iVar, i - iFirst );
            iVar = Vec_IntEntry(vCube, 0);
            iFirst = i;
        }
        Vec_IntUpdateEntry( p->vLevels, iVar, Fx2_ManComputeLevelCube(p, vCube) );
    }
}

/**Function*************************************************************

  Synopsis    [Printing procedures.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fx2_PrintDivArray( Vec_Int_t * vDiv )
{
    int i, Lit;
    Vec_IntForEachEntry( vDiv, Lit, i )
        if ( !Abc_LitIsCompl(Lit) )
            printf( "%d(1)", Abc_Lit2Var(Lit) );
    printf( " + " );
    Vec_IntForEachEntry( vDiv, Lit, i )
        if ( Abc_LitIsCompl(Lit) )
            printf( "%d(2)", Abc_Lit2Var(Lit) );
}
static inline void Fx2_PrintDiv( Fx2_Man_t * p, int iDiv )
{
    int i;
    printf( "%4d : ", p->nDivs );
    printf( "Div %7d : ", iDiv );
    printf( "Weight %12.5f  ", Vec_FltEntry(p->vWeights, iDiv) );
    Fx2_PrintDivArray( Fx2_HashRead(p->pHash, iDiv) );
    for ( i = Vec_IntSize(Fx2_HashRead(p->pHash, iDiv)) + 3; i < 16; i++ )
        printf( " " );
    printf( "Lits =%7d  ", p->nLits );
    printf( "Divs =%8d  ", Fx2_HashSize(p->pHash) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->timeStart );
}
static void Fx2_PrintDivisors( Fx2_Man_t * p )
{
    int iDiv;
    for ( iDiv = 0; iDiv < Vec_FltSize(p->vWeights); iDiv++ )
        Fx2_PrintDiv( p, iDiv );
}
static void Fx2_PrintStats( Fx2_Man_t * p, abctime clk )
{
    printf( "Cubes =%8d  ", Vec_WecSizeUsed(p->vCubes) );
    printf( "Lits  =%8d  ", Vec_WecSizeUsed(p->vLits) );
    printf( "Divs  =%8d  ", Fx2_HashSize(p->pHash) );
    printf( "Divs+ =%8d  ", Vec_QueSize(p->vPrio) );
    printf( "Compl =%8d  ", p->nDivMux[1] );
    printf( "Extr  =%7d  ", p->nDivs );
    Abc_PrintTime( 1, "Time", clk );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the divisor should be complemented.]

  Description [Normalizes the divisor by putting, first, positive control
  literal first and, second, positive data1 literal. As the result,
  a MUX divisor is (ab + !ac) and an XOR divisor is (ab + !a!b).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fx2_ManDivNormalize( Vec_Int_t * vCubeFree ) // return 1 if complemented
{
    int * L = Vec_IntArray(vCubeFree);
    int RetValue = 0, LitA0 = -1, LitB0 = -1, LitA1 = -1, LitB1 = -1;
    assert( Vec_IntSize(vCubeFree) == 4 );
    if ( Abc_LitIsCompl(L[0]) != Abc_LitIsCompl(L[1]) && (L[0] >> 2) == (L[1] >> 2) ) // diff cubes, same vars
    {
        if ( Abc_LitIsCompl(L[2]) == Abc_LitIsCompl(L[3]) )
            return -1;
        LitA0 = Abc_Lit2Var(L[0]), LitB0 = Abc_Lit2Var(L[1]);
        if ( Abc_LitIsCompl(L[0]) == Abc_LitIsCompl(L[2]) )
        {
            assert( Abc_LitIsCompl(L[1]) == Abc_LitIsCompl(L[3]) );
            LitA1 = Abc_Lit2Var(L[2]), LitB1 = Abc_Lit2Var(L[3]);
        }
        else
        {
            assert( Abc_LitIsCompl(L[0]) == Abc_LitIsCompl(L[3]) );
            assert( Abc_LitIsCompl(L[1]) == Abc_LitIsCompl(L[2]) );
            LitA1 = Abc_Lit2Var(L[3]), LitB1 = Abc_Lit2Var(L[2]);
        }
    }
    else if ( Abc_LitIsCompl(L[1]) != Abc_LitIsCompl(L[2]) && (L[1] >> 2) == (L[2] >> 2) )
    {
        if ( Abc_LitIsCompl(L[0]) == Abc_LitIsCompl(L[3]) )
            return -1;
        LitA0 = Abc_Lit2Var(L[1]), LitB0 = Abc_Lit2Var(L[2]);
        if ( Abc_LitIsCompl(L[1]) == Abc_LitIsCompl(L[0]) )
            LitA1 = Abc_Lit2Var(L[0]), LitB1 = Abc_Lit2Var(L[3]);
        else
            LitA1 = Abc_Lit2Var(L[3]), LitB1 = Abc_Lit2Var(L[0]);
    }
    else if ( Abc_LitIsCompl(L[2]) != Abc_LitIsCompl(L[3]) && (L[2] >> 2) == (L[3] >> 2) )
    {
        if ( Abc_LitIsCompl(L[0]) == Abc_LitIsCompl(L[1]) )
            return -1;
        LitA0 = Abc_Lit2Var(L[2]), LitB0 = Abc_Lit2Var(L[3]);
        if ( Abc_LitIsCompl(L[2]) == Abc_LitIsCompl(L[0]) )
            LitA1 = Abc_Lit2Var(L[0]), LitB1 = Abc_Lit2Var(L[1]);
        else
            LitA1 = Abc_Lit2Var(L[1]), LitB1 = Abc_Lit2Var(L[0]);
    }
    else
        return -1;
    assert( LitA0 == Abc_LitNot(LitB0) );
    if ( Abc_LitIsCompl(LitA0) )
    {
        ABC_SWAP( int, LitA0, LitB0 );
        ABC_SWAP( int, LitA1, LitB1 );
    }
    assert( !Abc_LitIsCompl(LitA0) );
    if ( Abc_LitIsCompl(LitA1) )
    {
        LitA1 = Abc_LitNot(LitA1);
        LitB1 = Abc_LitNot(LitB1);
        RetValue = 1;
    }
    assert( !Abc_LitIsCompl(LitA1) );
    // arrange literals in such as a way that
    // - the first two literals are control literals from different cubes
    // - the third literal is non-complented data input
    // - the forth literal is possibly complemented data input
    L[0] = Abc_Var2Lit( LitA0, 0 );
    L[1] = Abc_Var2Lit( LitB0, 1 );
    L[2] = Abc_Var2Lit( LitA1, 0 );
    L[3] = Abc_Var2Lit( LitB1, 1 );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Find a cube-free divisor of the two cubes.]

  Description [Returns the common literal count, or -1 for containment,
  -2 for a divisor exceeding the limit, -3 for duplicate cubes, and -4
  for unsupported containment by two or more literals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fx2_ManDivFindCubeFree( Vec_Int_t * vArr1, Vec_Int_t * vArr2, Vec_Int_t * vCubeFree, int nLimit )
{
    int * pBeg1 = Vec_IntArray( vArr1 ) + 1;  // skip variable ID
    int * pBeg2 = Vec_IntArray( vArr2 ) + 1;  // skip variable ID
    int * pEnd1 = Vec_IntLimit( vArr1 );
    int * pEnd2 = Vec_IntLimit( vArr2 );
    int Counter = 0, fAttr0 = 0, fAttr1 = 1;
    Vec_IntClear( vCubeFree );
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        if ( *pBeg1 == *pBeg2 )
            pBeg1++, pBeg2++, Counter++;
        else if ( *pBeg1 < *pBeg2 )
            Vec_IntPush( vCubeFree, Abc_Var2Lit(*pBeg1++, fAttr0) );
        else
        {
            if ( Vec_IntSize(vCubeFree) == 0 )
                fAttr0 = 1, fAttr1 = 0;
            Vec_IntPush( vCubeFree, Abc_Var2Lit(*pBeg2++, fAttr1) );
        }
        if ( nLimit && Vec_IntSize(vCubeFree) > nLimit )
            return -2;
    }
    if ( nLimit && Vec_IntSize(vCubeFree) + (pEnd1 - pBeg1) + (pEnd2 - pBeg2) > nLimit )
        return -2;
    while ( pBeg1 < pEnd1 )
        Vec_IntPush( vCubeFree, Abc_Var2Lit(*pBeg1++, fAttr0) );
    while ( pBeg2 < pEnd2 )
        Vec_IntPush( vCubeFree, Abc_Var2Lit(*pBeg2++, fAttr1) );
    if ( Vec_IntSize(vCubeFree) == 0 )
        return -3;
    else if ( Vec_IntSize(vCubeFree) == 1 )
        return -1;
    else if ( Counter == Vec_IntSize(vArr1) - 1 || Counter == Vec_IntSize(vArr2) - 1 )
        return -4;
    else if ( Vec_IntSize( vCubeFree ) == 3 )
    {
        int * pArray = Vec_IntArray( vCubeFree );

        if ( Abc_Lit2Var( pArray[0] ) == Abc_LitNot( Abc_Lit2Var( pArray[1] ) ) )
        {
            if ( Abc_LitIsCompl( pArray[0] ) == Abc_LitIsCompl( pArray[2] ) )
                Vec_IntDrop( vCubeFree, 0 );
            else
                Vec_IntDrop( vCubeFree, 1 );
        }
        else if ( Abc_Lit2Var( pArray[1] ) == Abc_LitNot( Abc_Lit2Var( pArray[2] ) ) )
        {
            if ( Abc_LitIsCompl( pArray[1] ) == Abc_LitIsCompl( pArray[0] ) )
                Vec_IntDrop( vCubeFree, 1 );
            else
                Vec_IntDrop( vCubeFree, 2 );
        }

        if ( Vec_IntSize( vCubeFree ) == 2 )
        {
            int Lit0 = Abc_Lit2Var( pArray[0] ),
                Lit1 = Abc_Lit2Var( pArray[1] );

            if ( Lit0 > Lit1 )
                ABC_SWAP( int, Lit0, Lit1 );

            Vec_IntWriteEntry( vCubeFree, 0, Abc_Var2Lit( Lit0, 0 ) );
            Vec_IntWriteEntry( vCubeFree, 1, Abc_Var2Lit( Lit1, 1 ) );
        }
    }
    assert( !Abc_LitIsCompl(Vec_IntEntry(vCubeFree, 0)) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Procedures operating on a two-cube divisor.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fx2_ManDivFindPivots( Vec_Int_t * vDiv, int * pLit0, int * pLit1 )
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
static inline int Fx2_ManDivRemoveLits( Vec_Int_t * vCube, Vec_Int_t * vDiv, int fCompl )
{
    int i, Lit, Count = 0;
    assert( !fCompl || Vec_IntSize(vDiv) == 4 );
    Vec_IntForEachEntry( vDiv, Lit, i )
    {
        Count += Vec_IntRemove1( vCube, Abc_Lit2Var(Lit) ^ (fCompl && i > 1) );  // the last two lits can be complemented
        if ( Vec_IntSize( vDiv ) == 2 )
            Count += Vec_IntRemove1( vCube, Abc_LitNot( Abc_Lit2Var(Lit) ) );
    }
    return Count;
}
static inline void Fx2_ManDivAddLits( Vec_Int_t * vCube, Vec_Int_t * vCube2, Vec_Int_t * vDiv )
{
    int i, Lit, * pArray;
//    Vec_IntClear( vCube );
//    Vec_IntClear( vCube2 );
    Vec_IntForEachEntry( vDiv, Lit, i )
        if ( Abc_LitIsCompl(Lit) )
            Vec_IntPush( vCube2, Abc_Lit2Var(Lit) );
        else
            Vec_IntPush( vCube, Abc_Lit2Var(Lit) );
    if ( Vec_IntSize(vDiv) == 4 && Vec_IntSize(vCube) == 3 )
    {
        assert( Vec_IntSize(vCube2) == 3 );
        pArray = Vec_IntArray(vCube);
        if ( pArray[1] > pArray[2] )
            ABC_SWAP( int, pArray[1], pArray[2] );
        pArray = Vec_IntArray(vCube2);
        if ( pArray[1] > pArray[2] )
            ABC_SWAP( int, pArray[1], pArray[2] );
    }
}

/**Function*************************************************************

  Synopsis    [Setting up the data-structure.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fx2_ManCreateLiterals( Fx2_Man_t * p, int nVars )
{
    Vec_Int_t * vCube, * vCounts;
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
    assert( p->nVars < nVars );
    p->nVars = nVars;
    // count literals
    vCounts = Vec_IntStart( 2*p->nVars );
    Vec_WecForEachLevel( p->vCubes, vCube, i )
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            Vec_IntAddToEntry( vCounts, Lit, 1 );
    // start literals
    p->vLits = Vec_WecStart( 2*p->nVars );
    Vec_IntForEachEntry( vCounts, Count, Lit )
        Vec_IntGrow( Vec_WecEntry(p->vLits, Lit), Count );
    Vec_IntFree( vCounts );
    // fill out literals
    Vec_WecForEachLevel( p->vCubes, vCube, i )
        Vec_IntForEachEntryStart( vCube, Lit, k, 1 )
            Vec_WecPush( p->vLits, Lit, i );
    // create mapping of variable into the first cube
    p->vVarCube = Vec_IntStartFull( p->nVars );
    p->vVarStop = Vec_IntStart( p->nVars );
    Vec_WecForEachLevel( p->vCubes, vCube, i )
    {
        if ( Vec_IntEntry(p->vVarCube, Vec_IntEntry(vCube, 0)) == -1 )
            Vec_IntWriteEntry( p->vVarCube, Vec_IntEntry(vCube, 0), i );
        Vec_IntWriteEntry( p->vVarStop, Vec_IntEntry(vCube, 0), i + 1 );
    }
}
/**Function*************************************************************

  Synopsis    [Rejects cube pairs whose difference exceeds the limit.]

  Description [Each literal sets one signature bit. Differing bits give
  a lower bound on the number of differing literals, even with collisions.
  Three differing literals must still be checked because normalization
  can reduce them to two. Larger differences cannot shrink.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Fx2_ManCubeSign( Vec_Int_t * vCube )
{
    word Sign = 0;
    int i, Lit;
    Vec_IntForEachEntryStart( vCube, Lit, i, 1 )
        Sign |= (word)1 << (Lit & 63);
    return Sign;
}
static inline int Fx2_ManPairReject( word Sign0, word Sign1, int nLimit )
{
    word Diff = Sign0 ^ Sign1;
    int i;
    if ( !nLimit )
        return 0;
    if ( nLimit == 4 )
    {
        Diff &= Diff - 1;
        Diff &= Diff - 1;
        Diff &= Diff - 1;
        Diff &= Diff - 1;
        return Diff != 0;
    }
    for ( i = 0; i < nLimit && Diff; i++ )
        Diff &= Diff - 1;
    return Diff != 0;
}

/**Function*************************************************************

  Synopsis    [Filters signatures before accessing the cube vectors.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Fx2_ManCandidates( Fx2_Man_t * p, int iFirst, int iStop, word Sign, int nLimit )
{
    word * pSigns = Vec_WrdArray( p->vSigns );
    int i, nSize = 0, * pArray;
    assert( iFirst >= 0 && iFirst <= iStop && iStop <= Vec_WrdSize(p->vSigns) );
    Vec_IntGrow( p->vCandidates, iStop - iFirst );
    pArray = Vec_IntArray( p->vCandidates );
    if ( nLimit == 4 )
    {
        for ( i = iFirst; i < iStop; i++ )
            if ( !Fx2_ManPairReject(Sign, pSigns[i], 4) )
                pArray[nSize++] = i;
    }
    else
        for ( i = iFirst; i < iStop; i++ )
            if ( !Fx2_ManPairReject(Sign, pSigns[i], nLimit) )
                pArray[nSize++] = i;
    p->vCandidates->nSize = nSize;
}

/**Function*************************************************************

  Synopsis    [Counts cached literal pairs using wide intermediate arithmetic.]

  Description [Returns -1 if ABC's signed vector size or the allocation's
  byte count cannot represent the cache.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Fx2_ManPairCount( int nLits )
{
    word nPairs = nLits < 2 ? 0 : (word)nLits * (word)(nLits - 1) / 2;
    return nPairs > ABC_INT_MAX || nPairs > (word)((size_t)-1 / sizeof(int)) ? -1 : (int)nPairs;
}

/**Function*************************************************************

  Synopsis    [Updates single-cube divisors using cached pair IDs.]

  Description [Unchanged literal pairs keep their original divisor IDs.
  Weight updates and queue operations retain the original order.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fx2_ManCubeSingleCubeDivisors( Fx2_Man_t * p, Vec_Int_t * vPivot, int fRemove, int fUpdate )
{
    Vec_Int_t * vIds, * vOld;
    int k, n, Lit, Lit2, iDiv, a, b, iOld = 0;
    int iCube;
    int nLits = Vec_IntSize(vPivot) - 1, nNew = 0;
    int nPairs = Fx2_ManPairCount( nLits );
    int * pIds, * pNew, * pMap;
    float * pWeights;
    if ( nLits < 1 || p->fInvalid )
        return 0;
    // Check every call, including divisor cubes created during extraction.
    if ( nPairs < 0 )
    {
        printf( "Cannot perform \"fx2\": a cube's pair cache exceeds the vector size limit.\n" );
        p->fInvalid = 1;
        return 0;
    }
    iCube = Vec_WecLevelId( p->vCubes, vPivot );
    while ( Vec_WecSize(p->vSingles) <= iCube )
    {
        Vec_WecPushLevel( p->vSingles );
        Vec_WecPushLevel( p->vSingleLits );
    }
    vIds = Vec_WecEntry( p->vSingles, iCube );
    vOld = Vec_WecEntry( p->vSingleLits, iCube );
    if ( fRemove && Vec_IntSize(vIds) == nPairs )
    {
        assert( Vec_IntSize(vOld) == nLits );
        assert( !memcmp(Vec_IntArray(vOld), Vec_IntArray(vPivot) + 1, sizeof(int) * (size_t)nLits) );
        pWeights = Vec_FltArray( p->vWeights );
        pIds = Vec_IntArray( vIds );
        for ( k = 0; k < Vec_IntSize(vIds); k++ )
        {
            iDiv = pIds[k];
            pWeights[iDiv] -= 1;
            p->nPairsS--;
            if ( fUpdate && Vec_QueIsMember(p->vPrio, iDiv) )
                Vec_QueMoveDown( p->vPrio, iDiv );
        }
        return nPairs;
    }
    // Map the surviving literals back into the previous pair list.
    Vec_IntClear( p->vSingleMap );
    Vec_IntPush( p->vSingleMap, -1 );
    Vec_IntForEachEntryStart( vPivot, Lit, k, 1 )
    {
        while ( iOld < Vec_IntSize(vOld) && Vec_IntEntry(vOld, iOld) < Lit )
            iOld++;
        Vec_IntPush( p->vSingleMap, iOld < Vec_IntSize(vOld) && Vec_IntEntry(vOld, iOld) == Lit ? iOld : -1 );
    }
    Vec_IntGrow( p->vSingleNew, nPairs );
    pIds = Vec_IntArray( vIds );
    pNew = Vec_IntArray( p->vSingleNew );
    pMap = Vec_IntArray( p->vSingleMap );
    Vec_IntForEachEntryStart( vPivot, Lit, k, 1 )
    Vec_IntForEachEntryStart( vPivot, Lit2, n, k+1 )
    {
        assert( Lit < Lit2 );
        a = pMap[k];
        b = pMap[n];
        if ( a >= 0 && b >= 0 )
        {
            iDiv = pIds[(int)((word)a * (2 * (word)Vec_IntSize(vOld) - a - 1) / 2 + b - a - 1)];
            if ( !fRemove )
            {
                pNew[nNew++] = iDiv;
                p->vWeights->pArray[iDiv] += 1;
                p->nPairsS++;
                if ( fUpdate )
                {
                    if ( Vec_QueIsMember(p->vPrio, iDiv) )
                        Vec_QueMoveUp( p->vPrio, iDiv );
                    else
                        Vec_QuePush( p->vPrio, iDiv );
                }
                continue;
            }
        }
        else
        {
            Vec_IntClear( p->vCubeFree );
            Vec_IntPush( p->vCubeFree, Abc_Var2Lit(Abc_LitNot(Lit), 0) );
            Vec_IntPush( p->vCubeFree, Abc_Var2Lit(Abc_LitNot(Lit2), 1) );
            iDiv = Fx2_HashAdd( p->pHash, p->vCubeFree );
            if ( iDiv < 0 )
            {
                p->fInvalid = 1;
                return 0;
            }
        }
        if ( !fRemove )
        {
            pNew[nNew++] = iDiv;
            if ( Vec_FltSize(p->vWeights) == iDiv )
            {
                Vec_FltPush(p->vWeights, -2 + 0.9 - 0.001 * Fx2_ManComputeLevelDiv(p, p->vCubeFree));
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
            {
                if ( fRemove )
                    Vec_QueMoveDown( p->vPrio, iDiv );
                else
                    Vec_QueMoveUp( p->vPrio, iDiv );
            }
            else if ( !fRemove )
                Vec_QuePush( p->vPrio, iDiv );
        }
    }
    if ( !fRemove )
    {
        p->vSingleNew->nSize = nNew;
        ABC_SWAP( Vec_Int_t, *vIds, *p->vSingleNew );
        Vec_IntClear( vOld );
        Vec_IntForEachEntryStart( vPivot, Lit, k, 1 )
            Vec_IntPush( vOld, Lit );
    }
    return nPairs;
}
void Fx2_ManCubeDoubleCubeDivisors( Fx2_Man_t * p, int iFirst, Vec_Int_t * vPivot, int fRemove, int fUpdate )
{
    Vec_Int_t * vCube;
    int i, k, iDiv, Base;
    int nLimit = p->LitCountMax ? Abc_MaxInt(p->LitCountMax, 3) : 0;
    word Sign = Vec_WrdEntry( p->vSigns, Vec_WecLevelId(p->vCubes, vPivot) );
    if ( p->fInvalid )
        return;
    Fx2_ManCandidates( p, iFirst, Vec_IntEntry(p->vVarStop, Vec_IntEntry(vPivot, 0)), Sign, nLimit );
    Vec_IntForEachEntry( p->vCandidates, i, k )
    {
        vCube = Vec_WecEntry( p->vCubes, i );
        if ( Vec_IntSize(vCube) == 0 || vCube == vPivot )
            continue;
        if ( Vec_WecIntHasMark(vCube) && Vec_WecIntHasMark(vPivot) && vCube > vPivot )
            continue;
        assert( Vec_IntEntry(vCube, 0) == Vec_IntEntry(vPivot, 0) );
        if ( nLimit && abs(Vec_IntSize(vCube) - Vec_IntSize(vPivot)) > nLimit )
            continue;
        Base = Fx2_ManDivFindCubeFree( vCube, vPivot, p->vCubeFree, nLimit );
        if ( Base == -3 || Base == -4 )
        {
            printf( "Cannot perform \"fx2\": the cover %s.\n",
                Base == -3 ? "contains duplicate cubes" : "has a nontrivial cube containment" );
            p->fInvalid = 1;
            return;
        }
        if ( Base == -2 )
            continue;
        if ( Base == -1 )
        {
            if ( fRemove == 0 )
            {
                if ( Vec_IntSize( vCube ) > Vec_IntSize( vPivot ) )
                    Vec_IntPush( p->vSCC, Vec_WecLevelId( p->vCubes, vCube ) );
                else
                    Vec_IntPush( p->vSCC, Vec_WecLevelId( p->vCubes, vPivot ) );
            }
            continue;
        }
        if ( Vec_IntSize(p->vCubeFree) == 4 )
        {
            int Value = Fx2_ManDivNormalize( p->vCubeFree );
            if ( Value == 0 )
                p->nDivMux[0]++;
            else if ( Value == 1 )
                p->nDivMux[1]++;
            else
                p->nDivMux[2]++;
            if ( p->fCanonDivs && Value < 0 )
                continue;
        }
        if ( p->LitCountMax && p->LitCountMax < Vec_IntSize(p->vCubeFree) )
            continue;
        if ( p->fCanonDivs && Vec_IntSize(p->vCubeFree) == 3 )
            continue;
        iDiv = Fx2_HashAdd( p->pHash, p->vCubeFree );
        if ( iDiv < 0 )
        {
            p->fInvalid = 1;
            return;
        }
        if ( !fRemove )
        {
            if ( iDiv == Vec_FltSize(p->vWeights) )
                Vec_FltPush(p->vWeights, -Vec_IntSize(p->vCubeFree) + 0.9 - 0.0009 * Fx2_ManComputeLevelDiv(p, p->vCubeFree));
            assert( iDiv < Vec_FltSize(p->vWeights) );
            Vec_FltAddToEntry( p->vWeights, iDiv, Base + Vec_IntSize(p->vCubeFree) - 1 );
            p->nPairsD++;
        }
        else
        {
            assert( iDiv < Vec_FltSize(p->vWeights) );
            Vec_FltAddToEntry( p->vWeights, iDiv, -(Base + Vec_IntSize(p->vCubeFree) - 1) );
            p->nPairsD--;
        }
        if ( fUpdate )
        {
            if ( Vec_QueIsMember(p->vPrio, iDiv) )
            {
                if ( fRemove )
                    Vec_QueMoveDown( p->vPrio, iDiv );
                else
                    Vec_QueMoveUp( p->vPrio, iDiv );
            }
            else if ( !fRemove )
                Vec_QuePush( p->vPrio, iDiv );
        }
    }
}
void Fx2_ManCreateDivisors( Fx2_Man_t * p )
{
    Vec_Int_t * vCube;
    float Weight;
    int i;
    // alloc hash table
    assert( p->pHash == NULL );
    p->pHash = Fx2_HashStart( 1000 );
    p->vWeights = Vec_FltAlloc( 1000 );
    Vec_WecForEachLevel( p->vCubes, vCube, i )
        Vec_WrdPush( p->vSigns, Fx2_ManCubeSign(vCube) );
    // create single-cube two-literal divisors
    Vec_WecForEachLevel( p->vCubes, vCube, i )
    {
        Fx2_ManCubeSingleCubeDivisors( p, vCube, 0, 0 ); // add - no update
        if ( p->fInvalid )
            return;
    }
    assert( p->nDivsS == Vec_FltSize(p->vWeights) );
    // create two-cube divisors
    Vec_WecForEachLevel( p->vCubes, vCube, i )
    {
        Fx2_ManCubeDoubleCubeDivisors( p, i+1, vCube, 0, 0 ); // add - no update
        if ( p->fInvalid )
            return;
    }
    // create queue with all divisors
    p->vPrio = Vec_QueAlloc( Vec_FltSize(p->vWeights) );
    Vec_QueSetPriority( p->vPrio, Vec_FltArrayP(p->vWeights) );
    Vec_FltForEachEntry( p->vWeights, Weight, i )
        if ( Weight > 0.0 )
            Vec_QuePush( p->vPrio, i );
}


/**Function*************************************************************

  Synopsis    [Compress the cubes by removing unused ones.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fx2_ManCompressCubes( Vec_Wec_t * vCubes, Vec_Int_t * vLit2Cube )
{
    int i, CubeId, k = 0;
    Vec_IntForEachEntry( vLit2Cube, CubeId, i )
        if ( Vec_IntSize(Vec_WecEntry(vCubes, CubeId)) > 0 )
            Vec_IntWriteEntry( vLit2Cube, k++, CubeId );
    Vec_IntShrink( vLit2Cube, k );
}


/**Function*************************************************************

  Synopsis    [Find common cube pairs.]

  Description [Returns zero if two occurrences share a cube. Temporary
  marks are restored before returning on either path.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Fx2_ManGetCubeVar( Vec_Wec_t * vCubes, int iCube )  { return Vec_IntEntry( Vec_WecEntry(vCubes, iCube), 0 );      }
int Fx2_ManFindCommonPairs( Vec_Wec_t * vCubes, Vec_Wrd_t * vSigns, Vec_Int_t * vPart0, Vec_Int_t * vPart1, Vec_Int_t * vPairs, Vec_Int_t * vCompls, Vec_Int_t * vDiv, Vec_Int_t * vCubeFree )
{
    int * pBeg1 = vPart0->pArray;
    int * pBeg2 = vPart1->pArray;
    int * pEnd1 = vPart0->pArray + vPart0->nSize;
    int * pEnd2 = vPart1->pArray + vPart1->nSize;
    int i, k, i_, k_, fCompl, CubeId1, CubeId2, iCube;
    Vec_Int_t * vCube;
    int nLimit = Abc_MaxInt( Vec_IntSize(vDiv), 3 );
    Vec_IntClear( vPairs );
    Vec_IntClear( vCompls );
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        CubeId1 = Fx2_ManGetCubeVar(vCubes, *pBeg1);
        CubeId2 = Fx2_ManGetCubeVar(vCubes, *pBeg2);
        if ( CubeId1 == CubeId2 )
        {
            for ( i = 1; pBeg1+i < pEnd1; i++ )
                if ( CubeId1 != Fx2_ManGetCubeVar(vCubes, pBeg1[i]) )
                    break;
            for ( k = 1; pBeg2+k < pEnd2; k++ )
                if ( CubeId1 != Fx2_ManGetCubeVar(vCubes, pBeg2[k]) )
                    break;
            for ( i_ = 0; i_ < i; i_++ )
            for ( k_ = 0; k_ < k; k_++ )
            {
                if ( pBeg1[i_] == pBeg2[k_] )
                    continue;
                if ( Fx2_ManPairReject(Vec_WrdEntry(vSigns, pBeg1[i_]), Vec_WrdEntry(vSigns, pBeg2[k_]), nLimit) )
                    continue;
                if ( Fx2_ManDivFindCubeFree(Vec_WecEntry(vCubes, pBeg1[i_]), Vec_WecEntry(vCubes, pBeg2[k_]), vCubeFree, nLimit) < 0 )
                    continue;
                fCompl = (Vec_IntSize(vCubeFree) == 4 && Fx2_ManDivNormalize(vCubeFree) == 1);
                if ( !Vec_IntEqual( vDiv, vCubeFree ) )
                    continue;
                Vec_IntPush( vPairs, pBeg1[i_] );
                Vec_IntPush( vPairs, pBeg2[k_] );
                Vec_IntPush( vCompls, fCompl );
            }
            pBeg1 += i;
            pBeg2 += k;
        }
        else if ( CubeId1 < CubeId2 )
            pBeg1++;
        else
            pBeg2++;
    }
    // Each occurrence must own two distinct cubes. Restore all temporary
    // marks even when an unsupported overlapping occurrence is detected.
    Vec_IntForEachEntry( vPairs, iCube, i )
    {
        vCube = Vec_WecEntry( vCubes, iCube );
        if ( Vec_WecIntHasMark(vCube) )
            break;
        Vec_WecIntSetMark( vCube );
    }
    k = i;
    while ( i-- > 0 )
        Vec_WecIntXorMark( Vec_WecEntry(vCubes, Vec_IntEntry(vPairs, i)) );
    return k == Vec_IntSize(vPairs);
}

/**Function*************************************************************

  Synopsis    [Updates the data-structure when one divisor is selected.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fx2_ManUpdate( Fx2_Man_t * p, int iDiv )
{
    Vec_Int_t * vCube, * vCube2, * vLitP = NULL, * vLitN = NULL;
    Vec_Int_t * vDiv = p->vDiv;
    int i, k, Lit0, Lit1, iVarNew = 0, RetValue, Level;
    float Diff = Vec_FltEntry(p->vWeights, iDiv) - (float)((int)Vec_FltEntry(p->vWeights, iDiv));
    (void)Diff;
    assert( Diff > 0.0 && Diff < 1.0 );

    // get the divisor and select pivot variables
    p->nDivs++;
    Vec_IntClear( vDiv );
    Vec_IntAppend( vDiv, Fx2_HashRead(p->pHash, iDiv) );
    Fx2_ManDivFindPivots( vDiv, &Lit0, &Lit1 );
    assert( Lit0 >= 0 && Lit1 >= 0 );


    // collect single-cube-divisor cubes
    Vec_IntClear( p->vCubesS );
    if ( Vec_IntSize(vDiv) == 2 )
    {
        Fx2_ManCompressCubes( p->vCubes, Vec_WecEntry(p->vLits, Abc_LitNot(Lit0)) );
        Fx2_ManCompressCubes( p->vCubes, Vec_WecEntry(p->vLits, Abc_LitNot(Lit1)) );
        Vec_IntTwoRemoveCommon( Vec_WecEntry(p->vLits, Abc_LitNot(Lit0)), Vec_WecEntry(p->vLits, Abc_LitNot(Lit1)), p->vCubesS );
    }

    // collect double-cube-divisor cube pairs
    Fx2_ManCompressCubes( p->vCubes, Vec_WecEntry(p->vLits, Lit0) );
    Fx2_ManCompressCubes( p->vCubes, Vec_WecEntry(p->vLits, Lit1) );
    if ( !Fx2_ManFindCommonPairs( p->vCubes, p->vSigns, Vec_WecEntry(p->vLits, Lit0), Vec_WecEntry(p->vLits, Lit1), p->vCubesD, p->vCompls, vDiv, p->vCubeFree ) )
    {
        printf( "Cannot perform \"fx2\": divisor occurrences overlap.\n" );
        p->fInvalid = 1;
        return;
    }

    // subtract cost of single-cube divisors
    Fx2_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
        Fx2_ManCubeSingleCubeDivisors( p, vCube, 1, 1 );  // remove - update
    Fx2_ManForEachCubeVec( p->vCubesD, p->vCubes, vCube, i )
        Fx2_ManCubeSingleCubeDivisors( p, vCube, 1, 1 );  // remove - update
    if ( p->fInvalid )
        return;

    // mark the cubes to be removed
    Vec_WecMarkLevels( p->vCubes, p->vCubesS );
    Vec_WecMarkLevels( p->vCubes, p->vCubesD );

    // subtract cost of double-cube divisors
    Fx2_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
        Fx2_ManCubeDoubleCubeDivisors( p, Fx2_ManGetFirstVarCube(p, vCube), vCube, 1, 1 );  // remove - update
    Fx2_ManForEachCubeVec( p->vCubesD, p->vCubes, vCube, i )
        Fx2_ManCubeDoubleCubeDivisors( p, Fx2_ManGetFirstVarCube(p, vCube), vCube, 1, 1 );  // remove - update

    // unmark the cubes to be removed
    Vec_WecUnmarkLevels( p->vCubes, p->vCubesS );
    Vec_WecUnmarkLevels( p->vCubes, p->vCubesD );
    if ( p->fInvalid )
        return;

    if ( Abc_Lit2Var(Lit0) == Abc_Lit2Var(Lit1) && Vec_IntSize(Fx2_HashRead(p->pHash, iDiv)) == 2 )
        goto ExtractFromPairs;

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
        Level = 1 + Fx2_ManComputeLevelCube( p, vCube );
    }
    else
    {
        vCube2 = Vec_WecPushLevel( p->vCubes );
        vCube = Vec_WecEntry( p->vCubes, Vec_WecSize(p->vCubes) - 2 );
        Vec_IntPush( vCube2, iVarNew );
        Fx2_ManDivAddLits( vCube, vCube2, vDiv );
        Level = 2 + Abc_MaxInt( Fx2_ManComputeLevelCube(p, vCube), Fx2_ManComputeLevelCube(p, vCube2) );
    }
    assert( Vec_IntSize(p->vLevels) == iVarNew );
    Vec_IntPush( p->vLevels, Level );
    Vec_IntPush( p->vVarStop, Vec_WecSize(p->vCubes) );
    // do not add new cubes to the matrix
    p->nLits += Vec_IntSize( vDiv );
    // create new literals
    vLitP = Vec_WecPushLevel( p->vLits );
    vLitN = Vec_WecPushLevel( p->vLits );
    vLitP = Vec_WecEntry( p->vLits, Vec_WecSize(p->vLits) - 2 );
    // create updated single-cube divisor cubes
    Fx2_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
    {
        RetValue  = Vec_IntRemove1( vCube, Abc_LitNot(Lit0) );
        RetValue += Vec_IntRemove1( vCube, Abc_LitNot(Lit1) );
        assert( RetValue == 2 );
        Vec_IntPush( vCube, Abc_Var2Lit(iVarNew, 0) );
        Vec_IntPush( vLitP, Vec_WecLevelId(p->vCubes, vCube) );
        p->nLits--;
    }
    // create updated double-cube divisor cube pairs
ExtractFromPairs:
    k = 0;
    p->nCompls = 0;
    assert( Vec_IntSize(p->vCubesD) % 2 == 0 );
    assert( Vec_IntSize(p->vCubesD) == 2 * Vec_IntSize(p->vCompls) );
    for ( i = 0; i < Vec_IntSize(p->vCubesD); i += 2 )
    {
        int fCompl = Vec_IntEntry(p->vCompls, i/2);
        p->nCompls += fCompl;
        vCube  = Vec_WecEntry( p->vCubes, Vec_IntEntry(p->vCubesD, i) );
        vCube2 = Vec_WecEntry( p->vCubes, Vec_IntEntry(p->vCubesD, i+1) );
        RetValue  = Fx2_ManDivRemoveLits( vCube, vDiv, fCompl );  // cube 2*i
        RetValue += Fx2_ManDivRemoveLits( vCube2, vDiv, fCompl ); // cube 2*i+1
        assert( RetValue == Vec_IntSize(vDiv) || RetValue == Vec_IntSize( vDiv ) + 1);
        if ( iVarNew > 0 )
        {
            if ( Vec_IntSize(vDiv) == 2 || fCompl )
            {
                Vec_IntPush( vCube, Abc_Var2Lit(iVarNew, 1) );
                Vec_IntPush( vLitN, Vec_WecLevelId(p->vCubes, vCube) ); // MAKE SURE vCube IS SORTED BY ID
            }
            else
            {
                Vec_IntPush( vCube, Abc_Var2Lit(iVarNew, 0) );
                Vec_IntPush( vLitP, Vec_WecLevelId(p->vCubes, vCube) ); // MAKE SURE vCube IS SORTED BY ID
            }
        }
        p->nLits -= Vec_IntSize(vDiv) + Vec_IntSize(vCube2) - 2;

        // remove second cube
        Vec_IntWriteEntry( p->vCubesD, k++, Vec_WecLevelId(p->vCubes, vCube) );
        // Empty cubes need no matches; a dense signature usually rejects them.
        Vec_WrdWriteEntry( p->vSigns, Vec_WecLevelId(p->vCubes, vCube2), ~(word)0 );
        Vec_IntClear( vCube2 );
    }
    assert( k == Vec_IntSize(p->vCubesD) / 2 );
    Vec_IntShrink( p->vCubesD, k );
    Vec_IntSort( p->vCubesD, 0 );
    //Vec_IntSort( vLitN, 0 );
    //Vec_IntSort( vLitP, 0 );

    // Refresh signatures after edits, including newly allocated divisor cubes.
    Fx2_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
        Vec_WrdWriteEntry( p->vSigns, Vec_WecLevelId(p->vCubes, vCube), Fx2_ManCubeSign(vCube) );
    Fx2_ManForEachCubeVec( p->vCubesD, p->vCubes, vCube, i )
        Vec_WrdWriteEntry( p->vSigns, Vec_WecLevelId(p->vCubes, vCube), Fx2_ManCubeSign(vCube) );
    while ( Vec_WrdSize(p->vSigns) < Vec_WecSize(p->vCubes) )
        Vec_WrdPush( p->vSigns, Fx2_ManCubeSign(Vec_WecEntry(p->vCubes, Vec_WrdSize(p->vSigns))) );

    // add cost of single-cube divisors
    Fx2_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
        Fx2_ManCubeSingleCubeDivisors( p, vCube, 0, 1 );  // add - update
    Fx2_ManForEachCubeVec( p->vCubesD, p->vCubes, vCube, i )
        Fx2_ManCubeSingleCubeDivisors( p, vCube, 0, 1 );  // add - update
    if ( p->fInvalid )
        return;

    // mark the cubes to be removed
    Vec_WecMarkLevels( p->vCubes, p->vCubesS );
    Vec_WecMarkLevels( p->vCubes, p->vCubesD );

    // add cost of double-cube divisors
    Fx2_ManForEachCubeVec( p->vCubesS, p->vCubes, vCube, i )
        Fx2_ManCubeDoubleCubeDivisors( p, Fx2_ManGetFirstVarCube(p, vCube), vCube, 0, 1 );  // add - update
    Fx2_ManForEachCubeVec( p->vCubesD, p->vCubes, vCube, i )
        Fx2_ManCubeDoubleCubeDivisors( p, Fx2_ManGetFirstVarCube(p, vCube), vCube, 0, 1 );  // add - update

    // unmark the cubes to be removed
    Vec_WecUnmarkLevels( p->vCubes, p->vCubesS );
    Vec_WecUnmarkLevels( p->vCubes, p->vCubesD );
    if ( p->fInvalid )
        return;

    // Deal with SCC
    if ( Vec_IntSize( p->vSCC ) )
    {
        Vec_IntUniqify( p->vSCC );
        Fx2_ManForEachCubeVec( p->vSCC, p->vCubes, vCube, i )
        {
            int iCube = Vec_WecLevelId( p->vCubes, vCube );
            // Pending containment facts may predate this extraction. A
            // rewritten cube can now cover its former partner's minterms.
            // Only live, untouched cubes are still safe to clear.
            if ( !Vec_IntSize(vCube) || Vec_IntFind(p->vCubesS, iCube) >= 0 ||
                 Vec_IntFind(p->vCubesD, iCube) >= 0 )
                continue;
            Fx2_ManCubeDoubleCubeDivisors( p, Fx2_ManGetFirstVarCube(p, vCube), vCube, 1, 1 );  // remove - update
            if ( p->fInvalid )
                return;
            Vec_WrdWriteEntry( p->vSigns, Vec_WecLevelId(p->vCubes, vCube), ~(word)0 );
            Vec_IntClear( vCube );
        }
        Vec_IntClear( p->vSCC );
    }
    // add cost of the new divisor
    if ( Vec_IntSize(vDiv) > 2 )
    {
        vCube  = Vec_WecEntry( p->vCubes, Vec_WecSize(p->vCubes) - 2 );
        vCube2 = Vec_WecEntry( p->vCubes, Vec_WecSize(p->vCubes) - 1 );
        Fx2_ManCubeSingleCubeDivisors( p, vCube,  0, 1 );  // add - update
        Fx2_ManCubeSingleCubeDivisors( p, vCube2, 0, 1 );  // add - update
        if ( p->fInvalid )
            return;
        Vec_IntForEachEntryStart( vCube, Lit0, i, 1 )
            Vec_WecPush( p->vLits, Lit0, Vec_WecLevelId(p->vCubes, vCube) );
        Vec_IntForEachEntryStart( vCube2, Lit0, i, 1 )
            Vec_WecPush( p->vLits, Lit0, Vec_WecLevelId(p->vCubes, vCube2) );
    }

    // remove these cubes from the lit array of the divisor
    Vec_IntForEachEntry( vDiv, Lit0, i )
    {
        Vec_IntTwoRemove( Vec_WecEntry(p->vLits, Abc_Lit2Var(Lit0)), p->vCubesD );
        if ( (p->nCompls && i > 1) || Vec_IntSize( vDiv ) == 2 ) // the last two lits are possibly complemented
            Vec_IntTwoRemove( Vec_WecEntry(p->vLits, Abc_LitNot(Abc_Lit2Var(Lit0))), p->vCubesD );
    }

}

/**Function*************************************************************

  Synopsis    [Implements the traditional fast_extract algorithm.]

  Description [J. Rajski and J. Vasudevamurthi, "The testability-
  preserving concurrent decomposition and factorization of Boolean
  expressions", IEEE TCAD, Vol. 11, No. 6, June 1992, pp. 778-793.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Fx2_FastExtract( Vec_Wec_t * vCubes, int ObjIdMax, int nNewNodesMax, int LitCountMax, int fCanonDivs, int fVerbose, int fVeryVerbose )
{
    int fVeryVeryVerbose = 0;
    int i, iDiv, RetValue;
    Vec_Int_t * vCube;
    Fx2_Man_t * p;
    abctime clk = Abc_Clock();
    if ( Vec_WecSize(vCubes) == 0 )
        return 0;
    Vec_WecForEachLevel( vCubes, vCube, i )
        if ( Fx2_ManPairCount(Vec_IntSize(vCube) - 1) < 0 )
        {
            printf( "Cannot perform \"fx2\": a cube's pair cache exceeds the vector size limit.\n" );
            return -1;
        }
    // initialize the data-structure
    p = Fx2_ManStart( vCubes );
    p->LitCountMax = LitCountMax;
    p->fCanonDivs = fCanonDivs;
    Fx2_ManCreateLiterals( p, ObjIdMax );
    Fx2_ManComputeLevel( p );
    Fx2_ManCreateDivisors( p );
    if ( p->fInvalid )
    {
        Fx2_ManStop( p );
        return -1;
    }
    if ( fVeryVerbose )
        Fx2_PrintDivisors( p );
    if ( fVerbose )
        Fx2_PrintStats( p, Abc_Clock() - clk );
    // perform extraction
    p->timeStart = Abc_Clock();
    for ( i = 0; i < nNewNodesMax && Vec_QueTopPriority(p->vPrio) > 0.0; i++ )
    {
        iDiv = Vec_QuePop(p->vPrio);
        if ( fVeryVerbose )
            Fx2_PrintDiv( p, iDiv );
        Fx2_ManUpdate( p, iDiv );
        if ( p->fInvalid )
            break;
        if ( fVeryVeryVerbose )
            Fx2_PrintDivisors( p );
    }
    if ( fVerbose )
        Fx2_PrintStats( p, Abc_Clock() - clk );
    RetValue = p->fInvalid ? -1 : 1;
    Fx2_ManStop( p );
    // return the result
    if ( RetValue > 0 )
        Vec_WecRemoveEmpty( vCubes );
    return RetValue;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
