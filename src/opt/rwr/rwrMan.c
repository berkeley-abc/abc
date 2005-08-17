/**CFile****************************************************************

  FileName    [rwrMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the following information was derived by computing all 4-input cuts of IWLS, MCNC, and ISCAS benchmarks
#define RWR_NUM_CLASSES  775
static int s_PracticalClasses[RWR_NUM_CLASSES] = {
    0, 1, 3, 5, 6, 7, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 51, 53, 54, 55, 60, 61, 63, 85, 86, 
    87, 90, 91, 95, 102, 103, 105, 107, 111, 119, 123, 125, 126, 127, 255, 257, 258, 259, 260, 261, 262, 263, 264, 265, 
    266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 281, 282, 284, 286, 287, 288, 289, 290, 291, 293, 297, 
    298, 299, 300, 302, 303, 304, 305, 306, 307, 308, 310, 311, 312, 313, 315, 316, 317, 319, 320, 321, 323, 324, 325, 329, 
    332, 334, 335, 336, 337, 338, 340, 341, 342, 343, 345, 347, 349, 351, 352, 357, 358, 359, 361, 367, 368, 369, 371, 
    373, 375, 379, 381, 383, 384, 385, 386, 388, 389, 392, 393, 395, 397, 399, 400, 404, 408, 409, 416, 417, 419, 420, 
    421, 424, 425, 426, 427, 431, 433, 443, 448, 449, 451, 453, 456, 457, 459, 460, 461, 462, 463, 465, 476, 477, 480, 
    481, 483, 489, 492, 493, 494, 495, 496, 497, 499, 500, 501, 506, 507, 508, 509, 510, 771, 773, 774, 775, 780, 781, 
    783, 785, 786, 787, 788, 790, 791, 792, 796, 797, 799, 816, 817, 819, 820, 821, 834, 835, 836, 837, 838, 839, 840, 
    844, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 859, 860, 861, 863, 864, 867, 870, 871, 876, 878, 880, 883, 
    884, 885, 887, 967, 973, 975, 979, 984, 988, 989, 990, 1009, 1011, 1012, 1013, 1020, 1285, 1286, 1287, 1290, 1291, 
    1295, 1297, 1298, 1300, 1301, 1303, 1307, 1308, 1309, 1311, 1314, 1316, 1317, 1318, 1319, 1322, 1325, 1327, 1329, 
    1330, 1331, 1332, 1333, 1334, 1335, 1336, 1338, 1340, 1341, 1360, 1361, 1363, 1365, 1367, 1380, 1381, 1382, 1383, 
    1390, 1392, 1395, 1397, 1399, 1440, 1445, 1447, 1450, 1451, 1455, 1458, 1461, 1463, 1467, 1525, 1530, 1542, 1543, 
    1545, 1547, 1551, 1553, 1554, 1558, 1559, 1561, 1567, 1569, 1570, 1572, 1574, 1576, 1587, 1588, 1590, 1591, 1596, 
    1618, 1620, 1621, 1623, 1624, 1632, 1638, 1641, 1647, 1654, 1655, 1680, 1686, 1687, 1689, 1695, 1718, 1776, 1782, 
    1785, 1799, 1803, 1805, 1806, 1807, 1811, 1813, 1815, 1823, 1826, 1831, 1843, 1844, 1847, 1859, 1860, 1863, 1875, 
    1877, 1879, 1895, 1902, 1904, 1911, 1912, 1927, 1928, 1933, 1935, 1945, 1956, 1957, 1959, 1962, 1964, 1965, 1975, 
    1979, 1987, 1991, 1995, 1996, 2000, 2002, 2007, 2013, 2023, 2032, 2040, 3855, 3857, 3859, 3861, 3864, 3866, 3867, 
    3868, 3869, 3870, 3891, 3892, 3893, 3900, 3921, 3925, 3942, 3945, 3956, 3960, 4080, 4369, 4370, 4371, 4372, 4373, 
    4374, 4375, 4376, 4377, 4378, 4379, 4380, 4381, 4382, 4386, 4387, 4388, 4389, 4391, 4392, 4394, 4396, 4403, 4405, 
    4408, 4409, 4411, 4420, 4421, 4422, 4423, 4424, 4426, 4428, 4437, 4439, 4445, 4488, 4494, 4505, 4507, 4509, 4522, 
    4524, 4525, 4526, 4539, 4540, 4542, 4556, 4557, 4573, 4574, 4590, 4626, 4627, 4629, 4630, 4631, 4632, 4634, 4638, 
    4641, 4643, 4648, 4659, 4680, 4695, 4698, 4702, 4713, 4731, 4740, 4758, 4766, 4773, 4791, 4812, 4830, 4845, 4883, 
    4885, 4887, 4888, 4891, 4892, 4899, 4903, 4913, 4914, 4915, 4934, 4940, 4945, 4947, 4949, 4951, 4972, 5005, 5011, 
    5017, 5019, 5029, 5043, 5049, 5058, 5059, 5060, 5068, 5075, 5079, 5083, 5084, 5100, 5140, 5141, 5142, 5143, 5148, 
    5160, 5171, 5174, 5180, 5182, 5185, 5186, 5187, 5189, 5205, 5207, 5214, 5238, 5245, 5246, 5250, 5270, 5278, 5290, 
    5310, 5315, 5335, 5355, 5397, 5399, 5401, 5402, 5405, 5413, 5414, 5415, 5418, 5427, 5429, 5445, 5457, 5460, 5461, 
    5463, 5469, 5482, 5522, 5525, 5533, 5540, 5546, 5557, 5565, 5571, 5580, 5589, 5593, 5605, 5610, 5654, 5673, 5692, 
    5698, 5729, 5734, 5782, 5790, 5796, 5814, 5826, 5846, 5911, 5931, 5965, 6001, 6066, 6120, 6168, 6174, 6180, 6206, 
    6210, 6229, 6234, 6270, 6273, 6279, 6363, 6375, 6425, 6427, 6438, 6446, 6451, 6457, 6478, 6482, 6485, 6489, 6502, 
    6545, 6553, 6564, 6570, 6594, 6617, 6630, 6682, 6683, 6685, 6686, 6693, 6709, 6741, 6746, 6817, 6821, 6826, 6833, 
    6849, 6885, 6939, 6940, 6951, 6963, 6969, 6990, 6997, 7065, 7077, 7089, 7140, 7196, 7212, 7219, 7220, 7228, 7230, 
    7251, 7324, 7356, 7361, 7363, 7372, 7377, 7395, 7453, 7470, 7475, 7495, 7509, 7513, 7526, 7619, 7633, 7650, 7710, 
    7725, 7731, 7740, 7755, 7770, 7800, 7815, 7830, 7845, 7860, 7890, 7905, 13107, 13109, 13110, 13116, 13141, 13146, 
    13161, 13164, 13621, 13622, 13626, 13651, 13653, 13658, 13669, 13670, 13763, 13765, 13770, 13878, 13881, 13884, 
    13910, 13923, 13926, 13932, 13971, 13974, 13980, 14022, 14025, 15420, 15445, 15450, 15462, 15465, 15555, 21845, 
    21846, 21850, 21865, 21866, 21930, 22102, 22105, 22106, 22117, 22118, 22122, 22165, 22166, 22169, 22170, 22181, 
    22182, 22185, 23130, 23142, 23145, 23205, 26214, 26217, 26985, 27030 
};

static unsigned short      Rwr_FunctionPerm( unsigned uTruth, int Phase );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_ManRwr_t * Abc_NtkManRwrStart( char * pFileName )
{
    Abc_ManRwr_t * p;
    unsigned uTruth;
    int i, k, nClasses;
    int clk = clock();

    p = ALLOC( Abc_ManRwr_t, 1 );
    memset( p, 0, sizeof(Abc_ManRwr_t) );
    // canonical forms
    p->nFuncs    = (1<<16);
    p->puCanons  = ALLOC( unsigned short, p->nFuncs );
    memset( p->puCanons, 0, sizeof(unsigned short) * p->nFuncs );
    // permutations
    p->puPhases  = ALLOC( char, p->nFuncs );
    memset( p->puPhases, 0, sizeof(char) * p->nFuncs );
    // hash table
    p->pTable  = ALLOC( Rwr_Node_t *, p->nFuncs );
    memset( p->pTable, 0, sizeof(Rwr_Node_t *) * p->nFuncs );
    // practical classes
    p->pPractical  = ALLOC( char, p->nFuncs );
    memset( p->pPractical, 0, sizeof(char) * p->nFuncs );
    // other stuff
    p->vForest  = Vec_PtrAlloc( 100 );
    p->vForm    = Vec_IntAlloc( 50 );
    p->vFanins  = Vec_PtrAlloc( 50 );
    p->vTfo     = Vec_PtrAlloc( 50 );
    p->vLevels  = Vec_VecAlloc( 50 );
    p->pMmNode  = Extra_MmFixedStart( sizeof(Rwr_Node_t) );
    p->nTravIds = 1;
    assert( sizeof(Rwr_Node_t) == sizeof(Rwr_Cut_t) );

    // initialize the canonical forms
    nClasses = 1;
    for ( i = 1; i < p->nFuncs-1; i++ )
    {
        if ( p->puCanons[i] )
            continue;
        nClasses++;
        for ( k = 0; k < 32; k++ )
        {
            uTruth = Rwr_FunctionPhase( (unsigned)i, (unsigned)k );
            if ( p->puCanons[uTruth] == 0 )
            {
                p->puCanons[uTruth] = (unsigned short)i;
                p->puPhases[uTruth] = (char)k;
            }
            else
                assert( p->puCanons[uTruth] == (unsigned short)i );
        }
    }
    // set info for constant 1
    p->puCanons[p->nFuncs-1] = 0;
    p->puPhases[p->nFuncs-1] = 16;
    printf( "The number of NN-canonical forms = %d.\n", nClasses );

    // initialize permutations
    for ( i = 0; i < 256; i++ )
        for ( k = 0; k < 16; k++ )
            p->puPerms[i][k] = Rwr_FunctionPerm( i, k );

    // initialize practical classes
    for ( i = 0; i < RWR_NUM_CLASSES; i++ )
        p->pPractical[ s_PracticalClasses[i] ] = 1;

    // initialize forest
    Rwr_ManAddVar( p, 0xFFFF ); // constant 1
    Rwr_ManAddVar( p, 0xAAAA ); // var A
    Rwr_ManAddVar( p, 0xCCCC ); // var B
    Rwr_ManAddVar( p, 0xF0F0 ); // var C
    Rwr_ManAddVar( p, 0xFF00 ); // var D
    p->nClasses = 5;
PRT( "Manager startup time", clock() - clk ); 

    // create the nodes
    if ( pFileName == NULL )
    {   // precompute
        Rwr_ManPrecompute( p );
        Rwr_ManWriteToFile( p, "data.aaa" );
    }
    else
    {   // load previously saved nodes
        Rwr_ManLoadFromFile( p, pFileName );
    }
    Rwr_ManPrint( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkManRwrStop( Abc_ManRwr_t * p )
{
    if ( p->vFanNums )  Vec_IntFree( p->vFanNums );
    if ( p->vReqTimes ) Vec_IntFree( p->vReqTimes );
    Vec_IntFree( p->vForm );
    Vec_PtrFree( p->vFanins );
    Vec_PtrFree( p->vTfo );
    Vec_VecFree( p->vLevels );
    Vec_PtrFree( p->vForest );
    Extra_MmFixedStop( p->pMmNode,   0 );
    free( p->pPractical );
    free( p->puCanons );
    free( p->puPhases );
    free( p->pTable );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkManRwrDecs( Abc_ManRwr_t * p )
{
    return p->vForm;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkManRwrFanins( Abc_ManRwr_t * p )
{
    return p->vFanins;
}

/**Function*************************************************************

  Synopsis    [Computes a phase of the 4-var function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned short Rwr_FunctionPhase( unsigned uTruth, unsigned uPhase )
{
    static unsigned uMasks0[4] = { 0x5555, 0x3333, 0x0F0F, 0x00FF };
    static unsigned uMasks1[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    int v, Shift;
    for ( v = 0, Shift = 1; v < 4; v++, Shift <<= 1 )
        if ( uPhase & Shift )
            uTruth = (((uTruth & uMasks0[v]) << Shift) | ((uTruth & uMasks1[v]) >> Shift));
    if ( uPhase & 16 )
        uTruth = ~uTruth & 0xFFFF;
    return uTruth;
}

/**Function*************************************************************

  Synopsis    [Computes a phase of the 3-var function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned short Rwr_FunctionPerm( unsigned uTruth, int Phase )
{
    static int Perm[16][4] = {
        { 0, 1, 2, 3 }, // 0000  - skip
        { 0, 1, 2, 3 }, // 0001  - skip
        { 1, 0, 2, 3 }, // 0010
        { 0, 1, 2, 3 }, // 0011  - skip
        { 2, 1, 0, 3 }, // 0100
        { 0, 2, 1, 3 }, // 0101
        { 2, 0, 1, 3 }, // 0110
        { 0, 1, 2, 3 }, // 0111  - skip
        { 3, 1, 2, 0 }, // 1000
        { 0, 3, 2, 1 }, // 1001
        { 3, 0, 2, 1 }, // 1010
        { 0, 1, 3, 2 }, // 1011
        { 2, 3, 0, 1 }, // 1100
        { 0, 3, 1, 2 }, // 1101
        { 3, 0, 1, 2 }, // 1110
        { 0, 1, 2, 3 }  // 1111  - skip
    };
    int i, k, iRes;
    unsigned uTruthRes;
    assert( Phase < 16 );
    uTruthRes = 0;
    for ( i = 0; i < 16; i++ )
        if ( uTruth & (1 << i) )
        {
            for ( iRes = 0, k = 0; k < 4; k++ )
                if ( i & (1 << k) )
                    iRes |= (1 << Perm[Phase][k]);
            uTruthRes |= (1 << iRes);
        }
    return uTruthRes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


