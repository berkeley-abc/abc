/**CFile****************************************************************

  FileName    [luckyInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Semi-canonical form computation package.]

  Synopsis    [Internal declarations.]

  Author      [Jake]

  Date        [Started - August 2012]

***********************************************************************/

#ifndef ABC__bool__lucky__LUCKY_INT_H_
#define ABC__bool__lucky__LUCKY_INT_H_

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <math.h>
#include <time.h>

// comment out this line to run Lucky Code outside of ABC
#define _RUNNING_ABC_

#ifdef _RUNNING_ABC_
#include "misc/util/abc_global.h"
#else
#define ABC_NAMESPACE_HEADER_START
#define ABC_NAMESPACE_HEADER_END
#define ABC_NAMESPACE_IMPL_START
#define ABC_NAMESPACE_IMPL_END
typedef unsigned __int64  word;
#endif


ABC_NAMESPACE_HEADER_START


#define bool int
#define false 0
#define true 1
#define inline __inline  // compatible with MS VS 6.0
#define ABC_ALLOC(type, num)    ((type *) malloc(sizeof(type) * (num)))
static word mask1[6] = { 0xAAAAAAAAAAAAAAAA,0xCCCCCCCCCCCCCCCC, 0xF0F0F0F0F0F0F0F0,0xFF00FF00FF00FF00,0xFFFF0000FFFF0000, 0xFFFFFFFF00000000 };
static word mask0[6] = { 0x5555555555555555,0x3333333333333333, 0x0F0F0F0F0F0F0F0F,0x00FF00FF00FF00FF,0x0000FFFF0000FFFF, 0x00000000FFFFFFFF};    
static word mask[6][2] =   {
    {0x5555555555555555,0xAAAAAAAAAAAAAAAA},
    {0x3333333333333333,0xCCCCCCCCCCCCCCCC},
    {0x0F0F0F0F0F0F0F0F,0xF0F0F0F0F0F0F0F0},
    {0x00FF00FF00FF00FF,0xFF00FF00FF00FF00},
    {0x0000FFFF0000FFFF,0xFFFF0000FFFF0000},
    {0x00000000FFFFFFFF,0xFFFFFFFF00000000}
};

typedef struct  
{
    int      nVars;
    int      nWords;
    int      nFuncs;
    word **  pFuncs;
}Abc_TtStore_t;

typedef struct 
{
    int direction; 
    int position;
} varInfo;


typedef struct 
{
    varInfo* posArray;
    int* realArray;
    int varN;
    int positionToSwap1;
    int positionToSwap2;
} swapInfo;

typedef struct
{
    int varN;
    int* swapArray;
    int swapCtr;
    int totalSwaps;
    int* flipArray;
    int flipCtr;
    int totalFlips;    
}permInfo;

static inline void TimePrint( char* Message )
{
    static int timeBegin;
    double time = 1.0*(clock() - timeBegin)/CLOCKS_PER_SEC ;
    if ( Message != NULL)
        printf("%s = %f sec.\n", Message, time);
    timeBegin = clock();
}

extern  inline int memCompare(word* x, word*  y, int nVars);
extern  inline int Kit_TruthWordNum_64bit( int nVars );
extern  Abc_TtStore_t * setTtStore(char * pFileInput);
extern  inline void Abc_TruthStoreFree( Abc_TtStore_t * p );
extern  inline void Kit_TruthChangePhase_64bit( word * pInOut, int nVars, int iVar );
extern  inline void Kit_TruthNot_64bit(word * pIn, int nVars );
extern  inline void Kit_TruthCopy_64bit( word * pOut, word * pIn, int nVars );
extern  inline void Kit_TruthSwapAdjacentVars_64bit( word * pInOut, int nVars, int iVar );
extern  inline int Kit_TruthCountOnes_64bit( word* pIn, int nVars );
extern  void simpleMinimal(word* x, word* pAux,word* minimal, permInfo* pi, int nVars);
extern  permInfo* setPermInfoPtr(int var);
extern  void freePermInfoPtr(permInfo* x);
extern  inline unsigned  Kit_TruthSemiCanonicize_Yasha_simple( word* pInOut, int nVars, char * pCanonPerm  );
extern  inline unsigned  Kit_TruthSemiCanonicize_Yasha( word* pInOut, int nVars, char * pCanonPerm );

ABC_NAMESPACE_HEADER_END

#endif /* LUCKY_H_ */