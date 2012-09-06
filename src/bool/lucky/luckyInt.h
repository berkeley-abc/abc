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
#define bool int
#define false 0
#define true 1
#define inline __inline  // compatible with MS VS 6.0
#define ABC_ALLOC(type, num)    ((type *) malloc(sizeof(type) * (num)))
#endif


ABC_NAMESPACE_HEADER_START

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

static word SFmask[5][4] = {
    {0x8888888888888888,0x4444444444444444,0x2222222222222222,0x1111111111111111},
    {0xC0C0C0C0C0C0C0C0,0x3030303030303030,0x0C0C0C0C0C0C0C0C,0x0303030303030303},
    {0xF000F000F000F000,0x0F000F000F000F00,0x00F000F000F000F0,0x000F000F000F000F},
    {0xFF000000FF000000,0x00FF000000FF0000,0x0000FF000000FF00,0x000000FF000000FF},
    {0xFFFF000000000000,0x0000FFFF00000000,0x00000000FFFF0000,0x000000000000FFFF}    
};

static inline int CompareWords(word x, word  y)
{
    if(x>y)
        return 1;
    else if(x<y)
        return -1;
    else
        return 0;
    
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
extern  inline void  Kit_TruthSemiCanonicize_Yasha_simple( word* pInOut, int nVars, int * pStore );
extern  inline unsigned  Kit_TruthSemiCanonicize_Yasha( word* pInOut, int nVars, char * pCanonPerm);
extern  inline unsigned  Kit_TruthSemiCanonicize_Yasha1( word* pInOut, int nVars, char * pCanonPerm, int * pStore );
extern  inline word luckyCanonicizer_final_fast_6Vars(word InOut, int* pStore, char* pCanonPerm, unsigned* pCanonPhase );
extern  inline void luckyCanonicizer_final_fast_16Vars(word* pInOut, int  nVars, int nWords, int * pStore, char * pCanonPerm, unsigned* pCanonPhase);
extern  inline void resetPCanonPermArray_6Vars(char* x);
extern  void swap_ij( word* f,int totalVars, int varI, int varJ);
extern  inline unsigned adjustInfoAfterSwap(char* pCanonPerm, unsigned uCanonPhase, int iVar, unsigned info);
extern  inline void resetPCanonPermArray(char* x, int nVars);


ABC_NAMESPACE_HEADER_END

#endif /* LUCKY_H_ */