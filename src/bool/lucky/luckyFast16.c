/**CFile****************************************************************

  FileName    [luckyFast16.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Semi-canonical form computation package.]

  Synopsis    [Truth table minimization procedures for up to  16 vars.]

  Author      [Jake]

  Date        [Started - September 2012]

***********************************************************************/

#include "luckyInt.h"


ABC_NAMESPACE_IMPL_START

static word SFmask[5][4] = {
    {0x8888888888888888,0x4444444444444444,0x2222222222222222,0x1111111111111111},
    {0xC0C0C0C0C0C0C0C0,0x3030303030303030,0x0C0C0C0C0C0C0C0C,0x0303030303030303},
    {0xF000F000F000F000,0x0F000F000F000F00,0x00F000F000F000F0,0x000F000F000F000F},
    {0xFF000000FF000000,0x00FF000000FF0000,0x0000FF000000FF00,0x000000FF000000FF},
    {0xFFFF000000000000,0x0000FFFF00000000,0x00000000FFFF0000,0x000000000000FFFF}   
};


////////////////////////////////////lessThen5/////////////////////////////////////////////////////////////////////////////////////////////

// there are 4 parts in every block to compare and rearrange - quoters(0Q,1Q,2Q,3Q)
//updataInfo updates CanonPerm and CanonPhase based on what quoter in position iQ and jQ
inline void updataInfo(int iQ, int jQ, int iVar,  char * pCanonPerm, unsigned* pCanonPhase)
{
    *pCanonPhase = adjustInfoAfterSwap(pCanonPerm, *pCanonPhase, iVar, ((abs(iQ-jQ)-1)<<2) + iQ );

}
// It rearranges InOut (swaps and flips through rearrangement of quoters)
// It updates Info at the end
inline void arrangeQuoters_superFast_lessThen5(word* pInOut, int start, int iQ, int jQ, int kQ, int lQ, int iVar, int nWords, char * pCanonPerm, unsigned* pCanonPhase)
{
    int i;
    int  blockSize = 1<<iVar;
    for(i=start;i>=0;i--)
    {   
        pInOut[i] = (pInOut[i] & SFmask[iVar][iQ])<<(iQ*blockSize) |
            (((pInOut[i] & SFmask[iVar][jQ])<<(jQ*blockSize))>>blockSize) |
            (((pInOut[i] & SFmask[iVar][kQ])<<(kQ*blockSize))>>2*blockSize) |
            (((pInOut[i] & SFmask[iVar][lQ])<<(lQ*blockSize))>>3*blockSize);
    }
    updataInfo(iQ, jQ, iVar, pCanonPerm, pCanonPhase);
}

//It compares 0Q and 3Q and returns 0 if 0Q is smaller then 3Q ( comparison starts at highest bit) and visa versa
// DifStart contains the information about the first different bit in 0Q and 3Q
inline int minTemp0_fast(word* pInOut, int iVar, int nWords, int* pDifStart)
{
    int i, j=1;
    int  blockSize = 1<<iVar;
    int  shiftSize = blockSize*4;
    word temp;
    for(i=nWords - 1; i>=0; i--)
    {
        temp = ((pInOut[i] & SFmask[iVar][0])) ^ ((pInOut[i] & SFmask[iVar][3])<<(3*blockSize));
        if( temp == 0)
            continue;
        else
        {
            *pDifStart = i*100;
            while(temp == (temp<<(shiftSize*j))>>shiftSize*j)
                j++;
            *pDifStart += 21 - j;

            if( ((pInOut[i] & SFmask[iVar][0])) < ((pInOut[i] & SFmask[iVar][3])<<(3*blockSize)) )
                return 0;
            else
                return 3;
        }
    }
    *pDifStart=0;
    return 0;

}

//It compares 1Q and 2Q and returns 1 if 1Q is smaller then 2Q ( comparison starts at highest bit) and visa versa
// DifStart contains the information about the first different bit in 1Q and 2Q
inline int minTemp1_fast(word* pInOut, int iVar, int nWords, int* pDifStart)
{
    int i, j=1;
    int  blockSize = 1<<iVar;
    int  shiftSize = blockSize*4;
    word temp;
    for(i=nWords - 1; i>=0; i--)
    {
        temp = ((pInOut[i] & SFmask[iVar][1])<<(blockSize)) ^ ((pInOut[i] & SFmask[iVar][2])<<(2*blockSize));
        if( temp == 0)
            continue;
        else
        {
            *pDifStart = i*100;
            while(temp == (temp<<(shiftSize*j))>>shiftSize*j)
                j++;
            *pDifStart += 21 - j;
            if( ((pInOut[i] & SFmask[iVar][1])<<(blockSize)) < ((pInOut[i] & SFmask[iVar][2])<<(2*blockSize)) )
                return 1;
            else
                return 2;
        }
    }
    *pDifStart=0;
    return 1;
}

//It compares iQ and jQ and returns 0 if iQ is smaller then jQ ( comparison starts at highest bit) and visa versa
// DifStart contains the information about the first different bit in iQ and jQ
inline int minTemp2_fast(word* pInOut, int iVar, int iQ, int jQ, int nWords, int* pDifStart)
{
    int i, j=1;
    int  blockSize = 1<<iVar;
    int  shiftSize = blockSize*4;
    word temp;
    for(i=nWords - 1; i>=0; i--)
    {
        temp = ((pInOut[i] & SFmask[iVar][iQ])<<(iQ*blockSize)) ^ ((pInOut[i] & SFmask[iVar][jQ])<<(jQ*blockSize));
        if( temp == 0)
            continue;
        else
        {
            *pDifStart = i*100;
            while(temp == (temp<<(shiftSize*j))>>shiftSize*j)
                j++;
            *pDifStart += 21 - j;
            if( ((pInOut[i] & SFmask[iVar][iQ])<<(iQ*blockSize)) <= ((pInOut[i] & SFmask[iVar][jQ])<<(jQ*blockSize)) )
                return 0;
            else
                return 1;
        }
    }
    *pDifStart=0;
    return iQ;
}
// same as minTemp2_fast but this one has a start position
inline int minTemp3_fast(word* pInOut, int iVar, int start, int finish, int iQ, int jQ, int* pDifStart)
{
    int i, j=1;
    int  blockSize = 1<<iVar;
    int  shiftSize = blockSize*4;
    word temp;
    for(i=start; i>=finish; i--)
    {
        temp = ((pInOut[i] & SFmask[iVar][iQ])<<(iQ*blockSize)) ^ ((pInOut[i] & SFmask[iVar][jQ])<<(jQ*blockSize));
        if( temp == 0)
            continue;
        else
        {
            *pDifStart = i*100;
            while(temp == (temp<<(shiftSize*j))>>shiftSize*j)
                j++;
            *pDifStart += 21 - j;

            if( ((pInOut[i] & SFmask[iVar][iQ])<<(iQ*blockSize)) <= ((pInOut[i] & SFmask[iVar][jQ])<<(jQ*blockSize)) )
                return 0;
            else
                return 1;
        }
    }
    *pDifStart=0;
    return iQ;
}

// It considers all swap and flip possibilities of iVar and iVar+1 and switches InOut to a minimal of them  
inline void minimalSwapAndFlipIVar_superFast_lessThen5(word* pInOut, int iVar, int nWords, char * pCanonPerm, unsigned* pCanonPhase)
{
    int min1, min2, DifStart0, DifStart1, DifStartMin;
    int M[2];   

    M[0] = minTemp0_fast(pInOut, iVar, nWords, &DifStart0); // 0, 3
    M[1] = minTemp1_fast(pInOut, iVar, nWords, &DifStart1); // 1, 2
    min1 = minTemp2_fast(pInOut, iVar, M[0], M[1], nWords, &DifStartMin);
    if(DifStart0 != DifStart1)
    {   
        if( DifStartMin>=DifStart1 && DifStartMin>=DifStart0 )
            arrangeQuoters_superFast_lessThen5(pInOut, DifStartMin/100, M[min1], M[(min1+1)%2], 3 - M[(min1+1)%2], 3 - M[min1], iVar, nWords, pCanonPerm, pCanonPhase);
        else if( DifStart0 > DifStart1)
            arrangeQuoters_superFast_lessThen5(pInOut,luckyMax(DifStartMin/100, DifStart0/100), M[0], M[1], 3 - M[1], 3 - M[0], iVar, nWords, pCanonPerm, pCanonPhase);
        else
            arrangeQuoters_superFast_lessThen5(pInOut,luckyMax(DifStartMin/100, DifStart1/100), M[1], M[0], 3 - M[0], 3 - M[1], iVar, nWords, pCanonPerm, pCanonPhase);
    }
    else
    {
        if(DifStartMin>=DifStart0)
            arrangeQuoters_superFast_lessThen5(pInOut, DifStartMin/100, M[min1], M[(min1+1)%2], 3 - M[(min1+1)%2], 3 - M[min1], iVar, nWords, pCanonPerm, pCanonPhase);
        else
        {
            min2 = minTemp3_fast(pInOut, iVar, DifStart0/100, DifStartMin/100, 3-M[0], 3-M[1], &DifStart1);  // reuse DifStart1 because DifStart1 = DifStart1=0
            if(DifStart1>DifStartMin)
                arrangeQuoters_superFast_lessThen5(pInOut, DifStart0/100, M[(min2+1)%2], M[min2], 3 - M[min2], 3 - M[(min2+1)%2], iVar, nWords, pCanonPerm, pCanonPhase);
            else
                arrangeQuoters_superFast_lessThen5(pInOut, DifStart0/100, M[min1], M[(min1+1)%2], 3 - M[(min1+1)%2], 3 - M[min1], iVar, nWords, pCanonPerm, pCanonPhase);
        }
    }
}
////////////////////////////////////iVar = 5/////////////////////////////////////////////////////////////////////////////////////////////

// It rearranges InOut (swaps and flips through rearrangement of quoters)
// It updates Info at the end
inline void arrangeQuoters_superFast_iVar5(unsigned* pInOut, unsigned* temp, int start,  int iQ, int jQ, int kQ, int lQ, char * pCanonPerm, unsigned* pCanonPhase)
{
    int i,blockSize,shiftSize;
    unsigned* tempPtr = temp+start;
    if(iQ == 0 && jQ == 1)
        return; 
    blockSize = sizeof(unsigned);
    shiftSize = 4;
    for(i=start-1;i>0;i-=shiftSize)
    {       
        tempPtr -= 1;       
        memcpy(tempPtr, pInOut+i-iQ, blockSize);
        tempPtr -= 1;
        memcpy(tempPtr, pInOut+i-jQ, blockSize);
        tempPtr -= 1;
        memcpy(tempPtr, pInOut+i-kQ, blockSize);
        tempPtr -= 1;
        memcpy(tempPtr, pInOut+i-lQ, blockSize);        
        
    }   
    memcpy(pInOut, temp, start*sizeof(unsigned));
    updataInfo(iQ, jQ, 5, pCanonPerm, pCanonPhase);
}

//It compares 0Q and 3Q and returns 0 if 0Q is smaller then 3Q ( comparison starts at highest bit) and visa versa
// DifStart contains the information about the first different bit in 0Q and 3Q
inline int minTemp0_fast_iVar5(unsigned* pInOut, int nWords, int* pDifStart)
{
    int i, temp;
    for(i=(nWords)*2 - 1; i>=0; i-=4)   
    {
        temp = CompareWords(pInOut[i],pInOut[i-3]);
        if(temp == 0)
            continue;
        else if(temp == -1)
        {
            *pDifStart = i+1;
            return 0;
        }
        else
        {
            *pDifStart = i+1;
            return 3;
        }
    }
    *pDifStart=0;
    return 0;
}

//It compares 1Q and 2Q and returns 1 if 1Q is smaller then 2Q ( comparison starts at highest bit) and visa versa
// DifStart contains the information about the first different bit in 1Q and 2Q
inline int minTemp1_fast_iVar5(unsigned* pInOut, int nWords, int* pDifStart)
{
    int i, temp;
    for(i=(nWords)*2 - 2; i>=0; i-=4)   
    {
        temp = CompareWords(pInOut[i],pInOut[i-1]);
        if(temp == 0)
            continue;
        else if(temp == -1)
        {
            *pDifStart = i+2;
            return 1;
        }
        else
        {
            *pDifStart = i+2;
            return 2;
        }
    }
    *pDifStart=0;
    return 1;
}

//It compares iQ and jQ and returns 0 if iQ is smaller then jQ ( comparison starts at highest bit) and visa versa
// DifStart contains the information about the first different bit in iQ and jQ
inline int minTemp2_fast_iVar5(unsigned* pInOut, int iQ, int jQ, int nWords, int* pDifStart)
{
    int i, temp;
    for(i=(nWords)*2 - 1; i>=0; i-=4)   
    {
        temp = CompareWords(pInOut[i-iQ],pInOut[i-jQ]);
        if(temp == 0)
            continue;
        else if(temp == -1)
        {
            *pDifStart = i+1;
            return 0;
        }
        else
        {
            *pDifStart = i+1;
            return 1;
        }
    }
    *pDifStart=0;
    return iQ;
}

// same as minTemp2_fast but this one has a start position
inline int minTemp3_fast_iVar5(unsigned* pInOut, int start, int finish, int iQ, int jQ, int* pDifStart)
{
    int i, temp;
    for(i=start-1; i>=finish; i-=4) 
    {
        temp = CompareWords(pInOut[i-iQ],pInOut[i-jQ]);
        if(temp == 0)
            continue;
        else if(temp == -1)
        {
            *pDifStart = i+1;
            return 0;
        }
        else
        {
            *pDifStart = i+1;
            return 1;
        }
    }
    *pDifStart=0;
    return iQ;
}

// It considers all swap and flip possibilities of iVar and iVar+1 and switches InOut to a minimal of them 
inline void minimalSwapAndFlipIVar_superFast_iVar5(unsigned* pInOut, int nWords, char * pCanonPerm, unsigned* pCanonPhase)
{
    int min1, min2, DifStart0, DifStart1, DifStartMin;
    int M[2];
    unsigned temp[2048];

    M[0] = minTemp0_fast_iVar5(pInOut, nWords, &DifStart0); // 0, 3
    M[1] = minTemp1_fast_iVar5(pInOut, nWords, &DifStart1); // 1, 2
    min1 = minTemp2_fast_iVar5(pInOut, M[0], M[1], nWords, &DifStartMin);
    if(DifStart0 != DifStart1)
    {   
        if( DifStartMin>=DifStart1 && DifStartMin>=DifStart0 )
            arrangeQuoters_superFast_iVar5(pInOut, temp, DifStartMin, M[min1], M[(min1+1)%2], 3 - M[(min1+1)%2], 3 - M[min1], pCanonPerm, pCanonPhase);
        else if( DifStart0 > DifStart1)
            arrangeQuoters_superFast_iVar5(pInOut, temp, luckyMax(DifStartMin,DifStart0), M[0], M[1], 3 - M[1], 3 - M[0], pCanonPerm, pCanonPhase);
        else
            arrangeQuoters_superFast_iVar5(pInOut, temp, luckyMax(DifStartMin,DifStart1), M[1], M[0], 3 - M[0], 3 - M[1], pCanonPerm, pCanonPhase);
    }
    else
    {
        if(DifStartMin>=DifStart0)
            arrangeQuoters_superFast_iVar5(pInOut, temp, DifStartMin, M[min1], M[(min1+1)%2], 3 - M[(min1+1)%2], 3 - M[min1], pCanonPerm, pCanonPhase);
        else
        {
            min2 = minTemp3_fast_iVar5(pInOut, DifStart0, DifStartMin, 3-M[0], 3-M[1], &DifStart1);  // reuse DifStart1 because DifStart1 = DifStart1=0
            if(DifStart1>DifStartMin)
                arrangeQuoters_superFast_iVar5(pInOut, temp, DifStart0, M[(min2+1)%2], M[min2], 3 - M[min2], 3 - M[(min2+1)%2], pCanonPerm, pCanonPhase);
            else
                arrangeQuoters_superFast_iVar5(pInOut, temp, DifStart0, M[min1], M[(min1+1)%2], 3 - M[(min1+1)%2], 3 - M[min1], pCanonPerm, pCanonPhase);
        }
    }
}

////////////////////////////////////moreThen5/////////////////////////////////////////////////////////////////////////////////////////////

// It rearranges InOut (swaps and flips through rearrangement of quoters)
// It updates Info at the end
inline void arrangeQuoters_superFast_moreThen5(word* pInOut, word* temp, int start,  int iQ, int jQ, int kQ, int lQ, int iVar, char * pCanonPerm, unsigned* pCanonPhase)
{
    int i,wordBlock,blockSize,shiftSize;
    word* tempPtr = temp+start;
    if(iQ == 0 && jQ == 1)
        return;
    wordBlock = (1<<(iVar-6));
    blockSize = wordBlock*sizeof(word);
    shiftSize = wordBlock*4;
    for(i=start-wordBlock;i>0;i-=shiftSize)
    {       
        tempPtr -= wordBlock;       
        memcpy(tempPtr, pInOut+i-iQ*wordBlock, blockSize);
        tempPtr -= wordBlock;
        memcpy(tempPtr, pInOut+i-jQ*wordBlock, blockSize);
        tempPtr -= wordBlock;
        memcpy(tempPtr, pInOut+i-kQ*wordBlock, blockSize);
        tempPtr -= wordBlock;
        memcpy(tempPtr, pInOut+i-lQ*wordBlock, blockSize);      
        
    }   
    memcpy(pInOut, temp, start*sizeof(word));
    updataInfo(iQ, jQ, iVar, pCanonPerm, pCanonPhase);
}

//It compares 0Q and 3Q and returns 0 if 0Q is smaller then 3Q ( comparison starts at highest bit) and visa versa
// DifStart contains the information about the first different bit in 0Q and 3Q
inline int minTemp0_fast_moreThen5(word* pInOut, int iVar, int nWords, int* pDifStart)
{
    int i, j, temp;
    int  wordBlock = 1<<(iVar-6);
    int wordDif = 3*wordBlock;
    int  shiftBlock = wordBlock*4;
    for(i=nWords - 1; i>=0; i-=shiftBlock)
        for(j=0;j<wordBlock;j++)
        {
            temp = CompareWords(pInOut[i-j],pInOut[i-j-wordDif]);
            if(temp == 0)
                continue;
            else if(temp == -1)
            {
                *pDifStart = i+1;
                return 0;
            }
            else
            {
                *pDifStart = i+1;
                return 3;
            }
        }
    *pDifStart=0;
    return 0;
}

//It compares 1Q and 2Q and returns 1 if 1Q is smaller then 2Q ( comparison starts at highest bit) and visa versa
// DifStart contains the information about the first different bit in 1Q and 2Q
inline int minTemp1_fast_moreThen5(word* pInOut, int iVar, int nWords, int* pDifStart)
{
    int i, j, temp;
    int  wordBlock = 1<<(iVar-6);
    int  shiftBlock = wordBlock*4;
    for(i=nWords - wordBlock - 1; i>=0; i-=shiftBlock)
        for(j=0;j<wordBlock;j++)
        {
            temp = CompareWords(pInOut[i-j],pInOut[i-j-wordBlock]);
            if(temp == 0)
                continue;
            else if(temp == -1)
            {
                *pDifStart = i+wordBlock+1;
                return 1;
            }
            else
            {
                *pDifStart = i+wordBlock+1;
                return 2;
            }
        }
    *pDifStart=0;
    return 1;
}

//It compares iQ and jQ and returns 0 if iQ is smaller then jQ ( comparison starts at highest bit) and visa versa
// DifStart contains the information about the first different bit in iQ and jQ
inline int minTemp2_fast_moreThen5(word* pInOut, int iVar, int iQ, int jQ, int nWords, int* pDifStart)
{
    int i, j, temp;
    int  wordBlock = 1<<(iVar-6);
    int  shiftBlock = wordBlock*4;
    for(i=nWords - 1; i>=0; i-=shiftBlock)
        for(j=0;j<wordBlock;j++)
        {
            temp = CompareWords(pInOut[i-j-iQ*wordBlock],pInOut[i-j-jQ*wordBlock]);
            if(temp == 0)
                continue;
            else if(temp == -1)
            {
                *pDifStart = i+1;
                return 0;
            }
            else
            {
                *pDifStart = i+1;
                return 1;
            }
        }
    *pDifStart=0;
    return iQ;
}

// same as minTemp2_fast but this one has a start position
inline int minTemp3_fast_moreThen5(word* pInOut, int iVar, int start, int finish, int iQ, int jQ, int* pDifStart)
{
    int i, j, temp;
    int  wordBlock = 1<<(iVar-6);
    int  shiftBlock = wordBlock*4;
    for(i=start-1; i>=finish; i-=shiftBlock)
        for(j=0;j<wordBlock;j++)
        {
            temp = CompareWords(pInOut[i-j-iQ*wordBlock],pInOut[i-j-jQ*wordBlock]);
            if(temp == 0)
                continue;
            else if(temp == -1)
            {
                *pDifStart = i+1;
                return 0;
            }
            else
            {
                *pDifStart = i+1;
                return 1;
            }
        }
    *pDifStart=0;
    return iQ;
}

// It considers all swap and flip possibilities of iVar and iVar+1 and switches InOut to a minimal of them 
inline void minimalSwapAndFlipIVar_superFast_moreThen5(word* pInOut, int iVar, int nWords, char * pCanonPerm, unsigned* pCanonPhase)
{
    int min1, min2, DifStart0, DifStart1, DifStartMin;
    int M[2];
    word temp[1024];

    M[0] = minTemp0_fast_moreThen5(pInOut, iVar, nWords, &DifStart0); // 0, 3
    M[1] = minTemp1_fast_moreThen5(pInOut, iVar, nWords, &DifStart1); // 1, 2
    min1 = minTemp2_fast_moreThen5(pInOut, iVar, M[0], M[1], nWords, &DifStartMin);
    if(DifStart0 != DifStart1)
    {   
        if( DifStartMin>=DifStart1 && DifStartMin>=DifStart0 )
            arrangeQuoters_superFast_moreThen5(pInOut, temp, DifStartMin, M[min1], M[(min1+1)%2], 3 - M[(min1+1)%2], 3 - M[min1], iVar, pCanonPerm, pCanonPhase);
        else if( DifStart0 > DifStart1)
            arrangeQuoters_superFast_moreThen5(pInOut, temp, luckyMax(DifStartMin,DifStart0), M[0], M[1], 3 - M[1], 3 - M[0], iVar, pCanonPerm, pCanonPhase);
        else
            arrangeQuoters_superFast_moreThen5(pInOut, temp, luckyMax(DifStartMin,DifStart1), M[1], M[0], 3 - M[0], 3 - M[1], iVar, pCanonPerm, pCanonPhase);
    }
    else
    {
        if(DifStartMin>=DifStart0)
            arrangeQuoters_superFast_moreThen5(pInOut, temp, DifStartMin, M[min1], M[(min1+1)%2], 3 - M[(min1+1)%2], 3 - M[min1], iVar, pCanonPerm, pCanonPhase);
        else
        {
            min2 = minTemp3_fast_moreThen5(pInOut, iVar, DifStart0, DifStartMin, 3-M[0], 3-M[1], &DifStart1);  // reuse DifStart1 because DifStart1 = DifStart1=0
            if(DifStart1>DifStartMin)
                arrangeQuoters_superFast_moreThen5(pInOut, temp, DifStart0, M[(min2+1)%2], M[min2], 3 - M[min2], 3 - M[(min2+1)%2], iVar, pCanonPerm, pCanonPhase);
            else
                arrangeQuoters_superFast_moreThen5(pInOut, temp, DifStart0, M[min1], M[(min1+1)%2], 3 - M[(min1+1)%2], 3 - M[min1], iVar, pCanonPerm, pCanonPhase);
        }
    }
}

/////////////////////////////////// for all /////////////////////////////////////////////////////////////////////////////////////////////
inline void minimalInitialFlip_fast_16Vars(word* pInOut, int  nVars, unsigned* pCanonPhase)
{
    word oneWord=1;
    if(  (pInOut[Kit_TruthWordNum_64bit( nVars ) -1]>>63) & oneWord )
    {
        Kit_TruthNot_64bit( pInOut, nVars );
        (* pCanonPhase) ^=(1<<nVars);       
    }

}

// this function finds minimal for all TIED(and tied only) iVars 
//it finds tied vars based on rearranged  Store info - group of tied vars has the same bit count in Store
inline int minimalSwapAndFlipIVar_superFast_all(word* pInOut, int nVars, int nWords, int * pStore, char * pCanonPerm, unsigned* pCanonPhase)
{
    int i;
    word pDuplicate[1024];  
    int bitInfoTemp = pStore[0];
    memcpy(pDuplicate,pInOut,nWords*sizeof(word));
    for(i=0;i<5;i++)
    {
        if(bitInfoTemp == pStore[i+1])
            minimalSwapAndFlipIVar_superFast_lessThen5(pInOut, i, nWords, pCanonPerm, pCanonPhase);
        else
        {
            bitInfoTemp = pStore[i+1];
            continue;
        }
    }
    if(bitInfoTemp == pStore[i+1])
        minimalSwapAndFlipIVar_superFast_iVar5((unsigned*) pInOut, nWords, pCanonPerm, pCanonPhase);
    else    
        bitInfoTemp = pStore[i+1];
    
    for(i=6;i<nVars-1;i++)
    {
        if(bitInfoTemp == pStore[i+1])
            minimalSwapAndFlipIVar_superFast_moreThen5(pInOut, i, nWords, pCanonPerm, pCanonPhase);
        else
        {
            bitInfoTemp = pStore[i+1];
            continue;
        }
    }
    if(memcmp(pInOut,pDuplicate , nWords*sizeof(word)) == 0)
        return 0;
    else
        return 1;
}

inline void luckyCanonicizerS_F_first_16Vars(word* pInOut, int  nVars, int nWords, int * pStore, char * pCanonPerm, unsigned* pCanonPhase)
{
    minimalInitialFlip_fast_16Vars(pInOut, nVars, pCanonPhase);
    while( minimalSwapAndFlipIVar_superFast_all(pInOut, nVars, nWords, pStore, pCanonPerm, pCanonPhase) != 0)
        continue;
}

inline void luckyCanonicizer_final_fast_16Vars(word* pInOut, int  nVars, int nWords, int * pStore, char * pCanonPerm, unsigned* pCanonPhase)
{
//  word pDuplicateLocal[1024]={0};
//  memcpy(pDuplicateLocal,pInOut,nWords*sizeof(word));
    assert( nVars <= 16 );
    assert( nVars > 6 );
    (* pCanonPhase) = Kit_TruthSemiCanonicize_Yasha1( pInOut, nVars, pCanonPerm, pStore );
    luckyCanonicizerS_F_first_16Vars(pInOut, nVars, nWords, pStore, pCanonPerm, pCanonPhase );
//  memcpy(pDuplicate,pInOut,nWords*sizeof(word));
//  assert(!luckyCheck(pDuplicate, pDuplicateLocal, nVars, pCanonPerm, * pCanonPhase));
}

// top-level procedure calling two special cases (nVars <= 6 and nVars <= 16)
int luckyCanonicizer_final_fast( word * pInOut, int nVars, char * pCanonPerm )
{
    int pStore[16];
    unsigned uCanonPhase = 0;
    int nWords = (nVars <= 6) ? 1 : (1 << (nVars - 6));
    if ( nVars <= 6 )
        pInOut[0] = luckyCanonicizer_final_fast_6Vars( pInOut[0], pStore, pCanonPerm, &uCanonPhase );
    else if ( nVars <= 16 )
        luckyCanonicizer_final_fast_16Vars( pInOut, nVars, nWords, pStore, pCanonPerm, &uCanonPhase );
    else assert( 0 );
    return uCanonPhase;
}


ABC_NAMESPACE_IMPL_END




