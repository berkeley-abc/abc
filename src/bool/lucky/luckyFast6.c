/**CFile****************************************************************

  FileName    [luckyFast6.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Semi-canonical form computation package.]

  Synopsis    [Truth table minimization procedures for 6 vars.]

  Author      [Jake]

  Date        [Started - September 2012]

***********************************************************************/

#include "luckyInt.h"

ABC_NAMESPACE_IMPL_START

inline void resetPCanonPermArray_6Vars(char* x)
{
    x[0]='a';
    x[1]='b';
    x[2]='c';
    x[3]='d';
    x[4]='e';
    x[5]='f';
}
inline void resetPCanonPermArray(char* x, int nVars)
{
    int i;
    for(i=0;i<nVars;i++)
        x[i] = 'a'+i;
}

// we need next two functions only for verification of lucky method in debugging mode 
void swapAndFlip(word* pAfter, int nVars, int iVarInPosition, int jVar, char * pCanonPerm, unsigned* pUCanonPhase)
{
    int Temp;
    swap_ij(pAfter, nVars, iVarInPosition, jVar);
    
    Temp = pCanonPerm[iVarInPosition];
    pCanonPerm[iVarInPosition] = pCanonPerm[jVar];
    pCanonPerm[jVar] = Temp;
    
    if ( ((*pUCanonPhase & (1 << iVarInPosition)) > 0) != ((*pUCanonPhase & (1 << jVar)) > 0) )
    {
        *pUCanonPhase ^= (1 << iVarInPosition);
        *pUCanonPhase ^= (1 << jVar);
    }
    if((*pUCanonPhase>>iVarInPosition) & 1)
        Kit_TruthChangePhase_64bit( pAfter, nVars, iVarInPosition );
    
}
int luckyCheck(word* pAfter, word* pBefore, int nVars, char * pCanonPerm, unsigned uCanonPhase)
{
    int i,j;
    char tempChar;
    for(j=0;j<nVars;j++)
    {
        tempChar = 'a'+ j;
        for(i=j;i<nVars;i++)
        {
            if(tempChar != pCanonPerm[i])
                continue;
            swapAndFlip(pAfter , nVars, j, i, pCanonPerm, &uCanonPhase);
            break;
        }
    }
    if((uCanonPhase>>nVars) & 1)
        Kit_TruthNot_64bit(pAfter, nVars );
    if(memcmp(pAfter, pBefore, Kit_TruthWordNum_64bit( nVars )*sizeof(word)) == 0)
        return 0;
    else
        return 1;
}

inline word Abc_allFlip(word x, unsigned* pCanonPhase)
{
    if(  (x>>63) )
    {
        (* pCanonPhase) ^=(1<<6);
        return ~x;
    }
    else 
        return x;
    
}

inline unsigned adjustInfoAfterSwap(char* pCanonPerm, unsigned uCanonPhase, int iVar, unsigned info)
{   
    if(info<4)
        return (uCanonPhase ^= (info << iVar));
    else
    {
        char temp;
        uCanonPhase ^= ((info-4) << iVar);
        temp=pCanonPerm[iVar];
        pCanonPerm[iVar]=pCanonPerm[iVar+1];
        pCanonPerm[iVar+1]=temp;
        if ( ((uCanonPhase & (1 << iVar)) > 0) != ((uCanonPhase & (1 << (iVar+1))) > 0) )
        {
            uCanonPhase ^= (1 << iVar);
            uCanonPhase ^= (1 << (iVar+1));
        }
        return uCanonPhase; 
    }


}

inline word Extra_Truth6SwapAdjacent( word t, int iVar )
{
    // variable swapping code
    static word PMasks[5][3] = {
        { 0x9999999999999999, 0x2222222222222222, 0x4444444444444444 },
        { 0xC3C3C3C3C3C3C3C3, 0x0C0C0C0C0C0C0C0C, 0x3030303030303030 },
        { 0xF00FF00FF00FF00F, 0x00F000F000F000F0, 0x0F000F000F000F00 },
        { 0xFF0000FFFF0000FF, 0x0000FF000000FF00, 0x00FF000000FF0000 },
        { 0xFFFF00000000FFFF, 0x00000000FFFF0000, 0x0000FFFF00000000 }
    };
    assert( iVar < 5 );
    return (t & PMasks[iVar][0]) | ((t & PMasks[iVar][1]) << (1 << iVar)) | ((t & PMasks[iVar][2]) >> (1 << iVar));
}
inline word Extra_Truth6ChangePhase( word t, int iVar)
{
    // elementary truth tables
    static word Truth6[6] = {
        0xAAAAAAAAAAAAAAAA,
            0xCCCCCCCCCCCCCCCC,
            0xF0F0F0F0F0F0F0F0,
            0xFF00FF00FF00FF00,
            0xFFFF0000FFFF0000,
            0xFFFFFFFF00000000
    };
    assert( iVar < 6 );
    return ((t & ~Truth6[iVar]) << (1 << iVar)) | ((t & Truth6[iVar]) >> (1 << iVar));
}

inline word Extra_Truth6MinimumRoundOne( word t, int iVar, char* pCanonPerm, unsigned* pCanonPhase )
{
    word tCur, tMin = t; // ab 
    unsigned info =0;
    assert( iVar >= 0 && iVar < 5 );
    
    tCur = Extra_Truth6ChangePhase( t, iVar );    // !a b
    if(tCur<tMin)
    {
        info = 1;
        tMin = tCur;
    }
    tCur = Extra_Truth6ChangePhase( t, iVar+1 );  // a !b
    if(tCur<tMin)
    {
        info = 2;
        tMin = tCur;
    }
    tCur = Extra_Truth6ChangePhase( tCur, iVar ); // !a !b
    if(tCur<tMin)
    {
        info = 3;
        tMin = tCur;
    }
    
    t    = Extra_Truth6SwapAdjacent( t, iVar );   // b a
    if(t<tMin)
    {
        info = 4;
        tMin = t;
    }
    
    tCur = Extra_Truth6ChangePhase( t, iVar );    // !b a
    if(tCur<tMin)
    {
        info = 6;
        tMin = tCur;
    }
    tCur = Extra_Truth6ChangePhase( t, iVar+1 );  // b !a
    if(tCur<tMin)
    {
        info = 5;
        tMin = tCur;
    }
    tCur = Extra_Truth6ChangePhase( tCur, iVar ); // !b !a
    if(tCur<tMin)
    {
        (* pCanonPhase) = adjustInfoAfterSwap(pCanonPerm, * pCanonPhase, iVar, 7);
        return tCur;
    }
    else
    {
        (* pCanonPhase) = adjustInfoAfterSwap(pCanonPerm, * pCanonPhase, iVar, info);
        return tMin;
    }
}
// this function finds minimal for all TIED(and tied only) iVars 
//it finds tied vars based on rearranged  Store info - group of tied vars has the same bit count in Store
inline word Extra_Truth6MinimumRoundMany( word t, int* pStore, char* pCanonPerm, unsigned* pCanonPhase )
{
    int i, bitInfoTemp;
    word tMin0, tMin;
    tMin=Abc_allFlip(t, pCanonPhase);
    do
    {
        bitInfoTemp = pStore[0];
        tMin0 = tMin;
        for ( i = 0; i < 5; i++ )
        {
            if(bitInfoTemp == pStore[i+1])          
                tMin = Extra_Truth6MinimumRoundOne( tMin, i, pCanonPerm, pCanonPhase );         
            else
                bitInfoTemp = pStore[i+1];
        } 
        
    }while ( tMin0 != tMin );
    return tMin;
}


inline word luckyCanonicizer_final_fast_6Vars(word InOut, int* pStore, char* pCanonPerm, unsigned* pCanonPhase )
{
//  word temp, duplicat = InOut;
    (* pCanonPhase) = Kit_TruthSemiCanonicize_Yasha1( &InOut, 6, pCanonPerm, pStore);
//  InOut = Extra_Truth6MinimumRoundMany(InOut, pStore, pCanonPhase, pCanonPerm );
//      temp = InOut;
//      assert(!luckyCheck(&temp, &duplicat, 6, pCanonPerm, * pCanonPhase));
//      return(InOut); 
    return Extra_Truth6MinimumRoundMany(InOut, pStore, pCanonPerm, pCanonPhase );
    
}

ABC_NAMESPACE_IMPL_END
