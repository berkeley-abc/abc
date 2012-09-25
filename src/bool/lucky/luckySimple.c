/**CFile****************************************************************

  FileName    [luckySimple.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Semi-canonical form computation package.]

  Synopsis    [Truth table minimization procedures.]

  Author      [Jake]

  Date        [Started - August 2012]

***********************************************************************/

#include "luckyInt.h"

ABC_NAMESPACE_IMPL_START

static swapInfo* setSwapInfoPtr(int varsN)
{
    int i;
    swapInfo* x = (swapInfo*) malloc(sizeof(swapInfo));
    x->posArray = (varInfo*) malloc (sizeof(varInfo)*(varsN+2));
    x->realArray = (int*) malloc (sizeof(int)*(varsN+2));
    x->varN = varsN;
    x->realArray[0]=varsN+100;
    for(i=1;i<=varsN;i++)
    {
        x->posArray[i].position=i;
        x->posArray[i].direction=-1;
        x->realArray[i]=i;
    }    
    x->realArray[varsN+1]=varsN+10;
    return x;
}


static void freeSwapInfoPtr(swapInfo* x)
{
    free(x->posArray);
    free(x->realArray);
    free(x);
}

int nextSwap(swapInfo* x)
{
    int i,j,temp;
    for(i=x->varN;i>1;i--)
    {
        if( i > x->realArray[x->posArray[i].position + x->posArray[i].direction] )
        {
            x->posArray[i].position = x->posArray[i].position + x->posArray[i].direction;
            temp = x->realArray[x->posArray[i].position];
            x->realArray[x->posArray[i].position] = i; 
            x->realArray[x->posArray[i].position - x->posArray[i].direction] = temp;
            x->posArray[temp].position = x->posArray[i].position - x->posArray[i].direction; 
            for(j=x->varN;j>i;j--)
            {
                x->posArray[j].direction =     x->posArray[j].direction * -1;
            }
            x->positionToSwap1 = x->posArray[temp].position - 1;
            x->positionToSwap2 = x->posArray[i].position - 1;            
            return 1;
        }
        
    }
    return 0;    
}

void fillInSwapArray(permInfo* pi)
{
    int counter=pi->totalSwaps-1;
    swapInfo* x= setSwapInfoPtr(pi->varN);
    while(nextSwap(x)==1)
    {
        if(x->positionToSwap1<x->positionToSwap2)
            pi->swapArray[counter--]=x->positionToSwap1;
        else
            pi->swapArray[counter--]=x->positionToSwap2;
    }
    
    freeSwapInfoPtr(x);    
}
int oneBitPosition(int x, int size)
{
    int i;
    for(i=0;i<size;i++)
        if((x>>i)&1)
            return i;
    return -1;
}
void fillInFlipArray(permInfo* pi)
{
    int i, temp=0, grayNumber;
    for(i=1;i<=pi->totalFlips;i++)
    {
        grayNumber = i^(i>>1);
        pi->flipArray[pi->totalFlips-i]=oneBitPosition(temp^grayNumber, pi->varN);
        temp = grayNumber;        
    }
    
    
}
inline int factorial(int n)
{
    return (n == 1 || n == 0) ? 1 : factorial(n - 1) * n;
}
permInfo* setPermInfoPtr(int var)
{
    permInfo* x;
    x = (permInfo*) malloc(sizeof(permInfo));
    x->flipCtr=0;
    x->varN = var; 
    x->totalFlips=(1<<var)-1;
    x->swapCtr=0;
    x->totalSwaps=factorial(var)-1;
    x->flipArray = (int*) malloc(sizeof(int)*x->totalFlips);
    x->swapArray = (int*) malloc(sizeof(int)*x->totalSwaps);
    fillInSwapArray(x);
    fillInFlipArray(x);
    return x;
}

void freePermInfoPtr(permInfo* x)
{
    free(x->flipArray);
    free(x->swapArray);
    free(x);
}
inline void minWord(word* a, word* b, word* minimal, int nVars)
{
    if(memCompare(a, b, nVars) == -1)
        Kit_TruthCopy_64bit( minimal, a, nVars );
    else
        Kit_TruthCopy_64bit( minimal, b, nVars );
}
inline void minWord3(word* a, word* b, word* minimal, int nVars)
{ 
    if (memCompare(a, b, nVars) <= 0)
    {
        if (memCompare(a, minimal, nVars) < 0) 
            Kit_TruthCopy_64bit( minimal, a, nVars ); 
        else 
            return ;
    }    
    if (memCompare(b, minimal, nVars) <= 0)
        Kit_TruthCopy_64bit( minimal, b, nVars );
}
void simpleMinimal(word* x, word* pAux,word* minimal, permInfo* pi, int nVars)
{
    int i,j=0;
    Kit_TruthCopy_64bit( pAux, x, nVars );
    Kit_TruthNot_64bit( x, nVars );
    
    minWord(x, pAux, minimal, nVars);
    
    for(i=pi->totalSwaps-1;i>=0;i--)
    {
        Kit_TruthSwapAdjacentVars_64bit(x, nVars, pi->swapArray[i]);
        Kit_TruthSwapAdjacentVars_64bit(pAux, nVars, pi->swapArray[i]);
        minWord3(x, pAux, minimal, nVars);
    }
    for(j=pi->totalFlips-1;j>=0;j--)
    {
        Kit_TruthSwapAdjacentVars_64bit(x, nVars, 0);
        Kit_TruthSwapAdjacentVars_64bit(pAux, nVars, 0);
        Kit_TruthChangePhase_64bit(x, nVars, pi->flipArray[j]);
        Kit_TruthChangePhase_64bit(pAux, nVars, pi->flipArray[j]);
        minWord3(x, pAux, minimal, nVars);
        for(i=pi->totalSwaps-1;i>=0;i--)
        {
            Kit_TruthSwapAdjacentVars_64bit(x, nVars, pi->swapArray[i]);
            Kit_TruthSwapAdjacentVars_64bit(pAux, nVars, pi->swapArray[i]);
            minWord3(x, pAux, minimal, nVars);
        }
    } 
    Kit_TruthCopy_64bit( x, minimal, nVars );    
}


ABC_NAMESPACE_IMPL_END
