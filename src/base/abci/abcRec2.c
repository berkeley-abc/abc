/**CFile****************************************************************

  FileName    [abcRec2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Record of semi-canonical AIG subgraphs.]

  Author      [Allan Yang, Alan Mishchenko]
  
  Affiliation [Fudan University in Shanghai, UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "map/if/if.h"
#include "bool/kit/kit.h"
#include "aig/gia/giaAig.h"
#include "misc/vec/vecMem.h"

ABC_NAMESPACE_IMPL_START

//#define LibOut

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define  IF_BIG_CHAR 120
#define  REC_EMPTY_ID -1

typedef struct Abc_ManRec_t_2 Abc_ManRec_t2;
typedef struct Rec_Obj_t_2 Rec_Obj_t2;

typedef enum {
    REC_ERROR,                  //0: error
    REC_SMALL,                  //1: smaller than
    REC_EQUAL,                  //2: equal with
    REC_BIG,                    //3: bigger than    
    REC_DOMINANCE,              //4: dominance
    REC_BEDOMINANCED            //5: be dominated
} Abc_LookUpStatus_t2;

struct Rec_Obj_t_2
{
    int pNext;                  // link to the next structure of the same functional class
    int pCopy;                  // link to the next functional class in the same bucket
    int truthID;                // structure's Truth ID
    int nFrequency;             // appear times of this functional class among benchmarks
    unsigned char cost;         // structure's cost
    char pinToPinDelay[0];      // structure's pin-to-pin delay
};

struct Abc_ManRec_t_2
{
    Gia_Man_t *       pGia;                     // the record
    Vec_Str_t *       vInputs;                  // the input number of nodes
    Vec_Ptr_t *       vTtElems;                 // the elementary truth tables
//    Vec_Ptr_t *       vTtNodes;                 // the node truth tables
//    Mem_Fixed_t *     pMmTruth;                 // memory manager for truth tables
    Vec_Mem_t *       vTtMem;                   // memory for truth tables of primary outputs
    int *             pBins;                    // hash table mapping truth tables into nodes
    int               nBins;                    // the number of allocated bins
    int               nVars;                    // the number of variables
    int               nVarsInit;                // the number of variables requested initially
    int               nWords;                   // the number of TT words
    int               nCuts;                    // the max number of cuts to use
    //Mem_Fixed_t *     pMemObj;                  // memory manager for Rec objects
    int               recObjSize;               // size for one Rec object
    int               fTrim;                    // filter the library or not.
    char *            pRecObjs;
    int               nRecObjs;
    int               nRecObjsAlloc;
    // temporaries
    int *             pBytes;                   // temporary storage for minterms
    int *             pMints;                   // temporary storage for minterm counters
    unsigned *        pTemp1;                   // temporary truth table
    unsigned *        pTemp2;                   // temporary truth table
    Vec_Ptr_t *       vNodes;                   // the temporary nodes
    Vec_Ptr_t *       vTtTemps;                 // the truth tables for the internal nodes of the cut
    Vec_Ptr_t *       vLabels;                  // temporary storage for AIG node labels
    Vec_Int_t *       vUselessPos;
    // statistics
    int               nTried;                   // the number of cuts tried
    int               nFilterSize;              // the number of same structures
    int               nFilterRedund;            // the number of same structures
    int               nFilterVolume;            // the number of same structures
    int               nFilterTruth;             // the number of same structures
    int               nFilterError;             // the number of same structures
    int               nFilterSame;              // the number of same structures
    int               nAdded;                   // the number of subgraphs added
    int               nAddedFuncs;              // the number of functions added
    int               nIfMapError;
    int               nTrimed;                  // the number of structures filtered
    // rewriting
    int               nFunsFound;               // the found functions
    int               nFunsNotFound;            // the missing functions
    int               nFunsTried;
    int               nFunsFilteredBysupport;   // the function filtered when rewriting because not all supports are in use.
    int               nFunsDelayComput;         // the times delay computed, just for statistics
    int               nNoBetter;                // the number of functions found but no better than the current structures.
    // rewriting runtime
    int               timeIfTotal;              // time used on the whole process of rewriting a structure.
    int               timeIfComputDelay;        // time used on the structure's delay computation.
    int               timeIfCanonicize;         // time used on canonicize the function
    int               timeIfDerive;             // time used on derive the final network;
    int               timeIfCopmutCur;          // time used on compute the current structures info
    int               timeIfOther;              // time used on other things
    // record runtime
    int               timeTrim;                 // the runtime to filter the library
    int               timeCollect;              // the runtime to collect the node of a structure.
    int               timeTruth;                // the runtime to compute truth table.
    int               timeCanon;                // the runtime to canonicize
    int               timeInsert;               // the runtime to insert a structure.
    int               timeBuild;                // the runtime to build a new structure in the library.
    int               timeMerge;                // the runtime to merge libraries;
    int               timeReHash;                // the runtime to resize the hash table.
    int               timeOther;                // the runtime of other
    int               timeTotal;                // the runtime to total.
};

static Abc_ManRec_t2 * s_pMan = NULL;

static inline void Abc_ObjSetMax2( Vec_Str_t * p, Gia_Man_t * pGia, Gia_Obj_t * pObj, char Value )  { Vec_StrWriteEntry(p, Gia_ObjId(pGia, pObj), Value); }
//static inline void Abc_ObjClearMax( Gia_Obj_t * pObj )          { pObj->Value = (pObj->Value & 0xff); }
static inline int  Abc_ObjGetMax2( Vec_Str_t * p, Gia_Man_t * pGia, Gia_Obj_t * pObj )              { return Vec_StrEntry(p, Gia_ObjId(pGia, pObj)); }
static inline int   Rec_ObjID(Abc_ManRec_t2 *p, Rec_Obj_t2 * pRecObj)                                  
{   char * pObj = (char *)pRecObj;
    assert(p->pRecObjs <= pObj && pObj < p->pRecObjs + p->nRecObjs * p->recObjSize); 
    return (pObj - p->pRecObjs)/p->recObjSize;
}
static inline Rec_Obj_t2 * Rec_Obj(Abc_ManRec_t2 *p, int v)
{
    assert( v < p->nRecObjs ); 
    return (Rec_Obj_t2 *)(p->pRecObjs + v * p->recObjSize);
}

static inline unsigned * Rec_MemReadEntry( Abc_ManRec_t2 * p, int i )                    { return (unsigned *)Vec_MemReadEntry( p->vTtMem, i ); }
static inline void       Rec_MemSetEntry( Abc_ManRec_t2 * p, int i, unsigned * pEntry )  { Vec_MemSetEntry( p->vTtMem, i, (word *)pEntry );     }

/**Function*************************************************************

  Synopsis    [Alloc the Rec object from its manger.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Rec_AppendObj( Abc_ManRec_t2 * p, Rec_Obj_t2 ** pObj )  
{ 
    //Rec_Obj_t2 * pObj;
    int hasRealloced = 0;
    if ( p->nRecObjs == p->nRecObjsAlloc )
    {
        assert( p->nRecObjs > 0 );
        p->pRecObjs = realloc(p->pRecObjs, 2 * p->nRecObjsAlloc * p->recObjSize );
        memset( p->pRecObjs + p->nRecObjsAlloc * p->recObjSize, 0, p->recObjSize * p->nRecObjsAlloc );
        p->nRecObjsAlloc *= 2;
        hasRealloced = 1;
    }
    *pObj = Rec_Obj( p, p->nRecObjs++ );
    (*pObj)->pCopy = REC_EMPTY_ID;
    (*pObj)->pNext = REC_EMPTY_ID;
    return hasRealloced;
}


/**Function*************************************************************

  Synopsis    [set the property of a Rec object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rec_ObjSet2(Abc_ManRec_t2* p, Rec_Obj_t2* pRecObj, char* newDelay, unsigned char cost, int nVar)
{
    int i;
    //pRecObj->obj = pObj;
    //pRecObj->Id = Gia_ObjId(p->pGia, pObj);
    pRecObj->cost = cost;
    for (i = 0; i < nVar; i++)
        pRecObj->pinToPinDelay[i] = newDelay[i]; 
    return Rec_ObjID(p, pRecObj);
}

/**Function*************************************************************

  Synopsis    [Set input number for every structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecMarkInputs(Abc_ManRec_t2 * p, Gia_Man_t * pGia)
{
    Gia_Obj_t * pObj;
    int i;
    Vec_Str_t * pStr = p->vInputs;
     if (Vec_StrSize(pStr) < Gia_ManObjNum(pGia))
         Vec_StrFillExtra( pStr, Gia_ManObjNum(pGia), 0 );

    
    Gia_ManForEachPi( pGia, pObj, i )
        Abc_ObjSetMax2(pStr, pGia, pObj, (char)(i+1) );
    Gia_ManForEachAnd( pGia, pObj, i )
        Abc_ObjSetMax2(pStr, pGia, pObj, (char)Abc_MaxInt( Abc_ObjGetMax2(pStr, pGia, Gia_ObjFanin0(pObj)), Abc_ObjGetMax2(pStr, pGia, Gia_ObjFanin1(pObj)) ) );
}

/**Function*************************************************************

  Synopsis    [Get the Gia_Obj_t.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Obj_t * Abc_NtkRecGetObj(int Rec_ID)
{
    Gia_Man_t * p = s_pMan->pGia;
    Gia_Obj_t * pPO = Gia_ManPo(p, Rec_ID);
    return Gia_ObjFanin0(pPO);
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecIsRunning2()
{
    return s_pMan != NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecIsInTrimMode2()
{
    return (s_pMan != NULL && s_pMan->fTrim);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abc_NtkRecGetGia()
{
    return s_pMan->pGia;
}

/**Function*************************************************************

  Synopsis    [Set frequency.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

static inline void Abc_NtkRecFrequencyInc(int entry)     
{   
    // the hit number of this functional class increased
    if (entry != REC_EMPTY_ID && Rec_Obj(s_pMan, entry)->nFrequency < 0x7fffffff)
        Rec_Obj(s_pMan, entry)->nFrequency += 1;
}

/**Function*************************************************************

  Synopsis    [stretch the truthtable to have more input variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If_CutTruthStretch(unsigned* pInOut, int nVarS, int nVarB)
{
    int w, i;
    int step = Kit_TruthWordNum(nVarS);
    int nWords = Kit_TruthWordNum(nVarB);
    assert(step <= nWords);
    if (step == nWords)
        return;
    for (w = 0; w <nWords; w += step)
        for (i = 0; i < step; i++)
            pInOut[w + i] = pInOut[i];              
}

/**Function*************************************************************

  Synopsis    [Compare delay profile of two structures.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

static Abc_LookUpStatus_t2 ABC_NtkRecDelayCompare(char* delayFromStruct, char* delayFromTable, int nVar)
{
    int i, bigThan = 0, smallThan = 0, equal = 1, dominace = 1, beDominaced = 1;
    for (i = 0; i < nVar; i++)
    {
        if(delayFromStruct[i] < delayFromTable[i])
        {
            equal = 0;
            beDominaced = 0;
            if(bigThan == 0)
                smallThan = 1;
        }
        else if (delayFromStruct[i] > delayFromTable[i])
        {
            equal = 0;
            dominace = 0;
            if (smallThan == 0)
                bigThan = 1;        
        }   
    }
    if(equal)
        return REC_EQUAL;
    else if(dominace)
        return REC_DOMINANCE;
    else if(beDominaced)
        return REC_BEDOMINANCED;
     if(bigThan)
        return REC_BIG;
    else if(smallThan)
        return REC_SMALL;
    else
        return REC_SMALL;
}



/**Function*************************************************************

  Synopsis    [Delete a useless structure in the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecDeleteSubGragh2(Gia_Obj_t* pObj)
{
    //assert(pObj->fMark0 == 0);
    //pObj->fMark0 = 1;
    Vec_IntPush(s_pMan->vUselessPos, Gia_ObjId(s_pMan->pGia, pObj));
    s_pMan->nTrimed++;
}


/**Function*************************************************************

  Synopsis    [Mark NonDangling nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecMarkNonDanglingNodes_Rec(Gia_Man_t * pGia, Gia_Obj_t * pRoot)
{
    Gia_Obj_t * pFanin0, * pFanin1;
    //assert(pRoot->fMark0 == 0);
    pRoot->fMark0 = 1;
    pFanin0 = Gia_ObjFanin0(pRoot);
    pFanin1 = Gia_ObjFanin1(pRoot);
    if (pFanin0->fMark0 == 0)
    {
        if(Gia_ObjIsPi(pGia, pFanin0))
            pFanin0->fMark0 = 1;
        else
            Abc_NtkRecMarkNonDanglingNodes_Rec(pGia, pFanin0);   
    }
    if (pFanin1->fMark0 == 0)
    {
        if(Gia_ObjIsPi(pGia, pFanin1))
            pFanin1->fMark0 = 1;
        else
            Abc_NtkRecMarkNonDanglingNodes_Rec(pGia, pFanin1);   
    }   
}

/**Function*************************************************************

  Synopsis    [Mark Dangling nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecMarkCompl(Gia_Man_t * pGia)
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj1(pGia, pObj,i)
        pObj->fMark0 = !pObj->fMark0;
}

/**Function*************************************************************

  Synopsis    [Mark Dangling nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecMarkNonDanglingNodes(Gia_Man_t * pGia)
{
    Gia_Obj_t * pObj, * pFanin;
    int i;
    int Id;
    int counter = 0;
    Gia_ManForEachObj(pGia, pObj, i)
    {
        if (pObj->fMark1 == 1)
        {
            pObj->fMark1 = 0;
        }
        if (pObj->fMark0 == 1)
        {
            pObj->fMark0 = 0;
        }     
    }

    Vec_IntForEachEntry(s_pMan->vUselessPos, Id, i)
    {
        pObj = Gia_ManObj(pGia, Id);
        pObj->fMark1 = 1;
    }
    Gia_ManForEachPo(pGia, pObj,i)
    {
        pFanin = Gia_ObjFanin0(pObj);      
        if (!pFanin->fMark1)
        {
            pObj->fMark0 = 1;
            Abc_NtkRecMarkNonDanglingNodes_Rec(pGia, pFanin);
        }
    }

    Vec_IntClear(s_pMan->vUselessPos);
    Abc_NtkRecMarkCompl(pGia);
}

/**Function*************************************************************

  Synopsis    [Duplicates non-dangling nodes and POs driven by constants.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abc_NtkDupWithoutDangling2( Gia_Man_t * pGia )
{
    Gia_Man_t * pGiaNew; 
    Abc_NtkRecMarkNonDanglingNodes(pGia);
    pGiaNew = Gia_ManDupMarked(pGia);
    return pGiaNew;
}


/**Function*************************************************************

  Synopsis    [Filter the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecFilter2(int nLimit)
{
    int  previous = REC_EMPTY_ID,  entry = REC_EMPTY_ID,  pTemp;
    int i;
    Gia_Man_t * pGia = s_pMan->pGia, *newPGia;
    //int time = clock();
    Abc_ManRec_t2 *p = s_pMan;
//    Gia_Obj_t * pObj;
    char fileName[256];
    if (nLimit > 0)
    {
        for ( i = 0; i < s_pMan->nBins; i++ )
        {
            previous = REC_EMPTY_ID;
            for ( entry = s_pMan->pBins[i]; entry != REC_EMPTY_ID; entry = Rec_Obj(p, entry)->pCopy)
            {
                assert(Rec_Obj(p, entry)->nFrequency != 0);
                // only filter the functional classed with frequency less than nLimit.
                if(Rec_Obj(p, entry)->nFrequency > nLimit)
                {
                    previous = entry;
                    continue;
                }
                if(previous == REC_EMPTY_ID)
                {
                    s_pMan->pBins[i] = Rec_Obj(p, entry)->pCopy;
                    previous = REC_EMPTY_ID;
                }
                else
                    Rec_Obj(p, previous)->pCopy = Rec_Obj(p, entry)->pCopy;

                s_pMan->nAddedFuncs--;
                //delete all the subgragh.
                for ( pTemp = entry; pTemp != REC_EMPTY_ID;)
                {       
                    s_pMan->nAdded--;
                    Abc_NtkRecDeleteSubGragh2(Abc_NtkRecGetObj(pTemp));
                    pTemp = Rec_Obj(p, pTemp)->pNext;
                    //Mem_FixedEntryRecycle(s_pMan->pMemObj, (char *)pTemp);
                    //pTemp = pNextOne;
                }
            }
        }
    }

    // remove dangling nodes and POs driven by constants
    newPGia = Abc_NtkDupWithoutDangling2(pGia);
    sprintf( fileName, "RecLib%d_Filtered%d.aig", p->nVars, nLimit);
    Gia_WriteAiger( newPGia, fileName, 0, 0 );
    Abc_Print(1, "Library %s was written.");
    //Gia_ManHashStop(newPGia);
    Gia_ManStop(newPGia); 
    Abc_NtkRecStop2();
    Abc_Print(1, "Record stopped.");
    // collect runtime stats
    //s_pMan->timeTrim += clock() - time;
   //s_pMan->timeTotal += clock() - time;
}


/**Function*************************************************************

  Synopsis    [Returns the hash key.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Abc_NtkRecTableHash( unsigned * pTruth, int nVars, int nBins, int * pPrimes )
{
    int i, nWords = Kit_TruthWordNum( nVars );
    unsigned uHash = 0;
    for ( i = 0; i < nWords; i++ )
        uHash ^= pTruth[i] * pPrimes[i & 0x7];
    return uHash % nBins;
}

/**Function*************************************************************

  Synopsis    [Returns the given record.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int * Abc_NtkRecTableLookup2(Abc_ManRec_t2* p,  int * pBins, int nBins, unsigned * pTruth, int nVars )
{
    static int s_Primes[10] = { 1291, 1699, 2357, 4177, 5147, 5647, 6343, 7103, 7873, 8147 };
    int * ppSpot,  pEntry;
    ppSpot = pBins + Abc_NtkRecTableHash( pTruth, nVars, nBins, s_Primes );
    for ( pEntry = *ppSpot; pEntry != REC_EMPTY_ID; ppSpot = &(Rec_Obj(p,pEntry)->pCopy), pEntry = Rec_Obj(p,pEntry)->pCopy )
//        if ( Kit_TruthIsEqualWithPhase((unsigned *)Vec_PtrEntry(p->vTtNodes, pEntry), pTruth, nVars) )
        if ( Kit_TruthIsEqualWithPhase( Rec_MemReadEntry(p, Rec_Obj(p, pEntry)->truthID), pTruth, nVars) )
            return ppSpot;
    return ppSpot;
}

/**Function*************************************************************

  Synopsis    [Resize the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_NtkRecResizeHash2(Abc_ManRec_t2* p)
{
    int * pBinsNew, *ppSpot;
    int pEntry, pTemp;
    int nBinsNew, Counter, i;
    int clk = clock();
    // get the new table size
    nBinsNew = Cudd_Prime( 2 * p->nBins ); 
    printf("Hash table resize from %d to %d.\n", p->nBins, nBinsNew);
    // allocate a new array
    pBinsNew = ABC_ALLOC( int, nBinsNew );
    memset( pBinsNew, -1, sizeof(int *) * nBinsNew );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < p->nBins; i++ )
        for ( pEntry = p->pBins[i]; pEntry != REC_EMPTY_ID;)
        {          
            pTemp = Rec_Obj(p, pEntry)->pCopy;
//            ppSpot = Abc_NtkRecTableLookup2(p, pBinsNew, nBinsNew, (unsigned *)Vec_PtrEntry(p->vTtNodes, pEntry), p->nVars);
            ppSpot = Abc_NtkRecTableLookup2(p, pBinsNew, nBinsNew, Rec_MemReadEntry(p, Rec_Obj(p, pEntry)->truthID), p->nVars);
            assert(*ppSpot == REC_EMPTY_ID);
            *ppSpot = pEntry;
            Rec_Obj(p, pEntry)->pCopy = REC_EMPTY_ID;
            pEntry = pTemp;
            Counter++;
        }
        assert( Counter == p->nAddedFuncs);
        ABC_FREE( p->pBins );
        p->pBins = pBinsNew;
        p->nBins = nBinsNew;
        p->timeReHash += clock() - clk;
        p->timeTotal += clock() - clk;

}

/**Function*************************************************************

  Synopsis    [Compute area of the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned char Abc_NtkRecAreaAndMark_rec(Gia_Obj_t* pObj)
{
    unsigned char Area0, Area1, Area;
    pObj = Gia_Regular(pObj);
    if(Gia_ObjIsCi(pObj) || pObj->fMark0 == 1)
        return 0;
    Area0 = Abc_NtkRecAreaAndMark_rec(Gia_ObjFanin0(pObj));
    Area1 = Abc_NtkRecAreaAndMark_rec(Gia_ObjFanin1(pObj));
    Area = Area1 + Area0 + 1;
    assert(Area <= 255);
    pObj->fMark0 = 1;
    return Area;
}

/**Function*************************************************************

  Synopsis    [Compute area of the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_NtkRecAreaUnMark_rec(Gia_Obj_t* pObj)
{
    pObj = Gia_Regular(pObj);
    if ( Gia_ObjIsCi(pObj) || pObj->fMark0 == 0 )
        return;
    Abc_NtkRecAreaUnMark_rec( Gia_ObjFanin0(pObj) ); 
    Abc_NtkRecAreaUnMark_rec( Gia_ObjFanin1(pObj) );
    assert( pObj->fMark0 ); // loop detection
    pObj->fMark0 = 0;
}

/**Function*************************************************************

  Synopsis    [Compute area of the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned char Abc_NtkRecArea2(Gia_Obj_t* pObj)
{
    unsigned char area;
    area = Abc_NtkRecAreaAndMark_rec(pObj);
    Abc_NtkRecAreaUnMark_rec(pObj);
    return area;
}

/**Function*************************************************************

  Synopsis    [Compute pin-to-pin delay of the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char If_CutDepthRecComput_rec2(Gia_Obj_t* pObj, int iLeaf)
{
    char Depth0, Depth1, Depth;
    pObj = Gia_Regular(pObj);
    if(Gia_ObjId(s_pMan->pGia, pObj) == iLeaf)
        return 0;
    if(Gia_ObjIsCi(pObj))
        return -IF_BIG_CHAR;
    Depth0 = If_CutDepthRecComput_rec2(Gia_ObjFanin0(pObj), iLeaf);
    Depth1 = If_CutDepthRecComput_rec2(Gia_ObjFanin1(pObj), iLeaf);
    Depth = Abc_MaxInt(Depth0, Depth1);
    Depth = (Depth == -IF_BIG_CHAR) ? -IF_BIG_CHAR : Depth + 1;
    assert(Depth <= 127);
    return Depth;
}

/**Function*************************************************************

  Synopsis    [Check if the structure is dominant or not.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int ABC_NtkRecIsDominant(char* delayFromStruct, char* delayFromTable, int nVar)
{
    int i;
    for (i = 0; i < nVar; i++)
    {
        if(delayFromStruct[i] > delayFromTable[i])
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Sweep the dominated structures.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_NtkRecSweepDominance(Abc_ManRec_t2* p, int previous, int current, char * delayFromStruct, int nVars)
{
    Gia_Obj_t* pObj;
    while(current != REC_EMPTY_ID)
    {
        if (ABC_NtkRecIsDominant(delayFromStruct, Rec_Obj(p, current)->pinToPinDelay, nVars))
        {
            pObj = Abc_NtkRecGetObj(current);
            Rec_Obj(p, previous)->pNext = Rec_Obj(p, current)->pNext;
            //current->pNext = NULL;
            //Mem_FixedEntryRecycle(p->pMemObj, (char *)current);
            current = Rec_Obj(p, previous)->pNext;
            p->nAdded--;
            // if filter the library is needed, then point the PO to a constant.
            Abc_NtkRecDeleteSubGragh2(pObj);
        }
        else
        {
            previous = current;
            current = Rec_Obj(p, current)->pNext;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Insert a structure into the look up table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecReplaceCurrentEntry(int previous, int * current, int entry, int * ppSpot)
{
    Abc_ManRec_t2 * p = s_pMan;
    Rec_Obj(p,entry)->pCopy =  Rec_Obj(p, *current)->pCopy;
    Rec_Obj(p,entry)->pNext = Rec_Obj(p, *current)->pNext;
    if (previous == REC_EMPTY_ID)
    {
        *ppSpot = entry;
        Rec_Obj(p,entry)->nFrequency = Rec_Obj(p, *current)->nFrequency;
    }
    else
    {
        Rec_Obj(p,previous)->pNext = entry;
    }
    *current = entry;
    
}

/**Function*************************************************************

  Synopsis    [Insert a structure into the look up table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecInsertToLookUpTable2(Abc_ManRec_t2* p, int* ppSpot, Gia_Obj_t* pPO, int nVars, unsigned * pTruth, int fTrim)
{
    char delayFromStruct[16];
    int i, hasRealloced = 0;  
    Gia_Obj_t* pLeaf, *pObj = Gia_ObjFanin0(pPO);
    int entry, previous = REC_EMPTY_ID, current = * ppSpot;
    unsigned char costFromStruct = Abc_NtkRecArea2(pObj);
    Abc_LookUpStatus_t2 result;
    Rec_Obj_t2 * pRecObj;
    assert( nVars > 0 );
    for (i = 0; i < nVars; i++)
    {
        pLeaf = Gia_ManPi( p->pGia,  i);
        pLeaf =Gia_Regular(pLeaf);
        delayFromStruct[i] = If_CutDepthRecComput_rec2(pObj, Gia_ObjId(p->pGia, pLeaf));
    }
    hasRealloced = Rec_AppendObj(p, &pRecObj);
    if(hasRealloced)
//        ppSpot = Abc_NtkRecTableLookup2(p, p->pBins, p->nBins, (unsigned *)Vec_PtrEntry( p->vTtNodes, Gia_ObjCioId(pPO)), p->nVars );
        ppSpot = Abc_NtkRecTableLookup2(p, p->pBins, p->nBins, pTruth, p->nVars );
    assert(Rec_ObjID(p, pRecObj) == Gia_ObjCioId(pPO));
    if (current == REC_EMPTY_ID)
    {
        pRecObj->truthID = p->nAddedFuncs;
        Rec_MemSetEntry( p, pRecObj->truthID, pTruth);
    }
    else
        pRecObj->truthID = Rec_Obj(p, current)->truthID;
    

    if(fTrim)
    {       
        while(1)
        {
            if (current == REC_EMPTY_ID)
            {
                p->nAdded++;
                entry = Rec_ObjSet2(p, pRecObj, delayFromStruct, costFromStruct, nVars);          
                if(previous != REC_EMPTY_ID)
                {
                    Rec_Obj(p, previous)->pNext = entry;
                    //previous->pNext = entry;
                }
                else
                {
                    // new functional class found
                    p->nAddedFuncs++;
                    *ppSpot = entry;
                    Rec_Obj(p, entry)->nFrequency = 1;
                }
                break;
            }
            result = ABC_NtkRecDelayCompare(delayFromStruct, Rec_Obj(p, current)->pinToPinDelay, nVars);    
            if(result == REC_EQUAL)
            {
                // when delay profile is equal, replace only if it has smaller cost.
                if(costFromStruct < (Rec_Obj(p, current)->cost))
                {   
                    Abc_NtkRecDeleteSubGragh2(Abc_NtkRecGetObj(current));
                    entry = Rec_ObjSet2(p, pRecObj, delayFromStruct, costFromStruct, nVars);
                    Abc_NtkRecReplaceCurrentEntry(previous, &current, entry, ppSpot);

                }
                else
                    Abc_NtkRecDeleteSubGragh2(pObj);
                break;
            }
            // when the new structure can dominate others, sweep them out of the library, delete them if required.
            else if(result == REC_DOMINANCE)
            {
                Abc_NtkRecDeleteSubGragh2(Abc_NtkRecGetObj(current));
                entry = Rec_ObjSet2(p, pRecObj, delayFromStruct, costFromStruct, nVars);
                Abc_NtkRecReplaceCurrentEntry(previous, &current, entry, ppSpot);
                Abc_NtkRecSweepDominance(p,current,Rec_Obj(p, current)->pNext,delayFromStruct, nVars);       
                break;
            }
            // when the new structure is domianted by an existed one, don't store it.
            else if (result == REC_BEDOMINANCED)
            {
                Abc_NtkRecDeleteSubGragh2(pObj);
                break;
            }
            // when the new structure's delay profile is big than the current, test the next one
            else if (result == REC_BIG)
            {
                previous = current;
                current = Rec_Obj(p, current)->pNext;
            }
            // insert the new structure to the right position, sweep the ones it can dominate.
            else if (result == REC_SMALL)
            {
                p->nAdded++;
                entry = Rec_ObjSet2(p, pRecObj, delayFromStruct, costFromStruct, nVars);  
                if(previous != REC_EMPTY_ID)
                {
                    Rec_Obj(p, previous)->pNext = entry;
                    Rec_Obj(p, entry)->pNext = current;
                }
                else
                {
                    Rec_Obj(p, entry)->pNext = current;
                    Rec_Obj(p, entry)->pCopy = Rec_Obj(p, *ppSpot)->pCopy;
                    Rec_Obj(p, entry)->nFrequency = Rec_Obj(p, *ppSpot)->nFrequency;
                    Rec_Obj(p, *ppSpot)->pCopy = REC_EMPTY_ID;
                    Rec_Obj(p, *ppSpot)->nFrequency = 0;
                    *ppSpot = entry;
                }
                Abc_NtkRecSweepDominance(p,current,Rec_Obj(p, current)->pNext,delayFromStruct, nVars);           
                break;
            }
            else
                assert(0);      
        }
    }
    else
    {
        entry = Rec_ObjSet2(p, pRecObj, delayFromStruct, costFromStruct, nVars);
        if (current == REC_EMPTY_ID)
        {
            p->nAdded++;
            p->nAddedFuncs++;
            *ppSpot = entry;
            Rec_Obj(p, entry)->nFrequency = 1;
        }
        else
        {
            p->nAdded++;
            Rec_Obj(p, entry)->pNext = Rec_Obj(p, *ppSpot)->pNext;
            Rec_Obj(p, *ppSpot)->pNext = entry;
        }
    }
}


/*
int Abc_NtkRecComputeTruth2( Gia_Obj_t * pObj, Vec_Ptr_t * vTtNodes, int nVars )
{
    unsigned * pTruth, * pTruth0, * pTruth1;
    //int RetValue;
    Gia_Man_t *pGia = s_pMan->pGia;
    Gia_Obj_t *pFanin0, *pFanin1;
    pFanin0 = Gia_ObjFanin0(pObj);
    pFanin1 = Gia_ObjFanin1(pObj);
    assert( Gia_ObjIsAnd(pObj) );
    pTruth  = (unsigned *)Vec_PtrEntry( vTtNodes, Gia_ObjId(pGia, pObj) );
    pTruth0 = (unsigned *)Vec_PtrEntry( vTtNodes, Gia_ObjId(pGia, pFanin0) );
    pTruth1 = (unsigned *)Vec_PtrEntry( vTtNodes, Gia_ObjId(pGia, pFanin1) );
    Kit_TruthAndPhase( pTruth, pTruth0, pTruth1, nVars, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj) );   
    //assert((pTruth[0] & 1) == pObj->fPhase )
    //RetValue = ((pTruth[0] & 1) == pObj->fPhase);
    return 1;
}
*/
void Abc_NtkRecStart2( Gia_Man_t * pGia, int nVars, int nCuts, int fTrim )
{
    Abc_ManRec_t2 * p;
    Gia_Obj_t * pObj, *pFanin;
    int * ppSpot;
    unsigned * pTruth;
    int i, j = 0;
    int clkTotal = clock(), clk, timeInsert;

    assert( s_pMan == NULL );
    if ( pGia == NULL )
    {
        assert( nVars > 2 && nVars <= 16 );
        pGia = Gia_ManStart( 1 << 16 );
        pGia->pName = Extra_UtilStrsav( "record" );
       
        
    }
    else
    {
        if ( Gia_ManCountChoices(pGia) > 0 )
        {
            printf( "The starting record should be a network without choice nodes.\n" );
            return;
        }
        if ( Gia_ManPiNum(pGia) > 16 )
        {
            printf( "The starting record should be a network with no more than %d primary inputs.\n", 16 );
            return;
        }
        if ( Gia_ManPiNum(pGia) > nVars )
            printf( "The starting record has %d inputs (warning only).\n", Gia_ManPiNum(pGia) );
    }
//    Gia_ManHashStart( pGia );
    // move this to rec_add2, because if the library is never used for adding new structures
    // structural hashing is not needed
    if ( pGia->pHTable != NULL )
        Gia_ManHashStop( pGia );

    // create the primary inputs
    for ( i = Gia_ManPiNum(pGia); i < nVars; i++ )
        Gia_ManAppendCi(pGia);

    p = ABC_CALLOC( Abc_ManRec_t2, 1 );
    s_pMan = p;
//    memset( p, 0, sizeof(Abc_ManRec_t2) ); // no need for this if we use ABC_CALLOC
    p->pGia = pGia;
    p->nVars = Gia_ManPiNum(pGia);
    p->nWords = Kit_TruthWordNum( p->nVars );
    p->nCuts = nCuts;
    p->nVarsInit = nVars;
    p->recObjSize = sizeof(Rec_Obj_t2) + sizeof(char) * p->nVars;
    p->recObjSize = sizeof(void *) * ((p->recObjSize / sizeof(void *)) + ((p->recObjSize % sizeof(void *)) > 0));

    p->nRecObjsAlloc = 1 << 16;
    p->pRecObjs = (char *) calloc(p->nRecObjsAlloc, p->recObjSize);

    //p->pMemObj = Mem_FixedStart(p->recObjSize);
    p->fTrim = fTrim;
    // create elementary truth tables
    p->vTtElems = Vec_PtrAlloc( 0 ); assert( p->vTtElems->pArray == NULL );
    p->vTtElems->nSize = p->nVars;
    p->vTtElems->nCap = p->nVars;
    p->vTtElems->pArray = (void **)Extra_TruthElementary( p->nVars );  
    
    p->vInputs = Vec_StrStart( 1 << 16 );
    p->vUselessPos = Vec_IntAlloc(1 << 16);
//    p->vTtNodes = Vec_PtrAlloc( 1000 );
//    p->pMmTruth = Mem_FixedStart( sizeof(unsigned)*p->nWords );
//    for ( i = 0; i < Gia_ManPoNum(pGia); i++ )
//        Vec_PtrPush( p->vTtNodes, Mem_FixedEntryFetch(p->pMmTruth) );
    p->vTtMem = Vec_MemAlloc( p->nWords/2, 12 ); // 32 KB/page for 6-var functions

    // create hash table
    p->nBins = 20011;
    //p->nBins =500011;
    p->pBins = ABC_ALLOC( int, p->nBins );
    memset( p->pBins, -1, sizeof(int) * p->nBins );

clk = clock();
//     Gia_ManForEachPo( pGia, pObj, i )
//     {
//         pTruthSrc = Gia_ObjComputeTruthTable(pGia, pObj);
// //        pTruthDst = (unsigned *)Vec_PtrEntry( p->vTtNodes, Gia_ObjCioId(pObj) );
// //        Kit_TruthCopy(pTruthDst, pTruthSrc, p->nVars);
//         Rec_MemSetEntry( p, Gia_ObjCioId(pObj), pTruthSrc );
//     }
p->timeTruth += clock() - clk;  

    // insert the PO nodes into the table
timeInsert = clock();
    Abc_NtkRecMarkInputs(p, pGia);
    Gia_ManForEachPo( pGia, pObj, i )
    {
        p->nTried++;       
        pFanin = Gia_ObjFanin0(pObj);
        // mark the nodes with CO fanout.
        assert(pFanin->fMark1 == 0);
        pFanin->fMark1 = 1;
//        pTruth = (unsigned *)Vec_PtrEntry( p->vTtNodes, Gia_ObjCioId(pObj) );
        pTruth = Gia_ObjComputeTruthTable(pGia, pObj);

        //pTruth = Rec_MemReadEntry( p, Gia_ObjCioId(pObj) );
        // add the resulting truth table to the hash table 
        if(p->nAddedFuncs > 2 * p->nBins)
            Abc_NtkRecResizeHash2(p);
        ppSpot = Abc_NtkRecTableLookup2(p, p->pBins, p->nBins, pTruth, p->nVars );
        Abc_NtkRecInsertToLookUpTable2(p, ppSpot, pObj, Abc_ObjGetMax2(p->vInputs, pGia, pFanin), pTruth, p->fTrim);       
    }
p->timeInsert += clock() - timeInsert;

    // temporaries
    p->pBytes = ABC_ALLOC( int, 4*p->nWords );
    p->pMints = ABC_ALLOC( int, 2*p->nVars );
    p->pTemp1 = ABC_ALLOC( unsigned, p->nWords );
    p->pTemp2 = ABC_ALLOC( unsigned, p->nWords );
    p->vNodes = Vec_PtrAlloc( 100 );
    p->vTtTemps = Vec_PtrAllocSimInfo( 1024, p->nWords );
    p->vLabels = Vec_PtrStart( 1000 );


 p->timeTotal += clock() - clkTotal;  
}

/**Function*************************************************************

  Synopsis    [Print statistics about the current record.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecPs2(int fPrintLib)
{
    int Counter, Counters[17] = {0};
    int CounterS, CountersS[17] = {0};
    Abc_ManRec_t2 * p = s_pMan;
    Gia_Man_t * pGia = p->pGia;
    int pEntry, pTemp;
    //Gia_Obj_t * pObj;
    int i;
    FILE * pFile;
    unsigned* pTruth;
    int entry;
    int j;
    int nVars = s_pMan->nVars;
    // set the max PI number
    Abc_NtkRecMarkInputs(s_pMan, s_pMan->pGia);
    
if(fPrintLib)
{
    pFile = fopen( "tt10.txt", "wb" );
for ( i = 0; i < p->nBins; i++ )
    for ( entry = p->pBins[i]; entry != REC_EMPTY_ID; entry = Rec_Obj(p, entry)->pCopy )
    {
        int tmp = 0;

        assert( 0 );
        // added the next line to silence the warning that 'pEntry' is not initialized
        pEntry = -1;

//        pTruth = (unsigned*)Vec_PtrEntry(p->vTtNodes, entry);
        pTruth = Rec_MemReadEntry( p, Rec_Obj(p, pEntry)->truthID );
        /*if ( (int)Kit_TruthSupport(pTruth, nVars) != (1<<nVars)-1 )
            continue;*/
        Extra_PrintHex( pFile, pTruth, nVars );
        fprintf( pFile, " : nVars:  %d, Frequency:%d, nBin:%d  :  ", Abc_ObjGetMax2(s_pMan->vInputs, s_pMan->pGia, Abc_NtkRecGetObj(entry)), Rec_Obj(p, entry)->nFrequency, i);
        Kit_DsdPrintFromTruth2( pFile, pTruth, Abc_ObjGetMax2(s_pMan->vInputs, s_pMan->pGia, Abc_NtkRecGetObj(entry)) );
        fprintf( pFile, "\n" );
        for ( pTemp = entry; pTemp != REC_EMPTY_ID; pTemp = Rec_Obj(p, pTemp)->pNext )
        {
            fprintf(pFile,"%d :", tmp);
            for (j = 0; j <Abc_ObjGetMax2(s_pMan->vInputs, s_pMan->pGia, Abc_NtkRecGetObj(pTemp)); j++)
            {
                fprintf(pFile, " %d, ", Rec_Obj(p, pTemp)->pinToPinDelay[j]);
            }
            fprintf(pFile, "cost = %d ID = %d\n", Rec_Obj(p, pTemp)->cost, pTemp);             
            tmp++;
        }
        fprintf( pFile, "\n");
        fprintf( pFile, "\n");
    }
    fclose( pFile) ;
}

    // go through the table
    Counter = CounterS = 0;
    for ( i = 0; i < p->nBins; i++ )
    for ( pEntry = p->pBins[i]; pEntry != REC_EMPTY_ID; pEntry = Rec_Obj(p, pEntry)->pCopy )
    {
        assert(Abc_ObjGetMax2(s_pMan->vInputs, s_pMan->pGia, Abc_NtkRecGetObj(pEntry)) >= 2);    
        Counters[ Abc_ObjGetMax2(s_pMan->vInputs, s_pMan->pGia, Abc_NtkRecGetObj(pEntry))]++;
        Counter++;
        for ( pTemp = pEntry; pTemp != REC_EMPTY_ID; pTemp = Rec_Obj(p, pTemp)->pNext )
        {
            assert( Abc_ObjGetMax2(s_pMan->vInputs, s_pMan->pGia, Abc_NtkRecGetObj(pTemp)) == Abc_ObjGetMax2(s_pMan->vInputs, s_pMan->pGia, Abc_NtkRecGetObj(pEntry)) );
            CountersS[ Abc_ObjGetMax2(s_pMan->vInputs, s_pMan->pGia, Abc_NtkRecGetObj(pTemp)) ]++;
            CounterS++;
        }
    }
    //printf( "Functions = %d. Expected = %d.\n", Counter, p->nAddedFuncs );
    //printf( "Subgraphs = %d. Expected = %d.\n", CounterS, p->nAdded );
    assert( Counter == p->nAddedFuncs );
    assert( CounterS == p->nAdded );
    // clean

    printf( "The record with %d AND nodes in %d subgraphs for %d functions with %d inputs:\n", 
        Gia_ManAndNum(pGia), Gia_ManPoNum(pGia), p->nAddedFuncs, Gia_ManPiNum(pGia) );
    for ( i = 0; i <= 16; i++ )
    {
        if ( Counters[i] )
            printf( "Inputs = %2d.  Funcs = %8d.  Subgrs = %8d.  Ratio = %6.2f.\n", i, Counters[i], CountersS[i], 1.0*CountersS[i]/Counters[i] );
    }

    printf( "Subgraphs tried                             = %10d. (%6.2f %%)\n", p->nTried,        !p->nTried? 0 : 100.0*p->nTried/p->nTried );
    printf( "Subgraphs filtered by support size          = %10d. (%6.2f %%)\n", p->nFilterSize,   !p->nTried? 0 : 100.0*p->nFilterSize/p->nTried );
    printf( "Subgraphs filtered by structural redundancy = %10d. (%6.2f %%)\n", p->nFilterRedund, !p->nTried? 0 : 100.0*p->nFilterRedund/p->nTried );
    printf( "Subgraphs filtered by volume                = %10d. (%6.2f %%)\n", p->nFilterVolume, !p->nTried? 0 : 100.0*p->nFilterVolume/p->nTried );
    printf( "Subgraphs filtered by TT redundancy         = %10d. (%6.2f %%)\n", p->nFilterTruth,  !p->nTried? 0 : 100.0*p->nFilterTruth/p->nTried );
    printf( "Subgraphs filtered by error                 = %10d. (%6.2f %%)\n", p->nFilterError,  !p->nTried? 0 : 100.0*p->nFilterError/p->nTried );
    printf( "Subgraphs filtered by isomorphism           = %10d. (%6.2f %%)\n", p->nFilterSame,   !p->nTried? 0 : 100.0*p->nFilterSame/p->nTried );
    printf( "Subgraphs added                             = %10d. (%6.2f %%)\n", p->nAdded,        !p->nTried? 0 : 100.0*p->nAdded/p->nTried );
    printf( "Functions added                             = %10d. (%6.2f %%)\n", p->nAddedFuncs,   !p->nTried? 0 : 100.0*p->nAddedFuncs/p->nTried );
    if(s_pMan->fTrim)
        printf( "Functions trimed                            = %10d. (%6.2f %%)\n", p->nTrimed,       !p->nTried? 0 : 100.0*p->nTrimed/p->nTried );
    p->timeOther = p->timeTotal - p->timeCollect - p->timeTruth - p->timeCanon - p->timeInsert - p->timeBuild - p->timeTrim - p->timeMerge - p->timeReHash;
    ABC_PRTP( "Collecting nodes ", p->timeCollect, p->timeTotal);
    ABC_PRTP( "Computing truth  ", p->timeTruth, p->timeTotal );
    ABC_PRTP( "Canonicizing     ", p->timeCanon, p->timeTotal );
    ABC_PRTP( "Building         ", p->timeBuild, p->timeTotal );
    ABC_PRTP( "ReHash           ", p->timeReHash, p->timeTotal );
    ABC_PRTP( "Merge            ", p->timeMerge, p->timeTotal );
    ABC_PRTP( "Insert           ", p->timeInsert, p->timeTotal);
    if(s_pMan->fTrim)
        ABC_PRTP( "Filter           ", p->timeTrim, p->timeTotal);
    ABC_PRTP( "Other            ", p->timeOther, p->timeTotal );
    ABC_PRTP( "TOTAL            ", p->timeTotal, p->timeTotal );
    
    if ( p->nFunsFound )
    {
        printf("\n");
        printf( "During rewriting found = %d and not found = %d functions.\n", p->nFunsFound, p->nFunsNotFound );
        printf( "Functions tried                             = %10d. (%6.2f %%)\n", p->nFunsTried,    !p->nFunsTried? 0 : 100.0*p->nFunsTried/p->nFunsTried );
        printf( "Functions filtered by support               = %10d. (%6.2f %%)\n", p->nFunsFilteredBysupport, !p->nFunsFilteredBysupport? 0 : 100.0*p->nFunsFilteredBysupport/p->nFunsTried );
        printf( "Functions not found in lib                  = %10d. (%6.2f %%)\n", p->nFunsNotFound, !p->nFunsNotFound? 0 : 100.0*p->nFunsNotFound/p->nFunsTried );
        printf( "Functions founded                           = %10d. (%6.2f %%)\n", p->nFunsFound,   !p->nFunsFound? 0 : 100.0*p->nFunsFound/p->nFunsTried );
        printf( "Functions delay computed                    = %10d.  Ratio   = %6.2f.\n", p->nFunsDelayComput,  !p->nFunsDelayComput? 0 : 1.0*p->nFunsDelayComput/p->nFunsFound ); 
        p->timeIfOther = p->timeIfTotal - p->timeIfCanonicize - p->timeIfComputDelay -p->timeIfDerive;
        ABC_PRTP( "Canonicize       ", p->timeIfCanonicize, p->timeIfTotal );
        ABC_PRTP( "Compute Delay    ", p->timeIfComputDelay, p->timeIfTotal );
        ABC_PRTP( "Derive           ", p->timeIfDerive, p->timeIfTotal );
        ABC_PRTP( "Other            ", p->timeIfOther, p->timeIfTotal );
        ABC_PRTP( "TOTAL            ", p->timeIfTotal, p->timeIfTotal );
    }
    
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abc_NtkRecCollectNodes_rec( If_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    if ( pNode->fMark )
        return;
    pNode->fMark = 1;
    assert( If_ObjIsAnd(pNode) );
    Abc_NtkRecCollectNodes_rec( If_ObjFanin0(pNode), vNodes );
    Abc_NtkRecCollectNodes_rec( If_ObjFanin1(pNode), vNodes );
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_NtkRecCollectNodes( If_Man_t * pIfMan, If_Obj_t * pRoot, If_Cut_t * pCut, Vec_Ptr_t * vNodes )
{
    If_Obj_t * pLeaf;
    int i, RetValue = 1;

    // collect the internal nodes of the cut
    Vec_PtrClear( vNodes );
    If_CutForEachLeaf( pIfMan, pCut, pLeaf, i )
    {
        Vec_PtrPush( vNodes, pLeaf );
        assert( pLeaf->fMark == 0 );
        pLeaf->fMark = 1;
    }

    // collect other nodes
    Abc_NtkRecCollectNodes_rec( pRoot, vNodes );

    // check if there are leaves, such that both of their fanins are marked
    // this indicates a redundant cut
    If_CutForEachLeaf( pIfMan, pCut, pLeaf, i )
    {
        if ( !If_ObjIsAnd(pLeaf) )
            continue;
        if ( If_ObjFanin0(pLeaf)->fMark && If_ObjFanin1(pLeaf)->fMark )
        {
            RetValue = 0;
            break;
        }
    }

    // clean the mark
    Vec_PtrForEachEntry( If_Obj_t *, vNodes, pLeaf, i )
        pLeaf->fMark = 0;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Computes truth tables of nodes in the cut.]

  Description [Returns 0 if the TT does not depend on some cut variables.
  Or if the TT can be expressed simpler using other nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_NtkRecCutTruth( Vec_Ptr_t * vNodes, int nLeaves, Vec_Ptr_t * vTtTemps, Vec_Ptr_t * vTtElems )
{
    unsigned * pSims, * pSims0, * pSims1;
    unsigned * pTemp = s_pMan->pTemp2;
    unsigned uWord;
    If_Obj_t * pObj, * pObj2, * pRoot;
    int i, k, nLimit, nInputs = s_pMan->nVars;

    assert( Vec_PtrSize(vNodes) > nLeaves );

    // set the elementary truth tables and compute the truth tables of the nodes
    Vec_PtrForEachEntry( If_Obj_t *, vNodes, pObj, i )
    {
        pObj->pCopy = Vec_PtrEntry(vTtTemps, i);
        pSims = (unsigned *)pObj->pCopy;
        if ( i < nLeaves )
        {
            Kit_TruthCopy( pSims, (unsigned *)Vec_PtrEntry(vTtElems, i), nInputs );
            continue;
        }
        assert( If_ObjIsAnd(pObj) );
        // get hold of the simulation information
        pSims0 = (unsigned *)If_ObjFanin0(pObj)->pCopy;
        pSims1 = (unsigned *)If_ObjFanin1(pObj)->pCopy;
        // simulate the node
        Kit_TruthAndPhase( pSims, pSims0, pSims1, nInputs, If_ObjFaninC0(pObj), If_ObjFaninC1(pObj) );
    }

    // check the support size
    pRoot = (If_Obj_t *)Vec_PtrEntryLast( vNodes );
    pSims = (unsigned *)pRoot->pCopy;
    if ( Kit_TruthSupport(pSims, nInputs) != Kit_BitMask(nLeaves) )
        return 0;

    // make sure none of the nodes has the same simulation info as the output
    // check pairwise comparisons
    nLimit = Vec_PtrSize(vNodes) - 1;
    Vec_PtrForEachEntryStop( If_Obj_t *, vNodes, pObj, i, nLimit )
    {
        pSims0 = (unsigned *)pObj->pCopy;
        if ( Kit_TruthIsEqualWithPhase(pSims, pSims0, nInputs) )
            return 0;
        Vec_PtrForEachEntryStop( If_Obj_t *, vNodes, pObj2, k, i )
        {
            if ( (If_ObjFanin0(pRoot) == pObj && If_ObjFanin1(pRoot) == pObj2) ||
                 (If_ObjFanin1(pRoot) == pObj && If_ObjFanin0(pRoot) == pObj2) )
                 continue;
            pSims1 = (unsigned *)pObj2->pCopy;

            uWord = pSims0[0] & pSims1[0];
            if ( pSims[0] == uWord || pSims[0] == ~uWord )
            {
                Kit_TruthAndPhase( pTemp, pSims0, pSims1, nInputs, 0, 0 );
                if ( Kit_TruthIsEqualWithPhase(pSims, pTemp, nInputs) )
                    return 0;
            }

            uWord = pSims0[0] & ~pSims1[0];
            if ( pSims[0] == uWord || pSims[0] == ~uWord )
            {
                Kit_TruthAndPhase( pTemp, pSims0, pSims1, nInputs, 0, 1 );
                if ( Kit_TruthIsEqualWithPhase(pSims, pTemp, nInputs) )
                    return 0;
            }

            uWord = ~pSims0[0] & pSims1[0];
            if ( pSims[0] == uWord || pSims[0] == ~uWord )
            {
                Kit_TruthAndPhase( pTemp, pSims0, pSims1, nInputs, 1, 0 );
                if ( Kit_TruthIsEqualWithPhase(pSims, pTemp, nInputs) )
                    return 0;
            }

            uWord = ~pSims0[0] & ~pSims1[0];
            if ( pSims[0] == uWord || pSims[0] == ~uWord )
            {
                Kit_TruthAndPhase( pTemp, pSims0, pSims1, nInputs, 1, 1 );
                if ( Kit_TruthIsEqualWithPhase(pSims, pTemp, nInputs) )
                    return 0;
            }
        }
    }
    return 1;
}



/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecAddCut2( If_Man_t * pIfMan, If_Obj_t * pRoot, If_Cut_t * pCut )
{
    static int s_MaxSize[16] = { 0 };
    char pCanonPerm[16];
    Gia_Obj_t * pObj = NULL,  *pPO;
    int iFanin0, iFanin1, iRecObj;
    int * ppSpot, lit;//, test;
    Gia_Man_t * pAig = s_pMan->pGia;
    If_Obj_t * pIfObj;
    Vec_Ptr_t * vNodes = s_pMan->vNodes;
    unsigned * pInOut = s_pMan->pTemp1;
    unsigned * pTemp = s_pMan->pTemp2;
    unsigned *pTruth;//, *pTruthDst;
    int objectID = 0;
    int i, RetValue, nNodes, nNodesBeg, nInputs = s_pMan->nVars, nLeaves = If_CutLeaveNum(pCut);
    unsigned uCanonPhase;
    int clk, timeInsert, timeBuild;
    //int begin = clock();
    assert( nInputs <= 16 );
    assert( nInputs == (int)pCut->nLimit );
    s_pMan->nTried++;
    // skip small cuts
     if ( nLeaves < 2 )
     {
        s_pMan->nFilterSize++;
        return 1;
     }
    // collect internal nodes and skip redundant cuts
clk = clock();
    RetValue = Abc_NtkRecCollectNodes( pIfMan, pRoot, pCut, vNodes );

s_pMan->timeCollect += clock() - clk;
    if ( !RetValue )
    {
        s_pMan->nFilterRedund++;
        return 1;
    }

    // skip cuts with very large volume
    if ( Vec_PtrSize(vNodes) > nLeaves + 3*(nLeaves-1) + s_MaxSize[nLeaves] )
    {
        s_pMan->nFilterVolume++;
        return 1;
    }
   

    // compute truth table and skip the redundant structures
clk = clock();
    RetValue = Abc_NtkRecCutTruth( vNodes, nLeaves, s_pMan->vTtTemps, s_pMan->vTtElems );
    s_pMan->timeTruth += clock() - clk;
    if ( !RetValue )
    {
        //fprintf(file,"redundant structures\n");
        //fclose(file);
        s_pMan->nFilterTruth++;
        return 1;
    }

    // copy the truth table
    Kit_TruthCopy( pInOut, (unsigned *)pRoot->pCopy, nInputs );

    // set permutation
    for ( i = 0; i < nLeaves; i++ )
        pCanonPerm[i] = i;

    // semi-canonicize the truth table
clk = clock();
    uCanonPhase = Kit_TruthSemiCanonicize( pInOut, pTemp, nLeaves, pCanonPerm );
    If_CutTruthStretch(pInOut, nLeaves, s_pMan->nVars);
    s_pMan->timeCanon += clock() - clk;
    // pCanonPerm and uCanonPhase show what was the variable corresponding to each var in the current truth

    // go through the variables in the new truth table
timeBuild = clock();
    for ( i = 0; i < nLeaves; i++ )
    {
        // get hold of the corresponding leaf
        pIfObj = If_ManObj( pIfMan, pCut->pLeaves[(int)pCanonPerm[i]] );
        // get hold of the corresponding new node
        pObj = Gia_ManPi( pAig, i );
        lit = Gia_ObjId(pAig, pObj);
        lit = Abc_Var2Lit( lit, ((uCanonPhase & (1 << i)) != 0) );
        // map them
        pIfObj->iCopy = lit;
    }

    // build the node and compute its truth table
    nNodesBeg = Gia_ManObjNum( pAig );
    Vec_PtrForEachEntryStart( If_Obj_t *, vNodes, pIfObj, i, nLeaves )
    {
        iFanin0 = Abc_LitNotCond( If_ObjFanin0(pIfObj)->iCopy, If_ObjFaninC0(pIfObj) );
        iFanin1 = Abc_LitNotCond( If_ObjFanin1(pIfObj)->iCopy, If_ObjFaninC1(pIfObj) );

        nNodes = Gia_ManObjNum( pAig );
        iRecObj = Gia_ManHashAnd(pAig, iFanin0, iFanin1 );
        //assert( !Gia_IsComplement(pObj) );
        //pObj = Gia_Regular(pObj);
        pIfObj->iCopy = iRecObj;

    }
    //assert(pObj);
    pObj = Gia_ManObj(pAig, Abc_Lit2Var(iRecObj));
    pTruth = Gia_ObjComputeTruthTable(pAig, pObj);
s_pMan->timeBuild += clock() - timeBuild;
    
    if ( Kit_TruthSupport(pTruth, nInputs) != Kit_BitMask(nLeaves) )
    {
        s_pMan->nFilterError++;
        printf( "S" );
        return 1;
    }

    // compare the truth tables
    if ( !Kit_TruthIsEqualWithPhase( pTruth, pInOut, nInputs ) )
    {
        s_pMan->nFilterError++;
        printf( "F" );
        return 1;
    }
//    Extra_PrintBinary( stdout, pInOut, 8 ); printf( "\n" );
    
    // look up in the hash table and increase the hit number of the functional class
    if(s_pMan->nAddedFuncs > 2 * s_pMan->nBins)
        Abc_NtkRecResizeHash2(s_pMan);
    ppSpot = Abc_NtkRecTableLookup2(s_pMan, s_pMan->pBins,s_pMan->nBins , pTruth, nInputs );
    Abc_NtkRecFrequencyInc(*ppSpot);   
    // if not new nodes were added and the node has a CO fanout
    
    if ( nNodesBeg == Gia_ManObjNum(pAig) && pObj->fMark1 == 1 )
    {
        s_pMan->nFilterSame++;
        //assert(*ppSpot != NULL);
        return 1;
    }

    // create PO for this node
    objectID = Gia_ObjId(pAig, pObj);
    pPO = Gia_ManObj(pAig, Gia_ManAppendCo(pAig, Gia_ObjToLit(pAig, pObj)) >> 1);
    pObj = Gia_ManObj(pAig, objectID);  
    assert(pObj->fMark1 == 0);
    pObj->fMark1 = 1;

//    if ( Vec_PtrSize(s_pMan->vTtNodes) <= Gia_ManPoNum(pAig) )
//    {
//        while ( Vec_PtrSize(s_pMan->vTtNodes) <= Gia_ObjCioId(pPO) )
//            Vec_PtrPush( s_pMan->vTtNodes, Mem_FixedEntryFetch(s_pMan->pMmTruth) );
//    }

//    pTruthDst = (unsigned *)Vec_PtrEntry( s_pMan->vTtNodes, Gia_ObjCioId(pPO));
//    Kit_TruthCopy(pTruthDst, pTruthSrc, s_pMan->nVars);
    //Rec_MemSetEntry( s_pMan, Gia_ObjCioId(pPO), pTruthSrc );

    // add the resulting truth table to the hash table 
    timeInsert = clock();
    Abc_NtkRecInsertToLookUpTable2(s_pMan, ppSpot, pPO, nLeaves, pTruth, s_pMan->fTrim);
    s_pMan->timeInsert += clock() - timeInsert;
//  if (pIfMan->pPars->fDelayOpt)
//      Abc_NtkRecAddSOPB(pIfMan, pCut, pTruth, pCanonPerm, uCanonPhase );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs renoding as technology mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecAdd2( Abc_Ntk_t * pNtk, int fUseSOPB)
{
    extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
    extern int Abc_NtkRecAddCut( If_Man_t * pIfMan, If_Obj_t * pRoot, If_Cut_t * pCut );

    If_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkNew;
    int clk = clock();

    if ( Abc_NtkGetChoiceNum( pNtk ) )
        printf( "Performing recoding structures with choices.\n" );

    // create hash table if not available
    if ( s_pMan->pGia->pHTable == NULL )
        Gia_ManHashStart( s_pMan->pGia );

    // set defaults
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
    pPars->nLutSize    =  s_pMan->nVarsInit;
    pPars->nCutsMax    =  s_pMan->nCuts;
    pPars->nFlowIters  =  0;
    pPars->nAreaIters  =  0;
    pPars->DelayTarget = -1;
    pPars->Epsilon     =  (float)0.005;
    pPars->fPreprocess =  0;
    pPars->fArea       =  1;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  0; 
    pPars->fLatchPaths =  0;
    pPars->fSeqMap     =  0;
    pPars->fVerbose    =  0;
    //pPars->fCutMin     =  1;
    // internal parameters
    if (fUseSOPB)
    {
        pPars->fTruth      =  1;
        pPars->fUsePerm    =  1; 
        pPars->fDelayOpt   =  1;
    }
    else
    {
        pPars->fTruth      =  1;
        pPars->fUsePerm    =  0; 
        pPars->fDelayOpt   =  0;
    }
    pPars->nLatchesCi  =  0;
    pPars->nLatchesCo  =  0;
    pPars->pLutLib     =  NULL; // Abc_FrameReadLibLut();
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->fUseBdds    =  0;
    pPars->fUseSops    =  0;
    pPars->fUseCnfs    =  0;
    pPars->fUseMv      =  0;
    pPars->fSkipCutFilter = 1;
    pPars->pFuncCost   =  NULL;
    pPars->pFuncUser   =  Abc_NtkRecAddCut2;

    // perform recording
    pNtkNew = Abc_NtkIf( pNtk, pPars );
    Abc_NtkDelete( pNtkNew );
s_pMan->timeTotal += clock() - clk;

//    if ( !Abc_NtkCheck( s_pMan->pNtk ) )
//        printf( "Abc_NtkRecAdd: The network check has failed.\n" );
}


/**Function*************************************************************

  Synopsis    [Compute delay of the structure using pin-to-pin delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_CutComputDelay(If_Man_t* p, Rec_Obj_t2* entry, If_Cut_t* pCut, char* pCanonPerm , int nVars)
{
    If_Obj_t* pLeaf;
    int i, delayTemp, delayMax = -ABC_INFINITY;
    for (i = 0; i < nVars; i++)
    {
        pLeaf = If_ManObj(p, (pCut)->pLeaves[(int)pCanonPerm[i]]);
        pLeaf = If_Regular(pLeaf);
        delayTemp = entry->pinToPinDelay[i] + If_ObjCutBest(pLeaf)->Delay;
        if(delayTemp > delayMax)
            delayMax = delayTemp;
    }
    // plus each pin's delay with its pin-to-output delay, the biggest one is the delay of the structure.
    return delayMax;
}

  /**Function*************************************************************

  Synopsis    [Look up the best strcuture in the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
 static int Abc_NtkRecLookUpEnum(If_Man_t * pIfMan,If_Cut_t * pCut, int * ppSpot, int * pCandMin, char * pCanonPerm)
 {
    int DelayMin = ABC_INFINITY , Delay = -ABC_INFINITY;
    int pCand;
    int nLeaves = pCut->nLeaves;
    *pCandMin = -1;
    assert( *ppSpot != -1 );
    for ( pCand = *ppSpot; pCand != -1 ; pCand = Rec_Obj(s_pMan,pCand)->pNext )
    {
        s_pMan->nFunsDelayComput++; 
        Delay = If_CutComputDelay(pIfMan, Rec_Obj(s_pMan,pCand), pCut, pCanonPerm ,nLeaves);
        if ( DelayMin > Delay )
        {
            DelayMin = Delay;
            *pCandMin = pCand;
        }
        else if(Delay == DelayMin)
        {
            if(Rec_Obj(s_pMan,pCand)->cost < Rec_Obj(s_pMan, *pCandMin)->cost)
                *pCandMin = pCand;
        }
    }
    assert( *pCandMin != -1 );
    return DelayMin;
 }

 /**Function*************************************************************

  Synopsis    [Look up the best strcuture in the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
 static Rec_Obj_t2 * Abc_NtkRecLookUpBest(If_Man_t * pIfMan,If_Cut_t * pCut, unsigned * pInOut, char * pCanonPerm,  int * fCompl, int * delayBest)
 {
     int pCandMin = REC_EMPTY_ID, pCandMinCompl = REC_EMPTY_ID, *ppSpot;
     int delay = ABC_INFINITY, delayCompl = ABC_INFINITY;
     int nVars = s_pMan->nVars;
     //int nLeaves = pCut->nLeaves;
     ppSpot = Abc_NtkRecTableLookup2(s_pMan, s_pMan->pBins, s_pMan->nBins, pInOut, nVars );
     if (*ppSpot != REC_EMPTY_ID)
         delay = Abc_NtkRecLookUpEnum(pIfMan, pCut, ppSpot, &pCandMin, pCanonPerm);
     Kit_TruthNot(pInOut, pInOut, nVars);
     ppSpot = Abc_NtkRecTableLookup2(s_pMan, s_pMan->pBins, s_pMan->nBins, pInOut, nVars );
     if (*ppSpot != REC_EMPTY_ID)
         delayCompl = Abc_NtkRecLookUpEnum(pIfMan, pCut, ppSpot, &pCandMinCompl, pCanonPerm);
     if (delayBest)
         *delayBest = delay < delayCompl ? delay : delayCompl;
     if (pCandMin == REC_EMPTY_ID && pCandMinCompl == REC_EMPTY_ID)
         return NULL;
     else if (pCandMin != REC_EMPTY_ID && pCandMinCompl != REC_EMPTY_ID)
     {
         if (delay > delayCompl || (delay == delayCompl && Rec_Obj(s_pMan, pCandMin)->cost > Rec_Obj(s_pMan, pCandMinCompl)->cost))
         {
             if (fCompl)
                 *fCompl = 1;
             return Rec_Obj(s_pMan, pCandMinCompl);
         }
         else
         {
             if (fCompl)
                 *fCompl = 0;
             return Rec_Obj(s_pMan, pCandMin);
         }
     }
     else if (pCandMin != REC_EMPTY_ID)
     {
         if (fCompl)
             *fCompl = 0;
         return Rec_Obj(s_pMan, pCandMin);
     }
     else
     {
         if (fCompl)
             *fCompl = 1;
         return Rec_Obj(s_pMan, pCandMinCompl);
     }
 }

 /**Function*************************************************************

  Synopsis    [Computes the  delay using library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutDelayRecCost2(If_Man_t* p, If_Cut_t* pCut, If_Obj_t * pObj)
{
    //int fVerbose = 0;
    int timeDelayComput, timeTotal = clock(), timeCanonicize;
    int nLeaves, i, DelayMin = ABC_INFINITY , * pDelayBest = &DelayMin;
    char pCanonPerm[16];
    unsigned uCanonPhase;
    unsigned* pTruthRec;
    Rec_Obj_t2 * pCandMin;
    //Abc_Ntk_t *pAig = s_pMan->pNtk;
    unsigned *pInOut = s_pMan->pTemp1;
    unsigned *pTemp = s_pMan->pTemp2;
    int nVars = s_pMan->nVars;
    //int Counter;
    assert( s_pMan != NULL );
    nLeaves = If_CutLeaveNum(pCut);
    s_pMan->nFunsTried++;
    assert( nLeaves >= 2 && nLeaves <= nVars );
    Kit_TruthCopy(pInOut, If_CutTruth(pCut), nLeaves);
    //if not every variables are in the support, skip this cut.
    if ( Kit_TruthSupport(pInOut, nLeaves) != Kit_BitMask(nLeaves) )
    {
        DelayMin = 0;
        //s_pMan->nFunsFilteredBysupport++;
        pCut->fUser = 1;
        pCut->fUseless = 0;
        pCut->Cost = 1;
        for (i = 0; i < nLeaves; i++)
        {
            if(Kit_TruthVarInSupport( pInOut, nLeaves, i ))
            {
                pCut->pPerm[i] = 0;
                DelayMin = If_ObjCutBest(If_ManObj( p, pCut->pLeaves[i]))->Delay;
            }
            else
                pCut->pPerm[i] = IF_BIG_CHAR;
        }
            
        return DelayMin;
    }
    timeCanonicize = clock();
    //canonicize
    for (i = 0; i < nLeaves; i++)
        pCanonPerm[i] = i;
    uCanonPhase = Kit_TruthSemiCanonicize(pInOut, pTemp, nLeaves, pCanonPerm);
    If_CutTruthStretch(pInOut, nLeaves, nVars);
    s_pMan->timeIfCanonicize += clock() - timeCanonicize;   
    timeDelayComput = clock();
    pCandMin = Abc_NtkRecLookUpBest(p, pCut, pInOut, pCanonPerm, NULL,pDelayBest);
    assert (!(pCandMin == NULL && nLeaves == 2));
    s_pMan->timeIfComputDelay += clock() - timeDelayComput;
    //functional class not found in the library.
    if ( pCandMin == NULL )
    {
        s_pMan->nFunsNotFound++;        
        pCut->Cost = IF_COST_MAX;
        pCut->fUser = 1;
        pCut->fUseless = 1;
        return ABC_INFINITY;
    }
    s_pMan->nFunsFound++; 
    // make sure the truth table is the same
//    pTruthRec = (unsigned*)Vec_PtrEntry( s_pMan->vTtNodes, Rec_ObjID(s_pMan, pCandMin) );
    pTruthRec = Rec_MemReadEntry( s_pMan, pCandMin->truthID );
    if ( !Kit_TruthIsEqualWithPhase( pTruthRec, pInOut, nLeaves ) )
    {
        assert( 0 );
        s_pMan->nIfMapError++;  
        return -1;
    }
    // mark as user cut.
    pCut->fUser = 1;
       
    //assert( pCandMin != NULL );
    for ( i = 0; i < nLeaves; i++ )
    {
        pCut->pPerm[(int)pCanonPerm[i]] = pCandMin->pinToPinDelay[i];
    }
    s_pMan->timeIfTotal += clock() - timeTotal;
    pCut->Cost = pCandMin->cost;
        return DelayMin;
    
}

 /**Function*************************************************************

  Synopsis    [Build up the structure using library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NtkRecBuildUp_rec2(Hop_Man_t* pMan, Gia_Obj_t* pObj, Vec_Ptr_t * vNodes)
{
    Hop_Obj_t * pRes0, *pRes1, *pRes;
    Gia_Obj_t *pRegular = Gia_Regular(pObj);
    if (Gia_ObjIsTravIdCurrent(s_pMan->pGia, pRegular) || Gia_ObjIsPi(s_pMan->pGia, pRegular))
        return (Hop_Obj_t *)Vec_PtrEntry(vNodes, Gia_ObjId(s_pMan->pGia, pRegular));
    Gia_ObjSetTravIdCurrent(s_pMan->pGia, pRegular);
    pRes0 = Abc_NtkRecBuildUp_rec2(pMan, Gia_ObjFanin0(pRegular), vNodes);
    pRes0 = Hop_NotCond(pRes0, pRegular->fCompl0);
    pRes1 = Abc_NtkRecBuildUp_rec2(pMan, Gia_ObjFanin1(pRegular), vNodes);
    pRes1 = Hop_NotCond(pRes1, pRegular->fCompl1);
    pRes = Hop_And(pMan, pRes0, pRes1);
    Vec_PtrWriteEntry(vNodes,Gia_ObjId(s_pMan->pGia, pRegular),pRes);
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Derive the final network from the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_RecToHop2( Hop_Man_t * pMan, If_Man_t * pIfMan, If_Cut_t * pCut, If_Obj_t * pIfObj )
{
    Rec_Obj_t2 * pCandMin;
    Hop_Obj_t* pHopObj, * pFan0, * pFan1;
    Gia_Obj_t* pGiaObj, *pGiaTemp;
    Gia_Man_t * pAig = s_pMan->pGia;
    int nLeaves, i;// DelayMin = ABC_INFINITY , Delay = -ABC_INFINITY
    unsigned uCanonPhase;
    int nVars = s_pMan->nVars;
    char pCanonPerm[16];
    unsigned *pInOut = s_pMan->pTemp1;
    unsigned *pTemp = s_pMan->pTemp2;
    int time = clock();
    int fCompl;
    int * pCompl = &fCompl;
    nLeaves = If_CutLeaveNum(pCut);
//  if (nLeaves < 3)
//      return Abc_NodeTruthToHop(pMan, pIfMan, pCut);
    Kit_TruthCopy(pInOut, If_CutTruth(pCut), pCut->nLimit);
    //special cases when cut-minimization return 2, that means there is only one leaf in the cut.
    if ((Kit_TruthIsConst0(pInOut, nLeaves) && pCut->fCompl == 0) || (Kit_TruthIsConst1(pInOut, nLeaves) && pCut->fCompl == 1))
        return Hop_ManConst0(pMan);
    if ((Kit_TruthIsConst0(pInOut, nLeaves) && pCut->fCompl == 1) || (Kit_TruthIsConst1(pInOut, nLeaves) && pCut->fCompl == 0))
        return Hop_ManConst1(pMan);
    if (Kit_TruthSupport(pInOut, nLeaves) != Kit_BitMask(nLeaves))
    {   
        for (i = 0; i < nLeaves; i++)
            if(Kit_TruthVarInSupport( pInOut, nLeaves, i ))
                return Hop_NotCond(Hop_IthVar(pMan, i), (pCut->fCompl ^ ((*pInOut & 0x01) > 0)));
    }
    
    for (i = 0; i < nLeaves; i++)
        pCanonPerm[i] = i;
    uCanonPhase = Kit_TruthSemiCanonicize(pInOut, pTemp, nLeaves, pCanonPerm);
    If_CutTruthStretch(pInOut, nLeaves, nVars);
    pCandMin = Abc_NtkRecLookUpBest(pIfMan, pCut, pInOut, pCanonPerm, pCompl,NULL);

/*
    Vec_PtrGrow(s_pMan->vLabels, Gia_ManObjNum(pAig));
    s_pMan->vLabels->nSize = s_pMan->vLabels->nCap;
    for (i = 0; i < nLeaves; i++)
    {
        pGiaObj = Gia_ManPi( pAig, i );
        pHopObj = Hop_IthVar(pMan, pCanonPerm[i]);
        pHopObj = Hop_NotCond(pHopObj, ((uCanonPhase & (1 << i)) > 0));
        Vec_PtrWriteEntry(s_pMan->vLabels, Gia_ObjId(pAig, pGiaObj), pHopObj);
    }
    //Abc_NtkIncrementTravId(pAig);
    Gia_ManIncrementTravId(pAig);
    //derive the best structure in the library.
    pHopObj = Abc_NtkRecBuildUp_rec2(pMan, Abc_NtkRecGetObj(Rec_ObjID(s_pMan, pCandMin)), s_pMan->vLabels);
*/

    // get the top-most GIA node
    pGiaObj = Abc_NtkRecGetObj( Rec_ObjID(s_pMan, pCandMin) );
    assert( Gia_ObjIsAnd(pGiaObj) || Gia_ObjIsPi(pAig, pGiaObj) );
    // collect internal nodes into pAig->vTtNodes
    if ( pAig->vTtNodes == NULL )
        pAig->vTtNodes = Vec_IntAlloc( 256 );
    Gia_ObjCollectInternal( pAig, pGiaObj );
    // collect HOP nodes for leaves
    Vec_PtrClear( s_pMan->vLabels );
    for (i = 0; i < nLeaves; i++)
    {
        pHopObj = Hop_IthVar(pMan, pCanonPerm[i]);
        pHopObj = Hop_NotCond(pHopObj, ((uCanonPhase & (1 << i)) > 0));
        Vec_PtrPush(s_pMan->vLabels, pHopObj);
    }
    // compute HOP nodes for internal nodes
    Gia_ManForEachObjVec( pAig->vTtNodes, pAig, pGiaTemp, i )
    {
        pGiaTemp->fMark0 = 0; // unmark node marked by Gia_ObjCollectInternal()

        if ( Gia_ObjIsAnd(Gia_ObjFanin0(pGiaTemp)) )
            pFan0 = (Hop_Obj_t *)Vec_PtrEntry(s_pMan->vLabels, Gia_ObjNum(pAig, Gia_ObjFanin0(pGiaTemp)) + nLeaves);
        else
            pFan0 = (Hop_Obj_t *)Vec_PtrEntry(s_pMan->vLabels, Gia_ObjCioId(Gia_ObjFanin0(pGiaTemp)));
        pFan0 = Hop_NotCond(pFan0, Gia_ObjFaninC0(pGiaTemp));

        if ( Gia_ObjIsAnd(Gia_ObjFanin1(pGiaTemp)) )
            pFan1 = (Hop_Obj_t *)Vec_PtrEntry(s_pMan->vLabels, Gia_ObjNum(pAig, Gia_ObjFanin1(pGiaTemp)) + nLeaves);
        else
            pFan1 = (Hop_Obj_t *)Vec_PtrEntry(s_pMan->vLabels, Gia_ObjCioId(Gia_ObjFanin1(pGiaTemp)));
        pFan1 = Hop_NotCond(pFan1, Gia_ObjFaninC1(pGiaTemp));

        pHopObj = Hop_And(pMan, pFan0, pFan1);
        Vec_PtrPush(s_pMan->vLabels, pHopObj);
    }
    // get the final result
    if ( Gia_ObjIsAnd(pGiaObj) )
        pHopObj = (Hop_Obj_t *)Vec_PtrEntry(s_pMan->vLabels, Gia_ObjNum(pAig, pGiaObj) + nLeaves);
    else if ( Gia_ObjIsPi(pAig, pGiaObj) )
        pHopObj = (Hop_Obj_t *)Vec_PtrEntry(s_pMan->vLabels, Gia_ObjCioId(pGiaObj));
    else assert( 0 );

    
    s_pMan->timeIfDerive += clock() - time;
    s_pMan->timeIfTotal += clock() - time;
    // complement the result if needed
    return Hop_NotCond(pHopObj, (pCut->fCompl)^(((uCanonPhase & (1 << nLeaves)) > 0)) ^ fCompl);    
}

/**Function*************************************************************

  Synopsis    [Returns the given record.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecStop2()
{
    assert( s_pMan != NULL );
//    Abc_NtkRecDumpTruthTables( s_pMan );
    if ( s_pMan->pGia )
        Gia_ManStop(s_pMan->pGia);
//    Vec_PtrFreeFree( s_pMan->vTtNodes );

//    Mem_FixedStop( s_pMan->pMmTruth, 0 );
//    Vec_PtrFree( s_pMan->vTtNodes );
    Vec_MemFreeP( &s_pMan->vTtMem );

    Vec_StrFree( s_pMan->vInputs );
    Vec_PtrFree( s_pMan->vTtElems );
    ABC_FREE( s_pMan->pBins );

    // temporaries
    ABC_FREE( s_pMan->pBytes );
    ABC_FREE( s_pMan->pMints );
    ABC_FREE( s_pMan->pTemp1 );
    ABC_FREE( s_pMan->pTemp2 );
    Vec_PtrFree( s_pMan->vNodes );
    Vec_PtrFree( s_pMan->vTtTemps );
    if ( s_pMan->vLabels )
        Vec_PtrFree( s_pMan->vLabels );
    //if(s_pMan->pMemObj)
    //    Mem_FixedStop(s_pMan->pMemObj, 0);
    Vec_IntFree( s_pMan->vUselessPos);
    ABC_FREE(s_pMan->pRecObjs);
//  if(s_pMan->vFiltered)
//      Vec_StrFree(s_pMan->vFiltered);
        
    ABC_FREE( s_pMan );
    s_pMan = NULL;
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecCollectNodesFromLib_rec2(Gia_Man_t* pGia, Gia_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    if ( Gia_ObjIsPi(pGia, pNode))
        return;
    Abc_NtkRecCollectNodesFromLib_rec2(pGia, Gia_ObjFanin0(pNode), vNodes );
    Abc_NtkRecCollectNodesFromLib_rec2(pGia, Gia_ObjFanin1(pNode), vNodes );
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecCollectNodesFromLib2(Gia_Man_t* pGia, Gia_Obj_t * pRoot, Vec_Ptr_t * vNodes , int nVars)
{
    int i;
    // collect the internal nodes of the cut
    Vec_PtrClear( vNodes );
    for ( i = 0; i < nVars; i++ )
        Vec_PtrPush( vNodes, Gia_ManPi(pGia, i));


    // collect other nodes
    Abc_NtkRecCollectNodesFromLib_rec2(pGia, pRoot, vNodes );
}

/**Function*************************************************************

  Synopsis    [Computes truth tables of nodes in the cut.]

  Description [Returns 0 if the TT does not depend on some cut variables.
  Or if the TT can be expressed simpler using other nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecCutTruthFromLib2( Gia_Man_t * pGia2, Vec_Ptr_t * vNodes, int nLeaves, Vec_Ptr_t * vTtTemps, Vec_Ptr_t * vTtElems )
{
    unsigned * pSims, * pSims0, * pSims1;
    //unsigned * pTemp = s_pMan->pTemp2;
    Gia_Obj_t * pObj, * pRoot;
    int i, nInputs = s_pMan->nVars;

    assert( Vec_PtrSize(vNodes) > nLeaves );
    Vec_PtrForEachEntry( Gia_Obj_t *, vNodes, pObj, i )
    {
        Gia_ObjSetCopyF(pGia2, 0, pObj, i);
        pSims = Vec_PtrEntry(vTtTemps, i);
        if ( i < nLeaves )
        {
            Kit_TruthCopy( pSims, (unsigned *)Vec_PtrEntry(vTtElems, i), nInputs );
            continue;
        }
        // get hold of the simulation information
        pSims0 = (unsigned *)Vec_PtrEntry(vTtTemps,Gia_ObjCopyF(pGia2, 0, Gia_ObjFanin0(pObj)));
        pSims1 = (unsigned *)Vec_PtrEntry(vTtTemps,Gia_ObjCopyF(pGia2, 0, Gia_ObjFanin1(pObj)));
        // simulate the node
        Kit_TruthAndPhase( pSims, pSims0, pSims1, nInputs, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj) );
    }

    // check the support size
    pRoot = (Gia_Obj_t *)Vec_PtrEntryLast( vNodes );
    pSims = (unsigned *)Vec_PtrEntry(vTtTemps,Gia_ObjCopyF(pGia2, 0, pRoot));
    assert ( Kit_TruthSupport(pSims, nInputs) == Kit_BitMask(nLeaves) );
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecAddFromLib2( Gia_Man_t * pGia2, Gia_Obj_t * pRoot, int nVars )
{
    Gia_Obj_t * pObj = NULL, * pFanin0, * pFanin1, *pPO;
    int* ppSpot;
    Gia_Man_t * pGia = s_pMan->pGia;
    Gia_Obj_t * pAbcObj;
    Vec_Ptr_t * vNodes = s_pMan->vNodes;
    unsigned * pInOut = s_pMan->pTemp1;
    //unsigned * pTemp = s_pMan->pTemp2;
    unsigned *pTruth;//, *pTruthDst;
    int objectID;
    int i, nNodes, nNodesBeg, nInputs = s_pMan->nVars, nLeaves = nVars;
    assert( nInputs <= 16 );
    // collect internal nodes and skip redundant cuts
    Abc_NtkRecCollectNodesFromLib2(pGia2, pRoot, vNodes , nLeaves);
    Abc_NtkRecCutTruthFromLib2(pGia2, vNodes, nLeaves, s_pMan->vTtTemps, s_pMan->vTtElems );
    // copy the truth table
    Kit_TruthCopy( pInOut, (unsigned *)Vec_PtrEntry(s_pMan->vTtTemps, Gia_ObjCopyF(pGia2, 0, pRoot)), nInputs );
    // go through the variables in the new truth table
    for ( i = 0; i < nLeaves; i++ )
    {
        // get hold of the corresponding leaf
        pAbcObj = Gia_ManPi(pGia2, i);
        // get hold of the corresponding new node
        pObj = Gia_ManPi( pGia, i );
        // map them
        Gia_ObjSetCopyF(pGia2, 0, pAbcObj, Gia_ObjId(pGia,pObj));
    }

    nNodesBeg = Gia_ManObjNum( pGia );
    Vec_PtrForEachEntryStart( Gia_Obj_t *, vNodes, pAbcObj, i, nLeaves )
    {
        pFanin0 = Gia_NotCond(Gia_ManObj(pGia, Gia_ObjCopyF(pGia2, 0, Gia_ObjFanin0(pAbcObj))), Gia_ObjFaninC0(pAbcObj) );
        pFanin1 = Gia_NotCond(Gia_ManObj(pGia, Gia_ObjCopyF(pGia2, 0, Gia_ObjFanin1(pAbcObj))), Gia_ObjFaninC1(pAbcObj) );

        nNodes = Gia_ManObjNum( pGia );
        pObj = Gia_ObjFromLit(pGia, Gia_ManHashAnd(pGia, Gia_ObjToLit(pGia,pFanin0), Gia_ObjToLit(pGia,pFanin1) )) ;
        //assert( !Gia_IsComplement(pObj) );
        pObj = Gia_Regular(pObj);
        Gia_ObjSetCopyF(pGia2, 0, pAbcObj, Gia_ObjId(pGia,pObj));
    }
    assert(pObj);
    pTruth = Gia_ObjComputeTruthTable(pGia, pObj);
    //pTruth = (unsigned *)Vec_PtrEntry( s_pMan->vTtNodes, Gia_ObjId(pGia, pObj) );
    assert ( Kit_TruthSupport(pTruth, nInputs) == Kit_BitMask(nLeaves) );
    // compare the truth tables
    assert (Kit_TruthIsEqual( pTruth, pInOut, nInputs ) );

    if(s_pMan->nAddedFuncs > 2 * s_pMan->nBins)
        Abc_NtkRecResizeHash2(s_pMan);
    ppSpot = Abc_NtkRecTableLookup2(s_pMan, s_pMan->pBins,s_pMan->nBins , pTruth, nInputs ); 
    // if not new nodes were added and the node has a CO fanout

    if ( nNodesBeg == Gia_ManObjNum(pGia) && pObj->fMark1 == 1 )
    {
        s_pMan->nFilterSame++;
        //assert(*ppSpot != NULL);
        return;
    }

    // create PO for this node
    objectID = Gia_ObjId(pGia, pObj);
    pPO = Gia_ManObj(pGia, Gia_ManAppendCo(pGia, Gia_ObjToLit(pGia, pObj)) >> 1);
    pObj = Gia_ManObj(pGia, objectID);  
    assert(pObj->fMark1 == 0);
    pObj->fMark1 = 1;

//    if ( Vec_PtrSize(s_pMan->vTtNodes) <= Gia_ManPoNum(pGia) )
//    {
//        while ( Vec_PtrSize(s_pMan->vTtNodes) <= Gia_ObjCioId(pPO) )
//            Vec_PtrPush( s_pMan->vTtNodes, Mem_FixedEntryFetch(s_pMan->pMmTruth) );
//    }

//    pTruthDst = (unsigned *)Vec_PtrEntry( s_pMan->vTtNodes, Gia_ObjCioId(pPO));
//    Kit_TruthCopy(pTruthDst, pTruthSrc, s_pMan->nVars);
    //Rec_MemSetEntry( s_pMan, Gia_ObjCioId(pPO), pTruthSrc );

    // add the resulting truth table to the hash table 
    Abc_NtkRecInsertToLookUpTable2(s_pMan, ppSpot, pPO, nLeaves, pTruth, s_pMan->fTrim);
    return;
}

/**Function*************************************************************

  Synopsis    [Starts the record for the given network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecLibMerge2(Gia_Man_t* pGia2)
{
    int i;
    Gia_Obj_t * pObj;
    Abc_ManRec_t2 * p = s_pMan;
    int clk = clock();
    if ( Gia_ManPiNum(pGia2) > s_pMan->nVars )
    {
        printf( "The library has more inputs than the record.\n");
        return;
    }
    pGia2->pCopies = ABC_FALLOC( int, Gia_ManObjNum(pGia2) );
    // create hash table if not available
    if ( s_pMan->pGia->pHTable == NULL )
        Gia_ManHashStart( s_pMan->pGia );
    Abc_NtkRecMarkInputs(p, pGia2);

    // insert the PO nodes into the table
    Gia_ManForEachPo( pGia2, pObj, i )
    {
        p->nTried++;
        //if the PO's input is a constant, skip it.
        if (Gia_ObjChild0(pObj) == Gia_ManConst0(pGia2))
        {
            p->nTrimed++;
            continue;
        }   
        pObj = Gia_ObjFanin0(pObj);
        Abc_NtkRecAddFromLib2(pGia2, pObj, Abc_ObjGetMax2(s_pMan->vInputs, pGia2, pObj) );     
    }
    ABC_FREE(pGia2->pCopies);

    s_pMan->timeMerge += clock() - clk;
    s_pMan->timeTotal += clock() - clk;
}




ABC_NAMESPACE_IMPL_END