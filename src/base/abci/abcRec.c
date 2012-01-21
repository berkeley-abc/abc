/**CFile****************************************************************

  FileName    [abcRec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Record of semi-canonical AIG subgraphs.]

  Author      [Allan Yang, Alan Mishchenko]
  
  Affiliation [Fudan University in Shanghai, UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "src/base/abc/abc.h"
#include "src/map/if/if.h"
#include "src/bool/kit/kit.h"

ABC_NAMESPACE_IMPL_START

//#define LibOut
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define  IF_BIG_CHAR 120
typedef struct Abc_ManRec_t_ Abc_ManRec_t;
typedef struct Rec_Obj_t_ Rec_Obj_t;

typedef enum {
    REC_ERROR,                  //0: error
    REC_SMALL,                  //1: smaller than
    REC_EQUAL,                  //2: equal with
    REC_BIG,                    //3: bigger than    
    REC_DOMINANCE,              //4: dominance
    REC_BEDOMINANCED            //5: be dominated
} Abc_LookUpStatus_t;

struct Rec_Obj_t_
{
    Abc_Obj_t* obj;             // the actual structure in the library
    Rec_Obj_t* pNext;           // link to the next structure of the same functional class
    Rec_Obj_t* pCopy;           // link to the next functional class in the same bucket
    int Id;                     // structure's ID
    int nFrequency;             // appear times of this functional class among benchmarks
    unsigned char cost;         // structure's cost
    char* pinToPinDelay;        // structure's pin-to-pin delay
};


struct Abc_ManRec_t_
{
    Abc_Ntk_t *       pNtk;                     // the record
    Vec_Ptr_t *       vTtElems;                 // the elementary truth tables
    Vec_Ptr_t *       vTtNodes;                 // the node truth tables
    Mem_Fixed_t *     pMmTruth;                 // memory manager for truth tables
    Rec_Obj_t **      pBins;                    // hash table mapping truth tables into nodes
    int               nBins;                    // the number of allocated bins
    int               nVars;                    // the number of variables
    int               nVarsInit;                // the number of variables requested initially
    int               nWords;                   // the number of TT words
    int               nCuts;                    // the max number of cuts to use
    Mem_Fixed_t *     pMemObj;                  // memory manager for Rec objects
    int               recObjSize;               // size for one Rec object
    int               fTrim;                    // filter the library or not.
    // temporaries
    int *             pBytes;                   // temporary storage for minterms
    int *             pMints;                   // temporary storage for minterm counters
    unsigned *        pTemp1;                   // temporary truth table
    unsigned *        pTemp2;                   // temporary truth table
    unsigned *        pTempTruth;               // temporary truth table
    char *            pTempDepths;              // temporary depths
    int  *            pTempleaves;              // temporary leaves
    unsigned          tempUsign;
    unsigned          tempNleaves;
    unsigned          currentCost;
    int               currentDelay;
    Vec_Ptr_t *       vNodes;                   // the temporary nodes
    Vec_Ptr_t *       vTtTemps;                 // the truth tables for the internal nodes of the cut
    Vec_Ptr_t *       vLabels;                  // temporary storage for AIG node labels
    Vec_Str_t *       vCosts;                   // temporary storage for costs
    Vec_Int_t *       vMemory;                  // temporary memory for truth tables
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
    int               nIfMapTried;
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


// the truth table is canonicized in such a way that for (00000) its value is 0

static Rec_Obj_t ** Abc_NtkRecTableLookup( Abc_ManRec_t* p, Rec_Obj_t ** pBins, int nBins, unsigned * pTruth, int nVars );
static int          Abc_NtkRecComputeTruth( Abc_Obj_t * pObj, Vec_Ptr_t * vTtNodes, int nVars );
static int          Abc_NtkRecAddCutCheckCycle_rec( Abc_Obj_t * pRoot, Abc_Obj_t * pObj );
static void         Abc_NtkRecAddFromLib( Abc_Ntk_t* pNtk, Abc_Obj_t * pRoot, int nVars );
static void         Abc_NtkRecCurrentUnMark_rec(If_Obj_t * pObj);
static Abc_ManRec_t * s_pMan = NULL;

static inline void Abc_ObjSetMax( Abc_Obj_t * pObj, int Value ) { assert( pObj->Level < 0xff ); pObj->Level = (Value << 8) | (pObj->Level & 0xff); }
static inline void Abc_ObjClearMax( Abc_Obj_t * pObj )          { pObj->Level = (pObj->Level & 0xff); }
static inline int  Abc_ObjGetMax( Abc_Obj_t * pObj )            { return (pObj->Level >> 8) & 0xff; }

static inline void Abc_NtkRecFrequencyInc(Rec_Obj_t* entry)     
{   
    // the hit number of this functional class increased
    if (entry != NULL && entry->nFrequency < 0x7fffffff)
        entry->nFrequency += 1;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [stretch the truthtable to have more input variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_CutTruthStretch(unsigned* pInOut, int nVarS, int nVarB)
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

  Synopsis    [Alloc the Rec object from its manger.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

Rec_Obj_t* Rec_ObjAlloc(Abc_ManRec_t* p, Abc_Obj_t* pObj, char* pinToPinDelay, char cost, int nVar)
{
    int i;
    Rec_Obj_t * pRecObj;
    pRecObj = (Rec_Obj_t *)Mem_FixedEntryFetch( p->pMemObj);
    pRecObj->pinToPinDelay = (char*)(pRecObj + 1);
    pRecObj->pNext = NULL;
    pRecObj->pCopy = NULL;
    pRecObj->obj = pObj;
    pRecObj->Id = pObj->Id;
    for (i = 0; i < nVar; i++)
        pRecObj->pinToPinDelay[i] = pinToPinDelay[i];
    pRecObj->cost = cost;   
    pRecObj->nFrequency = 0;
    return pRecObj;
}

/**Function*************************************************************

  Synopsis    [set the property of a Rec object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rec_ObjSet(Abc_ManRec_t* p, Rec_Obj_t* pRecObj, Abc_Obj_t* pObj, char* newDelay, unsigned char cost, int nVar)
{
    int i;
    pRecObj->obj = pObj;
    pRecObj->Id = pObj->Id;
    pRecObj->cost = cost;
    for (i = 0; i < nVar; i++)
        pRecObj->pinToPinDelay[i] = newDelay[i];        
}

/**Function*************************************************************

  Synopsis    [Compute the delay of the structure recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/* int If_CutDelayRecComput_rec(Abc_Obj_t* pObj, Vec_Str_t* vCosts)
 {
    char Delay0, Delay1, Delay;
    Abc_Obj_t *pFanin0, *pFanin1;
    pObj = Abc_ObjRegular(pObj);
    if (Abc_NodeIsTravIdCurrent(pObj) || pObj->Type == ABC_OBJ_PI)
        return Vec_StrEntry(vCosts,pObj->Id);
    Abc_NodeSetTravIdCurrent(pObj);
    Delay0 = If_CutDelayRecComput_rec(Abc_ObjFanin0(pObj), vCosts);
    Delay1 = If_CutDelayRecComput_rec(Abc_ObjFanin1(pObj), vCosts);
    Delay = Abc_MaxInt(Delay0, Delay1) + 1;
    Vec_StrWriteEntry(vCosts,pObj->Id,Delay);
    return Delay;
 }*/

/**Function*************************************************************

  Synopsis    [Compute delay of the structure using pin-to-pin delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
inline int If_CutComputDelay(If_Man_t* p, Rec_Obj_t* entry, If_Cut_t* pCut, char* pCanonPerm , int nVars)
{
    If_Obj_t* pLeaf;
    int i, delayTemp, delayMax = -ABC_INFINITY;
    for (i = 0; i < nVars; i++)
    {
        pLeaf = If_ManObj(p, (pCut)->pLeaves[pCanonPerm[i]]);
        pLeaf = If_Regular(pLeaf);
        delayTemp = entry->pinToPinDelay[i] + If_ObjCutBest(pLeaf)->Delay;
        if(delayTemp > delayMax)
            delayMax = delayTemp;
    }
    // plus each pin's delay with its pin-to-output delay, the biggest one is the delay of the structure.
    return delayMax;
}

/**Function*************************************************************

  Synopsis    [Compute pin-to-pin delay of the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char If_CutDepthRecComput_rec(Abc_Obj_t* pObj, int iLeaf)
{
    char Depth0, Depth1, Depth;
    pObj = Abc_ObjRegular(pObj);
    if(pObj->Id == iLeaf)
        return 0;
    if(pObj->Type == ABC_OBJ_PI )
        return -IF_BIG_CHAR;
    Depth0 = If_CutDepthRecComput_rec(Abc_ObjFanin0(pObj), iLeaf);
    Depth1 = If_CutDepthRecComput_rec(Abc_ObjFanin1(pObj), iLeaf);
    Depth = Abc_MaxInt(Depth0, Depth1);
    Depth = (Depth == -IF_BIG_CHAR) ? -IF_BIG_CHAR : Depth + 1;
    assert(Depth <= 127);
    return Depth;
}

/**Function*************************************************************

  Synopsis    [Compute area of the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned char Abc_NtkRecAreaAndMark_rec(Abc_Obj_t* pObj)
{
    unsigned char Area0, Area1, Area;
    pObj = Abc_ObjRegular(pObj);
    if(Abc_ObjIsCi(pObj) || pObj->fMarkA == 1)
        return 0;
    Area0 = Abc_NtkRecAreaAndMark_rec(Abc_ObjFanin0(pObj));
    Area1 = Abc_NtkRecAreaAndMark_rec(Abc_ObjFanin1(pObj));
    Area = Area1 + Area0 + 1;
    assert(Area <= 255);
    pObj->fMarkA = 1;
    return Area;
}


/**Function*************************************************************

  Synopsis    [Compute area of the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecAreaUnMark_rec(Abc_Obj_t* pObj)
{
    pObj = Abc_ObjRegular(pObj);
    if ( Abc_ObjIsCi(pObj) || pObj->fMarkA == 0 )
        return;
    Abc_NtkRecAreaUnMark_rec( Abc_ObjFanin0(pObj) ); 
    Abc_NtkRecAreaUnMark_rec( Abc_ObjFanin1(pObj) );
    assert( pObj->fMarkA ); // loop detection
    pObj->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Compute area of the structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned char Abc_NtkRecArea(Abc_Obj_t* pObj)
{
    unsigned char area;
    area = Abc_NtkRecAreaAndMark_rec(pObj);
    Abc_NtkRecAreaUnMark_rec(pObj);
    return area;
}

/**Function*************************************************************

  Synopsis    [Compare delay profile of two structures.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

Abc_LookUpStatus_t ABC_NtkRecDelayCompare(char* delayFromStruct, char* delayFromTable, int nVar)
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

  Synopsis    [link a useless PO to constant 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecReplacePO(Abc_Obj_t* pObj )
{
    Abc_Obj_t * pConst0, * pFaninNew;
    Abc_Ntk_t * pNtk = pObj->pNtk;
    if ( Abc_ObjFanin0(pObj) == Abc_AigConst1(pNtk) )
    {
        if ( !Abc_ObjFaninC0(pObj) )
            Abc_ObjXorFaninC( pObj, 0 );
        return;
    }
    pConst0 = Abc_ObjNot( Abc_AigConst1(pNtk) );
    pFaninNew = Abc_ObjNotCond( pConst0, Abc_ObjFaninC0(pObj) );
    Abc_ObjPatchFanin( pObj, Abc_ObjFanin0(pObj), pFaninNew );
    assert( Abc_ObjChild0(pObj) == pConst0 );
    //Abc_AigCleanup( (Abc_Aig_t *)pNtk->pManFunc );
}

/**Function*************************************************************

  Synopsis    [Delete a useless structure in the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecDeleteSubGragh(Abc_ManRec_t* p, Abc_Obj_t* pObj)
{
    Abc_Obj_t* pFanOut;
    int i, deleted = 0;
    Abc_ObjForEachFanout(pObj, pFanOut, i)
    {
        if (Abc_ObjIsCo(pFanOut))
        {
            Abc_NtkRecReplacePO(pFanOut);
            deleted++;
            p->nTrimed++;
        }       
    }
    assert(deleted == 1);
}

/**Function*************************************************************

  Synopsis    [Check if the structure is dominant or not.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int ABC_NtkRecIsDominant(char* delayFromStruct, char* delayFromTable, int nVar)
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
void Abc_NtkRecSweepDominance(Abc_ManRec_t* p, Rec_Obj_t* previous, Rec_Obj_t* current, char * delayFromStruct, int nVars, int fTrim)
{
    Abc_Obj_t* pObj;
    while(current != NULL)
    {
        if (ABC_NtkRecIsDominant(delayFromStruct, current->pinToPinDelay, nVars))
        {
            pObj = current->obj;
            previous->pNext = current->pNext;
            current->pNext = NULL;
            Mem_FixedEntryRecycle(p->pMemObj, (char *)current);
            current = previous->pNext;
            p->nAdded--;
            // if filter the library is needed, then point the PO to a constant.
            if (fTrim)
                Abc_NtkRecDeleteSubGragh(p, pObj);
        }
        else
        {
            previous = current;
            current = current->pNext;
        }
    }
}


/**Function*************************************************************

  Synopsis    [Insert a structure into the look up table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecInsertToLookUpTable(Abc_ManRec_t* p, Rec_Obj_t** ppSpot, Abc_Obj_t* pObj, int nVars, int fTrim)
{
    char delayFromStruct[16] ;
    int i;  
    Abc_Obj_t* pLeaf;
    Rec_Obj_t* entry, *previous = NULL, *current = * ppSpot;
    unsigned char costFromStruct = Abc_NtkRecArea(pObj);
    Abc_LookUpStatus_t result;
    for (i = 0; i < nVars; i++)
    {
        pLeaf = Abc_NtkPi( p->pNtk,  i);
        pLeaf =Abc_ObjRegular(pLeaf);
        delayFromStruct[i] = If_CutDepthRecComput_rec(pObj, pLeaf->Id);
    }
    if(fTrim)
    {       
        while(1)
        {
            if (current == NULL)
            {
                p->nAdded++;
                entry = Rec_ObjAlloc(p, pObj, delayFromStruct, costFromStruct, nVars);          
                if(previous != NULL)
                {
                    previous->pNext = entry;
                }
                else
                {
                    // new functional class found
                    p->nAddedFuncs++;
                    *ppSpot = entry;
                    entry->nFrequency = 1;
                }
                break;
            }
            result = ABC_NtkRecDelayCompare(delayFromStruct, current->pinToPinDelay, nVars);    
            if(result == REC_EQUAL)
            {
                // when delay profile is equal, replace only if it has smaller cost.
                if(costFromStruct < current->cost)
                {   
                    Abc_NtkRecDeleteSubGragh(p, current->obj);
                    Rec_ObjSet(p, current, pObj, delayFromStruct, costFromStruct, nVars);
                }
                else
                    Abc_NtkRecDeleteSubGragh(p, pObj);
                break;
            }
            // when the new structure can dominate others, sweep them out of the library, delete them if required.
            else if(result == REC_DOMINANCE)
            {
                Abc_NtkRecDeleteSubGragh(p, current->obj);
                Rec_ObjSet(p, current, pObj, delayFromStruct, costFromStruct, nVars);
                Abc_NtkRecSweepDominance(p,current,current->pNext,delayFromStruct, nVars, fTrim);       
                break;
            }
            // when the new structure is domianted by an existed one, don't store it.
            else if (result == REC_BEDOMINANCED)
            {
                Abc_NtkRecDeleteSubGragh(p, pObj);
                break;
            }
            // when the new structure's delay profile is big than the current, test the next one
            else if (result == REC_BIG)
            {
                previous = current;
                current = current->pNext;
            }
            // insert the new structure to the right position, sweep the ones it can dominate.
            else if (result == REC_SMALL)
            {
                p->nAdded++;
                entry = Rec_ObjAlloc(p, pObj, delayFromStruct, costFromStruct, nVars);  
                if(previous != NULL)
                {
                    previous->pNext = entry;
                    entry->pNext = current;
                }
                else
                {
                    entry->pNext = current;
                    entry->pCopy = (*ppSpot)->pCopy;
                    entry->nFrequency = (*ppSpot)->nFrequency;
                    (*ppSpot)->pCopy = NULL;
                    (*ppSpot)->nFrequency = 0;
                    *ppSpot = entry;
                }
                Abc_NtkRecSweepDominance(p,current,current->pNext,delayFromStruct, nVars, fTrim);           
                break;
            }
            else
                assert(0);      
        }
    }
    else
    {
        if (current == NULL)
        {
            p->nAdded++;
            entry = Rec_ObjAlloc(p, pObj, delayFromStruct, costFromStruct, nVars);          
            p->nAddedFuncs++;
            *ppSpot = entry;
            entry->nFrequency = 1;
        }
        else
        {
            p->nAdded++;
            entry = Rec_ObjAlloc(p, pObj, delayFromStruct, costFromStruct, nVars);  
            entry->pNext = (*ppSpot)->pNext;
            (*ppSpot)->pNext = entry;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Build up the structure using library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
 Hop_Obj_t * Abc_NtkRecBuildUp_rec(Hop_Man_t* pMan, Abc_Obj_t* pObj, Vec_Ptr_t * vNodes)
 {
     Hop_Obj_t * pRes0, *pRes1, *pRes;
    Abc_Obj_t *pRegular = Abc_ObjRegular(pObj);
    if (Abc_NodeIsTravIdCurrent(pRegular) || pRegular->Type == ABC_OBJ_PI)
        return (Hop_Obj_t *)Vec_PtrEntry(vNodes, pRegular->Id);
    Abc_NodeSetTravIdCurrent(pRegular);
    pRes0 = Abc_NtkRecBuildUp_rec(pMan, Abc_ObjFanin0(pRegular), vNodes);
    pRes0 = Hop_NotCond(pRes0, pRegular->fCompl0);
    pRes1 = Abc_NtkRecBuildUp_rec(pMan, Abc_ObjFanin1(pRegular), vNodes);
    pRes1 = Hop_NotCond(pRes1, pRegular->fCompl1);
    pRes = Hop_And(pMan, pRes0, pRes1);
    Vec_PtrWriteEntry(vNodes,pRegular->Id,pRes);
    return pRes;
 }

 /**Function*************************************************************

  Synopsis    [Build up the structure using library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
 Hop_Obj_t * Abc_NtkRecBuildUpFromCurrent_rec(Hop_Man_t* pMan, If_Obj_t* pObj, Vec_Ptr_t * vNodes)
 {
     Hop_Obj_t * pRes0, *pRes1, *pRes;
    If_Obj_t *pRegular = If_Regular(pObj);
    if (Vec_PtrEntry(vNodes, pRegular->Id) && pRegular->fMark == 1)
        return (Hop_Obj_t *)Vec_PtrEntry(vNodes, pRegular->Id);
    pRes0 = Abc_NtkRecBuildUpFromCurrent_rec(pMan, If_ObjFanin0(pRegular), vNodes);
    pRes0 = Hop_NotCond(pRes0, pRegular->fCompl0);
    pRes1 = Abc_NtkRecBuildUpFromCurrent_rec(pMan, If_ObjFanin1(pRegular), vNodes);
    pRes1 = Hop_NotCond(pRes1, pRegular->fCompl1);
    pRes = Hop_And(pMan, pRes0, pRes1);
    Vec_PtrWriteEntry(vNodes,pRegular->Id,pRes);
    assert(pRegular->fMark == 0);
    pRegular->fMark = 1;
    return pRes;
 }

 /**Function*************************************************************

  Synopsis    [Derive the final network from the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
 Hop_Obj_t * Abc_RecFromCurrentToHop(Hop_Man_t * pMan, If_Man_t * pIfMan, If_Cut_t * pCut, If_Obj_t * pRoot)
 {
     int i;
     If_Obj_t * pLeaf;
     Hop_Obj_t* pHopObj;
     Vec_PtrGrow(s_pMan->vLabels, pIfMan->vObjs->nSize);
     s_pMan->vLabels->nSize = s_pMan->vLabels->nCap;
     If_CutForEachLeaf(pIfMan, pCut, pLeaf, i)
     {
         pHopObj = Hop_IthVar(pMan, i);
         Vec_PtrWriteEntry(s_pMan->vLabels, pLeaf->Id, pHopObj);
         assert(pLeaf->fMark == 0);
         pLeaf->fMark = 1;
     }
     pHopObj = Abc_NtkRecBuildUpFromCurrent_rec(pMan, pRoot, s_pMan->vLabels);
     Abc_NtkRecCurrentUnMark_rec(pRoot);
     return pHopObj;


 }

/**Function*************************************************************

  Synopsis    [Derive the final network from the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_RecToHop( Hop_Man_t * pMan, If_Man_t * pIfMan, If_Cut_t * pCut, If_Obj_t * pIfObj )
{
    Rec_Obj_t *pCand, *pCandMin, **ppSpot;
    Hop_Obj_t* pHopObj;
    Abc_Obj_t* pAbcObj;
    Abc_Ntk_t * pAig = s_pMan->pNtk;
    int nLeaves, i, DelayMin = ABC_INFINITY , Delay = -ABC_INFINITY;
    unsigned uCanonPhase;
    int nVars = s_pMan->nVars;
    char pCanonPerm[16];
    unsigned *pInOut = s_pMan->pTemp1;
    unsigned *pTemp = s_pMan->pTemp2;
    int time = clock();
    int fCompl = 0;
    nLeaves = If_CutLeaveNum(pCut);
//  if (nLeaves < 3)
//      return Abc_NodeTruthToHop(pMan, pIfMan, pCut);
    Kit_TruthCopy(pInOut, If_CutTruth(pCut), pCut->nLimit);
    for (i = 0; i < nLeaves; i++)
        pCanonPerm[i] = i;
    uCanonPhase = Kit_TruthSemiCanonicize(pInOut, pTemp, nLeaves, pCanonPerm, (short*)s_pMan->pMints);
    If_CutTruthStretch(pInOut, nLeaves, nVars);
    ppSpot = Abc_NtkRecTableLookup(s_pMan, s_pMan->pBins, s_pMan->nBins, pInOut, nVars );
    if (*ppSpot == NULL)
    {
        Kit_TruthNot(pInOut, pInOut, nVars);
        ppSpot = Abc_NtkRecTableLookup(s_pMan, s_pMan->pBins, s_pMan->nBins, pInOut, nVars );
        fCompl = 1;
    }
    assert(*ppSpot != NULL);
    DelayMin = ABC_INFINITY;
    pCandMin = NULL;
    // find the best one
    for ( pCand = *ppSpot; pCand; pCand = pCand->pNext )
    {
        s_pMan->nFunsDelayComput++; 
        Delay = If_CutComputDelay(pIfMan, pCand, pCut, pCanonPerm ,nLeaves);
        if ( DelayMin > Delay )
        {
            DelayMin = Delay;
            pCandMin = pCand;
        }
        else if(Delay == DelayMin)
        {
            if(pCand->cost < pCandMin->cost)
                pCandMin = pCand;
        }
    }
    assert( pCandMin != NULL );
    Vec_PtrGrow(s_pMan->vLabels, Abc_NtkObjNumMax(pAig));
    s_pMan->vLabels->nSize = s_pMan->vLabels->nCap;
    for (i = 0; i < nLeaves; i++)
    {
        pAbcObj = Abc_NtkPi( pAig, i );
        pHopObj = Hop_IthVar(pMan, pCanonPerm[i]);
        pHopObj = Hop_NotCond(pHopObj, ((uCanonPhase & (1 << i)) > 0));
        Vec_PtrWriteEntry(s_pMan->vLabels, pAbcObj->Id, pHopObj);
    }
    Abc_NtkIncrementTravId(pAig);
    //derive the best structure in the library.
    pHopObj = Abc_NtkRecBuildUp_rec(pMan, pCandMin->obj, s_pMan->vLabels);
    s_pMan->timeIfDerive += clock() - time;
    s_pMan->timeIfTotal += clock() - time;
    return Hop_NotCond(pHopObj, (pCut->fCompl)^(((uCanonPhase & (1 << nLeaves)) > 0)) ^ fCompl);    
}

/**Function*************************************************************

  Synopsis    [Duplicates non-danglingn nodes and POs driven by constants.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDupWithoutDangling_rec( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj )
{
    if ( pObj->pCopy != NULL )
        return;
    assert( Abc_ObjIsNode(pObj) );
    Abc_NtkDupWithoutDangling_rec( pNtkNew, Abc_ObjFanin0(pObj) );
    Abc_NtkDupWithoutDangling_rec( pNtkNew, Abc_ObjFanin1(pObj) );
    pObj->pCopy = Abc_AigAnd( (Abc_Aig_t *)pNtkNew->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Duplicates non-danglingn nodes and POs driven by constants.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkDupWithoutDangling( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsStrash(pNtk) );
    // start the network
    pNtkNew = Abc_NtkAlloc( pNtk->ntkType, pNtk->ntkFunc, 1 );
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pNtk->pSpec);
    // clean the node copy fields
    Abc_NtkCleanCopy( pNtk );
    // map the constant nodes
    Abc_AigConst1(pNtk)->pCopy = Abc_AigConst1(pNtkNew);
    // clone PIs
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj, 0 );
    // recursively add non-dangling logic
    Abc_NtkForEachPo( pNtk, pObj, i )
        if ( Abc_ObjFanin0(pObj) != Abc_AigConst1(pNtk) )
            Abc_NtkDupWithoutDangling_rec( pNtkNew, Abc_ObjFanin0(pObj) );
    // clone POs
    Abc_NtkForEachPo( pNtk, pObj, i )
        if ( Abc_ObjFanin0(pObj) != Abc_AigConst1(pNtk) )
        {
            Abc_NtkDupObj( pNtkNew, pObj, 0 );
            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pObj)->pCopy );
        } 
    Abc_NtkAddDummyPiNames( pNtkNew );
    Abc_NtkAddDummyPoNames( pNtkNew );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkDupWithoutDangling(): Network check has failed.\n" );
    pNtk->pCopy = pNtkNew;
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Filter the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_RecUpdateHashTable()
{
    Abc_ManRec_t * p = s_pMan;
    Rec_Obj_t * pEntry, * pTemp;
    int i;
    for ( i = 0; i < p->nBins; i++ )
        for ( pEntry = p->pBins[i]; pEntry; pEntry = pEntry->pCopy )
            for ( pTemp = pEntry; pTemp; pTemp = pTemp->pNext )
                pTemp->obj = pTemp->obj->pCopy;
}

/**Function*************************************************************

  Synopsis    [Filter the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecFilter(int nLimit)
{
    Rec_Obj_t * previous = NULL, * entry = NULL, * pTemp;
    int i;
    Abc_Ntk_t * pNtk = s_pMan->pNtk;
    int time = clock();
    if (nLimit > 0)
    {
        for ( i = 0; i < s_pMan->nBins; i++ )
        {
            previous = NULL;
            for ( entry = s_pMan->pBins[i]; entry; entry = entry->pCopy)
            {
                assert(entry->nFrequency != 0);
                // only filter the functional classed with frequency less than nLimit.
                if(entry->nFrequency > nLimit)
                {
                    previous = entry;
                    continue;
                }
                if(previous == NULL)
                {
                    s_pMan->pBins[i] = entry->pCopy;
                    previous = NULL;
                }
                else
                    previous->pCopy = entry->pCopy;

                s_pMan->nAddedFuncs--;
                //delete all the subgragh.
                for ( pTemp = entry; pTemp; pTemp = pTemp->pNext )
                {       
                    s_pMan->nAdded--;
                    Abc_NtkRecDeleteSubGragh(s_pMan, pTemp->obj);
                    Mem_FixedEntryRecycle(s_pMan->pMemObj, (char *)pTemp);              
                }
            }
        }
    }

    // remove dangling nodes and POs driven by constants
    s_pMan->pNtk = Abc_NtkDupWithoutDangling( pNtk );
    Abc_RecUpdateHashTable();
    Abc_NtkDelete( pNtk );

    // collect runtime stats
    s_pMan->timeTrim += clock() - time;
    s_pMan->timeTotal += clock() - time;
}



/**Function*************************************************************

  Synopsis    [Test if the record is running.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecIsRunning()
{
    return s_pMan != NULL;
}

/**Function*************************************************************

  Synopsis    [Test if the record is working in trim mode.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecIsInTrimMode()
{
    return (s_pMan != NULL && s_pMan->fTrim);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecVarNum()
{
    return (s_pMan != NULL)? s_pMan->nVars : -1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkRecMemory()
{
    return s_pMan->vMemory;
}

/**Function*************************************************************

  Synopsis    [Starts the record for the given network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecLibMerge(Abc_Ntk_t* pNtk)
{
    int i;
    Abc_Obj_t * pObj;
    Abc_ManRec_t * p = s_pMan;
    int clk = clock();
    if ( Abc_NtkPiNum(pNtk) > s_pMan->nVars )
    {
        printf( "The library has more inputs than the record.\n");
        return;
    }
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_ObjSetMax( pObj, i+1 );
    Abc_AigForEachAnd( pNtk, pObj, i )
        Abc_ObjSetMax( pObj, Abc_MaxInt( Abc_ObjGetMax(Abc_ObjFanin0(pObj)), Abc_ObjGetMax(Abc_ObjFanin1(pObj)) ) );

    // insert the PO nodes into the table
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        p->nTried++;
        //if the PO's input is a constant, skip it.
        if (Abc_ObjChild0(pObj) == Abc_ObjNot( Abc_AigConst1(pNtk)))
        {
            p->nTrimed++;
            continue;
        }   
        pObj = Abc_ObjFanin0(pObj); 
        Abc_NtkRecAddFromLib(pNtk, pObj, Abc_ObjGetMax(pObj) );     
    }
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        Abc_ObjClearMax( pObj );
    }
    s_pMan->timeMerge += clock() - clk;
    s_pMan->timeTotal += clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Resize the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecRezieHash(Abc_ManRec_t* p)
{
    Rec_Obj_t ** pBinsNew, **ppSpot;
    Rec_Obj_t * pEntry, * pTemp;
    int nBinsNew, Counter, i;
    int clk = clock();
    // get the new table size
    nBinsNew = Abc_PrimeCudd( 3 * p->nBins ); 
    printf("Hash table resize from %d to %d.\n", p->nBins, nBinsNew);
    // allocate a new array
    pBinsNew = ABC_ALLOC( Rec_Obj_t *, nBinsNew );
    memset( pBinsNew, 0, sizeof(Rec_Obj_t *) * nBinsNew );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < p->nBins; i++ )
        for ( pEntry = p->pBins[i]; pEntry;)
        {          
            pTemp = pEntry->pCopy;
            ppSpot = Abc_NtkRecTableLookup(p, pBinsNew, nBinsNew, (unsigned *)Vec_PtrEntry(p->vTtNodes, pEntry->Id), p->nVars);
            assert(*ppSpot == NULL);
            *ppSpot = pEntry;
            pEntry->pCopy = NULL;
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

  Synopsis    [Starts the record for the given network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecStart( Abc_Ntk_t * pNtk, int nVars, int nCuts, int fTrim )
{
    Abc_ManRec_t * p;
    Abc_Obj_t * pObj;
    Rec_Obj_t** ppSpot;
    char Buffer[10];
    unsigned * pTruth;
    int i, RetValue;
    int clkTotal = clock(), clk, timeInsert;
    int testNum = 0;

    assert( s_pMan == NULL );
    if ( pNtk == NULL )
    {
        assert( nVars > 2 && nVars <= 16 );
        pNtk = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1 );
        pNtk->pName = Extra_UtilStrsav( "record" );
    }
    else
    {
        if ( Abc_NtkGetChoiceNum(pNtk) > 0 )
        {
            printf( "The starting record should be a network without choice nodes.\n" );
            return;
        }
        if ( Abc_NtkPiNum(pNtk) > 16 )
        {
            printf( "The starting record should be a network with no more than %d primary inputs.\n", 16 );
            return;
        }
        if ( Abc_NtkPiNum(pNtk) > nVars )
            printf( "The starting record has %d inputs (warning only).\n", Abc_NtkPiNum(pNtk) );
        pNtk = Abc_NtkDup( pNtk );
    }
    // create the primary inputs
    for ( i = Abc_NtkPiNum(pNtk); i < nVars; i++ )
    {
        pObj = Abc_NtkCreatePi( pNtk );
        Buffer[0] = 'a' + i;
        Buffer[1] = 0;
        Abc_ObjAssignName( pObj, Buffer, NULL );
    }
    Abc_NtkCleanCopy( pNtk );
    Abc_NtkCleanEquiv( pNtk );

    // start the manager
    p = ABC_ALLOC( Abc_ManRec_t, 1 );
    memset( p, 0, sizeof(Abc_ManRec_t) );
    p->pNtk = pNtk;
    p->nVars = Abc_NtkPiNum(pNtk);
    p->nWords = Kit_TruthWordNum( p->nVars );
    p->nCuts = nCuts;
    p->nVarsInit = nVars;
    p->recObjSize = sizeof(Rec_Obj_t) + sizeof(char) * p->nVars;
    p->pMemObj = Mem_FixedStart(p->recObjSize);
    p->fTrim = fTrim;
    // create elementary truth tables
    p->vTtElems = Vec_PtrAlloc( 0 ); assert( p->vTtElems->pArray == NULL );
    p->vTtElems->nSize = p->nVars;
    p->vTtElems->nCap = p->nVars;
    p->vTtElems->pArray = (void **)Extra_TruthElementary( p->nVars );        
/*
    // allocate room for node truth tables
    if ( Abc_NtkObjNum(pNtk) > (1<<14) )
        p->vTtNodes = Vec_PtrAllocSimInfo( 2 * Abc_NtkObjNum(pNtk), p->nWords );
    else
        p->vTtNodes = Vec_PtrAllocSimInfo( 1<<14, p->nWords );
*/
    p->vTtNodes = Vec_PtrAlloc( 1000 );
    p->pMmTruth = Mem_FixedStart( sizeof(unsigned)*p->nWords );
    for ( i = 0; i < Abc_NtkObjNumMax(pNtk); i++ )
//        Vec_PtrPush( p->vTtNodes, ABC_ALLOC(unsigned, p->nWords) );
        Vec_PtrPush( p->vTtNodes, Mem_FixedEntryFetch(p->pMmTruth) );

    // create hash table
    //p->nBins = 50011;
    p->nBins =500011;
    p->pBins = ABC_ALLOC( Rec_Obj_t *, p->nBins );
    memset( p->pBins, 0, sizeof(Rec_Obj_t *) * p->nBins );

    // set elementary tables
    Kit_TruthFill( (unsigned *)Vec_PtrEntry(p->vTtNodes, 0), p->nVars );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Kit_TruthCopy( (unsigned *)Vec_PtrEntry(p->vTtNodes, pObj->Id), (unsigned *)Vec_PtrEntry(p->vTtElems, i), p->nVars );

    // compute the tables
clk = clock();
    
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        RetValue = Abc_NtkRecComputeTruth( pObj, p->vTtNodes, p->nVars );
        assert( RetValue );
    }
p->timeTruth += clock() - clk;

    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_ObjSetMax( pObj, i+1 );
    Abc_AigForEachAnd( pNtk, pObj, i )
        Abc_ObjSetMax( pObj, Abc_MaxInt( Abc_ObjGetMax(Abc_ObjFanin0(pObj)), Abc_ObjGetMax(Abc_ObjFanin1(pObj)) ) );

    // insert the PO nodes into the table
    timeInsert = clock();
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        p->nTried++;
        //if the PO's input is a constant, skip it.
        if (Abc_ObjChild0(pObj) == Abc_ObjNot( Abc_AigConst1(pNtk)))
        {
            p->nTrimed++;
            continue;
        }   
        pObj = Abc_ObjFanin0(pObj);     
        pTruth = (unsigned *)Vec_PtrEntry( p->vTtNodes, pObj->Id );
        // add the resulting truth table to the hash table 
        if(p->nAddedFuncs > 2 * p->nBins)
            Abc_NtkRecRezieHash(p);
        ppSpot = Abc_NtkRecTableLookup(p, p->pBins, p->nBins, pTruth, p->nVars );
        Abc_NtkRecInsertToLookUpTable(p, ppSpot, pObj, Abc_ObjGetMax(pObj), p->fTrim);       
    }
    p->timeInsert += clock() - timeInsert;
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        Abc_ObjClearMax( pObj );
    }
    // temporaries
    p->pBytes = ABC_ALLOC( int, 4*p->nWords );
    p->pMints = ABC_ALLOC( int, 2*p->nVars );
    p->pTemp1 = ABC_ALLOC( unsigned, p->nWords );
    p->pTemp2 = ABC_ALLOC( unsigned, p->nWords );
    p->pTempTruth = ABC_ALLOC( unsigned, p->nWords );
    p->pTempDepths = ABC_ALLOC( char, p->nVars );
    p->pTempleaves = ABC_ALLOC( int, p->nVars );
    p->vNodes = Vec_PtrAlloc( 100 );
    p->vTtTemps = Vec_PtrAllocSimInfo( 1024, p->nWords );
    p->vMemory = Vec_IntAlloc( Abc_TruthWordNum(p->nVars) * 1000 );
    p->vLabels = Vec_PtrStart( 1000);

    // set the manager
    s_pMan = p;
    p->timeTotal += clock() - clkTotal;
}

/**Function*************************************************************

  Synopsis    [Dump truth tables into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecDumpTruthTables( Abc_ManRec_t * p )
{
    int nVars = 10;
    FILE * pFile;
    Rec_Obj_t * pObj;
    unsigned * pTruth;
    int i;
    pFile = fopen( "tt10.txt", "wb" );
    for ( i = 0; i < p->nBins; i++ )
        for ( pObj = p->pBins[i]; pObj; pObj = pObj->pCopy )
        {
            pTruth = (unsigned *)Vec_PtrEntry(p->vTtNodes, pObj->Id);
            if ( (int)Kit_TruthSupport(pTruth, nVars) != (1<<nVars)-1 )
                continue;
            Extra_PrintHex( pFile, pTruth, nVars );
            fprintf( pFile, " " );
            Kit_DsdPrintFromTruth2( pFile, pTruth, nVars );
            fprintf( pFile, "\n" );
        }
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Returns the given record.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecStop()
{
    assert( s_pMan != NULL );
//    Abc_NtkRecDumpTruthTables( s_pMan );
    if ( s_pMan->pNtk )
        Abc_NtkDelete( s_pMan->pNtk );
//    Vec_PtrFreeFree( s_pMan->vTtNodes );
    Mem_FixedStop( s_pMan->pMmTruth, 0 );
    Vec_PtrFree( s_pMan->vTtNodes );
    Vec_PtrFree( s_pMan->vTtElems );
    ABC_FREE( s_pMan->pBins );

    // temporaries
    ABC_FREE( s_pMan->pBytes );
    ABC_FREE( s_pMan->pMints );
    ABC_FREE( s_pMan->pTemp1 );
    ABC_FREE( s_pMan->pTemp2 );
    ABC_FREE( s_pMan->pTempTruth );
    ABC_FREE( s_pMan->pTempDepths );
    Vec_PtrFree( s_pMan->vNodes );
    Vec_PtrFree( s_pMan->vTtTemps );
    if ( s_pMan->vLabels )
        Vec_PtrFree( s_pMan->vLabels );
    if ( s_pMan->vCosts )
        Vec_StrFree( s_pMan->vCosts );
    if(s_pMan->pMemObj)
        Mem_FixedStop(s_pMan->pMemObj, 0);
    Vec_IntFree( s_pMan->vMemory );
//  if(s_pMan->vFiltered)
//      Vec_StrFree(s_pMan->vFiltered);
        
    ABC_FREE( s_pMan );
    s_pMan = NULL;
}

/**Function*************************************************************

  Synopsis    [Returns the given record.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkRecUse()
{
    Abc_ManRec_t * p = s_pMan;
    Abc_Ntk_t * pNtk = p->pNtk;
    assert( p != NULL );
    Abc_NtkRecPs(0);
    p->pNtk = NULL;
    Abc_NtkRecStop();
    Abc_NtkCleanData(pNtk);
    return pNtk;
}


/**Function*************************************************************

  Synopsis    [Print statistics about the current record.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecPs(int fPrintLib)
{
    int Counter, Counters[17] = {0};
    int CounterS, CountersS[17] = {0};
    Abc_ManRec_t * p = s_pMan;
    Abc_Ntk_t * pNtk = p->pNtk;
    Rec_Obj_t * pEntry, * pTemp;
    Abc_Obj_t * pObj;
    int i;
    FILE * pFile;
    unsigned* pTruth;
    Rec_Obj_t* entry;
    int j;
    int nVars = s_pMan->nVars;
    // set the max PI number
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_ObjSetMax( pObj, i+1 );
    Abc_AigForEachAnd( pNtk, pObj, i )
        Abc_ObjSetMax( pObj, Abc_MaxInt( Abc_ObjGetMax(Abc_ObjFanin0(pObj)), Abc_ObjGetMax(Abc_ObjFanin1(pObj)) ) );
if(fPrintLib)
{
    pFile = fopen( "tt10.txt", "wb" );
for ( i = 0; i < p->nBins; i++ )
    for ( entry = p->pBins[i]; entry; entry = entry->pCopy )
    {
        int tmp = 0;
        pTruth = (unsigned *)Vec_PtrEntry(p->vTtNodes, entry->Id);
        /*if ( (int)Kit_TruthSupport(pTruth, nVars) != (1<<nVars)-1 )
            continue;*/
        Extra_PrintHex( pFile, pTruth, nVars );
        fprintf( pFile, " : nVars:  %d, Frequency:%d, nBin:%d  :  ", Abc_ObjGetMax(entry->obj), entry->nFrequency, i);
        Kit_DsdPrintFromTruth2( pFile, pTruth, Abc_ObjGetMax(entry->obj) );
        fprintf( pFile, "\n" );
        for ( pTemp = entry; pTemp; pTemp = pTemp->pNext )
        {
            fprintf(pFile,"%d :", tmp);
            for (j = 0; j <Abc_ObjGetMax(pTemp->obj); j++)
            {
                fprintf(pFile, " %d, ", pTemp->pinToPinDelay[j]);
            }
            fprintf(pFile, "cost = %d ID = %d\n", pTemp->cost, pTemp->Id);             
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
    for ( pEntry = p->pBins[i]; pEntry; pEntry = pEntry->pCopy )
    {
        assert(Abc_ObjGetMax(pEntry->obj) >= 2);    
        Counters[ Abc_ObjGetMax(pEntry->obj)]++;
        Counter++;
        for ( pTemp = pEntry; pTemp; pTemp = pTemp->pNext )
        {
            assert( Abc_ObjGetMax(pTemp->obj) == Abc_ObjGetMax(pEntry->obj) );
            CountersS[ Abc_ObjGetMax(pTemp->obj) ]++;
            CounterS++;
        }
    }
    //printf( "Functions = %d. Expected = %d.\n", Counter, p->nAddedFuncs );
    //printf( "Subgraphs = %d. Expected = %d.\n", CounterS, p->nAdded );
    assert( Counter == p->nAddedFuncs );
    assert( CounterS == p->nAdded );
    // clean
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        Abc_ObjClearMax( pObj );
    }
    printf( "The record with %d AND nodes in %d subgraphs for %d functions with %d inputs:\n", 
        Abc_NtkNodeNum(pNtk), Abc_NtkPoNum(pNtk), p->nAddedFuncs, Abc_NtkPiNum(pNtk) );
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
Rec_Obj_t ** Abc_NtkRecTableLookup(Abc_ManRec_t* p,  Rec_Obj_t ** pBins, int nBins, unsigned * pTruth, int nVars )
{
    static int s_Primes[10] = { 1291, 1699, 2357, 4177, 5147, 5647, 6343, 7103, 7873, 8147 };
    Rec_Obj_t ** ppSpot, * pEntry;
    ppSpot = pBins + Abc_NtkRecTableHash( pTruth, nVars, nBins, s_Primes );
    for ( pEntry = *ppSpot; pEntry; ppSpot = &pEntry->pCopy, pEntry = pEntry->pCopy )
        if ( Kit_TruthIsEqualWithPhase((unsigned *)Vec_PtrEntry(p->vTtNodes, pEntry->Id), pTruth, nVars) )
            return ppSpot;
    return ppSpot;
}

/**Function*************************************************************

  Synopsis    [Computes the truth table of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecComputeTruth( Abc_Obj_t * pObj, Vec_Ptr_t * vTtNodes, int nVars )
{
    unsigned * pTruth, * pTruth0, * pTruth1;
    int RetValue;
    assert( Abc_ObjIsNode(pObj) );
    pTruth  = (unsigned *)Vec_PtrEntry( vTtNodes, pObj->Id );
    pTruth0 = (unsigned *)Vec_PtrEntry( vTtNodes, Abc_ObjFaninId0(pObj) );
    pTruth1 = (unsigned *)Vec_PtrEntry( vTtNodes, Abc_ObjFaninId1(pObj) );
    Kit_TruthAndPhase( pTruth, pTruth0, pTruth1, nVars, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    assert( (pTruth[0] & 1) == pObj->fPhase );
    RetValue = ((pTruth[0] & 1) == pObj->fPhase);
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Performs renoding as technology mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecAdd( Abc_Ntk_t * pNtk )
{
    extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
    extern int Abc_NtkRecAddCut( If_Man_t * pIfMan, If_Obj_t * pRoot, If_Cut_t * pCut );

    If_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkNew;
    int clk = clock();

    if ( Abc_NtkGetChoiceNum( pNtk ) )
        printf( "Performing renoding with choices.\n" );

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
    pPars->fTruth      =  1;
    pPars->fUsePerm    =  0; 
    pPars->nLatches    =  0;
    pPars->pLutLib     =  NULL; // Abc_FrameReadLibLut();
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->fUseBdds    =  0;
    pPars->fUseSops    =  0;
    pPars->fUseCnfs    =  0;
    pPars->fUseMv      =  0;
    pPars->fSkipCutFilter = 1;
    pPars->pFuncCost   =  NULL;
    pPars->pFuncUser   =  Abc_NtkRecAddCut;

    // perform recording
    pNtkNew = Abc_NtkIf( pNtk, pPars );
    Abc_NtkDelete( pNtkNew );
s_pMan->timeTotal += clock() - clk;

//    if ( !Abc_NtkCheck( s_pMan->pNtk ) )
//        printf( "Abc_NtkRecAdd: The network check has failed.\n" );
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecCollectNodes_rec( If_Obj_t * pNode, Vec_Ptr_t * vNodes )
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
void Abc_NtkRecCollectNodesFromLib_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    if ( Abc_ObjIsPi(pNode))
        return;
    Abc_NtkRecCollectNodesFromLib_rec( Abc_ObjFanin0(pNode), vNodes );
    Abc_NtkRecCollectNodesFromLib_rec( Abc_ObjFanin1(pNode), vNodes );
    Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecCollectNodes( If_Man_t * pIfMan, If_Obj_t * pRoot, If_Cut_t * pCut, Vec_Ptr_t * vNodes )
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
/*
    if ( pRoot->Id == 2639 )
    {
        // print the cut
        Vec_PtrForEachEntry( If_Obj_t *, vNodes, pLeaf, i )
        {
            if ( If_ObjIsAnd(pLeaf) )
                printf( "%4d = %c%4d & %c%4d\n", pLeaf->Id, 
                    (If_ObjFaninC0(pLeaf)? '-':'+'), If_ObjFanin0(pLeaf)->Id, 
                    (If_ObjFaninC1(pLeaf)? '-':'+'), If_ObjFanin1(pLeaf)->Id ); 
            else
                printf( "%4d = pi\n", pLeaf->Id ); 
        }
        printf( "\n" );
    }
*/
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecCollectNodesFromLib(Abc_Ntk_t* pNtk, Abc_Obj_t * pRoot, Vec_Ptr_t * vNodes , int nVars)
{
    int i;
    // collect the internal nodes of the cut
    Vec_PtrClear( vNodes );
    for ( i = 0; i < nVars; i++ )
        Vec_PtrPush( vNodes, Abc_NtkPi(pNtk, i));


    // collect other nodes
    Abc_NtkRecCollectNodesFromLib_rec( pRoot, vNodes );
}

/**Function*************************************************************

  Synopsis    [Computes truth tables of nodes in the cut.]

  Description [Returns 0 if the TT does not depend on some cut variables.
  Or if the TT can be expressed simpler using other nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecCutTruth( Vec_Ptr_t * vNodes, int nLeaves, Vec_Ptr_t * vTtTemps, Vec_Ptr_t * vTtElems )
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

  Synopsis    [Computes truth tables of nodes in the cut.]

  Description [Returns 0 if the TT does not depend on some cut variables.
  Or if the TT can be expressed simpler using other nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecCutTruthFromLib( Vec_Ptr_t * vNodes, int nLeaves, Vec_Ptr_t * vTtTemps, Vec_Ptr_t * vTtElems )
{
    unsigned * pSims, * pSims0, * pSims1;
    unsigned * pTemp = s_pMan->pTemp2;
    Abc_Obj_t * pObj, * pRoot;
    int i, nInputs = s_pMan->nVars;

    assert( Vec_PtrSize(vNodes) > nLeaves );

    // set the elementary truth tables and compute the truth tables of the nodes
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        pObj->pTemp = Vec_PtrEntry(vTtTemps, i);
        pSims = (unsigned *)pObj->pTemp;
        if ( i < nLeaves )
        {
            Kit_TruthCopy( pSims, (unsigned *)Vec_PtrEntry(vTtElems, i), nInputs );
            continue;
        }
        // get hold of the simulation information
        pSims0 = (unsigned *)Abc_ObjFanin0(pObj)->pTemp;
        pSims1 = (unsigned *)Abc_ObjFanin1(pObj)->pTemp;
        // simulate the node
        Kit_TruthAndPhase( pSims, pSims0, pSims1, nInputs, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    }

    // check the support size
    pRoot = (Abc_Obj_t *)Vec_PtrEntryLast( vNodes );
    pSims = (unsigned *)pRoot->pTemp;
    assert ( Kit_TruthSupport(pSims, nInputs) == Kit_BitMask(nLeaves) );
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecAddCutCheckCycle_rec( Abc_Obj_t * pRoot, Abc_Obj_t * pObj )
{
    assert( pRoot->Level > 0 );
    if ( pObj->Level < pRoot->Level )
        return 1;
    if ( pObj == pRoot )
        return 0;
    if ( !Abc_NtkRecAddCutCheckCycle_rec(pRoot, Abc_ObjFanin0(pObj)) )
        return 0;
    if ( !Abc_NtkRecAddCutCheckCycle_rec(pRoot, Abc_ObjFanin1(pObj)) )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecAddCut( If_Man_t * pIfMan, If_Obj_t * pRoot, If_Cut_t * pCut )
{
    static int s_MaxSize[16] = { 0 };
    char Buffer[40], Name[20], Truth[20];
    char pCanonPerm[16];
    Abc_Obj_t * pObj = NULL, * pFanin0, * pFanin1, * pObjPo;
    Rec_Obj_t ** ppSpot;
    Abc_Ntk_t * pAig = s_pMan->pNtk;
    If_Obj_t * pIfObj;
    Vec_Ptr_t * vNodes = s_pMan->vNodes;
    unsigned * pInOut = s_pMan->pTemp1;
    unsigned * pTemp = s_pMan->pTemp2;
    unsigned * pTruth;
    int i, RetValue, nNodes, nNodesBeg, nInputs = s_pMan->nVars, nLeaves = If_CutLeaveNum(pCut);
    unsigned uCanonPhase;
    int clk, timeInsert, timeBuild;
    int begin = clock();
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
    uCanonPhase = Kit_TruthSemiCanonicize( pInOut, pTemp, nLeaves, pCanonPerm, (short *)s_pMan->pMints );
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
        pObj = Abc_NtkPi( pAig, i );
        pObj = Abc_ObjNotCond( pObj, (uCanonPhase & (1 << i)) );
        // map them
        pIfObj->pCopy = pObj;
    }

    // build the node and compute its truth table
    nNodesBeg = Abc_NtkObjNumMax( pAig );
    Vec_PtrForEachEntryStart( If_Obj_t *, vNodes, pIfObj, i, nLeaves )
    {
        pFanin0 = Abc_ObjNotCond( (Abc_Obj_t *)If_ObjFanin0(pIfObj)->pCopy, If_ObjFaninC0(pIfObj) );
        pFanin1 = Abc_ObjNotCond( (Abc_Obj_t *)If_ObjFanin1(pIfObj)->pCopy, If_ObjFaninC1(pIfObj) );

        nNodes = Abc_NtkObjNumMax( pAig );
        pObj = Abc_AigAnd( (Abc_Aig_t *)pAig->pManFunc, pFanin0, pFanin1 );
        assert( !Abc_ObjIsComplement(pObj) );
        pIfObj->pCopy = pObj;

        if ( pObj->Id == nNodes )
        {
            // increase storage for truth tables
//            if ( Vec_PtrSize(s_pMan->vTtNodes) <= pObj->Id )
//                Vec_PtrDoubleSimInfo(s_pMan->vTtNodes);
            while ( Vec_PtrSize(s_pMan->vTtNodes) <= pObj->Id )
//                Vec_PtrPush( s_pMan->vTtNodes, ABC_ALLOC(unsigned, s_pMan->nWords) );
                Vec_PtrPush( s_pMan->vTtNodes, Mem_FixedEntryFetch(s_pMan->pMmTruth) );

            // compute the truth table
            RetValue = Abc_NtkRecComputeTruth( pObj, s_pMan->vTtNodes, nInputs );
            if ( RetValue == 0 )
            {
                s_pMan->nFilterError++;
                printf( "T" );
                return 1;
            }
        }
    }
    assert(pObj);
    s_pMan->timeBuild += clock() - timeBuild;
    pTruth = (unsigned *)Vec_PtrEntry( s_pMan->vTtNodes, pObj->Id );
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
        Abc_NtkRecRezieHash(s_pMan);
    ppSpot = Abc_NtkRecTableLookup(s_pMan, s_pMan->pBins,s_pMan->nBins , pTruth, nInputs );
    Abc_NtkRecFrequencyInc(*ppSpot);   
    // if not new nodes were added and the node has a CO fanout
    
    if ( nNodesBeg == Abc_NtkObjNumMax(pAig) && Abc_NodeFindCoFanout(pObj) != NULL )
    {
        s_pMan->nFilterSame++;
        //assert(*ppSpot != NULL);
        return 1;
    }

    // create PO for this node
    pObjPo = Abc_NtkCreatePo(pAig);
    Abc_ObjAddFanin( pObjPo, pObj );

    // assign the name to this PO
    sprintf( Name, "%d_%06d", nLeaves, Abc_NtkPoNum(pAig) );
    if ( (nInputs <= 6) && 0 )
    {
        Extra_PrintHexadecimalString( Truth, pInOut, nInputs );
        sprintf( Buffer, "%s_%s", Name, Truth );
    }
    else
    {
        sprintf( Buffer, "%s", Name );
    }
    Abc_ObjAssignName( pObjPo, Buffer, NULL );

    // add the resulting truth table to the hash table 
    timeInsert = clock();
    Abc_NtkRecInsertToLookUpTable(s_pMan, ppSpot, pObj, nLeaves, s_pMan->fTrim);
    s_pMan->timeInsert += clock() - timeInsert;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds the cut function to the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecAddFromLib( Abc_Ntk_t* pNtk, Abc_Obj_t * pRoot, int nVars )
{
    char Buffer[40], Name[20], Truth[20];
    Abc_Obj_t * pObj = NULL, * pFanin0, * pFanin1, * pObjPo;
    Rec_Obj_t ** ppSpot;
    Abc_Ntk_t * pAig = s_pMan->pNtk;
    Abc_Obj_t * pAbcObj;
    Vec_Ptr_t * vNodes = s_pMan->vNodes;
    unsigned * pInOut = s_pMan->pTemp1;
    unsigned * pTemp = s_pMan->pTemp2;
    unsigned * pTruth;
    int i, RetValue, nNodes, nNodesBeg, nInputs = s_pMan->nVars, nLeaves = nVars;
    assert( nInputs <= 16 );   
    // collect internal nodes and skip redundant cuts
    Abc_NtkRecCollectNodesFromLib(pNtk, pRoot, vNodes , nLeaves);
    Abc_NtkRecCutTruthFromLib(vNodes, nLeaves, s_pMan->vTtTemps, s_pMan->vTtElems );
    // copy the truth table
    Kit_TruthCopy( pInOut, (unsigned *)pRoot->pTemp, nInputs );
    // go through the variables in the new truth table
    for ( i = 0; i < nLeaves; i++ )
    {
        // get hold of the corresponding leaf
        pAbcObj = Abc_NtkPi(pNtk, i);
        // get hold of the corresponding new node
        pObj = Abc_NtkPi( pAig, i );
        // map them
        pAbcObj->pCopy = pObj;
    }

    // build the node and compute its truth table
    nNodesBeg = Abc_NtkObjNumMax( pAig );
    Vec_PtrForEachEntryStart( Abc_Obj_t *, vNodes, pAbcObj, i, nLeaves )
    {
        pFanin0 = Abc_ObjNotCond( (Abc_Obj_t *)Abc_ObjFanin0(pAbcObj)->pCopy, Abc_ObjFaninC0(pAbcObj) );
        pFanin1 = Abc_ObjNotCond( (Abc_Obj_t *)Abc_ObjFanin1(pAbcObj)->pCopy, Abc_ObjFaninC1(pAbcObj) );

        nNodes = Abc_NtkObjNumMax( pAig );
        pObj = Abc_AigAnd( (Abc_Aig_t *)pAig->pManFunc, pFanin0, pFanin1 );
        assert( !Abc_ObjIsComplement(pObj) );
        pAbcObj->pCopy = pObj;

        if ( pObj->Id == nNodes )
        {
            // increase storage for truth tables
//            if ( Vec_PtrSize(s_pMan->vTtNodes) <= pObj->Id )
//                Vec_PtrDoubleSimInfo(s_pMan->vTtNodes);
            while ( Vec_PtrSize(s_pMan->vTtNodes) <= pObj->Id )
//                Vec_PtrPush( s_pMan->vTtNodes, ABC_ALLOC(unsigned, s_pMan->nWords) );
                Vec_PtrPush( s_pMan->vTtNodes, Mem_FixedEntryFetch(s_pMan->pMmTruth) );
            // compute the truth table
            RetValue = Abc_NtkRecComputeTruth( pObj, s_pMan->vTtNodes, nInputs );
            if ( RetValue == 0 )
            {
                s_pMan->nFilterError++;
                printf( "T" );
            }
        }
    }
    assert(pObj);
    pTruth = (unsigned *)Vec_PtrEntry( s_pMan->vTtNodes, pObj->Id );
    assert ( Kit_TruthSupport(pTruth, nInputs) == Kit_BitMask(nLeaves) );
    // compare the truth tables
    assert (Kit_TruthIsEqual( pTruth, pInOut, nInputs ) );

//    Extra_PrintBinary( stdout, pInOut, 8 ); printf( "\n" );

    // look up in the hash table and increase the hit number of the functional class
    if(s_pMan->nAddedFuncs > 2 * s_pMan->nBins)
        Abc_NtkRecRezieHash(s_pMan);
    ppSpot = Abc_NtkRecTableLookup(s_pMan, s_pMan->pBins, s_pMan->nBins, pTruth, nInputs );

    // if not new nodes were added and the node has a CO fanout
    if ( nNodesBeg == Abc_NtkObjNumMax(pAig) && Abc_NodeFindCoFanout(pObj) != NULL )
    {
        s_pMan->nFilterSame++;
        //assert(*ppSpot != NULL);
        return;
    }

    // create PO for this node
    pObjPo = Abc_NtkCreatePo(pAig);
    Abc_ObjAddFanin( pObjPo, pObj );

    // assign the name to this PO
    sprintf( Name, "%d_%06d", nLeaves, Abc_NtkPoNum(pAig) );
    if ( (nInputs <= 6) && 0 )
    {
        Extra_PrintHexadecimalString( Truth, pInOut, nInputs );
        sprintf( Buffer, "%s_%s", Name, Truth );
    }
    else
    {
        sprintf( Buffer, "%s", Name );
    }
    Abc_ObjAssignName( pObjPo, Buffer, NULL );

    // add the resulting truth table to the hash table 
    Abc_NtkRecInsertToLookUpTable(s_pMan, ppSpot, pObj, nLeaves, s_pMan->fTrim);
}

/**Function*************************************************************

  Synopsis    [Prints one AIG sugraph recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_RecPrint_rec( Abc_Obj_t * pObj )
{
    if ( Abc_ObjIsPi(pObj) )
    {
        printf( "%c", 'a' + pObj->Id - 1 );
        return;
    }
    assert( Abc_ObjIsNode(pObj) );
    printf( "(%s", Abc_ObjFaninC0(pObj)? "!" : "" );
    Abc_RecPrint_rec( Abc_ObjFanin0(pObj) );
    printf( "*%s", Abc_ObjFaninC1(pObj)? "!" : "" );
    Abc_RecPrint_rec( Abc_ObjFanin1(pObj) );
    printf( ")" );
}

/**Function*************************************************************

  Synopsis    [back up the info of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecBackUpCut(If_Cut_t* pCut)
{
    int i;
    s_pMan->tempUsign = pCut->uSign;
    s_pMan->tempNleaves = pCut->nLeaves;
    for (i = 0; i < (int)pCut->nLeaves; i++)
        s_pMan->pTempleaves[i] = pCut->pLeaves[i];
    Kit_TruthCopy(s_pMan->pTempTruth, pCut->pTruth, s_pMan->nVars);    
}

/**Function*************************************************************

  Synopsis    [restore the info of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecRestoreCut(If_Cut_t* pCut)
{
    int i;
    pCut->uSign = s_pMan->tempUsign;
    pCut->nLeaves = s_pMan->tempNleaves;
    for (i = 0; i < (int)pCut->nLeaves; i++)
        pCut->pLeaves[i] = s_pMan->pTempleaves[i];
    Kit_TruthCopy(pCut->pTruth ,s_pMan->pTempTruth, s_pMan->nVars);    
}

/**Function*************************************************************

  Synopsis    [compute current cut's area.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecCurrentUnMark_rec(If_Obj_t * pObj)
{
    pObj = If_Regular(pObj);
    if(pObj->fMark == 0)
        return;
    if(pObj->pFanin0)
        Abc_NtkRecCurrentUnMark_rec(If_ObjFanin0(pObj));
    if(pObj->pFanin1)
        Abc_NtkRecCurrentUnMark_rec(If_ObjFanin1(pObj));
    pObj->fMark = 0;
    return;
}

/**Function*************************************************************

  Synopsis    [compute current cut's area.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecCurrentMarkAndCount_rec(If_Obj_t * pObj)
{
    int Area0, Area1, Area;
    pObj = If_Regular(pObj);
    if(pObj->fMark == 1)
        return 0;
    Area0 = Abc_NtkRecCurrentMarkAndCount_rec(If_ObjFanin0(pObj));
    Area1 = Abc_NtkRecCurrentMarkAndCount_rec(If_ObjFanin1(pObj));
    Area = Area1 + Area0 + 1;
    pObj->fMark = 1;
    return Area;
}

/**Function*************************************************************

  Synopsis    [compute current cut's area.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecCurrentAera(If_Man_t* p, If_Cut_t* pCut, If_Obj_t * pRoot)
{
    int Area, i;
    If_Obj_t * pLeaf;
    Vec_PtrClear( s_pMan->vNodes );
    If_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        Vec_PtrPush( s_pMan->vNodes, pLeaf );
        assert( pLeaf->fMark == 0 );
        pLeaf->fMark = 1;
    }

    // collect other nodes
    Abc_NtkRecCollectNodes_rec( pRoot, s_pMan->vNodes );
    Vec_PtrForEachEntry( If_Obj_t *, s_pMan->vNodes, pLeaf, i )
        pLeaf->fMark = 0;
    If_CutForEachLeaf(p, pCut, pLeaf, i)
        pLeaf->fMark = 1;
    Area  = Abc_NtkRecCurrentMarkAndCount_rec(pRoot);
    Abc_NtkRecCurrentUnMark_rec(pRoot);
    return Area;
}

/**Function*************************************************************

  Synopsis    [compute current cut's delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char Abc_NtkRecCurrentDepth_rec(If_Obj_t * pObj, int iLeaf)
{
    char Depth0, Depth1, Depth;
    pObj = If_Regular(pObj);
    if(pObj->Id == iLeaf)
        return 0;
    if(pObj->fMark)
        return -IF_BIG_CHAR;
    Depth0 = Abc_NtkRecCurrentDepth_rec(If_ObjFanin0(pObj), iLeaf);
    Depth1 = Abc_NtkRecCurrentDepth_rec(If_ObjFanin1(pObj), iLeaf);
    Depth = Abc_MaxInt(Depth0, Depth1);
    Depth = (Depth == -IF_BIG_CHAR) ? -IF_BIG_CHAR : Depth + 1;
    assert(Depth <= 127);
    return Depth;
}

/**Function*************************************************************

  Synopsis    [compute current cut's delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecCurrentDepth(If_Man_t* p, If_Cut_t* pCut, If_Obj_t * pRoot)
{
    int i;
    If_Obj_t * pLeaf;
    If_CutForEachLeaf(p, pCut, pLeaf, i)
        pLeaf->fMark = 1;
    If_CutForEachLeaf(p, pCut, pLeaf, i)
        s_pMan->pTempDepths[i] = Abc_NtkRecCurrentDepth_rec(pRoot, pLeaf->Id);
    If_CutForEachLeaf(p, pCut, pLeaf, i)
        pLeaf->fMark = 0;
}

/**Function*************************************************************

  Synopsis    [compute current cut's delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRecCurrentDelay(If_Man_t* p, If_Cut_t* pCut, If_Obj_t * pRoot)
{  
    If_Obj_t* pLeaf;
    int i, delayTemp, delayMax = -ABC_INFINITY;
    Abc_NtkRecCurrentDepth(p , pCut, pRoot);
    If_CutForEachLeaf(p, pCut, pLeaf, i)
    {
        delayTemp = s_pMan->pTempDepths[i] + If_ObjCutBest(pLeaf)->Delay;
        if(delayTemp > delayMax)
            delayMax = delayTemp;
    }
    // plus each pin's delay with its pin-to-output delay, the biggest one is the delay of the structure.
    return delayMax;
}

/**Function*************************************************************

  Synopsis    [compute current cut's delay and area.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkRecComputCurrentStructure(If_Man_t* p, If_Cut_t* pCut, If_Obj_t * pRoot)
{
    if (pRoot->Id == 78)
    {
        int  a = 1;
    }
    
    s_pMan->currentCost = Abc_NtkRecCurrentAera(p, pCut, pRoot);
    s_pMan->currentDelay = Abc_NtkRecCurrentDelay(p, pCut, pRoot);
}

/**Function*************************************************************

  Synopsis    [the cut not found in the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void SetUselessCut(If_Cut_t* pCut)
{
    int i;
    pCut->fUseless = 1;
    pCut->fUser = 1;
    pCut->Cost = s_pMan->currentCost;
    for (i = 0; i < (int)pCut->nLeaves; i++)
        pCut->pPerm[i] = s_pMan->pTempDepths[i];
    return;   
}

/**Function*************************************************************

  Synopsis    [the cut not found in the library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void SetUseCut(If_Cut_t* pCut, Rec_Obj_t * pRecObj, char * pCanonPerm)
{
    int i;
    pCut->fUseless = 0;
    pCut->fUser = 1;
    pCut->Cost = pRecObj->cost;
    for (i = 0; i < (int)pCut->nLeaves; i++)
        pCut->pPerm[pCanonPerm[i]] = pRecObj->pinToPinDelay[i];
    return;  

}

/**Function*************************************************************

  Synopsis    [Computes the  delay using library.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_CutDelayRecCost(If_Man_t* p, If_Cut_t* pCut, If_Obj_t * pObj)
{
    int fVerbose = 0;
    int timeDelayComput, timeTotal = clock(), timeCanonicize;
    int nLeaves, i, DelayMin = ABC_INFINITY , Delay = -ABC_INFINITY;
    char pCanonPerm[16];
    unsigned uCanonPhase;
    unsigned* pTruthRec;
    Rec_Obj_t *pCand, *pCandMin, **ppSpot;
    Abc_Ntk_t *pAig = s_pMan->pNtk;
    unsigned *pInOut = s_pMan->pTemp1;
    unsigned *pTemp = s_pMan->pTemp2;
    int nVars = s_pMan->nVars;
    int Counter;
    assert( s_pMan != NULL );
    nLeaves = If_CutLeaveNum(pCut);
    s_pMan->nFunsTried++;
    assert( nLeaves >= 2 && nLeaves <= nVars );
    Kit_TruthCopy(pInOut, If_CutTruth(pCut), nLeaves);
    //if not every variables are in the support, skip this cut.
    if ( Kit_TruthSupport(pInOut, nLeaves) != Kit_BitMask(nLeaves) )
    {
        s_pMan->nFunsFilteredBysupport++;
        pCut->fUser = 1;
        pCut->fUseless = 1;
        pCut->Cost = IF_COST_MAX;
        return ABC_INFINITY;
    }
    timeCanonicize = clock();
    //canonicize
    for (i = 0; i < nLeaves; i++)
        pCanonPerm[i] = i;
    uCanonPhase = Kit_TruthSemiCanonicize(pInOut, pTemp, nLeaves, pCanonPerm, (short*)s_pMan->pMints);
    If_CutTruthStretch(pInOut, nLeaves, nVars);
    ppSpot = Abc_NtkRecTableLookup(s_pMan, s_pMan->pBins, s_pMan->nBins, pInOut, nVars );
    if (*ppSpot == NULL)
    {
        Kit_TruthNot(pInOut, pInOut, nVars);
        ppSpot = Abc_NtkRecTableLookup(s_pMan, s_pMan->pBins, s_pMan->nBins, pInOut, nVars );
    }
    s_pMan->timeIfCanonicize += clock() - timeCanonicize;   
    assert (!(*ppSpot == NULL && nLeaves == 2));
    //functional class not found in the library.
    if ( *ppSpot == NULL )
    {

        s_pMan->nFunsNotFound++;        
        pCut->Cost = IF_COST_MAX;
        pCut->fUser = 1;
        pCut->fUseless = 1;
        return ABC_INFINITY;
    }
    s_pMan->nFunsFound++; 
    // make sure the truth table is the same
    pTruthRec = (unsigned*)Vec_PtrEntry( s_pMan->vTtNodes, (*ppSpot)->Id );
    if ( !Kit_TruthIsEqualWithPhase( pTruthRec, pInOut, nLeaves ) )
    {
        assert( 0 );
        s_pMan->nIfMapError++;  
        return -1;
    }
    // mark as user cut.
    pCut->fUser = 1;
    DelayMin = ABC_INFINITY;
    pCandMin = NULL;
    timeDelayComput = clock();

    if ( fVerbose )
        Kit_DsdPrintFromTruth( pInOut, nLeaves ), printf( "   Subgraphs: " );

    //find the best structure of the functional class.
    Counter = 0;
    for ( pCand = *ppSpot; pCand; pCand = pCand->pNext )
    {
        Counter++;
        if ( fVerbose )
        {
            printf( "%s(", Abc_ObjIsComplement(pCand->obj)? "!" : "" );
            Abc_RecPrint_rec( Abc_ObjRegular(pCand->obj) );
            printf( ")   " );
        }
        s_pMan->nFunsDelayComput++;
        Delay = If_CutComputDelay(p, pCand, pCut, pCanonPerm ,nLeaves);
        if ( DelayMin > Delay )
        {
            //            printf( "%d ", Cost );
            DelayMin = Delay;
            pCandMin = pCand;
        }
        else if(Delay == DelayMin)
        {
            if(pCand->cost < pCandMin->cost)
                pCandMin = pCand;
        }
    }
    if ( fVerbose )
        printf( "Printed %d subgraphs.\n", Counter );
    s_pMan->timeIfComputDelay += clock() - timeDelayComput;
    assert( pCandMin != NULL );
    for ( i = 0; i < nLeaves; i++ )
    {
        pCut->pPerm[pCanonPerm[i]] = pCandMin->pinToPinDelay[i];
    }
    s_pMan->timeIfTotal += clock() - timeTotal;
    pCut->Cost = pCandMin->cost;
        return DelayMin;
    
}

/**Function*************************************************************

  Synopsis    [Labels the record AIG with the corresponding new AIG nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*Abc_Obj_t * Abc_NtkRecStrashNodeLabel_rec( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj, int fBuild, Vec_Ptr_t * vLabels )
{
    Abc_Obj_t * pFanin0New, * pFanin1New, * pLabel;
    assert( !Abc_ObjIsComplement(pObj) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return (Abc_Obj_t *)Vec_PtrEntry( vLabels, pObj->Id );
    assert( Abc_ObjIsNode(pObj) );
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pObj );
    // label the fanins
    pFanin0New = Abc_NtkRecStrashNodeLabel_rec( pNtkNew, Abc_ObjFanin0(pObj), fBuild, vLabels );
    pFanin1New = Abc_NtkRecStrashNodeLabel_rec( pNtkNew, Abc_ObjFanin1(pObj), fBuild, vLabels );
    // label the node if possible
    pLabel = NULL;
    if ( pFanin0New && pFanin1New )
    {
        pFanin0New = Abc_ObjNotCond( pFanin0New, Abc_ObjFaninC0(pObj) );
        pFanin1New = Abc_ObjNotCond( pFanin1New, Abc_ObjFaninC1(pObj) );
        if ( fBuild )
            pLabel = Abc_AigAnd( (Abc_Aig_t *)pNtkNew->pManFunc, pFanin0New, pFanin1New );
        else
            pLabel = Abc_AigAndLookup( (Abc_Aig_t *)pNtkNew->pManFunc, pFanin0New, pFanin1New );
    }
    Vec_PtrWriteEntry( vLabels, pObj->Id, pLabel );
    return pLabel;
}*/

/**Function*************************************************************

  Synopsis    [Counts the area of the given node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*int Abc_NtkRecStrashNodeCount_rec( Abc_Obj_t * pObj, Vec_Str_t * vCosts, Vec_Ptr_t * vLabels )
{
    int Cost0, Cost1;
    if ( Vec_PtrEntry( vLabels, pObj->Id ) )
        return 0;
    assert( Abc_ObjIsNode(pObj) );
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return Vec_StrEntry( vCosts, pObj->Id );
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pObj );
    // count for the fanins
    Cost0 = Abc_NtkRecStrashNodeCount_rec( Abc_ObjFanin0(pObj), vCosts, vLabels );
    Cost1 = Abc_NtkRecStrashNodeCount_rec( Abc_ObjFanin1(pObj), vCosts, vLabels );
    Vec_StrWriteEntry( vCosts, pObj->Id, (char)(Cost0 + Cost1 + 1) );
    return Cost0 + Cost1 + 1;
}*/

/**Function*************************************************************

  Synopsis    [Strashes the given node using its local function.]

  Description [Assumes that the fanins are already strashed.
  Returns 0 if the function is not found in the table.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*int Abc_NtkRecStrashNode( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj, unsigned * pTruth, int nVars )
{
    char pCanonPerm[16];
    Abc_Ntk_t * pAig = s_pMan->pNtk;
    unsigned * pInOut = s_pMan->pTemp1;
    unsigned * pTemp = s_pMan->pTemp2;
    unsigned * pTruthRec;
    Abc_Obj_t * pCand, * pCandMin, * pLeaf, * pFanin, ** ppSpot;
    unsigned uCanonPhase;
    int i, nLeaves, CostMin, Cost, nOnes, fCompl;

    // check if the record works
    nLeaves = Abc_ObjFaninNum(pObj);
    assert( nLeaves >= 3 && nLeaves <= s_pMan->nVars );
    pFanin = Abc_ObjFanin0(pObj);
    assert( Abc_ObjRegular(pFanin->pCopy)->pNtk == pNtkNew );
    assert( s_pMan != NULL );
    assert( nVars == s_pMan->nVars );

    // copy the truth table
    Kit_TruthCopy( pInOut, pTruth, nVars );

    // set permutation
    for ( i = 0; i < nVars; i++ )
        pCanonPerm[i] = i;

    // canonicize the truth table
    uCanonPhase = Kit_TruthSemiCanonicize( pInOut, pTemp, nVars, pCanonPerm, (short *)s_pMan->pMints );

    // get hold of the curresponding class
    ppSpot = Abc_NtkRecTableLookup( s_pMan, pInOut, nVars );
    if ( *ppSpot == NULL )
    {
        s_pMan->nFunsNotFound++;        
//        printf( "The class of a function with %d inputs is not found.\n", nLeaves );
        return 0;
    }
    s_pMan->nFunsFound++;        

    // make sure the truth table is the same
    pTruthRec = (unsigned *)Vec_PtrEntry( s_pMan->vTtNodes, (*ppSpot)->Id );
    if ( !Kit_TruthIsEqualWithPhase( pTruthRec, pInOut, nVars ) )
    {
        assert( 0 );
        return 0;
    }


    // allocate storage for costs
    if ( s_pMan->vLabels && Vec_PtrSize(s_pMan->vLabels) < Abc_NtkObjNumMax(pAig) )
    {
        Vec_PtrFree( s_pMan->vLabels );
        s_pMan->vLabels = NULL;
    }
    if ( s_pMan->vLabels == NULL )
        s_pMan->vLabels = Vec_PtrStart( Abc_NtkObjNumMax(pAig) );

    // go through the variables in the new truth table
    Abc_NtkIncrementTravId( pAig );
    for ( i = 0; i < nLeaves; i++ )
    {
        // get hold of the corresponding fanin
        pFanin = Abc_ObjFanin( pObj, pCanonPerm[i] )->pCopy;
        pFanin = Abc_ObjNotCond( pFanin, (uCanonPhase & (1 << i)) );
        // label the PI of the AIG subgraphs with this fanin
        pLeaf = Abc_NtkPi( pAig, i );
        Vec_PtrWriteEntry( s_pMan->vLabels, pLeaf->Id, pFanin );
        Abc_NodeSetTravIdCurrent( pLeaf );
    }

    // go through the candidates - and recursively label them
    for ( pCand = *ppSpot; pCand; pCand = (Abc_Obj_t *)pCand->pData )
        Abc_NtkRecStrashNodeLabel_rec( pNtkNew, pCand, 0, s_pMan->vLabels );


    // allocate storage for costs
    if ( s_pMan->vCosts && Vec_StrSize(s_pMan->vCosts) < Abc_NtkObjNumMax(pAig) )
    {
        Vec_StrFree( s_pMan->vCosts );
        s_pMan->vCosts = NULL;
    }
    if ( s_pMan->vCosts == NULL )
        s_pMan->vCosts = Vec_StrStart( Abc_NtkObjNumMax(pAig) );

    // find the best subgraph
    CostMin = ABC_INFINITY;
    pCandMin = NULL;
    for ( pCand = *ppSpot; pCand; pCand = (Abc_Obj_t *)pCand->pData )
    {
        // label the leaves
        Abc_NtkIncrementTravId( pAig );
        // count the number of non-labeled nodes
        Cost = Abc_NtkRecStrashNodeCount_rec( pCand, s_pMan->vCosts, s_pMan->vLabels );
        if ( CostMin > Cost )
        {
//            printf( "%d ", Cost );
            CostMin = Cost;
            pCandMin = pCand;
        }
    }
//    printf( "\n" );
    assert( pCandMin != NULL );
    if ( pCandMin == NULL )
        return 0;


    // label the leaves
    Abc_NtkIncrementTravId( pAig );
    for ( i = 0; i < nLeaves; i++ )
        Abc_NodeSetTravIdCurrent( Abc_NtkPi(pAig, i) );

    // implement the subgraph
    pObj->pCopy = Abc_NtkRecStrashNodeLabel_rec( pNtkNew, pCandMin, 1, s_pMan->vLabels );
    assert( Abc_ObjRegular(pObj->pCopy)->pNtk == pNtkNew );

    // determine phase difference
    nOnes = Kit_TruthCountOnes(pTruth, nVars);
    fCompl = (nOnes > (1<< nVars)/2);
//    assert( fCompl == ((uCanonPhase & (1 << nVars)) > 0) );

    nOnes = Kit_TruthCountOnes(pTruthRec, nVars);
    fCompl ^= (nOnes > (1<< nVars)/2);
    // complement
    pObj->pCopy = Abc_ObjNotCond( pObj->pCopy, fCompl );
    return 1;
}*/






////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

