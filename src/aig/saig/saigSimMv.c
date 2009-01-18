/**CFile****************************************************************

  FileName    [saigSimMv.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Multi-valued simulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigSimMv.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define SAIG_DIFF_VALUES  8
#define SAIG_UNDEF_VALUE  0x1ffffffe  //536870910

// old AIG
typedef struct Saig_MvObj_t_ Saig_MvObj_t;
struct Saig_MvObj_t_
{
    int              iFan0;
    int              iFan1;
    unsigned         Type   :  3;
    unsigned         Value  : 29;
};

// new AIG
typedef struct Saig_MvAnd_t_ Saig_MvAnd_t;
struct Saig_MvAnd_t_
{
    int              iFan0;
    int              iFan1;
    int              iNext;
};

// simulation manager
typedef struct Saig_MvMan_t_ Saig_MvMan_t;
struct Saig_MvMan_t_
{
    // user data
    Aig_Man_t *      pAig;         // original AIG    
    // parameters
    int              nStatesMax;   // maximum number of states
    int              nLevelsMax;   // maximum number of levels
    int              nValuesMax;   // maximum number of values
    int              nFlops;       // number of flops
    // compacted AIG
    Saig_MvObj_t *   pAigOld;      // AIG objects
    Vec_Ptr_t *      vFlops;       // collected flops
    Vec_Ptr_t *      vTired;       // collected flops
    int *            pTStates;     // hash table for states
    int              nTStatesSize; // hash table size
    Aig_MmFixed_t *  pMemStates;   // memory for states
    Vec_Ptr_t *      vStates;      // reached states
    int *            pRegsUndef;   // count the number of undef values
    int **           pRegsValues;  // write the first different values
    int *            nRegsValues;  // count the number of different values
    int              nRUndefs;     // the number of undef registers
    int              nRValues[SAIG_DIFF_VALUES+1]; // the number of registers with given values
    // internal AIG
    Saig_MvAnd_t *   pAigNew;      // AIG nodes
    int              nObjsAlloc;   // the number of objects allocated 
    int              nObjs;        // the number of objects
    int              nPis;         // the number of primary inputs
    int *            pTNodes;      // hash table
    int              nTNodesSize;  // hash table size
    unsigned char *  pLevels;      // levels of AIG nodes
};

static inline int    Saig_MvObjFaninC0( Saig_MvObj_t * pObj )  { return pObj->iFan0 & 1;          }
static inline int    Saig_MvObjFaninC1( Saig_MvObj_t * pObj )  { return pObj->iFan1 & 1;          }
static inline int    Saig_MvObjFanin0( Saig_MvObj_t * pObj )   { return pObj->iFan0 >> 1;         }
static inline int    Saig_MvObjFanin1( Saig_MvObj_t * pObj )   { return pObj->iFan1 >> 1;         }

static inline int    Saig_MvConst0()                           { return 1;                        }
static inline int    Saig_MvConst1()                           { return 0;                        }
static inline int    Saig_MvConst( int c )                     { return !c;                       }
static inline int    Saig_MvUndef()                            { return SAIG_UNDEF_VALUE;         }

static inline int    Saig_MvIsConst0( int iNode )              { return iNode == 1;               }
static inline int    Saig_MvIsConst1( int iNode )              { return iNode == 0;               }
static inline int    Saig_MvIsConst( int iNode )               { return iNode  < 2;               }
static inline int    Saig_MvIsUndef( int iNode )               { return iNode == SAIG_UNDEF_VALUE;}

static inline int    Saig_MvRegular( int iNode )               { return (iNode & ~01);            }
static inline int    Saig_MvNot( int iNode )                   { return (iNode ^  01);            }
static inline int    Saig_MvNotCond( int iNode, int c )        { return (iNode ^ (c));            }
static inline int    Saig_MvIsComplement( int iNode )          { return (int)(iNode & 01);        }

static inline int    Saig_MvLit2Var( int iNode )               { return (iNode >> 1);             }
static inline int    Saig_MvVar2Lit( int iVar )                { return (iVar << 1);              }
static inline int    Saig_MvLev( Saig_MvMan_t * p, int iNode ) { return p->pLevels[iNode >> 1];   }

// iterator over compacted objects
#define Saig_MvManForEachObj( pAig, pEntry ) \
    for ( pEntry = pAig; pEntry->Type != AIG_OBJ_VOID; pEntry++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates reduced manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Saig_MvObj_t * Saig_ManCreateReducedAig( Aig_Man_t * p, Vec_Ptr_t ** pvFlops )
{
    Saig_MvObj_t * pAig, * pEntry;
    Aig_Obj_t * pObj;
    int i;
    *pvFlops = Vec_PtrAlloc( Aig_ManRegNum(p) );
    pAig = CALLOC( Saig_MvObj_t, Aig_ManObjNumMax(p)+1 );
    Aig_ManForEachObj( p, pObj, i )
    {
        pEntry = pAig + i;
        pEntry->Type = pObj->Type;
        if ( Aig_ObjIsPi(pObj) || i == 0 )
        {
            if ( Saig_ObjIsLo(p, pObj) )
            {
                pEntry->iFan0 = (Saig_ObjLoToLi(p, pObj)->Id << 1);
                pEntry->iFan1 = -1;
                Vec_PtrPush( *pvFlops, pEntry );
            }
            continue;
        }
        pEntry->iFan0 = (Aig_ObjFaninId0(pObj) << 1) | Aig_ObjFaninC0(pObj);
        if ( Aig_ObjIsPo(pObj) )
            continue;
        assert( Aig_ObjIsNode(pObj) );
        pEntry->iFan1 = (Aig_ObjFaninId1(pObj) << 1) | Aig_ObjFaninC1(pObj);
    }
    pEntry = pAig + Aig_ManObjNumMax(p);
    pEntry->Type = AIG_OBJ_VOID;
    return pAig;
}

/**Function*************************************************************

  Synopsis    [Creates a new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Saig_MvCreateObj( Saig_MvMan_t * p, int iFan0, int iFan1 )
{
    Saig_MvAnd_t * pNode;
    if ( p->nObjs == p->nObjsAlloc )
    {
        p->pAigNew = REALLOC( Saig_MvAnd_t, p->pAigNew, 2*p->nObjsAlloc );
        p->pLevels = REALLOC( unsigned char, p->pLevels, 2*p->nObjsAlloc );
        p->nObjsAlloc *= 2;
    }
    pNode = p->pAigNew + p->nObjs;
    pNode->iFan0 = iFan0;
    pNode->iFan1 = iFan1;
    pNode->iNext = 0;
    if ( iFan0 || iFan1 )
        p->pLevels[p->nObjs] = 1 + AIG_MAX( Saig_MvLev(p, iFan0), Saig_MvLev(p, iFan1) );
    else
        p->pLevels[p->nObjs] = 0, p->nPis++;
    return p->nObjs++;
}

/**Function*************************************************************

  Synopsis    [Creates multi-valued simulation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Saig_MvMan_t * Saig_MvManStart( Aig_Man_t * pAig )
{
    Saig_MvMan_t * p;
    int i;
    assert( Aig_ManRegNum(pAig) > 0 );
    p = (Saig_MvMan_t *)ALLOC( Saig_MvMan_t, 1 );
    memset( p, 0, sizeof(Saig_MvMan_t) );
    // set parameters
    p->pAig         = pAig;
    p->nStatesMax   = 200;
    p->nLevelsMax   = 4;
    p->nValuesMax   = SAIG_DIFF_VALUES;
    p->nFlops       = Aig_ManRegNum(pAig);
    // compacted AIG
    p->pAigOld      = Saig_ManCreateReducedAig( pAig, &p->vFlops );
    p->nTStatesSize = Aig_PrimeCudd( p->nStatesMax );
    p->pTStates     = CALLOC( int, p->nTStatesSize );
    p->pMemStates   = Aig_MmFixedStart( sizeof(int) * (p->nFlops+1), p->nStatesMax );
    p->vStates      = Vec_PtrAlloc( p->nStatesMax );
    Vec_PtrPush( p->vStates, NULL );
    p->pRegsUndef   = CALLOC( int, p->nFlops );
    p->pRegsValues  = ALLOC( int *, p->nFlops );
    p->pRegsValues[0] = ALLOC( int, p->nValuesMax * p->nFlops );
    for ( i = 1; i < p->nFlops; i++ )
        p->pRegsValues[i] = p->pRegsValues[i-1] + p->nValuesMax;
    p->nRegsValues  = CALLOC( int, p->nFlops );
    p->vTired       = Vec_PtrAlloc( 100 );
    // internal AIG
    p->nObjsAlloc   = 1000000;
    p->pAigNew      = ALLOC( Saig_MvAnd_t, p->nObjsAlloc );
    p->nTNodesSize  = Aig_PrimeCudd( p->nObjsAlloc / 3 );
    p->pTNodes      = CALLOC( int, p->nTNodesSize );
    p->pLevels      = ALLOC( unsigned char, p->nObjsAlloc );
    Saig_MvCreateObj( p, 0, 0 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Destroys multi-valued simulation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_MvManStop( Saig_MvMan_t * p )
{
    Aig_MmFixedStop( p->pMemStates, 0 );
    Vec_PtrFree( p->vStates );
    Vec_PtrFree( p->vFlops );
    Vec_PtrFree( p->vTired );
    free( p->pRegsValues[0] );
    free( p->pRegsValues );
    free( p->nRegsValues );
    free( p->pRegsUndef );
    free( p->pAigOld );
    free( p->pTStates );
    free( p->pAigNew );
    free( p->pTNodes );
    free( p->pLevels );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Hashing the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Saig_MvHash( int iFan0, int iFan1, int TableSize ) 
{
    unsigned Key = 0;
    assert( iFan0 < iFan1 );
    Key ^= Saig_MvLit2Var(iFan0) * 7937;
    Key ^= Saig_MvLit2Var(iFan1) * 2971;
    Key ^= Saig_MvIsComplement(iFan0) * 911;
    Key ^= Saig_MvIsComplement(iFan1) * 353;
    return (int)(Key % TableSize);
}

/**Function*************************************************************

  Synopsis    [Returns the place where this node is stored (or should be stored).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int * Saig_MvTableFind( Saig_MvMan_t * p, int iFan0, int iFan1 )
{
    Saig_MvAnd_t * pEntry;
    int * pPlace = p->pTNodes + Saig_MvHash( iFan0, iFan1, p->nTNodesSize );
    for ( pEntry = (*pPlace)? p->pAigNew + *pPlace : NULL; pEntry; 
          pPlace = &pEntry->iNext, pEntry = (*pPlace)? p->pAigNew + *pPlace : NULL )
              if ( pEntry->iFan0 == iFan0 && pEntry->iFan1 == iFan1 )
                  break;
    return pPlace;
}

/**Function*************************************************************

  Synopsis    [Performs an AND-operation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Saig_MvAnd( Saig_MvMan_t * p, int iFan0, int iFan1 )
{
    if ( iFan0 == iFan1 )
        return iFan0;
    if ( iFan0 == Saig_MvNot(iFan1) )
        return Saig_MvConst0();
    if ( Saig_MvIsConst(iFan0) )
        return Saig_MvIsConst1(iFan0) ? iFan1 : Saig_MvConst0();
    if ( Saig_MvIsConst(iFan1) )
        return Saig_MvIsConst1(iFan1) ? iFan0 : Saig_MvConst0();
    if ( Saig_MvIsUndef(iFan0) || Saig_MvIsUndef(iFan1) )
        return Saig_MvUndef();
    if ( Saig_MvLev(p, iFan0) >= p->nLevelsMax || Saig_MvLev(p, iFan1) >= p->nLevelsMax )
        return Saig_MvUndef();

//    return Saig_MvUndef();

    if ( iFan0 > iFan1 )
    {
        int Temp = iFan0;
        iFan0 = iFan1;
        iFan1 = Temp;
    }
    {
    int * pPlace;
    pPlace = Saig_MvTableFind( p, iFan0, iFan1 );
    if ( *pPlace == 0 )
        *pPlace = Saig_MvCreateObj( p, iFan0, iFan1 );
    return Saig_MvVar2Lit( *pPlace );
    }
}

/**Function*************************************************************

  Synopsis    [Propagates one edge.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Saig_MvSimulateValue0( Saig_MvObj_t * pAig, Saig_MvObj_t * pObj )
{
    Saig_MvObj_t * pObj0 = pAig + Saig_MvObjFanin0(pObj);
    if ( Saig_MvIsUndef( pObj0->Value ) )
        return Saig_MvUndef();
    return Saig_MvNotCond( pObj0->Value, Saig_MvObjFaninC0(pObj) );
}
static inline int Saig_MvSimulateValue1( Saig_MvObj_t * pAig, Saig_MvObj_t * pObj )
{
    Saig_MvObj_t * pObj1 = pAig + Saig_MvObjFanin1(pObj);
    if ( Saig_MvIsUndef( pObj1->Value ) )
        return Saig_MvUndef();
    return Saig_MvNotCond( pObj1->Value, Saig_MvObjFaninC1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Performs one iteration of simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_MvSimulateFrame( Saig_MvMan_t * p, int fFirst )
{
    int fPrintState = 0;
    Saig_MvObj_t * pEntry;
    int i, NewValue;
    Saig_MvManForEachObj( p->pAigOld, pEntry )
    {
        if ( pEntry->Type == AIG_OBJ_AND )
        {
            pEntry->Value = Saig_MvAnd( p, 
                Saig_MvSimulateValue0(p->pAigOld, pEntry),
                Saig_MvSimulateValue1(p->pAigOld, pEntry) );
/*
printf( "%d = %d%s * %d%s  --> %d\n", pEntry - p->pAigOld,
       Saig_MvObjFanin0(pEntry), Saig_MvObjFaninC0(pEntry)? "-":"+",
       Saig_MvObjFanin1(pEntry), Saig_MvObjFaninC1(pEntry)? "-":"+", pEntry->Value );
*/
        }
        else if ( pEntry->Type == AIG_OBJ_PO )
            pEntry->Value = Saig_MvSimulateValue0(p->pAigOld, pEntry);
        else if ( pEntry->Type == AIG_OBJ_PI )
        {
            if ( pEntry->iFan1 == 0 ) // true PI
                pEntry->Value = Saig_MvVar2Lit( Saig_MvCreateObj( p, 0, 0 ) );
//            else if ( fFirst ) // register output
//                pEntry->Value = Saig_MvConst0();
//            else
//                pEntry->Value = Saig_MvSimulateValue0(p->pAigOld, pEntry);
        }
        else if ( pEntry->Type == AIG_OBJ_CONST1 )
            pEntry->Value = Saig_MvConst1();
        else if ( pEntry->Type != AIG_OBJ_NONE )
            assert( 0 );
    }
    Vec_PtrClear( p->vTired );
    Vec_PtrForEachEntry( p->vFlops, pEntry, i )
    {
        NewValue = Saig_MvSimulateValue0(p->pAigOld, pEntry);
        if ( NewValue != (int)pEntry->Value )
            Vec_PtrPush( p->vTired, pEntry );
        pEntry->Value = NewValue;
        if ( !fPrintState )
            continue;
        if ( pEntry->Value == 536870910 )
            printf( "* " );
        else
            printf( "%d ", pEntry->Value );
    }
if ( fPrintState )
printf( "\n" );
}


/**Function*************************************************************

  Synopsis    [Computes hash value of the node using its simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_MvSimHash( int * pState, int nFlops, int TableSize )
{
    static int s_SPrimes[128] = { 
        1009, 1049, 1093, 1151, 1201, 1249, 1297, 1361, 1427, 1459, 
        1499, 1559, 1607, 1657, 1709, 1759, 1823, 1877, 1933, 1997, 
        2039, 2089, 2141, 2213, 2269, 2311, 2371, 2411, 2467, 2543, 
        2609, 2663, 2699, 2741, 2797, 2851, 2909, 2969, 3037, 3089, 
        3169, 3221, 3299, 3331, 3389, 3461, 3517, 3557, 3613, 3671, 
        3719, 3779, 3847, 3907, 3943, 4013, 4073, 4129, 4201, 4243, 
        4289, 4363, 4441, 4493, 4549, 4621, 4663, 4729, 4793, 4871, 
        4933, 4973, 5021, 5087, 5153, 5227, 5281, 5351, 5417, 5471, 
        5519, 5573, 5651, 5693, 5749, 5821, 5861, 5923, 6011, 6073, 
        6131, 6199, 6257, 6301, 6353, 6397, 6481, 6563, 6619, 6689, 
        6737, 6803, 6863, 6917, 6977, 7027, 7109, 7187, 7237, 7309, 
        7393, 7477, 7523, 7561, 7607, 7681, 7727, 7817, 7877, 7933, 
        8011, 8039, 8059, 8081, 8093, 8111, 8123, 8147
    };
    unsigned uHash = 0;
    int i;
    for ( i = 0; i < nFlops; i++ )
        uHash ^= pState[i] * s_SPrimes[i & 0x7F];
    return (int)(uHash % TableSize);
}

/**Function*************************************************************

  Synopsis    [Returns the place where this state is stored (or should be stored).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int * Saig_MvSimTableFind( Saig_MvMan_t * p, int * pState )
{
    int * pEntry;
    int * pPlace = p->pTStates + Saig_MvSimHash( pState+1, p->nFlops, p->nTStatesSize );
    for ( pEntry = (*pPlace)? Vec_PtrEntry(p->vStates, *pPlace) : NULL; pEntry; 
          pPlace = pEntry, pEntry = (*pPlace)? Vec_PtrEntry(p->vStates, *pPlace) : NULL )
              if ( memcmp( pEntry+1, pState+1, sizeof(int)*p->nFlops ) == 0 )
                  break;
    return pPlace;
}

/**Function*************************************************************

  Synopsis    [Saves current state.]

  Description [Returns -1 if there is no fixed point.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_MvSaveState( Saig_MvMan_t * p, int * piReg )
{
    Saig_MvObj_t * pEntry;
    int i, k, * pState, * pPlace, nMaxUndefs = 0;
    int iTimesOld, iTimesNew;
    *piReg = -1;
    pState = (int *)Aig_MmFixedEntryFetch( p->pMemStates );
    pState[0] = 0;
    Vec_PtrForEachEntry( p->vFlops, pEntry, i )
    {
        iTimesOld = p->nRegsValues[i];
        // count the number of different def values
        if ( !Saig_MvIsUndef( pEntry->Value ) && p->nRegsValues[i] < p->nValuesMax )
        {
            for ( k = 0; k < p->nRegsValues[i]; k++ )
                if ( p->pRegsValues[i][k] == (int)pEntry->Value )
                    break;
            if ( k == p->nRegsValues[i] )
                p->pRegsValues[i][ p->nRegsValues[i]++ ] = pEntry->Value;
        }
        else // retire this register (consider moving this up!)
        {
            pEntry->Value = Saig_MvUndef();
            p->nRegsValues[i] = SAIG_DIFF_VALUES+1;
        }
        iTimesNew = p->nRegsValues[i];
        // count the number of times
        if ( iTimesOld != iTimesNew )
        {
            if ( iTimesOld > 0 )
                p->nRValues[iTimesOld]--;
            if ( iTimesNew <= SAIG_DIFF_VALUES )
                p->nRValues[iTimesNew]++;
        }
        // count the number of undef values
        if ( Saig_MvIsUndef( pEntry->Value ) )
        {
            if ( p->pRegsUndef[i]++ == 0 )
                p->nRUndefs++;
        }
        // find def reg with the max number of undef values
        if ( nMaxUndefs < p->pRegsUndef[i] )
        {
             nMaxUndefs = p->pRegsUndef[i];
            *piReg = i;
        }
        // remember state
        pState[i+1] = pEntry->Value;

//        if ( pEntry->Value == 536870910 )
//            printf( "* " );
//        else
//            printf( "%d ", pEntry->Value );
    }
//printf( "\n" );
    pPlace = Saig_MvSimTableFind( p, pState );
    if ( *pPlace )
        return *pPlace;
    *pPlace = Vec_PtrSize( p->vStates );
    Vec_PtrPush( p->vStates, pState );
    return -1;
}

/**Function*************************************************************

  Synopsis    [Performs multi-valued simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_MvManPostProcess( Saig_MvMan_t * p, int iState )
{
    Saig_MvObj_t * pEntry;
    int i, k, j, nTotal = 0, * pState, Counter = 0, iFlop;
    Vec_Int_t * vUniques = Vec_IntAlloc( 100 );
    Vec_Int_t * vCounter = Vec_IntAlloc( 100 );
    // count registers that never became undef
    Vec_PtrForEachEntry( p->vFlops, pEntry, i )
        if ( p->pRegsUndef[i] == 0 )
            nTotal++;
    printf( "The number of registers that never became undef = %d. (Total = %d.)\n", nTotal, p->nFlops );
    Vec_PtrForEachEntry( p->vFlops, pEntry, i )
    {
        if ( p->pRegsUndef[i] )
            continue;
        Vec_IntForEachEntry( vUniques, iFlop, k )
        {
            Vec_PtrForEachEntryStart( p->vStates, pState, j, 1 )
                if ( pState[iFlop+1] != pState[i+1] )
                    break;
            if ( j == Vec_PtrSize(p->vStates) )
            {
                Vec_IntAddToEntry( vCounter, k, 1 );
                break;
            }
        }
        if ( k == Vec_IntSize(vUniques) )
        {
            Vec_IntPush( vUniques, i );
            Vec_IntPush( vCounter, 1 );
        }
    }
    Vec_IntForEachEntry( vUniques, iFlop, i )
    {
        printf( "FLOP %5d : (%3d) ", iFlop, Vec_IntEntry(vCounter,i) );
/*
        for ( k = 0; k < p->nRegsValues[iFlop]; k++ )
            if ( p->pRegsValues[iFlop][k] == 536870910 )
                printf( "* " );
            else
                printf( "%d ", p->pRegsValues[iFlop][k] );
        printf( "\n" );
*/
        Vec_PtrForEachEntryStart( p->vStates, pState, k, 1 )
        {
            if ( k == iState+1 )
                printf( " # " );
            if ( pState[iFlop+1] == 536870910 )
                printf( "*" );
            else
                printf( "%d", pState[iFlop+1] );
        }
        printf( "\n" );
//        if ( ++Counter == 10 )
//            break;
    }

    Vec_IntFree( vUniques );
    Vec_IntFree( vCounter );
}

/**Function*************************************************************

  Synopsis    [Performs multi-valued simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_MvManSimulate( Aig_Man_t * pAig, int fVerbose )
{
    Saig_MvMan_t * p;
    Saig_MvObj_t * pEntry;
    int f, i, k, iRegMax, iState, clk = clock();
    // start the manager
    p = Saig_MvManStart( pAig );
PRT( "Constructing the problem", clock() - clk );
    clk = clock();
    // initiliaze registers
    Vec_PtrForEachEntry( p->vFlops, pEntry, i )
    {
        pEntry->Value = Saig_MvConst0();
        if ( pEntry->iFan0 == 1 )
            printf( "Constant value %d\n", i );
    }

    Saig_MvSaveState( p, &iRegMax );
    // simulate until convergence
    for ( f = 0; ; f++ )
    {
/*
        if ( fVerbose )
        {
            printf( "%3d :  ", f+1 );
            printf( "*=%6d  ", p->nRUndefs );
            for ( k = 1; k < SAIG_DIFF_VALUES; k++ )
                if ( p->nRValues[k] == 0 )
                    printf( "          " );
                else
                    printf( "%d=%6d  ", k, p->nRValues[k] );
            printf( "aig=%6d", p->nObjs );
            printf( "\n" );
        }
*/
        Saig_MvSimulateFrame( p, f==0 );
        iState = Saig_MvSaveState( p, &iRegMax );
        if ( iState >= 0 )
        {
            printf( "Converged after %d frames with lasso in state %d. Cycle = %d.\n", f+1, iState-1, f+2-iState );
            printf( "Total number of PIs = %d. AND nodes = %d.\n", p->nPis, p->nObjs - p->nPis );
            break;
        }
        if ( f >= p->nStatesMax && iRegMax >= 0 )
        {
/*
            pEntry = Vec_PtrEntry( p->vFlops, iRegMax );
            assert( pEntry->Value != (unsigned)Saig_MvUndef() );
            pEntry->Value = Saig_MvUndef();
            printf( "Retiring flop %d.\n", iRegMax );
*/
//            printf( "Retiring %d flops.\n", Vec_PtrSize(p->vTired) );
            Vec_PtrForEachEntry( p->vTired, pEntry, k )
                pEntry->Value = Saig_MvUndef();
        }
    }
PRT( "Multi-value simulation", clock() - clk );
    // implement equivalences
    Saig_MvManPostProcess( p, iState-1 );
    Saig_MvManStop( p );
    return 1;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


