/**CFile****************************************************************

  FileName    [aigIso.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Graph isomorphism package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigIso.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"

ABC_NAMESPACE_IMPL_START

static int s_1kPrimes[1024] = 
{
    901403,984877,908741,966307,924437,965639,918787,931067,982621,917669,981473,936407,990487,926077,922897,970861,
    942317,961747,979717,978947,940157,987821,981221,917713,983083,992231,928253,961187,991817,927643,923129,934291,
    998071,967567,961087,988661,910031,930481,904489,974167,941351,959911,963811,921463,900161,934489,905629,930653,
    901819,909457,939871,924083,915113,937969,928457,946291,973787,912869,994093,959279,905803,995219,949903,911011,
    986707,995053,930583,955511,928307,930889,968729,911507,949043,939359,961679,918041,937681,909091,963913,923539,
    929587,953347,917573,913037,995387,976483,986239,946949,922489,917887,957553,931529,929813,949567,941683,905161,
    928819,932417,900089,935903,926587,914467,967361,944833,945881,941741,915949,903407,904157,971863,993893,963607,
    918943,912463,980957,962963,968089,904513,963763,907363,904097,904093,991343,918347,986983,986659,935819,903569,
    929171,913933,999749,923123,961531,935861,915053,994853,943511,969923,927191,968333,949391,950959,968311,991409,
    911681,987101,904027,975259,907399,946223,907259,900409,957221,901063,974657,912337,979001,970147,982301,968213,
    923959,964219,935443,950161,989251,936127,985679,958159,930077,971899,944857,956083,914293,941981,909481,909047,
    960527,958183,970687,914827,949051,928159,933551,964423,914041,915869,929953,901367,914219,975551,912391,917809,
    991499,904781,949153,959887,961957,970943,947741,941263,984541,951437,984301,947423,905761,964913,971357,927709,
    916441,941933,956993,988243,921197,905453,922081,950813,946331,998561,929023,937421,956231,907651,977897,905491,
    960173,931837,955217,911951,990643,971021,949439,988453,996781,951497,906011,944309,911293,917123,983803,928097,
    977747,928703,949957,919189,925513,923953,904997,986351,930689,902009,912007,906757,955793,926803,906809,962743,
    911917,909329,949021,974651,959083,945367,905137,948377,931757,945409,920279,915007,960121,920609,946163,946391,
    928903,932951,944329,901529,959809,918469,978643,911159,982573,965411,962233,911269,953273,974437,907589,992269,
    929399,980431,905693,968267,970481,911089,950557,913799,920407,974489,909863,918529,975277,929323,971549,969181,
    972787,964267,939971,943763,940483,971501,921637,945341,955211,920701,978349,969041,929861,904103,908539,995369,
    995567,917471,908879,993821,947783,954599,978463,914519,942869,947263,988343,914657,956987,903641,943343,991063,
    985403,926327,982829,958439,942017,960353,944987,934793,948971,999331,990767,915199,912211,946459,997019,965059,
    924907,983233,943273,945359,919613,933883,928927,942763,994087,996211,918971,924871,938491,957139,918839,914629,
    974329,900577,952823,941641,900461,946997,983123,935149,923693,908419,995651,912871,987067,920201,913921,929209,
    962509,974599,972001,920273,922099,951781,958549,909971,975133,937207,929941,961397,980677,923579,980081,942199,
    940319,942979,912349,942691,986989,947711,972343,932663,937877,940369,919571,927187,981439,932353,952313,915947,
    915851,974041,989381,921029,997013,999199,914801,918751,997327,992843,982133,932051,964861,903979,937463,916781,
    944389,986719,958369,961451,917767,954367,949853,934939,958807,975797,949699,957097,980773,969989,934907,909281,
    904679,909833,991741,946769,908381,932447,957889,981697,905701,919033,999023,993541,912953,911719,934603,925019,
    989341,912269,917789,981049,959149,989909,960521,952183,922627,936253,910957,972047,945037,940399,928313,928471,
    962459,959947,927541,917333,926899,911837,985631,955127,922729,911171,900511,926251,918209,943477,955277,959773,
    971039,917353,955313,930301,990799,957731,917519,938507,988111,911657,999721,968917,934537,903073,921703,966227,
    904661,998213,954307,931309,909331,933643,910099,958627,914533,902903,950149,972721,915157,969037,988219,944137,
    976411,952873,964787,970927,968963,920741,975187,966817,982909,975281,931907,959267,980711,924617,975691,962309,
    976307,932209,989921,907969,947927,932207,945397,948929,904903,938563,961691,977671,963173,927149,951061,966547,
    937661,983597,948139,948041,982759,941093,993703,910097,902347,990307,978217,996763,904919,924641,902299,929549,
    977323,975071,932917,996293,925579,925843,915487,917443,999541,943043,919109,959879,912173,986339,939193,939599,
    927077,977183,966521,959471,991943,985951,942187,932557,904297,972337,931751,964097,942341,966221,929113,960131,
    906427,970133,996511,925637,971651,983443,981703,933613,939749,929029,958043,961511,957241,901079,950479,975493,
    985799,909401,945601,911077,978359,948151,950333,968879,978727,961151,957823,950393,960293,915683,971513,915659,
    943841,902477,916837,911161,958487,963691,949607,935707,987607,901613,972557,938947,931949,919021,982217,914737,
    913753,971279,981683,915631,907807,970421,983173,916099,984587,912049,981391,947747,966233,932101,991733,969757,
    904283,996601,979807,974419,964693,931537,917251,967961,910093,989321,988129,997307,963427,999221,962447,991171,
    993137,914339,964973,908617,968567,920497,980719,949649,912239,907367,995623,906779,914327,918131,983113,962993,
    977849,914941,932681,905713,932579,923977,965507,916469,984119,931981,998423,984407,993841,901273,910799,939847,
    997153,971429,994927,912631,931657,968377,927833,920149,978041,947449,993233,927743,939737,975017,961861,984539,
    938857,977437,950921,963659,923917,932983,922331,982393,983579,935537,914357,973051,904531,962077,990281,989231,
    910643,948281,961141,911839,947413,923653,982801,903883,931943,930617,928679,962119,969977,926921,999773,954181,
    963019,973411,918139,959719,918823,941471,931883,925273,918173,949453,946993,945457,959561,968857,935603,978283,
    978269,947389,931267,902599,961189,947621,920039,964049,947603,913259,997811,943843,978277,972119,929431,918257,
    991663,954043,910883,948797,929197,985057,990023,960961,967139,923227,923371,963499,961601,971591,976501,989959,
    908731,951331,989887,925307,909299,949159,913447,969797,959449,976957,906617,901213,922667,953731,960199,960049,
    985447,942061,955613,965443,947417,988271,945887,976369,919823,971353,962537,929963,920473,974177,903649,955777,
    963877,973537,929627,994013,940801,985709,995341,936319,904681,945817,996617,953191,952859,934889,949513,965407,
    988357,946801,970391,953521,905413,976187,968419,940669,908591,976439,915731,945473,948517,939181,935183,978067,
    907663,967511,968111,981599,913907,933761,994933,980557,952073,906557,935621,914351,967903,949129,957917,971821,
    925937,926179,955729,966871,960737,968521,949997,956999,961273,962683,990377,908851,932231,929749,932149,966971,
    922079,978149,938453,958313,995381,906259,969503,922321,918947,972443,916411,935021,944429,928643,952199,918157,
    917783,998497,944777,917771,936731,999953,975157,908471,989557,914189,933787,933157,938953,922931,986569,964363,
    906473,963419,941467,946079,973561,957431,952429,965267,978473,924109,979529,991901,988583,918259,961991,978037,
    938033,949967,986071,986333,974143,986131,963163,940553,950933,936587,923407,950357,926741,959099,914891,976231,
    949387,949441,943213,915353,983153,975739,934243,969359,926557,969863,961097,934463,957547,916501,904901,928231,
    903673,974359,932219,916933,996019,934399,955813,938089,907693,918223,969421,940903,940703,913027,959323,940993,
    937823,906691,930841,923701,933259,911959,915601,960251,985399,914359,930827,950251,975379,903037,905783,971237
};

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ISO_NUM_INTS 3

typedef struct Iso_Obj_t_ Iso_Obj_t;
struct Iso_Obj_t_
{
    // hashing entries (related to the parameter ISO_NUM_INTS!)
    unsigned      Level     : 30;
    unsigned      nFinNeg   :  2;
    unsigned      nFoutPos  :  8;
    unsigned      nFoutNeg  :  8;
    unsigned      nFinLev0  :  8;
    unsigned      nFinLev1  :  8;
    unsigned      FaninSig  : 16;
    unsigned      FanoutSig : 16;
    // other data
    int           iNext;          // hash table entry
    int           iClass;         // next one in class
    int           Id;             // unique ID
    Vec_Int_t *   vAllies;        // solved neighbors
};

typedef struct Iso_Man_t_ Iso_Man_t;
struct Iso_Man_t_
{
    Aig_Man_t *   pAig;           // user's AIG manager
    Iso_Obj_t *   pObjs;          // isomorphism objects
    int           nObjIds;        // counter of object IDs
    int           nClasses;       // total number of classes
    int           nEntries;       // total number of entries
    int           nSingles;       // total number of singletons
    int           nObjs;          // total objects
    int           nBins;          // hash table size
    int *         pBins;          // hash table 
    Vec_Ptr_t *   vSingles;       // singletons 
    Vec_Ptr_t *   vClasses;       // other classes
    Vec_Ptr_t *   vTemp1;         // other classes
    Vec_Ptr_t *   vTemp2;         // other classes
    int           timeHash;
    int           timeFout;
    int           timeOther;
    int           timeTotal;
};

static inline Iso_Obj_t *  Iso_ManObj( Iso_Man_t * p, int i )            { assert( i >= 0 && i < p->nObjs ); return i ? p->pObjs + i : NULL;                     }
static inline int          Iso_ObjId( Iso_Man_t * p, Iso_Obj_t * pObj )  { assert( pObj > p->pObjs && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs;      }
static inline Aig_Obj_t *  Iso_AigObj( Iso_Man_t * p, Iso_Obj_t * q )    { return Aig_ManObj( p->pAig, Iso_ObjId(p, q) );                                        }

#define Iso_ManForEachObj( p, pObj, i )   \
    for ( i = 1; (i < p->nObjs) && ((pObj) = Iso_ManObj(p, i)); i++ ) if ( pIso->Level == -1 ) {} else

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

//extern void Iso_ReadPrimes( char * pFileName );
//Iso_ReadPrimes( "primes.txt" );

/**Function*************************************************************

  Synopsis    [Read primes from file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ReadPrimes( char * pFileName )
{
    FILE * pFile;
    int Nums[10000];
    int i, j, Temp, nSize = 0;
    // read the numbers
    pFile = fopen( pFileName, "rb" );
    while ( fscanf( pFile, "%d", Nums + nSize++ ) == 1 );
    fclose( pFile );
    assert( nSize >= (1<<10) );
    // randomly permute
    srand( 111 );
    for ( i = 0; i < nSize; i++ )
    {
        j = rand() % nSize;
        Temp = Nums[i];
        Nums[i] = Nums[j];
        Nums[j] = Temp;
    }
    // write out
    for ( i = 0; i < 64; i++ )
    {
        printf( "    " );
        for ( j = 0; j < 16; j++ )
            printf( "%d,", Nums[i*16+j] );
        printf( "\n" );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManObjCount_rec( Aig_Man_t * p, Aig_Obj_t * pObj, int * pnNodes, int * pnEdges )
{
    if ( Aig_ObjIsPi(pObj) )
        return;
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    Iso_ManObjCount_rec( p, Aig_ObjFanin0(pObj), pnNodes, pnEdges );
    Iso_ManObjCount_rec( p, Aig_ObjFanin1(pObj), pnNodes, pnEdges );
    (*pnEdges) += Aig_ObjFaninC0(pObj) + Aig_ObjFaninC1(pObj);
    (*pnNodes)++;
}
void Iso_ManObjCount( Aig_Man_t * p, Aig_Obj_t * pObj, int * pnNodes, int * pnEdges )
{
    assert( Aig_ObjIsNode(pObj) );
    *pnNodes = *pnEdges = 0;
    Aig_ManIncrementTravId( p );
    Iso_ManObjCount_rec( p, pObj, pnNodes, pnEdges );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Iso_Man_t * Iso_ManStart( Aig_Man_t * pAig )
{
    Iso_Man_t * p;
    p = ABC_CALLOC( Iso_Man_t, 1 );
    p->pAig     = pAig;
    p->nObjs    = Aig_ManObjNumMax( pAig );
    p->pObjs    = ABC_CALLOC( Iso_Obj_t, p->nObjs );
    p->nBins    = Abc_PrimeCudd( p->nObjs );
    p->pBins    = ABC_CALLOC( int, p->nBins );    
    p->vSingles = Vec_PtrAlloc( 1000 );
    p->vClasses = Vec_PtrAlloc( 1000 );
    p->vTemp1   = Vec_PtrAlloc( 1000 );
    p->vTemp2   = Vec_PtrAlloc( 1000 );
    p->nObjIds  = 1;
    return p;
}
void Iso_ManStop( Iso_Man_t * p, int fVerbose )
{
    Iso_Obj_t * pIso;
    int i;

    if ( fVerbose )
    {
        p->timeOther = p->timeTotal - p->timeHash - p->timeFout;
        ABC_PRTP( "Building ", p->timeFout,   p->timeTotal );
        ABC_PRTP( "Hashing  ", p->timeHash,   p->timeTotal );
        ABC_PRTP( "Other    ", p->timeOther,  p->timeTotal );
        ABC_PRTP( "TOTAL    ", p->timeTotal,  p->timeTotal );
    }

    Iso_ManForEachObj( p, pIso, i )
        Vec_IntFreeP( &pIso->vAllies );
    Vec_PtrFree( p->vTemp1 );
    Vec_PtrFree( p->vTemp2 );
    Vec_PtrFree( p->vClasses );
    Vec_PtrFree( p->vSingles );
    ABC_FREE( p->pBins );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Compares two objects by their signature.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Iso_ObjCompare( Iso_Obj_t ** pp1, Iso_Obj_t ** pp2 )
{
    Iso_Obj_t * pIso1 = *pp1;
    Iso_Obj_t * pIso2 = *pp2;
    int Diff = -memcmp( pIso1, pIso2, sizeof(int) * ISO_NUM_INTS );
    if ( Diff )
        return Diff;
    return -Vec_IntCompareVec( pIso1->vAllies, pIso2->vAllies );
}

/**Function*************************************************************

  Synopsis    [Compares two objects by their ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Iso_ObjCompareByData( Aig_Obj_t ** pp1, Aig_Obj_t ** pp2 )
{
    Aig_Obj_t * pIso1 = *pp1;
    Aig_Obj_t * pIso2 = *pp2;
    assert( Aig_ObjIsPi(pIso1) || Aig_ObjIsPo(pIso1) );
    assert( Aig_ObjIsPi(pIso2) || Aig_ObjIsPo(pIso2) );
    return pIso1->iData - pIso2->iData;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Iso_ObjHash( Iso_Obj_t * pIso, int nBins )
{
    static unsigned BigPrimes[8] = {12582917, 25165843, 50331653, 100663319, 201326611, 402653189, 805306457, 1610612741};
    unsigned * pArray = (unsigned *)pIso;
    unsigned i, Value = 0;
    assert( ISO_NUM_INTS < 8 );
    for ( i = 0; i < ISO_NUM_INTS; i++ )
        Value ^= BigPrimes[i] * pArray[i];
    if ( pIso->vAllies )
    {
        pArray = (unsigned *)Vec_IntArray(pIso->vAllies);
        for ( i = 0; i < (unsigned)Vec_IntSize(pIso->vAllies); i++ )
            Value ^= BigPrimes[i&7] * pArray[i];
    }
    return Value % nBins;
}
static inline int Iso_ObjHashAdd( Iso_Man_t * p, Iso_Obj_t * pIso )
{
    Iso_Obj_t * pThis;
    int * pPlace = p->pBins + Iso_ObjHash( pIso, p->nBins );
    p->nEntries++;
    for ( pThis = Iso_ManObj(p, *pPlace); 
          pThis; pPlace = &pThis->iNext, 
          pThis = Iso_ManObj(p, *pPlace) )
        if ( Iso_ObjCompare( &pThis, &pIso ) == 0 ) // equal signatures
        {
            if ( pThis->iClass == 0 )
            {
                p->nClasses++;
                p->nSingles--;
            }
            // add to the list
            pIso->iClass = pThis->iClass;
            pThis->iClass = Iso_ObjId( p, pIso );
            return 1;
        }
    // create new list
    *pPlace = Iso_ObjId( p, pIso );
    p->nSingles++;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManCollectClasses( Iso_Man_t * p )
{
    Iso_Obj_t * pIso;
    int i;
    Vec_PtrClear( p->vSingles );
    Vec_PtrClear( p->vClasses );
    for ( i = 0; i < p->nBins; i++ )
    {
//        int Counter = 0;
        for ( pIso = Iso_ManObj(p, p->pBins[i]); pIso; pIso = Iso_ManObj(p, pIso->iNext) )
        {
            assert( pIso->Id == 0 );
            if ( pIso->iClass )
                Vec_PtrPush( p->vClasses, pIso );
            else 
                Vec_PtrPush( p->vSingles, pIso );
//            Counter++;
        }
//        if ( Counter )
//        printf( "%d ", Counter );
    }
//    printf( "\n" );
    Vec_PtrSort( p->vSingles, (int (*)(void))Iso_ObjCompare );
    Vec_PtrSort( p->vClasses, (int (*)(void))Iso_ObjCompare );
    assert( Vec_PtrSize(p->vSingles) == p->nSingles );
    assert( Vec_PtrSize(p->vClasses) == p->nClasses );
    // assign IDs to singletons
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vSingles, pIso, i )
        if ( pIso->Id == 0 )
            pIso->Id = p->nObjIds++;
}

static inline int      Abc_Base2Log64( word n )             { int r; if ( n < 2 ) return (int)n; for ( r = 0, n--; n; n >>= 1, r++ ); return r; }

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Iso_Man_t * Iso_ManCreate( Aig_Man_t * pAig )
{
    int fUseSignatures = 1;
    Iso_Man_t * p;
    Iso_Obj_t * pIso;
    Aig_Obj_t * pObj;
    int i;//, nNodes = 0, nEdges = 0;
    p = Iso_ManStart( pAig );
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( Aig_ObjIsNode(pObj) )
        {
            pIso = p->pObjs + Aig_ObjFaninId0(pObj);
            if ( Aig_ObjFaninC0(pObj) )
                pIso->nFoutNeg++;
            else
                pIso->nFoutPos++;
            pIso = p->pObjs + Aig_ObjFaninId1(pObj);
            if ( Aig_ObjFaninC1(pObj) )
                pIso->nFoutNeg++;
            else
                pIso->nFoutPos++;
        }
        else if ( Aig_ObjIsPo(pObj) )
        {
            pIso = p->pObjs + Aig_ObjFaninId0(pObj);
            if ( Aig_ObjFaninC0(pObj) )
                pIso->nFoutNeg++;
            else
                pIso->nFoutPos++;
        }
    }

    // create TFI signatures
    if ( fUseSignatures )
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( Aig_ObjIsPo(pObj) )
            continue;
        pIso = p->pObjs + i;
        assert( pIso->FaninSig == 0 );
        assert( pIso->FanoutSig == 0 );
        pIso->FaninSig = pIso->nFoutNeg * s_1kPrimes[pObj->Level & 0x3FF];
        if ( Aig_ObjIsNode(pObj) )
        {
            pIso->FaninSig += p->pObjs[Aig_ObjFaninId0(pObj)].FaninSig;
            pIso->FaninSig += p->pObjs[Aig_ObjFaninId1(pObj)].FaninSig;
        }
    }

    // create TFO signatures
    if ( fUseSignatures )
    Aig_ManForEachObjReverse( pAig, pObj, i )
    {
        if ( Aig_ObjIsPi(pObj) || Aig_ObjIsConst1(pObj) )
            continue;
        pIso = p->pObjs + i;
//        pIso->FanoutSig += pIso->nFoutNeg * s_1kPrimes[pObj->Level & 0x3FF];
        pIso->FanoutSig += s_1kPrimes[pObj->Level & 0x3FF];
        if ( Aig_ObjIsNode(pObj) )
        {
            p->pObjs[Aig_ObjFaninId0(pObj)].FanoutSig += pIso->FanoutSig;
            p->pObjs[Aig_ObjFaninId1(pObj)].FanoutSig += pIso->FanoutSig;
        }
        else if ( Aig_ObjIsPo(pObj) )
            p->pObjs[Aig_ObjFaninId0(pObj)].FanoutSig += pIso->FanoutSig;
    }


//    Aig_ManForEachPi( pAig, pObj, i )
//        printf( "%d ", Abc_Base2Log64( (p->pObjs + Aig_ObjId(pObj))->FanoutSig ) );
//    printf( "\n" );

    // create other signatures
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( !Aig_ObjIsPi(pObj) && !Aig_ObjIsNode(pObj) )
            continue;
        pIso = p->pObjs + i;
        pIso->Level = pObj->Level;
        pIso->nFinNeg = Aig_ObjFaninC0(pObj) + Aig_ObjFaninC1(pObj);
        if ( Aig_ObjIsNode(pObj) )
        {
            if ( Aig_ObjIsMuxType(pObj) ) // uniqify MUX/XOR
                pIso->nFinNeg = 3;
            if ( Aig_ObjFaninC0(pObj) < Aig_ObjFaninC1(pObj) || (Aig_ObjFaninC0(pObj) == Aig_ObjFaninC1(pObj) && Aig_ObjFanin0(pObj)->Level < Aig_ObjFanin1(pObj)->Level) )
            {
                pIso->nFinLev0 = Aig_ObjFanin0(pObj)->Level;
                pIso->nFinLev1 = Aig_ObjFanin1(pObj)->Level;
            }
            else
            {
                pIso->nFinLev0 = Aig_ObjFanin1(pObj)->Level;
                pIso->nFinLev1 = Aig_ObjFanin0(pObj)->Level;
            }
//            Iso_ManObjCount( pAig, pObj, &nNodes, &nEdges );
//            pIso->nNodes = nNodes;
//            pIso->nEdges = nEdges;
        }
        else
        {  
            pIso->nFinLev0 = (int)(Aig_ObjPioNum(pObj) >= Aig_ManPiNum(pAig) - Aig_ManRegNum(pAig)); // uniqify flop
        }
        // add to the hash table
        Iso_ObjHashAdd( p, pIso );
    }
    // derive classes for the first time
    Iso_ManCollectClasses( p );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManPrintClasseSizes( Iso_Man_t * p )
{
    Iso_Obj_t * pIso, * pTemp;
    int i, Counter;
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
    {
        Counter = 0;
        for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
            Counter++;
        printf( "%d ", Counter );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManPrintClasses( Iso_Man_t * p, int fVerbose, int fVeryVerbose )
{
    int fOnlyCis = 0;
    Iso_Obj_t * pIso, * pTemp;
    int i;

    // count unique objects
    if ( fVerbose )
        printf( "Total objects =%7d.  Entries =%7d.  Classes =%7d.  Singles =%7d.\n", 
            p->nObjs, p->nEntries, p->nClasses, p->nSingles );

    if ( !fVeryVerbose )
        return;

    printf( "Non-trivial classes:\n" );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
    {
        if ( fOnlyCis && pIso->Level > 0 )
            continue;

        printf( "%5d : {", i );
        for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
        {
            if ( fOnlyCis )
                printf( " %d", Aig_ObjPioNum( Iso_AigObj(p, pTemp) ) );
            else
            {
                Aig_Obj_t * pObj = Iso_AigObj(p, pTemp);
                if ( Aig_ObjIsNode(pObj) )
                    printf( " %d{%s%d(%d),%s%d(%d)}", Iso_ObjId(p, pTemp), 
                        Aig_ObjFaninC0(pObj)? "-": "+", Aig_ObjFaninId0(pObj), Aig_ObjLevel(Aig_ObjFanin0(pObj)), 
                        Aig_ObjFaninC1(pObj)? "-": "+", Aig_ObjFaninId1(pObj), Aig_ObjLevel(Aig_ObjFanin1(pObj)) );
                else
                    printf( " %d", Iso_ObjId(p, pTemp) );
            }
            printf( "(%d,%d,%d)", pTemp->Level, pTemp->nFoutPos, pTemp->nFoutNeg );
            if ( pTemp->vAllies )
            {
                int Entry, k;
                printf( "[" );
                Vec_IntForEachEntry( pTemp->vAllies, Entry, k )
                    printf( "%s%d", k?",":"", Entry );
                printf( "]" );
            }
        }        
        printf( " }\n" );
    }
}


/**Function*************************************************************

  Synopsis    [Creates adjacency lists.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Iso_ObjAddToAllies( Iso_Obj_t * pIso, int Id, int fCompl )
{
    assert( pIso->Id == 0 );
    if ( pIso->vAllies == NULL )
        pIso->vAllies = Vec_IntAlloc( 8 );
    Vec_IntPush( pIso->vAllies, fCompl ? -Id : Id );        
}
void Iso_ManAssignAdjacency( Iso_Man_t * p )
{
    Iso_Obj_t * pIso, * pIso0, * pIso1;
    Aig_Obj_t * pObj, * pObjLi;
    int i;
    // clean
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( i == 0 ) continue;
        pIso = Iso_ManObj( p, i );
        if ( pIso->vAllies )
            Vec_IntClear( pIso->vAllies );
    }
    // create
    Aig_ManForEachNode( p->pAig, pObj, i )
    {
        pIso  = Iso_ManObj( p, i );
        pIso0 = Iso_ManObj( p, Aig_ObjFaninId0(pObj) );
        pIso1 = Iso_ManObj( p, Aig_ObjFaninId1(pObj) );
        if ( pIso->Id ) // unique - add to non-unique fanins
        {
            if ( pIso0->Id == 0 )
                Iso_ObjAddToAllies( pIso0, pIso->Id, Aig_ObjFaninC0(pObj) );
            if ( pIso1->Id == 0 )
                Iso_ObjAddToAllies( pIso1, pIso->Id, Aig_ObjFaninC1(pObj) );
        }
        else // non-unique - assign unique fanins to it
        {
            if ( pIso0->Id != 0 )
                Iso_ObjAddToAllies( pIso, pIso0->Id, Aig_ObjFaninC0(pObj) );
            if ( pIso1->Id != 0 )
                Iso_ObjAddToAllies( pIso, pIso1->Id, Aig_ObjFaninC1(pObj) );
        }
    }
    // consider flops
    Aig_ManForEachLiLoSeq( p->pAig, pObjLi, pObj, i )
    {
        if ( Aig_ObjFaninId0(pObjLi) == 0 ) // ignore constant!
            continue;
        pIso  = Iso_ManObj( p, Aig_ObjId(pObj) );
        pIso0 = Iso_ManObj( p, Aig_ObjFaninId0(pObjLi) );
        if ( pIso->Id ) // unique - add to non-unique fanins
        {
            if ( pIso0->Id == 0 )
                Iso_ObjAddToAllies( pIso0, pIso->Id, Aig_ObjFaninC0(pObjLi) );
        }
        else // non-unique - assign unique fanins to it
        {
            if ( pIso0->Id != 0 )
                Iso_ObjAddToAllies( pIso, pIso0->Id, Aig_ObjFaninC0(pObjLi) );
        }
    }
    // sort
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( i == 0 ) continue;
        pIso = Iso_ManObj( p, i );
        if ( pIso->vAllies )
            Vec_IntSort( pIso->vAllies, 0 );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManRehashClassNodes( Iso_Man_t * p )
{
    Iso_Obj_t * pIso, * pTemp;
    int i;
    // collect nodes
    Vec_PtrClear( p->vTemp1 );
    Vec_PtrClear( p->vTemp2 );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
    {
        for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
            if ( pTemp->Id == 0 )
                Vec_PtrPush( p->vTemp1, pTemp );
            else
                Vec_PtrPush( p->vTemp2, pTemp );
    }
    // clean and add nodes
    p->nClasses = 0;       // total number of classes
    p->nEntries = 0;       // total number of entries
    p->nSingles = 0;       // total number of singletons
    memset( p->pBins, 0, sizeof(int) * p->nBins );
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vTemp1, pTemp, i )
    {
        assert( pTemp->Id == 0 );
        pTemp->iClass = pTemp->iNext = 0;
        Iso_ObjHashAdd( p, pTemp );
    }
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vTemp2, pTemp, i )
    {
        assert( pTemp->Id != 0 );
        pTemp->iClass = pTemp->iNext = 0;
    }
    // collect new classes
    Iso_ManCollectClasses( p );
}

/**Function*************************************************************

  Synopsis    [Find nodes with the min number of edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Iso_Obj_t * Iso_ManFindBestObj( Iso_Man_t * p, Iso_Obj_t * pIso )
{
    Iso_Obj_t * pTemp, * pBest = NULL;
    int nNodesBest = -1, nNodes;
    int nEdgesBest = -1, nEdges;
    assert( pIso->Id == 0 );
    if ( pIso->Level == 0 )
        return pIso;
    for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
    {
        assert( pTemp->Id == 0 );
        Iso_ManObjCount( p->pAig, Iso_AigObj(p, pTemp), &nNodes, &nEdges );
//        printf( "%d,%d ", nNodes, nEdges );
        if ( nNodesBest < nNodes || (nNodesBest == nNodes && nEdgesBest < nEdges) )
        {
            nNodesBest = nNodes;
            nEdgesBest = nEdges;
            pBest = pTemp;
        }
    }
//    printf( "\n" );
    return pBest;
}

/**Function*************************************************************

  Synopsis    [Find nodes with the min number of edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManBreakTies( Iso_Man_t * p, int fVerbose )
{
    int fUseOneBest = 0;
    Iso_Obj_t * pIso, * pTemp;
    int i, LevelStart = 0;
    pIso = (Iso_Obj_t *)Vec_PtrEntry( p->vClasses, 0 );
    LevelStart = pIso->Level;
    if ( fVerbose )
        printf( "Best level %d\n", LevelStart ); 
    Vec_PtrForEachEntry( Iso_Obj_t *, p->vClasses, pIso, i )
    {
        if ( (int)pIso->Level < LevelStart )
            break;
        if ( !fUseOneBest )
        {
            for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
            {
                assert( pTemp->Id ==  0 );
                pTemp->Id = p->nObjIds++;
            }
            continue;
        }
        if ( pIso->Level == 0 && pIso->nFoutPos + pIso->nFoutNeg == 0 )
        {
            for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
                pTemp->Id = p->nObjIds++;
            continue;
        }
        pIso = Iso_ManFindBestObj( p, pIso );
        pIso->Id = p->nObjIds++;
    }
}

/**Function*************************************************************

  Synopsis    [Finalizes unification of combinational outputs.]

  Description [Assigns IDs to the unclassified CIs in the order of obj IDs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Iso_ManFinalize( Iso_Man_t * p )
{
    Vec_Int_t * vRes;
    Aig_Obj_t * pObj;
    int i;
    assert( p->nClasses == 0 );
    assert( Vec_PtrSize(p->vClasses) == 0 );
    // set canonical numbers
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( !Aig_ObjIsPi(pObj) && !Aig_ObjIsNode(pObj) )
        {
            pObj->iData = -1;
            continue;
        }
        pObj->iData = Iso_ManObj(p, Aig_ObjId(pObj))->Id;
        assert( pObj->iData > 0 );
    }
    Aig_ManConst1(p->pAig)->iData = 0;
    // assign unique IDs to the CIs
    Vec_PtrClear( p->vTemp1 );
    Vec_PtrClear( p->vTemp2 );
    Aig_ManForEachPi( p->pAig, pObj, i )
    {
        assert( pObj->iData > 0 );
        if ( Aig_ObjPioNum(pObj) >= Aig_ManPiNum(p->pAig) - Aig_ManRegNum(p->pAig) ) // flop
            Vec_PtrPush( p->vTemp2, pObj );
        else // PI
            Vec_PtrPush( p->vTemp1, pObj );
    }
    // sort CIs by their IDs
    Vec_PtrSort( p->vTemp1, (int (*)(void))Iso_ObjCompareByData );
    Vec_PtrSort( p->vTemp2, (int (*)(void))Iso_ObjCompareByData );
    // create the result
    vRes = Vec_IntAlloc( Aig_ManPiNum(p->pAig) );
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vTemp1, pObj, i )
        Vec_IntPush( vRes, Aig_ObjPioNum(pObj) );
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vTemp2, pObj, i )
        Vec_IntPush( vRes, Aig_ObjPioNum(pObj) );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Find nodes with the min number of edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Iso_ManDumpOneClass( Iso_Man_t * p )
{
    Vec_Ptr_t * vNodes = Vec_PtrAlloc( 100 );
    Iso_Obj_t * pIso, * pTemp;
    Aig_Man_t * pNew = NULL;
    assert( p->nClasses > 0 );
    pIso = (Iso_Obj_t *)Vec_PtrEntry( p->vClasses, 0 );
    assert( pIso->Id == 0 );
    for ( pTemp = pIso; pTemp; pTemp = Iso_ManObj(p, pTemp->iClass) )
    {
        assert( pTemp->Id == 0 );
        Vec_PtrPush( vNodes, Iso_AigObj(p, pTemp) );
    }
    pNew = Aig_ManDupNodes( p->pAig, vNodes );
    Vec_PtrFree( vNodes );
    Aig_ManShow( pNew, 0, NULL ); 
    Aig_ManStopP( &pNew );
}

/**Function*************************************************************

  Synopsis    [Finds canonical permutation of CIs and assigns unique IDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Saig_ManFindIsoPerm( Aig_Man_t * pAig, int fVerbose )
{
    Vec_Int_t * vRes;
    Iso_Man_t * p;
    int clk, clk2 = clock();
    p = Iso_ManCreate( pAig );
    Iso_ManPrintClasses( p, fVerbose, 0 );
    while ( p->nClasses )
    {
        // assign adjacency to classes
        clk = clock();
        Iso_ManAssignAdjacency( p );
        p->timeFout += clock() - clk;
        // rehash the class nodes
        clk = clock();
        Iso_ManRehashClassNodes( p );
        p->timeHash += clock() - clk;
        Iso_ManPrintClasses( p, fVerbose, 0 );
        // force refinement
        while ( p->nSingles == 0 && p->nClasses )
        {
//            Iso_ManPrintClasseSizes( p );
            // assign IDs to the topmost level of classes
            Iso_ManBreakTies( p, fVerbose );
            // assign adjacency to classes
            clk = clock();
            Iso_ManAssignAdjacency( p );
            p->timeFout += clock() - clk;
            // rehash the class nodes
            clk = clock();
            Iso_ManRehashClassNodes( p );
            p->timeHash += clock() - clk;
            Iso_ManPrintClasses( p, fVerbose, 0 );
        }
    }
    p->timeTotal = clock() - clk2;
//    printf( "IDs assigned = %d.  Objects = %d.\n", p->nObjIds, 1+Aig_ManPiNum(p->pAig)+Aig_ManNodeNum(p->pAig) );
    assert( p->nObjIds == 1+Aig_ManPiNum(p->pAig)+Aig_ManNodeNum(p->pAig) );
//    if ( p->nClasses )
//        Iso_ManDumpOneClass( p );
    vRes = Iso_ManFinalize( p );
    Iso_ManStop( p, fVerbose );
    return vRes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

