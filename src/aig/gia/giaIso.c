/**CFile****************************************************************

  FileName    [giaIso.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Graph isomorphism.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaIso.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START
 

#define ISO_MASK 0xFF
static int s_256Primes[ISO_MASK+1] = 
{
    0x984b6ad9,0x18a6eed3,0x950353e2,0x6222f6eb,0xdfbedd47,0xef0f9023,0xac932a26,0x590eaf55,
    0x97d0a034,0xdc36cd2e,0x22736b37,0xdc9066b0,0x2eb2f98b,0x5d9c7baf,0x85747c9e,0x8aca1055,
    0x50d66b74,0x2f01ae9e,0xa1a80123,0x3e1ce2dc,0xebedbc57,0x4e68bc34,0x855ee0cf,0x17275120,
    0x2ae7f2df,0xf71039eb,0x7c283eec,0x70cd1137,0x7cf651f3,0xa87bfa7a,0x14d87f02,0xe82e197d,
    0x8d8a5ebe,0x1e6a15dc,0x197d49db,0x5bab9c89,0x4b55dea7,0x55dede49,0x9a6a8080,0xe5e51035,
    0xe148d658,0x8a17eb3b,0xe22e4b38,0xe5be2a9a,0xbe938cbb,0x3b981069,0x7f9c0c8e,0xf756df10,
    0x8fa783f7,0x252062ce,0x3dc46b4b,0xf70f6432,0x3f378276,0x44b137a1,0x2bf74b77,0x04892ed6,
    0xfd318de1,0xd58c235e,0x94c6d25b,0x7aa5f218,0x35c9e921,0x5732fbbb,0x06026481,0xf584a44f,
    0x946e1b5f,0x8463d5b2,0x4ebca7b2,0x54887b15,0x08d1e804,0x5b22067d,0x794580f6,0xb351ea43,
    0xbce555b9,0x19ae2194,0xd32f1396,0x6fc1a7f1,0x1fd8a867,0x3a89fdb0,0xea49c61c,0x25f8a879,
    0xde1e6437,0x7c74afca,0x8ba63e50,0xb1572074,0xe4655092,0xdb6f8b1c,0xc2955f3c,0x327f85ba,
    0x60a17021,0x95bd261d,0xdea94f28,0x04528b65,0xbe0109cc,0x26dd5688,0x6ab2729d,0xc4f029ce,
    0xacf7a0be,0x4c912f55,0x34c06e65,0x4fbb938e,0x1533fb5f,0x03da06bd,0x48262889,0xc2523d7d,
    0x28a71d57,0x89f9713a,0xf574c551,0x7a99deb5,0x52834d91,0x5a6f4484,0xc67ba946,0x13ae698f,
    0x3e390f34,0x34fc9593,0x894c7932,0x6cf414a3,0xdb7928ab,0x13a3b8a3,0x4b381c1d,0xa10b54cb,
    0x55359d9d,0x35a3422a,0x58d1b551,0x0fd4de20,0x199eb3f4,0x167e09e2,0x3ee6a956,0x5371a7fa,
    0xd424efda,0x74f521c5,0xcb899ff6,0x4a42e4f4,0x747917b6,0x4b08df0b,0x090c7a39,0x11e909e4,
    0x258e2e32,0xd9fad92d,0x48fe5f69,0x0545cde6,0x55937b37,0x9b4ae4e4,0x1332b40e,0xc3792351,
    0xaff982ef,0x4dba132a,0x38b81ef1,0x28e641bf,0x227208c1,0xec4bbe37,0xc4e1821c,0x512c9d09,
    0xdaef1257,0xb63e7784,0x043e04d7,0x9c2cea47,0x45a0e59a,0x281315ca,0x849f0aac,0xa4071ed3,
    0x0ef707b3,0xfe8dac02,0x12173864,0x471f6d46,0x24a53c0a,0x35ab9265,0xbbf77406,0xa2144e79,
    0xb39a884a,0x0baf5b6d,0xcccee3dd,0x12c77584,0x2907325b,0xfd1adcd2,0xd16ee972,0x345ad6c1,
    0x315ebe66,0xc7ad2b8d,0x99e82c8d,0xe52da8c8,0xba50f1d3,0x66689cd8,0x2e8e9138,0x43e15e74,
    0xf1ced14d,0x188ec52a,0xe0ef3cbb,0xa958aedc,0x4107a1bc,0x5a9e7a3e,0x3bde939f,0xb5b28d5a,
    0x596fe848,0xe85ad00c,0x0b6b3aae,0x44503086,0x25b5695c,0xc0c31dcd,0x5ee617f0,0x74d40c3a,
    0xd2cb2b9f,0x1e19f5fa,0x81e24faf,0xa01ed68f,0xcee172fc,0x7fdf2e4d,0x002f4774,0x664f82dd,
    0xc569c39a,0xa2d4dcbe,0xaadea306,0xa4c947bf,0xa413e4e3,0x81fb5486,0x8a404970,0x752c980c,
    0x98d1d881,0x5c932c1e,0xeee65dfb,0x37592cdd,0x0fd4e65b,0xad1d383f,0x62a1452f,0x8872f68d,
    0xb58c919b,0x345c8ee3,0xb583a6d6,0x43d72cb3,0x77aaa0aa,0xeb508242,0xf2db64f8,0x86294328,
    0x82211731,0x1239a9d5,0x673ba5de,0xaf4af007,0x44203b19,0x2399d955,0xa175cd12,0x595928a7,
    0x6918928b,0xde3126bb,0x6c99835c,0x63ba1fa2,0xdebbdff0,0x3d02e541,0xd6f7aac6,0xe80b4cd0,
    0xd0fa29f1,0x804cac5e,0x2c226798,0x462f624c,0xad05b377,0x22924fcd,0xfbea205c,0x1b47586d
};
static int s_256Primes2[ISO_MASK+1] = 
{
    0xcaa57efb,0x64bd4878,0x3419334a,0x712e5f6b,0x9fa9d687,0x06f8645f,0x620ca96f,0xdc5d6cce,
    0x392f3257,0x52140f06,0xc4b3bda4,0xe8c7eba7,0x066bd754,0xc5941f26,0xe6dfd573,0x328dd14d,
    0xb1cb4ba7,0x1d37a9b8,0x96a195a5,0x970e535a,0x290351b8,0x570000f6,0xe14ae341,0x35ede6a6,
    0x9a02f032,0xaf2ebb58,0x146be492,0x670b3e4b,0x72fa6cfd,0xa243af97,0xbbd5fc21,0xcb8852a2,
    0x5d5b4a42,0xeefff0ac,0xa59ad1b6,0x3ec55544,0x48d64f69,0x9065d3d0,0xdd09485b,0xdd63bd09,
    0x605e811d,0xc4b4ed7d,0xb0b58558,0x0644400b,0x12222346,0x086f146a,0xad6dee36,0x5488d1a3,
    0x0c93bc0c,0x18555d92,0x9f4427bf,0xa590a66a,0x3a630fda,0xf1681c2e,0x948a16fb,0x16fe3338,
    0xc9832357,0xd1e8e6b5,0xd9cfe034,0x05b22f26,0x27233c6e,0x355890e1,0xfbe6eaf3,0x0dcd8e8f,
    0x00b5df46,0xd97730ac,0xc6dfd8ff,0x0cb1840a,0x41e9d249,0xbb471b4e,0x480b8f63,0x1ffe8871,
    0x17b11821,0x1709e440,0xcefb3668,0xa4954ddd,0xf03ef8b5,0x6b3e633c,0xe5813096,0x3697c9a6,
    0x7800f52f,0x73a7aa39,0x59ac23b7,0xb4663166,0x9ca9d6f8,0x2d441072,0x38cef3d3,0x39a3faf6,
    0x89299fb9,0xd558295f,0xcf79c633,0x232dd96e,0xadb2955b,0xe962cbb9,0xab7c0061,0x1027c329,
    0xb4b43e07,0x25240a7a,0x98ea4825,0xdbf2edbd,0x8be15d26,0x879f3cd9,0xa4138089,0xa32dcb06,
    0x602af961,0x4b13f451,0x1c87d0d5,0xc3bb141b,0x9ebf55a1,0xef030a9a,0x8d199b93,0xdabcbb56,
    0xf412f80f,0x302e90ad,0xc4d9878b,0xc392f650,0x4fd3a614,0x0a96ddc4,0xcd1878c7,0x9ddd3ae1,
    0xdaf46458,0xba7c8656,0xf667948f,0xc37e3c23,0x04a577c6,0xbe615f1e,0xcc97406c,0xd497f16f,
    0x79586586,0xd2057d14,0x1bb92028,0xab888e5e,0x26bef100,0xf46b3671,0xf21f1acc,0x67f288c8,
    0x39c722df,0x61d21eaf,0x9c5853a0,0x63b693c7,0x1ea53c0a,0x95bc0a85,0xa7372f2d,0x3ef6a6b3,
    0x82c9c4ac,0x4dea10ee,0xdfcb543d,0xd412f427,0x53e27f2c,0x875d8422,0x5367a7d8,0x41acf3fa,
    0xbce47234,0x8056fb9a,0x4e9a4c48,0xe4a45945,0x2cfee3ae,0xb4554b10,0x5e37a915,0x591b1963,
    0x4fa255c1,0xe01c897b,0x504e6208,0x7c7368eb,0x13808fd7,0x02ac0816,0x30305d2c,0x6c4bbdb7,
    0xa48a9599,0x57466059,0x4c6ebfc7,0x8587ccdf,0x6ff0abf0,0x5b6b63fe,0x31d9ec64,0x63458abd,
    0x21245905,0xccdb28fc,0xac828acb,0xe5e82bea,0xa7d76141,0xa699038e,0xcaba7e06,0x2710253f,
    0x2ff9c94d,0x26e48a2c,0xd713ec5e,0x869f2ed4,0x25bcd712,0xcb3e918f,0x615c3a5a,0x9fb43903,
    0x37900eb9,0x4f682db0,0x35a80dc6,0x4eb27c65,0x502735ab,0xb163b4c8,0x604649a8,0xb23a6cd3,
    0x9f715091,0x2e6fbb51,0x2ec9144b,0x272cbe65,0x90a0a453,0x420e1503,0x2d00d338,0x4aa96675,
    0xd025b61c,0xab02d9d7,0x2afe2a37,0xf8129b9b,0x4db04c54,0x654a5c06,0x3213ff51,0x4e09d0b1,
    0x333369a3,0xae27310a,0x91d076d0,0xa96ebcd0,0xefde54f4,0x021c309a,0xd506f53d,0xa5635251,
    0x2f23916e,0x1fe86bb1,0xcbc62160,0x2147c8cc,0xdeb3e47c,0x028e3987,0x8061de42,0x39be931b,
    0x2b7e54c5,0xe64d2f96,0x4069522d,0x4aa66857,0x83b62634,0x4ba72095,0x9aade2a9,0xf1223cd9,
    0x91cbddf0,0xec5d237f,0x593f3280,0x0b924439,0x446f4063,0xc66f8d8c,0x8b7128ba,0xb597f451,
    0xc8925236,0x1720f235,0x7cd2e9a0,0x4c130339,0x8a665a52,0x5bef2733,0xba35d9bc,0x6d26644c
};

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Gia_IsoMan_t_       Gia_IsoMan_t;
struct Gia_IsoMan_t_ 
{
    Gia_Man_t *      pGia;
    int              nObjs;
    int              nUniques;
    int              nSingles;
    int              nEntries;
    // internal data
    int *            pLevels;
    int *            pUniques;
    word *           pStoreW;
    unsigned *       pStoreU;
    // equivalence classes
    Vec_Int_t *      vLevCounts;
    Vec_Int_t *      vClasses;
    Vec_Int_t *      vClasses2;
    // statistics 
    int              timeStart;
    int              timeSim;
    int              timeRefine;
    int              timeSort;
    int              timeOther;
    int              timeTotal;
};

static inline unsigned  Gia_IsoGetValue( Gia_IsoMan_t * p, int i )             { return (unsigned)(p->pStoreW[i]);       }
static inline unsigned  Gia_IsoGetItem( Gia_IsoMan_t * p, int i )              { return (unsigned)(p->pStoreW[i] >> 32); }

static inline void      Gia_IsoSetValue( Gia_IsoMan_t * p, int i, unsigned v ) { ((unsigned *)(p->pStoreW + i))[0] = v;  }
static inline void      Gia_IsoSetItem( Gia_IsoMan_t * p, int i, unsigned v )  { ((unsigned *)(p->pStoreW + i))[1] = v;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_IsoMan_t * Gia_IsoManStart( Gia_Man_t * pGia )
{
    Gia_IsoMan_t * p;
    p = ABC_CALLOC( Gia_IsoMan_t, 1 );
    p->pGia      = pGia;
    p->nObjs     = Gia_ManObjNum( pGia );
    p->nUniques  = 1;
    p->nEntries  = p->nObjs;
    // internal data
    p->pLevels   = ABC_CALLOC( int, p->nObjs );
    p->pUniques  = ABC_CALLOC( int, p->nObjs );
    p->pStoreW   = ABC_CALLOC( word, p->nObjs );
    // class representation
    p->vClasses  = Vec_IntAlloc( p->nObjs/4 );
    p->vClasses2 = Vec_IntAlloc( p->nObjs/4 );
    return p;
}
void Gia_IsoManStop( Gia_IsoMan_t * p )
{
    // class representation
    Vec_IntFree( p->vClasses );
    Vec_IntFree( p->vClasses2 );
    // internal data
    ABC_FREE( p->pLevels );
    ABC_FREE( p->pUniques );
    ABC_FREE( p->pStoreW );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoPrintClasses( Gia_IsoMan_t * p )
{
    int fVerbose = 0;
    int i, k, iBegin, nSize;
    printf( "The total of %d classes:\n", Vec_IntSize(p->vClasses)/2 );
    Vec_IntForEachEntryDouble( p->vClasses, iBegin, nSize, i )
    {
        printf( "%5d : (%3d,%3d)  ", i/2, iBegin, nSize );
        if ( fVerbose )
        {
            printf( "{" );
            for ( k = 0; k < nSize; k++ )
                printf( " %3d,%08x", Gia_IsoGetItem(p, iBegin+k), Gia_IsoGetValue(p, iBegin+k) );
            printf( " }" );
        }
        printf( "\n" );
    }
}
void Gia_IsoPrint( Gia_IsoMan_t * p, int Iter, int Time )
{
    printf( "Iter %4d :  ", Iter );
    printf( "Entries =%8d.  ", p->nEntries );
    printf( "Classes =%8d.  ", Vec_IntSize(p->vClasses)/2 );
    printf( "Singles =%8d.  ", p->nSingles );
    printf( "%9.2f sec", (float)(Time)/(float)(CLOCKS_PER_SEC) );
    printf( "\n" );
    fflush( stdout );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoPrepare( Gia_IsoMan_t * p )
{
    Gia_Obj_t * pObj;
    int * pLevBegins, * pLevSizes;
    int i, iObj, MaxLev = 0;
    // assign levels
    p->pLevels[0] = 0;
    Gia_ManForEachCi( p->pGia, pObj, i )
        p->pLevels[Gia_ObjId(p->pGia, pObj)] = 0;
    Gia_ManForEachAnd( p->pGia, pObj, i )
        p->pLevels[i] = 1 + Abc_MaxInt( p->pLevels[Gia_ObjFaninId0(pObj, i)], p->pLevels[Gia_ObjFaninId1(pObj, i)] );
    Gia_ManForEachCo( p->pGia, pObj, i )
    {
        iObj = Gia_ObjId(p->pGia, pObj);
        p->pLevels[iObj] = 1 + p->pLevels[Gia_ObjFaninId0(pObj, iObj)]; // "1 +" is different!
        MaxLev = Abc_MaxInt( MaxLev, p->pLevels[Gia_ObjId(p->pGia, pObj)] );
    }

    // count nodes on each level
    pLevSizes = ABC_CALLOC( int, MaxLev+1 );
    for ( i = 1; i < p->nObjs; i++ )
        pLevSizes[p->pLevels[i]]++;
    // start classes
    Vec_IntClear( p->vClasses );
    Vec_IntPush( p->vClasses, 0 );
    Vec_IntPush( p->vClasses, 1 );
    // find beginning of each level
    pLevBegins = ABC_CALLOC( int, MaxLev+2 );
    pLevBegins[0] = 1;
    for ( i = 0; i <= MaxLev; i++ )
    {
        Vec_IntPush( p->vClasses, pLevBegins[i] );
        Vec_IntPush( p->vClasses, pLevSizes[i] );
        pLevBegins[i+1] = pLevBegins[i] + pLevSizes[i];
    }
    assert( pLevBegins[MaxLev+1] == p->nObjs );
    // put them into the structure
    for ( i = 1; i < p->nObjs; i++ )
    {
//        Gia_IsoSetValue( p, pLevBegins[p->pLevels[i]], p->pLevels[i] );
        Gia_IsoSetItem( p, pLevBegins[p->pLevels[i]]++, i );
    }
    ABC_FREE( pLevBegins );
    ABC_FREE( pLevSizes );
/*
    // print the results
    for ( i = 0; i < p->nObjs; i++ )
        printf( "%3d : (%d,%d)\n", i, Gia_IsoGetItem(p, i), Gia_IsoGetValue(p, i) );
    printf( "\n" );
*/
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoAssignUnique( Gia_IsoMan_t * p )
{
    int i, iBegin, nSize;
    p->nSingles = 0;
    Vec_IntClear( p->vClasses2 );
    Vec_IntForEachEntryDouble( p->vClasses, iBegin, nSize, i )
    {
        if ( nSize == 1 )
        {
            assert( p->pUniques[Gia_IsoGetItem(p, iBegin)] == 0 );
            p->pUniques[Gia_IsoGetItem(p, iBegin)] = p->nUniques++;
            p->nSingles++;
        }
        else
        {
            Vec_IntPush( p->vClasses2, iBegin );
            Vec_IntPush( p->vClasses2, nSize );
        }
    }
    ABC_SWAP( Vec_Int_t *, p->vClasses, p->vClasses2 );
    p->nEntries -= p->nSingles;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Gia_IsoUpdate( int Iter, int iLevel, int iUniqueF, int fCompl )
{
//    iLevel = ((Iter + iLevel) * (Iter + iLevel + 1)) >> 1;
    if ( iUniqueF == 0 )
        return iLevel * s_256Primes[Abc_Var2Lit(iLevel, fCompl) & ISO_MASK];
//    iUniqueF = ((Iter + iUniqueF) * (Iter + iUniqueF + 1)) >> 1;
    return iLevel * s_256Primes[Abc_Var2Lit(iLevel, fCompl) & ISO_MASK] + 
           iUniqueF * s_256Primes[Abc_Var2Lit(iUniqueF, fCompl) & ISO_MASK];
}
void Gia_IsoSimulate( Gia_IsoMan_t * p, int Iter )
{
    Gia_Obj_t * pObj, * pObjF;
    int i, iObj;
    // initialize constant, inputs, and flops in the first frame
//    Gia_ManConst0(p->pGia)->Value = s_256Primes2[Abc_Var2Lit(Iter, 0) & ISO_MASK];
    Gia_ManConst0(p->pGia)->Value = s_256Primes2[ISO_MASK-2];
    Gia_ManForEachPi( p->pGia, pObj, i )
//        pObj->Value = s_256Primes2[Abc_Var2Lit(Iter, 1) & ISO_MASK];
        pObj->Value = s_256Primes2[ISO_MASK-1];
    if ( Iter == 0 )
        Gia_ManForEachRo( p->pGia, pObj, i )
            pObj->Value = s_256Primes2[ISO_MASK];
    // simulate objects
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        pObj->Value += Gia_ObjFanin0(pObj)->Value + Gia_IsoUpdate(Iter, p->pLevels[i], p->pUniques[Gia_ObjFaninId0(pObj, i)], Gia_ObjFaninC0(pObj));
        pObj->Value += Gia_ObjFanin1(pObj)->Value + Gia_IsoUpdate(Iter, p->pLevels[i], p->pUniques[Gia_ObjFaninId1(pObj, i)], Gia_ObjFaninC1(pObj));
//printf( "AND %3d: %08x\n", i, pObj->Value );
    }
    Gia_ManForEachCo( p->pGia, pObj, i )
    {
        iObj = Gia_ObjId(p->pGia, pObj);
        pObj->Value += Gia_ObjFanin0(pObj)->Value + Gia_IsoUpdate(Iter, p->pLevels[iObj], p->pUniques[Gia_ObjFaninId0(pObj, iObj)], Gia_ObjFaninC0(pObj));
//printf( "CO  %3d: %08x\n", i, pObj->Value );
    }
    // transfer flop values
    Gia_ManForEachRiRo( p->pGia, pObjF, pObj, i )
        pObj->Value += pObjF->Value;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_IsoSort( Gia_IsoMan_t * p )
{
    Gia_Obj_t * pObj, * pObj0;
    int i, k, fSameValue, iBegin, iBeginOld, nSize, nSizeNew, clk;
    int fRefined = 0;

    // go through the equiv classes
    p->nSingles = 0;
    Vec_IntClear( p->vClasses2 );
    Vec_IntForEachEntryDouble( p->vClasses, iBegin, nSize, i )
    {
        assert( nSize > 1 );
        fSameValue = 1;
        pObj0 = Gia_ManObj( p->pGia, Gia_IsoGetItem(p,iBegin) );
        for ( k = 0; k < nSize; k++ )
        {
            pObj = Gia_ManObj( p->pGia, Gia_IsoGetItem(p,iBegin+k) );
            Gia_IsoSetValue( p, iBegin+k, pObj->Value );
            if ( pObj->Value != pObj0->Value )
                fSameValue = 0;
        }
        if ( fSameValue )
        {
            Vec_IntPush( p->vClasses2, iBegin );
            Vec_IntPush( p->vClasses2, nSize );
            continue;
        }
        fRefined = 1;
        // sort objects
        clk = clock();
        Abc_QuickSort3( p->pStoreW + iBegin, nSize, 0 );
        p->timeSort += clock() - clk;
        // divide into new classes
        iBeginOld = iBegin;
        pObj0 = Gia_ManObj( p->pGia, Gia_IsoGetItem(p,iBegin) );
        for ( k = 1; k < nSize; k++ )
        {
            pObj = Gia_ManObj( p->pGia, Gia_IsoGetItem(p,iBegin+k) );
            if ( pObj0->Value == pObj->Value )
                continue;
            nSizeNew = iBegin + k - iBeginOld;
            if ( nSizeNew == 1 )
            {
                assert( p->pUniques[Gia_IsoGetItem(p, iBeginOld)] == 0 );
                p->pUniques[Gia_IsoGetItem(p, iBeginOld)] = p->nUniques++;
                p->nSingles++;
            }
            else
            {
                Vec_IntPush( p->vClasses2, iBeginOld );
                Vec_IntPush( p->vClasses2, nSizeNew );
            }
            iBeginOld = iBegin + k;
            pObj0 = pObj;
        }
        // add the last one
        nSizeNew = iBegin + k - iBeginOld;
        if ( nSizeNew == 1 )
        {
            assert( p->pUniques[Gia_IsoGetItem(p, iBeginOld)] == 0 );
            p->pUniques[Gia_IsoGetItem(p, iBeginOld)] = p->nUniques++;
            p->nSingles++;
        }
        else
        {
            Vec_IntPush( p->vClasses2, iBeginOld );
            Vec_IntPush( p->vClasses2, nSizeNew );
        }
    }

    ABC_SWAP( Vec_Int_t *, p->vClasses, p->vClasses2 );
    p->nEntries -= p->nSingles;
    return fRefined;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Gia_IsoCollectCos( Gia_IsoMan_t * p, int fVerbose )
{
    Vec_Ptr_t * vGroups;
    Vec_Int_t * vLevel;
    Gia_Obj_t * pObj;
    int i, k, iBegin, nSize;

    // add singletons
    vGroups = Vec_PtrAlloc( 1000 );
    Gia_ManForEachPo( p->pGia, pObj, i )
        if ( p->pUniques[Gia_ObjId(p->pGia, pObj)] > 0 )
        {
            vLevel = Vec_IntAlloc( 1 );
            Vec_IntPush( vLevel, i );
            Vec_PtrPush( vGroups, vLevel );
        }

    // add groups
    Vec_IntForEachEntryDouble( p->vClasses, iBegin, nSize, i )
    {
        for ( k = 0; k < nSize; k++ )
        {
            pObj = Gia_ManObj( p->pGia, Gia_IsoGetItem(p,iBegin+k) );
            if ( Gia_ObjIsPo(p->pGia, pObj) )
                break;
        }
        if ( k == nSize )
            continue;
        vLevel = Vec_IntAlloc( 8 );
        for ( k = 0; k < nSize; k++ )
        {
            pObj = Gia_ManObj( p->pGia, Gia_IsoGetItem(p,iBegin+k) );
            if ( Gia_ObjIsPo(p->pGia, pObj) )
                Vec_IntPush( vLevel, Gia_ObjCioId(pObj) );
        }
        Vec_PtrPush( vGroups, vLevel );
    }
    // canonicize order
    Vec_PtrForEachEntry( Vec_Int_t *, vGroups, vLevel, i )
        Vec_IntSort( vLevel, 0 );
    Vec_VecSortByFirstInt( (Vec_Vec_t *)vGroups, 0 );
//    Vec_VecFree( (Vec_Vec_t *)vGroups );
//    return NULL;
    return vGroups;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Gia_IsoDeriveEquivPos( Gia_Man_t * pGia, int fVerbose )
{
    Vec_Ptr_t * vEquivs;
    Gia_IsoMan_t * p;
    int nIterMax = 1000, fRefined;
    int i, c, clk = clock(), clkTotal = clock();

    Gia_ManCleanValue( pGia );
    p = Gia_IsoManStart( pGia );
    Gia_IsoPrepare( p );
    Gia_IsoAssignUnique( p );
    p->timeStart = clock() - clk;
//    Gia_IsoPrintClasses( p );
    if ( fVerbose )
        Gia_IsoPrint( p, 0, clock() - clkTotal );
    for ( i = 0, c = 0; i < nIterMax && c < 3; i++, c++ )
    {
        clk = clock();
        Gia_IsoSimulate( p, i );
        p->timeSim += clock() - clk;

        clk = clock();
        fRefined = Gia_IsoSort( p );
        if ( fRefined )
            c = 0;
        p->timeRefine += clock() - clk;

//        Gia_IsoPrintClasses( p );
        if ( fVerbose )
            Gia_IsoPrint( p, i+1, clock() - clkTotal );
    }
    if ( fVerbose )
    {
        p->timeTotal = clock() - clkTotal;
        p->timeOther = p->timeTotal - p->timeStart - p->timeSim - p->timeRefine;

        ABC_PRTP( "Start    ", p->timeStart,              p->timeTotal );
        ABC_PRTP( "Simulate ", p->timeSim,                p->timeTotal );
        ABC_PRTP( "Refine   ", p->timeRefine-p->timeSort, p->timeTotal );
        ABC_PRTP( "Sort     ", p->timeSort,               p->timeTotal );
        ABC_PRTP( "Other    ", p->timeOther,              p->timeTotal );
        ABC_PRTP( "TOTAL    ", p->timeTotal,              p->timeTotal );
    }
    vEquivs = Gia_IsoCollectCos( p, fVerbose );
    Gia_IsoManStop( p );
    return vEquivs;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManIsoReduce( Gia_Man_t * pGia, Vec_Ptr_t ** pvPosEquivs, int fVerbose )
{ 
    Gia_Man_t * pPart;
    Vec_Ptr_t * vEquivs;
    Vec_Int_t * vRemain, * vLevel;
    int i, clk = clock();
    // create equivalences
    vEquivs = Gia_IsoDeriveEquivPos( pGia, fVerbose );
    // collect the first ones
    vRemain = Vec_IntAlloc( 100 );
    Vec_PtrForEachEntry( Vec_Int_t *, vEquivs, vLevel, i )
        Vec_IntPush( vRemain, Vec_IntEntry(vLevel, 0) );
    // derive the resulting AIG
    pPart = Gia_ManDupCones( pGia, Vec_IntArray(vRemain), Vec_IntSize(vRemain) );
    Vec_IntFree( vRemain );
    // report the results
    printf( "Reduced %d outputs to %d outputs.  ", Gia_ManPoNum(pGia), Gia_ManPoNum(pPart) );
    Abc_PrintTime( 1, "Time", clock() - clk );
    if ( fVerbose )
    {
        printf( "Nontrivial classes:\n" );
        Vec_VecPrintInt( (Vec_Vec_t *)vEquivs, 1 );
    }
    if ( pvPosEquivs )
        *pvPosEquivs = vEquivs;
    else
        Vec_VecFree( (Vec_Vec_t *)vEquivs );
//    Gia_ManStopP( &pPart );
    return pPart;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_IsoTest( Gia_Man_t * pGia, int fVerbose )
{
    Vec_Ptr_t * vEquivs;
    int clk = clock(); 
    vEquivs = Gia_IsoDeriveEquivPos( pGia, fVerbose );
    printf( "Reduced %d outputs to %d.  ", Gia_ManPoNum(pGia), Vec_PtrSize(vEquivs) );
    Abc_PrintTime( 1, "Time", clock() - clk );
    if ( fVerbose && Gia_ManPoNum(pGia) != Vec_PtrSize(vEquivs) )
    {
        printf( "Nontrivial classes:\n" );
        Vec_VecPrintInt( (Vec_Vec_t *)vEquivs, 1 );
    }
    Vec_VecFree( (Vec_Vec_t *)vEquivs );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

