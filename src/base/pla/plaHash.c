/**CFile****************************************************************

  FileName    [plaHash.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SOP manager.]

  Synopsis    [Scalable SOP transformations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - March 18, 2015.]

  Revision    [$Id: plaHash.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pla.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define PLA_HASH_VALUE_NUM 256
static unsigned s_PlaHashValues[PLA_HASH_VALUE_NUM] = 
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

static inline int Pla_HashValue( int i )  { assert( i >= 0 && i < PLA_HASH_VALUE_NUM ); return s_PlaHashValues[i] & 0xFFFFFF; }


#define PLA_LIT_UNUSED 0xFFFF

typedef struct Tab_Obj_t_ Tab_Obj_t;
struct Tab_Obj_t_
{
    int         Table;
    int         Next;
    int         Cube;
    unsigned    VarA : 16;
    unsigned    VarB : 16;
};
typedef struct Tab_Man_t_ Tab_Man_t;
struct Tab_Man_t_
{
    int         SizeMask; // table size (2^Degree-1)
    int         nBins;    // number of entries
    Tab_Obj_t * pBins;    // hash table (lits -> cube + lit + lit)
    Pla_Man_t * pMan;     // manager
};

static inline Tab_Obj_t *  Tab_ManBin( Tab_Man_t * p, int Value ) { return p->pBins + (Value & p->SizeMask); }
static inline Tab_Obj_t *  Tab_ManEntry( Tab_Man_t * p, int i )   { return i ? p->pBins + i : NULL;          }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Tab_Man_t * Tab_ManAlloc( int LogSize, Pla_Man_t * pMan )
{
    Tab_Man_t * p = ABC_CALLOC( Tab_Man_t, 1 );
    assert( LogSize >= 4 && LogSize <= 24 );
    p->SizeMask = (1 << LogSize) - 1;
    p->pBins = ABC_CALLOC( Tab_Obj_t, p->SizeMask + 1 );
    p->nBins = 1;
    p->pMan  = pMan;
    return p;
}
static inline void Tab_ManFree( Tab_Man_t * p )
{
    ABC_FREE( p->pBins );
    ABC_FREE( p );
}
static inline void Tab_ManHashInsert( Tab_Man_t * p, int Value, int iCube )
{
    Tab_Obj_t * pBin  = Tab_ManBin( p, Value );
    Tab_Obj_t * pCell = p->pBins + p->nBins;
    pCell->Cube = iCube;
    pCell->Next = pBin->Table;
    pBin->Table = p->nBins++;
}
static inline int Tab_ManHashLookup( Tab_Man_t * p, int Value, Vec_Int_t * vCube )
{
    Tab_Obj_t * pEnt, * pBin = Tab_ManBin( p, Value );
    for ( pEnt = Tab_ManEntry(p, pBin->Table); pEnt; pEnt = Tab_ManEntry(p, pEnt->Next) )
       if ( Vec_IntEqual( Vec_WecEntry(&p->pMan->vLits, pEnt->Cube), vCube ) )
            return 1;
    return 0;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pla_CubeHashValue( Vec_Int_t * vCube )
{
    int i, Lit, Value = 0;
    Vec_IntForEachEntry( vCube, Lit, i )
        Value += Pla_HashValue(Lit);
    return Value;
}
void Pla_ManHashCubes( Pla_Man_t * p, Tab_Man_t * pTab )
{
    Vec_Int_t * vCube; int i, Value;
    Vec_IntClear( &p->vHashes );
    Vec_IntGrow( &p->vHashes, Pla_ManCubeNum(p) );
    Vec_WecForEachLevel( &p->vLits, vCube, i )
    {
        Value = Pla_CubeHashValue(vCube);
        Vec_IntPush( &p->vHashes, Value );
        Tab_ManHashInsert( pTab, Value, i );
    }
}
int Pla_ManHashDistance1( Pla_Man_t * p )
{
    Tab_Man_t * pTab;
    Vec_Int_t * vCube;
    Vec_Int_t * vCubeCopy = Vec_IntAlloc( p->nIns );
    int nBits = Abc_Base2Log( Pla_ManCubeNum(p) ) + 2;
    int i, k, Lit, Value, ValueCopy, Count = 0;
    assert( nBits <= 24 );
    pTab = Tab_ManAlloc( nBits, p );
    Pla_ManConvertFromBits( p );
    Pla_ManHashCubes( p, pTab );
    Vec_WecForEachLevel( &p->vLits, vCube, i )
    {
        Vec_IntClear( vCubeCopy );
        Vec_IntAppend( vCubeCopy, vCube );
        Value = ValueCopy = Vec_IntEntry( &p->vHashes, i );
        Vec_IntForEachEntry( vCubeCopy, Lit, k )
        {
            // create new
            Value += Pla_HashValue(Abc_LitNot(Lit)) - Pla_HashValue(Lit);
            Vec_IntWriteEntry( vCubeCopy, k, Abc_LitNot(Lit) );
            // check the cube
            Count += Tab_ManHashLookup( pTab, Value, vCubeCopy );
            // create old
            Value -= Pla_HashValue(Abc_LitNot(Lit)) - Pla_HashValue(Lit);
            Vec_IntWriteEntry( vCubeCopy, k, Lit );
        }
        assert( Value == ValueCopy );
    }
    Vec_IntFree( vCubeCopy );
    Tab_ManFree( pTab );
    assert( !(Count & 1) );
    return Count/2;
}
int Pla_ManHashDist1NumTest( Pla_Man_t * p )
{
    abctime clk = Abc_Clock();
    int Count = Pla_ManHashDistance1( p );
    printf( "Found %d pairs among %d cubes using cube hashing.  ", Count, Pla_ManCubeNum(p) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

