/**CFile****************************************************************

  FileName    [sscSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT sweeping under constraints.]

  Synopsis    [Simulation procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: sscSim.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sscInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline word Ssc_Random()            { return ((word)Gia_ManRandom(0) << 32) | ((word)Gia_ManRandom(0) << 0);              }
static inline word Ssc_Random1( int Bit )  { return ((word)Gia_ManRandom(0) << 32) | ((word)Gia_ManRandom(0) << 1) | (word)Bit;  }
static inline word Ssc_Random2()           { return ((word)Gia_ManRandom(0) << 32) | ((word)Gia_ManRandom(0) << 2) | (word)2;    }

static inline void Ssc_SimAnd( word * pSim, word * pSim0, word * pSim1, int nWords, int fComp0, int fComp1 )
{
    int w;
    if ( fComp0 && fComp1 )
        for ( w = 0; w < nWords; w++ )
            pSim[w] = ~(pSim0[w] | pSim1[w]);
    else if ( fComp0 )
        for ( w = 0; w < nWords; w++ )
            pSim[w] = ~pSim0[w] & pSim1[w];
    else if ( fComp1 )
        for ( w = 0; w < nWords; w++ )
            pSim[w] = pSim0[w] & ~pSim1[w];
    else
        for ( w = 0; w < nWords; w++ )
            pSim[w] = pSim0[w] & pSim1[w];
}

static inline void Ssc_SimDup( word * pSim, word * pSim0, int nWords, int fComp0 )
{
    int w;
    if ( fComp0 )
        for ( w = 0; w < nWords; w++ )
            pSim[w] = ~pSim0[w];
    else
        for ( w = 0; w < nWords; w++ )
            pSim[w] = pSim0[w];
}

static inline void Ssc_SimConst( word * pSim, int nWords, int fComp0 )
{
    int w;
    if ( fComp0 )
        for ( w = 0; w < nWords; w++ )
            pSim[w] = ~(word)0;
    else
        for ( w = 0; w < nWords; w++ )
            pSim[w] = 0;
}

static inline void Ssc_SimOr( word * pSim, word * pSim0, int nWords, int fComp0 )
{
    int w;
    if ( fComp0 )
        for ( w = 0; w < nWords; w++ )
            pSim[w] |= ~pSim0[w];
    else
        for ( w = 0; w < nWords; w++ )
            pSim[w] |= pSim0[w];
}

static inline int Ssc_SimFindBitWord( word t )
{
    int n = 0;
    if ( t == 0 ) return -1;
    if ( (t & 0x00000000FFFFFFFF) == 0 ) { n += 32; t >>= 32; }
    if ( (t & 0x000000000000FFFF) == 0 ) { n += 16; t >>= 16; }
    if ( (t & 0x00000000000000FF) == 0 ) { n +=  8; t >>=  8; }
    if ( (t & 0x000000000000000F) == 0 ) { n +=  4; t >>=  4; }
    if ( (t & 0x0000000000000003) == 0 ) { n +=  2; t >>=  2; }
    if ( (t & 0x0000000000000001) == 0 ) { n++; }
    return n;
}
static inline int Ssc_SimFindBit( word * pSim, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        if ( pSim[w] )
            return 64*w + Ssc_SimFindBitWord(pSim[w]);
    return -1;
}


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vec_WrdDoubleSimInfo( Vec_Wrd_t * p, int nObjs )
{
    word * pArray = ABC_CALLOC( word, 2 * Vec_WrdSize(p) );
    int i, nWords = Vec_WrdSize(p) / nObjs;
    assert( Vec_WrdSize(p) % nObjs == 0 );
    for ( i = 0; i < nObjs; i++ )
        memcpy( pArray + 2*i*nWords, p->pArray + i*nWords, sizeof(word) * nWords );
    ABC_FREE( p->pArray ); p->pArray = pArray;
    p->nSize = p->nCap = 2*nWords*nObjs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssc_GiaResetPiPattern( Gia_Man_t * p, int nWords )
{
    p->iPatsPi = 0;
    if ( p->vSimsPi == NULL )
        p->vSimsPi = Vec_WrdStart(0);
    Vec_WrdFill( p->vSimsPi, nWords * Gia_ManPiNum(p), 0 );
    assert( nWords == Gia_ObjSimWords( p ) );
}
void Ssc_GiaRandomPiPattern( Gia_Man_t * p, int nWords, Vec_Int_t * vPivot )
{
    word * pSimPi;
    int i, w;
    Ssc_GiaResetPiPattern( p, nWords );
    pSimPi = Gia_ObjSimPi( p, 0 );
    for ( i = 0; i < Gia_ManPiNum(p); i++, pSimPi += nWords )
    {
        pSimPi[0] = vPivot ? Ssc_Random1(Vec_IntEntry(vPivot, i)) : Ssc_Random2();
        for ( w = 1; w < nWords; w++ )
            pSimPi[w] = Ssc_Random();
//        if ( i < 10 )
//            Extra_PrintBinary( stdout, (unsigned *)pSimPi, 64 ), printf( "\n" );
    }
}
void Ssc_GiaSavePiPattern( Gia_Man_t * p, Vec_Int_t * vPat )
{
    word * pSimPi;
    int i;
    assert( Vec_IntSize(vPat) == Gia_ManPiNum(p) );
    if ( p->iPatsPi == 64 * Gia_ObjSimWords(p) )
        Vec_WrdDoubleSimInfo( p->vSimsPi, Gia_ManPiNum(p) );
    assert( p->iPatsPi < 64 * Gia_ObjSimWords(p) );
    pSimPi = Gia_ObjSimPi( p, 0 );
    for ( i = 0; i < Gia_ManPiNum(p); i++, pSimPi += Gia_ObjSimWords(p) )
        if ( Vec_IntEntry(vPat, i) )
            Abc_InfoSetBit( (unsigned *)pSimPi, p->iPatsPi );
    p->iPatsPi++;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssc_GiaResetSimInfo( Gia_Man_t * p )
{
    assert( Vec_WrdSize(p->vSimsPi) % Gia_ManPiNum(p) == 0 );
    if ( p->vSims == NULL )
        p->vSims = Vec_WrdAlloc(0);
    Vec_WrdFill( p->vSims, Gia_ObjSimWords(p) * Gia_ManObjNum(p), 0 );
}
void Ssc_GiaSimRound( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    word * pSim, * pSim0, * pSim1;
    int i, nWords = Gia_ObjSimWords(p);
    Ssc_GiaResetSimInfo( p );
    assert( nWords == Vec_WrdSize(p->vSims) / Gia_ManObjNum(p) );
    // constant node
    Ssc_SimConst( Gia_ObjSim(p, 0), nWords, 0 );
    // primary inputs
    pSim = Gia_ObjSim( p, 1 );
    pSim0 = Gia_ObjSimPi( p, 0 );
    Gia_ManForEachPi( p, pObj, i )
    {
        assert( pSim == Gia_ObjSimObj( p, pObj ) );
        Ssc_SimDup( pSim, pSim0, nWords, 0 );
        pSim += nWords;
        pSim0 += nWords;
    }
    // intermediate nodes
    pSim = Gia_ObjSim( p, 1+Gia_ManPiNum(p) );
    Gia_ManForEachAnd( p, pObj, i )
    {
        assert( pSim == Gia_ObjSim( p, i ) );
        pSim0 = pSim - pObj->iDiff0 * nWords;
        pSim1 = pSim - pObj->iDiff1 * nWords;
        Ssc_SimAnd( pSim, pSim0, pSim1, nWords, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj) );
        pSim += nWords;
    }
    // primary outputs
    pSim = Gia_ObjSim( p, Gia_ManObjNum(p) - Gia_ManPoNum(p) );
    Gia_ManForEachPo( p, pObj, i )
    {
        assert( pSim == Gia_ObjSimObj( p, pObj ) );
        pSim0 = pSim - pObj->iDiff0 * nWords;
        Ssc_SimDup( pSim, pSim0, nWords, Gia_ObjFaninC0(pObj) );
        pSim += nWords;
    }
}

/**Function*************************************************************

  Synopsis    [Returns one SAT assignment of the PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ssc_GiaGetOneSim( Gia_Man_t * p )
{
    Vec_Int_t * vInit;
    Gia_Obj_t * pObj;
    int i, iBit, nWords = Gia_ObjSimWords( p );
    word * pRes = ABC_FALLOC( word, nWords );
    Gia_ManForEachPo( p, pObj, i )
        Ssc_SimAnd( pRes, pRes, Gia_ObjSimObj(p, pObj), nWords, 0, 0 );
    iBit = Ssc_SimFindBit( pRes, nWords );
    ABC_FREE( pRes );
    if ( iBit == -1 )
        return NULL;
    vInit = Vec_IntAlloc( 100 );
    Gia_ManForEachPi( p, pObj, i )
        Vec_IntPush( vInit, Abc_InfoHasBit((unsigned *)Gia_ObjSimObj(p, pObj), iBit) );
    return vInit;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ssc_GiaFindPivotSim( Gia_Man_t * p )
{
    Vec_Int_t * vInit;
    Ssc_GiaRandomPiPattern( p, 1, NULL );
    Ssc_GiaSimRound( p );
    vInit = Ssc_GiaGetOneSim( p );
    return vInit;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

