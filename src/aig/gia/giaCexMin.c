/**CFile****************************************************************

  FileName    [giaCexMin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [CEX minimization.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCexMin.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int  Abc_InfoGet2Bits( Vec_Int_t * vData, int nWords, int iFrame, int iObj )
{
    unsigned * pInfo = (unsigned *)Vec_IntEntryP( vData, nWords * iFrame );
    return 3 & (pInfo[iObj >> 4] >> ((iObj & 15) << 1));
}
static inline void Abc_InfoSet2Bits( Vec_Int_t * vData, int nWords, int iFrame, int iObj, int Value )
{
    unsigned * pInfo = (unsigned *)Vec_IntEntryP( vData, nWords * iFrame );
    Value ^= (3 & (pInfo[iObj >> 4] >> ((iObj & 15) << 1)));
    pInfo[iObj >> 4] ^= (Value << ((iObj & 15) << 1));
}
static inline void Abc_InfoAdd2Bits( Vec_Int_t * vData, int nWords, int iFrame, int iObj, int Value )
{
    unsigned * pInfo = (unsigned *)Vec_IntEntryP( vData, nWords * iFrame );
    pInfo[iObj >> 4] |= (Value << ((iObj & 15) << 1));
}

static inline int  Gia_ManGetTwo( Gia_Man_t * p, int iFrame, int iObj )              { return Abc_InfoGet2Bits( p->vTruths, p->nTtWords, iFrame, iObj ); }
static inline void Gia_ManSetTwo( Gia_Man_t * p, int iFrame, int iObj, int Value )   { Abc_InfoSet2Bits( p->vTruths, p->nTtWords, iFrame, iObj, Value ); }
static inline void Gia_ManAddTwo( Gia_Man_t * p, int iFrame, int iObj, int Value )   { Abc_InfoAdd2Bits( p->vTruths, p->nTtWords, iFrame, iObj, Value ); }

/*
    For CEX minimization, all terminals (const0, PI, RO in frame0) have equal priority.
    For abstraction refinement, all terminals, except PPis, have higher priority.
*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Annotates the unrolling with CEX value/priority.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManAnnotateUnrolling( Gia_Man_t * p, Abc_Cex_t * pCex )
{
    Gia_Obj_t * pObj, * pObjRi, * pObjRo;
    int RetValue, f, k, Value0, Value1, iBit;
    // start storage for internal info
    assert( p->vTruths == NULL );
    p->nTtWords = Abc_BitWordNum( 2 * Gia_ManObjNum(p) );
    p->vTruths  = Vec_IntStart( (pCex->iFrame + 1) * p->nTtWords );
    // assign values to all objects (const0 and RO in frame0 are assigned 0)
    Gia_ManCleanMark0(p);
    for ( f = 0, iBit = pCex->nRegs; f <= pCex->iFrame; f++ )
    {
        Gia_ManForEachPi( p, pObj, k )
            if ( (pObj->fMark0 = Abc_InfoHasBit(pCex->pData, iBit++)) )
                Gia_ManAddTwo( p, f, Gia_ObjId(p, pObj), 1 );
        Gia_ManForEachAnd( p, pObj, k )
            if ( (pObj->fMark0 = (Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj)) & (Gia_ObjFanin1(pObj)->fMark0 ^ Gia_ObjFaninC1(pObj))) )
                Gia_ManAddTwo( p, f, k, 1 );
        Gia_ManForEachCo( p, pObj, k )
            if ( (pObj->fMark0 = Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj)) )
                Gia_ManAddTwo( p, f, Gia_ObjId(p, pObj), 1 );
        if ( f == pCex->iFrame )
            break;
        Gia_ManForEachRiRo( p, pObjRi, pObjRo, k )
            if ( (pObjRo->fMark0 = pObjRi->fMark0) )
                Gia_ManAddTwo( p, f+1, Gia_ObjId(p, pObjRo), 1 );
    }
    assert( iBit == pCex->nBits );
    // check the output value
    RetValue = Gia_ManPo(p, pCex->iPo)->fMark0;
    if ( RetValue != 1 )
        printf( "Counter-example is invalid.\n" );
    // assign justification to nodes
    Gia_ManCleanMark0(p);
    pObj = Gia_ManPo(p, pCex->iPo);
    pObj->fMark0 = 1;
    Gia_ManAddTwo( p, pCex->iFrame, Gia_ObjFaninId0(pObj, k), 2 );
    for ( f = pCex->iFrame; f >= 0; f-- )
    {
        // transfer to CO drivers
        Gia_ManForEachCo( p, pObj, k )
            if ( (Gia_ObjFanin0(pObj)->fMark0 = pObj->fMark0) )
                Gia_ManAddTwo( p, f, Gia_ObjFaninId0p(p, Gia_ObjFanin0(pObj)), 2 );
        // compute justification
        Gia_ManForEachAndReverse( p, pObj, k )
        {
            if ( !pObj->fMark0 ) continue;
            Value0 = (1 & Gia_ManGetTwo(p, f, Gia_ObjFaninId0(pObj, k))) ^ Gia_ObjFaninC0(pObj);
            Value1 = (1 & Gia_ManGetTwo(p, f, Gia_ObjFaninId1(pObj, k))) ^ Gia_ObjFaninC1(pObj);
            if ( Value0 == Value1 )
            {
                Gia_ObjFanin0(pObj)->fMark0 = Gia_ObjFanin1(pObj)->fMark0 = 1;
                Gia_ManAddTwo( p, f, Gia_ObjFaninId0(pObj, k), 2 );
                Gia_ManAddTwo( p, f, Gia_ObjFaninId1(pObj, k), 2 );
            }
            else if ( Value0 == 0 )
            {
                Gia_ObjFanin0(pObj)->fMark0 = 1;
                Gia_ManAddTwo( p, f, Gia_ObjFaninId0(pObj, k), 2 );
            }
            else if ( Value1 == 0 )
            {
                Gia_ObjFanin1(pObj)->fMark0 = 1;
                Gia_ManAddTwo( p, f, Gia_ObjFaninId1(pObj, k), 2 );
            }
            else assert( 0 );
        }
        if ( f == 0 )
            break;
        // clean COs
        Gia_ManForEachCo( p, pObj, k )
            pObj->fMark0 = 0;
        // transfer to RIs
        Gia_ManForEachRiRo( p, pObjRi, pObjRo, k )
            if ( (pObjRi->fMark0 = pObjRo->fMark0) )
                Gia_ManAddTwo( p, f-1, Gia_ObjId(p, pObjRi), 2 );
    }
    Gia_ManCleanMark0(p);
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Gia_ManCexMin( Gia_Man_t * p, Abc_Cex_t * pCex )
{
    assert( pCex->nPis == Gia_ManPiNum(p) );
    assert( pCex->nRegs == Gia_ManRegNum(p) );
    assert( pCex->iPo < Gia_ManPoNum(p) );

    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

