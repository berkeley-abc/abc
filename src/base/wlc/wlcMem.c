/**CFile****************************************************************

  FileName    [wlcMem.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Memory abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcMem.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"
#include "sat/bsat/satStore.h"
#include "proof/pdr/pdr.h"
#include "proof/pdr/pdrInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect memory nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Wlc_NtkCollectMemSizes( Wlc_Ntk_t * p )
{
    Wlc_Obj_t * pObj; int i;
    Vec_Int_t * vMemSizes = Vec_IntAlloc( 10 );
    Wlc_NtkForEachObj( p, pObj, i )
    {
        if ( Wlc_ObjType(pObj) != WLC_OBJ_WRITE && Wlc_ObjType(pObj) != WLC_OBJ_READ )
            continue;
        pObj = Wlc_ObjFanin( p, pObj, 0 );
        Vec_IntPushUnique( vMemSizes, Wlc_ObjRange(pObj) );
    }
    return vMemSizes;
}
Vec_Int_t * Wlc_NtkCollectMemory( Wlc_Ntk_t * p )
{
    Wlc_Obj_t * pObj; int i;
    Vec_Int_t * vMemSizes = Wlc_NtkCollectMemSizes( p );
    Vec_Int_t * vMemObjs = Vec_IntAlloc( 10 );
    Wlc_NtkForEachObj( p, pObj, i )
    {
        if ( Wlc_ObjType(pObj) == WLC_OBJ_WRITE || Wlc_ObjType(pObj) == WLC_OBJ_READ )
            Vec_IntPush( vMemObjs, i );
        else if ( Vec_IntFind(vMemSizes, Wlc_ObjRange(pObj)) >= 0 )
            Vec_IntPush( vMemObjs, i );
    }
    Vec_IntFree( vMemSizes );
    return vMemObjs;
}
void Wlc_NtkPrintMemory( Wlc_Ntk_t * p )
{
    Vec_Int_t * vMemory;
    vMemory = Wlc_NtkCollectMemSizes( p );
    Vec_IntSort( vMemory, 0 );
    Wlc_NtkPrintNodeArray( p, vMemory );
    Vec_IntFree( vMemory );
}

/**Function*************************************************************

  Synopsis    [Collect fanins of memory subsystem.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Wlc_NtkCollectMemFanins( Wlc_Ntk_t * p, Vec_Int_t * vMemObjs )
{
    Wlc_Obj_t * pObj; int i, k, iFanin;
    Vec_Int_t * vMemFanins = Vec_IntAlloc( 100 );
    Wlc_NtkForEachObjVec( vMemObjs, p, pObj, i )
    {
        if ( Wlc_ObjType(pObj) == WLC_OBJ_MUX )
            Vec_IntPush( vMemFanins, Wlc_ObjFaninId0(pObj) );
        else if ( Wlc_ObjType(pObj) == WLC_OBJ_READ || Wlc_ObjType(pObj) == WLC_OBJ_WRITE )
        {
            Wlc_ObjForEachFanin( pObj, iFanin, k )
                if ( k > 0 )
                    Vec_IntPush( vMemFanins, iFanin );
        }
    }
    return vMemFanins;
}

/**Function*************************************************************

  Synopsis    [Abstract memory nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Wlc_CountDcs( char * pInit )
{
    int Count = 0;
    for ( ; *pInit; pInit++ )
        Count += (*pInit == 'x' || *pInit == 'X');
    return Count;
}
int Wlc_NtkDupOneObject( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p, Wlc_Obj_t * pObj, int TypeNew, Vec_Int_t * vFanins )
{
    unsigned Type = pObj->Type;
    int iObjNew, nFanins = Wlc_ObjFaninNum(pObj);
    pObj->Type = TypeNew;
    pObj->nFanins = 0;
    iObjNew = Wlc_ObjDup( pNew, p, Wlc_ObjId(p, pObj), vFanins );
    pObj->Type = Type;
    pObj->nFanins = (unsigned)nFanins;
    if ( TypeNew == WLC_OBJ_FO )
        Vec_IntPush( pNew->vInits, -Wlc_ObjRange(pObj) );
    return iObjNew;
}
void Wlc_NtkDupOneBuffer( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p, Wlc_Obj_t * pObj, Vec_Int_t * vFanins, int fIsFi )
{
    int iObj = Wlc_ObjAlloc( pNew, WLC_OBJ_BUF, pObj->Signed, pObj->End, pObj->Beg );
    Wlc_Obj_t * pObjNew = Wlc_NtkObj( pNew, iObj );
    Vec_IntFill( vFanins, 1, Wlc_ObjCopy(p, Wlc_ObjId(p, pObj)) );
    Wlc_ObjAddFanins( pNew, pObjNew, vFanins );
    Wlc_ObjSetCo( pNew, pObjNew, fIsFi );
}

void Wlc_NtkAbsAddToNodeFrames( Vec_Int_t * vNodeFrames, Vec_Int_t * vLevel ) 
{
    int i, Entry;
    Vec_IntForEachEntry( vLevel, Entry, i )
        Vec_IntPushUnique( vNodeFrames, Entry );
    Vec_IntSort( vNodeFrames, 0 );
}
Vec_Int_t * Wlc_NtkAbsCreateFlopOutputs( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p, Vec_Int_t * vNodeFrames, Vec_Int_t * vFanins ) 
{
    Vec_Int_t * vNewObjs = Vec_IntAlloc( 2*Vec_IntSize(vNodeFrames) );
    Wlc_Obj_t * pObj, * pFanin = NULL;
    int i, Entry, iObj, iFrame;
    Vec_IntForEachEntry( vNodeFrames, Entry, i )
    {
        iObj   = Entry >> 10;
        iFrame = Entry & 0x3FF;
        pObj   = Wlc_NtkObj( p, iObj );
        // address
        if ( Wlc_ObjType(pObj) == WLC_OBJ_MUX )
            pFanin = Wlc_ObjFanin0(p, pObj);
        else if ( Wlc_ObjType(pObj) == WLC_OBJ_READ || Wlc_ObjType(pObj) == WLC_OBJ_WRITE )
            pFanin = Wlc_ObjFanin1(p, pObj);
        else assert( 0 );
        Vec_IntPush( vNewObjs, Wlc_NtkDupOneObject(pNew, p, pFanin, WLC_OBJ_FO, vFanins) );
        // data
        if ( Wlc_ObjType(pObj) == WLC_OBJ_MUX )
            pFanin = NULL;
        else if ( Wlc_ObjType(pObj) == WLC_OBJ_READ )
            pFanin = pObj;
        else if ( Wlc_ObjType(pObj) == WLC_OBJ_WRITE )
            pFanin = Wlc_ObjFanin2(p, pObj);
        else assert( 0 );
        Vec_IntPush( vNewObjs, pFanin ? Wlc_NtkDupOneObject(pNew, p, pFanin, WLC_OBJ_FO, vFanins) : 0 );
    }
    assert( Vec_IntSize(vNewObjs) == Vec_IntCap(vNewObjs) );
    return vNewObjs;
}
Wlc_Obj_t * Wlc_NtkAbsCreateLogic( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p, Vec_Int_t * vNodeFrames, Vec_Int_t * vFanins, Vec_Int_t * vNewObjs, Vec_Wec_t * vConstrs ) 
{
    Vec_Int_t * vLevel; 
    Vec_Int_t * vBitConstr = Vec_IntAlloc( 100 );
    Vec_Int_t * vLevConstr = Vec_IntAlloc( 100 );
    Wlc_Obj_t * pAddrs[2], * pDatas[2], * pCond, * pConstr = NULL;
    int i, k, Entry, Index[2];
    Vec_WecForEachLevel( vConstrs, vLevel, i )
    {
        assert( Vec_IntSize(vLevel) >= 2 );
        Vec_IntClear( vLevConstr );

        Index[0] = Vec_IntFind( vNodeFrames, Vec_IntEntry(vLevel, 0) );
        Index[1] = Vec_IntFind( vNodeFrames, Vec_IntEntryLast(vLevel) );
        assert( Index[0] >= 0 && Index[1] >= 0 );

        pAddrs[0] = Wlc_NtkObj( pNew, Vec_IntEntry(vNewObjs, 2*Index[0]) );
        pAddrs[1] = Wlc_NtkObj( pNew, Vec_IntEntry(vNewObjs, 2*Index[1]) );

        pDatas[0] = Wlc_NtkObj( pNew, Vec_IntEntry(vNewObjs, 2*Index[0]+1) );
        pDatas[1] = Wlc_NtkObj( pNew, Vec_IntEntry(vNewObjs, 2*Index[1]+1) );

        // equal addresses
        pCond = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_COMP_EQU, 0, 0, 0));
        Vec_IntFillTwo( vFanins, 2, Wlc_ObjId(pNew, pAddrs[0]), Wlc_ObjId(pNew, pAddrs[1]) );
        Wlc_ObjAddFanins( pNew, pCond, vFanins );
        Vec_IntPush( vLevConstr, Wlc_ObjId(pNew, pCond) );

        // different datas
        pCond = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_COMP_NOTEQU, 0, 0, 0));
        Vec_IntFillTwo( vFanins, 2, Wlc_ObjId(pNew, pDatas[0]), Wlc_ObjId(pNew, pDatas[1]) );
        Wlc_ObjAddFanins( pNew, pCond, vFanins );
        Vec_IntPush( vLevConstr, Wlc_ObjId(pNew, pCond) );

        Vec_IntForEachEntryStartStop( vLevel, Entry, k, 0, Vec_IntSize(vLevel)-1 )
        {
            Index[0]  = Vec_IntFind( vNodeFrames, Entry );            
            pAddrs[0] = Wlc_NtkObj( pNew, Vec_IntEntry(vNewObjs, 2*Index[0]) );
            if ( Vec_IntEntry(vNewObjs, 2*Index[0]+1) == 0 ) // MUX
                Vec_IntPush( vLevConstr, Wlc_ObjId(pNew, pAddrs[0]) );
            else // different addresses
            {
                assert( Wlc_ObjRange(pAddrs[0]) == Wlc_ObjRange(pAddrs[1]) );
                pCond = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_COMP_NOTEQU, 0, 0, 0));
                Vec_IntFillTwo( vFanins, 2, Wlc_ObjId(pNew, pAddrs[0]), Wlc_ObjId(pNew, pAddrs[1]) );
                Wlc_ObjAddFanins( pNew, pCond, vFanins );
                Vec_IntPush( vLevConstr, Wlc_ObjId(pNew, pCond) );
            }
        }

        // create last output
        pConstr = Wlc_NtkObj( pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_BIT_CONCAT, 0, Vec_IntSize(vLevConstr)-1, 0) );
        Wlc_ObjAddFanins( pNew, pConstr, vLevConstr );
        Vec_IntFill( vFanins, 1, Wlc_ObjId(pNew, pConstr) );
        pConstr = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_REDUCT_AND, 0, 0, 0));
        Wlc_ObjAddFanins( pNew, pConstr, vFanins );

        // save the result
        Vec_IntPush( vBitConstr, Wlc_ObjId(pNew, pConstr) );
    }
    if ( Vec_IntSize(vBitConstr) > 0 )
    {
        // create last output
        pConstr = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_BIT_CONCAT, 0, Vec_IntSize(vBitConstr)-1, 0));
        Wlc_ObjAddFanins( pNew, pConstr, vBitConstr );
        // create last output
        Vec_IntFill( vFanins, 1, Wlc_ObjId(pNew, pConstr) );
        pConstr = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_REDUCT_OR, 0, 0, 0));
        Wlc_ObjAddFanins( pNew, pConstr, vFanins );
    }
    else
    {
        pConstr = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_CONST, 0, 0, 0));
        Vec_IntFill( vFanins, 1, 0 ); // const0 - always true
        Wlc_ObjAddFanins( pNew, pConstr, vFanins );
    }
    // cleanup
    Vec_IntFree( vBitConstr );
    Vec_IntFree( vLevConstr );
    return pConstr;
}
void Wlc_NtkAbsCreateFlopInputs( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p, Vec_Int_t * vNodeFrames, Vec_Int_t * vFanins, Vec_Int_t * vNewObjs, Wlc_Obj_t * pCounter, int AdderBits, Vec_Bit_t * vMuxVal ) 
{
    Wlc_Obj_t * pObj, * pFanin, * pFlop, * pCond, * pMux, * pConst;
    int i, n, Entry, iObj, iFrame, Index;
    Vec_IntForEachEntry( vNodeFrames, Entry, i )
    {
        iObj   = Entry >> 10;
        iFrame = Entry & 0x3FF;
        pObj   = Wlc_NtkObj( p, iObj );
        Index  = Vec_IntFind( vNodeFrames, Entry );
        for ( n = 0; n < 2; n++ ) // n=0 -- address   n=1 -- data
        {
            pFlop = Wlc_NtkObj( pNew, Vec_IntEntry(vNewObjs, 2*Index+n) );
            if ( Wlc_ObjType(pObj) == WLC_OBJ_WRITE )
                pFanin = Wlc_ObjCopyObj( pNew, p, n ? Wlc_ObjFanin2(pNew, pObj) : Wlc_ObjFanin1(pNew, pObj) );
            else if ( Wlc_ObjType(pObj) == WLC_OBJ_READ )
                pFanin = n ? Wlc_NtkObj(pNew, Wlc_ObjCopy(p, iObj)) : Wlc_ObjCopyObj( pNew, p, Wlc_ObjFanin1(pNew, pObj) );
            else if ( Wlc_ObjType(pObj) == WLC_OBJ_MUX )
            {
                if ( n ) continue;
                pFanin = Wlc_ObjCopyObj( pNew, p, Wlc_ObjFanin0(p, pObj) );
                if ( Vec_BitEntry( vMuxVal, iFrame * Wlc_NtkObjNum(p) + iObj ) )
                {
                    Vec_IntFill( vFanins, 1, Wlc_ObjId(pNew, pFanin) );
                    pFanin = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_BIT_NOT, 0, 0, 0));
                    Wlc_ObjAddFanins( pNew, pFanin, vFanins );
                }
            }
            else assert( 0 );
            assert( Wlc_ObjRange(pFlop) == Wlc_ObjRange(pFanin) );
            // create constant
            pConst = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_CONST, 0, AdderBits-1, 0));
            Vec_IntFill( vFanins, 1, iFrame );
            Wlc_ObjAddFanins( pNew, pConst, vFanins );
            // create equality
            pCond = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_COMP_EQU, 0, 0, 0));
            Vec_IntFillTwo( vFanins, 1, Wlc_ObjId(pNew, pConst), Wlc_ObjId(pNew, pCounter) );
            Wlc_ObjAddFanins( pNew, pCond, vFanins );
            // create MUX
            pMux = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_MUX, 0, Wlc_ObjRange(pFlop)-1, 0));
            Vec_IntClear( vFanins );
            Vec_IntPush( vFanins, Wlc_ObjId(pNew, pCond) );
            Vec_IntPush( vFanins, Wlc_ObjId(pNew, pFlop) );
            Vec_IntPush( vFanins, Wlc_ObjId(pNew, pFanin) );
            Wlc_ObjAddFanins( pNew, pMux, vFanins );
            Wlc_ObjSetCo( pNew, pMux, 1 );
        }
    }
}
Wlc_Ntk_t * Wlc_NtkAbstractMemory( Wlc_Ntk_t * p, Vec_Int_t * vMemObjs, Vec_Int_t * vMemFanins, int * piFirstMemPi, int * piFirstCi, int * piFirstMemCi, Vec_Wec_t * vConstrs, Vec_Int_t * vNodeFrames, Vec_Bit_t * vMuxVal )
{
    Wlc_Ntk_t * pNew;
    Wlc_Obj_t * pObj, * pCounter, * pConst, * pAdder, * pConstr = NULL;
    Vec_Int_t * vNewObjs = NULL;
    Vec_Int_t * vFanins  = Vec_IntAlloc( 100 );
    int i, Po0, Po1, AdderBits = 20, nBits = 0;

    // mark memory nodes
    Wlc_NtkCleanMarks( p );
    Wlc_NtkForEachObjVec( vMemObjs, p, pObj, i )
        pObj->Mark = 1;

    // start new network
    Wlc_NtkCleanCopy( p );
    pNew = Wlc_NtkAlloc( p->pName, p->nObjsAlloc + 1000 );
    pNew->fSmtLib = p->fSmtLib;
    pNew->vInits = Vec_IntAlloc( 100 );

    // duplicate PIs
    Wlc_NtkForEachPi( p, pObj, i )
        if ( !pObj->Mark )
        {
            Wlc_ObjDup( pNew, p, Wlc_ObjId(p, pObj), vFanins );
            nBits += Wlc_ObjRange(pObj);
        }

    // create new PIs
    *piFirstMemPi = nBits;
    Wlc_NtkForEachObjVec( vMemObjs, p, pObj, i )
        if ( Wlc_ObjType(pObj) == WLC_OBJ_READ )
        {
            int iObjNew = Wlc_NtkDupOneObject( pNew, p, pObj, WLC_OBJ_PI, vFanins );
            nBits += Wlc_ObjRange(pObj);
        }

    // duplicate flop outputs
    *piFirstCi = nBits;
    Wlc_NtkForEachCi( p, pObj, i )
        if ( !Wlc_ObjIsPi(pObj) && !pObj->Mark )
        {
            Wlc_ObjDup( pNew, p, Wlc_ObjId(p, pObj), vFanins );
            Vec_IntPush( pNew->vInits, Vec_IntEntry(p->vInits, i-Wlc_NtkPiNum(p)) );
            nBits += Wlc_ObjRange(pObj);
        }

    // create flop for time-frame counter 
    pCounter = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_FO, 0, AdderBits-1, 0));
    Vec_IntPush( pNew->vInits, -AdderBits );
    nBits += AdderBits;

    // create flops for memory objects
    *piFirstMemCi = nBits;
    if ( vMemFanins )
        Wlc_NtkForEachObjVec( vMemFanins, p, pObj, i )
            Wlc_NtkDupOneObject( pNew, p, pObj, WLC_OBJ_FO, vFanins );

    // create flops for constraint objects
    if ( vConstrs )
        vNewObjs = Wlc_NtkAbsCreateFlopOutputs( pNew, p, vNodeFrames, vFanins );

    // duplicate objects
    Wlc_NtkForEachObj( p, pObj, i )
        if ( !Wlc_ObjIsCi(pObj) && !pObj->Mark )
            Wlc_ObjDup( pNew, p, Wlc_ObjId(p, pObj), vFanins );

    // create logic nodes for constraints
    if ( vConstrs )
        pConstr = Wlc_NtkAbsCreateLogic( pNew, p, vNodeFrames, vFanins, vNewObjs, vConstrs );

    if ( Vec_IntSize(&p->vPoPairs) )
    {
        // create miter for the PO pairs
        Vec_IntForEachEntryDouble( &p->vPoPairs, Po0, Po1, i )
        {
            int iCopy0 = Wlc_ObjCopy(p, Wlc_ObjId(p, Wlc_NtkPo(p, Po0)));
            int iCopy1 = Wlc_ObjCopy(p, Wlc_ObjId(p, Wlc_NtkPo(p, Po1)));
            int iObj = Wlc_ObjAlloc( pNew, WLC_OBJ_COMP_NOTEQU, 0, 0, 0 );
            Wlc_Obj_t * pObjNew = Wlc_NtkObj( pNew, iObj );
            Vec_IntFillTwo( vFanins, 1, iCopy0, iCopy1 );
            Wlc_ObjAddFanins( pNew, pObjNew, vFanins );
            Wlc_ObjSetCo( pNew, pObjNew, 0 );
        }
        printf( "Created %d miter outputs.\n", Wlc_NtkPoNum(pNew) );
        Wlc_NtkForEachCo( p, pObj, i )
            if ( pObj->fIsFi )
                Wlc_ObjSetCo( pNew, Wlc_ObjCopyObj(pNew, p, pObj), pObj->fIsFi );

        // create constraint output
        if ( vConstrs )
            Wlc_ObjSetCo( pNew, pConstr, 0 );
    }
    else
    {
        // duplicate POs
        Wlc_NtkForEachPo( p, pObj, i )
            if ( !pObj->Mark )
                Wlc_ObjSetCo( pNew, Wlc_ObjCopyObj(pNew, p, pObj), pObj->fIsFi );
        // create constraint output
        if ( pConstr )
            Wlc_ObjSetCo( pNew, pConstr, 0 );
        // duplicate FIs
        Wlc_NtkForEachCo( p, pObj, i )
            if ( !Wlc_ObjIsPo(pObj) && !pObj->Mark )
                Wlc_ObjSetCo( pNew, Wlc_ObjCopyObj(pNew, p, pObj), pObj->fIsFi );
    }

    // create time-frame counter
    pConst = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_CONST, 0, AdderBits-1, 0));
    Vec_IntFill( vFanins, 1, 1 );
    Wlc_ObjAddFanins( pNew, pConst, vFanins );

    pAdder = Wlc_NtkObj(pNew, Wlc_ObjAlloc(pNew, WLC_OBJ_ARI_ADD, 0, AdderBits-1, 0));
    Vec_IntFillTwo( vFanins, 2, Wlc_ObjId(pNew, pCounter), Wlc_ObjId(pNew, pConst) );
    Wlc_ObjAddFanins( pNew, pAdder, vFanins );
    Wlc_ObjSetCo( pNew, pAdder, 1 );

    // create new flop inputs
    if ( vMemFanins )
        Wlc_NtkForEachObjVec( vMemFanins, p, pObj, i )
            Wlc_NtkDupOneBuffer( pNew, p, pObj, vFanins, 1 );

    // create flop inputs for constraint objects
    if ( vConstrs )
        Wlc_NtkAbsCreateFlopInputs( pNew, p, vNodeFrames, vFanins, vNewObjs, pCounter, AdderBits, vMuxVal );

    // append init states
    pNew->pInits = Wlc_PrsConvertInitValues( pNew );
    if ( p->pSpec )
        pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    //Wlc_NtkTransferNames( pNew, p );
    Vec_IntFree( vFanins );
    Vec_IntFreeP( &vNewObjs );
    Wlc_NtkCleanMarks( p );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives values of memory subsystem objects under the CEX.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Wlc_NtkDeriveFirstTotal( Wlc_Ntk_t * p, Vec_Int_t * vMemObjs, Vec_Int_t * vMemFanins, int iFirstMemPi, int iFirstMemCi )
{
    Vec_Int_t * vFirstTotal = Vec_IntStart( 3 * Vec_IntSize(vMemObjs) ); // contains pairs of (first CO bit: range) for each input/output of a node
    Wlc_Obj_t * pObj, * pFanin; int i, k, iFanin, nMemFanins = 0;
    Wlc_NtkForEachObjVec( vMemObjs, p, pObj, i )
    {
        if ( Wlc_ObjType(pObj) == WLC_OBJ_MUX )
        {
            //Vec_IntPush( vMemFanins, Wlc_ObjFaninId0(pObj) );
            pFanin = Wlc_ObjFanin0(p, pObj);
            assert( Wlc_ObjRange(pFanin) == 1 );
            Vec_IntWriteEntry( vFirstTotal, 3*i, (iFirstMemCi << 10) | Wlc_ObjRange(pFanin) );
            iFirstMemCi += Wlc_ObjRange(pFanin);
            nMemFanins++;
        }
        else if ( Wlc_ObjType(pObj) == WLC_OBJ_READ || Wlc_ObjType(pObj) == WLC_OBJ_WRITE )
        {
            Wlc_ObjForEachFanin( pObj, iFanin, k )
                if ( k > 0 )
                {
                    //Vec_IntPush( vMemFanins, iFanin );
                    pFanin = Wlc_NtkObj(p, iFanin);
                    Vec_IntWriteEntry( vFirstTotal, 3*i + k, (iFirstMemCi << 10) | Wlc_ObjRange(pFanin) );
                    iFirstMemCi += Wlc_ObjRange(pFanin);
                    nMemFanins++;
                }
            if ( Wlc_ObjType(pObj) == WLC_OBJ_READ )
            {
                Vec_IntWriteEntry( vFirstTotal, 3*i + 2, (iFirstMemPi << 10) | Wlc_ObjRange(pObj) );
                iFirstMemPi += Wlc_ObjRange(pObj);
            }
        }
    }
    assert( nMemFanins == Vec_IntSize(vMemFanins) );
//    Vec_IntForEachEntry( vFirstTotal, iFanin, i )
//        printf( "%16s : %d(%d)\n", Wlc_ObjName(p, Vec_IntEntry(vMemObjs, i/3)), iFanin >> 10, iFanin & 0x3FF );
    return vFirstTotal;
}
int Wlc_NtkCexResim( Gia_Man_t * pAbs, Abc_Cex_t * p, Vec_Int_t * vFirstTotal, int iBit, Vec_Wrd_t * vRes, int iFrame )
{
    Gia_Obj_t * pObj, * pObjRi, * pObjRo; 
    int k, b, Entry, First, nBits; word Value;
    // assuming that flop inputs have been assigned from previous timeframe
    // assign primary inputs
    Gia_ManForEachPi( pAbs, pObj, k )
        pObj->fMark0 = Abc_InfoHasBit(p->pData, iBit++);
    // simulate
    Gia_ManForEachAnd( pAbs, pObj, k )
        pObj->fMark0 = (Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj)) & 
                       (Gia_ObjFanin1(pObj)->fMark0 ^ Gia_ObjFaninC1(pObj));
    // transfer to combinational outputs
    Gia_ManForEachCo( pAbs, pObj, k )
        pObj->fMark0 = Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj);
    // transfer values to flop outputs
    Gia_ManForEachRiRo( pAbs, pObjRi, pObjRo, k )
        pObjRo->fMark0 = pObjRi->fMark0;
    // at this point PIs and FOs area assigned according to this time-frame
    // collect values
    Vec_IntForEachEntry( vFirstTotal, Entry, k )
    {
        if ( Entry == 0 )
        {
            Vec_WrdPush( vRes, ~(word)0 );
            continue;
        }
        First = Entry >> 10;
        assert( First < Gia_ManCiNum(pAbs) );
        nBits = Entry & 0x3FF;
        assert( nBits <= 64 );
        Value = 0;
        for ( b = 0; b < nBits; b++ )
            if ( Gia_ManCi(pAbs, First+b)->fMark0 )
                Value |= ((word)1) << b;
        Vec_WrdWriteEntry( vRes, Vec_IntSize(vFirstTotal)*iFrame + k, Value );
    }
    return iBit;
}
Vec_Wrd_t * Wlc_NtkConvertCex( Wlc_Ntk_t * p, Vec_Int_t * vFirstTotal, Gia_Man_t * pAbs, Abc_Cex_t * pCex )
{
    Vec_Wrd_t * vValues = Vec_WrdStartFull( Vec_IntSize(vFirstTotal) * (pCex->iFrame + 1) );
    int f, nBits = pCex->nRegs;
    Gia_ManCleanMark0(pAbs); // init FOs to zero
    for ( f = 0; f <= pCex->iFrame; f++ )
        nBits = Wlc_NtkCexResim( pAbs, pCex, vFirstTotal, nBits, vValues, f );
    return vValues;
}

/**Function*************************************************************

  Synopsis    [Derives refinement.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_NtkTrace_rec( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, int iFrame, Vec_Int_t * vMemObjs, Vec_Wrd_t * vValues, word ValueA, Vec_Int_t * vRes )
{
    int iObj = Wlc_ObjId(p, pObj);
    int iNum = Wlc_ObjCopy( p, iObj );
    assert( iObj == Vec_IntEntry(vMemObjs, iNum) );
    assert( iFrame >= 0 );
    if ( Wlc_ObjIsPi(pObj) ) 
        Vec_IntPush( vRes, (iObj << 10) | iFrame );
    else if ( Wlc_ObjIsCo(pObj) )
        Wlc_NtkTrace_rec( p, Wlc_ObjFo2Fi(p, pObj), iFrame - 1, vMemObjs, vValues, ValueA, vRes );
    else if ( Wlc_ObjType(pObj) == WLC_OBJ_BUF )
        Wlc_NtkTrace_rec( p, Wlc_ObjFanin0(p, pObj), iFrame, vMemObjs, vValues, ValueA, vRes );
    else if ( Wlc_ObjType(pObj) == WLC_OBJ_MUX )
    {
        int Index = 3*(iFrame*Vec_IntSize(vMemObjs) + iNum);
        Wlc_NtkTrace_rec( p, Vec_WrdEntry(vValues, Index) ? Wlc_ObjFanin2(p, pObj) : Wlc_ObjFanin1(p, pObj), iFrame, vMemObjs, vValues, ValueA, vRes );
        Vec_IntPush( vRes, (iObj << 10) | iFrame );
    }
    else if ( Wlc_ObjType(pObj) == WLC_OBJ_WRITE )
    {
        int Index = 3*(iFrame*Vec_IntSize(vMemObjs) + iNum);
        if ( Vec_WrdEntry(vValues, Index + 1) != ValueA ) // address 
            Wlc_NtkTrace_rec( p, Wlc_ObjFanin0(p, pObj), iFrame, vMemObjs, vValues, ValueA, vRes );
        Vec_IntPush( vRes, (iObj << 10) | iFrame );
    }
    else assert( 0 );
}
Vec_Int_t * Wlc_NtkTrace( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, int iFrame, Vec_Int_t * vMemObjs, Vec_Wrd_t * vValues )
{
    int iObj = Wlc_ObjId(p, pObj);
    int iNum = Wlc_ObjCopy( p, iObj );
    Vec_Int_t * vTrace = Vec_IntAlloc( 10 );
    assert( Wlc_ObjType(pObj) == WLC_OBJ_READ );
    assert( iObj == Vec_IntEntry(vMemObjs, iNum) );
    Wlc_NtkTrace_rec( p, Wlc_ObjFanin0(p, pObj), iFrame, vMemObjs, vValues, Vec_WrdEntry(vValues, 3*(iFrame*Vec_IntSize(vMemObjs) + iNum) + 1), vTrace );
    Vec_IntPush( vTrace, (iObj << 10) | iFrame );
    return vTrace;
}
int Wlc_NtkTraceCheckConfict( Wlc_Ntk_t * p, Vec_Int_t * vTrace, Vec_Int_t * vMemObjs, Vec_Wrd_t * vValues )
{
    Wlc_Obj_t * pObjLast, * pObjFirst; 
    int iFrmLast = Vec_IntEntryLast(vTrace) & 0x3FF;
    int iObjLast = Vec_IntEntryLast(vTrace) >> 10;
    int iNumLast = Wlc_ObjCopy( p, iObjLast );
    int iIndLast = 3*(iFrmLast*Vec_IntSize(vMemObjs) + iNumLast);
    int iFrmFirst = Vec_IntEntry(vTrace, 0) & 0x3FF;
    int iObjFirst = Vec_IntEntry(vTrace, 0) >> 10;
    int iNumFirst = Wlc_ObjCopy( p, iObjFirst );
    int iIndFirst = 3*(iFrmFirst*Vec_IntSize(vMemObjs) + iNumFirst);
    assert( Vec_IntSize(vTrace) >= 2 );
    assert( iObjLast  == Vec_IntEntry(vMemObjs, iNumLast) );
    assert( iObjFirst == Vec_IntEntry(vMemObjs, iNumFirst) );
    pObjLast  = Wlc_NtkObj(p, iObjLast);
    pObjFirst = Wlc_NtkObj(p, iObjFirst);
    assert( Wlc_ObjType(pObjLast) == WLC_OBJ_READ );
    assert( Wlc_ObjType(pObjFirst) == WLC_OBJ_WRITE || Wlc_ObjIsPi(pObjFirst) );
    if ( Wlc_ObjIsPi(pObjFirst) )
        return 0;
    assert( Vec_WrdEntry(vValues, iIndLast + 1) == Vec_WrdEntry(vValues, iIndFirst + 1) );
    return Vec_WrdEntry(vValues, iIndLast + 2) != Vec_WrdEntry(vValues, iIndFirst + 2); // diff data
}
Vec_Int_t * Wlc_NtkFindConflict( Wlc_Ntk_t * p, Vec_Int_t * vMemObjs, Vec_Wrd_t * vValues, int nFrames )
{
    Wlc_Obj_t * pObj; int i, f, Entry;
    Vec_Wec_t * vTraces = Vec_WecStart( 100 );
    Vec_Int_t * vTrace, * vTrace1, * vTrace2;
    assert( 3 * nFrames * Vec_IntSize(vMemObjs) == Vec_WrdSize(vValues) );
    for ( f = 0; f < nFrames; f++ )
    {
        Wlc_NtkForEachObjVec( vMemObjs, p, pObj, i )
        {
            if ( Wlc_ObjType(pObj) != WLC_OBJ_READ )
                continue;
            vTrace = Wlc_NtkTrace( p, pObj, nFrames, vMemObjs, vValues );
            if ( Wlc_NtkTraceCheckConfict( p, vTrace, vMemObjs, vValues ) )
            {
                Vec_WecFree( vTraces );
                return vTrace;
            }
            Vec_WecPushLevel( vTraces );
            Vec_IntAppend( Vec_WecEntryLast(vTraces), vTrace );
            Vec_IntFree( vTrace );
        }
    }
    // check if there are any common read addresses
    Vec_WecForEachLevel( vTraces, vTrace1, i )
    Vec_WecForEachLevelStop( vTraces, vTrace2, f, i )
        if ( Vec_IntEntry(vTrace1, 0) == Vec_IntEntry(vTrace2, 0) )
        {
            int iObj1 = Vec_IntEntryLast(vTrace1);
            int iNum1 = Wlc_ObjCopy( p, iObj1 );
            int iObj2 = Vec_IntEntryLast(vTrace2);
            int iNum2 = Wlc_ObjCopy( p, iObj2 );
            assert( iObj1 == Vec_IntEntry(vMemObjs, iNum1) );
            assert( iObj2 == Vec_IntEntry(vMemObjs, iNum2) );
            if ( Vec_WrdEntry(vValues, 3*iNum1 + 1) == Vec_WrdEntry(vValues, 3*iNum2 + 1) &&  // same address
                 Vec_WrdEntry(vValues, 3*iNum2 + 1) != Vec_WrdEntry(vValues, 3*iNum2 + 1) )   // different data
            {
                vTrace = Vec_IntAlloc( 100 );
                Vec_IntPush( vTrace, Vec_IntPop(vTrace1) );
                Vec_IntForEachEntry( vTrace1, Entry, i )
                    Vec_IntPushUnique( vTrace, Entry );
                Vec_IntForEachEntry( vTrace2, Entry, i )
                    Vec_IntPushUnique( vTrace, Entry );
                Vec_WecFree( vTraces );
                return vTrace;
            }
        }
    Vec_WecFree( vTraces );
    return NULL;
}
Vec_Bit_t * Wlc_NtkCollectMuxValues( Wlc_Ntk_t * p, Vec_Int_t * vMemObjs, Vec_Wrd_t * vValues, int nFrames )
{
    Vec_Bit_t * vBitValues = Vec_BitStart( nFrames * Wlc_NtkObjNum(p) );
    Wlc_Obj_t * pObj; int i, f;
    Wlc_NtkForEachObjVec( vMemObjs, p, pObj, i )
        if ( Wlc_ObjType(pObj) == WLC_OBJ_MUX )
            for ( f = 0; f < nFrames; f++ )
                if ( Vec_WrdEntry(vValues, 3*f*Vec_IntSize(vMemObjs) + i) )
                    Vec_BitWriteEntry( vBitValues, f*Wlc_NtkObjNum(p) + Wlc_ObjId(p, pObj), 1 );
    return vBitValues;
}

/**Function*************************************************************

  Synopsis    [Perform abstraction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Wlc_Ntk_t * Wlc_NtkMemAbstractTest( Wlc_Ntk_t * p )
{
    int iFirstMemPi, iFirstCi, iFirstMemCi, nDcBits;
    Vec_Int_t * vFirstTotal;
    Vec_Int_t * vMemObjs    = Wlc_NtkCollectMemory( p );
    Vec_Int_t * vMemFanins  = Wlc_NtkCollectMemFanins( p, vMemObjs );

    Vec_Wec_t * vRefines    = Vec_WecAlloc( 100 );
    Vec_Int_t * vNodeFrames = Vec_IntAlloc( 100 );
//    Wlc_Ntk_t * pNewFull    = Wlc_NtkAbstractMemory( p, vMemObjs, vMemFanins, &iFirstMemPi, &iFirstCi, &iFirstMemCi, NULL, NULL, NULL );
    Wlc_Ntk_t * pNewFull    = Wlc_NtkAbstractMemory( p, vMemObjs, NULL, &iFirstMemPi, &iFirstCi, &iFirstMemCi, vRefines, vNodeFrames, NULL );
    Vec_WecFree( vRefines );
    Vec_IntFree( vNodeFrames );

    nDcBits     = Wlc_CountDcs( pNewFull->pInits );
    vFirstTotal = Wlc_NtkDeriveFirstTotal( p, vMemObjs, vMemFanins, iFirstMemPi, nDcBits + iFirstMemCi );
    printf( "iFirstMemPi = %d  iFirstCi = %d  iFirstMemCi = %d  nDcBits = %d\n", iFirstMemPi, iFirstCi, iFirstMemCi, nDcBits );
    Vec_IntFreeP( &vMemObjs );
    Vec_IntFreeP( &vMemFanins );
    Vec_IntFreeP( &vFirstTotal );
    return pNewFull;
}

int Wlc_NtkMemAbstract( Wlc_Ntk_t * p, int nIterMax, int fPdrVerbose, int fVerbose )
{
    abctime clk = Abc_Clock();
    Wlc_Ntk_t * pNewFull, * pNew; Aig_Man_t * pAig;
    Gia_Man_t * pAbsFull, * pAbs, * pTemp;
    Abc_Cex_t * pCex = NULL;  Vec_Wrd_t * vValues = NULL; Vec_Bit_t * vMuxVal = NULL;
    Vec_Wec_t * vRefines = Vec_WecAlloc( 100 );
    Vec_Int_t * vNodeFrames = Vec_IntAlloc( 100 );
    Vec_Int_t * vMemObjs, * vMemFanins, * vFirstTotal, * vRefine; 
    int RetValue, iFirstMemPi, iFirstCi, iFirstMemCi, nDcBits, nIters;

    vMemObjs    = Wlc_NtkCollectMemory( p );
    vMemFanins  = Wlc_NtkCollectMemFanins( p, vMemObjs );
    pNewFull    = Wlc_NtkAbstractMemory( p, vMemObjs, vMemFanins, &iFirstMemPi, &iFirstCi, &iFirstMemCi, NULL, NULL, NULL );
    nDcBits     = Wlc_CountDcs( pNewFull->pInits );
    vFirstTotal = Wlc_NtkDeriveFirstTotal( p, vMemObjs, vMemFanins, iFirstMemPi, nDcBits + iFirstMemCi );

    pAbsFull    = Wlc_NtkBitBlast( pNewFull, NULL );
    assert( Gia_ManPiNum(pAbsFull) == iFirstCi + nDcBits );

    // perform abstraction
    for ( nIters = 1; nIters < 10000; nIters++ )
    {
        // set up parameters to run PDR
        Pdr_Par_t PdrPars, * pPdrPars = &PdrPars;
        Pdr_ManSetDefaultParams( pPdrPars );
        pPdrPars->fUseAbs    = 0;   // use 'pdr -t'  (on-the-fly abstraction)
        pPdrPars->fVerbose   = fVerbose;

        // derive specific abstraction
        pNew = Wlc_NtkAbstractMemory( p, vMemObjs, NULL, &iFirstMemPi, &iFirstCi, &iFirstMemCi, vRefines, vNodeFrames, vMuxVal );
        pAbs = Wlc_NtkBitBlast( pNew, NULL );
        Wlc_NtkFree( pNew );
        // simplify the AIG
        pAbs = Gia_ManSeqStructSweep( pTemp = pAbs, 1, 1, 0 );
        Gia_ManStop( pTemp );

        // try to prove abstracted GIA by converting it to AIG and calling PDR
        pAig = Gia_ManToAigSimple( pAbs );
        Gia_ManStop( pAbs );
        RetValue = Pdr_ManSolve( pAig, pPdrPars );
        pCex = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );

        // check if proved or undecided
        if ( pCex == NULL ) 
        {
            assert( RetValue );
            break;
        }

        // analyze counter-example
        Vec_BitFreeP( &vMuxVal );
        vValues = Wlc_NtkConvertCex( p, vFirstTotal, pAbs, pCex );
        vMuxVal = Wlc_NtkCollectMuxValues( p, vMemObjs, vValues, pCex->iFrame + 1 );
        vRefine = Wlc_NtkFindConflict( p, vMemObjs, vValues, pCex->iFrame + 1 );
        Vec_WrdFree( vValues );
        Abc_CexFree( pCex ); // return CEX in the future
        if ( vRefine == NULL )
            break;

        // save refinement for the future
        Vec_WecPushLevel( vRefines );
        Vec_IntAppend( Vec_WecEntryLast(vRefines), vRefine );
        Wlc_NtkAbsAddToNodeFrames( vNodeFrames, vRefine );
        Vec_IntFree( vRefine );
    }
    // cleanup
    Wlc_NtkFree( pNew );
    Vec_WecFree( vRefines );
    Vec_IntFreeP( &vMemObjs );
    Vec_IntFreeP( &vMemFanins );
    Vec_IntFreeP( &vFirstTotal );
    Vec_IntFreeP( &vNodeFrames );
    Vec_BitFreeP( &vMuxVal );

    // report the result
    if ( fVerbose )
        printf( "\n" );
    printf( "Abstraction " );
    if ( RetValue == 0 )
        printf( "resulted in a real CEX" );
    else if ( RetValue == 1 )
        printf( "is successfully proved" );
    else 
        printf( "timed out" );
    printf( " after %d iterations. ", nIters );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

