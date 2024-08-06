/**CFile****************************************************************

  FileName    [giaMulFind.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Multiplier detection.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaMulFind.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManMulFindOverlap( Vec_Int_t * p1, Vec_Int_t * p2 )
{
    int i, k, ObjI, ObjK, Counter = 0;
    Vec_IntForEachEntry( p1, ObjI, i )
    Vec_IntForEachEntry( p2, ObjK, k )
        if ( ObjI == ObjK )
            Counter++;
    return Counter;
}
void Gia_ManMulFindAssignGroup( Vec_Int_t * vTemp, int iGroup, Vec_Int_t * vMap )
{
    int k, Obj;
    Vec_IntForEachEntry( vTemp, Obj, k ) {
        //assert( Vec_IntEntry(vMap, Obj) == -1 || Vec_IntEntry(vMap, Obj) == iGroup );
        Vec_IntWriteEntry(vMap, Obj, iGroup);
    }
    Vec_IntPush( vTemp, iGroup );    
}
Vec_Int_t * Gia_ManMulFindGroups( Vec_Wec_t * p, int nObjs, int fUseMap )
{
    Vec_Int_t * vIndex = Vec_IntAlloc( 100 ), * vTemp;
    Vec_Int_t * vMap = Vec_IntStartFull( nObjs ); int i, Counter, nGroups = 0;
    Vec_Int_t * vUngrouped = Vec_IntStartNatural( Vec_WecSize(p) );
    while ( Vec_IntSize(vUngrouped) ) {
        int k, Obj, Item = Vec_IntPop(vUngrouped);
        vTemp = Vec_WecEntry(p, Item);
        Gia_ManMulFindAssignGroup( vTemp, nGroups, vMap );
        int fChanges = 1;
        while ( fChanges ) {
            fChanges = 0;            
            Vec_IntForEachEntry( vUngrouped, Item, i ) {
                vTemp = Vec_WecEntry(p, Item);
                Counter = 0;
                Vec_IntForEachEntry( vTemp, Obj, k )
                    if ( Vec_IntEntry(vMap, Obj) >= 0 )
                        Counter++;
                if ( Counter < 1 )
                    continue;
                Gia_ManMulFindAssignGroup( vTemp, nGroups, vMap );
                Vec_IntDrop( vUngrouped, i-- );
                fChanges = 1;
            }
        }
        nGroups++;
    }
    Vec_IntFree( vUngrouped );
    Vec_IntFree( vMap );
    if ( fUseMap )
        Vec_WecForEachLevel( p, vTemp, i )
            Vec_IntPushTwo( vTemp, i, Vec_IntPop(vTemp) );            
    Vec_WecSortByLastInt( p, 0 );
    Counter = 0;
    Vec_IntPush( vIndex, 0 );
    Vec_WecForEachLevel( p, vTemp, i )
        if ( Vec_IntPop(vTemp) != Counter )
            Vec_IntPush( vIndex, i ), Counter++;
    Vec_IntPush( vIndex, Vec_WecSize(p) );
    assert( Vec_WecSize(p) == 0 || Vec_IntSize(vIndex) == nGroups + 1 );
    return vIndex;
}
Vec_Wec_t * Gia_ManMulFindXors( Gia_Man_t * p, Vec_Wec_t * vCuts3, int fVerbose )
{
    Vec_Wec_t * vXors    = Vec_WecAlloc( 10 ); 
    Vec_Int_t * vIndex   = Gia_ManMulFindGroups( vCuts3, Gia_ManObjNum(p), 0 );
    Vec_Int_t * vAll     = Vec_IntAlloc( 100 );
    Vec_Bit_t * vSigs[2] = { Vec_BitStart(Gia_ManObjNum(p)), Vec_BitStart(Gia_ManObjNum(p)) };
    Vec_Int_t * vTemp; int g, c, k, Obj, Start;
    Vec_IntForEachEntryStop( vIndex, Start, g, Vec_IntSize(vIndex)-1 ) {
        Vec_WecForEachLevelStartStop( vCuts3, vTemp, c, Start, Vec_IntEntry(vIndex, g+1) )
            Vec_IntForEachEntry( vTemp, Obj, k )
                if ( !Vec_BitEntry(vSigs[k==0], Obj) ) {
                    Vec_BitWriteEntry( vSigs[k==0], Obj, 1 );
                    Vec_IntPush( vAll, Obj );
                }
        Vec_Int_t * vIns  = Vec_WecPushLevel( vXors );
        Vec_Int_t * vOuts = Vec_WecPushLevel( vXors );        
        Vec_IntForEachEntry( vAll, Obj, k ) {
            if ( Vec_BitEntry(vSigs[0], Obj) && !Vec_BitEntry(vSigs[1], Obj) )
                Vec_IntPush( vIns, Obj );
            if ( !Vec_BitEntry(vSigs[0], Obj) && Vec_BitEntry(vSigs[1], Obj) )
                Vec_IntPush( vOuts, Obj );
            Vec_BitWriteEntry( vSigs[0], Obj, 0 );
            Vec_BitWriteEntry( vSigs[1], Obj, 0 );
        }
        Vec_IntClear( vAll );
    }
    return vXors; 
}
Vec_Int_t * Gia_ManFindMulDetectOrder( Vec_Wec_t * vAll, int iStart, int iStop )
{
    Vec_Int_t * vOrder = Vec_IntAlloc( iStop - iStart );
    Vec_Int_t * vUsed = Vec_IntStart( iStop ), * vTemp;
    int i, nMatches = 0, iNext = -1;
    Vec_WecForEachLevelStartStop( vAll, vTemp, i, iStart, iStop )
        if ( Vec_IntSize(vTemp) == 2 )
            nMatches++, iNext = i;
    if ( nMatches == 1 ) {
        while ( Vec_IntSize(vOrder) < iStop - iStart ) {
            Vec_IntPush( vOrder, iNext );
            Vec_IntWriteEntry( vUsed, iNext, 1 );
            nMatches = 0;
            Vec_WecForEachLevelStartStop( vAll, vTemp, i, iStart, iStop ) {
                if ( Vec_IntEntry(vUsed, i) )
                    continue;
                Vec_Int_t * vLast = Vec_WecEntry(vAll, Vec_IntEntryLast(vOrder));
                if ( Gia_ManMulFindOverlap(vTemp, vLast) == Vec_IntSize(vLast) && Vec_IntSize(vTemp) == Vec_IntSize(vLast) + 2 )
                    nMatches++, iNext = i;
            }
            if ( nMatches != 1 )
                break;
        }
    }
    Vec_IntFree( vUsed );
    if ( Vec_IntSize(vOrder) == 0 )
        Vec_IntFreeP( &vOrder );
    return vOrder;
}
Vec_Wec_t * Gia_ManMulFindAInputs( Gia_Man_t * p, Vec_Wec_t * vXors, int fVerbose )
{
    Vec_Wec_t * vRes = Vec_WecAlloc( 10 ); 
    Vec_Wec_t * vAll = Vec_WecAlloc( Vec_WecSize(vXors)/2 );
    Gia_Obj_t * pObj; Vec_Int_t * vIns, * vOuts, * vTemp, * vIndex, * vOrder; int i, k, g, Start, Entry, Entry0, Entry1;
    Gia_ManCreateRefs( p );
    Vec_WecForEachLevelDouble( vXors, vIns, vOuts, i ) {
        vTemp = Vec_WecPushLevel( vAll );
        Gia_ManForEachObjVec( vIns, p, pObj, k )
            if ( Gia_ObjIsAnd(pObj) 
                 && !Gia_ObjFaninC0(pObj) && Gia_ObjRefNum(p, Gia_ObjFanin0(pObj)) >= 4 
                 && !Gia_ObjFaninC1(pObj) && Gia_ObjRefNum(p, Gia_ObjFanin1(pObj)) >= 4 )
                Vec_IntPushTwo( vTemp, Gia_ObjFaninId0p(p, pObj), Gia_ObjFaninId1p(p, pObj) );
        if ( Vec_IntSize(vTemp) == 0 )
            Vec_WecShrink(vAll, Vec_WecSize(vAll)-1);
    }
    vIndex = Gia_ManMulFindGroups( vAll, Gia_ManObjNum(p), 0 );
    Vec_IntForEachEntryStop( vIndex, Start, g, Vec_IntSize(vIndex)-1 ) {
        vOrder = Gia_ManFindMulDetectOrder( vAll, Start, Vec_IntEntry(vIndex, g+1) );
        if ( vOrder == NULL )
            continue;
        Vec_Int_t * vIn0 = Vec_WecPushLevel( vRes );
        Vec_Int_t * vIn1 = Vec_WecPushLevel( vRes );
        Vec_Int_t * vOut = Vec_WecPushLevel( vRes );
        vTemp = Vec_WecEntry( vAll, Vec_IntEntry(vOrder, 0) );
        assert( Vec_IntSize(vTemp) == 2 );
        Vec_IntPush( vIn0, Vec_IntEntry(vTemp, 0) );
        Vec_IntPush( vIn1, Vec_IntEntry(vTemp, 1) );        
        Vec_IntForEachEntryStart( vOrder, Entry, i, 1 ) {
            vTemp = Vec_WecEntry( vAll, Entry );
            Vec_IntForEachEntryDouble( vTemp, Entry0, Entry1, k ) {
                if ( Vec_IntFind(vIn0, Entry0) >= 0 && Vec_IntFind(vIn1, Entry1) == -1 )
                    Vec_IntPush( vIn1, Entry1 );
                else if ( Vec_IntFind(vIn0, Entry0) == -1 && Vec_IntFind(vIn1, Entry1) >= 0 )
                    Vec_IntPush( vIn0, Entry0 );
                else 
                    assert( (Vec_IntFind(vIn0, Entry0) >= 0 && Vec_IntFind(vIn1, Entry1) >= 0) ||
                            (Vec_IntFind(vIn0, Entry1) >= 0 && Vec_IntFind(vIn1, Entry0) >= 0) );
            }
        }
        Vec_IntReverseOrder( vIn0 );
        Vec_IntReverseOrder( vIn1 );
        vOut = NULL;
    }
    Vec_IntFree( vIndex );
    Vec_WecFree( vAll );
    return vRes;    
}
Vec_Wec_t * Gia_ManMulFindBInputs( Gia_Man_t * p, Vec_Wec_t * vCuts4, Vec_Wec_t * vCuts5, int fVerbose )
{
    Vec_Wec_t * vRes = Vec_WecAlloc( 10 );  Vec_Int_t * vTemp; int g, c, k, Obj, Start;
    Vec_Int_t * vIndex = Gia_ManMulFindGroups( vCuts4, Gia_ManObjNum(p), 0 );
    Vec_IntForEachEntryStop( vIndex, Start, g, Vec_IntSize(vIndex)-1 ) {
        Vec_Int_t * vAll = Vec_IntAlloc ( 100 );
        Vec_WecForEachLevelStartStop( vCuts4, vTemp, c, Start, Vec_IntEntry(vIndex, g+1) )
            Vec_IntForEachEntryStart( vTemp, Obj, k, 1 )
                Vec_IntPush( vAll, Obj );
        Vec_IntUniqify( vAll );
        int GroupSize = Vec_IntEntry(vIndex, g+1) - Start;
        Vec_Int_t * vCnt = Vec_IntStart( Vec_IntSize(vAll) );
        Vec_WecForEachLevelStartStop( vCuts4, vTemp, c, Start, Vec_IntEntry(vIndex, g+1) )
            Vec_IntForEachEntryStart( vTemp, Obj, k, 1 )
                Vec_IntAddToEntry( vCnt, Vec_IntFind(vAll, Obj), 1 );
        if ( Vec_IntCountEntry(vCnt, 1) != 2 || Vec_IntCountEntry(vCnt, 2) != GroupSize-1 || Vec_IntCountEntry(vCnt, GroupSize) != 2 ) {
            printf( "Detection of group %d failed.\n", g );
            continue;
        }
        Vec_Int_t * vIn1 = Vec_WecPushLevel( vRes );
        Vec_Int_t * vIn2 = Vec_WecPushLevel( vRes );
        Vec_Int_t * vOut = Vec_WecPushLevel( vRes );
        Vec_IntForEachEntry( vAll, Obj, k )
            if ( Vec_IntEntry(vCnt, k) <= 2 )
                Vec_IntPush( vIn1, Obj );
            else 
                Vec_IntPush( vIn2, Obj );
        Vec_IntSort( vIn1, 0 );
        Vec_IntSort( vIn2, 0 );
        // TODO: check chain in[i] -> in[i+1]
        Vec_WecForEachLevel( vCuts5, vTemp, c ) {
            Vec_IntShift( vTemp, 1 );
            if ( Gia_ManMulFindOverlap(vTemp, vIn1) >= 2 )
                Vec_IntForEachEntryStart( vTemp, Obj, k, 1 )
                    if ( Vec_IntFind(vIn1, Obj) == -1 ) {
                        Vec_IntPushUnique(vIn2, Obj);
                    }
            Vec_IntShift( vTemp, -1 );
        }
        Vec_IntSort( vIn2, 0 );
        vOut = NULL;
    }
    Vec_IntFree( vIndex );
    return vRes;    
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManMulFindTfo( Gia_Man_t * p, Vec_Int_t * vIn0, Vec_Int_t * vIn1 )
{
    Vec_Int_t * vTfo = Vec_IntAlloc( 100 );
    Gia_Obj_t * pObj; int i, Obj;
    Gia_ManIncrementTravId( p );
    Vec_IntForEachEntry( vIn0, Obj, i )
        Gia_ObjSetTravIdCurrentId( p, Obj );
    Vec_IntForEachEntry( vIn1, Obj, i )
        Gia_ObjSetTravIdCurrentId( p, Obj );
    Gia_ManForEachAnd( p, pObj, i ) {
        if ( Gia_ObjIsTravIdCurrentId(p, i) )
            continue;
        if ( Gia_ObjIsTravIdCurrentId(p, Gia_ObjFaninId0(pObj, i)) && Gia_ObjIsTravIdCurrentId(p, Gia_ObjFaninId1(pObj, i)) )
            Gia_ObjSetTravIdCurrentId( p, i ), Vec_IntPush( vTfo, i );
    }
    return vTfo;
}
Vec_Wrd_t * Gia_ManMulFindSimCone( Gia_Man_t * p, Vec_Int_t * vIn0, Vec_Int_t * vIn1, Vec_Wrd_t * vSim0, Vec_Wrd_t * vSim1, Vec_Int_t * vTfo )
{
    Vec_Wrd_t * vRes = Vec_WrdAlloc( Vec_IntSize(vTfo) );
    Vec_Wrd_t * vSims = Vec_WrdStart( Gia_ManObjNum(p) );
    Gia_Obj_t * pObj; int i, Obj;
    Vec_IntForEachEntry( vIn0, Obj, i )
        Vec_WrdWriteEntry( vSims, Obj, Vec_WrdEntry(vSim0, i) );
    Vec_IntForEachEntry( vIn1, Obj, i )
        Vec_WrdWriteEntry( vSims, Obj, Vec_WrdEntry(vSim1, i) );
    Gia_ManForEachObjVec( vTfo, p, pObj, i ) {
        word Sim0 = Vec_WrdEntry(vSims, Gia_ObjFaninId0p(p, pObj) );
        word Sim1 = Vec_WrdEntry(vSims, Gia_ObjFaninId1p(p, pObj) );
        Vec_WrdWriteEntry( vSims, Gia_ObjId(p, pObj), (Gia_ObjFaninC0(pObj) ? ~Sim0 : Sim0) & (Gia_ObjFaninC1(pObj) ? ~Sim1 : Sim1) );
    }
    Vec_IntForEachEntry( vTfo, Obj, i )
        Vec_WrdPush( vRes, Vec_WrdEntry(vSims, Obj) );
    Vec_WrdFree( vSims );
    return vRes;        
}
int Gia_ManMulFindGetArg( Vec_Wrd_t * vSim, int i, int fSigned )
{
    int w, Res = 0; word Word = 0;
    Vec_WrdForEachEntry( vSim, Word, w )
        if ( (Word >> i) & 1 )
            Res |= (1 << w);
    if ( fSigned && ((Word >> i) & 1) )
        Res |= ~0 << Vec_WrdSize(vSim);
    return Res;
}
void Gia_ManMulFindSetArg( Vec_Wrd_t * vSim, int i, int iNum )
{
    int w;  word * pWords = Vec_WrdArray(vSim);
    for ( w = 0; w < Vec_WrdSize(vSim); w++ )
        if ( (iNum >> w) & 1 )
            pWords[w] |= (word)1 << i;
}
Vec_Wrd_t * Gia_ManMulFindSim( Vec_Wrd_t * vSim0, Vec_Wrd_t * vSim1, int fSigned )
{
    assert( Vec_WrdSize(vSim0) + Vec_WrdSize(vSim1) <= 30 );
    Vec_Wrd_t * vRes = Vec_WrdStart( Vec_WrdSize(vSim0) + Vec_WrdSize(vSim1) );
    for ( int i = 0; i < 64; i++ )
    {
        int a = Gia_ManMulFindGetArg( vSim0, i, fSigned );
        int b = Gia_ManMulFindGetArg( vSim1, i, fSigned );
        Gia_ManMulFindSetArg( vRes, i, a * b );
    }
    return vRes;
}
void Gia_ManMulFindOutputs( Gia_Man_t * p, Vec_Wec_t * vTerms, int fVerbose )
{
    for ( int m = 0; m < Vec_WecSize(vTerms)/3; m++ ) {
        Vec_Int_t * vIn0 = Vec_WecEntry(vTerms, 3*m+0);
        Vec_Int_t * vIn1 = Vec_WecEntry(vTerms, 3*m+1);
        Vec_Int_t * vOut = Vec_WecEntry(vTerms, 3*m+2);
        Vec_Wrd_t * vSim0 = Vec_WrdStartRandom( Vec_IntSize(vIn0) );
        Vec_Wrd_t * vSim1 = Vec_WrdStartRandom( Vec_IntSize(vIn1) );
        Vec_Wrd_t * vSimU = Gia_ManMulFindSim( vSim0, vSim1, 0 );
        Vec_Wrd_t * vSimS = Gia_ManMulFindSim( vSim0, vSim1, 1 );
        Vec_Int_t * vTfo  = Gia_ManMulFindTfo( p, vIn0, vIn1 );
        Vec_Wrd_t * vSims = Gia_ManMulFindSimCone( p, vIn0, vIn1, vSim0, vSim1, vTfo );
        word Word; int w, iPlace;
        assert( Vec_IntSize(vOut) == 0 );
        Vec_WrdForEachEntry( vSimU, Word, w ) {
            if ( (iPlace = Vec_WrdFind(vSims, Word)) >= 0 )
                Vec_IntPush( vOut, Abc_Var2Lit(Vec_IntEntry(vTfo, iPlace), 0) );
            else if ( (iPlace = Vec_WrdFind(vSims, ~Word)) >= 0 )
                Vec_IntPush( vOut, Abc_Var2Lit(Vec_IntEntry(vTfo, iPlace), 1) );
            else
                break;                             
        }
        if ( w == Vec_WrdSize(vSimU) )
            Vec_IntPush(vOut, 0);
        else
            Vec_IntClear(vOut);
        if ( Vec_IntSize(vOut) == 0 )
        {
            Vec_IntClear(vOut);
            Vec_WrdForEachEntry( vSimS, Word, w ) {
                if ( (iPlace = Vec_WrdFind(vSims, Word)) >= 0 )
                    Vec_IntPush( vOut, Abc_Var2Lit(Vec_IntEntry(vTfo, iPlace), 0) );
                else if ( (iPlace = Vec_WrdFind(vSims, ~Word)) >= 0 )
                    Vec_IntPush( vOut, Abc_Var2Lit(Vec_IntEntry(vTfo, iPlace), 1) );
                else
                    break;                             
            }
            if ( w == Vec_WrdSize(vSimS) )
                Vec_IntPush(vOut, 1);
            else
                Vec_IntClear(vOut);
        }
        Vec_WrdFree( vSim0 );
        Vec_WrdFree( vSim1 );
        Vec_WrdFree( vSimU );
        Vec_WrdFree( vSimS );
        Vec_WrdFree( vSims );
        Vec_IntFree( vTfo );
        if ( Vec_IntSize(vOut) )
            continue;
        Vec_IntClear(vIn0);
        Vec_IntClear(vIn1);
    }
    Vec_WecRemoveEmpty( vTerms );
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Gia_ManMulFindCuts( Gia_Man_t * p, int nCutNum, int fVerbose )
{
    extern Vec_Mem_t * Dau_CollectNpnFunctions( word * p, int nVars, int fVerbose );
    extern Vec_Ptr_t * Gia_ManMatchCutsArray( Vec_Ptr_t * vTtMems, Gia_Man_t * pGia, int nCutSize, int nCutNum, int fVerbose );
    word pTruths[3] = { ABC_CONST(0x6969696969696969), ABC_CONST(0x35C035C035C035C0), ABC_CONST(0xF335ACC0F335ACC0) };
    Vec_Ptr_t * vTtMems = Vec_PtrAlloc( 3 ); Vec_Mem_t * vTtMem; int i;
    for ( i = 0; i < 3; i++ )
        Vec_PtrPush( vTtMems, Dau_CollectNpnFunctions( pTruths+i, i+3, fVerbose ) );
    Vec_Ptr_t * vAll = Gia_ManMatchCutsArray( vTtMems, p, 5, nCutNum, fVerbose );
    Vec_PtrForEachEntry( Vec_Mem_t *, vTtMems, vTtMem, i )
        Vec_MemHashFree( vTtMem ), Vec_MemFree( vTtMem );
    Vec_PtrFree( vTtMems );
    return vAll;
}
Vec_Wec_t * Gia_ManMulFindA( Gia_Man_t * p, Vec_Wec_t * vCuts3, int fVerbose )
{
    Vec_Wec_t * vXors = Gia_ManMulFindXors( p, vCuts3, fVerbose );
    Vec_Wec_t * vTerms = Gia_ManMulFindAInputs( p, vXors, fVerbose );
    if ( Vec_WecSize(vTerms) )
        Gia_ManMulFindOutputs( p, vTerms, fVerbose );          
    Vec_WecFree( vXors );
    return vTerms;    
}
Vec_Wec_t * Gia_ManMulFindB( Gia_Man_t * p, Vec_Wec_t * vCuts4, Vec_Wec_t * vCuts5, int fVerbose )
{
    Vec_Wec_t * vTerms = Vec_WecAlloc( 12 );
    if ( Vec_WecSize(vCuts4) && Vec_WecSize(vCuts5) )
        vTerms = Gia_ManMulFindBInputs( p, vCuts4, vCuts5, fVerbose );
    if ( Vec_WecSize(vTerms) )
        Gia_ManMulFindOutputs( p, vTerms, fVerbose );
    return vTerms;
}
void Gia_ManMulFindPrintSet( Vec_Int_t * vSet, int fLit, int fSkipLast )
{
    int i, Temp, Limit = Vec_IntSize(vSet) - fSkipLast;
    printf( "{" );
    Vec_IntForEachEntryStop( vSet, Temp, i, Limit )
        printf( "%s%d%s", (fLit & Abc_LitIsCompl(Temp)) ? "~":"", fLit ? Abc_Lit2Var(Temp) : Temp, i < Limit-1 ? " ":"" );
    printf( "}" );
}
void Gia_ManMulFindPrintOne( Vec_Wec_t * vTerms, int m, int fBooth )
{
    Vec_Int_t * vIn0 = Vec_WecEntry(vTerms, 3*m+0);
    Vec_Int_t * vIn1 = Vec_WecEntry(vTerms, 3*m+1);
    Vec_Int_t * vOut = Vec_WecEntry(vTerms, 3*m+2);
    printf( "%sooth %ssigned : ", fBooth ? "B" : "Non-b", Vec_IntEntryLast(vOut) ? "" : "un" );
    Gia_ManMulFindPrintSet( vIn0, 0, 0 );
    printf( " * " );
    Gia_ManMulFindPrintSet( vIn1, 0, 0 );
    printf( " = " );
    Gia_ManMulFindPrintSet( vOut, 1, 1 );
    printf( "\n" );
}
void Gia_ManMulFind( Gia_Man_t * p, int nCutNum, int fVerbose )
{
    Vec_Ptr_t * vAll   = Gia_ManMulFindCuts( p, nCutNum, fVerbose ); int m;
    Vec_Wec_t * vCuts3 = (Vec_Wec_t *)Vec_PtrEntry(vAll, 0);
    Vec_Wec_t * vCuts4 = (Vec_Wec_t *)Vec_PtrEntry(vAll, 1);
    Vec_Wec_t * vCuts5 = (Vec_Wec_t *)Vec_PtrEntry(vAll, 2);
    Vec_Wec_t * vTermsB = Gia_ManMulFindB( p, vCuts4, vCuts5, fVerbose );
    Vec_Wec_t * vTermsA = Gia_ManMulFindA( p, vCuts3, fVerbose ); 
    printf( "Detected %d booth and %d non-booth multipliers.\n", Vec_WecSize(vTermsB)/3, Vec_WecSize(vTermsA)/3 );
    for ( m = 0; m < Vec_WecSize(vTermsA)/3; m++ )
        Gia_ManMulFindPrintOne( vTermsA, m, 0 );
    for ( m = 0; m < Vec_WecSize(vTermsB)/3; m++ )
        Gia_ManMulFindPrintOne( vTermsB, m, 1 );
    Vec_WecFree( vTermsB );
    Vec_WecFree( vTermsA );
    Vec_WecFree( vCuts3 );
    Vec_WecFree( vCuts4 );
    Vec_WecFree( vCuts5 );
    Vec_PtrFree( vAll );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

