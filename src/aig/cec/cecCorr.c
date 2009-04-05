/**CFile****************************************************************

  FileName    [cecCorr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Latch/signal correspondence computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecCorr.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Gia_ManCorrSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the real value of the literal w/o spec reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_ManCorrSpecReal( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f )
{
    if ( Gia_ObjIsAnd(pObj) )
    {
        Gia_ManCorrSpecReduce_rec( pNew, p, Gia_ObjFanin0(pObj), f );
        Gia_ManCorrSpecReduce_rec( pNew, p, Gia_ObjFanin1(pObj), f );
        return Gia_ManHashAnd( pNew, Gia_ObjFanin0CopyF(p, f, pObj), Gia_ObjFanin1CopyF(p, f, pObj) );
    }
    assert( f && Gia_ObjIsRo(p, pObj) );
    pObj = Gia_ObjRoToRi( p, pObj );
    Gia_ManCorrSpecReduce_rec( pNew, p, Gia_ObjFanin0(pObj), f-1 );
    return Gia_ObjFanin0CopyF( p, f-1, pObj );
}

/**Function*************************************************************

  Synopsis    [Recursively performs speculative reduction for the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f )
{
    Gia_Obj_t * pRepr;
    int iLitNew;
    if ( ~Gia_ObjCopyF(p, f, pObj) )
        return;
    if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
    {
        Gia_ManCorrSpecReduce_rec( pNew, p, pRepr, f );
        iLitNew = Gia_LitNotCond( Gia_ObjCopyF(p, f, pRepr), Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
        Gia_ObjSetCopyF( p, f, pObj, iLitNew );
        return;
    }
    assert( Gia_ObjIsCand(pObj) );
    iLitNew = Gia_ManCorrSpecReal( pNew, p, pObj, f );
    Gia_ObjSetCopyF( p, f, pObj, iLitNew );
}

/**Function*************************************************************

  Synopsis    [Derives SRM for signal correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCorrSpecReduce( Gia_Man_t * p, int nFrames, int fScorr, Vec_Int_t ** pvOutputs, int fRings )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits;
    int f, i, iPrev, iObj, iPrevNew, iObjNew;
    assert( nFrames > 0 );
    assert( Gia_ManRegNum(p) > 0 );
    assert( p->pReprs != NULL );
    p->pCopies = ABC_FALLOC( int, (nFrames+fScorr)*Gia_ManObjNum(p) );
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( nFrames * Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ObjSetCopyF( p, 0, Gia_ManConst0(p), 0 );
    Gia_ManForEachRo( p, pObj, i )
        Gia_ObjSetCopyF( p, 0, pObj, Gia_ManAppendCi(pNew) );
    Gia_ManForEachRo( p, pObj, i )
        if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
            Gia_ObjSetCopyF( p, 0, pObj, Gia_ObjCopyF(p, 0, pRepr) );
    for ( f = 0; f < nFrames+fScorr; f++ )
    { 
        Gia_ObjSetCopyF( p, f, Gia_ManConst0(p), 0 );
        Gia_ManForEachPi( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManAppendCi(pNew) );
    }
    *pvOutputs = Vec_IntAlloc( 1000 );
    vXorLits = Vec_IntAlloc( 1000 );
    if ( fRings )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsConst( p, i ) )
            {
                iObjNew = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames );
                iObjNew = Gia_LitNotCond( iObjNew, Gia_ObjPhase(pObj) );
                if ( iObjNew != 0 )
                {
                    Vec_IntPush( *pvOutputs, 0 );
                    Vec_IntPush( *pvOutputs, i );
                    Vec_IntPush( vXorLits, iObjNew );
                }
            }
            else if ( Gia_ObjIsHead( p, i ) )
            {
                iPrev = i;
                Gia_ClassForEachObj1( p, i, iObj )
                {
                    iPrevNew = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iPrev), nFrames );
                    iObjNew  = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iObj), nFrames );
                    iPrevNew = Gia_LitNotCond( iPrevNew, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                    iObjNew  = Gia_LitNotCond( iObjNew,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
                    if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                    {
                        Vec_IntPush( *pvOutputs, iPrev );
                        Vec_IntPush( *pvOutputs, iObj );
                        Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Gia_LitNot(iObjNew)) );
                    }
                    iPrev = iObj;
                }
                iObj = i;
                iPrevNew = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iPrev), nFrames );
                iObjNew  = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iObj), nFrames );
                iPrevNew = Gia_LitNotCond( iPrevNew, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                iObjNew  = Gia_LitNotCond( iObjNew,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
                if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                {
                    Vec_IntPush( *pvOutputs, iPrev );
                    Vec_IntPush( *pvOutputs, iObj );
                    Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Gia_LitNot(iObjNew)) );
                }
            }
        }
    }
    else
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
            if ( pRepr == NULL )
                continue;
            iPrevNew = Gia_ObjIsConst(p, i)? 0 : Gia_ManCorrSpecReal( pNew, p, pRepr, nFrames );
            iObjNew  = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames );
            iObjNew  = Gia_LitNotCond( iObjNew, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pObj) );
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
            }
        }
    }
    Vec_IntForEachEntry( vXorLits, iObjNew, i )
        Gia_ManAppendCo( pNew, iObjNew );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
    ABC_FREE( p->pCopies );
//printf( "Before sweeping = %d\n", Gia_ManAndNum(pNew) );
    pNew = Gia_ManCleanup( pTemp = pNew );
//printf( "After sweeping = %d\n", Gia_ManAndNum(pNew) );
    Gia_ManStop( pTemp );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Initializes simulation info for lcorr/scorr counter-examples.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManStartSimInfo( Vec_Ptr_t * vInfo, int nFlops )
{
    unsigned * pInfo;
    int k, w, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    assert( nFlops <= Vec_PtrSize(vInfo) );
    for ( k = 0; k < nFlops; k++ )
    {
        pInfo = Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = 0;
    }
    for ( k = nFlops; k < Vec_PtrSize(vInfo); k++ )
    {
        pInfo = Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = Aig_ManRandom( 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Remaps simulation info from SRM to the original AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrRemapSimInfo( Gia_Man_t * p, Vec_Ptr_t * vInfo )
{
    Gia_Obj_t * pObj, * pRepr;
    unsigned * pInfoObj, * pInfoRepr;
    int i, w, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    Gia_ManForEachRo( p, pObj, i )
    {
        // skip ROs without representatives
        pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
        if ( pRepr == NULL || Gia_ObjFailed(p, Gia_ObjId(p,pObj)) )
            continue;
        pInfoObj = Vec_PtrEntry( vInfo, i );
        for ( w = 0; w < nWords; w++ )
            assert( pInfoObj[w] == 0 );
        // skip ROs with constant representatives
        if ( Gia_ObjIsConst0(pRepr) )
            continue;
        assert( Gia_ObjIsRo(p, pRepr) );
//        printf( "%d -> %d    ", i, Gia_ObjId(p, pRepr) );
        // transfer info from the representative
        pInfoRepr = Vec_PtrEntry( vInfo, Gia_ObjCioId(pRepr) - Gia_ManPiNum(p) );
        for ( w = 0; w < nWords; w++ )
            pInfoObj[w] = pInfoRepr[w];
    }
//    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Collects information about remapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManCorrCreateRemapping( Gia_Man_t * p )
{
    Vec_Int_t * vPairs;
    Gia_Obj_t * pObj, * pRepr;
    int i;
    vPairs = Vec_IntAlloc( 100 );
    Gia_ManForEachRo( p, pObj, i )
    {
        // skip ROs without representatives
        pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
        if ( pRepr == NULL || Gia_ObjIsConst0(pRepr) || Gia_ObjFailed(p, Gia_ObjId(p,pObj)) )
//        if ( pRepr == NULL || Gia_ObjIsConst0(pRepr) || Gia_ObjIsFailedPair(p, Gia_ObjId(p, pRepr), Gia_ObjId(p, pObj)) )
            continue;
        assert( Gia_ObjIsRo(p, pRepr) );
//        printf( "%d -> %d    ", Gia_ObjId(p,pObj), Gia_ObjId(p, pRepr) );
        // remember the pair
        Vec_IntPush( vPairs, Gia_ObjCioId(pRepr) - Gia_ManPiNum(p) );
        Vec_IntPush( vPairs, i );
    }
    return vPairs;
}

/**Function*************************************************************

  Synopsis    [Remaps simulation info from SRM to the original AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrPerformRemapping( Vec_Int_t * vPairs, Vec_Ptr_t * vInfo )
{
    unsigned * pInfoObj, * pInfoRepr;
    int w, i, iObj, iRepr, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    Vec_IntForEachEntry( vPairs, iRepr, i )
    {
        iObj = Vec_IntEntry( vPairs, ++i );
        pInfoObj = Vec_PtrEntry( vInfo, iObj );
        pInfoRepr = Vec_PtrEntry( vInfo, iRepr );
        for ( w = 0; w < nWords; w++ )
        {
            assert( pInfoObj[w] == 0 );
            pInfoObj[w] = pInfoRepr[w];
        }
    }
}

/**Function*************************************************************

  Synopsis    [Packs one counter-examples into the array of simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

*************************************`**********************************/
int Cec_ManLoadCounterExamplesTry( Vec_Ptr_t * vInfo, Vec_Ptr_t * vPres, int iBit, int * pLits, int nLits )
{
    unsigned * pInfo, * pPres;
    int i;
    for ( i = 0; i < nLits; i++ )
    {
        pInfo = Vec_PtrEntry(vInfo, Gia_Lit2Var(pLits[i]));
        pPres = Vec_PtrEntry(vPres, Gia_Lit2Var(pLits[i]));
        if ( Aig_InfoHasBit( pPres, iBit ) && 
             Aig_InfoHasBit( pInfo, iBit ) == Gia_LitIsCompl(pLits[i]) )
             return 0;
    }
    for ( i = 0; i < nLits; i++ )
    {
        pInfo = Vec_PtrEntry(vInfo, Gia_Lit2Var(pLits[i]));
        pPres = Vec_PtrEntry(vPres, Gia_Lit2Var(pLits[i]));
        Aig_InfoSetBit( pPres, iBit );
        if ( Aig_InfoHasBit( pInfo, iBit ) == Gia_LitIsCompl(pLits[i]) )
            Aig_InfoXorBit( pInfo, iBit );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs bitpacking of counter-examples.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLoadCounterExamples( Vec_Ptr_t * vInfo, Vec_Int_t * vCexStore, int iStart )
{ 
    Vec_Int_t * vPat;
    Vec_Ptr_t * vPres;
    int nWords = Vec_PtrReadWordsSimInfo(vInfo);
    int nBits = 32 * nWords; 
    int k, nSize, iBit = 1, kMax = 0;
    vPat  = Vec_IntAlloc( 100 );
    vPres = Vec_PtrAllocSimInfo( Vec_PtrSize(vInfo), nWords );
    Vec_PtrCleanSimInfo( vPres, 0, nWords );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        // skip the output number
        iStart++;
        // get the number of items
        nSize = Vec_IntEntry( vCexStore, iStart++ );
        if ( nSize <= 0 )
            continue;
        // extract pattern
        Vec_IntClear( vPat );
        for ( k = 0; k < nSize; k++ )
            Vec_IntPush( vPat, Vec_IntEntry( vCexStore, iStart++ ) );
        // add pattern to storage
        for ( k = 1; k < nBits; k++ )
            if ( Cec_ManLoadCounterExamplesTry( vInfo, vPres, k, (int *)Vec_IntArray(vPat), Vec_IntSize(vPat) ) )
                break;
        kMax = AIG_MAX( kMax, k );
        if ( k == nBits-1 )
            break;
    }
    Vec_PtrFree( vPres );
    Vec_IntFree( vPat );
    return iStart;
}

/**Function*************************************************************

  Synopsis    [Performs bitpacking of counter-examples.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLoadCounterExamples2( Vec_Ptr_t * vInfo, Vec_Int_t * vCexStore, int iStart )
{ 
    unsigned * pInfo;
    int nBits = 32 * Vec_PtrReadWordsSimInfo(vInfo); 
    int k, iLit, nLits, Out, iBit = 1;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        // skip the output number
//        iStart++;
        Out = Vec_IntEntry( vCexStore, iStart++ );
//        printf( "iBit = %d. Out = %d.\n", iBit, Out );
        // get the number of items
        nLits = Vec_IntEntry( vCexStore, iStart++ );
        if ( nLits <= 0 )
            continue;
        // add pattern to storage
        for ( k = 0; k < nLits; k++ )
        {
            iLit = Vec_IntEntry( vCexStore, iStart++ );
            pInfo = Vec_PtrEntry( vInfo, Gia_Lit2Var(iLit) );
            if ( Aig_InfoHasBit( pInfo, iBit ) == Gia_LitIsCompl(iLit) )
                Aig_InfoXorBit( pInfo, iBit );
        }
        if ( ++iBit == nBits )
            break;
    }
//    printf( "added %d bits\n", iBit-1 );
    return iStart;
}

/**Function*************************************************************

  Synopsis    [Resimulates counter-examples derived by the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManResimulateCounterExamples( Cec_ManSim_t * pSim, Vec_Int_t * vCexStore, int nFrames )
{ 
    Vec_Int_t * vPairs;
    Vec_Ptr_t * vSimInfo; 
    int RetValue = 0, iStart = 0;
    vPairs = Gia_ManCorrCreateRemapping( pSim->pAig );
    Gia_ManSetRefs( pSim->pAig );
//    pSim->pPars->nWords  = 63;
    pSim->pPars->nRounds = nFrames;
    vSimInfo = Vec_PtrAllocSimInfo( Gia_ManRegNum(pSim->pAig) + Gia_ManPiNum(pSim->pAig) * nFrames, pSim->pPars->nWords );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        Cec_ManStartSimInfo( vSimInfo, Gia_ManRegNum(pSim->pAig) );
        iStart = Cec_ManLoadCounterExamples( vSimInfo, vCexStore, iStart );
//        iStart = Cec_ManLoadCounterExamples2( vSimInfo, vCexStore, iStart );
//        Gia_ManCorrRemapSimInfo( pSim->pAig, vSimInfo );
        Gia_ManCorrPerformRemapping( vPairs, vSimInfo );
        RetValue |= Cec_ManSeqResimulate( pSim, vSimInfo );
//        Cec_ManSeqResimulateInfo( pSim->pAig, vSimInfo, NULL );
    }
//Gia_ManEquivPrintOne( pSim->pAig, 85, 0 );
    assert( iStart == Vec_IntSize(vCexStore) );
    Vec_PtrFree( vSimInfo );
    Vec_IntFree( vPairs );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Updates equivalence classes by marking those that timed out.]

  Description [Returns 1 if all ndoes are proved.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCheckRefinements( Gia_Man_t * p, Vec_Str_t * vStatus, Vec_Int_t * vOutputs, Cec_ManSim_t * pSim, int fRings )
{
    int i, status, iRepr, iObj;
    int Counter = 0;
    assert( 2 * Vec_StrSize(vStatus) == Vec_IntSize(vOutputs) );
    Vec_StrForEachEntry( vStatus, status, i )
    {
        iRepr = Vec_IntEntry( vOutputs, 2*i );
        iObj  = Vec_IntEntry( vOutputs, 2*i+1 );
        if ( status == 1 )
            continue;
        if ( status == 0 )
        {
            if ( Gia_ObjHasSameRepr(p, iRepr, iObj) )
                Counter++;
//            if ( Gia_ObjHasSameRepr(p, iRepr, iObj) )
//                printf( "Gia_ManCheckRefinements(): Disproved equivalence (%d,%d) is not refined!\n", iRepr, iObj );
//            if ( Gia_ObjHasSameRepr(p, iRepr, iObj) )
//                Cec_ManSimClassRemoveOne( pSim, iObj );
            continue;
        }
        if ( status == -1 )
        {
//            if ( !Gia_ObjFailed( p, iObj ) )
//                printf( "Gia_ManCheckRefinements(): Failed equivalence is not marked as failed!\n" );
//            Gia_ObjSetFailed( p, iRepr );
//            Gia_ObjSetFailed( p, iObj );        
//            if ( fRings )
//            Cec_ManSimClassRemoveOne( pSim, iRepr );
            Cec_ManSimClassRemoveOne( pSim, iObj );
            continue;
        }
    }
//    if ( Counter )
//    printf( "Gia_ManCheckRefinements(): Could not refine %d nodes.\n", Counter );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Marks all the nodes as proved.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetProvedNodes( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, nLits = 0;
    Gia_ManForEachObj1( p, pObj, i )
    {
        if ( Gia_ObjRepr(p, i) == GIA_VOID )
            continue;
        Gia_ObjSetProved( p, i );
        nLits++;
    }
//    printf( "Identified %d proved literals.\n", nLits );
}

/**Function*************************************************************

  Synopsis    [Prints statistics during solving.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManLCorrPrintStats( Gia_Man_t * p, Vec_Str_t * vStatus, int iIter, int Time )
{ 
    int nLits, CounterX = 0, Counter0 = 0, Counter = 0;
    int i, Entry, nProve = 0, nDispr = 0, nFail = 0;
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        if ( Gia_ObjIsNone(p, i) )
            CounterX++;
        else if ( Gia_ObjIsConst(p, i) )
            Counter0++;
        else if ( Gia_ObjIsHead(p, i) )
            Counter++;
    }
    CounterX -= Gia_ManCoNum(p);
    nLits = Gia_ManCiNum(p) + Gia_ManAndNum(p) - Counter - CounterX;
    printf( "%3d : c =%8d  cl =%7d  lit =%8d  ", iIter, Counter0, Counter, nLits );
    if ( vStatus )
    Vec_StrForEachEntry( vStatus, Entry, i )
    {
        if ( Entry == 1 )
            nProve++;
        else if ( Entry == 0 )
            nDispr++;
        else if ( Entry == -1 )
            nFail++;
    }
    printf( "p =%6d  d =%6d  f =%6d  ", nProve, nDispr, nFail );
    ABC_PRT( "T", Time );
}

/**Function*************************************************************

  Synopsis    [Top-level procedure for register correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManLSCorrespondence( Gia_Man_t * pAig, Cec_ParCor_t * pPars )
{  
    int nAddFrames = 1; // additional timeframes to simulate
    Vec_Str_t * vStatus;
    Vec_Int_t * vOutputs;
    Vec_Int_t * vCexStore;
    Gia_Man_t * pNew, * pTemp;
    Cec_ParSim_t ParsSim, * pParsSim = &ParsSim;
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Cec_ManSim_t * pSim;
    Gia_Man_t * pSrm;
    int r, RetValue;
    int clkSat = 0, clkSim = 0, clkSrm = 0, clkTotal = clock();
    int clk2, clk = clock();
    ABC_FREE( pAig->pReprs );
    ABC_FREE( pAig->pNexts );
    if ( Gia_ManRegNum(pAig) == 0 )
    {
        printf( "Cec_ManLatchCorrespondence(): Not a sequential AIG.\n" );
        return NULL;
    }
    Aig_ManRandom( 1 );
    // prepare simulation manager
    Cec_ManSimSetDefaultParams( pParsSim );
    pParsSim->nWords     = pPars->nWords;
    pParsSim->nRounds    = pPars->nRounds;
    pParsSim->fVerbose   = pPars->fVerbose;
    pParsSim->fLatchCorr = pPars->fLatchCorr;
    pParsSim->fSeqSimulate = 1;
    // create equivalence classes of registers
    pSim = Cec_ManSimStart( pAig, pParsSim );
    Cec_ManSimClassesPrepare( pSim );
    Cec_ManSimClassesRefine( pSim );
    // prepare SAT solving
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->nBTLimit = pPars->nBTLimit;
    pParsSat->fVerbose = pPars->fVerbose;
    if ( pPars->fVerbose )
    {
        printf( "Obj = %7d. And = %7d. Conf = %5d. Fr = %d. Lcorr = %d. Ring = %d. CSat = %d.\n",
            Gia_ManObjNum(pAig), Gia_ManAndNum(pAig), 
            pPars->nBTLimit, pPars->nFrames, pPars->fLatchCorr, pPars->fUseRings, pPars->fUseCSat );
        Cec_ManLCorrPrintStats( pAig, NULL, 0, clock() - clk );
    }
    // perform refinement of equivalence classes
    for ( r = 0; r < 100000; r++ )
    { 
        clk = clock();
        // perform speculative reduction
        clk2 = clock();
        pSrm = Gia_ManCorrSpecReduce( pAig, pPars->nFrames, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings );
        assert( Gia_ManRegNum(pSrm) == 0 && Gia_ManPiNum(pSrm) == Gia_ManRegNum(pAig)+(pPars->nFrames+!pPars->fLatchCorr)*Gia_ManPiNum(pAig) );
        clkSrm += clock() - clk2;
        if ( Gia_ManCoNum(pSrm) == 0 )
        {
            Vec_IntFree( vOutputs );
            Gia_ManStop( pSrm );            
            break;
        }
//Gia_DumpAiger( pSrm, "corrsrm", r, 2 );
        // found counter-examples to speculation
        clk2 = clock();
        if ( pPars->fUseCSat )
            vCexStore = Cbs_ManSolveMiterNc( pSrm, pPars->nBTLimit, &vStatus, 0 );
        else
            vCexStore = Cec_ManSatSolveMiter( pSrm, pParsSat, &vStatus );
        Gia_ManStop( pSrm );
        clkSat += clock() - clk2;
        if ( Vec_IntSize(vCexStore) == 0 )
        {
            Vec_IntFree( vCexStore );
            Vec_StrFree( vStatus );
            Vec_IntFree( vOutputs );
            break;
        }
        // refine classes with these counter-examples
        clk2 = clock();
        RetValue = Cec_ManResimulateCounterExamples( pSim, vCexStore, pPars->nFrames + 1 + nAddFrames );
        Vec_IntFree( vCexStore );
        clkSim += clock() - clk2;
        Gia_ManCheckRefinements( pAig, vStatus, vOutputs, pSim, pPars->fUseRings );
        if ( pPars->fVerbose )
            Cec_ManLCorrPrintStats( pAig, vStatus, r+1, clock() - clk );
        Vec_StrFree( vStatus );
        Vec_IntFree( vOutputs );
//Gia_ManEquivPrintClasses( pAig, 1, 0 );
    }
    if ( r == 100000 )
        printf( "The refinement was not finished. The result may be incorrect.\n" );
    Cec_ManSimStop( pSim );
    clkTotal = clock() - clkTotal;
    if ( pPars->fVerbose )
        Cec_ManLCorrPrintStats( pAig, NULL, r+1, clock() - clk );
    // derive reduced AIG
    Gia_ManSetProvedNodes( pAig );
    pNew = Gia_ManEquivReduce( pAig, 0, 0, 0 );
//Gia_WriteAiger( pNew, "reduced.aig", 0, 0 );
    pNew = Gia_ManSeqCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    // report the results
    if ( pPars->fVerbose )
    {
        printf( "NBeg = %d. NEnd = %d. (Gain = %6.2f %%).  RBeg = %d. REnd = %d. (Gain = %6.2f %%).\n", 
            Gia_ManAndNum(pAig), Gia_ManAndNum(pNew), 
            100.0*(Gia_ManAndNum(pAig)-Gia_ManAndNum(pNew))/(Gia_ManAndNum(pAig)?Gia_ManAndNum(pAig):1), 
            Gia_ManRegNum(pAig), Gia_ManRegNum(pNew), 
            100.0*(Gia_ManRegNum(pAig)-Gia_ManRegNum(pNew))/(Gia_ManRegNum(pAig)?Gia_ManRegNum(pAig):1) );
        ABC_PRTP( "Srm  ", clkSrm,                        clkTotal );
        ABC_PRTP( "Sat  ", clkSat,                        clkTotal );
        ABC_PRTP( "Sim  ", clkSim,                        clkTotal );
        ABC_PRTP( "Other", clkTotal-clkSat-clkSrm-clkSim, clkTotal );
        ABC_PRT( "TOTAL",  clkTotal );
    }
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


