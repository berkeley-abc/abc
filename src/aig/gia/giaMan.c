/**CFile****************************************************************

  FileName    [giaMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Package manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/tim/tim.h"
#include "proof/abs/abs.h"
#include "opt/dar/dar.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManStart( int nObjsMax )
{
    Gia_Man_t * p;
    assert( nObjsMax > 0 );
    p = ABC_CALLOC( Gia_Man_t, 1 );
    p->nObjsAlloc = nObjsMax;
    p->pObjs = ABC_CALLOC( Gia_Obj_t, nObjsMax );
    p->pObjs->iDiff0 = p->pObjs->iDiff1 = GIA_NONE;
    p->nObjs = 1;
    p->vCis  = Vec_IntAlloc( nObjsMax / 20 );
    p->vCos  = Vec_IntAlloc( nObjsMax / 20 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deletes AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManStop( Gia_Man_t * p )
{
    if ( p->vSeqModelVec )
        Vec_PtrFreeFree( p->vSeqModelVec );
    Gia_ManStaticFanoutStop( p );
    Tim_ManStopP( (Tim_Man_t **)&p->pManTime );
    assert( p->pManTime == NULL );
    Vec_PtrFreeFree( p->vNamesIn );
    Vec_PtrFreeFree( p->vNamesOut );
    Vec_IntFreeP( &p->vSuper );
    Vec_IntFreeP( &p->vStore );
    Vec_IntFreeP( &p->vClassNew );
    Vec_IntFreeP( &p->vClassOld );
    Vec_WrdFreeP( &p->vSims );
    Vec_WrdFreeP( &p->vSimsPi );
    Vec_FltFreeP( &p->vTiming );
    Vec_VecFreeP( &p->vClockDoms );
    Vec_IntFreeP( &p->vLutConfigs );
    Vec_IntFreeP( &p->vUserPiIds );
    Vec_IntFreeP( &p->vUserPoIds );
    Vec_IntFreeP( &p->vUserFfIds );
    Vec_IntFreeP( &p->vFlopClasses );
    Vec_IntFreeP( &p->vGateClasses );
    Vec_IntFreeP( &p->vObjClasses );
    Vec_IntFreeP( &p->vDoms );
    Vec_IntFreeP( &p->vLevels );
    Vec_IntFreeP( &p->vTruths );
    Vec_IntFreeP( &p->vTtNums );
    Vec_IntFreeP( &p->vTtNodes );
    Vec_WrdFreeP( &p->vTtMemory );
    Vec_PtrFreeP( &p->vTtInputs );
    Vec_IntFreeP( &p->vMapping );
    Vec_IntFreeP( &p->vPacking );
    Vec_FltFreeP( &p->vInArrs );
    Vec_FltFreeP( &p->vOutReqs );
    Gia_ManStopP( &p->pAigExtra );
    Vec_IntFree( p->vCis );
    Vec_IntFree( p->vCos );
    ABC_FREE( p->pData2 );
    ABC_FREE( p->pTravIds );
    ABC_FREE( p->pPlacement );
    ABC_FREE( p->pSwitching );
    ABC_FREE( p->pCexSeq );
    ABC_FREE( p->pCexComb );
    ABC_FREE( p->pIso );
//    ABC_FREE( p->pMapping );
    ABC_FREE( p->pFanData );
    ABC_FREE( p->pReprsOld );
    ABC_FREE( p->pReprs );
    ABC_FREE( p->pNexts );
    ABC_FREE( p->pSibls );
    ABC_FREE( p->pRefs );
//    ABC_FREE( p->pNodeRefs );
    ABC_FREE( p->pHTable );
    ABC_FREE( p->pMuxes );
    ABC_FREE( p->pObjs );
    ABC_FREE( p->pSpec );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Returns memory used in megabytes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
double Gia_ManMemory( Gia_Man_t * p )
{
    double Memory = sizeof(Gia_Man_t);
    Memory += sizeof(Gia_Obj_t) * Gia_ManObjNum(p);
    Memory += sizeof(int) * Gia_ManCiNum(p);
    Memory += sizeof(int) * Gia_ManCoNum(p);
    Memory += sizeof(int) * p->nHTable * (p->pHTable != NULL);
    return Memory;
}

/**Function*************************************************************

  Synopsis    [Stops the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManStopP( Gia_Man_t ** p )
{
    if ( *p == NULL )
        return;
    Gia_ManStop( *p );
    *p = NULL;
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintClasses_old( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    if ( p->vFlopClasses == NULL )
        return;
    Gia_ManForEachRo( p, pObj, i )
        Abc_Print( 1, "%d", Vec_IntEntry(p->vFlopClasses, i) );
    Abc_Print( 1, "\n" );

    {
        Gia_Man_t * pTemp;
        pTemp = Gia_ManDupFlopClass( p, 1 );
        Gia_AigerWrite( pTemp, "dom1.aig", 0, 0 );
        Gia_ManStop( pTemp );
        pTemp = Gia_ManDupFlopClass( p, 2 );
        Gia_AigerWrite( pTemp, "dom2.aig", 0, 0 );
        Gia_ManStop( pTemp );
    }
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintPlacement( Gia_Man_t * p )
{
    int i, nFixed = 0, nUndef = 0;
    if ( p->pPlacement == NULL )
        return;
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
    {
        nFixed += p->pPlacement[i].fFixed;
        nUndef += p->pPlacement[i].fUndef;
    }
    Abc_Print( 1, "Placement:  Objects = %8d.  Fixed = %8d.  Undef = %8d.\n", Gia_ManObjNum(p), nFixed, nUndef );
}


/**Function*************************************************************

  Synopsis    [Duplicates AIG for unrolling.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintTents_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vObjs )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    Vec_IntPush( vObjs, Gia_ObjId(p, pObj) );
    if ( Gia_ObjIsCi(pObj) )
        return;
    Gia_ManPrintTents_rec( p, Gia_ObjFanin0(pObj), vObjs );
    if ( Gia_ObjIsAnd(pObj) )
        Gia_ManPrintTents_rec( p, Gia_ObjFanin1(pObj), vObjs );
}
void Gia_ManPrintTents( Gia_Man_t * p )
{
    Vec_Int_t * vObjs;
    Gia_Obj_t * pObj;
    int t, i, iObjId, nSizePrev, nSizeCurr;
    assert( Gia_ManPoNum(p) > 0 );
    vObjs = Vec_IntAlloc( 100 );
    // save constant class
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrent( p, Gia_ManConst0(p) );
    Vec_IntPush( vObjs, 0 );
    // create starting root
    nSizePrev = Vec_IntSize(vObjs);
    Gia_ManForEachPo( p, pObj, i )
        Gia_ManPrintTents_rec( p, pObj, vObjs );
    // build tents
    Abc_Print( 1, "Tents:  " );
    for ( t = 1; nSizePrev < Vec_IntSize(vObjs); t++ )
    {
        int nPis = 0;
        nSizeCurr = Vec_IntSize(vObjs);
        Vec_IntForEachEntryStartStop( vObjs, iObjId, i, nSizePrev, nSizeCurr )
        {
            nPis += Gia_ObjIsPi(p, Gia_ManObj(p, iObjId));
            if ( Gia_ObjIsRo(p, Gia_ManObj(p, iObjId)) )
                Gia_ManPrintTents_rec( p, Gia_ObjRoToRi(p, Gia_ManObj(p, iObjId)), vObjs );
        }
        Abc_Print( 1, "%d=%d(%d)  ", t, nSizeCurr - nSizePrev, nPis );
        nSizePrev = nSizeCurr;
    }
    Abc_Print( 1, " Unused=%d\n", Gia_ManObjNum(p) - Vec_IntSize(vObjs) );
    Vec_IntFree( vObjs );
    // the remaining objects are PIs without fanout
//    Gia_ManForEachObj( p, pObj, i )
//        if ( !Gia_ObjIsTravIdCurrent(p, pObj) )
//            Gia_ObjPrint( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintChoiceStats( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, nEquivs = 0, nChoices = 0;
    Gia_ManMarkFanoutDrivers( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !Gia_ObjSibl(p, i) )
            continue;
        nEquivs++;
        if ( pObj->fMark0 )
            nChoices++;
        assert( !Gia_ObjSiblObj(p, i)->fMark0 );
        assert( Gia_ObjIsAnd(Gia_ObjSiblObj(p, i)) );
    }
    Abc_Print( 1, "Choice stats: Equivs =%7d. Choices =%7d.\n", nEquivs, nChoices );
    Gia_ManCleanMark0( p );
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintStats( Gia_Man_t * p, Gps_Par_t * pPars )
{
    if ( p->pName )
        Abc_Print( 1, "%-8s : ", p->pName );
    Abc_Print( 1, "i/o =%7d/%7d", Gia_ManPiNum(p), Gia_ManPoNum(p) );
    if ( Gia_ManConstrNum(p) )
        Abc_Print( 1, "(c=%d)", Gia_ManConstrNum(p) );
    if ( Gia_ManRegNum(p) )
        Abc_Print( 1, "  ff =%7d", Gia_ManRegNum(p) );
    Abc_Print( 1, "  %s =%8d", p->pMuxes? "nod" : "and", Gia_ManAndNum(p) );
    Abc_Print( 1, "  lev =%5d", Gia_ManLevelNum(p) ); Vec_IntFreeP( &p->vLevels );
    if ( pPars && pPars->fCut )
        Abc_Print( 1, "  cut = %d(%d)", Gia_ManCrossCut(p, 0), Gia_ManCrossCut(p, 1) );
    Abc_Print( 1, "  mem =%5.2f MB", Gia_ManMemory(p)/(1<<20) );
    if ( Gia_ManHasDangling(p) )
        Abc_Print( 1, "  ch =%5d", Gia_ManEquivCountClasses(p) );
    if ( p->pMuxes )
    {
        Abc_Print( 1, "  and =%5d", Gia_ManAndNum(p)-Gia_ManXorNum(p)-Gia_ManMuxNum(p) );
        Abc_Print( 1, "  xor =%5d", Gia_ManXorNum(p) );
        Abc_Print( 1, "  mux =%5d", Gia_ManMuxNum(p) );
    }
    if ( pPars && pPars->fSwitch )
    {
        if ( p->pSwitching )
            Abc_Print( 1, "  power =%7.2f", Gia_ManEvaluateSwitching(p) );
        else
            Abc_Print( 1, "  power =%7.2f", Gia_ManComputeSwitching(p, 48, 16, 0) );
    }
//    Abc_Print( 1, "obj =%5d  ", Gia_ManObjNum(p) );
    Abc_Print( 1, "\n" );

//    Gia_ManSatExperiment( p );
    if ( p->pReprs && p->pNexts )
        Gia_ManEquivPrintClasses( p, 0, 0.0 );
    if ( p->pSibls )
        Gia_ManPrintChoiceStats( p );
    if ( Gia_ManHasMapping(p) )
        Gia_ManPrintMappingStats( p, pPars && pPars->fDumpFile );
    if ( pPars && pPars->fNpn && Gia_ManHasMapping(p) && Gia_ManLutSizeMax(p) <= 4 )
        Gia_ManPrintNpnClasses( p );
    if ( p->vPacking )
        Gia_ManPrintPackingStats( p );
    if ( pPars && pPars->fLutProf && Gia_ManHasMapping(p) )
        Gia_ManPrintLutStats( p );
    if ( p->pPlacement )
        Gia_ManPrintPlacement( p );
    if ( p->pManTime )
        Tim_ManPrintStats( (Tim_Man_t *)p->pManTime, p->nAnd2Delay );
    // print register classes
    Gia_ManPrintFlopClasses( p );
    Gia_ManPrintGateClasses( p );
    Gia_ManPrintObjClasses( p );
    if ( pPars && pPars->fTents )
    {
/*
        int k, Entry, Prev = 1;
        Vec_Int_t * vLimit = Vec_IntAlloc( 1000 );
        Gia_Man_t * pNew = Gia_ManUnrollDup( p, vLimit );
        Abc_Print( 1, "Tents:  " );
        Vec_IntForEachEntryStart( vLimit, Entry, k, 1 )
            Abc_Print( 1, "%d=%d  ", k, Entry-Prev ), Prev = Entry;
        Abc_Print( 1, " Unused=%d.", Gia_ManObjNum(p) - Gia_ManObjNum(pNew) );
        Abc_Print( 1, "\n" );
        Vec_IntFree( vLimit );
        Gia_ManStop( pNew );
*/
        Gia_ManPrintTents( p );
    }
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintStatsShort( Gia_Man_t * p )
{
    Abc_Print( 1, "i/o =%7d/%7d  ", Gia_ManPiNum(p), Gia_ManPoNum(p) );
    Abc_Print( 1, "ff =%7d  ", Gia_ManRegNum(p) );
    Abc_Print( 1, "and =%8d  ", Gia_ManAndNum(p) );
    Abc_Print( 1, "lev =%5d  ", Gia_ManLevelNum(p) );
//    Abc_Print( 1, "mem =%5.2f MB", 12.0*Gia_ManObjNum(p)/(1<<20) );
    Abc_Print( 1, "\n" );
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintMiterStatus( Gia_Man_t * p )
{
    Gia_Obj_t * pObj, * pChild;
    int i, nSat = 0, nUnsat = 0, nUndec = 0, iOut = -1;
    Gia_ManForEachPo( p, pObj, i )
    {
        pChild = Gia_ObjChild0(pObj);
        // check if the output is constant 0
        if ( pChild == Gia_ManConst0(p) )
            nUnsat++;
        // check if the output is constant 1
        else if ( pChild == Gia_ManConst1(p) )
        {
            nSat++;
            if ( iOut == -1 )
                iOut = i;
        }
        // check if the output is a primary input
        else if ( Gia_ObjIsPi(p, Gia_Regular(pChild)) )
        {
            nSat++;
            if ( iOut == -1 )
                iOut = i;
        }
/*
        // check if the output is 1 for the 0000 pattern
        else if ( Gia_Regular(pChild)->fPhase != (unsigned)Gia_IsComplement(pChild) )
        {
            nSat++;
            if ( iOut == -1 )
                iOut = i;
        }
*/
        else
            nUndec++;
    }
    Abc_Print( 1, "Outputs = %7d.  Unsat = %7d.  Sat = %7d.  Undec = %7d.\n",
        Gia_ManPoNum(p), nUnsat, nSat, nUndec );
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetRegNum( Gia_Man_t * p, int nRegs )
{
    assert( p->nRegs == 0 );
    p->nRegs = nRegs;
}


/**Function*************************************************************

  Synopsis    [Reports the reduction of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManReportImprovement( Gia_Man_t * p, Gia_Man_t * pNew )
{
    Abc_Print( 1, "REG: Beg = %5d. End = %5d. (R =%5.1f %%)  ",
        Gia_ManRegNum(p), Gia_ManRegNum(pNew),
        Gia_ManRegNum(p)? 100.0*(Gia_ManRegNum(p)-Gia_ManRegNum(pNew))/Gia_ManRegNum(p) : 0.0 );
    Abc_Print( 1, "AND: Beg = %6d. End = %6d. (R =%5.1f %%)",
        Gia_ManAndNum(p), Gia_ManAndNum(pNew),
        Gia_ManAndNum(p)? 100.0*(Gia_ManAndNum(p)-Gia_ManAndNum(pNew))/Gia_ManAndNum(p) : 0.0 );
    Abc_Print( 1, "\n" );
}

/**Function*************************************************************

  Synopsis    [Prints NPN class statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintNpnClasses( Gia_Man_t * p )
{
    extern char ** Kit_DsdNpn4ClassNames();
    char ** pNames = Kit_DsdNpn4ClassNames();
    Vec_Int_t * vLeaves, * vTruth, * vVisited;
    int * pLutClass, ClassCounts[222] = {0};
    int i, k, iFan, Class, OtherClasses, OtherClasses2, nTotal, Counter, Counter2;
    unsigned * pTruth;
    assert( Gia_ManHasMapping(p) );
    assert(  Gia_ManLutSizeMax( p ) <= 4 );
    vLeaves   = Vec_IntAlloc( 100 );
    vVisited  = Vec_IntAlloc( 100 );
    vTruth    = Vec_IntAlloc( (1<<16) );
    pLutClass = ABC_CALLOC( int, Gia_ManObjNum(p) );
    Gia_ManCleanTruth( p );
    Gia_ManForEachLut( p, i )
    {
        if ( Gia_ObjLutSize(p,i) > 4 )
            continue;
        Vec_IntClear( vLeaves );
        Gia_LutForEachFanin( p, i, iFan, k )
            Vec_IntPush( vLeaves, iFan );
        for ( ; k < 4; k++ )
            Vec_IntPush( vLeaves, 0 );
        pTruth = Gia_ManConvertAigToTruth( p, Gia_ManObj(p, i), vLeaves, vTruth, vVisited );
        Class = Dar_LibReturnClass( *pTruth );
        ClassCounts[ Class ]++;
        pLutClass[i] = Class;
    }
    Vec_IntFree( vLeaves );
    Vec_IntFree( vTruth );
    Vec_IntFree( vVisited );
    Vec_IntFreeP( &p->vTruths );
    nTotal = 0;
    for ( i = 0; i < 222; i++ )
        nTotal += ClassCounts[i];
    Abc_Print( 1, "NPN CLASS STATISTICS (for %d LUT4 present in the current mapping):\n", nTotal );
    OtherClasses = 0;
    for ( i = 0; i < 222; i++ )
    {
        if ( ClassCounts[i] == 0 )
            continue;
//        if ( 100.0 * ClassCounts[i] / (nTotal+1) < 0.1 ) // do not show anything below 0.1 percent
//            continue;
        OtherClasses += ClassCounts[i];
        Abc_Print( 1, "Class %3d :  Count = %6d   (%7.2f %%)   %s\n", 
            i, ClassCounts[i], 100.0 * ClassCounts[i] / (nTotal+1), pNames[i] );
    }
    OtherClasses = nTotal - OtherClasses;
    Abc_Print( 1, "Other     :  Count = %6d   (%7.2f %%)\n", 
        OtherClasses, 100.0 * OtherClasses / (nTotal+1) );
    // count the number of LUTs that have MUX function and two fanins with MUX functions
    OtherClasses = OtherClasses2 = 0;
    ABC_FREE( p->pRefs );
    Gia_ManSetRefsMapped( p );
    Gia_ManForEachLut( p, i )
    {
        if ( pLutClass[i] != 109 )
            continue;
        Counter = Counter2 = 0;
        Gia_LutForEachFanin( p, i, iFan, k )
        {
            Counter  += (pLutClass[iFan] == 109);
            Counter2 += (pLutClass[iFan] == 109) && (Gia_ObjRefNumId(p, iFan) == 1);
        }
        OtherClasses  += (Counter > 1);
        OtherClasses2 += (Counter2 > 1);
//            Abc_Print( 1, "%d -- ", pLutClass[i] );
//            Gia_LutForEachFanin( p, i, iFan, k )
//                Abc_Print( 1, "%d ", pLutClass[iFan] );
//            Abc_Print( 1, "\n" );
    }
    ABC_FREE( p->pRefs );
    Abc_Print( 1, "Approximate number of 4:1 MUX structures: All = %6d  (%7.2f %%)  MFFC = %6d  (%7.2f %%)\n", 
        OtherClasses,  100.0 * OtherClasses  / (nTotal+1),
        OtherClasses2, 100.0 * OtherClasses2 / (nTotal+1) );
    ABC_FREE( pLutClass );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
