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
#include "tim.h"

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
    p->vCis  = Vec_IntAlloc( nObjsMax / 10 );
    p->vCos  = Vec_IntAlloc( nObjsMax / 10 );
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
    Tim_ManStopP( (Tim_Man_t **)&p->pManTime );
    assert( p->pManTime == NULL );
    Vec_PtrFreeFree( p->vNamesIn );
    Vec_PtrFreeFree( p->vNamesOut );
    Vec_FltFreeP( &p->vTiming );
    Vec_VecFreeP( &p->vClockDoms );
    Vec_IntFreeP( &p->vLutConfigs );
    Vec_IntFreeP( &p->vCiNumsOrig );
    Vec_IntFreeP( &p->vCoNumsOrig );
    Vec_IntFreeP( &p->vFlopClasses );
    Vec_IntFreeP( &p->vLevels );
    Vec_IntFreeP( &p->vTruths );
    Vec_IntFree( p->vCis );
    Vec_IntFree( p->vCos );
    ABC_FREE( p->pTravIds );
    ABC_FREE( p->pPlacement );
    ABC_FREE( p->pSwitching );
    ABC_FREE( p->pCexSeq );
    ABC_FREE( p->pCexComb );
    ABC_FREE( p->pIso );
    ABC_FREE( p->pMapping );
    ABC_FREE( p->pFanData );
    ABC_FREE( p->pReprsOld );
    ABC_FREE( p->pReprs );
    ABC_FREE( p->pNexts );
    ABC_FREE( p->pName );
    ABC_FREE( p->pRefs );
    ABC_FREE( p->pNodeRefs );
    ABC_FREE( p->pHTable );
    ABC_FREE( p->pObjs );
    ABC_FREE( p );
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
        printf( "%d", Vec_IntEntry(p->vFlopClasses, i) );
    printf( "\n" );

    {
        Gia_Man_t * pTemp;
        pTemp = Gia_ManDupFlopClass( p, 1 );
        Gia_WriteAiger( pTemp, "dom1.aig", 0, 0 );
        Gia_ManStop( pTemp );
        pTemp = Gia_ManDupFlopClass( p, 2 );
        Gia_WriteAiger( pTemp, "dom2.aig", 0, 0 );
        Gia_ManStop( pTemp );
    }
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintClasses( Gia_Man_t * p )
{
    int i, Class, Counter0, Counter1;
    if ( p->vFlopClasses == NULL )
        return;
    if ( Vec_IntSize(p->vFlopClasses) != Gia_ManRegNum(p) )
    {
        printf( "Gia_ManPrintClasses(): The number of flop map entries differs from the number of flops.\n" );
        return;
    }
    printf( "Register classes: " );
    // count zero entries
    Counter0 = 0;
    Vec_IntForEachEntry( p->vFlopClasses, Class, i )
        Counter0 += (Class == 0);
    printf( "0=%d  ", Counter0 );
    // count one entries
    Counter1 = 0;
    Vec_IntForEachEntry( p->vFlopClasses, Class, i )
        Counter1 += (Class == 1);
    printf( "1=%d  ", Counter1 );
    // add comment
    if ( Counter0 + Counter1 < Gia_ManRegNum(p) )
        printf( "there are other classes..." );
    printf( "\n" );
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
    printf( "Placement:  Objects = %8d.  Fixed = %8d.  Undef = %8d.\n", Gia_ManObjNum(p), nFixed, nUndef );
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintStats( Gia_Man_t * p, int fSwitch )
{
    if ( p->pName )
        printf( "%-8s : ", p->pName );
    printf( "i/o =%7d/%7d", Gia_ManPiNum(p), Gia_ManPoNum(p) );
    if ( Gia_ManConstrNum(p) )
        printf( "(c=%d)", Gia_ManConstrNum(p) );
    if ( Gia_ManRegNum(p) )
        printf( "  ff =%7d", Gia_ManRegNum(p) );
    printf( "  and =%8d", Gia_ManAndNum(p) );
    printf( "  lev =%5d", Gia_ManLevelNum(p) );
    printf( "  cut =%5d", Gia_ManCrossCut(p) );
    printf( "  mem =%5.2f Mb", 12.0*Gia_ManObjNum(p)/(1<<20) );
    if ( Gia_ManHasDangling(p) )
        printf( "  ch =%5d", Gia_ManEquivCountClasses(p) );
    if ( fSwitch )
    {
        if ( p->pSwitching )
            printf( "  power =%7.2f", Gia_ManEvaluateSwitching(p) );
        else
            printf( "  power =%7.2f", Gia_ManComputeSwitching(p, 48, 16, 0) );
    }
//    printf( "obj =%5d  ", Gia_ManObjNum(p) );
    printf( "\n" );

//    Gia_ManSatExperiment( p );
    if ( p->pReprs && p->pNexts )
        Gia_ManEquivPrintClasses( p, 0, 0.0 );
    if ( p->pMapping )
        Gia_ManPrintMappingStats( p );
    if ( p->pPlacement )
        Gia_ManPrintPlacement( p );
    // print register classes
    Gia_ManPrintClasses( p );
}

/**Function*************************************************************

  Synopsis    [Prints stats for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintStatsShort( Gia_Man_t * p )
{
    printf( "i/o =%7d/%7d  ", Gia_ManPiNum(p), Gia_ManPoNum(p) );
    printf( "ff =%7d  ", Gia_ManRegNum(p) );
    printf( "and =%8d  ", Gia_ManAndNum(p) );
    printf( "lev =%5d  ", Gia_ManLevelNum(p) );
//    printf( "mem =%5.2f Mb", 12.0*Gia_ManObjNum(p)/(1<<20) );
    printf( "\n" );
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
    printf( "Outputs = %7d.  Unsat = %7d.  Sat = %7d.  Undec = %7d.\n", 
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
    printf( "REG: Beg = %5d. End = %5d. (R =%5.1f %%)  ",
        Gia_ManRegNum(p), Gia_ManRegNum(pNew), 
        Gia_ManRegNum(p)? 100.0*(Gia_ManRegNum(p)-Gia_ManRegNum(pNew))/Gia_ManRegNum(p) : 0.0 );
    printf( "AND: Beg = %6d. End = %6d. (R =%5.1f %%)",
        Gia_ManAndNum(p), Gia_ManAndNum(pNew), 
        Gia_ManAndNum(p)? 100.0*(Gia_ManAndNum(p)-Gia_ManAndNum(pNew))/Gia_ManAndNum(p) : 0.0 );
    printf( "\n" );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

