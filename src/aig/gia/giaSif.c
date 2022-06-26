/**CFile****************************************************************

  FileName    [giaSif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSif.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/util/utilTruth.h"

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
static inline void Gia_ManCutMerge( int * pCut, int * pCut1, int * pCut2, int nSize )
{
    int * pBeg  = pCut+1;
    int * pBeg1 = pCut1+1;
    int * pBeg2 = pCut2+1;
    int * pEnd1 = pBeg1 + pCut1[0];
    int * pEnd2 = pBeg2 + pCut2[0];
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        if ( pBeg == pCut+nSize )
        {
            pCut[0] = -1;
            return;
        }
        if ( *pBeg1 == *pBeg2 )
            *pBeg++ = *pBeg1++, pBeg2++;
        else if ( *pBeg1 < *pBeg2 )
            *pBeg++ = *pBeg1++;
        else 
            *pBeg++ = *pBeg2++;
    }
    while ( pBeg1 < pEnd1 )
    {
        if ( pBeg == pCut+nSize )
        {
            pCut[0] = -1;
            return;
        }
        *pBeg++ = *pBeg1++;
    }
    while ( pBeg2 < pEnd2 )
    {
        if ( pBeg == pCut+nSize )
        {
            pCut[0] = -1;
            return;
        }
        *pBeg++ = *pBeg2++;
    }
    pCut[0] = pBeg-(pCut+1);
    assert( pCut[0] < nSize );
}
static inline int Gia_ManCutChoice( Gia_Man_t * p, int Level, int iObj, int iSibl, Vec_Int_t * vCuts, Vec_Int_t * vTimes, int nSize )
{
    int * pCut  = Vec_IntEntryP( vCuts, iObj*nSize );
    int * pCut2 = Vec_IntEntryP( vCuts, iSibl*nSize );
    int Level2 = Vec_IntEntry( vTimes, iSibl ); int i;
    assert( iObj > iSibl );
    if ( Level < Level2 || (Level == Level2 && pCut[0] <= pCut2[0]) )
        return Level;
    for ( i = 0; i <= pCut2[0]; i++ )
        pCut[i] = pCut2[i];
    return Level2;
}
static inline int Gia_ManCutOne( Gia_Man_t * p, int iObj, Vec_Int_t * vCuts, Vec_Int_t * vTimes, int nSize )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    int iFan0 = Gia_ObjFaninId0(pObj, iObj);
    int iFan1 = Gia_ObjFaninId1(pObj, iObj);
    int Cut0[2] = { 1, iFan0 };
    int Cut1[2] = { 1, iFan1 };
    int * pCut  = Vec_IntEntryP( vCuts, iObj*nSize );
    int * pCut0 = Vec_IntEntryP( vCuts, iFan0*nSize );
    int * pCut1 = Vec_IntEntryP( vCuts, iFan1*nSize );
    int Level_ = Vec_IntEntry( vTimes, iObj );
    int Level0 = Vec_IntEntry( vTimes, iFan0 );
    int Level1 = Vec_IntEntry( vTimes, iFan1 );
    int Level = Abc_MaxInt( Level0, Level1 );
    if ( Level == 0 ) 
        Level = 1;
    if ( Level0 == Level1 )
        Gia_ManCutMerge( pCut, pCut0, pCut1, nSize );
    else if ( Level0 > Level1 )
        Gia_ManCutMerge( pCut, pCut0, Cut1, nSize );
    else //if ( Level0 < Level1 )
        Gia_ManCutMerge( pCut, pCut1, Cut0, nSize );
    if ( pCut[0] == -1 )
    {
        pCut[0] = 2;
        pCut[1] = iFan0;
        pCut[2] = iFan1;
        Level++;
    }
    if ( Gia_ObjSibl(p, iObj) )
        Level = Gia_ManCutChoice( p, Level, iObj, Gia_ObjSibl(p, iObj), vCuts, vTimes, nSize );
    assert( pCut[0] > 0 && pCut[0] < nSize );
    Vec_IntUpdateEntry( vTimes, iObj, Level );
    return Level > Level_;
}
int Gia_ManCheckIter( Gia_Man_t * p, Vec_Int_t * vCuts, Vec_Int_t * vTimes, int nLutSize, int Period )
{
    int i, fChange = 0, nSize = nLutSize+1;
    Gia_Obj_t * pObj, * pObjRi, * pObjRo; 
    Gia_ManForEachRiRo( p, pObjRi, pObjRo, i )
        Vec_IntWriteEntry( vTimes, Gia_ObjId(p, pObjRo), Vec_IntEntry(vTimes, Gia_ObjId(p, pObjRi)) - Period );
    Gia_ManForEachAnd( p, pObj, i )
        fChange |= Gia_ManCutOne( p, i, vCuts, vTimes, nSize );
    Gia_ManForEachRi( p, pObj, i )
        Vec_IntWriteEntry( vTimes, Gia_ObjId(p, pObj), Vec_IntEntry(vTimes, Gia_ObjFaninId0p(p, pObj)) );
    return fChange;
}
int Gia_ManCheckPeriod( Gia_Man_t * p, Vec_Int_t * vCuts, Vec_Int_t * vTimes, int nLutSize, int Period, int * pIters )
{
    Gia_Obj_t * pObj; int i;
    assert( Gia_ManRegNum(p) > 0 );
    Vec_IntFill( vTimes, Gia_ManObjNum(p), -ABC_INFINITY );
    Vec_IntWriteEntry( vTimes, 0, 0 );
    Gia_ManForEachPi( p, pObj, i )
        Vec_IntWriteEntry( vTimes, Gia_ObjId(p, pObj), 0 );
    for ( *pIters = 0; *pIters < 100; (*pIters)++ )
    {
        if ( !Gia_ManCheckIter(p, vCuts, vTimes, nLutSize, Period) )
            return 1;
        Gia_ManForEachPo( p, pObj, i )
            if ( Vec_IntEntry(vTimes, Gia_ObjFaninId0p(p, pObj)) > Period )
                return 0;
    }
    return 0;
}
static inline void Gia_ManPrintCutOne( Gia_Man_t * p, int iObj, Vec_Int_t * vCuts, Vec_Int_t * vTimes, int nSize )
{
    int i, * pCut  = Vec_IntEntryP( vCuts, iObj*nSize );
    printf( "Obj %4d : Depth %d  CutSize %d  Cut {", iObj, Vec_IntEntry(vTimes, iObj), pCut[0] );
    for ( i = 1; i <= pCut[0]; i++ )
        printf( " %d", pCut[i] );
    printf( " }\n" );
}
int Gia_ManTestMapComb( Gia_Man_t * p, Vec_Int_t * vCuts, Vec_Int_t * vTimes, int nLutSize )
{
    Gia_Obj_t * pObj; int i, Id, Res = 0, nSize = nLutSize+1; 
    Vec_IntFill( vTimes, Gia_ManObjNum(p), 0 );
    Gia_ManForEachCiId( p, Id, i )
        Vec_IntWriteEntry( vCuts, Id*nSize, 1 );
    Gia_ManForEachCiId( p, Id, i )
        Vec_IntWriteEntry( vCuts, Id*nSize+1, Id );
    Gia_ManForEachAnd( p, pObj, i )
        Gia_ManCutOne( p, i, vCuts, vTimes, nSize );
    Gia_ManForEachCo( p, pObj, i )
        Res = Abc_MaxInt( Res, Vec_IntEntry(vTimes, Gia_ObjFaninId0p(p, pObj)) );
    //Gia_ManForEachAnd( p, pObj, i )
    //    Gia_ManPrintCutOne( p, i, vCuts, vTimes, nSize );
    return Res;
}
void Gia_ManPrintTimes( Gia_Man_t * p, Vec_Int_t * vTimes, int Period )
{
    int Pos[16] = {0};
    int Neg[16] = {0};
    Gia_Obj_t * pObj; int i;
    Gia_ManForEachAnd( p, pObj, i )
    {
        int Time = Vec_IntEntry(vTimes, i)-Period;
        Time = Abc_MinInt( Time,  10*Period );
        Time = Abc_MaxInt( Time, -10*Period );
        if ( Time >= 0 )
            Pos[(Time + Period-1)/Period]++;
        else
            Neg[(-Time + Period-1)/Period]++;
    }
    printf( "Statistics: " );
    for ( i = 15; i > 0; i-- )
        if ( Neg[i] )
            printf( " -%d=%d", i, Neg[i] );
    for ( i = 0; i < 16; i++ )
        if ( Pos[i] )
            printf( " %d=%d", i, Pos[i] );
    printf( "\n" );
}
Gia_Man_t * Gia_ManTestSif( Gia_Man_t * p, int nLutSize, int fVerbose )
{
    int nIters, nSize = nLutSize+1; // (2+1+nSize)*4=40 bytes/node
    abctime clk = Abc_Clock(); 
    Vec_Int_t * vCuts  = Vec_IntStart( Gia_ManObjNum(p) * nSize );
    Vec_Int_t * vTimes = Vec_IntAlloc( Gia_ManObjNum(p) );
    int Lower = 0;
    int Upper = Gia_ManTestMapComb( p, vCuts, vTimes, nLutSize );
    if ( fVerbose && Gia_ManRegNum(p) )
    printf( "Clock period %2d is %s\n", Lower, 0 ? "Yes" : "No " );
    if ( fVerbose && Gia_ManRegNum(p) )
    printf( "Clock period %2d is %s\n", Upper, 1 ? "Yes" : "No " );
    while ( Gia_ManRegNum(p) > 0 && Upper - Lower > 1 )
    {
        int Middle = (Upper + Lower) / 2;
        int Status = Gia_ManCheckPeriod( p, vCuts, vTimes, nLutSize, Middle, &nIters );
        if ( Status )
            Upper = Middle;
        else
            Lower = Middle;
        if ( fVerbose )
        printf( "Clock period %2d is %s after %d iterations\n", Middle, Status ? "Yes" : "No ", nIters );
    }
    if ( fVerbose )
    printf( "Clock period = %2d   ", Upper );
    if ( fVerbose )
    printf( "LUT size = %d   ", nLutSize );
    if ( fVerbose )
    printf( "Memory usage = %.2f MB   ", 4.0*(2+1+nSize)*Gia_ManObjNum(p)/(1 << 20) );
    if ( fVerbose )
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    //Gia_ManCheckPeriod( p, vCuts, vTimes, nLutSize, Upper, &nIters );
    //Gia_ManPrintTimes( p, vTimes, Upper );
    Vec_IntFree( vCuts );
    Vec_IntFree( vTimes );
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

