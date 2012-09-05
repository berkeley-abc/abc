/**CFile****************************************************************

  FileName    [giaIter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Iterative improvement of abstraction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaIter.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "giaAig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int  Gia_ObjIsInGla( Gia_Man_t * p, Gia_Obj_t * pObj )    { return Vec_IntEntry(p->vGateClasses, Gia_ObjId(p, pObj));  }
static inline void Gia_ObjAddToGla( Gia_Man_t * p, Gia_Obj_t * pObj )   { Vec_IntWriteEntry(p->vGateClasses, Gia_ObjId(p, pObj), 1); }
static inline void Gia_ObjRemFromGla( Gia_Man_t * p, Gia_Obj_t * pObj ) { Vec_IntWriteEntry(p->vGateClasses, Gia_ObjId(p, pObj), 0); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_IterTryImprove( Gia_Man_t * p, int nTimeOut, int iFrame0 )
{
    extern int Saig_BmcPerform( Aig_Man_t * pAig, int nStart, int nFramesMax, int nNodesMax, int nTimeOut, int nConfMaxOne, int nConfMaxAll, int fVerbose, int fVerbOverwrite, int * piFrames, int fSilent );
    Gia_Man_t * pAbs = Gia_ManDupAbsGates( p, p->vGateClasses );
    Aig_Man_t * pAig = Gia_ManToAigSimple( pAbs );
    int nStart      =            0;
    int nFrames     =  iFrame0 ? iFrame0 + 1 : 10000000;
    int nNodeDelta  =         2000;
    int nBTLimit    =            0;
    int nBTLimitAll =            0;
    int fVerbose    =            0;
    int RetValue, iFrame; 
    RetValue = Saig_BmcPerform( pAig, nStart, nFrames, nNodeDelta, nTimeOut, nBTLimit, nBTLimitAll, fVerbose, 0, &iFrame, 1 );
    assert( RetValue == 0 || RetValue == -1 );
    Aig_ManStop( pAig );
    Gia_ManStop( pAbs );
    return iFrame;
}
Gia_Man_t * Gia_IterImprove( Gia_Man_t * p, int nFrameMax, int nTimeOut, int fUsePdr, int fUseSat, int fUseBdd, int fVerbose )
{
    Gia_Obj_t * pObj;
    int i, iFrame0, iFrame;
    int nTotal = 0, nRemoved = 0;
    Vec_Int_t * vGScopy;
    clock_t clk, clkTotal = clock();
    assert( Gia_ManPoNum(p) == 1 );
    assert( p->vGateClasses != NULL );
    vGScopy = Vec_IntDup( p->vGateClasses );
    if ( nFrameMax == 0 )
        iFrame0 = Gia_IterTryImprove( p, 0, 0 );
    else
        iFrame0 = nFrameMax - 1;
    while ( 1 )
    {
        int fChanges = 0;
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( pObj->fMark0 )
                continue;
            if ( !Gia_ObjIsInGla(p, pObj) )
                continue;
            if ( pObj == Gia_ObjFanin0( Gia_ManPo(p, 0) ) )
                continue;
            if ( Gia_ObjIsAnd(pObj) )
            {
                if ( Gia_ObjIsInGla(p, Gia_ObjFanin0(pObj)) && Gia_ObjIsInGla(p, Gia_ObjFanin1(pObj)) )
                    continue;
            }
            if ( Gia_ObjIsRo(p, pObj) )
            {
                if ( Gia_ObjIsInGla(p, Gia_ObjRoToRi(p, pObj)) )
                    continue;
            }        
            clk = clock();
            printf( "%5d : ", nTotal );
            printf( "Obj =%7d   ", i );
            Gia_ObjRemFromGla( p, pObj );
            iFrame = Gia_IterTryImprove( p, nTimeOut, iFrame0 );
            if ( nFrameMax )
                assert( iFrame <= nFrameMax );
            else
                assert( iFrame <= iFrame0 );
            printf( "Frame =%6d   ", iFrame );
            if ( iFrame < iFrame0 )
            {
                pObj->fMark0 = 1;
                Gia_ObjAddToGla( p, pObj );
                printf( "           " );
            }
            else
            {
                fChanges = 1;
                nRemoved++;
                printf( "Removing   " );
                Vec_IntWriteEntry( vGScopy, Gia_ObjId(p, pObj), 0 );
            }
            Abc_PrintTime( 1, "Time", clock() - clk );
            nTotal++;
            // update the classes
            Vec_IntFreeP( &p->vGateClasses );
            p->vGateClasses = Vec_IntDup(vGScopy);
        }
        if ( !fChanges )
            break;
    }
    Gia_ManCleanMark0(p);
    Vec_IntFree( vGScopy );
    printf( "Tried = %d.  ",     nTotal );
    printf( "Removed = %d. (%.2f %%)  ",  nRemoved, 100.0 * nRemoved / Vec_IntCountPositive(p->vGateClasses) );
    Abc_PrintTime( 1, "Time",  clock() - clkTotal );
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

