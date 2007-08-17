/**CFile****************************************************************

  FileName    [fraPart.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    [Partitioning for induction.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraPart.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

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
void Fra_ManPartitionTest( Aig_Man_t * p, int nComLim )
{
    ProgressBar * pProgress;
    Vec_Vec_t * vSupps, * vSuppsIn;
    Vec_Ptr_t * vSuppsNew;
    Vec_Int_t * vSupNew, * vSup, * vSup2, * vTemp;//, * vSupIn;
    Vec_Int_t * vOverNew, * vQuantNew;
    Aig_Obj_t * pObj;
    int i, k, nCommon, CountOver, CountQuant;
    int nTotalSupp, nTotalSupp2, Entry, Largest;//, iVar;
    double Ratio, R;
    int clk;

    nTotalSupp = 0;
    nTotalSupp2 = 0;
    Ratio = 0.0;
 
    // compute supports
clk = clock();
    vSupps = Aig_ManSupports( p );
PRT( "Supports", clock() - clk );
    // remove last entry
    Aig_ManForEachPo( p, pObj, i )
    {
        vSup = Vec_VecEntry( vSupps, i );
        Vec_IntPop( vSup );
        // remember support
//        pObj->pNext = (Aig_Obj_t *)vSup;
    }

    // create reverse supports
clk = clock();
    vSuppsIn = Vec_VecStart( Aig_ManPiNum(p) );
    Aig_ManForEachPo( p, pObj, i )
    {
        vSup = Vec_VecEntry( vSupps, i );
        Vec_IntForEachEntry( vSup, Entry, k )
            Vec_VecPush( vSuppsIn, Entry, (void *)i );
    }
PRT( "Inverse ", clock() - clk );

clk = clock();
    // compute extended supports
    Largest = 0;
    vSuppsNew = Vec_PtrAlloc( Aig_ManPoNum(p) );
    vOverNew  = Vec_IntAlloc( Aig_ManPoNum(p) );
    vQuantNew = Vec_IntAlloc( Aig_ManPoNum(p) );
    pProgress = Extra_ProgressBarStart( stdout, Aig_ManPoNum(p) );
    Aig_ManForEachPo( p, pObj, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // get old supports
        vSup = Vec_VecEntry( vSupps, i );
        if ( Vec_IntSize(vSup) < 2 )
            continue;
        // compute new supports
        CountOver = CountQuant = 0;
        vSupNew = Vec_IntDup( vSup );
        // go through the nodes where the first var appears
        Aig_ManForEachPo( p, pObj, k )
//        iVar = Vec_IntEntry( vSup, 0 );
//        vSupIn = Vec_VecEntry( vSuppsIn, iVar );
//        Vec_IntForEachEntry( vSupIn, Entry, k )
        {
//            pObj = Aig_ManObj( p, Entry );
            // get support of this output
//            vSup2 = (Vec_Int_t *)pObj->pNext;
            vSup2 = Vec_VecEntry( vSupps, k );
            // count the number of common vars
            nCommon = Vec_IntTwoCountCommon(vSup, vSup2);
            if ( nCommon < 2 )
                continue;
            if ( nCommon > nComLim )
            {
                vSupNew = Vec_IntTwoMerge( vTemp = vSupNew, vSup2 );
                Vec_IntFree( vTemp );
                CountOver++;
            }
            else
                CountQuant++;
        }
        // save the results
        Vec_PtrPush( vSuppsNew, vSupNew );
        Vec_IntPush( vOverNew, CountOver );
        Vec_IntPush( vQuantNew, CountQuant );

        if ( Largest < Vec_IntSize(vSupNew) )
            Largest = Vec_IntSize(vSupNew);

        nTotalSupp  += Vec_IntSize(vSup);
        nTotalSupp2 += Vec_IntSize(vSupNew);
        if ( Vec_IntSize(vSup) )
            R = Vec_IntSize(vSupNew) / Vec_IntSize(vSup);
        else
            R = 0;
        Ratio += R;

        if ( R < 5.0 )
            continue;

        printf( "%6d : ", i );
        printf( "S = %5d. ", Vec_IntSize(vSup) );
        printf( "SNew = %5d. ", Vec_IntSize(vSupNew) );
        printf( "R = %7.2f. ", R );
        printf( "Over = %5d. ", CountOver );
        printf( "Quant = %5d. ", CountQuant );
        printf( "\n" );
/*
        Vec_IntForEachEntry( vSupNew, Entry, k )
            printf( "%d ", Entry );
        printf( "\n" );
*/
    }
    Extra_ProgressBarStop( pProgress );
PRT( "Scanning", clock() - clk );

    // print cumulative statistics
    printf( "PIs = %6d. POs = %6d. Lim = %3d.   AveS = %3d. SN = %3d. R = %4.2f Max = %5d.\n",
        Aig_ManPiNum(p), Aig_ManPoNum(p), nComLim,
        nTotalSupp/Aig_ManPoNum(p), nTotalSupp2/Aig_ManPoNum(p),
        Ratio/Aig_ManPoNum(p), Largest );

    Vec_VecFree( vSupps );
    Vec_VecFree( vSuppsIn );
    Vec_VecFree( (Vec_Vec_t *)vSuppsNew );
    Vec_IntFree( vOverNew );
    Vec_IntFree( vQuantNew );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


