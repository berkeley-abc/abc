/**CFile****************************************************************

  FileName    [bmcBmcAnd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Memory-efficient BMC engine]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmcBmcAnd.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"

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
int Gia_ManCountUnmarked_rec( Gia_Obj_t * pObj )
{
    if ( !Gia_ObjIsAnd(pObj) || pObj->fMark0 )
        return 0;
    pObj->fMark0 = 1;
    return 1 + Gia_ManCountUnmarked_rec( Gia_ObjFanin0(pObj) ) + 
        Gia_ManCountUnmarked_rec( Gia_ObjFanin1(pObj) );
}
int Gia_ManCountUnmarked( Gia_Man_t * p, int iStart )
{
    int i, Counter = 0;
    for ( i = iStart; i < Gia_ManPoNum(p); i++ )
        Counter += Gia_ManCountUnmarked_rec( Gia_ObjFanin0(Gia_ManPo(p, i)) );
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManBmcPerform( Gia_Man_t * pGia, Bmc_AndPar_t * pPars )
{
    Unr_Man_t * p;
    Gia_Man_t * pFrames;
    abctime clk = Abc_Clock();
    int nFramesMax = pPars->nFramesMax ? pPars->nFramesMax : ABC_INFINITY;
    int i, f, iStart, status = -1, Counter = 0;
    p = Unr_ManUnrollStart( pGia, pPars->fVeryVerbose );
    for ( f = 0; f < nFramesMax; f++ )
    {
        pFrames = Unr_ManUnrollFrame( p, f );
        assert( Gia_ManPoNum(pFrames) == (f + 1) * Gia_ManPoNum(pGia) );
        iStart = f * Gia_ManPoNum(pGia);
        for ( i = iStart; i < Gia_ManPoNum(pFrames); i++ )
            if ( Gia_ObjChild0(Gia_ManPo(pFrames, i)) != Gia_ManConst0(pFrames) )
                break;
        if ( i == Gia_ManPoNum(pFrames) )
        {
            if ( pPars->fVerbose )
            {
                printf( "Frame %4d :  Trivally UNSAT.   Memory = %5.1f Mb   ", f, Gia_ManMemory(pFrames) );
                Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
            }
            continue;
        }
        if ( pPars->fVerbose )
        {
            printf( "Frame %4d :  AIG =%9d.   Memory = %5.1f Mb   ", f, Gia_ManCountUnmarked(pFrames, iStart), Gia_ManMemory(pFrames) );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        }
        if ( ++Counter == 10 )
            break;
    }
    Unr_ManFree( p );
    return status;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

