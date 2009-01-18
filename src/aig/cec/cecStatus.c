/**CFile****************************************************************

  FileName    [cecStatus.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [Miter status.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecStatus.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if the output is known.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_OutputStatus( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pChild;
    assert( Aig_ObjIsPo(pObj) );
    pChild = Aig_ObjChild0(pObj);
    // check if the output is constant 0
    if ( pChild == Aig_ManConst0(p) )
        return 1;
    // check if the output is constant 1
    if ( pChild == Aig_ManConst1(p) )
        return 1;
    // check if the output is a primary input
    if ( Aig_ObjIsPi(Aig_Regular(pChild)) )
        return 1;
    // check if the output is 1 for the 0000 pattern
    if ( Aig_Regular(pChild)->fPhase != (unsigned)Aig_IsComplement(pChild) )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns number of used inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_CountInputs( Aig_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i, Counter = 0;
    Aig_ManForEachPi( p, pObj, i )
        Counter += (int)(pObj->nRefs > 0);
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Checks the status of the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cec_MtrStatus_t Cec_MiterStatus( Aig_Man_t * p )
{
    Cec_MtrStatus_t Status;
    Aig_Obj_t * pObj, * pChild;
    int i;
    assert( p->nRegs == 0 );
    memset( &Status, 0, sizeof(Cec_MtrStatus_t) );
    Status.iOut = -1;
    Status.nInputs  = Cec_CountInputs( p );
    Status.nNodes   = Aig_ManNodeNum( p );
    Status.nOutputs = Aig_ManPoNum(p);
    Aig_ManForEachPo( p, pObj, i )
    {
        pChild = Aig_ObjChild0(pObj);
        // check if the output is constant 0
        if ( pChild == Aig_ManConst0(p) )
            Status.nUnsat++;
        // check if the output is constant 1
        else if ( pChild == Aig_ManConst1(p) )
        {
            Status.nSat++;
            if ( Status.iOut == -1 )
                Status.iOut = i;
        }
        // check if the output is a primary input
        else if ( Aig_ObjIsPi(Aig_Regular(pChild)) )
        {
            Status.nSat++;
            if ( Status.iOut == -1 )
                Status.iOut = i;
        }
    // check if the output is 1 for the 0000 pattern
        else if ( Aig_Regular(pChild)->fPhase != (unsigned)Aig_IsComplement(pChild) )
        {
            Status.nSat++;
            if ( Status.iOut == -1 )
                Status.iOut = i;
        }
        else
            Status.nUndec++;
    }
    return Status;
}

/**Function*************************************************************

  Synopsis    [Checks the status of the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cec_MtrStatus_t Cec_MiterStatusTrivial( Aig_Man_t * p )
{
    Cec_MtrStatus_t Status;
    memset( &Status, 0, sizeof(Cec_MtrStatus_t) );
    Status.iOut = -1;
    Status.nInputs  = Aig_ManPiNum(p);
    Status.nNodes   = Aig_ManNodeNum( p );
    Status.nOutputs = Aig_ManPoNum(p);
    Status.nUndec   = Aig_ManPoNum(p);
    return Status;
}

/**Function*************************************************************

  Synopsis    [Prints the status of the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_MiterStatusPrint( Cec_MtrStatus_t S, char * pString, int Time )
{
    printf( "%s:", pString );
    printf( "  I =%6d", S.nInputs );
    printf( "  N =%7d", S.nNodes );
    printf( "  " );
    printf( "  ? =%6d", S.nUndec );
    printf( "  U =%6d", S.nUnsat );
    printf( "  S =%6d", S.nSat );
    printf(" %7.2f sec\n", (float)(Time)/(float)(CLOCKS_PER_SEC));
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


