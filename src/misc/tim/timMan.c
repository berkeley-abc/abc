/**CFile****************************************************************

  FileName    [timMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchy/timing manager.]

  Synopsis    [Manipulation of manager data-structure.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: timMan.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "timInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Tim_Man_t * Tim_ManStart( int nCis, int nCos )
{
    Tim_Man_t * p;
    Tim_Obj_t * pObj;
    int i;
    p = ABC_ALLOC( Tim_Man_t, 1 );
    memset( p, 0, sizeof(Tim_Man_t) );
    p->pMemObj = Mem_FlexStart();
    p->nCis = nCis;
    p->nCos = nCos;
    p->pCis = ABC_ALLOC( Tim_Obj_t, nCis );
    memset( p->pCis, 0, sizeof(Tim_Obj_t) * nCis );
    p->pCos = ABC_ALLOC( Tim_Obj_t, nCos );
    memset( p->pCos, 0, sizeof(Tim_Obj_t) * nCos );
    Tim_ManForEachCi( p, pObj, i )
    {
        pObj->Id = i;
        pObj->iObj2Box = pObj->iObj2Num = -1;
        pObj->timeReq = TIM_ETERNITY;
    }
    Tim_ManForEachCo( p, pObj, i )
    {
        pObj->Id = i;
        pObj->iObj2Box = pObj->iObj2Num = -1;
        pObj->timeReq = TIM_ETERNITY;
    }
    p->fUseTravId = 1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Duplicates the timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Tim_Man_t * Tim_ManDup( Tim_Man_t * p, int fUnitDelay )
{
    Tim_Man_t * pNew;
    Tim_Box_t * pBox;
    Tim_Obj_t * pObj;
    float * pDelayTable, * pDelayTableNew;
    int i, k, nInputs, nOutputs;
    // create new manager
    pNew = Tim_ManStart( p->nCis, p->nCos );
    // copy box connectivity information
    memcpy( pNew->pCis, p->pCis, sizeof(Tim_Obj_t) * p->nCis );
    memcpy( pNew->pCos, p->pCos, sizeof(Tim_Obj_t) * p->nCos );
    // clear traversal IDs
    Tim_ManForEachCi( p, pObj, i )
        pObj->TravId = 0;
    Tim_ManForEachCo( p, pObj, i )
        pObj->TravId = 0;
    if ( fUnitDelay )
    {
        // discretize PI arrival times
//        Tim_ManForEachPi( pNew, pObj, k )
//          pObj->timeArr = (int)pObj->timeArr;
        // discretize PO required times
//        Tim_ManForEachPo( pNew, pObj, k )
//          pObj->timeReq = 1 + (int)pObj->timeReq;
        // clear PI arrival and PO required
        Tim_ManInitPiArrivalAll( p, 0.0 );
        Tim_ManInitPoRequiredAll( p, (float)TIM_ETERNITY );
    }
    // duplicate delay tables
    pNew->vDelayTables = Vec_PtrAlloc( Vec_PtrSize(p->vDelayTables) );
    Vec_PtrForEachEntry( float *, p->vDelayTables, pDelayTable, i )
    {
        assert( i == (int)pDelayTable[0] );
        nInputs   = (int)pDelayTable[1];
        nOutputs  = (int)pDelayTable[2];
        pDelayTableNew = ABC_ALLOC( float, 3 + nInputs * nOutputs );
        pDelayTableNew[0] = (int)pDelayTable[0];
        pDelayTableNew[1] = (int)pDelayTable[1];
        pDelayTableNew[2] = (int)pDelayTable[2];
        for ( k = 0; k < nInputs * nOutputs; k++ )
            pDelayTableNew[3+k] = fUnitDelay ? 1.0 : pDelayTable[3+k];
        assert( (int)pDelayTableNew[0] == Vec_PtrSize(pNew->vDelayTables) );
        Vec_PtrPush( pNew->vDelayTables, pDelayTableNew );
    }
    // duplicate boxes
    Tim_ManForEachBox( p, pBox, i )
       Tim_ManCreateBox( pNew, pBox->Inouts[0], pBox->nInputs, 
            pBox->Inouts[pBox->nInputs], pBox->nOutputs, pBox->iDelayTable );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Stops the timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManStop( Tim_Man_t * p )
{
    float * pTable;
    int i;
    if ( p->vDelayTables )
    {
        Vec_PtrForEachEntry( float *, p->vDelayTables, pTable, i )
            ABC_FREE( pTable );
        Vec_PtrFree( p->vDelayTables );
    }
    Vec_PtrFree( p->vBoxes );
    Mem_FlexStop( p->pMemObj, 0 );
    ABC_FREE( p->pCis );
    ABC_FREE( p->pCos );
    ABC_FREE( p );
}
void Tim_ManStopP( Tim_Man_t ** p )
{
    if ( *p == NULL )
        return;
    Tim_ManStop( *p );
    *p = NULL;
}

/**Function*************************************************************

  Synopsis    [Prints the timing manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManPrint( Tim_Man_t * p )
{
    Tim_Box_t * pBox;
    Tim_Obj_t * pObj, * pPrev;
    float * pTable;
    int i, k;
    printf( "TIMING INFORMATION:\n" );

    // print CI info
    pPrev = p->pCis;
    Tim_ManForEachPi( p, pObj, i )
        if ( pPrev->timeArr != pObj->timeArr || pPrev->timeReq != pObj->timeReq )
            break;
    if ( i == Tim_ManCiNum(p) )
        printf( "All PIs :  arr = %5.3f  req = %5.3f\n", pPrev->timeArr, pPrev->timeReq );
    else
        Tim_ManForEachPi( p, pObj, i )
            printf( "PI%5d :  arr = %5.3f  req = %5.3f\n", i, pObj->timeArr, pObj->timeReq );

    // print CO info
    pPrev = p->pCos;
    Tim_ManForEachPo( p, pObj, i )
        if ( pPrev->timeArr != pObj->timeArr || pPrev->timeReq != pObj->timeReq )
            break;
    if ( i == Tim_ManCoNum(p) )
        printf( "All POs :  arr = %5.3f  req = %5.3f\n", pPrev->timeArr, pPrev->timeReq );
    else
        Tim_ManForEachPo( p, pObj, i )
            printf( "PO%5d :  arr = %5.3f  req = %5.3f\n", i, pObj->timeArr, pObj->timeReq );

    // print box info
    Tim_ManForEachBox( p, pBox, i )
    {
        printf( "*** Box %3d :  Ins = %d. Outs = %d.\n", i, pBox->nInputs, pBox->nOutputs );
        printf( "Delay table:\n" );
        pTable = Tim_ManBoxDelayTable( p, pBox->iBox );
        for ( i = 0; i < pBox->nOutputs; i++, printf( "\n" ) )
            for ( k = 0; k < pBox->nInputs; k++ )
                if ( pTable[3+i*pBox->nInputs+k] == -ABC_INFINITY )
                    printf( "%5s", "-" );
                else
                    printf( "%5.0f", pTable[3+i*pBox->nInputs+k] );
        printf( "\n" );

        // print box inputs
        pPrev = Tim_ManBoxInput( p, pBox, 0 );
        Tim_ManBoxForEachInput( p, pBox, pObj, i )
            if ( pPrev->timeArr != pObj->timeArr || pPrev->timeReq != pObj->timeReq )
                break;
        if ( i == Tim_ManBoxInputNum(p, pBox->iBox) )
            printf( "Box inputs  :  arr = %5.3f  req = %5.3f\n", pPrev->timeArr, pPrev->timeReq );
        else
            Tim_ManBoxForEachInput( p, pBox, pObj, i )
                printf( "box-inp%3d :  arr = %5.3f  req = %5.3f\n", i, pObj->timeArr, pObj->timeReq );

        // print box outputs
        pPrev = Tim_ManBoxOutput( p, pBox, 0 );
        Tim_ManBoxForEachOutput( p, pBox, pObj, i )
            if ( pPrev->timeArr != pObj->timeArr || pPrev->timeReq != pObj->timeReq )
                break;
        if ( i == Tim_ManBoxOutputNum(p, pBox->iBox) )
            printf( "Box outputs :  arr = %5.3f  req = %5.3f\n", pPrev->timeArr, pPrev->timeReq );
        else
            Tim_ManBoxForEachOutput( p, pBox, pObj, i )
                printf( "box-out%3d :  arr = %5.3f  req = %5.3f\n", i, pObj->timeArr, pObj->timeReq );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Read parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Tim_ManCiNum( Tim_Man_t * p )
{
    return p->nCis;
}
int Tim_ManCoNum( Tim_Man_t * p )
{
    return p->nCos;
}
int Tim_ManPiNum( Tim_Man_t * p )
{
    return Tim_ManBoxOutputFirst(p, 0);
}
int Tim_ManPoNum( Tim_Man_t * p )
{
    int iLastBoxId = Tim_ManBoxNum(p) - 1;
    return Tim_ManCoNum(p) - (Tim_ManBoxInputFirst(p, iLastBoxId) + Tim_ManBoxInputNum(p, iLastBoxId));
}
int Tim_ManBoxNum( Tim_Man_t * p )
{
    return Vec_PtrSize(p->vBoxes);
}
int Tim_ManDelayTableNum( Tim_Man_t * p )
{
    return Vec_PtrSize(p->vDelayTables);
}

/**Function*************************************************************

  Synopsis    [Sets the vector of timing tables associated with the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManSetDelayTables( Tim_Man_t * p, Vec_Ptr_t * vDelayTables )
{
    assert( p->vDelayTables == NULL );
    p->vDelayTables = vDelayTables;
}

/**Function*************************************************************

  Synopsis    [Disables the use of the traversal ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManTravIdDisable( Tim_Man_t * p )
{
    p->fUseTravId = 0;
}

/**Function*************************************************************

  Synopsis    [Enables the use of the traversal ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Tim_ManTravIdEnable( Tim_Man_t * p )
{
    p->fUseTravId = 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

