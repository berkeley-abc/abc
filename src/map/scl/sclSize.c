/**CFile****************************************************************

  FileName    [sclSize.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  Synopsis    [Standard-cell library representation.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclSize.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "map/mio/mio.h"
#include "sclInt.h"
#include "sclMan.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect TFO of the fanins of the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclCollectTfo_rec( Abc_Obj_t * pObj, Vec_Int_t * vVisited )
{
    Abc_Obj_t * pNext;
    int i;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    Abc_ObjForEachFanout( pObj, pNext, i )
        Abc_SclCollectTfo_rec( pNext, vVisited );
    Vec_IntPush( vVisited, Abc_ObjId(pObj) );
}
Vec_Int_t * Abc_SclCollectTfo( Abc_Ntk_t * p, Abc_Obj_t * pObj )
{
    Vec_Int_t * vVisited;
    Abc_Obj_t * pFanin;
    int i;
    assert( Abc_ObjIsNode(pObj) );
    vVisited = Vec_IntAlloc( 100 );
    Abc_NtkIncrementTravId( p ); 
    Abc_SclCollectTfo_rec( pObj, vVisited );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        if ( Abc_ObjIsNode(pFanin) )
            Abc_SclCollectTfo_rec( pFanin, vVisited );
    Vec_IntReverseOrder( vVisited );
    return vVisited;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
SC_Cell * Abc_SclObjResiable( SC_Man * p, Abc_Obj_t * pObj )
{
    SC_Cell * pOld = Abc_SclObjCell( p, pObj );
    return pOld->pNext != pOld ? pOld->pNext : NULL;
}
float Abc_SclSizingGain( SC_Man * p, Abc_Obj_t * pPivot )
{
    double dGain = 0;
    Vec_Int_t * vCone;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_ObjIsNode(pPivot) );
    vCone = Abc_SclCollectTfo( p->pNtk, pPivot );
    Abc_SclConeStore( p, vCone );
    Abc_SclTimeCone( p, vCone );
    Abc_NtkForEachObjVec( vCone, p->pNtk, pObj, i )
        if ( Abc_ObjIsCo(pObj) )
            dGain += Abc_SclObjGain( p, pObj );
    Abc_SclConeRestore( p, vCone );
    Vec_IntFree( vCone );
    return dGain;
}
Abc_Obj_t * Abc_SclChooseBiggestGain( SC_Man * p, Vec_Int_t * vPath )
{
    SC_Cell * pOld, * pNew;
    Abc_Obj_t * pPivot = NULL, * pObj;
    double dGainBest = 0, dGain;
    int i, gateId;
    Abc_NtkForEachObjVec( vPath, p->pNtk, pObj, i )
    {
        if ( Abc_ObjIsCo(pObj) )
            continue;
        pOld = Abc_SclObjCell( p, pObj );
        pNew = Abc_SclObjResiable( p, pObj );
        if ( pNew == NULL )
            continue;
printf( "changing %s for %s\n", pOld->name, pNew->name );

        gateId = Vec_IntEntry(p->vGates, Abc_ObjId(pObj));
        Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), Abc_SclCellFind(p->pLib, pNew->name) );
        
        Abc_SclUpdateLoad( p, pObj, pOld, pNew );
        dGain = Abc_SclSizingGain( p, pObj );
        Abc_SclUpdateLoad( p, pObj, pNew, pOld );

        Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), Abc_SclCellFind(p->pLib, pOld->name) );
        assert( gateId == Vec_IntEntry(p->vGates, Abc_ObjId(pObj)) );

        if ( dGainBest < dGain )
        {
            dGainBest = dGain;
            pPivot = pObj;
        }
    }
    return pPivot;
}
void Abc_SclUpdateNetwork( SC_Man * p, Abc_Obj_t * pObj )
{
    Vec_Int_t * vCone;
    SC_Cell * pOld, * pNew;
    // find new gate
    pOld = Abc_SclObjCell( p, pObj );
    pNew = Abc_SclObjResiable( p, pObj );
    assert( pNew != NULL );
    // update gate
    Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), Abc_SclCellFind(p->pLib, pNew->name) );
    pObj->pData = Mio_LibraryReadGateByName( (Mio_Library_t *)p->pNtk->pManFunc, pNew->name );
    Abc_SclUpdateLoad( p, pObj, pOld, pNew );
    p->SumArea += pNew->area - pOld->area;
    // update info
    vCone = Abc_SclCollectTfo( p->pNtk, pObj );
    Abc_SclTimeCone( p, vCone );
    Vec_IntFree( vCone );
}

float Abc_SclFindMaxDelay( SC_Man * p )
{
    float fMaxArr = 0;
    Abc_Obj_t * pObj;
    SC_Pair * pArr;
    int i;
    Abc_NtkForEachCo( p->pNtk, pObj, i )
    {
        pArr = Abc_SclObjTime( p, pObj );
        if ( fMaxArr < pArr->rise )  fMaxArr = pArr->rise;
        if ( fMaxArr < pArr->fall )  fMaxArr = pArr->fall;
    }
    return fMaxArr;
}

void Abc_SclPrintResult( SC_Man * p, int i )
{
    int fRise = 0;
    Abc_Obj_t * pPivot = Abc_SclFindMostCritical( p, &fRise );
    printf( "%5d : ",             i );
    printf( "area =%10.2f   ",    p->SumArea );
    printf( "delay =%8.2f ps   ", Abc_SclObjTimePs(p, pPivot, fRise) );
    Abc_PrintTime( 1, "time",     clock() - p->clkStart );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclSizingPerform( SC_Lib * pLib, void * pNt, int nSteps )
{
    SC_Man * p;
    Abc_Ntk_t * pNtk = (Abc_Ntk_t *)pNt;
    Vec_Int_t * vPath;
    Abc_Obj_t * pBest;
    int i;
    p = Abc_SclManStart( pLib, pNtk );   
    Abc_SclCriticalPathPrint( p );
    for ( i = 0; i < nSteps; i++ )
    {
        vPath = Abc_SclCriticalPathFind( p );
        pBest = Abc_SclChooseBiggestGain( p, vPath );
        Vec_IntFree( vPath );
        if ( pBest == NULL )
            break;
        Abc_SclUpdateNetwork( p, pBest );
        Abc_SclPrintResult( p, i );
    }
    Abc_SclCriticalPathPrint( p );
    Abc_SclManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

