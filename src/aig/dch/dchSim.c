/**CFile****************************************************************

  FileName    [dchSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Computation of equivalence classes using simulation.]

  Synopsis    [Calls to the SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: dchSim.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dchInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline unsigned * Dch_ObjSim( Vec_Ptr_t * vSims, Aig_Obj_t * pObj )
{ 
    return Vec_PtrEntry( vSims, pObj->Id ); 
}
static inline unsigned Dch_ObjRandomSim()    
{ 
    return Aig_ManRandom(0);               
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Perform random simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_PerformRandomSimulation( Aig_Man_t * pAig, Vec_Ptr_t * vSims, int nWords )
{
    unsigned * pSim, * pSim0, * pSim1;
    Aig_Obj_t * pObj;
    int i, k;

    // assign const 1 sim info
    pObj = Aig_ManConst1(pAig);
    pSim = Dch_ObjSim( vSims, pObj );
    memset( pSim, 0xff, sizeof(unsigned) * nWords );

    // assign primary input random sim info
    Aig_ManForEachPi( pAig, pObj, i )
    {
        pSim = Dch_ObjSim( vSims, pObj );
        for ( k = 0; k < nWords; k++ )
            pSim[k] = Dch_ObjRandomSim();
    }

    // simulate AIG in the topological order
    Aig_ManForEachNode( pAig, pObj, i )
    {
        pSim0 = Dch_ObjSim( vSims, Aig_ObjFanin0(pObj) ); 
        pSim1 = Dch_ObjSim( vSims, Aig_ObjFanin1(pObj) ); 
        pSim  = Dch_ObjSim( vSims, pObj );

        if ( Aig_ObjFaninC0(pObj) && Aig_ObjFaninC1(pObj) ) // both are compls
        {
            for ( k = 0; k < nWords; k++ )
                pSim[k] = ~pSim0[k] & ~pSim1[k];
        }
        else if ( Aig_ObjFaninC0(pObj) && !Aig_ObjFaninC1(pObj) ) // first one is compl
        {
            for ( k = 0; k < nWords; k++ )
                pSim[k] = ~pSim0[k] & pSim1[k];
        }
        else if ( !Aig_ObjFaninC0(pObj) && Aig_ObjFaninC1(pObj) ) // second one is compl
        {
            for ( k = 0; k < nWords; k++ )
                pSim[k] = pSim0[k] & ~pSim1[k];
        }
        else // if ( Aig_ObjFaninC0(pObj) && Aig_ObjFaninC1(pObj) ) // none is compl
        {
            for ( k = 0; k < nWords; k++ )
                pSim[k] = pSim0[k] & pSim1[k];
        }
    }

    // get simulation information for primary outputs
}

/**Function*************************************************************

  Synopsis    [Hashing nodes by sim info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_HashNodesBySimulationInfo( Aig_Man_t * pAig, Vec_Ptr_t * vSims, int nWords )
{
    unsigned * pSim0, * pSim1;
    Aig_Obj_t * pObj, * pUnique;
    int i, k, j, nodeId, Counter, c, CountNodes;

    Vec_Int_t * vUniqueNodes, * vNodeCounters;

    vUniqueNodes  = Vec_IntAlloc( 1000 );
    vNodeCounters = Vec_IntStart( Aig_ManObjNumMax(pAig) );

    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( Aig_ObjIsPo(pObj) )
            continue;

        // node's sim info
        pSim0 = Dch_ObjSim( vSims, pObj );

        Vec_IntForEachEntry( vUniqueNodes, nodeId, j )
        {
            pUnique = Aig_ManObj( pAig, nodeId );
            // unique node's sim info
            pSim1 = Dch_ObjSim( vSims, pUnique );

            for ( k = 0; k < nWords; k++ )
                if ( pSim0[k] != pSim1[k] )
                    break;
            if ( k == nWords ) // sim info is same as this node
            {
                Counter = Vec_IntEntry( vNodeCounters, nodeId );
                Vec_IntWriteEntry( vNodeCounters, nodeId, Counter+1 );
                break;
            }
        }

        if ( j == Vec_IntSize(vUniqueNodes) ) // sim info of pObj is unique
        {
            Vec_IntPush( vUniqueNodes, pObj->Id );

            Counter = Vec_IntEntry( vNodeCounters, pObj->Id );
            assert( Counter == 0 );
            Vec_IntWriteEntry( vNodeCounters, pObj->Id, Counter+1 );
        }
    }

    Counter = 0;
    Vec_IntForEachEntry( vNodeCounters, c, k )
        if ( c > 1 )
            Counter++;


    printf( "Detected %d non-trivial candidate equivalence classes for %d nodes.\n", 
        Counter, Vec_IntSize(vUniqueNodes) );

    CountNodes = 0;
    Vec_IntForEachEntry( vUniqueNodes, nodeId, k )
    {
        if (  Vec_IntEntry( vNodeCounters, nodeId ) == 1 )
            continue;
//        printf( "%d ", Vec_IntEntry( vNodeCounters, nodeId ) );
        CountNodes += Vec_IntEntry( vNodeCounters, nodeId );
    }
//    printf( "\n" );
    printf( "Nodes participating in non-trivial classes = %d.\n", CountNodes );


}

/**Function*************************************************************

  Synopsis    [Derives candidate equivalence classes of AIG nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dch_Cla_t ** Dch_CreateCandEquivClasses( Aig_Man_t * pAig, int nWords, int fVerbose )
{
    Dch_Cla_t ** ppClasses;  // place for equivalence classes
    Aig_MmFlex_t * pMemCla;  // memory for equivalence classes
    Vec_Ptr_t * vSims;

    // start storage for equivalence classes
    ppClasses  = CALLOC( Dch_Cla_t *, Aig_ManObjNumMax(pAig) );
    pMemCla = Aig_MmFlexStart();

    // allocate simulation information
    vSims = Vec_PtrAllocSimInfo( Aig_ManObjNumMax(pAig), nWords );

    // run simulation
    Dch_PerformRandomSimulation( pAig, vSims, nWords );

    // hash nodes by sim info
    Dch_HashNodesBySimulationInfo( pAig, vSims, nWords );

    // collect equivalence classes
//    ppClasses = NULL;

    // clean up and return
    Aig_MmFlexStop( pMemCla, 0 );
    Vec_PtrFree( vSims );
    return ppClasses;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


