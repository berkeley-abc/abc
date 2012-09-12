/**CFile****************************************************************

  FileName    [sclUpsize.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Selective increase of gate sizes.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclUpsize.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

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

  Synopsis    [Begin by upsizing gates will many fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SclManUpsize( SC_Man * p, int Degree )
{
    SC_Cell * pOld, * pNew;
    Abc_Obj_t * pObj;
    int i, Count = 0;
    Abc_NtkForEachNode1( p->pNtk, pObj, i )
    {
        if ( Abc_ObjFanoutNum(pObj) < Degree )
            continue;
        // find new gate
        pOld = Abc_SclObjCell( p, pObj );
        pNew = Abc_SclObjResiable( p, pObj, 1 );
        if ( pNew == NULL )
            continue;
        Vec_IntWriteEntry( p->vGates, Abc_ObjId(pObj), Abc_SclCellFind(p->pLib, pNew->pName) );
        Count++;
    }
    return Count;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclUpsizingPerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int Degree, int nRange, int fVerbose )
{
    SC_Man * p;
    int nUpsizes;

    // prepare the manager; collect init stats
    p = Abc_SclManStart( pLib, pNtk, 1 );

    // perform upsizing
    nUpsizes = Abc_SclManUpsize( p, Degree );

    // recompute timing
    Abc_SclTimeNtkRecompute( p, &p->SumArea, &p->MaxDelay );

    // print cumulative statistics
    printf( "Resized: %d. ",     nUpsizes );
    printf( "Delay: " );
    printf( "%.2f -> %.2f ps ",  SC_LibTimePs(p->pLib, p->MaxDelay0), SC_LibTimePs(p->pLib, p->MaxDelay) );
    printf( "(%+.1f %%).  ",     100.0 * (p->MaxDelay - p->MaxDelay0)/ p->MaxDelay0 );
    printf( "Area: " );
    printf( "%.2f -> %.2f ",     p->SumArea0, p->SumArea );
    printf( "(%+.1f %%).  ",     100.0 * (p->SumArea - p->SumArea0)/ p->SumArea0 );
    Abc_PrintTime( 1, "Time",    clock() - p->clkStart );

    // save the result and quit
    Abc_SclManSetGates( pLib, pNtk, p->vGates ); // updates gate pointers
    Abc_SclManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

