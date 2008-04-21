/**CFile****************************************************************

  FileName    [nwkMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Logic network representation.]
 
  Synopsis    [Network manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nwkMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "nwk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Nwk_Man_t * Nwk_ManAlloc()
{
    Nwk_Man_t * p;
    p = ALLOC( Nwk_Man_t, 1 );
    memset( p, 0, sizeof(Nwk_Man_t) );
    p->vCis = Vec_PtrAlloc( 1000 );
    p->vCos = Vec_PtrAlloc( 1000 );
    p->vObjs = Vec_PtrAlloc( 1000 );
    p->vTemp = Vec_PtrAlloc( 1000 );
    p->nFanioPlus = 2;
    p->pMemObjs = Aig_MmFlexStart();
    p->pManHop = Hop_ManStart();
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManFree( Nwk_Man_t * p )
{
//    printf( "The number of realloced nodes = %d.\n", p->nRealloced );
    if ( p->pName )    free( p->pName );
    if ( p->pSpec )    free( p->pSpec );
    if ( p->vCis )     Vec_PtrFree( p->vCis );
    if ( p->vCos )     Vec_PtrFree( p->vCos );
    if ( p->vObjs )    Vec_PtrFree( p->vObjs );
    if ( p->vTemp )    Vec_PtrFree( p->vTemp );
    if ( p->pManTime ) Tim_ManStop( p->pManTime );
    if ( p->pMemObjs ) Aig_MmFlexStop( p->pMemObjs, 0 );
    if ( p->pManHop )  Hop_ManStop( p->pManHop );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Prints stats of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManPrintLutSizes( Nwk_Man_t * p, If_Lib_t * pLutLib )
{
    Nwk_Obj_t * pObj;
    int i, Counters[256] = {0};
    Nwk_ManForEachNode( p, pObj, i )
        Counters[Nwk_ObjFaninNum(pObj)]++;
    printf( "LUTs by size: " );
    for ( i = 0; i <= pLutLib->LutMax; i++ )
        printf( "%d:%d ", i, Counters[i] );
}

/**Function*************************************************************

  Synopsis    [If the network is best, saves it in "best.blif" and returns 1.]

  Description [If the networks are incomparable, saves the new network, 
  returns its parameters in the internal parameter structure, and returns 1.
  If the new network is not a logic network, quits without saving and returns 0.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Nwk_ManCompareAndSaveBest( Nwk_Man_t * pNtk, void * pNtl )
{
    extern void Ioa_WriteBlifLogic( Nwk_Man_t * pNtk, void * pNtl, char * pFileName );
    static struct ParStruct {
        char * pName;  // name of the best saved network
        int    Depth;  // depth of the best saved network
        int    Flops;  // flops in the best saved network 
        int    Nodes;  // nodes in the best saved network
        int    nPis;   // the number of primary inputs
        int    nPos;   // the number of primary outputs
    } ParsNew, ParsBest = { 0 };
    // free storage for the name
    if ( pNtk == NULL )
    {
        FREE( ParsBest.pName );
        return 0;
    }
    // get the parameters
    ParsNew.Depth = Nwk_ManLevel( pNtk );
    ParsNew.Flops = Nwk_ManLatchNum( pNtk );
    ParsNew.Nodes = Nwk_ManNodeNum( pNtk );
    ParsNew.nPis  = Nwk_ManPiNum( pNtk );
    ParsNew.nPos  = Nwk_ManPoNum( pNtk );
    // reset the parameters if the network has the same name
    if ( ParsBest.pName == NULL || 
         strcmp(ParsBest.pName, pNtk->pName) ||
         ParsBest.Depth >  ParsNew.Depth || 
         ParsBest.Depth == ParsNew.Depth && ParsBest.Flops >  ParsNew.Flops || 
         ParsBest.Depth == ParsNew.Depth && ParsBest.Flops == ParsNew.Flops && ParsBest.Nodes >  ParsNew.Nodes )
    {
        FREE( ParsBest.pName );
        ParsBest.pName = Aig_UtilStrsav( pNtk->pName );
        ParsBest.Depth = ParsNew.Depth; 
        ParsBest.Flops = ParsNew.Flops; 
        ParsBest.Nodes = ParsNew.Nodes; 
        ParsBest.nPis  = ParsNew.nPis; 
        ParsBest.nPos  = ParsNew.nPos;
        // writ the network
        Ioa_WriteBlifLogic( pNtk, pNtl, "best.blif" );
        return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Nwk_FileNameGeneric( char * FileName )
{
    char * pDot;
    char * pUnd;
    char * pRes;
    // find the generic name of the file
    pRes = Aig_UtilStrsav( FileName );
    // find the pointer to the "." symbol in the file name
//  pUnd = strstr( FileName, "_" );
    pUnd = NULL;
    pDot = strstr( FileName, "." );
    if ( pUnd )
        pRes[pUnd - FileName] = 0;
    else if ( pDot )
        pRes[pDot - FileName] = 0;
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Prints stats of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nwk_ManPrintStats( Nwk_Man_t * pNtk, If_Lib_t * pLutLib, int fSaveBest, int fDumpResult, void * pNtl )
{
    extern int Ntl_ManLatchNum( void * p );
    extern void Ioa_WriteBlifLogic( Nwk_Man_t * pNtk, void * pNtl, char * pFileName );
    if ( fSaveBest )
        Nwk_ManCompareAndSaveBest( pNtk, pNtl );
    if ( fDumpResult )
    {
        char Buffer[1000] = {0};
        char * pNameGen = pNtk->pSpec? Nwk_FileNameGeneric( pNtk->pSpec ) : "nameless_";
        sprintf( Buffer, "%s_dump.blif", pNameGen );
        Ioa_WriteBlifLogic( pNtk, pNtl, Buffer );
        if ( pNtk->pSpec ) free( pNameGen );
    }

    pNtk->pLutLib = pLutLib;
    printf( "%-15s : ",      pNtk->pName );
    printf( "pi = %5d  ",    Nwk_ManPiNum(pNtk) );
    printf( "po = %5d  ",    Nwk_ManPoNum(pNtk) );
    printf( "ci = %5d  ",    Nwk_ManCiNum(pNtk) );
    printf( "co = %5d  ",    Nwk_ManCoNum(pNtk) );
    printf( "lat = %5d  ",   Ntl_ManLatchNum(pNtl) );
    printf( "node = %5d  ",  Nwk_ManNodeNum(pNtk) );
    printf( "edge = %5d  ",  Nwk_ManGetTotalFanins(pNtk) );
    printf( "aig = %6d  ",   Nwk_ManGetAigNodeNum(pNtk) );
    printf( "lev = %3d  ",   Nwk_ManLevel(pNtk) );
//    printf( "lev2 = %3d  ",  Nwk_ManLevelBackup(pNtk) );
    printf( "delay = %5.2f   ", Nwk_ManDelayTraceLut(pNtk) );
    Nwk_ManPrintLutSizes( pNtk, pLutLib );
    printf( "\n" );
//    Nwk_ManDelayTracePrint( pNtk, pLutLib );
    fflush( stdout );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


