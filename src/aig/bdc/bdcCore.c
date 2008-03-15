/**CFile****************************************************************

  FileName    [bdcCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Truth-table-based bi-decomposition engine.]

  Synopsis    [The gateway to bi-decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 30, 2007.]

  Revision    [$Id: bdcCore.c,v 1.00 2007/01/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bdcInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocate resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Bdc_Man_t * Bdc_ManAlloc( Bdc_Par_t * pPars )
{
    Bdc_Man_t * p;
    p = ALLOC( Bdc_Man_t, 1 );
    memset( p, 0, sizeof(Bdc_Man_t) );
    assert( pPars->nVarsMax > 2 && pPars->nVarsMax < 16 );
    p->pPars = pPars;
    p->nWords = Kit_TruthWordNum( pPars->nVarsMax );
    p->nDivsLimit = 200;
    // internal nodes
    p->nNodesAlloc = 512;
    p->pNodes = ALLOC( Bdc_Fun_t, p->nNodesAlloc );
    // memory
    p->vMemory = Vec_IntStart( 4 * p->nWords * p->nNodesAlloc );
    // set up hash table
    p->nTableSize = (1 << p->pPars->nVarsMax);
    p->pTable = ALLOC( Bdc_Fun_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Bdc_Fun_t *) * p->nTableSize );
    p->vSpots = Vec_IntAlloc( 256 );
    // truth tables
    p->vTruths = Vec_PtrAllocTruthTables( p->pPars->nVarsMax );
    p->puTemp1 = ALLOC( unsigned, 4 * p->nWords );
    p->puTemp2 = p->puTemp1 + p->nWords;
    p->puTemp3 = p->puTemp2 + p->nWords;
    p->puTemp4 = p->puTemp3 + p->nWords;
    // start the internal ISFs
    p->pIsfOL = &p->IsfOL;  Bdc_IsfStart( p, p->pIsfOL );
    p->pIsfOR = &p->IsfOR;  Bdc_IsfStart( p, p->pIsfOR );
    p->pIsfAL = &p->IsfAL;  Bdc_IsfStart( p, p->pIsfAL );
    p->pIsfAR = &p->IsfAR;  Bdc_IsfStart( p, p->pIsfAR );   
    return p; 
}

/**Function*************************************************************

  Synopsis    [Deallocate resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_ManFree( Bdc_Man_t * p )
{
    if ( p->pPars->fVerbose )
    {
        printf( "Bi-decomposition stats: Calls = %d.  Nodes = %d. Reuse = %d.\n", 
            p->numCalls, p->numNodes, p->numReuse );
        printf( "ANDs = %d.  ORs = %d.  Weak = %d.  Muxes = %d.  Memory = %.2f K\n", 
            p->numAnds, p->numOrs, p->numWeaks, p->numMuxes, 4.0 * Vec_IntSize(p->vMemory) / (1<<10) );
        PRT( "Cache", p->timeCache );
        PRT( "Check", p->timeCheck );
        PRT( "Muxes", p->timeMuxes );
        PRT( "Supps", p->timeSupps );
        PRT( "TOTAL", p->timeTotal );
    }
    Vec_IntFree( p->vMemory );
    Vec_IntFree( p->vSpots );
    Vec_PtrFree( p->vTruths );
    free( p->puTemp1 );
    free( p->pNodes );
    free( p->pTable );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Clears the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_ManPrepare( Bdc_Man_t * p, Vec_Ptr_t * vDivs )
{
    unsigned * puTruth;
    Bdc_Fun_t * pNode;
    int i;
    Bdc_TableClear( p );
    Vec_IntClear( p->vMemory );
    // add constant 1 and elementary vars
    p->nNodes = 0;
    p->nNodesNew = - 1 - p->nVars - (vDivs? Vec_PtrSize(vDivs) : 0);
    // add constant 1
    pNode = Bdc_FunNew( p );
    pNode->Type = BDC_TYPE_CONST1;
    pNode->puFunc = (unsigned *)Vec_IntFetch(p->vMemory, p->nWords); 
    Kit_TruthFill( pNode->puFunc, p->nVars );
    pNode->uSupp = 0;
    Bdc_TableAdd( p, pNode );
    // add variables
    for ( i = 0; i < p->nVars; i++ )
    {
        pNode = Bdc_FunNew( p );
        pNode->Type = BDC_TYPE_PI;
        pNode->puFunc = Vec_PtrEntry( p->vTruths, i );
        pNode->uSupp = (1 << i);
        Bdc_TableAdd( p, pNode );
    }
    // add the divisors
    if ( vDivs )
    Vec_PtrForEachEntry( vDivs, puTruth, i )
    {
        pNode = Bdc_FunNew( p );
        pNode->Type = BDC_TYPE_PI;
        pNode->puFunc = puTruth;
        pNode->uSupp = Kit_TruthSupport( puTruth, p->nVars );
        Bdc_TableAdd( p, pNode );
        if ( i == p->nDivsLimit )
            break;
    }
    assert( p->nNodesNew == 0 );
}

/**Function*************************************************************

  Synopsis    [Clears the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_ManDecPrint( Bdc_Man_t * p )
{
    Bdc_Fun_t * pNode;
    int i;
    printf( " 0 : Const 1\n" );
    for ( i = 1; i < p->nNodes; i++ )
    {
        printf( " %d : ", i );
        pNode = p->pNodes + i;
        if ( pNode->Type == BDC_TYPE_PI )
            printf( "PI   " );
        else
        {
            printf( "%s%d &", Bdc_IsComplement(pNode->pFan0)? "-":"", Bdc_FunId(p,Bdc_Regular(pNode->pFan0)) );
            printf( " %s%d   ", Bdc_IsComplement(pNode->pFan1)? "-":"", Bdc_FunId(p,Bdc_Regular(pNode->pFan1)) );
        }
        Extra_PrintBinary( stdout, pNode->puFunc, (1<<p->nVars) );
        printf( "\n" );
    }
    printf( "Root = %s%d.\n", Bdc_IsComplement(p->pRoot)? "-":"", Bdc_FunId(p,Bdc_Regular(p->pRoot)) );
}

/**Function*************************************************************

  Synopsis    [Performs decomposition of one function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bdc_ManDecompose( Bdc_Man_t * p, unsigned * puFunc, unsigned * puCare, int nVars, Vec_Ptr_t * vDivs, int nNodesMax )
{
    Bdc_Isf_t Isf, * pIsf = &Isf;
    int clk = clock();
    assert( nVars <= p->pPars->nVarsMax );
    // set current manager parameters
    p->nVars = nVars;
    p->nWords = Kit_TruthWordNum( nVars );
    p->nNodesMax = nNodesMax;
    Bdc_ManPrepare( p, vDivs );
    // copy the function
    Bdc_IsfStart( p, pIsf );
    if ( puCare )
    {
        Kit_TruthAnd( pIsf->puOn, puCare, puFunc, p->nVars );
        Kit_TruthSharp( pIsf->puOff, puCare, puFunc, p->nVars );
    }
    else
    {
        Kit_TruthCopy( pIsf->puOn, puFunc, p->nVars );
        Kit_TruthNot( pIsf->puOff, puFunc, p->nVars );
    }
    Bdc_SuppMinimize( p, pIsf );
    // call decomposition
    p->pRoot = Bdc_ManDecompose_rec( p, pIsf );
    p->timeTotal += clock() - clk;
    p->numCalls++;
    p->numNodes += p->nNodesNew;
    if ( p->pRoot == NULL )
        return -1;
    if ( !Bdc_ManNodeVerify( p, pIsf, p->pRoot ) )
        printf( "Bdc_ManDecompose(): Internal verification failed.\n" );
//    assert( Bdc_ManNodeVerify( p, pIsf, p->pRoot ) );
    return p->nNodesNew;
}

/**Function*************************************************************

  Synopsis    [Performs decomposition of one function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bdc_ManDecomposeTest( unsigned uTruth, int nVars )
{
    static int Counter = 0;
    static int Total = 0;
    Bdc_Par_t Pars = {0}, * pPars = &Pars;
    Bdc_Man_t * p;
    int RetValue;
//    unsigned uCare = ~0x888f888f;
    unsigned uCare = ~0;
//    unsigned uFunc =  0x88888888;
//    unsigned uFunc =  0xf888f888;
//    unsigned uFunc =  0x117e117e;
//    unsigned uFunc =  0x018b018b;
    unsigned uFunc = uTruth; 

    pPars->nVarsMax = 8;
    p = Bdc_ManAlloc( pPars );
    RetValue = Bdc_ManDecompose( p, &uFunc, &uCare, nVars, NULL, 1000 );
    Total += RetValue;
    printf( "%5d : Nodes = %5d. Total = %8d.\n", ++Counter, RetValue, Total );
//    Bdc_ManDecPrint( p );
    Bdc_ManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


