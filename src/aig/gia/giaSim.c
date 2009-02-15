/**CFile****************************************************************

  FileName    [giaSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Fast sequential simulator.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSim.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Gia_ManSim_t_ Gia_ManSim_t;
struct Gia_ManSim_t_
{
    Gia_Man_t *    pAig;
    Gia_ParSim_t * pPars; 
    int            nWords;
    Vec_Int_t *    vCis2Ids;
    // simulation information
    unsigned *     pDataSim;     // simulation data
    unsigned *     pDataSimCis;  // simulation data for CIs
    unsigned *     pDataSimCos;  // simulation data for COs
};

static inline unsigned * Gia_SimData( Gia_ManSim_t * p, int i )    { return p->pDataSim + i * p->nWords;    }
static inline unsigned * Gia_SimDataCi( Gia_ManSim_t * p, int i )  { return p->pDataSimCis + i * p->nWords; }
static inline unsigned * Gia_SimDataCo( Gia_ManSim_t * p, int i )  { return p->pDataSimCos + i * p->nWords; }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSimSetDefaultParams( Gia_ParSim_t * p )
{
    memset( p, 0, sizeof(Gia_ParSim_t) );
    // user-controlled parameters
    p->nWords       =   8;    // the number of machine words
    p->nIters       =  32;    // the number of timeframes
    p->TimeLimit    =  60;    // time limit in seconds
    p->fCheckMiter  =   0;    // check if miter outputs are non-zero 
    p->fVerbose     =   1;    // enables verbose output
}

/**Function*************************************************************

  Synopsis    [Creates fast simulation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_ManSim_t * Gia_ManSimCreate( Gia_Man_t * pAig, Gia_ParSim_t * pPars )
{
    Gia_ManSim_t * p;
    int Entry, i;
    p = ABC_ALLOC( Gia_ManSim_t, 1 );
    memset( p, 0, sizeof(Gia_ManSim_t) );
    p->pAig   = Gia_ManFront( pAig );
    p->pPars  = pPars;
    p->nWords = pPars->nWords;
    p->pDataSim = ABC_ALLOC( unsigned, p->nWords * p->pAig->nFront );
    p->pDataSimCis = ABC_ALLOC( unsigned, p->nWords * Gia_ManCiNum(p->pAig) );
    p->pDataSimCos = ABC_ALLOC( unsigned, p->nWords * Gia_ManCoNum(p->pAig) );
    p->vCis2Ids = Vec_IntAlloc( Gia_ManCiNum(p->pAig) );
    Vec_IntForEachEntry( pAig->vCis, Entry, i )
        Vec_IntPush( p->vCis2Ids, Entry );  
    printf( "AIG = %7.2f Mb.   Front mem = %7.2f Mb.  Other mem = %7.2f Mb.\n", 
        12.0*Gia_ManObjNum(p->pAig)/(1<<20), 
        4.0*p->nWords*p->pAig->nFront/(1<<20), 
        4.0*p->nWords*(Gia_ManCiNum(p->pAig) + Gia_ManCoNum(p->pAig))/(1<<20) );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSimDelete( Gia_ManSim_t * p )
{
    Vec_IntFree( p->vCis2Ids );
    Gia_ManStop( p->pAig );
    ABC_FREE( p->pDataSim );
    ABC_FREE( p->pDataSimCis );
    ABC_FREE( p->pDataSimCos );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimInfoRandom( Gia_ManSim_t * p, unsigned * pInfo )
{
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = Aig_ManRandom( 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimInfoZero( Gia_ManSim_t * p, unsigned * pInfo )
{
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = 0;
}

/**Function*************************************************************

  Synopsis    [Returns index of the first pattern that failed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_ManSimInfoIsZero( Gia_ManSim_t * p, unsigned * pInfo )
{
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        if ( pInfo[w] )
            return 32*(w-1) + Aig_WordFindFirstBit( pInfo[w] );
    return -1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimInfoOne( Gia_ManSim_t * p, unsigned * pInfo )
{
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = ~0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimInfoCopy( Gia_ManSim_t * p, unsigned * pInfo, unsigned * pInfo0 )
{
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = pInfo0[w];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimulateCi( Gia_ManSim_t * p, Gia_Obj_t * pObj, int iCi )
{
    unsigned * pInfo  = Gia_SimData( p, Gia_ObjValue(pObj) );
    unsigned * pInfo0 = Gia_SimDataCi( p, iCi );
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = pInfo0[w];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimulateCo( Gia_ManSim_t * p, int iCo, Gia_Obj_t * pObj )
{
    unsigned * pInfo  = Gia_SimDataCo( p, iCo );
    unsigned * pInfo0 = Gia_SimData( p, Gia_ObjDiff0(pObj) );
    int w;
    if ( Gia_ObjFaninC0(pObj) )
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] = ~pInfo0[w];
    else 
        for ( w = p->nWords-1; w >= 0; w-- )
            pInfo[w] = pInfo0[w];
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimulateNode( Gia_ManSim_t * p, Gia_Obj_t * pObj )
{
    unsigned * pInfo  = Gia_SimData( p, Gia_ObjValue(pObj) );
    unsigned * pInfo0 = Gia_SimData( p, Gia_ObjDiff0(pObj) );
    unsigned * pInfo1 = Gia_SimData( p, Gia_ObjDiff1(pObj) );
    int w;
    if ( Gia_ObjFaninC0(pObj) )
    {
        if (  Gia_ObjFaninC1(pObj) )
            for ( w = p->nWords-1; w >= 0; w-- )
                pInfo[w] = ~(pInfo0[w] | pInfo1[w]);
        else 
            for ( w = p->nWords-1; w >= 0; w-- )
                pInfo[w] = ~pInfo0[w] & pInfo1[w];
    }
    else 
    {
        if (  Gia_ObjFaninC1(pObj) )
            for ( w = p->nWords-1; w >= 0; w-- )
                pInfo[w] = pInfo0[w] & ~pInfo1[w];
        else 
            for ( w = p->nWords-1; w >= 0; w-- )
                pInfo[w] = pInfo0[w] & pInfo1[w];
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimInfoInit( Gia_ManSim_t * p )
{
    int iPioNum, i;
    Vec_IntForEachEntry( p->vCis2Ids, iPioNum, i )
    {
        if ( iPioNum < Gia_ManPiNum(p->pAig) )
            Gia_ManSimInfoRandom( p, Gia_SimDataCi(p, i) );
        else
            Gia_ManSimInfoZero( p, Gia_SimDataCi(p, i) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimInfoTransfer( Gia_ManSim_t * p )
{
    int iPioNum, i;
    Vec_IntForEachEntry( p->vCis2Ids, iPioNum, i )
    {
        if ( iPioNum < Gia_ManPiNum(p->pAig) )
            Gia_ManSimInfoRandom( p, Gia_SimDataCi(p, i) );
        else
            Gia_ManSimInfoCopy( p, Gia_SimDataCi(p, i), Gia_SimDataCo(p, Gia_ManPoNum(p->pAig)+iPioNum-Gia_ManPiNum(p->pAig)) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSimulateRound( Gia_ManSim_t * p )
{
    Gia_Obj_t * pObj;
    int i, iCis = 0, iCos = 0;
    assert( p->pAig->nFront > 0 );
    assert( Gia_ManConst0(p->pAig)->Value == 0 );
    Gia_ManSimInfoZero( p, Gia_SimData(p, 0) );
    Gia_ManForEachObj1( p->pAig, pObj, i )
    {
        if ( Gia_ObjIsAndOrConst0(pObj) )
        {
            assert( Gia_ObjValue(pObj) < p->pAig->nFront );
            Gia_ManSimulateNode( p, pObj );
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            assert( Gia_ObjValue(pObj) == GIA_NONE );
            Gia_ManSimulateCo( p, iCos++, pObj );
        }
        else // if ( Gia_ObjIsCi(pObj) )
        {
            assert( Gia_ObjValue(pObj) < p->pAig->nFront );
            Gia_ManSimulateCi( p, pObj, iCis++ );
        }
    }
    assert( Gia_ManCiNum(p->pAig) == iCis );
    assert( Gia_ManCoNum(p->pAig) == iCos );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManSimSimulate( Gia_Man_t * pAig, Gia_ParSim_t * pPars )
{
    Gia_ManSim_t * p;
    int i, clk = clock();
    p = Gia_ManSimCreate( pAig, pPars );
    Aig_ManRandom( 1 );
    Gia_ManSimInfoInit( p );
    for ( i = 0; i < pPars->nIters; i++ )
    {
        Gia_ManSimulateRound( p );
/*
        if ( pPars->fVerbose )
        {
            printf( "Frame %4d out of %4d and timeout %3d sec. ", i+1, pPars->nIters, pPars->TimeLimit );
            printf( "Time = %7.2f sec\r", (1.0*clock()-clkTotal)/CLOCKS_PER_SEC );
        }
        if ( pPars->fCheckMiter && Gia_ManCheckPos( p, &iOut, &iPat ) )
        {
            assert( pAig->pSeqModel == NULL );
            pAig->pSeqModel = Gia_ManGenerateCounter( pAig, i, iOut, p->nWords, iPat, p->vCis2Ids );
            if ( pPars->fVerbose )
            printf( "Miter is satisfiable after simulation (output %d).\n", iOut );
            break;
        }
        if ( (clock() - clkTotal)/CLOCKS_PER_SEC >= pPars->TimeLimit )
        {
            printf( "No bug detected after %d frames with time limit %d seconds.\n", i+1, pPars->TimeLimit );
            break;
        }
*/
        if ( i < pPars->nIters - 1 )
            Gia_ManSimInfoTransfer( p );
    }
    Gia_ManSimDelete( p );
    printf( "Simulated %d frames with %d words.  ", pPars->nIters, pPars->nWords );
    ABC_PRT( "Time", clock() - clk );
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


