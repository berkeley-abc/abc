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

ABC_NAMESPACE_IMPL_START


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
    p->fVerbose     =   0;    // enables verbose output
    p->iOutFail     =  -1;    // index of the failed output
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSimDelete( Gia_ManSim_t * p )
{
    Vec_IntFreeP( &p->vCis2Ids );
    Gia_ManStopP( &p->pAig );
    ABC_FREE( p->pDataSim );
    ABC_FREE( p->pDataSimCis );
    ABC_FREE( p->pDataSimCos );
    ABC_FREE( p );
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
    if ( !p->pDataSim || !p->pDataSimCis || !p->pDataSimCos )
    { 
        Abc_Print( 1, "Simulator could not allocate %.2f Gb for simulation info.\n", 
            4.0 * p->nWords * (p->pAig->nFront + Gia_ManCiNum(p->pAig) + Gia_ManCoNum(p->pAig)) / (1<<30) );
        Gia_ManSimDelete( p );
        return NULL;
    }
    p->vCis2Ids = Vec_IntAlloc( Gia_ManCiNum(p->pAig) );
    Vec_IntForEachEntry( pAig->vCis, Entry, i )
        Vec_IntPush( p->vCis2Ids, i );  //  do we need p->vCis2Ids?
    if ( pPars->fVerbose )
    Abc_Print( 1, "AIG = %7.2f Mb.   Front mem = %7.2f Mb.  Other mem = %7.2f Mb.\n", 
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
static inline void Gia_ManSimInfoRandom( Gia_ManSim_t * p, unsigned * pInfo )
{
    int w;
    for ( w = p->nWords-1; w >= 0; w-- )
        pInfo[w] = Gia_ManRandom( 0 );
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
    for ( w = 0; w < p->nWords; w++ )
        if ( pInfo[w] )
            return 32*w + Gia_WordFindFirstBit( pInfo[w] );
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

  Synopsis    [Returns index of the PO and pattern that failed it.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_ManCheckPos( Gia_ManSim_t * p, int * piPo, int * piPat )
{
    int i, iPat;
    for ( i = 0; i < Gia_ManPoNum(p->pAig); i++ )
    {
        iPat = Gia_ManSimInfoIsZero( p, Gia_SimDataCo(p, i) );
        if ( iPat >= 0 )
        {
            *piPo = i;
            *piPat = iPat;
            return 1;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Gia_ManGenerateCounter( Gia_Man_t * pAig, int iFrame, int iOut, int nWords, int iPat, Vec_Int_t * vCis2Ids )
{
    Abc_Cex_t * p;
    unsigned * pData;
    int f, i, w, iPioId, Counter;
    p = Gia_ManAllocCounterExample( Gia_ManRegNum(pAig), Gia_ManPiNum(pAig), iFrame+1 );
    p->iFrame = iFrame;
    p->iPo = iOut;
    // fill in the binary data
    Gia_ManRandom( 1 );
    Counter = p->nRegs;
    pData = ABC_ALLOC( unsigned, nWords );
    for ( f = 0; f <= iFrame; f++, Counter += p->nPis )
    for ( i = 0; i < Gia_ManPiNum(pAig); i++ )
    {
        iPioId = Vec_IntEntry( vCis2Ids, i );
        if ( iPioId >= p->nPis )
            continue;
        for ( w = nWords-1; w >= 0; w-- )
            pData[w] = Gia_ManRandom( 0 );
        if ( Gia_InfoHasBit( pData, iPat ) )
            Gia_InfoSetBit( p->pData, Counter + iPioId );
    }
    ABC_FREE( pData );
    return p;
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
    int i, clkTotal = clock();
    int iOut, iPat, RetValue = 0;
    ABC_FREE( pAig->pCexSeq );
    p = Gia_ManSimCreate( pAig, pPars );
    Gia_ManRandom( 1 );
    Gia_ManSimInfoInit( p );
    for ( i = 0; i < pPars->nIters; i++ )
    {
        Gia_ManSimulateRound( p );
        if ( pPars->fVerbose )
        {
            Abc_Print( 1, "Frame %4d out of %4d and timeout %3d sec. ", i+1, pPars->nIters, pPars->TimeLimit );
            Abc_Print( 1, "Time = %7.2f sec\r", (1.0*clock()-clkTotal)/CLOCKS_PER_SEC );
        }
        if ( pPars->fCheckMiter && Gia_ManCheckPos( p, &iOut, &iPat ) )
        {
            pPars->iOutFail = iOut;
            pAig->pCexSeq = Gia_ManGenerateCounter( pAig, i, iOut, p->nWords, iPat, p->vCis2Ids );
            Abc_Print( 1, "Networks are NOT EQUIVALENT.   Output %d was asserted in frame %d.  ", iOut, i );
            if ( !Gia_ManVerifyCounterExample( pAig, pAig->pCexSeq, 0 ) )
            {
//                Abc_Print( 1, "\n" );
                Abc_Print( 1, "\nGenerated counter-example is INVALID.                    " );
//                Abc_Print( 1, "\n" );
            }
            else
            {
//                Abc_Print( 1, "\n" );
//                if ( pPars->fVerbose )
//                Abc_Print( 1, "\nGenerated counter-example is verified correctly.         " );
//                Abc_Print( 1, "\n" );
            }
            RetValue = 1;
            break;
        }
        if ( (clock() - clkTotal)/CLOCKS_PER_SEC >= pPars->TimeLimit )
        {
            i++;
            break;
        }
        if ( i < pPars->nIters - 1 )
            Gia_ManSimInfoTransfer( p );
    }
    Gia_ManSimDelete( p );
    if ( pAig->pCexSeq == NULL )
        Abc_Print( 1, "No bug detected after simulating %d frames with %d words.  ", i, pPars->nWords );
    Abc_PrintTime( 1, "Time", clock() - clkTotal );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

