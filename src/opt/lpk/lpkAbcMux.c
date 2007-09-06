/**CFile****************************************************************

  FileName    [lpkAbcMux.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Fast Boolean matching for LUT structures.]

  Synopsis    [LUT-decomposition based on recursive MUX decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: lpkAbcMux.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lpkInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes cofactors w.r.t. the given var.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lpk_FunComputeCofs( Lpk_Fun_t * p, int iVar )
{
    unsigned * pTruth  = Lpk_FunTruth( p, 0 );
    unsigned * pTruth0 = Lpk_FunTruth( p, 1 );
    unsigned * pTruth1 = Lpk_FunTruth( p, 2 );
    Kit_TruthCofactor0New( pTruth0, pTruth, p->nVars, iVar );
    Kit_TruthCofactor1New( pTruth1, pTruth, p->nVars, iVar );
}

/**Function*************************************************************

  Synopsis    [Computes cofactors w.r.t. each variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lpk_FunComputeCofSupps( Lpk_Fun_t * p, unsigned * puSupps )
{
    unsigned * pTruth  = Lpk_FunTruth( p, 0 );
    unsigned * pTruth0 = Lpk_FunTruth( p, 1 );
    unsigned * pTruth1 = Lpk_FunTruth( p, 2 );
    int Var;
    Lpk_SuppForEachVar( p->uSupp, Var )
    {
        Lpk_FunComputeCofs( p, Var );
        puSupps[2*Var+0] = Kit_TruthSupport( pTruth0, p->nVars );
        puSupps[2*Var+1] = Kit_TruthSupport( pTruth1, p->nVars );
    }
}

/**Function*************************************************************

  Synopsis    [Checks the possibility of MUX decomposition.]

  Description [Returns the best variable to use for MUX decomposition.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Lpk_Res_t * Lpk_MuxAnalize( Lpk_Fun_t * p )
{
    static Lpk_Res_t Res, * pRes = &Res;
    unsigned puSupps[32];
    int nSuppSize0, nSuppSize1, nSuppSizeBest;
    int Var, Area, Polarity, Delay, Delay0, Delay1, DelayA, DelayB;
    memset( pRes, 0, sizeof(Lpk_Res_t) );
    assert( p->uSupp == Kit_BitMask(p->nVars) );
    // get cofactor supports for each variable
    Lpk_FunComputeCofSupps( p, puSupps );
    // derive the delay and area after MUX-decomp with each var - and find the best var
    pRes->Variable = -1;
    Lpk_SuppForEachVar( p->uSupp, Var )
    {
        nSuppSize0 = Kit_WordCountOnes(puSupps[2*Var+0]);
        nSuppSize1 = Kit_WordCountOnes(puSupps[2*Var+1]);
        if ( nSuppSize0 <= (int)p->nLutK - 2 && nSuppSize1 <= (int)p->nLutK - 2 )
        {
            // include cof var into 0-block
            DelayA = Lpk_SuppDelay( puSupps[2*Var+0] | (1<<Var), p->pDelays );
            DelayB = Lpk_SuppDelay( puSupps[2*Var+1]           , p->pDelays );
            Delay0 = ABC_MAX( DelayA, DelayB + 1 );
            // include cof var into 1-block
            DelayA = Lpk_SuppDelay( puSupps[2*Var+1] | (1<<Var), p->pDelays );
            DelayB = Lpk_SuppDelay( puSupps[2*Var+0]           , p->pDelays );
            Delay1 = ABC_MAX( DelayA, DelayB + 1 );
            // get the best delay
            Delay = ABC_MIN( Delay0, Delay1 );
            Area = 2;
            Polarity = (int)(Delay1 == Delay);
        }
        else if ( nSuppSize0 <= (int)p->nLutK - 2 )
        {
            DelayA = Lpk_SuppDelay( puSupps[2*Var+0] | (1<<Var), p->pDelays );
            DelayB = Lpk_SuppDelay( puSupps[2*Var+1]           , p->pDelays );
            Delay = ABC_MAX( DelayA, DelayB + 1 );
            Area = 1 + Lpk_LutNumLuts( nSuppSize1, p->nLutK );
            Polarity = 0;
        }
        else if ( nSuppSize1 <= (int)p->nLutK - 2 )
        {
            DelayA = Lpk_SuppDelay( puSupps[2*Var+1] | (1<<Var), p->pDelays );
            DelayB = Lpk_SuppDelay( puSupps[2*Var+0]           , p->pDelays );
            Delay = ABC_MAX( DelayA, DelayB + 1 );
            Area = 1 + Lpk_LutNumLuts( nSuppSize0, p->nLutK );
            Polarity = 1;
        }
        else if ( nSuppSize0 <= (int)p->nLutK )
        {
            DelayA = Lpk_SuppDelay( puSupps[2*Var+1] | (1<<Var), p->pDelays );
            DelayB = Lpk_SuppDelay( puSupps[2*Var+0]           , p->pDelays );
            Delay = ABC_MAX( DelayA, DelayB + 1 );
            Area = 1 + Lpk_LutNumLuts( nSuppSize1+2, p->nLutK );
            Polarity = 1;
        }
        else if ( nSuppSize1 <= (int)p->nLutK )
        {
            DelayA = Lpk_SuppDelay( puSupps[2*Var+0] | (1<<Var), p->pDelays );
            DelayB = Lpk_SuppDelay( puSupps[2*Var+1]           , p->pDelays );
            Delay = ABC_MAX( DelayA, DelayB + 1 );
            Area = 1 + Lpk_LutNumLuts( nSuppSize0+2, p->nLutK );
            Polarity = 0;
        }
        else
        {
            // include cof var into 0-block
            DelayA = Lpk_SuppDelay( puSupps[2*Var+0] | (1<<Var), p->pDelays );
            DelayB = Lpk_SuppDelay( puSupps[2*Var+1]           , p->pDelays );
            Delay0 = ABC_MAX( DelayA, DelayB + 1 );
            // include cof var into 1-block
            DelayA = Lpk_SuppDelay( puSupps[2*Var+1] | (1<<Var), p->pDelays );
            DelayB = Lpk_SuppDelay( puSupps[2*Var+0]           , p->pDelays );
            Delay1 = ABC_MAX( DelayA, DelayB + 1 );
            // get the best delay
            Delay = ABC_MIN( Delay0, Delay1 );
            if ( Delay == Delay0 )
                Area = Lpk_LutNumLuts( nSuppSize0+2, p->nLutK ) + Lpk_LutNumLuts( nSuppSize1, p->nLutK );
            else
                Area = Lpk_LutNumLuts( nSuppSize1+2, p->nLutK ) + Lpk_LutNumLuts( nSuppSize0, p->nLutK );
            Polarity = (int)(Delay1 == Delay);
        }
        // find the best variable
        if ( Delay > (int)p->nDelayLim )
            continue;
        if ( Area > (int)p->nAreaLim )
            continue;
        if ( pRes->Variable == -1 || pRes->AreaEst > Area || (pRes->AreaEst == Area && nSuppSizeBest > nSuppSize0+nSuppSize1) )
        {
            pRes->Variable = Var;
            pRes->Polarity = Polarity;
            pRes->AreaEst  = Area;
            pRes->DelayEst = Delay;
            nSuppSizeBest  = nSuppSize0+nSuppSize1;
        }
    }
    return pRes->Variable == -1 ? NULL : pRes;
}

/**Function*************************************************************

  Synopsis    [Transforms the function decomposed by the MUX decomposition.]

  Description [Returns the best variable to use for MUX decomposition.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Lpk_Fun_t * Lpk_MuxSplit( Lpk_Fun_t * p, int Var, int Pol )
{
    Lpk_Fun_t * pNew;
    unsigned * pTruth  = Lpk_FunTruth( p, 0 );
    unsigned * pTruth0 = Lpk_FunTruth( p, 1 );
    unsigned * pTruth1 = Lpk_FunTruth( p, 2 );
    int iVarVac;
    assert( Var >= 0 && Var < (int)p->nVars );
    assert( p->nAreaLim >= 2 );
    Lpk_FunComputeCofs( p, Var );
    // derive the new component
    pNew = Lpk_FunDup( p, Pol ? pTruth0 : pTruth1 );
    // update the support of the old component
    p->uSupp  = Kit_TruthSupport( Pol ? pTruth1 : pTruth0, p->nVars );
    p->uSupp |= (1 << Var);
    // update the truth table of the old component
    iVarVac = Kit_WordFindFirstBit( ~p->uSupp );
    assert( iVarVac < (int)p->nVars );
    Kit_TruthIthVar( pTruth, p->nVars, Var );
    if ( Pol )
        Kit_TruthMuxVar( pTruth, pTruth, pTruth1, p->nVars, iVarVac );
    else
        Kit_TruthMuxVar( pTruth, pTruth0, pTruth, p->nVars, iVarVac );
    // set the decomposed variable
    p->pFanins[iVarVac] = pNew->Id;
    p->pDelays[iVarVac] = p->nDelayLim - 1;
    // support minimize both
    Lpk_FunSuppMinimize( p );
    Lpk_FunSuppMinimize( pNew );
    // update delay and area requirements
    pNew->nDelayLim = p->nDelayLim - 1;
    if ( p->nVars <= p->nLutK )
    {
        pNew->nAreaLim = p->nAreaLim - 1;
        p->nAreaLim = 1;
    }
    else if ( pNew->nVars <= pNew->nLutK )
    {
        pNew->nAreaLim = 1;
        p->nAreaLim = p->nAreaLim - 1;
    }
    else if ( p->nVars < pNew->nVars )
    {
        pNew->nAreaLim = p->nAreaLim / 2 + p->nAreaLim % 2;
        p->nAreaLim = p->nAreaLim / 2 - p->nAreaLim % 2;
    }
    else // if ( pNew->nVars < p->nVars )
    {
        pNew->nAreaLim = p->nAreaLim / 2 - p->nAreaLim % 2;
        p->nAreaLim = p->nAreaLim / 2 + p->nAreaLim % 2;
    }
    return p;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


