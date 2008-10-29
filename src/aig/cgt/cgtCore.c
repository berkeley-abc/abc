/**CFile****************************************************************

  FileName    [cgtCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Clock gating package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cgtCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cgtInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_SetDefaultParams( Cgt_Par_t * p )
{
    memset( p, 0, sizeof(Cgt_Par_t) );
    p->nLevelMax  =  1000;   // the max number of levels to look for clock-gates
    p->nCandMax   =  1000;   // the max number of candidates at each node
    p->nOdcMax    =     0;   // the max number of ODC levels to consider
    p->nConfMax   =  1000;   // the max number of conflicts at a node
    p->nVarsMin   =  5000;   // the min number of vars to recycle the SAT solver
    p->nFlopsMin  =    25;   // the min number of flops to recycle the SAT solver
    p->fVerbose   =     0;   // verbosity flag
}

/**Function*************************************************************

  Synopsis    [Returns 1 if simulation does not filter out this candidate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cgt_SimulationFilter( Cgt_Man_t * p, Aig_Obj_t * pCandFrame, Aig_Obj_t * pMiterFrame )
{
    unsigned * pInfoCand, * pInfoMiter;
    int w, nWords = Aig_BitWordNum( p->nPatts );  
    pInfoCand  = Vec_PtrEntry( p->vPatts, Aig_ObjId(Aig_Regular(pCandFrame)) );
    pInfoMiter = Vec_PtrEntry( p->vPatts, Aig_ObjId(pMiterFrame) );
    // C => !M -- true   is the same as    C & M -- false
    if ( !Aig_IsComplement(pCandFrame) )
    {
        for ( w = 0; w < nWords; w++ )
            if ( pInfoCand[w] & pInfoMiter[w] )
                return 0;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( ~pInfoCand[w] & pInfoMiter[w] )
                return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Saves one simulation pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_SimulationRecord( Cgt_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManForEachObj( p->pPart, pObj, i )
        if ( sat_solver_var_value( p->pSat, p->pCnf->pVarNums[i] ) )
            Aig_InfoSetBit( Vec_PtrEntry(p->vPatts, i), p->nPatts );
    p->nPatts++;
    if ( p->nPatts == 32 * p->nPattWords )
    {
        Vec_PtrReallocSimInfo( p->vPatts );
        p->nPattWords *= 2;
    }
}

/**Function*************************************************************

  Synopsis    [Performs clock-gating for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_ClockGatingRangeCheck( Cgt_Man_t * p, int iStart )
{
    Vec_Ptr_t * vNodes = p->vFanout;
    Aig_Obj_t * pMiter, * pCand, * pMiterFrame, * pCandFrame, * pMiterPart, * pCandPart;
    int i, k, RetValue;
    assert( Vec_VecSize(p->vGatesAll) == Aig_ManPoNum(p->pFrame) );
    // go through all the registers inputs of this range
    for ( i = iStart; i < iStart + Aig_ManPoNum(p->pPart); i++ )
    {
        pMiter = Saig_ManLi( p->pAig, i );
        Cgt_ManDetectCandidates( p->pAig, Aig_ObjFanin0(pMiter), p->pPars->nLevelMax, vNodes );
        // go through the candidates of this PO
        Vec_PtrForEachEntry( vNodes, pCand, k )
        {
            // get the corresponding nodes from the frames
            pCandFrame  = pCand->pData;
            pMiterFrame = pMiter->pData;
            // get the corresponding nodes from the part
            pCandPart   = pCandFrame->pData;
            pMiterPart  = pMiterFrame->pData;
            // try direct polarity
            if ( Cgt_SimulationFilter( p, pCandPart, pMiterPart ) )
            {
                RetValue = Cgt_CheckImplication( p, pCandPart, pMiterPart );
                if ( RetValue == 1 )
                {
                    Vec_VecPush( p->vGatesAll, i, pCand );
                    continue;
                }
                if ( RetValue == 0 )
                    Cgt_SimulationRecord( p );
            }
            // try reverse polarity
            if ( Cgt_SimulationFilter( p, Aig_Not(pCandPart), pMiterPart ) )
            {
                RetValue = Cgt_CheckImplication( p, Aig_Not(pCandPart), pMiterPart );
                if ( RetValue == 1 )
                {
                    Vec_VecPush( p->vGatesAll, i, Aig_Not(pCand) );
                    continue;
                }
                if ( RetValue == 0 )
                    Cgt_SimulationRecord( p );
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    [Performs clock-gating for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cgt_ClockGatingRange( Cgt_Man_t * p, int iStart )
{
    int iStop;
    p->pPart = Cgt_ManDupPartition( p->pFrame, p->pPars->nVarsMin, p->pPars->nFlopsMin, iStart );
    p->pCnf  = Cnf_DeriveSimple( p->pPart, Aig_ManPoNum(p->pPart) );
    p->pSat  = Cnf_DataWriteIntoSolver( p->pCnf, 1, 0 );
    sat_solver_compress( p->pSat );
    p->vPatts = Vec_PtrAllocSimInfo( Aig_ManObjNumMax(p->pPart), 16 );
    Vec_PtrCleanSimInfo( p->vPatts, 0, p->nPattWords );
    Cgt_ClockGatingRangeCheck( p, iStart );
    iStop = iStart + Aig_ManPoNum(p->pPart);
    Cgt_ManClean( p );
    return iStop;
}

/**Function*************************************************************

  Synopsis    [Performs clock-gating for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Vec_t * Cgt_ClockGatingCandidates( Aig_Man_t * pAig, Aig_Man_t * pCare, Cgt_Par_t * pPars )
{
    Cgt_Par_t Pars;
    Cgt_Man_t * p;
    Vec_Vec_t * vGatesAll;
    int iStart;
    if ( pPars == NULL )
        Cgt_SetDefaultParams( pPars = &Pars );    
    p = Cgt_ManCreate( pAig, pCare, pPars );
    p->pFrame = Cgt_ManDeriveAigForGating( p );
    assert( Aig_ManPoNum(p->pFrame) == Saig_ManRegNum(p->pAig) );
    for ( iStart = 0; iStart < Aig_ManPoNum(p->pFrame); )
        iStart = Cgt_ClockGatingRange( p, iStart );
    vGatesAll = p->vGatesAll;
    return vGatesAll;
}

/**Function*************************************************************

  Synopsis    [Performs clock-gating for the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Cgt_ClockGating( Aig_Man_t * pAig, Aig_Man_t * pCare, Cgt_Par_t * pPars )
{
    Aig_Man_t * pGated;
    Vec_Vec_t * vGatesAll;
    Vec_Ptr_t * vGates;
    vGatesAll = Cgt_ClockGatingCandidates( pAig, pCare, pPars );
    vGates = Cgt_ManDecideSimple( pAig, vGatesAll );
    pGated = Cgt_ManDeriveGatedAig( pAig, vGates );
    Vec_PtrFree( vGates );
    Vec_VecFree( vGatesAll );
    return pGated;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


