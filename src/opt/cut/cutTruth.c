/**CFile****************************************************************

  FileName    [cutTruth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [K-feasible cut computation package.]

  Synopsis    [Incremental truth table computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cutTruth.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cutInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Cut_TruthCompute4( Cut_Man_t * p, Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 );
static void Cut_TruthCompute5( Cut_Man_t * p, Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 );
static void Cut_TruthCompute6( Cut_Man_t * p, Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Cut_TruthPhase( Cut_Cut_t * pCut, Cut_Cut_t * pCut1 )
{
    unsigned uPhase = 0;
    int i, k;
    for ( i = k = 0; i < (int)pCut->nLeaves; i++ )
    {
        if ( k == (int)pCut1->nLeaves )
            break;
        if ( pCut->pLeaves[i] < pCut1->pLeaves[k] )
            continue;
        assert( pCut->pLeaves[i] == pCut1->pLeaves[k] );
        uPhase |= (1 << i);
        k++;
    }
    return uPhase;
}

/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_TruthCompute( Cut_Man_t * p, Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 )
{
int clk = clock();
    if ( pCut->nVarsMax == 4 )
        Cut_TruthCompute4( p, pCut, pCut0, pCut1 );
    else if ( pCut->nVarsMax == 5 )
        Cut_TruthCompute5( p, pCut, pCut0, pCut1 );
    else // if ( pCut->nVarsMax == 6 )
        Cut_TruthCompute6( p, pCut, pCut0, pCut1 );
p->timeTruth += clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_TruthCompute4( Cut_Man_t * p, Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 )
{
    unsigned * puTruthCut0, * puTruthCut1;
    unsigned uTruth0, uTruth1, uPhase;

    puTruthCut0 = Cut_CutReadTruth(pCut0);
    puTruthCut1 = Cut_CutReadTruth(pCut1);

    uPhase  = Cut_TruthPhase( pCut, pCut0 );
    uTruth0 = Extra_TruthPerm4One( *puTruthCut0, uPhase );
    uTruth0 = p->fCompl0? ~uTruth0: uTruth0;

    uPhase  = Cut_TruthPhase( pCut, pCut1 );
    uTruth1 = Extra_TruthPerm4One( *puTruthCut1, uPhase );
    uTruth1 = p->fCompl1? ~uTruth1: uTruth1;

    uTruth1 = uTruth0 & uTruth1;
    if ( pCut->fCompl )
        uTruth1 = ~uTruth1;
    if ( pCut->nVarsMax == 4 )
        uTruth1 &= 0xFFFF; 
    Cut_CutWriteTruth( pCut, &uTruth1 );
}

/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_TruthCompute5( Cut_Man_t * p, Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 )
{
    unsigned * puTruthCut0, * puTruthCut1;
    unsigned uTruth0, uTruth1, uPhase;

    puTruthCut0 = Cut_CutReadTruth(pCut0);
    puTruthCut1 = Cut_CutReadTruth(pCut1);

    uPhase  = Cut_TruthPhase( pCut, pCut0 );
    uTruth0 = Extra_TruthPerm5One( *puTruthCut0, uPhase );
    uTruth0 = p->fCompl0? ~uTruth0: uTruth0;

    uPhase  = Cut_TruthPhase( pCut, pCut1 );
    uTruth1 = Extra_TruthPerm5One( *puTruthCut1, uPhase );
    uTruth1 = p->fCompl1? ~uTruth1: uTruth1;

    uTruth1 = uTruth0 & uTruth1;
    if ( pCut->fCompl )
        uTruth1 = ~uTruth1;
    Cut_CutWriteTruth( pCut, &uTruth1 );
}

/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_TruthCompute6( Cut_Man_t * p, Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 )
{
    unsigned * puTruthCut0, * puTruthCut1;
    unsigned uTruth0[2], uTruth1[2], uPhase;

    puTruthCut0 = Cut_CutReadTruth(pCut0);
    puTruthCut1 = Cut_CutReadTruth(pCut1);

    uPhase = Cut_TruthPhase( pCut, pCut0 );
    Extra_TruthPerm6One( puTruthCut0, uPhase, uTruth0 );
    uTruth0[0] = p->fCompl0? ~uTruth0[0]: uTruth0[0];
    uTruth0[1] = p->fCompl0? ~uTruth0[1]: uTruth0[1];

    uPhase = Cut_TruthPhase( pCut, pCut1 );
    Extra_TruthPerm6One( puTruthCut1, uPhase, uTruth1 );
    uTruth1[0] = p->fCompl1? ~uTruth1[0]: uTruth1[0];
    uTruth1[1] = p->fCompl1? ~uTruth1[1]: uTruth1[1];

    uTruth1[0] = uTruth0[0] & uTruth1[0];
    uTruth1[1] = uTruth0[1] & uTruth1[1];
    if ( pCut->fCompl )
    {
        uTruth1[0] = ~uTruth0[0];
        uTruth1[1] = ~uTruth0[1];
    }
    Cut_CutWriteTruth( pCut, uTruth1 );
}






/**Function*************************************************************

  Synopsis    [Performs truth table computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cut_TruthComputeOld( Cut_Man_t * p, Cut_Cut_t * pCut, Cut_Cut_t * pCut0, Cut_Cut_t * pCut1 )
{
    unsigned uTruth0, uTruth1, uPhase;
    int clk = clock();

    assert( pCut->nVarsMax < 6 );

    // assign the truth table
    if ( pCut0->nLeaves == pCut->nLeaves )
        uTruth0 = *Cut_CutReadTruth(pCut0);
    else
    {
        assert( pCut0->nLeaves < pCut->nLeaves );
        uPhase = Cut_TruthPhase( pCut, pCut0 );
        if ( pCut->nVarsMax == 4 )
        {
            assert( pCut0->nLeaves < 4 );
            assert( uPhase < 16 );
            uTruth0 = p->pPerms43[pCut0->uTruth & 0xFF][uPhase];
        }
        else
        {
            assert( pCut->nVarsMax == 5 );
            assert( pCut0->nLeaves < 5 );
            assert( uPhase < 32 );
            if ( pCut0->nLeaves == 4 )
            {
//                Count4++;
/*
                if ( uPhase == 31-16 ) // 01111
                    uTruth0 = pCut0->uTruth;
                else if ( uPhase == 31-8 ) // 10111
                    uTruth0 = p->pPerms54[pCut0->uTruth & 0xFFFF][0];
                else if ( uPhase == 31-4 ) // 11011
                    uTruth0 = p->pPerms54[pCut0->uTruth & 0xFFFF][1];
                else if ( uPhase == 31-2 ) // 11101
                    uTruth0 = p->pPerms54[pCut0->uTruth & 0xFFFF][2];
                else if ( uPhase == 31-1 ) // 11110
                    uTruth0 = p->pPerms54[pCut0->uTruth & 0xFFFF][3];
                else
                    assert( 0 );
*/
                uTruth0 = Extra_TruthPerm5One( *Cut_CutReadTruth(pCut0), uPhase );
            }
            else
            {
//                Count5++;
//                uTruth0 = p->pPerms53[pCut0->uTruth & 0xFF][uPhase];
                uTruth0 = Extra_TruthPerm5One( *Cut_CutReadTruth(pCut0), uPhase );
            }
        }
    }
    uTruth0 = p->fCompl0? ~uTruth0: uTruth0;

    // assign the truth table
    if ( pCut1->nLeaves == pCut->nLeaves )
        uTruth0 = *Cut_CutReadTruth(pCut1);
    else
    {
        assert( pCut1->nLeaves < pCut->nLeaves );
        uPhase = Cut_TruthPhase( pCut, pCut1 );
        if ( pCut->nVarsMax == 4 )
        {
            assert( pCut1->nLeaves < 4 );
            assert( uPhase < 16 );
            uTruth1 = p->pPerms43[pCut1->uTruth & 0xFF][uPhase];
        }
        else
        {
            assert( pCut->nVarsMax == 5 );
            assert( pCut1->nLeaves < 5 );
            assert( uPhase < 32 );
            if ( pCut1->nLeaves == 4 )
            {
//                Count4++;
/*
                if ( uPhase == 31-16 ) // 01111
                    uTruth1 = pCut1->uTruth;
                else if ( uPhase == 31-8 ) // 10111
                    uTruth1 = p->pPerms54[pCut1->uTruth & 0xFFFF][0];
                else if ( uPhase == 31-4 ) // 11011
                    uTruth1 = p->pPerms54[pCut1->uTruth & 0xFFFF][1];
                else if ( uPhase == 31-2 ) // 11101
                    uTruth1 = p->pPerms54[pCut1->uTruth & 0xFFFF][2];
                else if ( uPhase == 31-1 ) // 11110
                    uTruth1 = p->pPerms54[pCut1->uTruth & 0xFFFF][3];
                else
                    assert( 0 );
*/
                uTruth1 = Extra_TruthPerm5One( *Cut_CutReadTruth(pCut1), uPhase );
            }
            else
            {
//                Count5++;
//                uTruth1 = p->pPerms53[pCut1->uTruth & 0xFF][uPhase];
                uTruth1 = Extra_TruthPerm5One( *Cut_CutReadTruth(pCut1), uPhase );
            }
        }
    }
    uTruth1 = p->fCompl1? ~uTruth1: uTruth1;
    uTruth1 = uTruth0 & uTruth1;
    if ( pCut->fCompl )
        uTruth1 = ~uTruth1;
    if ( pCut->nVarsMax == 4 )
        uTruth1 &= 0xFFFF; 
    Cut_CutWriteTruth( pCut, &uTruth1 );
p->timeTruth += clock() - clk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


