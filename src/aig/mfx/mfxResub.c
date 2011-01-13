/**CFile****************************************************************

  FileName    [mfxResub.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Procedures to perform resubstitution.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfxResub.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfxInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Updates the network after resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mfx_UpdateNetwork( Mfx_Man_t * p, Nwk_Obj_t * pObj, Vec_Ptr_t * vFanins, Hop_Obj_t * pFunc )
{
    Nwk_Obj_t * pObjNew, * pFanin;
    int k;
    // create the new node
    pObjNew = Nwk_ManCreateNode( pObj->pMan, Vec_PtrSize(vFanins), Nwk_ObjFanoutNum(pObj) );
    pObjNew->pFunc = pFunc;
    Vec_PtrForEachEntry( Nwk_Obj_t *, vFanins, pFanin, k )
        Nwk_ObjAddFanin( pObjNew, pFanin );
    // replace the old node by the new node
    Nwk_ManUpdate( pObj, pObjNew, p->vLevels );
}

/**Function*************************************************************

  Synopsis    [Prints resub candidate stats.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mfx_PrintResubStats( Mfx_Man_t * p )
{
    Nwk_Obj_t * pFanin, * pNode;
    int i, k, nAreaCrits = 0, nAreaExpanse = 0;
    int nFaninMax = Nwk_ManGetFaninMax(p->pNtk);
    Nwk_ManForEachNode( p->pNtk, pNode, i )
        Nwk_ObjForEachFanin( pNode, pFanin, k )
        {
            if ( !Nwk_ObjIsCi(pFanin) && Nwk_ObjFanoutNum(pFanin) == 1 )
            {
                nAreaCrits++;
                nAreaExpanse += (int)(Nwk_ObjFaninNum(pNode) < nFaninMax);
            }
        }
    printf( "Total area-critical fanins = %d. Belonging to expandable nodes = %d.\n", 
        nAreaCrits, nAreaExpanse );
}

/**Function*************************************************************

  Synopsis    [Tries resubstitution.]

  Description [Returns 1 if it is feasible, or 0 if c-ex is found.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_TryResubOnce( Mfx_Man_t * p, int * pCands, int nCands )
{
    unsigned * pData;
    int RetValue, iVar, i;
    p->nSatCalls++;
    RetValue = sat_solver_solve( p->pSat, pCands, pCands + nCands, (ABC_INT64_T)p->pPars->nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
//    assert( RetValue == l_False || RetValue == l_True );
    if ( RetValue == l_False )
        return 1;
    if ( RetValue != l_True )
    {
        p->nTimeOuts++;
        return -1;
    }
    p->nSatCexes++;
    // store the counter-example
    Vec_IntForEachEntry( p->vProjVarsSat, iVar, i )
    {
        pData = (unsigned *)Vec_PtrEntry( p->vDivCexes, i );
        if ( !sat_solver_var_value( p->pSat, iVar ) ) // remove 0s!!!
        {
            assert( Aig_InfoHasBit(pData, p->nCexes) );
            Aig_InfoXorBit( pData, p->nCexes );
        }
    }
    p->nCexes++;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Performs resubstitution for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_SolveSatResub( Mfx_Man_t * p, Nwk_Obj_t * pNode, int iFanin, int fOnlyRemove, int fSkipUpdate )
{
    int fVeryVerbose = p->pPars->fVeryVerbose && Vec_PtrSize(p->vDivs) < 80;
    unsigned * pData;
    int pCands[MFX_FANIN_MAX];
    int RetValue, iVar, i, nCands, nWords, w, clk;
    Nwk_Obj_t * pFanin;
    Hop_Obj_t * pFunc;
    assert( iFanin >= 0 );

    // clean simulation info
    Vec_PtrFillSimInfo( p->vDivCexes, 0, p->nDivWords ); 
    p->nCexes = 0;
    if ( fVeryVerbose )
    {
        printf( "\n" );
        printf( "Node %5d : Level = %2d. Divs = %3d.  Fanin = %d (out of %d). MFFC = %d\n", 
            pNode->Id, pNode->Level, Vec_PtrSize(p->vDivs)-Nwk_ObjFaninNum(pNode), 
            iFanin, Nwk_ObjFaninNum(pNode), 
            Nwk_ObjFanoutNum(Nwk_ObjFanin(pNode, iFanin)) == 1 ? Nwk_ObjMffcLabel(Nwk_ObjFanin(pNode, iFanin)) : 0 );
    }

    // try fanins without the critical fanin
    nCands = 0;
    Vec_PtrClear( p->vFanins );
    Nwk_ObjForEachFanin( pNode, pFanin, i )
    {
        if ( i == iFanin )
            continue;
        Vec_PtrPush( p->vFanins, pFanin );
        iVar = Vec_PtrSize(p->vDivs) - Nwk_ObjFaninNum(pNode) + i;
        pCands[nCands++] = toLitCond( Vec_IntEntry( p->vProjVarsSat, iVar ), 1 );
    }
    RetValue = Mfx_TryResubOnce( p, pCands, nCands );
    if ( RetValue == -1 )
        return 0;
    if ( RetValue == 1 )
    {
        if ( fVeryVerbose )
        printf( "Node %d: Fanin %d can be removed.\n", pNode->Id, iFanin );
        p->nNodesResub++;
        p->nNodesGainedLevel++;
        if ( fSkipUpdate )
            return 1;
clk = clock();
        // derive the function
        pFunc = Mfx_Interplate( p, pCands, nCands );
        if ( pFunc == NULL )
            return 0;
        // update the network
        Mfx_UpdateNetwork( p, pNode, p->vFanins, pFunc );
p->timeInt += clock() - clk;
        return 1;
    }

    if ( fOnlyRemove )
        return 0;

    if ( fVeryVerbose )
    {
        for ( i = 0; i < 8; i++ )
            printf( " " );
        for ( i = 0; i < Vec_PtrSize(p->vDivs)-Nwk_ObjFaninNum(pNode); i++ )
            printf( "%d", i % 10 );
        for ( i = 0; i < Nwk_ObjFaninNum(pNode); i++ )
            if ( i == iFanin )
                printf( "*" );
            else
                printf( "%c", 'a' + i );
        printf( "\n" );
    }
    iVar = -1;
    while ( 1 )
    {
        float * pProbab = (float *)(p->vProbs? p->vProbs->pArray : NULL);
        assert( (pProbab != NULL) == p->pPars->fPower );
        if ( fVeryVerbose )
        {
            printf( "%3d: %2d ", p->nCexes, iVar );
            for ( i = 0; i < Vec_PtrSize(p->vDivs); i++ )
            {
                pData = (unsigned *)Vec_PtrEntry( p->vDivCexes, i );
                printf( "%d", Aig_InfoHasBit(pData, p->nCexes-1) );
            }
            printf( "\n" );
        }

        // find the next divisor to try
        nWords = Aig_BitWordNum(p->nCexes);
        assert( nWords <= p->nDivWords );
        for ( iVar = 0; iVar < Vec_PtrSize(p->vDivs)-Nwk_ObjFaninNum(pNode); iVar++ )
        {
            if ( p->pPars->fPower )
            {
                Nwk_Obj_t * pDiv = (Nwk_Obj_t *)Vec_PtrEntry(p->vDivs, iVar);
                // only accept the divisor if it is "cool"
                if ( pProbab[Nwk_ObjId(pDiv)] >= 0.2 )
                    continue;
            }
            pData  = (unsigned *)Vec_PtrEntry( p->vDivCexes, iVar );
            for ( w = 0; w < nWords; w++ )
                if ( pData[w] != ~0 )
                    break;
            if ( w == nWords )
                break;
        }
        if ( iVar == Vec_PtrSize(p->vDivs)-Nwk_ObjFaninNum(pNode) )
            return 0;

        pCands[nCands] = toLitCond( Vec_IntEntry(p->vProjVarsSat, iVar), 1 );
        RetValue = Mfx_TryResubOnce( p, pCands, nCands+1 );
        if ( RetValue == -1 )
            return 0;
        if ( RetValue == 1 )
        {
            if ( fVeryVerbose )
            printf( "Node %d: Fanin %d can be replaced by divisor %d.\n", pNode->Id, iFanin, iVar );
            p->nNodesResub++;
            p->nNodesGainedLevel++;
            if ( fSkipUpdate )
                return 1;
clk = clock();
            // derive the function
            pFunc = Mfx_Interplate( p, pCands, nCands+1 );
            if ( pFunc == NULL )
                return 0;
            // update the network
            Vec_PtrPush( p->vFanins, Vec_PtrEntry(p->vDivs, iVar) );
            Mfx_UpdateNetwork( p, pNode, p->vFanins, pFunc );
p->timeInt += clock() - clk;
            return 1;
        }
        if ( p->nCexes >= p->pPars->nDivMax )
            break;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Performs resubstitution for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_SolveSatResub2( Mfx_Man_t * p, Nwk_Obj_t * pNode, int iFanin, int iFanin2 )
{
    int fVeryVerbose = p->pPars->fVeryVerbose && Vec_PtrSize(p->vDivs) < 80;
    unsigned * pData, * pData2;
    int pCands[MFX_FANIN_MAX];
    int RetValue, iVar, iVar2, i, w, nCands, clk, nWords, fBreak;
    Nwk_Obj_t * pFanin;
    Hop_Obj_t * pFunc;
    assert( iFanin >= 0 );
    assert( iFanin2 >= 0 || iFanin2 == -1 );

    // clean simulation info
    Vec_PtrFillSimInfo( p->vDivCexes, 0, p->nDivWords ); 
    p->nCexes = 0;
    if ( fVeryVerbose )
    {
        printf( "\n" );
        printf( "Node %5d : Level = %2d. Divs = %3d.  Fanins = %d/%d (out of %d). MFFC = %d\n", 
            pNode->Id, pNode->Level, Vec_PtrSize(p->vDivs)-Nwk_ObjFaninNum(pNode), 
            iFanin, iFanin2, Nwk_ObjFaninNum(pNode), 
            Nwk_ObjFanoutNum(Nwk_ObjFanin(pNode, iFanin)) == 1 ? Nwk_ObjMffcLabel(Nwk_ObjFanin(pNode, iFanin)) : 0 );
    }

    // try fanins without the critical fanin
    nCands = 0;
    Vec_PtrClear( p->vFanins );
    Nwk_ObjForEachFanin( pNode, pFanin, i )
    {
        if ( i == iFanin || i == iFanin2 )
            continue;
        Vec_PtrPush( p->vFanins, pFanin );
        iVar = Vec_PtrSize(p->vDivs) - Nwk_ObjFaninNum(pNode) + i;
        pCands[nCands++] = toLitCond( Vec_IntEntry( p->vProjVarsSat, iVar ), 1 );
    }
    RetValue = Mfx_TryResubOnce( p, pCands, nCands );
    if ( RetValue == -1 )
        return 0;
    if ( RetValue == 1 )
    {
        if ( fVeryVerbose )
        printf( "Node %d: Fanins %d/%d can be removed.\n", pNode->Id, iFanin, iFanin2 );
        p->nNodesResub++;
        p->nNodesGainedLevel++;
clk = clock();
        // derive the function
        pFunc = Mfx_Interplate( p, pCands, nCands );
        if ( pFunc == NULL )
            return 0;
        // update the network
        Mfx_UpdateNetwork( p, pNode, p->vFanins, pFunc );
p->timeInt += clock() - clk;
        return 1;
    }

    if ( fVeryVerbose )
    {
        for ( i = 0; i < 11; i++ )
            printf( " " );
        for ( i = 0; i < Vec_PtrSize(p->vDivs)-Nwk_ObjFaninNum(pNode); i++ )
            printf( "%d", i % 10 );
        for ( i = 0; i < Nwk_ObjFaninNum(pNode); i++ )
            if ( i == iFanin || i == iFanin2 )
                printf( "*" );
            else
                printf( "%c", 'a' + i );
        printf( "\n" );
    }
    iVar = iVar2 = -1;
    while ( 1 )
    {
        if ( fVeryVerbose )
        {
            printf( "%3d: %2d %2d ", p->nCexes, iVar, iVar2 );
            for ( i = 0; i < Vec_PtrSize(p->vDivs); i++ )
            {
                pData = (unsigned *)Vec_PtrEntry( p->vDivCexes, i );
                printf( "%d", Aig_InfoHasBit(pData, p->nCexes-1) );
            }
            printf( "\n" );
        }

        // find the next divisor to try
        nWords = Aig_BitWordNum(p->nCexes);
        assert( nWords <= p->nDivWords );
        fBreak = 0;
        for ( iVar = 1; iVar < Vec_PtrSize(p->vDivs)-Nwk_ObjFaninNum(pNode); iVar++ )
        {
            pData  = (unsigned *)Vec_PtrEntry( p->vDivCexes, iVar );
            for ( iVar2 = 0; iVar2 < iVar; iVar2++ )
            {
                pData2 = (unsigned *)Vec_PtrEntry( p->vDivCexes, iVar2 );
                for ( w = 0; w < nWords; w++ )
                    if ( (pData[w] | pData2[w]) != ~0 )
                        break;
                if ( w == nWords )
                {
                    fBreak = 1;
                    break;
                }
            }
            if ( fBreak )
                break;
        }
        if ( iVar == Vec_PtrSize(p->vDivs)-Nwk_ObjFaninNum(pNode) )
            return 0;

        pCands[nCands]   = toLitCond( Vec_IntEntry(p->vProjVarsSat, iVar2), 1 );
        pCands[nCands+1] = toLitCond( Vec_IntEntry(p->vProjVarsSat, iVar), 1 );
        RetValue = Mfx_TryResubOnce( p, pCands, nCands+2 );
        if ( RetValue == -1 )
            return 0;
        if ( RetValue == 1 )
        {
            if ( fVeryVerbose )
            printf( "Node %d: Fanins %d/%d can be replaced by divisors %d/%d.\n", pNode->Id, iFanin, iFanin2, iVar, iVar2 );
            p->nNodesResub++;
            p->nNodesGainedLevel++;
clk = clock();
            // derive the function
            pFunc = Mfx_Interplate( p, pCands, nCands+2 );
            if ( pFunc == NULL )
                return 0;
            // update the network
            Vec_PtrPush( p->vFanins, Vec_PtrEntry(p->vDivs, iVar2) );
            Vec_PtrPush( p->vFanins, Vec_PtrEntry(p->vDivs, iVar) );
            assert( Vec_PtrSize(p->vFanins) == nCands + 2 );
            Mfx_UpdateNetwork( p, pNode, p->vFanins, pFunc );
p->timeInt += clock() - clk;
            return 1;
        }
        if ( p->nCexes >= p->pPars->nDivMax )
            break;
    }
    return 0;
}


/**Function*************************************************************

  Synopsis    [Evaluates the possibility of replacing given edge by another edge.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_EdgeSwapEval( Mfx_Man_t * p, Nwk_Obj_t * pNode )
{
    Nwk_Obj_t * pFanin;
    int i;
    Nwk_ObjForEachFanin( pNode, pFanin, i )
        Mfx_SolveSatResub( p, pNode, i, 0, 1 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Evaluates the possibility of replacing given edge by another edge.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_EdgePower( Mfx_Man_t * p, Nwk_Obj_t * pNode )
{
    Nwk_Obj_t * pFanin;
    float * pProbab = (float *)p->vProbs->pArray;
    int i;
    // try replacing area critical fanins
    Nwk_ObjForEachFanin( pNode, pFanin, i )
        if ( pProbab[pFanin->Id] >= 0.4 )
        {
            if ( Mfx_SolveSatResub( p, pNode, i, 0, 0 ) )
                return 1;
        }
    return 0;
}


/**Function*************************************************************

  Synopsis    [Performs resubstitution for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_ResubNode( Mfx_Man_t * p, Nwk_Obj_t * pNode )
{
    Nwk_Obj_t * pFanin;
    int i;
    // try replacing area critical fanins
    Nwk_ObjForEachFanin( pNode, pFanin, i )
        if ( !Nwk_ObjIsCi(pFanin) && Nwk_ObjFanoutNum(pFanin) == 1 )
        {
            if ( Mfx_SolveSatResub( p, pNode, i, 0, 0 ) )
                return 1;
        }
    // try removing redundant edges
    if ( !p->pPars->fArea )
    {
        Nwk_ObjForEachFanin( pNode, pFanin, i )
            if ( Nwk_ObjIsCi(pFanin) || Nwk_ObjFanoutNum(pFanin) != 1 )
            {
                if ( Mfx_SolveSatResub( p, pNode, i, 1, 0 ) )
                    return 1;
            }
    }
    if ( Nwk_ObjFaninNum(pNode) == p->nFaninMax )
        return 0;

    return 0; /// !!!!! temporary workaround

    // try replacing area critical fanins while adding two new fanins
    Nwk_ObjForEachFanin( pNode, pFanin, i )
        if ( !Nwk_ObjIsCi(pFanin) && Nwk_ObjFanoutNum(pFanin) == 1 )
        {
            if ( Mfx_SolveSatResub2( p, pNode, i, -1 ) )
                return 1;
        }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Performs resubstitution for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mfx_ResubNode2( Mfx_Man_t * p, Nwk_Obj_t * pNode )
{
    Nwk_Obj_t * pFanin, * pFanin2;
    int i, k;
/*
    Nwk_ObjForEachFanin( pNode, pFanin, i )
        if ( !Nwk_ObjIsCi(pFanin) && Nwk_ObjFanoutNum(pFanin) == 1 )
        {
            if ( Mfx_SolveSatResub( p, pNode, i, 0, 0 ) )
                return 1;
        }
*/
    if ( Nwk_ObjFaninNum(pNode) < 2 )
        return 0;
    // try replacing one area critical fanin and one other fanin while adding two new fanins
    Nwk_ObjForEachFanin( pNode, pFanin, i )
    {
        if ( !Nwk_ObjIsCi(pFanin) && Nwk_ObjFanoutNum(pFanin) == 1 )
        {
            // consider second fanin to remove at the same time
            Nwk_ObjForEachFanin( pNode, pFanin2, k )
            {
                if ( i != k && Mfx_SolveSatResub2( p, pNode, i, k ) )
                    return 1;
            }
        }
    }
    return 0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

