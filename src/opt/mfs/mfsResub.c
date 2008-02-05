/**CFile****************************************************************

  FileName    [mfsResub.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Procedures to perform resubstitution.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfsResub.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfsInt.h"

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
void Abc_NtkMfsUpdateNetwork( Mfs_Man_t * p, Abc_Obj_t * pObj, Vec_Ptr_t * vFanins, Hop_Obj_t * pFunc )
{
    Abc_Obj_t * pObjNew, * pFanin;
    int k;
    // create the new node
    pObjNew = Abc_NtkCreateNode( pObj->pNtk );
    pObjNew->pData = pFunc;
    Vec_PtrForEachEntry( vFanins, pFanin, k )
        Abc_ObjAddFanin( pObjNew, pFanin );
    // replace the old node by the new node
//printf( "Replacing node " ); Abc_ObjPrint( stdout, pObj );
//printf( "Inserting node " ); Abc_ObjPrint( stdout, pObjNew );
    // update the level of the node
    Abc_NtkUpdate( pObj, pObjNew, p->vLevels );
}

/**Function*************************************************************

  Synopsis    [Tries resubstitution.]

  Description [Returns 1 if it is feasible, or 0 if c-ex is found.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMfsTryResubOnce( Mfs_Man_t * p, int * pCands, int nCands )
{
    unsigned * pData, * pDataTot;
    int RetValue, iVar, i;
    p->nSatCalls++;
    RetValue = sat_solver_solve( p->pSat, pCands, pCands + nCands, (sint64)0, (sint64)0, (sint64)0, (sint64)0 );
    assert( RetValue == l_False || RetValue == l_True );
    if ( RetValue == l_False )
        return 1;
    p->nSatCexes++;
    // store the counter-example
    pData = Vec_PtrEntry( p->vDivCexes, p->nCexes++ );
    assert( pData[0] == 0 );
    Vec_IntForEachEntry( p->vProjVars, iVar, i )
    {
        if ( sat_solver_var_value( p->pSat, iVar ) )
            Aig_InfoSetBit( pData, i );
    }
    // AND the result with the previous ones
    pDataTot = Vec_PtrEntry( p->vDivCexes, Vec_PtrSize(p->vDivs) );
    for ( i = 0; i < p->nDivWords; i++ )
        pDataTot[i] &= pData[i];
    return 0;
}

/**Function*************************************************************

  Synopsis    [Performs resubstitution for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMfsSolveSatResub( Mfs_Man_t * p, Abc_Obj_t * pNode, int iFanin, int fOnlyRemove )
{
    int fVeryVerbose = p->pPars->fVeryVerbose && Vec_PtrSize(p->vDivs) < 80;
    unsigned * pData;
    int pCands[MFS_FANIN_MAX];
    int iVar, i, nCands, clk;
    Abc_Obj_t * pFanin;
    Hop_Obj_t * pFunc;
    assert( iFanin >= 0 );

    // clean simulation info
    Vec_PtrCleanSimInfo( p->vDivCexes, 0, p->nDivWords ); 
    pData = Vec_PtrEntry( p->vDivCexes, Vec_PtrSize(p->vDivs) );
    memset( pData, 0xFF, sizeof(unsigned) * p->nDivWords );
    p->nCexes = 0;

    if ( fVeryVerbose )
    {
        printf( "\n" );
        printf( "Node %5d : Level = %2d. Divs = %3d.  Fanin = %d (out of %d). MFFC = %d\n", 
            pNode->Id, pNode->Level, Vec_PtrSize(p->vDivs)-Abc_ObjFaninNum(pNode), 
            iFanin, Abc_ObjFaninNum(pNode), 
            Abc_ObjFanoutNum(Abc_ObjFanin(pNode, iFanin)) == 1 ? Abc_NodeMffcLabel(Abc_ObjFanin(pNode, iFanin)) : 0 );
    }

    // try fanins without the critical fanin
    nCands = 0;
    Vec_PtrClear( p->vFanins );
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        if ( i == iFanin )
            continue;
        Vec_PtrPush( p->vFanins, pFanin );
        iVar = Vec_PtrSize(p->vDivs) - Abc_ObjFaninNum(pNode) + i;
        pCands[nCands++] = toLitCond( Vec_IntEntry( p->vProjVars, iVar ), 1 );
    }
    if ( Abc_NtkMfsTryResubOnce( p, pCands, nCands ) )
    {
        if ( fVeryVerbose )
        printf( "Node %d: Fanin %d can be removed.\n", pNode->Id, iFanin );
        p->nNodesResub++;
//        p->nNodesGained += Abc_NodeMffcLabel(pNode);
clk = clock();
        // derive the function
        pFunc = Abc_NtkMfsInterplate( p, pCands, nCands );
        // update the network
        Abc_NtkMfsUpdateNetwork( p, pNode, p->vFanins, pFunc );
p->timeInt += clock() - clk;
        return 1;
    }

    if ( fOnlyRemove )
        return 0;

    // shift variables by 1
    for ( i = Vec_PtrSize(p->vFanins); i > 0; i-- )
        p->vFanins->pArray[i] = p->vFanins->pArray[i-1];
    p->vFanins->nSize++;

    if ( fVeryVerbose )
    {
        for ( i = 0; i < 8; i++ )
            printf( " " );
        for ( i = 0; i < Vec_PtrSize(p->vDivs)-Abc_ObjFaninNum(pNode); i++ )
            printf( "%d", i % 10 );
        for ( i = 0; i < Abc_ObjFaninNum(pNode); i++ )
            if ( i == iFanin )
                printf( "*" );
            else
                printf( "%c", 'a' + i );
        printf( "\n" );
    }
    iVar = -1;
    while ( 1 )
    {
        if ( fVeryVerbose )
        {
            printf( "%3d: %2d ", p->nCexes, iVar );
            pData = Vec_PtrEntry( p->vDivCexes, p->nCexes-1 );
//            Extra_PrintBinary( stdout, pData, Vec_PtrSize(p->vDivs) );
            for ( i = 0; i < Vec_PtrSize(p->vDivs); i++ )
                printf( "%d", Aig_InfoHasBit(pData, i) );
            printf( "\n" );
        }

        // find the next divisor to try
        pData = Vec_PtrEntry( p->vDivCexes, Vec_PtrSize(p->vDivs) );
        for ( iVar = 0; iVar < Vec_PtrSize(p->vDivs)-Abc_ObjFaninNum(pNode); iVar++ )
            if ( Aig_InfoHasBit( pData, iVar ) )
                break;
        if ( iVar == Vec_PtrSize(p->vDivs)-Abc_ObjFaninNum(pNode) )
            return 0;
        pCands[nCands] = toLitCond( Vec_IntEntry(p->vProjVars, iVar), 1 );
        if ( Abc_NtkMfsTryResubOnce( p, pCands, nCands+1 ) )
        {
            if ( fVeryVerbose )
            printf( "Node %d: Fanin %d can be replaced by divisor %d.\n", pNode->Id, iFanin, iVar );
            p->nNodesResub++;
//            p->nNodesGained += Abc_NodeMffcLabel(pNode);
clk = clock();
            // derive the function
            pFunc = Abc_NtkMfsInterplate( p, pCands, nCands+1 );
            // update the network
//            Vec_PtrPush( p->vFanins, Vec_PtrEntry(p->vDivs, iVar) );
            Vec_PtrWriteEntry( p->vFanins, 0, Vec_PtrEntry(p->vDivs, iVar) );
            Abc_NtkMfsUpdateNetwork( p, pNode, p->vFanins, pFunc );
p->timeInt += clock() - clk;
            return 1;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Performs resubstitution for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMfsResubArea( Mfs_Man_t * p, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin;
    int i;
    Abc_ObjForEachFanin( pNode, pFanin, i )
        if ( !Abc_ObjIsCi(pFanin) && Abc_ObjFanoutNum(pFanin) == 1 )
        {
            if ( Abc_NtkMfsSolveSatResub( p, pNode, i, 0 ) )
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
int Abc_NtkMfsResubEdge( Mfs_Man_t * p, Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin;
    int i;
    Abc_ObjForEachFanin( pNode, pFanin, i )
        if ( !Abc_ObjIsCi(pFanin) && Abc_ObjFanoutNum(pFanin) == 1 )
        {
            if ( Abc_NtkMfsSolveSatResub( p, pNode, i, 0 ) )
                return 1;
        }
    Abc_ObjForEachFanin( pNode, pFanin, i )
        if ( !Abc_ObjIsCi(pFanin) && Abc_ObjFanoutNum(pFanin) != 1 )
        {
            if ( Abc_NtkMfsSolveSatResub( p, pNode, i, 1 ) )
                return 1;
        }
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


