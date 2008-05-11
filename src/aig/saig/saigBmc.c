/**CFile****************************************************************

  FileName    [saigBmc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential AIG package.]

  Synopsis    [Simple BMC package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: saigBmc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "saig.h"
#include "cnf.h"
#include "satStore.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Create timeframes of the manager for BMC.]

  Description [The resulting manager is combinational. The primary inputs
  corresponding to register outputs are ordered first. POs correspond to \
  the property outputs in each time-frame.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_ManFramesBmc( Aig_Man_t * pAig, int nFrames )
{
    Aig_Man_t * pFrames;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo;
    int i, f;
    assert( Saig_ManRegNum(pAig) > 0 );
    pFrames = Aig_ManStart( Aig_ManNodeNum(pAig) * nFrames );
    // map the constant node
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pFrames );
    // create variables for register outputs
    Saig_ManForEachLo( pAig, pObj, i )
        pObj->pData = Aig_ManConst0( pFrames );
    // add timeframes
    for ( f = 0; f < nFrames; f++ )
    {
        // create PI nodes for this frame
        Saig_ManForEachPi( pAig, pObj, i )
            pObj->pData = Aig_ObjCreatePi( pFrames );
        // add internal nodes of this frame
        Aig_ManForEachNode( pAig, pObj, i )
            pObj->pData = Aig_And( pFrames, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        // create POs for this frame
        Saig_ManForEachPo( pAig, pObj, i )
            Aig_ObjCreatePo( pFrames, Aig_ObjChild0Copy(pObj) );
        if ( f == nFrames - 1 )
            break;
        // save register inputs
        Saig_ManForEachLi( pAig, pObj, i )
            pObj->pData = Aig_ObjChild0Copy(pObj);
        // transfer to register outputs
        Saig_ManForEachLiLo(  pAig, pObjLi, pObjLo, i )
            pObjLo->pData = pObjLi->pData;
    }
    Aig_ManCleanup( pFrames );
    return pFrames;
}

/**Function*************************************************************

  Synopsis    [Performs BMC for the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManBmcSimple( Aig_Man_t * pAig, int nFrames, int nConfLimit, int fRewrite, int fVerbose, int * piFrame )
{
    sat_solver * pSat;
    Cnf_Dat_t * pCnf;
    Aig_Man_t * pFrames, * pAigTemp;
    Aig_Obj_t * pObj;
    int status, clk, Lit, i, RetValue = 1;
    *piFrame = -1;
    // derive the timeframes
    clk = clock();
    pFrames = Saig_ManFramesBmc( pAig, nFrames );
    if ( fVerbose )
    {
        printf( "AIG:  PI/PO/Reg = %d/%d/%d.  Node = %6d. Lev = %5d.\n", 
            Saig_ManPiNum(pAig), Saig_ManPoNum(pAig), Saig_ManRegNum(pAig),
            Aig_ManNodeNum(pAig), Aig_ManLevelNum(pAig) );
        printf( "Time-frames (%d):  PI/PO = %d/%d.  Node = %6d. Lev = %5d.  ", 
            nFrames, Aig_ManPiNum(pFrames), Aig_ManPoNum(pFrames), 
            Aig_ManNodeNum(pFrames), Aig_ManLevelNum(pFrames) );
        PRT( "Time", clock() - clk );
    }
    // rewrite the timeframes
    if ( fRewrite )
    {
        clk = clock();
//        pFrames = Dar_ManBalance( pAigTemp = pFrames, 0 );
        pFrames = Dar_ManRwsat( pAigTemp = pFrames, 1, 0 );
        Aig_ManStop( pAigTemp );
        if ( fVerbose )
        {
            printf( "Time-frames after rewriting:  Node = %6d. Lev = %5d.  ", 
                Aig_ManNodeNum(pFrames), Aig_ManLevelNum(pFrames) );
            PRT( "Time", clock() - clk );
        }
    }
    // create the SAT solver
    clk = clock();
    pCnf = Cnf_Derive( pFrames, Aig_ManPoNum(pFrames) );  
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnf->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            assert( 0 );
    }
    if ( fVerbose )
    {
        printf( "CNF: Variables = %6d. Clauses = %7d. Literals = %8d. ", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );
        PRT( "Time", clock() - clk );
    }
    status = sat_solver_simplify(pSat);
    if ( status == 0 )
    {
        if ( fVerbose )
            printf( "The BMC problem is trivially UNSAT\n" );
    }
    else
    {
        Aig_ManForEachPo( pFrames, pObj, i )
        {
            Lit = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
            if ( fVerbose )
                printf( "Solving output %2d of frame %3d ... \r", 
                    i % Saig_ManPoNum(pAig), i / Saig_ManPoNum(pAig) );
            clk = clock();
            status = sat_solver_solve( pSat, &Lit, &Lit + 1, (sint64)nConfLimit, (sint64)0, (sint64)0, (sint64)0 );
            if ( fVerbose )
            {
                printf( "Solved  output %2d of frame %3d.  ", 
                    i % Saig_ManPoNum(pAig), i / Saig_ManPoNum(pAig) );
                printf( "Conf =%8.0f. Imp =%11.0f. ", (double)pSat->stats.conflicts, (double)pSat->stats.propagations );
                PRT( "Time", clock() - clk );
            }
            if ( status == l_False )
            {
            }
            else if ( status == l_True )
            {
                extern void * Fra_SmlCopyCounterExample( Aig_Man_t * pAig, Aig_Man_t * pFrames, int * pModel );
                Vec_Int_t * vCiIds = Cnf_DataCollectPiSatNums( pCnf, pFrames );
                int * pModel = Sat_SolverGetModel( pSat, vCiIds->pArray, vCiIds->nSize );
                pModel[Aig_ManPiNum(pFrames)] = pObj->Id;
                pAig->pSeqModel = Fra_SmlCopyCounterExample( pAig, pFrames, pModel );
                free( pModel );
                Vec_IntFree( vCiIds );

                RetValue = 0;
                break;
            }
            else
            {
                *piFrame = i;
                RetValue = -1;
                break;
            }
        }
    }
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnf );
    Aig_ManStop( pFrames );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


