/**CFile****************************************************************

  FileName    [cnfMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG-to-CNF conversion.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: cnfMan.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cnf.h"
#include "satSolver.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int Cnf_Lit2Var( int Lit )        { return (Lit & 1)? -(Lit >> 1)-1 : (Lit >> 1)+1;  }
static inline int Cnf_Lit2Var2( int Lit )       { return (Lit & 1)? -(Lit >> 1)   : (Lit >> 1);    }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cnf_Man_t * Cnf_ManStart()
{
    Cnf_Man_t * p;
    int i;
    // allocate the manager
    p = ALLOC( Cnf_Man_t, 1 );
    memset( p, 0, sizeof(Cnf_Man_t) );
    // derive internal data structures
    Cnf_ReadMsops( &p->pSopSizes, &p->pSops );
    // allocate memory manager for cuts
    p->pMemCuts = Aig_MmFlexStart();
    p->nMergeLimit = 10;
    // allocate temporary truth tables
    p->pTruths[0] = ALLOC( unsigned, 4 * Aig_TruthWordNum(p->nMergeLimit) );
    for ( i = 1; i < 4; i++ )
        p->pTruths[i] = p->pTruths[i-1] + Aig_TruthWordNum(p->nMergeLimit);
    p->vMemory = Vec_IntAlloc( 1 << 18 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the fraiging manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_ManStop( Cnf_Man_t * p )
{
    Vec_IntFree( p->vMemory );
    free( p->pTruths[0] );
    Aig_MmFlexStop( p->pMemCuts, 0 );
    free( p->pSopSizes );
    free( p->pSops[1] );
    free( p->pSops );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Returns the array of CI IDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cnf_DataCollectPiSatNums( Cnf_Dat_t * pCnf, Aig_Man_t * p )
{
    Vec_Int_t * vCiIds;
    Aig_Obj_t * pObj;
    int i;
    vCiIds = Vec_IntAlloc( Aig_ManPiNum(p) );
    Aig_ManForEachPi( p, pObj, i )
        Vec_IntPush( vCiIds, pCnf->pVarNums[pObj->Id] );
    return vCiIds;
}

/**Function*************************************************************

  Synopsis    [Allocates the new CNF.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cnf_Dat_t * Cnf_DataAlloc( Aig_Man_t * pAig, int nVars, int nClauses, int nLiterals )
{
    Cnf_Dat_t * pCnf;
    pCnf = ALLOC( Cnf_Dat_t, 1 );
    memset( pCnf, 0, sizeof(Cnf_Dat_t) );
    pCnf->pMan = pAig;
    pCnf->nVars = nVars;
    pCnf->nClauses = nClauses;
    pCnf->nLiterals = nLiterals;
    pCnf->pClauses = ALLOC( int *, nClauses + 1 );
    pCnf->pClauses[0] = ALLOC( int, nLiterals );
    pCnf->pClauses[nClauses] = pCnf->pClauses[0] + nLiterals;
    pCnf->pVarNums = ALLOC( int, Aig_ManObjNumMax(pAig) );
    memset( pCnf->pVarNums, 0xff, sizeof(int) * Aig_ManObjNumMax(pAig) );
    return pCnf;
}

/**Function*************************************************************

  Synopsis    [Allocates the new CNF.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cnf_Dat_t * Cnf_DataDup( Cnf_Dat_t * p )
{
    Cnf_Dat_t * pCnf;
    int i;
    pCnf = Cnf_DataAlloc( p->pMan, p->nVars, p->nClauses, p->nLiterals );
    memcpy( pCnf->pClauses[0], p->pClauses[0], sizeof(int) * p->nLiterals );
    memcpy( pCnf->pVarNums, p->pVarNums, sizeof(int) * Aig_ManObjNumMax(p->pMan) );
    for ( i = 1; i < p->nClauses; i++ )
        pCnf->pClauses[i] = pCnf->pClauses[0] + (p->pClauses[i] - p->pClauses[0]);
    return pCnf;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_DataFree( Cnf_Dat_t * p )
{
    if ( p == NULL )
        return;
    free( p->pClauses[0] );
    free( p->pClauses );
    free( p->pVarNums );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Writes CNF into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_DataLift( Cnf_Dat_t * p, int nVarsPlus )
{
    Aig_Obj_t * pObj;
    int v;
    Aig_ManForEachObj( p->pMan, pObj, v )
        if ( p->pVarNums[pObj->Id] )
            p->pVarNums[pObj->Id] += nVarsPlus;
    for ( v = 0; v < p->nLiterals; v++ )
        p->pClauses[0][v] += 2*nVarsPlus;
}

/**Function*************************************************************

  Synopsis    [Writes CNF into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_DataWriteIntoFile( Cnf_Dat_t * p, char * pFileName, int fReadable )
{
    FILE * pFile;
    int * pLit, * pStop, i;
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        printf( "Cnf_WriteIntoFile(): Output file cannot be opened.\n" );
        return;
    }
    fprintf( pFile, "c Result of efficient AIG-to-CNF conversion using package CNF\n" );
    fprintf( pFile, "p %d %d\n", p->nVars, p->nClauses );
    for ( i = 0; i < p->nClauses; i++ )
    {
        for ( pLit = p->pClauses[i], pStop = p->pClauses[i+1]; pLit < pStop; pLit++ )
            fprintf( pFile, "%d ", fReadable? Cnf_Lit2Var2(*pLit) : Cnf_Lit2Var(*pLit) );
        fprintf( pFile, "0\n" );
    }
    fprintf( pFile, "\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Writes CNF into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Cnf_DataWriteIntoSolver( Cnf_Dat_t * p, int nFrames, int fInit )
{
    sat_solver * pSat;
    int i, f, status;
    assert( nFrames > 0 );
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, p->nVars * nFrames );
    for ( i = 0; i < p->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, p->pClauses[i], p->pClauses[i+1] ) )
        {
            sat_solver_delete( pSat );
            return NULL;
        }
    }
    if ( nFrames > 1 )
    {
        Aig_Obj_t * pObjLo, * pObjLi;
        int nLitsAll, * pLits, Lits[2];
        nLitsAll = 2 * p->nVars;
        pLits = p->pClauses[0];
        for ( f = 1; f < nFrames; f++ )
        {
            // add equality of register inputs/outputs for different timeframes
            Aig_ManForEachLiLoSeq( p->pMan, pObjLi, pObjLo, i )
            {
                Lits[0] = (f-1)*nLitsAll + toLitCond( p->pVarNums[pObjLi->Id], 0 );
                Lits[1] =  f   *nLitsAll + toLitCond( p->pVarNums[pObjLo->Id], 1 );
                if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
                {
                    sat_solver_delete( pSat );
                    return NULL;
                }
                Lits[0]++;
                Lits[1]--;
                if ( !sat_solver_addclause( pSat, Lits, Lits + 2 ) )
                {
                    sat_solver_delete( pSat );
                    return NULL;
                }
            }
            // add clauses for the next timeframe
            for ( i = 0; i < p->nLiterals; i++ )
                pLits[i] += nLitsAll;
            for ( i = 0; i < p->nClauses; i++ )
            {
                if ( !sat_solver_addclause( pSat, p->pClauses[i], p->pClauses[i+1] ) )
                {
                    sat_solver_delete( pSat );
                    return NULL;
                }
            }
        }
        // return literals to their original state
        nLitsAll = (f-1) * nLitsAll;
        for ( i = 0; i < p->nLiterals; i++ )
            pLits[i] -= nLitsAll;
    }
    if ( fInit )
    {
        Aig_Obj_t * pObjLo;
        int Lits[1];
        Aig_ManForEachLoSeq( p->pMan, pObjLo, i )
        {
            Lits[0] = toLitCond( p->pVarNums[pObjLo->Id], 1 );
            if ( !sat_solver_addclause( pSat, Lits, Lits + 1 ) )
            {
                sat_solver_delete( pSat );
                return NULL;
            }
        }
    }
    status = sat_solver_simplify(pSat);
    if ( status == 0 )
    {
        sat_solver_delete( pSat );
        return NULL;
    }
    return pSat;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


