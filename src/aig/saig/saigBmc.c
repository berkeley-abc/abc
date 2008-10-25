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

#define AIG_VISITED       ((Aig_Obj_t *)(PORT_PTRUINT_T)1)

typedef struct Saig_Bmc_t_ Saig_Bmc_t;
struct Saig_Bmc_t_
{
    // parameters
    int                   nFramesMax;     // the max number of timeframes to consider
    int                   nConfMaxOne;    // the max number of conflicts at a target
    int                   nConfMaxAll;    // the max number of conflicts for all targets
    int                   nNodesMax;      // the max number of nodes to add
    int                   fVerbose;       // enables verbose output
    // AIG managers
    Aig_Man_t *           pAig;           // the user's AIG manager
    Aig_Man_t *           pFrm;           // Frames manager
    Vec_Ptr_t *           vVisited;       // nodes visited in Frames
    // node mapping
    int                   nObjs;          // the largest number of an AIG object
    Vec_Ptr_t *           vAig2Frm;       // mapping of AIG nodees into Frames nodes
    // SAT solver
    sat_solver *          pSat;           // SAT solver
    Vec_Int_t *           vObj2Var;       // mapping of frames objects in CNF variables
    int                   nSatVars;       // the number of used SAT variables
    Vec_Ptr_t *           vTargets;       // targets to be solved in this interval
    int                   iFramelast;     // last frame  
    int                   iOutputLast;    // last output
};

static inline int         Saig_BmcSatNum( Saig_Bmc_t * p, Aig_Obj_t * pObj )                                { return Vec_IntGetEntry( p->vObj2Var, pObj->Id );  }
static inline void        Saig_BmcSetSatNum( Saig_Bmc_t * p, Aig_Obj_t * pObj, int Num )                    { Vec_IntSetEntry(p->vObj2Var, pObj->Id, Num);      }

static inline Aig_Obj_t * Saig_BmcObjFrame( Saig_Bmc_t * p, Aig_Obj_t * pObj, int i )                       { return Vec_PtrGetEntry( p->vAig2Frm, p->nObjs*i+pObj->Id );     }
static inline void        Saig_BmcObjSetFrame( Saig_Bmc_t * p, Aig_Obj_t * pObj, int i, Aig_Obj_t * pNode ) { Vec_PtrSetEntry( p->vAig2Frm, p->nObjs*i+pObj->Id, pNode );     }

static inline Aig_Obj_t * Saig_BmcObjChild0( Saig_Bmc_t * p, Aig_Obj_t * pObj, int i )                   { assert( !Aig_IsComplement(pObj) ); return Aig_NotCond(Saig_BmcObjFrame(p, Aig_ObjFanin0(pObj), i), Aig_ObjFaninC0(pObj));  }
static inline Aig_Obj_t * Saig_BmcObjChild1( Saig_Bmc_t * p, Aig_Obj_t * pObj, int i )                   { assert( !Aig_IsComplement(pObj) ); return Aig_NotCond(Saig_BmcObjFrame(p, Aig_ObjFanin1(pObj), i), Aig_ObjFaninC1(pObj));  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Create manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Saig_Bmc_t * Saig_BmcManStart( Aig_Man_t * pAig, int nConfMaxOne, int nConfMaxAll, int nNodesMax, int fVerbose )
{
    Saig_Bmc_t * p;
    Aig_Obj_t * pObj;
    int i, Lit;
    assert( Aig_ManRegNum(pAig) > 0 );
    p = (Saig_Bmc_t *)malloc( sizeof(Saig_Bmc_t) );
    memset( p, 0, sizeof(Saig_Bmc_t) );
    // set parameters
    p->nFramesMax   = 1000000;
    p->nConfMaxOne  = nConfMaxOne;
    p->nConfMaxAll  = nConfMaxAll;
    p->nNodesMax    = nNodesMax;
    p->fVerbose     = fVerbose;
    p->pAig         = pAig;
    p->nObjs        = Aig_ManObjNumMax(pAig);
    // create node and variable mappings
    p->vAig2Frm     = Vec_PtrAlloc( 0 );
    Vec_PtrFill( p->vAig2Frm, 5 * p->nObjs, NULL );
    p->vObj2Var     = Vec_IntAlloc( 0 );
    Vec_IntFill( p->vObj2Var, 5 * p->nObjs, 0 );
    // start the AIG manager and map primary inputs
    p->pFrm         = Aig_ManStart( 5 * p->nObjs );
    Saig_ManForEachLo( pAig, pObj, i )
        Saig_BmcObjSetFrame( p, pObj, 0, Aig_ManConst0(p->pFrm) ); 
    // create SAT solver
    p->pSat         = sat_solver_new();
    sat_solver_setnvars( p->pSat, 2000 );
    p->nSatVars = 1;
    Lit = toLit( p->nSatVars );
    sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
    Saig_BmcSetSatNum( p, Aig_ManConst1(p->pFrm), p->nSatVars++ );
    // other data structures
    p->vTargets     = Vec_PtrAlloc( 0 );
    p->vVisited     = Vec_PtrAlloc( 0 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Delete manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_BmcManStop( Saig_Bmc_t * p )
{
    Aig_ManStop( p->pFrm  );
    Vec_PtrFree( p->vAig2Frm );
    Vec_IntFree( p->vObj2Var );
    sat_solver_delete( p->pSat );
    Vec_PtrFree( p->vTargets );
    Vec_PtrFree( p->vVisited );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Explores the possibility of constructing the output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Saig_BmcIntervalExplore_rec( Saig_Bmc_t * p, Aig_Obj_t * pObj, int i )
{
    Aig_Obj_t * pRes, * p0, * p1, * pConst1 = Aig_ManConst1(p->pAig);
    pRes = Saig_BmcObjFrame( p, pObj, i );
    if ( pRes != NULL )
        return pRes;
    if ( Saig_ObjIsPi( p->pAig, pObj ) )
        pRes = AIG_VISITED;
    else if ( Saig_ObjIsLo( p->pAig, pObj ) )
        pRes = Saig_BmcIntervalExplore_rec( p, Saig_ObjLoToLi(p->pAig, pObj), i-1 );
    else if ( Aig_ObjIsPo( pObj ) )
    {
        pRes = Saig_BmcIntervalExplore_rec( p, Aig_ObjFanin0(pObj), i );
        if ( pRes != AIG_VISITED )
            pRes = Saig_BmcObjChild0( p, pObj, i );
    }
    else 
    {
        p0 = Saig_BmcIntervalExplore_rec( p, Aig_ObjFanin0(pObj), i );
        if ( p0 != AIG_VISITED )
            p0 = Saig_BmcObjChild0( p, pObj, i );
        p1 = Saig_BmcIntervalExplore_rec( p, Aig_ObjFanin1(pObj), i );
        if ( p1 != AIG_VISITED )
            p1 = Saig_BmcObjChild1( p, pObj, i );

        if ( p0 == Aig_Not(p1) )
            pRes = Aig_Not(pConst1);
        else if ( Aig_Regular(p0) == pConst1 )
            pRes = (p0 == pConst1) ? p1 : Aig_Not(pConst1);
        else if ( Aig_Regular(p1) == pConst1 )
            pRes = (p1 == pConst1) ? p0 : Aig_Not(pConst1);
        else 
            pRes = AIG_VISITED;

        if ( pRes != pConst1 && pRes != Aig_Not(pConst1) )
            pRes = AIG_VISITED;
    }
    Saig_BmcObjSetFrame( p, pObj, i, pRes );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Performs the actual construction of the output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Saig_BmcIntervalConstruct_rec( Saig_Bmc_t * p, Aig_Obj_t * pObj, int i )
{
    Aig_Obj_t * pRes;
    pRes = Saig_BmcObjFrame( p, pObj, i );
    assert( pRes != NULL );
    if ( pRes != AIG_VISITED )
        return pRes;
    if ( Saig_ObjIsPi( p->pAig, pObj ) )
        pRes = Aig_ObjCreatePi(p->pFrm);
    else if ( Saig_ObjIsLo( p->pAig, pObj ) )
        pRes = Saig_BmcIntervalConstruct_rec( p, Saig_ObjLoToLi(p->pAig, pObj), i-1 );
    else if ( Aig_ObjIsPo( pObj ) )
    {
        Saig_BmcIntervalConstruct_rec( p, Aig_ObjFanin0(pObj), i );
        pRes = Saig_BmcObjChild0( p, pObj, i );
    }
    else 
    {
        Saig_BmcIntervalConstruct_rec( p, Aig_ObjFanin0(pObj), i );
        Saig_BmcIntervalConstruct_rec( p, Aig_ObjFanin1(pObj), i );
        pRes = Aig_And( p->pFrm, Saig_BmcObjChild0(p, pObj, i), Saig_BmcObjChild1(p, pObj, i) );
    }
    Saig_BmcObjSetFrame( p, pObj, i, pRes );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Adds new AIG nodes to the frames.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_BmcInterval( Saig_Bmc_t * p )
{
    Aig_Obj_t * pTarget, * pObj;
    int i, nNodes = Aig_ManNodeNum( p->pFrm );
    Vec_PtrClear( p->vTargets );
    for ( ; p->iFramelast < p->nFramesMax; p->iFramelast++, p->iOutputLast = 0 )
    {
        if ( p->iOutputLast == 0 )
        {
            Saig_BmcObjSetFrame( p, Aig_ManConst1(p->pAig), p->iFramelast, Aig_ManConst1(p->pFrm) );
            Saig_ManForEachPi( p->pAig, pObj, i )
                Saig_BmcObjSetFrame( p, pObj, p->iFramelast, Aig_ObjCreatePi(p->pFrm) ); 
        }
        for ( ; p->iOutputLast < Saig_ManPoNum(p->pAig); p->iOutputLast++ )
        {
            if ( Aig_ManNodeNum(p->pFrm) >= nNodes + p->nNodesMax )
                return;
            Saig_BmcIntervalExplore_rec( p, Aig_ManPo(p->pAig, p->iOutputLast), p->nFramesMax );
            pTarget = Saig_BmcIntervalConstruct_rec( p, Aig_ManPo(p->pAig, p->iOutputLast), p->nFramesMax );
            Vec_PtrPush( p->vTargets, pTarget );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Performs the actual construction of the output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Saig_BmcIntervalToAig_rec( Saig_Bmc_t * p, Aig_Man_t * pNew, Aig_Obj_t * pObj )
{
    if ( pObj->pData )
        return pObj->pData;
    Vec_PtrPush( p->vVisited, pObj );
    if ( Saig_BmcSatNum(p, pObj) || Aig_ObjIsPi(pObj) )
        return pObj->pData = Aig_ObjCreatePi(pNew);
    Saig_BmcIntervalToAig_rec( p, pNew, Aig_ObjFanin0(pObj) );
    Saig_BmcIntervalToAig_rec( p, pNew, Aig_ObjFanin1(pObj) );
    return pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Creates AIG of the newly added nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Saig_BmcIntervalToAig( Saig_Bmc_t * p )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    int i;
    pNew = Aig_ManStart( p->nNodesMax );
    Aig_ManConst1(p->pFrm)->pData = Aig_ManConst1(pNew);
    Vec_PtrClear( p->vVisited );
    Vec_PtrPush( p->vVisited, Aig_ManConst1(p->pFrm) );
    Vec_PtrForEachEntry( p->vTargets, pObj, i )
    {
        pObjNew = Saig_BmcIntervalToAig_rec( p, pNew, Aig_Regular(pObj) );
        Aig_ObjCreatePo( pNew, pObjNew );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Derives CNF for the newly added nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_BmcLoadCnf( Saig_Bmc_t * p, Cnf_Dat_t * pCnf )
{
    Aig_Obj_t * pObj, * pObjNew;
    int i, Lits[2], VarNumOld, VarNumNew;
    Vec_PtrForEachEntry( p->vVisited, pObj, i )
    {
        pObjNew   = pObj->pData;
        pObj->pData = NULL;
        VarNumNew = pCnf->pVarNums[ pObjNew->Id ];
        if ( VarNumNew == -1 )
            continue;
        VarNumOld = Saig_BmcSatNum( p, pObj );
        if ( VarNumOld == 0 )
        {
            Saig_BmcSetSatNum( p, pObj, VarNumNew );
            continue;
        }
        // add clauses connecting existing variables
        Lits[0] = toLitCond( VarNumOld, 0 );
        Lits[1] = toLitCond( VarNumNew, 1 );
        if ( !sat_solver_addclause( p->pSat, Lits, Lits+2 ) )
            assert( 0 );
        Lits[0] = toLitCond( VarNumOld, 1 );
        Lits[1] = toLitCond( VarNumNew, 0 );
        if ( !sat_solver_addclause( p->pSat, Lits, Lits+2 ) )
            assert( 0 );
    }
    // add CNF to the SAT solver
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( p->pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            break;
    if ( i < pCnf->nClauses )
        printf( "SAT solver became UNSAT after adding clauses.\n" );
}

/**Function*************************************************************

  Synopsis    [Solves targets with the given resource limit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_BmcSolveTargets( Saig_Bmc_t * p )
{
    Aig_Obj_t * pObj;
    int i, VarNum, Lit, RetValue;
    assert( Vec_PtrSize(p->vTargets) > 0 );
    Vec_PtrForEachEntry( p->vTargets, pObj, i )
    {
        if ( p->pSat->stats.conflicts > p->nConfMaxAll )
            return l_Undef;
        VarNum = Saig_BmcSatNum( p, Aig_Regular(pObj) );
        Lit = toLitCond( VarNum, Aig_IsComplement(pObj) );
        RetValue = sat_solver_solve( p->pSat, &Lit, &Lit + 1, (sint64)p->nConfMaxOne, (sint64)0, (sint64)0, (sint64)0 );
        if ( RetValue == l_False ) // unsat
            continue;
        if ( RetValue == l_Undef ) // undecided
            return l_Undef;
        // generate counter-example
        return l_True;
    }
    return l_False;
}

/**Function*************************************************************

  Synopsis    [Performs BMC with the given parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Saig_BmcPerform( Aig_Man_t * pAig, int nConfMaxOne, int nConfMaxAll, int nNodesMax, int fVerbose )
{
    Saig_Bmc_t * p;
    Aig_Man_t * pNew;
    Cnf_Dat_t * pCnf;
    int RetValue, clk = clock();
    p = Saig_BmcManStart( pAig, nConfMaxOne, nConfMaxAll, nNodesMax, fVerbose );
    while ( 1 )
    {
        // add new logic slice to frames
        Saig_BmcInterval( p );
        if ( Vec_PtrSize(p->vTargets) == 0 )
            break;
        // convert logic slice into new AIG
        pNew = Saig_BmcIntervalToAig( p );
        // derive CNF for the new AIG
        pCnf = Cnf_Derive( pNew, Aig_ManPoNum(pNew) );
        Cnf_DataLift( pCnf, p->nSatVars );
        p->nSatVars += pCnf->nVars;
        // add this CNF to the solver
        Saig_BmcLoadCnf( p, pCnf );
        Cnf_DataFree( pCnf );
        Aig_ManStop( pNew );
        // solve the targets
        RetValue = Saig_BmcSolveTargets( p );
        if ( RetValue != l_False )
            break;
    }
    if ( RetValue == l_True )
        printf( "BMC failed for output %d in frame %d.  ", p->iOutputLast, p->iFramelast );
    else // if ( RetValue == l_False || RetValue == l_Undef )
        printf( "BMC completed for %d timeframes.  ", p->iFramelast );
    PRT( "Time", clock() - clk );
    if ( p->iFramelast >= p->nFramesMax )
        printf( "Reached limit on the number of timeframes (%d).\n", p->nFramesMax );
    else if ( p->pSat->stats.conflicts > p->nConfMaxAll )
        printf( "Reached global conflict limit (%d).\n", p->nConfMaxAll );
    else
        printf( "Reached local conflict limit (%d).\n", p->nConfMaxOne );
    Saig_BmcManStop( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


