/**CFile****************************************************************

  FileName    [giaCSat2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [A simple circuit-based solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCSat2.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Cbs_Par_t_ Cbs_Par_t;
struct Cbs_Par_t_
{
    // conflict limits
    int           nBTLimit;     // limit on the number of conflicts
    int           nJustLimit;   // limit on the size of justification queue
    // current parameters
    int           nBTThis;      // number of conflicts
    int           nJustThis;    // max size of the frontier
    int           nBTTotal;     // total number of conflicts
    int           nJustTotal;   // total size of the frontier
    // decision heuristics
    int           fUseHighest;  // use node with the highest ID
    int           fUseLowest;   // use node with the highest ID
    int           fUseMaxFF;    // use node with the largest fanin fanout
    // other
    int           fVerbose;
};

typedef struct Cbs_Que_t_ Cbs_Que_t;
struct Cbs_Que_t_
{
    int           iHead;        // beginning of the queue
    int           iTail;        // end of the queue
    int           nSize;        // allocated size
    Gia_Obj_t **  pData;        // nodes stored in the queue
};

typedef struct Cbs_Man_t_ Cbs_Man_t;
struct Cbs_Man_t_
{
    Cbs_Par_t     Pars;         // parameters
    Gia_Man_t *   pAig;         // AIG manager
    Cbs_Que_t     pProp;        // propagation queue
    Cbs_Que_t     pJust;        // justification queue
    Vec_Int_t *   vModel;       // satisfying assignment
};

static inline int   Cbs_VarIsAssigned( Gia_Obj_t * pVar )      { return pVar->fMark0;                        }
static inline void  Cbs_VarAssign( Gia_Obj_t * pVar )          { assert(!pVar->fMark0); pVar->fMark0 = 1;    }
static inline void  Cbs_VarUnassign( Gia_Obj_t * pVar )        { assert(pVar->fMark0);  pVar->fMark0 = 0; pVar->fMark1 = 0;         }
static inline int   Cbs_VarValue( Gia_Obj_t * pVar )           { assert(pVar->fMark0);  return pVar->fMark1; }
static inline void  Cbs_VarSetValue( Gia_Obj_t * pVar, int v ) { assert(pVar->fMark0);  pVar->fMark1 = v;    }
static inline int   Cbs_VarIsJust( Gia_Obj_t * pVar )          { return Gia_ObjIsAnd(pVar) && !Cbs_VarIsAssigned(Gia_ObjFanin0(pVar)) && !Cbs_VarIsAssigned(Gia_ObjFanin1(pVar)); } 
static inline int   Cbs_VarFanin0Value( Gia_Obj_t * pVar )     { return !Cbs_VarIsAssigned(Gia_ObjFanin0(pVar)) ? 2 : (Cbs_VarValue(Gia_ObjFanin0(pVar)) ^ Gia_ObjFaninC0(pVar)); }
static inline int   Cbs_VarFanin1Value( Gia_Obj_t * pVar )     { return !Cbs_VarIsAssigned(Gia_ObjFanin1(pVar)) ? 2 : (Cbs_VarValue(Gia_ObjFanin1(pVar)) ^ Gia_ObjFaninC1(pVar)); }

#define Cbs_QueForEachEntry( Que, pObj, i )                    \
    for ( i = (Que).iHead; (i < (Que).iTail) && ((pObj) = (Que).pData[i]); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets default values of the parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cbs_SetDefaultParams( Cbs_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Cbs_Par_t) );
    pPars->nBTLimit    =  1000;   // limit on the number of conflicts
    pPars->nJustLimit  =   100;   // limit on the size of justification queue
    pPars->fUseHighest =     1;   // use node with the highest ID
    pPars->fUseLowest  =     0;   // use node with the highest ID
    pPars->fUseMaxFF   =     0;   // use node with the largest fanin fanout
    pPars->fVerbose    =     1;   // print detailed statistics
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cbs_Man_t * Cbs_ManAlloc()
{
    Cbs_Man_t * p;
    p = ABC_CALLOC( Cbs_Man_t, 1 );
    p->pProp.nSize = p->pJust.nSize = 10000;
    p->pProp.pData = ABC_ALLOC( Gia_Obj_t *, p->pProp.nSize );
    p->pJust.pData = ABC_ALLOC( Gia_Obj_t *, p->pJust.nSize );
    p->vModel = Vec_IntAlloc( 1000 );
    Cbs_SetDefaultParams( &p->Pars );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cbs_ManStop( Cbs_Man_t * p )
{
    Vec_IntFree( p->vModel );
    ABC_FREE( p->pProp.pData );
    ABC_FREE( p->pJust.pData );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Returns satisfying assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cbs_ReadModel( Cbs_Man_t * p )
{
    return p->vModel;
}




/**Function*************************************************************

  Synopsis    [Returns 1 if the solver is out of limits.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs_ManCheckLimits( Cbs_Man_t * p )
{
    return p->Pars.nJustThis > p->Pars.nJustLimit || p->Pars.nBTThis > p->Pars.nBTLimit;
}

/**Function*************************************************************

  Synopsis    [Saves the satisfying assignment as an array of literals.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs_ManSaveModel( Cbs_Man_t * p, Vec_Int_t * vCex )
{
    Gia_Obj_t * pVar;
    int i;
    Vec_IntClear( vCex );
    p->pProp.iHead = 0;
    Cbs_QueForEachEntry( p->pProp, pVar, i )
        if ( Gia_ObjIsCi(pVar) )
            Vec_IntPush( vCex, Gia_Var2Lit(Gia_ObjId(p->pAig,pVar), !Cbs_VarValue(pVar)) );
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs_QueIsEmpty( Cbs_Que_t * p )
{
    return p->iHead == p->iTail;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs_QuePush( Cbs_Que_t * p, Gia_Obj_t * pObj )
{
    if ( p->iTail == p->nSize )
    {
        p->nSize *= 2;
        p->pData = ABC_REALLOC( Gia_Obj_t *, p->pData, p->nSize ); 
    }
    p->pData[p->iTail++] = pObj;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the object in the queue.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs_QueHasNode( Cbs_Que_t * p, Gia_Obj_t * pObj )
{
    Gia_Obj_t * pTemp;
    int i;
    Cbs_QueForEachEntry( *p, pTemp, i )
        if ( pTemp == pObj )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs_QueStore( Cbs_Que_t * p, int * piHeadOld, int * piTailOld )
{
    int i;
    *piHeadOld = p->iHead;
    *piTailOld = p->iTail;
    for ( i = *piHeadOld; i < *piTailOld; i++ )
        Cbs_QuePush( p, p->pData[i] );
    p->iHead = *piTailOld;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs_QueRestore( Cbs_Que_t * p, int iHeadOld, int iTailOld )
{
    p->iHead = iHeadOld;
    p->iTail = iTailOld;
}


/**Function*************************************************************

  Synopsis    [Max number of fanins fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs_VarFaninFanoutMax( Cbs_Man_t * p, Gia_Obj_t * pObj )
{
    int Count0, Count1;
    assert( !Gia_IsComplement(pObj) );
    assert( Gia_ObjIsAnd(pObj) );
    Count0 = Gia_ObjRefs( p->pAig, Gia_ObjFanin0(pObj) );
    Count1 = Gia_ObjRefs( p->pAig, Gia_ObjFanin1(pObj) );
    return ABC_MAX( Count0, Count1 );
}

/**Function*************************************************************

  Synopsis    [Find variable with the highest ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Gia_Obj_t * Cbs_ManDecideHighest( Cbs_Man_t * p )
{
    Gia_Obj_t * pObj, * pObjMax = NULL;
    int i;
    Cbs_QueForEachEntry( p->pJust, pObj, i )
        if ( pObjMax == NULL || pObjMax < pObj )
            pObjMax = pObj;
    return pObjMax;
}

/**Function*************************************************************

  Synopsis    [Find variable with the lowest ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Gia_Obj_t * Cbs_ManDecideLowest( Cbs_Man_t * p )
{
    Gia_Obj_t * pObj, * pObjMin = NULL;
    int i;
    Cbs_QueForEachEntry( p->pJust, pObj, i )
        if ( pObjMin == NULL || pObjMin > pObj )
            pObjMin = pObj;
    return pObjMin;
}

/**Function*************************************************************

  Synopsis    [Find variable with the maximum number of fanin fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Gia_Obj_t * Cbs_ManDecideMaxFF( Cbs_Man_t * p )
{
    Gia_Obj_t * pObj, * pObjMax = NULL;
    int i, iMaxFF = 0, iCurFF;
    assert( p->pAig->pRefs != NULL );
    Cbs_QueForEachEntry( p->pJust, pObj, i )
    {
        iCurFF = Cbs_VarFaninFanoutMax( p, pObj );
        assert( iCurFF > 0 );
        if ( iMaxFF < iCurFF )
        {
            iMaxFF = iCurFF;
            pObjMax = pObj;
        }
    }
    return pObjMax;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs_ManCancelUntil( Cbs_Man_t * p, int iBound )
{
    Gia_Obj_t * pVar;
    int i;
    assert( iBound <= p->pProp.iTail );
    p->pProp.iHead = iBound;
    Cbs_QueForEachEntry( p->pProp, pVar, i )
        Cbs_VarUnassign( pVar );
    p->pProp.iTail = iBound;
}

/**Function*************************************************************

  Synopsis    [Assigns the variables a value.]

  Description [Returns 1 if conflict; 0 if no conflict.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs_ManAssign( Cbs_Man_t * p, Gia_Obj_t * pObj )
{
    Gia_Obj_t * pObjR = Gia_Regular(pObj);
    assert( Gia_ObjIsCand(pObjR) );
    assert( !Cbs_VarIsAssigned(pObjR) );
    Cbs_VarAssign( pObjR );
    Cbs_VarSetValue( pObjR, !Gia_IsComplement(pObj) );
    Cbs_QuePush( &p->pProp, pObjR );
}

/**Function*************************************************************

  Synopsis    [Propagates a variable.]

  Description [Returns 1 if conflict; 0 if no conflict.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs_ManPropagateOne( Cbs_Man_t * p, Gia_Obj_t * pVar )
{
    int Value0, Value1;
    assert( !Gia_IsComplement(pVar) );
    assert( Cbs_VarIsAssigned(pVar) );
    if ( Gia_ObjIsCi(pVar) )
        return 0;
    assert( Gia_ObjIsAnd(pVar) );
    Value0 = Cbs_VarFanin0Value(pVar);
    Value1 = Cbs_VarFanin1Value(pVar);
    if ( Cbs_VarValue(pVar) )
    { // value is 1
        if ( Value0 == 0 || Value1 == 0 ) // one is 0
            return 1;
        if ( Value0 == 2 ) // first is unassigned
            Cbs_ManAssign( p, Gia_ObjChild0(pVar) );
        if ( Value1 == 2 ) // first is unassigned
            Cbs_ManAssign( p, Gia_ObjChild1(pVar) );
        return 0;
    }
    // value is 0
    if ( Value0 == 0 || Value1 == 0 ) // one is 0
        return 0;
    if ( Value0 == 1 && Value1 == 1 ) // both are 1
        return 1;
    if ( Value0 == 1 || Value1 == 1 ) // one is 1 
    {
        if ( Value0 == 2 ) // first is unassigned
            Cbs_ManAssign( p, Gia_Not(Gia_ObjChild0(pVar)) );
        if ( Value1 == 2 ) // first is unassigned
            Cbs_ManAssign( p, Gia_Not(Gia_ObjChild1(pVar)) );
        return 0;
    }
    assert( Cbs_VarIsJust(pVar) );
    assert( !Cbs_QueHasNode( &p->pJust, pVar ) );
    Cbs_QuePush( &p->pJust, pVar );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Propagates a variable.]

  Description [Returns 1 if conflict; 0 if no conflict.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs_ManPropagateTwo( Cbs_Man_t * p, Gia_Obj_t * pVar )
{
    int Value0, Value1;
    assert( !Gia_IsComplement(pVar) );
    assert( Gia_ObjIsAnd(pVar) );
    assert( Cbs_VarIsAssigned(pVar) );
    assert( !Cbs_VarValue(pVar) );
    Value0 = Cbs_VarFanin0Value(pVar);
    Value1 = Cbs_VarFanin1Value(pVar);
    // value is 0
    if ( Value0 == 0 || Value1 == 0 ) // one is 0
        return 0;
    if ( Value0 == 1 && Value1 == 1 ) // both are 1
        return 1;
    assert( Value0 == 1 || Value1 == 1 );
    if ( Value0 == 2 ) // first is unassigned
        Cbs_ManAssign( p, Gia_Not(Gia_ObjChild0(pVar)) );
    if ( Value1 == 2 ) // first is unassigned
        Cbs_ManAssign( p, Gia_Not(Gia_ObjChild1(pVar)) );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Propagates all variables.]

  Description [Returns 1 if conflict; 0 if no conflict.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cbs_ManPropagate( Cbs_Man_t * p )
{
    Gia_Obj_t * pVar;
    int i, k;
    while ( 1 )
    {
        Cbs_QueForEachEntry( p->pProp, pVar, i )
        {
            if ( Cbs_ManPropagateOne( p, pVar ) )
                return 1;
        }
        p->pProp.iHead = p->pProp.iTail;
        k = p->pJust.iHead;
        Cbs_QueForEachEntry( p->pJust, pVar, i )
        {
            if ( Cbs_VarIsJust( pVar ) )
                p->pJust.pData[k++] = pVar;
            else if ( Cbs_ManPropagateTwo( p, pVar ) )
                return 1;
        }
        if ( k == p->pJust.iTail )
            break;
        p->pJust.iTail = k;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Solve the problem recursively.]

  Description [Returns 1 if unsat or undecided; 0 if satisfiable.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cbs_ManSolve_rec( Cbs_Man_t * p )
{
    Gia_Obj_t * pVar;
    int iPropHead, iJustHead, iJustTail;
    // propagate assignments
    assert( !Cbs_QueIsEmpty(&p->pProp) );
    if ( Cbs_ManPropagate( p ) )
        return 1;
    // check for satisfying assignment
    assert( Cbs_QueIsEmpty(&p->pProp) );
    if ( Cbs_QueIsEmpty(&p->pJust) )
        return 0;
    // quit using resource limits
    p->Pars.nBTThis++;
    p->Pars.nJustThis = ABC_MAX( p->Pars.nJustThis, p->pJust.iTail - p->pJust.iHead );
    if ( Cbs_ManCheckLimits( p ) )
        return 1;
    // remember the state before branching
    iPropHead = p->pProp.iHead;
    Cbs_QueStore( &p->pJust, &iJustHead, &iJustTail );
    // find the decision variable
    if ( p->Pars.fUseHighest )
        pVar = Cbs_ManDecideHighest( p );
    else if ( p->Pars.fUseLowest )
        pVar = Cbs_ManDecideLowest( p );
    else if ( p->Pars.fUseMaxFF )
        pVar = Cbs_ManDecideMaxFF( p );
    else assert( 0 );
    assert( Cbs_VarIsJust( pVar ) );
    // decide using fanout count!
    if ( Gia_ObjRefs(p->pAig, Gia_ObjFanin0(pVar)) < Gia_ObjRefs(p->pAig, Gia_ObjFanin1(pVar)) )
    {
        // decide on first fanin
        Cbs_ManAssign( p, Gia_Not(Gia_ObjChild0(pVar)) );
        if ( !Cbs_ManSolve_rec( p ) )
            return 0;
        if ( Cbs_ManCheckLimits( p ) )
            return 1;
        Cbs_ManCancelUntil( p, iPropHead );
        Cbs_QueRestore( &p->pJust, iJustHead, iJustTail );
        // decide on second fanin
        Cbs_ManAssign( p, Gia_Not(Gia_ObjChild1(pVar)) );
    }
    else
    {
        // decide on first fanin
        Cbs_ManAssign( p, Gia_Not(Gia_ObjChild1(pVar)) );
        if ( !Cbs_ManSolve_rec( p ) )
            return 0;
        if ( Cbs_ManCheckLimits( p ) )
            return 1;
        Cbs_ManCancelUntil( p, iPropHead );
        Cbs_QueRestore( &p->pJust, iJustHead, iJustTail );
        // decide on second fanin
        Cbs_ManAssign( p, Gia_Not(Gia_ObjChild0(pVar)) );
    }
    if ( !Cbs_ManSolve_rec( p ) )
        return 0;
    if ( Cbs_ManCheckLimits( p ) )
        return 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Looking for a satisfying assignment of the node.]

  Description [Assumes that each node has flag pObj->fMark0 set to 0.
  Returns 1 if unsatisfiable, 0 if satisfiable, and -1 if undecided.
  The node may be complemented. ]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cbs_ManSolve( Cbs_Man_t * p, Gia_Obj_t * pObj )
{
//    Gia_Obj_t * pTemp;
//    int i;
    int RetValue;
//    Gia_ManForEachObj( p->pAig, pTemp, i )
//        assert( pTemp->fMark0 == 0 );
    assert( !p->pProp.iHead && !p->pProp.iTail );
    assert( !p->pJust.iHead && !p->pJust.iTail );
    p->Pars.nBTThis = p->Pars.nJustThis = 0;
    Cbs_ManAssign( p, pObj );
    RetValue = Cbs_ManSolve_rec( p );
    if ( RetValue == 0 )
        Cbs_ManSaveModel( p, p->vModel );
    Cbs_ManCancelUntil( p, 0 );
    p->pJust.iHead = p->pJust.iTail = 0;
    p->Pars.nBTTotal += p->Pars.nBTThis;
    p->Pars.nJustTotal = ABC_MAX( p->Pars.nJustTotal, p->Pars.nJustThis );
    if ( Cbs_ManCheckLimits( p ) )
        return -1;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Procedure to test the new SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cbs_ManSolveTest( Gia_Man_t * pGia )
{
    extern void Gia_SatVerifyPattern( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vCex, Vec_Int_t * vVisit );
    int nConfsMax = 1000;
    int CountUnsat, CountSat, CountUndec;
    Cbs_Man_t * p; 
    Vec_Int_t * vCex;
    Vec_Int_t * vVisit;
    Gia_Obj_t * pRoot; 
    int i, RetValue, clk = clock();
    Gia_ManCreateRefs( pGia );
    // create logic network
    p = Cbs_ManAlloc();
    p->pAig = pGia;
    // prepare AIG
    Gia_ManCleanValue( pGia );
    Gia_ManCleanMark0( pGia );
    Gia_ManCleanMark1( pGia );
//    vCex   = Vec_IntAlloc( 100 );
    vVisit = Vec_IntAlloc( 100 );
    // solve for each output
    CountUnsat = CountSat = CountUndec = 0;
    Gia_ManForEachCo( pGia, pRoot, i )
    {
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pRoot)) )
            continue;

//        Gia_ManIncrementTravId( pGia );

//printf( "Output %6d : ", i );
//        iLit = Gia_Var2Lit( Gia_ObjHandle(Gia_ObjFanin0(pRoot)), Gia_ObjFaninC0(pRoot) );
//        RetValue = Cbs_ManSolve( p, &iLit, 1, nConfsMax, vCex );
        RetValue = Cbs_ManSolve( p, Gia_ObjChild0(pRoot) );
        if ( RetValue == 1 )
            CountUnsat++;
        else if ( RetValue == -1 )
            CountUndec++;
        else 
        {
            int iLit, k;
            vCex = Cbs_ReadModel( p );

//        printf( "complemented = %d.  ", Gia_ObjFaninC0(pRoot) );
//printf( "conflicts = %6d  max-frontier = %6d \n", p->Pars.nBTThis, p->Pars.nJustThis );
//            Vec_IntForEachEntry( vCex, iLit, k )
//                printf( "%s%d ", Gia_LitIsCompl(iLit)? "!": "", Gia_ObjCioId(Gia_ManObj(pGia,Gia_Lit2Var(iLit))) );
//            printf( "\n" );

            Gia_SatVerifyPattern( pGia, pRoot, vCex, vVisit );
            assert( RetValue == 0 );
            CountSat++;
        }
//        Gia_ManCheckMark0( p );
//        Gia_ManCheckMark1( p );
    }
    Cbs_ManStop( p );
//    Vec_IntFree( vCex );
    Vec_IntFree( vVisit );
    printf( "Unsat = %d. Sat = %d. Undec = %d.  ", CountUnsat, CountSat, CountUndec );
    ABC_PRT( "Time", clock() - clk );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


