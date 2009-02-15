/**CFile****************************************************************

  FileName    [giaSolver.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Circuit-based SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSolver.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sat_Man_t_ Sat_Man_t;
struct Sat_Man_t_
{
    Gia_Man_t *    pGia;             // the original AIG manager
    Vec_Int_t *    vModel;           // satisfying PI assignment
    int            nConfs;           // cur number of conflicts
    int            nConfsMax;        // max number of conflicts
    int            iHead;            // variable queue 
    int            iTail;            // variable queue
    int            iJust;            // head of justification
    int            nTrail;           // variable queue size
    int            pTrail[0];        // variable queue data
};

static inline int          Sat_VarIsAssigned( Gia_Obj_t * pVar )      { return pVar->fMark0;                        }
static inline void         Sat_VarAssign( Gia_Obj_t * pVar )          { assert(!pVar->fMark0); pVar->fMark0 = 1;    }
static inline void         Sat_VarUnassign( Gia_Obj_t * pVar )        { assert(pVar->fMark0);  pVar->fMark0 = 0;    }
static inline int          Sat_VarValue( Gia_Obj_t * pVar )           { assert(pVar->fMark0);  return pVar->fMark1; }
static inline void         Sat_VarSetValue( Gia_Obj_t * pVar, int v ) { assert(pVar->fMark0);  pVar->fMark1 = v;    }

extern void Cec_ManPatVerifyPattern( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vPat );
extern void Cec_ManPatCleanMark0( Gia_Man_t * p, Gia_Obj_t * pObj );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sat_Man_t * Sat_ManCreate( Gia_Man_t * pGia )
{
    Sat_Man_t * p;
    p = (Sat_Man_t *)ABC_ALLOC( char, sizeof(Sat_Man_t) + sizeof(int)*Gia_ManObjNum(pGia) );
    memset( p, 0, sizeof(Sat_Man_t) );
    p->pGia   = pGia;
    p->nTrail = Gia_ManObjNum(pGia);
    p->vModel = Vec_IntAlloc( 1000 );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sat_ManDelete( Sat_Man_t * p )
{
    Vec_IntFree( p->vModel );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Sat_ManCancelUntil( Sat_Man_t * p, int iBound )
{
    Gia_Obj_t * pVar;
    int i;
    for ( i = p->iTail-1; i >= iBound; i-- )
    {
        pVar = Gia_ManObj( p->pGia, p->pTrail[i] );
        Sat_VarUnassign( pVar );
    }
    p->iTail = p->iTail = iBound;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Sat_ManDeriveModel( Sat_Man_t * p )
{
    Gia_Obj_t * pVar;
    int i;
    Vec_IntClear( p->vModel );
    for ( i = 0; i < p->iTail; i++ )
    {
        pVar = Gia_ManObj( p->pGia, p->pTrail[i] );
        if ( Gia_ObjIsCi(pVar) )
            Vec_IntPush( p->vModel, Gia_ObjCioId(pVar) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Sat_ManEnqueue( Sat_Man_t * p, Gia_Obj_t * pVar, int Value )
{
    assert( p->iTail < p->nTrail );
    Sat_VarAssign( pVar );
    Sat_VarSetValue( pVar, Value );
    p->pTrail[p->iTail++] = Gia_ObjId(p->pGia, pVar);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Sat_ManAssume( Sat_Man_t * p, Gia_Obj_t * pVar, int Value )
{
    assert( p->iHead == p->iTail );
    Sat_ManEnqueue( p, pVar, Value );
}

/**Function*************************************************************

  Synopsis    [Propagates one assignment.]

  Description [Returns 1 if there is no conflict, 0 otherwise.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sat_ManPropagateOne( Sat_Man_t * p, int iPos )
{
    Gia_Obj_t * pVar, * pFan0, * pFan1;
    pVar = Gia_ManObj( p->pGia, p->pTrail[iPos] );
    if ( Gia_ObjIsCi(pVar) )
        return 1;
    pFan0 = Gia_ObjFanin0(pVar);
    pFan1 = Gia_ObjFanin1(pVar);
    if ( Sat_VarValue(pVar) ) // positive
    {
        if ( Sat_VarIsAssigned(pFan0) )
        {
            if ( Sat_VarValue(pFan0) == Gia_ObjFaninC0(pVar) ) // negative -> conflict
                return 0;
            // check second var
            if ( Sat_VarIsAssigned(pFan1) )
            {
                if ( Sat_VarValue(pFan1) == Gia_ObjFaninC1(pVar) ) // negative -> conflict
                    return 0;
                // positive + positive -> nothing to do
                return 1;
            }
        }
        else
        {
            // pFan0 unassigned -> enqueue first var
            Sat_ManEnqueue( p, pFan0, !Gia_ObjFaninC0(pVar) );
            // check second var
            if ( Sat_VarIsAssigned(pFan1) )
            {
                if ( Sat_VarValue(pFan1) == Gia_ObjFaninC1(pVar) ) // negative -> conflict
                    return 0;
                // positive + positive -> nothing to do
                return 1;
            }
        }
        // unassigned -> enqueue second var
        Sat_ManEnqueue( p, pFan1, !Gia_ObjFaninC1(pVar) );
    }
    else // negative
    {
        if ( Sat_VarIsAssigned(pFan0) )
        {
            if ( Sat_VarValue(pFan0) == Gia_ObjFaninC0(pVar) ) // negative -> nothing to do
                return 1;
            if ( Sat_VarIsAssigned(pFan1) )
            {
                if ( Sat_VarValue(pFan1) == Gia_ObjFaninC1(pVar) ) // negative -> nothing to do
                    return 1;
                // positive + positive -> conflict
                return 0;
            }
            // positive + unassigned -> enqueue second var
            Sat_ManEnqueue( p, pFan1, Gia_ObjFaninC1(pVar) );
        }
        else
        {
            if ( Sat_VarIsAssigned(pFan1) )
            {
                if ( Sat_VarValue(pFan1) == Gia_ObjFaninC1(pVar) ) // negative -> nothing to do
                    return 1;
                // unassigned + positive -> enqueue first var
                Sat_ManEnqueue( p, pFan0, Gia_ObjFaninC0(pVar) );
            }
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Propagates assignments.]

  Description [Returns 1 if there is no conflict.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sat_ManPropagate( Sat_Man_t * p )
{
    assert( p->iHead <= p->iTail );
    for ( ; p->iHead < p->iTail; p->iHead++ )
        if ( !Sat_ManPropagateOne( p, p->pTrail[p->iHead] ) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Propagates one assignment.]

  Description [Returns 1 if justified, 0 if conflict, -1 if needs justification.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sat_ManJustifyNextOne( Sat_Man_t * p, int iPos )
{
    Gia_Obj_t * pVar, * pFan0, * pFan1;
    pVar = Gia_ManObj( p->pGia, p->pTrail[iPos] );
    if ( Gia_ObjIsCi(pVar) )
        return 1;
    pFan0 = Gia_ObjFanin0(pVar);
    pFan1 = Gia_ObjFanin1(pVar);
    if ( Sat_VarValue(pVar) ) // positive
        return 1;
    // nevative
    if ( Sat_VarIsAssigned(pFan0) )
    {
        if ( Sat_VarValue(pFan0) == Gia_ObjFaninC0(pVar) ) // negative -> already justified
            return 1;
        // positive
        if ( Sat_VarIsAssigned(pFan1) )
        {
            if ( Sat_VarValue(pFan1) == Gia_ObjFaninC1(pVar) ) // negative -> already justified
                return 1;
            // positive -> conflict
            return 0;
        }
        // unasigned -> propagate
        Sat_ManAssume( p, pFan1, Gia_ObjFaninC1(pVar) );
        return Sat_ManPropagate(p);
    }
    if ( Sat_VarIsAssigned(pFan1) )
    {
        if ( Sat_VarValue(pFan1) == Gia_ObjFaninC1(pVar) ) // negative -> already justified
            return 1;
        // positive
        assert( !Sat_VarIsAssigned(pFan0) );
        // unasigned -> propagate
        Sat_ManAssume( p, pFan0, Gia_ObjFaninC0(pVar) );
        return Sat_ManPropagate(p);
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Justifies assignments.]

  Description [Returns 1 for UNSAT, 0 for SAT, -1 for UNDECIDED.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sat_ManJustify( Sat_Man_t * p )
{
    Gia_Obj_t * pVar, * pFan0, * pFan1;
    int RetValue, iState, iJustState;
    if ( p->nConfs && p->nConfs >= p->nConfsMax )
        return -1;
    // get the next variable to justify
    assert( p->iJust <= p->iTail );
    iJustState = p->iJust;
    for ( ; p->iJust < p->iTail; p->iJust++ )
    {
        RetValue = Sat_ManJustifyNextOne( p, p->pTrail[p->iJust] );
        if ( RetValue == 0 )
            return 1;
        if ( RetValue == -1 )
            break;
    }
    if ( p->iJust == p->iTail ) // could not find
        return 0;
    // found variable to justify
    pVar = Gia_ManObj( p->pGia, p->pTrail[p->iJust] );
    pFan0 = Gia_ObjFanin0(pVar);
    pFan1 = Gia_ObjFanin1(pVar);
    assert( !Sat_VarValue(pVar) && !Sat_VarIsAssigned(pFan0) && !Sat_VarIsAssigned(pFan1) );
    // remember the state of the stack
    iState = p->iHead;
    // try to justify by setting first fanin to 0
    Sat_ManAssume( p, pFan0, Gia_ObjFaninC0(pVar) );
    if ( Sat_ManPropagate(p) ) 
    {
        RetValue = Sat_ManJustify(p);
        if ( RetValue != 1 )
            return RetValue;
    }
    Sat_ManCancelUntil( p, iState );
    // try to justify by setting second fanin to 0
    Sat_ManAssume( p, pFan1, Gia_ObjFaninC1(pVar) );
    if ( Sat_ManPropagate(p) ) 
    {
        RetValue = Sat_ManJustify(p);
        if ( RetValue != 1 )
            return RetValue;
    }
    Sat_ManCancelUntil( p, iState );
    p->iJust = iJustState;
    p->nConfs++;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Runs one call to the SAT solver.]

  Description [Returns 1 for UNSAT, 0 for SAT, -1 for UNDECIDED.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sat_ManPrepare( Sat_Man_t * p, int * pLits, int nLits, int nConfsMax )
{
    Gia_Obj_t * pVar;
    int i;
    // double check that vars are unassigned
    Gia_ManForEachObj( p->pGia, pVar, i )
        assert( !Sat_VarIsAssigned(pVar) );
    // prepare
    p->iHead = p->iTail = p->iJust = 0;
    p->nConfsMax = nConfsMax;
    // assign literals
    for ( i = 0; i < nLits; i++ )
    {
        pVar = Gia_ManObj( p->pGia, Gia_Lit2Var(pLits[i]) );
        if ( Sat_VarIsAssigned(pVar) ) // assigned
        {
            if ( Sat_VarValue(pVar) != Gia_LitIsCompl(pLits[i]) ) // compatible assignment
                continue;
        }
        else // unassigned
        {
            Sat_ManAssume( p, pVar, !Gia_LitIsCompl(pLits[i]) );
            if ( Sat_ManPropagate(p) ) 
                continue;
        }
        // conflict
        Sat_ManCancelUntil( p, 0 );
        return 1;
    }
    assert( p->iHead == p->iTail );
    return 0;
}


/**Function*************************************************************

  Synopsis    [Runs one call to the SAT solver.]

  Description [Returns 1 for UNSAT, 0 for SAT, -1 for UNDECIDED.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sat_ManSolve( Sat_Man_t * p, int * pLits, int nLits, int nConfsMax )
{
    int RetValue;
    // propagate the assignments
    if ( Sat_ManPrepare( p, pLits, nLits, nConfsMax ) )
        return 1;
    // justify the assignments
    RetValue = Sat_ManJustify( p );
    if ( RetValue == 0 ) // SAT
        Sat_ManDeriveModel( p );
    // return the solver to the initial state
    Sat_ManCancelUntil( p, 0 );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Testing the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sat_ManTest( Gia_Man_t * pGia, Gia_Obj_t * pObj, int nConfsMax )
{
    Sat_Man_t * p;
    int RetValue, iLit;
    assert( Gia_ObjIsCo(pObj) );
    p = Sat_ManCreate( pGia );
    iLit = Gia_LitNot( Gia_ObjFaninLit0p(pGia, pObj) );
    RetValue = Sat_ManSolve( p, &iLit, 1, nConfsMax );
    if ( RetValue == 0 )
    {
        Cec_ManPatVerifyPattern( pGia, pObj, p->vModel );
        Cec_ManPatCleanMark0( pGia, pObj );
    }
    Sat_ManDelete( p );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


