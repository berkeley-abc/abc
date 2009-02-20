/**CFile****************************************************************

  FileName    [giaCsat1.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Circuit-based SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCsat1.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////


typedef struct Css_Fan_t_ Css_Fan_t;
struct Css_Fan_t_
{
    unsigned       iFan     : 31;    // ID of the fanin/fanout
    unsigned       fCompl   :  1;    // complemented attribute
};

typedef struct Css_Obj_t_ Css_Obj_t;
struct Css_Obj_t_
{
    unsigned       fCi      :  1;    // terminal node CI
    unsigned       fCo      :  1;    // terminal node CO
    unsigned       fAssign  :  1;    // assigned variable
    unsigned       fValue   :  1;    // variable value
    unsigned       fPhase   :  1;    // value under 000 pattern
    unsigned       nFanins  :  5;    // the number of fanins
    unsigned       nFanouts : 22;    // total number of fanouts
    unsigned       hHandle;          // application specific data
    union {
    unsigned       iFanouts;         // application specific data
    int            TravId;           // ID of the node
    };
    Css_Fan_t      Fanios[0];        // the array of fanins/fanouts
};

typedef struct Css_Man_t_ Css_Man_t;
struct Css_Man_t_
{
    Gia_Man_t *    pGia;             // the original AIG manager
    Vec_Int_t *    vCis;             // the vector of CIs (PIs + LOs)
    Vec_Int_t *    vCos;             // the vector of COs (POs + LIs)
    int            nObjs;            // the number of objects
    int            nNodes;           // the number of nodes
    int *          pObjData;         // the logic network defined for the AIG
    int            nObjData;         // the size of array to store the logic network
    int *          pLevels;          // the linked lists of levels
    int            nLevels;          // the max number of logic levels
    int            nTravIds;         // traversal ID to mark the cones
    Vec_Int_t *    vTrail;           // sequence of assignments
    int            nConfsMax;         // max number of conflicts
};

static inline unsigned    Gia_ObjHandle( Gia_Obj_t * pObj )                           { return pObj->Value;                                 } 

static inline int         Css_ObjIsCi( Css_Obj_t * pObj )                             { return pObj->fCi;                                   } 
static inline int         Css_ObjIsCo( Css_Obj_t * pObj )                             { return pObj->fCo;                                   } 
static inline int         Css_ObjIsNode( Css_Obj_t * pObj )                           { return!pObj->fCi &&!pObj->fCo && pObj->nFanins > 0; } 
static inline int         Css_ObjIsConst0( Css_Obj_t * pObj )                         { return!pObj->fCi &&!pObj->fCo && pObj->nFanins == 0;} 

static inline int         Css_ObjFaninNum( Css_Obj_t * pObj )                         { return pObj->nFanins;                               } 
static inline int         Css_ObjFanoutNum( Css_Obj_t * pObj )                        { return pObj->nFanouts;                              } 
static inline int         Css_ObjSize( Css_Obj_t * pObj )                             { return sizeof(Css_Obj_t) / 4 + pObj->nFanins + pObj->nFanouts;  } 
static inline int         Css_ObjId( Css_Obj_t * pObj )                               { assert( 0 ); return -1;                             } 

static inline Css_Obj_t * Css_ManObj( Css_Man_t * p, unsigned iHandle )               { return (Css_Obj_t *)(p->pObjData + iHandle);        } 
static inline Css_Obj_t * Css_ObjFanin( Css_Obj_t * pObj, int i )                     { return (Css_Obj_t *)(((int *)pObj) - pObj->Fanios[i].iFan);               } 
static inline Css_Obj_t * Css_ObjFanout( Css_Obj_t * pObj, int i )                    { return (Css_Obj_t *)(((int *)pObj) + pObj->Fanios[pObj->nFanins+i].iFan); } 
static inline int         Css_ObjFaninC( Css_Obj_t * pObj, int i )                    { return pObj->Fanios[i].fCompl;                      } 
static inline int         Css_ObjFanoutC( Css_Obj_t * pObj, int i )                   { return pObj->Fanios[pObj->nFanins+i].fCompl;        } 

static inline int         Css_ManObjNum( Css_Man_t * p )                              { return p->nObjs;                                    } 
static inline int         Css_ManNodeNum( Css_Man_t * p )                             { return p->nNodes;                                   } 
 
static inline void        Css_ManIncrementTravId( Css_Man_t * p )                     { p->nTravIds++;                                      }
static inline void        Css_ObjSetTravId( Css_Obj_t * pObj, int TravId )            { pObj->TravId = TravId;                              }
static inline void        Css_ObjSetTravIdCurrent( Css_Man_t * p, Css_Obj_t * pObj )  { pObj->TravId = p->nTravIds;                         }
static inline void        Css_ObjSetTravIdPrevious( Css_Man_t * p, Css_Obj_t * pObj ) { pObj->TravId = p->nTravIds - 1;                     }
static inline int         Css_ObjIsTravIdCurrent( Css_Man_t * p, Css_Obj_t * pObj )   { return ((int)pObj->TravId == p->nTravIds);          }
static inline int         Css_ObjIsTravIdPrevious( Css_Man_t * p, Css_Obj_t * pObj )  { return ((int)pObj->TravId == p->nTravIds - 1);      }

static inline int   Css_VarIsAssigned( Css_Obj_t * pVar )      { return pVar->fAssign;                        }
static inline void  Css_VarAssign( Css_Obj_t * pVar )          { assert(!pVar->fAssign); pVar->fAssign = 1;   }
static inline void  Css_VarUnassign( Css_Obj_t * pVar )        { assert(pVar->fAssign);  pVar->fAssign = 0;   }
static inline int   Css_VarValue( Css_Obj_t * pVar )           { assert(pVar->fAssign);  return pVar->fValue; }
static inline void  Css_VarSetValue( Css_Obj_t * pVar, int v ) { assert(pVar->fAssign);  pVar->fValue = v;    }

#define Css_ManForEachObj( p, pObj, i )               \
    for ( i = 0; (i < p->nObjData) && (pObj = Css_ManObj(p,i)); i += Css_ObjSize(pObj) )
#define Css_ManForEachObjVecStart( vVec, p, pObj, i, iStart )            \
    for ( i = iStart; (i < Vec_IntSize(vVec)) && (pObj = Css_ManObj(p,Vec_IntEntry(vVec,i))); i++ )
#define Css_ManForEachNode( p, pObj, i )              \
    for ( i = 0; (i < p->nObjData) && (pObj = Css_ManObj(p,i)); i += Css_ObjSize(pObj) ) if ( Css_ObjIsTerm(pObj) ) {} else
#define Css_ObjForEachFanin( pObj, pNext, i )         \
    for ( i = 0; (i < (int)pObj->nFanins) && (pNext = Css_ObjFanin(pObj,i)); i++ )
#define Css_ObjForEachFanout( pObj, pNext, i )        \
    for ( i = 0; (i < (int)pObj->nFanouts) && (pNext = Css_ObjFanout(pObj,i)); i++ )
#define Css_ObjForEachFaninLit( pObj, pNext, fCompl, i )         \
    for ( i = 0; (i < (int)pObj->nFanins) && (pNext = Css_ObjFanin(pObj,i)) && ((fCompl = Css_ObjFaninC(pObj,i)),1); i++ )
#define Css_ObjForEachFanoutLit( pObj, pNext, fCompl, i )        \
    for ( i = 0; (i < (int)pObj->nFanouts) && (pNext = Css_ObjFanout(pObj,i)) && ((fCompl = Css_ObjFanoutC(pObj,i)),1); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates logic network isomorphic to the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Css_Man_t * Css_ManCreateLogicSimple( Gia_Man_t * pGia )
{
    Css_Man_t * p;
    Css_Obj_t * pObjLog, * pFanLog;
    Gia_Obj_t * pObj;
    int i, iHandle = 0;
    p = ABC_CALLOC( Css_Man_t, 1 );
    p->pGia = pGia;
    p->vCis = Vec_IntAlloc( Gia_ManCiNum(pGia) );
    p->vCos = Vec_IntAlloc( Gia_ManCoNum(pGia) );
    p->nObjData = (sizeof(Css_Obj_t) / 4) * Gia_ManObjNum(pGia) + 4 * Gia_ManAndNum(pGia) + 2 * Gia_ManCoNum(pGia);
    p->pObjData = ABC_CALLOC( int, p->nObjData );
    ABC_FREE( pGia->pRefs );
    Gia_ManCreateRefs( pGia );
    Gia_ManForEachObj( pGia, pObj, i )
    {
        pObj->Value = iHandle;
        pObjLog = Css_ManObj( p, iHandle );
        pObjLog->nFanins  = 0;
        pObjLog->nFanouts = Gia_ObjRefs( pGia, pObj );
        pObjLog->hHandle  = iHandle;
        pObjLog->iFanouts = 0;
        if ( Gia_ObjIsAnd(pObj) )
        {
            pFanLog = Css_ManObj( p, Gia_ObjHandle(Gia_ObjFanin0(pObj)) ); 
            pFanLog->Fanios[pFanLog->nFanins + pFanLog->iFanouts].iFan = 
                pObjLog->Fanios[pObjLog->nFanins].iFan = pObjLog->hHandle - pFanLog->hHandle;
            pFanLog->Fanios[pFanLog->nFanins + pFanLog->iFanouts++].fCompl =
                pObjLog->Fanios[pObjLog->nFanins++].fCompl = Gia_ObjFaninC0(pObj);

            pFanLog = Css_ManObj( p, Gia_ObjHandle(Gia_ObjFanin1(pObj)) ); 
            pFanLog->Fanios[pFanLog->nFanins + pFanLog->iFanouts].iFan = 
                pObjLog->Fanios[pObjLog->nFanins].iFan = pObjLog->hHandle - pFanLog->hHandle;
            pFanLog->Fanios[pFanLog->nFanins + pFanLog->iFanouts++].fCompl =
                pObjLog->Fanios[pObjLog->nFanins++].fCompl = Gia_ObjFaninC1(pObj);

            p->nNodes++;
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            pFanLog = Css_ManObj( p, Gia_ObjHandle(Gia_ObjFanin0(pObj)) ); 
            pFanLog->Fanios[pFanLog->nFanins + pFanLog->iFanouts].iFan = 
                pObjLog->Fanios[pObjLog->nFanins].iFan = pObjLog->hHandle - pFanLog->hHandle;
            pFanLog->Fanios[pFanLog->nFanins + pFanLog->iFanouts++].fCompl =
                pObjLog->Fanios[pObjLog->nFanins++].fCompl = Gia_ObjFaninC0(pObj);

            pObjLog->fCo = 1;
            Vec_IntPush( p->vCos, iHandle );
        }
        else if ( Gia_ObjIsCi(pObj) )
        {
            pObjLog->fCi = 1;
            Vec_IntPush( p->vCis, iHandle );
        }
        iHandle += Css_ObjSize( pObjLog );
        p->nObjs++;
    }
    assert( iHandle == p->nObjData );
    Gia_ManForEachObj( pGia, pObj, i )
    {
        pObjLog = Css_ManObj( p, Gia_ObjHandle(pObj) );
        assert( pObjLog->nFanouts == pObjLog->iFanouts );
        pObjLog->TravId = 0;
    }
    p->nTravIds = 1;
    p->vTrail = Vec_IntAlloc( 100 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates logic network isomorphic to the given AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Css_ManStop( Css_Man_t * p )
{
    Vec_IntFree( p->vTrail );
    Vec_IntFree( p->vCis );
    Vec_IntFree( p->vCos );
    ABC_FREE( p->pObjData );
    ABC_FREE( p->pLevels );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Propagates implications for the net.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Css_ManImplyNet_rec( Css_Man_t * p, Css_Obj_t * pVar, unsigned Value )
{
    static inline Css_ManImplyNode_rec( Css_Man_t * p, Css_Obj_t * pVar );
    Css_Obj_t * pNext;
    int i;
    if ( !Css_ObjIsTravIdCurrent(p, pVar) )
        return 0;
    // assign the variable
    assert( !Css_VarIsAssigned(pVar) );
    Css_VarAssign( pVar );
    Css_VarSetValue( pVar, Value );
    Vec_IntPush( p->vTrail, pVar->hHandle );
    // propagate fanouts, then fanins
    Css_ObjForEachFanout( pVar, pNext, i )
        if ( Css_ManImplyNode_rec( p, pNext ) )
            return 1;
    Css_ObjForEachFanin( pVar, pNext, i )
        if ( Css_ManImplyNode_rec( p, pNext ) )
            return 1;
    return 0;
}
 
/**Function*************************************************************

  Synopsis    [Propagates implications for the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Css_ManImplyNode_rec( Css_Man_t * p, Css_Obj_t * pVar )
{
    Css_Obj_t * pFan0, * pFan1;
    if ( Css_ObjIsCi(pVar) )
        return 0;
    pFan0 = Css_ObjFanin(pVar, 0);
    pFan1 = Css_ObjFanin(pVar, 1);
    if ( !Css_VarIsAssigned(pVar) )
    {
        if ( Css_VarIsAssigned(pFan0) )
        {
            if ( Css_VarValue(pFan0) == Css_ObjFaninC(pVar,0) ) // negative -> propagate
                return Css_ManImplyNet_rec(p, pVar, 0);
            // assigned positive
            if ( Css_VarIsAssigned(pFan1) )
            {
                if ( Css_VarValue(pFan1) == Css_ObjFaninC(pVar,1) ) // negative -> propagate
                    return Css_ManImplyNet_rec(p, pVar, 0);
                // asigned positive -> propagate
                return Css_ManImplyNet_rec(p, pVar, 1);
            }
            return 0;
        }
        if ( Css_VarIsAssigned(pFan1) )
        {
            if ( Css_VarValue(pFan1) == Css_ObjFaninC(pVar,1) ) // negative -> propagate
                return Css_ManImplyNet_rec(p, pVar, 0);
            return 0;
        }
        assert( 0 );
        return 0;
    }
    if ( Css_VarValue(pVar) ) // positive
    {
        if ( Css_VarIsAssigned(pFan0) )
        {
            if ( Css_VarValue(pFan0) == Css_ObjFaninC(pVar,0) ) // negative -> conflict
                return 1;
            // check second var
            if ( Css_VarIsAssigned(pFan1) )
            {
                if ( Css_VarValue(pFan1) == Css_ObjFaninC(pVar,1) ) // negative -> conflict
                    return 1;
                // positive + positive -> nothing to do
                return 0;
            }
        }
        else
        {
            // pFan0 unassigned -> enqueue first var
//            Css_ManEnqueue( p, pFan0, !Css_ObjFaninC(pVar,0) );
            if ( Css_ManImplyNet_rec( p, pFan0, !Css_ObjFaninC(pVar,0) ) )
                return 1;
            // check second var
            if ( Css_VarIsAssigned(pFan1) )
            {
                if ( Css_VarValue(pFan1) == Css_ObjFaninC(pVar,1) ) // negative -> conflict
                    return 1;
                // positive + positive -> nothing to do
                return 0;
            }
        }
        // unassigned -> enqueue second var
//        Css_ManEnqueue( p, pFan1, !Css_ObjFaninC(pVar,1) );
        return Css_ManImplyNet_rec( p, pFan1, !Css_ObjFaninC(pVar,1) );
    }
    else // negative
    {
        if ( Css_VarIsAssigned(pFan0) )
        {
            if ( Css_VarValue(pFan0) == Css_ObjFaninC(pVar,0) ) // negative -> nothing to do
                return 0;
            if ( Css_VarIsAssigned(pFan1) )
            {
                if ( Css_VarValue(pFan1) == Css_ObjFaninC(pVar,1) ) // negative -> nothing to do
                    return 0;
                // positive + positive -> conflict
                return 1;
            }
            // positive + unassigned -> enqueue second var
//            Css_ManEnqueue( p, pFan1, Css_ObjFaninC(pVar,1) );
            return Css_ManImplyNet_rec( p, pFan1, Css_ObjFaninC(pVar,1) );
        }
        else
        {
            if ( Css_VarIsAssigned(pFan1) )
            {
                if ( Css_VarValue(pFan1) == Css_ObjFaninC(pVar,1) ) // negative -> nothing to do
                    return 0;
                // unassigned + positive -> enqueue first var
//                Css_ManEnqueue( p, pFan0, Css_ObjFaninC(pVar,0) );
                return Css_ManImplyNet_rec( p, pFan0, Css_ObjFaninC(pVar,0) );
            }
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Css_ManCancelUntil( Css_Man_t * p, int iBound, Vec_Int_t * vCex )
{
    Css_Obj_t * pVar;
    int i;
    Css_ManForEachObjVecStart( p->vTrail, p, pVar, i, iBound )
    {
        if ( vCex )  
            Vec_IntPush( vCex, Gia_Var2Lit(Css_ObjId(pVar), !pVar->fValue) );
        Css_VarUnassign( pVar );
    }
    Vec_IntShrink( p->vTrail, iBound );
}

/**Function*************************************************************

  Synopsis    [Justifies assignments.]

  Description [Returns 1 for UNSAT, 0 for SAT, -1 for UNDECIDED.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Css_ManJustify( Css_Man_t * p, int iBegin )
{
    Css_Obj_t * pVar, * pFan0, * pFan1;
    int iState, iThis;
    if ( p->nConfsMax == 0 )
        return 1;
    // get the next variable to justify
    Css_ManForEachObjVecStart( p->vTrail, p, pVar, iThis, iBegin )
    {
        assert( Css_VarIsAssigned(pVar) );
        if ( Css_VarValue(pVar) || Css_ObjIsCi(pVar) )
            continue;
        pFan0 = Css_ObjFanin(pVar,0);
        pFan1 = Css_ObjFanin(pVar,0);
        if ( !Css_VarIsAssigned(pFan0) && !Css_VarIsAssigned(pFan1) )
            break;
    }
    if ( iThis == Vec_IntSize(p->vTrail) ) // could not find
        return 0;
    // found variable to justify
    assert( !Css_VarValue(pVar) && !Css_VarIsAssigned(pFan0) && !Css_VarIsAssigned(pFan1) );
    // remember the state of the stack
    iState = Vec_IntSize( p->vTrail );
    // try to justify by setting first fanin to 0
    if ( !Css_ManImplyNet_rec(p, pFan0, 0) && !Css_ManJustify(p, iThis) )
        return 0;
    Css_ManCancelUntil( p, iState, NULL );
    if ( p->nConfsMax == 0 )
        return 1;
    // try to justify by setting second fanin to 0
    if ( !Css_ManImplyNet_rec(p, pFan1, 0) && !Css_ManJustify(p, iThis) )
        return 0;
    Css_ManCancelUntil( p, iState, NULL );
    if ( p->nConfsMax == 0 )
        return 1;
    p->nConfsMax--;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Marsk logic cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Css_ManMarkCone_rec( Css_Man_t * p, Css_Obj_t * pVar )
{
    if ( Css_ObjIsTravIdCurrent(p, pVar) )
        return;
    Css_ObjSetTravIdCurrent(p, pVar);
    assert( !Css_VarIsAssigned(pVar) );
    if ( Css_ObjIsCi(pVar) )
        return;
    else
    {
        Css_Obj_t * pNext;
        int i;
        Css_ObjForEachFanin( pVar, pNext, i )
            Css_ManMarkCone_rec( p, pNext );
    }
}

/**Function*************************************************************

  Synopsis    [Runs one call to the SAT solver.]

  Description [Returns 1 for UNSAT, 0 for SAT, -1 for UNDECIDED.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Css_ManPrepare( Css_Man_t * p, int * pLits, int nLits )
{
    Css_Obj_t * pVar;
    int i;
    // mark the cone
    Css_ManIncrementTravId( p );
    for ( i = 0; i < nLits; i++ )
    {
        pVar = Css_ManObj( p, Gia_Lit2Var(pLits[i]) );
        Css_ManMarkCone_rec( p, pVar );
    }
    // assign literals
    Vec_IntClear( p->vTrail );
    for ( i = 0; i < nLits; i++ )
    {
        pVar = Css_ManObj( p, Gia_Lit2Var(pLits[i]) );
        if ( Css_ManImplyNet_rec( p, pVar, !Gia_LitIsCompl(pLits[i]) ) )
        {
            Css_ManCancelUntil( p, 0, NULL );
            return 1;
        }
    }
    return 0;
}
 

/**Function*************************************************************

  Synopsis    [Runs one call to the SAT solver.]

  Description [Returns 1 for UNSAT, 0 for SAT, -1 for UNDECIDED.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Css_ManSolve( Css_Man_t * p, int * pLits, int nLits, int nConfsMax, Vec_Int_t * vCex )
{
    // propagate the assignments
    if ( Css_ManPrepare( p, pLits, nLits ) )
        return 1;
    // justify the assignments
    p->nConfsMax = nConfsMax;
    if ( Css_ManJustify( p, 0 ) )
        return p->nConfsMax? 1 : -1;
    // derive model and return the solver to the initial state
    Vec_IntClear( vCex );
    Css_ManCancelUntil( p, 0, vCex );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Procedure to test the new SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SatSolveTest2( Gia_Man_t * pGia )
{
    extern void Gia_SatVerifyPattern( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vCex, Vec_Int_t * vVisit );
    int nConfsMax = 1000;
    int CountUnsat, CountSat, CountUndec;
    Css_Man_t * p; 
    Vec_Int_t * vCex;
    Vec_Int_t * vVisit;
    Gia_Obj_t * pRoot; 
    int i, RetValue, iLit, clk = clock();
    // create logic network
    p = Css_ManCreateLogicSimple( pGia );
    // prepare AIG
    Gia_ManCleanValue( pGia );
    Gia_ManCleanMark0( pGia );
    Gia_ManCleanMark1( pGia );
    vCex   = Vec_IntAlloc( 100 );
    vVisit = Vec_IntAlloc( 100 );
    // solve for each output
    CountUnsat = CountSat = CountUndec = 0;
    Gia_ManForEachCo( pGia, pRoot, i )
    {
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pRoot)) )
            continue;
//printf( "Output %6d : ", i );
        iLit = Gia_Var2Lit( Gia_ObjHandle(Gia_ObjFanin0(pRoot)), Gia_ObjFaninC0(pRoot) );
        RetValue = Css_ManSolve( p, &iLit, 1, nConfsMax, vCex );
        if ( RetValue == 1 )
            CountUnsat++;
        else if ( RetValue == -1 )
            CountUndec++;
        else 
        {
//            Gia_Obj_t * pTemp;
//            int k;
            assert( RetValue == 0 );
            CountSat++;
/*
            Vec_PtrForEachEntry( vCex, pTemp, k )
//                printf( "%s%d ", Gia_IsComplement(pTemp)? "!": "", Gia_ObjCioId(Gia_Regular(pTemp)) );
                printf( "%s%d ", Gia_IsComplement(pTemp)? "!": "", Gia_ObjId(p,Gia_Regular(pTemp)) );
            printf( "\n" );
*/
            Gia_SatVerifyPattern( pGia, pRoot, vCex, vVisit );
        }
//        Gia_ManCheckMark0( p );
//        Gia_ManCheckMark1( p );
    }
    Css_ManStop( p );
    Vec_IntFree( vCex );
    Vec_IntFree( vVisit );
    printf( "Unsat = %d. Sat = %d. Undec = %d.  ", CountUnsat, CountSat, CountUndec );
    ABC_PRT( "Time", clock() - clk );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


