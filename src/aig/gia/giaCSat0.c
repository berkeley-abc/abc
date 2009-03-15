/**CFile****************************************************************

  FileName    [giaCsat0.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Circuit-based SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCsat0.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int          Sat_ObjXValue( Gia_Obj_t * pObj )          { return (pObj->fMark1 << 1) | pObj->fMark0; }
static inline void         Sat_ObjSetXValue( Gia_Obj_t * pObj, int v) { pObj->fMark0 = (v & 1); pObj->fMark1 = ((v >> 1) & 1); }

static inline int          Sat_VarIsAssigned( Gia_Obj_t * pVar )      { return pVar->Value > 0;                    }
static inline void         Sat_VarAssign( Gia_Obj_t * pVar, int i )   { assert(!pVar->Value); pVar->Value = i;     }
static inline void         Sat_VarUnassign( Gia_Obj_t * pVar )        { assert(pVar->Value);  pVar->Value = 0;     }
static inline int          Sat_VarValue( Gia_Obj_t * pVar )           { assert(pVar->Value);  return pVar->fMark0; }
static inline void         Sat_VarSetValue( Gia_Obj_t * pVar, int v ) { assert(pVar->Value);  pVar->fMark0 = v;    }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collects nodes in the cone and initialized them to x.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SatCollectCone_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vVisit )
{
    if ( Sat_ObjXValue(pObj) == GIA_UND )
        return;
    assert( pObj->Value == 0 );
    if ( Gia_ObjIsAnd(pObj) )
    {
        Gia_SatCollectCone_rec( p, Gia_ObjFanin0(pObj), vVisit );
        Gia_SatCollectCone_rec( p, Gia_ObjFanin1(pObj), vVisit );
    }
    assert( Sat_ObjXValue(pObj) == 0 );
    Sat_ObjSetXValue( pObj, GIA_UND );
    Vec_IntPush( vVisit, Gia_ObjId(p, pObj) );
}

/**Function*************************************************************

  Synopsis    [Collects nodes in the cone and initialized them to x.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SatCollectCone( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vVisit )
{
    assert( !Gia_IsComplement(pObj) );
    assert( !Gia_ObjIsConst0(pObj) );
    assert( Sat_ObjXValue(pObj) == 0 );
    Vec_IntClear( vVisit );
    Gia_SatCollectCone_rec( p, pObj, vVisit );
}

/**Function*************************************************************

  Synopsis    [Collects nodes in the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SatVerifyPattern( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vCex, Vec_Int_t * vVisit )
{
    Gia_Obj_t * pObj;
    int i, Entry, Value, Value0, Value1;
    assert( Gia_ObjIsCo(pRoot) );
    assert( !Gia_ObjIsConst0(Gia_ObjFanin0(pRoot)) );
    // collect nodes and initialized them to x
    Gia_SatCollectCone( p, Gia_ObjFanin0(pRoot), vVisit );
    // set binary values to nodes in the counter-example
    Vec_IntForEachEntry( vCex, Entry, i )
    {
        pObj = Gia_NotCond( Gia_ManObj( p, Gia_Lit2Var(Entry) ), Gia_LitIsCompl(Entry) );
        Sat_ObjSetXValue( Gia_Regular(pObj), Gia_IsComplement(pObj)? GIA_ZER : GIA_ONE );
        assert( Sat_ObjXValue(Gia_Regular(pObj)) == (Gia_IsComplement(pObj)? GIA_ZER : GIA_ONE) );
    }
    // simulate
    Gia_ManForEachObjVec( vVisit, p, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
            continue;
        assert( Gia_ObjIsAnd(pObj) );
        Value0 = Sat_ObjXValue( Gia_ObjFanin0(pObj) );
        Value1 = Sat_ObjXValue( Gia_ObjFanin1(pObj) );
        Value = Gia_XsimAndCond( Value0, Gia_ObjFaninC0(pObj), Value1, Gia_ObjFaninC1(pObj) );
        Sat_ObjSetXValue( pObj, Value );
    }
    Value = Gia_XsimNotCond( Value, Gia_ObjFaninC0(pRoot) );
    if ( Value != GIA_ONE )
        printf( "Gia_SatVerifyPattern(): Verification FAILED.\n" );
//    else
//        printf( "Gia_SatVerifyPattern(): Verification succeeded.\n" );
//    assert( Value == GIA_ONE );
    // clean the nodes
    Gia_ManForEachObjVec( vVisit, p, pObj, i )
        Sat_ObjSetXValue( pObj, 0 );
}


/**Function*************************************************************

  Synopsis    [Undoes the assignment since the given value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SatUndo_rec( Gia_Obj_t * pObj, unsigned Value, Vec_Int_t * vCex )
{
    if ( pObj->Value < Value )
        return;
    pObj->Value = 0;
    if ( Gia_ObjIsCi(pObj) )
    {
        if ( vCex ) Vec_IntPush( vCex, Gia_Var2Lit(Gia_ObjCioId(pObj), !pObj->fPhase) );
        return;
    }
    Gia_SatUndo_rec( Gia_ObjFanin0(pObj), Value, vCex );
    Gia_SatUndo_rec( Gia_ObjFanin1(pObj), Value, vCex );
}

/**Function*************************************************************

  Synopsis    [Propagates assignments.]

  Description [Returns 1 if UNSAT, 0 if SAT.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_SatProp_rec( Gia_Obj_t * pObj, unsigned Phase, unsigned * pValue, int * pnConfs )
{
    int Value = *pValue;
    if ( pObj->Value )
        return pObj->fPhase != Phase;
    if ( Gia_ObjIsCi(pObj) )
    {
        pObj->Value = Value;
        pObj->fPhase = Phase;
        return 0;
    }
    if ( Phase ) // output of AND should be 1
    {
        if ( Gia_SatProp_rec( Gia_ObjFanin0(pObj), !Gia_ObjFaninC0(pObj), pValue, pnConfs ) )
            return 1;
        if ( Gia_SatProp_rec( Gia_ObjFanin1(pObj), !Gia_ObjFaninC1(pObj), pValue, pnConfs ) )
        {
            Gia_SatUndo_rec( Gia_ObjFanin0(pObj), Value, NULL );
            return 1;
        }
/*
        if ( Gia_SatProp_rec( Gia_ObjFanin1(pObj), !Gia_ObjFaninC1(pObj), pValue, pnConfs ) )
            return 1;
        if ( Gia_SatProp_rec( Gia_ObjFanin0(pObj), !Gia_ObjFaninC0(pObj), pValue, pnConfs ) )
        {
            Gia_SatUndo_rec( Gia_ObjFanin1(pObj), Value, NULL );
            return 1;
        }
*/
        pObj->Value = Value;
        pObj->fPhase = 1;
        return 0; 
    }
    // output of AND should be 0

    (*pValue)++;
    if ( !Gia_SatProp_rec( Gia_ObjFanin1(pObj), Gia_ObjFaninC1(pObj), pValue, pnConfs ) )
    {
        pObj->Value = Value;
        pObj->fPhase = 0;
        return 0;
    }
    if ( !*pnConfs )
        return 1;

    (*pValue)++;
    if ( !Gia_SatProp_rec( Gia_ObjFanin0(pObj), Gia_ObjFaninC0(pObj), pValue, pnConfs ) )
    {
        pObj->Value = Value;
        pObj->fPhase = 0;
        return 0;
    }
    if ( !*pnConfs )
        return 1;
    // cannot be satisfied
    (*pnConfs)--;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Procedure to solve SAT for the node.]

  Description [Returns 1 if UNSAT, 0 if SAT, and -1 if undecided.]
               
  SideEffects [Precondition: pObj->Value should be 0.]

  SeeAlso     []

***********************************************************************/
int Gia_SatSolve( Gia_Obj_t * pObj, unsigned Phase, int nConfsMax, Vec_Int_t * vCex )
{
    int Value = 1;
    int nConfs = nConfsMax? nConfsMax : (1<<30);
    assert( !Gia_IsComplement(pObj) );
    assert( !Gia_ObjIsConst0(pObj) );
    assert( pObj->Value == 0 );
    if ( Gia_SatProp_rec( pObj, Phase, &Value, &nConfs ) )
    {
//        if ( nConfs )
//            printf( "UNSAT after %d conflicts\n", nConfsMax - nConfs );
//        else
//            printf( "UNDEC after %d conflicts\n", nConfsMax );
        return nConfs? 1 : -1;
    }
    Vec_IntClear( vCex );
    Gia_SatUndo_rec( pObj, 1, vCex );
//    printf( "SAT after %d conflicts\n", nConfsMax - nConfs );
    return 0;
}



/**Function*************************************************************

  Synopsis    [Procedure to test the new SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_SatSolveTest( Gia_Man_t * p )
{
    int nConfsMax = 1000;
    int CountUnsat, CountSat, CountUndec;
    Vec_Int_t * vCex;
    Vec_Int_t * vVisit;
    Gia_Obj_t * pRoot; 
    int i, RetValue, clk = clock();
    // prepare AIG
    Gia_ManCleanValue( p );
    Gia_ManCleanMark0( p );
    Gia_ManCleanMark1( p );
    vCex   = Vec_IntAlloc( 100 );
    vVisit = Vec_IntAlloc( 100 );
    // solve for each output
    CountUnsat = CountSat = CountUndec = 0;
    Gia_ManForEachCo( p, pRoot, i )
    {
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pRoot)) )
            continue;
//printf( "Output %6d : ", i );
        RetValue = Gia_SatSolve( Gia_ObjFanin0(pRoot), !Gia_ObjFaninC0(pRoot), nConfsMax, vCex );
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
            Vec_IntForEachEntry( vCex, pTemp, k )
//                printf( "%s%d ", Gia_IsComplement(pTemp)? "!": "", Gia_ObjCioId(Gia_Regular(pTemp)) );
                printf( "%s%d ", Gia_IsComplement(pTemp)? "!": "", Gia_ObjId(p,Gia_Regular(pTemp)) );
            printf( "\n" );
*/
//            Gia_SatVerifyPattern( p, pRoot, vCex, vVisit );
        }
//        Gia_ManCheckMark0( p );
//        Gia_ManCheckMark1( p );
    }
    Vec_IntFree( vCex );
    Vec_IntFree( vVisit );
    printf( "Unsat = %d. Sat = %d. Undec = %d.  ", CountUnsat, CountSat, CountUndec );
    ABC_PRT( "Time", clock() - clk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


