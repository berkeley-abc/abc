/**CFile****************************************************************

  FileName    [giaCSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [A simple circuit-based solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCSat.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START


//#define gia_assert(exp)     ((void)0)
//#define gia_assert(exp)     (assert(exp))

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Cbs2_Par_t_ Cbs2_Par_t;
struct Cbs2_Par_t_
{
    // conflict limits
    int           nBTLimit;     // limit on the number of conflicts
    int           nJustLimit;   // limit on the size of justification queue
    // current parameters
    int           nBTThis;      // number of conflicts
    int           nBTThisNc;    // number of conflicts
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

typedef struct Cbs2_Que_t_ Cbs2_Que_t;
struct Cbs2_Que_t_
{
    int           iHead;        // beginning of the queue
    int           iTail;        // end of the queue
    int           nSize;        // allocated size
    int *         pData;        // nodes stored in the queue
};
 
typedef struct Cbs2_Man_t_ Cbs2_Man_t;
struct Cbs2_Man_t_
{
    Cbs2_Par_t    Pars;         // parameters
    Gia_Man_t *   pAig;         // AIG manager
    Cbs2_Que_t    pProp;        // propagation queue
    Cbs2_Que_t    pJust;        // justification queue
    Cbs2_Que_t    pClauses;     // clause queue
    int *         pIter;        // iterator through clause vars
    //Vec_Int_t *   vLevReas;     // levels and decisions
    Vec_Int_t *   vModel;       // satisfying assignment
    Vec_Int_t *   vTemp;        // temporary storage
    // internal data
    Vec_Str_t     vAssign;
    Vec_Str_t     vValue;
    Vec_Int_t     vLevReason;
    Vec_Int_t     vIndex;
    // SAT calls statistics
    int           nSatUnsat;    // the number of proofs
    int           nSatSat;      // the number of failure
    int           nSatUndec;    // the number of timeouts
    int           nSatTotal;    // the number of calls
    // conflicts
    int           nConfUnsat;   // conflicts in unsat problems
    int           nConfSat;     // conflicts in sat problems
    int           nConfUndec;   // conflicts in undec problems
    // runtime stats
    abctime       timeSatUnsat; // unsat
    abctime       timeSatSat;   // sat
    abctime       timeSatUndec; // undecided
    abctime       timeTotal;    // total runtime
};

static inline int   Cbs2_VarUnused( Cbs2_Man_t * p, int iVar )                  { return Vec_IntEntry(&p->vLevReason, 3*iVar) == -1; }
static inline void  Cbs2_VarSetUnused( Cbs2_Man_t * p, int iVar )               { Vec_IntWriteEntry(&p->vLevReason, 3*iVar, -1);     } 

static inline int   Cbs2_VarMark0( Cbs2_Man_t * p, int iVar )                   { return Vec_StrEntry(&p->vAssign, iVar);            }
static inline void  Cbs2_VarSetMark0( Cbs2_Man_t * p, int iVar, int Value )     { Vec_StrWriteEntry(&p->vAssign, iVar, (char)Value); } 

static inline int   Cbs2_VarMark1( Cbs2_Man_t * p, int iVar )                   { return Vec_StrEntry(&p->vValue, iVar);             }
static inline void  Cbs2_VarSetMark1( Cbs2_Man_t * p, int iVar, int Value )     { Vec_StrWriteEntry(&p->vValue, iVar, (char)Value);  } 

static inline int   Cbs2_VarIsAssigned( Cbs2_Man_t * p, int iVar )              { return Cbs2_VarMark0(p, iVar);                                                                  }
static inline void  Cbs2_VarAssign( Cbs2_Man_t * p, int iVar )                  { assert(!Cbs2_VarIsAssigned(p, iVar)); Cbs2_VarSetMark0(p, iVar, 1);                             }
static inline void  Cbs2_VarUnassign( Cbs2_Man_t * p, int iVar )                { assert( Cbs2_VarIsAssigned(p, iVar)); Cbs2_VarSetMark0(p, iVar, 0); Cbs2_VarSetUnused(p, iVar); }
static inline int   Cbs2_VarValue( Cbs2_Man_t * p, int iVar )                   { assert( Cbs2_VarIsAssigned(p, iVar)); return Cbs2_VarMark1(p, iVar);                            }
static inline void  Cbs2_VarSetValue( Cbs2_Man_t * p, int iVar, int v )         { assert( Cbs2_VarIsAssigned(p, iVar)); Cbs2_VarSetMark1(p, iVar, v);                             }

static inline int   Cbs2_VarIsJust( Cbs2_Man_t * p, Gia_Obj_t * pVar, int iVar )      { return Gia_ObjIsAnd(pVar) && !Cbs2_VarIsAssigned(p, Gia_ObjFaninId0(pVar, iVar)) && !Cbs2_VarIsAssigned(p, Gia_ObjFaninId1(pVar, iVar));  } 
static inline int   Cbs2_VarFanin0Value( Cbs2_Man_t * p, Gia_Obj_t * pVar, int iVar ) { return Cbs2_VarIsAssigned(p, Gia_ObjFaninId0(pVar, iVar)) ? (Cbs2_VarValue(p, Gia_ObjFaninId0(pVar, iVar)) ^ Gia_ObjFaninC0(pVar)) : 2;   }
static inline int   Cbs2_VarFanin1Value( Cbs2_Man_t * p, Gia_Obj_t * pVar, int iVar ) { return Cbs2_VarIsAssigned(p, Gia_ObjFaninId1(pVar, iVar)) ? (Cbs2_VarValue(p, Gia_ObjFaninId1(pVar, iVar)) ^ Gia_ObjFaninC1(pVar)) : 2;   }

static inline int   Cbs2_VarDecLevel( Cbs2_Man_t * p, int iVar )                { assert( !Cbs2_VarUnused(p, iVar) ); return Vec_IntEntry(&p->vLevReason, 3*iVar);    }
static inline int   Cbs2_VarReason0( Cbs2_Man_t * p, int iVar )                 { assert( !Cbs2_VarUnused(p, iVar) ); return Vec_IntEntry(&p->vLevReason, 3*iVar+1);  }
static inline int   Cbs2_VarReason1( Cbs2_Man_t * p, int iVar )                 { assert( !Cbs2_VarUnused(p, iVar) ); return Vec_IntEntry(&p->vLevReason, 3*iVar+2);  }
static inline int   Cbs2_ClauseDecLevel( Cbs2_Man_t * p, int hClause )          { return Cbs2_VarDecLevel( p, p->pClauses.pData[hClause] );                           }

#define Cbs2_QueForEachEntry( Que, iObj, i )                         \
    for ( i = (Que).iHead; (i < (Que).iTail) && ((iObj) = (Que).pData[i]); i++ )

#define Cbs2_ClauseForEachVar( p, hClause, iObj )                    \
    for ( (p)->pIter = (p)->pClauses.pData + hClause; (iObj = *pIter); (p)->pIter++ )
#define Cbs2_ClauseForEachVar1( p, hClause, iObj )                   \
    for ( (p)->pIter = (p)->pClauses.pData+hClause+1; (iObj = *pIter); (p)->pIter++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets default values of the parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cbs2_SetDefaultParams( Cbs2_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Cbs2_Par_t) );
    pPars->nBTLimit    =  1000;   // limit on the number of conflicts
    pPars->nJustLimit  =   100;   // limit on the size of justification queue
    pPars->fUseHighest =     1;   // use node with the highest ID
    pPars->fUseLowest  =     0;   // use node with the highest ID
    pPars->fUseMaxFF   =     0;   // use node with the largest fanin fanout
    pPars->fVerbose    =     1;   // print detailed statistics
}
void Cbs2_ManSetConflictNum( Cbs2_Man_t * p, int Num )
{
    p->Pars.nBTLimit = Num;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cbs2_Man_t * Cbs2_ManAlloc( Gia_Man_t * pGia )
{
    Cbs2_Man_t * p;
    p = ABC_CALLOC( Cbs2_Man_t, 1 );
    p->pProp.nSize = p->pJust.nSize = p->pClauses.nSize = 10000;
    p->pProp.pData = ABC_ALLOC( int, p->pProp.nSize );
    p->pJust.pData = ABC_ALLOC( int, p->pJust.nSize );
    p->pClauses.pData = ABC_ALLOC( int, p->pClauses.nSize );
    p->pClauses.iHead = p->pClauses.iTail = 1;
    p->vModel   = Vec_IntAlloc( 1000 );
    //p->vLevReas = Vec_IntAlloc( 1000 );
    p->vTemp    = Vec_IntAlloc( 1000 );
    p->pAig     = pGia;
    Cbs2_SetDefaultParams( &p->Pars );
    Vec_StrFill( &p->vAssign,    Gia_ManObjNum(pGia), 0 );
    Vec_StrFill( &p->vValue,     Gia_ManObjNum(pGia), 0 );
    Vec_IntFill( &p->vLevReason, 3*Gia_ManObjNum(pGia), -1 );
    Vec_IntFill( &p->vIndex,     Gia_ManObjNum(pGia), -1 );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cbs2_ManStop( Cbs2_Man_t * p )
{
    Vec_StrErase( &p->vAssign );
    Vec_StrErase( &p->vValue );
    Vec_IntErase( &p->vLevReason );
    Vec_IntErase( &p->vIndex );
    //Vec_IntFree( p->vLevReas );
    Vec_IntFree( p->vModel );
    Vec_IntFree( p->vTemp );
    ABC_FREE( p->pClauses.pData );
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
Vec_Int_t * Cbs2_ReadModel( Cbs2_Man_t * p )
{
    return p->vModel;
}




/**Function*************************************************************

  Synopsis    [Returns 1 if the solver is out of limits.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_ManCheckLimits( Cbs2_Man_t * p )
{
    return p->Pars.nJustThis > p->Pars.nJustLimit || p->Pars.nBTThis > p->Pars.nBTLimit;
}

/**Function*************************************************************

  Synopsis    [Saves the satisfying assignment as an array of literals.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs2_ManSaveModel( Cbs2_Man_t * p, Vec_Int_t * vCex )
{
    int i, iVar;
    Vec_IntClear( vCex );
    p->pProp.iHead = 0;
    Cbs2_QueForEachEntry( p->pProp, iVar, i )
        if ( Gia_ObjIsCi(Gia_ManObj(p->pAig, iVar)) )
            Vec_IntPush( vCex, Abc_Var2Lit(Gia_ManIdToCioId(p->pAig, iVar), !Cbs2_VarValue(p, iVar)) );
} 
static inline void Cbs2_ManSaveModelAll( Cbs2_Man_t * p, Vec_Int_t * vCex )
{
    int i, iVar;
    Vec_IntClear( vCex );
    p->pProp.iHead = 0;
    Cbs2_QueForEachEntry( p->pProp, iVar, i )
        Vec_IntPush( vCex, Abc_Var2Lit(iVar, !Cbs2_VarValue(p, iVar)) );
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_QueIsEmpty( Cbs2_Que_t * p )
{
    return p->iHead == p->iTail;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs2_QuePush( Cbs2_Que_t * p, int iObj )
{
    if ( p->iTail == p->nSize )
    {
        p->nSize *= 2;
        p->pData = ABC_REALLOC( int, p->pData, p->nSize ); 
    }
    p->pData[p->iTail++] = iObj;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the object in the queue.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_QueHasNode( Cbs2_Que_t * p, int iObj )
{
    int i, iTemp;
    Cbs2_QueForEachEntry( *p, iTemp, i )
        if ( iTemp == iObj )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs2_QueStore( Cbs2_Que_t * p, int * piHeadOld, int * piTailOld )
{
    int i;
    *piHeadOld = p->iHead;
    *piTailOld = p->iTail;
    for ( i = *piHeadOld; i < *piTailOld; i++ )
        Cbs2_QuePush( p, p->pData[i] );
    p->iHead = *piTailOld;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs2_QueRestore( Cbs2_Que_t * p, int iHeadOld, int iTailOld )
{
    p->iHead = iHeadOld;
    p->iTail = iTailOld;
}

/**Function*************************************************************

  Synopsis    [Finalized the clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_QueFinish( Cbs2_Que_t * p )
{
    int iHeadOld = p->iHead;
    assert( p->iHead < p->iTail );
    Cbs2_QuePush( p, 0 );
    p->iHead = p->iTail;
    return iHeadOld;
}


/**Function*************************************************************

  Synopsis    [Max number of fanins fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_VarFaninFanoutMax( Cbs2_Man_t * p, Gia_Obj_t * pObj )
{
    int Count0, Count1;
    assert( !Gia_IsComplement(pObj) );
    assert( Gia_ObjIsAnd(pObj) );
    Count0 = Gia_ObjRefNum( p->pAig, Gia_ObjFanin0(pObj) );
    Count1 = Gia_ObjRefNum( p->pAig, Gia_ObjFanin1(pObj) );
    return Abc_MaxInt( Count0, Count1 );
}

/**Function*************************************************************

  Synopsis    [Find variable with the highest ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_ManDecideHighest( Cbs2_Man_t * p )
{
    int i, iObj, iObjMax = 0;
    Cbs2_QueForEachEntry( p->pJust, iObj, i )
        if ( iObjMax == 0 || iObjMax < iObj )
            iObjMax = iObj;
    return iObjMax;
}

/**Function*************************************************************

  Synopsis    [Find variable with the lowest ID.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Gia_Obj_t * Cbs2_ManDecideLowest( Cbs2_Man_t * p )
{
    int i, iObj, iObjMin = 0;
    Cbs2_QueForEachEntry( p->pJust, iObj, i )
        if ( iObjMin == 0 || iObjMin > iObj )
            iObjMin = iObj;
    return Gia_ManObj(p->pAig, iObjMin);
}

/**Function*************************************************************

  Synopsis    [Find variable with the maximum number of fanin fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Gia_Obj_t * Cbs2_ManDecideMaxFF( Cbs2_Man_t * p )
{
    Gia_Obj_t * pObj, * pObjMax = NULL;
    int i, iMaxFF = 0, iCurFF, iObj;
    assert( p->pAig->pRefs != NULL );
    Cbs2_QueForEachEntry( p->pJust, iObj, i )
    {
        pObj = Gia_ManObj(p->pAig, iObj);
        iCurFF = Cbs2_VarFaninFanoutMax( p, pObj );
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
static inline void Cbs2_ManCancelUntil( Cbs2_Man_t * p, int iBound )
{
    int i, iVar;
    assert( iBound <= p->pProp.iTail );
    p->pProp.iHead = iBound;
    Cbs2_QueForEachEntry( p->pProp, iVar, i )
        Cbs2_VarUnassign( p, iVar );
    p->pProp.iTail = iBound;
}

/**Function*************************************************************

  Synopsis    [Assigns the variables a value.]

  Description [Returns 1 if conflict; 0 if no conflict.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs2_ManAssign( Cbs2_Man_t * p, int iLit, int Level, int iRes0, int iRes1 )
{
    int iObj = Abc_Lit2Var(iLit);
    assert( Cbs2_VarUnused(p, iObj) );
    assert( !Cbs2_VarIsAssigned(p, iObj) );
    Cbs2_VarAssign( p, iObj );
    Cbs2_VarSetValue( p, iObj, !Abc_LitIsCompl(iLit) );
    Cbs2_QuePush( &p->pProp, iObj );
    Vec_IntWriteEntry( &p->vLevReason, 3*iObj,   Level );
    Vec_IntWriteEntry( &p->vLevReason, 3*iObj+1, iRes0 ? iRes0 : iObj );
    Vec_IntWriteEntry( &p->vLevReason, 3*iObj+2, iRes1 ? iRes1 : iObj );
}


/**Function*************************************************************

  Synopsis    [Returns clause size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_ManClauseSize( Cbs2_Man_t * p, int hClause )
{
    Cbs2_Que_t * pQue = &(p->pClauses);  int * pIter;
    for ( pIter = pQue->pData + hClause; *pIter; pIter++ );
    return pIter - pQue->pData - hClause ;
}

/**Function*************************************************************

  Synopsis    [Prints conflict clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs2_ManPrintClause( Cbs2_Man_t * p, int Level, int hClause )
{
    Cbs2_Que_t * pQue = &(p->pClauses);  int i, iObj;
    assert( Cbs2_QueIsEmpty( pQue ) );
    printf( "Level %2d : ", Level );
    for ( i = hClause; (iObj = pQue->pData[i]); i++ )
        printf( "%d=%d(%d) ", iObj, Cbs2_VarValue(p, iObj), Cbs2_VarDecLevel(p, iObj) );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Prints conflict clause.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs2_ManPrintClauseNew( Cbs2_Man_t * p, int Level, int hClause )
{
    Cbs2_Que_t * pQue = &(p->pClauses);  int i, iObj;
    assert( Cbs2_QueIsEmpty( pQue ) );
    printf( "Level %2d : ", Level );
    for ( i = hClause; (iObj = pQue->pData[i]); i++ )
        printf( "%c%d ", Cbs2_VarValue(p, iObj)? '+':'-', iObj );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Returns conflict clause.]

  Description [Performs conflict analysis.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cbs2_ManDeriveReason( Cbs2_Man_t * p, int Level )
{
    Cbs2_Que_t * pQue = &(p->pClauses);
    int i, k, iObj, iLitLevel, iReason;
    assert( pQue->pData[pQue->iHead] == 0 );
    assert( pQue->iHead + 1 < pQue->iTail );
    //for ( i = pQue->iHead + 1; i < pQue->iTail; i++ )
    //    assert( Cbs2_VarMark0(p, pQue->pData[i]) );
    // compact literals
    Vec_IntClear( p->vTemp );
    for ( i = k = pQue->iHead + 1; i < pQue->iTail; i++ )
    {
        iObj = pQue->pData[i];
        if ( !Cbs2_VarMark0(p, iObj) ) // unassigned - seen again
            continue;
        // assigned - seen first time
        Cbs2_VarSetMark0(p, iObj, 0);
        Vec_IntPush( p->vTemp, iObj );
        // check decision level
        iLitLevel = Cbs2_VarDecLevel( p, iObj );
        if ( iLitLevel < Level )
        {
            pQue->pData[k++] = iObj;
            continue;
        }
        assert( iLitLevel == Level );
        iReason = Cbs2_VarReason0( p, iObj );
        if ( iReason == iObj ) // no reason
        {
            //assert( pQue->pData[pQue->iHead] == NULL );
            pQue->pData[pQue->iHead] = iObj;
            continue;
        }
        Cbs2_QuePush( pQue, iReason );
        iReason = Cbs2_VarReason1( p, iObj );
        if ( iReason != iObj ) // second reason
            Cbs2_QuePush( pQue, iReason );
    }
    assert( pQue->pData[pQue->iHead] != 0 );
    pQue->iTail = k;
    // clear the marks
    Vec_IntForEachEntry( p->vTemp, iObj, i )
        Cbs2_VarSetMark0(p, iObj, 1);
}

/**Function*************************************************************

  Synopsis    [Returns conflict clause.]

  Description [Performs conflict analysis.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_ManAnalyze( Cbs2_Man_t * p, int Level, int iVar, int iFan0, int iFan1 )
{
    Cbs2_Que_t * pQue = &(p->pClauses);
    assert( Cbs2_VarIsAssigned(p, iVar) );
    assert( Cbs2_VarIsAssigned(p, iFan0) );
    assert( iFan1 == 0 || Cbs2_VarIsAssigned(p, iFan1) );
    assert( Cbs2_QueIsEmpty( pQue ) );
    Cbs2_QuePush( pQue, 0 );
    Cbs2_QuePush( pQue, iVar );
    Cbs2_QuePush( pQue, iFan0 );
    if ( iFan1 )
        Cbs2_QuePush( pQue, iFan1 );
    Cbs2_ManDeriveReason( p, Level );
    return Cbs2_QueFinish( pQue );
}


/**Function*************************************************************

  Synopsis    [Performs resolution of two clauses.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_ManResolve( Cbs2_Man_t * p, int Level, int hClause0, int hClause1 )
{
    Cbs2_Que_t * pQue = &(p->pClauses);
    int i, iObj, LevelMax = -1, LevelCur;
    assert( pQue->pData[hClause0] != 0 );
    assert( pQue->pData[hClause0] == pQue->pData[hClause1] );
    //for ( i = hClause0 + 1; (iObj = pQue->pData[i]); i++ )
    //    assert( Cbs2_VarMark0(p, iObj) );
    //for ( i = hClause1 + 1; (iObj = pQue->pData[i]); i++ )
    //    assert( Cbs2_VarMark0(p, iObj) );
    assert( Cbs2_QueIsEmpty( pQue ) );
    Cbs2_QuePush( pQue, 0 );
    for ( i = hClause0 + 1; (iObj = pQue->pData[i]); i++ )
    {
        if ( !Cbs2_VarMark0(p, iObj) ) // unassigned - seen again
            continue;
        // assigned - seen first time
        Cbs2_VarSetMark0(p, iObj, 0);
        Cbs2_QuePush( pQue, iObj );
        LevelCur = Cbs2_VarDecLevel( p, iObj );
        if ( LevelMax < LevelCur )
            LevelMax = LevelCur;
    }
    for ( i = hClause1 + 1; (iObj = pQue->pData[i]); i++ )
    {
        if ( !Cbs2_VarMark0(p, iObj) ) // unassigned - seen again
            continue;
        // assigned - seen first time
        Cbs2_VarSetMark0(p, iObj, 0);
        Cbs2_QuePush( pQue, iObj );
        LevelCur = Cbs2_VarDecLevel( p, iObj );
        if ( LevelMax < LevelCur )
            LevelMax = LevelCur;
    }
    for ( i = pQue->iHead + 1; i < pQue->iTail; i++ )
        Cbs2_VarSetMark0(p, pQue->pData[i], 1);
    Cbs2_ManDeriveReason( p, LevelMax );
    return Cbs2_QueFinish( pQue );
}

/**Function*************************************************************

  Synopsis    [Propagates a variable.]

  Description [Returns clause handle if conflict; 0 if no conflict.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_ManPropagateOne( Cbs2_Man_t * p, int iVar, int Level )
{
    Gia_Obj_t * pVar = Gia_ManObj( p->pAig, iVar ); int Value0, Value1;
    assert( !Gia_IsComplement(pVar) );
    assert( Cbs2_VarIsAssigned(p, iVar) );
    if ( Gia_ObjIsCi(pVar) )
        return 0;
    assert( Gia_ObjIsAnd(pVar) );
    Value0 = Cbs2_VarFanin0Value(p, pVar, iVar);
    Value1 = Cbs2_VarFanin1Value(p, pVar, iVar);
    if ( Cbs2_VarValue(p, iVar) )
    { // value is 1
        if ( Value0 == 0 || Value1 == 0 ) // one is 0
        {
            if ( Value0 == 0 && Value1 != 0 )
                return Cbs2_ManAnalyze( p, Level, iVar, Gia_ObjFaninId0(pVar, iVar), 0 );
            if ( Value0 != 0 && Value1 == 0 )
                return Cbs2_ManAnalyze( p, Level, iVar, Gia_ObjFaninId1(pVar, iVar), 0 );
            assert( Value0 == 0 && Value1 == 0 );
            return Cbs2_ManAnalyze( p, Level, iVar, Gia_ObjFaninId0(pVar, iVar), Gia_ObjFaninId1(pVar, iVar) );
        }
        if ( Value0 == 2 ) // first is unassigned
            Cbs2_ManAssign( p, Gia_ObjFaninLit0(pVar, iVar), Level, iVar, 0 );
        if ( Value1 == 2 ) // first is unassigned
            Cbs2_ManAssign( p, Gia_ObjFaninLit1(pVar, iVar), Level, iVar, 0 );
        return 0;
    }
    // value is 0
    if ( Value0 == 0 || Value1 == 0 ) // one is 0
        return 0;
    if ( Value0 == 1 && Value1 == 1 ) // both are 1
        return Cbs2_ManAnalyze( p, Level, iVar, Gia_ObjFaninId0(pVar, iVar), Gia_ObjFaninId1(pVar, iVar) );
    if ( Value0 == 1 || Value1 == 1 ) // one is 1 
    {
        if ( Value0 == 2 ) // first is unassigned
            Cbs2_ManAssign( p, Abc_LitNot(Gia_ObjFaninLit0(pVar, iVar)), Level, iVar, Gia_ObjFaninId1(pVar, iVar) );
        if ( Value1 == 2 ) // second is unassigned
            Cbs2_ManAssign( p, Abc_LitNot(Gia_ObjFaninLit1(pVar, iVar)), Level, iVar, Gia_ObjFaninId0(pVar, iVar) );
        return 0;
    }
    assert( Cbs2_VarIsJust(p, pVar, iVar) );
    //assert( !Cbs2_QueHasNode( &p->pJust, iVar ) );
    Cbs2_QuePush( &p->pJust, iVar );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Propagates a variable.]

  Description [Returns 1 if conflict; 0 if no conflict.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cbs2_ManPropagateTwo( Cbs2_Man_t * p, int iVar, int Level )
{
    Gia_Obj_t * pVar = Gia_ManObj( p->pAig, iVar ); int Value0, Value1;
    assert( !Gia_IsComplement(pVar) );
    assert( Gia_ObjIsAnd(pVar) );
    assert( Cbs2_VarIsAssigned(p, iVar) );
    assert( !Cbs2_VarValue(p, iVar) );
    Value0 = Cbs2_VarFanin0Value(p, pVar, iVar);
    Value1 = Cbs2_VarFanin1Value(p, pVar, iVar);
    // value is 0
    if ( Value0 == 0 || Value1 == 0 ) // one is 0
        return 0;
    if ( Value0 == 1 && Value1 == 1 ) // both are 1
        return Cbs2_ManAnalyze( p, Level, iVar, Gia_ObjFaninId0(pVar, iVar), Gia_ObjFaninId1(pVar, iVar) );
    assert( Value0 == 1 || Value1 == 1 );
    if ( Value0 == 2 ) // first is unassigned
        Cbs2_ManAssign( p, Abc_LitNot(Gia_ObjFaninLit0(pVar, iVar)), Level, iVar, Gia_ObjFaninId1(pVar, iVar) );
    if ( Value1 == 2 ) // first is unassigned
        Cbs2_ManAssign( p, Abc_LitNot(Gia_ObjFaninLit1(pVar, iVar)), Level, iVar, Gia_ObjFaninId0(pVar, iVar) );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Propagates all variables.]

  Description [Returns 1 if conflict; 0 if no conflict.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cbs2_ManPropagate( Cbs2_Man_t * p, int Level )
{
    while ( 1 )
    {
        int i, k, iVar, hClause;
        Cbs2_QueForEachEntry( p->pProp, iVar, i )
        {
            if ( (hClause = Cbs2_ManPropagateOne( p, iVar, Level )) )
                return hClause;
        }
        p->pProp.iHead = p->pProp.iTail;
        k = p->pJust.iHead;
        Cbs2_QueForEachEntry( p->pJust, iVar, i )
        {
            if ( Cbs2_VarIsJust(p, Gia_ManObj(p->pAig, iVar), iVar) )
                p->pJust.pData[k++] = iVar;
            else if ( (hClause = Cbs2_ManPropagateTwo( p, iVar, Level )) )
                return hClause;
        }
        if ( k == p->pJust.iTail )
            break;
        p->pJust.iTail = k;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Solve the problem recursively.]

  Description [Returns learnt clause if unsat, NULL if sat or undecided.]
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
int Cbs2_ManSolve_rec( Cbs2_Man_t * p, int Level )
{ 
    Gia_Obj_t * pVar;
    Cbs2_Que_t * pQue = &(p->pClauses);
    int iPropHead, iJustHead, iJustTail;
    int hClause, hLearn0, hLearn1, iVar, iDecLit;
    // propagate assignments
    assert( !Cbs2_QueIsEmpty(&p->pProp) );
    if ( (hClause = Cbs2_ManPropagate( p, Level )) )
        return hClause;
    // check for satisfying assignment
    assert( Cbs2_QueIsEmpty(&p->pProp) );
    if ( Cbs2_QueIsEmpty(&p->pJust) )
        return 0;
    // quit using resource limits
    p->Pars.nJustThis = Abc_MaxInt( p->Pars.nJustThis, p->pJust.iTail - p->pJust.iHead );
    if ( Cbs2_ManCheckLimits( p ) )
        return 0;
    // remember the state before branching
    iPropHead = p->pProp.iHead;
    Cbs2_QueStore( &p->pJust, &iJustHead, &iJustTail );
    // find the decision variable
/*
    if ( p->Pars.fUseHighest )
        pVar = Cbs2_ManDecideHighest( p );
    else if ( p->Pars.fUseLowest )
        pVar = Cbs2_ManDecideLowest( p );
    else if ( p->Pars.fUseMaxFF )
        pVar = Cbs2_ManDecideMaxFF( p );
    else assert( 0 );
*/
    assert( p->Pars.fUseHighest );
    iVar = Cbs2_ManDecideHighest( p );
    pVar = Gia_ManObj( p->pAig, iVar );
    assert( Cbs2_VarIsJust(p, pVar, iVar) );
    // chose decision variable using fanout count
    if ( Gia_ObjRefNum(p->pAig, Gia_ObjFanin0(pVar)) > Gia_ObjRefNum(p->pAig, Gia_ObjFanin1(pVar)) )
        iDecLit = Abc_LitNot(Gia_ObjFaninLit0(pVar, iVar));
    else
        iDecLit = Abc_LitNot(Gia_ObjFaninLit1(pVar, iVar));
    // decide on first fanin
    Cbs2_ManAssign( p, iDecLit, Level+1, 0, 0 );
    if ( !(hLearn0 = Cbs2_ManSolve_rec( p, Level+1 )) )
        return 0;
    if ( pQue->pData[hLearn0] != Abc_Lit2Var(iDecLit) )
        return hLearn0;
    Cbs2_ManCancelUntil( p, iPropHead );
    Cbs2_QueRestore( &p->pJust, iJustHead, iJustTail );
    // decide on second fanin
    Cbs2_ManAssign( p, Abc_LitNot(iDecLit), Level+1, 0, 0 );
    if ( !(hLearn1 = Cbs2_ManSolve_rec( p, Level+1 )) )
        return 0;
    if ( pQue->pData[hLearn1] != Abc_Lit2Var(iDecLit) )
        return hLearn1;
    hClause = Cbs2_ManResolve( p, Level, hLearn0, hLearn1 );
//    Cbs2_ManPrintClauseNew( p, Level, hClause );
//    if ( Level > Cbs2_ClauseDecLevel(p, hClause) )
//        p->Pars.nBTThisNc++;
    p->Pars.nBTThis++;
    return hClause;
}

/**Function*************************************************************

  Synopsis    [Looking for a satisfying assignment of the node.]

  Description [Assumes that each node has flag pObj->fMark0 set to 0.
  Returns 1 if unsatisfiable, 0 if satisfiable, and -1 if undecided.
  The node may be complemented. ]
               
  SideEffects [The two procedures differ in the CEX format.]

  SeeAlso     []

***********************************************************************/
int Cbs2_ManSolve( Cbs2_Man_t * p, int iLit )
{
    int RetValue = 0;
    assert( !p->pProp.iHead && !p->pProp.iTail );
    assert( !p->pJust.iHead && !p->pJust.iTail );
    assert( p->pClauses.iHead == 1 && p->pClauses.iTail == 1 );
    p->Pars.nBTThis = p->Pars.nJustThis = p->Pars.nBTThisNc = 0;
    Cbs2_ManAssign( p, iLit, 0, 0, 0 );
    if ( !Cbs2_ManSolve_rec(p, 0) && !Cbs2_ManCheckLimits(p) )
        Cbs2_ManSaveModel( p, p->vModel );
    else
        RetValue = 1;
    Cbs2_ManCancelUntil( p, 0 );
    p->pJust.iHead = p->pJust.iTail = 0;
    p->pClauses.iHead = p->pClauses.iTail = 1;
    p->Pars.nBTTotal += p->Pars.nBTThis;
    p->Pars.nJustTotal = Abc_MaxInt( p->Pars.nJustTotal, p->Pars.nJustThis );
    if ( Cbs2_ManCheckLimits( p ) )
        RetValue = -1;
    return RetValue;
}
int Cbs2_ManSolve2( Cbs2_Man_t * p, int iLit, int iLit2 )
{
    int RetValue = 0;
    assert( !p->pProp.iHead && !p->pProp.iTail );
    assert( !p->pJust.iHead && !p->pJust.iTail );
    assert( p->pClauses.iHead == 1 && p->pClauses.iTail == 1 );
    p->Pars.nBTThis = p->Pars.nJustThis = p->Pars.nBTThisNc = 0;
    Cbs2_ManAssign( p, iLit, 0, 0, 0 );
    if ( iLit2 ) 
    Cbs2_ManAssign( p, iLit2, 0, 0, 0 );
    if ( !Cbs2_ManSolve_rec(p, 0) && !Cbs2_ManCheckLimits(p) )
        Cbs2_ManSaveModelAll( p, p->vModel );
    else
        RetValue = 1;
    Cbs2_ManCancelUntil( p, 0 );
    p->pJust.iHead = p->pJust.iTail = 0;
    p->pClauses.iHead = p->pClauses.iTail = 1;
    p->Pars.nBTTotal += p->Pars.nBTThis;
    p->Pars.nJustTotal = Abc_MaxInt( p->Pars.nJustTotal, p->Pars.nJustThis );
    if ( Cbs2_ManCheckLimits( p ) )
        RetValue = -1;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Prints statistics of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cbs2_ManSatPrintStats( Cbs2_Man_t * p )
{
    printf( "CO = %8d  ", Gia_ManCoNum(p->pAig) );
    printf( "AND = %8d  ", Gia_ManAndNum(p->pAig) );
    printf( "Conf = %6d  ", p->Pars.nBTLimit );
    printf( "JustMax = %5d  ", p->Pars.nJustLimit );
    printf( "\n" );
    printf( "Unsat calls %6d  (%6.2f %%)   Ave conf = %8.1f   ", 
        p->nSatUnsat, p->nSatTotal? 100.0*p->nSatUnsat/p->nSatTotal :0.0, p->nSatUnsat? 1.0*p->nConfUnsat/p->nSatUnsat :0.0 );
    ABC_PRTP( "Time", p->timeSatUnsat, p->timeTotal );
    printf( "Sat   calls %6d  (%6.2f %%)   Ave conf = %8.1f   ", 
        p->nSatSat,   p->nSatTotal? 100.0*p->nSatSat/p->nSatTotal :0.0, p->nSatSat? 1.0*p->nConfSat/p->nSatSat : 0.0 );
    ABC_PRTP( "Time", p->timeSatSat,   p->timeTotal );
    printf( "Undef calls %6d  (%6.2f %%)   Ave conf = %8.1f   ", 
        p->nSatUndec, p->nSatTotal? 100.0*p->nSatUndec/p->nSatTotal :0.0, p->nSatUndec? 1.0*p->nConfUndec/p->nSatUndec : 0.0 );
    ABC_PRTP( "Time", p->timeSatUndec, p->timeTotal );
    ABC_PRT( "Total time", p->timeTotal );
}

/**Function*************************************************************

  Synopsis    [Procedure to test the new SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cbs2_ManSolveMiterNc( Gia_Man_t * pAig, int nConfs, Vec_Str_t ** pvStatus, int fVerbose )
{
    extern void Gia_ManCollectTest( Gia_Man_t * pAig );
    extern void Cec_ManSatAddToStore( Vec_Int_t * vCexStore, Vec_Int_t * vCex, int Out );
    Cbs2_Man_t * p; 
    Vec_Int_t * vCex, * vVisit, * vCexStore;
    Vec_Str_t * vStatus;
    Gia_Obj_t * pRoot; 
    int i, status;
    abctime clk, clkTotal = Abc_Clock();
    assert( Gia_ManRegNum(pAig) == 0 );
//    Gia_ManCollectTest( pAig );
    // prepare AIG
    Gia_ManCreateRefs( pAig );
    //Gia_ManCleanMark0( pAig );
    //Gia_ManCleanMark1( pAig );
    //Gia_ManFillValue( pAig ); // maps nodes into trail ids
    //Gia_ManSetPhase( pAig ); // maps nodes into trail ids
    // create logic network
    p = Cbs2_ManAlloc( pAig );
    p->Pars.nBTLimit = nConfs;
    // create resulting data-structures
    vStatus   = Vec_StrAlloc( Gia_ManPoNum(pAig) );
    vCexStore = Vec_IntAlloc( 10000 );
    vVisit    = Vec_IntAlloc( 100 );
    vCex      = Cbs2_ReadModel( p );
    // solve for each output
    Gia_ManForEachCo( pAig, pRoot, i )
    {
//        printf( "\n" );

        Vec_IntClear( vCex );
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pRoot)) )
        {
            if ( Gia_ObjFaninC0(pRoot) )
            {
//                printf( "Constant 1 output of SRM!!!\n" );
                Cec_ManSatAddToStore( vCexStore, vCex, i ); // trivial counter-example
                Vec_StrPush( vStatus, 0 );
            }
            else
            {
//                printf( "Constant 0 output of SRM!!!\n" );
                Vec_StrPush( vStatus, 1 );
            }
            continue;
        }
        clk = Abc_Clock();
        p->Pars.fUseHighest = 1;
        p->Pars.fUseLowest  = 0;
        status = Cbs2_ManSolve( p, Gia_ObjFaninLit0p(pAig, pRoot) );
//        printf( "\n" );
/*
        if ( status == -1 )
        {
            p->Pars.fUseHighest = 0;
            p->Pars.fUseLowest  = 1;
            status = Cbs2_ManSolve( p, Gia_ObjChild0(pRoot) );
        }
*/
        Vec_StrPush( vStatus, (char)status );
        if ( status == -1 )
        {
            p->nSatUndec++;
            p->nConfUndec += p->Pars.nBTThis;
            Cec_ManSatAddToStore( vCexStore, NULL, i ); // timeout
            p->timeSatUndec += Abc_Clock() - clk;
            continue;
        }
        if ( status == 1 )
        {
            p->nSatUnsat++;
            p->nConfUnsat += p->Pars.nBTThis;
            p->timeSatUnsat += Abc_Clock() - clk;
            continue;
        }
        p->nSatSat++;
        p->nConfSat += p->Pars.nBTThis;
//        Gia_SatVerifyPattern( pAig, pRoot, vCex, vVisit );
        Cec_ManSatAddToStore( vCexStore, vCex, i );
        p->timeSatSat += Abc_Clock() - clk;
    }
    Vec_IntFree( vVisit );
    p->nSatTotal = Gia_ManPoNum(pAig);
    p->timeTotal = Abc_Clock() - clkTotal;
    if ( fVerbose )
        Cbs2_ManSatPrintStats( p );
//    printf( "RecCalls = %8d.  RecClause = %8d.  RecNonChro = %8d.\n", p->nRecCall, p->nRecClause, p->nRecNonChro );
    Cbs2_ManStop( p );
    *pvStatus = vStatus;

//    printf( "Total number of cex literals = %d. (Ave = %d)\n", 
//         Vec_IntSize(vCexStore)-2*p->nSatUndec-2*p->nSatSat, 
//        (Vec_IntSize(vCexStore)-2*p->nSatUndec-2*p->nSatSat)/p->nSatSat );
    return vCexStore;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

