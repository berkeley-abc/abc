/**CFile****************************************************************

  FileName    [darOper.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [AIG operations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darOper.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// procedure to detect an EXOR gate
static inline int Dar_ObjIsExorType( Dar_Obj_t * p0, Dar_Obj_t * p1, Dar_Obj_t ** ppFan0, Dar_Obj_t ** ppFan1 )
{
    if ( !Dar_IsComplement(p0) || !Dar_IsComplement(p1) )
        return 0;
    p0 = Dar_Regular(p0);
    p1 = Dar_Regular(p1);
    if ( !Dar_ObjIsAnd(p0) || !Dar_ObjIsAnd(p1) )
        return 0;
    if ( Dar_ObjFanin0(p0) != Dar_ObjFanin0(p1) || Dar_ObjFanin1(p0) != Dar_ObjFanin1(p1) )
        return 0;
    if ( Dar_ObjFaninC0(p0) == Dar_ObjFaninC0(p1) || Dar_ObjFaninC1(p0) == Dar_ObjFaninC1(p1) )
        return 0;
    *ppFan0 = Dar_ObjChild0(p0);
    *ppFan1 = Dar_ObjChild1(p0);
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns i-th elementary variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_IthVar( Dar_Man_t * p, int i )
{
    int v;
    for ( v = Dar_ManPiNum(p); v <= i; v++ )
        Dar_ObjCreatePi( p );
    assert( i < Vec_PtrSize(p->vPis) );
    return Dar_ManPi( p, i );
}

/**Function*************************************************************

  Synopsis    [Perform one operation.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Oper( Dar_Man_t * p, Dar_Obj_t * p0, Dar_Obj_t * p1, Dar_Type_t Type )
{
    if ( Type == DAR_AIG_AND )
        return Dar_And( p, p0, p1 );
    if ( Type == DAR_AIG_EXOR )
        return Dar_Exor( p, p0, p1 );
    assert( 0 );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_And( Dar_Man_t * p, Dar_Obj_t * p0, Dar_Obj_t * p1 )
{
    Dar_Obj_t * pGhost, * pResult;
//    Dar_Obj_t * pFan0, * pFan1;
    // check trivial cases
    if ( p0 == p1 )
        return p0;
    if ( p0 == Dar_Not(p1) )
        return Dar_Not(p->pConst1);
    if ( Dar_Regular(p0) == p->pConst1 )
        return p0 == p->pConst1 ? p1 : Dar_Not(p->pConst1);
    if ( Dar_Regular(p1) == p->pConst1 )
        return p1 == p->pConst1 ? p0 : Dar_Not(p->pConst1);
    // check if it can be an EXOR gate
//    if ( Dar_ObjIsExorType( p0, p1, &pFan0, &pFan1 ) )
//        return Dar_Exor( p, pFan0, pFan1 );
    // check the table
    pGhost = Dar_ObjCreateGhost( p, p0, p1, DAR_AIG_AND );
    if ( pResult = Dar_TableLookup( p, pGhost ) )
        return pResult;
    return Dar_ObjCreate( p, pGhost );
}

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Exor( Dar_Man_t * p, Dar_Obj_t * p0, Dar_Obj_t * p1 )
{
/*
    Dar_Obj_t * pGhost, * pResult;
    // check trivial cases
    if ( p0 == p1 )
        return Dar_Not(p->pConst1);
    if ( p0 == Dar_Not(p1) )
        return p->pConst1;
    if ( Dar_Regular(p0) == p->pConst1 )
        return Dar_NotCond( p1, p0 == p->pConst1 );
    if ( Dar_Regular(p1) == p->pConst1 )
        return Dar_NotCond( p0, p1 == p->pConst1 );
    // check the table
    pGhost = Dar_ObjCreateGhost( p, p0, p1, DAR_AIG_EXOR );
    if ( pResult = Dar_TableLookup( p, pGhost ) )
        return pResult;
    return Dar_ObjCreate( p, pGhost );
*/
    return Dar_Or( p, Dar_And(p, p0, Dar_Not(p1)), Dar_And(p, Dar_Not(p0), p1) );
}

/**Function*************************************************************

  Synopsis    [Implements Boolean OR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Or( Dar_Man_t * p, Dar_Obj_t * p0, Dar_Obj_t * p1 )
{
    return Dar_Not( Dar_And( p, Dar_Not(p0), Dar_Not(p1) ) );
}

/**Function*************************************************************

  Synopsis    [Implements ITE operation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Mux( Dar_Man_t * p, Dar_Obj_t * pC, Dar_Obj_t * p1, Dar_Obj_t * p0 )
{
/*    
    Dar_Obj_t * pTempA1, * pTempA2, * pTempB1, * pTempB2, * pTemp;
    int Count0, Count1;
    // consider trivial cases
    if ( p0 == Dar_Not(p1) )
        return Dar_Exor( p, pC, p0 );
    // other cases can be added
    // implement the first MUX (F = C * x1 + C' * x0)

    // check for constants here!!!

    pTempA1 = Dar_TableLookup( p, Dar_ObjCreateGhost(p, pC,          p1, DAR_AIG_AND) );
    pTempA2 = Dar_TableLookup( p, Dar_ObjCreateGhost(p, Dar_Not(pC), p0, DAR_AIG_AND) );
    if ( pTempA1 && pTempA2 )
    {
        pTemp = Dar_TableLookup( p, Dar_ObjCreateGhost(p, Dar_Not(pTempA1), Dar_Not(pTempA2), DAR_AIG_AND) );
        if ( pTemp ) return Dar_Not(pTemp);
    }
    Count0 = (pTempA1 != NULL) + (pTempA2 != NULL);
    // implement the second MUX (F' = C * x1' + C' * x0')
    pTempB1 = Dar_TableLookup( p, Dar_ObjCreateGhost(p, pC,          Dar_Not(p1), DAR_AIG_AND) );
    pTempB2 = Dar_TableLookup( p, Dar_ObjCreateGhost(p, Dar_Not(pC), Dar_Not(p0), DAR_AIG_AND) );
    if ( pTempB1 && pTempB2 )
    {
        pTemp = Dar_TableLookup( p, Dar_ObjCreateGhost(p, Dar_Not(pTempB1), Dar_Not(pTempB2), DAR_AIG_AND) );
        if ( pTemp ) return pTemp;
    }
    Count1 = (pTempB1 != NULL) + (pTempB2 != NULL);
    // compare and decide which one to implement
    if ( Count0 >= Count1 )
    {
        pTempA1 = pTempA1? pTempA1 : Dar_And(p, pC,          p1);
        pTempA2 = pTempA2? pTempA2 : Dar_And(p, Dar_Not(pC), p0);
        return Dar_Or( p, pTempA1, pTempA2 );
    }
    pTempB1 = pTempB1? pTempB1 : Dar_And(p, pC,          Dar_Not(p1));
    pTempB2 = pTempB2? pTempB2 : Dar_And(p, Dar_Not(pC), Dar_Not(p0));
    return Dar_Not( Dar_Or( p, pTempB1, pTempB2 ) );
*/
    return Dar_Or( p, Dar_And(p, pC, p1), Dar_And(p, Dar_Not(pC), p0) );
}

/**Function*************************************************************

  Synopsis    [Implements ITE operation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Maj( Dar_Man_t * p, Dar_Obj_t * pA, Dar_Obj_t * pB, Dar_Obj_t * pC )
{
    return Dar_Or( p, Dar_Or(p, Dar_And(p, pA, pB), Dar_And(p, pA, pC)), Dar_And(p, pB, pC) );
}

/**Function*************************************************************

  Synopsis    [Constructs the well-balanced tree of gates.]

  Description [Disregards levels and possible logic sharing.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Multi_rec( Dar_Man_t * p, Dar_Obj_t ** ppObjs, int nObjs, Dar_Type_t Type )
{
    Dar_Obj_t * pObj1, * pObj2;
    if ( nObjs == 1 )
        return ppObjs[0];
    pObj1 = Dar_Multi_rec( p, ppObjs,           nObjs/2,         Type );
    pObj2 = Dar_Multi_rec( p, ppObjs + nObjs/2, nObjs - nObjs/2, Type );
    return Dar_Oper( p, pObj1, pObj2, Type );
}

/**Function*************************************************************

  Synopsis    [Old code.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Multi( Dar_Man_t * p, Dar_Obj_t ** pArgs, int nArgs, Dar_Type_t Type )
{
    assert( Type == DAR_AIG_AND || Type == DAR_AIG_EXOR );
    assert( nArgs > 0 );
    return Dar_Multi_rec( p, pArgs, nArgs, Type );
}

/**Function*************************************************************

  Synopsis    [Implements the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_Miter( Dar_Man_t * p, Vec_Ptr_t * vPairs )
{
    int i;
    assert( vPairs->nSize > 0 );
    assert( vPairs->nSize % 2 == 0 );
    // go through the cubes of the node's SOP
    for ( i = 0; i < vPairs->nSize; i += 2 )
        vPairs->pArray[i/2] = Dar_Not( Dar_Exor( p, vPairs->pArray[i], vPairs->pArray[i+1] ) );
    vPairs->nSize = vPairs->nSize/2;
    return Dar_Not( Dar_Multi_rec( p, (Dar_Obj_t **)vPairs->pArray, vPairs->nSize, DAR_AIG_AND ) );
}

/**Function*************************************************************

  Synopsis    [Creates AND function with nVars inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_CreateAnd( Dar_Man_t * p, int nVars )
{
    Dar_Obj_t * pFunc;
    int i;
    pFunc = Dar_ManConst1( p );
    for ( i = 0; i < nVars; i++ )
        pFunc = Dar_And( p, pFunc, Dar_IthVar(p, i) );
    return pFunc;
}

/**Function*************************************************************

  Synopsis    [Creates AND function with nVars inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_CreateOr( Dar_Man_t * p, int nVars )
{
    Dar_Obj_t * pFunc;
    int i;
    pFunc = Dar_ManConst0( p );
    for ( i = 0; i < nVars; i++ )
        pFunc = Dar_Or( p, pFunc, Dar_IthVar(p, i) );
    return pFunc;
}

/**Function*************************************************************

  Synopsis    [Creates AND function with nVars inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_CreateExor( Dar_Man_t * p, int nVars )
{
    Dar_Obj_t * pFunc;
    int i;
    pFunc = Dar_ManConst0( p );
    for ( i = 0; i < nVars; i++ )
        pFunc = Dar_Exor( p, pFunc, Dar_IthVar(p, i) );
    return pFunc;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


