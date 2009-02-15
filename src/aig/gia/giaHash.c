/**CFile****************************************************************

  FileName    [giaHash.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Structural hashing.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaHash.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Hashing the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_ManHashOne( int iLit0, int iLit1, int TableSize ) 
{
    unsigned Key = 0;
    assert( iLit0 < iLit1 );
    Key ^= Gia_Lit2Var(iLit0) * 7937;
    Key ^= Gia_Lit2Var(iLit1) * 2971;
    Key ^= Gia_LitIsCompl(iLit0) * 911;
    Key ^= Gia_LitIsCompl(iLit1) * 353;
    return (int)(Key % TableSize);
}

/**Function*************************************************************

  Synopsis    [Returns the place where this node is stored (or should be stored).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int * Gia_ManHashFind( Gia_Man_t * p, int iLit0, int iLit1 )
{
    Gia_Obj_t * pThis;
    int * pPlace = p->pHTable + Gia_ManHashOne( iLit0, iLit1, p->nHTable );
    for ( pThis = (*pPlace)? Gia_ManObj(p, Gia_Lit2Var(*pPlace)) : NULL; pThis; 
          pPlace = &pThis->Value, pThis = (*pPlace)? Gia_ManObj(p, Gia_Lit2Var(*pPlace)) : NULL )
              if ( Gia_ObjFaninLit0p(p, pThis) == iLit0 && Gia_ObjFaninLit1p(p, pThis) == iLit1 )
                  break;
    return pPlace;
}

/**Function*************************************************************

  Synopsis    [Starts the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManHashAlloc( Gia_Man_t * p )  
{
    assert( p->pHTable == NULL );
    p->nHTable = Aig_PrimeCudd( p->nObjsAlloc / 3 );
    p->pHTable = ABC_CALLOC( int, p->nHTable );
}

/**Function*************************************************************

  Synopsis    [Starts the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManHashStart( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int * pPlace, i;
    Gia_ManHashAlloc( p );
    Gia_ManCleanValue( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        pPlace = Gia_ManHashFind( p, Gia_ObjFaninLit0(pObj, i), Gia_ObjFaninLit1(pObj, i) );
        assert( *pPlace == 0 );
        *pPlace = Gia_Var2Lit( i, 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Stops the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManHashStop( Gia_Man_t * p )  
{
    ABC_FREE( p->pHTable );
    p->nHTable = 0;
}

/**Function*************************************************************

  Synopsis    [Resizes the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManHashResize( Gia_Man_t * p )
{
    Gia_Obj_t * pThis;
    int * pHTableOld, * pPlace;
    int nHTableOld, iNext, Counter, Counter2, i;
    assert( p->pHTable != NULL );
    // replace the table
    pHTableOld = p->pHTable;
    nHTableOld = p->nHTable;
    p->nHTable = Aig_PrimeCudd( 2 * Gia_ManAndNum(p) ); 
    p->pHTable = ABC_CALLOC( int, p->nHTable );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < nHTableOld; i++ )
    for ( pThis = (pHTableOld[i]? Gia_ManObj(p, Gia_Lit2Var(pHTableOld[i])) : NULL),
          iNext = (pThis? pThis->Value : 0);  
          pThis;  pThis = (iNext? Gia_ManObj(p, Gia_Lit2Var(iNext)) : NULL),   
          iNext = (pThis? pThis->Value : 0)  )
    {
        pThis->Value = 0;
        pPlace = Gia_ManHashFind( p, Gia_ObjFaninLit0p(p, pThis), Gia_ObjFaninLit1p(p, pThis) );
        assert( *pPlace == 0 ); // should not be there
        *pPlace = Gia_Var2Lit( Gia_ObjId(p, pThis), 0 );
        assert( *pPlace != 0 );
        Counter++;
    }
    Counter2 = Gia_ManAndNum(p);
    assert( Counter == Counter2 );
    ABC_FREE( pHTableOld );
}


/**Function*************************************************************

  Synopsis    [Recognizes what nodes are control and data inputs of a MUX.]

  Description [If the node is a MUX, returns the control variable C.
  Assigns nodes T and E to be the then and else variables of the MUX. 
  Node C is never complemented. Nodes T and E can be complemented.
  This function also recognizes EXOR/NEXOR gates as MUXes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Gia_Obj_t * Gia_ObjRecognizeMuxTwo( Gia_Obj_t * pNode0, Gia_Obj_t * pNode1, Gia_Obj_t ** ppNodeT, Gia_Obj_t ** ppNodeE )
{
    assert( !Gia_IsComplement(pNode0) );
    assert( !Gia_IsComplement(pNode1) );
    // find the control variable
    if ( Gia_ObjFanin1(pNode0) == Gia_ObjFanin1(pNode1) && (Gia_ObjFaninC1(pNode0) ^ Gia_ObjFaninC1(pNode1)) )
    {
//        if ( FrGia_IsComplement(pNode1->p2) )
        if ( Gia_ObjFaninC1(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Gia_Not(Gia_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Gia_Not(Gia_ObjChild0(pNode0));//pNode1->p1);
            return Gia_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Gia_Not(Gia_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Gia_Not(Gia_ObjChild0(pNode1));//pNode2->p1);
            return Gia_ObjChild1(pNode0);//pNode1->p2;
        }
    }
    else if ( Gia_ObjFanin0(pNode0) == Gia_ObjFanin0(pNode1) && (Gia_ObjFaninC0(pNode0) ^ Gia_ObjFaninC0(pNode1)) )
    {
//        if ( FrGia_IsComplement(pNode1->p1) )
        if ( Gia_ObjFaninC0(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Gia_Not(Gia_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Gia_Not(Gia_ObjChild1(pNode0));//pNode1->p2);
            return Gia_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Gia_Not(Gia_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Gia_Not(Gia_ObjChild1(pNode1));//pNode2->p2);
            return Gia_ObjChild0(pNode0);//pNode1->p1;
        }
    }
    else if ( Gia_ObjFanin0(pNode0) == Gia_ObjFanin1(pNode1) && (Gia_ObjFaninC0(pNode0) ^ Gia_ObjFaninC1(pNode1)) )
    {
//        if ( FrGia_IsComplement(pNode1->p1) )
        if ( Gia_ObjFaninC0(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Gia_Not(Gia_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Gia_Not(Gia_ObjChild1(pNode0));//pNode1->p2);
            return Gia_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Gia_Not(Gia_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Gia_Not(Gia_ObjChild0(pNode1));//pNode2->p1);
            return Gia_ObjChild0(pNode0);//pNode1->p1;
        }
    }
    else if ( Gia_ObjFanin1(pNode0) == Gia_ObjFanin0(pNode1) && (Gia_ObjFaninC1(pNode0) ^ Gia_ObjFaninC0(pNode1)) )
    {
//        if ( FrGia_IsComplement(pNode1->p2) )
        if ( Gia_ObjFaninC1(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Gia_Not(Gia_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Gia_Not(Gia_ObjChild0(pNode0));//pNode1->p1);
            return Gia_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Gia_Not(Gia_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Gia_Not(Gia_ObjChild1(pNode1));//pNode2->p2);
            return Gia_ObjChild1(pNode0);//pNode1->p2;
        }
    }
    assert( 0 ); // this is not MUX
    return NULL;
}


/**Function*************************************************************

  Synopsis    [Rehashes AIG with mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Gia_Obj_t * Gia_ManHashAndP( Gia_Man_t * p, Gia_Obj_t * p0, Gia_Obj_t * p1 )  
{ 
    return Gia_ObjFromLit( p, Gia_ManHashAnd( p, Gia_ObjToLit(p, p0), Gia_ObjToLit(p, p1) ) );
}

/**Function*************************************************************

  Synopsis    [Rehashes AIG with mapping.]

  Description [http://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Gia_Obj_t * Gia_ManAddStrash( Gia_Man_t * p, Gia_Obj_t * p0, Gia_Obj_t * p1 )  
{ 
    Gia_Obj_t * pNode0, * pNode1, * pFanA, * pFanB, * pFanC, * pFanD;
    assert( p->fAddStrash );
    if ( !Gia_ObjIsAnd(Gia_Regular(p0)) && !Gia_ObjIsAnd(Gia_Regular(p1)) )
        return NULL;
    pNode0 = Gia_Regular(p0);
    pNode1 = Gia_Regular(p1);
    pFanA = Gia_ObjChild0(pNode0);
    pFanB = Gia_ObjChild1(pNode0);
    pFanC = Gia_ObjChild0(pNode1);
    pFanD = Gia_ObjChild1(pNode1);
    if ( Gia_IsComplement(p0) )
    {
        if ( pFanA == Gia_Not(p1) || pFanB == Gia_Not(p1) )
            return p1;
        if ( pFanB == p1 )
            return Gia_ManHashAndP( p, Gia_Not(pFanA), pFanB );
        if ( pFanA == p1 )
            return Gia_ManHashAndP( p, Gia_Not(pFanB), pFanA );
    }
    else
    {
        if ( pFanA == Gia_Not(p1) || pFanB == Gia_Not(p1) )
            return Gia_ManConst0(p);
        if ( pFanA == p1 || pFanB == p1 )
            return p0;
    }
    if ( Gia_IsComplement(p1) )
    {
        if ( pFanC == Gia_Not(p0) || pFanD == Gia_Not(p0) )
            return p0;
        if ( pFanD == p0 )
            return Gia_ManHashAndP( p, Gia_Not(pFanC), pFanD );
        if ( pFanC == p0 )
            return Gia_ManHashAndP( p, Gia_Not(pFanD), pFanC );
    }
    else
    {
        if ( pFanC == Gia_Not(p0) || pFanD == Gia_Not(p0) )
            return Gia_ManConst0(p);
        if ( pFanC == p0 || pFanD == p0 )
            return p1;
    }
    if ( !Gia_IsComplement(p0) && !Gia_IsComplement(p1) ) 
    {
        if ( pFanA == Gia_Not(pFanC) || pFanA == Gia_Not(pFanD) || pFanB == Gia_Not(pFanC) || pFanB == Gia_Not(pFanD) )
            return Gia_ManConst0(p);
        if ( pFanA == pFanC || pFanB == pFanC )
            return Gia_ManHashAndP( p, p0, pFanD );
        if ( pFanB == pFanC || pFanB == pFanD )
            return Gia_ManHashAndP( p, pFanA, p1 );
        if ( pFanA == pFanD || pFanB == pFanD )
            return Gia_ManHashAndP( p, p0, pFanC );
        if ( pFanA == pFanC || pFanA == pFanD )
            return Gia_ManHashAndP( p, pFanB, p1 );
    }
    else if ( Gia_IsComplement(p0) && !Gia_IsComplement(p1) )
    {
        if ( pFanA == Gia_Not(pFanC) || pFanA == Gia_Not(pFanD) || pFanB == Gia_Not(pFanC) || pFanB == Gia_Not(pFanD) )
            return p1;
        if ( pFanB == pFanC || pFanB == pFanD )
            return Gia_ManHashAndP( p, Gia_Not(pFanA), p1 );
        if ( pFanA == pFanC || pFanA == pFanD )
            return Gia_ManHashAndP( p, Gia_Not(pFanB), p1 );
    }
    else if ( !Gia_IsComplement(p0) && Gia_IsComplement(p1) )
    {
        if ( pFanC == Gia_Not(pFanA) || pFanC == Gia_Not(pFanB) || pFanD == Gia_Not(pFanA) || pFanD == Gia_Not(pFanB) )
            return p0;
        if ( pFanD == pFanA || pFanD == pFanB )
            return Gia_ManHashAndP( p, Gia_Not(pFanC), p0 );
        if ( pFanC == pFanA || pFanC == pFanB )
            return Gia_ManHashAndP( p, Gia_Not(pFanD), p0 );
    }
    else // if ( Gia_IsComplement(p0) && Gia_IsComplement(p1) )
    {
        if ( pFanA == pFanD && pFanB == Gia_Not(pFanC) )
            return Gia_Not(pFanA);
        if ( pFanB == pFanC && pFanA == Gia_Not(pFanD) )
            return Gia_Not(pFanB);
        if ( pFanA == pFanC && pFanB == Gia_Not(pFanD) )
            return Gia_Not(pFanA);
        if ( pFanB == pFanD && pFanA == Gia_Not(pFanC) )
            return Gia_Not(pFanB);
    }
    if ( !Gia_IsComplement(p0) || !Gia_IsComplement(p1) )
        return NULL;
    if ( !Gia_ObjIsAnd(pNode0) || !Gia_ObjIsAnd(pNode1) )
        return NULL;
    if ( (Gia_ObjFanin0(pNode0) == Gia_ObjFanin0(pNode1) && (Gia_ObjFaninC0(pNode0) ^ Gia_ObjFaninC0(pNode1))) || 
         (Gia_ObjFanin0(pNode0) == Gia_ObjFanin1(pNode1) && (Gia_ObjFaninC0(pNode0) ^ Gia_ObjFaninC1(pNode1))) ||
         (Gia_ObjFanin1(pNode0) == Gia_ObjFanin0(pNode1) && (Gia_ObjFaninC1(pNode0) ^ Gia_ObjFaninC0(pNode1))) ||
         (Gia_ObjFanin1(pNode0) == Gia_ObjFanin1(pNode1) && (Gia_ObjFaninC1(pNode0) ^ Gia_ObjFaninC1(pNode1))) )
    {
        Gia_Obj_t * pNodeC, * pNodeT, * pNodeE;
        int fCompl;
        pNodeC = Gia_ObjRecognizeMuxTwo( pNode0, pNode1, &pNodeT, &pNodeE );
        // using non-standard canonical rule for MUX (d0 is not compl; d1 may be compl)
        if ( (fCompl = Gia_IsComplement(pNodeE)) )
        {
            pNodeE = Gia_Not(pNodeE);
            pNodeT = Gia_Not(pNodeT);
        }
        pNode0 = Gia_ManHashAndP( p, Gia_Not(pNodeC), pNodeE );
        pNode1 = Gia_ManHashAndP( p, pNodeC,          pNodeT );
        return Gia_NotCond( Gia_ManHashAndP( p, pNode0, pNode1 ), !fCompl );
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Rehashes AIG with mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManHashAnd( Gia_Man_t * p, int iLit0, int iLit1 )  
{ 
    if ( iLit0 < 2 )
        return iLit0 ? iLit1 : 0;
    if ( iLit1 < 2 )
        return iLit1 ? iLit0 : 0;
    if ( iLit0 == iLit1 )
        return iLit1;
    if ( iLit0 == Gia_LitNot(iLit1) )
        return 0;
    if ( (p->nObjs & 0xFF) == 0 && 2 * p->nHTable < Gia_ManAndNum(p) )
        Gia_ManHashResize( p );
    if ( p->fAddStrash )
    {
        Gia_Obj_t * pObj = Gia_ManAddStrash( p, Gia_ObjFromLit(p, iLit0), Gia_ObjFromLit(p, iLit1) );
        if ( pObj != NULL )
            return Gia_ObjToLit( p, pObj );
    }
    if ( iLit0 > iLit1 )
        iLit0 ^= iLit1, iLit1 ^= iLit0, iLit0 ^= iLit1;
    {
        int * pPlace = Gia_ManHashFind( p, iLit0, iLit1 );
        if ( *pPlace ) 
            return *pPlace;
        if ( p->nObjs < p->nObjsAlloc )
            return *pPlace = Gia_ManAppendAnd( p, iLit0, iLit1 );
        else
        {
            int iNode = Gia_ManAppendAnd( p, iLit0, iLit1 );
            pPlace = Gia_ManHashFind( p, iLit0, iLit1 );
            assert( *pPlace == 0 );
            return *pPlace = iNode;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Rehashes AIG with mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManHashAndTry( Gia_Man_t * p, int iLit0, int iLit1 )  
{ 
    if ( iLit0 < 2 )
        return iLit0 ? iLit1 : 0;
    if ( iLit1 < 2 )
        return iLit1 ? iLit0 : 0;
    if ( iLit0 == iLit1 )
        return iLit1;
    if ( iLit0 == Gia_LitNot(iLit1) )
        return 0;
    if ( iLit0 > iLit1 )
        iLit0 ^= iLit1, iLit1 ^= iLit0, iLit0 ^= iLit1;
    {
        int * pPlace = Gia_ManHashFind( p, iLit0, iLit1 );
        if ( *pPlace ) 
            return *pPlace;
        return -1;
    }
}

/**Function*************************************************************

  Synopsis    [Rehashes AIG with mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManHashXor( Gia_Man_t * p, int iLit0, int iLit1 )  
{ 
    int fCompl = Gia_LitIsCompl(iLit0) ^ Gia_LitIsCompl(iLit1);
    int iTemp0 = Gia_ManHashAnd( p, Gia_LitRegular(iLit0), Gia_LitNot(Gia_LitRegular(iLit1)) );
    int iTemp1 = Gia_ManHashAnd( p, Gia_LitRegular(iLit1), Gia_LitNot(Gia_LitRegular(iLit0)) );
    return Gia_LitNotCond( Gia_ManHashAnd( p, Gia_LitNot(iTemp0), Gia_LitNot(iTemp1) ), !fCompl );
}

/**Function*************************************************************

  Synopsis    [Rehashes AIG with mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManRehash( Gia_Man_t * p )  
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        else if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
//    printf( "Top gate is %s\n", Gia_ObjFaninC0(Gia_ManCo(pNew, 0))? "OR" : "AND" );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


