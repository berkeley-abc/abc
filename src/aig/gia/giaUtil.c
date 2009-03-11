/**CFile****************************************************************

  FileName    [giaUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets phases of the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetMark0( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
        pObj->fMark0 = 1;
}

/**Function*************************************************************

  Synopsis    [Sets phases of the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCleanMark0( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
        pObj->fMark0 = 0;
}

/**Function*************************************************************

  Synopsis    [Sets phases of the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCheckMark0( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
        assert( pObj->fMark0 == 0 );
}

/**Function*************************************************************

  Synopsis    [Sets phases of the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetMark1( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
        pObj->fMark1 = 1;
}

/**Function*************************************************************

  Synopsis    [Sets phases of the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCleanMark1( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
        pObj->fMark1 = 0;
}

/**Function*************************************************************

  Synopsis    [Sets phases of the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCheckMark1( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
        assert( pObj->fMark1 == 0 );
}

/**Function*************************************************************

  Synopsis    [Cleans the value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCleanValue( Gia_Man_t * p )  
{
    int i;
    for ( i = 0; i < p->nObjs; i++ )
        p->pObjs[i].Value = 0;
}

/**Function*************************************************************

  Synopsis    [Cleans the value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManFillValue( Gia_Man_t * p )  
{
    int i;
    for ( i = 0; i < p->nObjs; i++ )
        p->pObjs[i].Value = ~0;
}

/**Function*************************************************************

  Synopsis    [Sets phases of the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetPhase( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
            pObj->fPhase = (Gia_ObjPhase(Gia_ObjFanin0(pObj)) ^ Gia_ObjFaninC0(pObj)) & 
                           (Gia_ObjPhase(Gia_ObjFanin1(pObj)) ^ Gia_ObjFaninC1(pObj));
        else if ( Gia_ObjIsCo(pObj) )
            pObj->fPhase = (Gia_ObjPhase(Gia_ObjFanin0(pObj)) ^ Gia_ObjFaninC0(pObj));
        else
            pObj->fPhase = 0;
    }
}

/**Function*************************************************************

  Synopsis    [Assigns levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManLevelNum( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    if ( p->pLevels )
        return p->nLevels;
    p->nLevels = 0;
    p->pLevels = ABC_ALLOC( int, p->nObjsAlloc );
    Gia_ManForEachObj( p, pObj, i )
        if ( Gia_ObjIsAnd(pObj) )
        {
            if ( p->pLevels[Gia_ObjFaninId0(pObj, i)] > p->pLevels[Gia_ObjFaninId1(pObj, i)] )
                p->pLevels[i] = 1 + p->pLevels[Gia_ObjFaninId0(pObj, i)];
            else
                p->pLevels[i] = 1 + p->pLevels[Gia_ObjFaninId1(pObj, i)];
            if ( p->nLevels < p->pLevels[i] )
                p->nLevels = p->pLevels[i];
        }
        else if ( Gia_ObjIsCo(pObj) )
            p->pLevels[i] = p->pLevels[Gia_ObjFaninId0(pObj, i)];
        else
            p->pLevels[i] = 0;
    return p->nLevels;
}

/**Function*************************************************************

  Synopsis    [Assigns levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetRefs( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
    {
        pObj->Value = 0;
        if ( Gia_ObjIsAnd(pObj) )
        {
            Gia_ObjFanin0(pObj)->Value++;
            Gia_ObjFanin1(pObj)->Value++;
        }
        else if ( Gia_ObjIsCo(pObj) )
            Gia_ObjFanin0(pObj)->Value++;
    }
}

/**Function*************************************************************

  Synopsis    [Assigns references.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCreateRefs( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    assert( p->pRefs == NULL );
    p->pRefs = ABC_CALLOC( int, Gia_ManObjNum(p) );
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
            Gia_ObjRefFanin0Inc( p, pObj );
            Gia_ObjRefFanin1Inc( p, pObj );
        }
        else if ( Gia_ObjIsCo(pObj) )
            Gia_ObjRefFanin0Inc( p, pObj );
    }
}

/**Function*************************************************************

  Synopsis    [Assigns references.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Gia_ManCreateMuxRefs( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj, * pCtrl, * pFan0, * pFan1;
    int i, * pMuxRefs;
    pMuxRefs = ABC_CALLOC( int, Gia_ManObjNum(p) );
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( Gia_ObjRecognizeExor( pObj, &pFan0, &pFan1 ) )
            continue;
        if ( !Gia_ObjIsMuxType(pObj) )
            continue;
        pCtrl = Gia_ObjRecognizeMux( pObj, &pFan0, &pFan1 );
        pMuxRefs[ Gia_ObjId(p, Gia_Regular(pCtrl)) ]++;
    }
    return pMuxRefs;
}

/**Function*************************************************************

  Synopsis    [Computes the maximum frontier size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCrossCut( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, nCutCur = 0, nCutMax = 0;
    Gia_ManSetRefs( p );
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( pObj->Value )
            nCutCur++;
        if ( nCutMax < nCutCur )
            nCutMax = nCutCur;
        if ( Gia_ObjIsAnd(pObj) )
        {
            if ( --Gia_ObjFanin0(pObj)->Value == 0 )
                nCutCur--;
            if ( --Gia_ObjFanin1(pObj)->Value == 0 )
                nCutCur--;
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            if ( --Gia_ObjFanin0(pObj)->Value == 0 )
                nCutCur--;
        }
    }
//    Gia_ManForEachObj( p, pObj, i )
//        assert( pObj->Value == 0 );
    return nCutMax;
}

/**Function*************************************************************

  Synopsis    [Makes sure the manager is normalized.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManIsNormalized( Gia_Man_t * p )  
{
    int i, nOffset;
    nOffset = 1;
    for ( i = 0; i < Gia_ManCiNum(p); i++ )
        if ( !Gia_ObjIsCi( Gia_ManObj(p, nOffset+i) ) )
            return 0;
    nOffset = 1 + Gia_ManCiNum(p) + Gia_ManAndNum(p);
    for ( i = 0; i < Gia_ManCoNum(p); i++ )
        if ( !Gia_ObjIsCo( Gia_ManObj(p, nOffset+i) ) )
            return 0;
    return 1;
}


/**Function*************************************************************

  Synopsis    [Collects PO Ids into one array.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManCollectPoIds( Gia_Man_t * p )
{
    Vec_Int_t * vStart;
    int Entry, i;
    vStart = Vec_IntAlloc( Gia_ManPoNum(p) );
    Vec_IntForEachEntryStop( p->vCos, Entry, i, Gia_ManPoNum(p) )
        Vec_IntPush( vStart, Entry );
    return vStart;
}


/**Function*************************************************************

  Synopsis    [Returns 1 if the node is the root of MUX or EXOR/NEXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjIsMuxType( Gia_Obj_t * pNode )
{
    Gia_Obj_t * pNode0, * pNode1;
    // check that the node is regular
    assert( !Gia_IsComplement(pNode) );
    // if the node is not AND, this is not MUX
    if ( !Gia_ObjIsAnd(pNode) )
        return 0;
    // if the children are not complemented, this is not MUX
    if ( !Gia_ObjFaninC0(pNode) || !Gia_ObjFaninC1(pNode) )
        return 0;
    // get children
    pNode0 = Gia_ObjFanin0(pNode);
    pNode1 = Gia_ObjFanin1(pNode);
    // if the children are not ANDs, this is not MUX
    if ( !Gia_ObjIsAnd(pNode0) || !Gia_ObjIsAnd(pNode1) )
        return 0;
    // otherwise the node is MUX iff it has a pair of equal grandchildren
    return (Gia_ObjFanin0(pNode0) == Gia_ObjFanin0(pNode1) && (Gia_ObjFaninC0(pNode0) ^ Gia_ObjFaninC0(pNode1))) || 
           (Gia_ObjFanin0(pNode0) == Gia_ObjFanin1(pNode1) && (Gia_ObjFaninC0(pNode0) ^ Gia_ObjFaninC1(pNode1))) ||
           (Gia_ObjFanin1(pNode0) == Gia_ObjFanin0(pNode1) && (Gia_ObjFaninC1(pNode0) ^ Gia_ObjFaninC0(pNode1))) ||
           (Gia_ObjFanin1(pNode0) == Gia_ObjFanin1(pNode1) && (Gia_ObjFaninC1(pNode0) ^ Gia_ObjFaninC1(pNode1)));
}


/**Function*************************************************************

  Synopsis    [Recognizes what nodes are inputs of the EXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjRecognizeExor( Gia_Obj_t * pObj, Gia_Obj_t ** ppFan0, Gia_Obj_t ** ppFan1 )
{
    Gia_Obj_t * p0, * p1;
    assert( !Gia_IsComplement(pObj) );
    if ( !Gia_ObjIsAnd(pObj) )
        return 0;
    assert( Gia_ObjIsAnd(pObj) );
    p0 = Gia_ObjChild0(pObj);
    p1 = Gia_ObjChild1(pObj);
    if ( !Gia_IsComplement(p0) || !Gia_IsComplement(p1) )
        return 0;
    p0 = Gia_Regular(p0);
    p1 = Gia_Regular(p1);
    if ( !Gia_ObjIsAnd(p0) || !Gia_ObjIsAnd(p1) )
        return 0;
    if ( Gia_ObjFanin0(p0) != Gia_ObjFanin0(p1) || Gia_ObjFanin1(p0) != Gia_ObjFanin1(p1) )
        return 0;
    if ( Gia_ObjFaninC0(p0) == Gia_ObjFaninC0(p1) || Gia_ObjFaninC1(p0) == Gia_ObjFaninC1(p1) )
        return 0;
    *ppFan0 = Gia_ObjChild0(p0);
    *ppFan1 = Gia_ObjChild1(p0);
    return 1;
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
Gia_Obj_t * Gia_ObjRecognizeMux( Gia_Obj_t * pNode, Gia_Obj_t ** ppNodeT, Gia_Obj_t ** ppNodeE )
{
    Gia_Obj_t * pNode0, * pNode1;
    assert( !Gia_IsComplement(pNode) );
    assert( Gia_ObjIsMuxType(pNode) );
    // get children
    pNode0 = Gia_ObjFanin0(pNode);
    pNode1 = Gia_ObjFanin1(pNode);

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

  Synopsis    [Allocates a counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Cex_t * Gia_ManAllocCounterExample( int nRegs, int nRealPis, int nFrames )
{
    Gia_Cex_t * pCex;
    int nWords = Aig_BitWordNum( nRegs + nRealPis * nFrames );
    pCex = (Gia_Cex_t *)ABC_ALLOC( char, sizeof(Gia_Cex_t) + sizeof(unsigned) * nWords );
    memset( pCex, 0, sizeof(Gia_Cex_t) + sizeof(unsigned) * nWords );
    pCex->nRegs  = nRegs;
    pCex->nPis   = nRealPis;
    pCex->nBits  = nRegs + nRealPis * nFrames;
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Resimulates the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManVerifyCounterExample( Gia_Man_t * pAig, Gia_Cex_t * p, int fDualOut )
{
    Gia_Obj_t * pObj, * pObjRi, * pObjRo;
    int RetValue, i, k, iBit = 0;
    Gia_ManForEachRo( pAig, pObj, i )
        pObj->fMark0 = Aig_InfoHasBit(p->pData, iBit++);
    for ( i = 0; i <= p->iFrame; i++ )
    {
        Gia_ManForEachPi( pAig, pObj, k )
            pObj->fMark0 = Aig_InfoHasBit(p->pData, iBit++);
        Gia_ManForEachAnd( pAig, pObj, k )
            pObj->fMark0 = (Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj)) & 
                           (Gia_ObjFanin1(pObj)->fMark0 ^ Gia_ObjFaninC1(pObj));
        Gia_ManForEachCo( pAig, pObj, k )
            pObj->fMark0 = Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj);
        Gia_ManForEachRiRo( pAig, pObjRi, pObjRo, k )
            pObjRo->fMark0 = pObjRi->fMark0;
    }
    assert( iBit == p->nBits );
    if ( fDualOut )
        RetValue = Gia_ManPo(pAig, 2*p->iPo)->fMark0 ^ Gia_ManPo(pAig, 2*p->iPo+1)->fMark0;
    else
        RetValue = Gia_ManPo(pAig, p->iPo)->fMark0;
    Gia_ManCleanMark0(pAig);
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Prints out the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintCounterExample( Gia_Cex_t * p )
{
    int i, f, k;
    printf( "Counter-example: iPo = %d  iFrame = %d  nRegs = %d  nPis = %d  nBits = %d\n", 
        p->iPo, p->iFrame, p->nRegs, p->nPis, p->nBits );
    printf( "State    : " );
    for ( k = 0; k < p->nRegs; k++ )
        printf( "%d", Aig_InfoHasBit(p->pData, k) );
    printf( "\n" );
    for ( f = 0; f <= p->iFrame; f++ )
    {
        printf( "Frame %2d : ", f );
        for ( i = 0; i < p->nPis; i++ )
            printf( "%d", Aig_InfoHasBit(p->pData, k++) );
        printf( "\n" );
    }
    assert( k == p->nBits );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


