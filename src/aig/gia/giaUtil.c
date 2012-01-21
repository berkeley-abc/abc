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

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
#define NUMBER1  3716960521u
#define NUMBER2  2174103536u

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a sequence or random numbers.]

  Description []
               
  SideEffects []

  SeeAlso     [http://www.codeproject.com/KB/recipes/SimpleRNG.aspx]

***********************************************************************/
unsigned Gia_ManRandom( int fReset )
{
    static unsigned int m_z = NUMBER1;
    static unsigned int m_w = NUMBER2;
    if ( fReset )
    {
        m_z = NUMBER1;
        m_w = NUMBER2;
    }
    m_z = 36969 * (m_z & 65535) + (m_z >> 16);
    m_w = 18000 * (m_w & 65535) + (m_w >> 16);
    return (m_z << 16) + m_w;
}


/**Function*************************************************************

  Synopsis    [Creates random info for the primary inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManRandomInfo( Vec_Ptr_t * vInfo, int iInputStart, int iWordStart, int iWordStop )
{
    unsigned * pInfo;
    int i, w;
    Vec_PtrForEachEntryStart( unsigned *, vInfo, pInfo, i, iInputStart )
        for ( w = iWordStart; w < iWordStop; w++ )
            pInfo[w] = Gia_ManRandom(0);
}


/**Function*************************************************************

  Synopsis    [Returns the time stamp.]

  Description [The file should be closed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Gia_TimeStamp()
{
    static char Buffer[100];
    char * TimeStamp;
    time_t ltime;
    // get the current time
    time( &ltime );
    TimeStamp = asctime( localtime( &ltime ) );
    TimeStamp[ strlen(TimeStamp) - 1 ] = 0;
    strcpy( Buffer, TimeStamp );
    return Buffer;
}

/**Function*************************************************************

  Synopsis    [Returns the composite name of the file.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Gia_FileNameGenericAppend( char * pBase, char * pSuffix )
{
    static char Buffer[1000];
    char * pDot;
    strcpy( Buffer, pBase );
    if ( (pDot = strrchr( Buffer, '.' )) )
        *pDot = 0;
    strcat( Buffer, pSuffix );
    if ( (pDot = strrchr( Buffer, '\\' )) || (pDot = strrchr( Buffer, '/' )) )
        return pDot+1;
    return Buffer;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManIncrementTravId( Gia_Man_t * p )                     
{ 
    if ( p->pTravIds == NULL )
    {
        p->nTravIdsAlloc = Gia_ManObjNum(p) + 100; 
        p->pTravIds = ABC_CALLOC( int, p->nTravIdsAlloc ); 
        p->nTravIds = 0;  
    }
    while ( p->nTravIdsAlloc < Gia_ManObjNum(p) )
    {
        p->nTravIdsAlloc *= 2;
        p->pTravIds = ABC_REALLOC( int, p->pTravIds, p->nTravIdsAlloc );
        memset( p->pTravIds + p->nTravIdsAlloc/2, 0, sizeof(int) * p->nTravIdsAlloc/2 );
    }
    p->nTravIds++;                                                    
}

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

  Synopsis    [Sets the phase of one object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjSetPhase( Gia_Obj_t * pObj )  
{
    if ( Gia_ObjIsAnd(pObj) )
        pObj->fPhase = (Gia_ObjPhase(Gia_ObjFanin0(pObj)) ^ Gia_ObjFaninC0(pObj)) & 
                       (Gia_ObjPhase(Gia_ObjFanin1(pObj)) ^ Gia_ObjFaninC1(pObj));
    else if ( Gia_ObjIsCo(pObj) )
        pObj->fPhase = (Gia_ObjPhase(Gia_ObjFanin0(pObj)) ^ Gia_ObjFaninC0(pObj));
    else
        pObj->fPhase = 0;
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
        Gia_ObjSetPhase( pObj );
}

/**Function*************************************************************

  Synopsis    [Sets phases of the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSetPhase1( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachCi( p, pObj, i )
        pObj->fPhase = 1;
    Gia_ManForEachObj( p, pObj, i )
        if ( !Gia_ObjIsCi(pObj) )
            Gia_ObjSetPhase( pObj );
}

/**Function*************************************************************

  Synopsis    [Sets phases of the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCleanPhase( Gia_Man_t * p )  
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
        pObj->fPhase = 0;
}

/**Function*************************************************************

  Synopsis    [Prepares copies for the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCleanLevels( Gia_Man_t * p, int Size )
{
    if ( p->vLevels == NULL )
        p->vLevels = Vec_IntAlloc( Size );
    Vec_IntFill( p->vLevels, Size, 0 );
}
/**Function*************************************************************

  Synopsis    [Prepares copies for the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCleanTruth( Gia_Man_t * p )
{
    if ( p->vTruths == NULL )
        p->vTruths = Vec_IntAlloc( Gia_ManObjNum(p) );
    Vec_IntFill( p->vTruths, Gia_ManObjNum(p), -1 );
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
    Gia_ManCleanLevels( p, Gia_ManObjNum(p) );
    p->nLevels = 0;
    Gia_ManForEachObj( p, pObj, i )
        if ( Gia_ObjIsAnd(pObj) )
            Gia_ObjSetAndLevel( p, pObj );
        else if ( Gia_ObjIsCo(pObj) )
        {
            Gia_ObjSetCoLevel( p, pObj );
            p->nLevels = Abc_MaxInt( p->nLevels, Gia_ObjLevel(p, pObj) );
        }
        else
            Gia_ObjSetLevel( p, pObj, 0 );
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

  Synopsis    [Dereferences the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_NodeDeref_rec( Gia_Man_t * p, Gia_Obj_t * pNode )
{
    Gia_Obj_t * pFanin;
    int Counter = 0;
    if ( Gia_ObjIsCi(pNode) )
        return 0;
    assert( Gia_ObjIsAnd(pNode) );
    pFanin = Gia_ObjFanin0(pNode);
    assert( Gia_ObjRefs(p, pFanin) > 0 );
    if ( Gia_ObjRefDec(p, pFanin) == 0 )
        Counter += Gia_NodeDeref_rec( p, pFanin );
    pFanin = Gia_ObjFanin1(pNode);
    assert( Gia_ObjRefs(p, pFanin) > 0 );
    if ( Gia_ObjRefDec(p, pFanin) == 0 )
        Counter += Gia_NodeDeref_rec( p, pFanin );
    return Counter + 1;
}

/**Function*************************************************************

  Synopsis    [References the node's MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_NodeRef_rec( Gia_Man_t * p, Gia_Obj_t * pNode )
{
    Gia_Obj_t * pFanin;
    int Counter = 0;
    if ( Gia_ObjIsCi(pNode) )
        return 0;
    assert( Gia_ObjIsAnd(pNode) );
    pFanin = Gia_ObjFanin0(pNode);
    if ( Gia_ObjRefInc(p, pFanin) == 0 )
        Counter += Gia_NodeRef_rec( p, pFanin );
    pFanin = Gia_ObjFanin1(pNode);
    if ( Gia_ObjRefInc(p, pFanin) == 0 )
        Counter += Gia_NodeRef_rec( p, pFanin );
    return Counter + 1;
}

/**Function*************************************************************

  Synopsis    [Returns the number of internal nodes in the MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_NodeMffcSize( Gia_Man_t * p, Gia_Obj_t * pNode )
{
    int ConeSize1, ConeSize2;
    assert( !Gia_IsComplement(pNode) );
    assert( Gia_ObjIsCand(pNode) );
    ConeSize1 = Gia_NodeDeref_rec( p, pNode );
    ConeSize2 = Gia_NodeRef_rec( p, pNode );
    assert( ConeSize1 == ConeSize2 );
    assert( ConeSize1 >= 0 );
    return ConeSize1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if AIG has choices.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManHasChoices( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, Counter1 = 0, Counter2 = 0;
    int nFailNoRepr = 0;
    int nFailHaveRepr = 0;
    int nChoiceNodes = 0;
    int nChoices = 0;
    if ( p->pReprs == NULL || p->pNexts == NULL )
        return 0;
    // check if there are any representatives
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( Gia_ObjReprObj( p, Gia_ObjId(p, pObj) ) )
        {
//            printf( "%d ", i );
            Counter1++;
        }
//        if ( Gia_ObjNext( p, Gia_ObjId(p, pObj) ) )
//            Counter2++;
    }
//    printf( "\n" );
    Gia_ManForEachObj( p, pObj, i )
    {
//        if ( Gia_ObjReprObj( p, Gia_ObjId(p, pObj) ) )
//            Counter1++;
        if ( Gia_ObjNext( p, Gia_ObjId(p, pObj) ) )
        {
//            printf( "%d ", i );
            Counter2++;
        }
    }
//    printf( "\n" );
    if ( Counter1 == 0 )
    {
        printf( "Warning: AIG has repr data-strucure but not reprs.\n" );
        return 0;
    }
    printf( "%d nodes have reprs.\n", Counter1 );
    printf( "%d nodes have nexts.\n", Counter2 );
    // check if there are any internal nodes without fanout
    // make sure all nodes without fanout have representatives
    // make sure all nodes with fanout have no representatives
    ABC_FREE( p->pRefs );
    Gia_ManCreateRefs( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( Gia_ObjRefs(p, pObj) == 0 )
        {
            if ( Gia_ObjReprObj( p, Gia_ObjId(p, pObj) ) == NULL )
                nFailNoRepr++;
            else
                nChoices++;
        }
        else
        {
            if ( Gia_ObjReprObj( p, Gia_ObjId(p, pObj) ) != NULL )
                nFailHaveRepr++;
            if ( Gia_ObjNextObj( p, Gia_ObjId(p, pObj) ) != NULL )
                nChoiceNodes++;
        }
        if ( Gia_ObjReprObj( p, i ) )
            assert( Gia_ObjRepr(p, i) < i );
    }
    if ( nChoices == 0 )
        return 0;
    if ( nFailNoRepr )
    {
        printf( "Gia_ManHasChoices(): Error: %d internal nodes have no fanout and no repr.\n", nFailNoRepr );
//        return 0;
    }
    if ( nFailHaveRepr )
    {
        printf( "Gia_ManHasChoices(): Error: %d internal nodes have both fanout and repr.\n", nFailHaveRepr );
//        return 0;
    }
//    printf( "Gia_ManHasChoices(): AIG has %d choice nodes with %d choices.\n", nChoiceNodes, nChoices );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if AIG has dangling nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManHasDangling( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, Counter = 0;
    Gia_ManForEachObj( p, pObj, i )
    {
        pObj->fMark0 = 0;
        if ( Gia_ObjIsAnd(pObj) )
        {
            Gia_ObjFanin0(pObj)->fMark0 = 1;
            Gia_ObjFanin1(pObj)->fMark0 = 1;
        }
        else if ( Gia_ObjIsCo(pObj) )
            Gia_ObjFanin0(pObj)->fMark0 = 1;
    }
    Gia_ManForEachAnd( p, pObj, i )
        Counter += !pObj->fMark0;
    Gia_ManCleanMark0( p );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if AIG has dangling nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManGetDangling( Gia_Man_t * p )
{
    Vec_Int_t * vDangles;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
    {
        pObj->fMark0 = 0;
        if ( Gia_ObjIsAnd(pObj) )
        {
            Gia_ObjFanin0(pObj)->fMark0 = 1;
            Gia_ObjFanin1(pObj)->fMark0 = 1;
        }
        else if ( Gia_ObjIsCo(pObj) )
            Gia_ObjFanin0(pObj)->fMark0 = 1;
    }
    vDangles = Vec_IntAlloc( 100 );
    Gia_ManForEachAnd( p, pObj, i )
        if ( !pObj->fMark0 )
            Vec_IntPush( vDangles, i );
    Gia_ManCleanMark0( p );
    return vDangles;
}
/**Function*************************************************************

  Synopsis    [Verbose printing of the AIG node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ObjPrint( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( pObj == NULL )
    {
        printf( "Object is NULL." );
        return;
    }
    if ( Gia_IsComplement(pObj) )
    {
        printf( "Compl " );
        pObj = Gia_Not(pObj);
    }
    assert( !Gia_IsComplement(pObj) );
    printf( "Node %4d : ", Gia_ObjId(p, pObj) );
    if ( Gia_ObjIsConst0(pObj) )
        printf( "constant 0" );
    else if ( Gia_ObjIsPi(p, pObj) )
        printf( "PI" );
    else if ( Gia_ObjIsPo(p, pObj) )
        printf( "PO( %4d%s )", Gia_ObjFaninId0p(p, pObj), (Gia_ObjFaninC0(pObj)? "\'" : " ") );
    else if ( Gia_ObjIsCi(pObj) )
        printf( "RI" );
    else if ( Gia_ObjIsCo(pObj) )
        printf( "RO( %4d%s )", Gia_ObjFaninId0p(p, pObj), (Gia_ObjFaninC0(pObj)? "\'" : " ") );
//    else if ( Gia_ObjIsBuf(pObj) )
//        printf( "BUF( %d%s )", Gia_ObjFaninId0p(p, pObj), (Gia_ObjFaninC0(pObj)? "\'" : " ") );
    else
        printf( "AND( %4d%s, %4d%s )", 
            Gia_ObjFaninId0p(p, pObj), (Gia_ObjFaninC0(pObj)? "\'" : " "), 
            Gia_ObjFaninId1p(p, pObj), (Gia_ObjFaninC1(pObj)? "\'" : " ") );
    if ( p->pRefs )
        printf( " (refs = %3d)", Gia_ObjRefs(p, pObj) );
    printf( "\n" );
/*
    if ( p->pRefs )
    {
        Gia_Obj_t * pFanout;
        int i;
        int iFan = -1; // Suppress "might be used uninitialized"
        printf( "\nFanouts:\n" );
        Gia_ObjForEachFanout( p, pObj, pFanout, iFan, i )
        {
            printf( "    " );
            printf( "Node %4d : ", Gia_ObjId(pFanout) );
            if ( Gia_ObjIsPo(pFanout) )
                printf( "PO( %4d%s )", Gia_ObjFanin0(pFanout)->Id, (Gia_ObjFaninC0(pFanout)? "\'" : " ") );
            else if ( Gia_ObjIsBuf(pFanout) )
                printf( "BUF( %d%s )", Gia_ObjFanin0(pFanout)->Id, (Gia_ObjFaninC0(pFanout)? "\'" : " ") );
            else
                printf( "AND( %4d%s, %4d%s )", 
                    Gia_ObjFanin0(pFanout)->Id, (Gia_ObjFaninC0(pFanout)? "\'" : " "), 
                    Gia_ObjFanin1(pFanout)->Id, (Gia_ObjFaninC1(pFanout)? "\'" : " ") );
            printf( "\n" );
        }
        return;
    }
*/
}

/**Function*************************************************************

  Synopsis    [Resimulates the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManVerifyCex( Gia_Man_t * pAig, Abc_Cex_t * p, int fDualOut )
{
    Gia_Obj_t * pObj, * pObjRi, * pObjRo;
    int RetValue, i, k, iBit = 0;
    Gia_ManCleanMark0(pAig);
    Gia_ManForEachRo( pAig, pObj, i )
        pObj->fMark0 = Abc_InfoHasBit(p->pData, iBit++);
    for ( i = 0; i <= p->iFrame; i++ )
    {
        Gia_ManForEachPi( pAig, pObj, k )
            pObj->fMark0 = Abc_InfoHasBit(p->pData, iBit++);
        Gia_ManForEachAnd( pAig, pObj, k )
            pObj->fMark0 = (Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj)) & 
                           (Gia_ObjFanin1(pObj)->fMark0 ^ Gia_ObjFaninC1(pObj));
        Gia_ManForEachCo( pAig, pObj, k )
            pObj->fMark0 = Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj);
        if ( i == p->iFrame )
            break;
        Gia_ManForEachRiRo( pAig, pObjRi, pObjRo, k )
        {
            pObjRo->fMark0 = pObjRi->fMark0;
        }
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

  Synopsis    [Resimulates the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManFindFailedPoCex( Gia_Man_t * pAig, Abc_Cex_t * p, int nOutputs )
{
    Gia_Obj_t * pObj, * pObjRi, * pObjRo;
    int RetValue, i, k, iBit = 0;
    assert( Gia_ManPiNum(pAig) == p->nPis );
    Gia_ManCleanMark0(pAig);
//    Gia_ManForEachRo( pAig, pObj, i )
//       pObj->fMark0 = Abc_InfoHasBit(p->pData, iBit++);
    iBit = p->nRegs;
    for ( i = 0; i <= p->iFrame; i++ )
    {
        Gia_ManForEachPi( pAig, pObj, k )
            pObj->fMark0 = Abc_InfoHasBit(p->pData, iBit++);
        Gia_ManForEachAnd( pAig, pObj, k )
            pObj->fMark0 = (Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj)) & 
                           (Gia_ObjFanin1(pObj)->fMark0 ^ Gia_ObjFaninC1(pObj));
        Gia_ManForEachCo( pAig, pObj, k )
            pObj->fMark0 = Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj);
        Gia_ManForEachRiRo( pAig, pObjRi, pObjRo, k )
            pObjRo->fMark0 = pObjRi->fMark0;
    }
    assert( iBit == p->nBits );
    // figure out the number of failed output
    RetValue = -1;
//    for ( i = Gia_ManPoNum(pAig) - 1; i >= nOutputs; i-- )
    for ( i = nOutputs; i < Gia_ManPoNum(pAig); i++ )
    {
        if ( Gia_ManPo(pAig, i)->fMark0 )
        {
            RetValue = i;
            break;
        }
    }
    Gia_ManCleanMark0(pAig);
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Complements the constraint outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManInvertConstraints( Gia_Man_t * pAig )
{
    Gia_Obj_t * pObj;
    int i;
    if ( Gia_ManConstrNum(pAig) == 0 )
        return;
    Gia_ManForEachPo( pAig, pObj, i )
    {
        if ( i >= Gia_ManPoNum(pAig) - Gia_ManConstrNum(pAig) )
            Gia_ObjFlipFaninC0( pObj );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

