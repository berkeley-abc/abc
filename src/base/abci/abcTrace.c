/**CFile****************************************************************

  FileName    [abcHistory.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcHistory.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
#define ABC_SIM_VARS   16    // the max number of variables in the cone
#define ABC_SIM_OBJS  200    // the max number of objects in the cone

typedef struct Abc_HMan_t_ Abc_HMan_t;
typedef struct Abc_HObj_t_ Abc_HObj_t;
typedef struct Abc_HNum_t_ Abc_HNum_t;

struct Abc_HNum_t_
{
    unsigned         fCompl :  1;  // set to 1 if the node is complemented
    unsigned         NtkId  :  6;  // the network ID 
    unsigned         ObjId  : 24;  // the node ID 
};

struct Abc_HObj_t_
{
    // object info
    unsigned         fProof :  1;  // set to 1 if the node is proved
    unsigned         fPhase :  1;  // set to 1 if the node's phase differs from Old
    unsigned         fPi    :  1;  // the node is a PI
    unsigned         fPo    :  1;  // the node is a PO
    unsigned         fConst :  1;  // the node is a constant
    unsigned         fVisited: 1;  // the flag shows if the node is visited
    unsigned         NtkId  : 10;  // the network ID
    unsigned         Num    : 16;  // a temporary number
    // history record
    Abc_HNum_t       Fan0;         // immediate fanin
    Abc_HNum_t       Fan1;         // immediate fanin
    Abc_HNum_t       Proto;        // old node if present
//    Abc_HNum_t       Equ;          // equiv node if present
};

struct Abc_HMan_t_
{
    // storage for history information
    Vec_Vec_t *      vNtks;        // the history nodes belonging to each network
    Vec_Int_t *      vProof;       // flags showing if the network is proved
    // storage for simulation info
    int              nVarsMax;     // the max number of cone leaves
    int              nObjsMax;     // the max number of cone nodes
    Vec_Ptr_t *      vObjs;        // the cone nodes
    int              nBits;        // the number of simulation bits
    int              nWords;       // the number of unsigneds for siminfo
    int              nWordsCur;    // the current number of words
    Vec_Ptr_t *      vSims;        // simulation info
    unsigned *       pInfo;        // pointer to simulation info
    // other info
    Vec_Ptr_t *      vCone0;
    Vec_Ptr_t *      vCone1;
    // memory manager
    Extra_MmFixed_t* pMmObj;       // memory manager for objects
};

static Abc_HMan_t * s_pHMan = NULL;

static inline int          Abc_HObjProof( Abc_HObj_t * p )   { return p->fProof; }
static inline int          Abc_HObjPhase( Abc_HObj_t * p )   { return p->fPhase; }
static inline int          Abc_HObjPi   ( Abc_HObj_t * p )   { return p->fPi;    }
static inline int          Abc_HObjPo   ( Abc_HObj_t * p )   { return p->fPo;    }
static inline int          Abc_HObjConst( Abc_HObj_t * p )   { return p->fConst; }
static inline int          Abc_HObjNtkId( Abc_HObj_t * p )   { return p->NtkId;  }
static inline int          Abc_HObjNum  ( Abc_HObj_t * p )   { return p->Num;    }
static inline Abc_HObj_t * Abc_HObjFanin0( Abc_HObj_t * p )  { return !p->Fan0.NtkId ? NULL : Vec_PtrEntry( Vec_VecEntry(s_pHMan->vNtks, p->Fan0.NtkId),  p->Fan0.ObjId ); }
static inline Abc_HObj_t * Abc_HObjFanin1( Abc_HObj_t * p )  { return !p->Fan1.NtkId ? NULL : Vec_PtrEntry( Vec_VecEntry(s_pHMan->vNtks, p->Fan1.NtkId),  p->Fan1.ObjId ); }
static inline Abc_HObj_t * Abc_HObjProto ( Abc_HObj_t * p )  { return !p->Proto.NtkId ? NULL : Vec_PtrEntry( Vec_VecEntry(s_pHMan->vNtks, p->Proto.NtkId), p->Proto.ObjId ); }
static inline int          Abc_HObjFaninC0( Abc_HObj_t * p ) { return p->Fan0.fCompl; }
static inline int          Abc_HObjFaninC1( Abc_HObj_t * p ) { return p->Fan1.fCompl; }

static inline Abc_HObj_t * Abc_ObjHObj( Abc_Obj_t * p )      { return Vec_PtrEntry( Vec_VecEntry(s_pHMan->vNtks, p->pNtk->Id),  p->Id ); }

static int Abc_HManVerifyPair( int NtkIdOld, int NtkIdNew );
static int Abc_HManVerifyNodes_rec( Abc_HObj_t * pHOld, Abc_HObj_t * pHNew );

static Vec_Ptr_t * Abc_HManCollectLeaves( Abc_HObj_t * pHNew );
static Vec_Ptr_t * Abc_HManCollectCone( Abc_HObj_t * pHOld, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vCone );
static int Abc_HManSimulate( Vec_Ptr_t * vCone0, Vec_Ptr_t * vCone1, int nLeaves, int * pPhase );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManStart()
{
    Abc_HMan_t * p;
    unsigned * pData;
    int i, k;
    assert( s_pHMan == NULL );
    assert( sizeof(unsigned) == 4 );
    // allocate manager
    p = ALLOC( Abc_HMan_t, 1 );
    memset( p, 0, sizeof(Abc_HMan_t) );
    // allocate storage for all nodes
    p->vNtks  = Vec_VecStart( 1 );
    p->vProof = Vec_IntStart( 1 );
    // allocate temporary storage for objects
    p->nVarsMax = ABC_SIM_VARS;
    p->nObjsMax = ABC_SIM_OBJS;
    p->vObjs    = Vec_PtrAlloc( p->nObjsMax );
    // allocate simulation info
    p->nBits    = (1 << p->nVarsMax);
    p->nWords   = (p->nBits <= 32)? 1 : (p->nBits / 32);
    p->pInfo    = ALLOC( unsigned, p->nWords * p->nObjsMax );
    memset( p->pInfo, 0, sizeof(unsigned) * p->nWords * p->nVarsMax );
    p->vSims    = Vec_PtrAlloc( p->nObjsMax );
    for ( i = 0; i < p->nObjsMax; i++ )
        Vec_PtrPush( p->vSims, p->pInfo + i * p->nWords );
    // set elementary truth tables
    for ( k = 0; k < p->nVarsMax; k++ )
    {
        pData = p->vSims->pArray[k];
        for ( i = 0; i < p->nBits; i++ )
            if ( i & (1 << k) )
                pData[i/32] |= (1 << (i%32));
    }
    // allocate storage for the nodes
    p->pMmObj = Extra_MmFixedStart( sizeof(Abc_HObj_t) );
    p->vCone0 = Vec_PtrAlloc( p->nObjsMax );
    p->vCone1 = Vec_PtrAlloc( p->nObjsMax );
    s_pHMan = p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManStop()
{
    assert( s_pHMan != NULL );
    Extra_MmFixedStop( s_pHMan->pMmObj, 0 );
    Vec_PtrFree( s_pHMan->vObjs );
    Vec_PtrFree( s_pHMan->vSims );
    Vec_VecFree( s_pHMan->vNtks );
    Vec_IntFree( s_pHMan->vProof );
    Vec_PtrFree( s_pHMan->vCone0 );
    Vec_PtrFree( s_pHMan->vCone1 );
    free( s_pHMan->pInfo );
    free( s_pHMan );
    s_pHMan = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_HManIsRunning()
{
    return s_pHMan != NULL;
}

/**Function*************************************************************

  Synopsis    [Called when a new network is created.]

  Description [Returns the new ID for the network.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_HManGetNewNtkId()
{
    if ( s_pHMan == NULL )
        return 0;
    return Vec_VecSize( s_pHMan->vNtks );  // what if the new network has no nodes?
}

/**Function*************************************************************

  Synopsis    [Called when the object is created.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManAddObj( Abc_Obj_t * pObj )
{
    Abc_HObj_t * pHObj;
    if ( s_pHMan == NULL )
        return;
    pHObj = (Abc_HObj_t *)Extra_MmFixedEntryFetch( s_pHMan->pMmObj );
    memset( pHObj, 0, sizeof(Abc_HObj_t) );
    // set the object type
    pHObj->NtkId = pObj->pNtk->Id;
    if ( Abc_ObjIsCi(pObj) )
        pHObj->fPi = 1;
    else if ( Abc_ObjIsCo(pObj) )
        pHObj->fPo = 1;
    Vec_VecPush( s_pHMan->vNtks, pObj->pNtk->Id, pHObj );
    // set the proof parameter for the network
    if ( Vec_IntSize( s_pHMan->vProof ) == pObj->pNtk->Id )
        Vec_IntPush( s_pHMan->vProof, 0 );
}

/**Function*************************************************************

  Synopsis    [Called when the fanin is added to the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManAddFanin( Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    Abc_HObj_t * pHObj;
    int fCompl;
    if ( s_pHMan == NULL )
        return;
    // take off the complemented attribute
    assert( !Abc_ObjIsComplement(pObj) );
    fCompl = Abc_ObjIsComplement(pFanin);
    pFanin = Abc_ObjRegular(pFanin);
    // add the fanin
    assert( pObj->pNtk == pFanin->pNtk );
    pHObj = Abc_ObjHObj(pObj);
    if ( pHObj->Fan0.NtkId == 0 )
    {
        pHObj->Fan0.NtkId = pFanin->pNtk->Id;
        pHObj->Fan0.ObjId = pFanin->Id;
        pHObj->Fan0.fCompl = fCompl;
    }
    else if ( pHObj->Fan1.NtkId == 0 )
    {
        pHObj->Fan1.NtkId = pFanin->pNtk->Id;
        pHObj->Fan1.ObjId = pFanin->Id;
        pHObj->Fan1.fCompl = fCompl;
    }
    else assert( 0 );
}

/**Function*************************************************************

  Synopsis    [Called when the fanin's input should be complemented.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManXorFaninC( Abc_Obj_t * pObj, int iFanin )
{
    Abc_HObj_t * pHObj;
    if ( s_pHMan == NULL )
        return;
    assert( iFanin < 2 );
    pHObj = Abc_ObjHObj(pObj);
    if ( iFanin == 0 )
        pHObj->Fan0.fCompl ^= 1;
    else if ( iFanin == 1 )
        pHObj->Fan1.fCompl ^= 1;
}

/**Function*************************************************************

  Synopsis    [Called when the fanin is added to the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManRemoveFanins( Abc_Obj_t * pObj )
{
    Abc_HObj_t * pHObj;
    if ( s_pHMan == NULL )
        return;
    assert( !Abc_ObjIsComplement(pObj) );
    pHObj = Abc_ObjHObj(pObj);
    pHObj->Fan0.NtkId = 0;
    pHObj->Fan0.ObjId = 0;
    pHObj->Fan0.fCompl = 0;
    pHObj->Fan1.NtkId = 0;
    pHObj->Fan1.ObjId = 0;
    pHObj->Fan1.fCompl = 0;
}

/**Function*************************************************************

  Synopsis    [Called when a new prototype of the old object is set.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManAddProto( Abc_Obj_t * pObj, Abc_Obj_t * pProto )
{
    Abc_HObj_t * pHObj;
    if ( s_pHMan == NULL )
        return;
    // ignore polarity for now
    pObj   = Abc_ObjRegular(pObj);
    pProto = Abc_ObjRegular(pProto);
    // set the prototype
    assert( pObj->pNtk != pProto->pNtk );
    if ( pObj->pNtk->Id == 0 )
        return;
    pHObj = Abc_ObjHObj(pObj);
    pHObj->Proto.NtkId = pProto->pNtk->Id;
    pHObj->Proto.ObjId = pProto->Id;
}

/**Function*************************************************************

  Synopsis    [Called when an equivalent node is created.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManMapAddEqu( Abc_Obj_t * pObj, Abc_Obj_t * pEqu )
{
/*
    Abc_HObj_t * pHObj;
    if ( s_pHMan == NULL )
        return;
    // ignore polarity for now
    pObj  = Abc_ObjRegular(pObj);
    pEqu  = Abc_ObjRegular(pEqu);
    // set the equivalent node
    assert( pObj->pNtk == pEqu->pNtk );
    pHObj = Abc_ObjHObj(pObj);
    Abc_ObjHObj(pObj)->Equ.NtkId = pEqu->pNtk->Id;
    Abc_ObjHObj(pObj)->Equ.ObjId = pEqu->Id;
*/
}



/**Function*************************************************************

  Synopsis    [Starts the verification procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_HManPopulate( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;
    if ( !Abc_NtkIsStrash(pNtk) )
        return 0;
    // allocate the network ID
    pNtk->Id = Abc_HManGetNewNtkId();
    assert( pNtk->Id == 1 );
    // create the objects
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        Abc_HManAddObj( pObj );
        if ( Abc_ObjFaninNum(pObj) > 0 )
            Abc_HManAddFanin( pObj, Abc_ObjChild0(pObj) );
        if ( Abc_ObjFaninNum(pObj) > 1 )
            Abc_HManAddFanin( pObj, Abc_ObjChild1(pObj) );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [The main verification procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_HManVerify( int NtkIdOld, int NtkIdNew )
{
    int i;
    // prove the equality pairwise
    for ( i = NtkIdOld; i < NtkIdNew; i++ )
    {
        if ( Vec_IntEntry(s_pHMan->vProof, i) )
            continue;
        if ( !Abc_HManVerifyPair( i, i+1 ) )
            return 0;
        Vec_IntWriteEntry( s_pHMan->vProof, i, 1 );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Verifies two networks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_HManVerifyPair( int NtkIdOld, int NtkIdNew )
{
    Vec_Ptr_t * vNtkNew, * vNtkOld, * vPosNew;
    Abc_HObj_t * pHObj;
    int i;
    // get hold of the network nodes
    vNtkNew = Vec_VecEntry( s_pHMan->vNtks, NtkIdNew );
    vNtkOld = Vec_VecEntry( s_pHMan->vNtks, NtkIdOld );
    Vec_PtrForEachEntry( vNtkNew, pHObj, i )
        pHObj->fVisited = 0;
    Vec_PtrForEachEntry( vNtkOld, pHObj, i )
        pHObj->fVisited = 0;
    // collect new POs
    vPosNew = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( vNtkNew, pHObj, i )
        if ( pHObj->fPo )
            Vec_PtrPush( vPosNew, pHObj );
    // prove them recursively (assuming PO ordering is the same)
    Vec_PtrForEachEntry( vPosNew, pHObj, i )
    {
        if ( Abc_HObjProto(pHObj) == NULL )
        {
            printf( "History: PO %d has no prototype\n", i ); 
            return 0;
        }
        if ( !Abc_HManVerifyNodes_rec( Abc_HObjProto(pHObj), pHObj ) )
        {
            printf( "History: Verification failed for outputs of PO pair number %d\n", i ); 
            return 0;
        }
    }
    printf( "History: Verification succeeded.\n" ); 
    return 1;
}

/**Function*************************************************************

  Synopsis    [Recursively verifies two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_HManVerifyNodes_rec( Abc_HObj_t * pHOld, Abc_HObj_t * pHNew )
{
    Vec_Ptr_t * vLeaves;
    Abc_HObj_t * pHObj, * pHPro0, * pHPro1;
    int i, fPhase;

    assert( Abc_HObjProto(pHNew) == pHOld );
    if ( pHNew->fProof )
        return 1;
    pHNew->fProof = 1;
    // consider simple cases
    if ( pHNew->fPi || pHNew->fConst )
        return 1;
    if ( pHNew->fPo )
    {
        if ( !Abc_HManVerifyNodes_rec( Abc_HObjFanin0(pHOld), Abc_HObjFanin0(pHNew) ) )
            return 0;
        if ( (Abc_HObjFaninC0(pHOld) ^ Abc_HObjFaninC0(pHNew)) != (int)pHNew->fPhase )
        {
            printf( "History: Phase of PO nodes does not agree.\n" );
            return 0;
        }
        return 1;
    }
    // the elementary node
    pHPro0 = Abc_HObjProto( Abc_HObjFanin0(pHNew) );
    pHPro1 = Abc_HObjProto( Abc_HObjFanin1(pHNew) );
    if ( pHPro0 && pHPro1 )
    {
        if ( !Abc_HManVerifyNodes_rec( pHPro0, Abc_HObjFanin0(pHNew) ) )
            return 0;
        if ( !Abc_HManVerifyNodes_rec( pHPro1, Abc_HObjFanin1(pHNew) ) )
            return 0;
        if ( Abc_HObjFanin0(pHOld) != pHPro0 || Abc_HObjFanin1(pHOld) != pHPro1 )
        {
            printf( "History: Internal node does not match.\n" );
            return 0;
        }
        if ( Abc_HObjFaninC0(pHOld) != Abc_HObjFaninC0(pHNew) ||
             Abc_HObjFaninC1(pHOld) != Abc_HObjFaninC1(pHNew) )
        {
            printf( "History: Phase of internal node does not match.\n" );
            return 0;
        }
        return 1;
    }
    // collect the leaves
    vLeaves = Abc_HManCollectLeaves( pHNew );
    if ( Vec_PtrSize(vLeaves) > 16 )
    {
        printf( "History: The bound on the number of inputs is exceeded.\n" );
        return 0;
    }
    s_pHMan->nWordsCur = ((1 << Vec_PtrSize(vLeaves)) <= 32)? 1 : ((1 << Vec_PtrSize(vLeaves)) / 32);
    // prove recursively
    Vec_PtrForEachEntry( vLeaves, pHObj, i )
        if ( !Abc_HManVerifyNodes_rec( Abc_HObjProto(pHObj), pHObj ) )
        {
            Vec_PtrFree( vLeaves );
            return 0;
        }
    // get the first node
    Abc_HManCollectCone( pHNew, vLeaves, s_pHMan->vCone1 );
    if ( Vec_PtrSize(s_pHMan->vCone1) > ABC_SIM_OBJS - ABC_SIM_VARS - 1 )
    {
        printf( "History: The bound on the number of cone nodes is exceeded.\n" );
        return 0;
    }
    // get the second cone
    Vec_PtrForEachEntry( vLeaves, pHObj, i )
        Vec_PtrWriteEntry( vLeaves, i, Abc_HObjProto(pHObj) );
    Abc_HManCollectCone( pHOld, vLeaves, s_pHMan->vCone0 );
    if ( Vec_PtrSize(s_pHMan->vCone0) > ABC_SIM_OBJS - ABC_SIM_VARS - 1 )
    {
        printf( "History: The bound on the number of cone nodes is exceeded.\n" );
        return 0;
    }
    // compare the truth tables
    if ( !Abc_HManSimulate( s_pHMan->vCone0, s_pHMan->vCone1, Vec_PtrSize(vLeaves), &fPhase ) )
    {
        Vec_PtrFree( vLeaves );
        printf( "History: Verification failed at an internal node.\n" );
        return 0;
    }
    printf( "Succeeded.\n" );
    pHNew->fPhase = fPhase;
    Vec_PtrFree( vLeaves );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Finds the leaves of the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManCollectLeaves_rec( Abc_HObj_t * pHNew, Vec_Ptr_t * vLeaves )
{
    Abc_HObj_t * pHPro;
    if ( pHPro = Abc_HObjProto( pHNew ) )
    {
        Vec_PtrPushUnique( vLeaves, pHNew );
        return;
    }
    assert( !pHNew->fPi && !pHNew->fPo && !pHNew->fConst );
    Abc_HManCollectLeaves_rec( Abc_HObjFanin0(pHNew), vLeaves );
    Abc_HManCollectLeaves_rec( Abc_HObjFanin1(pHNew), vLeaves );
}

/**Function*************************************************************

  Synopsis    [Finds the leaves of the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_HManCollectLeaves( Abc_HObj_t * pHNew )
{
    Vec_Ptr_t * vLeaves;
    vLeaves = Vec_PtrAlloc( 100 );
    Abc_HManCollectLeaves_rec( Abc_HObjFanin0(pHNew), vLeaves );
    Abc_HManCollectLeaves_rec( Abc_HObjFanin1(pHNew), vLeaves );
    return vLeaves;
}


/**Function*************************************************************

  Synopsis    [Collects the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManCollectCone_rec( Abc_HObj_t * pHObj, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vCone )
{
    if ( pHObj->fVisited )
        return;
    pHObj->fVisited = 1;
    assert( !pHObj->fPi && !pHObj->fPo && !pHObj->fConst );
    Abc_HManCollectCone_rec( Abc_HObjFanin0(pHObj), vLeaves, vCone );
    Abc_HManCollectCone_rec( Abc_HObjFanin1(pHObj), vLeaves, vCone );
    pHObj->Num = Vec_PtrSize(vCone);
    Vec_PtrPush( vCone, pHObj );
}

/**Function*************************************************************

  Synopsis    [Collects the TFI cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_HManCollectCone( Abc_HObj_t * pHRoot, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vCone )
{
    Abc_HObj_t * pHObj;
    int i;
    Vec_PtrClear( vCone );
    Vec_PtrForEachEntry( vLeaves, pHObj, i )
    {
        pHObj->fVisited = 1;
        pHObj->Num = Vec_PtrSize(vCone);
        Vec_PtrPush( vCone, pHObj );
    }
    Abc_HManCollectCone_rec( Abc_HObjFanin0(pHRoot), vLeaves, vCone );
    Abc_HManCollectCone_rec( Abc_HObjFanin1(pHRoot), vLeaves, vCone );
    return vCone;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_HManSimulateOne( Vec_Ptr_t * vCone, int nLeaves, int fUsePhase )
{
    Abc_HObj_t * pHObj, * pHFan0, * pHFan1;
    unsigned * puData0, * puData1, * puData;
    int k, i, fComp0, fComp1;
    // set the leaves
    Vec_PtrForEachEntryStart( vCone, pHObj, i, nLeaves )
    {
        pHFan0  = Abc_HObjFanin0(pHObj);
        pHFan1  = Abc_HObjFanin1(pHObj);
        // consider the case of interver or buffer
        if ( pHFan1 == NULL )
        {
            puData  = Vec_PtrEntry(s_pHMan->vSims, ABC_SIM_VARS+i-nLeaves);
            puData0 = ((int)pHFan0->Num < nLeaves)? Vec_PtrEntry(s_pHMan->vSims, pHFan0->Num) : 
                                                    Vec_PtrEntry(s_pHMan->vSims, ABC_SIM_VARS+pHFan0->Num-nLeaves);
            fComp0 = Abc_HObjFaninC0(pHObj) ^ (fUsePhase && (int)pHFan0->Num < nLeaves && pHFan0->fPhase);
            if ( fComp0 )
                for ( k = 0; k < s_pHMan->nWordsCur; k++ )
                    puData[k] = ~puData0[k];
            else
                for ( k = 0; k < s_pHMan->nWordsCur; k++ )
                    puData[k] = puData0[k];
            continue;
        }
        // get the pointers to simulation data
        puData  = Vec_PtrEntry(s_pHMan->vSims, ABC_SIM_VARS+i-nLeaves);
        puData0 = ((int)pHFan0->Num < nLeaves)? Vec_PtrEntry(s_pHMan->vSims, pHFan0->Num) : 
                                                Vec_PtrEntry(s_pHMan->vSims, ABC_SIM_VARS+pHFan0->Num-nLeaves);
        puData1 = ((int)pHFan1->Num < nLeaves)? Vec_PtrEntry(s_pHMan->vSims, pHFan1->Num) : 
                                                Vec_PtrEntry(s_pHMan->vSims, ABC_SIM_VARS+pHFan1->Num-nLeaves);
        // here are the phases
        fComp0 = Abc_HObjFaninC0(pHObj) ^ (fUsePhase && (int)pHFan0->Num < nLeaves && pHFan0->fPhase);
        fComp1 = Abc_HObjFaninC1(pHObj) ^ (fUsePhase && (int)pHFan1->Num < nLeaves && pHFan1->fPhase);
        // simulate
        if ( fComp0 && fComp1 )
            for ( k = 0; k < s_pHMan->nWordsCur; k++ )
                puData[k] = ~puData0[k] & ~puData1[k];
        else if ( fComp0 )
            for ( k = 0; k < s_pHMan->nWordsCur; k++ )
                puData[k] = ~puData0[k] & puData1[k];
        else if ( fComp1 )
            for ( k = 0; k < s_pHMan->nWordsCur; k++ )
                puData[k] = puData0[k] & ~puData1[k];
        else 
            for ( k = 0; k < s_pHMan->nWordsCur; k++ )
                puData[k] = puData0[k] & puData1[k];
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_HManSimulate( Vec_Ptr_t * vCone0, Vec_Ptr_t * vCone1, int nLeaves, int * pPhase )
{
    unsigned * pDataTop, * pDataLast;
    int w;
    // simulate the first one
    Abc_HManSimulateOne( vCone0, nLeaves, 0 );
    // save the last simulation value
    pDataTop = Vec_PtrEntry( s_pHMan->vSims, ((Abc_HObj_t *)Vec_PtrEntryLast(vCone0))->Num );
    pDataLast = Vec_PtrEntry( s_pHMan->vSims, Vec_PtrSize(s_pHMan->vSims)-1 );
    for ( w = 0; w < s_pHMan->nWordsCur; w++ )
        pDataLast[w] = pDataTop[w];
    // simulate the other one
    Abc_HManSimulateOne( vCone1, nLeaves, 1 );
    // complement the output if needed
    pDataTop = Vec_PtrEntry( s_pHMan->vSims, ((Abc_HObj_t *)Vec_PtrEntryLast(vCone1))->Num );
    // mask unused bits
    if ( nLeaves < 5 )
    {
        pDataTop[0]  &= ((~((unsigned)0)) >> (32-(1<<nLeaves)));
        pDataLast[0] &= ((~((unsigned)0)) >> (32-(1<<nLeaves)));
    }
    if ( *pPhase = ((pDataTop[0] & 1) != (pDataLast[0] & 1)) )
        for ( w = 0; w < s_pHMan->nWordsCur; w++ )
            pDataTop[w] = ~pDataTop[w];
    // compare
    for ( w = 0; w < s_pHMan->nWordsCur; w++ )
        if ( pDataLast[w] != pDataTop[w] )
            return 0;
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


