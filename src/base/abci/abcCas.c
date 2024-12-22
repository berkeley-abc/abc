/**CFile****************************************************************

  FileName    [abcCas.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Decomposition of shared BDDs into LUT cascade.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcCas.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "bool/kit/kit.h"
#include "aig/miniaig/miniaig.h"

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#include "bdd/extrab/extraLutCas.h"
#endif

ABC_NAMESPACE_IMPL_START


/* 
    This LUT cascade synthesis algorithm is described in the paper:
    A. Mishchenko and T. Sasao, "Encoding of Boolean functions and its 
    application to LUT cascade synthesis", Proc. IWLS '02, pp. 115-120.
    http://www.eecs.berkeley.edu/~alanmi/publications/2002/iwls02_enc.pdf
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_CUDD

extern int Abc_CascadeExperiment( char * pFileGeneric, DdManager * dd, DdNode ** pOutputs, int nInputs, int nOutputs, int nLutSize, int fCheck, int fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkCascade( Abc_Ntk_t * pNtk, int nLutSize, int fCheck, int fVerbose )
{
    DdManager * dd;
    DdNode ** ppOutputs;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode;
    char * pFileGeneric;
    int fBddSizeMax = 500000;
    int i, fReorder = 1;
    abctime clk = Abc_Clock();

    assert( Abc_NtkIsStrash(pNtk) );
    // compute the global BDDs
    if ( Abc_NtkBuildGlobalBdds(pNtk, fBddSizeMax, 1, fReorder, 0, fVerbose) == NULL )
        return NULL;

    if ( fVerbose )
    {
        DdManager * dd = (DdManager *)Abc_NtkGlobalBddMan( pNtk );
        printf( "Shared BDD size = %6d nodes.  ", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd) );
        ABC_PRT( "BDD construction time", Abc_Clock() - clk );
    }

    // collect global BDDs
    dd = (DdManager *)Abc_NtkGlobalBddMan( pNtk );
    ppOutputs = ABC_ALLOC( DdNode *, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
        ppOutputs[i] = (DdNode *)Abc_ObjGlobalBdd(pNode);

    // call the decomposition
    pFileGeneric = Extra_FileNameGeneric( pNtk->pSpec );
    if ( !Abc_CascadeExperiment( pFileGeneric, dd, ppOutputs, Abc_NtkCiNum(pNtk), Abc_NtkCoNum(pNtk), nLutSize, fCheck, fVerbose ) )
    {
        // the LUT size is too small
    }

    // for now, duplicate the network
    pNtkNew = Abc_NtkDup( pNtk );

    // cleanup
    Abc_NtkFreeGlobalBdds( pNtk, 1 );
    ABC_FREE( ppOutputs );
    ABC_FREE( pFileGeneric );

//    if ( pNtk->pExdc )
//        pNtkNew->pExdc = Abc_NtkDup( pNtk->pExdc );
    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkCollapse: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

#else

Abc_Ntk_t * Abc_NtkCascade( Abc_Ntk_t * pNtk, int nLutSize, int fCheck, int fVerbose ) { return NULL; }
word * Abc_LutCascade( Mini_Aig_t * p, int nLutSize, int nLuts, int nRails, int nIters, int fVerbose ) { return NULL; }

#endif


/*
    The decomposed structure of the LUT cascade is represented as an array of 64-bit integers (words).
    The first word in the record is the number of LUT info blocks in the record, which follow one by one.
    Each LUT info block contains the following:
    - the number of words in this block
    - the number of fanins
    - the list of fanins
    - the variable ID of the output (can be one of the fanin variables)
    - truth tables (one word for 6 vars or less; more words as needed for more than 6 vars)
    For a 6-input node, the LUT info block takes 10 words (block size, fanin count, 6 fanins, output ID, truth table).
    For a 4-input node, the LUT info block takes  8 words (block size, fanin count, 4 fanins, output ID, truth table).
    If the LUT cascade contains a 6-LUT followed by a 4-LUT, the record contains 1+10+8=19 words.
*/

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word * Abc_LutCascadeGenTest()
{
    word * pLuts = ABC_CALLOC( word, 20 ); int i;
    // node count    
    pLuts[0] = 2;
    // first node
    pLuts[1+0] = 10;
    pLuts[1+1] =  6;
    for ( i = 0; i < 6; i++ )
        pLuts[1+2+i] = i;
    pLuts[1+8] = 0;
    pLuts[1+9] = ABC_CONST(0x8000000000000000);
    // second node    
    pLuts[11+0] = 8;
    pLuts[11+1] = 4;
    for ( i = 0; i < 4; i++ )
        pLuts[11+2+i] = i ? i + 5 : 0;
    pLuts[11+6] = 1;
    pLuts[11+7] = ABC_CONST(0xFFFEFFFEFFFEFFFE);
    return pLuts;
}
void Abc_LutCascadePrint( word * pLuts )
{
    int n, i, k;
    printf( "Single-rail LUT cascade has %d nodes:\n", (int)pLuts[0] );
    for ( n = 0, i = 1; n < pLuts[0]; n++, i += pLuts[i] ) 
    {
        word nIns   = pLuts[i+1];
        word * pIns = pLuts+i+2;
        word * pT   = pLuts+i+2+nIns+1;
        printf( "LUT%d : ", n );
        printf( "%02d = F( ", (int)pIns[nIns] );
        for ( k = 0; k < nIns; k++ )
            printf( "%02d ", (int)pIns[k] );
        for ( ; k < 8; k++ )
            printf( "   " );
        printf( ")  " );
        Extra_PrintHex2( stdout, (unsigned *)pT, nIns );
        printf( "\n" );
    }    
}
word * Abc_LutCascadeTest( Mini_Aig_t * p, int nLutSize, int fVerbose )
{
    word * pLuts = Abc_LutCascadeGenTest();
    Abc_LutCascadePrint( pLuts );
    return pLuts;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkLutCascadeDeriveSop( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNodeNew, word * pT, int nIns, Vec_Int_t * vCover )
{
    int RetValue = Kit_TruthIsop( (unsigned *)pT, nIns, vCover, 1 );
    assert( RetValue == 0 || RetValue == 1 );
    if ( Vec_IntSize(vCover) == 0 || (Vec_IntSize(vCover) == 1 && Vec_IntEntry(vCover,0) == 0) ) {
        assert( RetValue == 0 );
        pNodeNew->pData = Abc_SopCreateAnd( (Mem_Flex_t *)pNtkNew->pManFunc, nIns, NULL );
        return (Vec_IntSize(vCover) == 0) ? Abc_NtkCreateNodeConst0(pNtkNew) : Abc_NtkCreateNodeConst1(pNtkNew);
    }
    else {
        char * pSop = Abc_SopCreateFromIsop( (Mem_Flex_t *)pNtkNew->pManFunc, nIns, vCover );
        if ( RetValue ) Abc_SopComplement( (char *)pSop );
        pNodeNew->pData = pSop;
        return pNodeNew;
    }    
}
Abc_Ntk_t * Abc_NtkLutCascadeFromLuts( word * pLuts, Abc_Ntk_t * pNtk, int nLutSize, int fVerbose )
{
    Abc_Ntk_t * pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    Vec_Int_t * vCover = Vec_IntAlloc( 1000 ); word n, i, k, iLastLut = -1;
    assert( Abc_NtkCoNum(pNtk) == 1 );
    for ( n = 0, i = 1; n < pLuts[0]; n++, i += pLuts[i] ) 
    {
        word nIns   = pLuts[i+1];
        word * pIns = pLuts+i+2;
        word * pT   = pLuts+i+2+nIns+1;
        Abc_Obj_t * pNodeNew = Abc_NtkCreateNode( pNtkNew );
        for ( k = 0; k < nIns; k++ )
            Abc_ObjAddFanin( pNodeNew, Abc_NtkCi(pNtk, pIns[k])->pCopy );
        Abc_NtkCi(pNtk, pIns[nIns])->pCopy = Abc_NtkLutCascadeDeriveSop( pNtkNew, pNodeNew, pT, nIns, vCover );
        iLastLut = pIns[nIns];
    }
    Vec_IntFree( vCover );
    Abc_ObjAddFanin( Abc_NtkCo(pNtk, 0)->pCopy, Abc_NtkCi(pNtk, iLastLut)->pCopy );    
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkLutCascadeFromLuts: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;    
}
Abc_Ntk_t * Abc_NtkLutCascade( Abc_Ntk_t * pNtk, int nLutSize, int nLuts, int nRails, int nIters, int fVerbose )
{
    extern Gia_Man_t *  Abc_NtkStrashToGia( Abc_Ntk_t * pNtk );
    extern Mini_Aig_t * Gia_ManToMiniAig( Gia_Man_t * pGia );
    extern word *       Abc_LutCascade( Mini_Aig_t * p, int nLutSize, int nLuts, int nRails, int nIters, int fVerbose );
    Gia_Man_t * pGia  = Abc_NtkStrashToGia( pNtk );
    Mini_Aig_t * pM   = Gia_ManToMiniAig( pGia );
    word * pLuts      = Abc_LutCascade( pM, nLutSize, nLuts, nRails, nIters, fVerbose );
    //word * pLuts      = Abc_LutCascadeTest( pM, nLutSize, 0 );
    Abc_Ntk_t * pNew  = pLuts ? Abc_NtkLutCascadeFromLuts( pLuts, pNtk, nLutSize, fVerbose ) : NULL;
    ABC_FREE( pLuts );
    Mini_AigStop( pM );
    Gia_ManStop( pGia );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Structural LUT cascade mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

typedef struct Abc_LutCas_t_  Abc_LutCas_t;
struct Abc_LutCas_t_
{
    // mapped network
    Abc_Ntk_t *        pNtk;
    // parameters
    int                nLutSize;
    int                nLutsMax;
    int                nIters;
    int                fDelayLut;
    int                fDelayRoute;
    int                fDelayDirect;
    int                fVerbose;
    // internal data
    int                DelayMax;
    Vec_Int_t *        vTime[2];   // timing info
    Vec_Int_t *        vCrits[2];  // critical terminals
    Vec_Int_t *        vPath[2];   // direct connections
    Vec_Wec_t *        vStack;     // processing queue
    Vec_Int_t *        vZeroSlack; // zero-slack nodes
    Vec_Int_t *        vCands;     // direct edge candidates
    Vec_Int_t *        vTrace;     // modification trace
    Vec_Int_t *        vTraceBest; // modification trace
};

Abc_LutCas_t * Abc_LutCasAlloc( Abc_Ntk_t * pNtk, int nLutsMax, int nIters, int fDelayLut, int fDelayRoute, int fDelayDirect, int fVerbose )
{
    Abc_LutCas_t * p = ABC_ALLOC( Abc_LutCas_t, 1 );
    p->pNtk         = pNtk;
    p->nLutSize     = 6;
    p->nLutsMax     = nLutsMax;
    p->nIters       = nIters;
    p->fDelayLut    = fDelayLut;
    p->fDelayRoute  = fDelayRoute;
    p->fDelayDirect = fDelayDirect;
    p->fVerbose     = fVerbose;
    p->vTime[0]   = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    p->vTime[1]   = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    p->vCrits[0]  = Vec_IntAlloc(1000);
    p->vCrits[1]  = Vec_IntAlloc(1000);
    p->vPath[0]   = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    p->vPath[1]   = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    p->vStack     = Vec_WecStart( Abc_NtkLevel(pNtk) + 1 );
    p->vZeroSlack = Vec_IntAlloc( 1000 );
    p->vCands     = Vec_IntAlloc( 1000 );
    p->vTrace     = Vec_IntAlloc( 1000 );
    p->vTraceBest = Vec_IntAlloc( 1000 );
    return p;
}
void Abc_LutCasFree( Abc_LutCas_t * p )
{
    Vec_IntFree( p->vTime[0]   );
    Vec_IntFree( p->vTime[1]   );
    Vec_IntFree( p->vCrits[0]  );
    Vec_IntFree( p->vCrits[1]  );
    Vec_IntFree( p->vPath[0]   );
    Vec_IntFree( p->vPath[1]   );
    Vec_WecFree( p->vStack     );
    Vec_IntFree( p->vZeroSlack );
    Vec_IntFree( p->vCands     );
    Vec_IntFree( p->vTrace     );
    Vec_IntFree( p->vTraceBest );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    [Structural LUT cascade mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkFindPathTimeD_rec( Abc_LutCas_t * p, Abc_Obj_t * pObj )
{
    if ( !Abc_ObjIsNode(pObj) || !Abc_ObjFaninNum(pObj) )
        return 0;
    if ( Vec_IntEntry(p->vTime[0], pObj->Id) > 0 )
        return Vec_IntEntry(p->vTime[0], pObj->Id);    
    Abc_Obj_t * pNext; int i, Delay, DelayMax = 0;
    Abc_ObjForEachFanin( pObj, pNext, i ) {
        Delay  = Abc_NtkFindPathTimeD_rec( p, pNext );
        Delay += Vec_IntEntry(p->vPath[0], pObj->Id) == pNext->Id ? p->fDelayDirect : p->fDelayRoute;
        DelayMax = Abc_MaxInt( DelayMax, Delay + p->fDelayLut );
    }
    Vec_IntWriteEntry( p->vTime[0], pObj->Id, DelayMax );
    return DelayMax;
}
int Abc_NtkFindPathTimeD( Abc_LutCas_t * p )
{
    Abc_Obj_t * pObj; int i, Delay, DelayMax = 0;
    Vec_IntFill( p->vTime[0], Abc_NtkObjNumMax(p->pNtk), 0 );
    Abc_NtkForEachCo( p->pNtk, pObj, i ) {
        Delay = Abc_NtkFindPathTimeD_rec( p, Abc_ObjFanin0(pObj) );
        DelayMax = Abc_MaxInt( DelayMax, Delay + p->fDelayRoute );
    }
    Vec_IntClear( p->vCrits[0] );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        if ( DelayMax == Vec_IntEntry(p->vTime[0], Abc_ObjFaninId0(pObj)) + p->fDelayRoute )
            Vec_IntPush( p->vCrits[0], pObj->Id );
    return DelayMax;
}
int Abc_NtkFindPathTimeR_rec( Abc_LutCas_t * p, Abc_Obj_t * pObj )
{
    if ( Abc_ObjIsCo(pObj) )
        return 0;
    if ( Vec_IntEntry(p->vTime[1], pObj->Id) > 0 )
        return Vec_IntEntry(p->vTime[1], pObj->Id) + (Abc_ObjIsNode(pObj) ? p->fDelayLut : 0);
    Abc_Obj_t * pNext; int i; float Delay, DelayMax = 0;
    Abc_ObjForEachFanout( pObj, pNext, i ) {
        Delay  = Abc_NtkFindPathTimeR_rec( p, pNext );
        Delay += Vec_IntEntry(p->vPath[0], pNext->Id) == pObj->Id ? p->fDelayDirect : p->fDelayRoute;
        DelayMax = Abc_MaxInt( DelayMax, Delay );
    }
    Vec_IntWriteEntry( p->vTime[1], pObj->Id, DelayMax );
    return DelayMax + (Abc_ObjIsNode(pObj) ? p->fDelayLut : 0);
}
int Abc_NtkFindPathTimeR( Abc_LutCas_t * p )
{
    Abc_Obj_t * pObj; int i; int Delay, DelayMax = 0;
    Vec_IntFill( p->vTime[1], Abc_NtkObjNumMax(p->pNtk), 0 );
    Abc_NtkForEachCi( p->pNtk, pObj, i ) {        
        Delay = Abc_NtkFindPathTimeR_rec( p, pObj );
        DelayMax = Abc_MaxInt( DelayMax, Delay );
    }
    Vec_IntClear( p->vCrits[1] );
    Abc_NtkForEachCi( p->pNtk, pObj, i )
        if ( DelayMax == Vec_IntEntry(p->vTime[1], pObj->Id) )
            Vec_IntPush( p->vCrits[1], pObj->Id );
    return DelayMax;
}
void Abc_NtkFindCriticalEdges( Abc_LutCas_t * p )
{
    Abc_Obj_t * pObj, * pFanin; int i, k;
    Vec_IntClear( p->vCands );
    Abc_NtkForEachNode( p->pNtk, pObj, i ) {
        if ( Vec_IntEntry(p->vPath[0], pObj->Id) )
            continue;
        if ( Vec_IntEntry(p->vTime[0], pObj->Id) + Vec_IntEntry(p->vTime[1], pObj->Id) < p->DelayMax )
            continue;
        assert( Vec_IntEntry(p->vTime[0], pObj->Id) + Vec_IntEntry(p->vTime[1], pObj->Id == p->DelayMax) );
        Abc_ObjForEachFanin( pObj, pFanin, k )
            if ( Abc_ObjIsNode(pFanin) && !Vec_IntEntry(p->vPath[1], pFanin->Id) && 
                 Vec_IntEntry(p->vTime[0], pFanin->Id) + p->fDelayRoute + p->fDelayLut == Vec_IntEntry(p->vTime[0], pObj->Id) )
                Vec_IntPushTwo( p->vCands, pObj->Id, pFanin->Id );
    }    
}
int Abc_NtkFindTiming( Abc_LutCas_t * p )
{
    int Delay0 = Abc_NtkFindPathTimeD( p );
    int Delay1 = Abc_NtkFindPathTimeR( p );
    assert( Delay0 == Delay1 );
    p->DelayMax = Delay0;
    Abc_NtkFindCriticalEdges( p );
    return Delay0;
}

int Abc_NtkUpdateNodeD( Abc_LutCas_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pNext; int i; int Delay, DelayMax = 0;
    Abc_ObjForEachFanin( pObj, pNext, i ) {
        Delay  = Vec_IntEntry( p->vTime[0], pNext->Id );
        Delay += Vec_IntEntry(p->vPath[0], pObj->Id) == pNext->Id ? p->fDelayDirect : p->fDelayRoute;
        DelayMax = Abc_MaxInt( DelayMax, Delay + p->fDelayLut );
    }
    int DelayOld = Vec_IntEntry( p->vTime[0], pObj->Id );
    Vec_IntWriteEntry( p->vTime[0], pObj->Id, DelayMax );
    assert( DelayOld >= DelayMax );
    return DelayOld > DelayMax;
}
int Abc_NtkUpdateNodeR( Abc_LutCas_t * p, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pNext; int i; float Delay, DelayMax = 0;
    Abc_ObjForEachFanout( pObj, pNext, i ) {
        Delay  = Vec_IntEntry(p->vTime[1], pNext->Id) + (Abc_ObjIsNode(pNext) ? p->fDelayLut : 0);
        Delay += Vec_IntEntry(p->vPath[0], pNext->Id) == pObj->Id ? p->fDelayDirect : p->fDelayRoute;
        DelayMax = Abc_MaxInt( DelayMax, Delay );
    }
    int DelayOld = Vec_IntEntry( p->vTime[1], pObj->Id );
    Vec_IntWriteEntry( p->vTime[1], pObj->Id, DelayMax );
    assert( DelayOld >= DelayMax );
    return DelayOld > DelayMax;
}
int Abc_NtkUpdateTiming( Abc_LutCas_t * p, int Node, int Fanin )
{
    Abc_Obj_t * pNode  = Abc_NtkObj( p->pNtk, Node );
    Abc_Obj_t * pFanin = Abc_NtkObj( p->pNtk, Fanin );
    Abc_Obj_t * pNext, * pTemp; Vec_Int_t * vLevel; int i, k, j;
    assert( Abc_ObjIsNode(pNode) && Abc_ObjIsNode(pFanin) );
    Vec_WecForEachLevel( p->vStack, vLevel, i )
        Vec_IntClear( vLevel );
    Abc_NtkIncrementTravId( p->pNtk );
    Abc_NodeSetTravIdCurrentId( p->pNtk, Node );
    Abc_NodeSetTravIdCurrentId( p->pNtk, Fanin );
    Vec_WecPush( p->vStack, pNode->Level, Node );
    Vec_WecPush( p->vStack, pFanin->Level, Fanin );
    Vec_WecForEachLevelStart( p->vStack, vLevel, i, pNode->Level )
        Abc_NtkForEachObjVec( vLevel, p->pNtk, pTemp, k ) {
            if ( !Abc_NtkUpdateNodeD(p, pTemp) )
                continue;
            Abc_ObjForEachFanout( pTemp, pNext, j ) {
                if ( Abc_NodeIsTravIdCurrent(pNext) || Abc_ObjIsCo(pNext) ) 
                    continue;
                Abc_NodeSetTravIdCurrent( pNext );
                Vec_WecPush( p->vStack, pNext->Level, pNext->Id );                    
            }
        }
    Vec_WecForEachLevelReverseStartStop( p->vStack, vLevel, i, pFanin->Level+1, 0 )
        Abc_NtkForEachObjVec( vLevel, p->pNtk, pTemp, k ) {
            if ( !Abc_NtkUpdateNodeR(p, pTemp) )
                continue;
            Abc_ObjForEachFanin( pTemp, pNext, j ) {
                if ( Abc_NodeIsTravIdCurrent(pNext) ) 
                    continue;
                Abc_NodeSetTravIdCurrent( pNext );
                Vec_WecPush( p->vStack, pNext->Level, pNext->Id );                    
            }
        }
    j = 0;
    Abc_NtkForEachObjVec( p->vCrits[0], p->pNtk, pTemp, i )
        if ( Vec_IntEntry(p->vTime[0], Abc_ObjFaninId0(pTemp)) + p->fDelayRoute == p->DelayMax )
            Vec_IntWriteEntry( p->vCrits[0], j++, pTemp->Id );
    Vec_IntShrink( p->vCrits[0], j );
    j = 0;
    Abc_NtkForEachObjVec( p->vCrits[1], p->pNtk, pTemp, i )
        if ( Vec_IntEntry(p->vTime[1], pTemp->Id) == p->DelayMax )
            Vec_IntWriteEntry( p->vCrits[1], j++, pTemp->Id );
    Vec_IntShrink( p->vCrits[1], j );
    if ( Vec_IntSize(p->vCrits[0]) && Vec_IntSize(p->vCrits[1]) ) {
        int j = 0, Node2, Fanin2;
        Vec_IntForEachEntryDouble( p->vCands, Node2, Fanin2, i )
            if ( !Vec_IntEntry(p->vPath[0], Node2) && !Vec_IntEntry(p->vPath[1], Fanin2) && 
                 Vec_IntEntry(p->vTime[0], Node2) + Vec_IntEntry(p->vTime[1], Node2) == p->DelayMax && 
                 Vec_IntEntry(p->vTime[0], Fanin2) + p->fDelayRoute + p->fDelayLut == Vec_IntEntry(p->vTime[0], Node2) )
                    Vec_IntWriteEntry( p->vCands, j++, Node2 ), Vec_IntWriteEntry( p->vCands, j++, Fanin2 );
        Vec_IntShrink( p->vCands, j );
        return p->DelayMax;
    }
    int DelayOld = p->DelayMax;
    Abc_NtkFindTiming(p);
    assert( DelayOld > p->DelayMax );
    return p->DelayMax;
}

/**Function*************************************************************

  Synopsis    [Structural LUT cascade mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkAddEdges( Abc_LutCas_t * p )
{
    int nEdgesMax = 10000;
    Vec_IntClear( p->vTrace );
    Vec_IntFill( p->vPath[0], Vec_IntSize(p->vPath[0]), 0 );
    Vec_IntFill( p->vPath[1], Vec_IntSize(p->vPath[1]), 0 );
    Abc_NtkFindTiming( p );
    if ( p->fVerbose )
        printf( "Start : %d\n", p->DelayMax );
    int i, LastChange = 0;
    for ( i = 0; i < nEdgesMax; i++ ) 
    {
        float DelayPrev = p->DelayMax;
        if ( Vec_IntSize(p->vCands) == 0 )
            break;
        int Index = rand() % Vec_IntSize(p->vCands)/2;
        int Node  = Vec_IntEntry( p->vCands, 2*Index );
        int Fanin = Vec_IntEntry( p->vCands, 2*Index+1 );
        assert( Vec_IntEntry( p->vPath[0], Node ) == 0 );
        Vec_IntWriteEntry( p->vPath[0], Node, Fanin );
        assert( Vec_IntEntry( p->vPath[1], Fanin ) == 0 );
        Vec_IntWriteEntry( p->vPath[1], Fanin, Node );
        Vec_IntPushTwo( p->vTrace, Node, Fanin );
        //Abc_NtkFindTiming( p );
        Abc_NtkUpdateTiming( p, Node, Fanin );
        assert( DelayPrev >= p->DelayMax );
        if ( DelayPrev > p->DelayMax )
            LastChange = i+1;
        DelayPrev = p->DelayMax;
        if ( p->fVerbose )
            printf( "%5d : %d : %4d -> %4d\n", i, p->DelayMax, Fanin, Node );
    }
    Vec_IntShrink( p->vTrace, 2*LastChange );
    return p->DelayMax;
}
Vec_Wec_t * Abc_NtkProfileCascades( Abc_Ntk_t * pNtk, Vec_Int_t * vTrace )
{
    Vec_Wec_t * vCasc = Vec_WecAlloc( 100 );
    Vec_Int_t * vMap  = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    Vec_Int_t * vPath = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    Vec_Int_t * vCounts = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    Abc_Obj_t * pObj; int i, Node, Fanin, Count, nCascs = 0;
    Vec_IntForEachEntryDouble( vTrace, Node, Fanin, i ) {
        assert( Vec_IntEntry(vPath, Node) == 0 );
        Vec_IntWriteEntry( vPath, Node, Fanin );
        Vec_IntWriteEntry( vMap, Fanin, 1 );
    }
    Abc_NtkForEachNode( pNtk, pObj, i ) {
        if ( Vec_IntEntry(vMap, pObj->Id) )
            continue;
        if ( Vec_IntEntry(vPath, pObj->Id) == 0 )
            continue;
        Vec_Int_t * vLevel = Vec_WecPushLevel( vCasc );
        Node = pObj->Id;
        Vec_IntPush( vLevel, Node );
        while ( (Node = Vec_IntEntry(vPath, Node)) )
            Vec_IntPush( vLevel, Node );
        Vec_IntAddToEntry( vCounts, Vec_IntSize(vLevel), 1 );
    }
    printf( "Cascades: " );
    Vec_IntForEachEntry( vCounts, Count, i )
        if ( Count )
            printf( "%d=%d ", i, Count ), nCascs += Count;
    printf( "\n" );
    Vec_IntFree( vMap );
    Vec_IntFree( vPath );
    Vec_IntFree( vCounts );
    return vCasc;
}
void Abc_LutCasAssignNames( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew, Vec_Wec_t * vCascs )
{
    Abc_Obj_t * pObj; Vec_Int_t * vLevel; int i, k; char pName[100];
    Vec_Int_t * vMap = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachCo( pNtkNew, pObj, i )
        Vec_IntWriteEntry( vMap, Abc_ObjFaninId0(pObj), pObj->Id );
    Vec_WecForEachLevel( vCascs, vLevel, i ) {
        Abc_NtkForEachObjVec( vLevel, pNtk, pObj, k ) {
            assert( Abc_ObjIsNode(pObj) );
            sprintf( pName, "c%d_n%d", i, k );
            if ( Vec_IntEntry(vMap, pObj->pCopy->Id) == 0 )
                Abc_ObjAssignName( Abc_NtkObj(pNtkNew, pObj->pCopy->Id), pName, NULL );
            else {
                Nm_ManDeleteIdName( pNtkNew->pManName, Vec_IntEntry(vMap, pObj->pCopy->Id) );
                Abc_ObjAssignName( Abc_NtkObj(pNtkNew, Vec_IntEntry(vMap, pObj->pCopy->Id)), pName, NULL );
            }
        }
    }
    Vec_IntFree( vMap );
}
void Abc_NtkLutCascadeDumpResults( char * pDumpFile, char * pTest, int Nodes, int Edges, int Levs, int DelStart, int DelStop, float DelRatio, int EdgesUsed, float EdgeRatio, int Cascs, float AveLength, abctime time )
{
    FILE * pTable = fopen( pDumpFile, "a+" );
    fprintf( pTable, "%s,", pTest+28 );
    fprintf( pTable, "%d,", Nodes );
    fprintf( pTable, "%d,", Edges );
    fprintf( pTable, "%d,", Levs );
    fprintf( pTable, "%d,", DelStart );
    fprintf( pTable, "%d,", DelStop );
    fprintf( pTable, "%.2f,", DelRatio );
    fprintf( pTable, "%d,", EdgesUsed );
    fprintf( pTable, "%.2f,", EdgeRatio );
    fprintf( pTable, "%d,",   Cascs );
    fprintf( pTable, "%.1f,", AveLength );
    fprintf( pTable, "%.2f,", 1.0*((double)(time))/((double)CLOCKS_PER_SEC) );
    fprintf( pTable, "\n" );
    fclose( pTable );
}

Abc_Ntk_t * Abc_NtkLutCascadeMap( Abc_Ntk_t * pNtk, int nLutsMax, int nIters, int fDelayLut, int fDelayRoute, int fDelayDirect, int fVerbose )
{
    abctime clk = Abc_Clock();
    Abc_Ntk_t * pNtkNew = NULL;
    Abc_LutCas_t * p = Abc_LutCasAlloc( pNtk, nLutsMax, nIters, fDelayLut, fDelayRoute, fDelayDirect, fVerbose );
    int i, IterBest = 0, DelayStart = Abc_NtkFindTiming( p ),  DelayBest = DelayStart, nEdges = Abc_NtkGetTotalFanins(pNtk);
    //printf( "Delays: LUT (%d) Route (%d) Direct (%d).  Iters = %d.  LUTs = %d.\n", fDelayLut, fDelayRoute, fDelayDirect, nIters, Abc_NtkNodeNum(pNtk) );
    Vec_IntFill( p->vTraceBest, Abc_NtkNodeNum(pNtk), 0 );
    for ( i = 0; i < nIters; i++ )
    {
        if ( fVerbose )
            printf( "ITERATION %2d:\n", i );
        float Delay = Abc_NtkAddEdges( p );
        if ( DelayBest < Delay || (DelayBest == Delay && Vec_IntSize(p->vTraceBest) <= Vec_IntSize(p->vTrace)) )
            continue;
        IterBest = i;
        DelayBest = Delay;
        ABC_SWAP( Vec_Int_t *, p->vTrace, p->vTraceBest );
    }
    printf( "Delay reduction %d -> %d (-%.2f %%) is found after iter %d with %d edges (%.2f %%). ", 
        DelayStart, DelayBest, 100.0*(DelayStart - DelayBest)/DelayStart, IterBest, Vec_IntSize(p->vTraceBest)/2, 50.0*Vec_IntSize(p->vTraceBest)/nEdges );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Vec_Wec_t * vCascs = Abc_NtkProfileCascades( p->pNtk, p->vTraceBest );
//    Abc_NtkLutCascadeDumpResults( "stats.csv", pNtk->pName, Abc_NtkNodeNum(pNtk), nEdges, Abc_NtkLevel(pNtk), DelayStart, DelayBest, 100.0*(DelayStart - DelayBest)/DelayStart,
//        Vec_IntSize(p->vTraceBest)/2, 50.0*Vec_IntSize(p->vTraceBest)/nEdges, Vec_WecSize(vCascs), 0.5*Vec_IntSize(p->vTraceBest)/Abc_MaxInt(1, Vec_WecSize(vCascs)), Abc_Clock() - clk );
    Abc_LutCasFree( p );
    pNtkNew = Abc_NtkDup( pNtk );
    Abc_LutCasAssignNames( pNtk, pNtkNew, vCascs );
    Vec_WecFree( vCascs );
    return pNtkNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

