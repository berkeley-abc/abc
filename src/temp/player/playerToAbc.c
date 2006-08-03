/**CFile****************************************************************

  FileName    [playerToAbc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [PLAyer decomposition package.]

  Synopsis    [Bridge between ABC and PLAyer.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 20, 2006.]

  Revision    [$Id: playerToAbc.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "player.h"
#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Ivy_Man_t * Ivy_ManFromAbc( Abc_Ntk_t * p );
static Abc_Ntk_t * Ivy_ManToAbc( Abc_Ntk_t * pNtk, Ivy_Man_t * pMan, Pla_Man_t * p, int fFastMode );
static Abc_Obj_t * Ivy_ManToAbc_rec( Abc_Ntk_t * pNtkNew, Ivy_Man_t * pMan, Pla_Man_t * p, Ivy_Obj_t * pObjIvy, Vec_Int_t * vNodes, Vec_Int_t * vTemp );
static Abc_Obj_t * Ivy_ManToAbcFast_rec( Abc_Ntk_t * pNtkNew, Ivy_Man_t * pMan, Ivy_Obj_t * pObjIvy, Vec_Int_t * vNodes, Vec_Int_t * vTemp );
static Abc_Obj_t * Ivy_ManToAigCube( Abc_Ntk_t * pNtkNew, Ivy_Man_t * pMan, Ivy_Obj_t * pObjIvy, Esop_Cube_t * pCube, Vec_Int_t * vSupp );
static int Abc_NtkPlayerCost( Abc_Ntk_t * pNtk, int RankCost, int fVerbose );

static inline void        Abc_ObjSetIvy2Abc( Ivy_Man_t * p, int IvyId, Abc_Obj_t * pObjAbc ) {  assert(Vec_PtrEntry(p->pCopy, IvyId) == NULL); assert(!Abc_ObjIsComplement(pObjAbc)); Vec_PtrWriteEntry( p->pCopy, IvyId, pObjAbc );  }
static inline Abc_Obj_t * Abc_ObjGetIvy2Abc( Ivy_Man_t * p, int IvyId )                      {  return Vec_PtrEntry( p->pCopy, IvyId );         }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Applies PLA/LUT mapping to the ABC network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Abc_NtkPlayer( void * pNtk, int nLutMax, int nPlaMax, int RankCost, int fFastMode, int fVerbose )
{
    int fUseRewriting = 0;
    Pla_Man_t * p;
    Ivy_Man_t * pMan, * pManExt;
    Abc_Ntk_t * pNtkNew;
    if ( !Abc_NtkIsStrash(pNtk) )
        return NULL;
    // convert to the new AIG manager
    pMan = Ivy_ManFromAbc( pNtk );
    // check the correctness of conversion
    if ( !Ivy_ManCheck( pMan ) )
    {
        printf( "Abc_NtkPlayer: Internal AIG check has failed.\n" );
        Ivy_ManStop( pMan );
        return NULL;
    }
    if ( fVerbose )
        Ivy_ManPrintStats( pMan );
    if ( fUseRewriting )
    {
        // simplify
        pMan = Ivy_ManResyn( pManExt = pMan, 1, 0 );
        Ivy_ManStop( pManExt );
        if ( fVerbose )
            Ivy_ManPrintStats( pMan );
    }
    // perform decomposition
    if ( fFastMode )
    {
        // perform mapping into LUTs
        Pla_ManFastLutMap( pMan, nLutMax );
        // convert from the extended AIG manager into an SOP network
        pNtkNew = Ivy_ManToAbc( pNtk, pMan, NULL, fFastMode );
        Pla_ManFastLutMapStop( pMan );
    }
    else
    {
        // perform decomposition/mapping into PLAs/LUTs
        p = Pla_ManDecompose( pMan, nLutMax, nPlaMax, fVerbose );
        // convert from the extended AIG manager into an SOP network
        pNtkNew = Ivy_ManToAbc( pNtk, pMan, p, fFastMode );
        Pla_ManFree( p );
    }
    Ivy_ManStop( pMan );
    // chech the resulting network
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkPlayer: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    Abc_NtkPlayerCost( pNtkNew, RankCost, fVerbose );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Converts from strashed AIG in ABC into strash AIG in IVY.]

  Description [Assumes DFS ordering of nodes in the AIG of ABC.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Man_t * Ivy_ManFromAbc( Abc_Ntk_t * pNtk )
{
    Ivy_Man_t * pMan;
    Abc_Obj_t * pObj;
    int i;
    // create the manager
    pMan = Ivy_ManStart();
    // create the PIs
    Abc_NtkConst1(pNtk)->pCopy = (Abc_Obj_t *)Ivy_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Ivy_ObjCreatePi(pMan);
    // perform the conversion of the internal nodes
    Abc_AigForEachAnd( pNtk, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Ivy_And( pMan, (Ivy_Obj_t *)Abc_ObjChild0Copy(pObj), (Ivy_Obj_t *)Abc_ObjChild1Copy(pObj) );
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Ivy_ObjCreatePo( pMan, (Ivy_Obj_t *)Abc_ObjChild0Copy(pObj) );
    Ivy_ManCleanup( pMan );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Constructs the ABD network after mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Ivy_ManToAbc( Abc_Ntk_t * pNtk, Ivy_Man_t * pMan, Pla_Man_t * p, int fFastMode )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjAbc, * pObj;
    Ivy_Obj_t * pObjIvy;
    Vec_Int_t * vNodes, * vTemp;
    int i;
    // start mapping from Ivy into Abc
    pMan->pCopy = Vec_PtrStart( Ivy_ManObjIdMax(pMan) + 1 );
    // start the new ABC network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    // transfer the pointers to the basic nodes
    Abc_ObjSetIvy2Abc( pMan, Ivy_ManConst1(pMan)->Id, Abc_NtkConst1(pNtkNew) );
    Abc_NtkForEachCi( pNtkNew, pObjAbc, i )
        Abc_ObjSetIvy2Abc( pMan, Ivy_ManPi(pMan, i)->Id, pObjAbc ); 
    // recursively construct the network
    vNodes = Vec_IntAlloc( 100 );
    vTemp  = Vec_IntAlloc( 100 );
    Ivy_ManForEachPo( pMan, pObjIvy, i )
    {
        // get the new ABC node corresponding to the old fanin of the PO in IVY
        if ( fFastMode )
            pObjAbc = Ivy_ManToAbcFast_rec( pNtkNew, pMan, Ivy_ObjFanin0(pObjIvy), vNodes, vTemp );
        else
            pObjAbc = Ivy_ManToAbc_rec( pNtkNew, pMan, p, Ivy_ObjFanin0(pObjIvy), vNodes, vTemp );
        // consider the case of complemented fanin of the PO
        if ( Ivy_ObjFaninC0(pObjIvy) ) // complement
        {
            if ( Abc_ObjIsCi(pObjAbc) )
                pObjAbc = Abc_NodeCreateInv( pNtkNew, pObjAbc );
            else
            {
                // clone the node
                pObj = Abc_NodeClone( pObjAbc );
                // set complemented functions
                pObj->pData = Abc_SopRegister( pNtkNew->pManFunc, pObjAbc->pData );
                Abc_SopComplement(pObj->pData); 
                // return the new node
                pObjAbc = pObj;
            }
            assert( Abc_SopGetVarNum(pObjAbc->pData) == Abc_ObjFaninNum(pObjAbc) );
        }
        Abc_ObjAddFanin( Abc_NtkCo(pNtkNew, i), pObjAbc );
    }
    Vec_IntFree( vTemp );
    Vec_IntFree( vNodes );
    Vec_PtrFree( pMan->pCopy ); 
    pMan->pCopy = NULL;
    // remove dangling nodes
//    Abc_NtkForEachNode( pNtkNew, pObjAbc, i )
//        if ( Abc_ObjFanoutNum(pObjAbc) == 0 )
//            Abc_NtkDeleteObj(pObjAbc); 
    Abc_NtkCleanup( pNtkNew, 0 );
    // fix CIs feeding directly into COs
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Recursively construct the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Ivy_ManToAbc_rec( Abc_Ntk_t * pNtkNew, Ivy_Man_t * pMan, Pla_Man_t * p, Ivy_Obj_t * pObjIvy, Vec_Int_t * vNodes, Vec_Int_t * vTemp )
{
    Vec_Int_t * vSupp;
    Esop_Cube_t * pCover, * pCube;
    Abc_Obj_t * pObjAbc, * pFaninAbc;
    Pla_Obj_t * pStr;
    int Entry, nCubes, i;
    unsigned * puTruth;
    // skip the node if it is a constant or already processed
    pObjAbc = Abc_ObjGetIvy2Abc( pMan, pObjIvy->Id );
    if ( pObjAbc )
        return pObjAbc;
    assert( Ivy_ObjIsAnd(pObjIvy) || Ivy_ObjIsExor(pObjIvy) );
    // get the support and the cover
    pStr = Ivy_ObjPlaStr( pMan, pObjIvy );
    if ( Vec_IntSize( &pStr->vSupp[0] ) <= p->nLutMax )
    {
        vSupp = &pStr->vSupp[0]; 
        pCover = PLA_EMPTY;
    }
    else
    {
        vSupp = &pStr->vSupp[1]; 
        pCover = pStr->pCover[1];
        assert( pCover != PLA_EMPTY );
    }
    // create new node and its fanins
    Vec_IntForEachEntry( vSupp, Entry, i )
        Ivy_ManToAbc_rec( pNtkNew, pMan, p, Ivy_ManObj(pMan, Entry), vNodes, vTemp );
    // consider the case of a LUT
    if ( pCover == PLA_EMPTY )
    {
        pObjAbc = Abc_NtkCreateNode( pNtkNew );
        Vec_IntForEachEntry( vSupp, Entry, i )
            Abc_ObjAddFanin( pObjAbc, Abc_ObjGetIvy2Abc(pMan, Entry) );
        // check if the truth table is constant 0
        puTruth = Ivy_ManCutTruth( pMan, pObjIvy, vSupp, vNodes, vTemp );
        // if the function is constant 0, create constant 0 node
        if ( Extra_TruthIsConst0(puTruth, 8) )
        {
            pObjAbc->pData = Abc_SopCreateAnd( pNtkNew->pManFunc, Vec_IntSize(vSupp), NULL );
            pObjAbc = Abc_NodeCreateConst0( pNtkNew );  
        }
        else
        {
            int fCompl = Ivy_TruthIsop( puTruth, Vec_IntSize(vSupp), vNodes );
            pObjAbc->pData = Abc_SopCreateFromIsop( pNtkNew->pManFunc, Vec_IntSize(vSupp), vNodes );
            if ( fCompl ) Abc_SopComplement(pObjAbc->pData); 
//            printf( "Cover contains %d cubes.\n", Vec_IntSize(vNodes) );
//            pObjAbc->pData = Abc_SopCreateFromTruth( pNtkNew->pManFunc, Vec_IntSize(vSupp), puTruth );
        }
    }
    else
    {
        // for each cube, construct the node
        nCubes = Esop_CoverCountCubes( pCover );
        if ( nCubes == 0 )
            pObjAbc = Abc_NodeCreateConst0( pNtkNew );  
        else if ( nCubes == 1 )
            pObjAbc = Ivy_ManToAigCube( pNtkNew, pMan, pObjIvy, pCover, vSupp );
        else
        {
            pObjAbc = Abc_NtkCreateNode( pNtkNew );
            Esop_CoverForEachCube( pCover, pCube )
            {
                pFaninAbc = Ivy_ManToAigCube( pNtkNew, pMan, pObjIvy, pCube, vSupp );
                Abc_ObjAddFanin( pObjAbc, pFaninAbc );
            }
            pObjAbc->pData = Abc_SopCreateXorSpecial( pNtkNew->pManFunc, Abc_ObjFaninNum(pObjAbc) );
        }
    }
    Abc_ObjSetIvy2Abc( pMan, pObjIvy->Id, pObjAbc ); 
    return pObjAbc;
}

/**Function*************************************************************

  Synopsis    [Derives the decomposed network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Ivy_ManToAigCube( Abc_Ntk_t * pNtkNew, Ivy_Man_t * pMan, Ivy_Obj_t * pObjIvy, Esop_Cube_t * pCube, Vec_Int_t * vSupp )
{
    int pCompls[PLAYER_FANIN_LIMIT];
    Abc_Obj_t * pObjAbc, * pFaninAbc;
    int i, k, Value;
    // if tautology cube, create constant 1 node
    if ( pCube->nLits == 0 )
        return Abc_NodeCreateConst1(pNtkNew);
    // create AND node
    pObjAbc = Abc_NtkCreateNode( pNtkNew );
    for ( i = k = 0; i < (int)pCube->nVars; i++ )
    {
        Value = Esop_CubeGetVar( pCube, i );
        assert( Value != 0 );
        if ( Value == 3 )
            continue;
        pFaninAbc = Abc_ObjGetIvy2Abc( pMan, Vec_IntEntry(vSupp, i) );
        pFaninAbc = Abc_ObjNotCond( pFaninAbc, Value==1 );
        Abc_ObjAddFanin( pObjAbc, Abc_ObjRegular(pFaninAbc) );
        pCompls[k++] = Abc_ObjIsComplement(pFaninAbc);
    }
    pObjAbc->pData = Abc_SopCreateAnd( pNtkNew->pManFunc, Abc_ObjFaninNum(pObjAbc), pCompls );
    assert( Abc_ObjFaninNum(pObjAbc) == (int)pCube->nLits );
    return pObjAbc;
}




/**Function*************************************************************

  Synopsis    [Recursively construct the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Ivy_ManToAbcFast_rec( Abc_Ntk_t * pNtkNew, Ivy_Man_t * pMan, Ivy_Obj_t * pObjIvy, Vec_Int_t * vNodes, Vec_Int_t * vTemp )
{
    Vec_Int_t Supp, * vSupp = &Supp;
    Abc_Obj_t * pObjAbc, * pFaninAbc;
    int i, Entry;
    unsigned * puTruth;
    // skip the node if it is a constant or already processed
    pObjAbc = Abc_ObjGetIvy2Abc( pMan, pObjIvy->Id );
    if ( pObjAbc )
        return pObjAbc;
    assert( Ivy_ObjIsAnd(pObjIvy) || Ivy_ObjIsExor(pObjIvy) );
    // get the support of K-LUT
    Pla_ManFastLutMapReadSupp( pMan, pObjIvy, vSupp );
    // create new ABC node and its fanins
    pObjAbc = Abc_NtkCreateNode( pNtkNew );
    Vec_IntForEachEntry( vSupp, Entry, i )
    {
        pFaninAbc = Ivy_ManToAbcFast_rec( pNtkNew, pMan, Ivy_ManObj(pMan, Entry), vNodes, vTemp );
        Abc_ObjAddFanin( pObjAbc, pFaninAbc );
    }
    // check if the truth table is constant 0
    puTruth = Ivy_ManCutTruth( pMan, pObjIvy, vSupp, vNodes, vTemp );
    // if the function is constant 0, create constant 0 node
    if ( Extra_TruthIsConst0(puTruth, 8) )
    {
        pObjAbc->pData = Abc_SopCreateAnd( pNtkNew->pManFunc, Vec_IntSize(vSupp), NULL );
        pObjAbc = Abc_NodeCreateConst0( pNtkNew );  
    }
    else
    {
        int fCompl = Ivy_TruthIsop( puTruth, Vec_IntSize(vSupp), vNodes );
        pObjAbc->pData = Abc_SopCreateFromIsop( pNtkNew->pManFunc, Vec_IntSize(vSupp), vNodes );
        if ( fCompl ) Abc_SopComplement(pObjAbc->pData); 
    }
    Abc_ObjSetIvy2Abc( pMan, pObjIvy->Id, pObjAbc ); 
    return pObjAbc;
}


/**Function*************************************************************

  Synopsis    [Computes cost of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_NodePlayerCost( int nFanins )
{
    if ( nFanins <= 4 )
        return 1;
    if ( nFanins <= 6 )
        return 2;
    if ( nFanins <= 8 )
        return 4;
    if ( nFanins <= 16 )
        return 8;
    if ( nFanins <= 32 )
        return 16;
    if ( nFanins <= 64 )
        return 32;
    if ( nFanins <= 128 )
        return 64;
    assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Computes the number of ranks needed for one level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_NtkPlayerCostOne( int nCost, int RankCost )
{
    return (nCost / RankCost) + ((nCost % RankCost) > 0);
}

/**Function*************************************************************

  Synopsis    [Computes the cost function for the network (number of ranks).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkPlayerCost( Abc_Ntk_t * pNtk, int RankCost, int fVerbose )
{
    Abc_Obj_t * pObj;
    int nFanins, nLevels, * pLevelCosts, CostTotal, nRanksTotal, i; 
    // compute the costs for each level
    nLevels = Abc_NtkGetLevelNum( pNtk );
    pLevelCosts = ALLOC( int, nLevels + 1 );
    memset( pLevelCosts, 0, sizeof(int) * (nLevels + 1) );
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        nFanins = Abc_ObjFaninNum(pObj);
        if ( nFanins == 0 )
            continue;
        pLevelCosts[ pObj->Level ] += Abc_NodePlayerCost( nFanins );
    }
    // compute the total cost
    CostTotal = nRanksTotal = 0;
    for ( i = 1; i <= nLevels; i++ )
    {
        CostTotal   += pLevelCosts[i];
        nRanksTotal += Abc_NtkPlayerCostOne( pLevelCosts[i], RankCost );
    }
    // print out statistics
    if ( fVerbose )
    {
        for ( i = 1; i <= nLevels; i++ )
            printf( "Level %2d : Cost = %6d. Ranks = %6.3f.\n", i, pLevelCosts[i], ((double)pLevelCosts[i])/RankCost );
        printf( "TOTAL    : Cost = %6d. Ranks = %3d.\n", CostTotal, nRanksTotal );
    }
    return nRanksTotal;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


