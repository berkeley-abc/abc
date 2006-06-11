/**CFile****************************************************************

  FileName    [playerBuild.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [PLA decomposition package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: playerBuild.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "player.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Ivy_Obj_t * Pla_ManToAig_rec( Ivy_Man_t * pNew, Ivy_Obj_t * pObjOld );
static Ivy_Obj_t * Ivy_ManToAigCube( Ivy_Man_t * pNew, Ivy_Obj_t * pObj, Esop_Cube_t * pCube, Vec_Int_t * vSupp );
static Ivy_Obj_t * Ivy_ManToAigConst( Ivy_Man_t * pNew, int fConst1 );
static int         Pla_ManToAigLutFuncs( Ivy_Man_t * pNew, Ivy_Man_t * pOld );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Constructs the AIG manager (IVY) for the network after mapping.]

  Description [Uses extended node types (multi-input AND, multi-input EXOR, LUT).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Man_t * Pla_ManToAig( Ivy_Man_t * pOld )
{
    Ivy_Man_t * pNew;
    Ivy_Obj_t * pObjOld, * pObjNew;
    int i;
    // start the new manager
    pNew = Ivy_ManStart( Ivy_ManPiNum(pOld), Ivy_ManPoNum(pOld), 2*Ivy_ManNodeNum(pOld) + 10 );
    pNew->fExtended = 1;
    // transfer the const/PI numbers
    Ivy_ManCleanTravId(pOld);
    Ivy_ManConst1(pOld)->TravId = Ivy_ManConst1(pNew)->Id;
    Ivy_ManForEachPi( pOld, pObjOld, i )
        pObjOld->TravId = Ivy_ManPi(pNew, i)->Id;
    // recursively construct the network
    Ivy_ManForEachPo( pOld, pObjOld, i )
    {
        pObjNew = Pla_ManToAig_rec( pNew, Ivy_ObjFanin0(pObjOld) );
        Ivy_ObjStartFanins( Ivy_ManPo(pNew, i), 1 );
        Ivy_ObjAddFanin( Ivy_ManPo(pNew, i), Ivy_FanCreate(pObjNew->Id, Ivy_ObjFaninC0(pObjOld)) );
    }
    // compute the LUT functions
    Pla_ManToAigLutFuncs( pNew, pOld ); 
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Recursively construct the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Pla_ManToAig_rec( Ivy_Man_t * pNew, Ivy_Obj_t * pObjOld )
{
    Pla_Man_t * p = Ivy_ObjMan(pObjOld)->pData;
    Vec_Int_t * vSupp;
    Esop_Cube_t * pCover, * pCube;
    Ivy_Obj_t * pFaninOld, * pFaninNew, * pObjNew;
    Pla_Obj_t * pStr;
    int Entry, nCubes, ObjNewId, i;
    // skip the node if it is a constant or already processed
    if ( Ivy_ObjIsConst1(pObjOld) || pObjOld->TravId )
        return Ivy_ManObj( pNew, pObjOld->TravId );
    assert( Ivy_ObjIsAnd(pObjOld) || Ivy_ObjIsExor(pObjOld) );
    // get the support and the cover
    pStr = Ivy_ObjPlaStr( pObjOld );
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
    // process the fanins
    Vec_IntForEachEntry( vSupp, Entry, i )
        Pla_ManToAig_rec( pNew, Ivy_ObjObj(pObjOld, Entry) );
    // consider the case of a LUT
    if ( pCover == PLA_EMPTY )
    {
        pObjNew = Ivy_ObjCreateExt( pNew, IVY_LUT );
        Ivy_ObjStartFanins( pObjNew, p->nLutMax );
        // remember new object ID in case it changes
        ObjNewId = pObjNew->Id;
        Vec_IntForEachEntry( vSupp, Entry, i )
        {
            pFaninOld = Ivy_ObjObj( pObjOld, Entry );
            Ivy_ObjAddFanin( Ivy_ManObj(pNew, ObjNewId), Ivy_FanCreate(pFaninOld->TravId, 0) );
        }
        // get the new object
        pObjNew = Ivy_ManObj(pNew, ObjNewId);
    }
    else
    {
        // for each cube, construct the node
        nCubes = Esop_CoverCountCubes( pCover );
        if ( nCubes == 0 )
            pObjNew = Ivy_ManToAigConst( pNew, 0 );
        else if ( nCubes == 1 )
            pObjNew = Ivy_ManToAigCube( pNew, pObjOld, pCover, vSupp );
        else
        {
            pObjNew = Ivy_ObjCreateExt( pNew, IVY_EXORM );
            Ivy_ObjStartFanins( pObjNew, p->nLutMax );
            // remember new object ID in case it changes
            ObjNewId = pObjNew->Id;
            Esop_CoverForEachCube( pCover, pCube )
            {
                pFaninNew = Ivy_ManToAigCube( pNew, pObjOld, pCube, vSupp );
                Ivy_ObjAddFanin( Ivy_ManObj(pNew, ObjNewId), Ivy_FanCreate(pFaninNew->Id, 0) );
            }
            // get the new object
            pObjNew = Ivy_ManObj(pNew, ObjNewId);
        }
    }
    pObjOld->TravId = pObjNew->Id;
    pObjNew->TravId = pObjOld->Id;
    return pObjNew;
}


/**Function*************************************************************

  Synopsis    [Returns constant 1 node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_ManToAigConst( Ivy_Man_t * pNew, int fConst1 )
{
    Ivy_Obj_t * pObjNew;
    pObjNew = Ivy_ObjCreateExt( pNew, IVY_ANDM );
    Ivy_ObjStartFanins( pObjNew, 1 );
    Ivy_ObjAddFanin( pObjNew, Ivy_FanCreate(0, !fConst1) );
    return pObjNew;
}

/**Function*************************************************************

  Synopsis    [Derives the decomposed network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Ivy_ManToAigCube( Ivy_Man_t * pNew, Ivy_Obj_t * pObjOld, Esop_Cube_t * pCube, Vec_Int_t * vSupp )
{
    Ivy_Obj_t * pObjNew, * pFaninOld;
    int i, Value;
    // if tautology cube, create constant 1 node
    if ( pCube->nLits == 0 )
        return Ivy_ManToAigConst( pNew, 1 );
    // create AND node
    pObjNew = Ivy_ObjCreateExt( pNew, IVY_ANDM );
    Ivy_ObjStartFanins( pObjNew, pCube->nLits );
    // add fanins
    for ( i = 0; i < (int)pCube->nVars; i++ )
    {
        Value = Esop_CubeGetVar( pCube, i );
        assert( Value != 0 );
        if ( Value == 3 )
            continue;
        pFaninOld = Ivy_ObjObj( pObjOld, Vec_IntEntry(vSupp, i) );
        Ivy_ObjAddFanin( pObjNew, Ivy_FanCreate( pFaninOld->TravId, Value==1 ) );
    }
    assert( Ivy_ObjFaninNum(pObjNew) == (int)pCube->nLits );
    return pObjNew;
}


/**Function*************************************************************

  Synopsis    [Recursively construct the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pla_ManToAigLutFuncs( Ivy_Man_t * pNew, Ivy_Man_t * pOld )
{
    Vec_Int_t * vSupp, * vFanins, * vNodes, * vTemp;
    Ivy_Obj_t * pObjOld, * pObjNew;
    unsigned * pComputed, * pTruth;
    int i, k, Counter = 0;
    // create mapping from the LUT nodes into truth table indices
    assert( pNew->vTruths == NULL );
    vNodes = Vec_IntAlloc( 100 );
    vTemp  = Vec_IntAlloc( 100 );
    pNew->vTruths = Vec_IntStart( Ivy_ManObjIdNext(pNew) );
    Ivy_ManForEachObj( pNew, pObjNew, i )
    {
        if ( Ivy_ObjIsLut(pObjNew) )
            Vec_IntWriteEntry( pNew->vTruths, i, 8 * Counter++ );
        else
            Vec_IntWriteEntry( pNew->vTruths, i, -1 );
    }
    // allocate memory
    pNew->pMemory = ALLOC( unsigned, 8 * Counter );
    memset( pNew->pMemory, 0, sizeof(unsigned) * 8 * Counter );
    // derive truth tables
    Ivy_ManForEachObj( pNew, pObjNew, i )
    {
        if ( !Ivy_ObjIsLut(pObjNew) )
            continue;
        pObjOld = Ivy_ManObj( pOld, pObjNew->TravId );
        vSupp = Ivy_ObjPlaStr(pObjOld)->vSupp; 
        assert( Vec_IntSize(vSupp) <= 8 );
        pTruth = Ivy_ObjGetTruth( pObjNew );
        pComputed = Ivy_ManCutTruth( pObjOld, vSupp, vNodes, vTemp );
        // check if the truth table is constant 0
        for ( k = 0; k < 8; k++ )
            if ( pComputed[k] )
                break;
        if ( k == 8 )
        {
            // create inverter
            for ( k = 0; k < 8; k++ )
                pComputed[k] = 0x55555555;
            // point it to the constant 1 node
            vFanins = Ivy_ObjGetFanins( pObjNew );
            Vec_IntClear( vFanins );
            Vec_IntPush( vFanins, Ivy_FanCreate(0, 1) );
        }
        memcpy( pTruth, pComputed, sizeof(unsigned) * 8 );
//        Extra_PrintBinary( stdout, pTruth, 16 ); printf( "\n" );
    }
    Vec_IntFree( vTemp );
    Vec_IntFree( vNodes );
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


