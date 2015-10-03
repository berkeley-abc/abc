/**CFile****************************************************************

  FileName    [sfmDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [SAT-based decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmDec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"
#include "bool/kit/kit.h"
#include "base/abc/abc.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define SFM_FAN_MAX 6

typedef struct Sfm_Dec_t_ Sfm_Dec_t;
struct Sfm_Dec_t_
{
    // parameters
    Sfm_Par_t *       pPars;       // parameters
    // library
    Vec_Int_t         vGateSizes;  // fanin counts
    Vec_Wrd_t         vGateFuncs;  // gate truth tables
    Vec_Wec_t         vGateCnfs;   // gate CNFs
    // objects
    int               iTarget;     // target node
    Vec_Int_t         vObjTypes;   // PI (1), PO (2)
    Vec_Int_t         vObjGates;   // functionality
    Vec_Wec_t         vObjFanins;  // fanin IDs
    // solver
    sat_solver *      pSat;        // reusable solver 
    Vec_Wec_t         vClauses;    // CNF clauses for the node
    Vec_Int_t         vPols[2];    // onset/offset polarity
    Vec_Int_t         vImpls[2];   // onset/offset implications
    Vec_Wrd_t         vSets[2];    // onset/offset patterns
    int               nPats[3];
    // temporary
    Vec_Int_t         vTemp;
    Vec_Int_t         vTemp2;
    // statistics
    abctime           timeWin;
    abctime           timeCnf;
    abctime           timeSat;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sfm_Dec_t * Sfm_DecStart()
{
    Sfm_Dec_t * p = ABC_CALLOC( Sfm_Dec_t, 1 );
    p->pSat = sat_solver_new();
    return p;
}
void Sfm_DecStop( Sfm_Dec_t * p )
{
    // library
    Vec_IntErase( &p->vGateSizes );
    Vec_WrdErase( &p->vGateFuncs );
    Vec_WecErase( &p->vGateCnfs );
    // objects
    Vec_IntErase( &p->vObjTypes );
    Vec_IntErase( &p->vObjGates );
    Vec_WecErase( &p->vObjFanins );
    // solver
    sat_solver_delete( p->pSat );
    Vec_WecErase( &p->vClauses );
    Vec_IntErase( &p->vPols[0] );
    Vec_IntErase( &p->vPols[1] );
    Vec_IntErase( &p->vImpls[0] );
    Vec_IntErase( &p->vImpls[1] );
    Vec_WrdErase( &p->vSets[0] );
    Vec_WrdErase( &p->vSets[1] );
    // temporary
    Vec_IntErase( &p->vTemp );
    Vec_IntErase( &p->vTemp2 );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_DecCreateCnf( Sfm_Dec_t * p )
{
    Vec_Str_t * vCnf, * vCnfBase;
    Vec_Int_t * vCover;
    word uTruth;
    int i, nCubes;
    vCnf = Vec_StrAlloc( 100 );
    vCover = Vec_IntAlloc( 100 );
    Vec_WecInit( &p->vGateCnfs, Vec_IntSize(&p->vGateSizes) );
    Vec_WrdForEachEntry( &p->vGateFuncs, uTruth, i )
    {
        nCubes = Sfm_TruthToCnf( uTruth, Vec_IntEntry(&p->vGateSizes, i), vCover, vCnf );
        vCnfBase = (Vec_Str_t *)Vec_WecEntry( &p->vGateCnfs, i );
        Vec_StrGrow( vCnfBase, Vec_StrSize(vCnf) );
        memcpy( Vec_StrArray(vCnfBase), Vec_StrArray(vCnf), Vec_StrSize(vCnf) );
        vCnfBase->nSize = Vec_StrSize(vCnf);
    }
    Vec_IntFree( vCover );
    Vec_StrFree( vCnf );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_DecCreateAigLibrary( Sfm_Dec_t * p )
{
    // const0
    Vec_IntPush( &p->vGateSizes, 0 );
    Vec_WrdPush( &p->vGateFuncs, 0 );
    // const1
    Vec_IntPush( &p->vGateSizes, 0 );
    Vec_WrdPush( &p->vGateFuncs, ~(word)0 );
    // buffer
    Vec_IntPush( &p->vGateSizes, 1 );
    Vec_WrdPush( &p->vGateFuncs, ABC_CONST(0xAAAAAAAAAAAAAAAA) );
    // inverter
    Vec_IntPush( &p->vGateSizes, 1 );
    Vec_WrdPush( &p->vGateFuncs, ABC_CONST(0x5555555555555555) );
    // and00
    Vec_IntPush( &p->vGateSizes, 2 );
    Vec_WrdPush( &p->vGateFuncs, ABC_CONST(0xCCCCCCCCCCCCCCCC) & ABC_CONST(0xAAAAAAAAAAAAAAAA) );
    // and01
    Vec_IntPush( &p->vGateSizes, 2 );
    Vec_WrdPush( &p->vGateFuncs, ABC_CONST(0xCCCCCCCCCCCCCCCC) &~ABC_CONST(0xAAAAAAAAAAAAAAAA) );
    // and10
    Vec_IntPush( &p->vGateSizes, 2 );
    Vec_WrdPush( &p->vGateFuncs,~ABC_CONST(0xCCCCCCCCCCCCCCCC) & ABC_CONST(0xAAAAAAAAAAAAAAAA) );
    // and11
    Vec_IntPush( &p->vGateSizes, 2 );
    Vec_WrdPush( &p->vGateFuncs,~ABC_CONST(0xCCCCCCCCCCCCCCCC) &~ABC_CONST(0xAAAAAAAAAAAAAAAA) );
/*
    // xor
    Vec_IntPush( &p->vGateSizes, 2 );
    Vec_WrdPush( &p->vGateFuncs, ABC_CONST(0xCCCCCCCCCCCCCCCC) ^ ABC_CONST(0xAAAAAAAAAAAAAAAA) );
    // xnor
    Vec_IntPush( &p->vGateSizes, 2 );
    Vec_WrdPush( &p->vGateFuncs, ABC_CONST(0xCCCCCCCCCCCCCCCC) ^~ABC_CONST(0xAAAAAAAAAAAAAAAA) );
    // mux
    Vec_IntPush( &p->vGateSizes, 3 );
    Vec_WrdPush( &p->vGateFuncs, (ABC_CONST(0xF0F0F0F0F0F0F0F0) & ABC_CONST(0xCCCCCCCCCCCCCCCC)) | (ABC_CONST(0x0F0F0F0F0F0F0F0F) & ABC_CONST(0xAAAAAAAAAAAAAAAA)) );
*/
    // derive CNF for these functions
    Sfm_DecCreateCnf( p );
}

void Vec_IntLift( Vec_Int_t * p, int Amount )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        p->pArray[i] += Amount;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_DecPrepareSolver( Sfm_Dec_t * p )
{
    abctime clk = Abc_Clock();
    Vec_Int_t * vLevel, * vClause;
    int i, k, Type, Gate, iObj, RetValue;
    int nSatVars = 2 * Vec_IntSize(&p->vObjTypes) - p->iTarget - 1;
    assert( Vec_IntSize(&p->vObjTypes) == Vec_IntSize(&p->vObjGates) );
    assert( p->iTarget < Vec_IntSize(&p->vObjTypes) );
    // collect variables of root nodes
    Vec_IntClear( &p->vTemp );
    Vec_IntForEachEntryStart( &p->vObjTypes, Type, i, p->iTarget )
        if ( Type == 2 )
            Vec_IntPush( &p->vTemp, i );
    assert( Vec_IntSize(&p->vTemp) > 0 );
    // create SAT solver
    sat_solver_restart( p->pSat );
    sat_solver_setnvars( p->pSat, nSatVars + Vec_IntSize(&p->vTemp) );
    // add CNF clauses for the TFI
    Vec_IntForEachEntryStop( &p->vObjTypes, Type, i, p->iTarget + 1 )
    {
        if ( Type == 1 )
            continue;
        // generate CNF 
        Gate = Vec_IntEntry( &p->vObjGates, i );
        vLevel = Vec_WecEntry( &p->vObjFanins, i );
        Sfm_TranslateCnf( &p->vClauses, (Vec_Str_t *)Vec_WecEntry(&p->vGateCnfs, Gate), vLevel, -1 );
        // add clauses
        Vec_WecForEachLevel( &p->vClauses, vClause, k )
        {
            if ( Vec_IntSize(vClause) == 0 )
                break;
            RetValue = sat_solver_addclause( p->pSat, Vec_IntArray(vClause), Vec_IntArray(vClause) + Vec_IntSize(vClause) );
            if ( RetValue == 0 )
                return 0;
        }
    }
    // add CNF clauses for the TFO
    Vec_IntForEachEntryStart( &p->vObjTypes, Type, i, p->iTarget + 1 )
    {
        assert( Type != 1 );
        // generate CNF 
        Gate = Vec_IntEntry( &p->vObjGates, i );
        vLevel = Vec_WecEntry( &p->vObjFanins, i );
        Vec_IntLift( vLevel, Vec_IntSize(&p->vObjTypes) );
        Sfm_TranslateCnf( &p->vClauses, (Vec_Str_t *)Vec_WecEntry(&p->vGateCnfs, Gate), vLevel, p->iTarget );
        Vec_IntLift( vLevel, Vec_IntSize(&p->vObjTypes) );
        // add clauses
        Vec_WecForEachLevel( &p->vClauses, vClause, k )
        {
            if ( Vec_IntSize(vClause) == 0 )
                break;
            RetValue = sat_solver_addclause( p->pSat, Vec_IntArray(vClause), Vec_IntArray(vClause) + Vec_IntSize(vClause) );
            if ( RetValue == 0 )
                return 0;
        }
    }
    if ( p->iTarget + 1 < Vec_IntSize(&p->vObjTypes) )
    {
        // create XOR clauses for the roots
        Vec_IntForEachEntry( &p->vTemp, iObj, i )
        {
            sat_solver_add_xor( p->pSat, iObj, 2*iObj + Vec_IntSize(&p->vObjTypes) - p->iTarget - 1, nSatVars++, 0 );
            Vec_IntWriteEntry( &p->vTemp, i, Abc_Var2Lit(nSatVars-1, 0) );
        }
        // make OR clause for the last nRoots variables
        RetValue = sat_solver_addclause( p->pSat, Vec_IntArray(&p->vTemp), Vec_IntLimit(&p->vTemp) );
        if ( RetValue == 0 )
            return 0;
        assert( nSatVars == sat_solver_nvars(p->pSat) );
    }
    else assert( Vec_IntSize(&p->vTemp) == 1 );
    // finalize
    RetValue = sat_solver_simplify( p->pSat );
    p->timeCnf += Abc_Clock() - clk;
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_DecPeformDec( Sfm_Dec_t * p )
{
    int fVerbose = 1;
    int nBTLimit = 0;
    abctime clk = Abc_Clock();
    int i, k, c, status, Lits[2];
    // check stuck-at-0/1 (on/off-set empty)
    p->nPats[0] = p->nPats[1] = 0;
    for ( c = 0; c < 2; c++ )
    {
        Lits[0] = Abc_Var2Lit( p->iTarget, c );
        status = sat_solver_solve( p->pSat, Lits, Lits + 1, nBTLimit, 0, 0, 0 );
        if ( status == l_Undef )
            return 0;
        if ( status == l_False )
        {
            Vec_IntPush( &p->vObjTypes, 0 );
            Vec_IntPush( &p->vObjGates, c );
            Vec_WecPushLevel( &p->vObjFanins );
            return 1;
        }
        assert( status == l_True );
        // record this status
        for ( i = 0; i < p->iTarget; i++ )
        {
            Vec_IntPush( &p->vPols[c], sat_solver_var_value(p->pSat, i) );
            Vec_WrdPush( &p->vSets[c], 0 );
        }
        p->nPats[c]++;
    }
    // proceed checking divisors based on their values
    for ( c = 0; c < 2; c++ )
    {
        Lits[0] = Abc_Var2Lit( p->iTarget, c );
        for ( i = 0; i < p->iTarget; i++ )
        {
            if ( Vec_WrdEntry(&p->vSets[c], i) ) // diff value is possible
                continue;
            Lits[1] = Abc_Var2Lit( i, Vec_IntEntry(&p->vPols[c], i) );
            status = sat_solver_solve( p->pSat, Lits, Lits + 2, nBTLimit, 0, 0, 0 );
            if ( status == l_Undef )
                return 0;
            if ( status == l_False )
            {
                Vec_IntPush( &p->vImpls[c], i );
                continue;
            }
            assert( status == l_True );
            // record this status
            for ( i = 0; i < p->iTarget; i++ )
                if ( sat_solver_var_value(p->pSat, i) ^ Vec_IntEntry(&p->vPols[c], i) )
                    *Vec_WrdEntryP(&p->vSets[c], i) |= ((word)1 << p->nPats[c]);
            p->nPats[c]++;
        }
    }
    // print the results
    if ( fVerbose )
    for ( c = 0; c < 2; c++ )
    {
        printf( "\nON-SET reference vertex:\n" );
        for ( i = 0; i < p->iTarget; i++ )
            printf( "%d", Vec_IntEntry(&p->vPols[c], i) );
        printf( "\n" );
        printf( "     " );
        for ( i = 0; i < p->iTarget; i++ )
            printf( "%d", i % 10 );
        printf( "\n" );
        for ( k = 0; k < p->nPats[c]; k++ )
        {
            printf( "%2d : ", k );
            for ( i = 0; i < p->iTarget; i++ )
                printf( "%d", (int)((Vec_WrdEntry(&p->vSets[c], i) >> k) & 1) );
            printf( "\n" );
        }
    }
    p->timeSat += Abc_Clock() - clk;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Testbench for the new AIG minimization.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDfsReverseOne_rec( Abc_Obj_t * pNode, Vec_Int_t * vNodes )
{
    Abc_Obj_t * pFanout; int i;
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    Abc_NodeSetTravIdCurrent( pNode );
    if ( Abc_ObjIsCo(pNode) )
    {
        Vec_IntPush( vNodes, Abc_ObjId(pNode) );
        return;
    }
    assert( Abc_ObjIsNode( pNode ) );
    Abc_ObjForEachFanout( pNode, pFanout, i )
        Abc_NtkDfsReverseOne_rec( pFanout, vNodes );
    Vec_IntPush( vNodes, Abc_ObjId(pNode) );
}
void Abc_NtkDfsOne_rec( Abc_Obj_t * pNode, Vec_Int_t * vMap, Vec_Int_t * vTypes )
{
    Abc_Obj_t * pFanin; int i;
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    Abc_NodeSetTravIdCurrent( pNode );
    if ( Abc_ObjIsCi(pNode) )
    {
        pNode->iTemp = Vec_IntSize(vMap);
        Vec_IntPush( vMap, Abc_ObjId(pNode) );
        Vec_IntPush( vTypes, 1 );
        return;
    }
    assert( Abc_ObjIsNode(pNode) );
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_NtkDfsOne_rec( pFanin, vMap, vTypes );
    pNode->iTemp = Vec_IntSize(vMap);
    Vec_IntPush( vMap, Abc_ObjId(pNode) );
    Vec_IntPush( vTypes, 0 );
}
int Sfm_DecExtract( Abc_Ntk_t * pNtk, int iNode, Vec_Int_t * vTypes, Vec_Int_t * vGates, Vec_Wec_t * vFanins, Vec_Int_t * vMap, Vec_Int_t * vTemp )
{
    Abc_Obj_t * pNode = Abc_NtkObj( pNtk, iNode );
    Vec_Int_t * vLevel;
    int i, iObj, iTarget;
    assert( Abc_ObjIsNode(pNode) );
    // collect transitive fanout
    Vec_IntClear( vTemp );
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkDfsReverseOne_rec( pNode, vTemp );
    // collect transitive fanin
    Vec_IntClear( vMap );
    Vec_IntClear( vTypes );
    Abc_NtkDfsOne_rec( pNode, vMap, vTypes );
    Vec_IntPop( vMap );
    Vec_IntPop( vTypes );
    assert( Vec_IntSize(vMap) == Vec_IntSize(vTypes) );
    // remember target node
    iTarget = Vec_IntSize( vMap );
    // add transitive fanout
    Vec_IntForEachEntryReverse( vTemp, iObj, i )
    {
        pNode = Abc_NtkObj( pNtk, iObj );
        if ( Abc_ObjIsCo(pNode) )
        {
            assert( Vec_IntEntry(vTypes, Abc_ObjFanin0(pNode)->iTemp) == 0 );
            Vec_IntWriteEntry( vTypes, Abc_ObjFanin0(pNode)->iTemp, 2 );
            continue;
        }
        pNode->iTemp = Vec_IntSize(vMap);
        Vec_IntPush( vMap, Abc_ObjId(pNode) );
        Vec_IntPush( vTypes, 0 );
    }
    assert( Vec_IntSize(vMap) == Vec_IntSize(vTypes) );
    // create gates and fanins
    Vec_IntClear( vGates );
    Vec_WecClear( vFanins );
    Vec_IntForEachEntry( vMap, iObj, i )
    {
        vLevel = Vec_WecPushLevel( vFanins );
        pNode = Abc_NtkObj( pNtk, iObj );
        if ( Abc_ObjIsCi(pNode) )
        {
            Vec_IntPush( vGates, -1 );
            continue;
        }
        assert( Abc_ObjFaninNum(pNode) == 2 );
             if ( !Abc_ObjFaninC0(pNode) && !Abc_ObjFaninC1(pNode) )
            Vec_IntPush( vGates, 4 );
        else if ( !Abc_ObjFaninC0(pNode) &&  Abc_ObjFaninC1(pNode) )
            Vec_IntPush( vGates, 5 );
        else if (  Abc_ObjFaninC0(pNode) && !Abc_ObjFaninC1(pNode) )
            Vec_IntPush( vGates, 6 );
        else //if ( Abc_ObjFaninC0(pNode) && Abc_ObjFaninC1(pNode) )
            Vec_IntPush( vGates, 7 );
        Vec_IntPush( vLevel, Abc_ObjFanin0(pNode)->iTemp );
        Vec_IntPush( vLevel, Abc_ObjFanin1(pNode)->iTemp );
    }
    return iTarget;
}
void Sfm_DecInsert( Abc_Ntk_t * pNtk, int iNode, int Limit, Vec_Int_t * vTypes, Vec_Int_t * vGates, Vec_Wec_t * vFanins, Vec_Int_t * vMap )
{
    Abc_Obj_t * pTarget = Abc_NtkObj( pNtk, iNode );
    Vec_Int_t * vLevel;
    Abc_Obj_t * pObjNew = NULL; 
    int i, k, iObj, Gate;
    assert( Limit < Vec_IntSize(vTypes) );
    Vec_IntForEachEntryStart( vGates, Gate, i, Limit )
    {
        assert( Gate >= 0 && Gate <= 7 );
        vLevel = Vec_WecEntry( vFanins, i );
        if ( Gate == 0 )
            pObjNew = Abc_NtkCreateNodeConst0( pNtk );
        else if ( Gate == 1 )
            pObjNew = Abc_NtkCreateNodeConst1( pNtk );
        else if ( Gate == 2 )
            pObjNew = Abc_NtkCreateNodeBuf( pNtk, Abc_NtkObj(pNtk, Vec_IntEntry(vMap, Vec_IntEntry(vLevel,0))) );
        else if ( Gate == 3 )
            pObjNew = Abc_NtkCreateNodeInv( pNtk, Abc_NtkObj(pNtk, Vec_IntEntry(vMap, Vec_IntEntry(vLevel,0))) );
        else // if ( Gate >= 4 )
        {
            pObjNew = Abc_NtkCreateNode( pNtk );
            Vec_IntForEachEntry( vLevel, iObj, k )
                Abc_ObjAddFanin( pObjNew, Abc_NtkObj(pNtk, Vec_IntEntry(vMap, iObj)) );
            pObjNew->pData = NULL; // SELECTION FUNCTION
        }
        // transfer the fanout
        Abc_ObjTransferFanout( pTarget, pObjNew );
        assert( Abc_ObjFanoutNum(pTarget) == 0 );
        Abc_NtkDeleteObj_rec( pTarget, 1 );
    }
}
void Sfm_DecTestBench( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vMap, * vTemp;
    Abc_Obj_t * pObj; int i, Limit;
    Sfm_Dec_t * p = Sfm_DecStart();
    Sfm_DecCreateAigLibrary( p );
    assert( Abc_NtkIsSopLogic(pNtk) );
    assert( Abc_NtkGetFaninMax(pNtk) <= 2 );
    vMap  = Vec_IntAlloc( Abc_NtkObjNumMax(pNtk) ); // Sfm->Ntk
    vTemp = Vec_IntAlloc( Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        p->iTarget = Sfm_DecExtract( pNtk, i, &p->vObjTypes, &p->vObjGates, &p->vObjFanins, vMap, vTemp );
        Limit = Vec_IntSize( &p->vObjTypes );
        if ( !Sfm_DecPrepareSolver( p ) )
            continue;
        if ( !Sfm_DecPeformDec( p ) )
            continue;
        Sfm_DecInsert( pNtk, p->iTarget, Limit, &p->vObjTypes, &p->vObjGates, &p->vObjFanins, vMap );
    }
    Vec_IntFree( vMap );
    Vec_IntFree( vTemp );
    Sfm_DecStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

