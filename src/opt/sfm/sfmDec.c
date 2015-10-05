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
#include "misc/st/st.h"
#include "map/mio/mio.h"
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
    Vec_Ptr_t         vGateHands;  // gate handles
    int               GateConst0;  // special gates
    int               GateConst1;  // special gates
    int               GateBuffer;  // special gates
    int               GateInvert;  // special gates
    // objects
    int               iTarget;     // target node
    Vec_Int_t         vObjTypes;   // PI (1), PO (2)
    Vec_Int_t         vObjGates;   // functionality
    Vec_Wec_t         vObjFanins;  // fanin IDs
    // solver
    sat_solver *      pSat;        // reusable solver 
    Vec_Wec_t         vClauses;    // CNF clauses for the node
    Vec_Int_t         vPols[2];    // onset/offset polarity
    Vec_Int_t         vTaken[2];   // onset/offset implied nodes
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
    Vec_PtrErase( &p->vGateHands );
    // objects
    Vec_IntErase( &p->vObjTypes );
    Vec_IntErase( &p->vObjGates );
    Vec_WecErase( &p->vObjFanins );
    // solver
    sat_solver_delete( p->pSat );
    Vec_WecErase( &p->vClauses );
    Vec_IntErase( &p->vPols[0] );
    Vec_IntErase( &p->vPols[1] );
    Vec_IntErase( &p->vTaken[0] );
    Vec_IntErase( &p->vTaken[1] );
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
int Sfm_DecPrepareSolver( Sfm_Dec_t * p )
{
    abctime clk = Abc_Clock();
    Vec_Int_t * vRoots = &p->vTemp;
    Vec_Int_t * vFaninVars = &p->vTemp2;
    Vec_Int_t * vLevel, * vClause;
    int i, k, Type, Gate, iObj, RetValue;
    int nTfiSize = p->iTarget + 1; // including node
    int nWinSize = Vec_IntSize(&p->vObjTypes);
    int nSatVars = 2 * nWinSize - nTfiSize;
    assert( nWinSize == Vec_IntSize(&p->vObjGates) );
    assert( p->iTarget < nWinSize );
    // collect variables of root nodes
    Vec_IntClear( vRoots );
    Vec_IntForEachEntryStart( &p->vObjTypes, Type, i, p->iTarget )
        if ( Type == 2 )
            Vec_IntPush( vRoots, i );
    assert( Vec_IntSize(vRoots) > 0 );
    // create SAT solver
    sat_solver_restart( p->pSat );
    sat_solver_setnvars( p->pSat, nSatVars + Vec_IntSize(vRoots) );
    // add CNF clauses for the TFI
    Vec_IntForEachEntryStop( &p->vObjTypes, Type, i, nTfiSize )
    {
        if ( Type == 1 )
            continue;
        vLevel = Vec_WecEntry( &p->vObjFanins, i );
        // generate CNF 
        Gate = Vec_IntEntry( &p->vObjGates, i );
        Vec_IntPush( vLevel, i );
        Sfm_TranslateCnf( &p->vClauses, (Vec_Str_t *)Vec_WecEntry(&p->vGateCnfs, Gate), vLevel, -1 );
        Vec_IntPop( vLevel );
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
    Vec_IntForEachEntryStart( &p->vObjTypes, Type, i, nTfiSize )
    {
        assert( Type != 1 );
        vLevel = Vec_WecEntry( &p->vObjFanins, i );
        Vec_IntClear( vFaninVars );
        Vec_IntForEachEntry( vLevel, iObj, k )
            Vec_IntPush( vFaninVars, iObj <= p->iTarget ? iObj : iObj + nWinSize - nTfiSize );
        Vec_IntPush( vFaninVars, i + nWinSize - nTfiSize );
        // generate CNF 
        Gate  = Vec_IntEntry( &p->vObjGates, i );
        Sfm_TranslateCnf( &p->vClauses, (Vec_Str_t *)Vec_WecEntry(&p->vGateCnfs, Gate), vFaninVars, p->iTarget );
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
    if ( p->iTarget + 1 < nWinSize )
    {
        // create XOR clauses for the roots
        Vec_IntForEachEntry( vRoots, iObj, i )
        {
            sat_solver_add_xor( p->pSat, iObj, iObj + nWinSize - nTfiSize, nSatVars++, 0 );
            Vec_IntWriteEntry( vRoots, i, Abc_Var2Lit(nSatVars-1, 0) );
        }
        // make OR clause for the last nRoots variables
        RetValue = sat_solver_addclause( p->pSat, Vec_IntArray(vRoots), Vec_IntLimit(vRoots) );
        if ( RetValue == 0 )
            return 0;
        assert( nSatVars == sat_solver_nvars(p->pSat) );
    }
    else assert( Vec_IntSize(vRoots) == 1 );
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
    int i, j, k, c, n, Pol, Pol2, Entry, Entry2, status, Lits[3];
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
            Vec_IntPush( &p->vObjGates, c ? p->GateConst1 : p->GateConst0 );
            Vec_WecPushLevel( &p->vObjFanins );
            return 1;
        }
        assert( status == l_True );
        // record this status
        for ( i = 0; i <= p->iTarget; i++ )
        {
            Vec_IntPush( &p->vPols[c], sat_solver_var_value(p->pSat, i) );
            Vec_WrdPush( &p->vSets[c], 0 );
        }
        p->nPats[c]++;
        Vec_IntClear( &p->vImpls[c] );
        Vec_IntFill( &p->vTaken[c], p->iTarget, 0 );
    }
    // proceed checking divisors based on their values
    for ( c = 0; c < 2; c++ )
    {
        Lits[0] = Abc_Var2Lit( p->iTarget, c );
        for ( i = 0; i < p->iTarget; i++ )
        {
            if ( Vec_WrdEntry(&p->vSets[c], i) ) // diff value is possible
                continue;
            Pol = Vec_IntEntry(&p->vPols[c], i);
            Lits[1] = Abc_Var2Lit( i, Pol );
            status = sat_solver_solve( p->pSat, Lits, Lits + 2, nBTLimit, 0, 0, 0 );
            if ( status == l_Undef )
                return 0;
            if ( status == l_False )
            {
                Vec_IntWriteEntry( &p->vTaken[c], i, 1 );
                Vec_IntPushTwo( &p->vImpls[c], Abc_Var2Lit(i, Pol), -1 );
                continue;
            }
            assert( status == l_True );
            if ( p->nPats[c] == 64 )
                continue;
            // record this status
            for ( k = 0; k <= p->iTarget; k++ )
                if ( sat_solver_var_value(p->pSat, k) ^ Vec_IntEntry(&p->vPols[c], k) )
                    *Vec_WrdEntryP(&p->vSets[c], k) |= ((word)1 << p->nPats[c]);
            p->nPats[c]++;
        }
    }
    // proceed checking divisor pairs
    for ( c = 0; c < 2; c++ )
    {
        Lits[0] = Abc_Var2Lit( p->iTarget, c );
        for ( i = 0; i < p->iTarget; i++ )
        if ( !Vec_IntEntry(&p->vTaken[c], i) )
        for ( j = 0; j < i; j++ )
        if ( !Vec_IntEntry(&p->vTaken[c], j) )
        {
            word SignI = Vec_WrdEntry(&p->vSets[c], i);
            word SignJ = Vec_WrdEntry(&p->vSets[c], j);
            for ( n = 0; n < 3; n++ )
            {
                if ( ((n&1) ? ~SignI : SignI) & ((n>>1) ? ~SignJ : SignJ) ) // diff value is possible
                    continue;
                Pol = Vec_IntEntry(&p->vPols[c], i) ^ (n&1);
                Pol2 = Vec_IntEntry(&p->vPols[c], j) ^ (n>>1);
                Lits[1] = Abc_Var2Lit( i, Pol );
                Lits[2] = Abc_Var2Lit( j, Pol2 );
                status = sat_solver_solve( p->pSat, Lits, Lits + 3, nBTLimit, 0, 0, 0 );
                if ( status == l_Undef )
                    return 0;
                if ( status == l_False )
                {
                    Vec_IntPushTwo( &p->vImpls[c], Abc_Var2Lit(i, Pol), Abc_Var2Lit(j, Pol2) );
                    continue;
                }
                assert( status == l_True );
                if ( p->nPats[c] == 64 )
                    continue;
                // record this status
                for ( k = 0; k <= p->iTarget; k++ )
                    if ( sat_solver_var_value(p->pSat, k) ^ Vec_IntEntry(&p->vPols[c], k) )
                        *Vec_WrdEntryP(&p->vSets[c], k) |= ((word)1 << p->nPats[c]);
                p->nPats[c]++;
            }
        }
    }

    // print the results
    if ( fVerbose )
    for ( c = 0; c < 2; c++ )
    {
        Vec_Int_t * vLevel = Vec_WecEntry( &p->vObjFanins, p->iTarget );
        printf( "\n%s-SET of object %d with gate \"%s\" and fanins: ", c ? "OFF": "ON", p->iTarget, Mio_GateReadName((Mio_Gate_t *)Vec_PtrEntry(&p->vGateHands, Vec_IntEntry(&p->vObjGates,p->iTarget))) );
        Vec_IntForEachEntry( vLevel, Entry, i )
            printf( "%d ", Entry );
        printf( "\n" );

        printf( "Implications: " );
        Vec_IntForEachEntryDouble( &p->vImpls[c], Entry, Entry2, i )
        {
            if ( Entry2 == -1 )
                printf( "%s%d ", Abc_LitIsCompl(Entry)? "!":"", Abc_Lit2Var(Entry) );
            else
                printf( "%s%d:%s%d ", Abc_LitIsCompl(Entry)? "!":"", Abc_Lit2Var(Entry), Abc_LitIsCompl(Entry2)? "!":"", Abc_Lit2Var(Entry2) );
        }
        printf( "\n" );
        printf( "     " );
        for ( i = 0; i <= p->iTarget; i++ )
            printf( "%d", Vec_IntEntry(&p->vPols[c], i) );
        printf( "\n\n" );
        printf( "     " );
        for ( i = 0; i <= p->iTarget; i++ )
            printf( "%d", i % 10 );
        printf( "\n" );
        for ( k = 0; k < p->nPats[c]; k++ )
        {
            printf( "%2d : ", k );
            for ( i = 0; i <= p->iTarget; i++ )
                printf( "%d", (int)((Vec_WrdEntry(&p->vSets[c], i) >> k) & 1) );
            printf( "\n" );
        }
        printf( "\n" );
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
void Abc_NtkDfsReverseOne_rec( Abc_Obj_t * pNode, Vec_Int_t * vTfo )
{
    Abc_Obj_t * pFanout; int i;
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    Abc_NodeSetTravIdCurrent( pNode );
    if ( Abc_ObjIsCo(pNode) )
    {
        Vec_IntPush( vTfo, Abc_ObjId(pNode) );
        return;
    }
    assert( Abc_ObjIsNode( pNode ) );
    Abc_ObjForEachFanout( pNode, pFanout, i )
        Abc_NtkDfsReverseOne_rec( pFanout, vTfo );
    Vec_IntPush( vTfo, Abc_ObjId(pNode) );
}
void Abc_NtkDfsOne_rec( Abc_Obj_t * pNode, Vec_Int_t * vTfi, Vec_Int_t * vTypes )
{
    Abc_Obj_t * pFanin; int i;
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    Abc_NodeSetTravIdCurrent( pNode );
    if ( Abc_ObjIsCi(pNode) )
    {
        pNode->iTemp = Vec_IntSize(vTfi);
        Vec_IntPush( vTfi, Abc_ObjId(pNode) );
        Vec_IntPush( vTypes, 1 );
        return;
    }
    assert( Abc_ObjIsNode(pNode) );
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_NtkDfsOne_rec( pFanin, vTfi, vTypes );
    pNode->iTemp = Vec_IntSize(vTfi);
    Vec_IntPush( vTfi, Abc_ObjId(pNode) );
    Vec_IntPush( vTypes, 0 );
}
int Sfm_DecExtract( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, Vec_Int_t * vTypes, Vec_Int_t * vGates, Vec_Wec_t * vFanins, Vec_Int_t * vMap, Vec_Int_t * vTfo )
{
    Vec_Int_t * vLevel;
    Abc_Obj_t * pFanin;
    int i, k, iObj, iTarget;
    assert( Abc_ObjIsNode(pNode) );
    // collect transitive fanout including COs
    Vec_IntClear( vTfo );
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkDfsReverseOne_rec( pNode, vTfo );
    // collect transitive fanin
    Vec_IntClear( vMap );
    Vec_IntClear( vTypes );
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkDfsOne_rec( pNode, vMap, vTypes );
    Vec_IntPop( vMap );
    Vec_IntPop( vTypes );
    assert( Vec_IntSize(vMap) == Vec_IntSize(vTypes) );
    // remember target node
    iTarget = Vec_IntSize( vMap );
    // add transitive fanout
    Vec_IntForEachEntryReverse( vTfo, iObj, i )
    {
        pNode = Abc_NtkObj( pNtk, iObj );
        if ( Abc_ObjIsCo(pNode) )
        {
            assert( Vec_IntEntry(vTypes, Abc_ObjFanin0(pNode)->iTemp) == 0 ); // CO points to a unique node
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
        Abc_ObjForEachFanin( pNode, pFanin, k )
            Vec_IntPush( vLevel, pFanin->iTemp );
        Vec_IntPush( vGates, Mio_GateReadValue((Mio_Gate_t *)pNode->pData) );
    }
    return iTarget;
}
void Sfm_DecInsert( Abc_Ntk_t * pNtk, int iNode, int Limit, Vec_Int_t * vTypes, Vec_Int_t * vGates, Vec_Wec_t * vFanins, Vec_Int_t * vMap, Vec_Ptr_t * vGateHandles )
{
    Abc_Obj_t * pTarget = Abc_NtkObj( pNtk, iNode );
    Abc_Obj_t * pObjNew = NULL; 
    int i, k, iObj, Gate;
    // assuming that new gates are appended at the end
    assert( Limit < Vec_IntSize(vTypes) );
    // introduce new gates
    Vec_IntForEachEntryStart( vGates, Gate, i, Limit )
    {
        Vec_Int_t * vLevel = Vec_WecEntry( vFanins, i );
        pObjNew = Abc_NtkCreateNode( pNtk );
        Vec_IntForEachEntry( vLevel, iObj, k )
            Abc_ObjAddFanin( pObjNew, Abc_NtkObj(pNtk, Vec_IntEntry(vMap, iObj)) );
        pObjNew->pData = Vec_PtrEntry( vGateHandles, Gate );
    }
    // transfer the fanout
    Abc_ObjTransferFanout( pTarget, pObjNew );
    assert( Abc_ObjFanoutNum(pTarget) == 0 );
    Abc_NtkDeleteObj_rec( pTarget, 1 );
}
void Sfm_DecTestBench( Abc_Ntk_t * pNtk, int iNode )
{
    extern void Sfm_LibPreprocess( Mio_Library_t * pLib, Vec_Int_t * vGateSizes, Vec_Wrd_t * vGateFuncs, Vec_Wec_t * vGateCnfs, Vec_Ptr_t * vGateHands );
    Mio_Library_t * pLib = (Mio_Library_t *)pNtk->pManFunc;
    Sfm_Dec_t * p = Sfm_DecStart();
    Vec_Int_t * vMap = Vec_IntAlloc( Abc_NtkObjNumMax(pNtk) ); // Sfm->Ntk
    Abc_Obj_t * pObj; 
    int i, Limit;
    // enter library
    assert( Abc_NtkIsMappedLogic(pNtk) );
    Sfm_LibPreprocess( pLib, &p->vGateSizes, &p->vGateFuncs, &p->vGateCnfs, &p->vGateHands );
    p->GateConst0 = Mio_GateReadValue( Mio_LibraryReadConst0(pLib) );
    p->GateConst1 = Mio_GateReadValue( Mio_LibraryReadConst1(pLib) );
    p->GateBuffer = Mio_GateReadValue( Mio_LibraryReadBuf(pLib) );
    p->GateInvert = Mio_GateReadValue( Mio_LibraryReadInv(pLib) );
    // iterate over nodes
//    Abc_NtkForEachNode( pNtk, pObj, i )
    for ( ; pObj = Abc_NtkObj(pNtk, iNode);  )
    {
        p->iTarget = Sfm_DecExtract( pNtk, pObj, &p->vObjTypes, &p->vObjGates, &p->vObjFanins, vMap, &p->vTemp );
        Limit = Vec_IntSize( &p->vObjTypes );
        if ( !Sfm_DecPrepareSolver( p ) )
            continue;
        if ( !Sfm_DecPeformDec( p ) )
            continue;
//        Sfm_DecInsert( pNtk, p->iTarget, Limit, &p->vObjTypes, &p->vObjGates, &p->vObjFanins, vMap, vGateHandles );

        break;
    }
    Vec_IntFree( vMap );
    Sfm_DecStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

