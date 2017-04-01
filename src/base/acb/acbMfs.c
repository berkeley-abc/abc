/**CFile****************************************************************

  FileName    [abcMfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Optimization with don't-cares.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 21, 2015.]

  Revision    [$Id: abcMfs.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acb.h"
#include "bool/kit/kit.h"
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"
#include "misc/util/utilTruth.h"
#include "acbPar.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derive CNF for nodes in the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_DeriveCnfFromTruth( word Truth, int nVars, Vec_Int_t * vCover, Vec_Str_t * vCnf )
{
    Vec_StrClear( vCnf );
    if ( Truth == 0 || ~Truth == 0 )
    {
//        assert( nVars == 0 );
        Vec_StrPush( vCnf, (char)(Truth == 0) );
        Vec_StrPush( vCnf, (char)-1 );
        return 1;
    }
    else 
    {
        int i, k, c, RetValue, Literal, Cube, nCubes = 0;
        assert( nVars > 0 );
        for ( c = 0; c < 2; c ++ )
        {
            Truth = c ? ~Truth : Truth;
            RetValue = Kit_TruthIsop( (unsigned *)&Truth, nVars, vCover, 0 );
            assert( RetValue == 0 );
            nCubes += Vec_IntSize( vCover );
            Vec_IntForEachEntry( vCover, Cube, i )
            {
                for ( k = 0; k < nVars; k++ )
                {
                    Literal = 3 & (Cube >> (k << 1));
                    if ( Literal == 1 )      // '0'  -> pos lit
                        Vec_StrPush( vCnf, (char)Abc_Var2Lit(k, 0) );
                    else if ( Literal == 2 ) // '1'  -> neg lit
                        Vec_StrPush( vCnf, (char)Abc_Var2Lit(k, 1) );
                    else if ( Literal != 0 )
                        assert( 0 );
                }
                Vec_StrPush( vCnf, (char)Abc_Var2Lit(nVars, c) );
                Vec_StrPush( vCnf, (char)-1 );
            }
        }
        return nCubes;
    }
}
Vec_Wec_t * Acb_DeriveCnfForWindow( Acb_Ntk_t * p, Vec_Int_t * vWin, int PivotVar )
{
    Vec_Wec_t * vCnfs = &p->vCnfs;
    Vec_Str_t * vCnfBase, * vCnf = NULL; int i, iObj;
    assert( Vec_WecSize(vCnfs) == Acb_NtkObjNumMax(p) );
    Vec_IntForEachEntry( vWin, iObj, i )
    {
        if ( Abc_LitIsCompl(iObj) && i < PivotVar )
            continue;
        iObj = Abc_Lit2Var(iObj);
        vCnfBase = Acb_ObjCnfs( p, iObj );
        if ( Vec_StrSize(vCnfBase) > 0 )
            continue;
        if ( vCnf == NULL )
            vCnf = Vec_StrAlloc( 1000 );
        Acb_DeriveCnfFromTruth( Acb_ObjTruth(p, iObj), Acb_ObjFaninNum(p, iObj), &p->vCover, vCnf );
        Vec_StrGrow( vCnfBase, Vec_StrSize(vCnf) );
        memcpy( Vec_StrArray(vCnfBase), Vec_StrArray(vCnf), Vec_StrSize(vCnf) );
        vCnfBase->nSize = Vec_StrSize(vCnf);
    }
    Vec_StrFreeP( &vCnf );
    return vCnfs;
}

/**Function*************************************************************

  Synopsis    [Constructs CNF for the window.]

  Description [The window for the pivot node is represented as a DFS ordered array 
  of objects (vWinObjs) whose indexes are used as SAT variable IDs (stored in p->vCopies).
  PivotVar is the index of the pivot node in array vWinObjs.
  The nodes before (after) PivotVar are TFI (TFO) nodes.
  The leaf (root) nodes are labeled with Abc_LitIsCompl().
  If fQbf is 1, returns the instance meant for QBF solving. It uses the last 
  variable (LastVar) as the placeholder for the second copy of the pivot node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_TranslateCnf( Vec_Int_t * vClas, Vec_Int_t * vLits, Vec_Str_t * vCnf, Vec_Int_t * vSatVars, int iPivotVar )
{
    signed char Entry;
    int i, Lit;
    Vec_StrForEachEntry( vCnf, Entry, i )
    {
        if ( (int)Entry == -1 )
        {
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            continue;
        }
        Lit = Abc_Lit2LitV( Vec_IntArray(vSatVars), (int)Entry );
        Lit = Abc_LitNotCond( Lit, Abc_Lit2Var(Lit) == iPivotVar );
        Vec_IntPush( vLits, Lit );
    }
}
int Acb_NtkCountRoots( Vec_Int_t * vWinObjs, int PivotVar )
{
    int i, iObjLit, nRoots = 0;
    Vec_IntForEachEntryStart( vWinObjs, iObjLit, i, PivotVar + 1 )
        nRoots += Abc_LitIsCompl(iObjLit);
    return nRoots;
}
Cnf_Dat_t * Acb_NtkWindow2Cnf( Acb_Ntk_t * p, Vec_Int_t * vWinObjs, int Pivot )
{
    Cnf_Dat_t * pCnf;
    Vec_Int_t * vFaninVars = Vec_IntAlloc( 8 );
    int PivotVar = Vec_IntFind(vWinObjs, Abc_Var2Lit(Pivot, 0));
    int nRoots   = Acb_NtkCountRoots(vWinObjs, PivotVar);
    int TfoStart = PivotVar + 1;
    int nTfoSize = Vec_IntSize(vWinObjs) - TfoStart;
    int nVarsAll = Vec_IntSize(vWinObjs) + nTfoSize + nRoots;
    int i, k, iObj, iObjLit, iFanin, * pFanins, Entry;
    Vec_Wec_t * vCnfs = Acb_DeriveCnfForWindow( p, vWinObjs, PivotVar );
    Vec_Int_t * vClas = Vec_IntAlloc( 100 );
    Vec_Int_t * vLits = Vec_IntAlloc( 1000 );
    // mark new SAT variables
    Vec_IntForEachEntry( vWinObjs, iObj, i )
    {
        Acb_ObjSetFunc( p, Abc_Lit2Var(iObj), i );
//printf( "Node %d -> SAT var %d\n", Vec_IntEntry(&p->vArray2, Abc_Lit2Var(iObj)), i );
    }
    // add clauses for all nodes
    Vec_IntPush( vClas, Vec_IntSize(vLits) );
    Vec_IntForEachEntry( vWinObjs, iObjLit, i )
    {
        if ( Abc_LitIsCompl(iObjLit) && i < PivotVar )
            continue;
        iObj = Abc_Lit2Var(iObjLit);
        assert( !Acb_ObjIsCio(p, iObj) );
        // collect SAT variables
        Vec_IntClear( vFaninVars );
        Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
            Vec_IntPush( vFaninVars, Acb_ObjFunc(p, iFanin) );
        Vec_IntPush( vFaninVars, Acb_ObjFunc(p, iObj) );
        // derive CNF for the node
        Acb_TranslateCnf( vClas, vLits, (Vec_Str_t *)Vec_WecEntry(vCnfs, iObj), vFaninVars, -1 );
    }
    // add second clauses for the TFO
    Vec_IntForEachEntryStart( vWinObjs, iObjLit, i, TfoStart )
    {
        iObj = Abc_Lit2Var(iObjLit);
        assert( !Acb_ObjIsCio(p, iObj) );
        // collect SAT variables
        Vec_IntClear( vFaninVars );
        Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
            Vec_IntPush( vFaninVars, Acb_ObjFunc(p, iFanin) + (Acb_ObjFunc(p, iFanin) > PivotVar) * nTfoSize );
        Vec_IntPush( vFaninVars, Acb_ObjFunc(p, iObj) + nTfoSize );
        // derive CNF for the node
        Acb_TranslateCnf( vClas, vLits, (Vec_Str_t *)Vec_WecEntry(vCnfs, iObj), vFaninVars, PivotVar );
    }
    if ( nRoots > 0 )
    {
        // create XOR clauses for the roots
        int nVars = Vec_IntSize(vWinObjs) + nTfoSize;
        Vec_IntClear( vFaninVars );
        Vec_IntForEachEntryStart( vWinObjs, iObjLit, i, TfoStart )
        {
            if ( !Abc_LitIsCompl(iObjLit) )
                continue;
            iObj = Abc_Lit2Var(iObjLit);
            // add clauses
            Vec_IntPushThree( vLits, Abc_Var2Lit(Acb_ObjFunc(p, iObj), 1), Abc_Var2Lit(Acb_ObjFunc(p, iObj) + nTfoSize, 0), Abc_Var2Lit(nVars, 0) );
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPushThree( vLits, Abc_Var2Lit(Acb_ObjFunc(p, iObj), 0), Abc_Var2Lit(Acb_ObjFunc(p, iObj) + nTfoSize, 1), Abc_Var2Lit(nVars, 0) );
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPushThree( vLits, Abc_Var2Lit(Acb_ObjFunc(p, iObj), 0), Abc_Var2Lit(Acb_ObjFunc(p, iObj) + nTfoSize, 0), Abc_Var2Lit(nVars, 1) );
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPushThree( vLits, Abc_Var2Lit(Acb_ObjFunc(p, iObj), 1), Abc_Var2Lit(Acb_ObjFunc(p, iObj) + nTfoSize, 1), Abc_Var2Lit(nVars, 1) );
            Vec_IntPush( vClas, Vec_IntSize(vLits) );
            Vec_IntPush( vFaninVars, Abc_Var2Lit(nVars++, 0) );
        }
        Vec_IntAppend( vLits, vFaninVars );
        Vec_IntPush( vClas, Vec_IntSize(vLits) );
        assert( nRoots == Vec_IntSize(vFaninVars) );
        assert( nVars == nVarsAll );
    }
    Vec_IntFree( vFaninVars );
    // undo SAT variables
    Vec_IntForEachEntry( vWinObjs, iObj, i )
        Vec_IntWriteEntry( &p->vObjFunc, Abc_Lit2Var(iObj), -1 );
    // create CNF structure
    pCnf = ABC_CALLOC( Cnf_Dat_t, 1 );
    pCnf->nVars     = nVarsAll;
    pCnf->nClauses  = Vec_IntSize(vClas)-1;
    pCnf->nLiterals = Vec_IntSize(vLits);
    pCnf->pClauses  = ABC_ALLOC( int *, Vec_IntSize(vClas) );
    pCnf->pClauses[0] = Vec_IntReleaseArray(vLits);
    Vec_IntForEachEntry( vClas, Entry, i )
        pCnf->pClauses[i] = pCnf->pClauses[0] + Entry;
    // cleanup
    Vec_IntFree( vClas );
    Vec_IntFree( vLits );
    //Cnf_DataPrint( pCnf, 1 );
    return pCnf;
}


/**Function*************************************************************

  Synopsis    [Creates SAT solver containing several copies of the window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_NtkWindow2Solver( sat_solver * pSat, Cnf_Dat_t * pCnf, int PivotVar, int nDivs, int nTimes )
{
    int n, i, RetValue, nRounds = nTimes <= 2 ? nTimes-1 : 2;
    Vec_Int_t * vFlips = Cnf_DataCollectFlipLits( pCnf, PivotVar );
    sat_solver_setnvars( pSat, nTimes * pCnf->nVars + nRounds * nDivs + 1 );
    assert( nTimes == 1 || nTimes == 2 || nTimes == 6 );
    for ( n = 0; n < nTimes; n++ )
    {
        if ( n & 1 )
            Cnf_DataLiftAndFlipLits( pCnf, -pCnf->nVars, vFlips );
        for ( i = 0; i < pCnf->nClauses; i++ )
        {
            if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            {
                Vec_IntFree( vFlips );
                sat_solver_delete( pSat );
                return 0;
            }
        }
        if ( n & 1 )
            Cnf_DataLiftAndFlipLits( pCnf, pCnf->nVars, vFlips );
        if ( n < nTimes - 1 )
            Cnf_DataLift( pCnf, pCnf->nVars );
        else if ( n ) // if ( n == nTimes - 1 )
            Cnf_DataLift( pCnf, -(nTimes - 1) * pCnf->nVars );
    }
    Vec_IntFree( vFlips );
    // add conditional buffers
    for ( n = 0; n < nRounds; n++ )
    {
        int BaseA = n * pCnf->nVars;
        int BaseB = ((n + 1) % nTimes) * pCnf->nVars;
        int BaseC = nTimes * pCnf->nVars + (n & 1) * nDivs;
        for ( i = 0; i < nDivs; i++ )
            sat_solver_add_buffer_enable( pSat, BaseA + i, BaseB + i, BaseC + i, 0 );
    }
    // finalize
    RetValue = sat_solver_simplify( pSat );
    if ( RetValue == 0 )
    {
        sat_solver_delete( pSat );
        return 0;    
    }
    return 1;
}




/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkPrintVec( Acb_Ntk_t * p, Vec_Int_t * vVec, char * pName )
{
    int i;
    printf( "%s: ", pName );
    for ( i = 0; i < vVec->nSize; i++ )
        printf( "%d ", Vec_IntEntry(&p->vArray2, vVec->pArray[i]) );
    printf( "\n" );
}
void Acb_NtkPrintNode( Acb_Ntk_t * p, int Node )
{
    int k, iFanin, * pFanins;
    printf( "Node %d : ", Vec_IntEntry(&p->vArray2, Node) );
    Acb_ObjForEachFaninFast( p, Node, pFanins, iFanin, k )
        printf( "%d ", Vec_IntEntry(&p->vArray2, iFanin) );
    printf( "\n" );
}
void Acb_NtkPrintVec2( Acb_Ntk_t * p, Vec_Int_t * vVec, char * pName )
{
    int i;
    printf( "%s: \n", pName );
    for ( i = 0; i < vVec->nSize; i++ )
        Acb_NtkPrintNode( p, vVec->pArray[i] );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Collects divisors in a non-topo order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acb_NtkDivisors( Acb_Ntk_t * p, int Pivot, int * pTaboo, int nTaboo, int nDivsMax )
{
    Vec_Int_t * vDivs = Vec_IntAlloc( 100 );
    Vec_Int_t * vFront = Vec_IntAlloc( 100 );
    int i, k, iFanin, * pFanins;
    // mark taboo nodes
    Acb_NtkIncTravId( p );
    assert( !Acb_ObjIsCio(p, Pivot) );
    Acb_ObjSetTravIdCur( p, Pivot );
    for ( i = 0; i < nTaboo; i++ )
    {
        assert( !Acb_ObjIsCio(p, pTaboo[i]) );
        if ( Acb_ObjSetTravIdCur( p, pTaboo[i] ) )
            assert( 0 );
    }
    // collect non-taboo fanins of pivot but do not use them as frontier
    Acb_ObjForEachFaninFast( p, Pivot, pFanins, iFanin, k )
        if ( !Acb_ObjSetTravIdCur( p, iFanin ) )
            Vec_IntPush( vDivs, iFanin );
    // collect non-taboo fanins of taboo nodes and use them as frontier
    for ( i = 0; i < nTaboo; i++ )
        Acb_ObjForEachFaninFast( p, pTaboo[i], pFanins, iFanin, k )
            if ( !Acb_ObjSetTravIdCur( p, iFanin ) )
            {
                Vec_IntPush( vDivs, iFanin );
                if ( !Acb_ObjIsCio(p, iFanin) )
                    Vec_IntPush( vFront, iFanin );
            }
    // select divisors incrementally
    while ( Vec_IntSize(vFront) > 0 && Vec_IntSize(vDivs) < nDivsMax )
    {
        // select the topmost
        int iObj, iObjMax = -1, LevelMax = -1;
        Vec_IntForEachEntry( vFront, iObj, k )
            if ( LevelMax < Acb_ObjLevelD(p, iObj) )
                LevelMax = Acb_ObjLevelD(p, (iObjMax = iObj));
        assert( iObjMax > 0 );
        Vec_IntRemove( vFront, iObjMax );
        // expand the topmost
        Acb_ObjForEachFaninFast( p, iObjMax, pFanins, iFanin, k )
            if ( !Acb_ObjSetTravIdCur( p, iFanin ) )
            {
                Vec_IntPush( vDivs, iFanin );
                if ( !Acb_ObjIsCio(p, iFanin) )
                    Vec_IntPush( vFront, iFanin );
            }
    }
    Vec_IntFree( vFront );
    // sort them by level
    Vec_IntSelectSortCost( Vec_IntArray(vDivs), Vec_IntSize(vDivs), &p->vLevelD );
    return vDivs;
}

/**Function*************************************************************

  Synopsis    [Marks TFO of divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_ObjMarkTfo_rec( Acb_Ntk_t * p, int iObj, int nTfoLevMax, int nFanMax )
{
    int iFanout, i;
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    if ( Acb_ObjLevelD(p, iObj) > nTfoLevMax || Acb_ObjFanoutNum(p, iObj) > nFanMax )
        return;
    Acb_ObjForEachFanout( p, iObj, iFanout, i )
        Acb_ObjMarkTfo_rec( p, iFanout, nTfoLevMax, nFanMax );
}
void Acb_ObjMarkTfo( Acb_Ntk_t * p, Vec_Int_t * vDivs, int Pivot, int nTfoLevMax, int nFanMax )
{
    int i, iObj;
    Acb_NtkIncTravId( p );
    Acb_ObjSetTravIdCur( p, Pivot );
    Vec_IntForEachEntry( vDivs, iObj, i )
        Acb_ObjMarkTfo_rec( p, iObj, nTfoLevMax, nFanMax );
}

/**Function*************************************************************

  Synopsis    [Labels TFO nodes with {none, root, inner} based on their type.]

  Description [Assuming TFO of TFI is marked with the current trav ID.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_ObjLabelTfo_rec( Acb_Ntk_t * p, int iObj, int nTfoLevMax, int nFanMax )
{
    int iFanout, i, Diff, fHasNone = 0;
//printf( "Visiting %d\n", Vec_IntEntry(&p->vArray2, iObj) );
    if ( (Diff = Acb_ObjTravIdDiff(p, iObj)) <= 2 )
        return Diff;
    Acb_ObjSetTravIdDiff( p, iObj, 2 );
    if ( Acb_ObjIsCo(p, iObj) || Acb_ObjLevelD(p, iObj) > nTfoLevMax )
        return 2;
    if ( Acb_ObjLevelD(p, iObj) == nTfoLevMax || Acb_ObjFanoutNum(p, iObj) >= nFanMax )
    {
        if ( Diff == 3 )  // belongs to TFO of TFI
            Acb_ObjSetTravIdDiff( p, iObj, 1 ); // root
        return Acb_ObjTravIdDiff(p, iObj);
    }
    Acb_ObjForEachFanout( p, iObj, iFanout, i )
        fHasNone |= 2 == Acb_ObjLabelTfo_rec( p, iFanout, nTfoLevMax, nFanMax );
    if ( fHasNone && Diff == 3 )  // belongs to TFO of TFI
        Acb_ObjSetTravIdDiff( p, iObj, 1 ); // root
    else if ( !fHasNone )
        Acb_ObjSetTravIdDiff( p, iObj, 0 ); // inner
    return Acb_ObjTravIdDiff(p, iObj);
}
int Acb_ObjLabelTfo( Acb_Ntk_t * p, int Root, int nTfoLevMax, int nFanMax )
{
    Acb_NtkIncTravId( p ); // none  (2)    marked (3)  unmarked (4)
    Acb_NtkIncTravId( p ); // root  (1)
    Acb_NtkIncTravId( p ); // inner (0)
    assert( Acb_ObjTravIdDiff(p, Root) > 2 );
    return Acb_ObjLabelTfo_rec( p, Root, nTfoLevMax, nFanMax );
}

/**Function*************************************************************

  Synopsis    [Collects labeled TFO.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_ObjDeriveTfo_rec( Acb_Ntk_t * p, int iObj, Vec_Int_t * vTfo, Vec_Int_t * vRoots )
{
    int iFanout, i, Diff = Acb_ObjTravIdDiff(p, iObj);
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    if ( Diff == 2 ) // root
    {
        Vec_IntPush( vRoots, iObj );
        Vec_IntPush( vTfo, iObj );
        return;
    }
    assert( Diff == 1 );
    Acb_ObjForEachFanout( p, iObj, iFanout, i )
        Acb_ObjDeriveTfo_rec( p, iFanout, vTfo, vRoots );
    Vec_IntPush( vTfo, iObj );
}
void Acb_ObjDeriveTfo( Acb_Ntk_t * p, int Pivot, int nTfoLevMax, int nFanMax, Vec_Int_t ** pvTfo, Vec_Int_t ** pvRoots )
{
    int Res = Acb_ObjLabelTfo( p, Pivot, nTfoLevMax, nFanMax );
    Vec_Int_t * vTfo   = *pvTfo   = Vec_IntAlloc( 10 );
    Vec_Int_t * vRoots = *pvRoots = Vec_IntAlloc( 10 );
    if ( Res ) // none or root
        return;
    Acb_NtkIncTravId( p ); // root (2)   inner (1)  visited (0)
    Acb_ObjDeriveTfo_rec( p, Pivot, vTfo, vRoots );
    assert( Vec_IntEntryLast(vTfo) == Pivot );
    Vec_IntPop( vTfo );
    assert( Vec_IntEntryLast(vRoots) != Pivot );
    Vec_IntReverseOrder( vTfo );
    Vec_IntReverseOrder( vRoots );
}


/**Function*************************************************************

  Synopsis    [Collect side-inputs of the TFO, except the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acb_NtkCollectTfoSideInputs( Acb_Ntk_t * p, int Pivot, Vec_Int_t * vTfo )
{
    Vec_Int_t * vSide  = Vec_IntAlloc( 100 );
    int i, k, Node, iFanin, * pFanins;
    Acb_NtkIncTravId( p );
    Vec_IntPush( vTfo, Pivot );
    Vec_IntForEachEntry( vTfo, Node, i )
        Acb_ObjSetTravIdCur( p, Node );
    Vec_IntForEachEntry( vTfo, Node, i )
        Acb_ObjForEachFaninFast( p, Node, pFanins, iFanin, k )
            if ( !Acb_ObjSetTravIdCur(p, iFanin) && iFanin != Pivot )
                Vec_IntPush( vSide, iFanin );
    Vec_IntPop( vTfo );
    return vSide;
}

/**Function*************************************************************

  Synopsis    [From side inputs, collect marked nodes and their unmarked fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkCollectNewTfi1_rec( Acb_Ntk_t * p, int iObj, Vec_Int_t * vTfiNew )
{
    int i, iFanin, * pFanins;
    if ( !Acb_ObjIsTravIdPrev(p, iObj) )
        return;
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, i )
        Acb_NtkCollectNewTfi1_rec( p, iFanin, vTfiNew );
    Vec_IntPush( vTfiNew, iObj );
}
void Acb_NtkCollectNewTfi2_rec( Acb_Ntk_t * p, int iObj, Vec_Int_t * vTfiNew )
{
    int i, iFanin, * pFanins;
    int fTravIdPrev = Acb_ObjIsTravIdPrev(p, iObj);
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    if ( fTravIdPrev && !Acb_ObjIsCi(p, iObj) )
        Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, i )
            Acb_NtkCollectNewTfi2_rec( p, iFanin, vTfiNew );
    Vec_IntPush( vTfiNew, iObj );
}
Vec_Int_t * Acb_NtkCollectNewTfi( Acb_Ntk_t * p, int Pivot, Vec_Int_t * vDivs, Vec_Int_t * vSide, int * pnDivs )
{
    Vec_Int_t * vTfiNew  = Vec_IntAlloc( 100 );
    int i, Node;
    Acb_NtkIncTravId( p );
//Acb_NtkPrintVec( p, vDivs, "vDivs" );
    Vec_IntForEachEntry( vDivs, Node, i )
        Acb_NtkCollectNewTfi1_rec( p, Node, vTfiNew );
    *pnDivs = Vec_IntSize(vTfiNew);
//Acb_NtkPrintVec( p, vTfiNew, "vTfiNew" );
    Acb_NtkCollectNewTfi1_rec( p, Pivot, vTfiNew );
//Acb_NtkPrintVec( p, vTfiNew, "vTfiNew" );
    assert( Vec_IntEntryLast(vTfiNew) == Pivot );
    Vec_IntPop( vTfiNew );
    Vec_IntForEachEntry( vSide, Node, i )
        Acb_NtkCollectNewTfi2_rec( p, Node, vTfiNew );
    Vec_IntPush( vTfiNew, Pivot );
    return vTfiNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acb_NtkCollectWindow( Acb_Ntk_t * p, int Pivot, Vec_Int_t * vTfi, Vec_Int_t * vTfo, Vec_Int_t * vRoots )
{
    Vec_Int_t * vWin = Vec_IntAlloc( 100 );
    int i, k, iObj, iFanin, * pFanins;
    assert( Vec_IntEntryLast(vTfi) == Pivot );
    // mark nodes
    Acb_NtkIncTravId( p );
    Vec_IntForEachEntry( vTfi, iObj, i )
        Acb_ObjSetTravIdCur(p, iObj);
    // add TFI
    Vec_IntForEachEntry( vTfi, iObj, i )
    {
        int fIsTfiInput = 0;
        Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
            if ( !Acb_ObjIsTravIdCur(p, iFanin) ) // fanin is not in TFI
                fIsTfiInput = 1; // mark as leaf
        Vec_IntPush( vWin, Abc_Var2Lit(iObj, Acb_ObjIsCi(p, iObj) || fIsTfiInput) );
    }
    // mark roots
    Acb_NtkIncTravId( p );
    Vec_IntForEachEntry( vRoots, iObj, i )
        Acb_ObjSetTravIdCur(p, iObj);
    // add TFO
    Vec_IntForEachEntry( vTfo, iObj, i )
    {
        assert( !Acb_ObjIsCo(p, iObj) );
        Vec_IntPush( vWin, Abc_Var2Lit(iObj, Acb_ObjIsTravIdCur(p, iObj)) );
    }
    return vWin;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acb_NtkWindow( Acb_Ntk_t * p, int Pivot, int * pTaboo, int nTaboo, int nDivsMax, int nTfoLevs, int nFanMax, int * pnDivs )
{
    int fVerbose = 0;
    int nTfoLevMax = Acb_ObjLevelD(p, Pivot) + nTfoLevs;
    Vec_Int_t * vWin, * vDivs, * vTfo, * vRoots, * vSide, * vTfi;
    // collect divisors by traversing limited TFI
    vDivs = Acb_NtkDivisors( p, Pivot, pTaboo, nTaboo, nDivsMax );
    if ( fVerbose ) Acb_NtkPrintVec( p, vDivs, "vDivs" );
    // mark limited TFO of the divisors
    Acb_ObjMarkTfo( p, vDivs, Pivot, nTfoLevMax, nFanMax );
    // collect TFO and roots
    Acb_ObjDeriveTfo( p, Pivot, nTfoLevMax, nFanMax, &vTfo, &vRoots );
    if ( fVerbose ) Acb_NtkPrintVec( p, vTfo, "vTfo" );
    if ( fVerbose ) Acb_NtkPrintVec( p, vRoots, "vRoots" );
    // collect side inputs of the TFO
    vSide = Acb_NtkCollectTfoSideInputs( p, Pivot, vTfo );
    if ( fVerbose ) Acb_NtkPrintVec( p, vSide, "vSide" );
    // mark limited TFO of the divisors
    Acb_ObjMarkTfo( p, vDivs, Pivot, nTfoLevMax, nFanMax );
    // collect new TFI
    vTfi = Acb_NtkCollectNewTfi( p, Pivot, vDivs, vSide, pnDivs );
    if ( fVerbose ) Acb_NtkPrintVec( p, vTfi, "vTfi" );
    Vec_IntFree( vSide );
    Vec_IntFree( vDivs );
    // collect all nodes
    vWin = Acb_NtkCollectWindow( p, Pivot, vTfi, vTfo, vRoots );
    // cleanup
    Vec_IntFree( vTfi );
    Vec_IntFree( vTfo );
    Vec_IntFree( vRoots );
    return vWin;
}



/**Function*************************************************************

  Synopsis    [Computes function of the node]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
word Acb_ComputeFunction( sat_solver * pSat, int PivotVar, int FreeVar, Vec_Int_t * vDivVars )
{
    int fExpand = 1;
    word uCube, uTruth = 0;
    Vec_Int_t * vTempLits = Vec_IntAlloc( 100 );
    int status, i, iVar, iLit, nFinal, * pFinal, pLits[2];
    assert( FreeVar < sat_solver_nvars(pSat) );
    pLits[0] = Abc_Var2Lit( PivotVar, 0 ); // F = 1
    pLits[1] = Abc_Var2Lit( FreeVar, 0 );  // iNewLit
    while ( 1 ) 
    {
        // find onset minterm
        status = sat_solver_solve( pSat, pLits, pLits + 2, 0, 0, 0, 0 );
        if ( status == l_False )
        {
            Vec_IntFree( vTempLits );
            return uTruth;
        }
        assert( status == l_True );
        if ( fExpand )
        {
            // collect divisor literals
            Vec_IntFill( vTempLits, 1, Abc_LitNot(pLits[0]) ); // F = 0
            Vec_IntForEachEntry( vDivVars, iVar, i )
                Vec_IntPush( vTempLits, sat_solver_var_literal(pSat, iVar) );
            // check against offset
            status = sat_solver_solve( pSat, Vec_IntArray(vTempLits), Vec_IntLimit(vTempLits), 0, 0, 0, 0 );
            assert( status == l_False );
            // compute cube and add clause
            nFinal = sat_solver_final( pSat, &pFinal );
            Vec_IntFill( vTempLits, 1, Abc_LitNot(pLits[1]) ); // NOT(iNewLit)
            for ( i = 0; i < nFinal; i++ )
                if ( pFinal[i] != pLits[0] )
                    Vec_IntPush( vTempLits, pFinal[i] );
        }
        else
        {
            // collect divisor literals
            Vec_IntFill( vTempLits, 1, Abc_LitNot(pLits[1]) );// NOT(iNewLit)
            Vec_IntForEachEntry( vDivVars, iVar, i )
                Vec_IntPush( vTempLits, Abc_LitNot(sat_solver_var_literal(pSat, iVar)) );
        }
        uCube = ~(word)0;
        Vec_IntForEachEntryStart( vTempLits, iLit, i, 1 )
        {
            iVar = Vec_IntFind( vDivVars, Abc_Lit2Var(iLit) );   assert( iVar >= 0 );
            uCube &= Abc_LitIsCompl(iLit) ? s_Truths6[iVar] : ~s_Truths6[iVar];
        }
        uTruth |= uCube;
        status = sat_solver_addclause( pSat, Vec_IntArray(vTempLits), Vec_IntLimit(vTempLits) );
        if ( status == 0 )
        {
            Vec_IntFree( vTempLits );
            return uTruth;
        }
    }
    assert( 0 ); 
    return ~(word)0;
}


/**Function*************************************************************

  Synopsis    [Collects the taboo nodes (nodes that cannot be divisors).]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Acb_ObjIsCritFanin( Acb_Ntk_t * p, int i, int f )  { return Acb_ObjLevelR(p, i) + Acb_ObjLevelD(p, f) == p->LevelMax; }

static inline void Acb_ObjUpdateFanoutCount( Acb_Ntk_t * p, int iObj, int AddOn )
{
    int k, iFanin, * pFanins;
    Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
        Acb_ObjFanoutVec(p, iFanin)->nSize += AddOn;
}

int Acb_NtkCollectTaboo( Acb_Ntk_t * p, int Pivot, int Next, int nTabooMax, int * pTaboo )
{
    int i, k, iFanin, * pFanins, nTaboo = 0;
    if ( nTabooMax == 0 ) // delay optimization
    {
        // collect delay critical fanins of the pivot node
        Acb_ObjForEachFaninFast( p, Pivot, pFanins, iFanin, k )
            if ( !Acb_ObjIsCi(p, iFanin) && Acb_ObjIsCritFanin( p, Pivot, iFanin ) )
                pTaboo[ nTaboo++ ] = iFanin;
    }
    else // area optimization
    {
        // check if the node has any area critical fanins
//        Acb_ObjForEachFaninFast( p, Pivot, pFanins, iFanin, k )
//            if ( !Acb_ObjIsCi(p, iFanin) && Acb_ObjFanoutNum(p, iFanin) == 1 )
//                break;
        // collect this critical fanin
        assert( Next > 0 && !Acb_ObjIsCio(p, Next) && Acb_ObjFanoutNum(p, Next) == 1 );
        Acb_ObjForEachFaninFast( p, Pivot, pFanins, iFanin, k )
            if ( iFanin == Next )
                break;
        assert( k < Acb_ObjFaninNum(p, Pivot) );
        if ( k < Acb_ObjFaninNum(p, Pivot) ) // there is fanin
        {
            // mark pivot
            Acb_NtkIncTravId( p );
            Acb_ObjSetTravIdCur( p, Pivot );
            Acb_ObjUpdateFanoutCount( p, Pivot, -1 );
            // add the first taboo node
            assert( Acb_ObjFanoutNum(p, iFanin) == 0 );
            pTaboo[ nTaboo++ ] = iFanin;
            Acb_ObjSetTravIdCur( p, iFanin );
            Acb_ObjUpdateFanoutCount( p, iFanin, -1 );
            while ( nTaboo < nTabooMax )
            {
                // select the first unrefed fanin
                for ( i = 0; i < nTaboo; i++ )
                {
                    Acb_ObjForEachFaninFast( p, pTaboo[i], pFanins, iFanin, k )
                        if ( !Acb_ObjIsCi(p, iFanin) && !Acb_ObjIsTravIdCur(p, iFanin) && Acb_ObjFanoutNum(p, iFanin) == 0 )
                        {
                            pTaboo[ nTaboo++ ] = iFanin;
                            Acb_ObjSetTravIdCur( p, iFanin );
                            Acb_ObjUpdateFanoutCount( p, iFanin, -1 );
                            break;
                        }
                    if ( k < Acb_ObjFaninNum(p, pTaboo[i]) )
                        break;
                }
                if ( i == nTaboo ) // no change
                    break;
            }
            // reference nodes back
            Acb_ObjUpdateFanoutCount( p, Pivot, 1 );
            for ( i = 0; i < nTaboo; i++ )
                Acb_ObjUpdateFanoutCount( p, pTaboo[i], 1 );
        }
    }
    return nTaboo;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Vec_IntVars2Vars( Vec_Int_t * p, int Shift )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        p->pArray[i] += Shift;
}
static inline void Vec_IntVars2Lits( Vec_Int_t * p, int Shift, int fCompl )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        p->pArray[i] = Abc_Var2Lit( p->pArray[i] + Shift, fCompl );
}
static inline void Vec_IntLits2Vars( Vec_Int_t * p, int Shift )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        p->pArray[i] = Abc_Lit2Var( p->pArray[i] ) + Shift;
}
static inline void Vec_IntRemap( Vec_Int_t * p, Vec_Int_t * vMap )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        p->pArray[i] = Vec_IntEntry(vMap, p->pArray[i]);
}

void Acb_WinPrint( Acb_Ntk_t * p, Vec_Int_t * vWin, int Pivot, int nDivs )
{
    int i, Node;
    printf( "Window for node %d with %d divisors:\n", Vec_IntEntry(&p->vArray2, Pivot), nDivs );
    Vec_IntForEachEntry( vWin, Node, i )
    {
        if ( i == nDivs )
            printf( " | " );
        if ( Abc_Lit2Var(Node) == Pivot )
            printf( "(%d) ", Vec_IntEntry(&p->vArray2, Pivot) );
        else
            printf( "%s%d ", Abc_LitIsCompl(Node) ? "*":"", Vec_IntEntry(&p->vArray2, Abc_Lit2Var(Node)) );
    }
    printf( "\n" );
}

Vec_Int_t * Acb_NtkFindSupp( Acb_Ntk_t * p, sat_solver * pSat2, int nVars, int nDivs )
{
    int nSuppNew;
    Vec_Int_t * vSupp = Vec_IntStartNatural( nDivs );
    Vec_IntReverseOrder( vSupp );
    Vec_IntVars2Lits( vSupp, 2*nVars, 0 );
    nSuppNew = sat_solver_minimize_assumptions( pSat2, Vec_IntArray(vSupp), Vec_IntSize(vSupp), 0 );
    Vec_IntShrink( vSupp, nSuppNew );
    Vec_IntLits2Vars( vSupp, -2*nVars );
    return vSupp;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
typedef struct Acb_Mfs_t_ Acb_Mfs_t;
struct Acb_Mfs_t_
{
    Acb_Ntk_t *     pNtk;        // network
    Acb_Par_t *     pPars;       // parameters
    sat_solver *    pSat[3];     // SAT solvers
    int             nOvers;      // overflows
    int             nNodes;      // nodes
    int             nWins;       // windows
    int             nWinsAll;    // windows
    int             nDivsAll;    // windows
    int             nChanges[3]; // changes
    abctime         timeTotal;
    abctime         timeCnf;
    abctime         timeSol;
    abctime         timeWin;
    abctime         timeSat;
    abctime         timeSatU;
    abctime         timeSatS;
};
Acb_Mfs_t * Acb_MfsStart( Acb_Ntk_t * pNtk, Acb_Par_t * pPars )
{
    Acb_Mfs_t * p = ABC_CALLOC( Acb_Mfs_t, 1 );
    p->pNtk       = pNtk;
    p->pPars      = pPars;
    p->timeTotal  = Abc_Clock();
    p->pSat[0]    = sat_solver_new();
    p->pSat[1]    = sat_solver_new();
    p->pSat[2]    = sat_solver_new();
    return p;
}
void Acb_MfsStop( Acb_Mfs_t * p )
{
    sat_solver_delete( p->pSat[0] );
    sat_solver_delete( p->pSat[1] );
    sat_solver_delete( p->pSat[2] );
    ABC_FREE( p );
}
int Acb_NtkOptNode( Acb_Mfs_t * p, int Pivot, int Next )
{
    Cnf_Dat_t * pCnf; abctime clk;
    Vec_Int_t * vWin, * vSupp = NULL;
    int c, PivotVar, nDivs = 0, RetValue = 0; word uTruth;
    int pTaboo[16], nTaboo = Acb_NtkCollectTaboo( p->pNtk, Pivot, Next, p->pPars->nTabooMax, pTaboo );
    if ( nTaboo == 0 )
        return RetValue;
    p->nWins++;
    assert( p->pPars->nTabooMax == 0 || nTaboo <= p->pPars->nTabooMax );
    assert( nTaboo <= 16 );
    //printf( "Trying node %d with fanin %d\n", Pivot, Next );

    // compute divisors and window for this target node with these taboo nodes
    clk = Abc_Clock();
    vWin = Acb_NtkWindow( p->pNtk, Pivot, pTaboo, nTaboo, p->pPars->nDivMax, p->pPars->nTfoLevMax, p->pPars->nFanoutMax, &nDivs );
    p->nWinsAll += Vec_IntSize(vWin);
    p->nDivsAll += nDivs;
    p->timeWin  += Abc_Clock() - clk;
    PivotVar = Vec_IntFind( vWin, Abc_Var2Lit(Pivot, 0) );
    if ( p->pPars->fVerbose )
    printf( "Node %d: Window contains %d objects and %d divisors.  ", Vec_IntEntry(&p->pNtk->vArray2, Pivot), Vec_IntSize(vWin), nDivs );
//    Acb_WinPrint( p, vWin, Pivot, nDivs );
//    return;
    if ( nDivs >= 2 * p->pPars->nDivMax )
    {
        p->nOvers++;
        if ( p->pPars->fVerbose )
            printf( "Too many divisors.\n" );
        Vec_IntFree( vWin );
        return RetValue;
    }

    // derive CNF 
    clk = Abc_Clock();
    pCnf  = Acb_NtkWindow2Cnf( p->pNtk, vWin, Pivot );
    p->timeCnf += Abc_Clock() - clk;
    // derive SAT solver
    clk = Abc_Clock();
    Acb_NtkWindow2Solver( p->pSat[0], pCnf, PivotVar, nDivs, 1 );
    p->timeSol += Abc_Clock() - clk;
    // check constants
    for ( c = 0; c < 2; c++ )
    {
        int Lit = Abc_Var2Lit( PivotVar, c );
        int status = sat_solver_solve( p->pSat[0], &Lit, &Lit + 1, 0, 0, 0, 0 );
        if ( status == l_False )
        {
            p->nChanges[0]++;
            if ( p->pPars->fVerbose )
            printf( "Found constant %d.\n", c );
            Acb_NtkUpdateNode( p->pNtk, Pivot, c ? ~(word)0 : 0, NULL );
            RetValue = 1;
            goto cleanup;
        }
        assert( status == l_True );
    }

    // derive SAT solver
    clk = Abc_Clock();
    Acb_NtkWindow2Solver( p->pSat[1], pCnf, PivotVar, nDivs, 2 );
    p->timeSol += Abc_Clock() - clk;
    // check for one-node implementation
    clk = Abc_Clock();
    vSupp = Acb_NtkFindSupp( p->pNtk, p->pSat[1], pCnf->nVars, nDivs );
    p->timeSat += Abc_Clock() - clk;
    if ( Vec_IntSize(vSupp) <= p->pPars->nLutSize )
    {
        p->nChanges[1]++;
        if ( p->pPars->fVerbose )
        printf( "Found %d inputs: ", Vec_IntSize(vSupp) );
        uTruth = Acb_ComputeFunction( p->pSat[1], PivotVar, sat_solver_nvars(p->pSat[1])-1, vSupp );
        if ( p->pPars->fVerbose )
        Extra_PrintHex( stdout, (unsigned *)&uTruth, Vec_IntSize(vSupp) ); 
        if ( p->pPars->fVerbose )
        printf( "\n" );
        // create support in terms of nodes
        Vec_IntRemap( vSupp, vWin );
        Vec_IntLits2Vars( vSupp, 0 );
        Acb_NtkUpdateNode( p->pNtk, Pivot, uTruth, vSupp );
        RetValue = 1;
        goto cleanup;
    }
    if ( p->pPars->fVerbose )
    printf( "\n" );

cleanup:
    sat_solver_restart( p->pSat[0] );
    sat_solver_restart( p->pSat[1] );
    sat_solver_restart( p->pSat[2] );
    Cnf_DataFree( pCnf );
    Vec_IntFree( vWin );
    Vec_IntFreeP( &vSupp );
    return RetValue;
}
void Acb_NtkOptNodeTop( Acb_Mfs_t * p, int Pivot )
{
    if ( p->pPars->fArea )
    {
        p->nNodes++;
        while ( 1 )
        {
            int k, iFanin, * pFanins;
            Acb_ObjForEachFaninFast( p->pNtk, Pivot, pFanins, iFanin, k )
                if ( !Acb_ObjIsCi(p->pNtk, iFanin) && Acb_ObjFanoutNum(p->pNtk, iFanin) == 1 && Acb_NtkOptNode(p, Pivot, iFanin) )
                    break;
            if ( k == Acb_ObjFaninNum(p->pNtk, Pivot) ) // no change
                break;
        }
    }
    else
    {
        assert( 0 );
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkOpt( Acb_Ntk_t * pNtk, Acb_Par_t * pPars )
{
    Acb_Mfs_t * pMan = Acb_MfsStart( pNtk, pPars );
    //if ( pPars->fVerbose )
        printf( "%s-optimization parameters: TabooMax(M) = %d  DivMax(D) = %d  TfoLev(O) = %d  LutSize = %d\n", 
            pMan->pPars->fArea ? "Area" : "Delay", pMan->pPars->nTabooMax, pMan->pPars->nDivMax, pMan->pPars->nTfoLevMax, pMan->pPars->nLutSize );
    Acb_NtkCreateFanout( pMan->pNtk );  // fanout data structure
    Acb_NtkCleanObjFuncs( pMan->pNtk ); // SAT variables
    Acb_NtkCleanObjCnfs( pMan->pNtk );  // CNF representations
    if ( pMan->pPars->fArea )
    {
        int iObj;
        Acb_NtkUpdateLevelD( pMan->pNtk, -1 ); // compute forward logic level
        Acb_NtkForEachNode( pMan->pNtk, iObj )
        {
            //if ( iObj != 433 )
            //    continue;
            Acb_NtkOptNodeTop( pMan, iObj );
        }
    }
    else
    {
        Acb_NtkUpdateTiming( pMan->pNtk, -1 ); // compute delay information
        while ( Vec_QueTopPriority(pMan->pNtk->vQue) > 0 )
        {
            int iObj = Vec_QuePop(pMan->pNtk->vQue);
            //if ( iObj != 28 )
            //    continue;
            Acb_NtkOptNodeTop( pMan, iObj ); 
        }
    }
    //if ( pPars->fVerbose )
    {
        pMan->timeTotal = Abc_Clock() - pMan->timeTotal;
        printf( "Node = %d  Win = %d (Ave = %d)  DivAve = %d   Change = %d  Const = %d  Node1 = %d  Node2 = %d   Over = %d\n", 
            pMan->nNodes, pMan->nWins, pMan->nWinsAll/Abc_MaxInt(1, pMan->nWins), pMan->nDivsAll/Abc_MaxInt(1, pMan->nWins),
            pMan->nChanges[0] + pMan->nChanges[1] + pMan->nChanges[2],
            pMan->nChanges[0], pMan->nChanges[1], pMan->nChanges[2], pMan->nOvers );
        ABC_PRTP( "Windowing  ", pMan->timeWin,    pMan->timeTotal );
        ABC_PRTP( "CNF compute", pMan->timeCnf,    pMan->timeTotal );
        ABC_PRTP( "Make solver", pMan->timeSol,    pMan->timeTotal );
        ABC_PRTP( "SAT solving", pMan->timeSat,    pMan->timeTotal );
//        ABC_PRTP( "  unsat    ", pMan->timeSatU,   pMan->timeTotal );
//        ABC_PRTP( "  sat      ", pMan->timeSatS,   pMan->timeTotal );
        ABC_PRTP( "TOTAL      ", pMan->timeTotal,  pMan->timeTotal );
        fflush( stdout );
    }
    Acb_MfsStop( pMan );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

