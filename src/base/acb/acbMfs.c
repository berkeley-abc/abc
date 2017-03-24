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

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_Truth2Cnf( word Truth, int nVars, Vec_Int_t * vCover, Vec_Str_t * vCnf )
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
Vec_Wec_t * Acb_NtkDeriveCnf( Acb_Ntk_t * p )
{
    Vec_Wec_t * vCnfs = Vec_WecStart( Acb_NtkObjNumMax(p) );
    Vec_Str_t * vCnf = Vec_StrAlloc( 100 ); int iObj;
    Acb_NtkForEachNode( p, iObj )
    {
        int nCubes = Acb_Truth2Cnf( Acb_ObjTruth(p, iObj), Acb_ObjFaninNum(p, iObj), &p->vCover, vCnf );
        Vec_Str_t * vCnfBase = (Vec_Str_t *)Vec_WecEntry( vCnfs, iObj );
        Vec_StrGrow( vCnfBase, Vec_StrSize(vCnf) );
        memcpy( Vec_StrArray(vCnfBase), Vec_StrArray(vCnf), Vec_StrSize(vCnf) );
        vCnfBase->nSize = Vec_StrSize(vCnf);
    }
    Vec_StrFree( vCnf );
    return vCnfs;
}
void Acb_CnfTranslate( Vec_Wec_t * vRes, Vec_Str_t * vCnf, Vec_Int_t * vSatVars, int iPivotVar )
{
    Vec_Int_t * vClause;
    signed char Entry;
    int i, Lit;
    Vec_WecClear( vRes );
    vClause = Vec_WecPushLevel( vRes );
    Vec_StrForEachEntry( vCnf, Entry, i )
    {
        if ( (int)Entry == -1 )
        {
            vClause = Vec_WecPushLevel( vRes );
            continue;
        }
        Lit = Abc_Lit2LitV( Vec_IntArray(vSatVars), (int)Entry );
        Lit = Abc_LitNotCond( Lit, Abc_Lit2Var(Lit) == iPivotVar );
        Vec_IntPush( vClause, Lit );
    }
}
int Acb_ObjCreateCnf( sat_solver * pSat, Acb_Ntk_t * p, int iObj, Vec_Int_t * vSatVars, int iPivotVar )
{
    Vec_Int_t * vClause; int k, RetValue;
    Acb_CnfTranslate( &p->vClauses, (Vec_Str_t *)Vec_WecEntry(&p->vCnfs, iObj), vSatVars, iPivotVar );
    Vec_WecForEachLevel( &p->vClauses, vClause, k )
    {
        if ( Vec_IntSize(vClause) == 0 )
            break;
        RetValue = sat_solver_addclause( pSat, Vec_IntArray(vClause), Vec_IntLimit(vClause) );
        if ( RetValue == 0 )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Constructs SAT solver for the window.]

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
int Acb_NtkCountRoots( Vec_Int_t * vWinObjs, int PivotVar )
{
    int i, iObjLit, nRoots = 0;
    Vec_IntForEachEntryStart( vWinObjs, iObjLit, i, PivotVar + 1 )
        nRoots += Abc_LitIsCompl(iObjLit);
    return nRoots;
}
sat_solver * Acb_NtkWindow2Solver( sat_solver * pSat, Acb_Ntk_t * p, int Pivot, Vec_Int_t * vWinObjs, int fQbf )
{
    Vec_Int_t * vFaninVars = Vec_IntAlloc( 8 );
    int PivotVar = Vec_IntFind(vWinObjs, Abc_Var2Lit(Pivot, 0));
    int nRoots   = Acb_NtkCountRoots(vWinObjs, PivotVar);
    int TfoStart = PivotVar + 1;
    int nTfoSize = Vec_IntSize(vWinObjs) - TfoStart;
    int LastVar  = Vec_IntSize(vWinObjs) + TfoStart + nRoots;
    int i, k, iLit = 1, RetValue, iObj, iObjLit, iFanin, * pFanins;
    //Vec_IntPrint( vWinObjs );
    // mark new SAT variables
    Vec_IntForEachEntry( vWinObjs, iObj, i )
        Acb_ObjSetCopy( p, i, iObj );
    // create SAT solver
    if ( pSat == NULL )
        pSat = sat_solver_new();
    else
        sat_solver_restart( pSat );
    sat_solver_setnvars( pSat, Vec_IntSize(vWinObjs) + nTfoSize + nRoots + 1 );
    // create constant 0 clause
    sat_solver_addclause( pSat, &iLit, &iLit + 1 );
    // add clauses for all nodes
    Vec_IntForEachEntryStop( vWinObjs, iObjLit, i, TfoStart )
    {
        if ( Abc_LitIsCompl(iObjLit) )
            continue;
        iObj = Abc_Lit2Var(iObjLit);
        assert( !Acb_ObjIsCio(p, iObj) );
        // collect SAT variables
        Vec_IntClear( vFaninVars );
        Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
            Vec_IntPush( vFaninVars, Acb_ObjCopy(p, iFanin) );
        Vec_IntPush( vFaninVars, Acb_ObjCopy(p, iObj) );
        // derive CNF for the node
        RetValue = Acb_ObjCreateCnf( pSat, p, iObj, vFaninVars, -1 );
        assert( RetValue );
    }
    // add second clauses for the TFO
    Vec_IntForEachEntryStart( vWinObjs, iObjLit, i, TfoStart )
    {
        iObj = Abc_Lit2Var(iObjLit);
        assert( !Acb_ObjIsCio(p, iObj) );
        // collect SAT variables
        Vec_IntClear( vFaninVars );
        Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
            Vec_IntPush( vFaninVars, (fQbf && iFanin == Pivot) ? LastVar : Acb_ObjCopy(p, iFanin) );
        Vec_IntPush( vFaninVars, Acb_ObjCopy(p, iObj) );
        // derive CNF for the node
        RetValue = Acb_ObjCreateCnf( pSat, p, iObj, vFaninVars, fQbf ? -1 : PivotVar );
        assert( RetValue );
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
            Vec_IntPush( vFaninVars, Abc_Var2Lit(nVars, 0) );
            sat_solver_add_xor( pSat, Acb_ObjCopy(p, iObj), Acb_ObjCopy(p, iObj) + nTfoSize, nVars++, 0 );
        }
        // make OR clause for the last nRoots variables
        RetValue = sat_solver_addclause( pSat, Vec_IntArray(vFaninVars), Vec_IntLimit(vFaninVars) );
        if ( RetValue == 0 )
        {
            Vec_IntFree( vFaninVars );
            sat_solver_delete( pSat );
            return NULL;
        }
        assert( sat_solver_nvars(pSat) == nVars + 1 );
    }
    else if ( fQbf )
    {
        int n, pLits[2];
        for ( n = 0; n < 2; n++ )
        {
            pLits[0] = Abc_Var2Lit( PivotVar, n );
            pLits[1] = Abc_Var2Lit( LastVar, n );
            RetValue = sat_solver_addclause( pSat, pLits, pLits + 2 );
            assert( RetValue );
        }
    }
    Vec_IntFree( vFaninVars );
    // finalize
    RetValue = sat_solver_simplify( pSat );
    if ( RetValue == 0 )
    {
        sat_solver_delete( pSat );
        return NULL;    
    }
    return pSat;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkUnmarkWindow( Acb_Ntk_t * p, Vec_Int_t * vWin )
{
    int i, iObj;
    Vec_IntForEachEntry( vWin, iObj, i )
        Vec_IntWriteEntry( &p->vObjCopy, iObj, -1 );
}




/**Function*************************************************************

  Synopsis    [Collects divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Acb_ObjIsCritFanin( Acb_Ntk_t * p, int i, int f )  { return Acb_ObjLevelR(p, i) + Acb_ObjLevelD(p, f) == p->LevelMax; }
Vec_Int_t * Acb_NtkDivisors( Acb_Ntk_t * p, int Pivot, int nTfiLevMin )
{
    int i, k, iObj, iFanin, iFanin2, * pFanins, * pFanins2, Lev, Level = Acb_ObjLevelD(p, Pivot);
    // include non-critical pivot fanins AND fanins of critical pivot fanins
    Vec_Int_t * vDivs  = Vec_IntAlloc( 100 );
    Acb_ObjForEachFaninFast( p, Pivot, pFanins, iFanin, i )
    {
        if ( !Acb_ObjIsCritFanin(p, Pivot, iFanin) ) // non-critical fanin
            Vec_IntPush( vDivs, iFanin ); 
        else // critical fanin
            Acb_ObjForEachFaninFast( p, iFanin, pFanins2, iFanin2, k )
                Vec_IntPushUnique( vDivs, iFanin2 );
    }
    // continue for a few more levels
    for ( Lev = Level-2; Lev >= nTfiLevMin; Lev-- )
    {
        Vec_IntForEachEntry( vDivs, iObj, i )
            if ( Acb_ObjLevelD(p, iObj) == Lev )
                Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
                    Vec_IntPushUnique( vDivs, iFanin );
    }
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
void Acb_ObjMarkTfo_rec( Acb_Ntk_t * p, int iObj, int Pivot, int nTfoLevMax, int nFanMax )
{
    int iFanout, i;
    if ( Acb_ObjSetTravIdCur(p, iObj) )
        return;
    if ( Acb_ObjLevelD(p, iObj) > nTfoLevMax || Acb_ObjFanoutNum(p, iObj) >= nFanMax || iObj == Pivot )
        return;
    Acb_ObjForEachFanout( p, iObj, iFanout, i )
        Acb_ObjMarkTfo_rec( p, iFanout, Pivot, nTfoLevMax, nFanMax );
}
void Acb_ObjMarkTfo( Acb_Ntk_t * p, Vec_Int_t * vDivs, int Pivot, int nTfoLevMax, int nFanMax )
{
    int i, iObj;
    Acb_NtkIncTravId( p );
    Vec_IntForEachEntry( vDivs, iObj, i )
        Acb_ObjMarkTfo_rec( p, iObj, Pivot, nTfoLevMax, nFanMax );
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
    if ( (Diff = Acb_ObjTravIdDiff(p, iObj)) <= 2 )
        return Diff;
    Acb_ObjSetTravIdDiff( p, iObj, 2 );
    if ( Acb_ObjIsCo(p, iObj) || Acb_ObjLevelD(p, iObj) > nTfoLevMax )
        return 2;
    if ( Acb_ObjLevelD(p, iObj) == nTfoLevMax || Acb_ObjFanoutNum(p, iObj) >= nFanMax )
    {
        if ( Diff == 3 )  
            Acb_ObjSetTravIdDiff( p, iObj, 1 ); // mark root
        return Acb_ObjTravIdDiff(p, iObj);
    }
    Acb_ObjForEachFanout( p, iObj, iFanout, i )
        fHasNone |= 2 == Acb_ObjLabelTfo_rec( p, iFanout, nTfoLevMax, nFanMax );
    if ( fHasNone && Diff == 3 )
        Acb_ObjSetTravIdDiff( p, iObj, 1 ); // root
    else
        Acb_ObjSetTravIdDiff( p, iObj, 0 ); // inner
    return Acb_ObjTravIdDiff(p, iObj);
}
int Acb_ObjLabelTfo( Acb_Ntk_t * p, int Root, int nTfoLevMax, int nFanMax )
{
    Acb_NtkIncTravId( p ); // none  (2)    marked (3)  unmarked (4)
    Acb_NtkIncTravId( p ); // root  (1)
    Acb_NtkIncTravId( p ); // inner (0)
    assert( Acb_ObjTravIdDiff(p, Root) < 3 );
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
        Vec_IntPush( vRoots, Diff );
        return;
    }
    assert( Diff == 1 );
    Acb_ObjForEachFanout( p, iObj, iFanout, i )
        Acb_ObjDeriveTfo_rec( p, iFanout, vTfo, vRoots );
    Vec_IntPush( vTfo, Diff );
}
void Acb_ObjDeriveTfo( Acb_Ntk_t * p, int Root, int nTfoLevMax, int nFanMax, Vec_Int_t ** pvTfo, Vec_Int_t ** pvRoots )
{
    int Res = Acb_ObjLabelTfo( p, Root, nTfoLevMax, nFanMax );
    Vec_Int_t * vTfo   = *pvTfo   = Vec_IntAlloc( 100 );
    Vec_Int_t * vRoots = *pvRoots = Vec_IntAlloc( 100 );
    if ( Res ) // none or root
        return;
    Acb_NtkIncTravId( p ); // root (2)   inner (1)  visited (0)
    Acb_ObjDeriveTfo_rec( p, Root, vTfo, vRoots );
    assert( Vec_IntEntryLast(vTfo) == Root );
    Vec_IntPop( vTfo );
    assert( Vec_IntEntryLast(vRoots) != Root );
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
    Vec_IntForEachEntry( vTfo, Node, i )
        Acb_ObjSetTravIdCur( p, Node ), assert( Node != Pivot );
    Vec_IntForEachEntry( vTfo, Node, i )
        Acb_ObjForEachFaninFast( p, Node, pFanins, iFanin, k )
            if ( !Acb_ObjSetTravIdCur(p, iFanin) && iFanin != Pivot )
                Vec_IntPush( vSide, iFanin );
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
Vec_Int_t * Acb_NtkCollectNewTfi( Acb_Ntk_t * p, int Pivot, Vec_Int_t * vSide )
{
    Vec_Int_t * vTfiNew  = Vec_IntAlloc( 100 );
    int i, Node;
    Acb_NtkIncTravId( p );
    Acb_NtkCollectNewTfi1_rec( p, Pivot, vTfiNew );
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
    // mark leaves
    Acb_NtkIncTravId( p );
    Vec_IntForEachEntry( vTfi, iObj, i )
        Acb_ObjSetTravIdCur(p, iObj);
    Acb_NtkIncTravId( p );
    Vec_IntForEachEntry( vTfi, iObj, i )
        if ( !Acb_ObjIsCi(p, iObj) )
            Acb_ObjForEachFaninFast( p, iObj, pFanins, iFanin, k )
                if ( !Acb_ObjIsTravIdCur(p, iFanin) )
                    Acb_ObjSetTravIdCur(p, iObj);
    // add TFI
    Vec_IntForEachEntry( vTfi, iObj, i )
        Vec_IntPush( vWin, Abc_Var2Lit( iObj, Acb_ObjIsTravIdCur(p, iObj)) );
    // mark roots
    Vec_IntForEachEntry( vRoots, iObj, i )
        Acb_ObjSetTravIdCur(p, iObj);
    // add TFO
    Vec_IntForEachEntry( vTfo, iObj, i )
        Vec_IntPush( vWin, Abc_Var2Lit( iObj, Acb_ObjIsTravIdCur(p, iObj)) );
    return vWin;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acb_NtkWindow( Acb_Ntk_t * p, int Pivot, int nTfiLevs, int nTfoLevs, int nFanMax, Vec_Int_t ** pvDivs )
{
    int nTfiLevMin = Acb_ObjLevelD(p, Pivot) - nTfiLevs;
    int nTfoLevMax = Acb_ObjLevelD(p, Pivot) + nTfoLevs;
    Vec_Int_t * vWin, * vDivs, * vTfo, * vRoots, * vSide, * vTfi;
    // collect divisors by traversing limited TFI
    vDivs = Acb_NtkDivisors( p, Pivot, nTfiLevMin );
    // mark limited TFO of the divisors
    Acb_ObjMarkTfo( p, vDivs, Pivot, nTfoLevMax, nFanMax );
    // collect TFO and roots
    Acb_ObjDeriveTfo( p, Pivot, nTfoLevMax, nFanMax, &vTfo, &vRoots );
    // collect side inputs of the TFO
    vSide = Acb_NtkCollectTfoSideInputs( p, Pivot, vTfo );
    // collect new TFI
    vTfi = Acb_NtkCollectNewTfi( p, Pivot, vSide );
    // collect all nodes
    vWin = Acb_NtkCollectWindow( p, Pivot, vTfi, vTfo, vRoots );
    // cleanup
    Vec_IntFree( vTfi );
    Vec_IntFree( vTfo );
    Vec_IntFree( vRoots );
    Vec_IntFree( vSide );
    *pvDivs = vDivs;
    return vWin;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acb_NtkFindSupp( sat_solver * pSat, Acb_Ntk_t * p, Vec_Int_t * vWin, Vec_Int_t * vDivs, int nBTLimit )
{
    int i, iObj, nDivsNew;
    // reload divisors in terms of SAT variables
    Vec_IntForEachEntry( vDivs, iObj, i )
        Vec_IntWriteEntry( vDivs, i, Acb_ObjCopy(p, iObj) );
    // try solving 
    nDivsNew = sat_solver_minimize_assumptions( pSat, Vec_IntArray(vDivs), Vec_IntSize(vDivs), nBTLimit );
    Vec_IntShrink( vDivs, nDivsNew );
    // reload divisors in terms of network variables
    Vec_IntForEachEntry( vDivs, iObj, i )
        Vec_IntWriteEntry( vDivs, i, Vec_IntEntry(vWin, iObj) );
    return Vec_IntSize(vDivs);
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acb_NtkOptNode( Acb_Ntk_t * p, int Pivot, int nTfiLevs, int nTfoLevs, int nFanMax )
{
    Vec_Int_t * vSupp = &p->vArray0;
    Vec_Int_t * vDivs, * vWin = Acb_NtkWindow( p, Pivot, nTfiLevs, nTfoLevs, nFanMax, &vDivs );
    sat_solver * pSat = Acb_NtkWindow2Solver( pSat, p, Pivot, vWin, 0 );
    int nSuppNew, Level = Acb_ObjLevelD( p, Pivot );

    // try solving the original support
    Vec_IntClear( vSupp );
    Vec_IntAppend( vSupp, vDivs );
    nSuppNew = sat_solver_minimize_assumptions( pSat, Vec_IntArray(vSupp), Vec_IntSize(vSupp), 0 );
    Vec_IntShrink( vSupp, nSuppNew );

    // try solving by level

    Acb_NtkUnmarkWindow( p, vWin );
    Vec_IntFree( vWin );
    Vec_IntFree( vDivs );

}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

