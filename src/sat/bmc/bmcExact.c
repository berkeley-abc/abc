/**CFile****************************************************************

  FileName    [bmcExact.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Shared input, output, and minimum-search handling.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 8, 2026.]

***********************************************************************/

#include "bmcExact.h"
#include "aig/aig/aig.h"
#include "aig/gia/giaAig.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads explicit hex, or the current combinational network.]

  Description [A negative input count requests inference. Keep the original
               PI order and all unused inputs for subsequent verification.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_ExactRead( Abc_Frame_t * pAbc, const char * pHex, int nInputs, int nMaxInputs, Bmc_Exact_t * p )
{
    Abc_Ntk_t * pAig, * pLogic;
    Gia_Man_t * pGia;
    word * pSource;
    int i, n, nVars;
    memset(p, 0, sizeof(*p));
    assert( nMaxInputs >= 2 && nMaxInputs <= 16 );
    if ( pHex )
    {
        if ( pHex[0] == '0' && (pHex[1] == 'x' || pHex[1] == 'X') ) pHex += 2;
        n = (int)strlen(pHex);
        if ( n < 1 || n > (1 << (nMaxInputs-2)) || (n & (n-1)) )
        {
            Abc_Print(-1, "Hex length must be a power of two, at most %d digits.\n", 1 << (nMaxInputs-2));
            return 0;
        }
        for ( i = 0; i < n; ++i )
            if ( !Abc_TtIsHexDigit(pHex[i]) )
            {
                Abc_Print(-1, "Invalid hexadecimal digit.\n");
                return 0;
            }
        nVars = 2 + (n == 1 ? 0 : Abc_Base2Log(n));
        if ( nInputs >= 0 && nInputs != nVars && !(n == 1 && nInputs < 2) )
        {
            Abc_Print(-1, "Hex length disagrees with the specified input count.\n");
            return 0;
        }
        p->nVars = nInputs < 0 ? nVars : nInputs;
        p->pTruth = ABC_CALLOC(word, Abc_TtWordNum(p->nVars));
        for ( i = 0; i < n; ++i )
            Abc_TtSetHex(p->pTruth, i, Abc_TtReadHexDigit(pHex[n-1-i]));
        if ( p->nVars < 2 && (p->pTruth[0] >> (1 << p->nVars)) )
        {
            Abc_Print(-1, "Hex has nonzero bits outside the specified input space.\n");
            ABC_FREE(p->pTruth);
            return 0;
        }
    }
    else
    {
        p->pNtk = Abc_FrameReadNtk(pAbc);
        if ( !p->pNtk || Abc_NtkBoxNum(p->pNtk) || Abc_NtkCoNum(p->pNtk) != 1 ||
             Abc_NtkCiNum(p->pNtk) > nMaxInputs )
        {
            Abc_Print(-1, "Provide hex or a single-output combinational network with at most %d inputs.\n", nMaxInputs);
            return 0;
        }
        assert( Abc_NtkCoNum(p->pNtk) == 1 );
        assert( Abc_NtkCiNum(p->pNtk) <= nMaxInputs );
        p->nVars = Abc_NtkCiNum(p->pNtk);
        if ( nInputs >= 0 && nInputs != p->nVars )
        {
            Abc_Print(-1, "The specified input count disagrees with the current network.\n");
            return 0;
        }
        // Strashing accepts logic networks and AIGs, but not netlists.
        // Strashing also changes the local function representation of logic
        // nodes. Use a temporary to keep failed searches from changing it.
        pLogic = Abc_NtkIsStrash(p->pNtk) ? p->pNtk :
            Abc_NtkIsNetlist(p->pNtk) ? Abc_NtkToLogic(p->pNtk) : Abc_NtkDup(p->pNtk);
        if ( !pLogic ) { Abc_Print(-1, "Cannot convert the current netlist to logic.\n"); return 0; }
        pAig = Abc_NtkIsStrash(pLogic) ? pLogic : Abc_NtkStrash(pLogic, 0, 0, 0);
        if ( pLogic != p->pNtk ) Abc_NtkDelete(pLogic);
        if ( !pAig ) { Abc_Print(-1, "Cannot strash the current network.\n"); return 0; }
        pGia = Abc_NtkStrashToGia(pAig);
        if ( pAig != p->pNtk ) Abc_NtkDelete(pAig);
        if ( !pGia ) { Abc_Print(-1, "Cannot derive the current network's AIG.\n"); return 0; }
        pSource = Gia_ObjComputeTruthTable(pGia, Gia_ManCo(pGia, 0));
        p->pTruth = ABC_ALLOC(word, Abc_TtWordNum(p->nVars));
        Abc_TtCopy(p->pTruth, pSource, Abc_TtWordNum(p->nVars), 0);
        Gia_ManStop(pGia);
    }
    if ( p->nVars < 6 ) p->pTruth[0] = Abc_Tt6Stretch(p->pTruth[0], p->nVars);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Verifies and installs a solution as the current ABC network.]

  Description [Consumes pGia only on success. The independent GIA space is
               preserved. Failure leaves the current network unchanged.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_ExactInstall( Abc_Frame_t * pAbc, Gia_Man_t * pGia, Bmc_Exact_t * p )
{
    Abc_Ntk_t * pNew;
    Aig_Man_t * pAig;
    word * pTruth;
    int i, fEqual;
    if ( !pGia || Gia_ManRegNum(pGia) || Gia_ManCoNum(pGia) != 1 || Gia_ManCiNum(pGia) != p->nVars )
    {
        Abc_Print(-1, "Internal error: synthesized AIG has an invalid interface.\n");
        return 0;
    }
    pTruth = Gia_ObjComputeTruthTable(pGia, Gia_ManCo(pGia, 0));
    fEqual = Abc_TtEqual(p->pTruth, pTruth, Abc_TtWordNum(p->nVars));
    Gia_ObjComputeTruthTableStop(pGia);
    if ( !fEqual )
    {
        Abc_Print(-1, "Internal error: exported AIG failed exhaustive verification.\n");
        return 0;
    }
    pAig = Gia_ManToAigSimple(pGia);
    if ( !pAig ) return 0;
    pNew = Abc_NtkFromAigPhase(pAig);
    Aig_ManStop(pAig);
    if ( !pNew ) return 0;
    ABC_FREE(pNew->pName);
    pNew->pName = Abc_UtilStrsav(p->pNtk ? Abc_NtkName(p->pNtk) : pGia->pName ? pGia->pName : (char *)"exact");
    if ( p->pNtk )
    {
        ABC_FREE(pNew->pSpec);
        if ( p->pNtk->pSpec ) pNew->pSpec = Abc_UtilStrsav(p->pNtk->pSpec);
        Nm_ManFree(pNew->pManName);
        pNew->pManName = Nm_ManCreate(p->nVars+1);
        for ( i = 0; i < p->nVars; ++i )
            Abc_ObjAssignName(Abc_NtkCi(pNew, i), Abc_ObjName(Abc_ObjFanout0Ntk(Abc_NtkCi(p->pNtk, i))), NULL);
        Abc_ObjAssignName(Abc_NtkCo(pNew, 0), Abc_ObjName(Abc_ObjFanin0Ntk(Abc_NtkCo(p->pNtk, 0))), NULL);
    }
    if ( !Abc_NtkCheck(pNew) ) { Abc_NtkDelete(pNew); return 0; }
    Abc_FrameReplaceCurrentNetwork(pAbc, pNew);
    Gia_ManStop(pGia);
    p->pNtk = NULL;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Hashes a LUT into an AIG; pin zero is the address LSB.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_ExactLut( Gia_Man_t * pGia, const word * pTruth, const int * pFans, int nFans, int Offset )
{
    int Lit0, Lit1;
    if ( !nFans ) return (int)((pTruth[Offset >> 6] >> (Offset & 63)) & 1);
    Lit0 = Bmc_ExactLut(pGia, pTruth, pFans, nFans-1, Offset);
    Lit1 = Bmc_ExactLut(pGia, pTruth, pFans, nFans-1, Offset+(1 << (nFans-1)));
    return Gia_ManHashMux(pGia, pFans[nFans-1], Lit1, Lit0);
}

/**Function*************************************************************

  Synopsis    [Advances minimum search after UNSAT or a bounded UNKNOWN.]

  Description [A larger UNSAT never closes a skipped smaller count.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bmc_ExactContinue( int Status, int fMinimum, int nSeconds, int Count, int * pFirstUnknown )
{
    if ( !fMinimum ) return 0;
    if ( Status == 0 && *pFirstUnknown < 0 ) *pFirstUnknown = Count;
    return Status == 20 || (Status == 0 && nSeconds > 0);
}

/**Function*************************************************************

  Synopsis    [Reports minimum-search bounds without treating UNKNOWN as UNSAT.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_ExactReport( int Status, int FirstUnknown, int Count, int Limit, const char * pUnit, const char * pScope )
{
    if ( Status == 10 && FirstUnknown < 0 )
        Abc_Print(1, "Minimum %s count%s = %d.\n", pUnit, pScope, Count);
    else if ( Status == 10 )
        Abc_Print(1, "Solution uses %d %ss%s (upper bound); count %d is undecided, so the minimum is not established.\n", Count, pUnit, pScope, FirstUnknown);
    else if ( Status >= 0 && FirstUnknown >= 0 )
        Abc_Print(1, "Search incomplete%s; proved lower bound = %d %ss. No minimum is claimed.\n", pScope, FirstUnknown, pUnit);
    else if ( Status == 20 )
        Abc_Print(1, "No solution with at most %d %ss%s.\n", Limit, pUnit, pScope);
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
