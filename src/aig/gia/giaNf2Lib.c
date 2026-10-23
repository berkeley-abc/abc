/**CFile****************************************************************

  FileName    [giaNf2Lib.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Compact standard-cell mapping.]

  Synopsis    [Optional library preprocessing for constant and repeated pins.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaNf2Lib.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "base/main/main.h"
#include "map/mio/mio.h"
#include "map/amap/amap.h"
#include "map/scl/sclCon.h"
#include "misc/util/utilTruth.h"
#include "misc/vec/vecMem.h"
#include "misc/vec/vecWec.h"
#include "misc/vec/vecStr.h"

ABC_NAMESPACE_IMPL_START

// Internal library view; restore physical cell IDs after mapping.
extern Gia_Man_t * Nf2_ManPerformMappingWithLib( Gia_Man_t * pGia, Jf_Par_t * pPars,
    Mio_Library_t * pMio, Amap_Lib_t * pAmap );

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

typedef struct Nf2_TieCell_t_
{
    word Truth;
    int Gate, nInputs;
    int Delays[6];
    // Nonnegative values name logical inputs; -1 and -2 denote 0 and 1.
    signed char Pins[6];
} Nf2_TieCell_t;

typedef struct Nf2_TieLib_t_
{
    Mio_Cell2_t * pSource;
    int nSource, nCells, nCap;
    Nf2_TieCell_t * pCells;
    int * pMap;
    Mio_Library_t * pMio;
    Amap_Lib_t * pAmap;
} Nf2_TieLib_t;

// As with the compiled mapper cache, workers release this thread's library
// with Nf2_LibClearCache (also called by Abc_Stop) before exiting.
static ABC_THREAD_LOCAL Nf2_TieLib_t * s_pNf2Ties;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Releases the optional library without touching the real library.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Nf2_LibClearCache( void )
{
    Nf2_TieLib_t * p = s_pNf2Ties;
    if ( p == NULL ) return;
    if ( p->pMio ) Mio_LibraryDelete( p->pMio );
    if ( p->pAmap ) Amap_LibFree( p->pAmap );
    ABC_FREE( p->pSource );
    ABC_FREE( p->pCells );
    ABC_FREE( p->pMap );
    ABC_FREE( s_pNf2Ties );
}

/**Function*************************************************************

  Synopsis    [Evaluates a physical cell under a pin assignment.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Nf2_TieTruth( Mio_Cell2_t * pCell, signed char * pPins )
{
    word Truth = 0;
    int m, k, Index;
    for ( m = 0; m < 64; m++ )
    {
        Index = 0;
        for ( k = 0; k < (int)pCell->nFanins; k++ )
            if ( pPins[k] == -2 || (pPins[k] >= 0 && ((m >> pPins[k]) & 1)) )
                Index |= 1 << k;
        Truth |= ((pCell->uTruth >> Index) & 1) << m;
    }
    return Truth;
}

/**Function*************************************************************

  Synopsis    [Keeps one implementation per truth, as the normal library does.]

  Description [Area is primary, then average pin delay. Equal costs keep the
  first implementation, so original cells win ties. Basic constants, buffers,
  and inverters retain their ordinary implementations.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_TieAdd( Nf2_TieLib_t * p, int Gate, signed char * pPins, int nInputs )
{
    Mio_Cell2_t * pSource = p->pSource + Gate;
    Nf2_TieCell_t Cell, * pOld;
    int Remap[6], i, k, nUsed = 0, DelayConst = 0, DelayNew = 0, DelayOld = 0;
    memset( &Cell, 0, sizeof(Cell) );
    Cell.Gate = Gate;
    Cell.Truth = Nf2_TieTruth( pSource, pPins );
    for ( i = 0; i < nInputs; i++ )
        Remap[i] = Abc_Tt6HasVar(Cell.Truth, i) ? nUsed++ : -1;
    if ( nUsed < 2 && Gate >= 4 ) return;
    Cell.nInputs = nUsed;
    for ( k = 0; k < (int)pSource->nFanins; k++ )
    {
        // A vacuous logical input maps to -1, tying its physical pin to zero.
        // It consequently participates in the constant-pin delay floor below.
        int Pin = pPins[k] < 0 ? pPins[k] : Remap[(int)pPins[k]];
        Cell.Pins[k] = (signed char)Pin;
        if ( Pin < 0 ) DelayConst = Abc_MaxInt( DelayConst, pSource->iDelays[k] );
        else Cell.Delays[Pin] = Abc_MaxInt( Cell.Delays[Pin], pSource->iDelays[k] );
    }
    Cell.Truth = Nf2_TieTruth( pSource, Cell.Pins );
    // A constant pin can contribute to the reported delay after &put. This
    // conservative bound represents it without changing the mapper's model.
    for ( i = 0; i < nUsed; i++ )
    {
        Cell.Delays[i] = Abc_MaxInt( Cell.Delays[i], DelayConst );
        DelayNew += Cell.Delays[i];
    }
    for ( i = 0; i < p->nCells; i++ )
        if ( p->pCells[i].Truth == Cell.Truth )
        {
            pOld = p->pCells + i;
            if ( p->pSource[pOld->Gate].AreaF < pSource->AreaF ) return;
            if ( p->pSource[pOld->Gate].AreaF == pSource->AreaF )
            {
                for ( k = 0; k < pOld->nInputs; k++ ) DelayOld += pOld->Delays[k];
                if ( DelayOld <= DelayNew ) return;
            }
            *pOld = Cell;
            return;
        }
    if ( p->nCells == p->nCap )
    {
        p->nCap = p->nCap ? 2 * p->nCap : 128;
        p->pCells = ABC_REALLOC( Nf2_TieCell_t, p->pCells, p->nCap );
    }
    p->pCells[p->nCells++] = Cell;
}

/**Function*************************************************************

  Synopsis    [Enumerates constant ties and partitions of the remaining pins.]

  Description [Groups are numbered by first occurrence. Thus permutations of
  logical inputs are left to ordinary library matching, not re-enumerated.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_TieEnumerate( Nf2_TieLib_t * p, int Gate, signed char * pPins, int Pin, int nInputs )
{
    int i;
    if ( Pin == (int)p->pSource[Gate].nFanins )
    {
        if ( nInputs >= 2 && nInputs < Pin ) Nf2_TieAdd( p, Gate, pPins, nInputs );
        return;
    }
    for ( i = -2; i <= nInputs; i++ )
    {
        pPins[Pin] = (signed char)i;
        Nf2_TieEnumerate( p, Gate, pPins, Pin + 1, nInputs + (i == nInputs) );
    }
}

/**Function*************************************************************

  Synopsis    [Writes an in-memory GENLIB with stable logical pin order.]

  Description [Complete minterms make the parser encounter inputs in order.
  The library is small and this work is cached once per physical library.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Str_t * Nf2_TieGenlib( Nf2_TieLib_t * p )
{
    Vec_Str_t * v = Vec_StrAlloc( 4096 );
    Nf2_TieCell_t * pCell;
    int i, k, m, First;
    for ( i = 0; i < p->nCells; i++ )
    {
        pCell = p->pCells + i;
        // Preserve the original double area so both AreaF and AreaW round-trip.
        Vec_StrPrintF( v, "GATE nf2tie%d %.17g Y=", i,
            Mio_GateReadArea((Mio_Gate_t *)p->pSource[pCell->Gate].pMioGate) );
        if ( !pCell->nInputs ) Vec_StrPrintF( v, "CONST%d", pCell->Truth != 0 );
        else
        for ( m = 0, First = 1; m < (1 << pCell->nInputs); m++ )
            if ( (pCell->Truth >> m) & 1 )
            {
                if ( !First ) Vec_StrPush( v, '+' );
                First = 0;
                Vec_StrPush( v, '(' );
                for ( k = 0; k < pCell->nInputs; k++ )
                {
                    if ( k ) Vec_StrPush( v, '*' );
                    if ( !((m >> k) & 1) ) Vec_StrPush( v, '!' );
                    Vec_StrPrintF( v, "x%d", k );
                }
                Vec_StrPush( v, ')' );
            }
        Vec_StrAppend( v, ";\n" );
        // Use the middle of the integer-delay bin, avoiding truncation below
        // its boundary when the decimal value is parsed back into a double.
        for ( k = 0; k < pCell->nInputs; k++ )
            Vec_StrPrintF( v, "PIN x%d UNKNOWN 1 999 %.17g 0 %.17g 0\n", k,
                (pCell->Delays[k] + 0.5) / SCL_NUM, (pCell->Delays[k] + 0.5) / SCL_NUM );
    }
    Vec_StrAppend( v, ".end\n" );
    Vec_StrPush( v, 0 );
    return v;
}

/**Function*************************************************************

  Synopsis    [Compiles a private ordinary library from the restricted cells.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Nf2_TieLib_t * Nf2_TiePrepare( Mio_Cell2_t * pCells, int nCells )
{
    Nf2_TieLib_t * p = s_pNf2Ties;
    Vec_Str_t * vText;
    char * pCopy;
    signed char Pins[6];
    int i, k;
    if ( p && p->nSource == nCells && !memcmp(p->pSource, pCells, sizeof(Mio_Cell2_t) * nCells) )
        return p;
    Nf2_LibClearCache();
    s_pNf2Ties = p = ABC_CALLOC( Nf2_TieLib_t, 1 );
    p->nSource = nCells;
    p->pSource = ABC_ALLOC( Mio_Cell2_t, nCells );
    memcpy( p->pSource, pCells, sizeof(Mio_Cell2_t) * nCells );
    for ( i = 0; i < nCells; i++ )
    {
        for ( k = 0; k < (int)pCells[i].nFanins; k++ ) Pins[k] = (signed char)k;
        Nf2_TieAdd( p, i, Pins, pCells[i].nFanins );
    }
    for ( i = 4; i < nCells; i++ ) Nf2_TieEnumerate( p, i, Pins, 0, 0 );
    vText = Nf2_TieGenlib( p );
    pCopy = Abc_UtilStrsav( Vec_StrArray(vText) );
    p->pMio = Mio_LibraryRead( (char *)"nf2-tied-pins", pCopy, NULL, 6, 0 );
    ABC_FREE( pCopy );
    p->pAmap = Amap_LibReadAndPrepare( (char *)"nf2-tied-pins", Vec_StrArray(vText), 0, 0 );
    Vec_StrFree( vText );
    if ( p->pMio == NULL || p->pAmap == NULL )
    {
        Nf2_LibClearCache();
        return NULL;
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Restores physical gates, their original pin order, and tie wires.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Nf2_TieExpand( Nf2_TieLib_t * p, Gia_Man_t * pGia, Jf_Par_t * pPars )
{
    Vec_Int_t * v = Vec_IntStart( 2 * Gia_ManObjNum(pGia) );
    Nf2_TieCell_t * pCell;
    int Lit, k, Pin, nTied = 0, nConst = 0, nRepeat = 0, Mask;
    Gia_ManForEachCell( pGia, Lit )
    {
        int Entry = Vec_IntEntry( pGia->vCellMapping, Lit );
        if ( Entry < 0 ) { Vec_IntWriteEntry(v, Lit, Entry); continue; }
        pCell = p->pCells + p->pMap[Gia_ObjCellId(pGia, Lit)];
        Vec_IntWriteEntry( v, Lit, Vec_IntSize(v) );
        Vec_IntPush( v, p->pSource[pCell->Gate].nFanins );
        Mask = 0;
        for ( k = 0; k < (int)p->pSource[pCell->Gate].nFanins; k++ )
        {
            Pin = pCell->Pins[k];
            Vec_IntPush( v, Pin < 0 ? -1 - Pin : Gia_ObjCellFanin(pGia, Lit, Pin) );
            if ( Pin < 0 ) nConst++;
            else { nRepeat += (Mask >> Pin) & 1; Mask |= 1 << Pin; }
        }
        Vec_IntPush( v, pCell->Gate );
        pPars->Edge += p->pSource[pCell->Gate].nFanins - pCell->nInputs;
        nTied += (int)p->pSource[pCell->Gate].nFanins > pCell->nInputs;
    }
    Vec_IntFree( pGia->vCellMapping );
    pGia->vCellMapping = v;
    if ( pPars->fVerbose )
        Abc_Print( 1, "Tied-pin cells: %d used (%d constant pins, %d repeated pins).\n", nTied, nConst, nRepeat );
}

/**Function*************************************************************

  Synopsis    [Maps using an optional library view, then restores physical pins.]

  Description [No enumeration, matching, or recovery algorithm is changed.
  Private libraries are passed explicitly; the frame's libraries are unchanged.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Nf2_ManPerformMappingTied( Gia_Man_t * pGia, Jf_Par_t * pPars )
{
    Mio_Library_t * pMio = (Mio_Library_t *)Abc_FrameReadLibGen();
    Vec_Mem_t * vTruths;
    Vec_Wec_t * vMatches;
    Mio_Cell2_t * pCells;
    Nf2_TieLib_t * p;
    Gia_Man_t * pResult;
    int nCells, i, Id;
    abctime clk = Abc_Clock();
    if ( pGia == NULL || pPars == NULL || pMio == NULL ) return NULL;
    Mio_LibraryMatchesFetch( pMio, &vTruths, &vMatches, &pCells, &nCells, 0, pPars->fPinPerm, pPars->fPinQuick );
    if ( pCells == NULL ) return NULL;
    p = Nf2_TiePrepare( pCells, nCells );
    if ( p == NULL ) return NULL;
    Mio_LibraryMatchesFetch( p->pMio, &vTruths, &vMatches, &pCells, &nCells, 0, pPars->fPinPerm, pPars->fPinQuick );
    if ( pCells == NULL )
        return NULL;
    ABC_FREE( p->pMap );
    p->pMap = ABC_ALLOC( int, nCells );
    // Match-table gate IDs can change when pin-matching options change.
    for ( i = 0; i < nCells; i++ )
    {
        Id = atoi( pCells[i].pName + 6 );
        assert( Id >= 0 && Id < p->nCells && pCells[i].uTruth == p->pCells[Id].Truth );
        p->pMap[i] = Id;
    }
    if ( pPars->fVerbose )
    {
        Abc_Print( 1, "Tied-pin library: %d original cells, %d logical cells. ", p->nSource, nCells );
        Abc_PrintTime( 1, "Prepare", Abc_Clock() - clk );
    }
    pResult = Nf2_ManPerformMappingWithLib( pGia, pPars, p->pMio, p->pAmap );
    if ( pResult ) Nf2_TieExpand( p, pResult, pPars );
    return pResult;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
