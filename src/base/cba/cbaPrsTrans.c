/**CFile****************************************************************

  FileName    [cbaPrsTrans.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Parse tree to netlist transformation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaPrsTrans.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "cbaPrs.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Count range size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Prs_ManRangeSizeName( Prs_Ntk_t * p, int Name )
{
    return 1;
}
static inline int Prs_ManRangeSizeRange( Prs_Ntk_t * p, int Range )
{
    char * pStr; 
    int Left, Right;
    if ( Range == 0 ) 
        return 1;
    pStr = Prs_NtkStr( p, Range );
    assert( pStr[0] == '[' );
    Left = Right = atoi( pStr + 1 );
    pStr = strstr( pStr, "=" );
    if ( pStr )
        Right = atoi( pStr + 1 );
    return 1 + (Left > Right ? Left - Right : Right - Left);
}
static inline int Prs_ManRangeSizeConst( Prs_Ntk_t * p, int Const )
{
    return atoi( Prs_NtkStr(p, Const) );
}
static inline int Prs_ManRangeSizeConcat( Prs_Ntk_t * p, int Con )
{
    extern int Prs_ManRangeSizeArray( Prs_Ntk_t * p, Vec_Int_t * vSlices, int Start, int Stop );
    Vec_Int_t * vSigs = Prs_CatSignals(p, Con);
    return Prs_ManRangeSizeArray( p, vSigs, 0, Vec_IntSize(vSigs) );
}
static inline int Prs_ManRangeSizeSignal( Prs_Ntk_t * p, int Sig )
{
    int Value = Abc_Lit2Var2( Sig );
    Prs_ManType_t Type = Abc_Lit2Att2( Sig );
    if ( Type == CBA_PRS_NAME )
        return Prs_ManRangeSizeName( p, Value );
    if ( Type == CBA_PRS_SLICE )
        return Prs_ManRangeSizeRange( p, Prs_SliceRange(p, Value) );
    if ( Type == CBA_PRS_CONST )
        return Prs_ManRangeSizeConst( p, Value );
    if ( Type == CBA_PRS_CONCAT )
        return Prs_ManRangeSizeConcat( p, Value );
    assert( 0 );
    return 0;
}
int Prs_ManRangeSizeArray( Prs_Ntk_t * p, Vec_Int_t * vSlices, int Start, int Stop )
{
    int i, Sig, Count = 0;
    assert( Vec_IntSize(vSlices) > 0 );
    Vec_IntForEachEntryStartStop( vSlices, Sig, i, Start, Stop )
        Count += Prs_ManRangeSizeSignal( p, Sig );
    return Count;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

