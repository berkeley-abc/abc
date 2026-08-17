/**CFile****************************************************************

  FileName    [acbXec.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Shared XEC proof helper API.]

***********************************************************************/

#ifndef ABC__base__acb__acbXec_h
#define ABC__base__acb__acbXec_h

#include "acb.h"
#include "sat/cnf/cnf.h"

ABC_NAMESPACE_HEADER_START

/*
 * XEC/network-level proof status:
 *   ACB_XEC_EQ         : networks/output are proven equivalent/UNSAT miter
 *   ACB_XEC_NEQ        : networks/output are proven different/SAT miter
 *   ACB_XEC_UNDEC      : proof was inconclusive
 *   ACB_XEC_ONE_HARD   : local sweep proved all but one output
 *   ACB_XEC_MANY_HARD  : local sweep left multiple hard outputs
 *
 */
typedef enum Acb_XecStatus_t_
{
    ACB_XEC_MANY_HARD = -3,
    ACB_XEC_ONE_HARD  = -2,
    ACB_XEC_UNDEC     = -1,
    ACB_XEC_NEQ       =  0,
    ACB_XEC_EQ        =  1
} Acb_XecStatus_t;

static inline void Acb_NtkPrintUnsupportedObj( Acb_Ntk_t * p, int iObj, const char * pWhere, int ExpectedFans, int ActualFans )
{
    printf( "%s unsupported ACB object: obj = %d", pWhere ? pWhere : "XEC" , iObj );
    if ( p && iObj >= 0 && iObj < Acb_NtkObjNumMax(p) )
        printf( ", type = %d", Acb_ObjType(p, iObj) );
    if ( ExpectedFans >= 0 || ActualFans >= 0 )
        printf( ", fanins = %d, expected = %d", ActualFans, ExpectedFans );
    printf( ".\n" );
}

static inline void Acb_XecMergeTargetStatus( int StatusTarget, int fHasModel, int * pStatus, int * pCheckModel )
{
    if ( fHasModel && pCheckModel )
        *pCheckModel = 1;
    if ( pStatus == NULL )
        return;
    if ( StatusTarget == ACB_XEC_EQ )
        *pStatus = ACB_XEC_EQ;
    else if ( StatusTarget == ACB_XEC_NEQ )
        *pStatus = ACB_XEC_NEQ;
}

extern int *      Acb_NtkSolveCadicalLimit( Gia_Man_t * p, int fUseHeavyOpt, int fVerbose, int * pStatus, int nSatTimeLimit, const char * pLabel, int fUseXecOutputClauses );
extern int        Acb_CnfCoDriverLit( Cnf_Dat_t * pCnf, int iCo, int * pLit );
extern int        Acb_GiaAllPosConst0( Gia_Man_t * p );

extern int        Acb_XecGiaSolveSmallConeExhaustive( Gia_Man_t * p, int fVerbose, int nTotalLimit );
extern Gia_Man_t *Acb_XecGiaSmallConeXorRewrite( Gia_Man_t * p, int fVerbose );

ABC_NAMESPACE_HEADER_END

#endif
