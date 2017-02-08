/**CFile****************************************************************

  FileName    [giaSatoko.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Interface to Satoko solver.]

  Author      [Alan Mishchenko, Bruno Schmitt]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSatoko.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "sat/cnf/cnf.h"
#include "sat/satoko/satoko.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern Cnf_Dat_t * Mf_ManGenerateCnf( Gia_Man_t * pGia, int nLutSize, int fCnfObjIds, int fAddOrCla, int fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
satoko_t * Gia_ManCreateSatoko( Gia_Man_t * p )
{
    satoko_t * pSat = satoko_create();
    Cnf_Dat_t * pCnf = Mf_ManGenerateCnf( p, 8, 0, 1, 0 );
    int i, status;
    //sat_solver_setnvars( pSat, p->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        if ( !satoko_add_clause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1]-pCnf->pClauses[i] ) )
        {
            Cnf_DataFree( pCnf );
            satoko_destroy( pSat );
            return NULL;
        }
    }
    Cnf_DataFree( pCnf );
    status = satoko_simplify(pSat);
    if ( status == SATOKO_OK )
        return pSat;
    satoko_destroy( pSat );
    return NULL;
}
void Gia_ManCallSatokoOne( Gia_Man_t * p, satoko_opts_t * opts, int iOutput )
{
    abctime clk = Abc_Clock();
    satoko_t * pSat;
    int status;

    pSat = Gia_ManCreateSatoko( p );
    if ( pSat )
    {
        satoko_configure(pSat, opts);
        status = satoko_solve( pSat );
        satoko_destroy( pSat );
    }
    else 
        status = SATOKO_UNSAT;

    if ( iOutput >= 0 )
        Abc_Print( 1, "Output %6d : ", iOutput );
    else
        Abc_Print( 1, "Total: " );

    if ( status == SATOKO_UNDEC )
        Abc_Print( 1, "UNDECIDED      " );
    else if ( status == SATOKO_SAT )
        Abc_Print( 1, "SATISFIABLE    " );
    else
        Abc_Print( 1, "UNSATISFIABLE  " );

    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}
void Gia_ManCallSatoko( Gia_Man_t * p, satoko_opts_t * opts, int fSplit )
{
    if ( fSplit )
    {
        Gia_Man_t * pOne;
        Gia_Obj_t * pRoot;
        int i;
        Gia_ManForEachCo( p, pRoot, i )
        {
            pOne = Gia_ManDupDfsCone( p, pRoot );
            Gia_ManCallSatokoOne( pOne, opts, i );
            Gia_ManStop( pOne );
        }
        return;
    }
    Gia_ManCallSatokoOne( p, opts, -1 );
}    


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

