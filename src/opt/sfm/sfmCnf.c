/**CFile****************************************************************

  FileName    [sfmCnf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [CNF computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmCnf.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"
#include "bool/kit/kit.h"

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
int Sfm_TruthToCnf( word Truth, int nVars, Vec_Int_t * vCover, Vec_Str_t * vCnf )
{
    Vec_StrClear( vCnf );
    if ( Truth == 0 || ~Truth == 0 )
    {
        Vec_StrPush( vCnf, (char)(Truth == 0) );
        Vec_StrPush( vCnf, -1 );
        return 1;
    }
    else 
    {
        int i, k, c, RetValue, Literal, Cube, nCubes = 0;
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
                Vec_StrPush( vCnf, -1 );
            }
        }
        return nCubes;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_DeriveCnfs( Vec_Wrd_t * vTruths, Vec_Int_t * vFanins, Vec_Str_t ** pvCnfs, Vec_Int_t ** pvOffsets )
{
    Vec_Str_t * vCnfs, * vCnf;
    Vec_Int_t * vOffsets, * vCover;
    int i, k, nFanins, nClauses = 0;
    vCnf     = Vec_StrAlloc( 1000 );
    vCnfs    = Vec_StrAlloc( 1000 );
    vOffsets = Vec_IntAlloc( Vec_IntSize(vFanins) );
    vCover   = Vec_IntAlloc( 1 << 16 );
    assert( Vec_WrdSize(vTruths) == Vec_IntSize(vFanins) );
    Vec_IntForEachEntry( vFanins, nFanins, i )
    {
        nClauses += Sfm_TruthToCnf( Vec_WrdEntry(vTruths, i), nFanins, vCover, vCnf );
        Vec_IntPush( vOffsets, Vec_StrSize(vCnfs) );
        for ( k = 0; k < Vec_StrSize(vCnf); k++ )
            Vec_StrPush( vCnfs, Vec_StrEntry(vCnf, k) );
    }
    Vec_IntPush( vOffsets, Vec_StrSize(vCnfs) );
    Vec_StrFree( vCnf );
    Vec_IntFree( vCover );
    return nClauses;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

