/**CFile****************************************************************

  FileName    [dauGia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware unmapping.]

  Synopsis    [Coverting DSD into GIA.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: dauGia.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dauInt.h"
#include "aig/gia/gia.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Kit_TruthToGia( Gia_Man_t * pMan, unsigned * pTruth, int nVars, Vec_Int_t * vMemory, Vec_Int_t * vLeaves, int fHash );

#define DAU_DSD_MAX_VAR 8

static int m_Calls = 0;
static int m_NonDsd = 0;
static int m_Non1Step = 0;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Derives GIA for the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dau_DsdToGiaCompose_rec( Gia_Man_t * pGia, word Func, int * pFanins, int nVars )
{
    int t0, t1;
    if ( Func == 0 )
        return 0;
    if ( Func == ~(word)0 )
        return 1;
    assert( nVars > 0 );
    if ( --nVars == 0 )
    {
        assert( Func == s_Truths6[0] || Func == s_Truths6Neg[0] );
        return Abc_LitNotCond( pFanins[0], (int)(Func == s_Truths6Neg[0]) );
    }
    if ( !Abc_Tt6HasVar(Func, nVars) )
        return Dau_DsdToGiaCompose_rec( pGia, Func, pFanins, nVars );
    t0 = Dau_DsdToGiaCompose_rec( pGia, Abc_Tt6Cofactor0(Func, nVars), pFanins, nVars );
    t1 = Dau_DsdToGiaCompose_rec( pGia, Abc_Tt6Cofactor1(Func, nVars), pFanins, nVars );
    if ( pGia->pMuxes )
        return Gia_ManHashMuxReal( pGia, pFanins[nVars], t1, t0 );
    else
        return Gia_ManHashMux( pGia, pFanins[nVars], t1, t0 );
}

/**Function*************************************************************

  Synopsis    [Derives GIA for the DSD formula.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dau_DsdToGia_rec( Gia_Man_t * pGia, char * pStr, char ** p, int * pMatches, int * pLits, Vec_Int_t * vCover )
{
    int fCompl = 0;
    if ( **p == '!' )
        (*p)++, fCompl = 1;
    if ( **p >= 'a' && **p < 'a' + DAU_DSD_MAX_VAR ) // var
        return Abc_LitNotCond( pLits[**p - 'a'], fCompl );
    if ( **p == '(' ) // and/or
    {
        char * q = pStr + pMatches[ *p - pStr ];
        int Res = 1, Lit;
        assert( **p == '(' && *q == ')' );
        for ( (*p)++; *p < q; (*p)++ )
        {
            Lit = Dau_DsdToGia_rec( pGia, pStr, p, pMatches, pLits, vCover );
            Res = Gia_ManHashAnd( pGia, Res, Lit );
        }
        assert( *p == q );
        return Abc_LitNotCond( Res, fCompl );
    }
    if ( **p == '[' ) // xor
    {
        char * q = pStr + pMatches[ *p - pStr ];
        int Res = 0, Lit;
        assert( **p == '[' && *q == ']' );
        for ( (*p)++; *p < q; (*p)++ )
        {
            Lit = Dau_DsdToGia_rec( pGia, pStr, p, pMatches, pLits, vCover );
            if ( pGia->pMuxes )
                Res = Gia_ManHashXorReal( pGia, Res, Lit );
            else
                Res = Gia_ManHashXor( pGia, Res, Lit );
        }
        assert( *p == q );
        return Abc_LitNotCond( Res, fCompl );
    }
    if ( **p == '<' ) // mux
    {
        int nVars = 0;
        int Temp[3], * pTemp = Temp, Res;
        int Fanins[DAU_DSD_MAX_VAR], * pLits2;
        char * pOld = *p;
        char * q = pStr + pMatches[ *p - pStr ];
        // read fanins
        if ( *(q+1) == '{' )
        {
            char * q2;
            *p = q+1;
            q2 = pStr + pMatches[ *p - pStr ];
            assert( **p == '{' && *q2 == '}' );
            for ( nVars = 0, (*p)++; *p < q2; (*p)++, nVars++ )
                Fanins[nVars] = Dau_DsdToGia_rec( pGia, pStr, p, pMatches, pLits, vCover );
            assert( *p == q2 );
            pLits2 = Fanins;
        }
        else
            pLits2 = pLits;
        // read MUX
        *p = pOld;
        q = pStr + pMatches[ *p - pStr ];
        assert( **p == '<' && *q == '>' );
        // verify internal variables
        if ( nVars )
            for ( ; pOld < q; pOld++ )
                if ( *pOld >= 'a' && *pOld <= 'z' )
                    assert( *pOld - 'a' < nVars );
        // derive MUX components
        for ( (*p)++; *p < q; (*p)++ )
            *pTemp++ = Dau_DsdToGia_rec( pGia, pStr, p, pMatches, pLits2, vCover );
        assert( pTemp == Temp + 3 );
        assert( *p == q );
        if ( *(q+1) == '{' ) // and/or
        {
            char * q = pStr + pMatches[ ++(*p) - pStr ];
            assert( **p == '{' && *q == '}' );
            *p = q;
        }
        if ( pGia->pMuxes )
            Res = Gia_ManHashMuxReal( pGia, Temp[0], Temp[1], Temp[2] );
        else
            Res = Gia_ManHashMux( pGia, Temp[0], Temp[1], Temp[2] );
        return Abc_LitNotCond( Res, fCompl );
    }
    if ( (**p >= 'A' && **p <= 'F') || (**p >= '0' && **p <= '9') )
    {
        Vec_Int_t vLeaves;  char * q;
        word pFunc[DAU_DSD_MAX_VAR > 6 ? (1 << (DAU_DSD_MAX_VAR-6)) : 1];
        int Fanins[DAU_DSD_MAX_VAR], Res; 
        int i, nVars = Abc_TtReadHex( pFunc, *p );
        *p += Abc_TtHexDigitNum( nVars );
        q = pStr + pMatches[ *p - pStr ];
        assert( **p == '{' && *q == '}' );
        for ( i = 0, (*p)++; *p < q; (*p)++, i++ )
            Fanins[i] = Dau_DsdToGia_rec( pGia, pStr, p, pMatches, pLits, vCover );
        assert( i == nVars );
        assert( *p == q );
//        Res = Dau_DsdToGiaCompose_rec( pGia, Func, Fanins, nVars );
        vLeaves.nCap = nVars;
        vLeaves.nSize = nVars;
        vLeaves.pArray = Fanins;        
        Res = Kit_TruthToGia( pGia, (unsigned *)pFunc, nVars, vCover, &vLeaves, 1 );
        m_Non1Step++;
        return Abc_LitNotCond( Res, fCompl );
    }
    assert( 0 );
    return 0;
}
int Dau_DsdToGia( Gia_Man_t * pGia, char * p, int * pLits, Vec_Int_t * vCover )
{
    int Res;
    if ( *p == '0' && *(p+1) == 0 )
        Res = 0;
    else if ( *p == '1' && *(p+1) == 0 )
        Res = 1;
    else
        Res = Dau_DsdToGia_rec( pGia, p, &p, Dau_DsdComputeMatches(p), pLits, vCover );
    assert( *++p == 0 );
    return Res;
}

/**Function*************************************************************

  Synopsis    [Convert TT to GIA via DSD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dsm_ManTruthToGia( void * p, word * pTruth, Vec_Int_t * vLeaves, Vec_Int_t * vCover )
{
    Gia_Man_t * pGia = (Gia_Man_t *)p;
    char pDsd[1000];
    int nSizeNonDec;
    m_Calls++;
    assert( Vec_IntSize(vLeaves) <= DAU_DSD_MAX_VAR );
//    static int Counter = 0; Counter++;
    nSizeNonDec = Dau_DsdDecompose( pTruth, Vec_IntSize(vLeaves), 0, 1, pDsd );
    if ( nSizeNonDec )
        m_NonDsd++;
//    printf( "%s\n", pDsd );
    return Dau_DsdToGia( pGia, pDsd, Vec_IntArray(vLeaves), vCover );
}

/**Function*************************************************************

  Synopsis    [Convert TT to GIA via DSD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dsm_ManReportStats()
{
    printf( "Calls = %d. NonDSD = %d. Non1Step = %d.\n", m_Calls, m_NonDsd, m_Non1Step );
    m_Calls = m_NonDsd = m_Non1Step = 0;
}

/**Function*************************************************************

  Synopsis    [Performs structural hashing on the LUT functions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Dsm_ManDeriveGia( void * pGia, int fUseMuxes )
{
    Gia_Man_t * p = (Gia_Man_t *)pGia;
    Gia_Man_t * pNew, * pTemp;
    Vec_Int_t * vCover, * vLeaves;
    Gia_Obj_t * pObj; 
    int k, i, iLut, iVar;
    word * pTruth;
    assert( Gia_ManHasMapping(p) );   
    // create new manager
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    if ( fUseMuxes )
        pNew->pMuxes = ABC_CALLOC( unsigned, pNew->nObjsAlloc );
    // map primary inputs
    Gia_ManFillValue(p);
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    // iterate through nodes used in the mapping
    vLeaves = Vec_IntAlloc( 16 );
    vCover  = Vec_IntAlloc( 1 << 16 );
    Gia_ManHashStart( pNew );
    Gia_ObjComputeTruthTableStart( p, Gia_ManLutSizeMax(p) );
    Gia_ManForEachLut( p, iLut )
    {
        // collect leaves
        Vec_IntClear( vLeaves );
        Gia_LutForEachFanin( p, iLut, iVar, k )
            Vec_IntPush( vLeaves, iVar );
        pTruth = Gia_ObjComputeTruthTableCut( p, Gia_ManObj(p, iLut), vLeaves );
        // collect incoming literals
        Vec_IntClear( vLeaves );
        Gia_LutForEachFanin( p, iLut, iVar, k )
            Vec_IntPush( vLeaves, Gia_ManObj(p, iVar)->Value );
        Gia_ManObj(p, iLut)->Value = Dsm_ManTruthToGia( pNew, pTruth, vLeaves, vCover );
    }
    Gia_ObjComputeTruthTableStop( p );
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Vec_IntFree( vLeaves );
    Vec_IntFree( vCover );
    // perform cleanup
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

