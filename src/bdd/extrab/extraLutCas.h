/**CFile****************************************************************

  FileName    [extraLutCas.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [LUT cascade decomposition.]

  Description [LUT cascade decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 6, 2024.]

  Revision    [$Id: extraLutCas.h,v 1.00 2024/08/06 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__misc__extra__extra_lutcas_h
#define ABC__misc__extra__extra_lutcas_h

#ifdef _WIN32
#define inline __inline // compatible with MS VS 6.0
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "aig/miniaig/miniaig.h"
#include "bdd/cudd/cuddInt.h"
#include "bdd/dsd/dsd.h"

ABC_NAMESPACE_HEADER_START

/*
    The decomposed structure of the LUT cascade is represented as an array of 64-bit integers (words).
    The first word in the record is the number of LUT info blocks in the record, which follow one by one.
    Each LUT info block contains the following:
    - the number of words in this block
    - the number of fanins
    - the list of fanins
    - the variable ID of the output (can be one of the fanin variables)
    - truth tables (one word for 6 vars or less; more words as needed for more than 6 vars)
    For a 6-input node, the LUT info block takes 10 words (block size, fanin count, 6 fanins, output ID, truth table).
    For a 4-input node, the LUT info block takes  8 words (block size, fanin count, 4 fanins, output ID, truth table).
    If the LUT cascade contains a 6-LUT followed by a 4-LUT, the record contains 1+10+8=19 words.
*/

#define Mini_AigForEachNonPo( p, i )  for (i = 1; i < Mini_AigNodeNum(p); i++) if ( Mini_AigNodeIsPo(p, i) ) {} else 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_LutCasCollapseDeref( DdManager * dd, Vec_Ptr_t * vFuncs )
{
    DdNode * bFunc; int i;
    Vec_PtrForEachEntry( DdNode *, vFuncs, bFunc, i )
        if ( bFunc )
            Cudd_RecursiveDeref( dd, bFunc );
    Vec_PtrFree( vFuncs );
}
Vec_Ptr_t * Abc_LutCasCollapse( Mini_Aig_t * p, DdManager * dd, int nBddLimit, int fVerbose )
{
    DdNode * bFunc0, * bFunc1, * bFunc;  int Id, nOuts = 0;
    Vec_Ptr_t * vFuncs = Vec_PtrStart( Mini_AigNodeNum(p) );
    Vec_PtrWriteEntry( vFuncs, 0, Cudd_ReadLogicZero(dd) ), Cudd_Ref(Cudd_ReadLogicZero(dd));
    Mini_AigForEachPi( p, Id )
      Vec_PtrWriteEntry( vFuncs, Id, Cudd_bddIthVar(dd,Id-1) ), Cudd_Ref(Cudd_bddIthVar(dd,Id-1));
    Mini_AigForEachAnd( p, Id ) {
        bFunc0 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vFuncs, Mini_AigLit2Var(Mini_AigNodeFanin0(p, Id))), Mini_AigLitIsCompl(Mini_AigNodeFanin0(p, Id)) );
        bFunc1 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vFuncs, Mini_AigLit2Var(Mini_AigNodeFanin1(p, Id))), Mini_AigLitIsCompl(Mini_AigNodeFanin1(p, Id)) );
        bFunc  = Cudd_bddAndLimit( dd, bFunc0, bFunc1, nBddLimit );  
        if ( bFunc == NULL )
        {
            Abc_LutCasCollapseDeref( dd, vFuncs );
            return NULL;
        }        
        Cudd_Ref( bFunc );
        Vec_PtrWriteEntry( vFuncs, Id, bFunc );
    }
    Mini_AigForEachPo( p, Id ) {
        bFunc0 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vFuncs, Mini_AigLit2Var(Mini_AigNodeFanin0(p, Id))), Mini_AigLitIsCompl(Mini_AigNodeFanin0(p, Id)) );
        Vec_PtrWriteEntry( vFuncs, Id, bFunc0 ); Cudd_Ref( bFunc0 );
    }
    Mini_AigForEachNonPo( p, Id ) {
      bFunc = (DdNode *)Vec_PtrEntry(vFuncs, Id);
      Cudd_RecursiveDeref( dd, bFunc );
      Vec_PtrWriteEntry( vFuncs, Id, NULL );
    }
    Mini_AigForEachPo( p, Id ) 
        Vec_PtrWriteEntry( vFuncs, nOuts++, Vec_PtrEntry(vFuncs, Id) );
    Vec_PtrShrink( vFuncs, nOuts );
    return vFuncs;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_LutCasFakeNames( int nNames )
{
    Vec_Ptr_t * vNames;
    char Buffer[5];
    int i;

    vNames = Vec_PtrAlloc( nNames );
    for ( i = 0; i < nNames; i++ )
    {
        if ( nNames < 26 )
        {
            Buffer[0] = 'a' + i;
            Buffer[1] = 0;
        }
        else
        {
            Buffer[0] = 'a' + i%26;
            Buffer[1] = '0' + i/26;
            Buffer[2] = 0;
        }
        Vec_PtrPush( vNames, Extra_UtilStrsav(Buffer) );
    }
    return vNames;
}
void Abc_LutCasPrintDsd( DdManager * dd, DdNode * bFunc, int fVerbose )
{
    Dsd_Manager_t * pManDsd = Dsd_ManagerStart( dd, dd->size, 0 );
    Dsd_Decompose( pManDsd, &bFunc, 1 );
    if ( fVerbose )
    {
        Vec_Ptr_t * vNamesCi = Abc_LutCasFakeNames( dd->size );
        Vec_Ptr_t * vNamesCo = Abc_LutCasFakeNames( 1 );
        char ** ppNamesCi = (char **)Vec_PtrArray( vNamesCi );
        char ** ppNamesCo = (char **)Vec_PtrArray( vNamesCo );
        Dsd_TreePrint( stdout, pManDsd, ppNamesCi, ppNamesCo, 0, -1, 0 );
        Vec_PtrFreeFree( vNamesCi );
        Vec_PtrFreeFree( vNamesCo );
    }
    Dsd_ManagerStop( pManDsd );
}    
DdNode * Abc_LutCasBuildBdds( Mini_Aig_t * p, DdManager ** pdd )
{
    DdManager * dd = Cudd_Init( Mini_AigPiNum(p), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    Cudd_AutodynEnable( dd,  CUDD_REORDER_SYMM_SIFT );
    Vec_Ptr_t * vFuncs = Abc_LutCasCollapse( p, dd, 10000, 0 );
    Cudd_AutodynDisable( dd );
    if ( vFuncs == NULL ) {
        Extra_StopManager( dd );
        return NULL;
    }
    DdNode * bNode = (DdNode *)Vec_PtrEntry(vFuncs, 0);
    Vec_PtrFree(vFuncs);
    *pdd = dd;
    return bNode;
}
static inline word * Abc_LutCascade( Mini_Aig_t * p, int nLutSize, int fVerbose )
{
    DdManager * dd = NULL;
    DdNode * bFunc = Abc_LutCasBuildBdds( p, &dd );
    if ( bFunc == NULL ) return NULL;
    Abc_LutCasPrintDsd( dd, bFunc, 1 );
    Cudd_RecursiveDeref( dd, bFunc );
    Extra_StopManager( dd );

    word * pLuts = NULL;
    return pLuts;
}

ABC_NAMESPACE_HEADER_END

#endif /* ABC__misc__extra__extra_lutcas_h */
