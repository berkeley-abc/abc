/**CFile****************************************************************

  FileName    [extraBddMisc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [DD-based utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: extraBddMisc.c,v 1.0 2003/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "extra.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/


/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

// file "extraDdTransfer.c"
static DdNode * extraTransferPermuteRecur( DdManager * ddS, DdManager * ddD, DdNode * f, st_table * table, int * Permute );
static DdNode * extraTransferPermute( DdManager * ddS, DdManager * ddD, DdNode * f, int * Permute );

// file "cuddUtils.c"
static void ddSupportStep ARGS((DdNode *f, int *support));
static void ddClearFlag ARGS((DdNode *f));

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Convert a {A,B}DD from a manager to another with variable remapping.]

  Description [Convert a {A,B}DD from a manager to another one. The orders of the
  variables in the two managers may be different. Returns a
  pointer to the {A,B}DD in the destination manager if successful; NULL
  otherwise. The i-th entry in the array Permute tells what is the index
  of the i-th variable from the old manager in the new manager.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode * Extra_TransferPermute( DdManager * ddSource, DdManager * ddDestination, DdNode * f, int * Permute )
{
    DdNode * bRes;
    do
    {
        ddDestination->reordered = 0;
        bRes = extraTransferPermute( ddSource, ddDestination, f, Permute );
    }
    while ( ddDestination->reordered == 1 );
    return ( bRes );

}                               /* end of Extra_TransferPermute */

/**Function********************************************************************

  Synopsis    [Transfers the BDD from one manager into another level by level.]

  Description [Transfers the BDD from one manager into another while
  preserving the correspondence between variables level by level.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode * Extra_TransferLevelByLevel( DdManager * ddSource, DdManager * ddDestination, DdNode * f )
{
    DdNode * bRes;
    int * pPermute;
    int nMin, nMax, i;

    nMin = ddMin(ddSource->size, ddDestination->size);
    nMax = ddMax(ddSource->size, ddDestination->size);
    pPermute = ALLOC( int, nMax );
    // set up the variable permutation
    for ( i = 0; i < nMin; i++ )
        pPermute[ ddSource->invperm[i] ] = ddDestination->invperm[i];
    if ( ddSource->size > ddDestination->size )
    {
        for (      ; i < nMax; i++ )
            pPermute[ ddSource->invperm[i] ] = -1;
    }
    bRes = Extra_TransferPermute( ddSource, ddDestination, f, pPermute );
    FREE( pPermute );
    return bRes;
}

/**Function********************************************************************

  Synopsis    [Remaps the function to depend on the topmost variables on the manager.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
DdNode * Extra_bddRemapUp(
  DdManager * dd,
  DdNode * bF )
{
    int * pPermute;
    DdNode * bSupp, * bTemp, * bRes;
    int Counter;

    pPermute = ALLOC( int, dd->size );

    // get support
    bSupp = Cudd_Support( dd, bF );    Cudd_Ref( bSupp );

    // create the variable map
    // to remap the DD into the upper part of the manager
    Counter = 0;
    for ( bTemp = bSupp; bTemp != dd->one; bTemp = cuddT(bTemp) )
        pPermute[bTemp->index] = dd->invperm[Counter++];

    // transfer the BDD and remap it
    bRes = Cudd_bddPermute( dd, bF, pPermute );  Cudd_Ref( bRes );

    // remove support
    Cudd_RecursiveDeref( dd, bSupp );

    // return
    Cudd_Deref( bRes );
    free( pPermute );
    return bRes;
}

/**Function********************************************************************

  Synopsis    [Moves the BDD by the given number of variables up or down.]

  Description []

  SideEffects []

  SeeAlso     [Extra_bddShift]

******************************************************************************/
DdNode * Extra_bddMove( 
  DdManager * dd,   /* the DD manager */
  DdNode * bF,
  int nVars) 
{
    DdNode * res;
    DdNode * bVars;
    if ( nVars == 0 )
        return bF;
    if ( Cudd_IsConstant(bF) )
        return bF;
    assert( nVars <= dd->size );
    if ( nVars > 0 )
        bVars = dd->vars[nVars];
    else
        bVars = Cudd_Not(dd->vars[-nVars]);

    do {
        dd->reordered = 0;
        res = extraBddMove( dd, bF, bVars );
    } while (dd->reordered == 1);
    return(res);

} /* end of Extra_bddMove */

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Extra_StopManager( DdManager * dd )
{
    int RetValue;
    // check for remaining references in the package
    RetValue = Cudd_CheckZeroRef( dd );
    if ( RetValue > 0 )
        printf( "\nThe number of referenced nodes = %d\n\n", RetValue );
//  Cudd_PrintInfo( dd, stdout );
    Cudd_Quit( dd );
}

/**Function********************************************************************

  Synopsis    [Outputs the BDD in a readable format.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
void Extra_bddPrint( DdManager * dd, DdNode * F )
{
    DdGen * Gen;
    int * Cube;
    CUDD_VALUE_TYPE Value;
    int nVars = dd->size;
    int fFirstCube = 1;
    int i;

    if ( F == NULL )
    {
        printf("NULL");
        return;
    }
    if ( F == b0 )
    {
        printf("Constant 0");
        return;
    }
    if ( F == b1 )
    {
        printf("Constant 1");
        return;
    }

    Cudd_ForeachCube( dd, F, Gen, Cube, Value )
    {
        if ( fFirstCube )
            fFirstCube = 0;
        else
//          Output << " + ";
            printf( " + " );

        for ( i = 0; i < nVars; i++ )
            if ( Cube[i] == 0 )
                printf( "[%d]'", i );
//              printf( "%c'", (char)('a'+i) );
            else if ( Cube[i] == 1 )
                printf( "[%d]", i );
//              printf( "%c", (char)('a'+i) );
    }

//  printf("\n");
}
/**Function********************************************************************

  Synopsis    [Returns the size of the support.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_bddSuppSize( DdManager * dd, DdNode * bSupp )
{
    int Counter = 0;
    while ( bSupp != b1 )
    {
        assert( !Cudd_IsComplement(bSupp) );
        assert( cuddE(bSupp) == b0 );

        bSupp = cuddT(bSupp);
        Counter++;
    }
    return Counter;
}

/**Function********************************************************************

  Synopsis    [Returns 1 if the support contains the given BDD variable.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_bddSuppContainVar( DdManager * dd, DdNode * bS, DdNode * bVar )   
{ 
    for( ; bS != b1; bS = cuddT(bS) )
        if ( bS->index == bVar->index )
            return 1;
    return 0;
}

/**Function********************************************************************

  Synopsis    [Returns 1 if two supports represented as BDD cubes are overlapping.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_bddSuppOverlapping( DdManager * dd, DdNode * S1, DdNode * S2 )
{
    while ( S1->index != CUDD_CONST_INDEX && S2->index != CUDD_CONST_INDEX )
    {
        // if the top vars are the same, they intersect
        if ( S1->index == S2->index )
            return 1;
        // if the top vars are different, skip the one, which is higher
        if ( dd->perm[S1->index] < dd->perm[S2->index] )
            S1 = cuddT(S1);
        else
            S2 = cuddT(S2);
    }
    return 0;
}

/**Function********************************************************************

  Synopsis    [Returns the number of different vars in two supports.]

  Description [Counts the number of variables that appear in one support and 
  does not appear in other support. If the number exceeds DiffMax, returns DiffMax.]

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_bddSuppDifferentVars( DdManager * dd, DdNode * S1, DdNode * S2, int DiffMax )
{
    int Result = 0;
    while ( S1->index != CUDD_CONST_INDEX && S2->index != CUDD_CONST_INDEX )
    {
        // if the top vars are the same, this var is the same
        if ( S1->index == S2->index )
        {
            S1 = cuddT(S1);
            S2 = cuddT(S2);
            continue;
        }
        // the top var is different
        Result++;

        if ( Result >= DiffMax )
            return DiffMax;

        // if the top vars are different, skip the one, which is higher
        if ( dd->perm[S1->index] < dd->perm[S2->index] )
            S1 = cuddT(S1);
        else
            S2 = cuddT(S2);
    }

    // consider the remaining variables
    if ( S1->index != CUDD_CONST_INDEX )
        Result += Extra_bddSuppSize(dd,S1);
    else if ( S2->index != CUDD_CONST_INDEX )
        Result += Extra_bddSuppSize(dd,S2);

    if ( Result >= DiffMax )
        return DiffMax;
    return Result;
}


/**Function********************************************************************

  Synopsis    [Checks the support containment.]

  Description [This function returns 1 if one support is contained in another.
  In this case, bLarge (bSmall) is assigned to point to the larger (smaller) support.
  If the supports are identical, return 0 and does not assign the supports!]

  SideEffects []

  SeeAlso     []

******************************************************************************/
int Extra_bddSuppCheckContainment( DdManager * dd, DdNode * bL, DdNode * bH, DdNode ** bLarge, DdNode ** bSmall )
{
    DdNode * bSL = bL;
    DdNode * bSH = bH;
    int fLcontainsH = 1;
    int fHcontainsL = 1;
    int TopVar;
    
    if ( bSL == bSH )
        return 0;

    while ( bSL != b1 || bSH != b1 )
    {
        if ( bSL == b1 )
        { // Low component has no vars; High components has some vars
            fLcontainsH = 0;
            if ( fHcontainsL == 0 )
                return 0;
            else
                break;
        }

        if ( bSH == b1 )
        { // similarly
            fHcontainsL = 0;
            if ( fLcontainsH == 0 )
                return 0;
            else
                break;
        }

        // determine the topmost var of the supports by comparing their levels
        if ( dd->perm[bSL->index] < dd->perm[bSH->index] )
            TopVar = bSL->index;
        else
            TopVar = bSH->index;

        if ( TopVar == bSL->index && TopVar == bSH->index ) 
        { // they are on the same level
            // it does not tell us anything about their containment
            // skip this var
            bSL = cuddT(bSL);
            bSH = cuddT(bSH);
        }
        else if ( TopVar == bSL->index ) // and TopVar != bSH->index
        { // Low components is higher and contains more vars
            // it is not possible that High component contains Low
            fHcontainsL = 0;
            // skip this var
            bSL = cuddT(bSL);
        }
        else // if ( TopVar == bSH->index ) // and TopVar != bSL->index
        { // similarly
            fLcontainsH = 0;
            // skip this var
            bSH = cuddT(bSH);
        }

        // check the stopping condition
        if ( !fHcontainsL && !fLcontainsH )
            return 0;
    }
    // only one of them can be true at the same time
    assert( !fHcontainsL || !fLcontainsH );
    if ( fHcontainsL )
    {
        *bLarge = bH;
        *bSmall = bL;
    }
    else // fLcontainsH
    {
        *bLarge = bL;
        *bSmall = bH;
    }
    return 1;
}


/**Function********************************************************************

  Synopsis    [Finds variables on which the DD depends and returns them as am array.]

  Description [Finds the variables on which the DD depends. Returns an array 
  with entries set to 1 for those variables that belong to the support; 
  NULL otherwise. The array is allocated by the user and should have at least
  as many entries as the maximum number of variables in BDD and ZDD parts of 
  the manager.]

  SideEffects [None]

  SeeAlso     [Cudd_Support Cudd_VectorSupport Cudd_ClassifySupport]

******************************************************************************/
int * 
Extra_SupportArray(
  DdManager * dd, /* manager */
  DdNode * f,     /* DD whose support is sought */
  int * support ) /* array allocated by the user */
{
    int i, size;

    /* Initialize support array for ddSupportStep. */
    size = ddMax(dd->size, dd->sizeZ);
    for (i = 0; i < size; i++) 
        support[i] = 0;
    
    /* Compute support and clean up markers. */
    ddSupportStep(Cudd_Regular(f),support);
    ddClearFlag(Cudd_Regular(f));

    return(support);

} /* end of Extra_SupportArray */

/**Function********************************************************************

  Synopsis    [Finds the variables on which a set of DDs depends.]

  Description [Finds the variables on which a set of DDs depends.
  The set must contain either BDDs and ADDs, or ZDDs.
  Returns a BDD consisting of the product of the variables if
  successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Cudd_Support Cudd_ClassifySupport]

******************************************************************************/
int *
Extra_VectorSupportArray( 
  DdManager * dd, /* manager */ 
  DdNode ** F, /* array of DDs whose support is sought */ 
  int n, /* size of the array */  
  int * support ) /* array allocated by the user */
{
    int i, size;

    /* Allocate and initialize support array for ddSupportStep. */
    size = ddMax( dd->size, dd->sizeZ );
    for ( i = 0; i < size; i++ )
        support[i] = 0;

    /* Compute support and clean up markers. */
    for ( i = 0; i < n; i++ )
        ddSupportStep( Cudd_Regular(F[i]), support );
    for ( i = 0; i < n; i++ )
        ddClearFlag( Cudd_Regular(F[i]) );

    return support;
}

/**Function********************************************************************

  Synopsis    [Find any cube belonging to the on-set of the function.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
DdNode *  Extra_bddFindOneCube( DdManager * dd, DdNode * bF )
{
    char * s_Temp;
    DdNode * bCube, * bTemp;
    int v;

    // get the vector of variables in the cube
    s_Temp = ALLOC( char, dd->size );
    Cudd_bddPickOneCube( dd, bF, s_Temp );

    // start the cube
    bCube = b1; Cudd_Ref( bCube );
    for ( v = 0; v < dd->size; v++ )
        if ( s_Temp[v] == 0 )
        {
//          Cube &= !s_XVars[v];
            bCube = Cudd_bddAnd( dd, bTemp = bCube, Cudd_Not(dd->vars[v]) ); Cudd_Ref( bCube );
            Cudd_RecursiveDeref( dd, bTemp );
        }
        else if ( s_Temp[v] == 1 )
        {
//          Cube &=  s_XVars[v];
            bCube = Cudd_bddAnd( dd, bTemp = bCube,          dd->vars[v]  ); Cudd_Ref( bCube );
            Cudd_RecursiveDeref( dd, bTemp );
        }
    Cudd_Deref(bCube);
    free( s_Temp );
    return bCube;
}

/**Function********************************************************************

  Synopsis    [Returns one cube contained in the given BDD.]

  Description [This function returns the cube with the smallest 
  bits-to-integer value.]

  SideEffects []

******************************************************************************/
DdNode * Extra_bddGetOneCube( DdManager * dd, DdNode * bFunc )
{
    DdNode * bFuncR, * bFunc0, * bFunc1;
    DdNode * bRes0,  * bRes1,  * bRes;

    bFuncR = Cudd_Regular(bFunc);
    if ( cuddIsConstant(bFuncR) )
        return bFunc;

    // cofactor
    if ( Cudd_IsComplement(bFunc) )
    {
        bFunc0 = Cudd_Not( cuddE(bFuncR) );
        bFunc1 = Cudd_Not( cuddT(bFuncR) );
    }
    else
    {
        bFunc0 = cuddE(bFuncR);
        bFunc1 = cuddT(bFuncR);
    }

    // try to find the cube with the negative literal
    bRes0 = Extra_bddGetOneCube( dd, bFunc0 );  Cudd_Ref( bRes0 );

    if ( bRes0 != b0 )
    {
        bRes = Cudd_bddAnd( dd, bRes0, Cudd_Not(dd->vars[bFuncR->index]) ); Cudd_Ref( bRes );
        Cudd_RecursiveDeref( dd, bRes0 );
    }
    else
    {
        Cudd_RecursiveDeref( dd, bRes0 );
        // try to find the cube with the positive literal
        bRes1 = Extra_bddGetOneCube( dd, bFunc1 );  Cudd_Ref( bRes1 );
        assert( bRes1 != b0 );
        bRes = Cudd_bddAnd( dd, bRes1, dd->vars[bFuncR->index] ); Cudd_Ref( bRes );
        Cudd_RecursiveDeref( dd, bRes1 );
    }

    Cudd_Deref( bRes );
    return bRes;
}

/**Function********************************************************************

  Synopsis    [Performs the reordering-sensitive step of Extra_bddMove().]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
DdNode * Extra_bddComputeRangeCube( DdManager * dd, int iStart, int iStop )
{
    DdNode * bTemp, * bProd;
    int i;
    assert( iStart <= iStop );
    assert( iStart >= 0 && iStart <= dd->size );
    assert( iStop >= 0  && iStop  <= dd->size );
    bProd = b1;         Cudd_Ref( bProd );
    for ( i = iStart; i < iStop; i++ )
    {
        bProd = Cudd_bddAnd( dd, bTemp = bProd, dd->vars[i] );      Cudd_Ref( bProd );
        Cudd_RecursiveDeref( dd, bTemp ); 
    }
    Cudd_Deref( bProd );
    return bProd;
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Performs the reordering-sensitive step of Extra_bddMove().]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
DdNode * extraBddMove( 
  DdManager * dd,    /* the DD manager */
  DdNode * bF,
  DdNode * bDist) 
{
    DdNode * bRes;

    if ( Cudd_IsConstant(bF) )
        return bF;

    if ( bRes = cuddCacheLookup2(dd, extraBddMove, bF, bDist) )
        return bRes;
    else
    {
        DdNode * bRes0, * bRes1;             
        DdNode * bF0, * bF1;             
        DdNode * bFR = Cudd_Regular(bF); 
        int VarNew;
        
        if ( Cudd_IsComplement(bDist) )
            VarNew = bFR->index - Cudd_Not(bDist)->index;
        else
            VarNew = bFR->index + bDist->index;
        assert( VarNew < dd->size );

        // cofactor the functions
        if ( bFR != bF ) // bFunc is complemented 
        {
            bF0 = Cudd_Not( cuddE(bFR) );
            bF1 = Cudd_Not( cuddT(bFR) );
        }
        else
        {
            bF0 = cuddE(bFR);
            bF1 = cuddT(bFR);
        }

        bRes0 = extraBddMove( dd, bF0, bDist );
        if ( bRes0 == NULL ) 
            return NULL;
        cuddRef( bRes0 );

        bRes1 = extraBddMove( dd, bF1, bDist );
        if ( bRes1 == NULL ) 
        {
            Cudd_RecursiveDeref( dd, bRes0 );
            return NULL;
        }
        cuddRef( bRes1 );

        /* only bRes0 and bRes1 are referenced at this point */
        bRes = cuddBddIteRecur( dd, dd->vars[VarNew], bRes1, bRes0 );
        if ( bRes == NULL ) 
        {
            Cudd_RecursiveDeref( dd, bRes0 );
            Cudd_RecursiveDeref( dd, bRes1 );
            return NULL;
        }
        cuddRef( bRes );
        Cudd_RecursiveDeref( dd, bRes0 );
        Cudd_RecursiveDeref( dd, bRes1 );

        /* insert the result into cache */
        cuddCacheInsert2( dd, extraBddMove, bF, bDist, bRes );
        cuddDeref( bRes );
        return bRes;
    }
} /* end of extraBddMove */


/**Function********************************************************************

  Synopsis    [Finds three cofactors of the cover w.r.t. to the topmost variable.]

  Description [Finds three cofactors of the cover w.r.t. to the topmost variable.
  Does not check the cover for being a constant. Assumes that ZDD variables encoding 
  positive and negative polarities are adjacent in the variable order. Is different 
  from cuddZddGetCofactors3() in that it does not compute the cofactors w.r.t. the 
  given variable but takes the cofactors with respent to the topmost variable. 
  This function is more efficient when used in recursive procedures because it does 
  not require referencing of the resulting cofactors (compare cuddZddProduct() 
  and extraZddPrimeProduct()).]

  SideEffects [None]

  SeeAlso     [cuddZddGetCofactors3]

******************************************************************************/
void 
extraDecomposeCover( 
  DdManager* dd,    /* the manager */
  DdNode*  zC,      /* the cover */
  DdNode** zC0,     /* the pointer to the negative var cofactor */ 
  DdNode** zC1,     /* the pointer to the positive var cofactor */ 
  DdNode** zC2 )    /* the pointer to the cofactor without var */ 
{
    if ( (zC->index & 1) == 0 ) 
    { /* the top variable is present in positive polarity and maybe in negative */

        DdNode *Temp = cuddE( zC );
        *zC1  = cuddT( zC );
        if ( cuddIZ(dd,Temp->index) == cuddIZ(dd,zC->index) + 1 )
        {   /* Temp is not a terminal node 
             * top var is present in negative polarity */
            *zC2 = cuddE( Temp );
            *zC0 = cuddT( Temp );
        }
        else
        {   /* top var is not present in negative polarity */
            *zC2 = Temp;
            *zC0 = dd->zero;
        }
    }
    else 
    { /* the top variable is present only in negative */
        *zC1 = dd->zero;
        *zC2 = cuddE( zC );
        *zC0 = cuddT( zC );
    }
} /* extraDecomposeCover */

/*---------------------------------------------------------------------------*/
/* Definition of static Functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Convert a BDD from a manager to another one.]

  Description [Convert a BDD from a manager to another one. Returns a
  pointer to the BDD in the destination manager if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [Extra_TransferPermute]

******************************************************************************/
DdNode * extraTransferPermute( DdManager * ddS, DdManager * ddD, DdNode * f, int * Permute )
{
    DdNode *res;
    st_table *table = NULL;
    st_generator *gen = NULL;
    DdNode *key, *value;

    table = st_init_table( st_ptrcmp, st_ptrhash );
    if ( table == NULL )
        goto failure;
    res = extraTransferPermuteRecur( ddS, ddD, f, table, Permute );
    if ( res != NULL )
        cuddRef( res );

    /* Dereference all elements in the table and dispose of the table.
       ** This must be done also if res is NULL to avoid leaks in case of
       ** reordering. */
    gen = st_init_gen( table );
    if ( gen == NULL )
        goto failure;
    while ( st_gen( gen, ( char ** ) &key, ( char ** ) &value ) )
    {
        Cudd_RecursiveDeref( ddD, value );
    }
    st_free_gen( gen );
    gen = NULL;
    st_free_table( table );
    table = NULL;

    if ( res != NULL )
        cuddDeref( res );
    return ( res );

  failure:
    if ( table != NULL )
        st_free_table( table );
    if ( gen != NULL )
        st_free_gen( gen );
    return ( NULL );

}                               /* end of extraTransferPermute */


/**Function********************************************************************

  Synopsis    [Performs the recursive step of Extra_TransferPermute.]

  Description [Performs the recursive step of Extra_TransferPermute.
  Returns a pointer to the result if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [extraTransferPermute]

******************************************************************************/
static DdNode * 
extraTransferPermuteRecur( 
  DdManager * ddS, 
  DdManager * ddD, 
  DdNode * f, 
  st_table * table, 
  int * Permute )
{
    DdNode *ft, *fe, *t, *e, *var, *res;
    DdNode *one, *zero;
    int index;
    int comple = 0;

    statLine( ddD );
    one = DD_ONE( ddD );
    comple = Cudd_IsComplement( f );

    /* Trivial cases. */
    if ( Cudd_IsConstant( f ) )
        return ( Cudd_NotCond( one, comple ) );


    /* Make canonical to increase the utilization of the cache. */
    f = Cudd_NotCond( f, comple );
    /* Now f is a regular pointer to a non-constant node. */

    /* Check the cache. */
    if ( st_lookup( table, ( char * ) f, ( char ** ) &res ) )
        return ( Cudd_NotCond( res, comple ) );

    /* Recursive step. */
    if ( Permute )
        index = Permute[f->index];
    else
        index = f->index;

    ft = cuddT( f );
    fe = cuddE( f );

    t = extraTransferPermuteRecur( ddS, ddD, ft, table, Permute );
    if ( t == NULL )
    {
        return ( NULL );
    }
    cuddRef( t );

    e = extraTransferPermuteRecur( ddS, ddD, fe, table, Permute );
    if ( e == NULL )
    {
        Cudd_RecursiveDeref( ddD, t );
        return ( NULL );
    }
    cuddRef( e );

    zero = Cudd_Not(ddD->one);
    var = cuddUniqueInter( ddD, index, one, zero );
    if ( var == NULL )
    {
        Cudd_RecursiveDeref( ddD, t );
        Cudd_RecursiveDeref( ddD, e );
        return ( NULL );
    }
    res = cuddBddIteRecur( ddD, var, t, e );

    if ( res == NULL )
    {
        Cudd_RecursiveDeref( ddD, t );
        Cudd_RecursiveDeref( ddD, e );
        return ( NULL );
    }
    cuddRef( res );
    Cudd_RecursiveDeref( ddD, t );
    Cudd_RecursiveDeref( ddD, e );

    if ( st_add_direct( table, ( char * ) f, ( char * ) res ) ==
         ST_OUT_OF_MEM )
    {
        Cudd_RecursiveDeref( ddD, res );
        return ( NULL );
    }
    return ( Cudd_NotCond( res, comple ) );

}                               /* end of extraTransferPermuteRecur */

/**Function********************************************************************

  Synopsis    [Performs the recursive step of Cudd_Support.]

  Description [Performs the recursive step of Cudd_Support. Performs a
  DFS from f. The support is accumulated in supp as a side effect. Uses
  the LSB of the then pointer as visited flag.]

  SideEffects [None]

  SeeAlso     [ddClearFlag]

******************************************************************************/
static void
ddSupportStep(
  DdNode * f,
  int * support)
{
    if (cuddIsConstant(f) || Cudd_IsComplement(f->next)) {
    return;
    }

    support[f->index] = 1;
    ddSupportStep(cuddT(f),support);
    ddSupportStep(Cudd_Regular(cuddE(f)),support);
    /* Mark as visited. */
    f->next = Cudd_Not(f->next);
    return;

} /* end of ddSupportStep */


/**Function********************************************************************

  Synopsis    [Performs a DFS from f, clearing the LSB of the next
  pointers.]

  Description []

  SideEffects [None]

  SeeAlso     [ddSupportStep ddDagInt]

******************************************************************************/
static void
ddClearFlag(
  DdNode * f)
{
    if (!Cudd_IsComplement(f->next)) {
    return;
    }
    /* Clear visited flag. */
    f->next = Cudd_Regular(f->next);
    if (cuddIsConstant(f)) {
    return;
    }
    ddClearFlag(cuddT(f));
    ddClearFlag(Cudd_Regular(cuddE(f)));
    return;

} /* end of ddClearFlag */


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


