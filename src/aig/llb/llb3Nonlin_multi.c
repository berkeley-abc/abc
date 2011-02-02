/**CFile****************************************************************

  FileName    [llb2Nonlin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [BDD based reachability.]

  Synopsis    [Non-linear quantification scheduling.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: llb2Nonlin.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "llbInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Llb_Var_t_ Llb_Var_t;
struct Llb_Var_t_ 
{
    int           iVar;      // variable number
    int           nScore;    // variable score
    Vec_Int_t *   vParts;    // partitions
};

typedef struct Llb_Prt_t_ Llb_Prt_t;
struct Llb_Prt_t_ 
{
    int           iPart;     // partition number
    int           nSize;     // the number of BDD nodes
    DdNode *      bFunc;     // the partition
    Vec_Int_t *   vVars;     // support
};

typedef struct Llb_Mgr_t_ Llb_Mgr_t;
struct Llb_Mgr_t_
{
    Aig_Man_t *   pAig;      // AIG manager
    Vec_Ptr_t *   vLeaves;   // leaves in the AIG manager
    Vec_Ptr_t *   vRoots;    // roots in the AIG manager
    DdManager *   dd;        // working BDD manager
    Vec_Ptr_t *   vFuncs;    // current state functions in terms of vLeaves
    int *         pVars2Q;   // variables to quantify
    // internal
    Llb_Prt_t **  pParts;    // partitions
    Llb_Var_t **  pVars;     // variables
    int           iPartFree; // next free partition
    int           nVars;     // the number of BDD variables
    int           nSuppMax;  // maximum support size
    // temporary
    int *         pSupp;     // temporary support storage
};

static inline Llb_Var_t * Llb_MgrVar( Llb_Mgr_t * p, int i )   { return p->pVars[i];  }
static inline Llb_Prt_t * Llb_MgrPart( Llb_Mgr_t * p, int i )  { return p->pParts[i]; }

// iterator over vars
#define Llb_MgrForEachVar( p, pVar, i )     \
    for ( i = 0; (i < p->nVars) && (((pVar) = Llb_MgrVar(p, i)), 1); i++ ) if ( pVar == NULL ) {} else
// iterator over parts
#define Llb_MgrForEachPart( p, pPart, i )   \
    for ( i = 0; (i < p->iPartFree) && (((pPart) = Llb_MgrPart(p, i)), 1); i++ ) if ( pPart == NULL ) {} else

// iterator over vars of one partition
#define Llb_PartForEachVar( p, pPart, pVar, i )   \
    for ( i = 0; (i < Vec_IntSize(pPart->vVars)) && (((pVar) = Llb_MgrVar(p, Vec_IntEntry(pPart->vVars,i))), 1); i++ )
// iterator over parts of one variable
#define Llb_VarForEachPart( p, pVar, pPart, i )   \
    for ( i = 0; (i < Vec_IntSize(pVar->vParts)) && (((pPart) = Llb_MgrPart(p, Vec_IntEntry(pVar->vParts,i))), 1); i++ )

static int timeBuild, timeAndEx, timeOther;
static int nSuppMax;


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Finds variable whose 0-cofactor is the smallest.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_NonlinFindBestVar( DdManager * dd, DdNode * bFunc, Vec_Int_t * vVars )
{
    DdNode * bCof, * bVar;
    int i, iVar, iVarBest = -1;
    int Size, Size0, Size1;
    if ( vVars == NULL )
        vVars = Vec_IntStartNatural( Cudd_ReadSize(dd) );
    printf( "\nOriginal = %6d.  SuppSize = %3d. Vars = %3d.\n", 
        Size = Cudd_DagSize(bFunc), Cudd_SupportSize(dd, bFunc), Vec_IntSize(vVars) );
    Vec_IntForEachEntry( vVars, iVar, i )
    {
        printf( "Var =%3d : ", iVar );
        bVar = Cudd_bddIthVar(dd, iVar);

        bCof = Cudd_Cofactor( dd, bFunc, Cudd_Not(bVar) );      Cudd_Ref( bCof );
        printf( "Supp0 =%3d  ",    Cudd_SupportSize(dd, bCof) );
        printf( "Size0 =%6d   ", Size0 = Cudd_DagSize(bCof) );
        Cudd_RecursiveDeref( dd, bCof );

        bCof = Cudd_Cofactor( dd, bFunc, bVar );                Cudd_Ref( bCof );
        printf( "Supp1 =%3d  ",    Cudd_SupportSize(dd, bCof) );
        printf( "Size1 =%6d   ", Size1 = Cudd_DagSize(bCof) );
        Cudd_RecursiveDeref( dd, bCof );

        printf( "D =%6d  ", Size0 + Size1 - Size );
        printf( "B =%6d\n", ABC_MAX(Size0, Size1) - ABC_MIN(Size0, Size1) );
    }
    return iVarBest;
}


/**Function*************************************************************

  Synopsis    [Finds variable whose 0-cofactor is the smallest.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinTrySubsetting( DdManager * dd, DdNode * bFunc )
{
    DdNode * bNew;
    printf( "Original = %6d.  SuppSize = %3d.    ", 
        Cudd_DagSize(bFunc), Cudd_SupportSize(dd, bFunc) );
    bNew = Cudd_SubsetHeavyBranch( dd, bFunc, Cudd_SupportSize(dd, bFunc), 1000 );  Cudd_Ref( bNew );
    printf( "Result   = %6d.  SuppSize = %3d.\n", 
        Cudd_DagSize(bNew), Cudd_SupportSize(dd, bNew) );
    Cudd_RecursiveDeref( dd, bNew );
}


/**Function*************************************************************

  Synopsis    [Removes one variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinRemoveVar( Llb_Mgr_t * p, Llb_Var_t * pVar )
{
    assert( p->pVars[pVar->iVar] == pVar );
    p->pVars[pVar->iVar] = NULL;
    Vec_IntFree( pVar->vParts );
    ABC_FREE( pVar );
}

/**Function*************************************************************

  Synopsis    [Removes one partition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinRemovePart( Llb_Mgr_t * p, Llb_Prt_t * pPart )
{
    assert( p->pParts[pPart->iPart] == pPart );
    p->pParts[pPart->iPart] = NULL;
    Vec_IntFree( pPart->vVars );
    Cudd_RecursiveDeref( p->dd, pPart->bFunc );
    ABC_FREE( pPart );
}

/**Function*************************************************************

  Synopsis    [Create cube with singleton variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Llb_NonlinCreateCube1( Llb_Mgr_t * p, Llb_Prt_t * pPart )
{
    DdNode * bCube, * bTemp;
    Llb_Var_t * pVar;
    int i;
    bCube = Cudd_ReadOne(p->dd);   Cudd_Ref( bCube );
    Llb_PartForEachVar( p, pPart, pVar, i )
    {
        assert( Vec_IntSize(pVar->vParts) > 0 );
        if ( Vec_IntSize(pVar->vParts) != 1 )
            continue;
        assert( Vec_IntEntry(pVar->vParts, 0) == pPart->iPart );
        bCube = Cudd_bddAnd( p->dd, bTemp = bCube, Cudd_bddIthVar(p->dd, pVar->iVar) ); Cudd_Ref( bCube );
        Cudd_RecursiveDeref( p->dd, bTemp );
    }
    Cudd_Deref( bCube );
    return bCube;
}

/**Function*************************************************************

  Synopsis    [Create cube of variables appearing only in two partitions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Llb_NonlinCreateCube2( Llb_Mgr_t * p, Llb_Prt_t * pPart1, Llb_Prt_t * pPart2 )
{
    DdNode * bCube, * bTemp;
    Llb_Var_t * pVar;
    int i;
    bCube = Cudd_ReadOne(p->dd);   Cudd_Ref( bCube );
    Llb_PartForEachVar( p, pPart1, pVar, i )
    {
        assert( Vec_IntSize(pVar->vParts) > 0 );
        if ( Vec_IntSize(pVar->vParts) != 2 )
            continue;
        if ( (Vec_IntEntry(pVar->vParts, 0) == pPart1->iPart && Vec_IntEntry(pVar->vParts, 1) == pPart2->iPart) ||
             (Vec_IntEntry(pVar->vParts, 0) == pPart2->iPart && Vec_IntEntry(pVar->vParts, 1) == pPart1->iPart) )
        {
            bCube = Cudd_bddAnd( p->dd, bTemp = bCube, Cudd_bddIthVar(p->dd, pVar->iVar) );   Cudd_Ref( bCube );
            Cudd_RecursiveDeref( p->dd, bTemp );
        }
    }
    Cudd_Deref( bCube );
    return bCube;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if partition has singleton variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_NonlinHasSingletonVars( Llb_Mgr_t * p, Llb_Prt_t * pPart )
{
    Llb_Var_t * pVar;
    int i;
    Llb_PartForEachVar( p, pPart, pVar, i )
        if ( Vec_IntSize(pVar->vParts) == 1 )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if partition has singleton variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinPrint( Llb_Mgr_t * p )
{
    Llb_Prt_t * pPart;
    Llb_Var_t * pVar;
    int i, k;
    printf( "\n" );
    Llb_MgrForEachVar( p, pVar, i )
    {
        printf( "Var %3d : ", i );
        Llb_VarForEachPart( p, pVar, pPart, k )
            printf( "%d ", pPart->iPart );
        printf( "\n" );
    }
    Llb_MgrForEachPart( p, pPart, i )
    {
        printf( "Part %3d : ", i );
        Llb_PartForEachVar( p, pPart, pVar, k )
            printf( "%d ", pVar->iVar );
        printf( "\n" );
    }
}

/**Function*************************************************************

  Synopsis    [Quantifies singles belonging to one partition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_NonlinQuantify1( Llb_Mgr_t * p, Llb_Prt_t * pPart, int fSubset )
{
    Llb_Var_t * pVar;
    Llb_Prt_t * pTemp;
    Vec_Ptr_t * vSingles;
    DdNode * bCube, * bTemp;
    int i, RetValue, nSizeNew;
    if ( fSubset )
    {        
        int Length;
//        int nSuppSize = Cudd_SupportSize( p->dd, pPart->bFunc );
//        pPart->bFunc = Cudd_SubsetHeavyBranch( p->dd, bTemp = pPart->bFunc, nSuppSize, 3*pPart->nSize/4 );  Cudd_Ref( pPart->bFunc );
        pPart->bFunc = Cudd_LargestCube( p->dd, bTemp = pPart->bFunc, &Length );  Cudd_Ref( pPart->bFunc );

        printf( "Subsetting %3d : ", pPart->iPart );
        printf( "(Supp =%3d  Node =%5d) -> ", Cudd_SupportSize(p->dd, bTemp),        Cudd_DagSize(bTemp) );
        printf( "(Supp =%3d  Node =%5d)\n",   Cudd_SupportSize(p->dd, pPart->bFunc), Cudd_DagSize(pPart->bFunc) );

        RetValue = (Cudd_DagSize(bTemp) == Cudd_DagSize(pPart->bFunc));

        Cudd_RecursiveDeref( p->dd, bTemp );

        if ( RetValue )
            return 1;
    }
    else
    {
        // create cube to be quantified
        bCube = Llb_NonlinCreateCube1( p, pPart );   Cudd_Ref( bCube );
//        assert( !Cudd_IsConstant(bCube) );
        // derive new function
        pPart->bFunc = Cudd_bddExistAbstract( p->dd, bTemp = pPart->bFunc, bCube );  Cudd_Ref( pPart->bFunc );
        Cudd_RecursiveDeref( p->dd, bTemp );
        Cudd_RecursiveDeref( p->dd, bCube );
    }
    // get support
    vSingles = Vec_PtrAlloc( 0 );
    nSizeNew = Cudd_DagSize(pPart->bFunc);
    Extra_SupportArray( p->dd, pPart->bFunc, p->pSupp );
    Llb_PartForEachVar( p, pPart, pVar, i )
        if ( p->pSupp[pVar->iVar] )
        {
            assert( Vec_IntSize(pVar->vParts) > 1 );
            pVar->nScore -= pPart->nSize - nSizeNew;
        }
        else
        {
            RetValue = Vec_IntRemove( pVar->vParts, pPart->iPart );
            assert( RetValue );
            pVar->nScore -= pPart->nSize;
            if ( Vec_IntSize(pVar->vParts) == 0 )
                Llb_NonlinRemoveVar( p, pVar );
            else if ( Vec_IntSize(pVar->vParts) == 1 )
                Vec_PtrPushUnique( vSingles, Llb_MgrPart(p, Vec_IntEntry(pVar->vParts,0)) );
        }

    // update partition
    pPart->nSize = nSizeNew;
    Vec_IntClear( pPart->vVars );
    for ( i = 0; i < p->nVars; i++ )
        if ( p->pSupp[i] && p->pVars2Q[i] )
            Vec_IntPush( pPart->vVars, i );
    // remove other variables
    Vec_PtrForEachEntry( Llb_Prt_t *, vSingles, pTemp, i )
        Llb_NonlinQuantify1( p, pTemp, 0 );
    Vec_PtrFree( vSingles );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Quantifies singles belonging to one partition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_NonlinQuantify2( Llb_Mgr_t * p, Llb_Prt_t * pPart1, Llb_Prt_t * pPart2, int Limit )
{
    int fVerbose = 0;
    Llb_Var_t * pVar;
    Llb_Prt_t * pTemp;
    Vec_Ptr_t * vSingles;
    DdNode * bCube, * bFunc;
    int i, RetValue, nSuppSize;
    int iPart1 = pPart1->iPart;
    int iPart2 = pPart2->iPart;
/*
    if ( iPart1 == 91 && iPart2 == 134 )
    {
        fVerbose = 1;
    }
*/
    // create cube to be quantified
    bCube = Llb_NonlinCreateCube2( p, pPart1, pPart2 );   Cudd_Ref( bCube );
if ( fVerbose )
{
printf( "\n" );
printf( "\n" );
Llb_NonlinPrint( p );
printf( "Conjoining partitions %d and %d.\n", pPart1->iPart, pPart2->iPart );
Extra_bddPrintSupport( p->dd, bCube );  printf( "\n" );
}

    // derive new function
//    bFunc = Cudd_bddAndAbstract( p->dd, pPart1->bFunc, pPart2->bFunc, bCube );  Cudd_Ref( bFunc );
    bFunc = Cudd_bddAndAbstractLimit( p->dd, pPart1->bFunc, pPart2->bFunc, bCube, Limit );  
    if ( bFunc == NULL )
    {
        int RetValue;
        Cudd_RecursiveDeref( p->dd, bCube );
        if ( pPart1->nSize < pPart2->nSize )
            RetValue = Llb_NonlinQuantify1( p, pPart1, 1 );
        else
            RetValue = Llb_NonlinQuantify1( p, pPart2, 1 );
        if ( RetValue )
            Limit = Limit + 1000;

        Llb_NonlinQuantify2( p, pPart1, pPart2, Limit );
        return 1;
    }
    Cudd_Ref( bFunc );
    Cudd_RecursiveDeref( p->dd, bCube );
    // create new partition
    pTemp = p->pParts[p->iPartFree] = ABC_CALLOC( Llb_Prt_t, 1 );
    pTemp->iPart = p->iPartFree++;
    pTemp->nSize = Cudd_DagSize(bFunc);
    pTemp->bFunc = bFunc;
    pTemp->vVars = Vec_IntAlloc( 8 );
    // update variables
    Llb_PartForEachVar( p, pPart1, pVar, i )
    {
        RetValue = Vec_IntRemove( pVar->vParts, pPart1->iPart );
        assert( RetValue );
        pVar->nScore -= pPart1->nSize;
    }
    // update variables
    Llb_PartForEachVar( p, pPart2, pVar, i )
    {
        RetValue = Vec_IntRemove( pVar->vParts, pPart2->iPart );
        assert( RetValue );
        pVar->nScore -= pPart2->nSize;
    }
    // add variables to the new partition
    nSuppSize = 0;
    Extra_SupportArray( p->dd, bFunc, p->pSupp );
    for ( i = 0; i < p->nVars; i++ )
    {
        nSuppSize += p->pSupp[i];
        if ( p->pSupp[i] && p->pVars2Q[i] )
        {
            pVar = Llb_MgrVar( p, i );
            pVar->nScore += pTemp->nSize;
            Vec_IntPush( pVar->vParts, pTemp->iPart );
            Vec_IntPush( pTemp->vVars, i );
        }
    }
    p->nSuppMax = ABC_MAX( p->nSuppMax, nSuppSize ); 
    // remove variables and collect partitions with singleton variables
    vSingles = Vec_PtrAlloc( 0 );
    Llb_PartForEachVar( p, pPart1, pVar, i )
    {
        if ( Vec_IntSize(pVar->vParts) == 0 )
            Llb_NonlinRemoveVar( p, pVar );
        else if ( Vec_IntSize(pVar->vParts) == 1 )
        {
            if ( fVerbose )
                printf( "Adding partition %d because of var %d.\n", 
                    Llb_MgrPart(p, Vec_IntEntry(pVar->vParts,0))->iPart, pVar->iVar );
            Vec_PtrPushUnique( vSingles, Llb_MgrPart(p, Vec_IntEntry(pVar->vParts,0)) );
        }
    }
    Llb_PartForEachVar( p, pPart2, pVar, i )
    {
        if ( pVar == NULL )
            continue;
        if ( Vec_IntSize(pVar->vParts) == 0 )
            Llb_NonlinRemoveVar( p, pVar );
        else if ( Vec_IntSize(pVar->vParts) == 1 )
        {
            if ( fVerbose )
                printf( "Adding partition %d because of var %d.\n", 
                    Llb_MgrPart(p, Vec_IntEntry(pVar->vParts,0))->iPart, pVar->iVar );
            Vec_PtrPushUnique( vSingles, Llb_MgrPart(p, Vec_IntEntry(pVar->vParts,0)) );
        }
    }
    // remove partitions
    Llb_NonlinRemovePart( p, pPart1 );
    Llb_NonlinRemovePart( p, pPart2 );
    // remove other variables
if ( fVerbose )
Llb_NonlinPrint( p );
    Vec_PtrForEachEntry( Llb_Prt_t *, vSingles, pTemp, i )
    {
if ( fVerbose )
printf( "Updating partitiong %d with singlton vars.\n", pTemp->iPart );
        Llb_NonlinQuantify1( p, pTemp, 0 );
    }
if ( fVerbose )
Llb_NonlinPrint( p );
    Vec_PtrFree( vSingles );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Computes volume of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinCutNodes_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    if ( Saig_ObjIsLi(p, pObj) )
    {
        Llb_NonlinCutNodes_rec(p, Aig_ObjFanin0(pObj), vNodes);
        return;
    }
    if ( Aig_ObjIsConst1(pObj) )
        return;
    assert( Aig_ObjIsNode(pObj) );
    Llb_NonlinCutNodes_rec(p, Aig_ObjFanin0(pObj), vNodes);
    Llb_NonlinCutNodes_rec(p, Aig_ObjFanin1(pObj), vNodes);
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Computes volume of the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Llb_NonlinCutNodes( Aig_Man_t * p, Vec_Ptr_t * vLower, Vec_Ptr_t * vUpper )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj;
    int i;
    // mark the lower cut with the traversal ID
    Aig_ManIncrementTravId(p);
    Vec_PtrForEachEntry( Aig_Obj_t *, vLower, pObj, i )
        Aig_ObjSetTravIdCurrent( p, pObj );
    // count the upper cut
    vNodes = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vUpper, pObj, i )
        Llb_NonlinCutNodes_rec( p, pObj, vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Returns array of BDDs for the roots in terms of the leaves.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Llb_NonlinBuildBdds( Aig_Man_t * p, Vec_Ptr_t * vLower, Vec_Ptr_t * vUpper, DdManager * dd )
{
    Vec_Ptr_t * vNodes, * vResult;
    Aig_Obj_t * pObj;
    DdNode * bBdd0, * bBdd1, * bProd;
    int i;

    Aig_ManConst1(p)->pData = Cudd_ReadOne( dd );
    Vec_PtrForEachEntry( Aig_Obj_t *, vLower, pObj, i )
        pObj->pData = Cudd_bddIthVar( dd, Aig_ObjId(pObj) );

    vNodes = Llb_NonlinCutNodes( p, vLower, vUpper );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
    {
        bBdd0 = Cudd_NotCond( (DdNode *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj) );
        bBdd1 = Cudd_NotCond( (DdNode *)Aig_ObjFanin1(pObj)->pData, Aig_ObjFaninC1(pObj) );
        pObj->pData = Cudd_bddAnd( dd, bBdd0, bBdd1 );   Cudd_Ref( (DdNode *)pObj->pData );
    }

    vResult = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vUpper, pObj, i )
    {
        if ( Aig_ObjIsNode(pObj) )
        {
            bProd = Cudd_bddXnor( dd, Cudd_bddIthVar(dd, Aig_ObjId(pObj)), (DdNode *)pObj->pData );  Cudd_Ref( bProd );
        }
        else
        {
            assert( Saig_ObjIsLi(p, pObj) );
            bBdd0 = Cudd_NotCond( (DdNode *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj) );
            bProd = Cudd_bddXnor( dd, Cudd_bddIthVar(dd, Aig_ObjId(pObj)), bBdd0 );                  Cudd_Ref( bProd );
        }
        Vec_PtrPush( vResult, bProd );
    }
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        Cudd_RecursiveDeref( dd, (DdNode *)pObj->pData );

    Vec_PtrFree( vNodes );
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Starts non-linear quantification scheduling.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinAddPair( Llb_Mgr_t * p, DdNode * bFunc, int iPart, int iVar )
{
    if ( p->pVars[iVar] == NULL )
    {
        p->pVars[iVar] = ABC_CALLOC( Llb_Var_t, 1 );
        p->pVars[iVar]->iVar   = iVar;
        p->pVars[iVar]->nScore = 0;
        p->pVars[iVar]->vParts = Vec_IntAlloc( 8 );
    }
    Vec_IntPush( p->pVars[iVar]->vParts, iPart );
    Vec_IntPush( p->pParts[iPart]->vVars, iVar );
}

/**Function*************************************************************

  Synopsis    [Starts non-linear quantification scheduling.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinStart( Llb_Mgr_t * p )
{
    Vec_Ptr_t * vRootBdds;
    Llb_Prt_t * pPart;
    DdNode * bFunc;
    int i, k, nSuppSize;
    // create and collect BDDs
    vRootBdds = Llb_NonlinBuildBdds( p->pAig, p->vLeaves, p->vRoots, p->dd ); // come referenced
    Vec_PtrForEachEntry( DdNode *, p->vFuncs, bFunc, i )
        Vec_PtrPush( vRootBdds, bFunc );
    // add pairs (refs are consumed inside)
    Vec_PtrForEachEntry( DdNode *, vRootBdds, bFunc, i )
    {
        assert( !Cudd_IsConstant(bFunc) );
        // create partition
        p->pParts[i] = ABC_CALLOC( Llb_Prt_t, 1 );
        p->pParts[i]->iPart = i;
        p->pParts[i]->bFunc = bFunc;
        p->pParts[i]->vVars = Vec_IntAlloc( 8 );
        // add support dependencies
        nSuppSize = 0;
        Extra_SupportArray( p->dd, bFunc, p->pSupp );
        for ( k = 0; k < p->nVars; k++ )
        {
            nSuppSize += p->pSupp[k];
            if ( p->pSupp[k] && p->pVars2Q[k] )
                Llb_NonlinAddPair( p, bFunc, i, k );
        }
        p->nSuppMax = ABC_MAX( p->nSuppMax, nSuppSize ); 
    }
    Vec_PtrFree( vRootBdds );
    // remove singles
    Llb_MgrForEachPart( p, pPart, i )
        if ( Llb_NonlinHasSingletonVars(p, pPart) )
            Llb_NonlinQuantify1( p, pPart, 0 );
}

/**Function*************************************************************

  Synopsis    [Starts non-linear quantification scheduling.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Llb_Mgr_t * Llb_NonlinAlloc( Aig_Man_t * pAig, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vRoots, int * pVars2Q, DdManager * dd, Vec_Ptr_t * vFuncs )
{
    Llb_Mgr_t * p;
    p = ABC_CALLOC( Llb_Mgr_t, 1 );
    p->pAig      = pAig;
    p->vLeaves   = vLeaves;
    p->vRoots    = vRoots;
    p->dd        = dd;
    p->vFuncs    = vFuncs;
    p->pVars2Q   = pVars2Q;
    p->nVars     = Cudd_ReadSize(dd);
    p->iPartFree = Vec_PtrSize(vRoots) + Vec_PtrSize(vFuncs);
    p->pVars     = ABC_CALLOC( Llb_Var_t *, p->nVars );
    p->pParts    = ABC_CALLOC( Llb_Prt_t *, 2 * p->iPartFree );
    p->pSupp     = ABC_ALLOC( int, Cudd_ReadSize(dd) );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops non-linear quantification scheduling.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinFree( Llb_Mgr_t * p )
{
    Llb_Prt_t * pPart;
    Llb_Var_t * pVar;
    int i;
    Llb_MgrForEachVar( p, pVar, i )
        Llb_NonlinRemoveVar( p, pVar );
    Llb_MgrForEachPart( p, pPart, i )
        Llb_NonlinRemovePart( p, pPart );
    ABC_FREE( p->pVars );
    ABC_FREE( p->pParts );
    ABC_FREE( p->pSupp );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Checks that each var appears in at least one partition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinCheckVars( Llb_Mgr_t * p )
{
    Llb_Var_t * pVar;
    int i;
    Llb_MgrForEachVar( p, pVar, i )
        assert( Vec_IntSize(pVar->vParts) > 1 );
}

/**Function*************************************************************

  Synopsis    [Find next partition to quantify]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_NonlinNextPartitions( Llb_Mgr_t * p, Llb_Prt_t ** ppPart1, Llb_Prt_t ** ppPart2 )
{
    Llb_Var_t * pVar, * pVarBest = NULL;
    Llb_Prt_t * pPart, * pPart1Best = NULL, * pPart2Best = NULL;
    int i;
    Llb_NonlinCheckVars( p );
    // find variable with minimum score
    Llb_MgrForEachVar( p, pVar, i )
        if ( pVarBest == NULL || pVarBest->nScore > pVar->nScore )
            pVarBest = pVar;
    if ( pVarBest == NULL )
        return 0;
    // find two partitions with minimum size
    Llb_VarForEachPart( p, pVarBest, pPart, i )
    {
        if ( pPart1Best == NULL )
            pPart1Best = pPart;
        else if ( pPart2Best == NULL )
            pPart2Best = pPart;
        else if ( pPart1Best->nSize > pPart->nSize || pPart2Best->nSize > pPart->nSize )
        {
            if ( pPart1Best->nSize > pPart2Best->nSize )
                pPart1Best = pPart;
            else
                pPart2Best = pPart;
        }
    }
    *ppPart1 = pPart1Best;
    *ppPart2 = pPart2Best;
    return 1; 
}

/**Function*************************************************************

  Synopsis    [Reorders BDDs in the working manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinReorder( DdManager * dd, int fVerbose )
{
    int clk = clock();
    if ( fVerbose )
        Abc_Print( 1, "Reordering... Before =%5d. ", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd) );
    Cudd_ReduceHeap( dd, CUDD_REORDER_SYMM_SIFT, 100 );
    if ( fVerbose )
        Abc_Print( 1, "After =%5d. ", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd) );
    Cudd_ReduceHeap( dd, CUDD_REORDER_SYMM_SIFT, 100 );
    if ( fVerbose )
        Abc_Print( 1, "After =%5d. ", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd) );
    if ( fVerbose )
        Abc_PrintTime( 1, "Time", clock() - clk );
}

/**Function*************************************************************

  Synopsis    [Recomputes scores after variable reordering.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinRecomputeScores( Llb_Mgr_t * p )
{
    Llb_Prt_t * pPart;
    Llb_Var_t * pVar;
    int i, k;
    Llb_MgrForEachPart( p, pPart, i )
        pPart->nSize = Cudd_DagSize(pPart->bFunc);
    Llb_MgrForEachVar( p, pVar, i )
    {
        pVar->nScore = 0;
        Llb_VarForEachPart( p, pVar, pPart, k )
            pVar->nScore += pPart->nSize;
    }
}

/**Function*************************************************************

  Synopsis    [Recomputes scores after variable reordering.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinVerifyScores( Llb_Mgr_t * p )
{
    Llb_Prt_t * pPart;
    Llb_Var_t * pVar;
    int i, k, nScore;
    Llb_MgrForEachPart( p, pPart, i )
        assert( pPart->nSize == Cudd_DagSize(pPart->bFunc) );
    Llb_MgrForEachVar( p, pVar, i )
    {
        nScore = 0;
        Llb_VarForEachPart( p, pVar, pPart, k )
            nScore += pPart->nSize;
        assert( nScore == pVar->nScore );
    }
}

/**Function*************************************************************

  Synopsis    [Performs image computation.]

  Description [Computes image of BDDs (vFuncs).]
               
  SideEffects [BDDs in vFuncs are derefed inside. The result is refed.]

  SeeAlso     []

***********************************************************************/
int Llb_NonlinImage( Aig_Man_t * pAig, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vRoots, int * pVars2Q, 
    DdManager * dd, Vec_Ptr_t * vFuncs, int fReorder, int fVerbose, int * pOrder, int * pfSubset, int Limit )
{
    Llb_Prt_t * pPart, * pPart1, * pPart2;
    Llb_Mgr_t * p;
    int i, nReorders, timeInside, fSubset = 0;
    int clk = clock(), clk2;
    // start the manager
    clk2 = clock();
    p = Llb_NonlinAlloc( pAig, vLeaves, vRoots, pVars2Q, dd, vFuncs );
    Llb_NonlinStart( p );
    timeBuild += clock() - clk2;
    timeInside = clock() - clk2;
    // reorder variables
//    if ( fReorder )
//        Llb_NonlinReorder( dd, fVerbose );
    // compute scores
    Llb_NonlinRecomputeScores( p );
    // save permutation
    memcpy( pOrder, dd->invperm, sizeof(int) * dd->size );
    // iteratively quantify variables
    while ( Llb_NonlinNextPartitions(p, &pPart1, &pPart2) )
    {
        nReorders = Cudd_ReadReorderings(dd);
        clk2 = clock();
        fSubset |= Llb_NonlinQuantify2( p, pPart1, pPart2, Limit );
        timeAndEx += clock() - clk2;
        timeInside += clock() - clk2;
        if ( nReorders < Cudd_ReadReorderings(dd) )
            Llb_NonlinRecomputeScores( p );
//        else
//            Llb_NonlinVerifyScores( p );
    }
    // load partitions
    Vec_PtrClear( vFuncs );
    Llb_MgrForEachPart( p, pPart, i )
    {
        Vec_PtrPush( vFuncs, pPart->bFunc );
        Cudd_Ref( pPart->bFunc );
    }
    nSuppMax = p->nSuppMax;
    Llb_NonlinFree( p );
    // reorder variables
    if ( fReorder )
        Llb_NonlinReorder( dd, fVerbose );
    timeOther += clock() - clk - timeInside;
    if ( pfSubset )
        *pfSubset |= fSubset;
    return 1;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinPrepareVarMap( Aig_Man_t * pAig, Vec_Int_t ** pvNs2Glo, Vec_Int_t ** pvGlo2Cs )
{
    Aig_Obj_t * pObjLi, * pObjLo;
    int i, iVarLi, iVarLo;
    *pvNs2Glo = Vec_IntStartFull( Aig_ManObjNumMax(pAig) );
    *pvGlo2Cs = Vec_IntStartFull( Aig_ManRegNum(pAig) );
    Saig_ManForEachLiLo( pAig, pObjLi, pObjLo, i )
    {
        iVarLi = Aig_ObjId(pObjLi);
        iVarLo = Aig_ObjId(pObjLo);
        assert( iVarLi >= 0 && iVarLi < Aig_ManObjNumMax(pAig) );
        assert( iVarLo >= 0 && iVarLo < Aig_ManObjNumMax(pAig) );
        Vec_IntWriteEntry( *pvNs2Glo, iVarLi, i );
        Vec_IntWriteEntry( *pvGlo2Cs, i, iVarLo );
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Llb_NonlinComputeInitState( Aig_Man_t * pAig, DdManager * dd )
{
    Aig_Obj_t * pObj;
    DdNode * bRes, * bVar, * bTemp;
    int i, iVar;
    bRes = Cudd_ReadOne( dd );   Cudd_Ref( bRes );
    Saig_ManForEachLo( pAig, pObj, i )
    {
        iVar = (Cudd_ReadSize(dd) == Aig_ManRegNum(pAig)) ? i : Aig_ObjId(pObj);
        bVar = Cudd_bddIthVar( dd, iVar );
        bRes = Cudd_bddAnd( dd, bTemp = bRes, Cudd_Not(bVar) );  Cudd_Ref( bRes );
        Cudd_RecursiveDeref( dd, bTemp );
    }
    Cudd_Deref( bRes );
    return bRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Llb_NonlinComputeInitStateVec( Aig_Man_t * pAig, DdManager * dd )
{
    Vec_Ptr_t * vFuncs;
    Aig_Obj_t * pObj;
    DdNode * bVar;
    int i;
    vFuncs = Vec_PtrAlloc( Aig_ManRegNum(pAig) );
    Saig_ManForEachLo( pAig, pObj, i )
    {
        bVar = Cudd_bddIthVar( dd, Aig_ObjId(pObj) );  Cudd_Ref( bVar );
        Vec_PtrPush( vFuncs, Cudd_Not(bVar) );
    }
    return vFuncs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinDerefVec( DdManager * dd, Vec_Ptr_t * vFuncs )
{
    DdNode * bFunc;
    int i;
    Vec_PtrForEachEntry( DdNode *, vFuncs, bFunc, i )
        Cudd_RecursiveDeref( dd, bFunc );
    Vec_PtrFree( vFuncs );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinTransferVec( DdManager * dd, DdManager * ddG, Vec_Ptr_t * vFuncs, Vec_Int_t * vNs2Glo )
{
    DdNode * bFunc, * bTemp;
    int i;
    Vec_PtrForEachEntry( DdNode *, vFuncs, bFunc, i )
    {
        bFunc = Extra_TransferPermute( dd, ddG, bTemp = bFunc, Vec_IntArray(vNs2Glo) );    Cudd_Ref( bFunc );
        Cudd_RecursiveDeref( dd, bTemp );
        Vec_PtrWriteEntry( vFuncs, i, bFunc );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinSharpVec( DdManager * ddG, DdNode * bReached, Vec_Ptr_t * vFuncs )
{
    DdNode * bFunc, * bTemp;
    int i;
    Vec_PtrForEachEntry( DdNode *, vFuncs, bFunc, i )
    {
        bFunc = Cudd_bddAnd( ddG, bTemp = bFunc, Cudd_Not(bReached) );   Cudd_Ref( bFunc );
        Cudd_RecursiveDeref( ddG, bTemp );
        Vec_PtrWriteEntry( vFuncs, i, bFunc );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Llb_NonlinAddToReachVec( DdManager * ddG, DdNode * bReached, Vec_Ptr_t * vFuncs )
{
    DdNode * bFunc, * bProd, * bTemp;
    int i;
    bProd = Cudd_ReadOne( ddG );  Cudd_Ref( bProd );
    Vec_PtrForEachEntry( DdNode *, vFuncs, bFunc, i )
    {
        bProd = Cudd_bddAnd( ddG, bTemp = bProd, bFunc );     Cudd_Ref( bProd );
        Cudd_RecursiveDeref( ddG, bTemp );
    }
    if ( Cudd_IsConstant(bProd) )
    {
        Cudd_RecursiveDeref( ddG, bProd );
        return NULL;
    }
    bTemp = Cudd_bddOr( ddG, bReached, bProd );   Cudd_Ref( bTemp );
    Cudd_RecursiveDeref( ddG, bProd );
    Cudd_Deref( bTemp );
    return bTemp;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Llb_NonlinCreateReachVec( DdManager * dd, DdManager * ddG, DdNode * bReachG, Vec_Int_t * vGlo2Cs )
{
    Vec_Ptr_t * vFuncs;
    DdNode * bFunc;
    vFuncs = Vec_PtrAlloc( 1 );
    bFunc = Extra_TransferPermute( ddG, dd, bReachG, Vec_IntArray(vGlo2Cs) );    Cudd_Ref( bFunc );
    Vec_PtrPush( vFuncs, bFunc );
//    Llb_NonlinReorder( dd, 1 );
    return vFuncs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinPrintVec( DdManager * dd, Vec_Ptr_t * vFuncs )
{
    DdNode * bFunc;
    int i;
    Vec_PtrForEachEntry( DdNode *, vFuncs, bFunc, i )
    {
        printf( "%2d :  ", i );
        printf( "Support =%5d  ", Cudd_SupportSize(dd, bFunc) );
        printf( "DagSize =%7d\n", Cudd_DagSize(bFunc) );
    }
}

/**Function*************************************************************

  Synopsis    [Perform reachability with hints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_NonlinReachability( Aig_Man_t * pAig, Gia_ParLlb_t * pPars )
{ 
    Aig_Obj_t * pObj;
    Vec_Ptr_t * vLeaves, * vRoots, * vParts;
    Vec_Int_t * vNs2Glo, * vGlo2Cs;
    DdManager * dd, * ddG;
    DdNode * bReached, * bTemp;
    int i, nIters, nBddSize0, nBddSize, Limit, fSubset, * pVars2Q, * pOrder;
    int clk2, clk3, clk = clock();
//    int RetValue;
    int timeImage = 0;
    int timeTran1 = 0;
    int timeTran2 = 0;
    int timeGloba = 0;
    int timeOther = 0;
    int timeTotal = 0;
    int timeReo   = 0;
    int timeReoG  = 0;
    assert( Aig_ManRegNum(pAig) > 0 );
    timeBuild = timeAndEx = timeOther = 0;

    // compute time to stop
    if ( pPars->TimeLimit )
        pPars->TimeTarget = clock() + pPars->TimeLimit * CLOCKS_PER_SEC;
    else
        pPars->TimeTarget = 0;

    // create leaves
    vLeaves = Vec_PtrAlloc( Aig_ManPiNum(pAig) );
    Aig_ManForEachPi( pAig, pObj, i )
        Vec_PtrPush( vLeaves, pObj );

    // create roots
    vRoots = Vec_PtrAlloc( Aig_ManPoNum(pAig) );
    Saig_ManForEachLi( pAig, pObj, i )
        Vec_PtrPush( vRoots, pObj );

    // variables to quantify
    pOrder  = ABC_CALLOC( int, Aig_ManObjNumMax(pAig) );
    pVars2Q = ABC_CALLOC( int, Aig_ManObjNumMax(pAig) );
    Aig_ManForEachPi( pAig, pObj, i )
        pVars2Q[Aig_ObjId(pObj)] = 1;

    // start the managers
    Llb_NonlinPrepareVarMap( pAig, &vNs2Glo, &vGlo2Cs ); 
    dd  = Cudd_Init( Aig_ManObjNumMax(pAig), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    ddG = Cudd_Init( Aig_ManRegNum(pAig),    0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    Cudd_AutodynEnable( dd,  CUDD_REORDER_SYMM_SIFT );
    Cudd_AutodynEnable( ddG, CUDD_REORDER_SYMM_SIFT );

    // compute the starting set of states
    vParts   = Llb_NonlinComputeInitStateVec( pAig, dd );
    bReached = Llb_NonlinComputeInitState( pAig, ddG );          Cudd_Ref( bReached );
    fSubset  = 1;
    for ( Limit = pPars->nBddMax; fSubset; Limit *= 2 )
    {
        if ( pPars->fVerbose )
        printf( "*********** LIMIT %d ************\n", Limit );
        fSubset = 0;
        for ( nIters = 0; nIters < pPars->nIterMax; nIters++ )
        { 
            clk2 = clock();
            // check the runtime limit
            if ( pPars->TimeLimit && clock() >= pPars->TimeTarget )
            {
                if ( !pPars->fSilent )
                    printf( "Reached timeout during image computation (%d seconds).\n",  pPars->TimeLimit );
                pPars->iFrame = nIters - 1;
                Llb_NonlinDerefVec( dd, vParts );      vParts = NULL;
                Cudd_RecursiveDeref( ddG, bReached );  bReached = NULL;
                return -1;
            }

//            Llb_NonlinReorder( dd, 1 );

            // compute the next states
            clk3 = clock();
            nBddSize0 = Cudd_SharingSize( (DdNode **)Vec_PtrArray(vParts), Vec_PtrSize(vParts) );
            if ( !Llb_NonlinImage( pAig, vLeaves, vRoots, pVars2Q, dd, vParts, pPars->fReorder, pPars->fVeryVerbose, pOrder, &fSubset, Limit ) )
            {
                if ( !pPars->fSilent )
                    printf( "Reached timeout during image computation (%d seconds).\n",  pPars->TimeLimit );
                pPars->iFrame = nIters - 1;
                Llb_NonlinDerefVec( dd, vParts );      vParts = NULL;
                Cudd_RecursiveDeref( ddG, bReached );  bReached = NULL;
                return -1;
            }
            timeImage += clock() - clk3;
            nBddSize = Cudd_SharingSize( (DdNode **)Vec_PtrArray(vParts), Vec_PtrSize(vParts) );
//            Llb_NonlinPrintVec( dd, vParts );

            // check containment in reached and derive new frontier
            clk3 = clock();
            Llb_NonlinTransferVec( dd, ddG, vParts, vNs2Glo );
            timeTran1 += clock() - clk3;

            clk3 = clock();
            Llb_NonlinSharpVec( ddG, bReached, vParts );
            bReached = Llb_NonlinAddToReachVec( ddG, bTemp = bReached, vParts );
            if ( bReached == NULL )
            {
                bReached = bTemp;
                Llb_NonlinDerefVec( ddG, vParts );      vParts = NULL;
                if ( fSubset )
                    vParts = Llb_NonlinCreateReachVec( dd, ddG, bReached, vGlo2Cs );
                break;
            }
            Cudd_Ref( bReached );
            Cudd_RecursiveDeref( ddG, bTemp );
            timeGloba += clock() - clk3;

            // reset permutation
    //        RetValue = Cudd_CheckZeroRef( dd );
    //        assert( RetValue == 0 );
    //        Cudd_ShuffleHeap( dd, pOrder );

            clk3 = clock();
            Llb_NonlinTransferVec( ddG, dd, vParts, vGlo2Cs );
//            Llb_NonlinDerefVec( ddG, vParts );      vParts = NULL;
//            vParts = Llb_NonlinCreateReachVec( dd, ddG, bReached, vGlo2Cs );
            timeTran2 += clock() - clk3;

            // report the results
            if ( pPars->fVerbose )
            {
                printf( "I =%3d : ",   nIters );
                printf( "Fr =%6d ",    nBddSize0 );
                printf( "Im =%6d  ",   nBddSize );
                printf( "(%4d %3d)  ", Cudd_ReadReorderings(dd),  Cudd_ReadGarbageCollections(dd) );
                printf( "Rea =%6d  ",  Cudd_DagSize(bReached) );
                printf( "(%4d %3d)  ", Cudd_ReadReorderings(ddG), Cudd_ReadGarbageCollections(ddG) );
                printf( "S =%4d ",     nSuppMax );
                printf( "P =%2d  ",    Vec_PtrSize(vParts) );
                Abc_PrintTime( 1, "T", clock() - clk2 );
            }
    /*
            if ( pPars->fVerbose )
            {
                double nMints = Cudd_CountMinterm(ddG, bReached, Saig_ManRegNum(pAig) );
    //            Extra_bddPrint( ddG, bReached );printf( "\n" );
                printf( "Reachable states = %.0f. (Ratio = %.4f %%)\n", nMints, 100.0*nMints/pow(2.0, Saig_ManRegNum(pAig)) );
                fflush( stdout ); 
            }
    */

            if ( nIters == pPars->nIterMax - 1 )
            {
                if ( !pPars->fSilent )
                    printf( "Reached limit on the number of timeframes (%d).\n",  pPars->nIterMax );
                pPars->iFrame = nIters;
                Llb_NonlinDerefVec( dd, vParts );      vParts = NULL;
                Cudd_RecursiveDeref( ddG, bReached );  bReached = NULL;
                return -1;
            }

//            Llb_NonlinReorder( ddG, 1 );
//            Llb_NonlinFindBestVar( ddG, bReached, NULL );
        }
    } 
    
    if ( bReached == NULL )
        return 0; // reachable
    // report the stats
    if ( pPars->fVerbose )
    {
        double nMints = Cudd_CountMinterm(ddG, bReached, Saig_ManRegNum(pAig) );
        if ( nIters >= pPars->nIterMax || nBddSize > pPars->nBddMax )
            printf( "Reachability analysis is stopped after %d frames.\n", nIters );
        else
            printf( "Reachability analysis completed after %d frames.\n", nIters );
        printf( "Reachable states = %.0f. (Ratio = %.4f %%)\n", nMints, 100.0*nMints/pow(2.0, Saig_ManRegNum(pAig)) );
        fflush( stdout ); 
    }
    if ( nIters >= pPars->nIterMax || nBddSize > pPars->nBddMax )
    {
        if ( !pPars->fSilent )
            printf( "Verified only for states reachable in %d frames.  ", nIters );
        Cudd_RecursiveDeref( ddG, bReached );
        return -1; // undecided
    }
    // cleanup
    Cudd_RecursiveDeref( ddG, bReached );
    timeReo  = Cudd_ReadReorderingTime(dd);
    timeReoG = Cudd_ReadReorderingTime(ddG);
    Extra_StopManager( dd );
    Extra_StopManager( ddG );
    // cleanup
    Vec_IntFree( vNs2Glo );
    Vec_IntFree( vGlo2Cs );
    Vec_PtrFree( vLeaves );
    Vec_PtrFree( vRoots );
    ABC_FREE( pVars2Q );
    ABC_FREE( pOrder );
    // report
    if ( !pPars->fSilent )
        printf( "The miter is proved unreachable after %d iterations.  ", nIters );
    pPars->iFrame = nIters - 1;
    Abc_PrintTime( 1, "Time", clock() - clk );

    if ( pPars->fVerbose ) 
    {
        timeTotal = clock() - clk;
        timeOther = timeTotal - timeImage - timeTran1 - timeTran2 - timeGloba;
        ABC_PRTP( "Image    ", timeImage, timeTotal );
        ABC_PRTP( "  build  ", timeBuild, timeTotal );
        ABC_PRTP( "  and-ex ", timeAndEx, timeTotal );
        ABC_PRTP( "  other  ", timeOther, timeTotal );
        ABC_PRTP( "Transfer1", timeTran1, timeTotal );
        ABC_PRTP( "Transfer2", timeTran2, timeTotal );
        ABC_PRTP( "Global   ", timeGloba, timeTotal );
        ABC_PRTP( "Other    ", timeOther, timeTotal );
        ABC_PRTP( "TOTAL    ", timeTotal, timeTotal );
        ABC_PRTP( "  reo    ", timeReo,   timeTotal );
        ABC_PRTP( "  reoG   ", timeReoG,  timeTotal );
    }
    return 1; // unreachable
}

/**Function*************************************************************

  Synopsis    [Finds balanced cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_NonlinExperiment( Aig_Man_t * pAig, int Num )
{
    Gia_ParLlb_t Pars, * pPars = &Pars;
    Aig_Man_t * p;

    Llb_ManSetDefaultParams( pPars );
    pPars->fVerbose = 1;

    p = Aig_ManDupFlopsOnly( pAig );
//Aig_ManShow( p, 0, NULL );
    Aig_ManPrintStats( pAig );
    Aig_ManPrintStats( p );

    Llb_NonlinReachability( p, pPars );

    Aig_ManStop( p );
}

/**Function*************************************************************

  Synopsis    [Finds balanced cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_NonlinCoreReach( Aig_Man_t * pAig, Gia_ParLlb_t * pPars )
{
    Aig_Man_t * p;
    int RetValue = -1;

    p = Aig_ManDupFlopsOnly( pAig );
//Aig_ManShow( p, 0, NULL );
    if ( pPars->fVerbose )
    Aig_ManPrintStats( pAig );
    if ( pPars->fVerbose )
    Aig_ManPrintStats( p );

    if ( !pPars->fSkipReach )
        RetValue = Llb_NonlinReachability( p, pPars );

    Aig_ManStop( p );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

