/**CFile****************************************************************

  FileName    [kitDsd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Computation kit.]

  Synopsis    [Performs disjoint-support decomposition based on truth tables.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Dec 6, 2006.]

  Revision    [$Id: kitDsd.c,v 1.00 2006/12/06 00:00:00 alanmi Exp $]

***********************************************************************/

#include "kit.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Dsd_Man_t_ Dsd_Man_t;
typedef struct Dsd_Ntk_t_ Dsd_Ntk_t;
typedef struct Dsd_Obj_t_ Dsd_Obj_t;

// DSD node types
typedef enum { 
    KIT_DSD_NONE  = 0,  // 0: unknown
    KIT_DSD_CONST1,     // 1: constant 1
    KIT_DSD_VAR,        // 2: elementary variable
    KIT_DSD_AND,        // 3: multi-input AND
    KIT_DSD_XOR,        // 4: multi-input XOR
    KIT_DSD_PRIME       // 5: arbitrary function of 3+ variables
} Kit_Dsd_t;

// DSD manager
struct Dsd_Man_t_
{
    int            nVars;           // the maximum number of variables
    int            nWords;          // the number of words in TTs
    Vec_Ptr_t *    vTtElems;        // elementary truth tables
    Vec_Ptr_t *    vTtNodes;        // the node truth tables
};

// DSD network
struct Dsd_Ntk_t_
{
    unsigned char  nVars;           // at most 16 (perhaps 18?)
    unsigned char  nNodesAlloc;     // the number of allocated nodes (at most nVars)
    unsigned char  nNodes;          // the number of nodes
    unsigned char  Root;            // the root of the tree
    unsigned *     pMem;            // memory for the truth tables (memory manager?)
    Dsd_Obj_t *    pNodes[0];       // the nodes
};

// DSD node
struct Dsd_Obj_t_
{ 
    unsigned       Id         : 6;  // the number of this node
    unsigned       Type       : 3;  // none, const, var, AND, XOR, MUX, PRIME
    unsigned       fMark      : 1;  // finished checking output
    unsigned       Offset     : 8;  // offset to the truth table
    unsigned       nRefs      : 8;  // offset to the truth table
    unsigned       nFans      : 6;  // the number of fanins of this node
    unsigned char  pFans[0];        // the fanin literals
};

static inline int          Dsd_Var2Lit( int Var, int fCompl ) { return Var + Var + fCompl; }
static inline int          Dsd_Lit2Var( int Lit )             { return Lit >> 1;           }
static inline int          Dsd_LitIsCompl( int Lit )          { return Lit & 1;            }
static inline int          Dsd_LitNot( int Lit )              { return Lit ^ 1;            }
static inline int          Dsd_LitNotCond( int Lit, int c )   { return Lit ^ (int)(c > 0); }
static inline int          Dsd_LitRegular( int Lit )          { return Lit & 0xfe;         }
 
static inline unsigned     Dsd_ObjOffset( int nFans )         { return (nFans >> 2) + ((nFans & 3) > 0); }
static inline unsigned *   Dsd_ObjTruth( Dsd_Obj_t * pObj )   { return pObj->Type == KIT_DSD_PRIME ? (unsigned *)pObj->pFans + pObj->Offset: NULL; }
static inline Dsd_Obj_t *  Dsd_NtkObj( Dsd_Ntk_t * pNtk, int Id )  { assert( Id >= 0 && Id < pNtk->nVars + pNtk->nNodes ); return Id < pNtk->nVars ? NULL : pNtk->pNodes[Id - pNtk->nVars]; }
static inline Dsd_Obj_t *  Dsd_NtkRoot( Dsd_Ntk_t * pNtk )    { return Dsd_NtkObj( pNtk, Dsd_Lit2Var(pNtk->Root) ); }

#define Dsd_NtkForEachObj( pNtk, pObj, i )                                      \
    for ( i = 0; (i < (pNtk)->nNodes) && ((pObj) = (pNtk)->pNodes[i]); i++ )
#define Dsd_ObjForEachFanin( pNtk, pObj, iLit, i )                              \
    for ( i = 0; (i < (pObj)->nFans) && ((iLit) = (pObj)->pFans[i], 1); i++ )

extern unsigned *  Kit_DsdTruthCompute( Dsd_Man_t * p, Dsd_Ntk_t * pNtk );
extern void        Kit_DsdPrint( FILE * pFile, Dsd_Ntk_t * pNtk );
extern Dsd_Ntk_t * Kit_DsdDecompose( unsigned * pTruth, int nVars );
extern void        Kit_DsdNtkFree( Dsd_Ntk_t * pNtk );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the DSD manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dsd_Man_t * Dsd_ManAlloc( int nVars )
{
    Dsd_Man_t * p;
    p = ALLOC( Dsd_Man_t, 1 );
    memset( p, 0, sizeof(Dsd_Man_t) );
    p->nVars = nVars;
    p->nWords = Kit_TruthWordNum( p->nVars );
    p->vTtElems = Vec_PtrAllocTruthTables( p->nVars );
    p->vTtNodes = Vec_PtrAllocSimInfo( 64, p->nWords );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the DSD manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dsd_ManFree( Dsd_Man_t * p )
{
    Vec_PtrFree( p->vTtElems );
    Vec_PtrFree( p->vTtNodes );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Allocates the DSD node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dsd_Obj_t * Dsd_ObjAlloc( Dsd_Ntk_t * pNtk, Kit_Dsd_t Type, int nFans )
{
    Dsd_Obj_t * pObj;
    int nSize = sizeof(Dsd_Obj_t) + sizeof(unsigned) * (Dsd_ObjOffset(nFans) + (Type == KIT_DSD_PRIME) * Kit_TruthWordNum(nFans));
    pObj = (Dsd_Obj_t *)ALLOC( char, nSize );
    memset( pObj, 0, nSize );
    pObj->Id = pNtk->nVars + pNtk->nNodes;
    pObj->Type = Type;
    pObj->nFans = nFans;
    pObj->Offset = Dsd_ObjOffset( nFans );
    // add the object
    assert( pNtk->nNodes < pNtk->nNodesAlloc );
    pNtk->pNodes[pNtk->nNodes++] = pObj;
    return pObj;
}

/**Function*************************************************************

  Synopsis    [Deallocates the DSD node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dsd_ObjFree( Dsd_Ntk_t * p, Dsd_Obj_t * pObj )
{
    free( pObj );
}

/**Function*************************************************************

  Synopsis    [Allocates the DSD network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dsd_Ntk_t * Kit_DsdNtkAlloc( int nVars )
{
    Dsd_Ntk_t * pNtk;
    int nSize = sizeof(Dsd_Ntk_t) + sizeof(void *) * nVars;
    // allocate the network
    pNtk = (Dsd_Ntk_t *)ALLOC( char, nSize );
    memset( pNtk, 0, nSize );
    pNtk->nVars = nVars;
    pNtk->nNodesAlloc = nVars;
    pNtk->pMem = ALLOC( unsigned, 6 * Kit_TruthWordNum(nVars) );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Deallocate the DSD network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdNtkFree( Dsd_Ntk_t * pNtk )
{
    Dsd_Obj_t * pObj;
    unsigned i;
    Dsd_NtkForEachObj( pNtk, pObj, i )
        free( pObj );
    free( pNtk->pMem );
    free( pNtk );
}

/**Function*************************************************************

  Synopsis    [Prints the hex unsigned into a file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdPrintHex( FILE * pFile, unsigned * pTruth, int nFans )
{
    int nDigits, Digit, k;
    nDigits = (1 << nFans) / 4;
    for ( k = nDigits - 1; k >= 0; k-- )
    {
        Digit = ((pTruth[k/8] >> ((k%8) * 4)) & 15);
        if ( Digit < 10 )
            fprintf( pFile, "%d", Digit );
        else
            fprintf( pFile, "%c", 'A' + Digit-10 );
    }
}

/**Function*************************************************************

  Synopsis    [Recursively print the DSD formula.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdPrint_rec( FILE * pFile, Dsd_Ntk_t * pNtk, int Id )
{
    Dsd_Obj_t * pObj;
    unsigned iLit, i;
    char Symbol;

    pObj = Dsd_NtkObj( pNtk, Id );
    if ( pObj == NULL )
    {
        assert( Id < pNtk->nVars );
        fprintf( pFile, "%c", 'a' + Id );
        return;
    }

    if ( pObj->Type == KIT_DSD_CONST1 )
    {
        assert( pObj->nFans == 0 );
        fprintf( pFile, "Const1" );
        return;
    }

    if ( pObj->Type == KIT_DSD_VAR )
        assert( pObj->nFans == 1 );

    if ( pObj->Type == KIT_DSD_AND )
        Symbol = '*';
    else if ( pObj->Type == KIT_DSD_XOR )
        Symbol = '+';
    else 
        Symbol = ',';

    if ( pObj->Type == KIT_DSD_PRIME )
        Kit_DsdPrintHex( stdout, Dsd_ObjTruth(pObj), pObj->nFans );

    fprintf( pFile, "(" );
    Dsd_ObjForEachFanin( pNtk, pObj, iLit, i )
    {
        if ( Dsd_LitIsCompl(iLit) ) 
            fprintf( pFile, "!" );
        Kit_DsdPrint_rec( pFile, pNtk, Dsd_Lit2Var(iLit) );
        if ( i < pObj->nFans - 1 )
            fprintf( pFile, "%c", Symbol );
    }
    fprintf( pFile, ")" );
}

/**Function*************************************************************

  Synopsis    [Print the DSD formula.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdPrint( FILE * pFile, Dsd_Ntk_t * pNtk )
{
    fprintf( pFile, "F = " );
    if ( Dsd_LitIsCompl(pNtk->Root) )
        fprintf( pFile, "!" );
    Kit_DsdPrint_rec( pFile, pNtk, Dsd_Lit2Var(pNtk->Root) );
    fprintf( pFile, "\n" );
}

/**Function*************************************************************

  Synopsis    [Derives the truth table of the DSD node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Kit_DsdTruthComputeNode_rec( Dsd_Man_t * p, Dsd_Ntk_t * pNtk, int Id )
{
    Dsd_Obj_t * pObj;
    unsigned * pTruthRes, * pTruthPrime, * pTruthMint, * pTruthFans[16];
    unsigned i, m, iLit, nMints, fCompl;

    // get the node with this ID
    pObj = Dsd_NtkObj( pNtk, Id );
    pTruthRes = Vec_PtrEntry( p->vTtNodes, Id );

    // special case: literal of an internal node
    if ( pObj == NULL )
    {
        assert( Id < pNtk->nVars );
        return pTruthRes;
    }

    // constant node
    if ( pObj->Type == KIT_DSD_CONST1 )
    {
        assert( pObj->nFans == 0 );
        Kit_TruthFill( pTruthRes, pNtk->nVars );
        return pTruthRes;
    }

    // elementary variable node
    if ( pObj->Type == KIT_DSD_VAR )
    {
        assert( pObj->nFans == 1 );
        iLit = pObj->pFans[0];
        pTruthFans[0] = Kit_DsdTruthComputeNode_rec( p, pNtk, Dsd_Lit2Var(iLit) );
        if ( Dsd_LitIsCompl(iLit) )
            Kit_TruthNot( pTruthRes, pTruthFans[0], pNtk->nVars );
        else
            Kit_TruthCopy( pTruthRes, pTruthFans[0], pNtk->nVars );
        return pTruthRes;
    }

    // collect the truth tables of the fanins
    Dsd_ObjForEachFanin( pNtk, pObj, iLit, i )
        pTruthFans[i] = Kit_DsdTruthComputeNode_rec( p, pNtk, Dsd_Lit2Var(iLit) );
    // create the truth table

    // simple gates
    if ( pObj->Type == KIT_DSD_AND )
    {
        Kit_TruthFill( pTruthRes, pNtk->nVars );
        Dsd_ObjForEachFanin( pNtk, pObj, iLit, i )
            Kit_TruthAndPhase( pTruthRes, pTruthRes, pTruthFans[i], pNtk->nVars, 0, Dsd_LitIsCompl(iLit) );
        return pTruthRes;
    }
    if ( pObj->Type == KIT_DSD_XOR )
    {
        Kit_TruthClear( pTruthRes, pNtk->nVars );
        fCompl = 0;
        Dsd_ObjForEachFanin( pNtk, pObj, iLit, i )
        {
            Kit_TruthXor( pTruthRes, pTruthRes, pTruthFans[i], pNtk->nVars );
            fCompl ^= Dsd_LitIsCompl(iLit);
        }
        if ( fCompl )
            Kit_TruthNot( pTruthRes, pTruthRes, pNtk->nVars );
        return pTruthRes;
    }
    assert( pObj->Type == KIT_DSD_PRIME );

    // get the truth table of the prime node
    pTruthPrime = Dsd_ObjTruth( pObj );
    // get storage for the temporary minterm
    pTruthMint = Vec_PtrEntry(p->vTtNodes, pNtk->nVars + pNtk->nNodes);

    // go through the minterms
    nMints = (1 << pObj->nFans);
    Kit_TruthClear( pTruthRes, pNtk->nVars );
    for ( m = 0; m < nMints; m++ )
    {
        if ( !Kit_TruthHasBit(pTruthPrime, m) )
            continue;
        Kit_TruthFill( pTruthMint, pNtk->nVars );
        Dsd_ObjForEachFanin( pNtk, pObj, iLit, i )
            Kit_TruthAndPhase( pTruthMint, pTruthMint, pTruthFans[i], pNtk->nVars, 0, Dsd_LitIsCompl(iLit) );
        Kit_TruthOr( pTruthRes, pTruthRes, pTruthMint, pNtk->nVars );
    }
    return pTruthRes;
}

/**Function*************************************************************

  Synopsis    [Derives the truth table of the DSD network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Kit_DsdTruthCompute( Dsd_Man_t * p, Dsd_Ntk_t * pNtk )
{
    unsigned * pTruthRes;
    int i;
    // assign elementary truth ables
    assert( pNtk->nVars <= p->nVars );
    for ( i = 0; i < (int)pNtk->nVars; i++ )
        Kit_TruthCopy( Vec_PtrEntry(p->vTtNodes, i), Vec_PtrEntry(p->vTtElems, i), p->nVars );
    // compute truth table for each node
    pTruthRes = Kit_DsdTruthComputeNode_rec( p, pNtk, Dsd_Lit2Var(pNtk->Root) );
    // complement the truth table if needed
    if ( Dsd_LitIsCompl(pNtk->Root) )
        Kit_TruthNot( pTruthRes, pTruthRes, pNtk->nVars );
    return pTruthRes;
}

/**Function*************************************************************

  Synopsis    [Expands the node.]

  Description [Returns the new literal.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdExpandCollectAnd_rec( Dsd_Ntk_t * p, int iLit, int * piLitsNew, int * nLitsNew )
{
    Dsd_Obj_t * pObj;
    unsigned i, iLitFanin;
    // check the end of the supergate
    pObj = Dsd_NtkObj( p, Dsd_Lit2Var(iLit) );
    if ( Dsd_LitIsCompl(iLit) || Dsd_Lit2Var(iLit) < p->nVars || pObj->Type != KIT_DSD_AND )
    {
        piLitsNew[(*nLitsNew)++] = iLit;
        return;
    }
    // iterate through the fanins
    Dsd_ObjForEachFanin( p, pObj, iLitFanin, i )
        Kit_DsdExpandCollectAnd_rec( p, iLitFanin, piLitsNew, nLitsNew );
}

/**Function*************************************************************

  Synopsis    [Expands the node.]

  Description [Returns the new literal.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdExpandCollectXor_rec( Dsd_Ntk_t * p, int iLit, int * piLitsNew, int * nLitsNew )
{
    Dsd_Obj_t * pObj;
    unsigned i, iLitFanin;
    // check the end of the supergate
    pObj = Dsd_NtkObj( p, Dsd_Lit2Var(iLit) );
    if ( Dsd_Lit2Var(iLit) < p->nVars || pObj->Type != KIT_DSD_XOR )
    {
        piLitsNew[(*nLitsNew)++] = iLit;
        return;
    }
    // iterate through the fanins
    pObj = Dsd_NtkObj( p, Dsd_Lit2Var(iLit) );
    Dsd_ObjForEachFanin( p, pObj, iLitFanin, i )
        Kit_DsdExpandCollectXor_rec( p, iLitFanin, piLitsNew, nLitsNew );
    // if the literal was complemented, pass the complemented attribute somewhere
    if ( Dsd_LitIsCompl(iLit) )
        piLitsNew[0] = Dsd_LitNot( piLitsNew[0] );
}

/**Function*************************************************************

  Synopsis    [Expands the node.]

  Description [Returns the new literal.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Kit_DsdExpandNode_rec( Dsd_Ntk_t * pNew, Dsd_Ntk_t * p, int iLit )
{
    unsigned * pTruth, * pTruthNew;
    unsigned i, fCompl, iLitFanin, piLitsNew[16], nLitsNew = 0;
    Dsd_Obj_t * pObj, * pObjNew;

    // remember the complement
    fCompl = Dsd_LitIsCompl(iLit); 
    iLit = Dsd_LitRegular(iLit); 
    assert( !Dsd_LitIsCompl(iLit) );

    // consider the case of simple gate
    pObj = Dsd_NtkObj( p, Dsd_Lit2Var(iLit) );
    if ( pObj->Type == KIT_DSD_AND )
    {
        Kit_DsdExpandCollectAnd_rec( p, iLit, piLitsNew, &nLitsNew );
        pObjNew = Dsd_ObjAlloc( pNew, KIT_DSD_AND, nLitsNew );
        for ( i = 0; i < pObjNew->nFans; i++ )
            pObjNew->pFans[i] = Kit_DsdExpandNode_rec( pNew, p, piLitsNew[i] );
        return Dsd_Var2Lit( pObjNew->Id, fCompl );
    }
    if ( pObj->Type == KIT_DSD_XOR )
    {
        Kit_DsdExpandCollectXor_rec( p, iLit, piLitsNew, &nLitsNew );
        pObjNew = Dsd_ObjAlloc( pNew, KIT_DSD_XOR, nLitsNew );
        for ( i = 0; i < pObjNew->nFans; i++ )
        {
            pObjNew->pFans[i] = Kit_DsdExpandNode_rec( pNew, p, Dsd_LitRegular(piLitsNew[i]) );
            fCompl ^= Dsd_LitIsCompl(piLitsNew[i]);
        }
        return Dsd_Var2Lit( pObjNew->Id, fCompl );
    }
    assert( pObj->Type == KIT_DSD_PRIME );

    // create new PRIME node
    pObjNew = Dsd_ObjAlloc( pNew, KIT_DSD_PRIME, pObj->nFans );
    // copy the truth table
    pTruth = Dsd_ObjTruth( pObj );
    pTruthNew = Dsd_ObjTruth( pObjNew );
    Kit_TruthCopy( pTruthNew, pTruth, pObj->nFans );
    // create fanins
    Dsd_ObjForEachFanin( pNtk, pObj, iLitFanin, i )
    {
        pObjNew->pFans[i] = Kit_DsdExpandNode_rec( pNew, p, iLitFanin );
        // complement the corresponding inputs of the truth table
        if ( Dsd_LitIsCompl(pObjNew->pFans[i]) )
        {
            pObjNew->pFans[i] = Dsd_LitRegular(pObjNew->pFans[i]);
            Kit_TruthChangePhase( pTruthNew, pObjNew->nFans, i );
        }
    }
    // if the incoming phase is complemented, absorb it into the prime node
    if ( fCompl )
        Kit_TruthNot( pTruthNew, pTruthNew, pObj->nFans );
    return Dsd_Var2Lit( pObjNew->Id, 0 );
}

/**Function*************************************************************

  Synopsis    [Expands the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dsd_Ntk_t * Kit_DsdExpand( Dsd_Ntk_t * p )
{
    Dsd_Ntk_t * pNew;
    Dsd_Obj_t * pObjNew;
    assert( p->nVars <= 16 );
    // create a new network
    pNew = Kit_DsdNtkAlloc( p->nVars );
    // consider simple special cases
    if ( Dsd_NtkRoot(p)->Type == KIT_DSD_CONST1 )
    {
        pObjNew = Dsd_ObjAlloc( pNew, KIT_DSD_CONST1, 0 );
        pNew->Root = Dsd_Var2Lit( pObjNew->Id, Dsd_LitIsCompl(p->Root) );
        return pNew;
    }
    if ( Dsd_NtkRoot(p)->Type == KIT_DSD_VAR )
    {
        pObjNew = Dsd_ObjAlloc( pNew, KIT_DSD_VAR, 1 );
        pObjNew->pFans[0] = Dsd_NtkRoot(p)->pFans[0];
        pNew->Root = Dsd_Var2Lit( pObjNew->Id, Dsd_LitIsCompl(p->Root) );
        return pNew;
    }
    // convert the root node
    pNew->Root = Kit_DsdExpandNode_rec( pNew, p, p->Root );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if there is a component with more than 3 inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Kit_DsdFindLargeBox( Dsd_Ntk_t * pNtk, int Id )
{
    Dsd_Obj_t * pObj;
    unsigned iLit, i, RetValue;
    pObj = Dsd_NtkObj( pNtk, Id );
    if ( pObj->nFans > 3 )
        return 1;
    RetValue = 0;
    Dsd_ObjForEachFanin( pNtk, pObj, iLit, i )
        RetValue |= Kit_DsdFindLargeBox( pNtk, Dsd_Lit2Var(iLit) );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Performs decomposition of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdDecompose_rec( Dsd_Ntk_t * pNtk, Dsd_Obj_t * pObj, unsigned uSupp, unsigned char * pPar )
{
    Dsd_Obj_t * pRes, * pRes0, * pRes1;
    int nWords = Kit_TruthWordNum(pObj->nFans);
    unsigned * pTruth = Dsd_ObjTruth(pObj);
    unsigned * pCofs2[2] = { pNtk->pMem, pNtk->pMem + nWords };
    unsigned * pCofs4[2][2] = { {pNtk->pMem + 2 * nWords, pNtk->pMem + 3 * nWords}, {pNtk->pMem + 4 * nWords, pNtk->pMem + 5 * nWords} };
    int i, iLit0, iLit1, nFans0, nFans1, nPairs;
    int fEquals[2][2], fOppos, fPairs[4][4];
    unsigned j, k, nFansNew, uSupp0, uSupp1;

    assert( pObj->nFans > 0 );
    assert( pObj->Type == KIT_DSD_PRIME );
    assert( uSupp == (uSupp0 = (unsigned)Kit_TruthSupport(pTruth, pObj->nFans)) );

    // compress the truth table
    if ( uSupp != Kit_BitMask(pObj->nFans) )
    {
        nFansNew = Kit_WordCountOnes(uSupp);
        Kit_TruthShrink( pNtk->pMem, pTruth, nFansNew, pObj->nFans, uSupp, 1 );
        for ( j = k = 0; j < pObj->nFans; j++ )
            if ( uSupp & (1 << j) )
                pObj->pFans[k++] = pObj->pFans[j];
        assert( k == nFansNew );
        pObj->nFans = k;
        uSupp = Kit_BitMask(pObj->nFans);
    }

    // consider the single variable case
    if ( pObj->nFans == 1 )
    {
        pObj->Type = KIT_DSD_NONE;
        if ( pTruth[0] == 0x55555555 )
            pObj->pFans[0] = Dsd_LitNot(pObj->pFans[0]);
        else
            assert( pTruth[0] == 0xAAAAAAAA );
        // update the parent pointer
//        assert( !Dsd_LitIsCompl(*pPar) );
        *pPar = Dsd_LitNotCond( pObj->pFans[0], Dsd_LitIsCompl(*pPar) );
        return;
    }

    // decompose the output
    if ( !pObj->fMark )
    for ( i = pObj->nFans - 1; i >= 0; i-- )
    {
        // get the two-variable cofactors
        Kit_TruthCofactor0New( pCofs2[0], pTruth, pObj->nFans, i );
        Kit_TruthCofactor1New( pCofs2[1], pTruth, pObj->nFans, i );
//        assert( !Kit_TruthVarInSupport( pCofs2[0], pObj->nFans, i) );
//        assert( !Kit_TruthVarInSupport( pCofs2[1], pObj->nFans, i) );
        // get the constant cofs
        fEquals[0][0] = Kit_TruthIsConst0( pCofs2[0], pObj->nFans );
        fEquals[0][1] = Kit_TruthIsConst0( pCofs2[1], pObj->nFans );
        fEquals[1][0] = Kit_TruthIsConst1( pCofs2[0], pObj->nFans );
        fEquals[1][1] = Kit_TruthIsConst1( pCofs2[1], pObj->nFans );
        fOppos        = Kit_TruthIsOpposite( pCofs2[0], pCofs2[1], pObj->nFans );
        assert( !Kit_TruthIsEqual(pCofs2[0], pCofs2[1], pObj->nFans) );
        if ( fEquals[0][0] + fEquals[0][1] + fEquals[1][0] + fEquals[1][1] + fOppos == 0 )
        {
            // check the MUX decomposition
            uSupp0 = Kit_TruthSupport( pCofs2[0], pObj->nFans );
            uSupp1 = Kit_TruthSupport( pCofs2[1], pObj->nFans );
            assert( uSupp == (uSupp0 | uSupp1 | (1<<i)) );
            if ( uSupp0 & uSupp1 )
                continue;
            // perform MUX decomposition
            pRes0 = Dsd_ObjAlloc( pNtk, KIT_DSD_PRIME, pObj->nFans );
            pRes1 = Dsd_ObjAlloc( pNtk, KIT_DSD_PRIME, pObj->nFans );
            for ( k = 0; k < pObj->nFans; k++ )
            {
                pRes0->pFans[k] = (uSupp0 & (1 << k))? pObj->pFans[k] : 127;
                pRes1->pFans[k] = (uSupp1 & (1 << k))? pObj->pFans[k] : 127;
            }
            Kit_TruthCopy( Dsd_ObjTruth(pRes0), pCofs2[0], pObj->nFans );        
            Kit_TruthCopy( Dsd_ObjTruth(pRes1), pCofs2[1], pObj->nFans ); 
            // update the current one
            assert( pObj->Type == KIT_DSD_PRIME );
            pTruth[0] = 0xCACACACA;
            pObj->nFans = 3;
            pObj->pFans[0] = 2*pRes0->Id; pRes0->nRefs++;
            pObj->pFans[1] = 2*pRes1->Id; pRes1->nRefs++;
            pObj->pFans[2] = pObj->pFans[i];
            // call recursively
            Kit_DsdDecompose_rec( pNtk, pRes0, uSupp0, pObj->pFans + 0 );
            Kit_DsdDecompose_rec( pNtk, pRes1, uSupp1, pObj->pFans + 1 );
            return;
        }
//Extra_PrintBinary( stdout, pTruth, 1 << pObj->nFans ); printf( "\n" );

        // create the new node
        pRes = Dsd_ObjAlloc( pNtk, KIT_DSD_AND, 2 );
        pRes->nRefs++;
        pRes->nFans = 2;
        pRes->pFans[0] = pObj->pFans[i];  pObj->pFans[i] = 127;  uSupp &= ~(1 << i);
        pRes->pFans[1] = 2*pObj->Id;
        // update the parent pointer
        *pPar = 2 * pRes->Id;
        // consider different decompositions
        if ( fEquals[0][0] )
        {
            Kit_TruthCopy( pTruth, pCofs2[1], pObj->nFans );
        }
        else if ( fEquals[0][1] )
        {
            pRes->pFans[0] = Dsd_LitNot(pRes->pFans[0]);
            Kit_TruthCopy( pTruth, pCofs2[0], pObj->nFans );
        }
        else if ( fEquals[1][0] )
        {
            *pPar = Dsd_LitNot(*pPar);
            pRes->pFans[1] = Dsd_LitNot(pRes->pFans[1]);
            Kit_TruthCopy( pTruth, pCofs2[1], pObj->nFans );
        }
        else if ( fEquals[1][1] )
        {
            *pPar = Dsd_LitNot(*pPar);
            pRes->pFans[0] = Dsd_LitNot(pRes->pFans[0]);  
            pRes->pFans[1] = Dsd_LitNot(pRes->pFans[1]);
            Kit_TruthCopy( pTruth, pCofs2[0], pObj->nFans );
        }
        else if ( fOppos )
        {
            pRes->Type = KIT_DSD_XOR;
            Kit_TruthCopy( pTruth, pCofs2[0], pObj->nFans );
        }
        else
            assert( 0 );
        // decompose the remainder
        assert( Dsd_ObjTruth(pObj) == pTruth );
        Kit_DsdDecompose_rec( pNtk, pObj, uSupp, pRes->pFans + 1 );
        return;
    }
    pObj->fMark = 1;

    // decompose the input
    for ( i = pObj->nFans - 1; i >= 0; i-- )
    {
        assert( Kit_TruthVarInSupport( pTruth, pObj->nFans, i ) );
        // get the single variale cofactors
        Kit_TruthCofactor0New( pCofs2[0], pTruth, pObj->nFans, i );
        Kit_TruthCofactor1New( pCofs2[1], pTruth, pObj->nFans, i );
        // check the existence of MUX decomposition
        uSupp0 = Kit_TruthSupport( pCofs2[0], pObj->nFans );
        uSupp1 = Kit_TruthSupport( pCofs2[1], pObj->nFans );
        assert( uSupp == (uSupp0 | uSupp1 | (1<<i)) );
        // if one of the cofs is a constant, it is time to check the output again
        if ( uSupp0 == 0 || uSupp1 == 0 )
        {
            pObj->fMark = 0;
            Kit_DsdDecompose_rec( pNtk, pObj, uSupp, pPar );
            return;
        }
        assert( uSupp0 && uSupp1 );
        // get the number of unique variables
        nFans0 = Kit_WordCountOnes( uSupp0 & ~uSupp1 );
        nFans1 = Kit_WordCountOnes( uSupp1 & ~uSupp0 );
        if ( nFans0 == 1 && nFans1 == 1 )
        {
            // get the cofactors w.r.t. the unique variables
            iLit0 = Kit_WordFindFirstBit( uSupp0 & ~uSupp1 );
            iLit1 = Kit_WordFindFirstBit( uSupp1 & ~uSupp0 );
            // get four cofactors                                        
            Kit_TruthCofactor0New( pCofs4[0][0], pCofs2[0], pObj->nFans, iLit0 );
            Kit_TruthCofactor1New( pCofs4[0][1], pCofs2[0], pObj->nFans, iLit0 );
            Kit_TruthCofactor0New( pCofs4[1][0], pCofs2[1], pObj->nFans, iLit1 );
            Kit_TruthCofactor1New( pCofs4[1][1], pCofs2[1], pObj->nFans, iLit1 );
            // check existence conditions
            fEquals[0][0] = Kit_TruthIsEqual( pCofs4[0][0], pCofs4[1][0], pObj->nFans );
            fEquals[0][1] = Kit_TruthIsEqual( pCofs4[0][1], pCofs4[1][1], pObj->nFans );
            fEquals[1][0] = Kit_TruthIsEqual( pCofs4[0][0], pCofs4[1][1], pObj->nFans );
            fEquals[1][1] = Kit_TruthIsEqual( pCofs4[0][1], pCofs4[1][0], pObj->nFans );
            if ( (fEquals[0][0] && fEquals[0][1]) || (fEquals[1][0] && fEquals[1][1]) )
            {
                // construct the MUX
                pRes = Dsd_ObjAlloc( pNtk, KIT_DSD_PRIME, 3 );
                Dsd_ObjTruth(pRes)[0] = 0xCACACACA;
                pRes->nRefs++;
                pRes->nFans = 3;
                pRes->pFans[0] = pObj->pFans[iLit0]; pObj->pFans[iLit0] = 127;  uSupp &= ~(1 << iLit0);
                pRes->pFans[1] = pObj->pFans[iLit1]; pObj->pFans[iLit1] = 127;  uSupp &= ~(1 << iLit1);
                pRes->pFans[2] = pObj->pFans[i];     pObj->pFans[i] = 2 * pRes->Id; // remains in support
                // update the node
                if ( fEquals[0][0] && fEquals[0][1] )
                    Kit_TruthMux( pTruth, pCofs4[0][0], pCofs4[0][1], pObj->nFans, i );
                else
                    Kit_TruthMux( pTruth, pCofs4[0][1], pCofs4[0][0], pObj->nFans, i );
                // decompose the remainder
                Kit_DsdDecompose_rec( pNtk, pObj, uSupp, pPar );
                return;
            }
        }

        // try other inputs
        for ( k = i+1; k < pObj->nFans; k++ )
        {
            // get four cofactors                                                ik
            Kit_TruthCofactor0New( pCofs4[0][0], pCofs2[0], pObj->nFans, k ); // 00 
            Kit_TruthCofactor1New( pCofs4[0][1], pCofs2[0], pObj->nFans, k ); // 01 
            Kit_TruthCofactor0New( pCofs4[1][0], pCofs2[1], pObj->nFans, k ); // 10 
            Kit_TruthCofactor1New( pCofs4[1][1], pCofs2[1], pObj->nFans, k ); // 11 
            // compare equal pairs
            fPairs[0][1] = fPairs[1][0] = Kit_TruthIsEqual( pCofs4[0][0], pCofs4[0][1], pObj->nFans );
            fPairs[0][2] = fPairs[2][0] = Kit_TruthIsEqual( pCofs4[0][0], pCofs4[1][0], pObj->nFans );
            fPairs[0][3] = fPairs[3][0] = Kit_TruthIsEqual( pCofs4[0][0], pCofs4[1][1], pObj->nFans );
            fPairs[1][2] = fPairs[2][1] = Kit_TruthIsEqual( pCofs4[0][1], pCofs4[1][0], pObj->nFans );
            fPairs[1][3] = fPairs[3][1] = Kit_TruthIsEqual( pCofs4[0][1], pCofs4[1][1], pObj->nFans );
            fPairs[2][3] = fPairs[3][2] = Kit_TruthIsEqual( pCofs4[1][0], pCofs4[1][1], pObj->nFans );
            nPairs = fPairs[0][1] + fPairs[0][2] + fPairs[0][3] + fPairs[1][2] + fPairs[1][3] + fPairs[2][3];
            if ( nPairs != 3 && nPairs != 2 )
                continue;

            // decomposition exists
            pRes = Dsd_ObjAlloc( pNtk, KIT_DSD_AND, 2 );
            pRes->nRefs++;
            pRes->nFans = 2;
            pRes->pFans[0] = pObj->pFans[k]; pObj->pFans[k] = 2 * pRes->Id;  // remains in support
            pRes->pFans[1] = pObj->pFans[i]; pObj->pFans[i] = 127;       uSupp &= ~(1 << i);
            if ( !fPairs[0][1] && !fPairs[0][2] && !fPairs[0][3] ) // 00
            {
                pRes->pFans[0] = Dsd_LitNot(pRes->pFans[0]);  
                pRes->pFans[1] = Dsd_LitNot(pRes->pFans[1]);
                Kit_TruthMux( pTruth, pCofs4[1][1], pCofs4[0][0], pObj->nFans, k );
            }
            else if ( !fPairs[1][0] && !fPairs[1][2] && !fPairs[1][3] ) // 01
            {
                pRes->pFans[0] = Dsd_LitNot(pRes->pFans[0]);  
                Kit_TruthMux( pTruth, pCofs4[0][0], pCofs4[0][1], pObj->nFans, k );
            }
            else if ( !fPairs[2][0] && !fPairs[2][1] && !fPairs[2][3] ) // 10
            {
                pRes->pFans[1] = Dsd_LitNot(pRes->pFans[1]);  
                Kit_TruthMux( pTruth, pCofs4[0][0], pCofs4[1][0], pObj->nFans, k );
            }
            else if ( !fPairs[3][0] && !fPairs[3][1] && !fPairs[3][2] ) // 11
            {
//                unsigned uSupp0 = Kit_TruthSupport(pCofs4[0][0], pObj->nFans);
//                unsigned uSupp1 = Kit_TruthSupport(pCofs4[1][1], pObj->nFans);
//                unsigned uSupp;
//                Extra_PrintBinary( stdout, &uSupp0, pObj->nFans ); printf( "\n" );
//                Extra_PrintBinary( stdout, &uSupp1, pObj->nFans ); printf( "\n" );
                Kit_TruthMux( pTruth, pCofs4[0][0], pCofs4[1][1], pObj->nFans, k );
//                uSupp = Kit_TruthSupport(pTruth, pObj->nFans);
//                Extra_PrintBinary( stdout, &uSupp, pObj->nFans ); printf( "\n" ); printf( "\n" );
            }
            else
            {
                assert( fPairs[0][3] && fPairs[1][2] );
                pRes->Type = KIT_DSD_XOR;;
                Kit_TruthMux( pTruth, pCofs4[0][0], pCofs4[0][1], pObj->nFans, k );
            }
            // decompose the remainder
            Kit_DsdDecompose_rec( pNtk, pObj, uSupp, pPar );
            return;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Performs decomposition of the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dsd_Ntk_t * Kit_DsdDecompose( unsigned * pTruth, int nVars )
{
    Dsd_Ntk_t * pNtk;
    Dsd_Obj_t * pObj;
    unsigned uSupp;
    int i, nVarsReal;
    assert( nVars <= 16 );
    pNtk = Kit_DsdNtkAlloc( nVars );
    pNtk->Root = Dsd_Var2Lit( pNtk->nVars, 0 );
    // create the first node
    pObj = Dsd_ObjAlloc( pNtk, KIT_DSD_PRIME, nVars );
    assert( pNtk->pNodes[0] == pObj );
    for ( i = 0; i < nVars; i++ )
       pObj->pFans[i] = Dsd_Var2Lit( i, 0 );
    Kit_TruthCopy( Dsd_ObjTruth(pObj), pTruth, nVars );
    uSupp = Kit_TruthSupport( pTruth, nVars );
    // consider special cases
    nVarsReal = Kit_WordCountOnes( uSupp );
    if ( nVarsReal == 0 )
    {
        pObj->Type = KIT_DSD_CONST1;
        pObj->nFans = 0;
        if ( pTruth[0] == 0 )
             pNtk->Root = Dsd_LitNot(pNtk->Root);
        return pNtk;
    }
    if ( nVarsReal == 1 )
    {
        pObj->Type = KIT_DSD_VAR;
        pObj->nFans = 1;
        pObj->pFans[0] = Dsd_Var2Lit( Kit_WordFindFirstBit(uSupp), (pTruth[0] & 1) );
        return pNtk;
    }
    Kit_DsdDecompose_rec( pNtk, pNtk->pNodes[0], uSupp, &pNtk->Root );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Performs decomposition of the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdTestCofs( Dsd_Ntk_t * pNtk, unsigned * pTruthInit )
{
    Dsd_Ntk_t * pNtk0, * pNtk1;
//    Dsd_Obj_t * pRoot;
    unsigned * pCofs2[2] = { pNtk->pMem, pNtk->pMem + Kit_TruthWordNum(pNtk->nVars) };
    unsigned i, * pTruth;
    int fVerbose = 1;

    pTruth = pTruthInit;
//    pRoot = Dsd_NtkRoot(pNtk);
//    pTruth = Dsd_ObjTruth(pRoot);
//    assert( pRoot->nFans == pNtk->nVars );

    if ( fVerbose )
    {
        printf( "Function: " );
//        Extra_PrintBinary( stdout, pTruth, (1 << pNtk->nVars) ); 
        Extra_PrintHexadecimal( stdout, pTruth, pNtk->nVars ); 
        printf( "\n" );
        Kit_DsdPrint( stdout, pNtk );
    }
    for ( i = 0; i < pNtk->nVars; i++ )
    {
        Kit_TruthCofactor0New( pCofs2[0], pTruth, pNtk->nVars, i );
        pNtk0 = Kit_DsdDecompose( pCofs2[0], pNtk->nVars );
        if ( fVerbose )
        {
            printf( "Cof%d0: ", i );
            Kit_DsdPrint( stdout, pNtk0 );
        }
        Kit_DsdNtkFree( pNtk0 );

        Kit_TruthCofactor1New( pCofs2[1], pTruth, pNtk->nVars, i );
        pNtk1 = Kit_DsdDecompose( pCofs2[1], pNtk->nVars );
        if ( fVerbose )
        {
            printf( "Cof%d1: ", i );
            Kit_DsdPrint( stdout, pNtk1 );
        }
        Kit_DsdNtkFree( pNtk0 );
    }
    if ( fVerbose )
        printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Performs decomposition of the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdTest( unsigned * pTruth, int nVars )
{
    Dsd_Ntk_t * pNtk;
    pNtk = Kit_DsdDecompose( pTruth, nVars );

//    if ( Kit_DsdFindLargeBox(pNtk, Dsd_Lit2Var(pNtk->Root)) )
//        Kit_DsdPrint( stdout, pNtk );

//    if ( Dsd_NtkRoot(pNtk)->nFans == (unsigned)nVars && nVars == 6 )

    Kit_DsdTestCofs( pNtk, pTruth );

    Kit_DsdNtkFree( pNtk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


