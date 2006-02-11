/**CFile****************************************************************

  FileName    [rwrTruth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrTruth.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

/*  The code in this file was written with portability to 64-bits in mind.
    The type "unsigned" is assumed to be 32-bit on any platform.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ABCTMAX      8       // the max number of vars

typedef struct Aig_Truth_t_ Aig_Truth_t;
struct Aig_Truth_t_
{
    short        nVars;                   // the number of variables
    short        nWords;                  // the number of 32-bit words
    unsigned     Truth[1<<(ABCTMAX-5)];   // the truth table
    unsigned     Cofs[2][1<<(ABCTMAX-6)]; // the truth table of cofactors
    unsigned     Data[4][1<<(ABCTMAX-7)]; // the truth table of cofactors
    short        Counts[ABCTMAX][2];      // the minterm counters
    Aig_Node_t * pLeaves[ABCTMAX];        // the pointers to leaves
    Aig_Man_t *  pMan;                    // the AIG manager
};

static void Aig_TruthCount( Aig_Truth_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the function given the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Truth_t * Aig_TruthCreate( int nVars, unsigned * pTruth, Aig_Node_t ** pLeaves )
{
    Aig_Truth_t * p;
    int i;
    p = ALLOC( Aig_Truth_t, 1 );
    memset( p, 0, sizeof(Aig_Truth_t) );
    p->nVars  = nVars;
    p->nWords = (nVars < 5)? 1 : (1 << (nVars-5));
    for ( i = 0; i < p->nWords; i++ )
        p->Truth[i] = pTruth[i];
    if ( nVars < 5 )
        p->Truth[0] &= (~0u >> (32-(1<<nVars)));
    for ( i = 0; i < p->nVars; i++ )
        p->pLeaves[i] = pLeaves[i];
    Aig_TruthCount( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Counts the number of miterms in the cofactors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Aig_WordCountOnes( unsigned val )
{
    val = (val & 0x55555555) + ((val>>1) & 0x55555555);
    val = (val & 0x33333333) + ((val>>2) & 0x33333333);
    val = (val & 0x0F0F0F0F) + ((val>>4) & 0x0F0F0F0F);
    val = (val & 0x00FF00FF) + ((val>>8) & 0x00FF00FF);
    return (val & 0x0000FFFF) + (val>>8);
}

/**Function*************************************************************

  Synopsis    [Counts the number of miterms in the cofactors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TruthCount( Aig_Truth_t * p )
{
    static unsigned Masks[5][2] = {
        { 0x33333333, 0xAAAAAAAA },
        { 0x55555555, 0xCCCCCCCC },
        { 0x0F0F0F0F, 0xF0F0F0F0 },
        { 0x00FF00FF, 0xFF00FF00 },
        { 0x0000FFFF, 0xFFFF0000 }
    };

    int i, k;
    assert( p->Counts[0][0] == 0 && p->Counts[0][1] == 0 );
    for ( i = 0; i < p->nVars; i++ )
    {
        p->Counts[i][0] = p->Counts[i][1] = 0;
        if ( i < 5 )
        {
            for ( k = 0; k < p->nWords; k++ )
            {
                p->Counts[i][0] += Aig_WordCountOnes( p->Truth[k] & Masks[i][0] );
                p->Counts[i][1] += Aig_WordCountOnes( p->Truth[k] & Masks[i][1] );
            }
        }
        else
        {
            for ( k = 0; k < p->nWords; k++ )
                if ( i & (1 << (k-5)) )
                    p->Counts[i][1] += Aig_WordCountOnes( p->Truth[k] );
                else
                    p->Counts[i][0] += Aig_WordCountOnes( p->Truth[k] );
        }
    }
/*
    // normalize the variables
    for ( i = 0; i < p->nVars; i++ )
        if ( p->Counts[i][0] > p->Counts[i][1] )
        {
            k = p->Counts[i][0];
            p->Counts[i][0] = p->Counts[i][1];
            p->Counts[i][1] = k;
            p->pLeaves[i] = Aig_Not( p->pLeaves[i] );
        }
*/
}

/**Function*************************************************************

  Synopsis    [Extracts one part of the bitstring.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Aig_WordGetPart( unsigned * p, int Start, int Size )
{
    return (p[Start/5] >> (Start%32)) & (~0u >> (32-Size));
}

/**Function*************************************************************

  Synopsis    [Inserts one part of the bitstring.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Aig_WordSetPart( unsigned * p, int Start, unsigned Part )
{
    p[Start/5] |= (Part << (Start%32));
}

/**Function*************************************************************

  Synopsis    [Computes the cofactor with respect to one variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TruthCofactor( int Var, int Pol, int nVars, unsigned * pTruth, unsigned * pResult )
{
    if ( Var < 5 )
    {
        int nPartSize = ( 1 << Var );
        int nParts    = ( 1 << (nVars-Var-1) );
        unsigned uPart;
        int i;
        for ( i = 0; i < nParts; i++ )
        {
            uPart = Aig_WordGetPart( pTruth, (2*i+Pol)*nPartSize, nPartSize );
            Aig_WordSetPart( pResult, i*nPartSize, uPart ); 
        }
        if ( nVars <= 5 )
            pResult[0] &= (~0u >> (32-(1<<(nVars-1))));
    }
    else
    {
        int nWords = (1 << (nVars-5));
        int i, k = 0;
        for ( i = 0; i < nWords; i++ )
            if ( (i & (1 << (Var-5))) == Pol )
                pResult[k++] = pTruth[i];
        assert( k == nWords/2 );
    }
}




/**Function*************************************************************

  Synopsis    [Computes the BDD of the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Aig_TruthToBdd_rec( DdManager * dd, unsigned * pTruth, int Shift, int nVars, int iVar )
{
    DdNode * bCof0, * bCof1, * bRes;
    if ( nVars == 1 )
        return Cudd_NotCond( Cudd_ReadOne(dd), !Aig_WordGetPart(pTruth, Shift, 1) );
    if ( nVars == 3 )
    {
        unsigned char * pChar = ((char *)pTruth) + Shift/8;
        assert( Shift % 8 == 0 );
        if ( *pChar == 0 )
            return Cudd_ReadLogicZero(dd);
        if ( *pChar == 0xFF )
            return Cudd_ReadOne(dd);
    }
    if ( nVars == 5 )
    {
        unsigned * pWord = pTruth + Shift/32;
        assert( Shift % 32 == 0 );
        if ( *pWord == 0 )
            return Cudd_ReadLogicZero(dd);
        if ( *pWord == 0xFFFFFFFF )
            return Cudd_ReadOne(dd);
    }
    bCof0 = Aig_TruthToBdd_rec( dd, pTruth, Shift,                    nVars-1, iVar+1 );  Cudd_Ref( bCof0 );
    bCof1 = Aig_TruthToBdd_rec( dd, pTruth, Shift + (1 << (nVars-1)), nVars-1, iVar+1 );  Cudd_Ref( bCof1 );
    bRes  = Cudd_bddIte( dd, Cudd_bddIthVar(dd, iVar), bCof1, bCof0 );  Cudd_Ref( bRes );
    Cudd_RecursiveDeref( dd, bCof0 );
    Cudd_RecursiveDeref( dd, bCof1 );
    Cudd_Deref( bRes );
    return bRes;
}

/**Function*************************************************************

  Synopsis    [Computes the BDD of the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Aig_TruthToBdd( DdManager * dd, Aig_Truth_t * p )
{
    return Aig_TruthToBdd_rec( dd, p->Truth, 0, p->nVars, 0 );
}




/**Function*************************************************************

  Synopsis    [Compare bistrings.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Aig_WordCompare( unsigned * p0, unsigned * p1, int nWords )
{
    int i;
    for ( i = 0; i < nWords; i++ )
        if ( p0[i] != p1[i] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compare bistrings.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Aig_WordCompareCompl( unsigned * p0, unsigned * p1, int nWords )
{
    int i;
    for ( i = 0; i < nWords; i++ )
        if ( p0[i] != ~p1[i] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes the cofactor with respect to one variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TruthReplaceByCofactor( Aig_Truth_t * p, int iVar, unsigned * pTruth )
{
}


/**Function*************************************************************

  Synopsis    [Computes the cofactor with respect to one variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Aig_TruthDecompose( Aig_Truth_t * p )
{
    Aig_Node_t * pVar;
    int nOnesCof = ( 1 << (p->nVars-1) );
    int nWordsCof = (p->nWords == 1 ? 1 : p->nWords/2);
    int i;

    // check for constant function
    if ( p->nVars == 0 )
        return Aig_NotCond( Aig_ManConst1(p->pMan), (p->Truth[0]&1)==0 );

    // count the number of minterms in the cofactors
    Aig_TruthCount( p );

    // remove redundant variables and EXORs
    for ( i = p->nVars - 1; i >= 0; i-- )
    {
        if ( p->Counts[i][0] == p->Counts[i][1] )
        {
            // compute cofactors
            Aig_TruthCofactor( i, 0, p->nVars, p->Truth, p->Cofs[0] );
            Aig_TruthCofactor( i, 1, p->nVars, p->Truth, p->Cofs[1] );
            if ( Aig_WordCompare( p->Cofs[0], p->Cofs[1], nWordsCof ) )
            { // equal
                // remove redundant variable
                Aig_TruthReplaceByCofactor( p, i, p->Cofs[0] );
                return Aig_TruthDecompose( p );
            }
        }
        // check the case of EXOR
        if ( p->Counts[i][0] == nOnesCof - p->Counts[i][1] )
        {
            // compute cofactors
            Aig_TruthCofactor( i, 0, p->nVars, p->Truth, p->Cofs[0] );
            Aig_TruthCofactor( i, 1, p->nVars, p->Truth, p->Cofs[1] );
            if ( Aig_WordCompareCompl( p->Cofs[0], p->Cofs[1], nWordsCof ) )
            { // equal
                pVar = p->pLeaves[i];
                // remove redundant variable
                Aig_TruthReplaceByCofactor( p, i, p->Cofs[0] );
                // F = x' * F0 + x * F1 = x <+> F0   assuming that F0 == ~F1
                return Aig_Xor( p->pMan, pVar, Aig_TruthDecompose( p ) );
            }
        }
    }

    // process variables with constant cofactors
    for ( i = p->nVars - 1; i >= 0; i-- )
    {
        if ( p->Counts[i][0] != 0        && p->Counts[i][1] != 0 && 
             p->Counts[i][0] != nOnesCof && p->Counts[i][1] != nOnesCof ) 
             continue;
        pVar = p->pLeaves[i];
        if ( p->Counts[i][0] == 0 )
        {
            Aig_TruthCofactor( i, 1, p->nVars, p->Truth, p->Cofs[1] );
            // remove redundant variable
            Aig_TruthReplaceByCofactor( p, i, p->Cofs[1] );
            // F = x' * 0 + x * F1 = x * F1 
            return Aig_And( p->pMan, pVar, Aig_TruthDecompose( p ) );
        }
        if ( p->Counts[i][1] == 0 )
        {
            Aig_TruthCofactor( i, 0, p->nVars, p->Truth, p->Cofs[0] );
            // remove redundant variable
            Aig_TruthReplaceByCofactor( p, i, p->Cofs[0] );
            // F = x' * F0 + x * 0 = x' * F0 
            return Aig_And( p->pMan, Aig_Not(pVar), Aig_TruthDecompose( p ) );
         }
        if ( p->Counts[i][0] == nOnesCof )
        {
            Aig_TruthCofactor( i, 1, p->nVars, p->Truth, p->Cofs[1] );
            // remove redundant variable
            Aig_TruthReplaceByCofactor( p, i, p->Cofs[1] );
            // F = x' * 1 + x * F1 = x' + F1 
            return Aig_Or( p->pMan, Aig_Not(pVar), Aig_TruthDecompose( p ) );
        }
        if ( p->Counts[i][1] == nOnesCof )
        {
            Aig_TruthCofactor( i, 0, p->nVars, p->Truth, p->Cofs[0] );
            // remove redundant variable
            Aig_TruthReplaceByCofactor( p, i, p->Cofs[0] );
            // F = x' * F0 + x * 1 = x + F0 
            return Aig_Or( p->pMan, pVar, Aig_TruthDecompose( p ) );
         }
        assert( 0 );
    }

}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


