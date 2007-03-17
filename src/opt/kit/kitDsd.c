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

typedef struct Dsd_Ntk_t_ Dsd_Ntk_t;
typedef struct Dsd_Obj_t_ Dsd_Obj_t;

// network types
typedef enum { 
    KIT_DSD_NONE  = 0,  // 0: unknown
    KIT_DSD_CONST1,     // 1: constant 1
    KIT_DSD_VAR,        // 2: elementary variable
    KIT_DSD_AND,        // 3: multi-input AND
    KIT_DSD_XOR,        // 4: multi-input XOR
    KIT_DSD_MUX,        // 5: multiplexer
    KIT_DSD_PRIME       // 6: arbitrary function of 3+ variables
} Kit_Dsd_t;

struct Dsd_Obj_t_
{ 
    unsigned       uSupp;              // the support of this node
    unsigned       Id          :  6;   // the number of this node
    unsigned       Type        :  3;   // none, const, var, AND, XOR, MUX, PRIME
    unsigned       fMark       :  1;   // finished checking output
    unsigned       Offset      : 16;   // offset to the truth table
    unsigned       nFans       :  6;   // the number of fanins of this node
    unsigned char  pFans[0];           // the fanin literals
};

struct Dsd_Ntk_t_
{
    unsigned char  nVars;              // at most 16 (perhaps 18?)
    unsigned char  nNodesAlloc;        // the number of allocated nodes (at most nVars)
    unsigned char  nNodes;             // the number of nodes
    unsigned char  Root;               // the root of the tree
    unsigned *     pMem;               // memory for the truth tables (memory manager?)
    Dsd_Obj_t *    pNodes[0];          // the nodes
};

static inline unsigned     Dsd_ObjOffset( int nFans )        { return (nFans >> 2) + ((nFans & 3) > 0); }
static inline unsigned *   Dsd_ObjTruth( Dsd_Obj_t * pObj )  { return pObj->Type == KIT_DSD_PRIME ? (unsigned *)pObj->pFans + pObj->Offset: NULL; }
static inline Dsd_Obj_t *  Dsd_NtkRoot( Dsd_Ntk_t * pNtk )   { return pNtk->pNodes[(pNtk->Root >> 1) - pNtk->nVars]; }

#define Dsd_NtkForEachObj( pNtk, pObj, i )                                       \
    for ( i = 0; (i < (pNtk)->nNodes) && ((pObj) = (pNtk)->pNodes[i]); i++ )
#define Dsd_ObjForEachFanin( pNtk, pObj, pFanin, iVar, i )                       \
    for ( i = 0; (i < (pObj)->nFans) && (((pFanin) = ((pObj)->pFans[i] < 2*pNtk->nVars)? NULL: (pNtk)->pNodes[((pObj)->pFans[i]>>1) - pNtk->nVars]), 1) && ((iVar) = (pObj)->pFans[i], 1); i++ )

extern void        Kit_DsdPrint( FILE * pFile, Dsd_Ntk_t * pNtk );
extern Dsd_Ntk_t * Kit_DsdDecompose( unsigned * pTruth, int nVars );
extern void        Kit_DsdNtkFree( Dsd_Ntk_t * pNtk );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

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
    pObj->Type = Type;
    pObj->Id = pNtk->nVars + pNtk->nNodes;
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
Dsd_Ntk_t * Kit_DsdNtkAlloc( unsigned * pTruth, int nVars )
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
void Kit_DsdPrint_rec( FILE * pFile, Dsd_Ntk_t * pNtk, Dsd_Obj_t * pObj )
{
    Dsd_Obj_t * pFanin;
    unsigned iVar, i;
    char Symbol;

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

    if ( pObj->Type == KIT_DSD_MUX )
        fprintf( pFile, "CA" );
    else if ( pObj->Type == KIT_DSD_PRIME )
        Kit_DsdPrintHex( stdout, Dsd_ObjTruth(pObj), pObj->nFans );

    fprintf( pFile, "(" );
    Dsd_ObjForEachFanin( pNtk, pObj, pFanin, iVar, i )
    {
        if ( iVar & 1 ) 
            fprintf( pFile, "!" );
        if ( pFanin )
            Kit_DsdPrint_rec( pFile, pNtk, pFanin );
        else
            fprintf( pFile, "%c", 'a' + (pNtk->nVars - 1 - (iVar >> 1)) );
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
    if ( pNtk->Root & 1 )
        fprintf( pFile, "!" );
    Kit_DsdPrint_rec( pFile, pNtk, Dsd_NtkRoot(pNtk) );
    fprintf( pFile, "\n" );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if there is a component with more than 3 inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Kit_DsdFindLargeBox( Dsd_Ntk_t * pNtk, Dsd_Obj_t * pObj )
{
    Dsd_Obj_t * pFanin;
    unsigned iVar, i, RetValue;
    if ( pObj->nFans > 3 )
        return 1;
    RetValue = 0;
    Dsd_ObjForEachFanin( pNtk, pObj, pFanin, iVar, i )
        if ( pFanin )
            RetValue |= Kit_DsdFindLargeBox( pNtk, pFanin );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Performs decomposition of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_DsdDecompose_rec( Dsd_Ntk_t * pNtk, Dsd_Obj_t * pObj, unsigned char * pPar )
{
    Dsd_Obj_t * pRes, * pRes0, * pRes1;
    int nWords = Kit_TruthWordNum(pObj->nFans);
    unsigned * pTruth = Dsd_ObjTruth(pObj);
    unsigned * pCofs2[2] = { pNtk->pMem, pNtk->pMem + nWords };
    unsigned * pCofs4[2][2] = { {pNtk->pMem + 2 * nWords, pNtk->pMem + 3 * nWords}, {pNtk->pMem + 4 * nWords, pNtk->pMem + 5 * nWords} };
    int nFans0, nFans1, iVar0, iVar1, nPairs;
    int fEquals[2][2], fOppos, fPairs[4][4];
    unsigned j, k, nFansNew, uSupp0, uSupp1;
    int i;

    assert( pObj->nFans > 0 );
    assert( pObj->Type == KIT_DSD_PRIME );
    assert( pObj->uSupp == (uSupp0 = (unsigned)Kit_TruthSupport(pTruth, pObj->nFans)) );

    // compress the truth table
    if ( pObj->uSupp != Kit_BitMask(pObj->nFans) )
    {
        nFansNew = Kit_WordCountOnes(pObj->uSupp);
        Kit_TruthShrink( pNtk->pMem, pTruth, nFansNew, pObj->nFans, pObj->uSupp );
        Kit_TruthCopy( pTruth, pNtk->pMem, pObj->nFans );
        for ( j = k = 0; j < pObj->nFans; j++ )
            if ( pObj->uSupp & (1 << j) )
                pObj->pFans[k++] = pObj->pFans[j];
        assert( k == nFansNew );
        pObj->nFans = k;
        pObj->uSupp = Kit_BitMask(pObj->nFans);
    }

    // consider the single variable case
    if ( pObj->nFans == 1 )
    {
        pObj->Type = KIT_DSD_NONE;
        if ( pTruth[0] == 0x55555555 )
            pObj->pFans[0] ^= 1;
        else
            assert( pTruth[0] == 0xAAAAAAAA );
        // update the parent pointer
//        assert( !((*pPar) & 1) );
        *pPar = pObj->pFans[0] ^ ((*pPar) & 1);
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
            assert( pObj->uSupp == (uSupp0 | uSupp1 | (1<<i)) );
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
            pRes0->uSupp = uSupp0;
            pRes1->uSupp = uSupp1;
            // update the current one
            pObj->Type = KIT_DSD_MUX;
            pObj->nFans = 3;
            pObj->pFans[0] = pObj->pFans[i];
            pObj->pFans[1] = 2*pRes1->Id;
            pObj->pFans[2] = 2*pRes0->Id;
            // call recursively
            Kit_DsdDecompose_rec( pNtk, pRes0, pObj->pFans + 2 );
            Kit_DsdDecompose_rec( pNtk, pRes1, pObj->pFans + 1 );
            return;
        }
//Extra_PrintBinary( stdout, pTruth, 1 << pObj->nFans ); printf( "\n" );

        // create the new node
        pRes = Dsd_ObjAlloc( pNtk, KIT_DSD_AND, 2 );
        pRes->nFans = 2;
        pRes->pFans[0] = pObj->pFans[i];  pObj->pFans[i] = 127;  pObj->uSupp &= ~(1 << i);
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
            pRes->pFans[0] ^= 1;
            Kit_TruthCopy( pTruth, pCofs2[0], pObj->nFans );
        }
        else if ( fEquals[1][0] )
        {
            *pPar ^= 1;
            pRes->pFans[1] ^= 1;
            Kit_TruthCopy( pTruth, pCofs2[1], pObj->nFans );
        }
        else if ( fEquals[1][1] )
        {
            *pPar ^= 1;
            pRes->pFans[0] ^= 1;  
            pRes->pFans[1] ^= 1;
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
        Kit_DsdDecompose_rec( pNtk, pObj, pRes->pFans + 1 );
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
        // if one of the cofs is a constant, it is time to check it again
        if ( uSupp0 == 0 || uSupp1 == 0 )
        {
            pObj->fMark = 0;
            Kit_DsdDecompose_rec( pNtk, pObj, pPar );
            return;
        }
        assert( uSupp0 && uSupp1 );
        // get the number of unique variables
        nFans0 = Kit_WordCountOnes( uSupp0 & ~uSupp1 );
        nFans1 = Kit_WordCountOnes( uSupp1 & ~uSupp0 );
        if ( nFans0 == 1 && nFans1 == 1 )
        {
            // get the cofactors w.r.t. the unique variables
            iVar0 = Kit_WordFindFirstBit( uSupp0 & ~uSupp1 );
            iVar1 = Kit_WordFindFirstBit( uSupp1 & ~uSupp0 );
            // get four cofactors                                        
            Kit_TruthCofactor0New( pCofs4[0][0], pCofs2[0], pObj->nFans, iVar0 );
            Kit_TruthCofactor1New( pCofs4[0][1], pCofs2[0], pObj->nFans, iVar0 );
            Kit_TruthCofactor0New( pCofs4[1][0], pCofs2[1], pObj->nFans, iVar1 );
            Kit_TruthCofactor1New( pCofs4[1][1], pCofs2[1], pObj->nFans, iVar1 );
            // check existence conditions
            fEquals[0][0] = Kit_TruthIsEqual( pCofs4[0][0], pCofs4[1][0], pObj->nFans );
            fEquals[0][1] = Kit_TruthIsEqual( pCofs4[0][1], pCofs4[1][1], pObj->nFans );
            fEquals[1][0] = Kit_TruthIsEqual( pCofs4[0][0], pCofs4[1][1], pObj->nFans );
            fEquals[1][1] = Kit_TruthIsEqual( pCofs4[0][1], pCofs4[1][0], pObj->nFans );
            if ( (fEquals[0][0] && fEquals[0][1]) || (fEquals[1][0] && fEquals[1][1]) )
            {
                // construct the MUX
                pRes = Dsd_ObjAlloc( pNtk, KIT_DSD_MUX, 3 );
                pRes->nFans = 3;
                pRes->pFans[0] = pObj->pFans[i];     pObj->pFans[i] = 2 * pRes->Id; // remains in support
                pRes->pFans[1] = pObj->pFans[iVar1]; pObj->pFans[iVar1] = 127;  pObj->uSupp &= ~(1 << iVar1);
                pRes->pFans[2] = pObj->pFans[iVar0]; pObj->pFans[iVar0] = 127;  pObj->uSupp &= ~(1 << iVar0);
                // update the node
                if ( fEquals[0][0] && fEquals[0][1] )
                    Kit_TruthMux( pTruth, pCofs4[0][0], pCofs4[0][1], pObj->nFans, i );
                else
                    Kit_TruthMux( pTruth, pCofs4[0][1], pCofs4[0][0], pObj->nFans, i );
                // decompose the remainder
                Kit_DsdDecompose_rec( pNtk, pObj, pPar );
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
            fPairs[0][1] = fPairs[1][0] = Kit_TruthIsEqual(pCofs4[0][0], pCofs4[0][1], pObj->nFans);
            fPairs[0][2] = fPairs[2][0] = Kit_TruthIsEqual(pCofs4[0][0], pCofs4[1][0], pObj->nFans);
            fPairs[0][3] = fPairs[3][0] = Kit_TruthIsEqual(pCofs4[0][0], pCofs4[1][1], pObj->nFans);
            fPairs[1][2] = fPairs[2][1] = Kit_TruthIsEqual(pCofs4[0][1], pCofs4[1][0], pObj->nFans);
            fPairs[1][3] = fPairs[3][1] = Kit_TruthIsEqual(pCofs4[0][1], pCofs4[1][1], pObj->nFans);
            fPairs[2][3] = fPairs[3][2] = Kit_TruthIsEqual(pCofs4[1][0], pCofs4[1][1], pObj->nFans);
            nPairs = fPairs[0][1] + fPairs[0][2] + fPairs[0][3] + fPairs[1][2] + fPairs[1][3] + fPairs[2][3];
            if ( nPairs != 3 && nPairs != 2 )
                continue;

            // decomposition exists
            pRes = Dsd_ObjAlloc( pNtk, KIT_DSD_AND, 2 );
            pRes->nFans = 2;
            pRes->pFans[0] = pObj->pFans[k]; pObj->pFans[k] = 2 * pRes->Id;  // remains the support
            pRes->pFans[1] = pObj->pFans[i]; pObj->pFans[i] = 127;       pObj->uSupp &= ~(1 << i);
            if ( !fPairs[0][1] && !fPairs[0][2] && !fPairs[0][3] ) // 00
            {
                pRes->pFans[0] ^= 1;  
                pRes->pFans[1] ^= 1;
                Kit_TruthMux( pTruth, pCofs4[1][1], pCofs4[0][0], pObj->nFans, k );
            }
            else if ( !fPairs[1][0] && !fPairs[1][2] && !fPairs[1][3] ) // 01
            {
                pRes->pFans[0] ^= 1;  
                Kit_TruthMux( pTruth, pCofs4[0][0], pCofs4[0][1], pObj->nFans, k );
            }
            else if ( !fPairs[2][0] && !fPairs[2][1] && !fPairs[2][3] ) // 10
            {
                pRes->pFans[1] ^= 1;  
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
            Kit_DsdDecompose_rec( pNtk, pObj, pPar );
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
    int i, nVarsReal;
    assert( nVars <= 16 );
    pNtk = Kit_DsdNtkAlloc( pTruth, nVars );
    pNtk->Root = 2*pNtk->nVars;
    // create the first node
    pObj = Dsd_ObjAlloc( pNtk, KIT_DSD_PRIME, nVars );
    pNtk->pNodes[0] = pObj;
    for ( i = 0; i < nVars; i++ )
       pObj->pFans[i] = 2*i;
    Kit_TruthCopy( Dsd_ObjTruth(pObj), pTruth, nVars );
    pObj->uSupp = Kit_TruthSupport( pTruth, nVars );
    // consider special cases
    nVarsReal = Kit_WordCountOnes( pObj->uSupp );
    if ( nVarsReal == 0 )
    {
        pObj->Type = KIT_DSD_CONST1;
        pObj->nFans = 0;
        pNtk->Root ^= (pTruth[0] == 0);
        return pNtk;
    }
    if ( nVarsReal == 1 )
    {
        pObj->Type = KIT_DSD_VAR;
        pObj->nFans = 1;
        pObj->pFans[0] = 2 * Kit_WordFindFirstBit( pObj->uSupp );
        pObj->pFans[0] ^= (pTruth[0] & 1);
        return pNtk;
    }
    Kit_DsdDecompose_rec( pNtk, pNtk->pNodes[0], &pNtk->Root );
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
    Dsd_Obj_t * pRoot;
    unsigned * pCofs2[2] = { pNtk->pMem, pNtk->pMem + Kit_TruthWordNum(pNtk->nVars) };
    unsigned i, * pTruth;
    int fVerbose = 1;

//    pTruth = pTruthInit;

    pRoot = Dsd_NtkRoot(pNtk);
    pTruth = Dsd_ObjTruth(pRoot);
    assert( pRoot->nFans == pNtk->nVars );

    if ( fVerbose )
    {
        printf( "Function: " );
//        Extra_PrintBinary( stdout, pTruth, (1 << pNtk->nVars) ); 
        Extra_PrintHexadecimal( stdout, pTruth, pNtk->nVars ); 
        printf( "\n" );
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

//    if ( Kit_DsdFindLargeBox(pNtk, Dsd_NtkRoot(pNtk)) )
//        Kit_DsdPrint( stdout, pNtk );

    if ( Dsd_NtkRoot(pNtk)->nFans == (unsigned)nVars && nVars == 8 )
        Kit_DsdTestCofs( pNtk, pTruth );

    Kit_DsdNtkFree( pNtk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


