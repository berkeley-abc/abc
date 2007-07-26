/**CFile****************************************************************

  FileName    [cnfWrite.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG-to-CNF conversion.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: cnfWrite.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cnf.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writes the cover into the array.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cnf_SopConvertToVector( char * pSop, int nCubes, Vec_Int_t * vCover )
{
    int Lits[4], Cube, iCube, i, b;
    Vec_IntClear( vCover );
    for ( i = 0; i < nCubes; i++ )
    {
        Cube = pSop[i];
        for ( b = 0; b < 4; b++ )
        {
            if ( Cube % 3 == 0 )
                Lits[b] = 1;
            else if ( Cube % 3 == 1 )
                Lits[b] = 2;
            else
                Lits[b] = 0;
            Cube = Cube / 3;
        }
        iCube = 0;
        for ( b = 0; b < 4; b++ )
            iCube = (iCube << 2) | Lits[b];
        Vec_IntPush( vCover, iCube );
    }
}

/**Function*************************************************************

  Synopsis    [Returns the number of literals in the SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_SopCountLiterals( char * pSop, int nCubes )
{
    int nLits = 0, Cube, i, b;
    for ( i = 0; i < nCubes; i++ )
    {
        Cube = pSop[i];
        for ( b = 0; b < 4; b++ )
        {
            if ( Cube % 3 != 2 )
                nLits++;
            Cube = Cube / 3;
        }
    }
    return nLits;
}

/**Function*************************************************************

  Synopsis    [Returns the number of literals in the SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_IsopCountLiterals( Vec_Int_t * vIsop, int nVars )
{
    int nLits = 0, Cube, i, b;
    Vec_IntForEachEntry( vIsop, Cube, i )
    {
        for ( b = 0; b < nVars; b++ )
        {
            if ( (Cube & 3) == 1 || (Cube & 3) == 2 )
                nLits++;
            Cube >>= 2;
        }
    }
    return nLits;
}

/**Function*************************************************************

  Synopsis    [Writes the cube and returns the number of literals in it.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cnf_IsopWriteCube( int Cube, int nVars, int * pVars, int * pLiterals )
{
    int nLits = nVars, b;
    for ( b = 0; b < nVars; b++ )
    {
        if ( (Cube & 3) == 1 ) // value 0 --> write positive literal
            *pLiterals++ = 2 * pVars[b];
        else if ( (Cube & 3) == 2 ) // value 1 --> write negative literal
            *pLiterals++ = 2 * pVars[b] + 1;
        else
            nLits--;
        Cube >>= 2;
    }
    return nLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cnf_Dat_t * Cnf_ManWriteCnf( Cnf_Man_t * p, Vec_Ptr_t * vMapped )
{
    Aig_Obj_t * pObj;
    Cnf_Dat_t * pCnf;
    Cnf_Cut_t * pCut;
    Vec_Int_t * vCover, * vSopTemp;
    int OutVar, pVars[32], * pLits, ** pClas;
    unsigned uTruth;
    int i, k, nLiterals, nClauses, Cube, Number;

    // count the number of literals and clauses
    nLiterals = 1 + Aig_ManPoNum( p->pManAig );
    nClauses = 1 + Aig_ManPoNum( p->pManAig );
    Vec_PtrForEachEntry( vMapped, pObj, i )
    {
        assert( Aig_ObjIsNode(pObj) );
        pCut = Cnf_ObjBestCut( pObj );

        // positive polarity of the cut
        if ( pCut->nFanins < 5 )
        {
            uTruth = 0xFFFF & *Cnf_CutTruth(pCut);
            nLiterals += Cnf_SopCountLiterals( p->pSops[uTruth], p->pSopSizes[uTruth] ) + p->pSopSizes[uTruth];
            assert( p->pSopSizes[uTruth] >= 0 );
            nClauses += p->pSopSizes[uTruth];
        }
        else
        {
            nLiterals += Cnf_IsopCountLiterals( pCut->vIsop[1], pCut->nFanins ) + Vec_IntSize(pCut->vIsop[1]);
            nClauses += Vec_IntSize(pCut->vIsop[1]);
        }
        // negative polarity of the cut
        if ( pCut->nFanins < 5 )
        {
            uTruth = 0xFFFF & ~*Cnf_CutTruth(pCut);
            nLiterals += Cnf_SopCountLiterals( p->pSops[uTruth], p->pSopSizes[uTruth] ) + p->pSopSizes[uTruth];
            assert( p->pSopSizes[uTruth] >= 0 );
            nClauses += p->pSopSizes[uTruth];
        }
        else
        {
            nLiterals += Cnf_IsopCountLiterals( pCut->vIsop[0], pCut->nFanins ) + Vec_IntSize(pCut->vIsop[0]);
            nClauses += Vec_IntSize(pCut->vIsop[0]);
        }
//printf( "%d ", nClauses-(1 + Aig_ManPoNum( p->pManAig )) );
    }
//printf( "\n" );

    // allocate CNF
    pCnf = ALLOC( Cnf_Dat_t, 1 );
    memset( pCnf, 0, sizeof(Cnf_Dat_t) );
    pCnf->nLiterals = nLiterals;
    pCnf->nClauses = nClauses;
    pCnf->pClauses = ALLOC( int *, nClauses + 1 );
    pCnf->pClauses[0] = ALLOC( int, nLiterals );
    pCnf->pClauses[nClauses] = pCnf->pClauses[0] + nLiterals;

    // set variable numbers
    Number = 0;
    pCnf->pVarNums = ALLOC( int, 1+Aig_ManObjIdMax(p->pManAig) );
    memset( pCnf->pVarNums, 0xff, sizeof(int) * (1+Aig_ManObjIdMax(p->pManAig)) );
    Vec_PtrForEachEntry( vMapped, pObj, i )
        pCnf->pVarNums[pObj->Id] = Number++;
    Aig_ManForEachPi( p->pManAig, pObj, i )
        pCnf->pVarNums[pObj->Id] = Number++;
    pCnf->pVarNums[Aig_ManConst1(p->pManAig)->Id] = Number++;
    pCnf->nVars = Number;

    // assign the clauses
    vSopTemp = Vec_IntAlloc( 1 << 16 );
    pLits = pCnf->pClauses[0];
    pClas = pCnf->pClauses;
    Vec_PtrForEachEntry( vMapped, pObj, i )
    {
        pCut = Cnf_ObjBestCut( pObj );

        // save variables of this cut
        OutVar = pCnf->pVarNums[ pObj->Id ];
        for ( k = 0; k < (int)pCut->nFanins; k++ )
        {
            pVars[k] = pCnf->pVarNums[ pCut->pFanins[k] ];
            assert( pVars[k] <= Aig_ManObjIdMax(p->pManAig) );
        }

        // positive polarity of the cut
        if ( pCut->nFanins < 5 )
        {
            uTruth = 0xFFFF & *Cnf_CutTruth(pCut);
            Cnf_SopConvertToVector( p->pSops[uTruth], p->pSopSizes[uTruth], vSopTemp );
            vCover = vSopTemp;
        }
        else
            vCover = pCut->vIsop[1];
        Vec_IntForEachEntry( vCover, Cube, k )
        {
            *pClas++ = pLits;
            *pLits++ = 2 * OutVar; 
            pLits += Cnf_IsopWriteCube( Cube, pCut->nFanins, pVars, pLits );
        }

        // negative polarity of the cut
        if ( pCut->nFanins < 5 )
        {
            uTruth = 0xFFFF & ~*Cnf_CutTruth(pCut);
            Cnf_SopConvertToVector( p->pSops[uTruth], p->pSopSizes[uTruth], vSopTemp );
            vCover = vSopTemp;
        }
        else
            vCover = pCut->vIsop[0];
        Vec_IntForEachEntry( vCover, Cube, k )
        {
            *pClas++ = pLits;
            *pLits++ = 2 * OutVar + 1; 
            pLits += Cnf_IsopWriteCube( Cube, pCut->nFanins, pVars, pLits );
        }
    }
    Vec_IntFree( vSopTemp );
 
    // write the constant literal
    OutVar = pCnf->pVarNums[ Aig_ManConst1(p->pManAig)->Id ];
    assert( OutVar <= Aig_ManObjIdMax(p->pManAig) );
    *pClas++ = pLits;
    *pLits++ = 2 * OutVar; 

    // write the output literals
    Aig_ManForEachPo( p->pManAig, pObj, i )
    {
        OutVar = pCnf->pVarNums[ Aig_ObjFanin0(pObj)->Id ];
        *pClas++ = pLits;
        *pLits++ = 2 * OutVar + Aig_ObjFaninC0(pObj); 
    }

    // verify that the correct number of literals and clauses was written
    assert( pLits - pCnf->pClauses[0] == nLiterals );
    assert( pClas - pCnf->pClauses == nClauses );
    return pCnf;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


