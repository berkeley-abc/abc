/**CFile****************************************************************

  FileName    [npn.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName []

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: npn.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "extra.h"
#include "npn.h"
#include "vec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Npn_CompareVecs( void ** p0, void ** p1 );
static Vec_Int_t * Npn_GetSignature( unsigned uTruth, int nVars );
static void Npn_VecPrint( FILE * pFile, Vec_Int_t * vVec );
static int Npn_VecProperty( Vec_Int_t * vVec );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_Experiment()
{
    Vec_Int_t ** pVecs;
    FILE * pFile;
    int nFuncs, Num, i;

    pFile = fopen( "npn5.txt", "r" );
    pVecs = ALLOC( Vec_Int_t *, 1000000 );
    for ( i = 0; ; i++ )
    {
        if ( fscanf( pFile, "%x", &Num ) != 1 )
            break;
        pVecs[i] = Npn_GetSignature( Num, 5 );
        if ( Npn_VecProperty( pVecs[i] ) )
        {
            printf( "1s = %2d. ", Extra_CountOnes((unsigned char *)&Num, (1 << 5) / 8) );
            Extra_PrintHex( stdout, Num, 5 ); fprintf( stdout, "\n" );
        }
        
    }
    nFuncs = i;
    printf( "Read %d numbers.\n", nFuncs );
    fclose( pFile );
    /*
    // sort the vectors
    qsort( (void *)pVecs, nFuncs, sizeof(void *), 
            (int (*)(const void *, const void *)) Npn_CompareVecs );
    pFile = fopen( "npn5ar.txt", "w" );
    for ( i = 0; i < nFuncs; i++ )
    {
        Npn_VecPrint( pFile, pVecs[i] );
        Vec_IntFree( pVecs[i] );
    }
    fclose( pFile );
    */

    free( pVecs );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Npn_GetSignature( unsigned uTruth, int nVars )
{
    // elementary truth tables
    static unsigned Signs[5] = {
        0xAAAAAAAA,    // 1010 1010 1010 1010 1010 1010 1010 1010
        0xCCCCCCCC,    // 1010 1010 1010 1010 1010 1010 1010 1010
        0xF0F0F0F0,    // 1111 0000 1111 0000 1111 0000 1111 0000
        0xFF00FF00,    // 1111 1111 0000 0000 1111 1111 0000 0000
        0xFFFF0000     // 1111 1111 1111 1111 0000 0000 0000 0000
    };
    Vec_Int_t * vVec;
    unsigned uCofactor;
    int Count0, Count1, i;
    int nBytes = (1 << nVars) / 8;

    // collect the number of 1s in each cofactor
    vVec = Vec_IntAlloc( 5 );
    for ( i = 0; i < nVars; i++ )
    {
        uCofactor = uTruth & ~Signs[i];
        Count0 = Extra_CountOnes( (unsigned char *)&uCofactor, nBytes );
        uCofactor = uTruth &  Signs[i];
        Count1 = Extra_CountOnes( (unsigned char *)&uCofactor, nBytes );
        if ( Count0 < Count1 )
            Vec_IntPush( vVec, Count0 );
        else
            Vec_IntPush( vVec, Count1 );
    }
    // sort them
    Vec_IntSort( vVec, 0 );
    return vVec;
    
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Npn_CompareVecs( void ** p0, void ** p1 )
{
    Vec_Int_t * vVec0 = *p0;
    Vec_Int_t * vVec1 = *p1;
    int i;
    assert( vVec0->nSize == vVec1->nSize );
    for ( i = 0; i < vVec0->nSize; i++ )
        if ( vVec0->pArray[i] < vVec1->pArray[i] )
            return -1;
        else if ( vVec0->pArray[i] > vVec1->pArray[i] )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_VecPrint( FILE * pFile, Vec_Int_t * vVec )
{
    int i;
    for ( i = 0; i < vVec->nSize; i++ )
        fprintf( pFile, "%2d ", vVec->pArray[i] );
    fprintf( pFile, "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Npn_VecProperty( Vec_Int_t * vVec )
{
    int i;
    for ( i = 0; i < vVec->nSize; i++ )
        if ( vVec->pArray[i] != i + 1 )
            return 0;
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


