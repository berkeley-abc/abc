/**CFile****************************************************************

  FileName    [npnUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName []

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: npnUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "extra.h"
#include "npn.h"
#include "vec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Vec_Ptr_t * Npn_Generate_rec( int nVars, int fFold );
static void Npn_GenerateMerge( Vec_Ptr_t * vVec1, Vec_Ptr_t * vVec2, Vec_Ptr_t * vVec );
static void Npn_GenerateFree( Vec_Ptr_t * vVec );
static Vec_Ptr_t * Npn_GenerateFold( Vec_Ptr_t * vVec );
static void Npn_GenerateEmbed( Vec_Ptr_t * vVec );
static void Npn_GeneratePrint( Vec_Ptr_t * vVec );


static void Npn_RewritePrint( Vec_Ptr_t * vVec );
static Vec_Ptr_t * Npn_Rewrite( char * pStruct );

static int Npn_RewriteNumEntries( char * pString );
static int Npn_RewriteLastAnd( char * pBeg, char * pString );
static int Npn_RewriteLastExor( char * pBeg, char * pString );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_Generate()
{
    Vec_Ptr_t * vVec;
    vVec = Npn_Generate_rec( 7, 1 );
    Npn_GenerateEmbed( vVec );
    Npn_GeneratePrint( vVec );
    Npn_GenerateFree( vVec );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Npn_Generate_rec( int nVars, int fFold )
{
    char Buffer[20], * pChar;
    Vec_Ptr_t * vVec, * vVec1, * vVec2, * pTemp;
    int i;

    vVec = Vec_PtrAlloc( 100 );

    // generate the combination
    pChar = Buffer;
    for ( i = 0; i < nVars; i++ )
        *pChar++ = '.';
    *pChar++ = 0;

    Vec_PtrPush( vVec, util_strsav(Buffer) );
    if ( nVars == 2 || !fFold )
        return vVec;

    assert( nVars > 2 );
    for ( i = 2; i < nVars; i++ )
    {
        vVec1 = Npn_Generate_rec( i, 1 );
        vVec1 = Npn_GenerateFold( pTemp = vVec1 );
        Npn_GenerateFree( pTemp );
        // add folded pairs
        if ( nVars - i > 1 )
        {
            vVec2 = Npn_Generate_rec( nVars - i, 1 );
            vVec2 = Npn_GenerateFold( pTemp = vVec2 );
            Npn_GenerateFree( pTemp );
            Npn_GenerateMerge( vVec1, vVec2, vVec );
            Npn_GenerateFree( vVec2 );
        }
        // add unfolded pairs
        vVec2 = Npn_Generate_rec( nVars - i, 0 );
        Npn_GenerateMerge( vVec1, vVec2, vVec );
        Npn_GenerateFree( vVec2 );
        Npn_GenerateFree( vVec1 );
    }
    return vVec;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_GenerateMerge( Vec_Ptr_t * vVec1, Vec_Ptr_t * vVec2, Vec_Ptr_t * vVec )
{
    char Buffer[100];
    char * pEntry1, * pEntry2, * pEntry;
    int i, k, m;
    Vec_PtrForEachEntry( vVec1, pEntry1, i )
    Vec_PtrForEachEntry( vVec2, pEntry2, k )
    {
        if ( *pEntry1 == '(' && *pEntry2 == '(' )
            if ( strcmp( pEntry1, pEntry2 ) > 0 )
                continue;

        // get the new entry
        sprintf( Buffer, "%s%s", pEntry1, pEntry2 );
        // skip duplicates
        Vec_PtrForEachEntry( vVec, pEntry, m )
            if ( strcmp( pEntry, Buffer ) == 0 )
                break;
        if ( m != Vec_PtrSize(vVec) )
            continue;
        // add the new entry
        Vec_PtrPush( vVec, util_strsav(Buffer) );
    }    
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_GenerateFree( Vec_Ptr_t * vVec )
{
    char * pEntry;
    int i;
    Vec_PtrForEachEntry( vVec, pEntry, i )
        free( pEntry );
    Vec_PtrFree( vVec );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Npn_GenerateFold( Vec_Ptr_t * vVec )
{
    Vec_Ptr_t * vVecR;
    char Buffer[100];
    char * pEntry;
    int i;
    vVecR = Vec_PtrAlloc( 10 );
    Vec_PtrForEachEntry( vVec, pEntry, i )
    {
        // add entry without folding if the second part is folded
        if ( pEntry[strlen(pEntry) - 1] == ')' )
            Vec_PtrPush( vVecR, util_strsav(pEntry) );
        // add the entry with folding
        sprintf( Buffer, "(%s)", pEntry );
        Vec_PtrPush( vVecR, util_strsav(Buffer) );
    }
    return vVecR;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_GenerateEmbed( Vec_Ptr_t * vVec )
{
    char Buffer[100];
    char * pEntry;
    int i;
    Vec_PtrForEachEntry( vVec, pEntry, i )
    {
        sprintf( Buffer, "(%s)", pEntry );
        Vec_PtrWriteEntry( vVec, i, util_strsav(Buffer) );
        free( pEntry );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_GeneratePrint( Vec_Ptr_t * vVec )
{
    char * pEntry;
    int i;
    Vec_PtrForEachEntry( vVec, pEntry, i )
    {
        printf( "%5d : %s\n", i, pEntry );

        {
            Vec_Ptr_t * vFuncs;
            vFuncs = Npn_Rewrite( pEntry );
            Npn_RewritePrint( vFuncs );
            Vec_PtrFree( vFuncs );
        }
    }
}




/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_RewritePrint( Vec_Ptr_t * vVec )
{
    char * pEntry;
    int i;
    Vec_PtrForEachEntry( vVec, pEntry, i )
        printf( "    %3d : %s\n", i, pEntry );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Npn_Rewrite_rec( char * pStruct, Vec_Ptr_t * vVec, Vec_Str_t * vForm )
{
    int nSizeOld;
    char * pCur;
    // find the next opening paranthesis
    for ( pCur = pStruct; *pCur; pCur++ )
    {
        if ( *pCur == '(' )
            break;
        Vec_StrPush( vForm, *pCur );
    }
    // the paranthesis is not found quit
    if ( *pCur == 0 )
    {
        Vec_StrPush( vForm, 0 );
        Vec_PtrPush( vVec, util_strsav( vForm->pArray ) );
        return;
    }
    assert( *pCur == '(' );
    pCur++;
    // remember the current size
    nSizeOld = vForm->nSize;
    // add different types
    if ( Npn_RewriteLastAnd(vForm->pArray, vForm->pArray+vForm->nSize) )
    {
        Vec_StrPush( vForm, 'N' );
        Vec_StrPush( vForm, '(' );
        Npn_Rewrite_rec( pCur, vVec, vForm );
        Vec_StrShrink( vForm, nSizeOld );
    }
    else
    {
        Vec_StrPush( vForm, 'A' );
        Vec_StrPush( vForm, '(' );
        Npn_Rewrite_rec( pCur, vVec, vForm );
        Vec_StrShrink( vForm, nSizeOld );
    }
    // add different types
    if ( Npn_RewriteNumEntries(pCur) == 3 )
    {
        Vec_StrPush( vForm, 'P' );
        Vec_StrPush( vForm, '(' );
        Npn_Rewrite_rec( pCur, vVec, vForm );
        Vec_StrShrink( vForm, nSizeOld );
    }
    // add different types
    if ( !Npn_RewriteLastExor(vForm->pArray, vForm->pArray+vForm->nSize) )
    {
        Vec_StrPush( vForm, 'X' );
        Vec_StrPush( vForm, '(' );
        Npn_Rewrite_rec( pCur, vVec, vForm );
        Vec_StrShrink( vForm, nSizeOld );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Npn_Rewrite( char * pStruct )
{
    Vec_Ptr_t * vVec;
    Vec_Str_t * vForm;
    vVec  = Vec_PtrAlloc( 10 );
    vForm = Vec_StrAlloc( 10 );
    Npn_Rewrite_rec( pStruct, vVec, vForm );
    Vec_StrFree( vForm );
    return vVec;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Npn_RewriteNumEntries( char * pString )
{
    char * pCur;
    int Counter = 0;
    int nPars = 0;
    for ( pCur = pString; *pCur; pCur++ )
    {
        if ( nPars == 0 )
        {
            if ( *pCur == '.' )
                Counter++;
            else if ( *pCur == '(' )
            {
                Counter++;
                nPars++;
            }
            else if ( *pCur == ')' )
                nPars--;
        }
        else if ( nPars > 0 )
        {
            if ( *pCur == '(' )
                nPars++;
            else if ( *pCur == ')' )
                nPars--;
        }
        else
            break;
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the last was EXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Npn_RewriteLastAnd( char * pBeg, char * pEnd )
{
    char * pCur;
    int nPars = 1;
    for ( pCur = pEnd - 1; pCur >= pBeg; pCur-- )
    {
            if ( *pCur == ')' )
                nPars++;
            else if ( *pCur == '(' )
                nPars--;

            if ( nPars == 0 && *pCur == 'A' )
                return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the last was EXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Npn_RewriteLastExor( char * pBeg, char * pEnd )
{
    char * pCur;
    int nPars = 1;
    for ( pCur = pEnd - 1; pCur >= pBeg; pCur-- )
    {
            if ( *pCur == ')' )
                nPars++;
            else if ( *pCur == '(' )
                nPars--;

            if ( nPars == 0 && *pCur == 'X' )
                return 1;
    }
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


