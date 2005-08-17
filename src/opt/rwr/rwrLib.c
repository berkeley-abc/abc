/**CFile****************************************************************

  FileName    [rwrLib.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrLib.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Rwr_Node_t *        Rwr_ManTryNode( Abc_ManRwr_t * p, Rwr_Node_t * p0, Rwr_Node_t * p1, int fExor, int Level, int Volume );
static Rwr_Node_t *        Rwr_ManAddNode( Abc_ManRwr_t * p, Rwr_Node_t * p0, Rwr_Node_t * p1, int fExor, int Level, int Volume );
static int                 Rwr_ManNodeVolume( Abc_ManRwr_t * p, Rwr_Node_t * p0, Rwr_Node_t * p1 );

static void                Rwr_ManIncTravId_int( Abc_ManRwr_t * p );
static inline void         Rwr_ManIncTravId( Abc_ManRwr_t * p )     { if ( p->nTravIds++ == 0x8FFFFFFF ) Rwr_ManIncTravId_int( p ); }

static void                Rwr_MarkUsed_rec( Abc_ManRwr_t * p, Rwr_Node_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Precomputes the forest in the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManPrecompute( Abc_ManRwr_t * p )
{
    Rwr_Node_t * p0, * p1;
    int i, k, Level, Volume;
    int LevelOld = -1;
    int nNodes;

    Vec_PtrForEachEntryStart( p->vForest, p0, i, 1 )
    Vec_PtrForEachEntryStart( p->vForest, p1, k, 1 )
    {
        if ( LevelOld < (int)p0->Level )
        {
            LevelOld = p0->Level;
            printf( "Starting level %d  (at %d nodes).\n", LevelOld+1, i );
            printf( "Considered = %5d M.   Found = %8d.   Classes = %6d.   Trying %7d.\n", 
                p->nConsidered/1000000, p->vForest->nSize, p->nClasses, i );
        }

        if ( k == i )
            break;
//        if ( p0->Level + p1->Level > 6 ) // hard
//            break;

        if ( p0->Level + p1->Level > 5 ) // easy 
            break;

//        if ( p0->Level + p1->Level > 6 || (p0->Level == 3 && p1->Level == 3) )
//            break;

        // compute the level and volume of the new nodes
        Level  = 1 + ABC_MAX( p0->Level, p1->Level );
        Volume = 1 + Rwr_ManNodeVolume( p, p0, p1 );
        // try four different nodes
        Rwr_ManTryNode( p,         p0 ,         p1 , 0, Level, Volume );
        Rwr_ManTryNode( p, Rwr_Not(p0),         p1 , 0, Level, Volume );
        Rwr_ManTryNode( p,         p0 , Rwr_Not(p1), 0, Level, Volume );
        Rwr_ManTryNode( p, Rwr_Not(p0), Rwr_Not(p1), 0, Level, Volume );
        // try EXOR
        Rwr_ManTryNode( p,         p0 ,         p1 , 1, Level, Volume + 1 );
        // report the progress
        if ( p->nConsidered % 50000000 == 0 )
            printf( "Considered = %5d M.   Found = %8d.   Classes = %6d.   Trying %7d.\n", 
                p->nConsidered/1000000, p->vForest->nSize, p->nClasses, i );
        // quit after some time
        if ( p->vForest->nSize == RWR_LIMIT + 5 )
        {
            printf( "Considered = %5d M.   Found = %8d.   Classes = %6d.   Trying %7d.\n", 
                p->nConsidered/1000000, p->vForest->nSize, p->nClasses, i );
            goto save;
        }
    }
save :

    // mark the relevant ones
    Rwr_ManIncTravId( p );
    k = 5;
    nNodes = 0;
    Vec_PtrForEachEntryStart( p->vForest, p0, i, 5 )
        if ( p0->uTruth == p->puCanons[p0->uTruth] )
        {
            Rwr_MarkUsed_rec( p, p0 );
            nNodes++;
        }

    // compact the array by throwing away non-canonical
    k = 5;
    Vec_PtrForEachEntryStart( p->vForest, p0, i, 5 )
        if ( p0->fUsed )
        {
            p->vForest->pArray[k] = p0;
            p0->Id = k;
            k++;
        }
    p->vForest->nSize = k;
    printf( "Total canonical = %4d. Total used = %5d.\n", nNodes, p->vForest->nSize );
}

/**Function*************************************************************

  Synopsis    [Writes to file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManWriteToFile( Abc_ManRwr_t * p, char * pFileName )
{
    FILE * pFile;
    Rwr_Node_t * pNode;
    unsigned * pBuffer;
    int i, nEntries, clk = clock();
    // prepare the buffer
    nEntries = p->vForest->nSize - 5;
    pBuffer = ALLOC( unsigned, nEntries * 2 );
    for ( i = 0; i < nEntries; i++ )
    {
        pNode = p->vForest->pArray[i+5];
        pBuffer[2*i + 0] = (Rwr_Regular(pNode->p0)->Id << 1) | Rwr_IsComplement(pNode->p0);
        pBuffer[2*i + 1] = (Rwr_Regular(pNode->p1)->Id << 1) | Rwr_IsComplement(pNode->p1);
        // save EXOR flag
        pBuffer[2*i + 0] = (pBuffer[2*i + 0] << 1) | pNode->fExor;

    }
    pFile = fopen( pFileName, "wb" );
    fwrite( &nEntries, sizeof(int), 1, pFile );
    fwrite( pBuffer, sizeof(unsigned), nEntries * 2, pFile );
    free( pBuffer );
    fclose( pFile );
    printf( "The number of nodes saved = %d.   ", nEntries );  PRT( "Saving", clock() - clk );
}

/**Function*************************************************************

  Synopsis    [Loads data from file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManLoadFromFile( Abc_ManRwr_t * p, char * pFileName )
{
    FILE * pFile;
    Rwr_Node_t * p0, * p1;
    unsigned * pBuffer;
    int Level, Volume, nEntries, fExor;
    int i, clk = clock();

    // load the data
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Rwr_ManLoadFromFile: Cannot open file \"%s\".\n", pFileName );
        return;
    }
    fread( &nEntries, sizeof(int), 1, pFile );
    pBuffer = ALLOC( unsigned, nEntries * 2 );
    fread( pBuffer, sizeof(unsigned), nEntries * 2, pFile );
    fclose( pFile );
    // reconstruct the forest
    for ( i = 0; i < nEntries; i++ )
    {
        // get EXOR flag
        fExor = (pBuffer[2*i + 0] & 1);
        pBuffer[2*i + 0] = (pBuffer[2*i + 0] >> 1);
        // get the nodes
        p0 = p->vForest->pArray[pBuffer[2*i + 0] >> 1];
        p1 = p->vForest->pArray[pBuffer[2*i + 1] >> 1];
        // compute the level and volume of the new nodes
        Level  = 1 + ABC_MAX( p0->Level, p1->Level );
        Volume = 1 + Rwr_ManNodeVolume( p, p0, p1 );
        // set the complemented attributes
        p0 = Rwr_NotCond( p0, (pBuffer[2*i + 0] & 1) );
        p1 = Rwr_NotCond( p1, (pBuffer[2*i + 1] & 1) );
        // add the node
//        Rwr_ManTryNode( p, p0, p1, Level, Volume );
        Rwr_ManAddNode( p, p0, p1, fExor, Level, Volume + fExor );
    }
    free( pBuffer );
    printf( "The number of classes = %d. Canonical nodes = %d.\n", p->nClasses, p->nAdded );
    printf( "The number of nodes loaded = %d.   ", nEntries );  PRT( "Loading", clock() - clk );
}

/**Function*************************************************************

  Synopsis    [Adds one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManIncTravId_int( Abc_ManRwr_t * p )
{
    Rwr_Node_t * pNode;
    int i;
    Vec_PtrForEachEntry( p->vForest, pNode, i )
        pNode->TravId = 0;
    p->nTravIds = 1;
}

/**Function*************************************************************

  Synopsis    [Adds one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_MarkUsed_rec( Abc_ManRwr_t * p, Rwr_Node_t * pNode )
{
    if ( pNode->fUsed || pNode->TravId == p->nTravIds )
        return;
    pNode->TravId = p->nTravIds;
    pNode->fUsed = 1;
    Rwr_MarkUsed_rec( p, Rwr_Regular(pNode->p0) );
    Rwr_MarkUsed_rec( p, Rwr_Regular(pNode->p1) );
}

/**Function*************************************************************

  Synopsis    [Adds one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_Trav_rec( Abc_ManRwr_t * p, Rwr_Node_t * pNode, int * pVolume )
{
    if ( pNode->fMark || pNode->TravId == p->nTravIds )
        return;
    pNode->TravId = p->nTravIds;
    (*pVolume)++;
    if ( pNode->fExor )
        (*pVolume)++;
    Rwr_Trav_rec( p, Rwr_Regular(pNode->p0), pVolume );
    Rwr_Trav_rec( p, Rwr_Regular(pNode->p1), pVolume );
}

/**Function*************************************************************

  Synopsis    [Adds one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_Trav2_rec( Abc_ManRwr_t * p, Rwr_Node_t * pNode, int * pVolume )
{
    if ( pNode->fMark || pNode->TravId == p->nTravIds )
        return;
    pNode->TravId = p->nTravIds;
    (*pVolume)++;
    Rwr_Trav2_rec( p, Rwr_Regular(pNode->p0), pVolume );
    Rwr_Trav2_rec( p, Rwr_Regular(pNode->p1), pVolume );
}

/**Function*************************************************************

  Synopsis    [Adds one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rwr_ManNodeVolume( Abc_ManRwr_t * p, Rwr_Node_t * p0, Rwr_Node_t * p1 )
{
    int Volume = 0;
    Rwr_ManIncTravId( p );
    Rwr_Trav_rec( p, p0, &Volume );
    Rwr_Trav_rec( p, p1, &Volume );
    return Volume;
}

/**Function*************************************************************

  Synopsis    [Adds one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rwr_Node_t * Rwr_ManTryNode( Abc_ManRwr_t * p, Rwr_Node_t * p0, Rwr_Node_t * p1, int fExor, int Level, int Volume )
{
    Rwr_Node_t * pOld, * pNew, ** ppPlace;
    unsigned uTruth, uCanon;
    // compute truth table, level, volume
    p->nConsidered++;
    if ( fExor )
    {
//        printf( "Considering EXOR of %d and %d.\n", p0->Id, p1->Id );
        uTruth = (p0->uTruth ^ p1->uTruth);
    }
    else
        uTruth = (Rwr_IsComplement(p0)? ~Rwr_Regular(p0)->uTruth : Rwr_Regular(p0)->uTruth) & 
                 (Rwr_IsComplement(p1)? ~Rwr_Regular(p1)->uTruth : Rwr_Regular(p1)->uTruth) & 0xFFFF;
    uCanon = p->puCanons[uTruth];
    // skip non-practical classes
    if ( Level > 2 && p->pPractical[uCanon] == 0 )
        return NULL;
    // enumerate through the nodes with the same canonical form
    ppPlace = p->pTable + uCanon;
    for ( pOld = *ppPlace; pOld; ppPlace = &pOld->pNext, pOld = pOld->pNext )
    {
        if ( pOld->Level <  (unsigned)Level && pOld->Volume < (unsigned)Volume )
            return NULL;
        if ( pOld->Level == (unsigned)Level && pOld->Volume < (unsigned)Volume )
            return NULL;
//        if ( pOld->Level <  (unsigned)Level && pOld->Volume == (unsigned)Volume )
//            return NULL;
    }
//    if ( fExor )
//        printf( "Adding EXOR of %d and %d.\n", p0->Id, p1->Id );
    // create the new node
    pNew = (Rwr_Node_t *)Extra_MmFixedEntryFetch( p->pMmNode );
    pNew->Id     = p->vForest->nSize;
    pNew->TravId = 0;
    pNew->uTruth = uTruth;
    pNew->Level  = Level;
    pNew->Volume = Volume;
    pNew->fMark  = 0;
    pNew->fUsed  = 0;
    pNew->fExor  = fExor;
    pNew->p0     = p0;
    pNew->p1     = p1;
    pNew->pNext  = NULL;
    Vec_PtrPush( p->vForest, pNew );
    *ppPlace     = pNew;
    if ( p->pTable[uCanon] == pNew )
        p->nClasses++;
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Adds one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rwr_Node_t * Rwr_ManAddNode( Abc_ManRwr_t * p, Rwr_Node_t * p0, Rwr_Node_t * p1, int fExor, int Level, int Volume )
{
    Rwr_Node_t * pOld, * pNew;
    unsigned uTruth, uCanon;
    // compute truth table, leve, volume
    p->nConsidered++;
    if ( fExor )
        uTruth = (p0->uTruth ^ p1->uTruth);
    else
        uTruth = (Rwr_IsComplement(p0)? ~Rwr_Regular(p0)->uTruth : Rwr_Regular(p0)->uTruth) & 
                 (Rwr_IsComplement(p1)? ~Rwr_Regular(p1)->uTruth : Rwr_Regular(p1)->uTruth) & 0xFFFF;
    uCanon = p->puCanons[uTruth];
    // skip non-practical classes
//    if ( p->pPractical[uCanon] == 0 )
//        return NULL;
    // create the new node
    pNew = (Rwr_Node_t *)Extra_MmFixedEntryFetch( p->pMmNode );
    pNew->Id     = p->vForest->nSize;
    pNew->TravId = 0;
    pNew->uTruth = uTruth;
    pNew->Level  = Level;
    pNew->Volume = Volume;
    pNew->fMark  = 0;
    pNew->fUsed  = 0;
    pNew->fExor  = fExor;
    pNew->p0     = p0;
    pNew->p1     = p1;
    pNew->pNext  = NULL;
    Vec_PtrPush( p->vForest, pNew );
    // do not add if the node is not essential
    if ( uTruth != uCanon )
        return pNew;

    // add to the list
    p->nAdded++;
    pOld = p->pTable[uCanon];
    if ( pOld == NULL )
        p->nClasses++;
    pNew->pNext = pOld;
    p->pTable[uCanon] = pNew;
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Adds one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rwr_Node_t * Rwr_ManAddVar( Abc_ManRwr_t * p, unsigned uTruth )
{
    Rwr_Node_t * pNew;
    pNew = (Rwr_Node_t *)Extra_MmFixedEntryFetch( p->pMmNode );
    pNew->Id     = p->vForest->nSize;
    pNew->TravId = 0;
    pNew->uTruth = uTruth;
    pNew->Level  = 0;
    pNew->Volume = 0;
    pNew->fMark  = 1;
    pNew->fUsed  = 1;
    pNew->fExor  = 0;
    pNew->p0     = NULL;
    pNew->p1     = NULL;    pNew->pNext  = NULL;
    Vec_PtrPush( p->vForest, pNew );
    assert( p->pTable[p->puCanons[uTruth]] == NULL );
    p->pTable[p->puCanons[uTruth]] = pNew;
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Prints one rwr node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_NodePrint_rec( FILE * pFile, Rwr_Node_t * pNode )
{
    assert( !Rwr_IsComplement(pNode) );

    if ( pNode->Id == 0 )
    {
        fprintf( pFile, "Const1" );
        return;
    }

    if ( pNode->Id < 5 )
    {
        fprintf( pFile, "%c", 'a' + pNode->Id - 1 );
        return;
    }

    if ( Rwr_IsComplement(pNode->p0) )
    {
        if ( Rwr_Regular(pNode->p0)->Id < 5 )
        {
            Rwr_NodePrint_rec( pFile, Rwr_Regular(pNode->p0) );
            fprintf( pFile, "\'" );
        }
        else
        {
            fprintf( pFile, "(" );
            Rwr_NodePrint_rec( pFile, Rwr_Regular(pNode->p0) );
            fprintf( pFile, ")\'" );
        }
    }
    else
    {
        if ( Rwr_Regular(pNode->p0)->Id < 5 )
        {
            Rwr_NodePrint_rec( pFile, Rwr_Regular(pNode->p0) );
        }
        else
        {
            fprintf( pFile, "(" );
            Rwr_NodePrint_rec( pFile, Rwr_Regular(pNode->p0) );
            fprintf( pFile, ")" );
        }
    }

    if ( pNode->fExor )
        fprintf( pFile, "+" );

    if ( Rwr_IsComplement(pNode->p1) )
    {
        if ( Rwr_Regular(pNode->p1)->Id < 5 )
        {
            Rwr_NodePrint_rec( pFile, Rwr_Regular(pNode->p1) );
            fprintf( pFile, "\'" );
        }
        else
        {
            fprintf( pFile, "(" );
            Rwr_NodePrint_rec( pFile, Rwr_Regular(pNode->p1) );
            fprintf( pFile, ")\'" );
        }
    }
    else
    {
        if ( Rwr_Regular(pNode->p1)->Id < 5 )
        {
            Rwr_NodePrint_rec( pFile, Rwr_Regular(pNode->p1) );
        }
        else
        {
            fprintf( pFile, "(" );
            Rwr_NodePrint_rec( pFile, Rwr_Regular(pNode->p1) );
            fprintf( pFile, ")" );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Prints one rwr node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_NodePrint( FILE * pFile, Abc_ManRwr_t * p, Rwr_Node_t * pNode )
{
    unsigned uTruth;
    fprintf( pFile, "%5d :", pNode->Id );
    fprintf( pFile, " tt=", pNode->Id );
    uTruth = pNode->uTruth;
    Extra_PrintBinary( pFile, &uTruth, 16 );
    fprintf( pFile, " cn=", pNode->Id );
    uTruth = p->puCanons[pNode->uTruth];
    Extra_PrintBinary( pFile, &uTruth, 16 );
    fprintf( pFile, " lev=%d", pNode->Level );
    fprintf( pFile, " vol=%d", pNode->Volume );
    fprintf( pFile, "  " );
    Rwr_NodePrint_rec( pFile, pNode );
    fprintf( pFile, "\n" );
}

/**Function*************************************************************

  Synopsis    [Prints one rwr node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManPrint( Abc_ManRwr_t * p )
{
/*
    Rwr_Node_t * pNode;
    unsigned uTruth;
    int Limit = 4;
    int i;

    for ( i = 0; i < p->nFuncs; i++ )
    {
        if ( p->pTable[i] == NULL )
            continue;
        if ( Limit-- == 0 )
            break;
        printf( "\nClass " );
        uTruth = i;
        Extra_PrintBinary( stdout, &uTruth, 16 );
        printf( "\n" );
        for ( pNode = p->pTable[i]; pNode; pNode = pNode->pNext )
            if ( pNode->uTruth == p->puCanons[pNode->uTruth] )
                Rwr_NodePrint( p, pNode );
    }
*/
    FILE * pFile;
    Rwr_Node_t * pNode;
    unsigned uTruth;
    int Limit = 4;
    int Counter;
    int i;

    pFile = fopen( "graph_lib.txt", "w" );

    Counter = 0;
    for ( i = 0; i < p->nFuncs; i++ )
    {
        if ( p->pTable[i] == NULL )
            continue;
//        if ( Limit-- == 0 )
//            break;
        fprintf( pFile, "\nClass %3d  ", Counter++ );

        // count the volume of the bush
        {
            int Volume = 0;
            int nFuncs = 0;
            Rwr_ManIncTravId( p );
            for ( pNode = p->pTable[i]; pNode; pNode = pNode->pNext )
                if ( pNode->uTruth == p->puCanons[pNode->uTruth] )
                {
                    nFuncs++;
                    Rwr_Trav2_rec( p, pNode, &Volume );
                }
            fprintf( pFile, "Functions = %2d. Volume = %2d. ", nFuncs, Volume );
        }

        uTruth = i;
        Extra_PrintBinary( pFile, &uTruth, 16 );
        fprintf( pFile, "\n" );

        for ( pNode = p->pTable[i]; pNode; pNode = pNode->pNext )
            if ( pNode->uTruth == p->puCanons[pNode->uTruth] )
                Rwr_NodePrint( pFile, p, pNode );
    }

    fclose( pFile );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


