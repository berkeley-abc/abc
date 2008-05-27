/**CFile****************************************************************

  FileName    [ntlReadBlif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to read BLIF file.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 8, 2007.]

  Revision    [$Id: ntlReadBlif.c,v 1.00 2007/01/08 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Ioa_ReadMod_t_ Ioa_ReadMod_t;   // parsing model
typedef struct Ioa_ReadMan_t_ Ioa_ReadMan_t;   // parsing manager

struct Ioa_ReadMod_t_
{
    // file lines
    char *               pFirst;       // .model line
    char *               pAttrib;      // .attrib line
    Vec_Ptr_t *          vInputs;      // .inputs lines
    Vec_Ptr_t *          vOutputs;     // .outputs lines
    Vec_Ptr_t *          vLatches;     // .latch lines
    Vec_Ptr_t *          vNames;       // .names lines
    Vec_Ptr_t *          vSubckts;     // .subckt lines
    Vec_Ptr_t *          vDelays;      // .delay lines
    Vec_Ptr_t *          vArrivals;    // .input_arrival lines
    Vec_Ptr_t *          vRequireds;   // .output_required lines
    int                  fBlackBox;    // indicates blackbox model
    // the resulting network
    Ntl_Mod_t *          pNtk;   
    // the parent manager
    Ioa_ReadMan_t *      pMan;         
};

struct Ioa_ReadMan_t_
{
    // general info about file
    char *               pFileName;    // the name of the file
    char *               pBuffer;      // the contents of the file
    Vec_Ptr_t *          vLines;       // the line beginnings
    // the results of reading
    Ntl_Man_t *          pDesign;      // the design under construction
    // intermediate storage for models
    Vec_Ptr_t *          vModels;      // vector of models
    Ioa_ReadMod_t *      pLatest;      // the current model
    // current processing info
    Vec_Ptr_t *          vTokens;      // the current tokens
    Vec_Ptr_t *          vTokens2;     // the current tokens
    Vec_Str_t *          vFunc;        // the local function
    // error reporting
    char                 sError[512];  // the error string generated during parsing
    // statistics 
    int                  nTablesRead;  // the number of processed tables
    int                  nTablesLeft;  // the number of dangling tables
};

// static functions
static Ioa_ReadMan_t *   Ioa_ReadAlloc();
static void              Ioa_ReadFree( Ioa_ReadMan_t * p );
static Ioa_ReadMod_t *   Ioa_ReadModAlloc();
static void              Ioa_ReadModFree( Ioa_ReadMod_t * p );
static char *            Ioa_ReadLoadFile( char * pFileName );
static void              Ioa_ReadReadPreparse( Ioa_ReadMan_t * p );
static int               Ioa_ReadReadInterfaces( Ioa_ReadMan_t * p );
static Ntl_Man_t *       Ioa_ReadParse( Ioa_ReadMan_t * p );
static int               Ioa_ReadParseLineModel( Ioa_ReadMod_t * p, char * pLine );
static int               Ioa_ReadParseLineAttrib( Ioa_ReadMod_t * p, char * pLine );
static int               Ioa_ReadParseLineInputs( Ioa_ReadMod_t * p, char * pLine );
static int               Ioa_ReadParseLineOutputs( Ioa_ReadMod_t * p, char * pLine );
static int               Ioa_ReadParseLineLatch( Ioa_ReadMod_t * p, char * pLine );
static int               Ioa_ReadParseLineSubckt( Ioa_ReadMod_t * p, char * pLine );
static int               Ioa_ReadParseLineDelay( Ioa_ReadMod_t * p, char * pLine );
static int               Ioa_ReadParseLineTimes( Ioa_ReadMod_t * p, char * pLine, int fOutput );
static int               Ioa_ReadParseLineNamesBlif( Ioa_ReadMod_t * p, char * pLine );

static int               Ioa_ReadCharIsSpace( char s )   { return s == ' ' || s == '\t' || s == '\r' || s == '\n';             }
static int               Ioa_ReadCharIsSopSymb( char s ) { return s == '0' || s == '1' || s == '-' || s == '\r' || s == '\n';  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads the network from the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ioa_ReadBlif( char * pFileName, int fCheck )
{
    FILE * pFile;
    Ioa_ReadMan_t * p;
    Ntl_Man_t * pDesign;
//    int nNodes;

    // check that the file is available
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Ioa_ReadBlif(): The file is unavailable (absent or open).\n" );
        return 0;
    }
    fclose( pFile );

    // start the file reader
    p = Ioa_ReadAlloc();
    p->pFileName = pFileName;
    p->pBuffer   = Ioa_ReadLoadFile( pFileName );
    if ( p->pBuffer == NULL )
    {
        Ioa_ReadFree( p );
        return NULL;
    }
    // set the design name
    p->pDesign = Ntl_ManAlloc( pFileName );
    p->pDesign->pName = Ntl_ManStoreFileName( p->pDesign, pFileName );
    p->pDesign->pSpec = Ntl_ManStoreName( p->pDesign, pFileName );
    // prepare the file for parsing
    Ioa_ReadReadPreparse( p );
    // parse interfaces of each network
    if ( !Ioa_ReadReadInterfaces( p ) )
    {
        if ( p->sError[0] )
            fprintf( stdout, "%s\n", p->sError );
        Ioa_ReadFree( p );
        return NULL;
    }
    // construct the network
    pDesign = Ioa_ReadParse( p );
    if ( p->sError[0] )
        fprintf( stdout, "%s\n", p->sError );
    if ( pDesign == NULL )
    {
        Ioa_ReadFree( p );
        return NULL;
    }
    p->pDesign = NULL;
    Ioa_ReadFree( p );
// pDesign should be linked to all models of the design

    // make sure that everything is okay with the network structure
    if ( fCheck )
    {
        if ( !Ntl_ManCheck( pDesign ) )
        {
            printf( "Ioa_ReadBlif: The check has failed for design %s.\n", pDesign->pName );
            Ntl_ManFree( pDesign );
            return NULL;
        }

    }
    // transform the design by removing the CO drivers
//    if ( (nNodes = Ntl_ManReconnectCoDrivers(pDesign)) )
//        printf( "The design was transformed by removing %d buf/inv CO drivers.\n", nNodes );
//Ioa_WriteBlif( pDesign, "_temp_.blif" );
    return pDesign;
}

/**Function*************************************************************

  Synopsis    [Allocates the BLIF parsing structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Ioa_ReadMan_t * Ioa_ReadAlloc()
{
    Ioa_ReadMan_t * p;
    p = ALLOC( Ioa_ReadMan_t, 1 );
    memset( p, 0, sizeof(Ioa_ReadMan_t) );
    p->vLines   = Vec_PtrAlloc( 512 );
    p->vModels  = Vec_PtrAlloc( 512 );
    p->vTokens  = Vec_PtrAlloc( 512 );
    p->vTokens2 = Vec_PtrAlloc( 512 );
    p->vFunc    = Vec_StrAlloc( 512 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the BLIF parsing structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ioa_ReadFree( Ioa_ReadMan_t * p )
{
    Ioa_ReadMod_t * pMod;
    int i;
    if ( p->pDesign )
        Ntl_ManFree( p->pDesign );
    if ( p->pBuffer )  
        free( p->pBuffer );
    if ( p->vLines )
        Vec_PtrFree( p->vLines );
    if ( p->vModels )
    {
        Vec_PtrForEachEntry( p->vModels, pMod, i )
            Ioa_ReadModFree( pMod );
        Vec_PtrFree( p->vModels );
    }
    Vec_PtrFree( p->vTokens );
    Vec_PtrFree( p->vTokens2 );
    Vec_StrFree( p->vFunc );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Allocates the BLIF parsing structure for one model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Ioa_ReadMod_t * Ioa_ReadModAlloc()
{
    Ioa_ReadMod_t * p;
    p = ALLOC( Ioa_ReadMod_t, 1 );
    memset( p, 0, sizeof(Ioa_ReadMod_t) );
    p->vInputs  = Vec_PtrAlloc( 512 );
    p->vOutputs = Vec_PtrAlloc( 512 );
    p->vLatches = Vec_PtrAlloc( 512 );
    p->vNames   = Vec_PtrAlloc( 512 );
    p->vSubckts = Vec_PtrAlloc( 512 );
    p->vDelays  = Vec_PtrAlloc( 512 );
    p->vArrivals  = Vec_PtrAlloc( 512 );
    p->vRequireds = Vec_PtrAlloc( 512 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deallocates the BLIF parsing structure for one model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ioa_ReadModFree( Ioa_ReadMod_t * p )
{
    Vec_PtrFree( p->vInputs );
    Vec_PtrFree( p->vOutputs );
    Vec_PtrFree( p->vLatches );
    Vec_PtrFree( p->vNames );
    Vec_PtrFree( p->vSubckts );
    Vec_PtrFree( p->vDelays );
    Vec_PtrFree( p->vArrivals );
    Vec_PtrFree( p->vRequireds );
    free( p );
}



/**Function*************************************************************

  Synopsis    [Counts the number of given chars.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadCountChars( char * pLine, char Char )
{
    char * pCur;
    int Counter = 0;
    for ( pCur = pLine; *pCur; pCur++ )
        if ( *pCur == Char )
            Counter++;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Collects the already split tokens.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ioa_ReadCollectTokens( Vec_Ptr_t * vTokens, char * pInput, char * pOutput )
{
    char * pCur;
    Vec_PtrClear( vTokens );
    for ( pCur = pInput; pCur < pOutput; pCur++ )
    {
        if ( *pCur == 0 )
            continue;
        Vec_PtrPush( vTokens, pCur );
        while ( *++pCur );
    }
}

/**Function*************************************************************

  Synopsis    [Splits the line into tokens.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ioa_ReadSplitIntoTokens( Vec_Ptr_t * vTokens, char * pLine, char Stop )
{
    char * pCur;
    // clear spaces
    for ( pCur = pLine; *pCur != Stop; pCur++ )
        if ( Ioa_ReadCharIsSpace(*pCur) )
            *pCur = 0;
    // collect tokens
    Ioa_ReadCollectTokens( vTokens, pLine, pCur );
}

/**Function*************************************************************

  Synopsis    [Splits the line into tokens.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ioa_ReadSplitIntoTokensAndClear( Vec_Ptr_t * vTokens, char * pLine, char Stop, char Char )
{
    char * pCur;
    // clear spaces
    for ( pCur = pLine; *pCur != Stop; pCur++ )
        if ( Ioa_ReadCharIsSpace(*pCur) || *pCur == Char )
            *pCur = 0;
    // collect tokens
    Ioa_ReadCollectTokens( vTokens, pLine, pCur );
}

/**Function*************************************************************

  Synopsis    [Returns the 1-based number of the line in which the token occurs.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadGetLine( Ioa_ReadMan_t * p, char * pToken )
{
    char * pLine;
    int i;
    Vec_PtrForEachEntry( p->vLines, pLine, i )
        if ( pToken < pLine )
            return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Reads the file into a character buffer.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static char * Ioa_ReadLoadFile( char * pFileName )
{
    FILE * pFile;
    int nFileSize;
    char * pContents;
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Ioa_ReadLoadFile(): The file is unavailable (absent or open).\n" );
        return NULL;
    }
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile ); 
    if ( nFileSize == 0 )
    {
        printf( "Ioa_ReadLoadFile(): The file is empty.\n" );
        return NULL;
    }
    pContents = ALLOC( char, nFileSize + 10 );
    rewind( pFile );
    fread( pContents, nFileSize, 1, pFile );
    fclose( pFile );
    // finish off the file with the spare .end line
    // some benchmarks suddenly break off without this line
    strcpy( pContents + nFileSize, "\n.end\n" );
    return pContents;
}

/**Function*************************************************************

  Synopsis    [Prepares the parsing.]

  Description [Performs several preliminary operations:
  - Cuts the file buffer into separate lines.
  - Removes comments and line extenders.
  - Sorts lines by directives.
  - Estimates the number of objects.
  - Allocates room for the objects.
  - Allocates room for the hash table.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Ioa_ReadReadPreparse( Ioa_ReadMan_t * p )
{
    char * pCur, * pPrev;
    int i, fComment = 0;
    // parse the buffer into lines and remove comments
    Vec_PtrPush( p->vLines, p->pBuffer );
    for ( pCur = p->pBuffer; *pCur; pCur++ )
    {
        if ( *pCur == '\n' )
        {
            *pCur = 0;
//            if ( *(pCur-1) == '\r' )
//                *(pCur-1) = 0;
            fComment = 0;
            Vec_PtrPush( p->vLines, pCur + 1 );
        }
        else if ( *pCur == '#' )
            fComment = 1;
        // remove comments
        if ( fComment )
            *pCur = 0;
    }

    // unfold the line extensions and sort lines by directive
    Vec_PtrForEachEntry( p->vLines, pCur, i )
    {
        if ( *pCur == 0 )
            continue;
        // find previous non-space character
        for ( pPrev = pCur - 2; pPrev >= p->pBuffer; pPrev-- )
            if ( !Ioa_ReadCharIsSpace(*pPrev) )
                break;
        // if it is the line extender, overwrite it with spaces
        if ( *pPrev == '\\' )
        {
            for ( ; *pPrev; pPrev++ )
                *pPrev = ' ';
            *pPrev = ' ';
            continue;
        }
        // skip spaces at the beginning of the line
        while ( Ioa_ReadCharIsSpace(*pCur++) );
        // parse directives
        if ( *(pCur-1) != '.' )
            continue;
        if ( !strncmp(pCur, "names", 5) )
            Vec_PtrPush( p->pLatest->vNames, pCur );
        else if ( !strncmp(pCur, "latch", 5) )
            Vec_PtrPush( p->pLatest->vLatches, pCur );
        else if ( !strncmp(pCur, "inputs", 6) )
            Vec_PtrPush( p->pLatest->vInputs, pCur );
        else if ( !strncmp(pCur, "outputs", 7) )
            Vec_PtrPush( p->pLatest->vOutputs, pCur );
        else if ( !strncmp(pCur, "subckt", 6) )
            Vec_PtrPush( p->pLatest->vSubckts, pCur );
        else if ( !strncmp(pCur, "delay", 5) )
            Vec_PtrPush( p->pLatest->vDelays, pCur );
        else if ( !strncmp(pCur, "input_arrival", 13) )
            Vec_PtrPush( p->pLatest->vArrivals, pCur );
        else if ( !strncmp(pCur, "output_required", 15) )
            Vec_PtrPush( p->pLatest->vRequireds, pCur );
        else if ( !strncmp(pCur, "blackbox", 8) )
            p->pLatest->fBlackBox = 1;
        else if ( !strncmp(pCur, "model", 5) ) 
        {
            p->pLatest = Ioa_ReadModAlloc();
            p->pLatest->pFirst = pCur;
            p->pLatest->pMan = p;
        }
        else if ( !strncmp(pCur, "attrib", 6) ) 
            p->pLatest->pAttrib = pCur;
        else if ( !strncmp(pCur, "end", 3) )
        {
            if ( p->pLatest )
                Vec_PtrPush( p->vModels, p->pLatest );
            p->pLatest = NULL;
        }
        else if ( !strncmp(pCur, "exdc", 4) )
        {
            fprintf( stdout, "Line %d: Skipping EXDC network.\n", Ioa_ReadGetLine(p, pCur) );
            break;
        }
        else if ( !strncmp(pCur, "no_merge", 8) ) 
        {
        }
        else if ( !strncmp(pCur, "attribute", 9) ) 
        {
        }
        else if ( !strncmp(pCur, "input_required", 14) ) 
        {
        }
        else if ( !strncmp(pCur, "output_arrival", 14) ) 
        {
        }
        else
        {
            pCur--;
            if ( pCur[strlen(pCur)-1] == '\r' )
                pCur[strlen(pCur)-1] = 0;
            fprintf( stdout, "Line %d: Skipping line \"%s\".\n", Ioa_ReadGetLine(p, pCur), pCur );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Parses interfaces of the models.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadReadInterfaces( Ioa_ReadMan_t * p )
{
    Ioa_ReadMod_t * pMod;
    char * pLine;
    int i, k;
    // iterate through the models
    Vec_PtrForEachEntry( p->vModels, pMod, i )
    {
        // parse the model
        if ( !Ioa_ReadParseLineModel( pMod, pMod->pFirst ) )
            return 0;
        // parse the model attributes
        if ( pMod->pAttrib && !Ioa_ReadParseLineAttrib( pMod, pMod->pAttrib ) )
            return 0;
        // parse the inputs
        Vec_PtrForEachEntry( pMod->vInputs, pLine, k )
            if ( !Ioa_ReadParseLineInputs( pMod, pLine ) )
                return 0;
        // parse the outputs
        Vec_PtrForEachEntry( pMod->vOutputs, pLine, k )
            if ( !Ioa_ReadParseLineOutputs( pMod, pLine ) )
                return 0;
        // parse the delay info
        Vec_PtrForEachEntry( pMod->vDelays, pLine, k )
            if ( !Ioa_ReadParseLineDelay( pMod, pLine ) )
                return 0;
        Vec_PtrForEachEntry( pMod->vArrivals, pLine, k )
            if ( !Ioa_ReadParseLineTimes( pMod, pLine, 0 ) )
                return 0;
        Vec_PtrForEachEntry( pMod->vRequireds, pLine, k )
            if ( !Ioa_ReadParseLineTimes( pMod, pLine, 1 ) )
                return 0;
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Ntl_Man_t * Ioa_ReadParse( Ioa_ReadMan_t * p )
{
    Ntl_Man_t * pDesign;
    Ioa_ReadMod_t * pMod;
    char * pLine;
    int i, k;
    // iterate through the models
    Vec_PtrForEachEntry( p->vModels, pMod, i )
    {
        // parse the latches
        Vec_PtrForEachEntry( pMod->vLatches, pLine, k )
            if ( !Ioa_ReadParseLineLatch( pMod, pLine ) )
                return NULL;
        // parse the nodes
        Vec_PtrForEachEntry( pMod->vNames, pLine, k )
            if ( !Ioa_ReadParseLineNamesBlif( pMod, pLine ) )
                return NULL;
        // parse the subcircuits
        Vec_PtrForEachEntry( pMod->vSubckts, pLine, k )
            if ( !Ioa_ReadParseLineSubckt( pMod, pLine ) )
                return NULL;
        // finalize the network
        Ntl_ModelFixNonDrivenNets( pMod->pNtk );
    }
    if ( i == 0 )
        return NULL;
    // update the design name
    pMod = Vec_PtrEntry( p->vModels, 0 );
    p->pDesign->pName = Ntl_ManStoreName( p->pDesign, pMod->pNtk->pName );
    // return the network
    pDesign = p->pDesign;
    p->pDesign = NULL;
    return pDesign;
}

/**Function*************************************************************

  Synopsis    [Parses the model line.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadParseLineModel( Ioa_ReadMod_t * p, char * pLine )
{
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    char * pToken;
    Ioa_ReadSplitIntoTokens( vTokens, pLine, '\0' );
    pToken = Vec_PtrEntry( vTokens, 0 );
    assert( !strcmp(pToken, "model") );
    if ( Vec_PtrSize(vTokens) != 2 )
    {
        sprintf( p->pMan->sError, "Line %d: The number of entries (%d) in .model line is different from two.", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrSize(vTokens) );
        return 0;
    }
    p->pNtk = Ntl_ModelAlloc( p->pMan->pDesign, Vec_PtrEntry(vTokens, 1) );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses the model line.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadParseLineAttrib( Ioa_ReadMod_t * p, char * pLine )
{
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    char * pToken;
    Ioa_ReadSplitIntoTokens( vTokens, pLine, '\0' );
    pToken = Vec_PtrEntry( vTokens, 0 );
    assert( !strncmp(pToken, "attrib", 6) );
/*
    if ( Vec_PtrSize(vTokens) != 2 )
    {
        sprintf( p->pMan->sError, "Line %d: The number of entries (%d) in .attrib line is different from two.", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrSize(vTokens) );
        return 0;
    }
    if ( strcmp( Vec_PtrEntry(vTokens, 1), "keep" ) == 0 )
        p->pNtk->fKeep = 1;
    else
    {
        sprintf( p->pMan->sError, "Line %d: Unknown attribute (%s) in the .attrib line of model %s.", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntry(vTokens, 1), p->pNtk->pName );
        return 0;
    }
*/
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses the inputs line.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadParseLineInputs( Ioa_ReadMod_t * p, char * pLine )
{
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pObj;
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    char * pToken;
    int i;
    Ioa_ReadSplitIntoTokens( vTokens, pLine, '\0' );
    pToken = Vec_PtrEntry(vTokens, 0);
    assert( !strcmp(pToken, "inputs") );
    Vec_PtrForEachEntryStart( vTokens, pToken, i, 1 )
    {
        pObj = Ntl_ModelCreatePi( p->pNtk );
        pNet = Ntl_ModelFindOrCreateNet( p->pNtk, pToken );
        if ( !Ntl_ModelSetNetDriver( pObj, pNet ) )
        {
            sprintf( p->pMan->sError, "Line %d: Net %s already has a driver.", Ioa_ReadGetLine(p->pMan, pToken), pNet->pName );
            return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses the outputs line.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadParseLineOutputs( Ioa_ReadMod_t * p, char * pLine )
{
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pObj;
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    char * pToken;
    int i;
    Ioa_ReadSplitIntoTokens( vTokens, pLine, '\0' );
    pToken = Vec_PtrEntry(vTokens, 0);
    assert( !strcmp(pToken, "outputs") );
    Vec_PtrForEachEntryStart( vTokens, pToken, i, 1 )
    {
        pNet = Ntl_ModelFindOrCreateNet( p->pNtk, pToken );
        pObj = Ntl_ModelCreatePo( p->pNtk, pNet );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses the latches line.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadParseLineLatch( Ioa_ReadMod_t * p, char * pLine )
{
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    Ntl_Net_t * pNetLi, * pNetLo;
    Ntl_Obj_t * pObj;
    char * pToken, * pNameLi, * pNameLo;
    int Init, Class;
    Ioa_ReadSplitIntoTokens( vTokens, pLine, '\0' );
    pToken = Vec_PtrEntry(vTokens,0);
    assert( !strcmp(pToken, "latch") );
    if ( Vec_PtrSize(vTokens) < 3 )
    {
        sprintf( p->pMan->sError, "Line %d: Latch does not have input name and output name.", Ioa_ReadGetLine(p->pMan, pToken) );
        return 0;
    }
    // create latch
    pNameLi = Vec_PtrEntry( vTokens, 1 );
    pNameLo = Vec_PtrEntry( vTokens, 2 );
    pNetLi  = Ntl_ModelFindOrCreateNet( p->pNtk, pNameLi );
    pNetLo  = Ntl_ModelFindOrCreateNet( p->pNtk, pNameLo );
    pObj    = Ntl_ModelCreateLatch( p->pNtk );
    pObj->pFanio[0] = pNetLi;
    if ( !Ntl_ModelSetNetDriver( pObj, pNetLo ) )
    {
        sprintf( p->pMan->sError, "Line %d: Net %s already has a driver.", Ioa_ReadGetLine(p->pMan, pToken), pNetLo->pName );
        return 0;
    }
    // get initial value
    if ( Vec_PtrSize(vTokens) > 3 )
        Init = atoi( Vec_PtrEntry(vTokens,Vec_PtrSize(vTokens)-1) );
    else
        Init = 2;
    if ( Init < 0 || Init > 2 )
    {
        sprintf( p->pMan->sError, "Line %d: Initial state of the latch is incorrect \"%s\".", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntry(vTokens,3) );
        return 0;
    }
    // get the register class
    if ( Vec_PtrSize(vTokens) == 6 )
        Class = atoi( Vec_PtrEntry(vTokens,3) );
    else
        Class = 0;
    if ( Class < 0 || Class > (1<<24) )
    {
        sprintf( p->pMan->sError, "Line %d: Class of the latch is incorrect \"%s\".", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntry(vTokens,4) );
        return 0;
    }
    pObj->LatchId = (Class << 2) | Init;
    // get the clock
    if ( Vec_PtrSize(vTokens) == 5 || Vec_PtrSize(vTokens) == 6 )
    {
        pToken = Vec_PtrEntry(vTokens,Vec_PtrSize(vTokens)-2);
        pNetLi = Ntl_ModelFindOrCreateNet( p->pNtk, pToken );
//        pObj->pFanio[1] = pNetLi;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses the subckt line.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadParseLineSubckt( Ioa_ReadMod_t * p, char * pLine )
{
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    Ntl_Mod_t * pModel;
    Ntl_Obj_t * pBox, * pTerm;
    Ntl_Net_t * pNet;
    char * pToken, * pName, ** ppNames;
    int nEquals, i, k;

    // split the line into tokens
    nEquals = Ioa_ReadCountChars( pLine, '=' );
    Ioa_ReadSplitIntoTokensAndClear( vTokens, pLine, '\0', '=' );
    pToken = Vec_PtrEntry(vTokens,0);
    assert( !strcmp(pToken, "subckt") );

    // get the model for this box
    pName = Vec_PtrEntry(vTokens,1);
    pModel = Ntl_ManFindModel( p->pMan->pDesign, pName );
    if ( pModel == NULL )
    {
        sprintf( p->pMan->sError, "Line %d: Cannot find the model for subcircuit %s.", Ioa_ReadGetLine(p->pMan, pToken), pName );
        return 0;
    }
/*
    // temporary fix for splitting the .subckt line
    if ( nEquals < Ntl_ModelPiNum(pModel) + Ntl_ModelPoNum(pModel) )
    { 
        Vec_Ptr_t * vTokens2 = Vec_PtrAlloc( 10 );
        // get one additional token
        pToken = Vec_PtrEntry( vTokens, Vec_PtrSize(vTokens) - 1 );
        for ( ; *pToken; pToken++ );
        for ( ; *pToken == 0; pToken++ );
        Ioa_ReadSplitIntoTokensAndClear( vTokens2, pToken, '\0', '=' );
//        assert( Vec_PtrSize( vTokens2 ) == 2 );
        Vec_PtrForEachEntry( vTokens2, pToken, i )
            Vec_PtrPush( vTokens, pToken );
        nEquals += Vec_PtrSize(vTokens2)/2;
        Vec_PtrFree( vTokens2 );
    }
*/    
    // check if the number of tokens is correct
    if ( nEquals != Ntl_ModelPiNum(pModel) + Ntl_ModelPoNum(pModel) )
    {
        sprintf( p->pMan->sError, "Line %d: The number of ports (%d) in .subckt %s differs from the sum of PIs and POs of the model (%d).", 
            Ioa_ReadGetLine(p->pMan, pToken), nEquals, pName, Ntl_ModelPiNum(pModel) + Ntl_ModelPoNum(pModel) );
        return 0;
    }

    // get the names
    ppNames = (char **)Vec_PtrArray(vTokens) + 2;

    // create the box with these terminals
    pBox = Ntl_ModelCreateBox( p->pNtk, Ntl_ModelPiNum(pModel), Ntl_ModelPoNum(pModel) );
    pBox->pImplem = pModel;
    Ntl_ModelForEachPi( pModel, pTerm, i )
    {
        // find this terminal among the formal inputs of the subcircuit
        pName = Ntl_ObjFanout0(pTerm)->pName;
        for ( k = 0; k < nEquals; k++ )
            if ( !strcmp( ppNames[2*k], pName ) )
                break;
        if ( k == nEquals )
        {
            sprintf( p->pMan->sError, "Line %d: Cannot find PI \"%s\" of the model \"%s\" as a formal input of the subcircuit.", 
                Ioa_ReadGetLine(p->pMan, pToken), pName, pModel->pName );
            return 0;
        }
        // create the BI with the actual name
        pNet = Ntl_ModelFindOrCreateNet( p->pNtk, ppNames[2*k+1] );
        Ntl_ObjSetFanin( pBox, pNet, i );
    }
    Ntl_ModelForEachPo( pModel, pTerm, i )
    {
        // find this terminal among the formal outputs of the subcircuit
        pName = Ntl_ObjFanin0(pTerm)->pName;
        for ( k = 0; k < nEquals; k++ )
            if ( !strcmp( ppNames[2*k], pName ) )
                break;
        if ( k == nEquals )
        {
            sprintf( p->pMan->sError, "Line %d: Cannot find PO \"%s\" of the model \"%s\" as a formal output of the subcircuit.", 
                Ioa_ReadGetLine(p->pMan, pToken), pName, pModel->pName );
            return 0;
        }
        // create the BI with the actual name
        pNet = Ntl_ModelFindOrCreateNet( p->pNtk, ppNames[2*k+1] );
        Ntl_ObjSetFanout( pBox, pNet, i );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses the subckt line.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadParseLineDelay( Ioa_ReadMod_t * p, char * pLine )
{
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    int RetValue1, RetValue2, Number1, Number2, Temp;
    char * pToken, * pTokenNum;
    float Delay;
    assert( sizeof(float) == sizeof(int) );
    Ioa_ReadSplitIntoTokens( vTokens, pLine, '\0' );
    pToken = Vec_PtrEntry(vTokens,0);
    assert( !strcmp(pToken, "delay") );
    if ( Vec_PtrSize(vTokens) < 2 && Vec_PtrSize(vTokens) > 4 )
    {
        sprintf( p->pMan->sError, "Line %d: Delay line does not have a valid number of parameters (1, 2, or 3).", Ioa_ReadGetLine(p->pMan, pToken) );
        return 0;
    }
    // find the delay number
    pTokenNum = Vec_PtrEntryLast(vTokens);
    Delay = atof( pTokenNum );
    if ( Delay == 0.0 && pTokenNum[0] != '0' )
    {
        sprintf( p->pMan->sError, "Line %d: Delay value (%s) appears to be invalid.", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntryLast(vTokens) );
        return 0;
    }
    // find the PI/PO numbers
    RetValue1 = 0; Number1 = -1;
    if ( Vec_PtrSize(vTokens) > 2 )
    {
        RetValue1 = Ntl_ModelFindPioNumber( p->pNtk, Vec_PtrEntry(vTokens, 1), &Number1 );
        if ( RetValue1 == 0 )
        {
            sprintf( p->pMan->sError, "Line %d: Cannot find signal \"%s\" among PIs/POs.", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntry(vTokens, 1) );
            return 0;
        }
    }
    RetValue2 = 0; Number2 = -1;
    if ( Vec_PtrSize(vTokens) > 3 )
    {
        RetValue2 = Ntl_ModelFindPioNumber( p->pNtk, Vec_PtrEntry(vTokens, 2), &Number2 );
        if ( RetValue2 == 0 )
        {
            sprintf( p->pMan->sError, "Line %d: Cannot find signal \"%s\" among PIs/POs.", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntry(vTokens, 2) );
            return 0;
        }
    }
    if ( RetValue1 == RetValue2 && RetValue1 )
    {
        sprintf( p->pMan->sError, "Line %d: Both signals \"%s\" and \"%s\" listed appear to be PIs or POs.", 
            Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntry(vTokens, 1), Vec_PtrEntry(vTokens, 2) );
        return 0;
    }
    if ( RetValue2 < RetValue1 )
    {
        Temp = RetValue2; RetValue2 = RetValue1; RetValue1 = Temp;
        Temp = Number2;   Number2 = Number1;     Number1 = Temp;
    }
    assert( RetValue1 == 0 || RetValue1 == -1 );
    assert( RetValue2 == 0 || RetValue2 ==  1 );
    // store the values
    if ( p->pNtk->vDelays == NULL )
        p->pNtk->vDelays = Vec_IntAlloc( 100 );
    Vec_IntPush( p->pNtk->vDelays, Number1 );
    Vec_IntPush( p->pNtk->vDelays, Number2 );
    Vec_IntPush( p->pNtk->vDelays, Aig_Float2Int(Delay) );        
    return 1;
}

/**Function*************************************************************

  Synopsis    [Parses the subckt line.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadParseLineTimes( Ioa_ReadMod_t * p, char * pLine, int fOutput )
{
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    int RetValue, Number;
    char * pToken, * pTokenNum;
    float Delay;
    assert( sizeof(float) == sizeof(int) );
    Ioa_ReadSplitIntoTokens( vTokens, pLine, '\0' );
    pToken = Vec_PtrEntry(vTokens,0);
    if ( fOutput )
        assert( !strcmp(pToken, "output_required") );
    else
        assert( !strcmp(pToken, "input_arrival") );
    if ( Vec_PtrSize(vTokens) != 3 )
    {
        sprintf( p->pMan->sError, "Line %d: Delay line does not have a valid number of parameters (3).", Ioa_ReadGetLine(p->pMan, pToken) );
        return 0;
    }
    // find the delay number
    pTokenNum = Vec_PtrEntryLast(vTokens);
    if ( !strcmp( pTokenNum, "-inf" ) )
        Delay = -TIM_ETERNITY;
    else if ( !strcmp( pTokenNum, "inf" ) ) 
        Delay = TIM_ETERNITY;
    else
        Delay = atof( pTokenNum );
    if ( Delay == 0.0 && pTokenNum[0] != '0' )
    {
        sprintf( p->pMan->sError, "Line %d: Delay value (%s) appears to be invalid.", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntryLast(vTokens) );
        return 0;
    }
    // find the PI/PO numbers
    if ( fOutput )
    {
        RetValue = Ntl_ModelFindPioNumber( p->pNtk, Vec_PtrEntry(vTokens, 1), &Number );
        if ( RetValue == 0 )
        {
            sprintf( p->pMan->sError, "Line %d: Cannot find signal \"%s\" among POs.", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntry(vTokens, 1) );
            return 0;
        }
        // store the values
        if ( p->pNtk->vRequireds == NULL )
            p->pNtk->vRequireds = Vec_IntAlloc( 100 );
        Vec_IntPush( p->pNtk->vRequireds, Number );
        Vec_IntPush( p->pNtk->vRequireds, Aig_Float2Int(Delay) );        
    }
    else
    {
        RetValue = Ntl_ModelFindPioNumber( p->pNtk, Vec_PtrEntry(vTokens, 1), &Number );
        if ( RetValue == 0 )
        {
            sprintf( p->pMan->sError, "Line %d: Cannot find signal \"%s\" among PIs.", Ioa_ReadGetLine(p->pMan, pToken), Vec_PtrEntry(vTokens, 1) );
            return 0;
        }
        // store the values
        if ( p->pNtk->vArrivals == NULL )
            p->pNtk->vArrivals = Vec_IntAlloc( 100 );
        Vec_IntPush( p->pNtk->vArrivals, Number );
        Vec_IntPush( p->pNtk->vArrivals, Aig_Float2Int(Delay) );        
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Constructs the SOP cover from the file parsing info.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static char * Ioa_ReadParseTableBlif( Ioa_ReadMod_t * p, char * pTable, int nFanins )
{
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    Vec_Str_t * vFunc = p->pMan->vFunc;
    char * pProduct, * pOutput;
    int i, Polarity = -1;

    p->pMan->nTablesRead++;
    // get the tokens
    Ioa_ReadSplitIntoTokens( vTokens, pTable, '.' );
    if ( Vec_PtrSize(vTokens) == 0 )
        return Ntl_ManStoreSop( p->pMan->pDesign->pMemSops, " 0\n" );
    if ( Vec_PtrSize(vTokens) == 1 )
    {
        pOutput = Vec_PtrEntry( vTokens, 0 );
        if ( ((pOutput[0] - '0') & 0x8E) || pOutput[1] )
        {
            sprintf( p->pMan->sError, "Line %d: Constant table has wrong output value \"%s\".", Ioa_ReadGetLine(p->pMan, pOutput), pOutput );
            return NULL;
        }
        return Ntl_ManStoreSop( p->pMan->pDesign->pMemSops, (pOutput[0] == '0') ? " 0\n" : " 1\n" );
    }
    pProduct = Vec_PtrEntry( vTokens, 0 );
    if ( Vec_PtrSize(vTokens) % 2 == 1 )
    {
        sprintf( p->pMan->sError, "Line %d: Table has odd number of tokens (%d).", Ioa_ReadGetLine(p->pMan, pProduct), Vec_PtrSize(vTokens) );
        return NULL;
    }
    // parse the table
    Vec_StrClear( vFunc );
    for ( i = 0; i < Vec_PtrSize(vTokens)/2; i++ )
    {
        pProduct = Vec_PtrEntry( vTokens, 2*i + 0 );
        pOutput  = Vec_PtrEntry( vTokens, 2*i + 1 );
        if ( strlen(pProduct) != (unsigned)nFanins )
        {
            sprintf( p->pMan->sError, "Line %d: Cube \"%s\" has size different from the fanin count (%d).", Ioa_ReadGetLine(p->pMan, pProduct), pProduct, nFanins );
            return NULL;
        }
        if ( ((pOutput[0] - '0') & 0x8E) || pOutput[1] )
        {
            sprintf( p->pMan->sError, "Line %d: Output value \"%s\" is incorrect.", Ioa_ReadGetLine(p->pMan, pProduct), pOutput );
            return NULL;
        }
        if ( Polarity == -1 )
            Polarity = pOutput[0] - '0';
        else if ( Polarity != pOutput[0] - '0' )
        {
            sprintf( p->pMan->sError, "Line %d: Output value \"%s\" differs from the value in the first line of the table (%d).", Ioa_ReadGetLine(p->pMan, pProduct), pOutput, Polarity );
            return NULL;
        }
        // parse one product 
        Vec_StrAppend( vFunc, pProduct );
        Vec_StrPush( vFunc, ' ' );
        Vec_StrPush( vFunc, pOutput[0] );
        Vec_StrPush( vFunc, '\n' );
    }
    Vec_StrPush( vFunc, '\0' );
    return Vec_StrArray( vFunc );
}

/**Function*************************************************************

  Synopsis    [Parses the nodes line.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Ioa_ReadParseLineNamesBlif( Ioa_ReadMod_t * p, char * pLine )
{
    Vec_Ptr_t * vTokens = p->pMan->vTokens;
    Ntl_Obj_t * pNode;
    Ntl_Net_t * pNetOut, * pNetIn;
    char * pNameOut, * pNameIn;
    int i;
    Ioa_ReadSplitIntoTokens( vTokens, pLine, '\0' );
    // parse the mapped node
//    if ( !strcmp(Vec_PtrEntry(vTokens,0), "gate") )
//        return Ioa_ReadParseLineGateBlif( p, vTokens );
    // parse the regular name line
    assert( !strcmp(Vec_PtrEntry(vTokens,0), "names") );
    pNameOut = Vec_PtrEntryLast( vTokens );
    pNetOut = Ntl_ModelFindOrCreateNet( p->pNtk, pNameOut );
    // create fanins
    pNode = Ntl_ModelCreateNode( p->pNtk, Vec_PtrSize(vTokens) - 2 );
    for ( i = 0; i < Vec_PtrSize(vTokens) - 2; i++ )
    {
        pNameIn = Vec_PtrEntry(vTokens, i+1);
        pNetIn = Ntl_ModelFindOrCreateNet( p->pNtk, pNameIn );
        Ntl_ObjSetFanin( pNode, pNetIn, i );
    }
    if ( !Ntl_ModelSetNetDriver( pNode, pNetOut ) )
    {
        sprintf( p->pMan->sError, "Line %d: Signal \"%s\" is defined more than once.", Ioa_ReadGetLine(p->pMan, pNameOut), pNameOut );
        return 0;
    }
    // parse the table of this node
    pNode->pSop = Ioa_ReadParseTableBlif( p, pNameOut + strlen(pNameOut), pNode->nFanins );
    if ( pNode->pSop == NULL )
        return 0;
    pNode->pSop = Ntl_ManStoreSop( p->pNtk->pMan->pMemSops, pNode->pSop );
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


