/**CFile****************************************************************

  FileName    [ioReadBlif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to read BLIF files.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioReadBlif.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Io_ReadBlif_t_        Io_ReadBlif_t;   // all reading info
struct Io_ReadBlif_t_
{
    // general info about file
    char *              pFileName;    // the name of the file
    Extra_FileReader_t* pReader;      // the input file reader
    // current processing info
    Abc_Ntk_t *         pNtk;         // the primary network
    Abc_Ntk_t *         pNtkExdc;     // the exdc network
    int                 fParsingExdc; // this flag is on, when we are parsing EXDC network
    int                 LineCur;      // the line currently parsed
    // temporary storage for tokens
    Vec_Ptr_t *         vNewTokens;   // the temporary storage for the tokens
    Vec_Str_t *         vCubes;       // the temporary storage for the tokens
    // the error message
    FILE *              Output;       // the output stream
    char                sError[1000]; // the error string generated during parsing
};

static Io_ReadBlif_t * Io_ReadBlifFile( char * pFileName );
static void Io_ReadBlifFree( Io_ReadBlif_t * p );
static void Io_ReadBlifPrintErrorMessage( Io_ReadBlif_t * p );
static Vec_Ptr_t * Io_ReadBlifGetTokens( Io_ReadBlif_t * p );
static Abc_Ntk_t * Io_ReadBlifNetwork( Io_ReadBlif_t * p );

static int Io_ReadBlifNetworkInputs( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens );
static int Io_ReadBlifNetworkOutputs( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens );
static int Io_ReadBlifNetworkLatch( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens );
static int Io_ReadBlifNetworkNames( Io_ReadBlif_t * p, Vec_Ptr_t ** pvTokens );
static int Io_ReadBlifNetworkInputArrival( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens );
static int Io_ReadBlifNetworkDefaultInputArrival( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Read the network from BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadBlif( char * pFileName, int fCheck )
{
    Io_ReadBlif_t * p;
    Abc_Ntk_t * pNtk, * pNtkExdc;

    // start the file
    p = Io_ReadBlifFile( pFileName );
    if ( p == NULL )
        return NULL;

    // read the network
    pNtk = Io_ReadBlifNetwork( p );
    if ( pNtk == NULL )
    {
        Io_ReadBlifFree( p );
        return NULL;
    }
    Abc_NtkTimeInitialize( pNtk );

    // read the EXDC network
    if ( p->fParsingExdc )
    {
        pNtkExdc = Io_ReadBlifNetwork( p );
        if ( pNtkExdc == NULL )
        {
            Abc_NtkDelete( pNtk );
            Io_ReadBlifFree( p );
            return NULL;
        }
        pNtk->pExdc = pNtkExdc;
    }
    Io_ReadBlifFree( p );

    // make sure that everything is okay with the network structure
    if ( fCheck && !Abc_NtkCheck( pNtk ) )
    {
        printf( "Io_ReadBlif: The network check has failed.\n" );
        Abc_NtkDelete( pNtk );
        return NULL;
    }
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Starts the reading data structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Io_ReadBlif_t * Io_ReadBlifFile( char * pFileName )
{
    Extra_FileReader_t * pReader;
    Io_ReadBlif_t * p;

    // start the reader
    pReader = Extra_FileReaderAlloc( pFileName, "#", "\n", " \t\r" );
    if ( pReader == NULL )
        return NULL;

    // start the reading data structure
    p = ALLOC( Io_ReadBlif_t, 1 );
    memset( p, 0, sizeof(Io_ReadBlif_t) );
    p->pFileName  = pFileName;
    p->pReader    = pReader;
    p->Output     = stdout;
    p->vNewTokens = Vec_PtrAlloc( 100 );
    p->vCubes     = Vec_StrAlloc( 100 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the data structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_ReadBlifFree( Io_ReadBlif_t * p )
{
    Extra_FileReaderFree( p->pReader );
    Vec_PtrFree( p->vNewTokens );
    Vec_StrFree( p->vCubes );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Prints the error message including the file name and line number.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_ReadBlifPrintErrorMessage( Io_ReadBlif_t * p )
{
    if ( p->LineCur == 0 ) // the line number is not given
        fprintf( p->Output, "%s: %s\n", p->pFileName, p->sError );
    else // print the error message with the line number
        fprintf( p->Output, "%s (line %d): %s\n", p->pFileName, p->LineCur, p->sError );
}

/**Function*************************************************************

  Synopsis    [Gets the tokens taking into account the line breaks.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Io_ReadBlifGetTokens( Io_ReadBlif_t * p )
{
    Vec_Ptr_t * vTokens;
    char * pLastToken;
    int i;

    // get rid of the old tokens
    if ( p->vNewTokens->nSize > 0 )
    {
        for ( i = 0; i < p->vNewTokens->nSize; i++ )
            free( p->vNewTokens->pArray[i] );
        p->vNewTokens->nSize = 0;
    }

    // get the new tokens
    vTokens = Extra_FileReaderGetTokens(p->pReader);
    if ( vTokens == NULL )
        return vTokens;

    // check if there is a transfer to another line
    pLastToken = vTokens->pArray[vTokens->nSize - 1];
    if ( pLastToken[ strlen(pLastToken)-1 ] != '\\' )
        return vTokens;

    // remove the slash
    pLastToken[ strlen(pLastToken)-1 ] = 0;
    if ( pLastToken[0] == 0 )
        vTokens->nSize--;
    // load them into the new array
    for ( i = 0; i < vTokens->nSize; i++ )
        Vec_PtrPush( p->vNewTokens, util_strsav(vTokens->pArray[i]) );

    // load as long as there is the line break
    while ( 1 )
    {
        // get the new tokens
        vTokens = Extra_FileReaderGetTokens(p->pReader);
        if ( vTokens->nSize == 0 )
            return p->vNewTokens;
        // check if there is a transfer to another line
        pLastToken = vTokens->pArray[vTokens->nSize - 1];
        if ( pLastToken[ strlen(pLastToken)-1 ] == '\\' )
        {
            // remove the slash
            pLastToken[ strlen(pLastToken)-1 ] = 0;
            if ( pLastToken[0] == 0 )
                vTokens->nSize--;
            // load them into the new array
            for ( i = 0; i < vTokens->nSize; i++ )
                Vec_PtrPush( p->vNewTokens, util_strsav(vTokens->pArray[i]) );
            continue;
        }
        // otherwise, load them and break
        for ( i = 0; i < vTokens->nSize; i++ )
            Vec_PtrPush( p->vNewTokens, util_strsav(vTokens->pArray[i]) );
        break;
    }
    return p->vNewTokens;
}


/**Function*************************************************************

  Synopsis    [Reads the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadBlifNetwork( Io_ReadBlif_t * p )
{
    ProgressBar * pProgress;
    Vec_Ptr_t * vTokens;
    char * pModelName;
    int iLine, fTokensReady, fStatus;

    // read the model name
    if ( !p->fParsingExdc )
    {
        // read the model name
        vTokens = Io_ReadBlifGetTokens(p);
        if ( vTokens == NULL || strcmp( vTokens->pArray[0], ".model" ) )
        {
            p->LineCur = 0;
            sprintf( p->sError, "Wrong input file format." );
            Io_ReadBlifPrintErrorMessage( p );
            return NULL;
        }
        pModelName = vTokens->pArray[1];
        // allocate the empty network
        p->pNtk = Abc_NtkAlloc( ABC_NTK_NETLIST );
        p->pNtk->pName = util_strsav( pModelName );
        p->pNtk->pSpec = util_strsav( p->pFileName );
    }
    else
        p->pNtk = Abc_NtkAlloc( ABC_NTK_NETLIST );

    // read the inputs/outputs
    pProgress = Extra_ProgressBarStart( stdout, Extra_FileReaderGetFileSize(p->pReader) );
    fTokensReady = fStatus = 0;
    for ( iLine = 0; fTokensReady || (vTokens = Io_ReadBlifGetTokens(p)); iLine++ )
    {
        if ( iLine % 1000 == 0 )
        Extra_ProgressBarUpdate( pProgress, Extra_FileReaderGetCurPosition(p->pReader), NULL );

        // consider different line types
        fTokensReady = 0;
        if ( !strcmp( vTokens->pArray[0], ".names" ) )
            { fStatus = Io_ReadBlifNetworkNames( p, &vTokens ); fTokensReady = 1; }
        else if ( !strcmp( vTokens->pArray[0], ".latch" ) )
            fStatus = Io_ReadBlifNetworkLatch( p, vTokens );
        else if ( !strcmp( vTokens->pArray[0], ".inputs" ) )
            fStatus = Io_ReadBlifNetworkInputs( p, vTokens );
        else if ( !strcmp( vTokens->pArray[0], ".outputs" ) )
            fStatus = Io_ReadBlifNetworkOutputs( p, vTokens );
        else if ( !strcmp( vTokens->pArray[0], ".input_arrival" ) )
            fStatus = Io_ReadBlifNetworkInputArrival( p, vTokens );
        else if ( !strcmp( vTokens->pArray[0], ".default_input_arrival" ) )
            fStatus = Io_ReadBlifNetworkDefaultInputArrival( p, vTokens );
        else if ( !strcmp( vTokens->pArray[0], ".exdc" ) )
            { p->fParsingExdc = 1; break; }
        else if ( !strcmp( vTokens->pArray[0], ".end" ) )
            break;
        else
            printf( "%s (line %d): Skipping directive \"%s\".\n", p->pFileName, 
                Extra_FileReaderGetLineNumber(p->pReader, 0), vTokens->pArray[0] );
        if ( vTokens == NULL ) // some files do not have ".end" in the end
            break;
        if ( fStatus == 1 )
            return NULL;
    }
    Extra_ProgressBarStop( pProgress );
    Io_ReadSetNonDrivenNets( p->pNtk );
    return p->pNtk;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_ReadBlifNetworkInputs( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens )
{
    Abc_Ntk_t * pNtk = p->pNtk;
    Abc_Obj_t * pNet;
    int i;
    for ( i = 1; i < vTokens->nSize; i++ )
    {
        pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[i] );
        if ( Abc_ObjIsPi(pNet) )
            printf( "Warning: PI net \"%s\" appears twice in the list.\n", vTokens->pArray[i] );
        else
            Abc_NtkMarkNetPi( pNet );
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_ReadBlifNetworkOutputs( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens )
{
    Abc_Ntk_t * pNtk = p->pNtk;
    Abc_Obj_t * pNet;
    int i;
    for ( i = 1; i < vTokens->nSize; i++ )
    {
        pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[i] );
        if ( Abc_ObjIsPo(pNet) )
            printf( "Warning: PO net \"%s\" appears twice in the list.\n", vTokens->pArray[i] );
        else
            Abc_NtkMarkNetPo( pNet );
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_ReadBlifNetworkLatch( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens )
{
    Abc_Ntk_t * pNtk = p->pNtk;
    Abc_Obj_t * pNet, * pLatch;
    int ResetValue;

    if ( vTokens->nSize < 3 )
    {
        p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
        sprintf( p->sError, "The .latch line does not have enough tokens." );
        Io_ReadBlifPrintErrorMessage( p );
        return 1;
    }
    // create a new node and add it to the network
    pLatch = Abc_NtkCreateLatch( pNtk );
    // create the LO (PI)
    pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[2] );
    Abc_ObjAddFanin( pNet, pLatch );
    Abc_ObjSetSubtype( pNet, ABC_OBJ_SUBTYPE_LO );
    // save the LI (PO)
    pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[1] );
    Abc_ObjAddFanin( pLatch, pNet );
    Abc_ObjSetSubtype( pNet, ABC_OBJ_SUBTYPE_LI );
    // get the latch reset value
    if ( vTokens->nSize == 3 )
        ResetValue = 2;
    else
    {
        ResetValue = atoi(vTokens->pArray[3]);
        if ( ResetValue != 0 && ResetValue != 1 && ResetValue != 2 )
        {
            p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
            sprintf( p->sError, "The .latch line has an unknown reset value (%s).", vTokens->pArray[3] );
            Io_ReadBlifPrintErrorMessage( p );
            return 1;
        }
    }
    Abc_ObjSetData( pLatch, (void *)ResetValue );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_ReadBlifNetworkNames( Io_ReadBlif_t * p, Vec_Ptr_t ** pvTokens )
{
    Vec_Ptr_t * vTokens = *pvTokens;
    Abc_Ntk_t * pNtk = p->pNtk;
    Abc_Obj_t * pNet, * pNode;
    char * pToken, Char;
    int i, nFanins;

    // create a new node and add it to the network
    pNode = Abc_NtkCreateNode( pNtk );
    if ( vTokens->nSize < 2 )
    {
        p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
        sprintf( p->sError, "The .names line has less than two tokens." );
        Io_ReadBlifPrintErrorMessage( p );
        return 1;
    }
    // go through the nets 
    for ( i = 1; i < vTokens->nSize - 1; i++ )
    {
        pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[i] );
        Abc_ObjAddFanin( pNode, pNet );
    }
    pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[vTokens->nSize - 1] );
    Abc_ObjAddFanin( pNet, pNode );

    // derive the functionality of the node
    p->vCubes->nSize = 0;
    nFanins = vTokens->nSize - 2;
    if ( nFanins == 0 )
        while ( vTokens = Io_ReadBlifGetTokens(p) )
        {
            pToken = vTokens->pArray[0];
            if ( pToken[0] == '.' )
                break;
            // read the cube
            if ( vTokens->nSize != 1 )
            {
                p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
                sprintf( p->sError, "The number of tokens in the constant cube is wrong." );
                Io_ReadBlifPrintErrorMessage( p );
                return 1;
            }
            // create the cube
            Char = ((char *)vTokens->pArray[0])[0];
            Vec_StrPush( p->vCubes, ' ' );
            Vec_StrPush( p->vCubes, Char );
            Vec_StrPush( p->vCubes, '\n' );
        }
    else
        while ( vTokens = Io_ReadBlifGetTokens(p) )
        {
            pToken = vTokens->pArray[0];
            if ( pToken[0] == '.' )
                break;
            // read the cube
            if ( vTokens->nSize != 2 )
            {
                p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
                sprintf( p->sError, "The number of tokens in the cube is wrong." );
                Io_ReadBlifPrintErrorMessage( p );
                return 1;
            }
            // create the cube
            for ( i = 0; i < nFanins; i++ )
                Vec_StrPush( p->vCubes, ((char *)vTokens->pArray[0])[i] );
            // check the char 
            Char = ((char *)vTokens->pArray[1])[0];
            if ( Char != '0' && Char != '1' )
            {
                p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
                sprintf( p->sError, "The output character in the constant cube is wrong." );
                Io_ReadBlifPrintErrorMessage( p );
                return 1;
            }
            Vec_StrPush( p->vCubes, ' ' );
            Vec_StrPush( p->vCubes, Char );
            Vec_StrPush( p->vCubes, '\n' );
        }
    // if there is nothing there
    if ( p->vCubes->nSize == 0 )
    {
        // create an empty cube
        Vec_StrPush( p->vCubes, ' ' );
        Vec_StrPush( p->vCubes, '0' );
        Vec_StrPush( p->vCubes, '\n' );
    }
    Vec_StrPush( p->vCubes, 0 );
    // set the pointer to the functionality of the node
    Abc_ObjSetData( pNode, Abc_SopRegister(pNtk->pManFunc, p->vCubes->pArray) );
    // return the last array of tokens
    *pvTokens = vTokens;
    return 0;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_ReadBlifNetworkInputArrival( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens )
{
    Abc_Obj_t * pNet;
    char * pFoo1, * pFoo2;
    double TimeRise, TimeFall;

    // make sure this is indeed the .inputs line
    assert( strncmp( vTokens->pArray[0], ".input_arrival", 14 ) == 0 );
    if ( vTokens->nSize != 4 )
    {
        p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
        sprintf( p->sError, "Wrong number of arguments on .input_arrival line." );
        Io_ReadBlifPrintErrorMessage( p );
        return 1;
    }
    pNet = Abc_NtkFindNet( p->pNtk, vTokens->pArray[1] );
    if ( pNet == NULL )
    {
        p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
        sprintf( p->sError, "Cannot find object corresponding to %s on .input_arrival line.", vTokens->pArray[1] );
        Io_ReadBlifPrintErrorMessage( p );
        return 1;
    }
    TimeRise = strtod( vTokens->pArray[2], &pFoo1 );
    TimeFall = strtod( vTokens->pArray[3], &pFoo2 );
    if ( *pFoo1 != '\0' || *pFoo2 != '\0' )
    {
        p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
        sprintf( p->sError, "Bad value (%s %s) for rise or fall time on .input_arrival line.", vTokens->pArray[2], vTokens->pArray[3] );
        Io_ReadBlifPrintErrorMessage( p );
        return 1;
    }
    // set the arrival time
    Abc_NtkTimeSetArrival( p->pNtk, pNet->Id, (float)TimeRise, (float)TimeFall );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_ReadBlifNetworkDefaultInputArrival( Io_ReadBlif_t * p, Vec_Ptr_t * vTokens )
{
    char * pFoo1, * pFoo2;
    double TimeRise, TimeFall;

    // make sure this is indeed the .inputs line
    assert( strncmp( vTokens->pArray[0], ".default_input_arrival", 23 ) == 0 );
    if ( vTokens->nSize != 3 )
    {
        p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
        sprintf( p->sError, "Wrong number of arguments on .default_input_arrival line." );
        Io_ReadBlifPrintErrorMessage( p );
        return 1;
    }
    TimeRise = strtod( vTokens->pArray[1], &pFoo1 );
    TimeFall = strtod( vTokens->pArray[2], &pFoo2 );
    if ( *pFoo1 != '\0' || *pFoo2 != '\0' )
    {
        p->LineCur = Extra_FileReaderGetLineNumber(p->pReader, 0);
        sprintf( p->sError, "Bad value (%s %s) for rise or fall time on .default_input_arrival line.", vTokens->pArray[1], vTokens->pArray[2] );
        Io_ReadBlifPrintErrorMessage( p );
        return 1;
    }
    // set the arrival time
    Abc_NtkTimeSetDefaultArrival( p->pNtk, (float)TimeRise, (float)TimeFall );
    return 0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


