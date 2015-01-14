/**CFile****************************************************************

  FileName    [cbaPrs.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaPrs.h,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__prs__prs_h
#define ABC__base__prs__prs_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START 

/*
// parser objects (object types after parsing)
typedef enum { 
    CBA_PRS_NONE = 0,    // 0:  unused
    CBA_PRS_NODE,        // 1:  .names/assign/box2 (box without formal/actual binding)
    CBA_PRS_BOX,         // 2:  .subckt/.gate/box (box with formal/actual binding)
    CBA_PRS_LATCH,       // 3:  .latch
    CBA_PRS_CONCAT,      // 4:  concatenation
    CBA_PRS_UNKNOWN      // 5:  unknown
} Cba_PrsType_t; 
*/

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// parser
typedef struct Cba_Prs_t_ Cba_Prs_t;
struct Cba_Prs_t_
{
    // input data
    char *       pName;       // file name
    char *       pBuffer;     // file contents
    char *       pLimit;      // end of file
    char *       pCur;        // current position
    // construction
    Cba_Man_t *  pLibrary;
    Cba_Man_t *  pDesign; 
    // interface collected by the parser
    int          iModuleName; // name Id
    Vec_Int_t    vInoutsCur;  // inouts
    Vec_Int_t    vInputsCur;  // inputs 
    Vec_Int_t    vOutputsCur; // outputs
    Vec_Int_t    vWiresCur;   // wires
    // objects collected by the parser
    Vec_Int_t    vTypesCur;   // Cba_PrsType_t
    Vec_Int_t    vFuncsCur;   // functions (node->func; box->module; gate->cell; latch->init; concat->unused)
    Vec_Int_t    vInstIdsCur; // instance names
    Vec_Int_t    vFaninsCur;  // instances
    // temporary data
    Vec_Str_t    vCover;      // one SOP cover
    Vec_Int_t    vTemp;       // array of tokens
    Vec_Int_t    vTemp2;      // array of tokens
    // statistics
    Vec_Int_t    vKnown;
    Vec_Int_t    vFailed;
    Vec_Int_t    vSucceeded;
    // error handling
    char ErrorStr[1000];      // error
};

#define Cba_PrsForEachModelVec( vVec, p, pName, i ) \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pName) = Abc_NamStr(p->pDesign->pNames, Vec_IntEntry(vVec,i))); i++ )

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

// create error message
static inline int Cba_PrsErrorSet( Cba_Prs_t * p, char * pError, int Value )
{
    assert( !p->ErrorStr[0] );
    sprintf( p->ErrorStr, "%s", pError );
    return Value;
}
// clear error message
static inline void Cba_PrsErrorClear( Cba_Prs_t * p )
{
    p->ErrorStr[0] = '\0';
}
// print error message
static inline int Cba_PrsErrorPrint( Cba_Prs_t * p )
{
    char * pThis; int iLine = 0;
    if ( !p->ErrorStr[0] ) return 1;
    for ( pThis = p->pBuffer; pThis < p->pCur; pThis++ )
        iLine += (int)(*pThis == '\n');
    printf( "Line %d: %s\n", iLine, p->ErrorStr );
    return 0;
}

// create network
static inline Cba_Ntk_t * Cba_PrsAddCurrentModel( Cba_Prs_t * p, int iNameId )
{
    Cba_Ntk_t * pNtk = Cba_NtkAlloc( p->pDesign, Abc_NamStr(p->pDesign->pNames, iNameId) );
    assert( Vec_IntSize(&p->vInputsCur) != 0 || Vec_IntSize(&p->vOutputsCur) != 0 );
    Cba_ManSetupArray( p->pDesign, &pNtk->vInouts,  &p->vInoutsCur  );
    Cba_ManSetupArray( p->pDesign, &pNtk->vInputs,  &p->vInputsCur  );
    Cba_ManSetupArray( p->pDesign, &pNtk->vOutputs, &p->vOutputsCur );
    Cba_ManSetupArray( p->pDesign, &pNtk->vWires,   &p->vWiresCur   );
    Cba_ManSetupArray( p->pDesign, &pNtk->vTypes,   &p->vTypesCur   );
    Cba_ManSetupArray( p->pDesign, &pNtk->vFuncs,   &p->vFuncsCur   );
    Cba_ManSetupArray( p->pDesign, &pNtk->vInstIds, &p->vInstIdsCur );
    Cba_ManSetupArray( p->pDesign, &pNtk->vFanins,  &p->vFaninsCur  );
    return pNtk;
}



static inline char * Cba_PrsLoadFile( char * pFileName, char ** ppLimit )
{
    char * pBuffer;
    int nFileSize, RetValue;
    FILE * pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open input file.\n" );
        return NULL;
    }
    // get the file size, in bytes
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile );  
    // move the file current reading position to the beginning
    rewind( pFile ); 
    // load the contents of the file into memory
    pBuffer = ABC_ALLOC( char, nFileSize + 3 );
    pBuffer[0] = '\n';
    RetValue = fread( pBuffer+1, nFileSize, 1, pFile );
    // terminate the string with '\0'
    pBuffer[nFileSize + 0] = '\n';
    pBuffer[nFileSize + 1] = '\0';
    *ppLimit = pBuffer + nFileSize + 2;
    return pBuffer;
}
static inline Cba_Prs_t * Cba_PrsAlloc( char * pFileName )
{
    Cba_Prs_t * p;
    char * pBuffer, * pLimit;
    pBuffer = Cba_PrsLoadFile( pFileName, &pLimit );
    if ( pBuffer == NULL )
        return NULL;
    p = ABC_CALLOC( Cba_Prs_t, 1 );
    p->pName   = pFileName;
    p->pBuffer = pBuffer;
    p->pLimit  = pLimit;
    p->pCur    = pBuffer;
    p->pDesign = Cba_ManAlloc( pFileName );
    return p;
}
static inline void Cba_PrsFree( Cba_Prs_t * p )
{
    if ( p->pDesign )
        Cba_ManFree( p->pDesign );
    Vec_IntErase( &p->vInoutsCur );
    Vec_IntErase( &p->vInputsCur );
    Vec_IntErase( &p->vOutputsCur );
    Vec_IntErase( &p->vWiresCur );

    Vec_IntErase( &p->vTypesCur );
    Vec_IntErase( &p->vFuncsCur );
    Vec_IntErase( &p->vInstIdsCur );
    Vec_IntErase( &p->vFaninsCur );
    // temporary
    Vec_StrErase( &p->vCover );
    Vec_IntErase( &p->vTemp );
    Vec_IntErase( &p->vTemp2 );

    Vec_IntErase( &p->vKnown );
    Vec_IntErase( &p->vFailed );
    Vec_IntErase( &p->vSucceeded );
    ABC_FREE( p->pBuffer );
    ABC_FREE( p );
}

////////////////////////////////////////////////////////////////////////
///                             ITERATORS                            ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== cba.c ========================================================*/


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

