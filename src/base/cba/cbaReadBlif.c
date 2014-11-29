/**CFile****************************************************************

  FileName    [cbaReadBlif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaReadBlif.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "cbaPrs.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// BLIF keywords
typedef enum { 
    CBA_BLIF_NONE = 0, // 0:  unused
    CBA_BLIF_MODEL,    // 1:  .model
    CBA_BLIF_INPUTS,   // 2:  .inputs
    CBA_BLIF_OUTPUTS,  // 3:  .outputs
    CBA_BLIF_NAMES,    // 4:  .names
    CBA_BLIF_SUBCKT,   // 5:  .subckt
    CBA_BLIF_GATE,     // 6:  .gate
    CBA_BLIF_LATCH,    // 7:  .latch
    CBA_BLIF_END,      // 8:  .end
    CBA_BLIF_UNKNOWN   // 9:  unknown
} Cba_BlifType_t;

const char * s_BlifTypes[CBA_BLIF_UNKNOWN+1] = {
    NULL,              // 0:  unused
    ".model",          // 1:  .model   
    ".inputs",         // 2:  .inputs
    ".outputs",        // 3:  .outputs
    ".names",          // 4:  .names
    ".subckt",         // 5:  .subckt
    ".gate",           // 6:  .gate
    ".latch",          // 7:  .latch
    ".end",            // 8:  .end
    NULL               // 9:  unknown
};

static inline void Cba_PrsAddBlifDirectives( Cba_Prs_t * p )
{
    int i;
    for ( i = 1; s_BlifTypes[i]; i++ )
        Abc_NamStrFindOrAdd( p->pDesign->pNames, (char *)s_BlifTypes[i],   NULL );
    assert( Abc_NamObjNumMax(p->pDesign->pNames) == i );
}

static inline int  Cba_PrsIsSpace( char c )                    { return c == ' ' || c == '\t' || c == '\r';                     }
static inline int  Cba_PrsIsOk( Cba_Prs_t * p )                { return (int)(p->pCur < p->pLimit);                             }
static inline int  Cba_PrsIsChar( Cba_Prs_t * p, char c )      { return *p->pCur == 'c';                                        }
static inline int  Cba_PrsIsLit( Cba_Prs_t * p )               { return *p->pCur == '0' || *p->pCur == '1' || *p->pCur == '-';  }
static inline void Cba_PrsSkipToChar( Cba_Prs_t * p, char c )  { while ( *p->pCur != c ) p->pCur++;                             }
static inline char Cba_PrsSkip( Cba_Prs_t * p )                { return *p->pCur++;                                             }


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reading names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cba_PrsSkipSpaces( Cba_Prs_t * p )
{
    while ( Cba_PrsIsSpace(*p->pCur) )
        Cba_PrsSkip(p);
    if ( Cba_PrsIsChar(p, '#') )  
        Cba_PrsSkipToChar( p, '\n' );
    else if ( Cba_PrsIsChar(p, '\\') )
    {
        Cba_PrsSkipToChar( p, '\n' );
        Cba_PrsSkip(p);
        Cba_PrsSkipSpaces( p );
    }   
}
static inline int Cba_PrsReadName( Cba_Prs_t * p )
{
    char * pStart = p->pCur;
    while ( !Cba_PrsIsSpace(*p->pCur) && !Cba_PrsIsChar(p, '\\') )
        Cba_PrsSkip(p);
    if ( pStart == p->pCur )
        return 0;
    return Abc_NamStrFindOrAddLim( p->pDesign->pNames, pStart, p->pCur, NULL );
}
static inline int Cba_PrsReadName2( Cba_Prs_t * p )
{
    char * pStart = p->pCur;
    while ( !Cba_PrsIsSpace(*p->pCur) && !Cba_PrsIsChar(p, '\\') && !Cba_PrsIsChar(p, '=') )
        Cba_PrsSkip(p);
    if ( pStart == p->pCur )
        return 0;
    return Abc_NamStrFindOrAddLim( p->pDesign->pNames, pStart, p->pCur, NULL );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cba_PrsReadCube( Cba_Prs_t * p )
{
    while ( Cba_PrsIsLit(p) )
        Vec_StrPush( p->vCover, Cba_PrsSkip(p) );
    Cba_PrsSkipSpaces( p );
    Vec_StrPush( p->vCover, ' ' );
    if ( !Cba_PrsIsLit(p) )                           return Cba_PrsErrorSet(p, "Cannot detect output literal.", 1);
    Vec_StrPush( p->vCover, Cba_PrsSkip(p) );
    return 1;
}
static inline void Cba_PrsSaveCover( Cba_Prs_t * p )
{
    int iToken;
    assert( Vec_StrSize(p->vCover) > 0 );
    Vec_StrPush( p->vCover, '\0' );
    iToken = Abc_NamStrFindOrAdd( p->pDesign->pFuncs, Vec_StrArray(p->vCover), NULL );
    Vec_StrClear( p->vCover );
    assert( Vec_IntEntryLast(p->vFuncsCur) == 1 );
    Vec_IntWriteEntry( p->vFuncsCur, Vec_IntSize(p->vFuncsCur)-1, iToken );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cba_PrsReadSignals( Cba_Prs_t * p, int fSkipFirst )
{
    Cba_PrsSkipSpaces( p );
    Vec_IntFill( p->vTemp, fSkipFirst, -1 );
    while ( !Cba_PrsIsChar(p, '\n') )
    {
        Vec_IntPush( p->vTemp, Cba_PrsReadName(p) );
        Cba_PrsSkipSpaces( p );
    }
    if ( Vec_IntSize(p->vTemp) == 0 )  return Cba_PrsErrorSet(p, "List of signals is empty.", 1);
    if ( Vec_IntCountZero(p->vTemp) )  return Cba_PrsErrorSet(p, "Cannot read names in the list.", 1); 
    return 0;
}
static inline int Cba_PrsReadInputs( Cba_Prs_t * p )
{
    if ( Cba_PrsReadSignals(p, 0) )    return 1;
    Vec_IntAppend( p->vInputsCur, p->vTemp );
    return 0;
}
static inline int Cba_PrsReadOutputs( Cba_Prs_t * p )
{
    if ( Cba_PrsReadSignals(p, 0) )    return 1;
    Vec_IntAppend( p->vOutputsCur, p->vTemp );
    return 0;
}
static inline int Cba_PrsReadNode( Cba_Prs_t * p )
{
    if ( Cba_PrsReadSignals(p, 1) )    return 1;
    Vec_IntWriteEntry( p->vTemp, 0, Vec_IntPop(p->vTemp) );
    // save results
    Vec_IntPush( p->vFuncsCur, 1 );
    Vec_IntPush( p->vTypesCur, CBA_PRS_NODE );
    Cba_PrsSetupVecInt( p, Vec_WecPushLevel(p->vFaninsCur), p->vTemp );
    return 0;
}
static inline int Cba_PrsReadBox( Cba_Prs_t * p, int fGate )
{
    Cba_PrsSkipSpaces( p );
    if ( Cba_PrsIsChar(p, '\n') )      return Cba_PrsErrorSet(p, "Cannot read model name.", 1);
    Vec_IntPush( p->vFuncsCur, Cba_PrsReadName(p) );
    Cba_PrsSkipSpaces( p );
    if ( Cba_PrsIsChar(p, '\n') )      return Cba_PrsErrorSet(p, "Cannot read formal/actual inputs.", 1);
    while ( !Cba_PrsIsChar(p, '\n') )
    {
        Vec_IntPush( p->vTemp, Cba_PrsReadName(p) );
        Cba_PrsSkipSpaces( p );
        if ( !Cba_PrsIsChar(p, '=') )  return Cba_PrsErrorSet(p, "Cannot find symbol \'=\'.", 1);
        p->pCur++;
        Cba_PrsSkipSpaces( p );
        Vec_IntPush( p->vTemp, Cba_PrsReadName(p) );
        Cba_PrsSkipSpaces( p );
    }
    // save results
    Vec_IntPush( p->vTypesCur, CBA_PRS_BOX );
    Cba_PrsSetupVecInt( p, Vec_WecPushLevel(p->vFaninsCur), p->vTemp );
    return 0;
}
static inline int Cba_PrsReadLatch( Cba_Prs_t * p )
{
    Vec_IntFill( p->vTemp, 2, -1 );
    Cba_PrsSkipSpaces( p );
    if ( Cba_PrsIsChar(p, '\n') )      return Cba_PrsErrorSet(p, "Cannot read latch input.", 1);
    Vec_IntWriteEntry( p->vTemp, 1, Cba_PrsReadName(p) );
    Cba_PrsSkipSpaces( p );
    if ( Cba_PrsIsChar(p, '\n') )      return Cba_PrsErrorSet(p, "Cannot read latch output.", 1);
    Vec_IntWriteEntry( p->vTemp, 0, Cba_PrsReadName(p) );
    if ( Cba_PrsIsChar(p, '0') )
        Vec_IntPush( p->vFuncsCur, 0 );
    else if ( Cba_PrsIsChar(p, '1') )
        Vec_IntPush( p->vFuncsCur, 1 );
    else if ( Cba_PrsIsChar(p, '2') || Cba_PrsIsChar(p, '\n') )
        Vec_IntPush( p->vFuncsCur, 2 );
    else                               return Cba_PrsErrorSet(p, "Cannot read latch init value.", 1);
    // save results
    Vec_IntPush( p->vTypesCur, CBA_PRS_LATCH );
    Cba_PrsSetupVecInt( p, Vec_WecPushLevel(p->vFaninsCur), p->vTemp );
    return 0;
}
static inline int Cba_PrsReadModel( Cba_Prs_t * p )
{
    Cba_PrsSkipSpaces( p );
    if ( Vec_IntSize(p->vInputsCur) > 0 )           return Cba_PrsErrorSet(p, "Parsing previous model is unfinished.", 1);
    p->iModuleName = Cba_PrsReadName( p );
    if ( p->iModuleName == 0 )                      return Cba_PrsErrorSet(p, "Cannot read model name.", 1);
    Cba_PrsSkipSpaces( p );
    if ( !Cba_PrsIsChar(p, '\n') )                  return Cba_PrsErrorSet(p, "Trailing symbols on .model line.", 1);
    return 0;
}
static inline int Cba_PrsReadEnd( Cba_Prs_t * p )
{
    if ( Vec_IntSize(p->vInputsCur) == 0 )          return Cba_PrsErrorSet(p, "Directive .end without .model.", 1);
    Cba_PrsAddCurrentModel( p, p->iModuleName );
    return 0;
}

static inline int Cba_PrsReadDirective( Cba_Prs_t * p )
{
    int iToken;
    if ( !Cba_PrsIsChar(p, '.') )
        return Cba_PrsReadCube( p );
    if ( Vec_StrSize(p->vCover) > 0 ) // SOP was specified for the previous node
        Cba_PrsSaveCover( p );
    iToken = Cba_PrsReadName( p );  
    if ( iToken == CBA_BLIF_MODEL )
        return Cba_PrsReadModel( p );
    if ( iToken == CBA_BLIF_INPUTS )
        return Cba_PrsReadInputs( p );
    if ( iToken == CBA_BLIF_OUTPUTS )
        return Cba_PrsReadOutputs( p );
    if ( iToken == CBA_BLIF_NAMES )
        return Cba_PrsReadNode( p );
    if ( iToken == CBA_BLIF_SUBCKT )
        return Cba_PrsReadBox( p, 0 );
    if ( iToken == CBA_BLIF_GATE )
        return Cba_PrsReadBox( p, 1 );
    if ( iToken == CBA_BLIF_LATCH )
        return Cba_PrsReadLatch( p );
    if ( iToken == CBA_BLIF_END )
        return Cba_PrsReadEnd( p );
    assert( 0 );
    return 1;
}
static inline int Cba_PrsReadLines( Cba_Prs_t * p )
{
    while ( Cba_PrsIsChar(p, '\n') )
    {
        p->pCur++; Cba_PrsSkipSpaces( p );
        if ( Cba_PrsIsChar(p, '\n') )    
            continue;
        if ( Cba_PrsReadDirective( p ) )
            return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cba_Man_t * Cba_PrsReadBlif( char * pFileName )
{
    Cba_Man_t * pDesign = NULL;
    Cba_Prs_t * p = Cba_PrsAlloc( pFileName );
    if ( p == NULL )
        return NULL;
    Cba_PrsAddBlifDirectives( p );
    Cba_PrsReadLines( p );
    if ( Cba_PrsErrorPrint(p) )
        ABC_SWAP( Cba_Man_t *, pDesign, p->pDesign );
    Cba_PrsFree( p );
    return pDesign;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

