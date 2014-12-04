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
    CBA_BLIF_NONE = 0, // 0:   unused
    CBA_BLIF_MODEL,    // 1:   .model
    CBA_BLIF_INOUTS,   // 2:   .inouts
    CBA_BLIF_INPUTS,   // 3:   .inputs
    CBA_BLIF_OUTPUTS,  // 4:   .outputs
    CBA_BLIF_NAMES,    // 5:   .names
    CBA_BLIF_SUBCKT,   // 6:   .subckt
    CBA_BLIF_GATE,     // 7:   .gate
    CBA_BLIF_LATCH,    // 8:   .latch
    CBA_BLIF_SHORT,    // 9:   .short
    CBA_BLIF_END,      // 10:  .end
    CBA_BLIF_UNKNOWN   // 11:  unknown
} Cba_BlifType_t;

const char * s_BlifTypes[CBA_BLIF_UNKNOWN+1] = {
    NULL,              // 0:   unused
    ".model",          // 1:   .model   
    ".inouts",         // 2:   .inputs
    ".inputs",         // 3:   .inputs
    ".outputs",        // 4:   .outputs
    ".names",          // 5:   .names
    ".subckt",         // 6:   .subckt
    ".gate",           // 7:   .gate
    ".latch",          // 8:   .latch
    ".short",          // 9:   .short
    ".end",            // 10:  .end
    NULL               // 11:  unknown
};

static inline void Cba_PrsAddBlifDirectives( Cba_Prs_t * p )
{
    int i;
    for ( i = 1; s_BlifTypes[i]; i++ )
        Abc_NamStrFindOrAdd( p->pDesign->pNames, (char *)s_BlifTypes[i],   NULL );
    assert( Abc_NamObjNumMax(p->pDesign->pNames) == i );
    Abc_NamStrFindOrAdd( p->pDesign->pFuncs, (char *)" 0\n",   NULL );  // default const 0 function
    Abc_NamStrFindOrAdd( p->pDesign->pFuncs, (char *)"1 1\n",   NULL ); // default buffer function
    assert( Abc_NamObjNumMax(p->pDesign->pFuncs) == 3 );
}


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reading characters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int  Cba_CharIsSpace( char c )                { return c == ' ' || c == '\t' || c == '\r';              }
static inline int  Cba_CharIsStop( char c )                 { return c == '#' || c == '\\' || c == '\n' || c == '=';  }
static inline int  Cba_CharIsLit( char c )                  { return c == '0' || c == '1'  || c == '-';               }

static inline int  Cba_PrsIsSpace( Cba_Prs_t * p )          { return Cba_CharIsSpace(*p->pCur);                       }
static inline int  Cba_PrsIsStop( Cba_Prs_t * p )           { return Cba_CharIsStop(*p->pCur);                        }
static inline int  Cba_PrsIsLit( Cba_Prs_t * p )            { return Cba_CharIsLit(*p->pCur);                         }

static inline int  Cba_PrsIsChar( Cba_Prs_t * p, char c )   { return *p->pCur == c;                                   }
static inline int  Cba_PrsIsChar2( Cba_Prs_t * p, char c )  { return *p->pCur++ == c;                                 }

static inline void Cba_PrsSkip( Cba_Prs_t * p )             { p->pCur++;                                              }
static inline char Cba_PrsSkip2( Cba_Prs_t * p )            { return *p->pCur++;                                      }


/**Function*************************************************************

  Synopsis    [Reading names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cba_PrsSkipToChar( Cba_Prs_t * p, char c )  
{ 
    while ( !Cba_PrsIsChar(p, c) ) 
        Cba_PrsSkip(p);
}
static inline void Cba_PrsSkipSpaces( Cba_Prs_t * p )
{
    while ( 1 )
    {
        while ( Cba_PrsIsSpace(p) )
            Cba_PrsSkip(p);
        if ( Cba_PrsIsChar(p, '\\') )
        {
            Cba_PrsSkipToChar( p, '\n' );
            Cba_PrsSkip(p);
            continue;
        }
        if ( Cba_PrsIsChar(p, '#') )  
            Cba_PrsSkipToChar( p, '\n' );
        break;
    }
    assert( !Cba_PrsIsSpace(p) );
}
static inline int Cba_PrsReadName( Cba_Prs_t * p )
{
    char * pStart;
    Cba_PrsSkipSpaces( p );
    if ( Cba_PrsIsChar(p, '\n') )
        return 0;
    pStart = p->pCur;
    while ( !Cba_PrsIsSpace(p) && !Cba_PrsIsStop(p) )
        Cba_PrsSkip(p);
    if ( pStart == p->pCur )
        return 0;
    assert( pStart < p->pCur );
    return Abc_NamStrFindOrAddLim( p->pDesign->pNames, pStart, p->pCur, NULL );
}
static inline int Cba_PrsReadList( Cba_Prs_t * p )
{
    int iToken;
    Vec_IntClear( &p->vTemp );
    while ( (iToken = Cba_PrsReadName(p)) )
        Vec_IntPush( &p->vTemp, iToken );
    if ( Vec_IntSize(&p->vTemp) == 0 )                return Cba_PrsErrorSet(p, "Signal list is empty.", 1);
    return 0;
}
static inline int Cba_PrsReadList2( Cba_Prs_t * p )
{
    int iToken;
    Vec_IntFill( &p->vTemp, 1, -1 );
    while ( (iToken = Cba_PrsReadName(p)) )
        Vec_IntPush( &p->vTemp, iToken );
    iToken = Vec_IntPop(&p->vTemp);
    if ( Vec_IntSize(&p->vTemp) == 0 )                return Cba_PrsErrorSet(p, "Signal list is empty.", 1);
    Vec_IntWriteEntry( &p->vTemp, 0, iToken );
    return 0;
}
static inline int Cba_PrsReadList3( Cba_Prs_t * p )
{
    Vec_IntClear( &p->vTemp );
    while ( !Cba_PrsIsChar(p, '\n') )
    {
        int iToken = Cba_PrsReadName(p);
        if ( iToken == 0 )              return Cba_PrsErrorSet(p, "Cannot read formal name.", 1);
        Vec_IntPush( &p->vTemp, iToken );
        Cba_PrsSkipSpaces( p );
        if ( !Cba_PrsIsChar2(p, '=') )  return Cba_PrsErrorSet(p, "Cannot find symbol \"=\".", 1);
        iToken = Cba_PrsReadName(p);
        if ( iToken == 0 )              return Cba_PrsErrorSet(p, "Cannot read actual name.", 1);
        Vec_IntPush( &p->vTemp, iToken );
        Cba_PrsSkipSpaces( p );
    }
    if ( Vec_IntSize(&p->vTemp) == 0 )  return Cba_PrsErrorSet(p, "Cannot read a list of formal/actual names.", 1);
    if ( Vec_IntSize(&p->vTemp) % 2  )  return Cba_PrsErrorSet(p, "The number of formal/actual names is not even.", 1);
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cba_PrsReadCube( Cba_Prs_t * p )
{
    assert( Cba_PrsIsLit(p) );
    while ( Cba_PrsIsLit(p) )
        Vec_StrPush( &p->vCover, Cba_PrsSkip2(p) );
    Cba_PrsSkipSpaces( p );
    if ( Cba_PrsIsChar(p, '\n') )
    {
        if ( Vec_StrSize(&p->vCover) != 1 )            return Cba_PrsErrorSet(p, "Cannot read cube.", 1);
        // fix single literal cube by adding space
        Vec_StrPush( &p->vCover, Vec_StrEntry(&p->vCover,0) );
        Vec_StrWriteEntry( &p->vCover, 0, ' ' );
        Vec_StrPush( &p->vCover, '\n' );
        return 0;
    }
    if ( !Cba_PrsIsLit(p) )                           return Cba_PrsErrorSet(p, "Cannot read output literal.", 1);
    Vec_StrPush( &p->vCover, ' ' );
    Vec_StrPush( &p->vCover, Cba_PrsSkip2(p) );
    Vec_StrPush( &p->vCover, '\n' );
    Cba_PrsSkipSpaces( p );
    if ( !Cba_PrsIsChar(p, '\n') )                    return Cba_PrsErrorSet(p, "Cannot read end of cube.", 1);
    return 0;
}
static inline void Cba_PrsSaveCover( Cba_Prs_t * p )
{
    int iToken;
    assert( Vec_StrSize(&p->vCover) > 0 );
    Vec_StrPush( &p->vCover, '\0' );
    iToken = Abc_NamStrFindOrAdd( p->pDesign->pFuncs, Vec_StrArray(&p->vCover), NULL );
    assert( Vec_IntEntryLast(&p->vFuncsCur) == 1 );
    Vec_IntWriteEntry( &p->vFuncsCur, Vec_IntSize(&p->vFuncsCur)-1, iToken );
    Vec_StrClear( &p->vCover );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cba_PrsReadInouts( Cba_Prs_t * p )
{
    if ( Cba_PrsReadList(p) )    return 1;
    Vec_IntAppend( &p->vInoutsCur, &p->vTemp );
    return 0;
}
static inline int Cba_PrsReadInputs( Cba_Prs_t * p )
{
    if ( Cba_PrsReadList(p) )    return 1;
    Vec_IntAppend( &p->vInputsCur, &p->vTemp );
    return 0;
}
static inline int Cba_PrsReadOutputs( Cba_Prs_t * p )
{
    if ( Cba_PrsReadList(p) )    return 1;
    Vec_IntAppend( &p->vOutputsCur, &p->vTemp );
    return 0;
}
static inline int Cba_PrsReadNode( Cba_Prs_t * p )
{
    if ( Cba_PrsReadList2(p) )   return 1;
    // save results
    Vec_IntPush( &p->vTypesCur, CBA_PRS_NODE );
    Vec_IntPush( &p->vFuncsCur, 1 ); // default const 0 function
    Cba_PrsSetupVecInt( p, Vec_WecPushLevel(&p->vFaninsCur), &p->vTemp );
    return 0;
}
static inline int Cba_PrsReadBox( Cba_Prs_t * p, int fGate )
{
    int iToken = Cba_PrsReadName(p);
    if ( iToken == 0 )           return Cba_PrsErrorSet(p, "Cannot read model name.", 1);
    if ( Cba_PrsReadList3(p) )   return 1;
    // save results
    Vec_IntPush( &p->vTypesCur, CBA_PRS_BOX );
    Vec_IntPush( &p->vFuncsCur, iToken );
    Cba_PrsSetupVecInt( p, Vec_WecPushLevel(&p->vFaninsCur), &p->vTemp );
    return 0;
}
static inline int Cba_PrsReadLatch( Cba_Prs_t * p )
{
    int iToken = Cba_PrsReadName(p);
    Vec_IntFill( &p->vTemp, 2, -1 );
    if ( iToken == 0 )                 return Cba_PrsErrorSet(p, "Cannot read latch input.", 1);
    Vec_IntWriteEntry( &p->vTemp, 1, iToken );
    iToken = Cba_PrsReadName(p);
    if ( iToken == 0 )                 return Cba_PrsErrorSet(p, "Cannot read latch output.", 1);
    Vec_IntWriteEntry( &p->vTemp, 0, iToken );
    Cba_PrsSkipSpaces( p );
    if ( Cba_PrsIsChar(p, '0') )
        iToken = 0;
    else if ( Cba_PrsIsChar(p, '1') )
        iToken = 1;
    else 
        iToken = 2;
    Cba_PrsSkipToChar( p, '\n' );
    // save results
    Vec_IntPush( &p->vTypesCur, CBA_PRS_LATCH );
    Vec_IntPush( &p->vFuncsCur, iToken );
    Cba_PrsSetupVecInt( p, Vec_WecPushLevel(&p->vFaninsCur), &p->vTemp );
    return 0;
}
static inline int Cba_PrsReadShort( Cba_Prs_t * p )
{
    int iToken = Cba_PrsReadName(p);
    Vec_IntFill( &p->vTemp, 2, -1 );
    if ( iToken == 0 )                 return Cba_PrsErrorSet(p, "Cannot read .short input.", 1);
    Vec_IntWriteEntry( &p->vTemp, 1, iToken );
    iToken = Cba_PrsReadName(p);
    if ( iToken == 0 )                 return Cba_PrsErrorSet(p, "Cannot read .short output.", 1);
    Vec_IntWriteEntry( &p->vTemp, 0, iToken );
    Cba_PrsSkipSpaces( p );
    if ( !Cba_PrsIsChar(p, '\n') )     return Cba_PrsErrorSet(p, "Trailing symbols on .short line.", 1);
    // save results
    Vec_IntPush( &p->vTypesCur, CBA_PRS_NODE );
    Vec_IntPush( &p->vFuncsCur, 2 );   // default buffer function
    Cba_PrsSetupVecInt( p, Vec_WecPushLevel(&p->vFaninsCur), &p->vTemp );
    return 0;
}
static inline int Cba_PrsReadModel( Cba_Prs_t * p )
{
    if ( p->iModuleName > 0 )                      return Cba_PrsErrorSet(p, "Parsing previous model is unfinished.", 1);
    p->iModuleName = Cba_PrsReadName(p);
    Cba_PrsSkipSpaces( p );
    if ( !Cba_PrsIsChar(p, '\n') )                 return Cba_PrsErrorSet(p, "Trailing symbols on .model line.", 1);
    return 0;
}
static inline int Cba_PrsReadEnd( Cba_Prs_t * p )
{
    if ( p->iModuleName == 0 )                     return Cba_PrsErrorSet(p, "Directive .end without .model.", 1);
    //printf( "Saving model \"%s\".\n", Abc_NamStr(p->pDesign->pNames, p->iModuleName) );
    Cba_PrsAddCurrentModel( p, p->iModuleName );
    p->iModuleName = 0;
    Cba_PrsSkipSpaces( p );
    if ( !Cba_PrsIsChar(p, '\n') )                 return Cba_PrsErrorSet(p, "Trailing symbols on .end line.", 1);
    return 0;
}

static inline int Cba_PrsReadDirective( Cba_Prs_t * p )
{
    int iToken;
    if ( !Cba_PrsIsChar(p, '.') )
        return Cba_PrsReadCube( p );
    if ( Vec_StrSize(&p->vCover) > 0 ) // SOP was specified for the previous node
        Cba_PrsSaveCover( p );
    iToken = Cba_PrsReadName( p );  
    if ( iToken == CBA_BLIF_MODEL )
        return Cba_PrsReadModel( p );
    if ( iToken == CBA_BLIF_INOUTS )
        return Cba_PrsReadInouts( p );
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
    if ( iToken == CBA_BLIF_SHORT )
        return Cba_PrsReadShort( p );
    if ( iToken == CBA_BLIF_END )
        return Cba_PrsReadEnd( p );
    printf( "Cannot read directive \"%s\".\n", Abc_NamStr(p->pDesign->pNames, iToken) );
    return 1;
}
static inline int Cba_PrsReadLines( Cba_Prs_t * p )
{
    while ( p->pCur[1] != '\0' )
    {
        assert( Cba_PrsIsChar(p, '\n') );
        Cba_PrsSkip(p);
        Cba_PrsSkipSpaces( p );
        if ( Cba_PrsIsChar(p, '\n') )
            continue;
        if ( Cba_PrsReadDirective(p) )   
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

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_PrsReadBlifTest( char * pFileName )
{
    abctime clk = Abc_Clock();
    extern void Cba_PrsWriteBlif( char * pFileName, Cba_Man_t * pDes );
    Cba_Man_t * p = Cba_PrsReadBlif( "aga/ray/ray_hie_oper.blif" );
    if ( !p ) return;
    printf( "Finished reading %d networks. ", Cba_ManNtkNum(p) );
    printf( "Memory = %.2f MB. ", 1.0*Cba_ManMemory(p)/(1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
//    Abc_NamPrint( p->pDesign->pNames );
    Cba_PrsWriteBlif( "aga/ray/ray_hie_oper_out.blif", p );
    Cba_ManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

