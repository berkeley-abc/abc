/**CFile****************************************************************

  FileName    [cbaReadBlif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [BLIF parser.]

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
    PRS_BLIF_NONE = 0, // 0:   unused
    PRS_BLIF_MODEL,    // 1:   .model
    PRS_BLIF_INOUTS,   // 2:   .inouts
    PRS_BLIF_INPUTS,   // 3:   .inputs
    PRS_BLIF_OUTPUTS,  // 4:   .outputs
    PRS_BLIF_NAMES,    // 5:   .names
    PRS_BLIF_SUBCKT,   // 6:   .subckt
    PRS_BLIF_GATE,     // 7:   .gate
    PRS_BLIF_LATCH,    // 8:   .latch
    PRS_BLIF_SHORT,    // 9:   .short
    PRS_BLIF_END,      // 10:  .end
    PRS_BLIF_UNKNOWN   // 11:  unknown
} Cba_BlifType_t;

const char * s_BlifTypes[PRS_BLIF_UNKNOWN+1] = {
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

static inline void Prs_NtkAddBlifDirectives( Prs_Man_t * p )
{
    int i;
    for ( i = 1; s_BlifTypes[i]; i++ )
        Abc_NamStrFindOrAdd( p->pStrs, (char *)s_BlifTypes[i], NULL );
    assert( Abc_NamObjNumMax(p->pStrs) == i );
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
static inline int  Prs_CharIsSpace( char c )                { return c == ' ' || c == '\t' || c == '\r';              }
static inline int  Prs_CharIsStop( char c )                 { return c == '#' || c == '\\' || c == '\n' || c == '=';  }
static inline int  Prs_CharIsLit( char c )                  { return c == '0' || c == '1'  || c == '-';               }

static inline int  Prs_ManIsSpace( Prs_Man_t * p )          { return Prs_CharIsSpace(*p->pCur);                       }
static inline int  Prs_ManIsStop( Prs_Man_t * p )           { return Prs_CharIsStop(*p->pCur);                        }
static inline int  Prs_ManIsLit( Prs_Man_t * p )            { return Prs_CharIsLit(*p->pCur);                         }

static inline int  Prs_ManIsChar( Prs_Man_t * p, char c )   { return *p->pCur == c;                                   }
static inline int  Prs_ManIsChar2( Prs_Man_t * p, char c )  { return *p->pCur++ == c;                                 }

static inline void Prs_ManSkip( Prs_Man_t * p )             { p->pCur++;                                              }
static inline char Prs_ManSkip2( Prs_Man_t * p )            { return *p->pCur++;                                      }


/**Function*************************************************************

  Synopsis    [Reading names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Prs_ManSkipToChar( Prs_Man_t * p, char c )  
{ 
    while ( !Prs_ManIsChar(p, c) ) 
        Prs_ManSkip(p);
}
static inline void Prs_ManSkipSpaces( Prs_Man_t * p )
{
    while ( 1 )
    {
        while ( Prs_ManIsSpace(p) )
            Prs_ManSkip(p);
        if ( Prs_ManIsChar(p, '\\') )
        {
            Prs_ManSkipToChar( p, '\n' );
            Prs_ManSkip(p);
            continue;
        }
        if ( Prs_ManIsChar(p, '#') )  
            Prs_ManSkipToChar( p, '\n' );
        break;
    }
    assert( !Prs_ManIsSpace(p) );
}
static inline int Prs_ManReadName( Prs_Man_t * p )
{
    char * pStart;
    Prs_ManSkipSpaces( p );
    if ( Prs_ManIsChar(p, '\n') )
        return 0;
    pStart = p->pCur;
    while ( !Prs_ManIsSpace(p) && !Prs_ManIsStop(p) )
        Prs_ManSkip(p);
    if ( pStart == p->pCur )
        return 0;
    return Abc_NamStrFindOrAddLim( p->pStrs, pStart, p->pCur, NULL );
}
static inline int Prs_ManReadList( Prs_Man_t * p, Vec_Int_t * vOrder, int Type )
{
    int iToken;
    Vec_IntClear( &p->vTemp );
    while ( (iToken = Prs_ManReadName(p)) )
    {
        Vec_IntPush( &p->vTemp, iToken );
        Vec_IntPush( vOrder, Abc_Var2Lit2(iToken, Type) );
    }
    if ( Vec_IntSize(&p->vTemp) == 0 )                return Prs_ManErrorSet(p, "Signal list is empty.", 1);
    return 0;
}
static inline int Prs_ManReadList2( Prs_Man_t * p )
{
    int iToken;
    Vec_IntClear( &p->vTemp );
    while ( (iToken = Prs_ManReadName(p)) )
        Vec_IntPushTwo( &p->vTemp, 0, iToken );
    if ( Vec_IntSize(&p->vTemp) == 0 )                return Prs_ManErrorSet(p, "Signal list is empty.", 1);
    return 0;
}
static inline int Prs_ManReadList3( Prs_Man_t * p )
{
    Vec_IntClear( &p->vTemp );
    while ( !Prs_ManIsChar(p, '\n') )
    {
        int iToken = Prs_ManReadName(p);
        if ( iToken == 0 )              return Prs_ManErrorSet(p, "Cannot read formal name.", 1);
        Vec_IntPush( &p->vTemp, iToken );
        Prs_ManSkipSpaces( p );
        if ( !Prs_ManIsChar2(p, '=') )  return Prs_ManErrorSet(p, "Cannot find symbol \"=\".", 1);
        iToken = Prs_ManReadName(p);
        if ( iToken == 0 )              return Prs_ManErrorSet(p, "Cannot read actual name.", 1);
        Vec_IntPush( &p->vTemp, iToken );
        Prs_ManSkipSpaces( p );
    }
    if ( Vec_IntSize(&p->vTemp) == 0 )  return Prs_ManErrorSet(p, "Cannot read a list of formal/actual names.", 1);
    if ( Vec_IntSize(&p->vTemp) % 2  )  return Prs_ManErrorSet(p, "The number of formal/actual names is not even.", 1);
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Prs_ManReadCube( Prs_Man_t * p )
{
    assert( Prs_ManIsLit(p) );
    while ( Prs_ManIsLit(p) )
        Vec_StrPush( &p->vCover, Prs_ManSkip2(p) );
    Prs_ManSkipSpaces( p );
    if ( Prs_ManIsChar(p, '\n') )
    {
        if ( Vec_StrSize(&p->vCover) != 1 )           return Prs_ManErrorSet(p, "Cannot read cube.", 1);
        // fix single literal cube by adding space
        Vec_StrPush( &p->vCover, Vec_StrEntry(&p->vCover,0) );
        Vec_StrWriteEntry( &p->vCover, 0, ' ' );
        Vec_StrPush( &p->vCover, '\n' );
        return 0;
    }
    if ( !Prs_ManIsLit(p) )                           return Prs_ManErrorSet(p, "Cannot read output literal.", 1);
    Vec_StrPush( &p->vCover, ' ' );
    Vec_StrPush( &p->vCover, Prs_ManSkip2(p) );
    Vec_StrPush( &p->vCover, '\n' );
    Prs_ManSkipSpaces( p );
    if ( !Prs_ManIsChar(p, '\n') )                    return Prs_ManErrorSet(p, "Cannot read end of cube.", 1);
    return 0;
}
static inline void Prs_ManSaveCover( Prs_Man_t * p )
{
    int iToken;
    if ( Vec_StrSize(&p->vCover) == 0 )
        p->pNtk->fHasC0s = 1;
    else if ( Vec_StrSize(&p->vCover) == 2 )
    {
        if ( Vec_StrEntryLast(&p->vCover) == '0' )
            p->pNtk->fHasC0s = 1;
        else if ( Vec_StrEntryLast(&p->vCover) == '1' )
            p->pNtk->fHasC1s = 1;
        else assert( 0 );
    }
    assert( Vec_StrSize(&p->vCover) > 0 );
    Vec_StrPush( &p->vCover, '\0' );
    //iToken = Abc_NamStrFindOrAdd( p->pStrs, Vec_StrArray(&p->vCover), NULL );
    iToken = Ptr_SopToType( Vec_StrArray(&p->vCover) );
    Vec_StrClear( &p->vCover );
    // set the cover to the module of this box
    assert( Prs_BoxNtk(p->pNtk, Prs_NtkBoxNum(p->pNtk)-1) == 1 ); // default const 0
    Prs_BoxSetNtk( p->pNtk, Prs_NtkBoxNum(p->pNtk)-1, iToken );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Prs_ManReadInouts( Prs_Man_t * p )
{
    if ( Prs_ManReadList(p, &p->pNtk->vOrder, 3) )    return 1;
    Vec_IntAppend( &p->pNtk->vInouts, &p->vTemp );
    return 0;
}
static inline int Prs_ManReadInputs( Prs_Man_t * p )
{
    if ( Prs_ManReadList(p, &p->pNtk->vOrder, 1) )    return 1;
    Vec_IntAppend( &p->pNtk->vInputs, &p->vTemp );
    return 0;
}
static inline int Prs_ManReadOutputs( Prs_Man_t * p )
{
    if ( Prs_ManReadList(p, &p->pNtk->vOrder, 2) )    return 1;
    Vec_IntAppend( &p->pNtk->vOutputs, &p->vTemp );
    return 0;
}
static inline int Prs_ManReadNode( Prs_Man_t * p )
{
    if ( Prs_ManReadList2(p) )   return 1;
    // save results
    Prs_NtkAddBox( p->pNtk, 1, 0, &p->vTemp ); // default const 0 function
    return 0;
}
static inline int Prs_ManReadBox( Prs_Man_t * p, int fGate )
{
    int iToken = Prs_ManReadName(p);
    if ( iToken == 0 )           return Prs_ManErrorSet(p, "Cannot read model name.", 1);
    if ( Prs_ManReadList3(p) )   return 1;
    // save results
    Prs_NtkAddBox( p->pNtk, iToken, 0, &p->vTemp );
    if ( fGate ) p->pNtk->fMapped = 1;
    return 0;
}
static inline int Prs_ManReadLatch( Prs_Man_t * p )
{
    int iToken = Prs_ManReadName(p);
    Vec_IntClear( &p->vTemp );
    if ( iToken == 0 )                 return Prs_ManErrorSet(p, "Cannot read latch input.", 1);
    Vec_IntWriteEntry( &p->vTemp, 1, iToken );
    iToken = Prs_ManReadName(p);
    if ( iToken == 0 )                 return Prs_ManErrorSet(p, "Cannot read latch output.", 1);
    Vec_IntWriteEntry( &p->vTemp, 0, iToken );
    Prs_ManSkipSpaces( p );
    if ( Prs_ManIsChar(p, '0') )
        iToken = 0;
    else if ( Prs_ManIsChar(p, '1') )
        iToken = 1;
    else 
        iToken = 2;
    Prs_ManSkipToChar( p, '\n' );
    // save results
    Prs_NtkAddBox( p->pNtk, -1, iToken, &p->vTemp ); // -1 stands for latch
    return 0;
}
static inline int Prs_ManReadShort( Prs_Man_t * p )
{
    int iToken = Prs_ManReadName(p);
    Vec_IntClear( &p->vTemp );
    if ( iToken == 0 )                 return Prs_ManErrorSet(p, "Cannot read .short input.", 1);
    Vec_IntWriteEntry( &p->vTemp, 1, iToken );
    iToken = Prs_ManReadName(p);
    if ( iToken == 0 )                 return Prs_ManErrorSet(p, "Cannot read .short output.", 1);
    Vec_IntWriteEntry( &p->vTemp, 0, iToken );
    Prs_ManSkipSpaces( p );
    if ( !Prs_ManIsChar(p, '\n') )     return Prs_ManErrorSet(p, "Trailing symbols on .short line.", 1);
    // save results
    iToken = Abc_NamStrFindOrAdd( p->pStrs, "1 1\n", NULL );
    Prs_NtkAddBox( p->pNtk, iToken, 0, &p->vTemp );
    return 0;
}
static inline int Prs_ManReadModel( Prs_Man_t * p )
{
    int iToken;
    if ( p->pNtk != NULL )                         return Prs_ManErrorSet(p, "Parsing previous model is unfinished.", 1);
    iToken = Prs_ManReadName(p);
    if ( iToken == 0 )                             return Prs_ManErrorSet(p, "Cannot read model name.", 1);
    Prs_ManInitializeNtk( p, iToken, 0 );
    Prs_ManSkipSpaces( p );
    if ( !Prs_ManIsChar(p, '\n') )                 return Prs_ManErrorSet(p, "Trailing symbols on .model line.", 1);
    return 0;
}
static inline int Prs_ManReadEnd( Prs_Man_t * p )
{
    if ( p->pNtk == 0 )                            return Prs_ManErrorSet(p, "Directive .end without .model.", 1);
    //printf( "Saving model \"%s\".\n", Abc_NamStr(p->pStrs, p->iModuleName) );
    Prs_ManFinalizeNtk( p );
    Prs_ManSkipSpaces( p );
    if ( !Prs_ManIsChar(p, '\n') )                 return Prs_ManErrorSet(p, "Trailing symbols on .end line.", 1);
    return 0;
}

static inline int Prs_ManReadDirective( Prs_Man_t * p )
{
    int iToken;
    if ( !Prs_ManIsChar(p, '.') )
        return Prs_ManReadCube( p );
    if ( Vec_StrSize(&p->vCover) > 0 ) // SOP was specified for the previous node
        Prs_ManSaveCover( p );
    iToken = Prs_ManReadName( p );  
    if ( iToken == PRS_BLIF_MODEL )
        return Prs_ManReadModel( p );
    if ( iToken == PRS_BLIF_INOUTS )
        return Prs_ManReadInouts( p );
    if ( iToken == PRS_BLIF_INPUTS )
        return Prs_ManReadInputs( p );
    if ( iToken == PRS_BLIF_OUTPUTS )
        return Prs_ManReadOutputs( p );
    if ( iToken == PRS_BLIF_NAMES )
        return Prs_ManReadNode( p );
    if ( iToken == PRS_BLIF_SUBCKT )
        return Prs_ManReadBox( p, 0 );
    if ( iToken == PRS_BLIF_GATE )
        return Prs_ManReadBox( p, 1 );
    if ( iToken == PRS_BLIF_LATCH )
        return Prs_ManReadLatch( p );
    if ( iToken == PRS_BLIF_SHORT )
        return Prs_ManReadShort( p );
    if ( iToken == PRS_BLIF_END )
        return Prs_ManReadEnd( p );
    printf( "Cannot read directive \"%s\".\n", Abc_NamStr(p->pStrs, iToken) );
    return 1;
}
static inline int Prs_ManReadLines( Prs_Man_t * p )
{
    while ( p->pCur[1] != '\0' )
    {
        assert( Prs_ManIsChar(p, '\n') );
        Prs_ManSkip(p);
        Prs_ManSkipSpaces( p );
        if ( Prs_ManIsChar(p, '\n') )
            continue;
        if ( Prs_ManReadDirective(p) )   
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
Vec_Ptr_t * Prs_ManReadBlif( char * pFileName )
{
    Vec_Ptr_t * vPrs = NULL;
    Prs_Man_t * p = Prs_ManAlloc( pFileName );
    if ( p == NULL )
        return NULL;
    Prs_NtkAddBlifDirectives( p );
    Prs_ManReadLines( p );
    if ( Prs_ManErrorPrint(p) )
        ABC_SWAP( Vec_Ptr_t *, vPrs, p->vNtks );
    Prs_ManFree( p );
    return vPrs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Prs_ManReadBlifTest()
{
    abctime clk = Abc_Clock();
    extern void Prs_ManWriteBlif( char * pFileName, Vec_Ptr_t * vPrs );
//    Vec_Ptr_t * vPrs = Prs_ManReadBlif( "aga/ray/ray_hie_oper.blif" );
    Vec_Ptr_t * vPrs = Prs_ManReadBlif( "c/hie/dump/1/netlist_1_out8.blif" );
    if ( !vPrs ) return;
    printf( "Finished reading %d networks. ", Vec_PtrSize(vPrs) );
    printf( "NameIDs = %d. ", Abc_NamObjNumMax(Prs_ManNameMan(vPrs)) );
    printf( "Memory = %.2f MB. ", 1.0*Prs_ManMemory(vPrs)/(1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
//    Abc_NamPrint( p->pStrs );
    Prs_ManWriteBlif( "c/hie/dump/1/netlist_1_out8_out.blif", vPrs );
    Prs_ManVecFree( vPrs );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

