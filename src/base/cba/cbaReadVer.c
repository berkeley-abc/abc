/**CFile****************************************************************

  FileName    [cbaReadVer.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaReadVer.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"
#include "cbaPrs.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Verilog keywords
typedef enum { 
    CBA_VER_NONE = 0,  // 0:  unused
    CBA_VER_MODULE,    // 1:  module
    CBA_VER_INOUT,     // 2:  inout
    CBA_VER_INPUT,     // 3:  input
    CBA_VER_OUTPUT,    // 4:  output
    CBA_VER_WIRE,      // 5:  wire
    CBA_VER_ASSIGN,    // 6:  assign
    CBA_VER_REG,       // 7:  reg
    CBA_VER_ALWAYS,    // 8:  always
    CBA_VER_DEFPARAM,  // 9:  always
    CBA_VER_BEGIN,     // 10: begin
    CBA_VER_END,       // 11: end
    CBA_VER_ENDMODULE, // 12: endmodule
    CBA_VER_UNKNOWN    // 13: unknown
} Cba_VerType_t;

const char * s_VerTypes[CBA_VER_UNKNOWN+1] = {
    NULL,              // 0:  unused
    "module",          // 1:  module
    "inout",           // 2:  inout
    "input",           // 3:  input
    "output",          // 4:  output
    "wire",            // 5:  wire
    "assign",          // 6:  assign
    "reg",             // 7:  reg
    "always",          // 8:  always
    "defparam",        // 9:  defparam
    "begin",           // 10: begin
    "end",             // 11: end
    "endmodule",       // 12: endmodule
    NULL               // 13: unknown 
};

static inline void Cba_PrsAddVerilogDirectives( Cba_Prs_t * p )
{
    int i;
    for ( i = 1; s_VerTypes[i]; i++ )
        Abc_NamStrFindOrAdd( p->pDesign->pNames, (char *)s_VerTypes[i],   NULL );
    assert( Abc_NamObjNumMax(p->pDesign->pNames) == i );
}


// character recognition 
static inline int Cba_IsSpace( char c )   { return (c == ' ' || c == '\n' || c == '\t' || c == '\r');                           }
static inline int Cba_IsDigit( char c )   { return (c >= '0' && c <= '9');                                                      }
static inline int Cba_IsDigitB( char c )  { return (c >= '0' && c <= '1');                                                      }
static inline int Cba_IsDigitH( char c )  { return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f');  }
static inline int Cba_IsChar( char c )    { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');                            }
static inline int Cba_IsSymb1( char c )   { return Cba_IsChar(c) || c == '_';                                                   }
static inline int Cba_IsSymb2( char c )   { return Cba_IsSymb1(c) || Cba_IsDigit(c) || c == '$';                                }
static inline int Cba_IsSymb( char c )    { return c >= 33 && c <= 126;                                                         }
static inline int Cba_IsSymbC( char c )   { return Cba_IsDigit(c) || c == '\'' || c == 'b' || c == 'h' || c == 'd';             }


static inline int Cba_PrsOk( Cba_Prs_t * p )                { return p->pCur < p->pLimit && !p->ErrorStr[0]; }
static inline int Cba_PrsIsChar( Cba_Prs_t * p, char c )    { return *p->pCur == c;                          }
static inline int Cba_PrsIsDigit( Cba_Prs_t * p )           { return Cba_IsDigit(*p->pCur);                  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

// collect predefined models names
const char * s_KnownModels[100] = {
    NULL,
    "VERIFIC_",
    "reduce_",
    "add_",
    "mult_",
    "Select_",
    "LessThan_",
    "Decoder_",
    "Mux_",
    "ReadPort_",
    "WritePort_",
    "ClockedWritePort_",
    NULL
};

// check if it is a known module
static inline int Cba_PrsIsKnownModule( Cba_Prs_t * p, char * pName )
{
    int i;
    for ( i = 1; s_KnownModels[i]; i++ )
        if ( !strncmp(pName, s_KnownModels[i], strlen(s_KnownModels[i])) )
            return 1;
    return 0;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

// skip any number of spaces and comments
static inline int Cba_PrsUtilSkipSpaces( Cba_Prs_t * p )
{
    while ( *p->pCur )
    {
        while ( Cba_IsSpace(*p->pCur) ) 
            p->pCur++;
        if ( p->pCur[0] == '/' && p->pCur[1] == '/' )
        {
            for ( p->pCur += 2; *p->pCur; p->pCur++ )
                if ( p->pCur[0] == '\n' )
                    { p->pCur++; break; }
        }
        else if ( p->pCur[0] == '/' && p->pCur[1] == '*' )
        {
            for ( p->pCur += 2; *p->pCur; p->pCur++ )
                if ( p->pCur[0] == '*'  && p->pCur[1] == '/' )
                    { p->pCur++; p->pCur++; break; }
        }
        else return 1;
    }
    return 0;
}
// skip everything including comments until the given char
static inline int Cba_PrsUtilSkipUntilChar( Cba_Prs_t * p, char c )
{
    while ( *p->pCur )
    {
        if ( *p->pCur == c )
            return 1;
        if ( p->pCur[0] == '/' && p->pCur[1] == '/' ) // comment
        {
            for ( p->pCur += 2; *p->pCur; p->pCur++ )
                if ( p->pCur[0] == '\n' )
                    break;
        }
        else if ( p->pCur[0] == '/' && p->pCur[1] == '*' ) // comment
        {
            for ( p->pCur += 2; *p->pCur; p->pCur++ )
                if ( p->pCur[0] == '*'  && p->pCur[1] == '/' )
                    { p->pCur++; break; }
        }
        else if ( p->pCur[0] == '\\' ) // name
        {
            for ( p->pCur++; *p->pCur; p->pCur++ )
                if ( p->pCur[0] == ' ' )
                    break;
        }
        if ( *p->pCur == 0 )
            return 0;
        p->pCur++;
    }
    return 0;
}
// skip everything including comments until the given word
static inline int Cba_PrsUtilSkipUntilWord( Cba_Prs_t * p, char * pWord )
{
    char * pPlace = strstr( p->pCur, pWord );
    if ( pPlace == NULL )
        return 0;
    p->pCur = pPlace;
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

static inline int Cba_PrsReadName( Cba_Prs_t * p )
{
    char * pStart = p->pCur;
    if ( *p->pCur == '\\' ) // escaped name
    {
        pStart = ++p->pCur;
        while ( !Cba_IsSpace(*p->pCur) ) 
            p->pCur++;
    }
    else if ( Cba_IsDigit(*p->pCur) ) // constant
    {
        while ( Cba_IsDigit(*p->pCur) ) 
            p->pCur++;
        if ( *p->pCur != '\'' )
            return Cba_PrsErrorSet(p, "Cannot read constant.", 0);
        p->pCur++;
        if ( *p->pCur == 'b' )
            while ( Cba_IsDigitB(*p->pCur) ) 
                p->pCur++;
        else if ( *p->pCur == 'd' )
            while ( Cba_IsDigit(*p->pCur) ) 
                p->pCur++;
        else if ( *p->pCur == 'h' )
            while ( Cba_IsDigitH(*p->pCur) ) 
                p->pCur++;
        else
            return Cba_PrsErrorSet(p, "Cannot read radix of constant.", 0);
    }
    else // simple name
    {
        if ( !Cba_IsSymb1(*p->pCur) )
            return Cba_PrsErrorSet(p, "Cannot read first character of a name.", 0);
        while ( Cba_IsSymb2(*p->pCur) ) 
            p->pCur++;
    }
    if ( pStart == p->pCur )
        return Cba_PrsErrorSet(p, "Cannot read name.", 0);
    return Abc_NamStrFindOrAddLim( p->pDesign->pNames, pStart, p->pCur, NULL );
}

static inline int Cba_PrsReadRange( Cba_Prs_t * p )
{
    if ( !Cba_PrsIsChar(p, '[') )
        return 0;
    Vec_StrClear( p->vCover );
    Vec_StrPush( p->vCover, *p->pCur++ );
    Cba_PrsUtilSkipSpaces( p );
    if ( !Cba_PrsIsDigit(p) )     return Cba_PrsErrorSet(p, "Cannot read digit in range specification.", 2);
    while ( Cba_PrsIsDigit(p) )
        Vec_StrPush( p->vCover, *p->pCur++ );
    Cba_PrsUtilSkipSpaces( p );
    if ( Cba_PrsIsChar(p, ':') )
    {
        Vec_StrPush( p->vCover, *p->pCur++ );
        if ( !Cba_PrsIsDigit(p) ) return Cba_PrsErrorSet(p, "Cannot read digit in range specification.", 2);
        while ( Cba_PrsIsDigit(p) )
            Vec_StrPush( p->vCover, *p->pCur++ );
        Cba_PrsUtilSkipSpaces( p );
    }
    if ( !Cba_PrsIsChar(p, ']') ) return Cba_PrsErrorSet(p, "Cannot read closing brace in range specification.", 2);
    Vec_StrPush( p->vCover, *p->pCur++ );
    return Abc_NamStrFindOrAddLim( p->pDesign->pNames, Vec_StrArray(p->vCover), Vec_StrArray(p->vCover)+Vec_StrSize(p->vCover), NULL );
}
static inline void Cba_PrsReadSignalList( Cba_Prs_t * p, Vec_Int_t * vTemp )
{
    int NameId, RangeId;
    Vec_IntClear( vTemp );
    while ( 1 )
    {
        Cba_PrsUtilSkipSpaces( p );
        NameId  = Cba_PrsReadName( p );
        Cba_PrsUtilSkipSpaces( p );
        RangeId = Cba_PrsReadRange( p );
        Vec_IntPushTwo( vTemp, NameId, RangeId );
        Cba_PrsUtilSkipSpaces( p );
        if ( !Cba_PrsIsChar(p, ',') )
            break;
        p->pCur++;
    }
}
static inline int Cba_PrsReadDeclaration( Cba_Prs_t * p, int Type )
{
    int NameId, RangeId, RangeIdTemp;
    Vec_Int_t * vSigs[4] = { p->vInoutsCur, p->vInputsCur, p->vOutputsCur, p->vWiresCur };
    assert( Type >= CBA_VER_INOUT && Type <= CBA_VER_WIRE );
    Cba_PrsUtilSkipSpaces( p );
    RangeId = Cba_PrsReadRange( p );
    Cba_PrsReadSignalList( p, p->vTemp );
    Vec_IntForEachEntryDouble( p->vTemp, NameId, RangeId, RangeIdTemp )
    {
        if ( !RangeIdTemp )      return Cba_PrsErrorSet(p, "Range is specified twice in the declaration.", 0);
        Vec_IntPushTwo( vSigs[Type - CBA_VER_INOUT], NameId, RangeId );
    }
    return 1;
}
static inline int Cba_PrsReadConcat( Cba_Prs_t * p )
{
    int iToken = Vec_WecSize( p->vFaninsCur );
    assert( Cba_PrsIsChar(p, '{') );
    p->pCur++;
    Cba_PrsReadSignalList( p, p->vTemp2 );
    if ( !Cba_PrsIsChar(p, '}') )  return Cba_PrsErrorSet(p, "Cannot read concatenation.", 0);
    p->pCur++;
    // assign
    Vec_IntPush( p->vTypesCur, CBA_PRS_CONCAT );
    Vec_IntPush( p->vFuncsCur, 0 );
    Vec_IntPush( p->vInstIdsCur, 0 );
    Cba_PrsSetupVecInt( p, Vec_WecPushLevel(p->vFaninsCur), p->vTemp2 );
    return iToken;
}

static inline int Cba_PrsReadInstance( Cba_Prs_t * p, int Func )
{
    // have to assign Type, Func, InstId, vFanins
    int FormId, NameId, RangeId, Type, InstId;
    Vec_IntClear( p->vTemp );
    Cba_PrsUtilSkipSpaces( p );
    if ( Cba_PrsIsChar(p, '(') ) // node
    {
        Type = CBA_PRS_NODE;
        InstId = 0;
        p->pCur++;
        while ( 1 )
        {
            Cba_PrsUtilSkipSpaces( p );
            if ( Cba_PrsIsChar(p, '{') )
            {
                NameId = 0;
                RangeId = Cba_PrsReadConcat( p );
            }
            else
            {
                NameId  = Cba_PrsReadName( p );
                RangeId = Cba_PrsReadRange( p );
            }
            Vec_IntPushTwo( p->vTemp, NameId, RangeId );
            Cba_PrsUtilSkipSpaces( p );
            if ( Cba_PrsIsChar(p, ')') )
                break;
            if ( !Cba_PrsIsChar(p, ',') ) return Cba_PrsErrorSet(p, "Expecting comma in the instance definition.", 2);
            p->pCur++;
        }
    }
    else // box
    {
        Type = CBA_PRS_BOX;
        InstId = Cba_PrsReadName( p );
        Cba_PrsUtilSkipSpaces( p );
        if ( !Cba_PrsIsChar(p, '(') ) return Cba_PrsErrorSet(p, "Expecting opening paranthesis in the instance definition.", 2);
        p->pCur++;
        while ( 1 )
        {
            Cba_PrsUtilSkipSpaces( p );
            if ( !Cba_PrsIsChar(p, '.') ) return Cba_PrsErrorSet(p, "Expecting dot before the formal name.", 2);
            p->pCur++;
            FormId = Cba_PrsReadName( p );
            Cba_PrsUtilSkipSpaces( p );
            if ( !Cba_PrsIsChar(p, '(') ) return Cba_PrsErrorSet(p, "Expecting opening paranthesis after the formal name.", 2);
            p->pCur++;
            Cba_PrsUtilSkipSpaces( p );
            if ( Cba_PrsIsChar(p, '{') )
            {
                NameId = 0;
                RangeId = Cba_PrsReadConcat( p );
            }
            else
            {
                NameId  = Cba_PrsReadName( p );
                RangeId = Cba_PrsReadRange( p );
            }
            Vec_IntPushTwo( p->vTemp, NameId, RangeId );
            Cba_PrsUtilSkipSpaces( p );
            if ( !Cba_PrsIsChar(p, ')') ) return Cba_PrsErrorSet(p, "Expecting opening paranthesis after the acctual name.", 2);
            p->pCur++;
            Cba_PrsUtilSkipSpaces( p );
            if ( Cba_PrsIsChar(p, ')') )
                break;
            if ( !Cba_PrsIsChar(p, ',') ) return Cba_PrsErrorSet(p, "Expecting comma in the instance definition.", 2);
            p->pCur++;
        }
    }
    // assign
    Vec_IntPush( p->vTypesCur, Type );
    Vec_IntPush( p->vFuncsCur, Func );
    Vec_IntPush( p->vInstIdsCur, InstId );
    Cba_PrsSetupVecInt( p, Vec_WecPushLevel(p->vFaninsCur), p->vTemp );
    return 0;
}

// this procedure can return:
// 0 = reached end-of-file; 1 = successfully parsed; 2 = failed and skipped; 3 = error (failed and could not skip)
static inline int Cba_PrsReadModule( Cba_Prs_t * p )
{
    int fKnown, iToken, iNameId;
    assert( Vec_IntSize(p->vInputsCur) == 0 && Vec_IntSize(p->vOutputsCur) == 0 );
    Cba_PrsUtilSkipSpaces( p );
    if ( !Cba_PrsOk(p) )          return 0;
    // read keyword
    iToken = Cba_PrsReadName( p );
    if (iToken != CBA_VER_MODULE) return Cba_PrsErrorSet(p, "Cannot read \"module\" keyword.", 3);
    Cba_PrsUtilSkipSpaces( p );
    if ( !Cba_PrsOk(p) )          return Cba_PrsErrorSet(p, "Module declaration ends abruptly.", 3);
    // read module name
    iToken = iNameId = Cba_PrsReadName( p );
    Cba_PrsUtilSkipSpaces( p );
    if ( !Cba_PrsOk(p) )          return Cba_PrsErrorSet(p, "Module declaration ends abruptly.", 3);
    // check if module is known
    fKnown = Cba_PrsIsKnownModule( p, Abc_NamStr(p->pDesign->pNames, iNameId) );
    // skip arguments
    Cba_PrsUtilSkipSpaces( p );
    if ( !Cba_PrsOk(p) )          return Cba_PrsErrorSet(p, "Module declaration ends abruptly.", 3);
    if ( !Cba_PrsIsChar(p, '(') ) return Cba_PrsErrorSet(p, "Cannot find \"(\" in the argument declaration.", 3);
    Cba_PrsUtilSkipUntilChar( p, ')' );
    if ( !Cba_PrsOk(p) )          return Cba_PrsErrorSet(p, "Module declaration ends abruptly.", 3);
    assert( *p->pCur == ')' );
    // find semicolumn
    p->pCur++;
    Cba_PrsUtilSkipSpaces( p );
    if ( !Cba_PrsOk(p) )          return Cba_PrsErrorSet(p, "Module declaration ends abruptly.", 3);
    // read declarations and instances
    while ( Cba_PrsIsChar(p, ';') )
    {
        p->pCur++;
        iToken = Cba_PrsReadName( p );
        if ( iToken == CBA_VER_ENDMODULE )
        {
            Cba_PrsAddCurrentModel( p, iNameId );
            return 0;
        }
        if ( iToken == CBA_VER_ALWAYS )
        {
            Cba_PrsUtilSkipUntilWord( p, "endmodule" );
            if ( !Cba_PrsOk(p) )  return Cba_PrsErrorSet(p, "Module definition ends abruptly.", 3);
            Cba_PrsAddCurrentModel( p, iNameId );
            return 2;
        }
        if ( iToken >= CBA_VER_INOUT && iToken <= CBA_VER_WIRE ) // declaration
            Cba_PrsReadDeclaration( p, iToken );
        else if ( iToken == CBA_VER_REG || iToken == CBA_VER_DEFPARAM ) // unsupported keywords
            Cba_PrsUtilSkipUntilChar( p, ';' );
        else if ( !fKnown ) // read instance
            Cba_PrsReadInstance( p, iToken );
        else // skip known instance
            Cba_PrsUtilSkipUntilChar( p, ';' );
    }
    return Cba_PrsErrorSet(p, "Cannot find \";\" in the module definition.", 3);

}
static inline int Cba_PrsReadDesign( Cba_Prs_t * p )
{
    while ( 1 )
    {
        int RetValue = Cba_PrsReadModule( p );
        if ( RetValue == 0 ) // success
            return 1;
        if ( RetValue == 1 ) // end of file
            continue;
        if ( RetValue == 2 ) // failed and skipped
            continue;
        if ( RetValue == 3 ) // error
            return 0;
        assert( 0 );
    }
    return 0;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cba_Man_t * Cba_PrsReadVerilog( char * pFileName )
{
    Cba_Man_t * pDesign = NULL;
    Cba_Prs_t * p = Cba_PrsAlloc( pFileName );
    if ( p == NULL )
        return NULL;
    Cba_PrsAddVerilogDirectives( p );
    Cba_PrsReadDesign( p );
    if ( Cba_PrsErrorPrint(p) )
        ABC_SWAP( Cba_Man_t *, pDesign, p->pDesign );
    Cba_PrsFree( p );
    return pDesign;
}
void Cba_PrsTest( char * pFileName )
{
    Cba_Man_t * pDes = Cba_PrsReadVerilog( pFileName );
    Cba_PrsWriteVerilog( "__Test__.v", pDes );
    Cba_ManFree( pDes );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

