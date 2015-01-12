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
static inline int Cba_IsSpace( char c )   { return (c == ' ' || c == '\t' || c == '\r' || c == '\n');                           }
static inline int Cba_IsDigit( char c )   { return (c >= '0' && c <= '9');                                                      }
static inline int Cba_IsDigitB( char c )  { return (c == '0' || c == '1'  || c == 'x' || c == 'z');                             }
static inline int Cba_IsDigitH( char c )  { return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f');  }
static inline int Cba_IsChar( char c )    { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');                            }
static inline int Cba_IsSymb1( char c )   { return Cba_IsChar(c) || c == '_';                                                   }
static inline int Cba_IsSymb2( char c )   { return Cba_IsSymb1(c) || Cba_IsDigit(c) || c == '$';                                }

static inline int Cba_PrsIsChar( Cba_Prs_t * p, char c )    { return *p->pCur == c;                          }
static inline int Cba_PrsIsChar1( Cba_Prs_t * p, char c )   { return p->pCur[1] == c;                        }
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

// collect predefined modules names
const char * s_KnownModules[100] = {
    NULL,       // 0:  unused 
    "const",    // 1:  constant 
    "buf",      // 2:  buffer 
    "not",      // 3:  inverter 
    "and",      // 4:  AND 
    "nand",     // 5:  OR 
    "or",       // 6:  XOR 
    "nor",      // 7:  NAND 
    "xor",      // 8:  NOR 
    "xnor",     // 9: .XNOR 
    "mux",      // 10: MUX  
    "maj",      // 11: MAJ 

    "VERIFIC_",
    "wide_",
    "reduce_",
    "equal_",
    "not_equal_",
    "sub_",
    "add_",
    "mult_",
    "mux_",
    "Mux_",
    "Select_",
    "Decoder_",
    "LessThan_",
    "ReadPort_",
    "WritePort_",
    "ClockedWritePort_",
    NULL
};

// check if it is a known module
static inline int Cba_PrsIsKnownModule( Cba_Prs_t * p, char * pName )
{
    int i;
    for ( i = 1; s_KnownModules[i]; i++ )
        if ( !strncmp(pName, s_KnownModules[i], strlen(s_KnownModules[i])) )
            return i;
    return 0;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

// skips Verilog comments (returns 1 if some comments were skipped)
static inline int Cba_PrsUtilSkipComments( Cba_Prs_t * p )
{
    if ( !Cba_PrsIsChar(p, '/') )
        return 0;
    if ( Cba_PrsIsChar1(p, '/') )
    {
        for ( p->pCur += 2; p->pCur < p->pLimit; p->pCur++ )
            if ( Cba_PrsIsChar(p, '\n') )
                { p->pCur++; return 1; }
    }
    else if ( Cba_PrsIsChar1(p, '*') )
    {
        for ( p->pCur += 2; p->pCur < p->pLimit; p->pCur++ )
            if ( Cba_PrsIsChar(p, '*') && Cba_PrsIsChar1(p, '/') )
                { p->pCur++; p->pCur++; return 1; }
    }
    return 0;
}
static inline int Cba_PrsUtilSkipName( Cba_Prs_t * p )
{
    if ( !Cba_PrsIsChar(p, '\\') )
        return 0;
    for ( p->pCur++; p->pCur < p->pLimit; p->pCur++ )
        if ( Cba_PrsIsChar(p, ' ') )
            { p->pCur++; return 1; }
    return 0;
}

// skip any number of spaces and comments
static inline int Cba_PrsUtilSkipSpaces( Cba_Prs_t * p )
{
    while ( p->pCur < p->pLimit )
    {
        while ( Cba_IsSpace(*p->pCur) ) 
            p->pCur++;
        if ( !*p->pCur )
            return Cba_PrsErrorSet(p, "Unexpectedly reached end-of-file.", 1);
        if ( !Cba_PrsUtilSkipComments(p) )
            return 0;
    }
    return Cba_PrsErrorSet(p, "Unexpectedly reached end-of-file.", 1);
}
// skip everything including comments until the given char
static inline int Cba_PrsUtilSkipUntil( Cba_Prs_t * p, char c )
{
    while ( p->pCur < p->pLimit )
    {
        if ( Cba_PrsIsChar(p, c) )
            return 1;
        if ( Cba_PrsUtilSkipComments(p) )
            continue;
        if ( Cba_PrsUtilSkipName(p) )
            continue;
        p->pCur++;
    }
    return 0;
}
// skip everything including comments until the given word
static inline int Cba_PrsUtilSkipUntilWord( Cba_Prs_t * p, char * pWord )
{
    char * pPlace = strstr( p->pCur, pWord );
    if ( pPlace == NULL )  return 1;
    p->pCur = pPlace + strlen(pWord);
    return 0;
}

/* 
signal is a pair {NameId; RangeId}
if ( RangeId == 0 )  this is name without range
if ( RangeId == -1 ) this is constant
if ( RangeId == -2 ) this is concatenation
*/

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cba_PrsReadName( Cba_Prs_t * p )
{
    char * pStart = p->pCur;
    if ( Cba_PrsIsChar(p, '\\') ) // escaped name
    {
        pStart = ++p->pCur;
        while ( !Cba_PrsIsChar(p, ' ') ) 
            p->pCur++;
    }    
    else if ( Cba_IsSymb1(*p->pCur) ) // simple name
    {
        p->pCur++;
        while ( Cba_IsSymb2(*p->pCur) ) 
            p->pCur++;
    }
    else 
        return 0;
    return Abc_NamStrFindOrAddLim( p->pDesign->pNames, pStart, p->pCur, NULL );
}
static inline int Cba_PrsReadConstant( Cba_Prs_t * p )
{
    char * pStart = p->pCur;
    assert( Cba_PrsIsDigit(p) );
    while ( Cba_PrsIsDigit(p) ) 
        p->pCur++;
    if ( !Cba_PrsIsChar(p, '\'') )        return Cba_PrsErrorSet(p, "Cannot read constant.", 0);
    p->pCur++;
    if ( Cba_PrsIsChar(p, 'b') )
    {
        p->pCur++;
        while ( Cba_IsDigitB(*p->pCur) ) 
            p->pCur++;
    }
    else if ( Cba_PrsIsChar(p, 'h') )
    {
        p->pCur++;
        while ( Cba_IsDigitH(*p->pCur) ) 
            p->pCur++;
    }
    else if ( Cba_PrsIsChar(p, 'd') )
    {
        p->pCur++;
        while ( Cba_PrsIsDigit(p) ) 
            p->pCur++;
    }
    else                                  return Cba_PrsErrorSet(p, "Cannot read radix of constant.", 0);
    return Abc_NamStrFindOrAddLim( p->pDesign->pNames, pStart, p->pCur, NULL );
}
static inline int Cba_PrsReadRange( Cba_Prs_t * p )
{
    assert( Cba_PrsIsChar(p, '[') );
    Vec_StrClear( &p->vCover );
    Vec_StrPush( &p->vCover, *p->pCur++ );
    if ( Cba_PrsUtilSkipSpaces(p) )       return 0;
    if ( !Cba_PrsIsDigit(p) )             return Cba_PrsErrorSet(p, "Cannot read digit in range specification.", 0);
    while ( Cba_PrsIsDigit(p) )
        Vec_StrPush( &p->vCover, *p->pCur++ );
    if ( Cba_PrsUtilSkipSpaces(p) )      return 0;
    if ( Cba_PrsIsChar(p, ':') )
    {
        Vec_StrPush( &p->vCover, *p->pCur++ );
        if ( Cba_PrsUtilSkipSpaces(p) )   return 0;
        if ( !Cba_PrsIsDigit(p) )         return Cba_PrsErrorSet(p, "Cannot read digit in range specification.", 0);
        while ( Cba_PrsIsDigit(p) )
            Vec_StrPush( &p->vCover, *p->pCur++ );
        if ( Cba_PrsUtilSkipSpaces(p) )   return 0;
    }
    if ( !Cba_PrsIsChar(p, ']') )         return Cba_PrsErrorSet(p, "Cannot read closing brace in range specification.", 0);
    Vec_StrPush( &p->vCover, *p->pCur++ );
    Vec_StrPush( &p->vCover, '\0' );
    return Abc_NamStrFindOrAdd( p->pDesign->pNames, Vec_StrArray(&p->vCover), NULL );
}
static inline int Cba_PrsReadSignal( Cba_Prs_t * p, int * pName, int * pRange )
{
    *pName = *pRange = 0;
    if ( Cba_PrsUtilSkipSpaces(p) )       return 0;
    if ( Cba_PrsIsDigit(p) )
    {
        *pName = Cba_PrsReadConstant(p);
        if ( *pName == 0 )                return 0;
        if ( Cba_PrsUtilSkipSpaces(p) )   return 0;
        *pRange = -1;
        return 1;
    }
    *pName = Cba_PrsReadName( p );
    if ( *pName == 0 )                    
        return 1;
    if ( Cba_PrsUtilSkipSpaces(p) )       return 0;
    if ( !Cba_PrsIsChar(p, '[') )
        return 1;
    *pRange = Cba_PrsReadRange(p);
    if ( *pRange == 0 )                   return 0;
    if ( Cba_PrsUtilSkipSpaces(p) )       return 0;
    return 1;
}
static inline int Cba_PrsReadSignalList( Cba_Prs_t * p, Vec_Int_t * vTemp, char LastSymb )
{
    Vec_IntClear( vTemp );
    while ( 1 )
    {
        int NameId, RangeId;
        if ( !Cba_PrsReadSignal(p, &NameId, &RangeId) )  return 0;
        if ( NameId == 0 )                return Cba_PrsErrorSet(p, "Cannot read signal in the list.", 0);
        Vec_IntPushTwo( vTemp, NameId, RangeId );
        if ( Cba_PrsIsChar(p, LastSymb) ) break;
        if ( !Cba_PrsIsChar(p, ',') )     return Cba_PrsErrorSet(p, "Expecting comma in the list.", 0);
        p->pCur++;
    }
    assert( Vec_IntSize(vTemp) > 0 );
    assert( Vec_IntSize(vTemp) % 2 == 0 );
    return 1;
}
static inline int Cba_PrsReadConcat( Cba_Prs_t * p, Vec_Int_t * vTemp2 )
{
    assert( Cba_PrsIsChar(p, '{') );
    p->pCur++;
    if ( !Cba_PrsReadSignalList(p, vTemp2, '}') ) return 0;
    // check final
    assert( Cba_PrsIsChar(p, '}') );
    p->pCur++;
    // return special case
    if ( Vec_IntSize(vTemp2) == 2 )               return -1; // trivial concatentation
    assert( Vec_IntSize(vTemp2) > 2 );
    assert( Vec_IntSize(vTemp2) % 2 == 0 );
    // create new concatentation
    Vec_IntPush( &p->vTypesCur, CBA_PRS_CONCAT );
    Vec_IntPush( &p->vFuncsCur, 0 );
    Vec_IntPush( &p->vInstIdsCur, 0 );
    Vec_IntPush( &p->vFaninsCur, Cba_ManHandleArray(p->pDesign, vTemp2) ); 
    return Vec_IntSize(&p->vFaninsCur);
}
static inline int Cba_PrsReadSignalOrConcat( Cba_Prs_t * p, int * pName, int * pRange )
{
    if ( Cba_PrsUtilSkipSpaces(p) )       return 0;
    if ( Cba_PrsIsChar(p, '{') )
    {
        int Status = Cba_PrsReadConcat(p, &p->vTemp2);
        if ( Status == 0 )                return 0;
        *pName  = Status == -1 ? Vec_IntEntry( &p->vTemp2, 0 ) : Status;
        *pRange = Status == -1 ? Vec_IntEntry( &p->vTemp2, 1 ) : -2;
        if ( Cba_PrsUtilSkipSpaces(p) )   return 0;
    }
    else
    {
        if ( !Cba_PrsReadSignal(p, pName, pRange) )  return 0;
        if ( *pName == 0 )                return Cba_PrsErrorSet(p, "Cannot read formal name in the list.", 0);
    }
    return 1;
}
static inline int Cba_PrsReadSignalList1( Cba_Prs_t * p, Vec_Int_t * vTemp )
{
    Vec_IntClear( vTemp );
    while ( 1 )
    {
        int NameId, RangeId;
        if ( !Cba_PrsReadSignalOrConcat(p, &NameId, &RangeId) ) return 0;
        if ( NameId == 0 )                return Cba_PrsErrorSet(p, "Cannot read signal or concatenation in the list.", 0);
        Vec_IntPushTwo( vTemp, NameId, RangeId );
        if ( Cba_PrsIsChar(p, ')') )      break;
        if ( !Cba_PrsIsChar(p, ',') )     return Cba_PrsErrorSet(p, "Expecting comma in the list.", 0);
        p->pCur++;
    }
    p->pCur++;
    if ( Cba_PrsUtilSkipSpaces(p) )       return 0;
    if ( !Cba_PrsIsChar(p, ';') )         return Cba_PrsErrorSet(p, "Expecting semicolon in the instance.", 0);
    assert( Vec_IntSize(vTemp) > 0 );
    assert( Vec_IntSize(vTemp) % 2 == 0 );
    return 1;
}
static inline int Cba_PrsReadSignalList2( Cba_Prs_t * p, Vec_Int_t * vTemp )
{
    int FormId, NameId, RangeId;
    Vec_IntClear( vTemp );
    assert( Cba_PrsIsChar(p, '.') );
    while ( Cba_PrsIsChar(p, '.') )
    {
        p->pCur++;
        if ( !Cba_PrsReadSignal(p, &FormId, &RangeId) )  return 0;
        if ( FormId == 0 )                return Cba_PrsErrorSet(p, "Cannot read formal name of the instance.", 0);
        if ( RangeId != 0 )               return Cba_PrsErrorSet(p, "Formal signal cannot have range.", 0);
        if ( !Cba_PrsIsChar(p, '(') )     return Cba_PrsErrorSet(p, "Cannot read \"(\" in the instance.", 0);
        p->pCur++;
        if ( Cba_PrsUtilSkipSpaces(p) )   return 0;
        if ( !Cba_PrsReadSignalOrConcat(p, &NameId, &RangeId) )  return 0;
        if ( NameId == 0 )                return Cba_PrsErrorSet(p, "Cannot read actual name of the instance.", 0);
        if ( !Cba_PrsIsChar(p, ')') )     return Cba_PrsErrorSet(p, "Cannot read \")\" in the instance.", 0);
        p->pCur++;
        Vec_IntPush( vTemp, FormId );
        Vec_IntPushTwo( vTemp, NameId, RangeId );
        if ( Cba_PrsUtilSkipSpaces(p) )   return 0;
        if ( Cba_PrsIsChar(p, ')') )      break;
        if ( !Cba_PrsIsChar(p, ',') )     return Cba_PrsErrorSet(p, "Expecting comma in the instance.", 0);
        p->pCur++;
        if ( Cba_PrsUtilSkipSpaces(p) )   return 0;
    }
    p->pCur++;
    if ( Cba_PrsUtilSkipSpaces(p) )       return 0;
    if ( !Cba_PrsIsChar(p, ';') )         return Cba_PrsErrorSet(p, "Expecting semicolon in the instance.", 0);
    assert( Vec_IntSize(vTemp) > 0 );
    assert( Vec_IntSize(vTemp) % 3 == 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cba_PrsReadDeclaration( Cba_Prs_t * p, int Type )
{
    int NameId, RangeId, RangeIdTemp, i;
    Vec_Int_t * vSigs[4] = { &p->vInoutsCur, &p->vInputsCur, &p->vOutputsCur, &p->vWiresCur };
    assert( Type >= CBA_VER_INOUT && Type <= CBA_VER_WIRE );
    if ( Cba_PrsUtilSkipSpaces(p) )                                   return 0;
    RangeId = 0;
    if ( Cba_PrsIsChar(p, '[') && !(RangeId = Cba_PrsReadRange(p)) )  return 0;
    if ( !Cba_PrsReadSignalList( p, &p->vTemp, ';' ) )                return 0;
    Vec_IntForEachEntryDouble( &p->vTemp, NameId, RangeIdTemp, i )
    {
        if ( RangeIdTemp )                                            return Cba_PrsErrorSet(p, "Range is specified twice in the declaration.", 0);
        Vec_IntPushTwo( vSigs[Type - CBA_VER_INOUT], NameId, RangeId );
    }
    return 1;
}
static inline int Cba_PrsReadAssign( Cba_Prs_t * p )
{
    int OutName = 0, InName = 0, RangeId = 0, fCompl = 0, Oper = 0;
    Vec_IntClear( &p->vTemp );
    // read output name
    if ( !Cba_PrsReadSignal(p, &OutName, &RangeId) )  return 0;
    if ( OutName == 0 )                            return Cba_PrsErrorSet(p, "Cannot read output in assign-statement.", 0);
    if ( !Cba_PrsIsChar(p, '=') )                  return Cba_PrsErrorSet(p, "Expecting \"=\" in assign-statement.", 0);
    p->pCur++;
    if ( Cba_PrsUtilSkipSpaces(p) )                return 0;
    if ( Cba_PrsIsChar(p, '~') ) 
    { 
        fCompl = 1; 
        p->pCur++; 
    }
    Vec_IntPush( &p->vTemp, OutName );
    Vec_IntPush( &p->vTemp, RangeId );
    // read first name
    if ( !Cba_PrsReadSignal(p, &InName, &RangeId)) return 0;
    if ( InName == 0 )                             return Cba_PrsErrorSet(p, "Cannot read first input name in the assign-statement.", 0);
    Vec_IntPush( &p->vTemp, InName );
    Vec_IntPush( &p->vTemp, RangeId );
    // check unary operator
    if ( Cba_PrsIsChar(p, ';') )
    {
        Vec_IntPush( &p->vTypesCur, CBA_PRS_NODE );
        Vec_IntPush( &p->vFuncsCur, fCompl ? CBA_NODE_INV : CBA_NODE_BUF );
        Vec_IntPush( &p->vInstIdsCur, 0 );
        Vec_IntPush( &p->vFaninsCur, Cba_ManHandleArray(p->pDesign, &p->vTemp) ); 
        return 1;
    }
    if ( Cba_PrsIsChar(p, '&') ) 
        Oper = CBA_NODE_AND;
    else if ( Cba_PrsIsChar(p, '|') ) 
        Oper = CBA_NODE_OR;
    else if ( Cba_PrsIsChar(p, '^') ) 
        Oper = fCompl ? CBA_NODE_XNOR : CBA_NODE_XOR;
    else if ( Cba_PrsIsChar(p, '?') ) 
        Oper = CBA_NODE_MUX;
    else                                           return Cba_PrsErrorSet(p, "Unrecognized operator in the assign-statement.", 0);
    p->pCur++; 
    // read second name
    if ( !Cba_PrsReadSignal(p, &InName, &RangeId)) return 0;
    if ( InName == 0 )                             return Cba_PrsErrorSet(p, "Cannot read second input name in the assign-statement.", 0);
    Vec_IntPush( &p->vTemp, InName );
    Vec_IntPush( &p->vTemp, RangeId );
    // read third argument
    if ( Oper == CBA_NODE_MUX )
    {
        assert( fCompl == 0 ); 
        if ( !Cba_PrsIsChar(p, ':') )              return Cba_PrsErrorSet(p, "Expected colon in the MUX assignment.", 0);
        p->pCur++; 
        // read third name
        if ( !Cba_PrsReadSignal(p, &InName, &RangeId)) return 0;
        if ( InName == 0 )                         return Cba_PrsErrorSet(p, "Cannot read third input name in the assign-statement.", 0);
        Vec_IntPush( &p->vTemp, InName );
        Vec_IntPush( &p->vTemp, RangeId );
        if ( !Cba_PrsIsChar(p, ';') )              return Cba_PrsErrorSet(p, "Expected semicolon at the end of the assign-statement.", 0);
    }
    // write binary operator
    Vec_IntPush( &p->vTypesCur, CBA_PRS_NODE );
    Vec_IntPush( &p->vFuncsCur, Oper );
    Vec_IntPush( &p->vInstIdsCur, 0 );
    Vec_IntPush( &p->vFaninsCur, Cba_ManHandleArray(p->pDesign, &p->vTemp) ); 
    return 1;
}
static inline int Cba_PrsReadInstance( Cba_Prs_t * p, int Func )
{
    // have to assign Type, Func, InstId, vFanins
    int InstId, Status, Type;
    Vec_IntClear( &p->vTemp );
    if ( Cba_PrsUtilSkipSpaces(p) )               return 0;
    InstId = Cba_PrsReadName( p );
    if ( InstId && Cba_PrsUtilSkipSpaces(p) )     return 0;
    if ( !Cba_PrsIsChar(p, '(') )                 return Cba_PrsErrorSet(p, "Expecting \"(\" in module instantiation.", 0);
    p->pCur++;
    if ( Cba_PrsUtilSkipSpaces(p) )               return 0;
    if ( Cba_PrsIsChar(p, '.') ) // node
        Status = Cba_PrsReadSignalList2(p, &p->vTemp), Type = CBA_PRS_BOX;
    else 
        Status = Cba_PrsReadSignalList1(p, &p->vTemp), Type = CBA_PRS_NODE;
    if ( Status == 0 )                            return 0;
    // translate elementary gate
    if ( Type == CBA_PRS_NODE )
    {
        int iFuncNew = Cba_PrsIsKnownModule(p, Abc_NamStr(p->pDesign->pNames, Func));
        if ( iFuncNew == 0 )                      return Cba_PrsErrorSet(p, "Cannot find elementary gate.", 0);
        Func = iFuncNew;
    }
    // assign
    Vec_IntPush( &p->vTypesCur, Type );
    Vec_IntPush( &p->vFuncsCur, Func );
    Vec_IntPush( &p->vInstIdsCur, InstId );
    Vec_IntPush( &p->vFaninsCur, Cba_ManHandleArray(p->pDesign, &p->vTemp) ); 
    return 1;
}

// this procedure can return:
// 0 = reached end-of-file; 1 = successfully parsed; 2 = recognized as primitive; 3 = failed and skipped; 4 = error (failed and could not skip)
static inline int Cba_PrsReadModule( Cba_Prs_t * p )
{
    int iToken, Status;
    if ( p->iModuleName != 0 )            return Cba_PrsErrorSet(p, "Parsing previous module is unfinished.", 4);
    if ( Cba_PrsUtilSkipSpaces(p) )
    { 
        Cba_PrsErrorClear( p );       
        return 0; 
    }
    // read keyword
    iToken = Cba_PrsReadName( p );
    if ( iToken != CBA_VER_MODULE )       return Cba_PrsErrorSet(p, "Cannot read \"module\" keyword.", 4);
    if ( Cba_PrsUtilSkipSpaces(p) )       return 4;
    // read module name
    p->iModuleName = Cba_PrsReadName( p );
    if ( p->iModuleName == 0 )            return Cba_PrsErrorSet(p, "Cannot read module name.", 4);
    if ( Cba_PrsIsKnownModule(p, Abc_NamStr(p->pDesign->pNames, p->iModuleName)) )
    {
        if ( Cba_PrsUtilSkipUntilWord( p, "endmodule" ) ) return Cba_PrsErrorSet(p, "Cannot find \"endmodule\" keyword.", 4);
        //printf( "Warning! Skipped known module \"%s\".\n", Abc_NamStr(p->pDesign->pNames, p->iModuleName) );
        Vec_IntPush( &p->vKnown, p->iModuleName );
        p->iModuleName = 0;
        return 2;
    }
    // skip arguments
    if ( Cba_PrsUtilSkipSpaces(p) )       return 4;
    if ( !Cba_PrsIsChar(p, '(') )         return Cba_PrsErrorSet(p, "Cannot find \"(\" in the argument declaration.", 4);
    if ( !Cba_PrsUtilSkipUntil(p,')') )   return 4;
    assert( *p->pCur == ')' );
    p->pCur++;
    if ( Cba_PrsUtilSkipSpaces(p) )       return 4;
    // read declarations and instances
    while ( Cba_PrsIsChar(p, ';') )
    {
        p->pCur++;
        if ( Cba_PrsUtilSkipSpaces(p) )   return 4;
        iToken = Cba_PrsReadName( p );
        if ( iToken == CBA_VER_ENDMODULE )
        {
            Vec_IntPush( &p->vSucceeded, p->iModuleName );
            Cba_PrsAddCurrentModel( p, p->iModuleName );
            p->iModuleName = 0;
            return 1;
        }
        if ( iToken >= CBA_VER_INOUT && iToken <= CBA_VER_WIRE ) // declaration
            Status = Cba_PrsReadDeclaration( p, iToken );
        else if ( iToken == CBA_VER_REG || iToken == CBA_VER_DEFPARAM ) // unsupported keywords
            Status = Cba_PrsUtilSkipUntil( p, ';' );
        else // read instance
        {
            if ( iToken == CBA_VER_ASSIGN )
                Status = Cba_PrsReadAssign( p );
            else
                Status = Cba_PrsReadInstance( p, iToken );
            if ( Status == 0 )
            {
                if ( Cba_PrsUtilSkipUntilWord( p, "endmodule" ) ) return Cba_PrsErrorSet(p, "Cannot find \"endmodule\" keyword.", 4);
                //printf( "Warning! Failed to parse \"%s\". Adding module \"%s\" as blackbox.\n", 
                //    Abc_NamStr(p->pDesign->pNames, iToken), Abc_NamStr(p->pDesign->pNames, p->iModuleName) );
                Vec_IntPush( &p->vFailed, p->iModuleName );
                // cleanup
                Vec_IntClear( &p->vWiresCur );
                Vec_IntClear( &p->vFaninsCur );
                Vec_IntClear( &p->vTypesCur );
                Vec_IntClear( &p->vFuncsCur );
                Vec_IntClear( &p->vInstIdsCur );
                // add
                Cba_PrsAddCurrentModel( p, p->iModuleName );
                Cba_PrsErrorClear( p );
                p->iModuleName = 0;
                return 3;
            }
        }
        if ( !Status )                    return 4;
        if ( Cba_PrsUtilSkipSpaces(p) )   return 4;
    }
    return Cba_PrsErrorSet(p, "Cannot find \";\" in the module definition.", 4);
}
static inline int Cba_PrsReadDesign( Cba_Prs_t * p )
{
    while ( 1 )
    {
        int RetValue = Cba_PrsReadModule( p );
        if ( RetValue == 0 ) // end of file
            break;
        if ( RetValue == 1 ) // successfully parsed
            continue;
        if ( RetValue == 2 ) // recognized as primitive
            continue;
        if ( RetValue == 3 ) // failed and skipped
            continue;
        if ( RetValue == 4 ) // error
            return 0;
        assert( 0 );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_PrsPrintModules( Cba_Prs_t * p )
{
    char * pName; int i; 
    printf( "Succeeded parsing %d models:\n", Vec_IntSize(&p->vSucceeded) );
    Cba_PrsForEachModelVec( &p->vSucceeded, p, pName, i )
        printf( " %s", pName );
    printf( "\n" );
    printf( "Skipped %d known models:\n", Vec_IntSize(&p->vKnown) );
    Cba_PrsForEachModelVec( &p->vKnown, p, pName, i )
        printf( " %s", pName );
    printf( "\n" );
    printf( "Skipped %d failed models:\n", Vec_IntSize(&p->vFailed) );
    Cba_PrsForEachModelVec( &p->vFailed, p, pName, i )
        printf( " %s", pName );
    printf( "\n" );
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
    Cba_PrsPrintModules( p );
    if ( Cba_PrsErrorPrint(p) )
        ABC_SWAP( Cba_Man_t *, pDesign, p->pDesign );
    Cba_PrsFree( p );
    return pDesign;
}

void Cba_PrsReadVerilogTest( char * pFileName )
{
    abctime clk = Abc_Clock();
    extern void Cba_PrsWriteVerilog( char * pFileName, Cba_Man_t * pDes );
//    Cba_Man_t * p = Cba_PrsReadVerilog( "c/hie/dump/1/netlist_1.v" );
//    Cba_Man_t * p = Cba_PrsReadVerilog( "aga/me/me_wide.v" );
    Cba_Man_t * p = Cba_PrsReadVerilog( "aga/ray/ray_wide.v" );
    if ( !p ) return;
    printf( "Finished reading %d networks. ", Cba_ManNtkNum(p) );
    printf( "NameIDs = %d. ", Abc_NamObjNumMax(p->pNames) );
    printf( "Memory = %.2f MB. ", 1.0*Cba_ManMemory(p)/(1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
//    Abc_NamPrint( p->pDesign->pNames );
//    Cba_PrsWriteVerilog( "c/hie/dump/1/netlist_1_out.v", p );
//    Cba_PrsWriteVerilog( "aga/me/me_wide_out.v", p );
    Cba_PrsWriteVerilog( "aga/ray/ray_wide_out.v", p );
    Cba_ManFree( p );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

