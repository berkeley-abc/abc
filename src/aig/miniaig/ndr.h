/**CFile****************************************************************

  FileName    [ndr.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Format for word-level design representation.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: ndr.h,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__ndr__ndr_h
#define ABC__base__ndr__ndr_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

//ABC_NAMESPACE_HEADER_START 

#ifdef _WIN32
#define inline __inline
#endif

/*
    For the lack of a better name, this format is called New Data Representation (NDR).

    NDR is based on the following principles:
    - complex data is composed of individual records
    - a record has one of several known types (module, name, range, fanins, etc)
    - a record can be atomic, for example, a name or an operator type
    - a record can be composed of other records (for example, a module is composed of objects, etc)
    - the stored data should be easy to write into and read from a file, or pass around as a memory buffer
    - the format should be simple, easy to use, low-memory, and extensible
    - new record types can be added by the user as needed

    The implementation is based on the following ideas:
    - a record is composed of two parts (the header followed by the body)
    - the header contains two items (the record type and the body size, measured in terms of 4-byte integers)
    - the body contains as many entries as stated in the record size
    - if a record is composed of other records, its body contains these records

    As an example, consider a name. It can be a module name, an object name, or a net name.
    A record storing one name has a header {NDR_NAME, 1} containing record type (NDR_NAME) and size (1),
    The body of the record is composed of one unsigned integer representing the name (say, 357).  
    So the complete record looks as follows:  { <header>, <body> } = { {NDR_NAME, 1}, {357} }.

    As another example, consider a two-input AND-gate.  In this case, the recent is composed 
    of a header {NDR_OBJECT, 4}  containing record type (NDR_OBJECT) and the body size (4), followed 
    by an array of records creating the AND-gate:  (a) name, (b) operation type, (c) fanins.   
    The complete record  looks as follows: {  {NDR_OBJECT, 5}, {{{NDR_NAME, 1}, 357}, {{NDR_OPERTYPE, 1}, WLC_OBJ_LOGIC_AND}, 
    {{NDR_INPUT, 2}, {<id_fanin1>, <id_fanin2>}}} }.   Please note that only body entries are counted towards size. 
    In the case of one name, there is only one body entry.  In the case of the AND-gate, there are 4 body entries 
    (name ID, gate type, first fanin, second fanin).

    Headers and bodies of all objects are stored differently.  Headers are stored in an array of unsigned chars, 
    while bodies are stored in the array of 4-byte unsigned integers.  This is important for memory efficiency. 
    However, the user does not see these details.

    To estimate memory usage, we can assume that each header takes 1 byte and each body entry contains 4 bytes.   
    A name takes 5 bytes, and an AND-gate takes 1 * NumHeaders + 4 * NumBodyEntries = 1 * 4 + 4 * 4 = 20 bytes.  
    Not bad.  The same as memory usage in a well-designed AIG package with structural hashing. 

    Comments:
    - it is assumed that all port names, net names, and instance names are hashed into 1-based integer numbers called name IDs
    - nets are not explicitly represented but their name ID are used to establish connectivity between the objects
    - primary input and primary output objects have to be explicitly created (as shown in the example below)
    - object inputs are name IDs of the driving nets; object outputs are name IDs of the driven nets
    - objects can be added to a module in any order
    - if the ordering of inputs/outputs/flops of a module is not provided as a separate record,
      their ordering is determined by the order of their appearance of their records in the body of the module
    - if range limits and signedness are all 0, it is assumed that it is a Boolean object
    - if left limit and right limit of a range are equal, it is assumed that the range contains one bit
    - instances of known operators can have types defined by Wlc_ObjType_t below
    - instances of user modules have type equal to the name ID of the module plus 1000
    - initial states of the flops are given as char-strings containing 0, 1, and 'x' 
      (for example, "4'b10XX" is an init state of a 4-bit flop with bit-level init states const1, const0, unknown, unknown)
    - word-level constants are represented as char-strings given in the same way as they would appear in a Verilog file 
      (for example, the 16-bit constant 10 is represented as a string "4'b1010". This string contains  8 bytes, 
      including the char '\0' to denote the end of the string. It will take 2 unsigned ints, therefore 
      its record will look as follows { {NDR_FUNCTION, 2}, {"4'b1010"} }, but the user does not see these details.  
      The user only gives  "4'b1010" as an argument (char * pFunction) to the above procedure Ndr_ModuleAddObject(). 
*/

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

// record types
typedef enum {
    NDR_NONE = 0,          // 0:  unused
    NDR_DESIGN,            // 1:  design (or library of modules)
    NDR_MODULE,            // 2:  one module
    NDR_OBJECT,            // 3:  object
    NDR_INPUT,             // 4:  input
    NDR_OUTPUT,            // 5:  output
    NDR_OPERTYPE,          // 6:  operator type (buffer, shifter, adder, etc)
    NDR_NAME,              // 7:  name
    NDR_RANGE,             // 8:  bit range
    NDR_FUNCTION,          // 9:  specified for some operators (PLAs, etc)
    NDR_UNKNOWN            // 10: unknown
} Ndr_RecordType_t; 

// operator types
typedef enum { 
    WLC_OBJ_NONE = 0,      // 00: unknown
    WLC_OBJ_PI,            // 01: primary input 
    WLC_OBJ_PO,            // 02: primary output
    WLC_OBJ_FO,            // 03: flop output (unused)
    WLC_OBJ_FI,            // 04: flop input (unused)
    WLC_OBJ_FF,            // 05: flop
    WLC_OBJ_CONST,         // 06: constant
    WLC_OBJ_BUF,           // 07: buffer
    WLC_OBJ_MUX,           // 08: multiplexer
    WLC_OBJ_SHIFT_R,       // 09: shift right
    WLC_OBJ_SHIFT_RA,      // 10: shift right (arithmetic)
    WLC_OBJ_SHIFT_L,       // 11: shift left
    WLC_OBJ_SHIFT_LA,      // 12: shift left (arithmetic)
    WLC_OBJ_ROTATE_R,      // 13: rotate right
    WLC_OBJ_ROTATE_L,      // 14: rotate left
    WLC_OBJ_BIT_NOT,       // 15: bitwise NOT
    WLC_OBJ_BIT_AND,       // 16: bitwise AND
    WLC_OBJ_BIT_OR,        // 17: bitwise OR
    WLC_OBJ_BIT_XOR,       // 18: bitwise XOR
    WLC_OBJ_BIT_NAND,      // 19: bitwise AND
    WLC_OBJ_BIT_NOR,       // 20: bitwise OR
    WLC_OBJ_BIT_NXOR,      // 21: bitwise NXOR
    WLC_OBJ_BIT_SELECT,    // 22: bit selection
    WLC_OBJ_BIT_CONCAT,    // 23: bit concatenation
    WLC_OBJ_BIT_ZEROPAD,   // 24: zero padding
    WLC_OBJ_BIT_SIGNEXT,   // 25: sign extension
    WLC_OBJ_LOGIC_NOT,     // 26: logic NOT
    WLC_OBJ_LOGIC_IMPL,    // 27: logic implication
    WLC_OBJ_LOGIC_AND,     // 28: logic AND
    WLC_OBJ_LOGIC_OR,      // 29: logic OR
    WLC_OBJ_LOGIC_XOR,     // 30: logic XOR
    WLC_OBJ_COMP_EQU,      // 31: compare equal
    WLC_OBJ_COMP_NOTEQU,   // 32: compare not equal
    WLC_OBJ_COMP_LESS,     // 33: compare less
    WLC_OBJ_COMP_MORE,     // 34: compare more
    WLC_OBJ_COMP_LESSEQU,  // 35: compare less or equal
    WLC_OBJ_COMP_MOREEQU,  // 36: compare more or equal
    WLC_OBJ_REDUCT_AND,    // 37: reduction AND
    WLC_OBJ_REDUCT_OR,     // 38: reduction OR
    WLC_OBJ_REDUCT_XOR,    // 39: reduction XOR
    WLC_OBJ_REDUCT_NAND,   // 40: reduction NAND
    WLC_OBJ_REDUCT_NOR,    // 41: reduction NOR
    WLC_OBJ_REDUCT_NXOR,   // 42: reduction NXOR
    WLC_OBJ_ARI_ADD,       // 43: arithmetic addition
    WLC_OBJ_ARI_SUB,       // 44: arithmetic subtraction
    WLC_OBJ_ARI_MULTI,     // 45: arithmetic multiplier
    WLC_OBJ_ARI_DIVIDE,    // 46: arithmetic division
    WLC_OBJ_ARI_REM,       // 47: arithmetic remainder
    WLC_OBJ_ARI_MODULUS,   // 48: arithmetic modulus
    WLC_OBJ_ARI_POWER,     // 49: arithmetic power
    WLC_OBJ_ARI_MINUS,     // 50: arithmetic minus
    WLC_OBJ_ARI_SQRT,      // 51: integer square root
    WLC_OBJ_ARI_SQUARE,    // 52: integer square
    WLC_OBJ_TABLE,         // 53: bit table
    WLC_OBJ_NUMBER         // 54: unused
} Wlc_ObjType_t;

// printing operator types
static inline char * Ndr_OperName( int Type )
{
    if ( Type == WLC_OBJ_NONE         )   return NULL;
    if ( Type == WLC_OBJ_PI           )   return "pi";        // 01: primary input 
    if ( Type == WLC_OBJ_PO           )   return "po";        // 02: primary output (unused)
    if ( Type == WLC_OBJ_FO           )   return "ff";        // 03: flop output
    if ( Type == WLC_OBJ_FI           )   return "bi";        // 04: flop input (unused)
    if ( Type == WLC_OBJ_FF           )   return "ff";        // 05: flop (unused)
    if ( Type == WLC_OBJ_CONST        )   return "const";     // 06: constant
    if ( Type == WLC_OBJ_BUF          )   return "buf";       // 07: buffer
    if ( Type == WLC_OBJ_MUX          )   return "mux";       // 08: multiplexer
    if ( Type == WLC_OBJ_SHIFT_R      )   return ">>";        // 09: shift right
    if ( Type == WLC_OBJ_SHIFT_RA     )   return ">>>";       // 10: shift right (arithmetic)
    if ( Type == WLC_OBJ_SHIFT_L      )   return "<<";        // 11: shift left
    if ( Type == WLC_OBJ_SHIFT_LA     )   return "<<<";       // 12: shift left (arithmetic)
    if ( Type == WLC_OBJ_ROTATE_R     )   return "rotR";      // 13: rotate right
    if ( Type == WLC_OBJ_ROTATE_L     )   return "rotL";      // 14: rotate left
    if ( Type == WLC_OBJ_BIT_NOT      )   return "~";         // 15: bitwise NOT
    if ( Type == WLC_OBJ_BIT_AND      )   return "&";         // 16: bitwise AND
    if ( Type == WLC_OBJ_BIT_OR       )   return "|";         // 17: bitwise OR
    if ( Type == WLC_OBJ_BIT_XOR      )   return "^";         // 18: bitwise XOR
    if ( Type == WLC_OBJ_BIT_NAND     )   return "~&";        // 19: bitwise NAND
    if ( Type == WLC_OBJ_BIT_NOR      )   return "~|";        // 20: bitwise NOR
    if ( Type == WLC_OBJ_BIT_NXOR     )   return "~^";        // 21: bitwise NXOR
    if ( Type == WLC_OBJ_BIT_SELECT   )   return "[:]";       // 22: bit selection
    if ( Type == WLC_OBJ_BIT_CONCAT   )   return "{}";        // 23: bit concatenation
    if ( Type == WLC_OBJ_BIT_ZEROPAD  )   return "zPad";      // 24: zero padding
    if ( Type == WLC_OBJ_BIT_SIGNEXT  )   return "sExt";      // 25: sign extension
    if ( Type == WLC_OBJ_LOGIC_NOT    )   return "!";         // 26: logic NOT
    if ( Type == WLC_OBJ_LOGIC_IMPL   )   return "=>";        // 27: logic implication
    if ( Type == WLC_OBJ_LOGIC_AND    )   return "&&";        // 28: logic AND
    if ( Type == WLC_OBJ_LOGIC_OR     )   return "||";        // 29: logic OR
    if ( Type == WLC_OBJ_LOGIC_XOR    )   return "^^";        // 30: logic XOR
    if ( Type == WLC_OBJ_COMP_EQU     )   return "==";        // 31: compare equal
    if ( Type == WLC_OBJ_COMP_NOTEQU  )   return "!=";        // 32: compare not equal
    if ( Type == WLC_OBJ_COMP_LESS    )   return "<";         // 33: compare less
    if ( Type == WLC_OBJ_COMP_MORE    )   return ">";         // 34: compare more
    if ( Type == WLC_OBJ_COMP_LESSEQU )   return "<=";        // 35: compare less or equal
    if ( Type == WLC_OBJ_COMP_MOREEQU )   return ">=";        // 36: compare more or equal
    if ( Type == WLC_OBJ_REDUCT_AND   )   return "&";         // 37: reduction AND
    if ( Type == WLC_OBJ_REDUCT_OR    )   return "|";         // 38: reduction OR
    if ( Type == WLC_OBJ_REDUCT_XOR   )   return "^";         // 39: reduction XOR
    if ( Type == WLC_OBJ_REDUCT_NAND  )   return "~&";        // 40: reduction NAND
    if ( Type == WLC_OBJ_REDUCT_NOR   )   return "~|";        // 41: reduction NOR
    if ( Type == WLC_OBJ_REDUCT_NXOR  )   return "~^";        // 42: reduction NXOR
    if ( Type == WLC_OBJ_ARI_ADD      )   return "+";         // 43: arithmetic addition
    if ( Type == WLC_OBJ_ARI_SUB      )   return "-";         // 44: arithmetic subtraction
    if ( Type == WLC_OBJ_ARI_MULTI    )   return "*";         // 45: arithmetic multiplier
    if ( Type == WLC_OBJ_ARI_DIVIDE   )   return "/";         // 46: arithmetic division
    if ( Type == WLC_OBJ_ARI_REM      )   return "%";         // 47: arithmetic reminder
    if ( Type == WLC_OBJ_ARI_MODULUS  )   return "mod";       // 48: arithmetic modulus
    if ( Type == WLC_OBJ_ARI_POWER    )   return "**";        // 49: arithmetic power
    if ( Type == WLC_OBJ_ARI_MINUS    )   return "-";         // 50: arithmetic minus
    if ( Type == WLC_OBJ_ARI_SQRT     )   return "sqrt";      // 51: integer square root
    if ( Type == WLC_OBJ_ARI_SQUARE   )   return "squar";     // 52: integer square
    if ( Type == WLC_OBJ_TABLE        )   return "table";     // 53: bit table
    if ( Type == WLC_OBJ_NUMBER       )   return NULL;        // 54: unused
    return NULL;
}


////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// this is an internal procedure, which is not seen by the user
typedef struct Ndr_Data_t_  Ndr_Data_t;
struct Ndr_Data_t_ 
{
    int                     nSize;
    int                     nCap;
    unsigned char *         pHead;
    unsigned int *          pBody;
};

static inline int           Ndr_DataType( Ndr_Data_t * p, int i )                { assert( p->pHead[i] ); return (int)p->pHead[i];                }
static inline int           Ndr_DataSize( Ndr_Data_t * p, int i )                { return Ndr_DataType(p, i) > NDR_OBJECT ? 1 : p->pBody[i];      }
static inline int           Ndr_DataEntry( Ndr_Data_t * p, int i )               { return (int)p->pBody[i];                                       }
static inline int *         Ndr_DataEntryP( Ndr_Data_t * p, int i )              { return (int *)p->pBody + i;                                    }
static inline int           Ndr_DataEnd( Ndr_Data_t * p, int i )                 { return i + p->pBody[i];                                        }
static inline void          Ndr_DataAddTo( Ndr_Data_t * p, int i, int Add )      { assert(Ndr_DataType(p, i) <= NDR_OBJECT); p->pBody[i] += Add;  } 
static inline void          Ndr_DataPush( Ndr_Data_t * p, int Type, int Entry )  { p->pHead[p->nSize] = Type; p->pBody[p->nSize++] = Entry;       }

////////////////////////////////////////////////////////////////////////
///                          ITERATORS                               ///
////////////////////////////////////////////////////////////////////////

// iterates over modules in the design
#define Ndr_DesForEachMod( p, Mod )                                   \
    for ( Mod = 1; Mod < Ndr_DataEntry(p, 0); Mod += Ndr_DataSize(p, Mod) ) if (Ndr_DataType(p, Mod) != NDR_MODULE) {} else

// iterates over objects in a module
#define Ndr_ModForEachObj( p, Mod, Obj )                              \
    for ( Obj = Mod + 1; Obj < Ndr_DataEnd(p, Mod); Obj += Ndr_DataSize(p, Obj) ) if (Ndr_DataType(p, Obj) != NDR_OBJECT) {} else

// iterates over records in an object
#define Ndr_ObjForEachEntry( p, Obj, Ent )                            \
    for ( Ent = Obj + 1; Ent < Ndr_DataEnd(p, Obj); Ent += Ndr_DataSize(p, Ent) )

// iterates over primary inputs of a module
#define Ndr_ModForEachPi( p, Mod, Obj )                               \
    Ndr_ModForEachObj( p, 0, Obj ) if ( !Ndr_ObjIsType(p, Obj, WLC_OBJ_PI) ) {} else

// iteraots over primary outputs of a module
#define Ndr_ModForEachPo( p, Mod, Obj )                               \
    Ndr_ModForEachObj( p, 0, Obj ) if ( !Ndr_ObjIsType(p, Obj, WLC_OBJ_PO) ) {} else

// iterates over internal nodes of a module
#define Ndr_ModForEachNode( p, Mod, Obj )                             \
    Ndr_ModForEachObj( p, 0, Obj ) if ( Ndr_ObjIsType(p, Obj, WLC_OBJ_PI) || Ndr_ObjIsType(p, Obj, WLC_OBJ_PO) ) {} else


////////////////////////////////////////////////////////////////////////
///                    INTERNAL PROCEDURES                           ///
////////////////////////////////////////////////////////////////////////


static inline void Ndr_DataResize( Ndr_Data_t * p, int Add )
{
    if ( p->nSize + Add <= p->nCap )
        return;
    p->nCap *= 2;
    p->pHead = (unsigned char*)realloc( p->pHead,   p->nCap );
    p->pBody = (unsigned int *)realloc( p->pBody, 4*p->nCap );
}
static inline void Ndr_DataPushRange( Ndr_Data_t * p, int RangeLeft, int RangeRight, int fSignedness )
{ 
    if ( fSignedness )
    {
        Ndr_DataPush( p, NDR_RANGE, RangeLeft );
        Ndr_DataPush( p, NDR_RANGE, RangeRight );
        Ndr_DataPush( p, NDR_RANGE, fSignedness );
        return;
    }
    if ( !RangeLeft && !RangeRight )
        return;
    if ( RangeLeft == RangeRight )
        Ndr_DataPush( p, NDR_RANGE, RangeLeft );
    else
    {
        Ndr_DataPush( p, NDR_RANGE, RangeLeft );
        Ndr_DataPush( p, NDR_RANGE, RangeRight );
    }
}
static inline void Ndr_DataPushArray( Ndr_Data_t * p, int Type, int nArray, int * pArray )
{ 
    if ( !nArray )
        return;
    assert( nArray > 0 );
    Ndr_DataResize( p, nArray );
    memset( p->pHead + p->nSize, Type, nArray );
    memcpy( p->pBody + p->nSize, pArray, 4*nArray );
    p->nSize += nArray;
}
static inline void Ndr_DataPushString( Ndr_Data_t * p, int Type, char * pFunc )
{ 
    if ( !pFunc )
        return;
    Ndr_DataPushArray( p, Type, (strlen(pFunc) + 4) / 4, (int *)pFunc );
}


////////////////////////////////////////////////////////////////////////
///                     VERILOG WRITING                              ///
////////////////////////////////////////////////////////////////////////

static inline int Ndr_ObjReadEntry( Ndr_Data_t * p, int Obj, int Type )
{
    int Ent;
    Ndr_ObjForEachEntry( p, Obj, Ent )
        if ( Ndr_DataType(p, Ent) == Type )
            return Ndr_DataEntry(p, Ent);
    return -1;
}
static inline int Ndr_ObjReadArray( Ndr_Data_t * p, int Obj, int Type, int ** ppStart )
{
    int Ent, Counter = 0; *ppStart = NULL;
    Ndr_ObjForEachEntry( p, Obj, Ent )
        if ( Ndr_DataType(p, Ent) == Type )
        {
            Counter++;
            if ( *ppStart == NULL )
                *ppStart = (int *)p->pBody + Ent;
        }
        else if ( *ppStart )
            return Counter;
    return Counter;
} 
static inline int Ndr_ObjIsType( Ndr_Data_t * p, int Obj, int Type )
{
    int Ent;
    Ndr_ObjForEachEntry( p, Obj, Ent )
        if ( Ndr_DataType(p, Ent) == NDR_OPERTYPE )
            return (int)(Ndr_DataEntry(p, Ent) == Type);
    return -1;
}
static inline int Ndr_ObjReadBody( Ndr_Data_t * p, int Obj, int Type )
{
    int Ent;
    Ndr_ObjForEachEntry( p, Obj, Ent )
        if ( Ndr_DataType(p, Ent) == Type )
            return Ndr_DataEntry(p, Ent);
    return -1;
}
static inline int * Ndr_ObjReadBodyP( Ndr_Data_t * p, int Obj, int Type )
{
    int Ent;
    Ndr_ObjForEachEntry( p, Obj, Ent )
        if ( Ndr_DataType(p, Ent) == Type )
            return Ndr_DataEntryP(p, Ent);
    return NULL;
}
static inline void Ndr_ObjWriteRange( Ndr_Data_t * p, int Obj, FILE * pFile )
{
    int * pArray, nArray = Ndr_ObjReadArray( p, Obj, NDR_RANGE, &pArray );
    if ( nArray == 0 )
        return;
    if ( nArray == 3 )
        fprintf( pFile, "signed " ); 
    if ( nArray == 1 )
        fprintf( pFile, "[%d] ", pArray[0] );
    else
        fprintf( pFile, "[%d:%d] ", pArray[0], pArray[1] );
}
static inline char * Ndr_ObjReadOutName( Ndr_Data_t * p, int Obj, char ** pNames )
{
    return pNames[Ndr_ObjReadBody(p, Obj, NDR_OUTPUT)];
}
static inline char * Ndr_ObjReadInName( Ndr_Data_t * p, int Obj, char ** pNames )
{
    return pNames[Ndr_ObjReadBody(p, Obj, NDR_INPUT)];
}

// to write signal names, this procedure takes a mapping of name IDs into actual char-strings (pNames)
static inline void Ndr_ModuleWriteVerilog( char * pFileName, void * pModule, char ** pNames )
{
    Ndr_Data_t * p = (Ndr_Data_t *)pModule; 
    int Mod = 0, Obj, nArray, * pArray, fFirst = 1;

    FILE * pFile = pFileName ? fopen( pFileName, "wb" ) : stdout;
    if ( pFile == NULL ) { printf( "Cannot open file \"%s\" for writing.\n", pFileName ); return; }

    fprintf( pFile, "\nmodule %s (\n  ", pNames[Ndr_ObjReadEntry(p, 0, NDR_NAME)] );

    Ndr_ModForEachPi( p, Mod, Obj )
        fprintf( pFile, "%s, ", Ndr_ObjReadOutName(p, Obj, pNames) );

    fprintf( pFile, "\n  " );

    Ndr_ModForEachPo( p, Mod, Obj )
        fprintf( pFile, "%s%s", fFirst ? "":", ", Ndr_ObjReadInName(p, Obj, pNames) ), fFirst = 0;

    fprintf( pFile, "\n);\n\n" );

    Ndr_ModForEachPi( p, Mod, Obj )
    {
        fprintf( pFile, "  input " );
        Ndr_ObjWriteRange( p, Obj, pFile );
        fprintf( pFile, "%s;\n", Ndr_ObjReadOutName(p, Obj, pNames) );
    }

    Ndr_ModForEachPo( p, Mod, Obj )
    {
        fprintf( pFile, "  output " );
        Ndr_ObjWriteRange( p, Obj, pFile );
        fprintf( pFile, "%s;\n", Ndr_ObjReadInName(p, Obj, pNames) );
    }

    Ndr_ModForEachNode( p, Mod, Obj )
    {
        fprintf( pFile, "  wire " );
        Ndr_ObjWriteRange( p, Obj, pFile );
        fprintf( pFile, "%s;\n", Ndr_ObjReadOutName(p, Obj, pNames) );
    }

    fprintf( pFile, "\n" );

    Ndr_ModForEachNode( p, Mod, Obj )
    {
        fprintf( pFile, "  assign %s = ", Ndr_ObjReadOutName(p, Obj, pNames) );
        nArray = Ndr_ObjReadArray( p, Obj, NDR_INPUT, &pArray );
        if ( nArray == 0 )
            fprintf( pFile, "%s;\n", (char *)Ndr_ObjReadBodyP(p, Obj, NDR_FUNCTION) );
        else if ( nArray == 1 && Ndr_ObjReadBody(p, Obj, NDR_OPERTYPE) == WLC_OBJ_BUF )
            fprintf( pFile, "%s;\n", pNames[pArray[0]] );
        else if ( nArray == 1 )
            fprintf( pFile, "%s %s;\n", Ndr_OperName(Ndr_ObjReadBody(p, Obj, NDR_OPERTYPE)), pNames[pArray[0]] );
        else if ( nArray == 2 )
            fprintf( pFile, "%s %s %s;\n", pNames[pArray[0]], Ndr_OperName(Ndr_ObjReadBody(p, Obj, NDR_OPERTYPE)), pNames[pArray[1]] );
        else if ( Ndr_ObjReadBody(p, Obj, NDR_OPERTYPE) == WLC_OBJ_MUX )
            fprintf( pFile, "%s ? %s : %s;\n", pNames[pArray[0]], pNames[pArray[1]], pNames[pArray[2]] );
        else
            fprintf( pFile, "<cannot write operation %s>;\n", Ndr_OperName(Ndr_ObjReadBody(p, Obj, NDR_OPERTYPE)) );
    }

    fprintf( pFile, "\nendmodule\n\n" );
    fclose( pFile );
}


////////////////////////////////////////////////////////////////////////
///                     EXTERNAL PROCEDURES                          ///
////////////////////////////////////////////////////////////////////////

// creating a new module (returns pointer to the memory buffer storing the module info)
static inline void * Ndr_ModuleCreate( int Name )
{
    Ndr_Data_t * p = malloc( sizeof(Ndr_Data_t) );
    p->nSize = 0;
    p->nCap  = 16;
    p->pHead = malloc( p->nCap );
    p->pBody = malloc( p->nCap * 4 );
    Ndr_DataPush( p, NDR_MODULE, 0 );
    Ndr_DataPush( p, NDR_NAME, Name );
    Ndr_DataAddTo( p, 0, p->nSize );
    assert( p->nSize == 2 );
    assert( Name );
    return p;
}

// adding a new object (input/output/flop/intenal node) to an already module module
static inline void Ndr_ModuleAddObject( void * pModule, int Type, int InstName, 
                                        int RangeLeft, int RangeRight, int fSignedness, 
                                        int nInputs, int * pInputs, 
                                        int nOutputs, int * pOutputs, 
                                        char * pFunction )
{
    Ndr_Data_t * p = (Ndr_Data_t *)pModule;
    int Obj = p->nSize;  assert( Type != 0 );
    Ndr_DataResize( p, 6 );
    Ndr_DataPush( p, NDR_OBJECT, 0 );
    Ndr_DataPush( p, NDR_OPERTYPE, Type );
    Ndr_DataPushRange( p, RangeLeft, RangeRight, fSignedness );
    if ( InstName )
        Ndr_DataPush( p, NDR_NAME, InstName );
    Ndr_DataPushArray( p, NDR_INPUT, nInputs, pInputs );
    Ndr_DataPushArray( p, NDR_OUTPUT, nOutputs, pOutputs );
    Ndr_DataPushString( p, NDR_FUNCTION, pFunction );
    Ndr_DataAddTo( p, Obj, p->nSize - Obj );
    Ndr_DataAddTo( p, 0, p->nSize - Obj );
    assert( (int)p->pBody[0] == p->nSize );
}

// deallocate the memory buffer
static inline void Ndr_ModuleDelete( void * pModule )
{
    Ndr_Data_t * p = (Ndr_Data_t *)pModule;
    if ( !p ) return;
    free( p->pHead );
    free( p->pBody );
    free( p );
}


////////////////////////////////////////////////////////////////////////
///                  FILE READING AND WRITING                        ///
////////////////////////////////////////////////////////////////////////

// file reading/writing
static inline void * Ndr_ModuleRead( char * pFileName )
{
    Ndr_Data_t * p; int nFileSize, RetValue;
    FILE * pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL ) { printf( "Cannot open file \"%s\" for reading.\n", pFileName ); return NULL; }
    // check file size
    fseek( pFile, 0, SEEK_END );
    nFileSize = ftell( pFile ); 
    assert( nFileSize % 5 == 0 );
    rewind( pFile );
    // create structure
    p = malloc( sizeof(Ndr_Data_t) );
    p->nSize = p->nCap = nFileSize / 5;
    p->pHead = malloc( p->nCap );
    p->pBody = malloc( p->nCap * 4 );
    RetValue = fread( p->pBody, 4, p->nCap, pFile );
    RetValue = fread( p->pHead, 1, p->nCap, pFile );
    assert( p->nSize == (int)p->pBody[0] );
    fclose( pFile );
    return p;
}
static inline void Ndr_ModuleWrite( char * pFileName, void * pModule )
{
    Ndr_Data_t * p = (Ndr_Data_t *)pModule; int RetValue;
    FILE * pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL ) { printf( "Cannot open file \"%s\" for writing.\n", pFileName ); return; }
    RetValue = fwrite( p->pBody, 4, p->pBody[0], pFile );
    RetValue = fwrite( p->pHead, 1, p->pBody[0], pFile );
    fclose( pFile );
}


////////////////////////////////////////////////////////////////////////
///                     TESTING PROCEDURE                            ///
////////////////////////////////////////////////////////////////////////

// This testing procedure creates and writes into a Verilog file the following module

// module add10 ( input [3:0] a, output [3:0] s );
//   wire [3:0] const10 = 4'b1010;
//   assign s = a + const10;
// endmodule

static inline void Ndr_ModuleTest()
{
    // name IDs
    int NameIdA = 2;
    int NameIdS = 3;
    int NameIdC = 4;
    // array of fanins of node s
    int Fanins[2] = { NameIdA, NameIdC };
    // map name IDs into char strings
    char * ppNames[5] = { NULL, "add10", "a", "s", "const10" };

    // create a new module
    void * pModule = Ndr_ModuleCreate( 1 );

    // add objects to the modele
    Ndr_ModuleAddObject( pModule, WLC_OBJ_PI,       0,   3, 0, 0,   0, NULL,      1, &NameIdA,   NULL      ); // no fanins
    Ndr_ModuleAddObject( pModule, WLC_OBJ_CONST,    0,   3, 0, 0,   0, NULL,      1, &NameIdC,   "4'b1010" ); // no fanins
    Ndr_ModuleAddObject( pModule, WLC_OBJ_ARI_ADD,  0,   3, 0, 0,   2, Fanins,    1, &NameIdS,   NULL      ); // fanins are a and const10 
    Ndr_ModuleAddObject( pModule, WLC_OBJ_PO,       0,   3, 0, 0,   1, &NameIdS,  0, NULL,       NULL      ); // fanin is a

    // write Verilog for verification
    Ndr_ModuleWriteVerilog( NULL, pModule, ppNames );
    Ndr_ModuleDelete( pModule );
}


//ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

