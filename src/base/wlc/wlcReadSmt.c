/**CFile****************************************************************

  FileName    [wlcParse.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcParse.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"
#include "misc/vec/vecWec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// parser
typedef struct Smt_Prs_t_ Smt_Prs_t;
struct Smt_Prs_t_
{
    // input data
    char *       pName;       // file name
    char *       pBuffer;     // file contents
    char *       pLimit;      // end of file
    char *       pCur;        // current position
    Abc_Nam_t *  pStrs;       // string manager
    // network structure
    Vec_Int_t    vStack;      // current node on each level
    //Vec_Wec_t    vDepth;      // objects on each level
    Vec_Wec_t    vObjs;       // objects
    // error handling
    char ErrorStr[1000];     
};

// parser name types
typedef enum { 
    SMT_PRS_NONE = 0, 
    SMT_PRS_SET_OPTION,    
    SMT_PRS_SET_LOGIC,    
    SMT_PRS_SET_INFO,    
    SMT_PRS_DEFINE_FUN,
    SMT_PRS_DECLARE_FUN,   
    SMT_PRS_ASSERT,   
    SMT_PRS_LET,   
    SMT_PRS_CHECK_SAT,   
    SMT_PRS_GET_VALUE,   
    SMT_PRS_EXIT,
    SMT_PRS_END
} Smt_LineType_t; 

typedef struct Smt_Pair_t_ Smt_Pair_t;
struct Smt_Pair_t_
{
    Smt_LineType_t Type;
    char *         pName;
};
static Smt_Pair_t s_Types[SMT_PRS_END] =
{
    { SMT_PRS_NONE,         NULL         },
    { SMT_PRS_SET_OPTION,  "set-option"  },
    { SMT_PRS_SET_LOGIC,   "set-logic"   },
    { SMT_PRS_SET_INFO,    "set-info"    },
    { SMT_PRS_DEFINE_FUN,  "define-fun"  },
    { SMT_PRS_DECLARE_FUN, "declare-fun" },
    { SMT_PRS_ASSERT,      "assert"      },
    { SMT_PRS_LET,         "let"         },
    { SMT_PRS_CHECK_SAT,   "check-sat"   },
    { SMT_PRS_GET_VALUE,   "get-value"   },
    { SMT_PRS_EXIT,        "exit"        }
};
static inline char * Smt_GetTypeName( Smt_LineType_t Type )
{
    int i;
    for ( i = 1; i < SMT_PRS_END; i++ )
        if ( s_Types[i].Type == Type )
            return s_Types[i].pName;
    return NULL;
}
static inline void Smt_AddTypes( Abc_Nam_t * p )
{
    int Type;
    for ( Type = 1; Type < SMT_PRS_END; Type++ )
        Abc_NamStrFindOrAdd( p, Smt_GetTypeName((Smt_LineType_t)Type), NULL );
    assert( Abc_NamObjNumMax(p) == SMT_PRS_END );
}

static inline int         Smt_EntryIsName( int Fan )                          { return Abc_LitIsCompl(Fan);                                                         }
static inline int         Smt_EntryIsType( int Fan, Smt_LineType_t Type )     { assert(Smt_EntryIsName(Fan));  return Abc_Lit2Var(Fan) == Type;                     }
static inline char *      Smt_EntryName( Smt_Prs_t * p, int Fan )             { assert(Smt_EntryIsName(Fan));  return Abc_NamStr( p->pStrs, Abc_Lit2Var(Fan) );     }
static inline Vec_Int_t * Smt_EntryNode( Smt_Prs_t * p, int Fan )             { assert(!Smt_EntryIsName(Fan)); return Vec_WecEntry( &p->vObjs, Abc_Lit2Var(Fan) );  }

static inline int         Smt_VecEntryIsType( Vec_Int_t * vFans, int i, Smt_LineType_t Type ) { return i < Vec_IntSize(vFans) && Smt_EntryIsName(Vec_IntEntry(vFans, i)) && Smt_EntryIsType(Vec_IntEntry(vFans, i), Type); }
static inline char *      Smt_VecEntryName( Smt_Prs_t * p, Vec_Int_t * vFans, int i )         { return Smt_EntryIsName(Vec_IntEntry(vFans, i)) ? Smt_EntryName(p, Vec_IntEntry(vFans, i)) : NULL;                          }
static inline Vec_Int_t * Smt_VecEntryNode( Smt_Prs_t * p, Vec_Int_t * vFans, int i )         { return Smt_EntryIsName(Vec_IntEntry(vFans, i)) ? NULL : Smt_EntryNode(p, Vec_IntEntry(vFans, i));                          }

#define Smt_ManForEachDir( p, Type, vVec, i )                                                       \
    for ( i = 0; (i < Vec_WecSize(&p->vObjs)) && (((vVec) = Vec_WecEntry(&p->vObjs, i)), 1); i++ )  \
        if ( !Smt_VecEntryIsType(vVec, 0, Type) ) {} else

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Smt_StrToType( char * pName, int * pfSigned )
{
    int Type = 0; *pfSigned = 0;
    if ( !strcmp(pName, "ite") )
        Type = WLC_OBJ_MUX;           // 08: multiplexer
    else if ( !strcmp(pName, "bvlshr") )
        Type = WLC_OBJ_SHIFT_R;       // 09: shift right
    else if ( !strcmp(pName, "bvashr") )
        Type = WLC_OBJ_SHIFT_RA;      // 10: shift right (arithmetic)
    else if ( !strcmp(pName, "bvshl") )
        Type = WLC_OBJ_SHIFT_L;       // 11: shift left
//    else if ( !strcmp(pName, "") )
//        Type = WLC_OBJ_SHIFT_LA;    // 12: shift left (arithmetic)
    else if ( !strcmp(pName, "rotate_right") )
        Type = WLC_OBJ_ROTATE_R;      // 13: rotate right
    else if ( !strcmp(pName, "rotate_left") )
        Type = WLC_OBJ_ROTATE_L;      // 14: rotate left
    else if ( !strcmp(pName, "bvnot") )
        Type = WLC_OBJ_BIT_NOT;       // 15: bitwise NOT
    else if ( !strcmp(pName, "bvand") )
        Type = WLC_OBJ_BIT_AND;       // 16: bitwise AND
    else if ( !strcmp(pName, "bvor") )
        Type = WLC_OBJ_BIT_OR;        // 17: bitwise OR
    else if ( !strcmp(pName, "bvxor") )
        Type = WLC_OBJ_BIT_XOR;       // 18: bitwise XOR
    else if ( !strcmp(pName, "extract") )
        Type = WLC_OBJ_BIT_SELECT;    // 19: bit selection
    else if ( !strcmp(pName, "concat") )
        Type = WLC_OBJ_BIT_CONCAT;    // 20: bit concatenation
    else if ( !strcmp(pName, "zero_extend") )
        Type = WLC_OBJ_BIT_ZEROPAD;   // 21: zero padding
    else if ( !strcmp(pName, "sign_extend") )
        Type = WLC_OBJ_BIT_SIGNEXT, *pfSigned = 1;   // 22: sign extension
    else if ( !strcmp(pName, "not") )
        Type = WLC_OBJ_LOGIC_NOT;     // 23: logic NOT
    else if ( !strcmp(pName, "and") )
        Type = WLC_OBJ_LOGIC_AND;     // 24: logic AND
    else if ( !strcmp(pName, "or") )
        Type = WLC_OBJ_LOGIC_OR;      // 25: logic OR
    else if ( !strcmp(pName, "xor") )
        Type = WLC_OBJ_LOGIC_XOR;     // 26: logic OR
    else if ( !strcmp(pName, "bvcomp") )
        Type = WLC_OBJ_COMP_EQU;      // 27: compare equal
    else if ( !strcmp(pName, "distinct") )
        Type = WLC_OBJ_COMP_NOTEQU;   // 28: compare not equal
    else if ( !strcmp(pName, "bvult") )
        Type = WLC_OBJ_COMP_LESS;     // 29: compare less
    else if ( !strcmp(pName, "bvugt") )
        Type = WLC_OBJ_COMP_MORE;     // 30: compare more
    else if ( !strcmp(pName, "bvule") )
        Type = WLC_OBJ_COMP_LESSEQU;  // 31: compare less or equal
    else if ( !strcmp(pName, "bvuge") )
        Type = WLC_OBJ_COMP_MOREEQU;  // 32: compare more or equal
    else if ( !strcmp(pName, "bvslt") )
        Type = WLC_OBJ_COMP_LESS, *pfSigned = 1;     // 29: compare less
    else if ( !strcmp(pName, "bvsgt") )
        Type = WLC_OBJ_COMP_MORE, *pfSigned = 1;     // 30: compare more
    else if ( !strcmp(pName, "bvsle") )
        Type = WLC_OBJ_COMP_LESSEQU, *pfSigned = 1;  // 31: compare less or equal
    else if ( !strcmp(pName, "bvsge") )
        Type = WLC_OBJ_COMP_MOREEQU, *pfSigned = 1;  // 32: compare more or equal
    else if ( !strcmp(pName, "bvredand") )
        Type = WLC_OBJ_REDUCT_AND;    // 33: reduction AND
    else if ( !strcmp(pName, "bvredor") )
        Type = WLC_OBJ_REDUCT_OR;     // 34: reduction OR
    else if ( !strcmp(pName, "bvredxor") )
        Type = WLC_OBJ_REDUCT_XOR;    // 35: reduction XOR
    else if ( !strcmp(pName, "bvadd") )
        Type = WLC_OBJ_ARI_ADD;       // 36: arithmetic addition
    else if ( !strcmp(pName, "bvsub") )
        Type = WLC_OBJ_ARI_SUB;       // 37: arithmetic subtraction
    else if ( !strcmp(pName, "bvmul") )
        Type = WLC_OBJ_ARI_MULTI;     // 38: arithmetic multiplier
    else if ( !strcmp(pName, "bvudiv") )
        Type = WLC_OBJ_ARI_DIVIDE;    // 39: arithmetic division
    else if ( !strcmp(pName, "bvurem") )
        Type = WLC_OBJ_ARI_MODULUS;   // 40: arithmetic modulus
    else if ( !strcmp(pName, "bvsdiv") )
        Type = WLC_OBJ_ARI_DIVIDE, *pfSigned = 1;    // 39: arithmetic division
    else if ( !strcmp(pName, "bvsrem") )
        Type = WLC_OBJ_ARI_MODULUS, *pfSigned = 1;   // 40: arithmetic modulus
    else if ( !strcmp(pName, "bvsmod") )
        Type = WLC_OBJ_ARI_MODULUS, *pfSigned = 1;   // 40: arithmetic modulus
//    else if ( !strcmp(pName, "") )
//        Type = WLC_OBJ_ARI_POWER;     // 41: arithmetic power
    else if ( !strcmp(pName, "bvneg") )
        Type = WLC_OBJ_ARI_MINUS;       // 42: arithmetic minus
//    else if ( !strcmp(pName, "") )
//        Type = WLC_OBJ_TABLE;         // 43: bit table
    else
    {
        printf( "The following operations is currently not supported (%s)\n", pName );
        fflush( stdout );
        assert( 0 );
    }
    return Type;
}
static inline int Smt_PrsReadType( Smt_Prs_t * p, int iSig, int * pfSigned, int * Value1, int * Value2 )
{
    if ( Smt_EntryIsName(iSig) )
        return Smt_StrToType( Smt_EntryName(p, iSig), pfSigned );
    else
    {
        Vec_Int_t * vFans = Smt_EntryNode( p, iSig );
        char * pStr = Smt_VecEntryName( p, vFans, 0 );  int Type;
        assert( Vec_IntSize(vFans) >= 3 );
        assert( !strcmp(pStr, "_") ); // special op
        *Value1 = *Value2 = -1;
        assert( pStr[0] != 'b' || pStr[1] != 'v' );
        // read type
        Type = Smt_StrToType( Smt_VecEntryName(p, vFans, 1), pfSigned );
        if ( Type == 0 )
            return 0;
        *Value1 = atoi( Smt_VecEntryName(p, vFans, 2) );
        if ( Vec_IntSize(vFans) > 3 )
            *Value2 = atoi( Smt_VecEntryName(p, vFans, 3) );
        return Type;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Smt_PrsCreateNode( Wlc_Ntk_t * pNtk, int Type, int fSigned, int Range, Vec_Int_t * vFanins, char * pName )
{
    char Buffer[100];
    int NameId, fFound;
    int iObj = Wlc_ObjAlloc( pNtk, Type, fSigned, Range-1, 0 );
    assert( Type > 0 );
    assert( Range >= 0 );
    assert( fSigned >= 0 );
    Wlc_ObjAddFanins( pNtk, Wlc_NtkObj(pNtk, iObj), vFanins );
    if ( fSigned )
    {
        Wlc_NtkObj(pNtk, iObj)->Signed = fSigned;
        if ( Vec_IntSize(vFanins) > 0 )
            Wlc_NtkObj(pNtk, Vec_IntEntry(vFanins, 0))->Signed = fSigned;
        if ( Vec_IntSize(vFanins) > 1 )
            Wlc_NtkObj(pNtk, Vec_IntEntry(vFanins, 1))->Signed = fSigned;
    }
    if ( pName == NULL )
    {
        sprintf( Buffer, "_n%d_", iObj );
        pName = Buffer;
    }
    // add node's name
    NameId = Abc_NamStrFindOrAdd( pNtk->pManName, pName, &fFound );
    assert( !fFound );
    assert( iObj == NameId );
    return iObj;
}
static inline int Smt_PrsBuildConstant( Wlc_Ntk_t * pNtk, char * pStr, int nBits, char * pName )
{
    int i, nDigits, iObj;
    Vec_Int_t * vFanins = Vec_IntAlloc( 10 );
    if ( pStr[0] != '#' ) // decimal
    {
        if ( pStr[0] >= '0' && pStr[0] <= '9' )
        {
            int Number = atoi( pStr );
            nBits = Abc_Base2Log( Number+1 );
            assert( nBits < 32 );
            Vec_IntPush( vFanins, Number );
        }
        else
        {
            int fFound, iObj = Abc_NamStrFindOrAdd( pNtk->pManName, pStr, &fFound );
            assert( fFound );
            Vec_IntFree( vFanins );
            return iObj;
        }
    }
    else if ( pStr[1] == 'b' ) // binary
    {
        if ( nBits == -1 )
            nBits = strlen(pStr+2);
        Vec_IntFill( vFanins, Abc_BitWordNum(nBits), 0 );
        for ( i = 0; i < nBits; i++ )
            if ( pStr[2+i] == '1' )
                Abc_InfoSetBit( (unsigned *)Vec_IntArray(vFanins), nBits-1-i );
            else if ( pStr[2+i] != '0' )
                return 0;
    }
    else if ( pStr[1] == 'x' ) // hexadecimal
    {
        if ( nBits == -1 )
            nBits = strlen(pStr+2)*4;
        Vec_IntFill( vFanins, Abc_BitWordNum(nBits), 0 );
        nDigits = Abc_TtReadHexNumber( (word *)Vec_IntArray(vFanins), pStr+2 );
        if ( nDigits != (nBits + 3)/4 )
            return 0;
    }
    else return 0;
    // create constant node
    iObj = Smt_PrsCreateNode( pNtk, WLC_OBJ_CONST, 0, nBits, vFanins, pName );
    Vec_IntFree( vFanins );
    return iObj;
}
int Smt_PrsBuildNode( Wlc_Ntk_t * pNtk, Smt_Prs_t * p, int iNode, int RangeOut, char * pName )
{
    if ( Smt_EntryIsName(iNode) ) // name or constant
    {
        char * pStr = Abc_NamStr(p->pStrs, Abc_Lit2Var(iNode));
        if ( (pStr[0] >= '0' && pStr[0] <= '9') || pStr[0] == '#' )
        { 
            // (_ BitVec 8) #x19
            return Smt_PrsBuildConstant( pNtk, pStr, RangeOut, pName );
        }
        else
        {
            // s3087
            int fFound, iObj = Abc_NamStrFindOrAdd( pNtk->pManName, pStr, &fFound );
            assert( fFound );
            return iObj;
        }
    }
    else // node
    {
        Vec_Int_t * vFans = Smt_EntryNode( p, iNode );
        char * pStr0 = Smt_VecEntryName( p, vFans, 0 );
        char * pStr1 = Smt_VecEntryName( p, vFans, 1 );
        if ( pStr0 && pStr1 && pStr0[0] == '_' && pStr1[0] == 'b' && pStr1[1] == 'v' )
        {
            // (_ bv1 32)
            char * pStr2 = Smt_VecEntryName( p, vFans, 2 );
            assert( Vec_IntSize(vFans) == 3 );
            return Smt_PrsBuildConstant( pNtk, pStr2+2, atoi(pStr2), pName );
        }
        else if ( pStr0 && pStr0[0] == '=' )
        {
            assert( Vec_IntSize(vFans) == 3 );
            iNode = Vec_IntEntry(vFans, 2);
            assert( Smt_EntryIsName(iNode) );
            pStr0 = Smt_EntryName(p, iNode);
            // check the last one is "#b1"
            if ( !strcmp("#b1", pStr0) )
            {
                iNode = Vec_IntEntry(vFans, 1);
                return Smt_PrsBuildNode( pNtk, p, iNode, -1, pName );
            }
            else
            {
                Vec_Int_t * vFanins = Vec_IntAlloc( 2 );
                // get the constant
                int iObj, iOper, iConst = Smt_PrsBuildConstant( pNtk, pStr0, -1, NULL );
                // check the middle one is an operator
                iNode = Vec_IntEntry(vFans, 1);
                iOper = Smt_PrsBuildNode( pNtk, p, iNode, -1, pName );
                // build comparator
                Vec_IntPushTwo( vFanins, iOper, iConst );
                iObj = Smt_PrsCreateNode( pNtk, WLC_OBJ_COMP_EQU, 0, 1, vFanins, pName );
                Vec_IntFree( vFanins );
                return iObj;
            }
        }
        else
        {
            int i, Fan, NameId, iFanin, fSigned, Range, Value1 = -1, Value2 = -1;
            int Type = Smt_PrsReadType( p, Vec_IntEntry(vFans, 0), &fSigned, &Value1, &Value2 );
            // collect fanins
            Vec_Int_t * vFanins = Vec_IntAlloc( 100 );
            Vec_IntForEachEntryStart( vFans, Fan, i, 1 )
            {
                iFanin = Smt_PrsBuildNode( pNtk, p, Fan, -1, NULL );
                if ( iFanin == 0 )
                {
                    Vec_IntFree( vFanins );
                    return 0;
                }
                Vec_IntPush( vFanins, iFanin );
            }
            // update specialized nodes
            assert( Type != WLC_OBJ_BIT_SIGNEXT && Type != WLC_OBJ_BIT_ZEROPAD );
            if ( Type == WLC_OBJ_BIT_SELECT )
            {
                assert( Value1 >= 0 && Value2 >= 0 && Value1 >= Value2 );
                Vec_IntPush( vFanins, (Value1 << 16) | Value2 );
            }
            else if ( Type == WLC_OBJ_ROTATE_R || Type == WLC_OBJ_ROTATE_L )
            {
                char Buffer[10];
                assert( Value1 >= 0 );
                sprintf( Buffer, "%d", Value1 ); 
                NameId = Smt_PrsBuildConstant( pNtk, Buffer, -1, NULL );
                Vec_IntPush( vFanins, NameId );
            }
            // find range
            Range = 0;
            if ( Type >= WLC_OBJ_LOGIC_NOT && Type <= WLC_OBJ_REDUCT_XOR )
                Range = 1;
            else if ( Type == WLC_OBJ_BIT_SELECT )
                Range = Value1 - Value2 + 1;
            else if ( Type == WLC_OBJ_BIT_CONCAT )
            {
                Vec_IntForEachEntry( vFanins, NameId, i )
                    Range += Wlc_ObjRange( Wlc_NtkObj(pNtk, NameId) );
            }
            else if ( Type == WLC_OBJ_MUX )
            {
                int * pArray = Vec_IntArray(vFanins);
                assert( Vec_IntSize(vFanins) == 3 );
                ABC_SWAP( int, pArray[1], pArray[2] );
                NameId = Vec_IntEntry(vFanins, 1);
                Range = Wlc_ObjRange( Wlc_NtkObj(pNtk, NameId) );
            }
            else // to determine range, look at the first argument
            {
                NameId = Vec_IntEntry(vFanins, 0);
                Range = Wlc_ObjRange( Wlc_NtkObj(pNtk, NameId) );
            }
            // create node
            assert( Range > 0 );
            NameId = Smt_PrsCreateNode( pNtk, Type, fSigned, Range, vFanins, pName );
            Vec_IntFree( vFanins );
            return NameId;
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Wlc_Ntk_t * Smt_PrsBuild( Smt_Prs_t * p )
{
    Wlc_Ntk_t * pNtk;
    Vec_Int_t * vFans, * vFans2, * vFans3; 
    Vec_Int_t * vAsserts = Vec_IntAlloc(100);
    char * pName, * pRange, * pValue;
    int i, k, Fan, Fan3, iObj, Status, Range, NameId, nBits = 0;
    // issue warnings about unknown dirs
    vFans = Vec_WecEntry( &p->vObjs, 0 );
    Vec_IntForEachEntry( vFans, Fan, i )
    {
        assert( !Smt_EntryIsName(Fan) );
        vFans2 = Smt_VecEntryNode( p, vFans, i );
        Fan = Vec_IntEntry(vFans2, 0);
        assert( Smt_EntryIsName(Fan) );
        if ( Abc_Lit2Var(Fan) >= SMT_PRS_END )
            printf( "Ignoring directive \"%s\".\n", Smt_EntryName(p, Fan) );
    }
    // start network and create primary inputs
    pNtk = Wlc_NtkAlloc( p->pName, 1000 );
    pNtk->pManName = Abc_NamStart( 1000, 24 );
    Smt_ManForEachDir( p, SMT_PRS_DECLARE_FUN, vFans, i )
    {
        assert( Vec_IntSize(vFans) == 4 );
        assert( Smt_VecEntryIsType(vFans, 0, SMT_PRS_DECLARE_FUN) );
        // get name
        Fan = Vec_IntEntry(vFans, 1);
        assert( Smt_EntryIsName(Fan) );
        pName = Smt_EntryName(p, Fan);
        // skip ()
        Fan = Vec_IntEntry(vFans, 2);
        assert( !Smt_EntryIsName(Fan) );
        // check type (Bool or BitVec)
        Fan = Vec_IntEntry(vFans, 3);
        if ( Smt_EntryIsName(Fan) ) 
        {
            //(declare-fun s1 () Bool)
            assert( !strcmp("Bool", Smt_VecEntryName(p, vFans, 3)) );
            Range = 1;
        }
        else
        {
            // (declare-fun s1 () (_ BitVec 64))
            // get range
            Fan = Vec_IntEntry(vFans, 3);
            assert( !Smt_EntryIsName(Fan) );
            vFans2 = Smt_EntryNode(p, Fan);
            assert( Vec_IntSize(vFans2) == 3 );
            assert( !strcmp("_", Smt_VecEntryName(p, vFans2, 0)) );
            assert( !strcmp("BitVec", Smt_VecEntryName(p, vFans2, 1)) );
            Fan = Vec_IntEntry(vFans2, 2);
            assert( Smt_EntryIsName(Fan) );
            pRange = Smt_EntryName(p, Fan);
            Range = atoi(pRange);
        }
        // create node
        iObj = Wlc_ObjAlloc( pNtk, WLC_OBJ_PI, 0, Range-1, 0 );
        NameId = Abc_NamStrFindOrAdd( pNtk->pManName, pName, NULL );
        assert( iObj == NameId );
        // save values
        Vec_IntPush( &pNtk->vValues, NameId );
        Vec_IntPush( &pNtk->vValues, nBits );
        Vec_IntPush( &pNtk->vValues, Range );
        nBits += Range;
    }
    // create constants
    Smt_ManForEachDir( p, SMT_PRS_DEFINE_FUN, vFans, i )
    {
        assert( Vec_IntSize(vFans) == 5 );
        assert( Smt_VecEntryIsType(vFans, 0, SMT_PRS_DEFINE_FUN) );
        // get name
        Fan = Vec_IntEntry(vFans, 1);
        assert( Smt_EntryIsName(Fan) );
        pName = Smt_EntryName(p, Fan);
        // skip ()
        Fan = Vec_IntEntry(vFans, 2);
        assert( !Smt_EntryIsName(Fan) );
        // check type (Bool or BitVec)
        Fan = Vec_IntEntry(vFans, 3);
        if ( Smt_EntryIsName(Fan) ) 
        {
            // (define-fun s_2 () Bool false)
            assert( !strcmp("Bool", Smt_VecEntryName(p, vFans, 3)) );
            Range = 1;
            pValue = Smt_VecEntryName(p, vFans, 4);
            if ( !strcmp("false", pValue) )
                pValue = "#b0";
            else if ( !strcmp("true", pValue) )
                pValue = "#b1";
            else assert( 0 );
            Status = Smt_PrsBuildConstant( pNtk, pValue, Range, pName );
        }
        else
        {
            // (define-fun s702 () (_ BitVec 4) #xe)
            // (define-fun s1 () (_ BitVec 8) (bvneg #x7f))
            // get range
            Fan = Vec_IntEntry(vFans, 3);
            assert( !Smt_EntryIsName(Fan) );
            vFans2 = Smt_VecEntryNode(p, vFans, 3);
            assert( Vec_IntSize(vFans2) == 3 );
            assert( !strcmp("_", Smt_VecEntryName(p, vFans2, 0)) );
            assert( !strcmp("BitVec", Smt_VecEntryName(p, vFans2, 1)) );
            // get range
            Fan = Vec_IntEntry(vFans2, 2);
            assert( Smt_EntryIsName(Fan) );
            pRange = Smt_EntryName(p, Fan);
            Range = atoi(pRange);
            // get constant
            Fan = Vec_IntEntry(vFans, 4);
            Status = Smt_PrsBuildNode( pNtk, p, Fan, Range, pName );
        }        
        if ( !Status )
        {
            Wlc_NtkFree( pNtk ); pNtk = NULL;
            goto finish;
        }
    }
    // process let-statements
    Smt_ManForEachDir( p, SMT_PRS_LET, vFans, i )
    {
        // let ((s35550 (bvor s48 s35549)))
        assert( Vec_IntSize(vFans) == 3 );
        assert( Smt_VecEntryIsType(vFans, 0, SMT_PRS_LET) );
        // get parts
        Fan = Vec_IntEntry(vFans, 1);
        assert( !Smt_EntryIsName(Fan) );
        vFans2 = Smt_EntryNode(p, Fan);
        if ( Smt_VecEntryIsType(vFans2, 0, SMT_PRS_LET) )
            continue;
        // iterate through the parts
        Vec_IntForEachEntry( vFans2, Fan, k )
        {
            // s35550 (bvor s48 s35549)
            Fan = Vec_IntEntry(vFans2, 0);
            assert( !Smt_EntryIsName(Fan) );
            vFans3 = Smt_EntryNode(p, Fan);
            // get the name
            Fan3 = Vec_IntEntry(vFans3, 0);
            assert( Smt_EntryIsName(Fan3) );
            pName = Smt_EntryName(p, Fan3);
            // get function
            Fan3 = Vec_IntEntry(vFans3, 1);
            assert( !Smt_EntryIsName(Fan3) );
            Status = Smt_PrsBuildNode( pNtk, p, Fan3, -1, pName );
            if ( !Status )
            {
                Wlc_NtkFree( pNtk ); pNtk = NULL;
                goto finish;
            }
        }
    }
    // process assert-statements
    Vec_IntClear( vAsserts );
    Smt_ManForEachDir( p, SMT_PRS_ASSERT, vFans, i )
    {
        //(assert ; no quantifiers
        //   (let ((s2 (bvsge s0 s1)))
        //   (not s2)))
        //(assert (not (= s0 #x00)))
        assert( Vec_IntSize(vFans) == 2 );
        assert( Smt_VecEntryIsType(vFans, 0, SMT_PRS_ASSERT) );
        // get second directive
        Fan = Vec_IntEntry(vFans, 1);
        if ( !Smt_EntryIsName(Fan) )
        {
            // find the final let-statement
            vFans2 = Smt_VecEntryNode(p, vFans, 1);
            while ( Smt_VecEntryIsType(vFans2, 0, SMT_PRS_LET) )
            {
                Fan = Vec_IntEntry(vFans2, 2);
                if ( Smt_EntryIsName(Fan) )
                    break;
                vFans2 = Smt_VecEntryNode(p, vFans2, 2);
            }
        }
        // find name or create node
        iObj = Smt_PrsBuildNode( pNtk, p, Fan, -1, NULL );
        if ( !iObj )
        {
            Wlc_NtkFree( pNtk ); pNtk = NULL;
            goto finish;
        }
        Vec_IntPush( vAsserts, iObj );
    }
    // build AND of asserts
    if ( Vec_IntSize(vAsserts) == 1 )
        iObj = Smt_PrsCreateNode( pNtk, WLC_OBJ_BUF, 0, 1, vAsserts, "miter_output" );
    else
    {
        iObj = Smt_PrsCreateNode( pNtk, WLC_OBJ_BIT_CONCAT, 0, Vec_IntSize(vAsserts), vAsserts, NULL );
        Vec_IntFill( vAsserts, 1, iObj );
        iObj = Smt_PrsCreateNode( pNtk, WLC_OBJ_REDUCT_AND, 0, 1, vAsserts, "miter_output" );
    }
    Wlc_ObjSetCo( pNtk, Wlc_NtkObj(pNtk, iObj), 0 );
    // create nameIDs
    vFans = Vec_IntStartNatural( Wlc_NtkObjNumMax(pNtk) );
    Vec_IntAppend( &pNtk->vNameIds, vFans );
    Vec_IntFree( vFans );
    //Wlc_NtkReport( pNtk, NULL );
finish:
    // cleanup
    Vec_IntFree(vAsserts);
    return pNtk;
}




/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// create error message
static inline int Smt_PrsErrorSet( Smt_Prs_t * p, char * pError, int Value )
{
    assert( !p->ErrorStr[0] );
    sprintf( p->ErrorStr, "%s", pError );
    return Value;
}
// print error message
static inline int Smt_PrsErrorPrint( Smt_Prs_t * p )
{
    char * pThis; int iLine = 0;
    if ( !p->ErrorStr[0] ) return 1;
    for ( pThis = p->pBuffer; pThis < p->pCur; pThis++ )
        iLine += (int)(*pThis == '\n');
    printf( "Line %d: %s\n", iLine, p->ErrorStr );
    return 0;
}
static inline char * Smt_PrsLoadFile( char * pFileName, char ** ppLimit )
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
    pBuffer = ABC_ALLOC( char, nFileSize + 16 );
    pBuffer[0] = '\n';
    RetValue = fread( pBuffer+1, nFileSize, 1, pFile );
    fclose( pFile );
    // terminate the string with '\0'
    pBuffer[nFileSize + 1] = '\n';
    pBuffer[nFileSize + 2] = '\0';
    *ppLimit = pBuffer + nFileSize + 2;
    return pBuffer;
}
static inline int Smt_PrsRemoveComments( char * pBuffer, char * pLimit )
{
    char * pTemp; int nCount1 = 0, nCount2 = 0;
    for ( pTemp = pBuffer; pTemp < pLimit; pTemp++ )
    {
        if ( *pTemp == '(' )
            nCount1++;
        else if ( *pTemp == ')' )
            nCount2++;
        else if ( *pTemp == ';' )
            while ( *pTemp && *pTemp != '\n' )
                *pTemp++ = ' ';
    }
    if ( nCount1 != nCount2 )
        printf( "The input SMTLIB file has different number of opening and closing parentheses (%d and %d).\n", nCount1, nCount2 );
    else if ( nCount1 == 0 )
        printf( "The input SMTLIB file has no opening or closing parentheses.\n" );
    return nCount1 == nCount2 ? nCount1 : 0;
}
static inline Smt_Prs_t * Smt_PrsAlloc( char * pFileName, char * pBuffer, char * pLimit, int nObjs )
{
    Smt_Prs_t * p;
    if ( nObjs == 0 )
        return NULL;
    p = ABC_CALLOC( Smt_Prs_t, 1 );
    p->pName   = pFileName;
    p->pBuffer = pBuffer;
    p->pLimit  = pLimit;
    p->pCur    = pBuffer;
    p->pStrs   = Abc_NamStart( 1000, 24 );
    Smt_AddTypes( p->pStrs );
    Vec_IntGrow( &p->vStack, 100 );
    //Vec_WecGrow( &p->vDepth, 100 );
    Vec_WecGrow( &p->vObjs, nObjs+1 );
    return p;
}
static inline void Smt_PrsFree( Smt_Prs_t * p )
{
    if ( p->pStrs )
        Abc_NamDeref( p->pStrs );
    Vec_IntErase( &p->vStack );
    //Vec_WecErase( &p->vDepth );
    Vec_WecErase( &p->vObjs );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Smt_PrsIsSpace( char c )
{
    return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}
static inline void Smt_PrsSkipSpaces( Smt_Prs_t * p )
{
    while ( Smt_PrsIsSpace(*p->pCur) )
        p->pCur++;
}
static inline void Smt_PrsSkipNonSpaces( Smt_Prs_t * p )
{
    while ( p->pCur < p->pLimit && !Smt_PrsIsSpace(*p->pCur) && *p->pCur != '(' && *p->pCur != ')' )
        p->pCur++;
}
void Smt_PrsReadLines( Smt_Prs_t * p )
{
    assert( Vec_IntSize(&p->vStack) == 0 );
    //assert( Vec_WecSize(&p->vDepth) == 0 );
    assert( Vec_WecSize(&p->vObjs) == 0 );
    // add top node at level 0
    //Vec_WecPushLevel( &p->vDepth );
    //Vec_WecPush( &p->vDepth, Vec_IntSize(&p->vStack), Vec_WecSize(&p->vObjs) );
    // add top node
    Vec_IntPush( &p->vStack, Vec_WecSize(&p->vObjs) );
    Vec_WecPushLevel( &p->vObjs );
    // add other nodes
    for ( p->pCur = p->pBuffer; p->pCur < p->pLimit; p->pCur++ )
    {
        Smt_PrsSkipSpaces( p );
        if ( *p->pCur == '(' )
        {
            // add new node at this depth
            //assert( Vec_WecSize(&p->vDepth) >= Vec_IntSize(&p->vStack) );
            //if ( Vec_WecSize(&p->vDepth) == Vec_IntSize(&p->vStack) )
            //    Vec_WecPushLevel(&p->vDepth);
            //Vec_WecPush( &p->vDepth, Vec_IntSize(&p->vStack), Vec_WecSize(&p->vObjs) );
            // add fanin to node on the previous level
            Vec_IntPush( Vec_WecEntry(&p->vObjs, Vec_IntEntryLast(&p->vStack)), Abc_Var2Lit(Vec_WecSize(&p->vObjs), 0) );            
            // add node to the stack
            Vec_IntPush( &p->vStack, Vec_WecSize(&p->vObjs) );
            Vec_WecPushLevel( &p->vObjs );
        }
        else if ( *p->pCur == ')' )
        {
            Vec_IntPop( &p->vStack );
        }
        else  // token
        {
            char * pStart = p->pCur; 
            Smt_PrsSkipNonSpaces( p );
            if ( p->pCur < p->pLimit )
            {
                // add fanin
                int iToken = Abc_NamStrFindOrAddLim( p->pStrs, pStart, p->pCur--, NULL );
                Vec_IntPush( Vec_WecEntry(&p->vObjs, Vec_IntEntryLast(&p->vStack)), Abc_Var2Lit(iToken, 1) );
            }
        }
    }
    assert( Vec_IntSize(&p->vStack) == 1 );
    assert( Vec_WecSize(&p->vObjs) == Vec_WecCap(&p->vObjs) );
}
void Smt_PrsPrintParser_rec( Smt_Prs_t * p, int iObj, int Depth )
{
    Vec_Int_t * vFans; int i, Fan;
    printf( "%*s(\n", Depth, "" );
    vFans = Vec_WecEntry( &p->vObjs, iObj );
    Vec_IntForEachEntry( vFans, Fan, i )
    {
        if ( Abc_LitIsCompl(Fan) )
        {
            printf( "%*s", Depth+2, "" );
            printf( "%s\n", Abc_NamStr(p->pStrs, Abc_Lit2Var(Fan)) );
        }
        else
            Smt_PrsPrintParser_rec( p, Abc_Lit2Var(Fan), Depth+4 );
    }
    printf( "%*s)\n", Depth, "" );
}
void Smt_PrsPrintParser( Smt_Prs_t * p )
{
//    Vec_WecPrint( &p->vDepth, 0 );
    Smt_PrsPrintParser_rec( p, 0, 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Wlc_Ntk_t * Wlc_ReadSmtBuffer( char * pFileName, char * pBuffer, char * pLimit )
{
    Wlc_Ntk_t * pNtk = NULL;
    int nCount = Smt_PrsRemoveComments( pBuffer, pLimit );
    Smt_Prs_t * p = Smt_PrsAlloc( pFileName, pBuffer, pLimit, nCount );
    if ( p == NULL )
        return NULL;
    Smt_PrsReadLines( p );
    //Smt_PrsPrintParser( p );
    if ( Smt_PrsErrorPrint(p) )
        pNtk = Smt_PrsBuild( p );
    Smt_PrsFree( p );
    return pNtk;
}
Wlc_Ntk_t * Wlc_ReadSmt( char * pFileName )
{
    Wlc_Ntk_t * pNtk = NULL;
    char * pBuffer, * pLimit; 
    pBuffer = Smt_PrsLoadFile( pFileName, &pLimit );
    if ( pBuffer == NULL )
        return NULL;
    pNtk = Wlc_ReadSmtBuffer( pFileName, pBuffer, pLimit );
    ABC_FREE( pBuffer );
    return pNtk;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
