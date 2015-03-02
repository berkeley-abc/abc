/**CFile****************************************************************

  FileName    [cbaNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Netlist manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaNtk.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Cba_Pair_t_ Cba_Pair_t;
struct Cba_Pair_t_
{
    Cba_ObjType_t Type;
    char *        pName;
    char *        pSymb;
};
static const char * s_Pref = "ABC_";
static Cba_Pair_t s_Types[CBA_BOX_UNKNOWN] =
{ 
    { CBA_OBJ_NONE,     "NONE",    NULL    },
    { CBA_OBJ_PI,       "PI",      NULL    },
    { CBA_OBJ_PO,       "PO",      NULL    },
    { CBA_OBJ_BI,       "BI",      NULL    },
    { CBA_OBJ_BO,       "BO",      NULL    },
    { CBA_OBJ_BOX,      "BOX",     NULL    },
    
    { CBA_BOX_CF,       "CF",      "o"     },
    { CBA_BOX_CT,       "CT",      "o"     }, 
    { CBA_BOX_CX,       "CX",      "o"     }, 
    { CBA_BOX_CZ,       "CZ",      "o"     },
    { CBA_BOX_BUF,      "BUF",     "ao"    },
    { CBA_BOX_INV,      "INV",     "ao"    },
    { CBA_BOX_AND,      "AND",     "abo"   },
    { CBA_BOX_NAND,     "NAND",    "abo"   },
    { CBA_BOX_OR,       "OR",      "abo"   },
    { CBA_BOX_NOR,      "NOR",     "abo"   },
    { CBA_BOX_XOR,      "XOR",     "abo"   },
    { CBA_BOX_XNOR,     "XNOR",    "abo"   },
    { CBA_BOX_SHARP,    "SHARP",   "abo"   },
    { CBA_BOX_SHARPL,   "SHARPL",  "abo"   },
    { CBA_BOX_MUX,      "MUX",     "cabo"  },
    { CBA_BOX_MAJ,      "MAJ",     "abco"  },
    
    { CBA_BOX_RAND,     "RAND",    "ao"    },
    { CBA_BOX_RNAND,    "RNAND",   "ao"    },
    { CBA_BOX_ROR,      "ROR",     "ao"    },
    { CBA_BOX_RNOR,     "RNOR",    "ao"    },
    { CBA_BOX_RXOR,     "RXOR",    "ao"    },
    { CBA_BOX_RXNOR,    "RXNOR",   "ao"    },
    
    { CBA_BOX_LAND,     "LAND",    "abo"   },
    { CBA_BOX_LNAND,    "LNAND",   "abo"   },
    { CBA_BOX_LOR,      "LOR",     "abo"   },
    { CBA_BOX_LNOR,     "LNOR",    "abo"   },
    { CBA_BOX_LXOR,     "LXOR",    "abo"   },
    { CBA_BOX_LXNOR,    "LXNOR",   "abo"   },
    
    { CBA_BOX_NMUX,     "NMUX",    "abo"   },
    { CBA_BOX_SEL,      "SEL",     "abo"   },
    { CBA_BOX_PSEL,     "PSEL",    "iabo"  },
    { CBA_BOX_ENC,      "ENC",     "ao"    },
    { CBA_BOX_PENC,     "PENC",    "ao"    },
    { CBA_BOX_DEC,      "DEC",     "ao"    },
    { CBA_BOX_EDEC,     "EDEC",    "abo"   },
    
    { CBA_BOX_ADD,      "ADD",     "iabso" },
    { CBA_BOX_SUB,      "SUB",     "abo"   },
    { CBA_BOX_MUL,      "MUL",     "abo"   },
    { CBA_BOX_DIV,      "DIV",     "abo"   },
    { CBA_BOX_MOD,      "MOD",     "abo"   },
    { CBA_BOX_REM,      "REM",     "abo"   },
    { CBA_BOX_POW,      "POW",     "abo"   },
    { CBA_BOX_MIN,      "MIN",     "ao"    },
    { CBA_BOX_ABS,      "ABS",     "ao"    },

    { CBA_BOX_LTHAN,    "LTHAN",   "iabo"  },
    { CBA_BOX_LETHAN,   "LETHAN",  "abo"   },
    { CBA_BOX_METHAN,   "METHAN",  "abo"   },
    { CBA_BOX_MTHAN,    "MTHAN",   "abo"   },
    { CBA_BOX_EQU,      "EQU",     "abo"   },
    { CBA_BOX_NEQU,     "NEQU",    "abo"   },
    
    { CBA_BOX_SHIL,     "SHIL",    "abo"   },
    { CBA_BOX_SHIR,     "SHIR",    "abo"   },
    { CBA_BOX_ROTL,     "ROTL",    "abo"   },
    { CBA_BOX_ROTR,     "ROTR",    "abo"   },

    { CBA_BOX_GATE,     "GATE",    "io"    },
    { CBA_BOX_LUT,      "LUT",     "io"    },
    { CBA_BOX_ASSIGN,   "ASSIGN",  "abo"   },
    
    { CBA_BOX_TRI,      "TRI",     "abo"   },
    { CBA_BOX_RAM,      "RAM",     "eadro" },
    { CBA_BOX_RAMR,     "RAMR",    "eamo"  },
    { CBA_BOX_RAMW,     "RAMW",    "eado"  },
    { CBA_BOX_RAMWC,    "RAMWC",   "ceado" },
    { CBA_BOX_RAMBOX,   "RAMBOX",  "io"    },
    
    { CBA_BOX_LATCH,    "LATCH",   "dvsgq" },
    { CBA_BOX_LATCHRS,  "LATCHRS", "dsrgq" },
    { CBA_BOX_DFF,      "DFF",     "dvscq" },
    { CBA_BOX_DFFRS,    "DFFRS",   "dsrcq" }
}; 
static inline int Cba_GetTypeId( Cba_ObjType_t Type )
{
    int i;
    for ( i = 1; i < CBA_BOX_UNKNOWN; i++ )
        if ( s_Types[i].Type == Type )
            return i;
    return -1;
}
void Cba_ManSetupTypes( char ** pNames, char ** pSymbs )
{
    int Type, Id;
    for ( Type = 1; Type < CBA_BOX_UNKNOWN; Type++ )
    {
        Id = Cba_GetTypeId( Type );
        pNames[Type] = s_Types[Id].pName;
        pSymbs[Type] = s_Types[Id].pSymb;
    }
}

char * Cba_NtkGenerateName( Cba_Ntk_t * p, Cba_ObjType_t Type, Vec_Int_t * vBits )
{
    static char Buffer[100]; 
    char * pTemp; int i, Bits;
    char * pName = Cba_ManPrimName( p->pDesign, Type );
    char * pSymb = Cba_ManPrimSymb( p->pDesign, Type );
    assert( Vec_IntSize(vBits) == (int)strlen(pSymb) );
    sprintf( Buffer, "%s%s_", s_Pref, pName );
    pTemp = Buffer + strlen(Buffer);
    Vec_IntForEachEntry( vBits, Bits, i )
    {
        sprintf( pTemp, "%c%d", pSymb[i], Bits );
        pTemp += strlen(pTemp);
    }
    //Vec_IntPrint( vBits );
    //printf( "%s\n", Buffer );
    return Buffer;
}

Cba_ObjType_t Cba_NameToType( char * pName )
{
    int i;
    if ( strncmp(pName, s_Pref, strlen(s_Pref)) )
        return 0;
    pName += strlen(s_Pref);
    for ( i = 1; i < CBA_BOX_UNKNOWN; i++ )
        if ( !strncmp(pName, s_Types[i].pName, strlen(s_Types[i].pName)) )
            return s_Types[i].Type;
    return 0;
}
Vec_Int_t * Cba_NameToRanges( char * pName )
{
    static Vec_Int_t Bits, * vBits = &Bits;
    static int pArray[10];
    char * pTemp; 
    int Num = 0, Count = 0;
    // initialize array
    vBits->pArray = pArray;
    vBits->nSize = 0;
    vBits->nCap = 10;
    // check the name
    assert( !strncmp(pName, s_Pref, strlen(s_Pref)) );
    for ( pTemp = pName; *pTemp && !Cba_CharIsDigit(*pTemp); pTemp++ );
    assert( Cba_CharIsDigit(*pTemp) );
    for ( ; *pTemp; pTemp++ )
    {
        if ( Cba_CharIsDigit(*pTemp) )
            Num = 10 * Num + *pTemp - '0';
        else
            Vec_IntPush( vBits, Num ), Count += Num, Num = 0;
    }
    assert( Num > 0 );
    Vec_IntPush( vBits, Num );  Count += Num;
    assert( Vec_IntSize(vBits) <= 10 );
    return vBits;
}


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Replaces fanin iOld by iNew in all fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_NtkUpdateFanout( Cba_Ntk_t * p, int iOld, int iNew )
{
    int iCo;
    assert( Cba_ObjIsCi(p, iOld) );
    assert( Cba_ObjIsCi(p, iNew) );
    Cba_ObjForEachFanout( p, iOld, iCo )
    {
        assert( Cba_ObjFanin(p, iCo) == iOld );
        Cba_ObjCleanFanin( p, iCo );
        Cba_ObjSetFanin( p, iCo, iNew );
    }
    Cba_ObjSetFanout( p, iNew, Cba_ObjFanout(p, iOld) );
    Cba_ObjSetFanout( p, iOld, 0 );
}

/**Function*************************************************************

  Synopsis    [Derives fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_NtkDeriveFanout( Cba_Ntk_t * p )
{
    int iCi, iCo;
    assert( !Cba_NtkHasFanouts(p) );
    Cba_NtkStartFanouts( p );
    Cba_NtkForEachCo( p, iCo )
    {
        assert( !Cba_ObjNextFanout(p, iCo) );
        iCi = Cba_ObjFanin(p, iCo);
        if ( Cba_ObjFanout(p, iCi) )
            Cba_ObjSetNextFanout( p, Cba_ObjFanout(p, iCi), iCo );
        Cba_ObjSetFanout( p, iCi, iCo );
    }
    Cba_NtkForEachCo( p, iCo )
        if ( !Cba_ObjNextFanout(p, iCo) )
            Cba_ObjSetFanout( p, Cba_ObjFanin(p, iCo), iCo );
}
void Cba_ManDeriveFanout( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_NtkDeriveFanout( pNtk );
}

/**Function*************************************************************

  Synopsis    [Assigns word-level names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_ManAssignInternTwo( Cba_Ntk_t * p, int iNum, int nDigits, int fPis, Vec_Int_t * vMap )
{
    char Buffer[16]; int i, NameId = 0;
    for ( i = 0; !NameId || Vec_IntEntry(vMap, NameId); i++ )
    {
        if ( i == 0 )
            sprintf( Buffer, "%s%0*d", fPis ? "i" : "n", nDigits, iNum );
        else
            sprintf( Buffer, "%s%0*d_%d", fPis ? "i" : "n", nDigits, iNum, i );
        NameId = Abc_NamStrFindOrAdd( p->pDesign->pStrs, Buffer, NULL );
    }
    Vec_IntWriteEntry( vMap, NameId, iNum );
    return NameId;
}
int Cba_ManAssignCountNames( Cba_Ntk_t * p )
{
    int i, iObj, iBox, Count = 0;
    Cba_NtkForEachPiMain( p, iObj, i )
        if ( !Cba_ObjNameInt(p, iObj) )
            Count++;
    Cba_NtkForEachBox( p, iBox )
        Cba_BoxForEachBoMain( p, iBox, iObj, i )
            if ( !Cba_ObjNameInt(p, iObj) )
                Count++;
    return Count;
}
void Cba_ManAssignInternWordNamesNtk( Cba_Ntk_t * p, Vec_Int_t * vMap )
{
    int k, iObj, iTerm, iName = -1, iBit = -1;
    int nDigits, nPis = 0, nPos = 0, nNames = 1;
    // start names
    if ( !Cba_NtkHasNames(p) )
        Cba_NtkStartNames(p);
    nDigits = Abc_Base10Log( Cba_ManAssignCountNames(p) );
    // assign CI names
    Cba_NtkForEachCi( p, iObj )
    {
        if ( Cba_ObjNameInt(p, iObj) )
        {
            iName = -1;
            iBit = -1;
            continue;
        }
        if ( Cba_ObjBit(p, iObj) )
        {
            assert( iBit > 0 );
            Cba_ObjSetName( p, iObj, Abc_Var2Lit2(iBit++, CBA_NAME_INDEX) );
        }
        else
        {
            int Type = Cba_ObjType(p, iObj);
            int Range = Cba_ObjIsPi(p, iObj) ? Cba_ObjPiRange(p, iObj) : Cba_BoxBoRange(p, iObj);
            iName = Cba_ManAssignInternTwo( p, nNames++, nDigits, Cba_ObjIsPi(p, iObj), vMap );
            if ( Range == 1 )
                Cba_ObjSetName( p, iObj, Abc_Var2Lit2(iName, CBA_NAME_BIN) );
            else
                Cba_ObjSetName( p, iObj, Abc_Var2Lit2(iName, CBA_NAME_WORD) );
            iBit = 1;
        }
    }
    // transfer names to the interface
    for ( k = 0; k < Cba_NtkInfoNum(p); k++ )
    {
        //char * pName = Cba_NtkName(p);
        if ( Cba_NtkInfoType(p, k) == 1 ) // PI
        {
            iObj = Cba_NtkPi(p, nPis);
            assert( !Cba_ObjBit(p, iObj) );
            assert( Cba_ObjNameType(p, iObj) <= CBA_NAME_WORD );
            Cba_NtkSetInfoName( p, k, Abc_Var2Lit2(Cba_ObjNameId(p, iObj), 1) );
            nPis += Cba_NtkInfoRange(p, k);
        }
        else if ( Cba_NtkInfoType(p, k) == 2 ) // PO
        {
            iObj = Cba_NtkPo(p, nPos);
            assert( !Cba_ObjBit(p, iObj) );
            iObj = Cba_ObjFanin(p, iObj);
            assert( Cba_ObjNameType(p, iObj) <= CBA_NAME_WORD );
            Cba_NtkSetInfoName( p, k, Abc_Var2Lit2(Cba_ObjNameId(p, iObj), 2) );
            nPos += Cba_NtkInfoRange(p, k);
        }
        else assert( 0 );
    }
    assert( nPis == Cba_NtkPiNum(p) );
    assert( nPos == Cba_NtkPoNum(p) );
    // unmark all names
    Cba_NtkForEachPi( p, iObj, k )
        if ( Cba_ObjNameType(p, iObj) <= CBA_NAME_WORD )
            Vec_IntWriteEntry( vMap, Cba_ObjNameId(p, iObj), 0 );
    Cba_NtkForEachBox( p, iObj )
        Cba_BoxForEachBo( p, iObj, iTerm, k )
            if ( Cba_ObjNameType(p, iTerm) <= CBA_NAME_WORD )
                Vec_IntWriteEntry( vMap, Cba_ObjNameId(p, iTerm), 0 );
//    printf( "Generated %d word-level names.\n", nNames-1 );
}
void Cba_ManAssignInternWordNames( Cba_Man_t * p )
{
    Vec_Int_t * vMap = Vec_IntStart( Cba_ManObjNum(p) );
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManAssignInternWordNamesNtk( pNtk, vMap );
    Vec_IntFree( vMap );
}


/**Function*************************************************************

  Synopsis    [Count number of objects after collapsing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_ManClpObjNum_rec( Cba_Ntk_t * p )
{
    int i, Counter = 0;
    if ( p->Count >= 0 )
        return p->Count;
    Cba_NtkForEachBox( p, i )
        Counter += Cba_ObjIsBoxUser(p, i) ? Cba_ManClpObjNum_rec( Cba_BoxNtk(p, i) ) + 3*Cba_BoxBoNum(p, i) : Cba_BoxSize(p, i);
    return (p->Count = Counter);
}
int Cba_ManClpObjNum( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        pNtk->Count = -1;
    return Cba_NtkPioNum( Cba_ManRoot(p) ) + Cba_ManClpObjNum_rec( Cba_ManRoot(p) );
}

/**Function*************************************************************

  Synopsis    [Collects boxes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_NtkDfs_rec( Cba_Ntk_t * p, int iObj, Vec_Int_t * vBoxes )
{
    int k, iFanin;
    if ( Cba_ObjIsBo(p, iObj) == 1 )
    {
        Cba_NtkDfs_rec( p, Cba_ObjFanin(p, iObj), vBoxes );
        return;
    }
    assert( Cba_ObjIsPi(p, iObj) || Cba_ObjIsBox(p, iObj) );
    if ( Cba_ObjCopy(p, iObj) > 0 ) // visited
        return;
    Cba_ObjSetCopy( p, iObj, 1 );
    Cba_BoxForEachFanin( p, iObj, iFanin, k )
        Cba_NtkDfs_rec( p, iFanin, vBoxes );
    Vec_IntPush( vBoxes, iObj );
}
Vec_Int_t * Cba_NtkDfs( Cba_Ntk_t * p )
{
    int i, iObj;
    Vec_Int_t * vBoxes = Vec_IntAlloc( Cba_NtkBoxNum(p) );
    Cba_NtkStartCopies( p ); // -1 = not visited; 1 = finished
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjSetCopy( p, iObj, 1 );
    Cba_NtkForEachPo( p, iObj, i )
        Cba_NtkDfs_rec( p, Cba_ObjFanin(p, iObj), vBoxes );
    return vBoxes;
}

/**Function*************************************************************

  Synopsis    [Collects user boxes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_NtkDfsUserBoxes_rec( Cba_Ntk_t * p, int iObj, Vec_Int_t * vBoxes )
{
    int k, iFanin;
    assert( Cba_ObjIsBoxUser(p, iObj) );
    if ( Cba_ObjCopy(p, iObj) == 1 ) // visited
        return 1;
    if ( Cba_ObjCopy(p, iObj) == 0 ) // loop
        return 0;
    Cba_ObjSetCopy( p, iObj, 0 );
    Cba_BoxForEachFanin( p, iObj, iFanin, k )
        if ( Cba_ObjIsBo(p, iFanin) && Cba_ObjIsBoxUser(p, Cba_ObjFanin(p, iFanin)) )
            if ( !Cba_NtkDfsUserBoxes_rec( p, Cba_ObjFanin(p, iFanin), vBoxes ) )
                return 0;
    Vec_IntPush( vBoxes, iObj );
    Cba_ObjSetCopy( p, iObj, 1 );
    return 1;
}
int Cba_NtkDfsUserBoxes( Cba_Ntk_t * p )
{
    int iObj;
    Cba_NtkStartCopies( p ); // -1 = not visited; 0 = on the path; 1 = finished
    Vec_IntClear( &p->vArray );
    Cba_NtkForEachBoxUser( p, iObj )
        if ( !Cba_NtkDfsUserBoxes_rec( p, iObj, &p->vArray ) )
        {
            printf( "Cyclic dependency of user boxes is detected.\n" );
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
void Cba_NtkCollapse_rec( Cba_Ntk_t * pNew, Cba_Ntk_t * p, Vec_Int_t * vSigs )
{
    int i, iObj, iObjNew, iTerm;
    Cba_NtkStartCopies( p );
    // set PI copies
    assert( Vec_IntSize(vSigs) == Cba_NtkPiNum(p) );
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjSetCopy( p, iObj, Vec_IntEntry(vSigs, i) );
    // duplicate internal objects and create buffers for hierarchy instances
    Cba_NtkForEachBox( p, iObj )
        if ( Cba_ObjIsBoxPrim( p, iObj ) )
            Cba_BoxDup( pNew, p, iObj );
        else
        {
            Cba_BoxForEachBo( p, iObj, iTerm, i )
            {
                iObjNew = Cba_ObjAlloc( pNew, CBA_OBJ_BI,  -1 );
                iObjNew = Cba_ObjAlloc( pNew, CBA_BOX_BUF, -1 ); // buffer
                iObjNew = Cba_ObjAlloc( pNew, CBA_OBJ_BO,  -1 );
                Cba_ObjSetCopy( p, iTerm, iObjNew );
            }
        }
    // duplicate user modules and connect objects
    Cba_NtkForEachBox( p, iObj )
        if ( Cba_ObjIsBoxPrim( p, iObj ) )
        {
            Cba_BoxForEachBi( p, iObj, iTerm, i )
                Cba_ObjSetFanin( pNew, Cba_ObjCopy(p, iTerm), Cba_ObjCopy(p, Cba_ObjFanin(p, iTerm)) );
        }
        else
        {
            Vec_IntClear( vSigs );
            Cba_BoxForEachBi( p, iObj, iTerm, i )
                Vec_IntPush( vSigs, Cba_ObjCopy(p, Cba_ObjFanin(p, iTerm)) );
            Cba_NtkCollapse_rec( pNew, Cba_BoxNtk(p, iObj), vSigs );
            assert( Vec_IntSize(vSigs) == Cba_BoxBoNum(p, iObj) );
            Cba_BoxForEachBo( p, iObj, iTerm, i )
                Cba_ObjSetFanin( pNew, Cba_ObjCopy(p, iTerm)-2, Vec_IntEntry(vSigs, i) );
        }
    // collect POs
    Vec_IntClear( vSigs );
    Cba_NtkForEachPo( p, iObj, i )
        Vec_IntPush( vSigs, Cba_ObjCopy(p, Cba_ObjFanin(p, iObj)) );
}
Cba_Man_t * Cba_ManCollapse( Cba_Man_t * p )
{
    int i, iObj;
    Vec_Int_t * vSigs = Vec_IntAlloc( 1000 );
    Cba_Man_t * pNew = Cba_ManStart( p, 1 );
    Cba_Ntk_t * pRoot = Cba_ManRoot( p );
    Cba_Ntk_t * pRootNew = Cba_ManRoot( pNew );
    Cba_NtkAlloc( pRootNew, Cba_NtkNameId(pRoot), Cba_NtkPiNum(pRoot), Cba_NtkPoNum(pRoot), Cba_ManClpObjNum(p) );
    Cba_NtkForEachPi( pRoot, iObj, i )
        Vec_IntPush( vSigs, Cba_ObjAlloc(pRootNew, CBA_OBJ_PI, -1) );
    Cba_NtkCollapse_rec( pRootNew, pRoot, vSigs );
    assert( Vec_IntSize(vSigs) == Cba_NtkPoNum(pRoot) );
    Cba_NtkForEachPo( pRoot, iObj, i )
        Cba_ObjAlloc( pRootNew, CBA_OBJ_PO, Vec_IntEntry(vSigs, i) );
    assert( Cba_NtkObjNum(pRootNew) == Cba_NtkObjNumAlloc(pRootNew) );
    Vec_IntFree( vSigs );
    // transfer PI/PO names
    if ( Cba_NtkHasNames(pRoot) )
    {
        Cba_NtkStartNames( pRootNew );
        Cba_NtkForEachPi( pRoot, iObj, i )
            Cba_ObjSetName( pRootNew, Cba_NtkPi(pRootNew, i), Cba_ObjNameId(pRoot, iObj) );
        Cba_NtkForEachPoDriver( pRoot, iObj, i )
            if ( !Cba_ObjIsPi(pRoot, iObj) )
                Cba_ObjSetName( pRootNew, Cba_ObjCopy(pRoot, iObj), Cba_ObjNameId(pRoot, iObj) );
    }
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

