/**CFile****************************************************************

  FileName    [cbaPrs.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Parser declarations.]

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

#include "aig/gia/gia.h"
#include "misc/util/utilNam.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START 

// parser name types
typedef enum { 
    CBA_PRS_NAME = 0,        // 0:  name/variable
    CBA_PRS_SLICE,           // 1:  slice
    CBA_PRS_CONST,           // 2:  constant
    CBA_PRS_CONCAT,          // 3:  concatentation
} Prs_ManType_t; 

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// network
typedef struct Prs_Ntk_t_ Prs_Ntk_t;
struct Prs_Ntk_t_
{
    // general info
    int          iModuleName;
    unsigned     fMapped : 1;
    unsigned     fSlices : 1;
    unsigned     fHasC0s : 1;
    unsigned     fHasC1s : 1;
    unsigned     fHasCXs : 1;
    unsigned     fHasCZs : 1;
    Abc_Nam_t *  pStrs;
    // interface
    Vec_Int_t    vOrder;     // order of signals
    // signal names
    Vec_Int_t    vInouts;    // inouts 
    Vec_Int_t    vInputs;    // inputs 
    Vec_Int_t    vOutputs;   // outputs
    Vec_Int_t    vWires;     // wires  
    // signal ranges
    Vec_Int_t    vInoutsR;   // inouts 
    Vec_Int_t    vInputsR;   // inputs 
    Vec_Int_t    vOutputsR;  // outputs
    Vec_Int_t    vWiresR;    // wires  
    // slices/concatenations/objects
    Vec_Int_t    vSlices;    // NameId + RangeId
    Vec_Int_t    vConcats;   // array of NameId/SliceId/ConstId
    Vec_Int_t    vBoxes;     // ModuleId + InstId + array of pairs {FormNameId, ActSignalId(NameId/SliceId/ConstId/ConcatId)}
    Vec_Int_t    vObjs;      // box handles
};

// parser
typedef struct Prs_Man_t_ Prs_Man_t;
struct Prs_Man_t_
{
    // input data
    char *       pName;       // file name
    char *       pBuffer;     // file contents
    char *       pLimit;      // end of file
    char *       pCur;        // current position
    Abc_Nam_t *  pStrs;       // string manager
    Prs_Ntk_t *  pNtk;        // current network
    Vec_Ptr_t *  vNtks;       // input networks
    // temporary data
    Vec_Str_t    vCover;      // one SOP cover
    Vec_Int_t    vTemp;       // array of tokens
    Vec_Int_t    vTemp2;      // array of tokens
    // statistics
    Vec_Int_t    vKnown;
    Vec_Int_t    vFailed;
    Vec_Int_t    vSucceeded;
    // error handling
    int          fUsingTemp2; // vTemp2 is in use
    char ErrorStr[1000];      // error
};

static inline Prs_Ntk_t * Prs_ManNtk( Vec_Ptr_t * vPrs, int i )        { return i >= 0 && i < Vec_PtrSize(vPrs) ? (Prs_Ntk_t *)Vec_PtrEntry(vPrs, i) : NULL; }
static inline Prs_Ntk_t * Prs_ManRoot( Vec_Ptr_t * vPrs )              { return Prs_ManNtk(vPrs, 0);                             }
static inline Abc_Nam_t * Prs_ManNameMan( Vec_Ptr_t * vPrs )           { return Prs_ManRoot(vPrs)->pStrs;                        }

static inline int         Prs_NtkId( Prs_Ntk_t * p )                   { return p->iModuleName;                                  }
static inline int         Prs_NtkPioNum( Prs_Ntk_t * p )               { return Vec_IntSize(&p->vInouts);                        }
static inline int         Prs_NtkPiNum( Prs_Ntk_t * p )                { return Vec_IntSize(&p->vInputs);                        }
static inline int         Prs_NtkPoNum( Prs_Ntk_t * p )                { return Vec_IntSize(&p->vOutputs);                       }
static inline int         Prs_NtkBoxNum( Prs_Ntk_t * p )               { return Vec_IntSize(&p->vObjs);                          }
static inline int         Prs_NtkObjNum( Prs_Ntk_t * p )               { return Prs_NtkPioNum(p) + Prs_NtkPiNum(p) + Prs_NtkPoNum(p) + Prs_NtkBoxNum(p); }
static inline char *      Prs_NtkStr( Prs_Ntk_t * p, int h )           { return Abc_NamStr(p->pStrs, h);                         }
static inline char *      Prs_NtkName( Prs_Ntk_t * p )                 { return Prs_NtkStr(p, Prs_NtkId(p));                     }
static inline int         Prs_NtkSigName( Prs_Ntk_t * p, int i )       { if (!p->fSlices) return i; assert(Abc_Lit2Att2(i) == CBA_PRS_NAME); return Abc_Lit2Var2(i); }

static inline int         Prs_SliceName( Prs_Ntk_t * p, int h )        { return Vec_IntEntry(&p->vSlices, h);                    }
static inline int         Prs_SliceRange( Prs_Ntk_t * p, int h )       { return Vec_IntEntry(&p->vSlices, h+1);                  }

static inline int         Prs_CatSize( Prs_Ntk_t * p, int h )          { return Vec_IntEntry(&p->vConcats, h);                   }
static inline int *       Prs_CatArray( Prs_Ntk_t * p, int h )         { return Vec_IntEntryP(&p->vConcats, h+1);                }
static inline Vec_Int_t * Prs_CatSignals( Prs_Ntk_t * p, int h )       { static Vec_Int_t V; V.nSize = V.nCap = Prs_CatSize(p, h); V.pArray = Prs_CatArray(p, h); return &V; }

static inline int         Prs_BoxHand( Prs_Ntk_t * p, int i )          { return Vec_IntEntry(&p->vObjs, i);                      }
static inline int         Prs_BoxSize( Prs_Ntk_t * p, int i )          { return Vec_IntEntry(&p->vBoxes, Prs_BoxHand(p, i))-2;   }
static inline int         Prs_BoxIONum( Prs_Ntk_t * p, int i )         { return Prs_BoxSize(p, i) / 2;                           }
static inline int         Prs_BoxNtk( Prs_Ntk_t * p, int i )           { return Vec_IntEntry(&p->vBoxes, Prs_BoxHand(p, i)+1);   }
static inline void        Prs_BoxSetNtk( Prs_Ntk_t * p, int i, int m ) { Vec_IntWriteEntry(&p->vBoxes, Prs_BoxHand(p, i)+1, m);  }
static inline int         Prs_BoxName( Prs_Ntk_t * p, int i )          { return Vec_IntEntry(&p->vBoxes, Prs_BoxHand(p, i)+2);   }
static inline int         Prs_BoxIsNode( Prs_Ntk_t * p, int i )        { return!Vec_IntEntry(&p->vBoxes, Prs_BoxHand(p, i)+3);   } // no formal names
static inline int *       Prs_BoxArray( Prs_Ntk_t * p, int i )         { return Vec_IntEntryP(&p->vBoxes, Prs_BoxHand(p, i)+3);  }
static inline Vec_Int_t * Prs_BoxSignals( Prs_Ntk_t * p, int i )       { static Vec_Int_t V; V.nSize = V.nCap = Prs_BoxSize(p, i); V.pArray = Prs_BoxArray(p, i); return &V; }

#define Prs_ManForEachNameVec( vVec, p, pName, i )   \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pName) = Abc_NamStr(p->pStrs, Vec_IntEntry(vVec,i))); i++ )

#define Prs_NtkForEachPio( p, NameId, i )            \
    for ( i = 0; i < Prs_NtkPioNum(p) && ((NameId) = Vec_IntEntry(&p->vInouts, i)); i++ )
#define Prs_NtkForEachPi( p, NameId, i )             \
    for ( i = 0; i < Prs_NtkPiNum(p) && ((NameId) = Vec_IntEntry(&p->vInputs, i)); i++ )
#define Prs_NtkForEachPo( p, NameId, i )             \
    for ( i = 0; i < Prs_NtkPoNum(p) && ((NameId) = Vec_IntEntry(&p->vOutputs, i)); i++ )
#define Prs_NtkForEachBox( p, vVec, i )              \
    for ( i = 0; i < Prs_NtkBoxNum(p) && ((vVec) = Prs_BoxSignals(p, i)); i++ )

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

// create error message
static inline int Prs_ManErrorSet( Prs_Man_t * p, char * pError, int Value )
{
    assert( !p->ErrorStr[0] );
    sprintf( p->ErrorStr, "%s", pError );
    return Value;
}
// clear error message
static inline void Prs_ManErrorClear( Prs_Man_t * p )
{
    p->ErrorStr[0] = '\0';
}
// print error message
static inline int Prs_ManErrorPrint( Prs_Man_t * p )
{
    char * pThis; int iLine = 0;
    if ( !p->ErrorStr[0] ) return 1;
    for ( pThis = p->pBuffer; pThis < p->pCur; pThis++ )
        iLine += (int)(*pThis == '\n');
    printf( "Line %d: %s\n", iLine, p->ErrorStr );
    return 0;
}

// parsing network
static inline void Prs_ManInitializeNtk( Prs_Man_t * p, int iName, int fSlices )
{
    assert( p->pNtk == NULL );
    p->pNtk = ABC_CALLOC( Prs_Ntk_t, 1 );
    p->pNtk->iModuleName = iName;
    p->pNtk->fSlices = fSlices;
    p->pNtk->pStrs = Abc_NamRef( p->pStrs );
    Vec_PtrPush( p->vNtks, p->pNtk );
}
static inline void Prs_ManFinalizeNtk( Prs_Man_t * p )
{
    assert( p->pNtk != NULL );
    p->pNtk = NULL;
}

// parsing slice/concatentation/box
static inline int Prs_NtkAddSlice( Prs_Ntk_t * p, int Name, int Range )
{
    int Value = Vec_IntSize(&p->vSlices);
    Vec_IntPushTwo( &p->vSlices, Name, Range );
    return Value;
}
static inline int Prs_NtkAddConcat( Prs_Ntk_t * p, Vec_Int_t * vTemp )
{
    int Value;
    if ( !(Vec_IntSize(&p->vConcats) & 1) )
        Vec_IntPush(&p->vConcats, -1);
    Value = Vec_IntSize(&p->vConcats);
    assert( Value & 1 );
    Vec_IntPush( &p->vConcats, Vec_IntSize(vTemp) );
    Vec_IntAppend( &p->vConcats, vTemp );
    return Value;
}
static inline void Prs_NtkAddBox( Prs_Ntk_t * p, int ModName, int InstName, Vec_Int_t * vTemp )
{
    int Value;
    assert( Vec_IntSize(vTemp) % 2 == 0 );
    if ( !(Vec_IntSize(&p->vBoxes) & 1) )
        Vec_IntPush(&p->vBoxes, -1);
    Value = Vec_IntSize(&p->vBoxes);
    assert( Value & 1 );
    Vec_IntPush( &p->vObjs, Value );
    // create entry
    Vec_IntPush( &p->vBoxes, Vec_IntSize(vTemp)+2 );
    Vec_IntPush( &p->vBoxes, ModName );
    Vec_IntPush( &p->vBoxes, InstName );
    Vec_IntAppend( &p->vBoxes, vTemp );
}


static inline char * Prs_ManLoadFile( char * pFileName, char ** ppLimit )
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
    *ppLimit = pBuffer + nFileSize + 3;
    return pBuffer;
}
static inline Prs_Man_t * Prs_ManAlloc( char * pFileName )
{
    Prs_Man_t * p;
    char * pBuffer, * pLimit;
    pBuffer = Prs_ManLoadFile( pFileName, &pLimit );
    if ( pBuffer == NULL )
        return NULL;
    p = ABC_CALLOC( Prs_Man_t, 1 );
    p->pName   = pFileName;
    p->pBuffer = pBuffer;
    p->pLimit  = pLimit;
    p->pCur    = pBuffer;
    p->pStrs   = Abc_NamStart( 1000, 24 );
    p->vNtks   = Vec_PtrAlloc( 100 );
    return p;
}

static inline void Prs_NtkFree( Prs_Ntk_t * p )
{
    if ( p->pStrs )
        Abc_NamDeref( p->pStrs );
    Vec_IntErase( &p->vOrder );
    Vec_IntErase( &p->vInouts );
    Vec_IntErase( &p->vInputs );
    Vec_IntErase( &p->vOutputs );
    Vec_IntErase( &p->vWires );
    Vec_IntErase( &p->vInoutsR );
    Vec_IntErase( &p->vInputsR );
    Vec_IntErase( &p->vOutputsR );
    Vec_IntErase( &p->vWiresR );
    Vec_IntErase( &p->vSlices );
    Vec_IntErase( &p->vConcats );
    Vec_IntErase( &p->vBoxes );
    Vec_IntErase( &p->vObjs );
    ABC_FREE( p );
}

static inline void Prs_ManFree( Prs_Man_t * p )
{
    if ( p->pStrs )
        Abc_NamDeref( p->pStrs );
    if ( p->vNtks )
        Prs_ManVecFree( p->vNtks );
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

static inline int Prs_NtkMemory( Prs_Ntk_t * p )
{
    int nMem = sizeof(Prs_Ntk_t);
    nMem += Vec_IntMemory( &p->vOrder );
    nMem += Vec_IntMemory( &p->vInouts );
    nMem += Vec_IntMemory( &p->vInputs );
    nMem += Vec_IntMemory( &p->vOutputs );
    nMem += Vec_IntMemory( &p->vWires );
    nMem += Vec_IntMemory( &p->vInoutsR );
    nMem += Vec_IntMemory( &p->vInputsR );
    nMem += Vec_IntMemory( &p->vOutputsR );
    nMem += Vec_IntMemory( &p->vWiresR );
    nMem += Vec_IntMemory( &p->vSlices );
    nMem += Vec_IntMemory( &p->vBoxes );
    nMem += Vec_IntMemory( &p->vConcats );
    return nMem;
}
static inline int Prs_ManMemory( Vec_Ptr_t * vPrs )
{
    Prs_Ntk_t * pNtk; int i;
    int nMem = Vec_PtrMemory(vPrs);
    Vec_PtrForEachEntry( Prs_Ntk_t *, vPrs, pNtk, i )
        nMem += Prs_NtkMemory( pNtk );
    nMem += Abc_NamMemUsed(Prs_ManNameMan(vPrs));
    return nMem;
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

