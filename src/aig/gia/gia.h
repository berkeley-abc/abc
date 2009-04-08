/**CFile****************************************************************

  FileName    [gia.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: gia.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __GIA_H__
#define __GIA_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "vec.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

#ifdef __cplusplus
extern "C" {
#endif

#define GIA_NONE 0x1FFFFFFF
#define GIA_VOID 0x0FFFFFFF

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Gia_Rpr_t_ Gia_Rpr_t;
struct Gia_Rpr_t_
{
    unsigned       iRepr   : 28;  // representative node
    unsigned       fProved :  1;  // marks the proved equivalence
    unsigned       fFailed :  1;  // marks the failed equivalence
    unsigned       fColorA :  1;  // marks cone of A
    unsigned       fColorB :  1;  // marks cone of B
};

typedef struct Gia_Plc_t_ Gia_Plc_t;
struct Gia_Plc_t_
{
    unsigned       fFixed  :  1;  // the placement of this object is fixed
    unsigned       xCoord  : 15;  // x-ooordinate of the placement
    unsigned       fUndef  :  1;  // the placement of this object is not assigned
    unsigned       yCoord  : 15;  // y-ooordinate of the placement
};

typedef struct Gia_Obj_t_ Gia_Obj_t;
struct Gia_Obj_t_
{
    unsigned       iDiff0 :  29;  // the diff of the first fanin
    unsigned       fCompl0:   1;  // the complemented attribute
    unsigned       fMark0 :   1;  // first user-controlled mark
    unsigned       fTerm  :   1;  // terminal node (CI/CO)

    unsigned       iDiff1 :  29;  // the diff of the second fanin
    unsigned       fCompl1:   1;  // the complemented attribute
    unsigned       fMark1 :   1;  // second user-controlled mark
    unsigned       fPhase :   1;  // value under 000 pattern

    unsigned       Value;         // application-specific value
};
// Value is currently use to store several types of information
// - pointer to the next node in the hash table during structural hashing
// - pointer to the node copy during duplication 
// - traversal ID of the node during traversal
// - reference counter of the node (will not be used in the future)

// sequential counter-example
typedef struct Gia_Cex_t_   Gia_Cex_t;
struct Gia_Cex_t_
{
    int            iPo;           // the zero-based number of PO, for which verification failed
    int            iFrame;        // the zero-based number of the time-frame, for which verificaiton failed
    int            nRegs;         // the number of registers in the miter 
    int            nPis;          // the number of primary inputs in the miter
    int            nBits;         // the number of words of bit data used
    unsigned       pData[0];      // the cex bit data (the number of bits: nRegs + (iFrame+1) * nPis)
};

// new AIG manager
typedef struct Gia_Man_t_ Gia_Man_t;
struct Gia_Man_t_
{
    char *         pName;         // name of the AIG
    int            nRegs;         // number of registers
    int            nRegsAlloc;    // number of allocated registers
    int            nObjs;         // number of objects
    int            nObjsAlloc;    // number of allocated objects
    Gia_Obj_t *    pObjs;         // the array of objects
    Vec_Int_t *    vCis;          // the vector of CIs (PIs + LOs)
    Vec_Int_t *    vCos;          // the vector of COs (POs + LIs)
    int *          pHTable;       // hash table
    int            nHTable;       // hash table size 
    int            fAddStrash;    // performs additional structural hashing
    int *          pRefs;         // the reference count
    int *          pLevels;       // levels of the nodes
    int            nLevels;       // the mamixum level
    int            nTravIds;      // the current traversal ID
    int            nFront;        // frontier size 
    int *          pReprsOld;     // representatives (for CIs and ANDs)
    Gia_Rpr_t *    pReprs;        // representatives (for CIs and ANDs)
    int *          pNexts;        // next nodes in the equivalence classes
    int *          pIso;          // pairs of structurally isomorphic nodes
    int            nTerLoop;      // the state where loop begins  
    int            nTerStates;    // the total number of ternary states
    int *          pFanData;      // the database to store fanout information
    int            nFansAlloc;    // the size of fanout representation
    int *          pMapping;      // mapping for each node
    Gia_Cex_t *    pCexComb;      // combinational counter-example
    Gia_Cex_t *    pCexSeq;       // sequential counter-example
    int *          pCopies;       // intermediate copies
    Vec_Int_t *    vFlopClasses;  // classes of flops for retiming/merging/etc
    unsigned char* pSwitching;    // switching activity for each object
    Gia_Plc_t *    pPlacement;    // placement of the objects
};



typedef struct Emb_Par_t_ Emb_Par_t;
struct Emb_Par_t_
{
    int            nDims;         // the number of dimension
    int            nSols;         // the number of solutions (typically, 2)
    int            nIters;        // the number of iterations of FORCE
    int            fRefine;       // use refinement by FORCE
    int            fCluster;      // use clustered representation 
    int            fDump;         // dump Gnuplot file
    int            fDumpLarge;    // dump Gnuplot file for large benchmarks
    int            fShowImage;    // shows image if Gnuplot is installed
    int            fVerbose;      // verbose flag  
};


// frames parameters
typedef struct Gia_ParFra_t_ Gia_ParFra_t;
struct Gia_ParFra_t_
{
    int            nFrames;       // the number of frames to unroll
    int            fInit;         // initialize the timeframes
    int            fVerbose;      // enables verbose output
};



// simulation parameters
typedef struct Gia_ParSim_t_ Gia_ParSim_t;
struct Gia_ParSim_t_
{
    // user-controlled parameters
    int            nWords;        // the number of machine words
    int            nIters;        // the number of timeframes
    int            TimeLimit;     // time limit in seconds
    int            fCheckMiter;   // check if miter outputs are non-zero
    int            fVerbose;      // enables verbose output
};

extern void Gia_ManSimSetDefaultParams( Gia_ParSim_t * p );
extern int Gia_ManSimSimulate( Gia_Man_t * pAig, Gia_ParSim_t * pPars );


static inline int          Gia_IntAbs( int n )                    { return (n < 0)? -n : n;                                }
static inline int          Gia_Float2Int( float Val )             { return *((int *)&Val);                                 }
static inline float        Gia_Int2Float( int Num )               { return *((float *)&Num);                               }
static inline int          Gia_Base2Log( unsigned n )             { int r; assert( n >= 0 ); if ( n < 2 ) return n; for ( r = 0, n--; n; n >>= 1, r++ ); return r; }
static inline int          Gia_Base10Log( unsigned n )            { int r; assert( n >= 0 ); if ( n < 2 ) return n; for ( r = 0, n--; n; n /= 10, r++ ); return r; }
static inline char *       Gia_UtilStrsav( char * s )             { return s ? strcpy(ABC_ALLOC(char, strlen(s)+1), s) : NULL; }
static inline int          Gia_BitWordNum( int nBits )            { return (nBits>>5) + ((nBits&31) > 0);                  }
static inline int          Gia_TruthWordNum( int nVars )          { return nVars <= 5 ? 1 : (1 << (nVars - 5));            }
static inline int          Gia_InfoHasBit( unsigned * p, int i )  { return (p[(i)>>5] & (1<<((i) & 31))) > 0;              }
static inline void         Gia_InfoSetBit( unsigned * p, int i )  { p[(i)>>5] |= (1<<((i) & 31));                          }
static inline void         Gia_InfoXorBit( unsigned * p, int i )  { p[(i)>>5] ^= (1<<((i) & 31));                          }
static inline unsigned     Gia_InfoMask( int nVar )               { return (~(unsigned)0) >> (32-nVar);                    }
static inline unsigned     Gia_ObjCutSign( unsigned ObjId )       { return (1 << (ObjId & 31));                            }
static inline int          Gia_WordCountOnes( unsigned uWord )
{
    uWord = (uWord & 0x55555555) + ((uWord>>1) & 0x55555555);
    uWord = (uWord & 0x33333333) + ((uWord>>2) & 0x33333333);
    uWord = (uWord & 0x0F0F0F0F) + ((uWord>>4) & 0x0F0F0F0F);
    uWord = (uWord & 0x00FF00FF) + ((uWord>>8) & 0x00FF00FF);
    return  (uWord & 0x0000FFFF) + (uWord>>16);
}
static inline int          Gia_WordFindFirstBit( unsigned uWord )
{
    int i;
    for ( i = 0; i < 32; i++ )
        if ( uWord & (1 << i) )
            return i;
    return -1;
}


static inline int          Gia_Var2Lit( int Var, int fCompl )  { return Var + Var + fCompl; }
static inline int          Gia_Lit2Var( int Lit )              { return Lit >> 1;           }
static inline int          Gia_LitIsCompl( int Lit )           { return Lit & 1;            }
static inline int          Gia_LitNot( int Lit )               { return Lit ^ 1;            }
static inline int          Gia_LitNotCond( int Lit, int c )    { return Lit ^ (int)(c > 0); }
static inline int          Gia_LitRegular( int Lit )           { return Lit & ~01;          }

static inline Gia_Obj_t *  Gia_Regular( Gia_Obj_t * p )        { return (Gia_Obj_t *)((ABC_PTRUINT_T)(p) & ~01); }
static inline Gia_Obj_t *  Gia_Not( Gia_Obj_t * p )            { return (Gia_Obj_t *)((ABC_PTRUINT_T)(p) ^  01); }
static inline Gia_Obj_t *  Gia_NotCond( Gia_Obj_t * p, int c ) { return (Gia_Obj_t *)((ABC_PTRUINT_T)(p) ^ (c)); }
static inline int          Gia_IsComplement( Gia_Obj_t * p )   { return (int)((ABC_PTRUINT_T)(p) & 01);          }

static inline int          Gia_ManCiNum( Gia_Man_t * p )       { return Vec_IntSize(p->vCis);  }
static inline int          Gia_ManCoNum( Gia_Man_t * p )       { return Vec_IntSize(p->vCos);  }
static inline int          Gia_ManPiNum( Gia_Man_t * p )       { return Vec_IntSize(p->vCis) - p->nRegs;  }
static inline int          Gia_ManPoNum( Gia_Man_t * p )       { return Vec_IntSize(p->vCos) - p->nRegs;  }
static inline int          Gia_ManRegNum( Gia_Man_t * p )      { return p->nRegs;              }
static inline int          Gia_ManObjNum( Gia_Man_t * p )      { return p->nObjs;              }
static inline int          Gia_ManAndNum( Gia_Man_t * p )      { return p->nObjs - Vec_IntSize(p->vCis) - Vec_IntSize(p->vCos) - 1;  }
static inline int          Gia_ManCandNum( Gia_Man_t * p )     { return Gia_ManCiNum(p) + Gia_ManAndNum(p);                          }

static inline Gia_Obj_t *  Gia_ManConst0( Gia_Man_t * p )      { return p->pObjs;                                               }
static inline Gia_Obj_t *  Gia_ManConst1( Gia_Man_t * p )      { return Gia_Not(Gia_ManConst0(p));                              }
static inline Gia_Obj_t *  Gia_ManObj( Gia_Man_t * p, int v )  { assert( v < p->nObjs ); return p->pObjs + v;                   }
static inline Gia_Obj_t *  Gia_ManCi( Gia_Man_t * p, int v )   { return Gia_ManObj( p, Vec_IntEntry(p->vCis,v) );  }
static inline Gia_Obj_t *  Gia_ManCo( Gia_Man_t * p, int v )   { return Gia_ManObj( p, Vec_IntEntry(p->vCos,v) );  }
static inline Gia_Obj_t *  Gia_ManPi( Gia_Man_t * p, int v )   { assert( v < Gia_ManPiNum(p) );  return Gia_ManCi( p, v );      }
static inline Gia_Obj_t *  Gia_ManPo( Gia_Man_t * p, int v )   { assert( v < Gia_ManPoNum(p) );  return Gia_ManCo( p, v );      }
static inline Gia_Obj_t *  Gia_ManRo( Gia_Man_t * p, int v )   { assert( v < Gia_ManRegNum(p) ); return Gia_ManCi( p, Gia_ManRegNum(p)+v );      }
static inline Gia_Obj_t *  Gia_ManRi( Gia_Man_t * p, int v )   { assert( v < Gia_ManRegNum(p) ); return Gia_ManCo( p, Gia_ManRegNum(p)+v );      }

static inline int          Gia_ObjIsTerm( Gia_Obj_t * pObj )                   { return pObj->fTerm;                             } 
static inline int          Gia_ObjIsAndOrConst0( Gia_Obj_t * pObj )            { return!pObj->fTerm;                             } 
static inline int          Gia_ObjIsCi( Gia_Obj_t * pObj )                     { return pObj->fTerm && pObj->iDiff0 == GIA_NONE; } 
static inline int          Gia_ObjIsCo( Gia_Obj_t * pObj )                     { return pObj->fTerm && pObj->iDiff0 != GIA_NONE; } 
static inline int          Gia_ObjIsAnd( Gia_Obj_t * pObj )                    { return!pObj->fTerm && pObj->iDiff0 != GIA_NONE; } 
static inline int          Gia_ObjIsCand( Gia_Obj_t * pObj )                   { return Gia_ObjIsAnd(pObj) || Gia_ObjIsCi(pObj); } 
static inline int          Gia_ObjIsConst0( Gia_Obj_t * pObj )                 { return pObj->iDiff0 == GIA_NONE && pObj->iDiff1 == GIA_NONE; } 
static inline int          Gia_ManObjIsConst0( Gia_Man_t * p, Gia_Obj_t * pObj){ return pObj == p->pObjs;                        } 

static inline int          Gia_ObjId( Gia_Man_t * p, Gia_Obj_t * pObj )        { assert( p->pObjs <= pObj && pObj < p->pObjs + p->nObjs ); return pObj - p->pObjs; }
static inline int          Gia_ObjCioId( Gia_Obj_t * pObj )                    { assert( Gia_ObjIsTerm(pObj) ); return pObj->iDiff1;         }
static inline void         Gia_ObjSetCioId( Gia_Obj_t * pObj, int v )          { assert( Gia_ObjIsTerm(pObj) ); pObj->iDiff1 = v;            }
static inline int          Gia_ObjPhase( Gia_Obj_t * pObj )                    { return pObj->fPhase;                                        }
static inline int          Gia_ObjPhaseReal( Gia_Obj_t * pObj )                { return Gia_Regular(pObj)->fPhase ^ Gia_IsComplement(pObj);  }

static inline int          Gia_ObjIsPi( Gia_Man_t * p, Gia_Obj_t * pObj )      { return Gia_ObjIsCi(pObj) && Gia_ObjCioId(pObj) < Gia_ManPiNum(p);   } 
static inline int          Gia_ObjIsPo( Gia_Man_t * p, Gia_Obj_t * pObj )      { return Gia_ObjIsCo(pObj) && Gia_ObjCioId(pObj) < Gia_ManPoNum(p);   } 
static inline int          Gia_ObjIsRo( Gia_Man_t * p, Gia_Obj_t * pObj )      { return Gia_ObjIsCi(pObj) && Gia_ObjCioId(pObj) >= Gia_ManPiNum(p);  } 
static inline int          Gia_ObjIsRi( Gia_Man_t * p, Gia_Obj_t * pObj )      { return Gia_ObjIsCo(pObj) && Gia_ObjCioId(pObj) >= Gia_ManPoNum(p);  } 

static inline Gia_Obj_t *  Gia_ObjRoToRi( Gia_Man_t * p, Gia_Obj_t * pObj )    { assert( Gia_ObjIsRo(p, pObj) ); return Gia_ManCo(p, Gia_ManCoNum(p) - Gia_ManCiNum(p) + Gia_ObjCioId(pObj)); } 
static inline Gia_Obj_t *  Gia_ObjRiToRo( Gia_Man_t * p, Gia_Obj_t * pObj )    { assert( Gia_ObjIsRi(p, pObj) ); return Gia_ManCi(p, Gia_ManCiNum(p) - Gia_ManCoNum(p) + Gia_ObjCioId(pObj)); } 

static inline int          Gia_ObjDiff0( Gia_Obj_t * pObj )                    { return pObj->iDiff0;         }
static inline int          Gia_ObjDiff1( Gia_Obj_t * pObj )                    { return pObj->iDiff1;         }
static inline int          Gia_ObjFaninC0( Gia_Obj_t * pObj )                  { return pObj->fCompl0;        }
static inline int          Gia_ObjFaninC1( Gia_Obj_t * pObj )                  { return pObj->fCompl1;        }
static inline Gia_Obj_t *  Gia_ObjFanin0( Gia_Obj_t * pObj )                   { return pObj - pObj->iDiff0;  }
static inline Gia_Obj_t *  Gia_ObjFanin1( Gia_Obj_t * pObj )                   { return pObj - pObj->iDiff1;  }
static inline Gia_Obj_t *  Gia_ObjChild0( Gia_Obj_t * pObj )                   { return Gia_NotCond( Gia_ObjFanin0(pObj), Gia_ObjFaninC0(pObj) ); }
static inline Gia_Obj_t *  Gia_ObjChild1( Gia_Obj_t * pObj )                   { return Gia_NotCond( Gia_ObjFanin1(pObj), Gia_ObjFaninC1(pObj) ); }
static inline int          Gia_ObjFaninId0( Gia_Obj_t * pObj, int ObjId )      { return ObjId - pObj->iDiff0;    }
static inline int          Gia_ObjFaninId1( Gia_Obj_t * pObj, int ObjId )      { return ObjId - pObj->iDiff1;    }
static inline int          Gia_ObjFaninId0p( Gia_Man_t * p, Gia_Obj_t * pObj ) { return Gia_ObjFaninId0( pObj, Gia_ObjId(p, pObj) );              }
static inline int          Gia_ObjFaninId1p( Gia_Man_t * p, Gia_Obj_t * pObj ) { return Gia_ObjFaninId1( pObj, Gia_ObjId(p, pObj) );              }
static inline int          Gia_ObjFaninLit0( Gia_Obj_t * pObj, int ObjId )     { return Gia_Var2Lit( Gia_ObjFaninId0(pObj, ObjId), Gia_ObjFaninC0(pObj) ); }
static inline int          Gia_ObjFaninLit1( Gia_Obj_t * pObj, int ObjId )     { return Gia_Var2Lit( Gia_ObjFaninId1(pObj, ObjId), Gia_ObjFaninC1(pObj) ); }
static inline int          Gia_ObjFaninLit0p( Gia_Man_t * p, Gia_Obj_t * pObj) { return Gia_Var2Lit( Gia_ObjFaninId0p(p, pObj), Gia_ObjFaninC0(pObj) );    }
static inline int          Gia_ObjFaninLit1p( Gia_Man_t * p, Gia_Obj_t * pObj) { return Gia_Var2Lit( Gia_ObjFaninId1p(p, pObj), Gia_ObjFaninC1(pObj) );    }
static inline void         Gia_ObjFlipFaninC0( Gia_Obj_t * pObj )              { assert( Gia_ObjIsCo(pObj) ); pObj->fCompl0 ^= 1;          }
static inline int          Gia_ObjWhatFanin( Gia_Obj_t * pObj, Gia_Obj_t * pFanin )  { return Gia_ObjFanin0(pObj) == pFanin ? 0 : (Gia_ObjFanin1(pObj) == pFanin ? 1 : -1); }

static inline int          Gia_ObjFanin0Copy( Gia_Obj_t * pObj )               { return Gia_LitNotCond( Gia_ObjFanin0(pObj)->Value, Gia_ObjFaninC0(pObj) );     }
static inline int          Gia_ObjFanin1Copy( Gia_Obj_t * pObj )               { return Gia_LitNotCond( Gia_ObjFanin1(pObj)->Value, Gia_ObjFaninC1(pObj) );     }

static inline int          Gia_ObjCopyF( Gia_Man_t * p, int f, Gia_Obj_t * pObj )               { return p->pCopies[Gia_ManObjNum(p) * f + Gia_ObjId(p,pObj)];  }
static inline void         Gia_ObjSetCopyF( Gia_Man_t * p, int f, Gia_Obj_t * pObj, int iLit )  { p->pCopies[Gia_ManObjNum(p) * f + Gia_ObjId(p,pObj)] = iLit;  }

static inline int          Gia_ObjFanin0CopyF( Gia_Man_t * p, int f, Gia_Obj_t * pObj )         { return Gia_LitNotCond(Gia_ObjCopyF(p, f, Gia_ObjFanin0(pObj)), Gia_ObjFaninC0(pObj));  }
static inline int          Gia_ObjFanin1CopyF( Gia_Man_t * p, int f, Gia_Obj_t * pObj )         { return Gia_LitNotCond(Gia_ObjCopyF(p, f, Gia_ObjFanin1(pObj)), Gia_ObjFaninC1(pObj));  }

static inline Gia_Obj_t *  Gia_ObjFromLit( Gia_Man_t * p, int iLit )           { return Gia_NotCond( Gia_ManObj(p, Gia_Lit2Var(iLit)), Gia_LitIsCompl(iLit) );  }
static inline int          Gia_ObjToLit( Gia_Man_t * p, Gia_Obj_t * pObj )     { return Gia_Var2Lit( Gia_ObjId(p, Gia_Regular(pObj)), Gia_IsComplement(pObj) ); }
static inline int          Gia_ObjPhaseRealLit( Gia_Man_t * p, int iLit )      { return Gia_ObjPhaseReal( Gia_ObjFromLit(p, iLit) );        }

static inline int          Gia_ObjValue( Gia_Obj_t * pObj )                    { return pObj->Value;                                        }
static inline int          Gia_ObjLevel( Gia_Man_t * p, Gia_Obj_t * pObj )     { assert(p->pLevels);return p->pLevels[Gia_ObjId(p, pObj)];  }

static inline int          Gia_ObjRefs( Gia_Man_t * p, Gia_Obj_t * pObj )      { assert( p->pRefs); return p->pRefs[Gia_ObjId(p, pObj)];    }
static inline int          Gia_ObjRefInc( Gia_Man_t * p, Gia_Obj_t * pObj )    { assert( p->pRefs); return p->pRefs[Gia_ObjId(p, pObj)]++;  }
static inline int          Gia_ObjRefDec( Gia_Man_t * p, Gia_Obj_t * pObj )    { assert( p->pRefs); return --p->pRefs[Gia_ObjId(p, pObj)];  }
static inline void         Gia_ObjRefFanin0Inc(Gia_Man_t * p, Gia_Obj_t * pObj){ assert( p->pRefs); Gia_ObjRefInc(p, Gia_ObjFanin0(pObj));  }
static inline void         Gia_ObjRefFanin1Inc(Gia_Man_t * p, Gia_Obj_t * pObj){ assert( p->pRefs); Gia_ObjRefInc(p, Gia_ObjFanin1(pObj));  }
static inline void         Gia_ObjRefFanin0Dec(Gia_Man_t * p, Gia_Obj_t * pObj){ assert( p->pRefs); Gia_ObjRefDec(p, Gia_ObjFanin0(pObj));  }
static inline void         Gia_ObjRefFanin1Dec(Gia_Man_t * p, Gia_Obj_t * pObj){ assert( p->pRefs); Gia_ObjRefDec(p, Gia_ObjFanin1(pObj));  }

static inline void         Gia_ManResetTravId( Gia_Man_t * p )                             { extern void Gia_ManCleanValue( Gia_Man_t * p ); Gia_ManCleanValue( p ); p->nTravIds = 1;  }
static inline void         Gia_ManIncrementTravId( Gia_Man_t * p )                         { p->nTravIds++;                                 }
static inline void         Gia_ObjSetTravId( Gia_Obj_t * pObj, int TravId )                { pObj->Value = TravId;                          }
static inline void         Gia_ObjSetTravIdCurrent( Gia_Man_t * p, Gia_Obj_t * pObj )      { pObj->Value = p->nTravIds;                     }
static inline void         Gia_ObjSetTravIdPrevious( Gia_Man_t * p, Gia_Obj_t * pObj )     { pObj->Value = p->nTravIds - 1;                 }
static inline int          Gia_ObjIsTravIdCurrent( Gia_Man_t * p, Gia_Obj_t * pObj )       { return ((int)pObj->Value == p->nTravIds);      }
static inline int          Gia_ObjIsTravIdPrevious( Gia_Man_t * p, Gia_Obj_t * pObj )      { return ((int)pObj->Value == p->nTravIds - 1);  }

// AIG construction
extern void Gia_ObjAddFanout( Gia_Man_t * p, Gia_Obj_t * pObj, Gia_Obj_t * pFanout );
static inline Gia_Obj_t * Gia_ManAppendObj( Gia_Man_t * p )  
{ 
    if ( p->nObjs == p->nObjsAlloc )
    {
//        printf("Reallocing %d.\n", 2 * p->nObjsAlloc );
        assert( p->nObjsAlloc > 0 );
        p->pObjs = ABC_REALLOC( Gia_Obj_t, p->pObjs, 2 * p->nObjsAlloc );
        memset( p->pObjs + p->nObjsAlloc, 0, sizeof(Gia_Obj_t) * p->nObjsAlloc );
        p->nObjsAlloc *= 2;
    }
    return Gia_ManObj( p, p->nObjs++ );
}
static inline int Gia_ManAppendCi( Gia_Man_t * p )  
{ 
    Gia_Obj_t * pObj = Gia_ManAppendObj( p );
    pObj->fTerm = 1;
    pObj->iDiff0 = GIA_NONE;
    pObj->iDiff1 = Vec_IntSize( p->vCis );
    Vec_IntPush( p->vCis, Gia_ObjId(p, pObj) );
    return Gia_ObjId( p, pObj ) << 1;
}
static inline int Gia_ManAppendAnd( Gia_Man_t * p, int iLit0, int iLit1 )  
{ 
    Gia_Obj_t * pObj = Gia_ManAppendObj( p );
    assert( iLit0 != iLit1 );
    if ( iLit0 < iLit1 )
    {
        pObj->iDiff0  = Gia_ObjId(p, pObj) - Gia_Lit2Var(iLit0);
        pObj->fCompl0 = Gia_LitIsCompl(iLit0);
        pObj->iDiff1  = Gia_ObjId(p, pObj) - Gia_Lit2Var(iLit1);
        pObj->fCompl1 = Gia_LitIsCompl(iLit1);
    }
    else
    {
        pObj->iDiff1  = Gia_ObjId(p, pObj) - Gia_Lit2Var(iLit0);
        pObj->fCompl1 = Gia_LitIsCompl(iLit0);
        pObj->iDiff0  = Gia_ObjId(p, pObj) - Gia_Lit2Var(iLit1);
        pObj->fCompl0 = Gia_LitIsCompl(iLit1);
    }
    if ( p->pFanData )
    {
        Gia_ObjAddFanout( p, Gia_ObjFanin0(pObj), pObj );
        Gia_ObjAddFanout( p, Gia_ObjFanin1(pObj), pObj );
    }
    return Gia_ObjId( p, pObj ) << 1;
}
static inline int Gia_ManAppendCo( Gia_Man_t * p, int iLit0 )  
{ 
    Gia_Obj_t * pObj = Gia_ManAppendObj( p );
    pObj->fTerm = 1;
    pObj->iDiff0  = Gia_ObjId(p, pObj) - Gia_Lit2Var(iLit0);
    pObj->fCompl0 = Gia_LitIsCompl(iLit0);
    pObj->iDiff1  = Vec_IntSize( p->vCos );
    Vec_IntPush( p->vCos, Gia_ObjId(p, pObj) );
    if ( p->pFanData )
        Gia_ObjAddFanout( p, Gia_ObjFanin0(pObj), pObj );
    return Gia_ObjId( p, pObj ) << 1;
}

#define GIA_ZER 1
#define GIA_ONE 2
#define GIA_UND 3

static inline int Gia_XsimNotCond( int Value, int fCompl )   
{ 
    if ( Value == GIA_UND )
        return GIA_UND;
    if ( Value == GIA_ZER + fCompl )
        return GIA_ZER;
    return GIA_ONE;
}
static inline int Gia_XsimAndCond( int Value0, int fCompl0, int Value1, int fCompl1 )   
{ 
    if ( Value0 == GIA_ZER + fCompl0 || Value1 == GIA_ZER + fCompl1 )
        return GIA_ZER;
    if ( Value0 == GIA_UND || Value1 == GIA_UND )
        return GIA_UND;
    return GIA_ONE;
}

static inline Gia_Obj_t * Gia_ObjReprObj( Gia_Man_t * p, int Id )            { return p->pReprs[Id].iRepr == GIA_VOID ? NULL : Gia_ManObj( p, p->pReprs[Id].iRepr );                  }
static inline int         Gia_ObjRepr( Gia_Man_t * p, int Id )               { return p->pReprs[Id].iRepr;         }
static inline void        Gia_ObjSetRepr( Gia_Man_t * p, int Id, int Num )   { p->pReprs[Id].iRepr = Num;          }

static inline int         Gia_ObjProved( Gia_Man_t * p, int Id )             { return p->pReprs[Id].fProved;       }
static inline void        Gia_ObjSetProved( Gia_Man_t * p, int Id )          { p->pReprs[Id].fProved = 1;          }
static inline void        Gia_ObjUnsetProved( Gia_Man_t * p, int Id )        { p->pReprs[Id].fProved = 0;          }

static inline int         Gia_ObjFailed( Gia_Man_t * p, int Id )             { return p->pReprs[Id].fFailed;       }
static inline void        Gia_ObjSetFailed( Gia_Man_t * p, int Id )          { p->pReprs[Id].fFailed = 1;          }

static inline int         Gia_ObjColor( Gia_Man_t * p, int Id, int c )       { return c? p->pReprs[Id].fColorB : p->pReprs[Id].fColorA;          }
static inline int         Gia_ObjColors( Gia_Man_t * p, int Id )             { return p->pReprs[Id].fColorB * 2 + p->pReprs[Id].fColorA;         }
static inline void        Gia_ObjSetColor( Gia_Man_t * p, int Id, int c )    { if (c) p->pReprs[Id].fColorB = 1; else p->pReprs[Id].fColorA = 1; }
static inline void        Gia_ObjSetColors( Gia_Man_t * p, int Id )          { p->pReprs[Id].fColorB = p->pReprs[Id].fColorA = 1;                }
static inline int         Gia_ObjVisitColor( Gia_Man_t * p, int Id, int c )  { int x; if (c) { x = p->pReprs[Id].fColorB; p->pReprs[Id].fColorB = 1; } else { x = p->pReprs[Id].fColorA; p->pReprs[Id].fColorA = 1; } return x; }
static inline int         Gia_ObjDiffColors( Gia_Man_t * p, int i, int j )   { return (p->pReprs[i].fColorA ^ p->pReprs[j].fColorA) && (p->pReprs[i].fColorB ^ p->pReprs[j].fColorB); }
static inline int         Gia_ObjDiffColors2( Gia_Man_t * p, int i, int j )  { return (p->pReprs[i].fColorA ^ p->pReprs[j].fColorA) || (p->pReprs[i].fColorB ^ p->pReprs[j].fColorB); }

static inline int         Gia_ObjNext( Gia_Man_t * p, int Id )               { return p->pNexts[Id];               }
static inline void        Gia_ObjSetNext( Gia_Man_t * p, int Id, int Num )   { p->pNexts[Id] = Num;                }

static inline int         Gia_ObjIsConst( Gia_Man_t * p, int Id )            { return Gia_ObjRepr(p, Id) == 0;                                   }
static inline int         Gia_ObjIsHead( Gia_Man_t * p, int Id )             { return Gia_ObjRepr(p, Id) == GIA_VOID && Gia_ObjNext(p, Id) > 0;  }
static inline int         Gia_ObjIsNone( Gia_Man_t * p, int Id )             { return Gia_ObjRepr(p, Id) == GIA_VOID && Gia_ObjNext(p, Id) == 0; }
static inline int         Gia_ObjIsTail( Gia_Man_t * p, int Id )             { return (Gia_ObjRepr(p, Id) > 0 && Gia_ObjRepr(p, Id) != GIA_VOID) && Gia_ObjNext(p, Id) == 0;                  }
static inline int         Gia_ObjIsClass( Gia_Man_t * p, int Id )            { return (Gia_ObjRepr(p, Id) > 0 && Gia_ObjRepr(p, Id) != GIA_VOID) || Gia_ObjNext(p, Id) > 0;                   }
static inline int         Gia_ObjHasSameRepr( Gia_Man_t * p, int i, int k )  { assert( k ); return i? (Gia_ObjRepr(p, i) == Gia_ObjRepr(p, k) && Gia_ObjRepr(p, i) != GIA_VOID) : Gia_ObjRepr(p, k) == 0;  }
static inline int         Gia_ObjIsFailedPair( Gia_Man_t * p, int i, int k ) { assert( k ); return i? (Gia_ObjFailed(p, i) || Gia_ObjFailed(p, k)) : Gia_ObjFailed(p, k);                     }

#define Gia_ManForEachConst( p, i )                            \
    for ( i = 1; i < Gia_ManObjNum(p); i++ ) if ( !Gia_ObjIsConst(p, i) ) {} else
#define Gia_ManForEachClass( p, i )                            \
    for ( i = 1; i < Gia_ManObjNum(p); i++ ) if ( !Gia_ObjIsHead(p, i) ) {} else
#define Gia_ManForEachClassReverse( p, i )                     \
    for ( i = Gia_ManObjNum(p) - 1; i > 0; i-- ) if ( !Gia_ObjIsHead(p, i) ) {} else
#define Gia_ClassForEachObj( p, i, iObj )                      \
    for ( assert(Gia_ObjIsHead(p, i)), iObj = i; iObj; iObj = Gia_ObjNext(p, iObj) )
#define Gia_ClassForEachObj1( p, i, iObj )                     \
    for ( assert(Gia_ObjIsHead(p, i)), iObj = Gia_ObjNext(p, i); iObj; iObj = Gia_ObjNext(p, iObj) )


static inline int        Gia_ObjIsGate( Gia_Man_t * p, int Id )             { return p->pMapping[Id] != 0;               }
static inline int        Gia_ObjGateSize( Gia_Man_t * p, int Id )           { return p->pMapping[p->pMapping[Id]];       }
static inline int *      Gia_ObjGateFanins( Gia_Man_t * p, int Id )         { return p->pMapping + p->pMapping[Id] + 1;  }

#define Gia_ManForEachGate( p, i )                             \
    for ( i = 1; i < Gia_ManObjNum(p); i++ ) if ( !Gia_ObjIsGate(p, i) ) {} else
#define Gia_GateForEachFanin( p, i, iFan, k )                  \
    for ( k = 0; k < Gia_ObjGateSize(p,i) && ((iFan = Gia_ObjGateFanins(p,i)[k]),1); k++ )

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define Gia_ManForEachObj( p, pObj, i )                                 \
    for ( i = 0; (i < p->nObjs) && ((pObj) = Gia_ManObj(p, i)); i++ )
#define Gia_ManForEachObj1( p, pObj, i )                                \
    for ( i = 1; (i < p->nObjs) && ((pObj) = Gia_ManObj(p, i)); i++ )
#define Gia_ManForEachObjVec( vVec, p, pObj, i )                        \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pObj) = Gia_ManObj(p, Vec_IntEntry(vVec,i))); i++ )
#define Gia_ManForEachObjVecLit( vVec, p, pObj, fCompl, i )             \
    for ( i = 0; (i < Vec_IntSize(vVec)) && ((pObj) = Gia_ManObj(p, Gia_Lit2Var(Vec_IntEntry(vVec,i)))) && (((fCompl) = Gia_LitIsCompl(Vec_IntEntry(vVec,i))),1); i++ )
#define Gia_ManForEachObjReverse( p, pObj, i )                          \
    for ( i = p->nObjs - 1; (i > 0) && ((pObj) = Gia_ManObj(p, i)); i-- )
#define Gia_ManForEachAnd( p, pObj, i )                                 \
    for ( i = 0; (i < p->nObjs) && ((pObj) = Gia_ManObj(p, i)); i++ )  if ( !Gia_ObjIsAnd(pObj) ) {} else
#define Gia_ManForEachCi( p, pObj, i )                                  \
    for ( i = 0; (i < Vec_IntSize(p->vCis)) && ((pObj) = Gia_ManCi(p, i)); i++ )
#define Gia_ManForEachCo( p, pObj, i )                                  \
    for ( i = 0; (i < Vec_IntSize(p->vCos)) && ((pObj) = Gia_ManCo(p, i)); i++ )
#define Gia_ManForEachCoReverse( p, pObj, i )                           \
    for ( i = Vec_IntSize(p->vCos) - 1; (i >= 0) && ((pObj) = Gia_ManCo(p, i)); i-- )
#define Gia_ManForEachCoDriver( p, pObj, i )                            \
    for ( i = 0; (i < Vec_IntSize(p->vCos)) && ((pObj) = Gia_ObjFanin0(Gia_ManCo(p, i))); i++ )
#define Gia_ManForEachPi( p, pObj, i )                                  \
    for ( i = 0; (i < Gia_ManPiNum(p)) && ((pObj) = Gia_ManCi(p, i)); i++ )
#define Gia_ManForEachPo( p, pObj, i )                                  \
    for ( i = 0; (i < Gia_ManPoNum(p)) && ((pObj) = Gia_ManCo(p, i)); i++ )
#define Gia_ManForEachRo( p, pObj, i )                                  \
    for ( i = 0; (i < Gia_ManRegNum(p)) && ((pObj) = Gia_ManCi(p, Gia_ManPiNum(p)+i)); i++ )
#define Gia_ManForEachRi( p, pObj, i )                                  \
    for ( i = 0; (i < Gia_ManRegNum(p)) && ((pObj) = Gia_ManCo(p, Gia_ManPoNum(p)+i)); i++ )
#define Gia_ManForEachRiRo( p, pObjRi, pObjRo, i )                      \
    for ( i = 0; (i < Gia_ManRegNum(p)) && ((pObjRi) = Gia_ManCo(p, Gia_ManPoNum(p)+i)) && ((pObjRo) = Gia_ManCi(p, Gia_ManPiNum(p)+i)); i++ )
 
////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== giaAiger.c ===========================================================*/
extern Gia_Man_t *         Gia_ReadAiger( char * pFileName, int fCheck );
extern void                Gia_WriteAiger( Gia_Man_t * p, char * pFileName, int fWriteSymbols, int fCompact );
extern void                Gia_DumpAiger( Gia_Man_t * p, char * pFilePrefix, int iFileNum, int nFileNumDigits );
/*=== giaCsatOld.c ============================================================*/
extern Vec_Int_t *         Cbs_ManSolveMiter( Gia_Man_t * pGia, int nConfs, Vec_Str_t ** pvStatus, int fVerbose );
/*=== giaCsat.c ============================================================*/
extern Vec_Int_t *         Cbs_ManSolveMiterNc( Gia_Man_t * pGia, int nConfs, Vec_Str_t ** pvStatus, int fVerbose );
/*=== giaCof.c =============================================================*/
extern void                Gia_ManPrintFanio( Gia_Man_t * pGia, int nNodes );
extern Gia_Man_t *         Gia_ManDupCof( Gia_Man_t * p, int iVar );
extern Gia_Man_t *         Gia_ManDupCofAllInt( Gia_Man_t * p, Vec_Int_t * vSigs, int fVerbose );
extern Gia_Man_t *         Gia_ManDupCofAll( Gia_Man_t * p, int nFanLim, int fVerbose );
/*=== giaDfs.c ============================================================*/
extern void                Gia_ManCollectCis( Gia_Man_t * p, int * pNodes, int nNodes, Vec_Int_t * vSupp );
extern void                Gia_ManCollectAnds( Gia_Man_t * p, int * pNodes, int nNodes, Vec_Int_t * vNodes );
extern int                 Gia_ManSuppSize( Gia_Man_t * p, int * pNodes, int nNodes );
extern int                 Gia_ManConeSize( Gia_Man_t * p, int * pNodes, int nNodes );
/*=== giaDup.c ============================================================*/
extern Gia_Man_t *         Gia_ManDupOrderDfs( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManDupOrderDfsReverse( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManDupOrderAiger( Gia_Man_t * p );

extern Gia_Man_t *         Gia_ManDup( Gia_Man_t * p );  
extern Gia_Man_t *         Gia_ManDupSelf( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManDupFlopClass( Gia_Man_t * p, int iClass );
extern Gia_Man_t *         Gia_ManDupMarked( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManDupTimes( Gia_Man_t * p, int nTimes );  
extern Gia_Man_t *         Gia_ManDupDfs( Gia_Man_t * p );  
extern Gia_Man_t *         Gia_ManDupDfsSkip( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManDupDfsCone( Gia_Man_t * p, Gia_Obj_t * pObj );
extern Gia_Man_t *         Gia_ManDupDfsLitArray( Gia_Man_t * p, Vec_Int_t * vLits );
extern Gia_Man_t *         Gia_ManDupNormalized( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManDupTrimmed( Gia_Man_t * p, int fTrimCis, int fTrimCos );
extern Gia_Man_t *         Gia_ManDupDfsCiMap( Gia_Man_t * p, int * pCi2Lit, Vec_Int_t * vLits );
extern Gia_Man_t *         Gia_ManDupDfsClasses( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManDupTopAnd( Gia_Man_t * p, int fVerbose );
extern Gia_Man_t *         Gia_ManMiter( Gia_Man_t * pAig0, Gia_Man_t * pAig1, int fDualOut, int fSeq, int fVerbose );
extern Gia_Man_t *         Gia_ManTransformMiter( Gia_Man_t * p );
/*=== giaEnable.c ==========================================================*/
extern void                Gia_ManDetectSeqSignals( Gia_Man_t * p, int fSetReset, int fVerbose );
extern Gia_Man_t *         Gia_ManUnrollAndCofactor( Gia_Man_t * p, int nFrames, int nFanMax, int fVerbose );
extern Gia_Man_t *         Gia_ManRemoveEnables( Gia_Man_t * p );
/*=== giaEquiv.c ==========================================================*/
extern int                 Gia_ManCheckTopoOrder( Gia_Man_t * p );
extern int *               Gia_ManDeriveNexts( Gia_Man_t * p );
extern void                Gia_ManEquivPrintOne( Gia_Man_t * p, int i, int Counter );
extern void                Gia_ManEquivPrintClasses( Gia_Man_t * p, int fVerbose, float Mem );
extern Gia_Man_t *         Gia_ManEquivReduce( Gia_Man_t * p, int fUseAll, int fDualOut, int fVerbose );
extern Gia_Man_t *         Gia_ManEquivReduceAndRemap( Gia_Man_t * p, int fSeq, int fMiterPairs );
extern int                 Gia_ManEquivSetColors( Gia_Man_t * p, int fVerbose );
extern Gia_Man_t *         Gia_ManSpecReduce( Gia_Man_t * p, int fDualOut, int fVerbose );
extern Gia_Man_t *         Gia_ManSpecReduceInit( Gia_Man_t * p, Gia_Cex_t * pInit, int nFrames, int fDualOut );
extern void                Gia_ManEquivTransform( Gia_Man_t * p, int fVerbose );
extern void                Gia_ManEquivImprove( Gia_Man_t * p );
/*=== giaFanout.c =========================================================*/
extern void                Gia_ObjAddFanout( Gia_Man_t * p, Gia_Obj_t * pObj, Gia_Obj_t * pFanout );
extern void                Gia_ObjRemoveFanout( Gia_Man_t * p, Gia_Obj_t * pObj, Gia_Obj_t * pFanout );
extern void                Gia_ManFanoutStart( Gia_Man_t * p );
extern void                Gia_ManFanoutStop( Gia_Man_t * p );
/*=== giaForce.c =========================================================*/
extern void                For_ManExperiment( Gia_Man_t * pGia, int nIters, int fClustered, int fVerbose );
/*=== giaFrames.c =========================================================*/
extern void                Gia_ManFraSetDefaultParams( Gia_ParFra_t * p );
extern Gia_Man_t *         Gia_ManFrames( Gia_Man_t * pAig, Gia_ParFra_t * pPars );  
/*=== giaFront.c ==========================================================*/
extern Gia_Man_t *         Gia_ManFront( Gia_Man_t * p );
extern void                Gia_ManFrontTest( Gia_Man_t * p );
/*=== giaHash.c ===========================================================*/
extern void                Gia_ManHashAlloc( Gia_Man_t * p ); 
extern void                Gia_ManHashStart( Gia_Man_t * p ); 
extern void                Gia_ManHashStop( Gia_Man_t * p );  
extern int                 Gia_ManHashAnd( Gia_Man_t * p, int iLit0, int iLit1 ); 
extern int                 Gia_ManHashXor( Gia_Man_t * p, int iLit0, int iLit1 ); 
extern int                 Gia_ManHashMux( Gia_Man_t * p, int iCtrl, int iData1, int iData0 );
extern int                 Gia_ManHashAndTry( Gia_Man_t * p, int iLit0, int iLit1 );
extern Gia_Man_t *         Gia_ManRehash( Gia_Man_t * p, int fAddStrash );
extern void                Gia_ManHashProfile( Gia_Man_t * p );
/*=== giaLogic.c ===========================================================*/
extern void                Gia_ManTestDistance( Gia_Man_t * p );
extern void                Gia_ManSolveProblem( Gia_Man_t * pGia, Emb_Par_t * pPars );
 /*=== giaMan.c ===========================================================*/
extern Gia_Man_t *         Gia_ManStart( int nObjsMax ); 
extern void                Gia_ManStop( Gia_Man_t * p );  
extern void                Gia_ManPrintStats( Gia_Man_t * p, int fSwitch ); 
extern void                Gia_ManPrintStatsShort( Gia_Man_t * p ); 
extern void                Gia_ManPrintMiterStatus( Gia_Man_t * p ); 
extern void                Gia_ManSetRegNum( Gia_Man_t * p, int nRegs );
extern void                Gia_ManReportImprovement( Gia_Man_t * p, Gia_Man_t * pNew );
/*=== giaMap.c ===========================================================*/
extern void                Gia_ManPrintMappingStats( Gia_Man_t * p );
/*=== giaPat.c ===========================================================*/
extern void                Gia_SatVerifyPattern( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vCex, Vec_Int_t * vVisit );
/*=== giaRetime.c ===========================================================*/
extern Gia_Man_t *         Gia_ManRetimeForward( Gia_Man_t * p, int nMaxIters, int fVerbose );
/*=== giaSat.c ============================================================*/
extern int                 Sat_ManTest( Gia_Man_t * pGia, Gia_Obj_t * pObj, int nConfsMax );
/*=== giaScl.c ============================================================*/
extern int                 Gia_ManSeqMarkUsed( Gia_Man_t * p );
extern int                 Gia_ManCombMarkUsed( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManCleanup( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManSeqCleanup( Gia_Man_t * p );
extern Gia_Man_t *         Gia_ManSeqStructSweep( Gia_Man_t * p, int fConst, int fEquiv, int fVerbose );
/*=== giaSort.c ============================================================*/
extern int *               Gia_SortFloats( float * pArray, int * pPerm, int nSize );
/*=== giaSim.c ============================================================*/
extern int                 Gia_ManSimSimulate( Gia_Man_t * pAig, Gia_ParSim_t * pPars );
/*=== giaSwitch.c ============================================================*/
extern float               Gia_ManEvaluateSwitching( Gia_Man_t * p );
extern float               Gia_ManComputeSwitching( Gia_Man_t * p, int nFrames, int nPref, int fProbOne );
/*=== giaTsim.c ============================================================*/
extern Gia_Man_t *         Gia_ManReduceConst( Gia_Man_t * pAig, int fVerbose );
/*=== giaUtil.c ===========================================================*/
extern unsigned            Gia_ManRandom( int fReset );
extern void                Gia_ManRandomInfo( Vec_Ptr_t * vInfo, int iInputStart, int iWordStart, int iWordStop );
extern unsigned int        Gia_PrimeCudd( unsigned int p );
extern char *              Gia_FileNameGenericAppend( char * pBase, char * pSuffix );
extern void                Gia_ManSetMark0( Gia_Man_t * p );
extern void                Gia_ManCleanMark0( Gia_Man_t * p );
extern void                Gia_ManCheckMark0( Gia_Man_t * p );
extern void                Gia_ManSetMark1( Gia_Man_t * p );
extern void                Gia_ManCleanMark1( Gia_Man_t * p );
extern void                Gia_ManCheckMark1( Gia_Man_t * p );
extern void                Gia_ManCleanValue( Gia_Man_t * p );
extern void                Gia_ManFillValue( Gia_Man_t * p );
extern void                Gia_ManSetPhase( Gia_Man_t * p );
extern int                 Gia_ManLevelNum( Gia_Man_t * p );
extern void                Gia_ManSetRefs( Gia_Man_t * p );
extern int *               Gia_ManCreateMuxRefs( Gia_Man_t * p );
extern void                Gia_ManCreateRefs( Gia_Man_t * p );
extern int                 Gia_ManCrossCut( Gia_Man_t * p );
extern int                 Gia_ManIsNormalized( Gia_Man_t * p );
extern Vec_Int_t *         Gia_ManCollectPoIds( Gia_Man_t * p );
extern int                 Gia_ObjIsMuxType( Gia_Obj_t * pNode );
extern int                 Gia_ObjRecognizeExor( Gia_Obj_t * pObj, Gia_Obj_t ** ppFan0, Gia_Obj_t ** ppFan1 );
extern Gia_Obj_t *         Gia_ObjRecognizeMux( Gia_Obj_t * pNode, Gia_Obj_t ** ppNodeT, Gia_Obj_t ** ppNodeE );
extern Gia_Cex_t *         Gia_ManAllocCounterExample( int nRegs, int nRealPis, int nFrames );
extern int                 Gia_ManVerifyCounterExample( Gia_Man_t * pAig, Gia_Cex_t * p, int fDualOut );
extern void                Gia_ManPrintCounterExample( Gia_Cex_t * p );
extern int                 Gia_NodeMffcSize( Gia_Man_t * p, Gia_Obj_t * pNode );
 
#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

