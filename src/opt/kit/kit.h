/**CFile****************************************************************

  FileName    [kit.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Computation kit.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Dec 6, 2006.]

  Revision    [$Id: kit.h,v 1.00 2006/12/06 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef __KIT_H__
#define __KIT_H__

#ifdef __cplusplus
extern "C" {
#endif

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

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Kit_Sop_t_ Kit_Sop_t;
struct Kit_Sop_t_
{
    int               nCubes;         // the number of cubes
    unsigned *        pCubes;         // the storage for cubes
};

typedef struct Kit_Edge_t_ Kit_Edge_t;
struct Kit_Edge_t_
{
    unsigned          fCompl   :  1;   // the complemented bit
    unsigned          Node     : 30;   // the decomposition node pointed by the edge
};

typedef struct Kit_Node_t_ Kit_Node_t;
struct Kit_Node_t_
{
    Kit_Edge_t        eEdge0;          // the left child of the node
    Kit_Edge_t        eEdge1;          // the right child of the node
    // other info
    void *            pFunc;           // the function of the node (BDD or AIG)
    unsigned          Level    : 14;   // the level of this node in the global AIG
    // printing info 
    unsigned          fNodeOr  :  1;   // marks the original OR node
    unsigned          fCompl0  :  1;   // marks the original complemented edge
    unsigned          fCompl1  :  1;   // marks the original complemented edge
    // latch info
    unsigned          nLat0    :  5;   // the number of latches on the first edge
    unsigned          nLat1    :  5;   // the number of latches on the second edge
    unsigned          nLat2    :  5;   // the number of latches on the output edge
};

typedef struct Kit_Graph_t_ Kit_Graph_t;
struct Kit_Graph_t_
{
    int               fConst;          // marks the constant 1 graph
    int               nLeaves;         // the number of leaves
    int               nSize;           // the number of nodes (including the leaves) 
    int               nCap;            // the number of allocated nodes
    Kit_Node_t *      pNodes;          // the array of leaves and internal nodes
    Kit_Edge_t        eRoot;           // the pointer to the topmost node
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#ifndef ALLOC
#define ALLOC(type, num)     ((type *) malloc(sizeof(type) * (num)))
#endif

#ifndef FREE
#define FREE(obj)             ((obj) ? (free((char *) (obj)), (obj) = 0) : 0)
#endif

#ifndef REALLOC
#define REALLOC(type, obj, num)    \
        ((obj) ? ((type *) realloc((char *)(obj), sizeof(type) * (num))) : \
         ((type *) malloc(sizeof(type) * (num))))
#endif

static inline int          Kit_CubeHasLit( unsigned uCube, int i )                        { return(uCube &  (unsigned)(1<<i)) > 0;  }
static inline unsigned     Kit_CubeSetLit( unsigned uCube, int i )                        { return uCube |  (unsigned)(1<<i);       }
static inline unsigned     Kit_CubeXorLit( unsigned uCube, int i )                        { return uCube ^  (unsigned)(1<<i);       }
static inline unsigned     Kit_CubeRemLit( unsigned uCube, int i )                        { return uCube & ~(unsigned)(1<<i);       }

static inline int          Kit_CubeContains( unsigned uLarge, unsigned uSmall )           { return (uLarge & uSmall) == uSmall;     }
static inline unsigned     Kit_CubeSharp( unsigned uCube, unsigned uMask )                { return uCube & ~uMask;                  }
static inline unsigned     Kit_CubeMask( int nVar )                                       { return (~(unsigned)0) >> (32-nVar);     }

static inline int          Kit_CubeIsMarked( unsigned uCube )                             { return Kit_CubeHasLit( uCube, 31 );     }
static inline unsigned     Kit_CubeMark( unsigned uCube )                                 { return Kit_CubeSetLit( uCube, 31 );     }
static inline unsigned     Kit_CubeUnmark( unsigned uCube )                               { return Kit_CubeRemLit( uCube, 31 );     }

static inline int          Kit_SopCubeNum( Kit_Sop_t * cSop )                             { return cSop->nCubes;                    }
static inline unsigned     Kit_SopCube( Kit_Sop_t * cSop, int i )                         { return cSop->pCubes[i];                 }
static inline void         Kit_SopShrink( Kit_Sop_t * cSop, int nCubesNew )               { cSop->nCubes = nCubesNew;               }
static inline void         Kit_SopPushCube( Kit_Sop_t * cSop, unsigned uCube )            { cSop->pCubes[cSop->nCubes++] = uCube;   }
static inline void         Kit_SopWriteCube( Kit_Sop_t * cSop, unsigned uCube, int i )    { cSop->pCubes[i] = uCube;                }

static inline Kit_Edge_t   Kit_EdgeCreate( int Node, int fCompl )                         { Kit_Edge_t eEdge = { fCompl, Node }; return eEdge;  }
static inline unsigned     Kit_EdgeToInt( Kit_Edge_t eEdge )                              { return (eEdge.Node << 1) | eEdge.fCompl;            }
static inline Kit_Edge_t   Kit_IntToEdge( unsigned Edge )                                 { return Kit_EdgeCreate( Edge >> 1, Edge & 1 );       }
static inline unsigned     Kit_EdgeToInt_( Kit_Edge_t eEdge )                             { return *(unsigned *)&eEdge;                         }
static inline Kit_Edge_t   Kit_IntToEdge_( unsigned Edge )                                { return *(Kit_Edge_t *)&Edge;                        }

static inline int          Kit_GraphIsConst( Kit_Graph_t * pGraph )                       { return pGraph->fConst;                              }
static inline int          Kit_GraphIsConst0( Kit_Graph_t * pGraph )                      { return pGraph->fConst && pGraph->eRoot.fCompl;      }
static inline int          Kit_GraphIsConst1( Kit_Graph_t * pGraph )                      { return pGraph->fConst && !pGraph->eRoot.fCompl;     }
static inline int          Kit_GraphIsComplement( Kit_Graph_t * pGraph )                  { return pGraph->eRoot.fCompl;                        }
static inline int          Kit_GraphIsVar( Kit_Graph_t * pGraph )                         { return pGraph->eRoot.Node < (unsigned)pGraph->nLeaves; }
static inline void         Kit_GraphComplement( Kit_Graph_t * pGraph )                    { pGraph->eRoot.fCompl ^= 1;                          }
static inline void         Kit_GraphSetRoot( Kit_Graph_t * pGraph, Kit_Edge_t eRoot )     { pGraph->eRoot = eRoot;                              }
static inline int          Kit_GraphLeaveNum( Kit_Graph_t * pGraph )                      { return pGraph->nLeaves;                             }
static inline int          Kit_GraphNodeNum( Kit_Graph_t * pGraph )                       { return pGraph->nSize - pGraph->nLeaves;             }
static inline Kit_Node_t * Kit_GraphNode( Kit_Graph_t * pGraph, int i )                   { return pGraph->pNodes + i;                          }
static inline Kit_Node_t * Kit_GraphNodeLast( Kit_Graph_t * pGraph )                      { return pGraph->pNodes + pGraph->nSize - 1;          }
static inline int          Kit_GraphNodeInt( Kit_Graph_t * pGraph, Kit_Node_t * pNode )   { return pNode - pGraph->pNodes;                      }
static inline int          Kit_GraphNodeIsVar( Kit_Graph_t * pGraph, Kit_Node_t * pNode ) { return Kit_GraphNodeInt(pGraph,pNode) < pGraph->nLeaves; }
static inline Kit_Node_t * Kit_GraphVar( Kit_Graph_t * pGraph )                           { assert( Kit_GraphIsVar( pGraph ) );    return Kit_GraphNode( pGraph, pGraph->eRoot.Node ); }
static inline int          Kit_GraphVarInt( Kit_Graph_t * pGraph )                        { assert( Kit_GraphIsVar( pGraph ) );    return Kit_GraphNodeInt( pGraph, Kit_GraphVar(pGraph) );}

static inline int          Kit_Float2Int( float Val )     { return *((int *)&Val);               }
static inline float        Kit_Int2Float( int Num )       { return *((float *)&Num);             }
static inline int          Kit_BitWordNum( int nBits )    { return nBits/(8*sizeof(unsigned)) + ((nBits%(8*sizeof(unsigned))) > 0);  }
static inline int          Kit_TruthWordNum( int nVars )  { return nVars <= 5 ? 1 : (1 << (nVars - 5)); }

static inline void         Kit_TruthSetBit( unsigned * p, int Bit )   { p[Bit>>5] |= (1<<(Bit & 31));               }
static inline void         Kit_TruthXorBit( unsigned * p, int Bit )   { p[Bit>>5] ^= (1<<(Bit & 31));               }
static inline int          Kit_TruthHasBit( unsigned * p, int Bit )   { return (p[Bit>>5] & (1<<(Bit & 31))) > 0;   }

static inline int Kit_WordCountOnes( unsigned uWord )
{
    uWord = (uWord & 0x55555555) + ((uWord>>1) & 0x55555555);
    uWord = (uWord & 0x33333333) + ((uWord>>2) & 0x33333333);
    uWord = (uWord & 0x0F0F0F0F) + ((uWord>>4) & 0x0F0F0F0F);
    uWord = (uWord & 0x00FF00FF) + ((uWord>>8) & 0x00FF00FF);
    return  (uWord & 0x0000FFFF) + (uWord>>16);
}
static inline int Kit_TruthCountOnes( unsigned * pIn, int nVars )
{
    int w, Counter = 0;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        Counter += Kit_WordCountOnes(pIn[w]);
    return Counter;
}
static inline int Kit_TruthIsEqual( unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        if ( pIn0[w] != pIn1[w] )
            return 0;
    return 1;
}
static inline int Kit_TruthIsConst0( unsigned * pIn, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        if ( pIn[w] )
            return 0;
    return 1;
}
static inline int Kit_TruthIsConst1( unsigned * pIn, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        if ( pIn[w] != ~(unsigned)0 )
            return 0;
    return 1;
}
static inline int Kit_TruthIsImply( unsigned * pIn1, unsigned * pIn2, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        if ( pIn1[w] & ~pIn2[w] )
            return 0;
    return 1;
}
static inline void Kit_TruthCopy( unsigned * pOut, unsigned * pIn, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn[w];
}
static inline void Kit_TruthClear( unsigned * pOut, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = 0;
}
static inline void Kit_TruthFill( unsigned * pOut, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = ~(unsigned)0;
}
static inline void Kit_TruthNot( unsigned * pOut, unsigned * pIn, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = ~pIn[w];
}
static inline void Kit_TruthAnd( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn0[w] & pIn1[w];
}
static inline void Kit_TruthOr( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn0[w] | pIn1[w];
}
static inline void Kit_TruthSharp( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn0[w] & ~pIn1[w];
}
static inline void Kit_TruthNand( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Kit_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = ~(pIn0[w] & pIn1[w]);
}

////////////////////////////////////////////////////////////////////////
///                           ITERATORS                              ///
////////////////////////////////////////////////////////////////////////

#define Kit_SopForEachCube( cSop, uCube, i )                                      \
    for ( i = 0; (i < Kit_SopCubeNum(cSop)) && ((uCube) = Kit_SopCube(cSop, i)); i++ )
#define Kit_CubeForEachLiteral( uCube, Lit, nLits, i )                            \
    for ( i = 0; (i < (nLits)) && ((Lit) = Kit_CubeHasLit(uCube, i)); i++ )

#define Kit_GraphForEachLeaf( pGraph, pLeaf, i )                                              \
    for ( i = 0; (i < (pGraph)->nLeaves) && (((pLeaf) = Kit_GraphNode(pGraph, i)), 1); i++ )
#define Kit_GraphForEachNode( pGraph, pAnd, i )                                               \
    for ( i = (pGraph)->nLeaves; (i < (pGraph)->nSize) && (((pAnd) = Kit_GraphNode(pGraph, i)), 1); i++ )

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== kitBdd.c ==========================================================*/
extern DdNode *        Kit_SopToBdd( DdManager * dd, Kit_Sop_t * cSop, int nVars );
extern DdNode *        Kit_GraphToBdd( DdManager * dd, Kit_Graph_t * pGraph );
extern DdNode *        Kit_TruthToBdd( DdManager * dd, unsigned * pTruth, int nVars );
/*=== kitFactor.c ==========================================================*/
extern Kit_Graph_t *   Kit_SopFactor( Vec_Int_t * vCover, int fCompl, int nVars, Vec_Int_t * vMemory );
/*=== kitGraph.c ==========================================================*/
extern Kit_Graph_t *   Kit_GraphCreate( int nLeaves );   
extern Kit_Graph_t *   Kit_GraphCreateConst0();   
extern Kit_Graph_t *   Kit_GraphCreateConst1();   
extern Kit_Graph_t *   Kit_GraphCreateLeaf( int iLeaf, int nLeaves, int fCompl );   
extern void            Kit_GraphFree( Kit_Graph_t * pGraph );   
extern Kit_Node_t *    Kit_GraphAppendNode( Kit_Graph_t * pGraph );   
extern Kit_Edge_t      Kit_GraphAddNodeAnd( Kit_Graph_t * pGraph, Kit_Edge_t eEdge0, Kit_Edge_t eEdge1 );
extern Kit_Edge_t      Kit_GraphAddNodeOr( Kit_Graph_t * pGraph, Kit_Edge_t eEdge0, Kit_Edge_t eEdge1 );
extern Kit_Edge_t      Kit_GraphAddNodeXor( Kit_Graph_t * pGraph, Kit_Edge_t eEdge0, Kit_Edge_t eEdge1, int Type );
extern Kit_Edge_t      Kit_GraphAddNodeMux( Kit_Graph_t * pGraph, Kit_Edge_t eEdgeC, Kit_Edge_t eEdgeT, Kit_Edge_t eEdgeE, int Type );
extern unsigned        Kit_GraphToTruth( Kit_Graph_t * pGraph );
extern Kit_Graph_t *   Kit_TruthToGraph( unsigned * pTruth, int nVars, Vec_Int_t * vMemory );
/*=== kitHop.c ==========================================================*/
/*=== kitIsop.c ==========================================================*/
extern int             Kit_TruthIsop( unsigned * puTruth, int nVars, Vec_Int_t * vMemory, int fTryBoth );
/*=== kitSop.c ==========================================================*/
extern void            Kit_SopCreate( Kit_Sop_t * cResult, Vec_Int_t * vInput, int nVars, Vec_Int_t * vMemory );
extern void            Kit_SopCreateInverse( Kit_Sop_t * cResult, Vec_Int_t * vInput, int nVars, Vec_Int_t * vMemory );
extern void            Kit_SopDup( Kit_Sop_t * cResult, Kit_Sop_t * cSop, Vec_Int_t * vMemory );
extern void            Kit_SopDivideByLiteralQuo( Kit_Sop_t * cSop, int iLit );
extern void            Kit_SopDivideByCube( Kit_Sop_t * cSop, Kit_Sop_t * cDiv, Kit_Sop_t * vQuo, Kit_Sop_t * vRem, Vec_Int_t * vMemory );
extern void            Kit_SopDivideInternal( Kit_Sop_t * cSop, Kit_Sop_t * cDiv, Kit_Sop_t * vQuo, Kit_Sop_t * vRem, Vec_Int_t * vMemory );
extern void            Kit_SopMakeCubeFree( Kit_Sop_t * cSop );
extern int             Kit_SopIsCubeFree( Kit_Sop_t * cSop );
extern void            Kit_SopCommonCubeCover( Kit_Sop_t * cResult, Kit_Sop_t * cSop, Vec_Int_t * vMemory );
extern int             Kit_SopAnyLiteral( Kit_Sop_t * cSop, int nLits );
extern int             Kit_SopDivisor( Kit_Sop_t * cResult, Kit_Sop_t * cSop, int nLits, Vec_Int_t * vMemory );
extern void            Kit_SopBestLiteralCover( Kit_Sop_t * cResult, Kit_Sop_t * cSop, unsigned uCube, int nLits, Vec_Int_t * vMemory );
/*=== kitTruth.c ==========================================================*/
extern void            Kit_TruthSwapAdjacentVars( unsigned * pOut, unsigned * pIn, int nVars, int Start );
extern void            Kit_TruthStretch( unsigned * pOut, unsigned * pIn, int nVars, int nVarsAll, unsigned Phase );
extern void            Kit_TruthShrink( unsigned * pOut, unsigned * pIn, int nVars, int nVarsAll, unsigned Phase );
extern int             Kit_TruthVarInSupport( unsigned * pTruth, int nVars, int iVar );
extern int             Kit_TruthSupportSize( unsigned * pTruth, int nVars );
extern int             Kit_TruthSupport( unsigned * pTruth, int nVars );
extern void            Kit_TruthCofactor0( unsigned * pTruth, int nVars, int iVar );
extern void            Kit_TruthCofactor1( unsigned * pTruth, int nVars, int iVar );
extern void            Kit_TruthExist( unsigned * pTruth, int nVars, int iVar );
extern void            Kit_TruthForall( unsigned * pTruth, int nVars, int iVar );
extern void            Kit_TruthMux( unsigned * pOut, unsigned * pCof0, unsigned * pCof1, int nVars, int iVar );
extern void            Kit_TruthChangePhase( unsigned * pTruth, int nVars, int iVar );
extern int             Kit_TruthMinCofSuppOverlap( unsigned * pTruth, int nVars, int * pVarMin );
extern void            Kit_TruthCountOnesInCofs( unsigned * pTruth, int nVars, short * pStore );
extern unsigned        Kit_TruthHash( unsigned * pIn, int nWords );
extern unsigned        Kit_TruthSemiCanonicize( unsigned * pInOut, unsigned * pAux, int nVars, char * pCanonPerm, short * pStore );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

