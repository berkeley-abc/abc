/**CFile****************************************************************

  FileName    [ft.h]

  PackageName [MVSIS 2.0: Multi-valued logic synthesis system.]

  Synopsis    [Data structure for algebraic factoring.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - February 1, 2003.]

  Revision    [$Id: ft.h,v 1.1 2003/05/22 19:20:04 alanmi Exp $]

***********************************************************************/

#ifndef __FT_H__
#define __FT_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    STRUCTURE DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

typedef struct Ft_Node_t_ Ft_Node_t;
struct Ft_Node_t_
{
    // the first child
    unsigned   fCompl0  :  1;    // complemented attribute
    unsigned   iFanin0  : 11;    // fanin number
    // the second child
    unsigned   fCompl1  :  1;    // complemented attribute
    unsigned   iFanin1  : 11;    // fanin number (1-based)
    // other info
    unsigned   fIntern  :  1;    // marks any node that is not an elementary var
    unsigned   fConst   :  1;    // marks the constant 1 function
    unsigned   fCompl   :  1;    // marks the complement of topmost node
    // printing info
    unsigned   fNodeOr  :  1;    // marks the original OR node
    unsigned   fEdge0   :  1;    // marks the original complemented edge
    unsigned   fEdge1   :  1;    // marks the original complemented edge
    // some bits are unused
};

/*
    The factored form of an SOP is an array (Vec_Int_t) of entries of type Ft_Node_t.
    If the SOP has n input variables (some of them may not be in the true support)
    the first n entries of the factored form array are zeros. The other entries of the array
    represent the internal AND nodes of the factored form, and possibly the constant node.
    This representation makes it easy to translate the factored form into an AIG.
    The factored AND nodes contains fanins of the node and their complemented attributes 
    (using AIG semantics). The elementary variable (buffer or interver) are represented 
    as a node with the same fanins. For example: x' = AND( x', x' ).
    The constant node is represented a special node with the constant flag set. 
    If the constant node and the elementary variable are present, no other internal 
    AND nodes are allowed in the factored form.
*/

// working with complemented attributes of objects
static inline bool        Ptr_IsComplement( void * p )    { return (bool)(((unsigned)p) & 01);     }
static inline void *      Ptr_Regular( void * p )         { return (void *)((unsigned)(p) & ~01);  }
static inline void *      Ptr_Not( void * p )             { return (void *)((unsigned)(p) ^  01);  }
static inline void *      Ptr_NotCond( void * p, int c )  { return (void *)((unsigned)(p) ^ (c));  }

static inline Ft_Node_t * Ft_NodeRead( Vec_Int_t * vForm, int i )   {  return (Ft_Node_t *)vForm->pArray + i;  }
static inline Ft_Node_t * Ft_NodeReadLast( Vec_Int_t * vForm )      {  return (Ft_Node_t *)vForm->pArray + vForm->nSize - 1;  }
static inline Ft_Node_t * Ft_NodeFanin0( Vec_Int_t * vForm, Ft_Node_t * pNode )   { assert( pNode->fIntern ); return (Ft_Node_t *)vForm->pArray + pNode->iFanin0;  }
static inline Ft_Node_t * Ft_NodeFanin1( Vec_Int_t * vForm, Ft_Node_t * pNode )   { assert( pNode->fIntern ); return (Ft_Node_t *)vForm->pArray + pNode->iFanin1;  }

static inline Ft_Node_t   Ft_Int2Node( int Num  )                   {  return *((Ft_Node_t *)&Num);  }
static inline int         Ft_Node2Int( Ft_Node_t Node )             {  return *((int *)&Node);       }
static inline void        Ft_NodeClean( Ft_Node_t * pNode )         {  *((int *)pNode) = 0;          }

////////////////////////////////////////////////////////////////////////
///                       MACRO DEFITIONS                            ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/*=== ftFactor.c =====================================================*/
extern void               Ft_FactorStartMan();
extern void               Ft_FactorStopMan();
extern Vec_Int_t *        Ft_Factor( char * pSop );
extern int                Ft_FactorGetNumNodes( Vec_Int_t * vForm );
extern int                Ft_FactorGetNumVars( Vec_Int_t * vForm );
/*=== ftPrint.c =====================================================*/
extern void               Ft_FactorPrint( FILE * pFile, Vec_Int_t * vForm, char * pNamesIn[], char * pNameOut );


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

