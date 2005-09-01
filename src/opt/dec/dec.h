/**CFile****************************************************************

  FileName    [dec.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [A simple decomposition tree/node data structure and its APIs.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: dec.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __DEC_H__
#define __DEC_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Dec_Node_t_ Dec_Node_t;
struct Dec_Node_t_
{
    // the first child
    unsigned   fCompl0  :  1;    // complemented attribute of the first fanin
    unsigned   iFanin0  : 11;    // the number of the first fanin
    // the second child
    unsigned   fCompl1  :  1;    // complemented attribute of the second fanin
    unsigned   iFanin1  : 11;    // the number of the second fanin
    // other info
    unsigned   fIntern  :  1;    // marks all internal nodes (to distinquish them from elementary vars) 
    unsigned   fConst   :  1;    // marks the constant 1 function (topmost node only)
    unsigned   fCompl   :  1;    // marks the complement of topmost node (topmost node only)
    // printing info (factored forms only)
    unsigned   fNodeOr  :  1;    // marks the original OR node
    unsigned   fEdge0   :  1;    // marks the original complemented edge
    unsigned   fEdge1   :  1;    // marks the original complemented edge
    // some bits are left unused
};

/*
    The decomposition tree data structure is designed to represent relatively small
    (up to 100 nodes) AIGs used for factoring, rewriting, and decomposition.

    For simplicity, the nodes of the decomposition tree are written in DFS order 
    into an integer vector (Vec_Int_t). The decomposition node (Dec_Node_t)
    is typecast into an integer when written into the array.
    
    This representation can be readily translated into the main AIG represented 
    in the ABC network. Because of the linear order of the decomposition nodes 
    in the array, it is easy to put the existing AIG nodes in correspondence with 
    them. This process begins by first putting leaves of the decomposition tree 
    in correpondence with the fanins of the cut used to derive the function, 
    which was decomposed. Next for each internal node of the decomposition tree, 
    we find or create a corresponding node in the AIG. Finally, the root node of 
    the tree replaces the original root node of the cut, which was decomposed.

    To achieve the above scenario, we reserve the first n entries for the array
    to the fanins of the cut (the number of fanins is n). These entries are left
    empty in the array (that is, they are represented by 0 integer). Each entry
    after the fanins is an internal node (flag fIntern is set to 1). The internal
    nodes can have complemented inputs (denoted by flags fComp0 and fCompl1).
    The last node can be complemented (fCompl), which is true if the root node
    of the decomposition tree is represented by a complemented AIG node.

    Two cases have to be specially considered: a constant function and a function
    equal to an elementary variables (possibly complemented). In these two cases,
    the decomposition tree/array has exactly n+1 nodes, where n in the number of 
    fanins. (A constant function may depend on n variable, in which case these
    are redundant variables. Similarly, a function can be a function in n-D space
    but in fact depend only on one variable in this space.)

    When the function is a constant, the last node has a flag fConst set to 1.
    In this case the complemented flag (fCompl) shows the value of the constant.
    (fCompl = 0 means costant 1; fCompl = 1 means constant 0).
    When the function if an elementary variable, the last node has both pointers
    pointing to the same elementary node, while the complemented flag (fCompl)
    shows whether the variable is complemented. For example: x' = Not( AND(x, x) ).

    When manipulating the decomposition tree, it is convenient to return the 
    intermediate results of decomposition as an integer, which includes the number 
    of the Dec_Node_t in the array of decomposition nodes and the complemented flag.
    Factoring is a special case of decomposition, which demonstrates this kind
    of manipulation.
*/

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Cleans the decomposition node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/ 
static inline void         Dec_NodeClean( Dec_Node_t * pNode )       {  *((int *)pNode) = 0;           }

/**Function*************************************************************

  Synopsis    [Convert between an interger and an decomposition node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Dec_Node_t   Dec_Int2Node( int Num )                   {  return *((Dec_Node_t *)&Num);  }
static inline int          Dec_Node2Int( Dec_Node_t Node )           {  return *((int *)&Node);        }

/**Function*************************************************************

  Synopsis    [Returns the pointer to the i-th decomposition node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Dec_Node_t * Dec_NodeRead( Vec_Int_t * vDec, int i )   {  return (Dec_Node_t *)vDec->pArray + i;  }

/**Function*************************************************************

  Synopsis    [Returns the pointer to the last decomposition node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Dec_Node_t * Dec_NodeReadLast( Vec_Int_t * vDec )      {  return (Dec_Node_t *)vDec->pArray + vDec->nSize - 1;  }

/**Function*************************************************************

  Synopsis    [Returns the pointer to the fanins of the i-th decomposition node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Dec_Node_t * Dec_NodeFanin0( Vec_Int_t * vDec, int i ) { assert( Dec_NodeRead(vDec,i)->fIntern ); return (Dec_Node_t *)vDec->pArray + Dec_NodeRead(vDec,i)->iFanin0;  }
static inline Dec_Node_t * Dec_NodeFanin1( Vec_Int_t * vDec, int i ) { assert( Dec_NodeRead(vDec,i)->fIntern ); return (Dec_Node_t *)vDec->pArray + Dec_NodeRead(vDec,i)->iFanin1;  }

/**Function*************************************************************

  Synopsis    [Returns the complemented attributes of the i-th decomposition node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline bool         Dec_NodeFaninC0( Vec_Int_t * vDec, int i ) { assert( Dec_NodeRead(vDec,i)->fIntern ); return (bool)Dec_NodeRead(vDec,i)->fCompl0;  }
static inline bool         Dec_NodeFaninC1( Vec_Int_t * vDec, int i ) { assert( Dec_NodeRead(vDec,i)->fIntern ); return (bool)Dec_NodeRead(vDec,i)->fCompl1;  }

/**Function*************************************************************

  Synopsis    [Returns the number of leaf variables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Dec_TreeNumVars( Vec_Int_t * vDec )
{
    int i;
    for ( i = 0; i < vDec->nSize; i++ )
        if ( vDec->pArray[i] )
            break;
    return i;
}

/**Function*************************************************************

  Synopsis    [Returns the number of AND nodes in the tree.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Dec_TreeNumAnds( Vec_Int_t * vDec )
{
    Dec_Node_t * pNode;
    pNode = Dec_NodeReadLast(vDec);
    if ( pNode->fConst ) // constant
        return 0;
    if ( pNode->iFanin0 == pNode->iFanin1 ) // literal
        return 0;
    return vDec->nSize - Dec_TreeNumVars(vDec);
}

/**Function*************************************************************

  Synopsis    [Returns the number of literals in the factored form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Dec_TreeNumFFLits( Vec_Int_t * vDec )
{
    return 1 + Dec_TreeNumAnds( vDec );
}



/**Function*************************************************************

  Synopsis    [Checks if the output node of the decomposition tree is complemented.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline bool Dec_TreeIsComplement( Vec_Int_t * vForm )  { return Dec_NodeReadLast(vForm)->fCompl;  }

/**Function*************************************************************

  Synopsis    [Complements the output node of the decomposition tree.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Dec_TreeComplement( Vec_Int_t * vForm )    {  Dec_NodeReadLast(vForm)->fCompl ^= 1;   }


/**Function*************************************************************

  Synopsis    [Checks if the output node is a constant.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline bool Dec_TreeIsConst( Vec_Int_t * vForm )             {   return Dec_NodeReadLast(vForm)->fConst;  }
static inline bool Dec_TreeIsConst0( Vec_Int_t * vForm )            {   return Dec_NodeReadLast(vForm)->fConst &&  Dec_NodeReadLast(vForm)->fCompl;  }
static inline bool Dec_TreeIsConst1( Vec_Int_t * vForm )            {   return Dec_NodeReadLast(vForm)->fConst && !Dec_NodeReadLast(vForm)->fCompl;  }

/**Function*************************************************************

  Synopsis    [Creates a constant 0 decomposition tree.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Int_t * Dec_TreeCreateConst0()
{
    Vec_Int_t * vForm;
    Dec_Node_t * pNode;
    // create the constant node
    vForm = Vec_IntAlloc( 1 );
    Vec_IntPush( vForm, 0 );
    pNode = Dec_NodeReadLast( vForm );
    pNode->fIntern = 1;
    pNode->fConst  = 1;
    pNode->fCompl  = 1;
    return vForm;
}

/**Function*************************************************************

  Synopsis    [Creates a constant 1 decomposition tree.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Int_t * Dec_TreeCreateConst1()
{
    Vec_Int_t * vForm;
    Dec_Node_t * pNode;
    // create the constant node
    vForm = Vec_IntAlloc( 1 );
    Vec_IntPush( vForm, 0 );
    pNode = Dec_NodeReadLast( vForm );
    pNode->fIntern = 1;
    pNode->fConst  = 1;
    pNode->fCompl  = 0;
    return vForm;
}


/**Function*************************************************************

  Synopsis    [Checks if the decomposition tree is an elementary var.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline bool Dec_TreeIsVar( Vec_Int_t * vForm )
{
    return Dec_NodeReadLast(vForm)->iFanin0 == Dec_NodeReadLast(vForm)->iFanin1;
}

/**Function*************************************************************

  Synopsis    [Creates the decomposition tree to represent an elementary var.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Vec_Int_t * Dec_TreeCreateVar( int iVar, int nVars, int fCompl )
{
    Vec_Int_t * vForm;
    Dec_Node_t * pNode;
    // create the elementary variable node
    vForm = Vec_IntAlloc( nVars + 1 );
    Vec_IntFill( vForm, nVars + 1, 0 );
    pNode = Dec_NodeReadLast( vForm );
    pNode->iFanin0 = iVar;
    pNode->iFanin1 = iVar;
    pNode->fIntern = 1;
    pNode->fCompl  = fCompl;
    return vForm;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

