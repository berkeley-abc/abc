/**CFile****************************************************************

  FileName    [darUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Various procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darUtil.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the structure with default assignment of parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Par_t * Dar_ManDefaultParams()
{
    Dar_Par_t * p;
    p = ALLOC( Dar_Par_t, 1 );
    memset( p, 0, sizeof(Dar_Par_t) );
    return p;
}

/**Function*************************************************************

  Synopsis    [Increments the current traversal ID of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManIncrementTravId( Dar_Man_t * p )
{
    if ( p->nTravIds >= (1<<30)-1 )
        Dar_ManCleanData( p );
    p->nTravIds++;
}

/**Function*************************************************************

  Synopsis    [Collect the latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManLevels( Dar_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i, LevelMax = 0;
    Dar_ManForEachPo( p, pObj, i )
        LevelMax = DAR_MAX( LevelMax, (int)Dar_ObjFanin0(pObj)->Level );
    return LevelMax;
}

/**Function*************************************************************

  Synopsis    [Cleans the data pointers for the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManCleanData( Dar_Man_t * p )
{
    Dar_Obj_t * pObj;
    int i;
    Dar_ManForEachObj( p, pObj, i )
        pObj->pData = NULL;
}

/**Function*************************************************************

  Synopsis    [Recursively cleans the data pointers in the cone of the node.]

  Description [Applicable to small AIGs only because no caching is performed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjCleanData_rec( Dar_Obj_t * pObj )
{
    assert( !Dar_IsComplement(pObj) );
    assert( !Dar_ObjIsPo(pObj) );
    if ( Dar_ObjIsAnd(pObj) )
    {
        Dar_ObjCleanData_rec( Dar_ObjFanin0(pObj) );
        Dar_ObjCleanData_rec( Dar_ObjFanin1(pObj) );
    }
    pObj->pData = NULL;
}

/**Function*************************************************************

  Synopsis    [Detects multi-input gate rooted at this node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjCollectMulti_rec( Dar_Obj_t * pRoot, Dar_Obj_t * pObj, Vec_Ptr_t * vSuper )
{
    if ( pRoot != pObj && (Dar_IsComplement(pObj) || Dar_ObjIsPi(pObj) || Dar_ObjType(pRoot) != Dar_ObjType(pObj)) )
    {
        Vec_PtrPushUnique(vSuper, pObj);
        return;
    }
    Dar_ObjCollectMulti_rec( pRoot, Dar_ObjChild0(pObj), vSuper );
    Dar_ObjCollectMulti_rec( pRoot, Dar_ObjChild1(pObj), vSuper );
}

/**Function*************************************************************

  Synopsis    [Detects multi-input gate rooted at this node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjCollectMulti( Dar_Obj_t * pRoot, Vec_Ptr_t * vSuper )
{
    assert( !Dar_IsComplement(pRoot) );
    Vec_PtrClear( vSuper );
    Dar_ObjCollectMulti_rec( pRoot, pRoot, vSuper );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node is the root of MUX or EXOR/NEXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ObjIsMuxType( Dar_Obj_t * pNode )
{
    Dar_Obj_t * pNode0, * pNode1;
    // check that the node is regular
    assert( !Dar_IsComplement(pNode) );
    // if the node is not AND, this is not MUX
    if ( !Dar_ObjIsAnd(pNode) )
        return 0;
    // if the children are not complemented, this is not MUX
    if ( !Dar_ObjFaninC0(pNode) || !Dar_ObjFaninC1(pNode) )
        return 0;
    // get children
    pNode0 = Dar_ObjFanin0(pNode);
    pNode1 = Dar_ObjFanin1(pNode);
    // if the children are not ANDs, this is not MUX
    if ( !Dar_ObjIsAnd(pNode0) || !Dar_ObjIsAnd(pNode1) )
        return 0;
    // otherwise the node is MUX iff it has a pair of equal grandchildren
    return (Dar_ObjFanin0(pNode0) == Dar_ObjFanin0(pNode1) && (Dar_ObjFaninC0(pNode0) ^ Dar_ObjFaninC0(pNode1))) || 
           (Dar_ObjFanin0(pNode0) == Dar_ObjFanin1(pNode1) && (Dar_ObjFaninC0(pNode0) ^ Dar_ObjFaninC1(pNode1))) ||
           (Dar_ObjFanin1(pNode0) == Dar_ObjFanin0(pNode1) && (Dar_ObjFaninC1(pNode0) ^ Dar_ObjFaninC0(pNode1))) ||
           (Dar_ObjFanin1(pNode0) == Dar_ObjFanin1(pNode1) && (Dar_ObjFaninC1(pNode0) ^ Dar_ObjFaninC1(pNode1)));
}


/**Function*************************************************************

  Synopsis    [Recognizes what nodes are inputs of the EXOR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ObjRecognizeExor( Dar_Obj_t * pObj, Dar_Obj_t ** ppFan0, Dar_Obj_t ** ppFan1 )
{
    Dar_Obj_t * p0, * p1;
    assert( !Dar_IsComplement(pObj) );
    if ( !Dar_ObjIsNode(pObj) )
        return 0;
    if ( Dar_ObjIsExor(pObj) )
    {
        *ppFan0 = Dar_ObjChild0(pObj);
        *ppFan1 = Dar_ObjChild1(pObj);
        return 1;
    }
    assert( Dar_ObjIsAnd(pObj) );
    p0 = Dar_ObjChild0(pObj);
    p1 = Dar_ObjChild1(pObj);
    if ( !Dar_IsComplement(p0) || !Dar_IsComplement(p1) )
        return 0;
    p0 = Dar_Regular(p0);
    p1 = Dar_Regular(p1);
    if ( !Dar_ObjIsAnd(p0) || !Dar_ObjIsAnd(p1) )
        return 0;
    if ( Dar_ObjFanin0(p0) != Dar_ObjFanin0(p1) || Dar_ObjFanin1(p0) != Dar_ObjFanin1(p1) )
        return 0;
    if ( Dar_ObjFaninC0(p0) == Dar_ObjFaninC0(p1) || Dar_ObjFaninC1(p0) == Dar_ObjFaninC1(p1) )
        return 0;
    *ppFan0 = Dar_ObjChild0(p0);
    *ppFan1 = Dar_ObjChild1(p0);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Recognizes what nodes are control and data inputs of a MUX.]

  Description [If the node is a MUX, returns the control variable C.
  Assigns nodes T and E to be the then and else variables of the MUX. 
  Node C is never complemented. Nodes T and E can be complemented.
  This function also recognizes EXOR/NEXOR gates as MUXes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_ObjRecognizeMux( Dar_Obj_t * pNode, Dar_Obj_t ** ppNodeT, Dar_Obj_t ** ppNodeE )
{
    Dar_Obj_t * pNode0, * pNode1;
    assert( !Dar_IsComplement(pNode) );
    assert( Dar_ObjIsMuxType(pNode) );
    // get children
    pNode0 = Dar_ObjFanin0(pNode);
    pNode1 = Dar_ObjFanin1(pNode);

    // find the control variable
    if ( Dar_ObjFanin1(pNode0) == Dar_ObjFanin1(pNode1) && (Dar_ObjFaninC1(pNode0) ^ Dar_ObjFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Dar_ObjFaninC1(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Dar_Not(Dar_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Dar_Not(Dar_ObjChild0(pNode0));//pNode1->p1);
            return Dar_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Dar_Not(Dar_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Dar_Not(Dar_ObjChild0(pNode1));//pNode2->p1);
            return Dar_ObjChild1(pNode0);//pNode1->p2;
        }
    }
    else if ( Dar_ObjFanin0(pNode0) == Dar_ObjFanin0(pNode1) && (Dar_ObjFaninC0(pNode0) ^ Dar_ObjFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Dar_ObjFaninC0(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Dar_Not(Dar_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Dar_Not(Dar_ObjChild1(pNode0));//pNode1->p2);
            return Dar_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Dar_Not(Dar_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Dar_Not(Dar_ObjChild1(pNode1));//pNode2->p2);
            return Dar_ObjChild0(pNode0);//pNode1->p1;
        }
    }
    else if ( Dar_ObjFanin0(pNode0) == Dar_ObjFanin1(pNode1) && (Dar_ObjFaninC0(pNode0) ^ Dar_ObjFaninC1(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p1) )
        if ( Dar_ObjFaninC0(pNode0) )
        { // pNode2->p2 is positive phase of C
            *ppNodeT = Dar_Not(Dar_ObjChild0(pNode1));//pNode2->p1);
            *ppNodeE = Dar_Not(Dar_ObjChild1(pNode0));//pNode1->p2);
            return Dar_ObjChild1(pNode1);//pNode2->p2;
        }
        else
        { // pNode1->p1 is positive phase of C
            *ppNodeT = Dar_Not(Dar_ObjChild1(pNode0));//pNode1->p2);
            *ppNodeE = Dar_Not(Dar_ObjChild0(pNode1));//pNode2->p1);
            return Dar_ObjChild0(pNode0);//pNode1->p1;
        }
    }
    else if ( Dar_ObjFanin1(pNode0) == Dar_ObjFanin0(pNode1) && (Dar_ObjFaninC1(pNode0) ^ Dar_ObjFaninC0(pNode1)) )
    {
//        if ( Fraig_IsComplement(pNode1->p2) )
        if ( Dar_ObjFaninC1(pNode0) )
        { // pNode2->p1 is positive phase of C
            *ppNodeT = Dar_Not(Dar_ObjChild1(pNode1));//pNode2->p2);
            *ppNodeE = Dar_Not(Dar_ObjChild0(pNode0));//pNode1->p1);
            return Dar_ObjChild0(pNode1);//pNode2->p1;
        }
        else
        { // pNode1->p2 is positive phase of C
            *ppNodeT = Dar_Not(Dar_ObjChild0(pNode0));//pNode1->p1);
            *ppNodeE = Dar_Not(Dar_ObjChild1(pNode1));//pNode2->p2);
            return Dar_ObjChild1(pNode0);//pNode1->p2;
        }
    }
    assert( 0 ); // this is not MUX
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_ObjReal_rec( Dar_Obj_t * pObj )
{
    Dar_Obj_t * pObjNew, * pObjR = Dar_Regular(pObj);
    if ( !Dar_ObjIsBuf(pObjR) )
        return pObj;
    pObjNew = Dar_ObjReal_rec( Dar_ObjChild0(pObjR) );
    return Dar_NotCond( pObjNew, Dar_IsComplement(pObj) );
}


/**Function*************************************************************

  Synopsis    [Prints Eqn formula for the AIG rooted at this node.]

  Description [The formula is in terms of PIs, which should have
  their names assigned in pObj->pData fields.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjPrintEqn( FILE * pFile, Dar_Obj_t * pObj, Vec_Vec_t * vLevels, int Level )
{
    Vec_Ptr_t * vSuper;
    Dar_Obj_t * pFanin;
    int fCompl, i;
    // store the complemented attribute
    fCompl = Dar_IsComplement(pObj);
    pObj = Dar_Regular(pObj);
    // constant case
    if ( Dar_ObjIsConst1(pObj) )
    {
        fprintf( pFile, "%d", !fCompl );
        return;
    }
    // PI case
    if ( Dar_ObjIsPi(pObj) )
    {
        fprintf( pFile, "%s%s", fCompl? "!" : "", pObj->pData );
        return;
    }
    // AND case
    Vec_VecExpand( vLevels, Level );
    vSuper = Vec_VecEntry(vLevels, Level);
    Dar_ObjCollectMulti( pObj, vSuper );
    fprintf( pFile, "%s", (Level==0? "" : "(") );
    Vec_PtrForEachEntry( vSuper, pFanin, i )
    {
        Dar_ObjPrintEqn( pFile, Dar_NotCond(pFanin, fCompl), vLevels, Level+1 );
        if ( i < Vec_PtrSize(vSuper) - 1 )
            fprintf( pFile, " %s ", fCompl? "+" : "*" );
    }
    fprintf( pFile, "%s", (Level==0? "" : ")") );
    return;
}

/**Function*************************************************************

  Synopsis    [Prints Verilog formula for the AIG rooted at this node.]

  Description [The formula is in terms of PIs, which should have
  their names assigned in pObj->pData fields.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjPrintVerilog( FILE * pFile, Dar_Obj_t * pObj, Vec_Vec_t * vLevels, int Level )
{
    Vec_Ptr_t * vSuper;
    Dar_Obj_t * pFanin, * pFanin0, * pFanin1, * pFaninC;
    int fCompl, i;
    // store the complemented attribute
    fCompl = Dar_IsComplement(pObj);
    pObj = Dar_Regular(pObj);
    // constant case
    if ( Dar_ObjIsConst1(pObj) )
    {
        fprintf( pFile, "1\'b%d", !fCompl );
        return;
    }
    // PI case
    if ( Dar_ObjIsPi(pObj) )
    {
        fprintf( pFile, "%s%s", fCompl? "~" : "", pObj->pData );
        return;
    }
    // EXOR case
    if ( Dar_ObjIsExor(pObj) )
    {
        Vec_VecExpand( vLevels, Level );
        vSuper = Vec_VecEntry( vLevels, Level );
        Dar_ObjCollectMulti( pObj, vSuper );
        fprintf( pFile, "%s", (Level==0? "" : "(") );
        Vec_PtrForEachEntry( vSuper, pFanin, i )
        {
            Dar_ObjPrintVerilog( pFile, Dar_NotCond(pFanin, (fCompl && i==0)), vLevels, Level+1 );
            if ( i < Vec_PtrSize(vSuper) - 1 )
                fprintf( pFile, " ^ " );
        }
        fprintf( pFile, "%s", (Level==0? "" : ")") );
        return;
    }
    // MUX case
    if ( Dar_ObjIsMuxType(pObj) )
    {
        if ( Dar_ObjRecognizeExor( pObj, &pFanin0, &pFanin1 ) )
        {
            fprintf( pFile, "%s", (Level==0? "" : "(") );
            Dar_ObjPrintVerilog( pFile, Dar_NotCond(pFanin0, fCompl), vLevels, Level+1 );
            fprintf( pFile, " ^ " );
            Dar_ObjPrintVerilog( pFile, pFanin1, vLevels, Level+1 );
            fprintf( pFile, "%s", (Level==0? "" : ")") );
        }
        else 
        {
            pFaninC = Dar_ObjRecognizeMux( pObj, &pFanin1, &pFanin0 );
            fprintf( pFile, "%s", (Level==0? "" : "(") );
            Dar_ObjPrintVerilog( pFile, pFaninC, vLevels, Level+1 );
            fprintf( pFile, " ? " );
            Dar_ObjPrintVerilog( pFile, Dar_NotCond(pFanin1, fCompl), vLevels, Level+1 );
            fprintf( pFile, " : " );
            Dar_ObjPrintVerilog( pFile, Dar_NotCond(pFanin0, fCompl), vLevels, Level+1 );
            fprintf( pFile, "%s", (Level==0? "" : ")") );
        }
        return;
    }
    // AND case
    Vec_VecExpand( vLevels, Level );
    vSuper = Vec_VecEntry(vLevels, Level);
    Dar_ObjCollectMulti( pObj, vSuper );
    fprintf( pFile, "%s", (Level==0? "" : "(") );
    Vec_PtrForEachEntry( vSuper, pFanin, i )
    {
        Dar_ObjPrintVerilog( pFile, Dar_NotCond(pFanin, fCompl), vLevels, Level+1 );
        if ( i < Vec_PtrSize(vSuper) - 1 )
            fprintf( pFile, " %s ", fCompl? "|" : "&" );
    }
    fprintf( pFile, "%s", (Level==0? "" : ")") );
    return;
}


/**Function*************************************************************

  Synopsis    [Prints node in HAIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ObjPrintVerbose( Dar_Obj_t * pObj, int fHaig )
{
    assert( !Dar_IsComplement(pObj) );
    printf( "Node %p : ", pObj );
    if ( Dar_ObjIsConst1(pObj) )
        printf( "constant 1" );
    else if ( Dar_ObjIsPi(pObj) )
        printf( "PI" );
    else
        printf( "AND( %p%s, %p%s )", 
            Dar_ObjFanin0(pObj), (Dar_ObjFaninC0(pObj)? "\'" : " "), 
            Dar_ObjFanin1(pObj), (Dar_ObjFaninC1(pObj)? "\'" : " ") );
    printf( " (refs = %3d)", Dar_ObjRefs(pObj) );
}

/**Function*************************************************************

  Synopsis    [Prints node in HAIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManPrintVerbose( Dar_Man_t * p, int fHaig )
{
    Vec_Ptr_t * vNodes;
    Dar_Obj_t * pObj;
    int i;
    printf( "PIs: " );
    Dar_ManForEachPi( p, pObj, i )
        printf( " %p", pObj );
    printf( "\n" );
    vNodes = Dar_ManDfs( p );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Dar_ObjPrintVerbose( pObj, fHaig ), printf( "\n" );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Writes the AIG into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManDumpBlif( Dar_Man_t * p, char * pFileName )
{
    FILE * pFile;
    Vec_Ptr_t * vNodes;
    Dar_Obj_t * pObj, * pConst1 = NULL;
    int i, nDigits, Counter = 0;
    if ( Dar_ManPoNum(p) == 0 )
    {
        printf( "Dar_ManDumpBlif(): AIG manager does not have POs.\n" );
        return;
    }
    // collect nodes in the DFS order
    vNodes = Dar_ManDfs( p );
    // assign IDs to objects
    Dar_ManConst1(p)->pData = (void *)Counter++;
    Dar_ManForEachPi( p, pObj, i )
        pObj->pData = (void *)Counter++;
    Dar_ManForEachPo( p, pObj, i )
        pObj->pData = (void *)Counter++;
    Vec_PtrForEachEntry( vNodes, pObj, i )
        pObj->pData = (void *)Counter++;
    nDigits = Extra_Base10Log( Counter );
    // write the file
    pFile = fopen( pFileName, "w" );
    fprintf( pFile, "# BLIF file written by procedure Dar_ManDumpBlif() in ABC\n" );
    fprintf( pFile, "# http://www.eecs.berkeley.edu/~alanmi/abc/\n" );
    fprintf( pFile, ".model test\n" );
    // write PIs
    fprintf( pFile, ".inputs" );
    Dar_ManForEachPi( p, pObj, i )
        fprintf( pFile, " n%0*d", nDigits, (int)pObj->pData );
    fprintf( pFile, "\n" );
    // write POs
    fprintf( pFile, ".outputs" );
    Dar_ManForEachPo( p, pObj, i )
        fprintf( pFile, " n%0*d", nDigits, (int)pObj->pData );
    fprintf( pFile, "\n" );
    // write nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        fprintf( pFile, ".names n%0*d n%0*d n%0*d\n", 
            nDigits, (int)Dar_ObjFanin0(pObj)->pData, 
            nDigits, (int)Dar_ObjFanin1(pObj)->pData, 
            nDigits, (int)pObj->pData );
        fprintf( pFile, "%d%d 1\n", !Dar_ObjFaninC0(pObj), !Dar_ObjFaninC1(pObj) );
    }
    // write POs
    Dar_ManForEachPo( p, pObj, i )
    {
        fprintf( pFile, ".names n%0*d n%0*d\n", 
            nDigits, (int)Dar_ObjFanin0(pObj)->pData, 
            nDigits, (int)pObj->pData );
        fprintf( pFile, "%d 1\n", !Dar_ObjFaninC0(pObj) );
        if ( Dar_ObjIsConst1(Dar_ObjFanin0(pObj)) )
            pConst1 = Dar_ManConst1(p);
    }
    if ( pConst1 )
        fprintf( pFile, ".names n%0*d\n 1\n", nDigits, (int)pConst1->pData );
    fprintf( pFile, ".end\n\n" );
    fclose( pFile );
    Vec_PtrFree( vNodes );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


