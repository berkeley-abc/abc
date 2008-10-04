/**CFile****************************************************************

  FileName    [sswSimSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [Performs resimulation using counter-examples.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswSimSat.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Handle the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManResimulateBit( Ssw_Man_t * p, Aig_Obj_t * pCand, Aig_Obj_t * pRepr )
{
    Aig_Obj_t * pObj;
    int i, RetValue1, RetValue2, clk = clock();
    // set the PI simulation information
    Aig_ManConst1(p->pAig)->fMarkB = 1;
    Aig_ManForEachPi( p->pAig, pObj, i )
        pObj->fMarkB = Aig_InfoHasBit( p->pPatWords, i );
    // simulate internal nodes
    Aig_ManForEachNode( p->pAig, pObj, i )
        pObj->fMarkB = ( Aig_ObjFanin0(pObj)->fMarkB ^ Aig_ObjFaninC0(pObj) )
                     & ( Aig_ObjFanin1(pObj)->fMarkB ^ Aig_ObjFaninC1(pObj) );
    // check equivalence classes
    RetValue1 = Ssw_ClassesRefineConst1( p->ppClasses, 0 );
    RetValue2 = Ssw_ClassesRefine( p->ppClasses, 0 );
    // make sure refinement happened
    if ( Aig_ObjIsConst1(pRepr) ) 
    {
        assert( RetValue1 );
        if ( RetValue1 == 0 )
            printf( "\nSsw_ManResimulateBit() Error: RetValue1 does not hold.\n" );
    }
    else
    {
        assert( RetValue2 );
        if ( RetValue2 == 0 )
            printf( "\nSsw_ManResimulateBit() Error: RetValue2 does not hold.\n" );
    }
p->timeSimSat += clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Verifies the result of simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManResimulateWordVerify( Ssw_Man_t * p, int f )
{
    Aig_Obj_t * pObj, * pObjFraig;
    unsigned uWord;
    int Value1, Value2;
    int i, nVarNum, Counter = 0;
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        pObjFraig = Ssw_ObjFrame( p, pObj, f );
        if ( pObjFraig == NULL )
            continue;
        nVarNum = Ssw_ObjSatNum( p, Aig_Regular(pObjFraig) );
        if ( nVarNum == 0 )
            continue;
        Value1 = Ssw_ManGetSatVarValue( p, pObj, f );
        uWord  = Ssw_SmlObjGetWord( p->pSml, pObj, 0, 0 );
        Value2 = ((uWord != 0) ^ pObj->fPhase);
        Counter += (Value1 != Value2);
        if ( Value1 != Value2 )
        {
/*
            int Value1f = Ssw_ManGetSatVarValue( p, Aig_ObjFanin0(pObj), f );
            int Value2f = Ssw_ManGetSatVarValue( p, Aig_ObjFanin1(pObj), f );
*/
            int x = 0;
            int Value3 = Ssw_ManGetSatVarValue( p, pObj, f );
        }
    }
    if ( Counter )
        printf( "Counter = %d.\n", Counter );
}

/**Function*************************************************************

  Synopsis    [Handle the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManResimulateWord( Ssw_Man_t * p, Aig_Obj_t * pCand, Aig_Obj_t * pRepr, int f )
{
    int RetValue1, RetValue2, clk = clock();
    // set the PI simulation information
    Ssw_SmlAssignDist1Plus( p->pSml, p->pPatWords );
    // simulate internal nodes
    Ssw_SmlSimulateOne( p->pSml );
    Ssw_ManResimulateWordVerify( p, f );

    // check equivalence classes
    RetValue1 = Ssw_ClassesRefineConst1( p->ppClasses, 1 );
    RetValue2 = Ssw_ClassesRefine( p->ppClasses, 1 );
    // make sure refinement happened
    if ( Aig_ObjIsConst1(pRepr) )
    {
        assert( RetValue1 );
        if ( RetValue1 == 0 )
            printf( "\nSsw_ManResimulateWord() Error: RetValue1 does not hold.\n" );
    }
    else
    {
        assert( RetValue2 );
        if ( RetValue2 == 0 )
            printf( "\nSsw_ManResimulateWord() Error: RetValue2 does not hold.\n" );
    }
p->timeSimSat += clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Handle the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManResimulateWord2( Ssw_Man_t * p, Aig_Obj_t * pCand, Aig_Obj_t * pRepr, int f )
{
    int RetValue1, RetValue2, clk = clock();
    // set the PI simulation information
    Ssw_SmlAssignDist1Plus( p->pSml, p->pPatWords2 );
    // simulate internal nodes
    Ssw_SmlSimulateOne( p->pSml );
    Ssw_ManResimulateWordVerify( p, f );

    // check equivalence classes
    RetValue1 = Ssw_ClassesRefineConst1( p->ppClasses, 1 );
    RetValue2 = Ssw_ClassesRefine( p->ppClasses, 1 );
    // make sure refinement happened
    if ( Aig_ObjIsConst1(pRepr) )
    {
        assert( RetValue1 );
        if ( RetValue1 == 0 )
            printf( "\nSsw_ManResimulateWord() Error: RetValue1 does not hold.\n" );
    }
    else
    {
        assert( RetValue2 );
        if ( RetValue2 == 0 )
            printf( "\nSsw_ManResimulateWord() Error: RetValue2 does not hold.\n" );
    }
p->timeSimSat += clock() - clk;

}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


