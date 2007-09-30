/**CFile****************************************************************

  FileName    [darScript.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Rewriting scripts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darScript.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "darInt.h"
//#include "ioa.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs one iteration of AIG rewriting.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dar_ManRewriteDefault( Aig_Man_t * pAig )
{
    Aig_Man_t * pTemp;
    Dar_RwrPar_t Pars, * pPars = &Pars;
    Dar_ManDefaultRwrParams( pPars );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    Dar_ManRewrite( pAig, pPars );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    return pAig;
}

/**Function*************************************************************

  Synopsis    [Reproduces script "compress2".]

  Description []
               
  SideEffects [This procedure does not tighten level during restructuring.]

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dar_ManRwsat( Aig_Man_t * pAig, int fBalance, int fVerbose )
//alias rwsat       "st; rw -l; b -l; rw -l; rf -l"
{
    Aig_Man_t * pTemp;

    Dar_RwrPar_t ParsRwr, * pParsRwr = &ParsRwr;
    Dar_RefPar_t ParsRef, * pParsRef = &ParsRef;

    Dar_ManDefaultRwrParams( pParsRwr );
    Dar_ManDefaultRefParams( pParsRef );

    pParsRwr->fUpdateLevel = 0;
    pParsRef->fUpdateLevel = 0;

    pParsRwr->fVerbose = fVerbose;
    pParsRef->fVerbose = fVerbose;

    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    // balance
    if ( fBalance )
    {
    pAig = Dar_ManBalance( pTemp = pAig, 0 );
    Aig_ManStop( pTemp );
    }
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );

    return pAig;
}


/**Function*************************************************************

  Synopsis    [Reproduces script "compress".]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dar_ManCompress( Aig_Man_t * pAig, int fBalance, int fUpdateLevel, int fVerbose )
//alias compress2   "b -l; rw -l; rwz -l; b -l; rwz -l; b -l"
{
    Aig_Man_t * pTemp;

    Dar_RwrPar_t ParsRwr, * pParsRwr = &ParsRwr;
    Dar_RefPar_t ParsRef, * pParsRef = &ParsRef;

    Dar_ManDefaultRwrParams( pParsRwr );
    Dar_ManDefaultRefParams( pParsRef );

    pParsRwr->fUpdateLevel = fUpdateLevel;
    pParsRef->fUpdateLevel = fUpdateLevel;

    pParsRwr->fVerbose = 0;//fVerbose;
    pParsRef->fVerbose = 0;//fVerbose;

    pAig = Aig_ManDup( pAig, 0 ); 
    if ( fVerbose ) Aig_ManPrintStats( pAig );

    // balance
    if ( fBalance )
    {
//    pAig = Dar_ManBalance( pTemp = pAig, fUpdateLevel );
//    Aig_ManStop( pTemp );
//    if ( fVerbose ) Aig_ManPrintStats( pAig );
    }
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );

    // balance
    if ( fBalance )
    {
    pAig = Dar_ManBalance( pTemp = pAig, fUpdateLevel );
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );
    }

    pParsRwr->fUseZeros = 1;
    pParsRef->fUseZeros = 1;
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );

    return pAig;
}

/**Function*************************************************************

  Synopsis    [Reproduces script "compress2".]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dar_ManCompress2( Aig_Man_t * pAig, int fBalance, int fUpdateLevel, int fVerbose )
//alias compress2   "b -l; rw -l; rf -l; b -l; rw -l; rwz -l; b -l; rfz -l; rwz -l; b -l"
{
    Aig_Man_t * pTemp;

    Dar_RwrPar_t ParsRwr, * pParsRwr = &ParsRwr;
    Dar_RefPar_t ParsRef, * pParsRef = &ParsRef;

    Dar_ManDefaultRwrParams( pParsRwr );
    Dar_ManDefaultRefParams( pParsRef );

    pParsRwr->fUpdateLevel = fUpdateLevel;
    pParsRef->fUpdateLevel = fUpdateLevel;

    pParsRwr->fVerbose = 0;//fVerbose;
    pParsRef->fVerbose = 0;//fVerbose;

    pAig = Aig_ManDup( pAig, 0 ); 
    if ( fVerbose ) Aig_ManPrintStats( pAig );

    // balance
    if ( fBalance )
    {
//    pAig = Dar_ManBalance( pTemp = pAig, fUpdateLevel );
//    Aig_ManStop( pTemp );
//    if ( fVerbose ) Aig_ManPrintStats( pAig );
    }
    

    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );

    // balance
//    if ( fBalance )
    {
    pAig = Dar_ManBalance( pTemp = pAig, fUpdateLevel );
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );
    }
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );

    pParsRwr->fUseZeros = 1;
    pParsRef->fUseZeros = 1;
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );

    // balance
    if ( fBalance )
    {
    pAig = Dar_ManBalance( pTemp = pAig, fUpdateLevel );
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );
    }
    
    // refactor
    Dar_ManRefactor( pAig, pParsRef );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );
    
    // rewrite
    Dar_ManRewrite( pAig, pParsRwr );
    pAig = Aig_ManDup( pTemp = pAig, 0 ); 
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );

    // balance
    if ( fBalance )
    {
    pAig = Dar_ManBalance( pTemp = pAig, fUpdateLevel );
    Aig_ManStop( pTemp );
    if ( fVerbose ) Aig_ManPrintStats( pAig );
    }
    return pAig;
}

/**Function*************************************************************

  Synopsis    [Reproduces script "compress2".]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Dar_ManChoiceSynthesis( Aig_Man_t * pAig, int fBalance, int fUpdateLevel, int fVerbose )
//alias resyn    "b; rw; rwz; b; rwz; b"
//alias resyn2   "b; rw; rf; b; rw; rwz; b; rfz; rwz; b"
{
    Vec_Ptr_t * vAigs;
    vAigs = Vec_PtrAlloc( 3 );
    pAig = Aig_ManDup(pAig, 0);
    Vec_PtrPush( vAigs, pAig );
    pAig = Dar_ManCompress (pAig, 0, fUpdateLevel, fVerbose);
    Vec_PtrPush( vAigs, pAig );
    pAig = Dar_ManCompress2(pAig, fBalance, fUpdateLevel, fVerbose);
    Vec_PtrPush( vAigs, pAig );
    return vAigs;
}

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*
Vec_Ptr_t * Dar_ManChoiceSynthesisExt()
{
    Vec_Ptr_t * vAigs;
    Aig_Man_t * pMan;
    vAigs = Vec_PtrAlloc( 3 );
    pMan = Ioa_ReadAiger( "i10_1.aig", 1 );
    Vec_PtrPush( vAigs, pMan );
    pMan = Ioa_ReadAiger( "i10_2.aig", 1 );
    Vec_PtrPush( vAigs, pMan );
    pMan = Ioa_ReadAiger( "i10_3.aig", 1 );
    Vec_PtrPush( vAigs, pMan );
    return vAigs;
}
*/

/**Function*************************************************************

  Synopsis    [Reproduces script "compress2".]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dar_ManChoice( Aig_Man_t * pAig, int fBalance, int fUpdateLevel, int fVerbose )
{
/*
    Aig_Man_t * pMan, * pTemp;
    Vec_Ptr_t * vAigs;
    int i, clk;

clk = clock();
//    vAigs = Dar_ManChoiceSynthesisExt();
    vAigs = Dar_ManChoiceSynthesis( pAig, fBalance, fUpdateLevel, fVerbose );

    // swap the first and last network
    // this should lead to the primary choice being "better" because of synthesis
    pMan = Vec_PtrPop( vAigs );
    Vec_PtrPush( vAigs, Vec_PtrEntry(vAigs,0) );
    Vec_PtrWriteEntry( vAigs, 0, pMan );

if ( fVerbose )
{
PRT( "Synthesis time", clock() - clk );
}
clk = clock();
    pMan = Aig_ManChoicePartitioned( vAigs, 300 );
    Vec_PtrForEachEntry( vAigs, pTemp, i )
        Aig_ManStop( pTemp );
    Vec_PtrFree( vAigs );
if ( fVerbose )
{
PRT( "Choicing time ", clock() - clk );
}
    return pMan;
*/
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


