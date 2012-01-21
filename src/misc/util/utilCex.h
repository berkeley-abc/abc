/**CFile****************************************************************

  FileName    [utilCex.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Handling sequential counter-examples.]

  Synopsis    [Handling sequential counter-examples.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Feburary 13, 2011.]

  Revision    [$Id: utilCex.h,v 1.00 2011/02/11 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__misc__util__utilCex_h
#define ABC__misc__util__utilCex_h

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// sequential counter-example
typedef struct Abc_Cex_t_ Abc_Cex_t;
struct Abc_Cex_t_
{
    int              iPo;       // the zero-based number of PO, for which verification failed
    int              iFrame;    // the zero-based number of the time-frame, for which verificaiton failed
    int              nRegs;     // the number of registers in the miter 
    int              nPis;      // the number of primary inputs in the miter
    int              nBits;     // the number of words of bit data used
    unsigned         pData[0];  // the cex bit data (the number of bits: nRegs + (iFrame+1) * nPis)
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== utilCex.c ===========================================================*/
extern Abc_Cex_t *   Abc_CexAlloc( int nRegs, int nTruePis, int nFrames );
extern Abc_Cex_t *   Abc_CexMakeTriv( int nRegs, int nTruePis, int nTruePos, int iFrameOut );
extern Abc_Cex_t *   Abc_CexCreate( int nRegs, int nTruePis, int * pArray, int iFrame, int iPo, int fSkipRegs );
extern Abc_Cex_t *   Abc_CexDup( Abc_Cex_t * p, int nRegsNew );
extern Abc_Cex_t *   Abc_CexDeriveFromCombModel( int * pModel, int nPis, int nRegs, int iPo );
extern void          Abc_CexPrintStats( Abc_Cex_t * p );
extern void          Abc_CexPrint( Abc_Cex_t * p );
extern void          Abc_CexFreeP( Abc_Cex_t ** p );
extern void          Abc_CexFree( Abc_Cex_t * p );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
