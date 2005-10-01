/**CFile****************************************************************

  FileName    [npn.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName []

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: npn.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __NPN_H__
#define __NPN_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

#define EXTRA_WORD_VARS     5

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DEFINITIONS                          ///
////////////////////////////////////////////////////////////////////////

static inline int Extra_BitCharNum( int nVars )  {  if ( nVars <= 3 )  return 1;                return 1 << (nVars - 3); }
static inline int Extra_BitWordNum( int nVars )  {  if ( nVars <= EXTRA_WORD_VARS )  return 1;  return 1 << (nVars - EXTRA_WORD_VARS); }

static inline int  Extra_BitRead( uint8 * pBits, int iBit )  { return ( (pBits[iBit/8] & (1 << (iBit%8))) > 0 ); }
static inline void Extra_BitSet( uint8 * pBits, int iBit )   { pBits[iBit/8] |= (1 << (iBit%8));                 }
static inline void Extra_BitXor( uint8 * pBits, int iBit )   { pBits[iBit/8] ^= (1 << (iBit%8));                 }

static inline void Extra_BitClean( int nVars, uint8 * pBits )
{
    unsigned * pWords = (unsigned *)pBits;
    int i;
    for ( i = Extra_BitWordNum(nVars) - 1; i >= 0; i-- )
        pWords[i] = 0;
}
static inline void Extra_BitNot( int nVars, uint8 * pBits )
{
    unsigned * pWords = (unsigned *)pBits;
    int i;
    for ( i = Extra_BitWordNum(nVars) - 1; i >= 0; i-- )
        pWords[i] = ~pWords[i];
}
static inline void Extra_BitCopy( int nVars, uint8 * pBits1, uint8 * pBits )
{
    unsigned * pWords  = (unsigned *)pBits;
    unsigned * pWords1 = (unsigned *)pBits1;
    int i;
    for ( i = Extra_BitWordNum(nVars) - 1; i >= 0; i-- )
        pWords[i] = pWords1[i];
}
static inline void Extra_BitAnd( int nVars, uint8 * pBits1, uint8 * pBits2, uint8 * pBits )
{
    unsigned * pWords  = (unsigned *)pBits;
    unsigned * pWords1 = (unsigned *)pBits1;
    unsigned * pWords2 = (unsigned *)pBits2;
    int i;
    for ( i = Extra_BitWordNum(nVars) - 1; i >= 0; i-- )
        pWords[i] = pWords1[i] & pWords2[i];
}
static inline void Extra_BitSharp( int nVars, uint8 * pBits1, uint8 * pBits2, uint8 * pBits )
{
    unsigned * pWords  = (unsigned *)pBits;
    unsigned * pWords1 = (unsigned *)pBits1;
    unsigned * pWords2 = (unsigned *)pBits2;
    int i;
    for ( i = Extra_BitWordNum(nVars) - 1; i >= 0; i-- )
        pWords[i] = pWords1[i] & ~pWords2[i];
}

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== zzz.c ==========================================================*/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

