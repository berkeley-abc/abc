/**CFile****************************************************************

  FileName    [extraLutCas.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [LUT cascade decomposition.]

  Description [LUT cascade decomposition.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 6, 2024.]

  Revision    [$Id: extraLutCas.h,v 1.00 2024/08/06 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__misc__extra__extra_lutcas_h
#define ABC__misc__extra__extra_lutcas_h

#ifdef _WIN32
#define inline __inline // compatible with MS VS 6.0
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "bdd/cudd/cuddInt.h"

ABC_NAMESPACE_HEADER_START

/*
    The decomposed structure of the LUT cascade is represented as an array of 64-bit integers (words).
    The first word in the record is the number of LUT info blocks in the record, which follow one by one.
    Each LUT info block contains the following:
    - the number of words in this block
    - the number of fanins
    - the list of fanins
    - the variable ID of the output (can be one of the fanin variables)
    - truth tables (one word for 6 vars or less; more words as needed for more than 6 vars)
    For a 6-input node, the LUT info block takes 10 words (block size, fanin count, 6 fanins, output ID, truth table).
    For a 4-input node, the LUT info block takes  8 words (block size, fanin count, 4 fanins, output ID, truth table).
    If the LUT cascade contains a 6-LUT followed by a 4-LUT, the record contains 1+10+8=19 words.
*/

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word * Abc_LutCascade( Mini_Aig_t * p, int nLutSize, int fVerbose )
{
    word * pLuts = NULL;
    return pLuts;
}

ABC_NAMESPACE_HEADER_END

#endif /* __EXTRA_H__ */
