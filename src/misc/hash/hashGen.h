/**CFile****************************************************************

  FileName    [vecGen.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hash maps.]

  Synopsis    [Hash maps.]

  Author      [Aaron P. Hurst, Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Jan 26, 2011.]

  Revision    [$Id: vecGen.h,v 1.00 2005/06/20 00:00:00 ahurst Exp $]

***********************************************************************/
 
#ifndef __HASH_GEN_H__
#define __HASH_GEN_H__


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include "extra.h"

ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Hash_Gen_t_       Hash_Gen_t;
typedef struct Hash_Gen_Entry_t_ Hash_Gen_Entry_t;

struct Hash_Gen_Entry_t_
{
  char *                          key;
  void *                          data;
  struct Hash_Gen_Entry_t_ *     pNext;
};

struct Hash_Gen_t_ 
{
  int                             nSize;
  int                             nBins;
  int (* fHash)(void * key, int nBins);
  int (* fComp)(void * key, void * key);
  Hash_Gen_Entry_t **            pArray;
};



////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#define Hash_GenForEachEntry( pHash, pEntry, bin )   \
  for(bin=-1, pEntry=NULL; bin < pHash->nBins; (!pEntry)?(pEntry=pHash->pArray[++bin]):(pEntry=pEntry->pNext)) \
    if (pEntry)

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Default hash function for strings.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Hash_DefaultHashFuncStr( void * key, int nBins )
{
    int i, Value = 0;
    if ( key[0] == 0 )
        return 0;
    for ( i = strlen(key)-1; i >= 0; i-- )
        Value = 5 * Value + key[i];
    return Value % nBins;
}

/**Function*************************************************************

  Synopsis    [Allocates a hash map with the given number of bins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Hash_Gen_t * Hash_GenAlloc( 
  int nBins, 
  int (*Hash_FuncHash)(void *, int), 
  int (*Hash_FuncComp)(void *, void *) )
{
  Hash_Gen_t * p;
  int i;
  assert(nBins > 0);
  p = ABC_CALLOC( Hash_Gen_t, 1 );
  p->nBins  = nBins;
  p->fHash  = Hash_FuncHash? Hash_FuncHash : (int (*)(void *, int))Hash_DefaultHashFuncStr;
  p->fComp  = Hash_FuncComp? Hash_FuncComp : (int (*)(void *, void *))strcmp;
  p->nSize  = 0;
  p->pArray = ABC_CALLOC( Hash_Gen_Entry_t *, nBins );
  return p;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if a key already exists.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Hash_GenExists( Hash_Gen_t *p, void * key )
{
  int bin;
  Hash_Gen_Entry_t *pEntry;

  // find the bin where this key would live
  bin = (*(p->fHash))(key, p->nBins);

  // search for key
  pEntry = p->pArray[bin];
  while(pEntry) {
    if ( !p->fComp(pEntry->key,key) ) {
      return 1;
    }
    pEntry = pEntry->pNext;
  }

  return 0;
}

/**Function*************************************************************

  Synopsis    [Finds or creates an entry with a key and writes value.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Hash_GenWriteEntry( Hash_Gen_t *p, void * key, void * data )
{
  int bin;
  Hash_Gen_Entry_t *pEntry, **pLast;

  // find the bin where this key would live
  bin = (*(p->fHash))(key, p->nBins);

  // search for key
  pLast = &(p->pArray[bin]);
  pEntry = p->pArray[bin];
  while(pEntry) {
    if ( !p->fComp(pEntry->key,key) ) {
      pEntry->data = data;
      return;
    }
    pLast = &(pEntry->pNext);
    pEntry = pEntry->pNext;
  }

  // this key does not currently exist
  // create a new entry and add to bin
  p->nSize++;
  (*pLast) = pEntry = ABC_ALLOC( Hash_Gen_Entry_t, 1 );
  pEntry->pNext = NULL;
  pEntry->key  = key;
  pEntry->data = data;

  return;
}


/**Function*************************************************************

  Synopsis    [Finds or creates an entry with a key.]

  Description [fCreate specifies whether a new entry should be created.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void * Hash_GenEntry( Hash_Gen_t *p, void * key, int fCreate )
{
  int bin;
  Hash_Gen_Entry_t *pEntry, **pLast;

  // find the bin where this key would live
  bin = (*(p->fHash))(key, p->nBins);

  // search for key
  pLast = &(p->pArray[bin]);
  pEntry = p->pArray[bin];
  while(pEntry) {
    if ( !p->fComp(pEntry->key,key) )
      return pEntry->data;
    pLast = &(pEntry->pNext);
    pEntry = pEntry->pNext;
  }

  // this key does not currently exist
  if (fCreate) {
    // create a new entry and add to bin
    p->nSize++;
    (*pLast) = pEntry = ABC_ALLOC( Hash_Gen_Entry_t, 1 );
    pEntry->pNext = NULL;
    pEntry->key  = key;
    pEntry->data = NULL;
    return pEntry->data;
  }

  return NULL;
}


/**Function*************************************************************

  Synopsis    [Finds or creates an entry with a key and returns the pointer to it.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void** Hash_GenEntryPtr( Hash_Gen_t *p, void * key )
{
  int bin;
  Hash_Gen_Entry_t *pEntry, **pLast;

  // find the bin where this key would live
  bin = (*(p->fHash))(key, p->nBins);

  // search for key
  pLast = &(p->pArray[bin]);
  pEntry = p->pArray[bin];
  while(pEntry) {
    if ( !p->fComp(pEntry->key,key) )
      return &(pEntry->data);
    pLast = &(pEntry->pNext);
    pEntry = pEntry->pNext;
  }

  // this key does not currently exist
  // create a new entry and add to bin
  p->nSize++;
  (*pLast) = pEntry = ABC_ALLOC( Hash_Gen_Entry_t, 1 );
  pEntry->pNext = NULL;
  pEntry->key  = key;
  pEntry->data = NULL;

  return &(pEntry->data);
}

/**Function*************************************************************

  Synopsis    [Deletes an entry.]

  Description [Returns data, if there was any.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void* Hash_GenRemove( Hash_Gen_t *p, void * key )
{
  int    bin;
  void * data;
  Hash_Gen_Entry_t *pEntry, **pLast;

  // find the bin where this key would live
  bin = (*(p->fHash))(key, p->nBins);

  // search for key
  pLast = &(p->pArray[bin]);
  pEntry = p->pArray[bin];
  while(pEntry) {
    if ( !p->fComp(pEntry->key,key) ) {
      p->nSize--;
      data = pEntry->data;
      *pLast = pEntry->pNext;
      return data;
    }
    pLast = &(pEntry->pNext);
    pEntry = pEntry->pNext;
  }
    
  // could not find key
  return NULL;
}

/**Function*************************************************************

  Synopsis    [Frees the hash.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Hash_GenFree( Hash_Gen_t *p ) 
{
  int bin;
  Hash_Gen_Entry_t *pEntry, *pTemp;

  // free bins
  for(bin = 0; bin < p->nBins; bin++) {
    pEntry = p->pArray[bin];
    while(pEntry) {
      pTemp = pEntry;
      pEntry = pEntry->pNext;
      ABC_FREE( pTemp );
    }
  }
 
  // free hash
  ABC_FREE( p->pArray );
  ABC_FREE( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



ABC_NAMESPACE_HEADER_END

#endif
