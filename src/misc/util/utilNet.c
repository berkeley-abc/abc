/**CFile****************************************************************

  FileName    [utilNet.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network synthesis.]

  Synopsis    [Network synthesis.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: utilNet.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <time.h>

#include "abc_global.h"

ABC_NAMESPACE_IMPL_START

// the max number of nodes
#define MSIZE 15

/*************************************************************
                 literal manipulation, etc
**************************************************************/
 
 // operations on variables and literals
static inline int  tn_v2l( int Var, int c )    { assert(Var >= 0 && !(c >> 1)); return Var + Var + c; }
static inline int  tn_l2v( int Lit )           { assert(Lit >= 0); return Lit >> 1;                   }
static inline int  tn_l2c( int Lit )           { assert(Lit >= 0); return Lit & 1;                    }
static inline int  tn_lnot( int Lit )          { assert(Lit >= 0); return Lit ^ 1;                    }
static inline int  tn_lnotc( int Lit, int c )  { assert(Lit >= 0); return Lit ^ (int)(c > 0);         }
static inline int  tn_lreg( int Lit )          { assert(Lit >= 0); return Lit & ~01;                  }

// min/max/abs
static inline int  tn_abs( int a        )      { return a < 0 ? -a : a;                               }
static inline int  tn_max( int a, int b )      { return a > b ?  a : b;                               }
static inline int  tn_min( int a, int b )      { return a < b ?  a : b;                               }

// swapping two variables
#define TN_SWAP(Type, a, b)  { Type t = a; a = b; b = t; }

/*************************************************************
                 Vector of 32-bit integers
**************************************************************/

typedef struct tn_vi_ {
    int    size;
    int    cap;
    int*   ptr;
} tn_vi;

// iterator through the entries in the vector
#define tn_vi_for_each_entry( v, entry, i ) \
    for (i = 0; (i < (v)->size) && (((entry) = tn_vi_read((v), i)), 1); i++)
#define tn_vi_for_each_set( v, size, i )    \
    for (i = 0; (i < (v)->size) && (((size) = tn_vi_read((v), i++)), 1); i += size)

static inline void   tn_vi_start  (tn_vi* v, int cap)        { v->size = 0; v->cap = cap; v->ptr  = (int*)malloc( sizeof(int)*v->cap); }
static inline void   tn_vi_stop   (tn_vi* v)                 { if ( v->ptr ) free(v->ptr);                    }
static inline tn_vi* tn_vi_alloc  (int cap)                  { tn_vi* v = (tn_vi *)malloc(sizeof(tn_vi)); tn_vi_start(v, cap); return v; }
static inline void   tn_vi_free   (tn_vi* v)                 { if ( v->ptr ) free(v->ptr); free(v);           }
static inline int*   tn_vi_array  (tn_vi* v)                 { return v->ptr;                                 }
static inline int    tn_vi_read   (tn_vi* v, int k)          { assert(k < v->size); return v->ptr[k];         }
static inline void   tn_vi_write  (tn_vi* v, int k, int e)   { assert(k < v->size); v->ptr[k] = e;            }
static inline int    tn_vi_size   (tn_vi* v)                 { return v->size;                                }
static inline void   tn_vi_resize (tn_vi* v, int k)          { assert(k <= v->size); v->size = k;             } // only safe to shrink !!
static inline int    tn_vi_pop    (tn_vi* v)                 { assert(v->size > 0); return v->ptr[--v->size]; }
static inline void   tn_vi_grow   (tn_vi* v) 
{
    if (v->size < v->cap)
        return;
    int newcap = (v->cap < 4) ? 8 : (v->cap / 2) * 3;
    v->ptr = (int*)realloc( v->ptr, sizeof(int)*newcap );
    if ( v->ptr == NULL )
    {
        printf( "Failed to realloc memory from %.1f MB to %.1f MB.\n", 4.0 * v->cap / (1<<20), 4.0 * newcap / (1<<20) );
        fflush( stdout );
    }
    v->cap = newcap; 
}
static inline void tn_vi_push  (tn_vi* v, int e)           { tn_vi_grow(v);  v->ptr[v->size++] = e;          }
static inline void tn_vi_fill  (tn_vi* v, int n, int fill) { int i; tn_vi_resize(v, 0); for (i = 0; i < n; i++) tn_vi_push(v, fill); }
static inline int  tn_vi_remove(tn_vi* v, int e)
{
    int j;
    for ( j = 0; j < v->size; j++ )
        if ( v->ptr[j] == e )
            break;
    if ( j == v->size ) 
        return 0;
    for ( ; j < v->size-1; j++ ) 
        v->ptr[j] = v->ptr[j+1];
    tn_vi_resize( v, v->size-1 );
    return 1;
}
static inline tn_vi * tn_vi_dup(tn_vi* v) {
  tn_vi * p = tn_vi_alloc(v->size);
  p->size = v->size;
  memmove(p->ptr, v->ptr, sizeof(int)*p->size);
  return p;
}
static inline void  tn_vi_print(tn_vi* v) {
    printf( "Array with %d entries:", v->size ); int i, entry;
    tn_vi_for_each_entry( v, entry, i )
        printf( " %d", entry );
    printf( "\n" );
}
static inline void  tn_vi_print_sets(tn_vi* v) {
    int i, k, size, count = 0;
    tn_vi_for_each_set( v, size, i )
      count++;
    printf( "Array with %d sets:\n", count );
    count = 0;
    tn_vi_for_each_set( v, size, i ) {
      printf( "Set %3d : ", count );
      printf( "Size %3d  :", size );
      for ( k = 0; k < size; k++ )
        printf( " %d", tn_vi_read(v, i+k) );
      printf( "\n" );
      count++;
    }
}

/*************************************************************
                 counting wall time
**************************************************************/

static inline iword Tn_Clock()
{
#if defined(__APPLE__) && defined(__MACH__)
  #define APPLE_MACH (__APPLE__ & __MACH__)
#else
  #define APPLE_MACH 0
#endif
#if (defined(LIN) || defined(LIN64)) && !APPLE_MACH && !defined(__MINGW32__)
    struct timespec ts;
    if ( clock_gettime(CLOCK_MONOTONIC, &ts) < 0 ) 
        return (iword)-1;
    iword res = ((iword) ts.tv_sec) * CLOCKS_PER_SEC;
    res += (((iword) ts.tv_nsec) * CLOCKS_PER_SEC) / 1000000000;
    return res;
#else
    return (iword) clock();
#endif
}
static inline void Tn_PrintTime( const char * pStr, iword time )
{
  printf( "%s = %9.2f sec\n", pStr, 1.0*((double)(time))/((double)CLOCKS_PER_SEC));
}
static inline int Tn_Base2Log( unsigned n )   
{ 
  int r; if ( n < 2 ) return (int)n; for ( r = 0, n--; n; n >>= 1, r++ ) {}; return r; 
}

/*************************************************************
                  Permutation generation 
**************************************************************/

// generate next permutation in lexicographic order
static void Tn_GetNextPerm(int *currPerm, int nVars)
{
    int i = nVars - 1;
    while (i >= 0 && currPerm[i - 1] >= currPerm[i])
        i--;
    if (i >= 0)
    {
        int j = nVars;
        while (j > i && currPerm[j - 1] <= currPerm[i - 1])
            j--;
        TN_SWAP(int, currPerm[i - 1], currPerm[j - 1])
        i++;
        j = nVars;
        while (i < j)
        {
            TN_SWAP(int, currPerm[i - 1], currPerm[j - 1])
            i++;
            j--;
        }
    }
}
static int Tn_Factorial(int nVars)
{
    int i, Res = 1;
    for ( i = 1; i <= nVars; i++ )
        Res *= i;
    return Res;
}

// permutation testing procedure
void Tn_PermTest()
{
    int i, k, nVars = 5, currPerm[MSIZE] = {0};
    for ( i = 0; i < nVars; i++ )
        currPerm[i] = i;
    int fact = Tn_Factorial( nVars );
    for ( i = 0; i < fact; i++ )
    {
        printf( "%3d :", i );
        for ( k = 0; k < nVars; k++ )
            printf( " %d", currPerm[k] );
        printf( "\n" );
        Tn_GetNextPerm( currPerm, nVars );
    }
}

/*************************************************************
                  cut/path generation
**************************************************************/

// pos cut vars imply the nodes are connected
static inline tn_vi * Tn_CutGen( int n, int nins )
{
  tn_vi * v = tn_vi_alloc( 1000 );
  int i, j, m, nMiddle = 0, Middle[MSIZE] = {0};
  assert( n <= MSIZE );
  for ( i = 1+nins; i < n-1; i++ )
    Middle[nMiddle++] = i;
  assert( nMiddle == n - nins - 2 );
  for ( m = 0; m < (1<<nMiddle); m++ ) {
    int nPart[2] = {0}, Part[2][MSIZE];    
    Part[0][nPart[0]++] = 0;
    for ( i = 0; i < nMiddle; i++ )
      Part[(m >> i)&1][nPart[(m >> i)&1]++] = Middle[i];
    Part[1][nPart[1]++] = n-1;
    tn_vi_push( v, 2*nPart[0]*nPart[1] );
    for ( i = 0; i < nPart[0]; i++ )
    for ( j = 0; j < nPart[1]; j++ ) {
      tn_vi_push( v, Part[0][i] );
      tn_vi_push( v, Part[1][j] );
    }
  }
  //printf( "Generating cuts for %d nodes and %d inputs:\n", n, nins );
  //tn_vi_print_sets( v );
  return v;
}
// neg path vars imply the nodes are disconnected
static inline tn_vi * Tn_PathGen( int n, int nins )
{
  tn_vi * v = tn_vi_alloc( 1000 );
  assert( nins < n-2 );
  tn_vi_push( v, 2 );
  tn_vi_push( v, 0 );
  tn_vi_push( v, n-1 );
  for ( int i = 1; i <= n-2-nins; i++ ) {
    int nfact = Tn_Factorial(i);
    int m, nmints = 1 << (n-2-nins);
    for ( m = 0; m < nmints; m++ ) {
      int o, nones = 0;
      for ( o = 0; o < n-2-nins; o++ )
        nones += (m >> o) & 1;
      if ( nones != i )
        continue;
      // collect variables
      int j, nvars = 0, varMap[MSIZE];
      for ( j = 0; j < n-2-nins; j++ )
        if ( (m >> j) & 1 )
          varMap[nvars++] = 1+nins+j;
      assert( nvars == i );
      // generate permutations
      int p, currPerm[MSIZE];
      for ( j = 0; j < i; j++ )
        currPerm[j] = j;
      for ( p = 0; p < nfact; p++ ) {
        tn_vi_push( v, i+2 );
        tn_vi_push( v, 0 );
        for ( j = 0; j < i; j++ )
          tn_vi_push( v, varMap[currPerm[j]] );
        tn_vi_push( v, n-1 );           
        Tn_GetNextPerm( currPerm, i );
      }
    }
  }
  //printf( "Generating paths for %d nodes and %d inputs:\n", n, nins );
  //tn_vi_print_sets( v );
  return v;
}
static inline void Tn_SetSwap( tn_vi * p, int Obj1, int Obj2 )
{
  int i, n, size, * pArray = tn_vi_array(p);
  tn_vi_for_each_set( p, size, i )
    for ( n = 0; n < size; n++ )
      if ( pArray[i+n] == Obj1 )
        pArray[i+n] = Obj2;
      else if ( pArray[i+n] == Obj2 )
        pArray[i+n] = Obj1;
}


/*************************************************************
                 generating SAT instance
**************************************************************/

typedef struct tn_gr_ {
  int        nIns;          // primary inputs
  int        nOuts;         // primary outputs
  int        nNodes;        // all objects (const 1, nIns, internal nodes, nOuts)
  int        nNodes2;       // the square of the above
  int        nMints;        // the number of input minterms
  int        nEdgeLimit;    // maximum transistor count
  int        nLevelLimit;   // maximum transistor depth
  int        fVerbose;      // user flag
  char *     pTypes;        // control type for each node (none, neg, pos, both)
  word       pOuts[MSIZE];  // truth tables for each output
  tn_vi *    pVecs[6];      // constraints for each output
  FILE *     pFile;         // file for CNF writing
  int        nCnfVars;      // total number of variables
  int        nCnfClas;      // total number of clauses
  int        nCnfVars2;     // total number of variables
  int        nCnfClas2;     // total number of clauses  
  tn_vi *    vTemp[2];      // temporary vector
  tn_vi *    vCnf;          // collected clauses
  tn_vi *    vSol;          // assignment derived by the solver
} tn_gr;

/*************************************************************
                  variable mapping
**************************************************************/

static inline int Tn_MapVar( tn_gr * p, int i, int j, int Shift )
{
  assert( i >= 0 && i < p->nNodes );
  assert( j >= 0 && j < p->nNodes );
  return Shift * p->nNodes2 + i * p->nNodes + j;
}
static inline int Tn_CtrlVar( tn_gr * p, int i, int j, int iVar, int Inv ) 
{
  assert( i != j );
  assert( iVar >= 0 && iVar < p->nIns );  
  assert( Inv == 0 || Inv == 1 );
  if ( Inv )
    return Tn_MapVar( p, tn_max(i, j), tn_min(i, j), iVar );
  else
    return Tn_MapVar( p, tn_min(i, j), tn_max(i, j), iVar );
}
static inline int Tn_EdgeVar( tn_gr * p, int i, int j, int Mint ) 
{
  assert( i != j );
  assert( Mint >= 0 && Mint < (1 << p->nIns) );
  return Tn_MapVar( p, tn_min(i, j), tn_max(i, j), p->nIns + Mint );
}
static inline int Tn_NodeVar( tn_gr * p, int i, int Mint )
{
  assert( Mint >= 0 && Mint < (1 << p->nIns) );
  return Tn_MapVar( p, i, i, p->nIns + Mint );
}
static inline void Tn_PrintMapVar( tn_gr * p )
{
  int i, j, n, Limit = 3; // p->nIns + (1 << p->nIns);
  for ( n = 0; n < Limit; n++ ) {
    printf("\n");
    printf( "Set %2d : ", n );
    for ( j = 0; j < p->nNodes; j++ )
      printf( "%4d", j );
    printf( "\n\n" );    
    for ( i = 0; i < p->nNodes; i++ ) {
      printf( "%6d : ", i );
      for ( j = 0; j < p->nNodes; j++ )
        printf( "%4d", Tn_MapVar(p, i, j, n) );
      printf( "\n" );
    }
  }
}

/*************************************************************
                 graph manipulation
**************************************************************/

static inline tn_gr * Tn_Init( int nIns, int nOuts, word * pOuts, char * pTypes, int nEdgeLimit, int nLevelLimit, int fVerbose )
{
  tn_gr * p     = (tn_gr *)calloc( sizeof(tn_gr), 1 ); int i;
  p->nIns       = nIns;
  p->nOuts      = nOuts;
  p->nNodes     = strlen(pTypes);
  p->nNodes2    = p->nNodes * p->nNodes;
  p->nMints     = 1 << p->nIns;
  p->nCnfVars   = p->nNodes2 * (p->nIns + p->nMints);
  p->pTypes     = pTypes;
  p->nEdgeLimit = nEdgeLimit;
  p->nLevelLimit= nLevelLimit;
  p->fVerbose   = fVerbose; 
  for ( i = 0; i < p->nNodes; i++ )
    assert( pTypes[i] == '*' || pTypes[i] == '-' || (pTypes[i] >= '0' && pTypes[i] <= '2') );
  assert( 1 + p->nIns + p->nOuts <= p->nNodes && p->nNodes <= MSIZE );
  for ( i = 0; i < nOuts; i++ )
    p->pOuts[i] = pOuts[i];
  p->vCnf       = tn_vi_alloc( 1000 );
  p->pVecs[0]   = Tn_CutGen( p->nNodes, p->nIns );  // pos -> connected
  p->pVecs[1]   = Tn_PathGen( p->nNodes, p->nIns ); // neg -> disconnected
  assert( p->nOuts >= 1 && p->nOuts <= 3 );
  if ( nOuts == 2 || nOuts == 3 ) {
    Tn_SetSwap( (p->pVecs[2] = tn_vi_dup(p->pVecs[0])), p->nNodes-1, p->nNodes-2 );
    Tn_SetSwap( (p->pVecs[3] = tn_vi_dup(p->pVecs[1])), p->nNodes-1, p->nNodes-2 ); 
  }
  if ( nOuts == 3 ) {
    Tn_SetSwap( (p->pVecs[4] = tn_vi_dup(p->pVecs[0])), p->nNodes-1, p->nNodes-3 );
    Tn_SetSwap( (p->pVecs[5] = tn_vi_dup(p->pVecs[1])), p->nNodes-1, p->nNodes-3 ); 
  }
  p->vTemp[0]   = tn_vi_alloc( 100 ); 
  p->vTemp[1]   = tn_vi_alloc( 100 ); 
  //printf( "Created graph with %d input, %d output, %d nodes and %s node types.\n", p->nIns, p->nOuts, p->nNodes, p->pTypes );
  return p;
}
static inline void Tn_Free( tn_gr * p )
{
  tn_vi_free(p->vCnf);
  for ( int i = 0; i < 6; i++ )
    if ( p->pVecs[i] ) 
      tn_vi_free(p->pVecs[i]);
  tn_vi_free(p->vTemp[0]);
  tn_vi_free(p->vTemp[1]);  
  free(p);
}
static inline int Tn_CountLabel( tn_gr * p )
{
  int i, k, v, nLabels = 0;
  if ( p->vSol == NULL )
    return 0;
  for ( i = 0;   i < p->nNodes-1; i++ ) 
  for ( k = i+1; k < p->nNodes;   k++ )
  for ( v = 0;   v < p->nIns;     v++ ) 
  {
    int ValP = p->vSol ? tn_vi_read(p->vSol, Tn_CtrlVar(p, i, k, v, 0)) : 0;
    int ValN = p->vSol ? tn_vi_read(p->vSol, Tn_CtrlVar(p, i, k, v, 1)) : 0;
    assert( ValP + ValN < 2 );
    nLabels += ValP + ValN;
  }
  return nLabels;
}
static inline void Tn_PrintStats( tn_gr * p )
{
  printf( "Problem %s has %d inputs, %d outputs, %d nodes, and %d labels.\n", 
    p->pTypes, p->nIns, p->nOuts, p->nNodes-p->nIns, Tn_CountLabel(p) );
}
static inline void Tn_PrintGraph( tn_gr * p )
{
  int i, k, v, nLabels = 0;
  if ( 0 && p->vSol ) {
    tn_vi_for_each_entry( p->vSol, v, i )
    {
      if ( i % p->nNodes2 == 0 )
        printf( "\n" );
      if ( i == p->nIns * p->nNodes2 )
        break;
      if ( v == 1 )
        printf( " %d", i );
    }
    printf( "\n");
  }

  printf( "    " );
  for ( i = 0; i < p->nNodes; i++ ) {
    for ( v = 0; v <= p->nIns-2; v++ )
      printf( " " );
    printf( "%2d", i );
  }
  printf( "\n" );
  for ( i = 0; i < p->nNodes-1; i++, printf("\n") ) {
    printf( "%2d : ", i );
    for ( k = 0; k < p->nNodes; k++ ) {
      if ( k <= i )
      {
        for ( v = 0; v <= p->nIns; v++ )
          printf( " " );
        continue;
      }
      for ( v = 0; v < p->nIns; v++ ) 
      {
        int ValP = p->vSol ? tn_vi_read(p->vSol, Tn_CtrlVar(p, i, k, v, 0)) : 0;
        int ValN = p->vSol ? tn_vi_read(p->vSol, Tn_CtrlVar(p, i, k, v, 1)) : 0;
        assert( ValP + ValN < 2 );
        printf( "%c", ValP + ValN == 0 ? '-' : (ValP ? 'A' : 'a')+v );
        nLabels += ValP + ValN;
      }
      printf(" ");
    }
  }
  //printf( "\nTotal labels = %d.\n\n", nLabels );    
}
static inline void Tn_PrintGraph2( tn_gr * p )
{
  int i, k, v, nLabels = 0;
  if ( 0 && p->vSol ) {
    tn_vi_for_each_entry( p->vSol, v, i )
    {
      if ( i % p->nNodes2 == 0 )
        printf( "\n" );
      if ( i == p->nIns * p->nNodes2 )
        break;
      if ( v == 1 )
        printf( " %d", i );
    }
    printf( "\n");
  }

  printf( "    " );
  for ( i = p->nIns + 1; i < p->nNodes; i++ ) {
    for ( v = 0; v <= p->nIns-2; v++ )
      printf( " " );
    printf( "%2d", i-p->nIns );
  }
  printf( "\n" );
  for ( i = 0; i < p->nNodes-1; i++ ) {
    if ( i >= 1 && i <= p->nIns )
      continue;
    printf( "%2d : ", i ? i - p->nIns : 0 );
    for ( k = p->nIns + 1; k < p->nNodes; k++ ) {
      if ( k <= i )
      {
        for ( v = 0; v <= p->nIns; v++ )
          printf( " " );
        continue;
      }
      for ( v = 0; v < p->nIns; v++ ) 
      {
        int ValP = p->vSol ? tn_vi_read(p->vSol, Tn_CtrlVar(p, i, k, v, 0)) : 0;
        int ValN = p->vSol ? tn_vi_read(p->vSol, Tn_CtrlVar(p, i, k, v, 1)) : 0;
        assert( ValP + ValN < 2 );
        printf( "%c", ValP + ValN == 0 ? '-' : (ValP ? 'A' : 'a')+v );
        nLabels += ValP + ValN;
      }
      printf(" ");
    }
    printf("\n");
  }
  //printf( "\nTotal labels = %d.\n\n", nLabels );    
}

/*************************************************************
                      CNF writing
**************************************************************/

static inline void Tn_DumpFile( tn_gr * p, const char * pFileName )
{
  FILE * pFile = fopen( pFileName, "wb" );
  if ( pFile == NULL ) {
    printf( "Cannot open file \"%s\" for writing CNF.\n", pFileName );
    return;
  }
  fprintf( pFile, "p cnf %d %d\n", p->nCnfVars, p->nCnfClas );
  int i, n, size, nClas = 0, * pArray = tn_vi_array(p->vCnf);
  tn_vi_for_each_set( p->vCnf, size, i ) {
    for ( n = 0; n < size; n++ )
      fprintf( pFile, "%s%d ", tn_l2c(pArray[i+n]) ? "-" : "", tn_l2v(pArray[i+n]) );
    fprintf( pFile, "0\n" );
    nClas++;
  }
  assert( nClas == p->nCnfClas );
  fclose( pFile );
  //printf( "Finished dumping CNF with %d variables and %d clauses.\n", p->nCnfVars, p->nCnfClas );
}

static inline int Tn_GenClause( tn_gr * p, int * pLits, int nLits )
{
  int i, k = 0;
  for ( i = 0; i < nLits; i++ ) {
    if ( pLits[i] == 1 )
      return 0;
    else if ( pLits[i] == 0 )
      continue;
    else if ( pLits[i] <= 2*p->nCnfVars )
      pLits[k++] = pLits[i];
    else assert( 0 );
  }
  nLits = k;
  assert( nLits > 0 );
  //if ( p->pFile ) {
  if ( 1 ) {  
    p->nCnfClas++;
    //for ( i = 0; i < nLits; i++ )
    //  fprintf( p->pFile, "%s%d ", tn_l2c(pLits[i]) ? "-" : "", tn_l2v(pLits[i]) );
    //fprintf( p->pFile, "0\n" );
    tn_vi_push( p->vCnf, nLits );
    for ( i = 0; i < nLits; i++ )
      tn_vi_push( p->vCnf, pLits[i] );
  }
  if ( 0 ) 
  {
    for ( i = 0; i < nLits; i++ )
      fprintf( stdout, "%s%d ", tn_l2c(pLits[i]) ? "-" : " ", tn_l2v(pLits[i]) );
    fprintf( stdout, "\n" );
  }
  return 1;
}
static inline int Tn_GenClauseVec( tn_gr * p, tn_vi * v )
{
  return Tn_GenClause( p, tn_vi_array(v), tn_vi_size(v) );
}
static inline int Tn_GenClause4( tn_gr * p, int Lit0, int Lit1, int Lit2, int Lit3 )
{
  int pLits[4] = { Lit0, Lit1, Lit2, Lit3 };
  return Tn_GenClause( p, pLits, 4 );
}
// generate constraints for (Out = a0*b0 + a1*b1 + a2 + a3)
static inline void Tn_GenAndOrGate( tn_gr * pG, int iOutVar, tn_vi * vA, tn_vi * vB )
{
  tn_vi * pArrays[2] = { vA, vB };
  assert( tn_vi_size(vA) >= tn_vi_size(vB) );
  int v, m, nmints = 1 << tn_vi_size(vB);
  for ( m = 0; m < nmints; m++ ) {
    int nvars = 0, pVars[MSIZE];
    pVars[nvars++] = tn_v2l( iOutVar, 1 );
    for ( v = 0; v < tn_vi_size(vB); v++ )
      pVars[nvars++] = tn_v2l( tn_vi_read(pArrays[(m>>v)&1], v), 0 );
    for (      ; v < tn_vi_size(vA); v++ )
      pVars[nvars++] = tn_v2l( tn_vi_read(pArrays[0], v), 0 );
    Tn_GenClause( pG, pVars, nvars );
  }
  for ( v = 0; v < tn_vi_size(vA); v++ ) {
    int nvars = 0, pVars[MSIZE];
    pVars[nvars++] = tn_v2l( iOutVar, 0 );
    if ( v < tn_vi_size(vB) )
    pVars[nvars++] = tn_v2l( tn_vi_read(vB, v), 1 );
    pVars[nvars++] = tn_v2l( tn_vi_read(vA, v), 1 );
    Tn_GenClause( pG, pVars, nvars );    
  }
}
/*************************************************************
                  candinality constraint
**************************************************************/

static inline int Tn_AddClause( tn_vi * p, int* begin, int* end )
{
    tn_vi_push( p, (int)(end-begin) );
    while ( begin < end )
        tn_vi_push( p, (int)*begin++ );
    return 1;
}
static inline int Tn_AddHalfSorter( tn_vi * p, int iVarA, int iVarB, int iVar0, int iVar1 )
{
    int Lits[3];
    int Cid;

    Lits[0] = tn_v2l( iVarA, 0 );
    Lits[1] = tn_v2l( iVar0, 1 );
    Cid = Tn_AddClause( p, Lits, Lits + 2 );
    assert( Cid );

    Lits[0] = tn_v2l( iVarA, 0 );
    Lits[1] = tn_v2l( iVar1, 1 );
    Cid = Tn_AddClause( p, Lits, Lits + 2 );
    assert( Cid );

    Lits[0] = tn_v2l( iVarB, 0 );
    Lits[1] = tn_v2l( iVar0, 1 );
    Lits[2] = tn_v2l( iVar1, 1 );
    Cid = Tn_AddClause( p, Lits, Lits + 3 );
    assert( Cid );
    return 3;
}
static inline void Tn_AddSorter( tn_vi * p, int * pVars, int i, int k, int * pnVars )
{
    int iVar1 = (*pnVars)++;
    int iVar2 = (*pnVars)++;
    Tn_AddHalfSorter( p, iVar1, iVar2, pVars[i], pVars[k] );
    pVars[i] = iVar1;
    pVars[k] = iVar2;
}
static inline void Tn_AddCardinConstrMerge( tn_vi * p, int * pVars, int lo, int hi, int r, int * pnVars )
{
    int i, step = r * 2;
    if ( step < hi - lo )
    {
        Tn_AddCardinConstrMerge( p, pVars, lo, hi-r, step, pnVars );
        Tn_AddCardinConstrMerge( p, pVars, lo+r, hi, step, pnVars );
        for ( i = lo+r; i < hi-r; i += step )
            Tn_AddSorter( p, pVars, i, i+r, pnVars );
        for ( i = lo+r; i < hi-r-1; i += r )
        {
            int Lits[2] = { tn_v2l(pVars[i], 0), tn_v2l(pVars[i+r], 1) };
            int Cid = Tn_AddClause( p, Lits, Lits + 2 );
            assert( Cid );
        }
    }
}
static inline void Tn_AddCardinConstrRange( tn_vi * p, int * pVars, int lo, int hi, int * pnVars )
{
    if ( hi - lo >= 1 )
    {
        int i, mid = lo + (hi - lo) / 2;
        for ( i = lo; i <= mid; i++ )
            Tn_AddSorter( p, pVars, i, i + (hi - lo + 1) / 2, pnVars );
        Tn_AddCardinConstrRange( p, pVars, lo, mid, pnVars );
        Tn_AddCardinConstrRange( p, pVars, mid+1, hi, pnVars );
        Tn_AddCardinConstrMerge( p, pVars, lo, hi, 1, pnVars );
    }
}
int Tn_AddCardinConstrPairWise( tn_vi * p, tn_vi * vVars )
{
    int nVars = tn_vi_size(vVars);
    Tn_AddCardinConstrRange( p, tn_vi_array(vVars), 0, nVars - 1, &nVars );
    return nVars;
}
int Tn_AddCardinSolver( int LogN, tn_vi ** pvVars, tn_vi ** pvRes )
{
    int i, nVars   = 1 << LogN;
    int nVarsAlloc = nVars + 2 * (nVars * LogN * (LogN-1) / 4 + nVars - 1);
    tn_vi * vRes   = tn_vi_alloc( 1000 );
    tn_vi * vVars  = tn_vi_alloc( nVars );
    for ( i = 0; i < nVars; i++ )
      tn_vi_push( vVars, i );
    int nVarsReal = Tn_AddCardinConstrPairWise( vRes, vVars );
    assert( nVarsReal == nVarsAlloc );
    *pvVars = vVars;
    *pvRes  = vRes;  
    return nVarsReal;
}
void Tn_AddCardinality( tn_gr * p, tn_vi * vCard )
{
    assert( p->nEdgeLimit );
    tn_vi * vVars = NULL;
    tn_vi * vRes  = NULL;    
    int LogN      = Tn_Base2Log( tn_vi_size(vCard) );
    int nVarsReal = Tn_AddCardinSolver( LogN, &vVars, &vRes ), n, i, Var, size, pLits[2];
    p->nCnfVars2  = p->nCnfVars;
    p->nCnfClas2  = p->nCnfClas;    
    p->nCnfVars  += nVarsReal;
    tn_vi_for_each_entry( vCard, Var, i ) {
      for ( n = 0; n < 2; n++ ) {
        pLits[0] = tn_v2l( Var, n );
        pLits[1] = tn_v2l( p->nCnfVars2+i, !n );
        Tn_GenClause( p, pLits, 2 );
      }
    }
    for ( ; i < (1<<LogN); i++ ) {
      pLits[0] = tn_v2l( p->nCnfVars2+i, 1 );
      Tn_GenClause( p, pLits, 1 );
    }
    int * pArray = tn_vi_array(vRes);
    tn_vi_for_each_set( vRes, size, i ) {
      for ( n = 0; n < size; n++ )
        pArray[i+n] += 2*p->nCnfVars2;
      Tn_GenClause( p, pArray+i, size );  
    }
    pLits[0] = tn_v2l( p->nCnfVars2+tn_vi_read(vVars, p->nEdgeLimit), 1 );
    Tn_GenClause( p, pLits, 1 );
    tn_vi_free( vVars );
    tn_vi_free( vRes );
}

/*************************************************************
                 CNF generation 
**************************************************************/

static inline tn_vi * Tn_GenCnfStart( tn_gr * p )
{
  int i, j, n;
  //printf( "The first controls\n" );  
  for ( n = 0;   n < p->nIns; n++ )  
  for ( i = 1;   i <=p->nIns; i++ )
  for ( j = 0;   j < p->nNodes; j++ ) if ( i != j ) {
    Tn_GenClause4( p, tn_v2l(Tn_CtrlVar(p, i, j, n, 0), 1), 0, 0, 0 );
    Tn_GenClause4( p, tn_v2l(Tn_CtrlVar(p, i, j, n, 1), 1), 0, 0, 0 );
  }
  //printf( "Unused middle vars\n" );    
  for ( n = 0;   n < p->nIns; n++ )  
  for ( i = 0;   i < p->nNodes; i++ )
    Tn_GenClause4( p, tn_v2l(Tn_MapVar(p, i, i, n), 1), 0, 0, 0 );
  //printf( "The other controls\n" );
  tn_vi * vCard = tn_vi_alloc( 100 );
  for ( n = 0;   n < p->nIns; n++ )  
  for ( i = 0;   i < p->nNodes; i++ ) {
    if ( i >= 1 && i <= p->nIns )
      continue;
    for ( j = i+1; j < p->nNodes; j++ ) {
      if ( j >= 1 && j <= p->nIns )
        continue;
      if ( p->pTypes[1+n] == '0' ) {      // negative - remove positive (i < j) 
        Tn_GenClause4( p, tn_v2l(Tn_CtrlVar(p, i, j, n, 0), 1), 0, 0, 0 );
        tn_vi_push( vCard, Tn_CtrlVar(p, i, j, n, 1) );
      }
      else if ( p->pTypes[1+n] == '1' ) { // positive - remove negative (i > j)
        Tn_GenClause4( p, tn_v2l(Tn_CtrlVar(p, i, j, n, 1), 1), 0, 0, 0 );
        tn_vi_push( vCard, Tn_CtrlVar(p, i, j, n, 0) );
      }
      else if ( p->pTypes[1+n] == '-' || p->pTypes[1+n] == '*' ) {
        Tn_GenClause4( p, tn_v2l(Tn_CtrlVar(p, i, j, n, 0), 1), 0, 0, 0 );
        Tn_GenClause4( p, tn_v2l(Tn_CtrlVar(p, i, j, n, 1), 1), 0, 0, 0 );
      }
      else if ( p->pTypes[1+n] == '2' ) {
        tn_vi_push( vCard, Tn_CtrlVar(p, i, j, n, 0) );
        tn_vi_push( vCard, Tn_CtrlVar(p, i, j, n, 1) );
      }
      else assert( 0 );
    }
  }
  //printf( "Pair-wise one-hot\n" );  
  for ( n = 0;   n < p->nIns; n++ )
  for ( i = 0;   i < p->nNodes; i++ )
  for ( j = i+1; j < p->nNodes; j++ )
    Tn_GenClause4( p, tn_v2l(Tn_CtrlVar(p, i, j, n, 0), 1), tn_v2l(Tn_CtrlVar(p, i, j, n, 1), 1), 0, 0 );
  return vCard;
}
static inline void Tn_GenCnfMint( tn_gr * p, int m, int mout )
{
  int i, j, v, size;
/*  
  //printf( "Generating minterm %d / %d:\n", m, mout );
  Tn_GenClause4( p, tn_v2l(Tn_NodeVar(p, 0, m), 0), 0, 0, 0 );
  for ( i = 0; i < p->nIns; i++ )
    Tn_GenClause4( p, tn_v2l(Tn_NodeVar(p, 1+i, m), ((m>>i)&1)==0), 0, 0, 0 );
  for ( i = 0; i < p->nOuts; i++ )
    Tn_GenClause4( p, tn_v2l(Tn_NodeVar(p, p->nNodes-p->nOuts+p->nOuts-1-i, m), ((mout>>i)&1)==0), 0, 0, 0 );
  //printf( "Functionality:\n" );  
  for ( i = 0;   i < p->nNodes; i++ )
  for ( j = i+1; j < p->nNodes; j++ ) 
  {
    int iEdge  = Tn_EdgeVar(p, i, j, m);
    int iNodeI = Tn_NodeVar(p, i, m);
    int iNodeJ = Tn_NodeVar(p, j, m);
    Tn_GenClause4( p, tn_v2l(iEdge, 1), tn_v2l(iNodeI, 0), tn_v2l(iNodeJ, 1), 0 );
    Tn_GenClause4( p, tn_v2l(iEdge, 1), tn_v2l(iNodeI, 1), tn_v2l(iNodeJ, 0), 0 );    
  }
*/  
  //printf( "Edge variables:\n" );  
  for ( i = 0;   i < p->nNodes; i++ )
  for ( j = i+1; j < p->nNodes; j++ ) 
  {
    tn_vi_resize( p->vTemp[0], 0 );
    tn_vi_resize( p->vTemp[1], 0 );  
    for ( v = 0; v < p->nIns; v++ )
      tn_vi_push( p->vTemp[0], Tn_CtrlVar(p, i, j, v, ((m>>v)&1)==0) );
    Tn_GenAndOrGate( p, Tn_EdgeVar(p, i, j, m), p->vTemp[0], p->vTemp[1] );
  }
  //printf( "Connectivity:\n" );  
  for ( i = 0; i < p->nOuts; i++ )
  {
    if ( (mout>>i)&1 ) { // p->pVecs[0]  pos cut vars -> connected
      tn_vi_for_each_set( p->pVecs[2*i+0], size, j ) {
        assert( (size & 1) == 0 );
        tn_vi_resize( p->vTemp[0], 0 );
        for ( v = 0; v < size/2; v++ ) {
          int start = tn_vi_read(p->pVecs[2*i+0], j+2*v+0);
          int next  = tn_vi_read(p->pVecs[2*i+0], j+2*v+1);
          tn_vi_push( p->vTemp[0], tn_v2l(Tn_EdgeVar(p, start, next, m), 0) );
        }
        Tn_GenClauseVec( p, p->vTemp[0] );
      }
      if ( p->nLevelLimit == 0 )
        continue;
      tn_vi_for_each_set( p->pVecs[2*i+1], size, j ) { // p->pVecs[1]  neg path vars -> disconnected
        if ( size <= p->nLevelLimit+1 )
          continue;
        int next, start = tn_vi_read(p->pVecs[2*i+1], j);
        tn_vi_resize( p->vTemp[0], 0 );
        for ( v = 1; v < size && (next = tn_vi_read(p->pVecs[2*i+1], j+v)); v++, start = next )
          tn_vi_push( p->vTemp[0], tn_v2l(Tn_EdgeVar(p, start, next, m), 1) );
        Tn_GenClauseVec( p, p->vTemp[0] );
      }        
    }
    else { // p->pVecs[1]  neg path vars -> disconnected
      tn_vi_for_each_set( p->pVecs[2*i+1], size, j ) {
        int next, start = tn_vi_read(p->pVecs[2*i+1], j);
        tn_vi_resize( p->vTemp[0], 0 );
        for ( v = 1; v < size && (next = tn_vi_read(p->pVecs[2*i+1], j+v)); v++, start = next )
          tn_vi_push( p->vTemp[0], tn_v2l(Tn_EdgeVar(p, start, next, m), 1) );
        Tn_GenClauseVec( p, p->vTemp[0] );
      }      
    }    
  }
}
static inline void Tn_GenCnf( tn_gr * p, const char * pFileName )
{
  int o, m, mout;
  assert( p->pFile == NULL );
  p->pFile = fopen( pFileName, "wb" );
  if ( p->pFile == NULL ) {
    printf( "Cannot open file \"%s\" for writing CNF.\n", pFileName );
    return;
  }
  fputs( "p cnf                \n", p->pFile );
  tn_vi * vCard = Tn_GenCnfStart( p );
  for ( m = 0; m < (1<<p->nIns); m++ ) {
    for ( mout = o = 0; o < p->nOuts; o++ )
      if ( (p->pOuts[o] >> m) & 1 )
         mout |= 1 << o;
    Tn_GenCnfMint( p, m, mout );
  }
  if ( p->nEdgeLimit > 0 )
    Tn_AddCardinality( p, vCard );
  rewind( p->pFile );
  fprintf( p->pFile, "p cnf %d %d", p->nCnfVars, p->nCnfClas );
  fclose( p->pFile );
  p->pFile = NULL;
  printf( "Dumped file \"%s\" with %d vars and %d clauses (%d out of %d: %d vars and %d clauses).\n", 
    pFileName, p->nCnfVars, p->nCnfClas, p->nEdgeLimit, tn_vi_size(vCard),
    p->nCnfVars2 ? p->nCnfVars-p->nCnfVars2 : 0,
    p->nCnfClas2 ? p->nCnfClas-p->nCnfClas2 : 0 );
  tn_vi_free( vCard );
}
static inline void Tn_GenCnf2( tn_gr * p )
{
  int o, m, mout;
  assert( tn_vi_size(p->vCnf) == 0 );
  tn_vi * vCard = Tn_GenCnfStart( p );
  for ( m = 0; m < (1<<p->nIns); m++ ) {
    for ( mout = o = 0; o < p->nOuts; o++ )
      if ( (p->pOuts[o] >> m) & 1 )
         mout |= 1 << o;
    Tn_GenCnfMint( p, m, mout );
  }
  if ( p->nEdgeLimit > 0 )
    Tn_AddCardinality( p, vCard );
  printf( "Created CNF with %d vars and %d clauses (%d out of %d: %d vars and %d clauses).\n", 
    p->nCnfVars, p->nCnfClas, p->nEdgeLimit, tn_vi_size(vCard),
    p->nCnfVars2 ? p->nCnfVars-p->nCnfVars2 : 0,
    p->nCnfClas2 ? p->nCnfClas-p->nCnfClas2 : 0 );
  tn_vi_free( vCard );
}

/*************************************************************
                  Reading input data
**************************************************************/

// truth table size in 64-bit words
static inline int Tn_TruthWordNum( int n )  { return n <= 6 ? 1 : 1 << (n-6);    }
static inline int Tn_HexDigitNum( int n )   { return n <= 2 ? 1 : 1 << (n-2);    }

static inline int Tn_Hex2Int( char c ) {
    int Digit = 0;
    if ( c >= '0' && c <= '9' )
        Digit = c - '0';
    else if ( c >= 'A' && c <= 'F' )
        Digit = c - 'A' + 10;
    else if ( c >= 'a' && c <= 'f' )
        Digit = c - 'a' + 10;
    else return -1;
    assert( Digit >= 0 && Digit < 16 );
    return Digit;
}
static inline void Tn_PrintHexTruth( FILE * pFile, word * pTruth, int nVars )  {
    int k, Digit, nDigits = Tn_HexDigitNum(nVars);
    for ( k = nDigits-1; k >= 0; k-- ) {
        Digit = (int)((pTruth[k/16] >> ((k%16) * 4)) & 15);
        if ( Digit < 10 )
            fprintf( pFile, "%d", Digit );
        else
            fprintf( pFile, "%c", 'A' + Digit-10 );
    }
}
int Tn_ReadHexTruth( char * pInput, word * pTruth )
{
    int nChars = strlen(pInput), i; 
    int nVars  = Tn_Base2Log(4*nChars);
    if ( (1 << nVars) != 4*nChars ) {
        printf( "The input string length (%d chars) does not match the size (%d bits) of the truth table of %d-var function.\n", 
            nChars, 1<<nVars, nVars );
        return 0;
    }
    word Num = 0;
    for ( i = nChars-1; i >= 0; i-- ) {
        Num |= (word)Tn_Hex2Int(pInput[nChars-1-i]) << ((i & 0xF) * 4);
        if ( (i & 0xF) == 0 )
            pTruth[i>>4] = Num, Num = 0;
    }
    assert( Num == 0 );
    printf( "Finished entring %d-input function: ", nVars );
    Tn_PrintHexTruth( stdout, pTruth, nVars );
    printf( "\n" );
    return nVars;
}

/*************************************************************
                 dumping spice format
**************************************************************/

static inline void Tn_DumpNode( tn_gr * p, FILE * pFile, int i )
{
    if ( i == 0 )
      fprintf( pFile, " VDD" );
    else if ( i >= p->nNodes - p->nOuts ) {
      fprintf( pFile, " Y" );
      Tn_PrintHexTruth( pFile, p->pOuts+(i-(p->nNodes - p->nOuts)), p->nIns );
    }
    else 
      fprintf( pFile, " net%d", i-p->nIns );
}
static inline int Tn_DumpLabels( tn_gr * p, FILE * pFile )
{
  int i, k, v, nLabels = 0;
  if ( p->vSol == NULL )
    return 0;
  for ( i = 0;   i < p->nNodes-1; i++ ) 
  for ( k = i+1; k < p->nNodes;   k++ )
  for ( v = 0;   v < p->nIns;     v++ ) 
  {
    int ValP = p->vSol ? tn_vi_read(p->vSol, Tn_CtrlVar(p, i, k, v, 0)) : 0;
    int ValN = p->vSol ? tn_vi_read(p->vSol, Tn_CtrlVar(p, i, k, v, 1)) : 0;
    assert( ValP + ValN < 2 );
    if ( ValP + ValN == 0 )
      continue;
    // MM1 net10 B VDD VDD pmos_rvt w=xxxn l=yyyn nfin=2
    fprintf( pFile, "mm%d", nLabels );
    Tn_DumpNode( p, pFile, tn_max(i, k) );
    fprintf( pFile, " %c", 'A'+v );
    Tn_DumpNode( p, pFile, tn_min(i, k));
    fprintf( pFile, " VDD" );
    fprintf( pFile, " %cmos_rvt\n", ValP ? 'p' : 'n' );    
    nLabels += ValP + ValN;    
  }
  return nLabels;
}
static inline void Tn_DumpSpice( tn_gr * p )
{
  const char * pFileName = "temp.sp"; int i;
  FILE * pFile = fopen( pFileName, "wb" );
  if ( pFile == NULL ) {
    printf( "Cannot open file \"%s\" for writing SPICE format.\n", pFileName );
    return;
  }
  //.SUBCKT <name> A VDD VSS Y
  fprintf( pFile, ".SUBCKT tn" );
  for ( i = 0; i < p->nOuts; i++ ) {
    fprintf( pFile, "_" );
    Tn_PrintHexTruth( pFile, p->pOuts+i, p->nIns );
  }  
  for ( i = 0; i < p->nIns; i++ )
    fprintf( pFile, " %c", 'A' + i );
  fprintf( pFile, " VDD VSS");
  for ( i = 0; i < p->nOuts; i++ ) {
    fprintf( pFile, " Y" );
    Tn_PrintHexTruth( pFile, p->pOuts+i, p->nIns );
  }
  fprintf( pFile, "\n");
  Tn_DumpLabels( p, pFile );
  fprintf( pFile, ".ENDS\n\n" );  
  fclose( pFile );
  printf( "Finished dumping SPICE description into file \"%s\".\n", pFileName );
}

/*************************************************************
                  Solving the problem
**************************************************************/

tn_vi * Tn_ParseSolution( const char * pFileName )
{
    tn_vi * vRes = NULL;
    char * pToken, pBuffer[1000];
    FILE * pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\".\n", pFileName );
        return NULL;
    }
    while ( fgets( pBuffer, 1000, pFile ) != NULL )
    {
        if ( pBuffer[0] == 's' )
        {
            if ( strncmp(pBuffer+2, "SAT", 3) )
                break;
            assert( vRes == NULL );
            vRes = tn_vi_alloc( 100 );
        }
        else if ( pBuffer[0] == 'v' )
        {
            pToken = strtok( pBuffer+1, " \n\r\t" );
            while ( pToken )
            {
                int Token = atoi(pToken);
                if ( Token == 0 )
                    break;
                int nSizeMax = tn_abs(Token) + 1;
                while ( tn_vi_size(vRes) < nSizeMax )
                    tn_vi_push( vRes, -1 );
                tn_vi_write( vRes, tn_abs(Token), Token > 0 );
                //Vec_IntSetEntryFull( vRes, Tn_AbsInt(Token), Token > 0 );
                pToken = strtok( NULL, " \n\r\t" );
            }
        }
        else if ( pBuffer[0] != 'c' )
            assert( 0 );
    }
    fclose( pFile );
    unlink( pFileName );
    return vRes;
}
tn_vi * Tn_SolveSat( const char * pFileNameIn, const char * pFileNameOut, int Seed, int TimeOut, int fVerbose )
{
    int fVerboseSolver = 0;
    iword clkTotal = Tn_Clock();
    tn_vi * vRes = NULL;
#ifdef _WIN32
    const char * pKissat = "kissat.exe";
#else
    const char * pKissat = "kissat";
#endif
    char Command[1000], * pCommand = (char *)&Command;
    if ( TimeOut )
        sprintf( pCommand, "%s --seed=%d --time=%d %s %s > %s", pKissat, Seed, TimeOut, fVerboseSolver ? "": "-q", pFileNameIn, pFileNameOut );
    else
        sprintf( pCommand, "%s --seed=%d %s %s > %s", pKissat, Seed, fVerboseSolver ? "": "-q", pFileNameIn, pFileNameOut );
    //if ( fVerbose )
    //    printf( "Running command line: %s\n", pCommand );
#if defined(__wasm)
    if ( 1 )
#else
    if ( system( pCommand ) == -1 )
#endif
    {
        printf( "Command \"%s\" did not succeed.\n", pCommand );
        return 0;
    }
    vRes = Tn_ParseSolution( pFileNameOut );
    if ( fVerbose )
    {
        if ( vRes )
            printf( "The problem has a solution. " );
        else if ( vRes == NULL && TimeOut == 0 )
            printf( "The problem has no solution. " );
        else if ( vRes == NULL )
            printf( "The problem has no solution or timed out after %d sec. ", TimeOut );
        Tn_PrintTime( "SAT solver time", Tn_Clock() - clkTotal );
    }
    return vRes;
}
static inline void Tn_AppendClause( tn_gr * p, tn_vi * vSol )
{
  int v, k = 0, Limit = p->nIns * p->nNodes2;
  for ( v = 1; v < Limit; v++ )
    if ( tn_vi_read(p->vSol, v) )
      tn_vi_write( p->vSol, k++, tn_v2l(v, 1) );
  tn_vi_resize( p->vSol, k );
  Tn_GenClauseVec( p, p->vSol );
  //printf("Finished adding clause: ");
  //tn_vi_print( p->vSol );
}
void Tn_SolveProblem( int nIns, int nOuts, word * pOuts, char * pTypes, int nEdgeLimit, int nLevelLimit, int nSolsMax, int Seed, int TimeOut, int fVerbose )
{
  const char * pFileNameIn  = "_temp_.cnf";
  const char * pFileNameOut = "_temp_.txt";  
  tn_gr * p = Tn_Init( nIns, nOuts, pOuts, pTypes, nEdgeLimit, nLevelLimit, fVerbose );
  //Tn_PrintMapVar( p );
  Tn_GenCnf2( p );
  for ( int n = 0; n < nSolsMax; n++ ) {
    printf( "\nIteration %d:\n", n );
    Tn_DumpFile( p, pFileNameIn );
    p->vSol = Tn_SolveSat( pFileNameIn, pFileNameOut, Seed, TimeOut, fVerbose );
    Tn_PrintStats( p );  
    if ( p->vSol ) {
      //Tn_PrintGraph( p );
      Tn_PrintGraph2( p );
      Tn_DumpSpice( p );      
      Tn_AppendClause( p, p->vSol );
      tn_vi_free( p->vSol );
      p->vSol = NULL;
    }
    else {
      printf( "Problem has no solution.\n" );
      break;
    }
  }
  Tn_Free( p );
}

/*************************************************************
                    main() procedure
**************************************************************/

#if 0

int main(int argc, char ** argv)
{
    if ( argc == 1 )
    {
        printf( "usage:  %s -C <str> [-ELNSTV <num>] <truth[0]> ... <truth[m-1]>\n", argv[0] );
        printf( "                   this program synthesizes networks for multi-output functions\n" );
        printf( "\n" );     
        printf( "      -C <str>  :  the configuration string (no default)\n" );
        printf( "      -E <num>  :  the max number of edges (default = no limit)\n" );
        printf( "      -L <num>  :  the max number of levels (default = no limit)\n" );        
        printf( "      -N <num>  :  the max number of solutions (default = 1)\n" );        
        printf( "      -S <num>  :  the random seed (default = 0)\n" );        
        printf( "      -T <num>  :  the timeout in seconds (default = no timeout)\n" );                
        printf( "      -V <num>  :  the verbosiness levels (default = 1)\n" );             
        printf( "    <truth[0]>  :  the truth table of the first output in the hexadecimal notation\n" );
        printf( "  <truth[m-1]>  :  the truth table of the last output in the hexadecimal notation\n" );
        printf( "                   the truth tables are assumed to depend on the same variables\n" );
        printf( "                   the strings should contain 2^(<num_inputs>-2) hexadecimal digits\n" );
        printf( "\n" );        
        printf( "                   Example 1: Synthesizing 3-node 2-edge 2-input and-gate:\n" );
        printf( "                     %s -C *11** -E 2  8\n", argv[0] );
        printf( "                   Example 2: Synthesizing 4-node 5-edge 3-input majority gate:\n" );
        printf( "                     %s -C *111*** -E 5  E8\n", argv[0] );        
//        printf( "                   Example 3: Synthesizing 9-node 10-edge 3-input 2-output full-adder:\n" );
//        printf( "                     %s -C *111****1 -E 10  96 E8\n", argv[0] );
        return 1;
    }
    else
    {
        int nIns = 0, nOuts = 0, nEdgeLimit = 0, nLevelLimit = 0, nSolsMax = 1, Seed = 0, TimeOut = 0, fVerbose = 1;
        char * pTypes = NULL;  
        word Truths[MSIZE] = {0};
        for ( int c = 1; c < argc; c++ ) {
          if ( argv[c][0] == '-' && argv[c][1] == 'C' )
            pTypes = argv[++c];
          else if ( argv[c][0] == '-' && argv[c][1] == 'E' )
            nEdgeLimit = atoi(argv[++c]);
          else if ( argv[c][0] == '-' && argv[c][1] == 'L' )
            nLevelLimit = atoi(argv[++c]);            
          else if ( argv[c][0] == '-' && argv[c][1] == 'N' )
            nSolsMax = atoi(argv[++c]);            
          else if ( argv[c][0] == '-' && argv[c][1] == 'S' )
            Seed = atoi(argv[++c]);      
          else if ( argv[c][0] == '-' && argv[c][1] == 'T' )
            TimeOut = atoi(argv[++c]);      
          else if ( argv[c][0] == '-' && argv[c][1] == 'V' )
            fVerbose = atoi(argv[++c]);                 
          else if ( Tn_Hex2Int(argv[c][0]) != -1 ) {
            int nVarsOut = Tn_ReadHexTruth( argv[c], Truths + nOuts++ );
            if ( nIns == 0 )
              nIns = nVarsOut;
            else if ( nIns != nVarsOut ) {
              printf( "The support size of output functions is not the same.\n" ); 
              break;
            }
          }
          else {
              printf( "String \"%s\" does not look like a truth table in the hexadecimal notation.\n", argv[c] );
              break;
          }
        }
        printf( "Finished reading %d output%s\n\n", nOuts, nOuts == 1 ? "" : "s" );
        Tn_SolveProblem( nIns, nOuts, Truths, pTypes, nEdgeLimit, nLevelLimit, nSolsMax, Seed, TimeOut, fVerbose );
        return 1;
    }
}

#endif

/*************************************************************
                     end of file
**************************************************************/

ABC_NAMESPACE_IMPL_END

