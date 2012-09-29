/**CFile****************************************************************

  FileName    [miniaig.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Minimalistic AIG package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 29, 2012.]

  Revision    [$Id: miniaig.h,v 1.00 2012/09/29 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef MINI_AIG__mini_aig_h
#define MINI_AIG__mini_aig_h

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

#define MINI_AIG_NULL       (0x7FFFFFFF)
#define MINI_AIG_START_SIZE (0x000000FF)

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Mini_Aig_t_       Mini_Aig_t;
struct Mini_Aig_t_ 
{
    int           nCap;
    int           nSize;
    int *         pArray;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

// memory management
#define MINI_AIG_ALLOC(type, num)     ((type *) malloc(sizeof(type) * (num)))
#define MINI_AIG_CALLOC(type, num)    ((type *) calloc((num), sizeof(type)))
#define MINI_AIG_FALLOC(type, num)    ((type *) memset(malloc(sizeof(type) * (num)), 0xff, sizeof(type) * (num)))
#define MINI_AIG_FREE(obj)            ((obj) ? (free((char *) (obj)), (obj) = 0) : 0)
#define MINI_AIG_REALLOC(type, obj, num) \
        ((obj) ? ((type *) realloc((char *)(obj), sizeof(type) * (num))) : \
         ((type *) malloc(sizeof(type) * (num))))

// internal procedures
static void Mini_AigGrow( Mini_Aig_t * p, int nCapMin )
{
    if ( p->nCap >= nCapMin )
        return;
    p->pArray = MINI_AIG_REALLOC( int, p->pArray, nCapMin ); 
    assert( p->pArray );
    p->nCap   = nCapMin;
}
static void Mini_AigPush( Mini_Aig_t * p, int Lit0, int Lit1 )
{
    if ( p->nSize >= p->nCap + 1 )
    {
        if ( p->nCap < MINI_AIG_START_SIZE )
            Mini_AigGrow( p, MINI_AIG_START_SIZE );
        else
            Mini_AigGrow( p, 2 * p->nCap );
    }
    p->pArray[p->nSize++] = Lit0;
    p->pArray[p->nSize++] = Lit1;
}

// accessing fanins
static int Mini_AigNodeFanin0( Mini_Aig_t * p, int Id )
{
    assert( Id >= 0 && 2*Id < p->nSize );
    return p->pArray[2*Id];
}
static int Mini_AigNodeFanin1( Mini_Aig_t * p, int Id )
{
    assert( Id >= 0 && 2*Id < p->nSize );
    return p->pArray[2*Id+1];
}

// working with variables and literals
static int      Mini_AigVar2Lit( int Var, int fCompl )         { return Var + Var + fCompl;   }
static int      Mini_AigLit2Var( int Lit )                     { return Lit >> 1;             }
static int      Mini_AigLitIsCompl( int Lit )                  { return Lit & 1;              }
static int      Mini_AigLitNot( int Lit )                      { return Lit ^ 1;              }
static int      Mini_AigLitNotCond( int Lit, int c )           { return Lit ^ (int)(c > 0);   }
static int      Mini_AigLitRegular( int Lit )                  { return Lit & ~01;            }

static int      Mini_AigLitConst0()                            { return 0;                    }
static int      Mini_AigLitConst1()                            { return 1;                    }
static int      Mini_AigLitIsConst0( int Lit )                 { return Lit == 0;             }
static int      Mini_AigLitIsConst1( int Lit )                 { return Lit == 1;             }
static int      Mini_AigLitIsConst( int Lit )                  { return Lit == 0 || Lit == 1; }

static int      Mini_AigNumNodes(  Mini_Aig_t * p )            { return p->nSize/2;           }
static int      Mini_AigNodeIsConst( Mini_Aig_t * p, int Id )  { assert( Id >= 0 ); return Id == 0; }
static int      Mini_AigNodeIsPi( Mini_Aig_t * p, int Id )     { assert( Id >= 0 ); return Id > 0 && Mini_AigNodeFanin0( p, Id ) == MINI_AIG_NULL; }
static int      Mini_AigNodeIsPo( Mini_Aig_t * p, int Id )     { assert( Id >= 0 ); return Id > 0 && Mini_AigNodeFanin0( p, Id ) != MINI_AIG_NULL && Mini_AigNodeFanin1( p, Id ) == MINI_AIG_NULL; }
static int      Mini_AigNodeIsAnd( Mini_Aig_t * p, int Id )    { assert( Id >= 0 ); return Id > 0 && Mini_AigNodeFanin0( p, Id ) != MINI_AIG_NULL && Mini_AigNodeFanin1( p, Id ) != MINI_AIG_NULL; }


// constructor/destructor
static Mini_Aig_t * Mini_AigStart( int nCap )
{
    Mini_Aig_t * p;
    assert( nCap > 0 );
    p = MINI_AIG_ALLOC( Mini_Aig_t, 1 );
    if ( nCap < MINI_AIG_START_SIZE )
        nCap = MINI_AIG_START_SIZE;
    p->nSize  = 0;
    p->nCap   = nCap;
    p->pArray = MINI_AIG_ALLOC( int, p->nCap );
    Mini_AigPush( p, MINI_AIG_NULL, MINI_AIG_NULL );
    return p;
}
static void Mini_AigStop( Mini_Aig_t * p )
{
    MINI_AIG_FREE( p->pArray );
    MINI_AIG_FREE( p );
}


// creating nodes 
// (constant node is created when AIG manager is created)
static int Mini_AigCreatePi( Mini_Aig_t * p )
{
    int Lit = Mini_AigNumNodes(p);
    Mini_AigPush( p, MINI_AIG_NULL, MINI_AIG_NULL );
    return Lit;
}
static int Mini_AigCreatePo( Mini_Aig_t * p, int Lit0 )
{
    int Lit = Mini_AigNumNodes(p);
    assert( Lit0 >= 0 && Lit0 < 2 * Mini_AigNumNodes(p) );
    Mini_AigPush( p, Lit0, MINI_AIG_NULL );
    return Lit;
}

// boolean operations
static int Mini_AigAnd( Mini_Aig_t * p, int Lit0, int Lit1 )
{
    int Lit = Mini_AigNumNodes(p);
    assert( Lit0 >= 0 && Lit0 < 2 * Mini_AigNumNodes(p) );
    assert( Lit1 >= 0 && Lit1 < 2 * Mini_AigNumNodes(p) );
    Mini_AigPush( p, Lit0, Lit1 );
    return Lit;
}
static int Mini_AigOr( Mini_Aig_t * p, int Lit0, int Lit1 )
{
    return Mini_AigLitNot( Mini_AigAnd( p, Mini_AigLitNot(Lit0), Mini_AigLitNot(Lit1) ) );
}
static int Mini_AigMux( Mini_Aig_t * p, int LitC, int Lit1, int Lit0 )
{
    int Res0 = Mini_AigAnd( p, LitC, Lit1 );
    int Res1 = Mini_AigAnd( p, Mini_AigLitNot(LitC), Lit0 );
    return Mini_AigOr( p, Res0, Res1 );
}
static int Mini_AigXor( Mini_Aig_t * p, int Lit0, int Lit1 )
{
    return Mini_AigMux( p, Lit0, Mini_AigLitNot(Lit1), Lit1 );
}

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

