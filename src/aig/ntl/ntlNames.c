/**CFile****************************************************************

  FileName    [ntlNames.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Data-structure for storing hiNamrchical object names.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlNames.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// name object
typedef struct Ntl_ObjNam_t_ Ntl_ObjNam_t;
struct Ntl_ObjNam_t_
{
    int            iPrev;        // prefix of this name
    int            iNext;        // the next name in the hash table
    char           pName[0];     // name characters
};

// name manager
typedef struct Ntl_ManNam_t_ Ntl_ManNam_t;
struct Ntl_ManNam_t_
{
    // info storage for names
    char *         pStore;       // storage for name objects
    int            nStore;       // the size of allocated storage
    int            iHandle;      // the current free handle
    int            nHandles;     // the number of handles
    int            nRefs;        // reference counter for the manager
    // hash table for names
    int            nBins;         
    unsigned *     pBins;
    // temporaries
    Vec_Str_t *    vName;        // storage for returned name
};

static inline Ntl_ObjNam_t * Ntl_ManNamObj( Ntl_ManNam_t * p, int h )                      { assert( !(h & 3) ); return (Ntl_ObjNam_t *)(p->pStore + h);  }
static inline int            Ntl_ManNamObjHandle( Ntl_ManNam_t * p, Ntl_ObjNam_t * pObj )  { return ((char *)pObj) - p->pStore;                           }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_ManNam_t * Ntl_ManNamStart()
{
    Ntl_ManNam_t * p;
    p = ABC_CALLOC( Ntl_ManNam_t, 1 );
    p->nStore  = (1 << 20);
    p->pStore  = ABC_ALLOC( char, p->nStore );
    p->iHandle = 4;
    p->nBins   = Aig_PrimeCudd( 500000 );
    p->pBins   = ABC_CALLOC( unsigned, p->nBins );
    p->vName   = Vec_StrAlloc( 1000 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Deletes manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManNamStop( Ntl_ManNam_t * p )
{
    Vec_StrFree( p->vName );
    ABC_FREE( p->pStore );
    ABC_FREE( p->pBins );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Deletes manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManNamReportMemUsage( Ntl_ManNam_t * p )
{
    return sizeof(Ntl_ManNam_t) + p->nStore + sizeof(int) * p->nBins + sizeof(int) * Vec_StrSize(p->vName);
}

/**Function*************************************************************

  Synopsis    [References the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManNamRef( Ntl_ManNam_t * p )
{
    p->nRefs++;
}

/**Function*************************************************************

  Synopsis    [Dereferences the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManNamDeref( Ntl_ManNam_t * p )
{
    if ( --p->nRefs == 0 )
        Ntl_ManNamStop( p );
}

/**Function*************************************************************

  Synopsis    [Returns object with the given handle.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/


/**Function*************************************************************

  Synopsis    [Computes hash value of the node using its simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManNamStrHash( char * pStr, int Length, int nTableSize )
{
    static int s_FPrimes[128] = { 
        1009, 1049, 1093, 1151, 1201, 1249, 1297, 1361, 1427, 1459, 
        1499, 1559, 1607, 1657, 1709, 1759, 1823, 1877, 1933, 1997, 
        2039, 2089, 2141, 2213, 2269, 2311, 2371, 2411, 2467, 2543, 
        2609, 2663, 2699, 2741, 2797, 2851, 2909, 2969, 3037, 3089, 
        3169, 3221, 3299, 3331, 3389, 3461, 3517, 3557, 3613, 3671, 
        3719, 3779, 3847, 3907, 3943, 4013, 4073, 4129, 4201, 4243, 
        4289, 4363, 4441, 4493, 4549, 4621, 4663, 4729, 4793, 4871, 
        4933, 4973, 5021, 5087, 5153, 5227, 5281, 5351, 5417, 5471, 
        5519, 5573, 5651, 5693, 5749, 5821, 5861, 5923, 6011, 6073, 
        6131, 6199, 6257, 6301, 6353, 6397, 6481, 6563, 6619, 6689, 
        6737, 6803, 6863, 6917, 6977, 7027, 7109, 7187, 7237, 7309, 
        7393, 7477, 7523, 7561, 7607, 7681, 7727, 7817, 7877, 7933, 
        8011, 8039, 8059, 8081, 8093, 8111, 8123, 8147
    };
    unsigned uHash;
    int i;
    uHash = 0;
    for ( i = 0; i < Length; i++ )
        if ( i & 1 ) 
            uHash *= pStr[i] * s_FPrimes[i & 0x7F];
        else
            uHash ^= pStr[i] * s_FPrimes[i & 0x7F];
    return uHash % nTableSize;
}


/**Function*************************************************************

  Synopsis    [Compares two strings to be equal.]

  Description [Returns 1 if the strings match.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManNamStrCompare_rec( Ntl_ManNam_t * p, char * pStr, int Length, Ntl_ObjNam_t * pThis )
{
    Ntl_ObjNam_t * pNext = (pThis->iPrev)? Ntl_ManNamObj(p, pThis->iPrev) : NULL;
    int LengthNew = strlen(pThis->pName);
    if ( !strncmp( pThis->pName, pStr + Length - LengthNew, LengthNew ) )
        return 0;
    if ( pNext == NULL )
        return 1;
    return Ntl_ManNamStrCompare_rec( p, pStr, Length - LengthNew, pNext );
}


/**Function*************************************************************

  Synopsis    [Returns the place of this state in the table or NULL if it exists.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned * Ntl_ManNamStrHashFind( Ntl_ManNam_t * p, char * pStr, int Length, int * pHandle )
{
    Ntl_ObjNam_t * pThis;
    unsigned * pPlace = p->pBins + Ntl_ManNamStrHash( pStr, Length, p->nBins );
    for ( pThis = (*pPlace)? Ntl_ManNamObj(p, *pPlace) : NULL; pThis; 
          pPlace = (unsigned *)&pThis->iNext, pThis = (*pPlace)? Ntl_ManNamObj(p, *pPlace) : NULL )
              if ( !Ntl_ManNamStrCompare_rec( p, pStr, Length, pThis ) )
              {
                  *pHandle = Ntl_ManNamObjHandle( p, pThis );
                  return NULL;
              }
    *pHandle = -1;
    return pPlace;
}

/**Function*************************************************************

  Synopsis    [Resizes the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManNamStrHashResize( Ntl_ManNam_t * p )
{
    Ntl_ObjNam_t * pThis;
    unsigned * pBinsOld, * piPlace;
    int nBinsOld, iNext, iHandle, Counter, i;
    assert( p->pBins != NULL );
    // replace the table
    pBinsOld = p->pBins;
    nBinsOld = p->nBins;
    p->nBins = Aig_PrimeCudd( 3 * p->nBins ); 
    p->pBins = ABC_CALLOC( unsigned, p->nBins );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < nBinsOld; i++ )
    for ( pThis = (pBinsOld[i]? Ntl_ManNamObj(p, pBinsOld[i]) : NULL),
          iNext = (pThis? pThis->iNext : 0);  
          pThis;  pThis = (iNext? Ntl_ManNamObj(p, iNext) : NULL),   
          iNext = (pThis? pThis->iNext : 0)  )
    {
        pThis->iNext = 0;
        piPlace = Ntl_ManNamStrHashFind( p, pThis->pName, strlen(pThis->pName), &iHandle );
        assert( *piPlace == 0 ); // should not be there
        *piPlace = Ntl_ManNamObjHandle( p, pThis );
        Counter++;
    }
    assert( Counter == p->nHandles );
    ABC_FREE( pBinsOld );
}

/**Function*************************************************************

  Synopsis    [Returns the handle of a new object to represent the name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManNamStrGrow_rec( Ntl_ManNam_t * p, char * pStr, int Length, unsigned * piPlace )
{
    Ntl_ObjNam_t * pThis;
    char * pStrNew;
    int Separ, LengthNew;
    int iHandle;
    assert( Length > 0 );
    // find the separator symbol
    for ( Separ = Length - 2; Separ >= 0 && pStr[Separ] != '/'; Separ-- );
    pStrNew = (Separ == -1) ? pStr : pStr + Separ + 1;
    LengthNew = Length - (pStrNew - pStr);
    // realloc memory if needed
    if ( p->iHandle + (int)sizeof(Ntl_ObjNam_t) + LengthNew+5 > p->nStore )
    {
        int OffSet;
        if ( (char *)piPlace > p->pStore && (char *)piPlace < p->pStore + p->nStore )
            OffSet = (char *)piPlace - p->pStore;
        else
            OffSet = -1;
        p->nStore *= 2;
        p->pStore = ABC_REALLOC( char, p->pStore, p->nStore );
        if ( OffSet >= 0 )
            piPlace = (unsigned *)(p->pStore + OffSet);
    }
    // new entry is created
    p->nHandles++;
    *piPlace = p->iHandle;
    pThis = Ntl_ManNamObj( p, p->iHandle );
    p->iHandle += sizeof(Ntl_ObjNam_t) + 4 * Aig_BitWordNum( 8*(LengthNew+1) );
    pThis->iNext = 0;
    pThis->iPrev = 0;
    strncpy( pThis->pName, pStrNew, LengthNew );
    pThis->pName[LengthNew] = 0;
    // expand hash table if needed
//    if ( p->nHandles > 2 * p->nBins )
//        Ntl_ManNamStrHashResize( p );
    // create previous object if needed
    if ( Separ >= 0 )
    {
        assert( pStr[Separ] == '/' );
        Separ++;
        piPlace = Ntl_ManNamStrHashFind( p, pStr, Separ, &iHandle );
        if ( piPlace != NULL )
            iHandle = Ntl_ManNamStrGrow_rec( p, pStr, Separ, piPlace );
        pThis->iPrev = iHandle;
    }
    return Ntl_ManNamObjHandle( p, pThis );
}

/**Function*************************************************************

  Synopsis    [Finds or adds the given name to storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManNamStrFind( Ntl_ManNam_t * p, char * pStr )
{
    int iHandle;
    Ntl_ManNamStrHashFind( p, pStr, strlen(pStr), &iHandle );
    return iHandle;
}

/**Function*************************************************************

  Synopsis    [Finds or adds the given name to storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Ntl_ManNamStrFindOrAdd( Ntl_ManNam_t * p, char * pStr )
{
    unsigned * piPlace;
    int iHandle, Length = strlen(pStr);
    assert( Length > 0 );
    piPlace = Ntl_ManNamStrHashFind( p, pStr, Length, &iHandle );
    if ( piPlace == NULL )
        return iHandle;
    assert( *piPlace == 0 );
    return Ntl_ManNamStrGrow_rec( p, pStr, Length, piPlace );
}

/**Function*************************************************************

  Synopsis    [Returns name from handle.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ntl_ManNamStr( Ntl_ManNam_t * p, int h )
{
    Ntl_ObjNam_t * pObj;
    int k;
    assert( h && h < p->iHandle );
    Vec_StrClear( p->vName );
    for ( pObj = Ntl_ManNamObj( p, h ); pObj; pObj = pObj->iPrev ? Ntl_ManNamObj(p, pObj->iPrev) : NULL )
        for ( k = strlen(pObj->pName) - 1; k >= 0; k-- )
            Vec_StrPush( p->vName, pObj->pName[k] );
    Vec_StrReverseOrder( p->vName );
    Vec_StrPush( p->vName, 0 );
    return Vec_StrArray( p->vName );
}
 
/**Function*************************************************************

  Synopsis    [Testing procedure for the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManNamTest( Ntl_Man_t * pNtl )
{
    Ntl_ManNam_t * p;
    Ntl_Mod_t * pRoot;
    Ntl_Net_t * pNet;
    int Memory;
    int i, iHandle;
    int clk = clock();

    p = Ntl_ManNamStart();
printf( "a" );
    Memory = 0;
    pRoot = Ntl_ManRootModel( pNtl );
    Ntl_ModelForEachNet( pRoot, pNet, i )
    {
        Memory += strlen(pNet->pName) + 1;
        iHandle = Ntl_ManNamStrFindOrAdd( p, pNet->pName );

//        printf( "Before = %s\n", pNet->pName );
//        printf( "After  = %s\n", Ntl_ManNamStr(p, iHandle) );
    }
    printf( "Net =%7d. Handle =%8d. ", Vec_PtrSize(pRoot->vNets), p->nHandles );
    printf( "Mem old = %7.2f Mb.  Mem new = %7.2f Mb.\n",
        1.0 * Memory / (1 << 20), 1.0 * Ntl_ManNamReportMemUsage(p) / (1 << 20) );
    ABC_PRT( "Time", clock() - clk );
printf( "b" );

    Ntl_ManNamStop( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

