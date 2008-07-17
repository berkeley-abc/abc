/**CFile****************************************************************

  FileName    [vec.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resizable arrays.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: vec.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __VEC_H__
#define __VEC_H__

#ifdef __cplusplus
extern "C" {
#endif

#ifdef _WIN32
#define inline __inline // compatible with MS VS 6.0
#pragma warning(disable : 4152) // warning C4152: nonstandard extension, function/data pointer conversion in expression
#pragma warning(disable : 4244) // warning C4244: '+=' : conversion from 'int ' to 'unsigned short ', possible loss of data
#pragma warning(disable : 4514) // warning C4514: 'Vec_StrPop' : unreferenced inline function has been removed
#pragma warning(disable : 4710) // warning C4710: function 'Vec_PtrGrow' not inlined
#endif

#ifndef SINT64
#define SINT64

#ifdef _WIN32
typedef signed __int64     sint64;   // compatible with MS VS 6.0
#else
typedef long long          sint64;
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

// this include should be the first one in the list
// it is used to catch memory leaks on Windows
#ifdef ABC_CHECK_LEAKS
#include "leaks.h"       
#endif

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

#ifndef ABS
#define ABS(a)            ((a) < 0 ? -(a) : (a))
#endif

#ifndef MAX
#define MAX(a,b)        ((a) > (b) ? (a) : (b))
#endif

#ifndef MIN
#define MIN(a,b)        ((a) < (b) ? (a) : (b))
#endif

#ifndef ALLOC
#define ALLOC(type, num)     ((type *) malloc(sizeof(type) * (num)))
#endif

#ifndef CALLOC
#define CALLOC(type, num)     ((type *) calloc((num), sizeof(type)))
#endif

#ifndef FREE
#define FREE(obj)             ((obj) ? (free((char *) (obj)), (obj) = 0) : 0)
#endif

#ifndef REALLOC
#define REALLOC(type, obj, num)    \
        ((obj) ? ((type *) realloc((char *)(obj), sizeof(type) * (num))) : \
         ((type *) malloc(sizeof(type) * (num))))
#endif

#ifndef PRT
#define PRT(a,t)  printf("%s = ", (a)); printf("%7.2f sec\n", (float)(t)/(float)(CLOCKS_PER_SEC))
#endif

#ifndef PRTP
#define PRTP(a,t,T)  printf("%s = ", (a)); printf("%7.2f sec (%6.2f %%)\n", (float)(t)/(float)(CLOCKS_PER_SEC), (T)? 100.0*(t)/(T) : 0.0)
#endif

#include "vecInt.h"
#include "vecFlt.h"
#include "vecStr.h"
#include "vecPtr.h"
#include "vecVec.h"
#include "vecAtt.h"
#include "port_type.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

