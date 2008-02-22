// Portable Data Types

#ifndef __PORT_TYPE__
#define __PORT_TYPE__

/**
 * Pointer difference type; replacement for ptrdiff_t.
 *
 * This is a signed integral type that is the same size as a pointer.
 *
 * NOTE: This type may be different sizes on different platforms.
 */
#if       defined(__ccdoc__)
typedef platform_dependent_type PORT_PTRDIFF_T;
#elif     defined(LIN64)
typedef long PORT_PTRDIFF_T;
#elif     defined(NT64)
typedef long long PORT_PTRDIFF_T;
#elif     defined(NT) || defined(LIN) || defined(WIN32)
typedef int PORT_PTRDIFF_T;
#else
   #error unknown platform
#endif /* defined(PLATFORM) */

/**
 * Unsigned integral type that can contain a pointer.
 *
 * This is an unsigned integral type that is the same size as a pointer.
 *
 * NOTE: This type may be different sizes on different platforms.
 */
#if       defined(__ccdoc__)
typedef platform_dependent_type PORT_PTRUINT_T;
#elif     defined(LIN64)
typedef unsigned long PORT_PTRUINT_T;
#elif     defined(NT64)
typedef unsigned long long PORT_PTRUINT_T;
#elif     defined(NT) || defined(LIN) || defined(WIN32)
typedef unsigned int PORT_PTRUINT_T;
#else
   #error unknown platform
#endif /* defined(PLATFORM) */


/**
 * 64-bit signed integral type.
 */
#if       defined(__ccdoc__)
typedef platform_dependent_type PORT_INT64_T;
#elif     defined(LIN64)
typedef long PORT_INT64_T;
#elif     defined(NT64) || defined(LIN)
typedef long long PORT_INT64_T;
#elif     defined(WIN32) || defined(NT)
typedef signed __int64 PORT_INT64_T;
#else
   #error unknown platform
#endif /* defined(PLATFORM) */

#endif
