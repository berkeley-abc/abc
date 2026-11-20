#ifndef ABC__misc__espresso__espressoPort_h
#define ABC__misc__espresso__espressoPort_h

#ifdef ESPRESSO_MAIN
#include "../util/abc_namespaces.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#if defined(_MSC_VER)
#define ABC_THREAD_LOCAL __declspec(thread)
#elif defined(__cplusplus)
#define ABC_THREAD_LOCAL thread_local
#else
#define ABC_THREAD_LOCAL _Thread_local
#endif
#else
#include "../util/abc_global.h"
#endif
#include <ctype.h>
#include <limits.h>

ABC_NAMESPACE_HEADER_START

int Espresso_Main(int argc, char **argv, FILE *out, FILE *err);

ABC_NAMESPACE_HEADER_END

#endif
