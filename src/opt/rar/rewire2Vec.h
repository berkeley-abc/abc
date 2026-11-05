/**CFile****************************************************************

  FileName    [rewire2Vec.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring.]

  Synopsis    [Independent rewiring implementation derived from rewire.]

  Author      [Jiun-Hao Chen]

  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - November 4, 2026.]

  Revision    [$Id: rewire2Vec.h,v 1.00 2026/11/04 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef RAR2_VI_H
#define RAR2_VI_H

// vector of 32-bit integers

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#include "rewire2Rng.h"

ABC_NAMESPACE_HEADER_START

// swapping two variables
#define RW2_SWAP(Type, a, b) \
    {                       \
        Type t = a;         \
        a = b;              \
        b = t;              \
    }

typedef struct rw2_vi_ {
    int size;
    int cap;
    int *ptr;
} rw2_vi;

// iterator through the entries in the vector
#define Rw2_Vi_ForEachEntry(v, entry, i)             for (i = 0; (i < (v)->size) && (((entry) = Rw2_Vi_Read((v), i)), 1); i++)
#define Rw2_Vi_ForEachEntryReverse(v, entry, i)      for (i = (v)->size - 1; (i >= 0) && (((entry) = Rw2_Vi_Read((v), i)), 1); i--)
#define Rw2_Vi_ForEachEntryStart(v, entry, i, start) for (i = start; (i < (v)->size) && (((entry) = Rw2_Vi_Read((v), i)), 1); i++)
#define Rw2_Vi_ForEachEntryStop(v, entry, i, stop)   for (i = 0; (i < stop) && (((entry) = Rw2_Vi_Read((v), i)), 1); i++)

static inline void Rw2_Vi_Start(rw2_vi *v, int cap) {
    v->size = 0;
    v->cap = cap;
    v->ptr = (int *)malloc(sizeof(int) * cap);
}

static inline rw2_vi *Rw2_Vi_Alloc(int cap) {
    rw2_vi *v = (rw2_vi *)malloc(sizeof(rw2_vi));
    Rw2_Vi_Start(v, cap);
    return v;
}

static inline void Rw2_Vi_Stop(rw2_vi *v) {
    if (v->ptr) free(v->ptr);
}

static inline void Rw2_Vi_Free(rw2_vi *v) {
    if (v->ptr) free(v->ptr);
    free(v);
}

static inline int Rw2_Vi_Size(rw2_vi *v) {
    return v->size;
}

static inline int Rw2_Vi_Space(rw2_vi *v) {
    return v->cap - v->size;
}

static inline int *Rw2_Vi_Array(rw2_vi *v) {
    return v->ptr;
}

static inline int Rw2_Vi_Read(rw2_vi *v, int k) {
    assert(k < v->size);
    return v->ptr[k];
}

static inline void Rw2_Vi_Write(rw2_vi *v, int k, int e) {
    assert(k < v->size);
    v->ptr[k] = e;
}

static inline void Rw2_Vi_Shrink(rw2_vi *v, int k) {
    assert(k <= v->size);
    v->size = k;
} // only safe to shrink !!

static inline int Rw2_Vi_Pop(rw2_vi *v) {
    assert(v->size > 0);
    return v->ptr[--v->size];
}

static inline void Rw2_Vi_Grow(rw2_vi *v) {
    if (v->size < v->cap)
        return;
    int newcap = (v->cap < 4) ? 8 : (v->cap / 2) * 3;
    v->ptr = (int *)realloc(v->ptr, sizeof(int) * newcap);
    if (v->ptr == NULL) {
        printf("Failed to realloc memory from %.1f MB to %.1f MB.\n", 4.0 * v->cap / (1 << 20), (float)4.0 * newcap / (1 << 20));
        fflush(stdout);
    }
    v->cap = newcap;
}

static inline rw2_vi *Rw2_Vi_Dup(rw2_vi *v) {
    rw2_vi *pNew = Rw2_Vi_Alloc(v->size);
    memcpy(pNew->ptr, v->ptr, sizeof(int) * v->size);
    pNew->size = v->size;
    return pNew;
}

static inline void Rw2_Vi_Push(rw2_vi *v, int e) {
    Rw2_Vi_Grow(v);
    v->ptr[v->size++] = e;
}

static inline void Rw2_Vi_PushTwo(rw2_vi *v, int e1, int e2) {
    Rw2_Vi_Push(v, e1);
    Rw2_Vi_Push(v, e2);
}

static inline void Rw2_Vi_PushArray(rw2_vi *v, int *p, int n) {
    for (int i = 0; i < n; i++)
        Rw2_Vi_Push(v, p[i]);
}

static inline void Rw2_Vi_PushOrder(rw2_vi *v, int e) {
    Rw2_Vi_Push(v, e);
    if (v->size > 1)
        for (int i = v->size - 2; i >= 0; i--) {
            if (v->ptr[i] > v->ptr[i + 1]) {
                RW2_SWAP(int, v->ptr[i], v->ptr[i + 1])
            } else {
                break;
            }
        }
}

static inline void Rw2_Vi_Fill(rw2_vi *v, int n, int fill) {
    int i;
    Rw2_Vi_Shrink(v, 0);
    for (i = 0; i < n; i++)
        Rw2_Vi_Push(v, fill);
}

static inline int Rw2_Vi_Drop(rw2_vi *v, int i) {
    assert(i >= 0 && i < v->size);
    int Entry = v->ptr[i];
    for (; i < v->size - 1; i++)
        v->ptr[i] = v->ptr[i + 1];
    Rw2_Vi_Shrink(v, v->size - 1);
    return Entry;
}

static inline int Rw2_Vi_Find(rw2_vi *v, int e) {
    int j;
    for (j = 0; j < v->size; j++)
        if (v->ptr[j] == e)
            return j;
    return -1;
}

static inline int Rw2_Vi_Remove(rw2_vi *v, int e) {
    int j = Rw2_Vi_Find(v, e);
    if (j == -1)
        return 0;
    Rw2_Vi_Drop(v, j);
    return 1;
}

static inline void Rw2_Vi_Randomize(rw2_vi *v) {
    for (int i = 0; i < v->size; i++) {
        int iRand = Rw2_Random_Num(0) % v->size;
        RW2_SWAP(int, v->ptr[iRand], v->ptr[i]);
    }
}

static inline void Rw2_Vi_Reverse(rw2_vi *v) {
    int i, j;
    for (i = 0, j = v->size - 1; i < j; i++, j--)
        RW2_SWAP(int, v->ptr[i], v->ptr[j]);
}

static inline void Rw2_Vi_Print(rw2_vi *v) {
    printf("Array with %d entries:", v->size);
    int i, entry;
    Rw2_Vi_ForEachEntry(v, entry, i)
        printf(" %d", entry);
    printf("\n");
}

static inline void Rw2_Vi_SelectSort(rw2_vi *v) {
    int *pArray = Rw2_Vi_Array(v);
    int nSize = Rw2_Vi_Size(v);
    int temp, i, j, best_i;
    for (i = 0; i < nSize - 1; i++) {
        best_i = i;
        for (j = i + 1; j < nSize; j++)
            if (pArray[j] < pArray[best_i])
                best_i = j;
        temp = pArray[i];
        pArray[i] = pArray[best_i];
        pArray[best_i] = temp;
    }
}

ABC_NAMESPACE_HEADER_END

#endif // RAR2_VI_H
