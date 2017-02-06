//===--- vec_int.h ----------------------------------------------------------===
//
//                     satoko: Satisfiability solver
//
// This file is distributed under the BSD 2-Clause License.
// See LICENSE for details.
//
//===------------------------------------------------------------------------===
#ifndef satoko__utils__vec__vec_dble_h
#define satoko__utils__vec__vec_dble_h

#include <assert.h>
#include <stdio.h>
#include <string.h>

#include "../mem.h"

#include "misc/util/abc_global.h"
ABC_NAMESPACE_HEADER_START

typedef struct vec_dble_t_ vec_dble_t;
struct vec_dble_t_ {
    unsigned cap;
    unsigned size;
    double *data;
};

//===------------------------------------------------------------------------===
// Vector Macros
//===------------------------------------------------------------------------===
#define vec_dble_foreach(vec, entry, i) \
    for (i = 0; (i < vec->size) && (((entry) = vec_dble_at(vec, i)), 1); i++)

#define vec_dble_foreach_start(vec, entry, i, start) \
    for (i = start; (i < vec_dble_size(vec)) && (((entry) = vec_dble_at(vec, i)), 1); i++)

#define vec_dble_foreach_stop(vec, entry, i, stop) \
    for (i = 0; (i < stop) && (((entry) = vec_dble_at(vec, i)), 1); i++)

//===------------------------------------------------------------------------===
// Vector API
//===------------------------------------------------------------------------===
static inline vec_dble_t *vec_dble_alloc(unsigned cap)
{
    vec_dble_t* p = satoko_alloc(vec_dble_t, 1);

    if (cap > 0 && cap < 16)
        cap = 16;
    p->size = 0;
    p->cap = cap;
    p->data = p->cap ? satoko_alloc(double, p->cap) : NULL;
    return p;
}

static inline vec_dble_t *vec_dble_alloc_exact(unsigned cap)
{
    vec_dble_t* p = satoko_alloc(vec_dble_t, 1);

    p->size = 0;
    p->cap = cap;
    p->data = p->cap ? satoko_alloc(double, p->cap) : NULL;
    return p;
}

static inline vec_dble_t *vec_dble_init(unsigned size, double value)
{
    vec_dble_t* p = satoko_alloc(vec_dble_t, 1);

    p->cap = size;
    p->size = size;
    p->data = p->cap ? satoko_alloc(double, p->cap) : NULL;
    memset(p->data, value, sizeof(double) * p->size);
    return p;
}

static inline void vec_dble_free(vec_dble_t *p)
{
    if (p->data != NULL)
        satoko_free(p->data);
    satoko_free(p);
}

static inline unsigned vec_dble_size(vec_dble_t *p)
{
    return p->size;
}

static inline void vec_dble_resize(vec_dble_t *p, unsigned new_size)
{
    p->size = new_size;
    if (p->cap >= new_size)
        return;
    p->data = satoko_realloc(double, p->data, new_size);
    assert(p->data != NULL);
    p->cap = new_size;
}

static inline void vec_dble_reserve(vec_dble_t *p, unsigned new_cap)
{
    if (p->cap >= new_cap)
        return;
    p->data = satoko_realloc(double, p->data, new_cap);
    assert(p->data != NULL);
    p->cap = new_cap;
}

static inline unsigned vec_dble_capacity(vec_dble_t *p)
{
    return p->cap;
}

static inline int vec_dble_empty(vec_dble_t *p)
{
    return p->size ? 0 : 1;
}

static inline void vec_dble_erase(vec_dble_t *p)
{
    satoko_free(p->data);
    p->size = 0;
    p->cap = 0;
}

static inline double vec_dble_at(vec_dble_t *p, unsigned i)
{
    assert(i >= 0 && i < p->size);
    return p->data[i];
}

static inline double *vec_dble_at_ptr(vec_dble_t *p, unsigned i)
{
    assert(i >= 0 && i < p->size);
    return p->data + i;
}

static inline double *vec_dble_data(vec_dble_t *p)
{
    assert(p);
    return p->data;
}

static inline void vec_dble_duplicate(vec_dble_t *dest, const vec_dble_t *src)
{
    assert(dest != NULL && src != NULL);
    vec_dble_resize(dest, src->cap);
    memcpy(dest->data, src->data, sizeof(double) * src->cap);
    dest->size = src->size;
}

static inline void vec_dble_copy(vec_dble_t *dest, const vec_dble_t *src)
{
    assert(dest != NULL && src != NULL);
    vec_dble_resize(dest, src->size);
    memcpy(dest->data, src->data, sizeof(double) * src->size);
    dest->size = src->size;
}

static inline void vec_dble_push_back(vec_dble_t *p, double value)
{
    if (p->size == p->cap) {
        if (p->cap < 16)
            vec_dble_reserve(p, 16);
        else
            vec_dble_reserve(p, 2 * p->cap);
    }
    p->data[p->size] = value;
    p->size++;
}

static inline void vec_dble_assign(vec_dble_t *p, unsigned i, double value)
{
    assert((i >= 0) && (i < vec_dble_size(p)));
    p->data[i] = value;
}

static inline void vec_dble_insert(vec_dble_t *p, unsigned i, double value)
{
    assert((i >= 0) && (i < vec_dble_size(p)));
    vec_dble_push_back(p, 0);
    memmove(p->data + i + 1, p->data + i, (p->size - i - 2) * sizeof(double));
    p->data[i] = value;
}

static inline void vec_dble_drop(vec_dble_t *p, unsigned i)
{
    assert((i >= 0) && (i < vec_dble_size(p)));
    memmove(p->data + i, p->data + i + 1, (p->size - i - 1) * sizeof(double));
    p->size -= 1;
}

static inline void vec_dble_clear(vec_dble_t *p)
{
    p->size = 0;
}

static inline int vec_dble_asc_compare(const void *p1, const void *p2)
{
    const double *pp1 = (const double *) p1;
    const double *pp2 = (const double *) p2;

    if (*pp1 < *pp2)
        return -1;
    if (*pp1 > *pp2)
        return 1;
    return 0;
}

static inline int vec_dble_desc_compare(const void* p1, const void* p2)
{
    const double *pp1 = (const double *) p1;
    const double *pp2 = (const double *) p2;

    if (*pp1 > *pp2)
        return -1;
    if (*pp1 < *pp2)
        return 1;
    return 0;
}

static inline void vec_dble_sort(vec_dble_t* p, int ascending)
{
    if (ascending)
        qsort((void *) p->data, p->size, sizeof(double),
              (int (*)(const void*, const void*)) vec_dble_asc_compare);
    else
        qsort((void *) p->data, p->size, sizeof(double),
              (int (*)(const void*, const void*)) vec_dble_desc_compare);
}

static inline long vec_dble_memory(vec_dble_t *p)
{
    return p == NULL ? 0 : sizeof(double) * p->cap + sizeof(vec_dble_t);
}

static inline void vec_dble_print(vec_dble_t *p)
{
    unsigned i;
    assert(p != NULL);
    fprintf(stdout, "Vector has %u(%u) entries: {", p->size, p->cap);
    for (i = 0; i < p->size; i++)
        fprintf(stdout, " %f", p->data[i]);
    fprintf(stdout, " }\n");
}

ABC_NAMESPACE_HEADER_END
#endif /* satoko__utils__vec__vec_dble_h */
