/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko

#ifndef vec_h
#define vec_h

#include <stdlib.h>

struct vec_t {
    int    size;
    int    cap;
    void** ptr;
};
typedef struct vec_t vec;

static inline void vec_new (vec* v) {
    v->size = 0;
    v->cap  = 4;
    v->ptr  = (void**)malloc(sizeof(void*)*v->cap);
}

static inline void   vec_delete (vec* v)          { free(v->ptr);   }
static inline void** vec_begin  (vec* v)          { return v->ptr;  }
static inline int    vec_size   (vec* v)          { return v->size; }
static inline void   vec_resize (vec* v, int   k) { v->size = k;    } // only safe to shrink !!
static inline void   vec_push   (vec* v, void* e)
{
    if (v->size == v->cap) {
        int newsize = v->cap * 2+1;
        v->ptr = (void**)realloc(v->ptr,sizeof(void*)*newsize);
        v->cap = newsize; }
    v->ptr[v->size++] = e;
}

#endif
