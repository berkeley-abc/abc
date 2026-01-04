/**
 *  Btor2Tools: A tool package for the BTOR format.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2015-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of the Btor2Tools package.
 *  See LICENSE.txt for more information on using this software.
 */

#ifndef BTOR2STACK_H_INCLUDED
#define BTOR2STACK_H_INCLUDED

#include "btor2mem.h"

ABC_NAMESPACE_HEADER_START

#define BTOR2_DECLARE_STACK(name, type)   \
  typedef struct name##Stack name##Stack; \
  struct name##Stack                      \
  {                                       \
    type *start;                          \
    type *top;                            \
    type *end;                            \
  }

BTOR2_DECLARE_STACK (BtorChar, char);
BTOR2_DECLARE_STACK (BtorCharPtr, char *);
BTOR2_DECLARE_STACK (BtorVoidPtr, void *);

#define BTOR2_INIT_STACK(stack) \
  do                            \
  {                             \
    (stack).start = 0;          \
    (stack).top   = 0;          \
    (stack).end   = 0;          \
  } while (0)

#define BTOR2_COUNT_STACK(stack) ((stack).top - (stack).start)
#define BTOR2_SIZE_STACK(stack) ((stack).end - (stack).start)
#define BTOR2_EMPTY_STACK(stack) ((stack).top == (stack).start)
#define BTOR2_FULL_STACK(stack) ((stack).top == (stack).end)
#define BTOR2_RESET_STACK(stack) ((stack).top = (stack).start)

#define BTOR2_RELEASE_STACK(stack) \
  do                               \
  {                                \
    BTOR2_DELETE ((stack).start);  \
    BTOR2_INIT_STACK ((stack));    \
  } while (0)

#define BTOR2_ENLARGE(T, p, o, n)         \
  do                                      \
  {                                       \
    size_t internaln = (o) ? 2 * (o) : 1; \
    (p) = (T *) btorsim_realloc ((p), ((internaln) * sizeof (T))); \
    (n) = internaln;                      \
  } while (0)

#define BTOR2_ENLARGE_STACK(T, stack)                      \
  do                                                       \
  {                                                        \
    size_t old_size  = BTOR2_SIZE_STACK (stack), new_size; \
    size_t old_count = BTOR2_COUNT_STACK (stack);          \
    BTOR2_ENLARGE (T, (stack).start, old_size, new_size);  \
    (stack).top = (stack).start + old_count;               \
    (stack).end = (stack).start + new_size;                \
  } while (0)

#define BTOR2_PUSH_STACK(T, stack, elem)                           \
  do                                                               \
  {                                                                \
    if (BTOR2_FULL_STACK ((stack))) BTOR2_ENLARGE_STACK (T, (stack)); \
    *((stack).top++) = (elem);                                     \
  } while (0)

#define BTOR2_POP_STACK(stack) \
  (assert (!BTOR2_EMPTY_STACK (stack)), (*--(stack).top))

#define BTOR2_PEEK_STACK(stack, idx) \
  (assert ((idx) < BTOR2_COUNT_STACK (stack)), (stack).start[idx])

#define BTOR2_POKE_STACK(stack, idx, elem)      \
  do                                            \
  {                                             \
    assert ((idx) < BTOR2_COUNT_STACK (stack)); \
    (stack).start[idx] = (elem);                \
  } while (0)

ABC_NAMESPACE_HEADER_END

#endif
